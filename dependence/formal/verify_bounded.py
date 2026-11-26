"""Rebuild an archived Lean closure on local storage using a bounded number of processes."""
import argparse
from concurrent.futures import FIRST_COMPLETED, ThreadPoolExecutor, wait
from hashlib import file_digest
import json
import os
from pathlib import Path
import re
import shutil
import subprocess
import time

ALLOWED = {"propext", "Classical.choice", "Quot.sound"}
AXIOMS = re.compile(r"^'([^']+)' (?:does not depend on any axioms|depends on axioms:\s*\[([^\]]*)\])\s*$", re.M)
IMPORTS = re.compile(r"^(?:(?:public|private|meta)\s+)*import[ \t]+([^\n]+)", re.M)
ID = re.compile(r"[A-Za-z_][A-Za-z_0-9]*(?:\.[A-Za-z_][A-Za-z_0-9]*)*")


def digest(path):
    with path.open("rb") as f:
        return file_digest(f,"sha256").hexdigest()


def main():
    a=argparse.ArgumentParser(description=__doc__)
    a.add_argument("source",type=Path)
    a.add_argument("audit")
    a.add_argument("work",type=Path,help="New, nonexistent work directory on local storage")
    a.add_argument("--packages",type=Path,required=True)
    a.add_argument("--jobs",type=int,default=6)
    a.add_argument("--resume",action="store_true",help="Resume only this previously recorded cold run")
    args=a.parse_args()
    if not ID.fullmatch(args.audit) or not 1<=args.jobs<=16:
        a.error("Invalid audit or job count")
    src=args.source.resolve(strict=True)
    work=args.work.resolve()
    if args.resume:
        if not (work/"initial.json").is_file(): raise ValueError("No initialized cold run to resume")
    else:
        work.mkdir()
    deps=args.packages.resolve(strict=True)
    env={k:v for k,v in os.environ.items() if not k.startswith("LEAN_")}
    env["LEAN_NUM_THREADS"]="2"
    def query(argv):
        return subprocess.check_output(argv,cwd=work,env=env,text=True).strip()
    manifest={}
    for line in (src/"SHA256SUMS").read_text().splitlines():
        h,n=line.split(maxsplit=1)
        path=Path(n)
        if path.is_absolute() or ".." in path.parts or n in manifest or not re.fullmatch("[0-9a-f]{64}",h):
            raise ValueError(f"Invalid manifest entry {n}")
        if digest(src/n)!=h:
            raise ValueError(f"Digest mismatch for {n}")
        manifest[n]=h
    modules={n[:-5].replace("/","."):n for n in manifest if n.endswith(".lean")}
    for n in ["lean-toolchain","lake-manifest.json","lakefile.toml",*modules.values()]:
        (work/n).parent.mkdir(parents=True,exist_ok=True)
        if not args.resume:
            shutil.copyfile(src/n,work/n)
        if digest(work/n)!=manifest[n]: raise ValueError(f"Source copy differs for {n}")
    local=work/".lake/build/lib/lean"
    local.mkdir(parents=True,exist_ok=args.resume)
    if args.resume:
        if (work/".lake/packages").resolve(strict=True)!=deps: raise ValueError("Dependency root changed")
    else:
        (work/".lake/packages").symlink_to(deps,target_is_directory=True)
    external=set()
    for p in json.loads((work/"lake-manifest.json").read_text())["packages"]:
        if p["type"]!="git": raise ValueError(f"Unpinned path dependency {p}")
        repo=(deps/p["name"]).resolve(strict=True)
        rev=query(["git","-C",repo,"rev-parse","HEAD"])
        if rev!=p["rev"] or query(["git","-C",repo,"status","--porcelain","--untracked-files=no"]):
            raise ValueError(f"Modified dependency {p['name']}")
        external.add((repo/".lake/build/lib/lean").resolve())
        print("PIN",p["name"],rev,flush=True)
    prefix=Path(query(["lean","--print-prefix"])).resolve()
    tool=prefix/"bin"
    external.add(prefix/"lib/lean")
    paths=[Path(p).resolve() for p in query(["lake","env","printenv","LEAN_PATH"]).split(os.pathsep) if p]
    if set(paths)-external!={local} or (not args.resume and any(local.iterdir())):
        raise ValueError(f"Foreign path or preexisting local artifact: {paths}")
    env["LEAN_PATH"]=os.pathsep.join(map(str,paths))
    print(query([tool/"lean","--version"]),env["LEAN_PATH"],sep="\n",flush=True)
    logs=work/"receipts"
    logs.mkdir(exist_ok=args.resume)
    initial={"manifest_sha256":digest(src/"SHA256SUMS"),"driver":digest(Path(__file__)),
             "audit":args.audit,"external_packages":str(deps),"path":env["LEAN_PATH"],
             "toolchain":query([tool/"lean","--version"]),"empty_at_initialization":True}
    meta=work/"initial.json"
    if args.resume:
        if json.loads(meta.read_text())!=initial: raise ValueError("Run metadata differs from the frozen inputs")
    else:
        meta.write_text(json.dumps(initial,sort_keys=True,indent=2)+"\n")
    graph={}
    for mod,n in modules.items():
        if not ID.fullmatch(mod): raise ValueError(mod)
        graph[mod]={m for line in IMPORTS.findall((work/n).read_text())
                    for m in line.partition("--")[0].split() if m in modules}
    todo=[args.audit]
    closure=set()
    while todo:
        key=todo.pop()
        if key not in closure:
            closure.add(key)
            todo.extend(graph[key])
    if closure!=set(modules):
        raise ValueError("Source inventory differs from top import closure")
    targets=re.findall(r"^#print axioms (\S+)\s*$",(work/modules[args.audit]).read_text(),re.M)
    if not targets or len(set(targets))!=len(targets): raise ValueError("Missing or repeated audit entry")

    def objects(mod):
        obj=local/Path(modules[mod]).with_suffix(".olean")
        files={f.name:digest(f) for f in obj.parent.glob(obj.stem+".*") if f.is_file()}
        if obj.name not in files: raise ValueError(f"Missing local object for {mod}")
        return files
    def receipt(mod):
        return {"source_sha256":manifest[modules[mod]],"objects":objects(mod),
                "log_sha256":digest(logs/(mod+".log"))}
    def execute(mod):
        started=time.monotonic()
        log=logs/(mod+".log")
        obj=local/Path(modules[mod]).with_suffix(".olean")
        obj.parent.mkdir(parents=True,exist_ok=True)
        with log.open("w") as f:
            def run(argv):
                status=subprocess.run(argv,cwd=work,env=env,stdout=f,stderr=subprocess.STDOUT).returncode
                if status: raise RuntimeError(f"{mod} exit {status}: {log}\n{log.read_text(errors='replace')[-3600:]}")
            run([tool/"lean","-DwarningAsError=true","-o",obj,modules[mod]])
            if mod==args.audit:
                f.flush()
                result=AXIOMS.findall(log.read_text())
                if len(result)!=len(targets) or set(targets)!={name for name,_ in result}:
                    raise ValueError(f"Incomplete audit: {log}")
                for name,raw in result:
                    if {x.strip() for x in raw.split(",") if x.strip()}-ALLOWED:
                        raise ValueError(f"Unexpected axioms for {name}: {raw}")
            if any(m.startswith(mod+".") for m in modules):
                helper=logs/(mod+".replay.lean")
                helper.write_text("import LeanChecker\n#eval do\n  Lean.initSearchPath (← Lean.findSysroot)\n"
                                  +"  replayFromImports "+chr(96)+mod+"\n")
                run([tool/"lean","-DwarningAsError=true",helper])
            else:
                run([tool/"leanchecker","--verbose",mod])
        record=logs/(mod+".json")
        temp=record.with_suffix(".incomplete")
        data=receipt(mod)
        temp.write_text(json.dumps(data,sort_keys=True)+"\n")
        temp.replace(record)
        return mod,data["objects"][obj.name],data["log_sha256"],time.monotonic()-started
    pending=set(modules)
    done=set()
    active={}
    if args.resume:
        recorded={m for m in modules if (logs/(m+".json")).is_file()}
        for m in recorded:
            if not graph[m]<=recorded or json.loads((logs/(m+".json")).read_text())!=receipt(m):
                raise ValueError(f"Corrupt or unsupported cold checkpoint at {m}")
        pending-=recorded
        done|=recorded
        print(f"RESUME {len(done)} verified modules of this cold run",flush=True)
    with ThreadPoolExecutor(max_workers=args.jobs) as pool:
        while pending or active:
            ready=sorted((m for m in pending if graph[m]<=done),key=lambda m:(-(work/modules[m]).stat().st_size,m))
            for m in ready[:args.jobs-len(active)]:
                pending.remove(m)
                active[pool.submit(execute,m)]=m
            if not active: raise ValueError("Local import cycle")
            finished,_=wait(active,return_when=FIRST_COMPLETED)
            for run in finished:
                m,obj,log,t=run.result()
                active.pop(run)
                done.add(m)
                print(f"PASS {len(done)}/{len(modules)} {m} source={manifest[modules[m]]} olean={obj} receipt={log} elapsed={t:.2f}",flush=True)
    print((logs/(args.audit+".log")).read_text(),end="")
    print(f"PASS: {len(modules)} fresh local strict builds and independent kernel replays; {len(targets)} declarations audited.",flush=True)

if __name__=="__main__":
    main()
