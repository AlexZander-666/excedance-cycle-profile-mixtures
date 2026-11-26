"""Recompute the exact sign, reciprocal-grid and Lean data receipts from an unpacked source ZIP."""
from pathlib import Path
import shutil
import subprocess
import sys
from tempfile import TemporaryDirectory

here = Path(__file__).resolve().parent
project = here.parent
with TemporaryDirectory(prefix="two-cycle-130-independent-checks-") as folder:
    root = Path(folder)
    work = root / "independent-two-cycle-strip"
    shutil.copytree(here / "two-cycle-130", work / "two-cycle-130")
    shutil.copytree(here / "parity-concentration", work / "parity-concentration")
    primary = work / "two-cycle-130"
    independent = work / "parity-concentration"

    def run(script, cwd):
        return subprocess.check_output([sys.executable, "-B", script], cwd=cwd)

    print(run("check_arithmetic.py", primary).decode(), end="")
    log = run("individual_roots.py", primary)
    if log != (here / "two-cycle-130/individual-roots.log").read_bytes():
        raise SystemExit("Unexpected leading reciprocal-grid transcript")
    for name in ("P-half-brackets.tsv", "Q-half-brackets.tsv"):
        if (primary / name).read_bytes() != (here / "two-cycle-130" / name).read_bytes():
            raise SystemExit(f"Root bracket mismatch in {name}")
    independent_log = run("isolate_130.py", independent)
    if independent_log != (here / "parity-concentration/isolated-roots.log").read_bytes():
        raise SystemExit("Unexpected independent isolation transcript")
    generated = root / "formal/LongCycleBounds/TwoCycle130RootData.lean"
    generated.parent.mkdir(parents=True)
    run("generate_root_mesh.py", primary)
    if generated.read_bytes() != (project / "LongCycleBounds" / generated.name).read_bytes():
        raise SystemExit("Generated Lean data differ from the frozen formal source")
print("PASS both reciprocal isolations and the regenerated full-axis Lean meshes")
