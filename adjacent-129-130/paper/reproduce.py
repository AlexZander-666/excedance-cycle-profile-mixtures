"""Build the signed PDF twice and compare direct TeX with a fresh ZIP extraction."""

from hashlib import sha256
import os
from pathlib import Path
import re
import shutil
import subprocess
from tempfile import TemporaryDirectory
from zipfile import ZIP_DEFLATED, ZipFile, ZipInfo


root = Path(__file__).resolve().parent
sources = ("main.tex", "two-cycle.tex")
target = root / "arxiv-source.zip"
local_tex = Path.home() / ".cache/spark-math-research/texlive/2026/bin/aarch64-linux/pdflatex"
pdflatex = os.environ.get("PDFLATEX") or shutil.which("pdflatex")
if pdflatex is None:
    pdflatex = str(local_tex)
env = dict(os.environ, SOURCE_DATE_EPOCH="1795651200", FORCE_SOURCE_DATE="1", TZ="UTC")

def build(from_zip, staged_zip):
    label = "extracted ZIP" if from_zip else "direct TeX"
    with TemporaryDirectory(prefix="dependence-130-tex-") as temporary:
        folder = Path(temporary)
        if from_zip:
            with ZipFile(staged_zip) as archive:
                assert archive.testzip() is None
                assert tuple(archive.namelist()) == sources
                for name in sources:
                    data = archive.read(name)
                    assert data == (root / name).read_bytes()
                    (folder / name).write_bytes(data)
        else:
            for name in sources:
                shutil.copyfile(root / name, folder / name)
        for pass_number in (1, 2):
            result = subprocess.run(
                [pdflatex, "-no-shell-escape", "-interaction=nonstopmode", "-halt-on-error", "main.tex"],
                cwd=folder, env=env, stdout=subprocess.PIPE, stderr=subprocess.STDOUT,
            )
            if result.returncode:
                raise RuntimeError(result.stdout.decode(errors="replace"))
            print(f"{label} pass {pass_number}: exit 0")
        log = (folder / "main.log").read_text()
        messages = re.findall(
            r"^(?:Overfull|Missing character|LaTeX Warning|Package \S+ Warning).*", log, re.M,
        )
        if messages:
            raise RuntimeError("\n".join(messages))
        return (folder / "main.pdf").read_bytes()


# Read every input before staging output. A failed build leaves the distributed files intact.
inputs = {name: (root / name).read_bytes() for name in sources}
with TemporaryDirectory(prefix=".tex-rebuild-", dir=root) as temporary:
    stage = Path(temporary)
    staged_zip = stage / target.name
    with ZipFile(staged_zip, "w") as archive:
        for name, data in inputs.items():
            entry = ZipInfo(name, (2026, 11, 26, 0, 0, 0))
            entry.create_system = 3
            entry.external_attr = 0o100644 << 16
            archive.writestr(entry, data, ZIP_DEFLATED, compresslevel=9)
    pdf = build(False, staged_zip)
    if pdf != build(True, staged_zip):
        raise RuntimeError("Direct and extracted ZIP builds produced different PDFs")
    staged_pdf = stage / "main.pdf"
    staged_pdf.write_bytes(pdf)
    os.replace(staged_zip, target)
    os.replace(staged_pdf, root / "main.pdf")
print("Fresh direct and extracted-ZIP builds agree byte for byte")
print(f"{sha256(pdf).hexdigest()}  main.pdf")
print(f"{sha256(target.read_bytes()).hexdigest()}  arxiv-source.zip")
