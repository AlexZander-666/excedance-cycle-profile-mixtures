"""Run the exact printed certificate and reproduce the named PDF twice."""
from fractions import Fraction
from hashlib import sha256
import json,os,shutil,subprocess,tempfile
from pathlib import Path
base=Path(__file__).resolve().parent
s=(base/'main.tex').read_text()
scope={}
exec(s.split('\\begin{verbatim}',1)[1].split('\\end{verbatim}',1)[0],scope)
for n in (34,44):
    cert=json.loads((base.parent/f'certificates/dyadic{n}.json').read_text())
    a,b,gap=scope[f'case{n}']
    assert gap==Fraction(cert['gap'])
    assert a==[0]+cert['A']['quotient'] and b==[0]+cert['B']['quotient']
print('PASS printed finite calculation and independent coefficients')
with tempfile.TemporaryDirectory() as tmp:
    builds=[]
    for name in ('a','b'):
        folder=Path(tmp)/name;folder.mkdir()
        shutil.copyfile(base/'main.tex',folder/'main.tex')
        for _ in range(2):
            subprocess.run(['pdflatex','-no-shell-escape','-interaction=nonstopmode','-halt-on-error','main.tex'],cwd=folder,check=True,env=dict(os.environ,SOURCE_DATE_EPOCH='1795651200',FORCE_SOURCE_DATE='1',TZ='UTC'),stdout=subprocess.DEVNULL)
        bad=[x for x in (folder/'main.log').read_text().splitlines() if 'Warning:' in x or 'Overfull ' in x or 'Missing character:' in x]
        if bad:raise ValueError(bad)
        builds.append((folder/'main.pdf').read_bytes())
    assert builds[0]==builds[1]
    (base/'main.pdf').write_bytes(builds[0])
    print('Two matching builds:',sha256(builds[0]).hexdigest())
