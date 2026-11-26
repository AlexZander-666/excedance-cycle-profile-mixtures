"""Build integer endpoint rows and propose dyadic sign nodes; verify every sign exactly."""
from fractions import Fraction as Q
from math import comb,factorial
from pathlib import Path
from flint import fmpz_poly,ctx
import json

def cycle(j):
    return fmpz_poly([0]+[sum((-1)**b*comb(j,b)*(u+1-b)**(j-1)
                             for b in range(u+1)) for u in range(j-1)])
def parts(n,allowed):
    if n==0:
        yield ()
    elif allowed:
        a=allowed[0]
        for e in range(n//a+1):
            for rest in parts(n-e*a,allowed[1:]):
                yield ((a,e),)+rest if e else rest

def row(n,allowed):
    cs={j:cycle(j) for j in allowed}
    f=fmpz_poly()
    for part in parts(n,sorted(allowed,reverse=True)):
        scale=factorial(n);p=fmpz_poly([1])
        for j,e in part:
            d=factorial(j)**e*factorial(e)
            assert scale%d==0
            scale//=d;p*=cs[j]**e
        f+=scale*p
    return f

def mesh(f):
    degree = f.degree()-1
    assert f[0]==0
    f=fmpz_poly(f.coeffs()[1:]);ctx.prec=200
    roots=f.complex_roots()
    assert len(roots)==degree and all(r.imag.is_zero() and e==1 for r,e in roots)
    xs=sorted(float(r.real) for r,e in roots)
    nodes=[]
    for l,r in zip([2*xs[0],*xs],[*xs,xs[-1]/2]):
        for k in range(200):
            h=int((l+r)/2*2**k)
            if l<h/2**k<r and h<0:
                nodes.append((h,k));break
        else:raise ValueError('Cannot find node')
    for i,(h,k) in enumerate(nodes):
        val=sum(int(c)*h**j*(2**k)**(degree-j) for j,c in enumerate(f.coeffs()))
        assert (-1)**i*val>0
    return nodes

def jets(f,x):
    def ev(p):return sum(int(c)*x**j for j,c in enumerate(p.coeffs()))
    return ev(f),ev(f.derivative()),ev(f.derivative().derivative())

if __name__=='__main__':
    root=Path(__file__).resolve().parent
    sets={34:([3,4,7,10,13,14,16,17,20,23], [2,3,5,6,8,9,12,15,18,21,24,27])}
    short_a=[2,4,6,9,11,13,16,18,20,23,25,27,30,32,34,36,37,39,41,43]
    sets[44]=(short_a,sorted(set(range(2,44))-set(short_a)))
    for n,shorts in sets.items():
        data={};rows={}
        for tag,short in zip("AB",shorts):
            allowed=short+[n]
            f=row(n,allowed);rows[tag]=f
            data[tag]={'allowed':allowed,'quotient':[int(c) for c in f.coeffs()[1:]],'nodes':mesh(f)}
        weight=2 if n==34 else 1
        x=Q(-2,15) if n==34 else Q(-1,2)
        value,first,second=jets(rows['A']+weight*rows['B'],x)
        gap=first**2-value*second
        assert gap<0
        data['gap']=str(gap)
        (root/f'dyadic{n}.json').write_text(json.dumps(data,indent=2)+'\n')
        print(n,'PASS endpoint meshes and exact gap',gap)
