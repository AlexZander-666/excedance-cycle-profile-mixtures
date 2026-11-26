"""Reconstruct selected weighted excedance rows and check real-root counts with integers."""
from fractions import Fraction as F
from functools import reduce
from itertools import permutations
from math import comb, factorial, gcd

def add_product(out, a, b, scalar):
    for i, x in enumerate(a):
        if x:
            for j, y in enumerate(b):
                out[i+j] += scalar*x*y

def cycle_rows(n, method):
    if method=='insertion':
        rows=[[1]]
        for j in range(1,n):
            nxt=[0]*j
            for i,c in enumerate(rows[-1]):
                nxt[i]+=(i+1)*c
                if i+1<j: nxt[i+1]+=(j-i-1)*c
            rows.append(nxt)
    else:
        rows=[[1]]+[[sum((-1)**b*comb(j+1,b)*(i+1-b)**j for b in range(i+1))
                     for i in range(j)] for j in range(1,n)]
    return [[],[]]+[[0]+rows[a-1] for a in range(2,n+1)]

def anchored(n, allowed):
    cyc=cycle_rows(n,'insertion')
    rows=[[1]]
    for j in range(1,n+1):
        q=[0]*j
        for a in sorted(allowed):
            if a>j: break
            add_product(q,cyc[a],rows[j-a],comb(j-1,a-1))
        rows.append(q)
    return rows

def by_length(n, allowed):
    cyc=cycle_rows(n,'inclusion')
    rows=[[1]]+[[0]*j for j in range(1,n+1)]
    for a in sorted(allowed):
        old=rows
        rows=[v[:] for v in old]
        power=[1]
        for e in range(1,n//a+1):
            prod=[0]*(len(power)+a-1)
            add_product(prod,power,cyc[a],1)
            power=prod
            multiplicity=factorial(a*e)//(factorial(a)**e*factorial(e))
            for j in range(a*e,n+1):
                add_product(rows[j],old[j-a*e],power,comb(j,a*e)*multiplicity)
    return rows

def brute(n, allowed):
    out=[0]*n
    for sigma in permutations(range(n)):
        seen=set()
        for i in range(n):
            if i in seen: continue
            a,j=0,i
            while j not in seen:
                seen.add(j); a+=1; j=sigma[j]
            if a not in allowed: break
        else:
            out[sum(j<v for j,v in enumerate(sigma))]+=1
    return out

def trim(p):
    while p and not p[-1]:p.pop()
    return p

def primitive(p):
    trim(p)
    if not p:return []
    g=reduce(gcd,p,0)
    return [u//g for u in p]

def sturm(p):
    a=primitive(p[:]);b=primitive([i*x for i,x in enumerate(a)][1:])
    chain=[a,b]
    while len(b)>1:
        rem=a[:]
        while len(rem)>=len(b):
            scale=abs(b[-1])
            c=rem[-1]*(1 if b[-1]>0 else -1)
            shift=len(rem)-len(b)
            rem=[scale*x for x in rem]
            for j,v in enumerate(b):rem[j+shift]-=c*v
            rem=primitive(rem)
        assert rem, 'multiple roots in this witness'
        a,b=b,[-v for v in rem];chain.append(b)
    assert len(b)==1 and b[0]
    def var(signs):
        return sum(a!=b for a,b in zip(signs,signs[1:]))
    at_minus=[(q[-1]*(-1)**(len(q)-1)>0) for q in chain]
    at_plus=[q[-1]>0 for q in chain]
    return var(at_minus)-var(at_plus)

def jets(p,t):
    v=b=c=F(0)
    for a in reversed(p):
        v,b,c=v*t+a,b*t+v,c*t+2*b
    return v,b,c

def lag(p,t):
    a,b,c=jets(p,t)
    return b*b-a*c

def disk(p,a,b,radius=10,den=10**6):
    # Expand den^degree * p((a+bi+z)/den) as a Gaussian integer polynomial.
    c=[(0,0) for _ in p];c[0]=(p[-1],0)
    for step,h in enumerate(reversed(p[:-1]),1):
        for j in range(step,-1,-1):
            x,y=c[j];u,v=c[j-1] if j else (h*den**step,0)
            c[j]=(a*x-b*y+u,b*x+a*y+v)
    head=max(map(abs,c[1]))*radius
    rem=sum((abs(u)+abs(v))*radius**j for j,(u,v) in enumerate(c) if j!=1)
    assert 3*rem<head and b>radius
    return True

def check_size(n,b_weight,x,centers):
    import json
    from pathlib import Path
    cert=json.loads(Path(__file__).with_name(f"dyadic{n}.json").read_text())
    rows={}
    for tag in "AB":
        allowed=set(cert[tag]["allowed"])
        table=anchored(n,allowed)
        assert table==by_length(n,allowed)
        for j in range(2,9):assert table[j]==brute(j,allowed)
        p=table[n]
        assert p==[0]+cert[tag]["quotient"] and p[1]==p[-1]==1
        assert sturm(p[1:])==n-2
        for i,(h,k) in enumerate(cert[tag]["nodes"]):
            assert (-1)**i*sum(c*h**j*2**(k*(n-2-j)) for j,c in enumerate(p[1:]))>0
        print(n,tag,n-2,'simple negative roots; validated dyadic signs and original enumeration through 8')
        rows[tag]=p
    mixed=[a+b_weight*b for a,b in zip(rows["A"],rows["B"])]
    assert sturm(mixed[1:])==n-6 and all(c>0 for c in mixed[1:])
    assert lag(mixed,x)==F(cert["gap"])<0
    assert all(disk(mixed[1:],a,b) for a,b in centers)
    print(n, 'mixture quotient', n-6,'negative simple roots and four nonreal roots')
    print('Full-row gap',cert["gap"],'convex gap',F(cert["gap"])/(1+b_weight)**2)
if __name__=='__main__':
    check_size(34,2,F(-2,15),[(-130951,2544),(-7633538,148281)])
    check_size(44,1,F(-1,2),[(-494231,6159),(-2023030,25210)])
