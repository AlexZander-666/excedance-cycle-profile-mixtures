"""Exact one-cycle marginals, independent local weights, and common-profile comparison."""
from fractions import Fraction
from json import loads, dumps
from math import comb
from pathlib import Path
from original_rows import add_product, anchored, by_length, cycle_rows, sturm, jets

HERE = Path(__file__).resolve().parent


def scaled_row(n, z, A, B):
    # z^j times the independent probability at length j is integral.
    weights = {j: z**(j-1)*(int(j in A)+(z-1)*int(j in B)) for j in range(2,n+1)}
    cycles = cycle_rows(n,'insertion')
    rows = [[1]]
    for m in range(1,n+1):
        p = [0]*m
        for j in range(2,m+1):
            if weights[j]:
                add_product(p,cycles[j],rows[m-j],comb(m-1,j-1)*weights[j])
        rows.append(p)
    return rows[n]


def dyadic_sign(p,h,k):
    # Homogenized Horner at h / 2^k.
    denom = 1
    value = 0
    for c in reversed(p):
        value = value*h+c*denom
        denom <<= k
    return (value>0)-(value<0)


def mesh(p):
    simple = sorted({-Fraction(a,32) * Fraction(2)**e for e in range(-54,55)
                     for a in range(32,64)})
    blocks = []
    for t in simple:
        h = t.numerator
        k = t.denominator.bit_length()-1
        sign = dyadic_sign(p,h,k)
        if not sign:
            continue
        if not blocks or blocks[-1][0] != sign:
            blocks.append((sign,[]))
        blocks[-1][1].append((h,k))
    assert len(blocks)==len(p)
    out = [min(nodes,key=lambda node:(node[1],abs(node[0]).bit_length(),abs(node[0])))
           for _,nodes in blocks]
    assert all(dyadic_sign(p,*t)==(-1)**(len(p)-1+i) for i,t in enumerate(out))
    return out


def laguerre(z):
    value,first,second = z
    return first**2-value*second


def case(n,z,x):
    data=loads((HERE/f'dyadic{n}.json').read_text())
    A,B = [set(data[tag]['allowed']) for tag in ('A','B')]
    p=scaled_row(n,z,A,B)
    assert p[0]==0 and p[1]==p[-1]==z**n and p[1:]==p[:0:-1]
    assert sturm(p[1:])==n-2
    global_row=[0]+[a+(z-1)*b for a,b in zip(data['A']['quotient'],data['B']['quotient'])]
    assert laguerre(jets(global_row,x))==Fraction(data['gap'])<0
    assert sturm(global_row[1:])==n-6
    nodes=mesh(p[1:])
    return {'n':n,'z':z,'scaled_quotient':p[1:],'nodes':nodes,'global_gap':data['gap']}


if __name__=='__main__':
    for n,z,x in [(34,3,Fraction(-2,15)),(44,2,Fraction(-1,2))]:
        proof=case(n,z,x)
        (HERE/f'local{n}.json').write_text(dumps(proof,indent=2)+'\n')
        print(n, len(proof['nodes'])-1,'simple negative local roots; four nonreal global roots')

    allowed={2,3,5,6,8,9,12,15,18,21,24,27,39,40}
    table=anchored(40,allowed)
    assert table==by_length(40,allowed)
    assert sturm(table[39][1:])==37 and sturm(table[40][1:])==34
    assert laguerre(jets(table[40],Fraction(-2,15)))<0
    (HERE/'lower39.json').write_text(dumps({'quotient':table[39][1:],'nodes':mesh(table[39][1:])},indent=2)+'\n')
    print('39 to 40: 37 simple negative quotient roots in the lower row; 34 real quotient roots in the upper row')

    for n,m,x,expected in [(34,2,Fraction(-2,15),-9814),(44,1,Fraction(-1,2),-1650),
                           (40,0,Fraction(-2,15),-1993)]:
        if m==0:
            f=table[40]
        else:
            cert=loads((HERE/f'dyadic{n}.json').read_text())
            ends=[cert[tag]['quotient'] for tag in ('A','B')]
            f=[0]+[u+m*v for u,v in zip(*ends)]
            local=loads((HERE/f'local{n}.json').read_text())['scaled_quotient']
            if n==34:
                fixed=[2**35,2**25,2**18,2**13,2**10,200,75,35,19,11]
                pairs=[(6,4),(8,6),(7,5)]
                suffix=[3,Fraction(5,2),Fraction(7,4),Fraction(5,4),1]
            else:
                fixed=[2**45,2**41,2**24,2**17,2**13,2**10,400,155,75,40,24,16,10,7,5,4,3]
                pairs=[(Fraction(5,2),Fraction(17,8)),(Fraction(9,4),Fraction(15,8)),(Fraction(5,2),2)]
                suffix=[Fraction(3,2),Fraction(5,4),1]
            for q,pair in zip([*ends,local],pairs):
                magnitudes=fixed+list(pair)+suffix
                assert len(magnitudes)==n//2 and all(a>b for a,b in zip(magnitudes,magnitudes[1:]))
                assert q==q[::-1] and q[0]>0
                for i,v in enumerate(magnitudes):
                    v=Fraction(v)
                    assert dyadic_sign(q,-v.numerator,v.denominator.bit_length()-1)==(-1)**i
        j=jets(f,x);delta=laguerre(j)/j[0]**2
        assert expected<delta<expected+1
        print(n,'normalized Laguerre difference in', (expected,expected+1))
