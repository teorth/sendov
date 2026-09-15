"""Exact, stdlib-only replay of a generic continuous-degree-band criterion.
No degree-wise majorant evaluations or numerical integration are used.
"""
from fractions import Fraction as F
from math import comb, isqrt
from pathlib import Path
import hashlib
import json

# Each row is a continuous scalar degree interval, not one original degree.
BANDS = [(7,8,F(946,1000)), (9,10,F(921,1000)),
         (11,12,F(898,1000)), (13,14,F(877,1000)),
         (15,18,F(842,1000)), (19,22,F(812,1000)),
         (23,28,F(775,1000)), (27,34,F(745,1000))]

def mul2(A,B):
    C={}
    for (i,j),a in A.items():
        for (k,l),b in B.items():
            ij=(i+k,j+l);C[ij]=C.get(ij,0)+a*b
    return {ij:v for ij,v in C.items() if v}

def moment_poly(n,X):
    """Integral Q_(1-h,X,1)(t)^n dt, integer bivariate expansion."""
    p,r=X.numerator,X.denominator
    Q={(0,0):r,(1,0):-2*r,(1,1):4*p,
       (2,0):r,(2,1):-6*p,(2,2):4*r,
       (3,1):2*p,(3,2):-4*r,(4,2):r}
    P={(0,0):1}
    for _ in range(n):P=mul2(P,Q)
    c=[F(0)]*(4*n+1)
    for (i,j),v in P.items():c[i]+=F(v,(j+1)*r**n)
    return c

def bernstein(c,length=F(1,10)):
    n=len(c)-1
    return [sum((c[j]*length**j*F(comb(k,j),comb(n,j))
                 for j in range(k+1)),F(0)) for k in range(n+1)]

def mul1(A,B):
    C=[F(0)]*(len(A)+len(B)-1)
    for i,a in enumerate(A):
        for j,b in enumerate(B):C[i+j]+=a*b
    return C

def integral_quad_power(X,p):
    c=[F(1)]
    for _ in range(p):c=mul1(c,[F(1),-2*X,F(1)])
    return sum((v/F(i+4) for i,v in enumerate(c)),F(0)),c

def moment_at_h(n,X,h):
    """Independent univariate expansion at a fixed rational h."""
    a=1-h;d=1-a*a;c=[F(1)]
    for _ in range(n):c=mul1(c,[a*a,2*a*d*X,d*d])
    return sum((v/F(i+1) for i,v in enumerate(c)),F(0))

def sqrt_upper(q,denom=10**6):
    assert q>=0
    return F(isqrt(q.numerator*denom**2//q.denominator)+1,denom)

def main():
    checks=[];rows=[]
    def check(name,condition):
        if not condition:raise AssertionError(name)
        checks.append(name)
    for L,U,X in BANDS:
        tag=f'[{L},{U}]'
        check(tag+' admissible band',7<=L<=U and L%2==1 and U%2==0)
        check(tag+' admissible X',F(7,10)<X<=F(19,20) and X*X>F(1,2))
        n=U//2;c=moment_poly(n,X)
        check(tag+' moment at h=0',c[0]==1)
        b=bernstein(c[1:])
        check(tag+' moment derivative at 0',c[1]==U*(X-1))
        for k,bk in enumerate(b):check(tag+f' Bernstein negative {k}',bk<0)
        check(tag+' moment endpoint independent replay',1+F(1,10)*b[-1]==moment_at_h(n,X,F(1,10)))
        p=(L-3)//2;I,tailpoly=integral_quad_power(X,p)
        check(tag+' positive curved integral',I>0)
        S=F(9,4)-F(2,U-1)-F(1,2*U*(U-1))
        D=U*(U-1)*(U-2)
        T2=S*(U+1)**2*D*I*I*X*X*(1-X*X)
        tau=sqrt_upper(T2)
        check(tag+' exact positive tail square',0<T2<tau*tau)
        G=1/((L-1)*X*X)
        W=2*(1-X)
        B=U**2*W**((L-1)//2)
        K=tau+G*(1+B)
        excess=max(F(0),K-F(1,2))
        delta=X-F(1,15)-F(U,3)*excess
        check(tag+' margin at least 1/20',delta>=F(1,20))
        rows.append({'L':L,'U':U,'X':str(X),'moment_exponent':n,
          'moment_power_coefficients':[str(q) for q in c],
          'moment_bernstein_coefficients':[str(q) for q in b],
          'moment_bernstein_max':str(max(b)),
          'tail_power_coefficients':[str(q) for q in tailpoly],
          'tail_exponent':p,'tail_integral':str(I),'tail_constant_squared':str(T2),
          'tail_rational_upper':str(tau),'Gamma_constant':str(G),
          'B2_constant':str(B),'total_variance_constant':str(K),
          'margin_h':str(delta)})
        print(json.dumps({'band':[L,U],'X':str(X),'Bernstein_max':float(max(b)),
                          'tau':float(tau),'K':float(K),'margin_h':float(delta)}),flush=True)
    # Only interval coverage is enumerated; no degree-indexed analytic checks.
    expected=set(range(7,35))
    covered={m for L,U,_ in BANDS for m in range(L,U+1)}
    check('all requested integer degrees covered',expected<=covered)
    check('no out-of-range integer degrees used',covered<=expected)
    check('every certificate covers multiple degrees',all(U>L for L,U,_ in BANDS))
    check('eight interval certificates not 28 degree certificates',len(rows)==8)
    here=Path(__file__).resolve().parent
    root=here.parents[2]
    sources=[root/'research/centered-round3/math-polar/PROOF.md',
             root/'research/centered-round3/math-polar/verify.py',
             root/'research/centered-round2-verified/math-middle/PROOF.md',
             root/'research/centered-round2-verified/math-cutoff45/PROOF.md']
    hashes={str(p.relative_to(root)):hashlib.sha256(p.read_bytes()).hexdigest() for p in sources}
    record={'status':'PASS','checks_passed':len(checks),'checks':checks,
            'degree_cover_count':len(covered),'band_count':len(rows),
            'uniform_margin_h':'1/20','bands':rows,'read_only_source_sha256':hashes}
    cache=here/'cache';cache.mkdir(exist_ok=True)
    (cache/'exact-verification.json').write_text(json.dumps(record,indent=2)+'\n')
    print(json.dumps({'status':'PASS','checks_passed':len(checks),
      'bands':len(rows),'degree_cover_count':len(covered),'uniform_margin_h':'1/20'}))

if __name__=='__main__':main()
