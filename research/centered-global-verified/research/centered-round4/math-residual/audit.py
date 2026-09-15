"""Independent exact replay: trinomial moments and Horner Bernstein basis.
No imports from verify.py, no quadrature, and no degree-wise analytic checks.
"""
from fractions import Fraction as F
from math import comb
from pathlib import Path
import json

PARAMETERS=[(7,8,'473/500',535708), (9,10,'921/1000',444574),
            (11,12,'449/500',377455), (13,14,'877/1000',327153),
            (15,18,'421/500',506719), (19,22,'203/250',361012),
            (23,28,'31/40',407677), (27,34,'149/200',438549)]

def trinomial_moment(n,X):
    # [t^r]Q^n = M_r (1-h)^(2n-r) [h(2-h)]^r.
    c=[F(0)]*(4*n+1)
    for r in range(2*n+1):
        M=sum((F(comb(n,k)*comb(n-k,r-2*k))*(2*X)**(r-2*k)
               for k in range(max(0,r-n),r//2+1)),F(0))
        M/=r+1
        for i in range(2*n-r+1):
            A=comb(2*n-r,i)*(-1)**i
            for j in range(r+1):
                c[r+i+j]+=M*A*comb(r,j)*(-1)**j*2**(r-j)
    return c

def horner_bernstein(c):
    # Here c are coefficients in r=10h, NOT in h.
    b=[c[-1]]
    for constant in reversed(c[:-1]):
        d=len(b)
        b=[constant]+[constant+F(k,d)*b[k-1] for k in range(1,d+1)]
    return b

def trinomial_tail(p,X):
    return sum((F(comb(p,k)*comb(p-k,j))*(-2*X)**j/F(j+2*k+4)
                for k in range(p+1) for j in range(p-k+1)),F(0))

def main():
    here=Path(__file__).resolve().parent
    # Independent calculations below do not use these stored coefficients.
    old=json.loads((here/'cache/exact-verification.json').read_text())
    oldrows={(r['L'],r['U']):r for r in old['bands']}
    checks=[];summaries=[]
    def check(label,condition):
        if not condition:raise AssertionError(label)
        checks.append(label)
    check('record band count',len(oldrows)==len(PARAMETERS))
    for L,U,Xs,t in PARAMETERS:
        X=F(Xs);tau=F(t,10**6);n=U//2;p=(L-3)//2
        label=f'[{L},{U}]'
        c=trinomial_moment(n,X)
        b=horner_bernstein([c[j+1]/10**j for j in range(4*n)])
        check(label+' initial moment',c[0]==1)
        check(label+' initial derivative',c[1]==U*(X-1))
        for k,bk in enumerate(b):check(label+f' independent Bernstein negative {k}',bk<0)
        I=trinomial_tail(p,X)
        S=F(9,4)-F(2,U-1)-F(1,2*U*(U-1))
        T2=S*(U+1)**2*U*(U-1)*(U-2)*I**2*X**2*(1-X**2)
        check(label+' independent tail integral positive',I>0)
        check(label+' independent positive square enclosure',0<T2<tau**2)
        check(label+' X endpoint condition',F(1,2)<X**2 and X<=F(19,20))
        # Independently check the non-monotone-a endpoint issue.
        check(label+' w endpoint a=9/10',F(181,100)-F(9,5)*X<=2*(1-X))
        G=1/((L-1)*X**2)
        B=U**2*(2*(1-X))**((L-1)//2)
        K=tau+G*(1+B)
        delta=X-F(1,15)-F(U,3)*max(F(0),K-F(1,2))
        check(label+' independent final margin',delta>=F(1,20))
        r=oldrows[(L,U)]
        check(label+' independent moment coefficients agree',c==[F(v) for v in r['moment_power_coefficients']])
        check(label+' independent Bernstein coefficients agree',b==[F(v) for v in r['moment_bernstein_coefficients']])
        check(label+' independent tail integral agrees',I==F(r['tail_integral']))
        check(label+' independent tail square agrees',T2==F(r['tail_constant_squared']))
        check(label+' independent tail enclosure agrees',tau==F(r['tail_rational_upper']))
        check(label+' independent margin agrees',delta==F(r['margin_h']))
        summaries.append({'band':[L,U],'X':str(X),'margin_h':str(delta),
                          'moment_sign_count':len(b)})
    covered={m for L,U,_,_ in PARAMETERS for m in range(L,U+1)}
    check('independent integer coverage',covered==set(range(7,35)))
    check('multiple integer degrees in each band',all(L<U for L,U,_,_ in PARAMETERS))
    out={'status':'PASS','checks_passed':len(checks),'checks':checks,
         'band_count':len(PARAMETERS),'degree_cover_count':len(covered),
         'uniform_margin_h':'1/20','bands':summaries}
    (here/'cache/independent-audit.json').write_text(json.dumps(out,indent=2)+'\n')
    print(json.dumps({k:v for k,v in out.items() if k not in ('checks','bands')},indent=2))

if __name__=='__main__':main()
