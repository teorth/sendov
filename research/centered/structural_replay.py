"""Exact algebra checks for the structural (not per-degree-table) envelope."""
from rational import F,C,certify,sqrt_interval,OUT
from math import factorial
import json

def fall(n,k):
 r=1
 for j in range(k):r*=n-j
 return r

def mul(p,q):
 r=[F(0)]*(len(p)+len(q)-1)
 for i,x in enumerate(p):
  for j,y in enumerate(q):r[i+j]+=x*y
 return r

def run():
 # Telescoped finite CS constant, including its exact finite endpoint correction.
 for K in range(3,9):
  S=F(4,(K-2)*factorial(K-2))+F(2,(K-1)*factorial(K-1))
  for m in range(K,60):
   finite=sum((F(4*k+2,fall(k,K)) for k in range(K,m+1)),F())
   rem=F(4,(K-2)*fall(m-1,K-2))+F(2,(K-1)*fall(m,K-1))
   assert finite==S-rem
 # m=7+t: m^3-6m^2-3m+6 = t^3+15t^2+60t+34.
 p=mul(mul([F(7),F(1)],[F(7),F(1)]),[F(7),F(1)])
 q=mul([F(7),F(1)],[F(7),F(1)])
 for i,x in enumerate(q):p[i]-=6*x
 p[0]-=21;p[1]-=3;p[0]+=6
 assert p==[F(34),F(60),F(15),F(1)]
 # One instance consumes the single structural tail envelope, not a per-k budget table.
 m=13;a=F(9,10);groups=[(6,C(F(15,17),F(8,17))),(6,C(F(15,17),F(-8,17))),(1,C(1))]
 rec=certify(a,groups,'structural-envelope-example')
 mu=sum((n*q for n,q in groups),C())/m;assert mu.im==0
 x=mu.re;v=1-x*x;z=a*x;b=1-z;gamma=v/((m-1)*x*x)
 B2=b**(m+1)+(m+1)*z*b**m+F(m*(m+1),2)*z*z*b**(m-1)
 p=[F(1)]
 for _ in range((m-3)//2):p=mul(p,[F(1),-2*a*x,a*a])
 integral=sum((c/F(j+4) for j,c in enumerate(p)),F())
 assert integral>0
 S=F(9,2)-F(4,m-1)-F(1,m*(m-1))
 tail_sq=S*fall(m,3)*a**8*x*x*v**3*(m+1)**2*integral**2
 tl,tu=sqrt_interval(tail_sq);endpoint=b**(m+1)+gamma*B2
 assert endpoint+tu+gamma<1-a*x
 result=dict(factorial_telescoping=True,quartic_endpoint_polynomial=[str(c) for c in p] if False else ['34','60','15','1'],witness=rec,structural_tail_interval=[str(tl),str(tu)],structural_tail_display=float(tu),endpoint=str(endpoint),gamma=str(gamma),budget=str(1-a*x),envelope_ratio_display=float((endpoint+tu+gamma)/(1-a*x)),structural_budget_certified=True)
 (OUT/'structural_results.json').write_text(json.dumps(result,indent=2));print('structural envelope exact certificate ratio',result['envelope_ratio_display'])
if __name__=='__main__':run()
