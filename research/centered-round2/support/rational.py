"""Exact rational complex FULLpolar and actual-square-root-majorant diagnostics."""
from dataclasses import dataclass
from fractions import Fraction as F
from math import comb,isqrt
from pathlib import Path
import json,sys
sys.set_int_max_str_digits(0)
OUT=Path(__file__).parent
@dataclass(frozen=True)
class C:
 re:F=F(0);im:F=F(0)
 def __post_init__(self):
  object.__setattr__(self,'re',F(self.re));object.__setattr__(self,'im',F(self.im))
 def __add__(self,z):
  z=cc(z);return C(self.re+z.re,self.im+z.im)
 __radd__=__add__
 def __neg__(self):return C(-self.re,-self.im)
 def __sub__(self,z):return self+-cc(z)
 def __rsub__(self,z):return cc(z)+-self
 def __mul__(self,z):
  z=cc(z);return C(self.re*z.re-self.im*z.im,self.re*z.im+self.im*z.re)
 __rmul__=__mul__
 def __truediv__(self,z):
  z=cc(z);return self*C(z.re,-z.im)*C(1/z.n2())
 def __pow__(self,n):
  r=C(1);b=self
  while n:
   if n%2:r=r*b
   b=b*b;n//=2
  return r
 def n2(self):return self.re**2+self.im**2
 def out(self):return [str(self.re),str(self.im)]
def cc(z):return z if isinstance(z,C) else C(z)
def sqrt_interval(x):
 assert x>=0
 d=10**45;n=isqrt(x.numerator*d*d//x.denominator)
 lo=F(n,d);hi=lo if lo*lo==x else F(n+1,d)
 assert lo*lo<=x<=hi*hi
 return lo,hi
def rationalize(rec):
 groups=[]
 for n,x,y in rec['groups']:
  rad=(x*x+y*y)**.5
  t=F(round(y/(rad+x)*.999*10**12),10**12)
  r=F(1) if abs(rad-1)<1e-10 else F(round((1-(1-rad)*.999)*10**12),10**12)
  q=r*C((1-t*t)/(1+t*t),2*t/(1+t*t));assert q.n2()<=1
  groups.append((n,q))
 return F(str(rec['a'])),groups

def certify(a,groups,label):
 m=sum(n for n,q in groups);mu=sum((n*q for n,q in groups),C())/m
 v=sum((n*(q-mu).n2() for n,q in groups),F())/m;u2=mu.n2();assert u2>0
 assert v+u2==sum((n*q.n2() for n,q in groups),F())/m
 assert all(q.n2()<=1 for n,q in groups)
 poly=[C(1)];delta=1-a*a
 for n,q in groups:
  part=[comb(n,j)*a**(n-j)*delta**j*q**j for j in range(n+1)]
  new=[C()]*(len(poly)+n)
  for i,x in enumerate(poly):
   for j,y in enumerate(part):new[i+j]+=x*y
  poly=new
 K=sum((x/(j+1) for j,x in enumerate(poly)),C());full=K.n2()>=1
 z=a*mu;b=1-z;gamma=v/((m-1)*u2)
 B=C();Hs=[]
 for j in range(m+1):
  B+=comb(m+1,j)*z**j*b**(m+1-j);Hs.append(1-B)
 B2=1-Hs[2]
 el,eu=sqrt_interval(b.n2()**(m+1));l,u=sqrt_interval(B2.n2());el+=gamma*l;eu+=gamma*u
 tails=[]
 for k in range(3,m+1):
  csq=v**k*(1 if k==m else F(m**m,k**k*(m-k)**(m-k)))
  l,u=sqrt_interval(csq*Hs[k].n2()/(comb(m,k)**2*u2**k));el+=l;eu+=u;tails.append((l,u))
 ul,uu=sqrt_interval(u2);bl,bu=1-a*uu,1-a*ul
 assert full, ('FULLpolar rejected',m,a,float(K.n2()-1))
 assert eu<=(1-a)/2
 assert eu+gamma<bl
 rec=dict(label=label,m=m,a=str(a),groups=[[n,*q.out()] for n,q in groups],mu=mu.out(),variance=str(v),polar=K.out(),polar_norm_squared_gt_one=K.n2()>1,polar_margin_display=float(K.n2()-1),E_interval=[str(el),str(eu)],E_display=float(eu),E_over_h_display=float(eu/(1-a)),gamma=str(gamma),budget_interval=[str(bl),str(bu)],half_certified=True,C_near_certified=True,tail_ge4_upper=str(sum((u for l,u in tails[1:]),F())),tail_ge8_upper=str(sum((u for l,u in tails[5:]),F())))
 return rec

def run():
 data=json.loads((OUT/'search_results.json').read_text())['records'];selected=[]
 for m in [7,8,20,100,256]:
  rr=[r for r in data if r['m']==m and r['a']==.9]
  selected.append(max(rr,key=lambda r:r['ratio']))
 # a->1 and multimodal, explicitly nonreal actual means.
 for m in [7,8,100]:
  rr=[r for r in data if r['m']==m and r['a']==.999999 and len(r['groups'])>=3]
  selected.append(max(rr,key=lambda r:abs(r['mu'][1])))
 out=[]
 for i,r in enumerate(selected):
  a,g=rationalize(r);rec=certify(a,g,'boundary-rounded-inward-'+str(i));out.append(rec)
  (OUT/'rational_results.json').write_text(json.dumps(out,indent=2))
  print(rec['m'],rec['a'],'FULLpolar',rec['polar_margin_display'],'E/h',rec['E_over_h_display'],flush=True)
 print('exact certificates',len(out))
if __name__=='__main__':run()
