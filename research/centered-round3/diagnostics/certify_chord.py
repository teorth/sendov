"""Exact FULLpolar witness refuting a chord envelope, NOT original C-near."""
from fractions import Fraction as F
from math import comb
from pathlib import Path
import json
from rational_support import C,certify,sqrt_interval
ROOT=Path(__file__).resolve().parent

def main():
 m=44;a=F(9,10);phase=C(F(9999,10001),F(200,10001))
 groups=[(22,phase*C(F(21,29),F(20,29))),(22,phase*C(F(21,29),F(-20,29)))]
 assert all(q.n2()==1 for n,q in groups)
 original=certify(a,groups,'nonreal-fullpolar-chord-obstruction')
 mu=sum((n*q for n,q in groups),C())/m;u=F(21,29);v=1-u*u
 assert mu.n2()==u*u and mu.im!=0
 b=1-2*a*mu.re+a*a;wlo,whi=sqrt_interval(b);dhi=1-wlo
 S=F(9,4)-F(2,m-1)-F(1,2*m*(m-1));D=m*(m-1)*(m-2)
 preflo,prefhi=sqrt_interval(S*D*v**3)
 # beta integral after y=1-d*t; exact rational primitive, no numerical quadrature.
 I=sum(((-1)**j*F(comb(3,j),m-2+j)*(1-wlo**(m-2+j)) for j in range(4)),F())/dhi**4
 assert I>0 and 0<dhi<1
 finite_tail_lo=preflo*(m+1)*a**4*u*I
 budget=1-a*u
 assert finite_tail_lo>budget
 # Retain the actual quadratic instead. beta^(41/2)<=beta^20 on [0,1].
 assert 0<b<1 and mu.re**2<=1
 poly=[F(1)]
 for _ in range(20):
  new=[F(0)]*(len(poly)+2)
  for j,c in enumerate(poly):
   for k,d in enumerate([F(1),-2*a*mu.re,a*a]):new[j+k]+=c*d
  poly=new
 Iupper=sum((c/F(j+4) for j,c in enumerate(poly)),F())
 z=a*mu;end=1-z
 E0upper=sqrt_interval(end.n2()**(m+1))[1]
 B2=sum((comb(m+1,j)*z**j*end**(m+1-j) for j in range(3)),C())
 gamma=v/((m-1)*u*u)
 repaired_upper=E0upper+gamma*(1+sqrt_interval(B2.n2())[1])+prefhi*(m+1)*a**4*u*Iupper
 assert repaired_upper<budget
 output=dict(quadratic_curvature_budget_upper=str(repaired_upper),quadratic_ratio_display=float(repaired_upper/budget),scope='COUNTEREXAMPLE ONLY TO WHOLE-INTERVAL NORM-CHORD TAIL ENVELOPE; original C-near holds',
  original=original,b=str(b),finite_chord_tail_lower=str(finite_tail_lo),budget=str(budget),
  chord_tail_ratio_lower=str(finite_tail_lo/budget),chord_ratio_display=float(finite_tail_lo/budget),
  all_original_constraints_exact=True,original_C_near_certified=True,original_counterexample=False)
 (ROOT/'chord_obstruction.json').write_text(json.dumps(output,indent=2))
 print('FULLpolar norm² margin',original['polar_margin_display'])
 print('original E/h upper',original['E_over_h_display'])
 print('finite norm-chord tail/budget lower',output['chord_ratio_display'])
 print('actual mean',mu.out())
if __name__=='__main__':main()
