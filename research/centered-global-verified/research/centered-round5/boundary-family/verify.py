"""Exact boundary-family diagnostics; generic feasibility is proved in NOTE.md.
No original C-near counterexample and no global-max claim from these samples.
"""
from pathlib import Path
from fractions import Fraction as F
from math import comb
import json,sys
ROOT=Path(__file__).resolve().parent
sys.path.insert(0,str(ROOT.parents[1]/'centered-round3/diagnostics'))
from rational_support import C,certify

def mul(p,q):
 out=[F(0)]*(len(p)+len(q)-1)
 for i,a in enumerate(p):
  for j,b in enumerate(q):out[i+j]+=a*b
 return out

def power(p,n):
 out=[F(1)]
 for i in range(n):out=mul(out,p)
 return out

def main():
 # Reconstruct the EXACT complex polar integral with all seven q=1.
 K=[F(0)]*15
 for j in range(8):
  p=mul(power([F(1),F(-1)],7-j),power([F(0),F(2),F(-1)],j))
  for i,c in enumerate(p):K[i]+=F(comb(7,j),j+1)*c
 assert K[:2]==[1,0]
 P=K[2:]
 lower=P[0]+sum((c/F(10)**j for j,c in enumerate(P) if j and c<0),F())
 assert lower>F(27,10)
 assert F(11,10)**6/2<1
 margin=F(27,10)-F(4,1000)
 assert margin>0
 # Polynomial identity for the actual variance, w=h^4.
 left=[F(49),F(98),F(49)]
 num=mul([F(7),F(5)],[F(7),F(5)]);num[1]+=4
 assert [a-b for a,b in zip(left,num)]==[F(0),F(24),F(24)]
 records=[]
 for N in [10,30,300,1000000]:
  h=F(1,N);a=1-h;q=C((1-h**4)/(1+h**4),2*h*h/(1+h**4))
  rec=certify(a,[(6,C(1)),(1,q)],f'positive-variance-nonreal-h=1/{N}')
  v=F(rec['variance']);assert v==24*h**4/(49*(1+h**4)) and v>0
  assert F(rec['mu'][1])>0
  real_polar=F(rec['polar'][0]);assert real_polar>=1+margin*h*h
  records.append(rec)
 result=dict(scope='Explicit FULLpolar/pointwise feasible positive-variance nonreal family; global supremum0 requires the global C-near theorem',
  m=7,generic_q='six copies1; q7=(1-h^4+2ih²)/(1+h^4)',generic_h='0<h<=1/10',
  generic_variance='24h^4/[49(1+h^4)]',generic_fullpolar_real_lower='1+(337/125)h²',
  baseline_polar_coefficients=list(map(str,K)),baseline_P_lower=str(lower),samples=len(records),records=records)
 (ROOT/'RESULT.json').write_text(json.dumps(result,indent=2))
 print('generic polynomial checks PASS; exact sample certificates',len(records),'positive variance/nonreal/FULLpolar all PASS')
 print('FULLpolar real margin constant',margin)
if __name__=='__main__':main()
