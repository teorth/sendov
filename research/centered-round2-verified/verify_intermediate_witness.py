"""Exact nonvacuity witness in the new thin-variance intermediate band.
This is a diagnostic example, not a degree table or a quantified proof.
"""
from fractions import Fraction as F
from pathlib import Path
import sys,json
sys.dont_write_bytecode=True
HERE=Path(__file__).resolve().parent
sys.path.insert(0,str(HERE/'support'))
from rational import C,certify
m=100;a=F(19,20);x=F(999999,1000001);y=F(2000,1000001)
assert x*x+y*y==1
mu=F(98,100)+F(2,100)*x;v=1-mu*mu;h=1-a
assert F(1,4)<m*h<100 and 0<v<=h/(m*m)
# On [9/10,1], the conjugate-pair factor is at least a²; all other factors>=103/100.
assert a+(1-a*a)*F(9,10)>=F(103,100)
lower=F(1,10)*a*a*F(103,100)**98
assert lower>1
r=certify(a,[(98,C(1)),(1,C(x,y)),(1,C(x,-y))],'intermediate-thin-strip')
r['domain']='1/4<lambda<100 and 0<v<=h/m²';r['fullpolar_rectangle_lower']=str(lower)
(HERE/'intermediate_witness.json').write_text(json.dumps(r,indent=2))
print('lambda',m*h,'variance',v,'fullpolar lower',float(lower),'E/h',r['E_over_h_display'])
