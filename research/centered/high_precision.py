"""High-precision replay; mp values are evidence, not interval certificates."""
import json, math
from pathlib import Path
import mpmath as mp
OUT=Path(__file__).parent

def calc(rec,dps):
 mp.mp.dps=dps
 a=mp.mpf(str(rec['a']));g=[(n,mp.mpc(str(x),str(y))) for n,x,y in rec['groups']];m=sum(n for n,q in g)
 mu=sum(n*q for n,q in g)/m;u=abs(mu);v=sum(n*abs(q-mu)**2 for n,q in g)/m;z=a*mu;b=1-z
 terms=[mp.binomial(m+1,j)*z**j*b**(m+1-j) for j in range(m+2)]
 B2=sum(terms[:3]);gamma=v/((m-1)*u*u);Hs=[0]*(m+1);S=mp.mpc(0)
 for j in range(m+1,0,-1):S+=terms[j];Hs[j-1]=S
 tail=[]
 for k in range(3,m+1):
  H=1-sum(terms[:k+1]) if k<=m//2 else Hs[k]
  C=mp.sqrt(v**k*(1 if k==m else mp.mpf(m)**m/(mp.mpf(k)**k*mp.mpf(m-k)**(m-k))))
  tail.append(C/mp.binomial(m,k)/u**k*abs(H))
 E=abs(b)**(m+1)+gamma*abs(B2)+sum(tail)
 # Direct quadrature of FULL complex product, and independent finite polynomial integral.
 delta=1-a*a
 f=lambda t:mp.exp(sum(n*mp.log(a+delta*t*q) for n,q in g))
 K=mp.quad(f,[0,mp.mpf('.25'),mp.mpf('.5'),mp.mpf('.75'),1])
 poly=[mp.mpc(1)]
 for n,q in g:
  part=[mp.binomial(n,j)*a**(n-j)*(delta*q)**j for j in range(n+1)]
  new=[mp.mpc(0)]*(len(poly)+n)
  for i,x in enumerate(poly):
   for j,y in enumerate(part):new[i+j]+=x*y
  poly=new
 Kpoly=sum(c/(i+1) for i,c in enumerate(poly))
 return dict(dps=dps,m=m,a=str(a),mu=[str(mu.real),str(mu.imag)],variance=str(v),pointwise_max=str(max(abs(q) for n,q in g)),polar=str(abs(K)),polar_poly=str(abs(Kpoly)),polar_method_error=str(abs(K-Kpoly)),E=str(E),gamma=str(gamma),ratio=str(E/(1-a)),gap=str(E+gamma-(1-a*u)),half_gap=str(E-(1-a)/2),tail_ge4=str(sum(tail[1:])),tail_ge8=str(sum(tail[5:])))
def run():
 data=json.loads((OUT/'search_results.json').read_text());records=data['records'];chosen=[]
 for m in sorted(set(r['m'] for r in records)):
  rr=[r for r in records if r['m']==m]
  for key in ['ratio','gap']:
   chosen.append(max(rr,key=lambda r:r[key]))
  nonreal=[r for r in rr if abs(r['mu'][1])>.05]
  if nonreal:chosen.append(max(nonreal,key=lambda r:r['ratio']))
 chosen.append(data['best']['ratio'])
 seen=set();out=[]
 for r in chosen:
  token=json.dumps(r['groups'])+str(r['a'])
  if token in seen:continue
  seen.add(token)
  dps=max(90,int(r['m']*.4)+70)
  checks=[calc(r,dps),calc(r,dps+50)]
  mp.mp.dps=dps+50
  assert abs(mp.mpf(checks[0]['E'])-mp.mpf(checks[1]['E']))<mp.mpf('1e-45')
  assert mp.mpf(checks[1]['polar_method_error'])<mp.mpf('1e-40')
  out.append(dict(input=r,checks=checks))
  (OUT/'high_precision_results.json').write_text(json.dumps(out,indent=2))
  print(r['m'],r['a'],'ratio',checks[-1]['ratio'][:28],'polar margin',str(mp.mpf(checks[-1]['polar'])-1)[:28],flush=True)
 print('checked',len(out))
if __name__=='__main__':run()
