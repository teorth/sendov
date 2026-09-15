"""High-precision large-degree, nonreal-mean FULLpolar diagnostics."""
from high_precision import calc,OUT
import json,mpmath as mp

def run():
 records=[dict(a='.9',groups=[[1100,'.6','.8'],[948,'.6','-.8']]),
          dict(a='.999999999999',groups=[[513,'0.9999999999','0.00001'],[1535,'0.9999999999','-0.00001']])]
 out=[]
 for rec in records:
  rec['m']=sum(n for n,x,y in rec['groups'])
  checks=[calc(rec,dps) for dps in [240,320]]
  mp.mp.dps=320
  assert abs(mp.mpf(checks[0]['E'])-mp.mpf(checks[1]['E']))<mp.mpf('1e-100')
  assert mp.mpf(checks[1]['pointwise_max'])<=1
  assert mp.mpf(checks[1]['polar'])>=1
  assert mp.mpf(checks[1]['polar_method_error'])<mp.mpf('1e-100')
  assert mp.mpf(checks[1]['half_gap'])<0
  out.append(dict(input=rec,checks=checks));(OUT/'large_precision_results.json').write_text(json.dumps(out,indent=2))
  print(rec['m'],rec['a'],'E/h',checks[-1]['ratio'][:40],'polar',checks[-1]['polar'][:40],flush=True)
 print('large checks',len(out))
if __name__=='__main__':run()
