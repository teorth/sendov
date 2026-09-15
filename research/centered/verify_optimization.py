"""Replay optimizer finalists at two precisions and certify rounded witnesses."""
from high_precision import calc,OUT
from rational import rationalize,certify
import json,mpmath as mp

def run():
 data=json.loads((OUT/'optimization_results.json').read_text())['records'];selected=[]
 for m in [7,8,24,512]:
  selected.extend(r['best'] for r in data if r['best']['m']==m and r['objective'] in ['ratio','slack_ratio'])
 selected.append(max((r['best'] for r in data),key=lambda r:r['slack_ratio']))
 seen=set();out=[]
 for r in selected:
  token=json.dumps(r['groups'])+str(r['a'])
  if token in seen:continue
  seen.add(token)
  checks=[calc(r,dps) for dps in [max(100,int(.4*r['m'])+70),max(150,int(.4*r['m'])+120)]]
  mp.mp.dps=350
  assert abs(mp.mpf(checks[0]['E'])-mp.mpf(checks[1]['E']))<mp.mpf('1e-45')
  assert mp.mpf(checks[1]['polar'])>=1
  assert mp.mpf(checks[1]['gap'])<0
  out.append(dict(input=r,checks=checks));(OUT/'optimization_precision_results.json').write_text(json.dumps(out,indent=2))
  print(r['m'],'polar',checks[-1]['polar'][:24],'E/h',checks[-1]['ratio'][:24],flush=True)
 exact=[]
 for objective in ['ratio','slack_ratio']:
  r=max((r['best'] for r in data),key=lambda r:r[objective]);a,g=rationalize(r)
  exact.append(certify(a,g,'optimizer-'+objective));print('rational',objective,exact[-1]['E_over_h_display'],flush=True)
 (OUT/'optimized_rational_results.json').write_text(json.dumps(exact,indent=2))
 print('precision cases',len(out),'rational',len(exact))
if __name__=='__main__':run()
