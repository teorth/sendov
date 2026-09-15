"""Independently replay the local-optimization finalists."""
from high_precision import calc,OUT
from rational import rationalize,certify
import json

def run():
 rows=json.loads((OUT/'optimization_results.json').read_text())
 chosen=[max(rows,key=lambda r:r['result'][key])['result'] for key in ['ratio','stress']]
 chosen += [max((r['result'] for r in rows if r['result']['m']==m),key=lambda r:r['ratio']) for m in [7,8,512]]
 out=[]
 for rec in chosen:
  dps=max(100,int(rec['m']*.4)+70)
  hp=[calc(rec,dps),calc(rec,dps+50)]
  cert=None
  if rec['m']<=24:
   a,g=rationalize(rec);cert=certify(a,g,'optimized-rounded-inward')
  out.append(dict(input=rec,checks=hp,exact=cert))
  (OUT/'finalists_results.json').write_text(json.dumps(out,indent=2))
  print(rec['m'],hp[-1]['ratio'][:30],hp[-1]['gap'][:30],flush=True)
if __name__=='__main__':run()
