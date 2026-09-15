"""Replay saved diagnostics. Quick mode is NOT a fresh radical/integral proof.
--full-rational reconstructs every exact q family and all majorant radicals.
--full-numeric reruns two-precision diagnostics; they remain numerical evidence.
"""
from pathlib import Path
from fractions import Fraction as F
from decimal import Decimal as D
import argparse,json,sys,subprocess,time,hashlib
from rational import C,certify
HERE=Path(__file__).resolve().parent
sys.set_int_max_str_digits(0)
def load(name):return json.loads((HERE/name).read_text())
def main():
 p=argparse.ArgumentParser();p.add_argument('--quick',action='store_true');p.add_argument('--full-rational',action='store_true');p.add_argument('--full-numeric',action='store_true');a=p.parse_args();start=time.monotonic()
 if a.full_numeric:
  for script in ['high_precision.py','finalists.py','large_precision.py']:
   subprocess.run([sys.executable,str(HERE/script)],cwd=HERE,check=True)
 hp=load('high_precision_results.json')+load('finalists_results.json')+load('large_precision_results.json')
 for r in hp:
  assert len(r['checks'])==2
  assert abs(D(r['checks'][0]['E'])-D(r['checks'][1]['E']))<D('1e-40')
  assert D(r['checks'][-1]['polar_method_error'])<D('1e-40')
 certs=load('rational_results.json')+[r['exact'] for r in load('finalists_results.json') if r['exact']]+[load('structural_results.json')['witness']]
 seen=set()
 for i,c in enumerate(certs):
  seen.add(json.dumps([c['a'],c['groups']]))
  assert sum(n for n,x,y in c['groups'])==c['m']
  assert all(F(x)**2+F(y)**2<=1 for n,x,y in c['groups'])
  assert sum(F(z)**2 for z in c['polar'])>1
  assert F(c['E_interval'][1])<=(1-F(c['a']))/2
  assert F(c['E_interval'][1])+F(c['gamma'])<F(c['budget_interval'][0])
  if a.full_rational:
   fresh=certify(F(c['a']),[(n,C(F(x),F(y))) for n,x,y in c['groups']],c['label'])
   for key in ['mu','variance','polar','E_interval','gamma','budget_interval']:assert fresh[key]==c[key],(i,key)
   print('reconstructed exact case',i+1,'m',c['m'],flush=True)
 assert len(seen)==13
 subprocess.run([sys.executable,str(HERE/'structural_replay.py')],cwd=HERE,check=True)
 lean=load('lean_verification.json')
 assert len(lean['checks'])==10 and all(c['exit_code']==0 for c in lean['checks'])
 for rel,h in lean['source_hashes'].items():assert hashlib.sha256((HERE/rel).read_bytes()).hexdigest()==h
 receipt=dict(mode='full-rational' if a.full_rational else 'quick-record-consistency',exact_families=len(seen),two_precision_cases=len(hp),full_numeric_rerun=a.full_numeric,frozen_lean_checks=len(lean['checks']),seconds=time.monotonic()-start,uniform_C_near='OPEN',counterexample='none certified')
 (HERE/'verification_receipt.json').write_text(json.dumps(receipt,indent=2));print(json.dumps(receipt,indent=2))
if __name__=='__main__':main()
