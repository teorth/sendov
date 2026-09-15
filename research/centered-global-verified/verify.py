"""One-command paper/exact-example and Lean-evidence verification."""
from pathlib import Path
import subprocess,sys,json
ROOT=Path(__file__).resolve().parent

def main():
 for script,flag in [('verify_paper.py','--full-rational'),('verify_lean.py','--rebuild')]:
  cmd=[sys.executable,'-B',str(ROOT/script)]+([flag] if flag in sys.argv else [])
  subprocess.run(cmd,cwd=ROOT,check=True)
 paper=json.loads((ROOT/'PAPER_VERIFICATION.json').read_text());lean=json.loads((ROOT/'LEAN_VERIFICATION.json').read_text())
 assert paper['status']==lean['status']=='PASS'
 result=dict(status='REVIEWED GLOBAL PAPER PROOF; PARTIAL/GENERIC KERNEL EVIDENCE',
  domain='all naturalm>=7,9/10<=a<1,original FULLpolar and pointwise unit disk,actual mean and variance',
  paper_theorem='E_fin+Gamma<=1-a|mu|-(1-a)/20',paper_open_domain=None,
  original_C_counterexample=False,original_C_changed=False,global_half_h_bound_proved=False,
  method='generic analytic criterion with finite continuous-degree-band certificates plus unbounded cutoff; not per-degree original-majorant testing, not certificate-free',
  global_kernel_verified=False,kernel_complete_domains=['lambda<=1/3','actual v<=h/m²'],
  kernel_modules=lean['modules'],kernel_checks=lean['checks'],axiom_queries=lean['audited_queries'],
  outstanding_kernel_inputs=['concrete endpoint Bernstein integral identities and coefficient signs','concrete curved integral/scalar band certificates','unbounded-cutoff formalization and final global assembly'],
  exact_paper_replay=True,historical_full_rational=paper['historical_full_rational'])
 (ROOT/'RESULT.json').write_text(json.dumps(result,indent=2));print(json.dumps(result,indent=2))
if __name__=='__main__':main()
