"""Self-contained exact paper/certificate replay; no claim of kernel proof."""
from pathlib import Path
import subprocess,sys,json,tempfile,zipfile
ROOT=Path(__file__).resolve().parent
SCRIPTS=['centered-round2-verified/math-bound/verify.py',
 'centered-round2-verified/math-middle/verify.py',
 'centered-round2-verified/math-cutoff45/verify.py',
 'centered-round3/math-polar/verify.py',
 'centered-round4/math-residual/verify.py','centered-round4/math-residual/audit.py',
 'centered-round4/review35/audit.py','centered-round5/review-global/independent_checks.py',
 'centered-round3/diagnostics/certify_chord.py','centered-round5/boundary-family/verify.py']

def main():
 (ROOT/'logs').mkdir(exist_ok=True);records=[]
 for rel in SCRIPTS:
  src=ROOT/'research'/rel
  p=subprocess.run([sys.executable,'-B',str(src)],cwd=src.parent,text=True,capture_output=True)
  (ROOT/'logs'/('paper-'+rel.replace('/','_')+'.log')).write_text(p.stdout+p.stderr)
  if p.returncode:print(p.stdout,p.stderr);raise SystemExit(p.returncode)
  records.append(dict(script=rel,exit_code=0));print(rel,'PASS',flush=True)
 if '--full-rational' in sys.argv:
  with tempfile.TemporaryDirectory(prefix='centered-historical-replay-') as tmp:
   with zipfile.ZipFile(ROOT/'historical/centered-verified.zip') as z:z.extractall(tmp)
   stage=Path(tmp)/'centered-verified'
   p=subprocess.run([sys.executable,'-B',str(stage/'verify.py'),'--full-rational'],cwd=stage,text=True,capture_output=True)
   (ROOT/'logs/historical-full-rational.log').write_text(p.stdout+p.stderr)
   if p.returncode:print(p.stdout,p.stderr);raise SystemExit(p.returncode)
   receipt=json.loads((stage/'verification_receipt.json').read_text())
   assert receipt['mode']=='full-rational' and receipt['exact_families']==13
   (ROOT/'HISTORICAL_RATIONAL_VERIFICATION.json').write_text(json.dumps(dict(scope='reconstructed historical diagnostics; old global-status field is superseded by RESULT.json',receipt=receipt),indent=2))
   records.append(dict(script='historical/centered-verified.zip:verify.py --full-rational',exit_code=0,exact_families=receipt['exact_families']))
   print('historical13 exact families fully reconstructed PASS',flush=True)
 result=dict(status='PASS',scope='reviewed paper proof and exact arithmetic/certificates; NOT global Lean/kernel verification',global_domain='m>=7,9/10<=a<1,original FULLpolar+pointwise,actual complex mean/variance',global_margin='(1-a)/20',historical_full_rational='--full-rational' in sys.argv,records=records)
 (ROOT/'PAPER_VERIFICATION.json').write_text(json.dumps(result,indent=2));print(json.dumps({k:v for k,v in result.items() if k!='records'},indent=2))
if __name__=='__main__':main()
