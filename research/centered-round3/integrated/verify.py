"""Parent integration: fresh focused Lean build, kernel checks and axiom coverage."""
from pathlib import Path
import subprocess,sys,json,re,hashlib
ROOT=Path(__file__).resolve().parent
MODULES=['Sendov.Analytic.CenteredThirdTail','Sendov.Analytic.CenteredThirdScalar',
 'Sendov.Analytic.CenteredThirdActual','Sendov.Analytic.CenteredThirdEndpoint',
 'Sendov.Analytic.CenteredThirdTheorem','tests.CenteredThirdAudit',
 'Sendov.Analytic.CenteredMeanBudget','tests.MeanBudgetAudit']

def main():
 receipts=[];declarations=set();audits=set()
 for m in MODULES:
  src=ROOT/Path(*m.split('.')).with_suffix('.lean');text=src.read_text()
  if m.startswith('tests.'):
   audits.update(re.findall(r'^#print axioms (\S+)',text,re.M))
  else:
   ns=re.search(r'^namespace (\S+)',text,re.M).group(1)
   declarations.update(ns+'.'+s for s in re.findall(r'^(?:theorem|lemma)\s+(\w+)',text,re.M))
   assert not re.search(r'\b(sorry|admit|native_decide)\b|^\s*axiom\s',text,re.M)
  for kernel in [False,True]:
   cmd=[sys.executable,str(ROOT/'check.py'),m]+(['--kernel'] if kernel else [])
   p=subprocess.run(cmd,cwd=ROOT,text=True,capture_output=True)
   if p.returncode:print(p.stdout,p.stderr);raise SystemExit(p.returncode)
   suffix='-kernel' if kernel else ''
   r=json.loads((ROOT/'receipts'/f'{m}{suffix}.json').read_text())
   assert r['exit_code']==0 and r['source_sha256']==hashlib.sha256(src.read_bytes()).hexdigest()
   receipts.append(r);print(m,suffix or 'compile','PASS',flush=True)
 assert audits==declarations
 entries=[]
 for m in ['tests.CenteredThirdAudit','tests.MeanBudgetAudit']:
  text=(ROOT/f'.lake/paper/logs/third-{m}.log').read_text()
  rows=re.findall(r"'([^']+)' depends on axioms:\s*\[([^]]*)\]",text)
  for name,ax in rows:assert set(x.strip() for x in ax.split(','))<= {'propext','Classical.choice','Quot.sound'}
  entries+=rows
 assert {name for name,ax in entries}==declarations
 result=dict(status='PASS',modules=len(MODULES),checks=len(receipts),audited_theorems=len(declarations),
  kernel_domain='m>=7,0<a<1,lambda<=1/3, original FULLpolar/pointwise, actual complex mean/variance',
  main='Sendov.CenteredThird.C_near_fullpolar_third',margin='37h/819',uniform_C_near='OPEN',receipts=receipts)
 (ROOT/'VERIFICATION.json').write_text(json.dumps(result,indent=2))
 print(json.dumps({k:v for k,v in result.items() if k!='receipts'},indent=2))
if __name__=='__main__':main()
