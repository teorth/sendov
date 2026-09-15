"""Verify the parent-integrated round2 source tree and paper arithmetic."""
from pathlib import Path
import argparse,subprocess,sys,json,hashlib,re
HERE=Path(__file__).resolve().parent
MODULES=['Sendov.Analytic.PaperCenteredTail','Sendov.Analytic.PaperCenteredEndpoint','Sendov.Analytic.PaperCenteredVarianceEndpoint',
 'FirstMoment','BinomialMode','CoefficientBound','Sendov.Analytic.PaperFactorialTail',
 'Sendov.Analytic.CenteredNearScalar','Sendov.Analytic.CenteredNearEndpoint','Sendov.Analytic.CenteredNearChord',
 'Sendov.Analytic.CenteredActualTail','Sendov.Analytic.CenteredNearTheorem','Sendov.Analytic.CenteredChordGeneral','tests.CenteredNearAudit',
 'Sendov.Analytic.CenteredQuarterEndpoint','Sendov.Analytic.CenteredQuarterScalar','Sendov.Analytic.CenteredQuarterActual',
 'Sendov.Analytic.CenteredQuarterAudit','Sendov.Analytic.CenteredQuarterTheorem','tests.CenteredQuarterFinalAudit',
 'Sendov.Analytic.CenteredThinVariance','tests.CenteredThinAudit']
def main():
 p=argparse.ArgumentParser();p.add_argument('--rebuild',action='store_true');a=p.parse_args()
 if a.rebuild:
  for m in MODULES:
   for kernel in [False,True]:subprocess.run([sys.executable,str(HERE/'check.py'),m]+(['--kernel'] if kernel else []),cwd=HERE,check=True)
 records=[];hashes={}
 for m in MODULES:
  source=HERE/Path(*m.split('.')).with_suffix('.lean');text=source.read_text();digest=hashlib.sha256(source.read_bytes()).hexdigest();hashes[str(source.relative_to(HERE))]=digest
  assert not re.search(r'\b(sorry|admit|native_decide)\b',text)
  assert not re.search(r'^\s*(axiom|unsafe)\s',text,re.M)
  for kernel in [False,True]:
   rec=json.loads((HERE/'receipts'/f'{m}{"-kernel" if kernel else ""}.json').read_text());assert rec['exit_code']==0 and rec['source_sha256']==digest;records.append(rec)
 audits=[]
 for name,count in [('tests.CenteredNearAudit',12),('Sendov.Analytic.CenteredQuarterAudit',14),('tests.CenteredQuarterFinalAudit',5),('tests.CenteredThinAudit',5)]:
  log=HERE/f'.lake/paper/logs/round2-{name}.log'
  if not log.exists():log=HERE/f'logs/round2-{name}.log'
  audit=log.read_text()
  assert audit.count('depends on axioms:')==count
  for fragment in re.findall(r'depends on axioms:\s*\[([^]]*)\]',audit):
   assert set(x.strip() for x in fragment.split(','))<= {'propext','Classical.choice','Quot.sound'}
  audits.append(count)
 checks=subprocess.run([sys.executable,str(HERE/'math-bound/verify.py')],cwd=HERE,text=True,capture_output=True,check=True)
 (HERE/'paper_verification.log').write_text(checks.stdout+checks.stderr)
 assert 'ALL 53 EXACT CHECKS PASSED' in checks.stdout
 witness=subprocess.run([sys.executable,'-B',str(HERE/'verify_intermediate_witness.py')],cwd=HERE,text=True,capture_output=True,check=True)
 (HERE/'witness_verification.log').write_text(witness.stdout+witness.stderr)
 middle=subprocess.run([sys.executable,str(HERE/'math-middle/verify.py')],cwd=HERE,text=True,capture_output=True,check=True)
 (HERE/'middle_verification.log').write_text(middle.stdout+middle.stderr)
 assert 'ALL 48 EXACT RATIONAL CHECKS PASSED' in middle.stdout
 cutoff=subprocess.run([sys.executable,str(HERE/'math-cutoff45/verify.py')],cwd=HERE,text=True,capture_output=True,check=True)
 (HERE/'cutoff_verification.log').write_text(cutoff.stdout+cutoff.stderr)
 assert 'ALL 62 EXACT RATIONAL/ALGEBRA CHECKS PASSED' in cutoff.stdout
 result=dict(uniform_C_near='OPEN',kernel_domains=['m>=7,0<a<1,lambda<=1/4, all actual variances','m>=7,9/10<=a<1,actual v<=h/m², all lambda'],kernel_budget=['E_fin+Gamma<=1-a|mu|-79h/504','E_fin+Gamma<=1-a|mu|-19h/840'],kernel_main=['Sendov.CenteredQuarterTheorem.C_near_fullpolar_quarter','Sendov.CenteredThinVariance.C_near_fullpolar_strip'],kernel_origin_consumer='Sendov.CenteredQuarterTheorem.norm_J_gt_one_fullpolar_quarter',checks=len(records),axiom_audits=sum(audits),source_sha256=hashes,paper_domains=['lambda<=1/3, all actual variances','m>=45, all lambda/actual variances'],paper_exact_checks={'first':53,'middle':48,'cutoff45':62},open_domain='7<=m<=44,1/3<lambda<=m/10,v>h/m² (paper coverage); cutoff45 and lambda<=1/3 not yet kernel checked',certified_counterexample=False,record_checks=records)
 (HERE/'RESULT.json').write_text(json.dumps(result,indent=2));print(json.dumps({k:v for k,v in result.items() if k not in ['source_sha256','record_checks']},indent=2))
if __name__=='__main__':main()
