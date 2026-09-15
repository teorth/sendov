"""Audit stored exact/numerical evidence and actual Lean receipts.
This fast audit does not rerun polynomial integration. For full rational replay:
python3 rational.py; <mpmath-python> verify_optimization.py.
"""
from pathlib import Path
from fractions import Fraction as F
from decimal import Decimal
import json,hashlib,sys
sys.set_int_max_str_digits(0)
OUT=Path(__file__).parent;TREE=OUT.parent.parent

def read(name):return json.loads((OUT/name).read_text())
def run():
 search=read('search_results.json');opt=read('optimization_results.json');scalar=read('scalar_results.json');env=read('envelope_results.json')
 assert len(search['records'])==search['feasible']==2400
 assert len(opt['records'])==27
 assert len(scalar['records'])==7777
 assert len(env['records'])==6060
 rats=read('rational_results.json')+read('optimized_rational_results.json');assert len(rats)==10
 for r in rats:
  m=r['m'];a=F(r['a']);assert m>=7 and F(9,10)<=a<1
  assert sum(g[0] for g in r['groups'])==m
  assert all(F(x)**2+F(y)**2<=1 for n,x,y in r['groups'])
  mr=sum(n*F(x) for n,x,y in r['groups'])/m;mi=sum(n*F(y) for n,x,y in r['groups'])/m
  assert [mr,mi]==list(map(F,r['mu']))
  v=sum(n*((F(x)-mr)**2+(F(y)-mi)**2) for n,x,y in r['groups'])/m
  assert v==F(r['variance'])
  kr,ki=map(F,r['polar']);assert kr*kr+ki*ki>1
  el,eu=map(F,r['E_interval']);bl,bu=map(F,r['budget_interval']);assert 0<=el<=eu
  assert eu<=(1-a)/2 and eu+F(r['gamma'])<bl
 hp=read('high_precision_results.json');ohp=read('optimization_precision_results.json');large=read('large_precision_results.json')
 assert len(hp)==23 and len(ohp)==9 and len(large)==2
 for r in hp+ohp+large:
  c=r['checks'];assert len(c)==2
  assert abs(Decimal(c[0]['E'])-Decimal(c[1]['E']))<Decimal('1e-45')
  assert Decimal(c[-1]['gap'])<0 and Decimal(c[-1]['half_gap'])<0
 hp_rejected=sum(Decimal(r['checks'][-1]['polar'])<1 for r in hp)
 receipts={}
 for module,tag in [('Sendov.Analytic.PaperCenteredTail','centered-tail-02'),('Sendov.Analytic.PaperCenteredEndpoint','centered-endpoint-final'),('Sendov.Analytic.PaperCenteredVarianceEndpoint','centered-variance-final')]:
  log=TREE/'.lake/paper/logs'/f'{tag}-{module}-kernel.json';d=json.loads(log.read_text());assert d['exit_code']==0 and d['kernel'];receipts[module]=str(log.relative_to(TREE))
  source=TREE/Path(*module.split('.')).with_suffix('.lean');olean=TREE/'.lake/paper/objects'/Path(*module.split('.')).with_suffix('.olean');assert olean.stat().st_mtime>=source.stat().st_mtime
  assert all(token not in source.read_text() for token in ['sorry','admit','axiom '])
 audit=TREE/'.lake/paper/logs/centered-audit-final-tests.PaperCenteredVarianceAudit.log'
 text=audit.read_text();assert text.count('depends on axioms:')==10
 assert 'sorryAx' not in text and 'Lean.ofReduceBool' not in text
 sources=[OUT/f'{x}.py' for x in ['search','large_precision','scalar_scan','instability','envelope','high_precision','optimize','verify_optimization','rational','verify']]+[TREE/'Sendov/Analytic'/f'{x}.lean' for x in ['PaperCenteredTail','PaperCenteredEndpoint','PaperCenteredVarianceEndpoint']]
 result=dict(status='OPEN_positive_variance_C_near',certified_counterexample=False,proved_domains=['zeroth_endpoint_h_over_2: m>=7, 0<a<1, raw_polar, norm_mu<=1','entire_C_near_when_actual_variance_zero'],kernel_checked_modules=receipts,axiom_audit_count=10,search_cases=len(search['records']),optimization_evaluations=opt['evaluations'],optimizer_outputs=len(opt['records']),scalar_raw_only_cases=len(scalar['records']),structural_envelope_raw_only_cases=len(env['records']),high_precision_case_count=len(hp)+len(ohp)+len(large),high_precision_rejected_fullpolar_boundary_cases=hp_rejected,exact_rational_case_count=len(rats),largest_certified_E_over_h=max(r['E_over_h_display'] for r in rats),largest_hp_E_over_h=str(max(Decimal(r['checks'][-1]['ratio']) for r in hp+ohp+large)),largest_scalar_raw_only_E_over_h=scalar['best']['ratio'],largest_structural_C_budget_ratio=max(r['ratio'] for r in env['records']),largest_refined_structural_half_ratio=max(r['refined_half_ratio'] for r in env['records']),source_sha256={str(p.relative_to(TREE)):hashlib.sha256(p.read_bytes()).hexdigest() for p in sources})
 (OUT/'RESULT.json').write_text(json.dumps(result,indent=2));print(json.dumps(result,indent=2))
if __name__=='__main__':run()
