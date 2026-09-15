"""Verify the frozen Lean bundle; --rebuild freshly compiles and kernel-checks all modules."""
from pathlib import Path
import hashlib,json,re,subprocess,sys
ROOT=Path(__file__).resolve().parent

def main():
 modules=json.loads((ROOT/'MODULES.json').read_text());records=[];queries=set();seen={}
 for m in modules:
  src=ROOT/Path(*m.split('.')).with_suffix('.lean');text=src.read_text();digest=hashlib.sha256(src.read_bytes()).hexdigest()
  assert not re.search(r'\b(sorry|admit|native_decide)\b|^\s*axiom\s',text,re.M),src
  for query in re.findall(r'^#print axioms (\S+)',text,re.M):
   if '.' not in query:
    namespaces=re.findall(r'^namespace (\S+)',text,re.M)
    assert len(namespaces)==1,('ambiguous unqualified audit query',src,query)
    query=namespaces[0]+'.'+query
   queries.add(query)
  for kernel in [False,True]:
   suffix='-kernel' if kernel else ''
   if '--rebuild' in sys.argv:
    p=subprocess.run([sys.executable,str(ROOT/'check.py'),m]+(['--kernel'] if kernel else []),cwd=ROOT,text=True,capture_output=True)
    if p.returncode:print(p.stdout,p.stderr);raise SystemExit(p.returncode)
    print(m,suffix or 'compile','PASS',flush=True)
   rec=json.loads((ROOT/'receipts'/f'{m}{suffix}.json').read_text())
   assert rec['exit_code']==0 and rec['source_sha256']==digest
   records.append(rec)
  log=ROOT/f'.lake/paper/logs/global-{m}.log'
  if not log.exists():log=ROOT/f'logs/global-{m}.log'
  data=log.read_text()
  for name,ax in re.findall(r"'([^']+)' depends on axioms:\s*\[([^]]*)\]",data):
   values={x.strip() for x in ax.split(',') if x.strip()};assert values<={'propext','Classical.choice','Quot.sound'},(name,values)
   seen[name]=sorted(values)
  for name in re.findall(r"'([^']+)' does not depend on any axioms",data):seen[name]=[]
 assert queries<=set(seen),(queries-set(seen))
 result=dict(status='PASS',scope='compiled structural and partial-domain Lean bundle, NOT global kernel closure',modules=len(modules),checks=len(records),audited_queries=len(queries),axioms=seen,receipts=records)
 (ROOT/'LEAN_VERIFICATION.json').write_text(json.dumps(result,indent=2))
 print(json.dumps({k:v for k,v in result.items() if k not in ['axioms','receipts']},indent=2))
if __name__=='__main__':main()
