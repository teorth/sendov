"""Direct Lean in the parent-owned round2 stage; sibling stages are untouched."""
from pathlib import Path
import sys,subprocess,json,hashlib,os
HERE=Path(__file__).resolve().parent
PROJECT=Path(os.environ.get('CENTERED_PROJECT',str(HERE.parents[1]))).resolve()
CONFIG=Path(os.environ.get('CENTERED_CONFIG','/home/v-zhouziyu/work/sendov-research-20260914-research/environment/config.json')).resolve()
module=sys.argv[1];kernel='--kernel' in sys.argv
base=PROJECT/'.lake/paper/objects';stage=HERE/'.lake/paper/objects';stage.mkdir(parents=True,exist_ok=True)
for f in base.rglob('*'):
 if f.is_file():
  dst=stage/f.relative_to(base);dst.parent.mkdir(parents=True,exist_ok=True)
  if not dst.exists() and not dst.is_symlink():dst.symlink_to(f.resolve())
rel=Path(*module.split('.'));folder=stage/rel.parent;folder.mkdir(parents=True,exist_ok=True)
for f in folder.glob(rel.name+'.*'):
 if f.is_symlink():f.unlink()
cmd=[sys.executable,str(PROJECT/'scripts/check_paper.py'),str(HERE),module,'--config',str(CONFIG),'--tag','round2']+(['--kernel'] if kernel else [])
r=subprocess.run(cmd,text=True,stdout=subprocess.PIPE,stderr=subprocess.STDOUT);print(r.stdout)
source=HERE/rel.with_suffix('.lean')
record=dict(module=module,kernel=kernel,exit_code=r.returncode,source_sha256=hashlib.sha256(source.read_bytes()).hexdigest())
(HERE/'receipts').mkdir(exist_ok=True)
(HERE/'receipts'/f'{module}{"-kernel" if kernel else ""}.json').write_text(json.dumps(record,indent=2))
raise SystemExit(r.returncode)
