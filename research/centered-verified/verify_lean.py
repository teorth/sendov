"""Compile the frozen sources using an isolated project-object stage.
Requires the supplied project checkout/cache and pinned Lean config.
"""
from pathlib import Path
import argparse,json,os,shutil,subprocess,sys,hashlib
HERE=Path(__file__).resolve().parent

def main():
 p=argparse.ArgumentParser();p.add_argument('--project',type=Path,default=HERE.parents[1]);p.add_argument('--config',type=Path,default=Path('/home/v-zhouziyu/work/sendov-research-20260914-research/environment/config.json'));a=p.parse_args()
 modules=['Sendov.Analytic.PaperCenteredTail','Sendov.Analytic.PaperCenteredEndpoint','Sendov.Analytic.PaperCenteredVarianceEndpoint','tests.PaperCenteredStructural','tests.PaperCenteredVarianceAudit']
 original=a.project/'.lake/paper/objects';stage=HERE/'.lake/paper/objects';stage.mkdir(parents=True,exist_ok=True)
 for f in original.rglob('*'):
  if f.is_file():
   dst=stage/f.relative_to(original);dst.parent.mkdir(parents=True,exist_ok=True)
   if not dst.exists() and not dst.is_symlink():dst.symlink_to(f.resolve())
 # Never compile through a symlink into another object's cache.
 for module in modules:
  rel=Path(*module.split('.'));folder=stage/rel.parent
  for f in folder.glob(rel.name+'.*'):
   if f.is_symlink():f.unlink()
 results=[]
 for module in modules:
  for kernel in [False,True]:
   cmd=[sys.executable,str(a.project/'scripts/check_paper.py'),str(HERE),module,'--config',str(a.config),'--tag','frozen-final']+(['--kernel'] if kernel else [])
   r=subprocess.run(cmd,text=True,stdout=subprocess.PIPE,stderr=subprocess.STDOUT)
   print(r.stdout,flush=True);results.append(dict(module=module,kernel=kernel,exit_code=r.returncode))
   if r.returncode:raise SystemExit(r.returncode)
 logs=HERE/'lean-logs';logs.mkdir(exist_ok=True)
 for f in (HERE/'.lake/paper/logs').glob('frozen-final-*'):shutil.copy2(f,logs/f.name)
 hashes={str(f.relative_to(HERE)):hashlib.sha256(f.read_bytes()).hexdigest() for f in HERE.rglob('*.lean') if '.lake' not in f.parts}
 (HERE/'lean_verification.json').write_text(json.dumps(dict(checks=results,source_hashes=hashes),indent=2))
 print('frozen checks',len(results))
if __name__=='__main__':main()
