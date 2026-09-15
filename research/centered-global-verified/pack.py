"""Deterministic research archive, excluding compiler/dependency caches."""
from pathlib import Path
import os,shutil,json,hashlib,zipfile
ROOT=Path(__file__).resolve().parent

def main():
 (ROOT/'logs').mkdir(exist_ok=True)
 for p in (ROOT/'.lake/paper/logs').glob('global-*'):
  if p.suffix in {'.log','.json'}:shutil.copy2(p,ROOT/'logs'/p.name)
 files=[]
 for directory,dirs,names in os.walk(ROOT):
  dirs[:]=sorted(d for d in dirs if d not in {'.lake','.venv','__pycache__'})
  for name in sorted(names):
   p=Path(directory)/name
   if name in {'MANIFEST.json','pack_receipt.json'} or p.suffix=='.pyc':continue
   assert not p.is_symlink(),p
   files.append(p)
 paths={str(p.relative_to(ROOT)) for p in files}
 modules=json.loads((ROOT/'MODULES.json').read_text())
 assert {str(Path(*m.split('.')).with_suffix('.lean')) for m in modules}=={p for p in paths if p.endswith('.lean')}
 for required in ['REPORT.md','RESULT.md','RESULT.json','LEAN_VERIFICATION.json','PAPER_VERIFICATION.json','historical/centered-verified.zip']:
  assert required in paths,required
 manifest={str(p.relative_to(ROOT)):hashlib.sha256(p.read_bytes()).hexdigest() for p in sorted(files)}
 (ROOT/'MANIFEST.json').write_text(json.dumps(manifest,indent=2));files.append(ROOT/'MANIFEST.json')
 output=ROOT.parent/'centered-global-verified.zip'
 with zipfile.ZipFile(output,'w',compression=zipfile.ZIP_DEFLATED,compresslevel=9) as z:
  for p in sorted(files):
   info=zipfile.ZipInfo('centered-global-verified/'+str(p.relative_to(ROOT)),date_time=(2026,1,1,0,0,0))
   info.compress_type=zipfile.ZIP_DEFLATED;info.external_attr=0o100644<<16
   z.writestr(info,p.read_bytes(),compresslevel=9)
 with zipfile.ZipFile(output) as z:
  assert z.testzip() is None
  assert len(z.namelist())==len(files)==len(set(z.namelist()))
  for name,h in manifest.items():assert hashlib.sha256(z.read('centered-global-verified/'+name)).hexdigest()==h
 receipt=dict(path=str(output),bytes=output.stat().st_size,files=len(files),sha256=hashlib.sha256(output.read_bytes()).hexdigest(),all_members_verified=True)
 (ROOT/'pack_receipt.json').write_text(json.dumps(receipt,indent=2));print(json.dumps(receipt,indent=2))
if __name__=='__main__':main()
