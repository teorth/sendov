"""Package and hash-check the frozen round2 deliverable (no build caches)."""
from pathlib import Path
import shutil,json,hashlib,zipfile
HERE=Path(__file__).resolve().parent

def main():
 logs=HERE/'logs';logs.mkdir(exist_ok=True)
 for f in (HERE/'.lake/paper/logs').glob('round2-*'):
  if f.suffix in {'.log','.json'}:shutil.copy2(f,logs/f.name)
 files=[]
 for p in HERE.rglob('*'):
  rel=p.relative_to(HERE)
  if '.lake' in rel.parts or '__pycache__' in rel.parts:continue
  if not p.is_file() or p.name in {'MANIFEST.json','pack_receipt.json'} or p.suffix in {'.pyc','.zip'}:continue
  files.append(p)
 manifest={str(p.relative_to(HERE)):hashlib.sha256(p.read_bytes()).hexdigest() for p in sorted(files)}
 (HERE/'MANIFEST.json').write_text(json.dumps(manifest,indent=2));files.append(HERE/'MANIFEST.json')
 output=HERE.parent/'centered-round2-verified.zip'
 with zipfile.ZipFile(output,'w',compression=zipfile.ZIP_DEFLATED,compresslevel=9) as z:
  for p in sorted(files):z.write(p,'centered-round2-verified/'+str(p.relative_to(HERE)))
 with zipfile.ZipFile(output) as z:
  assert z.testzip() is None
  assert len(z.namelist())==len(set(z.namelist()))==len(files)
  for name,digest in manifest.items():assert hashlib.sha256(z.read('centered-round2-verified/'+name)).hexdigest()==digest
 receipt=dict(path=str(output),files=len(files),bytes=output.stat().st_size,sha256=hashlib.sha256(output.read_bytes()).hexdigest(),all_member_hashes_verified=True)
 (HERE/'pack_receipt.json').write_text(json.dumps(receipt,indent=2));print(json.dumps(receipt,indent=2))
if __name__=='__main__':main()
