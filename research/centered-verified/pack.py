"""Package the frozen deliverable, excluding caches and obsolete logs."""
from pathlib import Path
import json,hashlib,zipfile
HERE=Path(__file__).resolve().parent
ROOTLOGS={'verify_lean.log','full_rational_replay.log','high_precision.log','rational.log','large_precision.log','finalists.log','search.log','scalar_scan.log','optimization.log'}
def main():
 files=[]
 for p in HERE.rglob('*'):
  rel=p.relative_to(HERE)
  if not p.is_file() or '.lake' in rel.parts or '__pycache__' in rel.parts:continue
  if p.name in {'MANIFEST.json','pack_receipt.json'} or p.suffix=='.zip':continue
  if rel.parts[0]=='lean-logs' and not p.name.startswith('frozen-final-'):continue
  if p.suffix=='.log' and len(rel.parts)==1 and p.name not in ROOTLOGS:continue
  files.append(p)
 manifest={str(p.relative_to(HERE)):hashlib.sha256(p.read_bytes()).hexdigest() for p in sorted(files)}
 (HERE/'MANIFEST.json').write_text(json.dumps(manifest,indent=2));files.append(HERE/'MANIFEST.json')
 output=HERE.parent/'centered-verified.zip'
 with zipfile.ZipFile(output,'w',compression=zipfile.ZIP_DEFLATED,compresslevel=9) as z:
  for p in sorted(files):z.write(p,'centered-verified/'+str(p.relative_to(HERE)))
 with zipfile.ZipFile(output) as z:
  assert z.testzip() is None
  assert len(z.namelist())==len(set(z.namelist()))==len(files)
  for rel,h in manifest.items():assert hashlib.sha256(z.read('centered-verified/'+rel)).hexdigest()==h
 receipt=dict(path=str(output),files=len(files),bytes=output.stat().st_size,sha256=hashlib.sha256(output.read_bytes()).hexdigest(),all_member_hashes_verified=True)
 (HERE/'pack_receipt.json').write_text(json.dumps(receipt,indent=2));print(json.dumps(receipt,indent=2))
if __name__=='__main__':main()
