"""Direct Lean in the isolated lean-band stage; all external trees are read-only."""
from pathlib import Path
import sys
import subprocess
import json
import hashlib
import os

HERE = Path(__file__).resolve().parent
PROJECT = Path('/home/v-zhouziyu/work/sendov-paper-formalization-20260914-remaining-centered')
FROZEN = PROJECT / 'research/centered-round2-verified'
CONFIG = Path(os.environ.get('CENTERED_CONFIG',
    '/home/v-zhouziyu/work/sendov-research-20260914-research/environment/config.json')).resolve()
module = sys.argv[1]
assert all(x.isidentifier() for x in module.split('.'))
kernel = '--kernel' in sys.argv
rel = Path(*module.split('.'))
source = HERE / rel.with_suffix('.lean')
assert source.is_file() and not source.is_symlink(), 'Only owned source targets may be checked'
source_hash = hashlib.sha256(source.read_bytes()).hexdigest()
base = PROJECT / 'research/centered-round3/integrated/.lake/paper/objects'
stage = HERE / '.lake/paper/objects'
stage.mkdir(parents=True, exist_ok=True)
for f in base.rglob('*'):
    if f.is_file():
        dst = stage / f.relative_to(base)
        dst.parent.mkdir(parents=True, exist_ok=True)
        if not dst.exists() and not dst.is_symlink():
            try:
                dst.symlink_to(f.resolve())
            except FileExistsError:
                pass
folder = stage / rel.parent
folder.mkdir(parents=True, exist_ok=True)
output = stage / rel.with_suffix('.olean')
receipt_dir = HERE / 'receipts'
receipt_dir.mkdir(exist_ok=True)
compile_receipt = receipt_dir / f'{module}.json'
if kernel:
    previous = json.loads(compile_receipt.read_text())
    assert previous['exit_code'] == 0 and previous['source_sha256'] == source_hash
    assert output.is_file() and not output.is_symlink()
    assert previous['object_sha256'] == hashlib.sha256(output.read_bytes()).hexdigest()
else:
    # Unlink both staged symlinks and previous owned artifacts: a failed compile
    # must never leave a stale target available for a later kernel receipt.
    for f in folder.glob(rel.name + '.*'):
        if f.is_file() or f.is_symlink():
            f.unlink()
cmd = [sys.executable, str(PROJECT / 'scripts/check_paper.py'), str(HERE), module,
       '--config', str(CONFIG), '--tag', 'band'] + (['--kernel'] if kernel else [])
r = subprocess.run(cmd, text=True, stdout=subprocess.PIPE, stderr=subprocess.STDOUT)
print(r.stdout)
assert hashlib.sha256(source.read_bytes()).hexdigest() == source_hash, 'Source changed during check'
record = dict(module=module, kernel=kernel, exit_code=r.returncode,
              source_sha256=source_hash,
              object_sha256=hashlib.sha256(output.read_bytes()).hexdigest() if output.exists() else None)
(receipt_dir / f'{module}{"-kernel" if kernel else ""}.json').write_text(json.dumps(record, indent=2))
raise SystemExit(r.returncode)
