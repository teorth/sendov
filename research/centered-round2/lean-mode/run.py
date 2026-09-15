"""Serialized private-tree runner: remove every target output before elaboration."""
from pathlib import Path
import subprocess
import sys
HERE = Path(__file__).resolve().parent
ROOT = HERE.parents[2]
module = sys.argv[1]
kernel = '--kernel' in sys.argv[2:]
if not kernel:
    stem = HERE / '.lake/paper/objects' / Path(*module.split('.'))
    for suffix in ('.olean', '.ilean', '.olean.private', '.olean.server'):
        stem.with_suffix(suffix).unlink(missing_ok=True)
cmd = [sys.executable, str(ROOT / 'scripts/check_paper.py'), str(HERE), module,
       '--config', '/home/v-zhouziyu/work/sendov-research-20260914-research/environment/config.json',
       *sys.argv[2:]]
raise SystemExit(subprocess.call(cmd))
