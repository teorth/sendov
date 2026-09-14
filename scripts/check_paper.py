"""Direct Lean checks with private project objects and baseline package cache."""
import argparse
import json
import os
from pathlib import Path
import subprocess
import time

p = argparse.ArgumentParser()
p.add_argument('tree', type=Path)
p.add_argument('module')
p.add_argument('--config', type=Path, required=True, help='Pinned Lean/cache environment JSON')
p.add_argument('--kernel', action='store_true')
p.add_argument('--tag', default='check')
a = p.parse_args()
a.tree = a.tree.resolve()
assert all(x.isidentifier() for x in a.module.split('.'))
config = json.loads(a.config.read_text())
cache = a.tree / '.lake/paper'
objects = cache / 'objects'
rel = Path(*a.module.split('.'))
setup = dict(config['setup_template'], name=a.module, importArts={})
setup_path = cache / 'setups' / rel.with_suffix('.json')
setup_path.parent.mkdir(parents=True, exist_ok=True)
setup_path.write_text(json.dumps(setup))
env = os.environ.copy()
env.update(config['environment'])
parts = env['LEAN_PATH'].split(os.pathsep)
parts[parts.index(config['project_lib'])] = str(objects)
env['LEAN_PATH'] = os.pathsep.join(parts)
env['LEAN_NUM_THREADS'] = '1'
source = a.tree / rel.with_suffix('.lean')
output = objects / rel.with_suffix('.olean')
output.parent.mkdir(parents=True, exist_ok=True)
cmd = [config['leanchecker'], a.module] if a.kernel else [config['lean'], str(source), '-o', str(output), '-i', str(output.with_suffix('.ilean')), '--setup', str(setup_path)]
logs = cache / 'logs'
logs.mkdir(parents=True, exist_ok=True)
tag = a.tag + '-' + a.module + ('-kernel' if a.kernel else '')
start = time.monotonic()
try:
    result = subprocess.run(cmd, cwd=a.tree, env=env, text=True, stdout=subprocess.PIPE, stderr=subprocess.STDOUT, timeout=600)
    text, code = result.stdout, result.returncode
except subprocess.TimeoutExpired as e:
    text = e.stdout or b''
    if isinstance(text, bytes):
        text = text.decode(errors='replace')
    code = 124
record = dict(command=cmd, exit_code=code, seconds=time.monotonic()-start, module=a.module, kernel=a.kernel, lean_path=env['LEAN_PATH'], options=setup['options'])
(logs / (tag + '.log')).write_text(text)
(logs / (tag + '.json')).write_text(json.dumps(record, indent=2))
print(text, end='')
print(json.dumps(record))
raise SystemExit(code)
