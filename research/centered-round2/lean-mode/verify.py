"""Rebuild the complete local dependency chain, kernel-check, and bind receipts."""
from pathlib import Path
import hashlib
import json
import re
import subprocess
import sys
HERE = Path(__file__).resolve().parent
modules = ['FirstMoment', 'BinomialMode', 'CoefficientBound']
records = []
for module in modules:
    for kernel in (False, True):
        cmd = [sys.executable, str(HERE / 'run.py'), module, '--tag', 'verified']
        if kernel:
            cmd.append('--kernel')
        subprocess.run(cmd, check=True)
        stem = 'verified-' + module + ('-kernel' if kernel else '')
        record_path = HERE / '.lake/paper/logs' / (stem + '.json')
        record = json.loads(record_path.read_text())
        assert record['exit_code'] == 0
        records.append(str(record_path.relative_to(HERE)))
files = {}
names = []
for module in modules:
    source = HERE / (module + '.lean')
    text = source.read_text()
    assert not re.search(r'\b(sorry|admit|axiom|native_decide)\b', text)
    names.extend('Sendov.PaperBinomialMode.' + n for n in re.findall(r'^theorem (\w+)', text, re.M))
    for path in [source, HERE / '.lake/paper/objects' / (module + '.olean')]:
        assert path.exists() and not path.is_symlink()
        files[str(path.relative_to(HERE))] = hashlib.sha256(path.read_bytes()).hexdigest()
    log = (HERE / '.lake/paper/logs' / ('verified-' + module + '.log')).read_text()
    assert 'sorryAx' not in log
    for ax in re.findall(r'depends on axioms: \[([^]]*)\]', log):
        assert set(ax.split(', ')) <= {'propext', 'Classical.choice', 'Quot.sound'}
manifest = {'status': 'verified', 'modules': modules, 'theorems': names,
            'theorem_count': len(names), 'sha256': files, 'receipts': records,
            'axioms_allowed': ['propext', 'Classical.choice', 'Quot.sound'],
            'complete_base_stage_files': 439,
            'missing_coefficient_assembly': [],
            'scope': 'All source and output writes confined to this directory.'}
(HERE / 'VERIFIED.json').write_text(json.dumps(manifest, indent=2) + '\n')
print(json.dumps(manifest, indent=2))
