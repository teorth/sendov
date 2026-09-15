#!/usr/bin/env python3
"""Fresh compile, whole-module kernel replay, and closed axiom inventory.
Writes only within this private stage; imported cache objects remain read-only.
"""
import hashlib
import json
from pathlib import Path
import re
import subprocess
import sys

STAGE = Path(__file__).resolve().parent
ROOT = STAGE.parents[2]
CONFIG = Path('/home/v-zhouziyu/work/sendov-research-20260914-research/environment/config.json')
MODULE = 'Sendov.Analytic.PaperFactorialTail'
AUDIT = 'TailAudit'


def run(module, kernel=False):
    rel = Path(*module.split('.'))
    if not kernel:
        obj = STAGE / '.lake/paper/objects' / rel
        for suffix in ('.olean', '.ilean', '.olean.private', '.olean.server'):
            obj.with_suffix(suffix).unlink(missing_ok=True)
    cmd = [sys.executable, str(ROOT / 'scripts/check_paper.py'), str(STAGE), module,
           '--config', str(CONFIG), '--tag', 'final']
    if kernel:
        cmd.append('--kernel')
    subprocess.run(cmd, check=True)


run(MODULE)
run(MODULE, kernel=True)
run(AUDIT)
run(AUDIT, kernel=True)
source = STAGE / 'Sendov/Analytic/PaperFactorialTail.lean'
audit = STAGE / 'TailAudit.lean'
source_text = source.read_text()
names = re.findall(r'^theorem (\w+)', source_text, re.M)
expected = ['Sendov.PaperFactorialTail.' + name for name in names]
queries = re.findall(r'^#print axioms (\S+)', audit.read_text(), re.M)
assert len(expected) == len(set(expected))
assert set(expected) == set(queries) and len(expected) == len(queries)
text = (STAGE / '.lake/paper/logs/final-TailAudit.log').read_text()
records = re.findall(r"'([^']+)' depends on axioms: \[([^]]*)\]", text)
assert len(records) == len(expected)
assert {name for name, axioms in records} == set(expected)
allowed = {'propext', 'Classical.choice', 'Quot.sound'}
axiom_inventory = {}
for name, axioms in records:
    items = {x.strip() for x in axioms.split(',') if x.strip()}
    assert items <= allowed, (name, items)
    axiom_inventory[name] = sorted(items)
assert not re.search(r'\b(sorry|admit|native_decide|axiom)\b', source_text)
paths = [source, audit, STAGE / '.lake/paper/objects/Sendov/Analytic/PaperFactorialTail.olean',
         STAGE / '.lake/paper/objects/TailAudit.olean']
receipt = {
    'status': 'PASS',
    'scope': 'Fresh standalone mathematical module and explicit audit; no root integration',
    'theorem_count': len(expected),
    'axioms': axiom_inventory,
    'sha256': {str(p.relative_to(STAGE)): hashlib.sha256(p.read_bytes()).hexdigest() for p in paths},
    'compile_and_kernel_receipts': [f'.lake/paper/logs/final-{m}{suffix}.json'
                                    for m in (MODULE, AUDIT) for suffix in ('', '-kernel')],
}
(STAGE / 'verification.json').write_text(json.dumps(receipt, indent=2) + '\n')
print(json.dumps(receipt, indent=2))
