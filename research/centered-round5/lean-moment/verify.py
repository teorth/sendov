"""Fail-closed audit of this stage's exact source/object receipts and axiom output."""
from pathlib import Path
import hashlib
import json
import re

HERE = Path(__file__).resolve().parent
MODULES = [
    'Sendov.Analytic.CenteredEndpointMoment',
    'Sendov.Analytic.CenteredBernsteinMoment',
    'Sendov.Analytic.CenteredMomentAudit',
]
ALLOWED = {'propext', 'Classical.choice', 'Quot.sound'}
sha = lambda p: hashlib.sha256(p.read_bytes()).hexdigest()
records = []
for module in MODULES:
    rel = Path(*module.split('.'))
    source = HERE / rel.with_suffix('.lean')
    obj = HERE / '.lake/paper/objects' / rel.with_suffix('.olean')
    assert not source.is_symlink() and not obj.is_symlink()
    assert not re.search(r'\b(sorry|admit|native_decide|axiom)\b', source.read_text())
    for kernel in [False, True]:
        suffix = '-kernel' if kernel else ''
        receipt = json.loads((HERE / 'receipts' / f'{module}{suffix}.json').read_text())
        log = json.loads((HERE / '.lake/paper/logs' / f'moment-{module}{suffix}.json').read_text())
        assert receipt['exit_code'] == log['exit_code'] == 0
        assert receipt['source_sha256'] == sha(source)
        assert receipt['object_sha256'] == sha(obj)
        assert receipt['module'] == log['module'] == module
        assert receipt['kernel'] == log['kernel'] == kernel
        records.append(dict(module=module, kernel=kernel, seconds=log['seconds']))

audit_source = HERE / 'Sendov/Analytic/CenteredMomentAudit.lean'
expected = re.findall(r'^#print axioms (\S+)$', audit_source.read_text(), re.M)
assert len(expected) == len(set(expected))
text = (HERE / '.lake/paper/logs/moment-Sendov.Analytic.CenteredMomentAudit.log').read_text()
pattern = r"'([^']+)' depends on axioms: \[([^\]]*)\]"
found = re.findall(pattern, text)
assert not re.sub(pattern, '', text).strip(), 'Unrecognized audit output'
assert [name for name, _ in found] == expected
axioms = {name: sorted(x.strip() for x in values.split(',')) for name, values in found}
assert all(set(values) <= ALLOWED for values in axioms.values())
report = dict(status='PASS', checks=records, axiom_declarations=len(axioms), axioms=axioms,
              source_hashes={m: sha(HERE / Path(*m.split('.')).with_suffix('.lean')) for m in MODULES},
              note='No concrete endpoint polynomial certificate is instantiated in this stage.')
(HERE / 'receipts/verification.json').write_text(json.dumps(report, indent=2) + '\n')
print(json.dumps(dict(status='PASS', compile_checks=sum(not r['kernel'] for r in records),
                     kernel_checks=sum(r['kernel'] for r in records),
                     axiom_declarations=len(axioms), allowed_axioms=sorted(ALLOWED)), indent=2))
