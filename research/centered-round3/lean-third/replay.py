"""Rebuild only this owned stage, kernel-check, and verify complete audit coverage."""
from pathlib import Path
import hashlib
import json
import re
import subprocess
import sys

HERE = Path(__file__).resolve().parent
FROZEN = HERE.parent.parent / 'centered-round2-verified'
MODULES = [
    'Sendov.Analytic.CenteredThirdTail',
    'Sendov.Analytic.CenteredThirdScalar',
    'Sendov.Analytic.CenteredThirdActual',
    'Sendov.Analytic.CenteredThirdEndpoint',
    'Sendov.Analytic.CenteredThirdTheorem',
    'tests.CenteredThirdAudit',
]


def sha(path):
    return hashlib.sha256(path.read_bytes()).hexdigest()


def main():
    frozen_manifest = json.loads((FROZEN / 'MANIFEST.json').read_text())
    for rel, expected in frozen_manifest.items():
        assert sha(FROZEN / rel) == expected, f'Frozen input changed: {rel}'
    declarations = []
    for module in MODULES[:-1]:
        source = HERE / Path(*module.split('.')).with_suffix('.lean')
        text = source.read_text()
        assert not re.search(r'\b(sorry|admit|native_decide|axiom)\b', text), source
        declarations.extend('Sendov.CenteredThird.' + name for name in
                            re.findall(r'^(?:lemma|theorem)\s+(\w+)', text, re.M))
    audit = (HERE / 'tests/CenteredThirdAudit.lean').read_text()
    assert set(re.findall(r'^#print axioms (\S+)', audit, re.M)) == set(declarations)
    for module in MODULES:
        for kernel in [False, True]:
            cmd = [sys.executable, str(HERE / 'check.py'), module]
            if kernel:
                cmd.append('--kernel')
            result = subprocess.run(cmd, text=True, stdout=subprocess.PIPE, stderr=subprocess.STDOUT)
            if result.returncode:
                print(result.stdout)
                raise SystemExit(result.returncode)
            print(f'{module}: {"kernel" if kernel else "compile"} PASS', flush=True)
    audit_log = (HERE / '.lake/paper/logs/third-tests.CenteredThirdAudit.log').read_text()
    rows = re.findall(r"'([^']+)' depends on axioms: \[([^]]*)\]", audit_log)
    assert {name for name, _ in rows} == set(declarations)
    allowed = {'propext', 'Classical.choice', 'Quot.sound'}
    for name, values in rows:
        assert set(values.split(', ')) <= allowed, (name, values)
    receipts = {}
    for module in MODULES:
        source = HERE / Path(*module.split('.')).with_suffix('.lean')
        for kernel in [False, True]:
            key = module + ('-kernel' if kernel else '')
            record = json.loads((HERE / 'receipts' / (key + '.json')).read_text())
            assert record['exit_code'] == 0
            assert record['source_sha256'] == sha(source)
            receipts[key] = record
    for rel, expected in frozen_manifest.items():
        assert sha(FROZEN / rel) == expected, f'Frozen input changed after build: {rel}'
    manifest = {str(p.relative_to(HERE)): sha(p)
                for p in sorted(HERE.rglob('*.lean')) if '.lake' not in p.parts}
    manifest.update({p: sha(HERE / p) for p in ['check.py', 'replay.py']})
    output = dict(status='PASS', modules=MODULES, theorem_count=len(declarations),
                  audited_axioms=sorted(allowed), source_hashes=manifest,
                  frozen_manifest_sha256=sha(FROZEN / 'MANIFEST.json'),
                  frozen_manifest_entries_verified=len(frozen_manifest),
                  reviewed_proof_sha256=sha(FROZEN / 'math-middle/PROOF.md'),
                  receipts=receipts)
    (HERE / 'VERIFICATION.json').write_text(json.dumps(output, indent=2) + '\n')
    print(json.dumps({k: v for k, v in output.items() if k not in ['receipts', 'source_hashes']}, indent=2))


if __name__ == '__main__':
    main()
