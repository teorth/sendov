"""Rebuild, kernel-check, and audit only this owned generic-band stage."""
from pathlib import Path
import hashlib
import json
import re
import subprocess
import sys

HERE = Path(__file__).resolve().parent
MODULES = [f'Sendov.Analytic.CenteredBand{s}' for s in
           ['Scalar', 'Tail', 'Endpoint', 'Theorem', 'Certificate']]
MODULES += ['tests.CenteredBandAudit']
ALLOWED_AXIOMS = {'propext', 'Classical.choice', 'Quot.sound'}


def sha(path):
    return hashlib.sha256(path.read_bytes()).hexdigest()


def main():
    for module in MODULES:
        for kernel in (False, True):
            command = [sys.executable, str(HERE / 'check.py'), module]
            if kernel:
                command.append('--kernel')
            result = subprocess.run(command, cwd=HERE, capture_output=True, text=True)
            if result.returncode:
                print(result.stdout + result.stderr)
                raise SystemExit(result.returncode)
            print(f'{module}: {"kernel" if kernel else "compile"} PASS')

    declarations = set()
    sources = {}
    forbidden = []
    for module in MODULES:
        source = HERE / (module.replace('.', '/') + '.lean')
        assert source.is_file() and not source.is_symlink()
        text = source.read_text()
        declarations.update('Sendov.CenteredBand.' + name for name in
                            re.findall(r'^(?:lemma|theorem)\s+(\w+)', text, re.M))
        forbidden.extend((str(source), token) for token in
                         re.findall(r'\b(?:sorry|admit|native_decide|axiom|unsafe)\b', text))
        sources[str(source.relative_to(HERE))] = sha(source)
    assert not forbidden, forbidden

    log = HERE / '.lake/paper/logs/band-tests.CenteredBandAudit.log'
    axiom_lists = re.findall(r"'([^']+)' depends on axioms: \[([^\]]*)\]", log.read_text())
    observed = {name: set(x.strip() for x in axioms.split(',') if x.strip())
                for name, axioms in axiom_lists}
    assert set(observed) == declarations, (set(observed), declarations)
    assert all(axioms <= ALLOWED_AXIOMS for axioms in observed.values()), observed

    checks = []
    for module in MODULES:
        source = HERE / (module.replace('.', '/') + '.lean')
        obj = HERE / '.lake/paper/objects' / (module.replace('.', '/') + '.olean')
        assert obj.is_file() and not obj.is_symlink()
        for suffix in ('', '-kernel'):
            receipt = json.loads((HERE / 'receipts' / f'{module}{suffix}.json').read_text())
            assert receipt['exit_code'] == 0
            assert receipt['source_sha256'] == sha(source)
            assert receipt['object_sha256'] == sha(obj)
            checks.append(receipt)

    baseline = {}
    for obj in sorted((HERE / '.lake/paper/objects').rglob('*.olean')):
        if obj.is_symlink():
            baseline[str(obj.relative_to(HERE))] = {
                'resolved_target': str(obj.resolve()), 'sha256': sha(obj)}
    record = {
        'status': 'PASS', 'module_count': len(MODULES),
        'declaration_count': len(declarations), 'checks': checks,
        'sources': sources, 'checker_sha256': sha(HERE / 'check.py'),
        'verify_sha256': sha(Path(__file__)), 'forbidden_source_tokens': forbidden,
        'axioms': {name: sorted(values) for name, values in sorted(observed.items())},
        'read_only_baseline_objects': baseline,
    }
    (HERE / 'receipts/audit.json').write_text(json.dumps(record, indent=2) + '\n')
    print(json.dumps({key: record[key] for key in
                      ('status', 'module_count', 'declaration_count', 'forbidden_source_tokens')}))


if __name__ == '__main__':
    main()
