"""Serial exact-source replay in the private tree; no Lake build or cache writes."""
import argparse
import hashlib
import json
from pathlib import Path
import subprocess
import sys

TREE = Path(__file__).resolve().parents[1]
CHECK = Path('/home/v-zhouziyu/work/sendov-research-20260914-research/paper-formalization/check.py')
PROOFS = [
    'Sendov.Boundary', 'tests.BoundaryProbe',
    'Sendov.Analytic.FirstOriginAlgebra', 'Sendov.Analytic.FirstOriginBounds',
    'Sendov.Analytic.FirstOriginSmall', 'Sendov.Interior', 'Sendov.Conjecture', 'Solution',
    'Sendov.Collinear.Gate', 'Sendov.Collinear.Mass', 'Sendov.Collinear.Balance',
    'Sendov.Collinear.Diameter', 'Sendov.Collinear.Moment',
    'tests.CollinearTests', 'tests.CollinearRound2Tests', 'tests.CollinearAcceptance',
    'tests.Localanalytic', 'tests.Localreduction', 'tests.LocalMiddleAlpha',
    'tests.LocalPeakClosure',
]
AUDITS = ['scripts.axioms', 'tests.BoundaryWiring', 'tests.BoundaryAudit',
          'tests.BoundaryContracts', 'tests.FirstOriginAudit', 'tests.FirstOriginWiring',
          'tests.NoFiniteRows']


def main():
    parser = argparse.ArgumentParser()
    parser.add_argument('--tag', required=True)
    parser.add_argument('modules', nargs='*')
    args = parser.parse_args()
    logs = TREE / '.lake/paper/logs'
    evidence = TREE / 'tests/integration-existing'
    evidence.mkdir(parents=True, exist_ok=True)
    receipts = []
    modules = args.modules or PROOFS[:16] + ['Sendov'] + PROOFS[16:] + AUDITS
    for module in modules:
        source = TREE / Path(*module.split('.')).with_suffix('.lean')
        before = hashlib.sha256(source.read_bytes()).hexdigest()
        if module in PROOFS:
            assert not list(source.with_suffix('').glob('**/*.lean')), module
        for kernel in ([False, True] if module in PROOFS else [False]):
            stem = args.tag + '-' + module + ('-kernel' if kernel else '')
            assert not (logs / (stem + '.json')).exists(), 'use a fresh tag'
            command = [sys.executable, str(CHECK), str(TREE), module, '--tag', args.tag]
            if kernel:
                command.append('--kernel')
            result = subprocess.run(command, cwd=TREE, text=True, capture_output=True)
            record = json.loads((logs / (stem + '.json')).read_text())
            assert record['exit_code'] == result.returncode
            record.update(wrapper_command=command, source_sha256=before,
                          log=str(logs / (stem + '.log')))
            record['source_unchanged'] = hashlib.sha256(source.read_bytes()).hexdigest() == before
            receipts.append(record)
            (evidence / (args.tag + '-receipts.json')).write_text(json.dumps(receipts, indent=2) + '\n')
            print(f"{module} {'kernel' if kernel else 'compile'}: exit {result.returncode} ({record['seconds']:.2f}s)", flush=True)
            if result.returncode or not record['source_unchanged']:
                print(result.stdout + result.stderr)
                raise SystemExit(result.returncode or 1)
    print(f'PASS: {len(receipts)} gates; detailed actual commands in {evidence / (args.tag + "-receipts.json")}')


if __name__ == '__main__':
    main()
