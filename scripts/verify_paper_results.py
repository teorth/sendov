#!/usr/bin/env python3
"""Bounded direct replay of the complete affected paper-proof module DAG.

Package caches and pinned config are inputs. Private project objects must be
prepared first. No Lake build or dependency download occurs. Each completed
module records a source-bound receipt so an interrupted run can resume.
"""
import argparse
import hashlib
import json
from pathlib import Path
import subprocess
import sys

TREE = Path(__file__).resolve().parents[1]
p = argparse.ArgumentParser()
p.add_argument('--config', type=Path, required=True)
p.add_argument('--tag', required=True)
p.add_argument('--resume', action='store_true')
a = p.parse_args()
config = a.config.resolve()
manifest = json.loads((TREE / 'docs/paper-formalization/modules.json').read_text())
modules = manifest['affected_modules_topological']
assert len(modules) == len(set(modules))
logs = TREE / '.lake/paper/logs'
result_file = TREE / '.lake/paper' / (a.tag + '-receipts.json')
prior = json.loads(result_file.read_text()) if a.resume and result_file.exists() else []
accepted = {(r['module'], r['kernel']): r for r in prior}
rows = []


def digest(path):
    return hashlib.sha256(path.read_bytes()).hexdigest()


config_digest = digest(config)
expected_gates = 0
for module in modules:
    source = TREE / Path(*module.split('.')).with_suffix('.lean')
    source_digest = digest(source)
    # leanchecker targets are namespace prefixes. An import-only umbrella has
    # no declarations to replay, and passing it would replay every descendant.
    import_only = all(not line.strip() or line.startswith('import ')
                      for line in source.read_text().splitlines())
    checks = [False] if import_only else [False, True]
    expected_gates += len(checks)
    if import_only:
        print(module, 'IMPORT_ONLY: no local kernel declarations', flush=True)
    for kernel in checks:
        previous = accepted.get((module, kernel))
        if previous and previous['exit_code'] == 0:
            assert previous['source_sha256'] == source_digest, 'source changed; use a new tag'
            assert previous['config_sha256'] == config_digest, 'config changed; use a new tag'
            rows.append(previous)
            print(module, 'kernel' if kernel else 'compile', 'REUSED', flush=True)
            continue
        command = [sys.executable, str(TREE / 'scripts/check_paper.py'), str(TREE),
                   module, '--config', str(config), '--tag', a.tag]
        if kernel:
            command.append('--kernel')
        result = subprocess.run(command, cwd=TREE, capture_output=True, text=True)
        stem = a.tag + '-' + module + ('-kernel' if kernel else '')
        record = json.loads((logs / (stem + '.json')).read_text())
        record.update(source_sha256=source_digest, config_sha256=config_digest)
        assert digest(source) == source_digest, 'source changed during verification'
        assert record['exit_code'] == result.returncode
        rows.append(record)
        result_file.write_text(json.dumps(rows, indent=2))
        print(module, 'kernel' if kernel else 'compile', result.returncode,
              round(record['seconds'], 3), flush=True)
        if result.returncode:
            print(result.stdout + result.stderr, flush=True)
            raise SystemExit(result.returncode)
assert len(rows) == expected_gates
result_file.write_text(json.dumps(rows, indent=2))
print(f'PASS: {len(modules)} affected modules, {len(rows)} compile/kernel gates', flush=True)
