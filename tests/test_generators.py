"""Portable sinh regeneration and audit command-failure regressions."""
import hashlib
import json
import os
from pathlib import Path
import shutil
import subprocess
import sys
import tempfile
import unittest

ROOT = Path(__file__).resolve().parents[1]
EXPECTED = json.loads((Path(__file__).with_name('expected.json')).read_text())


def digest(path):
    return hashlib.sha256(path.read_bytes()).hexdigest()


def inventory(root):
    result = {}
    for path in root.rglob('*'):
        if path.is_symlink():
            value = ('symlink', os.readlink(path))
        elif path.is_dir():
            value = ('directory',)
        else:
            value = ('file', path.read_bytes())
        result[str(path.relative_to(root))] = value
    return result


class GeneratorTests(unittest.TestCase):
    def setUp(self):
        self.temp = tempfile.TemporaryDirectory()
        self.addCleanup(self.temp.cleanup)
        self.work = Path(self.temp.name)
        self.repo = self.work / 'relocated-source'
        self.repo.mkdir()
        shutil.copytree(ROOT / 'scripts', self.repo / 'scripts',
                        ignore=shutil.ignore_patterns('__pycache__'))
        self.elsewhere = self.work / 'unrelated'
        self.elsewhere.mkdir()

    def cli(self, *args, cwd=None):
        return subprocess.run([sys.executable, '-B', str(self.repo / 'scripts/gen_sinh.py'),
                               *map(str, args)], cwd=cwd or self.elsewhere,
                              capture_output=True, text=True,
                              env={**os.environ, 'PYTHONDONTWRITEBYTECODE': '1'}, timeout=120)

    def assert_success(self, result):
        self.assertEqual(result.returncode, 0, result.stdout + result.stderr)

    def test_sinh_explicit_and_default_outputs_from_all_cwds(self):
        for i, cwd in enumerate((self.repo, self.repo / 'scripts', self.elsewhere)):
            with self.subTest(cwd=cwd):
                output = self.work / f'Sinh-{i}.lean'
                self.assert_success(self.cli('--output', output, cwd=cwd))
                self.assertEqual(digest(output), EXPECTED['sinh']['sha256'])
                self.assertEqual(output.stat().st_size, EXPECTED['sinh']['bytes'])
                self.assert_success(self.cli(cwd=cwd))
                self.assertEqual(output.read_bytes(),
                                 (self.repo / 'Sendov/Common/Sinh.lean').read_bytes())

    def test_imports_have_no_generation_side_effects(self):
        for cwd in (self.repo, self.repo / 'scripts', self.elsewhere):
            with self.subTest(cwd=cwd):
                before = inventory(self.work)
                program = ('import sys; sys.path.insert(0, ' + repr(str(self.repo / 'scripts'))
                           + '); import gen_sinh, generator_output')
                result = subprocess.run([sys.executable, '-B', '-c', program], cwd=cwd,
                                        capture_output=True, text=True, timeout=30)
                self.assert_success(result)
                self.assertEqual(result.stdout, '')
                self.assertEqual(result.stderr, '')
                self.assertEqual(inventory(self.work), before)

    def test_sinh_missing_tail_preserves_existing_target(self):
        output = self.work / 'Sinh.lean'
        output.write_bytes(b'old theorem source\n')
        (self.repo / 'scripts/sinh_tail.lean.txt').unlink()
        before = inventory(self.work)
        result = self.cli('--output', output)
        self.assertNotEqual(result.returncode, 0)
        self.assertEqual(inventory(self.work), before)

    def test_sinh_actual_replace_failure_preserves_target(self):
        output = self.work / 'Sinh.lean'
        output.mkdir()
        (output / 'sentinel').write_bytes(b'old theorem source\n')
        before = inventory(self.work)
        result = self.cli('--output', output)
        self.assertNotEqual(result.returncode, 0)
        self.assertEqual(inventory(self.work), before)
        self.assertEqual(set(self.work.glob('.Sinh.lean.*.tmp')), set())

    def test_audit_propagates_lean_command_failure(self):
        (self.repo / 'Sendov').mkdir()
        (self.repo / 'Solution.lean').write_text('-- no proof in this I/O fixture\n')
        (self.repo / 'Challenge.lean').write_text('sorry\nsorry\n')
        bin_dir = self.work / 'bin'
        bin_dir.mkdir()
        lake = bin_dir / 'lake'
        lake.write_text('#!/bin/sh\nexit 42\n')
        lake.chmod(0o755)
        result = subprocess.run(['sh', str(self.repo / 'scripts/audit.sh')],
                                cwd=self.elsewhere, capture_output=True, text=True,
                                env={**os.environ, 'PATH': str(bin_dir) + os.pathsep + os.environ['PATH']})
        self.assertNotEqual(result.returncode, 0, result.stdout + result.stderr)
        self.assertIn('Lean axiom query failed', result.stdout)


if __name__ == '__main__':
    unittest.main()
