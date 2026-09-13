"""Portable active-route generator tests. Run with unittest, using Python with SymPy.

The digest fixture pins the accepted mathematical source (only the generator-path
comment changed). It is shipped here; no workspace report or external fixture is read.
These are Python regressions, not Lean acceptance tests.
"""
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
        for directory in ('scripts', 'data'):
            if (ROOT / directory).exists():
                shutil.copytree(ROOT / directory, self.repo / directory,
                                ignore=shutil.ignore_patterns('__pycache__'))
        (self.repo / 'scripts').mkdir(exist_ok=True)
        self.elsewhere = self.work / 'unrelated'
        self.elsewhere.mkdir()

    def cli(self, script, *args, cwd=None, optimized=False):
        return subprocess.run([sys.executable, '-B', *(['-O'] if optimized else []),
                               str(self.repo / 'scripts' / script), *map(str, args)],
                              cwd=cwd or self.elsewhere, capture_output=True, text=True,
                              env={**os.environ, 'PYTHONDONTWRITEBYTECODE': '1'}, timeout=120)

    def assert_success(self, result):
        self.assertEqual(result.returncode, 0, result.stdout + result.stderr)

    def assert_distillation(self, output):
        actual = {str(p.relative_to(output)): digest(p) for p in output.rglob('*') if p.is_file()}
        self.assertEqual(actual, EXPECTED['distillation'])
        aggregate = (output / 'Sendov/Common/DistillationFinite.lean').read_text()
        self.assertEqual(aggregate.count('  · exact (distillFinite_'), 77)
        self.assertTrue((output / 'Sendov/DistillationFinite/Row81.lean').is_file())
        self.assertFalse((output / 'Sendov/DistillationFinite/Row5.lean').exists())

    def test_complete_cli_regeneration_from_all_cwds(self):
        for i, cwd in enumerate((self.repo, self.repo / 'scripts', self.elsewhere)):
            with self.subTest(cwd=cwd):
                output = self.work / f'generated-{i}'
                if i == 1:
                    output.mkdir()  # explicitly empty targets are accepted too
                result = self.cli('gen_distillation.py', '--output', output, cwd=cwd)
                self.assert_success(result)
                self.assert_distillation(output)

    def test_sinh_explicit_and_default_outputs_from_all_cwds(self):
        for i, cwd in enumerate((self.repo, self.repo / 'scripts', self.elsewhere)):
            with self.subTest(cwd=cwd):
                output = self.work / f'Sinh-{i}.lean'
                self.assert_success(self.cli('gen_sinh.py', '--output', output, cwd=cwd))
                self.assertEqual(digest(output), EXPECTED['sinh']['sha256'])
                self.assertEqual(output.stat().st_size, EXPECTED['sinh']['bytes'])
                self.assert_success(self.cli('gen_sinh.py', cwd=cwd))
                self.assertEqual(output.read_bytes(),
                                 (self.repo / 'Sendov/Common/Sinh.lean').read_bytes())


    def test_bad_data_is_rejected_before_any_publication(self):
        original = json.loads((self.repo / 'data/paper_certificate_table.json').read_text())
        mutations = {
            'missing row': lambda r: r.pop(),
            'duplicate row': lambda r: r.__setitem__(1, r[0]),
            'row order': lambda r: r.reverse(),
            'missing component': lambda r: r[0]['components'].pop(),
            'component order': lambda r: r[0]['components'].reverse(),
            'boolean index': lambda r: r[0]['components'][0].__setitem__('index', False),
            'boolean degree': lambda r: r[0].__setitem__('m', True),
            'float degree': lambda r: r[0].__setitem__('m', 5.0),
            'false metadata': lambda r: r[0].__setitem__('e', '1/2'),
            'bad rational': lambda r: r[0].__setitem__('total', '1/0'),
            'changed total': lambda r: r[0].__setitem__('total', '1'),
            'changed square': lambda r: r[0]['components'][0].__setitem__('sq', '0'),
            'changed sign': lambda r: r[0]['components'][0].__setitem__('sign_lo', '0'),
            'bad budget': lambda r: r[0]['components'][0].__setitem__('u', 0),
            'bad bracket': lambda r: r[0]['components'][0].__setitem__('hi', '1/4'),
            'bad classification': lambda r: r[0]['components'][0].__setitem__('k', 'B'),
            'unknown field': lambda r: r[0].__setitem__('unused', 1),
            'missing field': lambda r: r[0]['components'][0].pop('sq'),
            'wrong container': lambda r: r[0].__setitem__('components', {}),
        }
        for name, mutation in mutations.items():
            with self.subTest(mutation=name):
                rows = json.loads(json.dumps(original))
                mutation(rows)
                table = self.work / 'bad.json'
                table.write_text(json.dumps(rows))
                output = self.work / ('invalid-' + name.replace(' ', '-'))
                output.mkdir(exist_ok=True)
                before = inventory(self.work)
                result = self.cli('gen_distillation.py', '--table', table, '--output', output,
                                  optimized=True)
                self.assertNotEqual(result.returncode, 0, name)
                self.assertNotIn('Traceback', result.stderr)
                self.assertEqual(inventory(self.work), before)
                self.assertEqual(list(output.iterdir()), [])

    def test_invalid_json_and_missing_inputs_do_not_create_output(self):
        for text in ('{', '{"a":1,"a":2}', '[NaN]', '[Infinity]'):
            with self.subTest(text=text):
                table = self.work / 'bad.json'
                table.write_text(text)
                output = self.work / 'never-created'
                result = self.cli('gen_distillation.py', '--table', table, '--output', output)
                self.assertNotEqual(result.returncode, 0)
                self.assertNotIn('Traceback', result.stderr)
                self.assertFalse(output.exists())
        missing = self.cli('gen_distillation.py', '--table', self.work / 'missing.json',
                           '--output', self.work / 'never-created')
        self.assertNotEqual(missing.returncode, 0)
        self.assertFalse((self.work / 'never-created').exists())


    def test_output_argument_is_required_and_subset_options_are_removed(self):
        before = inventory(self.work)
        for args in ((), ('--rows', '5'), ('--mutation', 'budget')):
            result = self.cli('gen_distillation.py', *args)
            self.assertNotEqual(result.returncode, 0)
            self.assertIn('--output', result.stderr)
        self.assertEqual(inventory(self.work), before)

    def test_nonempty_file_and_symlink_targets_are_preserved(self):
        directory = self.work / 'old'
        directory.mkdir()
        (directory / 'sentinel').write_bytes(b'original\x00bytes')
        regular = self.work / 'regular'
        regular.write_bytes(b'old-file')
        link = self.work / 'link'
        link.symlink_to(directory, target_is_directory=True)
        for output in (directory, regular, link):
            with self.subTest(output=output):
                before = inventory(self.work)
                result = self.cli('gen_distillation.py', '--output', output)
                self.assertNotEqual(result.returncode, 0)
                self.assertIn('new or empty directory', result.stderr)
                self.assertEqual(inventory(self.work), before)
                self.assertTrue(link.is_symlink())

    def test_missing_default_table_or_helper_has_no_output(self):
        for rel in ('data/paper_certificate_table.json', 'scripts/bundle_rows.py'):
            with self.subTest(missing=rel):
                path = self.repo / rel
                saved = path.read_bytes()
                path.unlink()
                before = inventory(self.work)
                result = self.cli('gen_distillation.py', '--output', self.work / 'out')
                self.assertNotEqual(result.returncode, 0)
                self.assertEqual(inventory(self.work), before)
                self.assertFalse((self.work / 'out').exists())
                path.write_bytes(saved)

    def test_imports_have_no_generation_side_effects(self):
        for cwd in (self.repo, self.repo / 'scripts', self.elsewhere):
            with self.subTest(cwd=cwd):
                before = inventory(self.work)
                program = ('import sys; sys.path.insert(0, ' + repr(str(self.repo / 'scripts'))
                           + '); import gen_sinh, gen_distillation, generator_output, '
                             'bundle_rows, distillation_data')
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
        result = self.cli('gen_sinh.py', '--output', output)
        self.assertNotEqual(result.returncode, 0)
        self.assertEqual(inventory(self.work), before)

    def test_sinh_actual_replace_failure_preserves_target(self):
        output = self.work / 'Sinh.lean'
        output.mkdir()
        (output / 'sentinel').write_bytes(b'old theorem source\n')
        before = inventory(self.work)
        result = self.cli('gen_sinh.py', '--output', output)
        self.assertNotEqual(result.returncode, 0)
        self.assertEqual(inventory(self.work), before)
        self.assertEqual(set(self.work.glob('.Sinh.lean.*.tmp')), set())


    def test_audit_propagates_lean_command_failure(self):
        # A deliberately failing executable models a missing/broken Lean command,
        # not a proof result. The shell audit must not turn its failure into PASS.
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


if __name__ == '__main__':
    unittest.main()
