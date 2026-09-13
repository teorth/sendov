from pathlib import Path
import importlib.util
import tempfile
import unittest

ROOT = Path(__file__).resolve().parents[1] / 'scripts'
spec = importlib.util.spec_from_file_location('bundle_rows', ROOT / 'bundle_rows.py')
bundle_rows = importlib.util.module_from_spec(spec)
spec.loader.exec_module(bundle_rows)

class Bundling(unittest.TestCase):
    def fixture(self, root):
        source = root / 'input'
        rows = source / 'Sendov/DistillationFinite'
        rows.mkdir(parents=True)
        (source / 'Sendov/Common').mkdir()
        for m in range(5, 82):
            (rows / f'Row{m}.lean').write_text(
                'import Mathlib.Data.Nat.Basic\n\n'
                f'namespace FixtureRow{m}\ntheorem value : (1 : Nat) = 1 := rfl\nend FixtureRow{m}\n')
        (source / 'Sendov/Common/DistillationFinite.lean').write_text(''.join(
            f'import Sendov.DistillationFinite.Row{m}\n' for m in range(5, 82)) + '\n-- aggregate body\n')
        return source

    def test_all_rows_once_in_original_order_and_bodies_preserved(self):
        with tempfile.TemporaryDirectory() as temporary:
            root = Path(temporary); source = self.fixture(root)
            result = bundle_rows.bundle(source, root / 'out', size=8)
            self.assertEqual([m for group in result['groups'] for m in group['rows']], list(range(5, 82)))
            for group in result['groups']:
                text = (root / 'out' / group['path']).read_text()
                for m in group['rows']:
                    original = (source / f'Sendov/DistillationFinite/Row{m}.lean').read_text()
                    body = ''.join(x for x in original.splitlines(keepends=True) if not x.startswith('import '))
                    self.assertIn(body, text)
            self.assertTrue((root / 'out/Sendov/DistillationFinite/Row81.lean').is_file())
            self.assertFalse((root / 'out/Sendov/DistillationFinite/Row46.lean').exists())
            aggregate = (root / 'out/Sendov/Common/DistillationFinite.lean').read_text()
            self.assertNotIn('import Sendov.DistillationFinite.Row46\n', aggregate)
            self.assertTrue(aggregate.endswith('\n-- aggregate body\n'))

    def test_missing_row_fails_before_output(self):
        with tempfile.TemporaryDirectory() as temporary:
            root = Path(temporary); source = self.fixture(root)
            (source / 'Sendov/DistillationFinite/Row6.lean').unlink()
            with self.assertRaisesRegex(ValueError, 'rows'):
                bundle_rows.bundle(source, root / 'out')
            self.assertFalse((root / 'out').exists())

    def test_duplicate_or_omitted_aggregate_import_is_not_repaired(self):
        with tempfile.TemporaryDirectory() as temporary:
            root = Path(temporary); source = self.fixture(root)
            aggregate = source / 'Sendov/Common/DistillationFinite.lean'
            aggregate.write_text(aggregate.read_text().replace('Row6\n', 'Row5\n'))
            with self.assertRaisesRegex(ValueError, 'aggregate'):
                bundle_rows.bundle(source, root / 'out')
            self.assertFalse((root / 'out').exists())

if __name__ == '__main__':
    unittest.main()
