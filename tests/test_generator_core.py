"""Exact-core regressions and publication I/O fault injection (never mocked math)."""
from fractions import Fraction as F
import json
from math import comb
from pathlib import Path
import sys
import tempfile
import unittest
from unittest.mock import patch

sys.path.insert(0, str(Path(__file__).resolve().parents[1] / 'scripts'))
import gen_distillation as g
from distillation_data import load_table
import generator_output


class ExactCoreTests(unittest.TestCase):
    def test_k64_exact_allowed_domain_and_components(self):
        selected = [r for r in json.loads(g.TABLE.read_text()) if 5 <= r['m'] <= 64]
        self.assertEqual([r['m'] for r in selected], list(range(5, 65)))
        with tempfile.TemporaryDirectory() as temporary:
            table = Path(temporary) / 'table.json'
            table.write_text(json.dumps(selected))
            self.assertEqual(load_table(table, g.coefficients), selected)
            mutations = {
                'missing64': lambda r: r.pop(),
                'extra65': lambda r: r.append(dict(r[-1], m=65)),
                'duplicate': lambda r: r.__setitem__(1, r[0]),
                'reordered': lambda r: r.reverse(),
                'duplicate component': lambda r: r[0]['components'].__setitem__(
                    1, r[0]['components'][0]),
                'reordered components': lambda r: r[0]['components'].reverse(),
                'mismatched components': lambda r: r[0].__setitem__(
                    'components', r[1]['components']),
            }
            for name, mutate in mutations.items():
                with self.subTest(mutation=name):
                    rows = json.loads(json.dumps(selected))
                    mutate(rows)
                    table.write_text(json.dumps(rows))
                    with self.assertRaises(ValueError):
                        load_table(table, g.coefficients)

    def test_k64_generator_covers_59_finite_cases_and_one_shared_base(self):
        with tempfile.TemporaryDirectory() as temporary:
            output = Path(temporary) / 'output'
            result = g.generate(output)
            self.assertEqual(result['rows'], list(range(5, 65)))
            self.assertEqual(result['groups'][-1]['rows'], [61, 62, 63, 64])
            self.assertEqual(len(result['groups']), 8)
            self.assertTrue((output / 'Sendov/DistillationFinite/Rows61_64.lean').is_file())
            self.assertFalse((output / 'Sendov/DistillationFinite/Row64.lean').exists())
            aggregate = (output / 'Sendov/Common/DistillationFinite.lean').read_text()
            cases = [f'  · exact (distillFinite_{m} α hα (by linarith)).trans_lt '
                     f'distillFiniteBound_{m}' for m in range(5, 64)]
            self.assertEqual([line for line in aggregate.splitlines()
                              if line.startswith('  · exact (distillFinite_')], cases)
            self.assertIn('(hm63 : m ≤ 63)', aggregate)
            for path in output.rglob('*.lean'):
                self.assertNotIn('two_thirds', path.read_text())
                self.assertNotIn('distillFiniteTailBase', path.read_text())

    def test_real_pilot_uses_raw_coefficient_list(self):
        row = next(r for r in json.loads(g.TABLE.read_text()) if r['m'] == 46)
        text = g.row_source(row)
        self.assertIn('BernsteinCert.coeffs_pos', text)
        self.assertNotIn('have hid', text)
        self.assertNotIn('sign_0_left_0', text)

    def test_empty_polynomial_and_bad_interval_are_rejected(self):
        with self.assertRaisesRegex(ValueError, 'empty'):
            g.certificate([], F(0), F(1))
        with self.assertRaisesRegex(ValueError, 'interval'):
            g.certificate([1], F(1), F(0))
        with self.assertRaisesRegex(ValueError, 'component'):
            g.coefficients(5, 3)

    def test_all_actual_sign_certificates_by_coefficient_reconstruction(self):
        # Expand the Bernstein basis back into powers, independently of the
        # renderer's change-of-basis implementation. No sampled evaluations.
        rows = json.loads(g.TABLE.read_text())
        for row in rows:
            m = row['m']
            for component in row['components']:
                j = component['index']
                for side, a, b in [('left', F(0), F(component['lo'])),
                                   ('right', F(component['hi']), min(F(17), F(m, 2)))]:
                    if a == b:
                        continue  # empty flank has an explicit False.elim proof
                    with self.subTest(m=m, component=j, side=side):
                        p = g.coefficients(m, j)
                        if (j == 0) != (side == 'left'):
                            p = [-c for c in p]
                        [(lo, hi, scale, cs)] = g.sign_cover(p, a, b)
                        n = len(p) - 1
                        reconstructed = [F(0)] * len(p)
                        for i, coefficient in enumerate(cs):
                            for u in range(i + 1):
                                for v in range(n - i + 1):
                                    reconstructed[u+v] += (coefficient * comb(i, u)
                                        * (-lo)**(i-u) * comb(n-i, v) * hi**(n-i-v) * (-1)**v)
                        self.assertEqual(reconstructed, [scale*c for c in p])
                        self.assertGreaterEqual(min(cs), 0)
                        self.assertGreater(cs[0], 0)
                        self.assertGreater(cs[-1], 0)

    def test_sign_cover_gap_overlap_and_negative_polynomial_are_rejected(self):
        for intervals in ([], [(F(0), F(1)), (F(2), F(3))],
                          [(F(0), F(2)), (F(1), F(3))]):
            with self.assertRaises(ValueError):
                g.validate_cover(intervals, F(0), F(3))
        with self.assertRaises(ValueError):
            g.sign_cover([-1], F(0), F(1))


class PublicationTests(unittest.TestCase):
    def test_staging_write_failure_leaves_empty_target_and_cleans_staging(self):
        with tempfile.TemporaryDirectory() as temporary:
            parent = Path(temporary)
            output = parent / 'output'
            output.mkdir()
            before = output.stat().st_ino
            actual_write = Path.write_text
            calls = 0

            def fail_seventh(path, *args, **kwargs):
                nonlocal calls
                calls += 1
                if calls == 7:
                    raise OSError('injected seventh staging write failure')
                return actual_write(path, *args, **kwargs)

            with patch.object(Path, 'write_text', fail_seventh):
                with self.assertRaisesRegex(OSError, 'seventh'):
                    g.generate(output)
            self.assertEqual(output.stat().st_ino, before)
            self.assertEqual(list(output.iterdir()), [])
            self.assertEqual(list(parent.iterdir()), [output])

    def test_publish_failure_preserves_empty_target(self):
        with tempfile.TemporaryDirectory() as temporary:
            parent = Path(temporary)
            output = parent / 'output'
            output.mkdir()
            before = output.stat().st_ino
            with patch.object(g.os, 'replace', side_effect=OSError('injected publish failure')):
                with self.assertRaisesRegex(OSError, 'publish'):
                    g.generate(output)
            self.assertEqual(output.stat().st_ino, before)
            self.assertEqual(list(output.iterdir()), [])
            self.assertEqual(list(parent.iterdir()), [output])

    def test_real_rename_refuses_late_nonempty_target(self):
        with tempfile.TemporaryDirectory() as temporary:
            parent = Path(temporary)
            output = parent / 'output'
            actual_replace = g.os.replace

            def competing_output(source, target):
                target.mkdir()
                (target / 'sentinel').write_bytes(b'competing output')
                return actual_replace(source, target)

            with patch.object(g.os, 'replace', competing_output):
                with self.assertRaises(OSError):
                    g.generate(output)
            self.assertEqual((output / 'sentinel').read_bytes(), b'competing output')
            self.assertEqual(list(parent.iterdir()), [output])

    def test_writer_success_replaces_target_and_cleans_staging(self):
        with tempfile.TemporaryDirectory() as temporary:
            output = Path(temporary) / 'file.lean'
            output.write_bytes(b'old')
            generator_output.write_lean(output, 'new α\n')
            self.assertEqual(output.read_bytes(), 'new α\n'.encode())
            self.assertEqual(list(Path(temporary).iterdir()), [output])

    def test_writer_rejected_source_preserves_previous_file(self):
        with tempfile.TemporaryDirectory() as temporary:
            output = Path(temporary) / 'file.lean'
            output.write_bytes(b'old')
            with self.assertRaises(TypeError):
                generator_output.write_lean(output, object())
            self.assertEqual(output.read_bytes(), b'old')
            self.assertEqual(list(Path(temporary).iterdir()), [output])


if __name__ == '__main__':
    unittest.main()
