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
    def test_interval_and_tail_exact_base_domain_and_components(self):
        selected = [r for r in json.loads(g.TABLE.read_text()) if 5 <= r['m'] <= 61]
        self.assertEqual([r['m'] for r in selected], [*range(5, 56), 61])
        with tempfile.TemporaryDirectory() as temporary:
            table = Path(temporary) / 'table.json'
            table.write_text(json.dumps(selected))
            self.assertEqual(load_table(table, g.coefficients), selected)
            mutations = {
                'missing61': lambda r: r.pop(),
                'missing55': lambda r: r.pop(-2),
                'retired56': lambda r: r.__setitem__(-2, dict(r[-2], m=56)),
                'extra62': lambda r: r.append(dict(r[-1], m=62)),
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

    def test_generator_covers_50_cases_six_degree_interval_and_tail(self):
        with tempfile.TemporaryDirectory() as temporary:
            output = Path(temporary) / 'output'
            result = g.generate(output)
            self.assertEqual(result['rows'], [*range(5, 56), 61])
            self.assertEqual(result['groups'][-2]['rows'], [53, 54, 55])
            self.assertEqual(result['groups'][-1]['rows'], [61])
            self.assertEqual(len(result['groups']), 8)
            self.assertTrue((output / 'Sendov/DistillationFinite/Rows61_61.lean').is_file())
            self.assertFalse((output / 'Sendov/DistillationFinite/Row61.lean').exists())
            aggregate = (output / 'Sendov/Common/DistillationFinite.lean').read_text()
            cases = [f'  · exact (distillFinite_{m} α hα (by linarith)).trans_lt '
                     f'distillFiniteBound_{m}' for m in range(5, 34)]
            cases += [f'  · exact (distillFinite_{m} α hα h17).trans_lt '
                      f'distillFiniteBound_{m}' for m in range(34, 55)]
            self.assertEqual([line for line in aggregate.splitlines()
                              if line.startswith('  · exact (distillFinite_')], cases)
            self.assertIn('(hm60 : m ≤ 60)', aggregate)
            self.assertIn('by_cases hinterval : 55 ≤ m', aggregate)
            self.assertIn('exact distillComponents_interval_55_61', aggregate)
            for path in output.rglob('*.lean'):
                self.assertNotIn('two_thirds', path.read_text())
                self.assertNotIn('distillFiniteTailBase', path.read_text())

    def test_real_pilot_uses_raw_coefficient_list(self):
        row = next(r for r in json.loads(g.TABLE.read_text()) if r['m'] == 46)
        text = g.row_source(row)
        self.assertIn('BernsteinCert.coeffs_pos', text)
        self.assertNotIn('have hid', text)
        self.assertNotIn('sign_0_left_0', text)

    def test_every_flank_keeps_the_complete_original_identity(self):
        identities = empty = 0
        for row in g.load_table(g.TABLE, g.coefficients):
            m = row['m']
            for component in row['components']:
                j = component['index']
                for side, a, b in [('left', F(0), F(component['lo'])),
                                   ('right', F(component['hi']), min(F(17), F(m, 2)))]:
                    with self.subTest(m=m, component=j, side=side):
                        text, count = g.sign_source(m, j, side, a, b)
                        self.assertIn(f'0 ≤ {g.signed(j, m, side)}', text)
                        if a == b:
                            empty += 1
                            self.assertEqual(count, 0)
                            self.assertIn('False.elim', text)
                            self.assertNotIn('coeffs_pos', text)
                            continue
                        identities += 1
                        self.assertEqual(count, 1)
                        p = g.coefficients(m, j)
                        if (j == 0) != (side == 'left'):
                            p = [-c for c in p]
                        scale, cs = g.certificate(p, a, b)
                        compact = ''.join(text.split())
                        self.assertIn('BernsteinCert.coeffs_pos[' +
                                      ','.join(map(str, cs)) + ']', compact)
                        self.assertIn(f'(lo:={g.rat(a)})(hi:={g.rat(b)})(s:={scale})'
                                      .replace(' ', ''), compact)
                        self.assertIn(f'unfold distillCritical{j}', text)
                        self.assertIn('simp only [BernsteinCert.coeffTree_eval_cons,', text)
                        self.assertIn('BernsteinCert.coeffTree_eval_nil', text)
                        self.assertEqual(text.count('  ring1\n'), 1)
                        self.assertNotIn('norm_num only', text)
                        self.assertNotIn('bernstein_ring', text)
        self.assertEqual((identities, empty), (291, 21))

    def test_interval_growth_budget_is_exact_and_has_strict_slack(self):
        # Independent numerical contract, not values read from generated Lean.
        row = next(r for r in json.loads(g.TABLE.read_text()) if r['m'] == 55)
        self.assertEqual([c['u'] for c in row['components']], [248, 91, 330])
        slope = F(1, 54) + F(2, 21)
        self.assertEqual(slope - 5 * (1 - F(979, 1000)), F(331, 37800))
        self.assertEqual(slope - F(1, 11), F(95, 4158))
        u = F(17, 20)
        eta = u - u**3 / 30
        node = F(4, 25) + F(3, 5)*eta + F(204, 1375)
        self.assertLessEqual(node, F(979, 1000)**10)
        self.assertLessEqual(eta, F(21, 22)**4)
        w1, w2 = 1 - F(331, 37800)*6, 1 - F(95, 4158)*6
        self.assertGreater(min(w1, w2), 0)
        total = F(43, 165) + F(31, 125) + F(91, 1000)/w1 + F(33, 100)/w2
        self.assertEqual(total, F(58135011269, 58896123000))
        self.assertLess(total, F(199, 200))
        # Removing growth or extending the same interval to 62 is not licensed.
        self.assertGreater(slope, F(1, 11))
        wider = F(43, 165) + F(31, 125) + F(91, 1000)/(1-F(331,37800)*7) + (
            F(33,100)/(1-F(95,4158)*7))
        self.assertGreater(wider, F(199, 200))

    def test_empty_polynomial_and_bad_interval_are_rejected(self):
        with self.assertRaisesRegex(ValueError, 'empty'):
            g.certificate([], F(0), F(1))
        with self.assertRaisesRegex(ValueError, 'interval'):
            g.certificate([1], F(1), F(0))
        with self.assertRaisesRegex(ValueError, 'component'):
            g.coefficients(5, 3)

    def test_all_central_budgets_keep_raw_factors_and_correlated_exponents(self):
        count = 0
        for row in json.loads(g.TABLE.read_text()):
            m = row['m']
            source = g.row_source(row)
            self.assertEqual(source.count(
                'norm_num only [distillKappa, distillRatio, distillNode, cubicPolarEnvelope]'), 3)
            self.assertNotIn('norm_num [distillEBudget] at *', source)
            self.assertIn('add_le_add (add_le_add (add_le_add le_rfl h0) h1) h2', source)
            self.assertIn(f"_ = {g.rat(row['total'])} := by norm_num only [distillEBudget]",
                          source)
            budgets = [g.rat(F(c['u'], 1000)) for c in row['components']]
            self.assertIn(f"_ ≤ distillEBudget {m} + " + ' + '.join(budgets), source)
            for c in row['components']:
                j, lo, hi = c['index'], F(c['lo']), F(c['hi'])
                with self.subTest(m=m, component=j):
                    # Reconstruct the raw formulas, including lo=0, rather than
                    # calling the table validator's cancelled-ratio evaluator.
                    u, v = lo / (lo + 3), hi / (hi + 3)
                    ratio = (1-u) * (1-u**2/30) / 3
                    kappa = F(m*m-1, 4*m) * ratio * (m-2*lo)**2
                    envelope = v-v**3/30
                    node = F(4, 25) + F(3, 5)*envelope + F(12, 25*m)*hi
                    if j == 0:
                        square = (kappa * 96*F(3, 5)**4 /
                                  ((m-1)*(m+1)*(m+3)*(m+5)*(1-node)**4))**2
                    else:
                        square = (F((259, 421)[j-1], 3125)*kappa)**2 * (
                            node if j == 1 else envelope)**(m-3)
                        component = source.split(f'theorem component{j} ')[1].split('\n\n')[0]
                        self.assertIn(f'    {m-3} (by norm_num) (by norm_num)', component)
                    self.assertEqual(square, F(c['sq']))
                    self.assertLess(square, F(c['u'], 1000)**2)
                    count += 1
        self.assertEqual(count, 156)

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
