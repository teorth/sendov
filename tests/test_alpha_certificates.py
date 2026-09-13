"""Reject mutations of the complete retained identities, using the real Lean frontend."""
import json
import hashlib
import os
from pathlib import Path
import re
import subprocess
import tempfile
import unittest

ROOT = Path(__file__).resolve().parents[1]
COMMON = ROOT / 'Sendov/Common'


def certificate_prefix(file, namespace, coefficient_name, identity):
    text = (COMMON / file).read_text()
    start = text.index(f'namespace {namespace}\n')
    end = text.index('\n\n', text.index('\n  ring1', text.index(identity, start)))
    prefix = text[:end]
    # Retain the entire polynomial identity, factor definitions and coefficient list.
    opened = []
    for line in prefix.splitlines():
        if line.startswith('namespace '):
            opened.append(line.removeprefix('namespace '))
        elif line.startswith('end '):
            assert opened.pop() == line.removeprefix('end ')
    prefix += '\n\n' + ''.join(f'end {name}\n' for name in reversed(opened))
    pattern = rf'private def {coefficient_name} : List \u2115 := \[(.*?)\]'
    matches = list(re.finditer(pattern, prefix, re.S))
    match = next(m for m in matches if m.start() > start)
    return prefix, match


class AlphaCertificateTests(unittest.TestCase):
    def lean(self, source, label):
        with tempfile.TemporaryDirectory(prefix='alpha-identity-', dir=ROOT / '.lake') as tmp:
            path = Path(tmp) / 'Identity.lean'
            path.write_text(source)
            result = subprocess.run(
                ['lake', 'env', 'lean', '-DwarningAsError=true', str(path)],
                cwd=ROOT, text=True, stdout=subprocess.PIPE, stderr=subprocess.STDOUT,
                timeout=180)
        if destination := os.environ.get('SENDOV_ALPHA_LOG_DIR'):
            log = Path(destination)
            log.mkdir(parents=True, exist_ok=True)
            (log / (label + '.log')).write_text(result.stdout)
            (log / (label + '.lean')).write_text(source)
            (log / (label + '.json')).write_text(json.dumps({
                'exit_code': result.returncode,
                'source_sha256': hashlib.sha256(source.encode()).hexdigest(),
            }))
        return result

    def assert_identity_rejected(self, source, label):
        result = self.lean(source, label)
        self.assertNotEqual(result.returncode, 0, result.stdout)
        errors = [line for line in result.stdout.splitlines() if ': error:' in line]
        self.assertEqual(len(errors), 1, result.stdout)
        self.assertIn('error: ring failed, ring expressions not equal', errors[0])
        for unexpected in ['unknown identifier', 'Unknown identifier', 'failed to synthesize',
                           'maximum recursion depth', 'maximum number of heartbeats',
                           'declaration uses', 'error: linter', 'unknown module']:
            self.assertNotIn(unexpected, result.stdout)

    def test_all_three_full_identities_reject_interior_coefficient_mutation(self):
        for label, file, namespace, name, identity, length in [
            ('first', 'DistillationPeakFirst.lean', 'Sendov.PeakClosure',
             'gap1Coefficients', 'private lemma gap1H_identity', 54),
            ('low', 'DistillationPeakRest.lean', 'LowHomogeneous',
             'coefficients', 'lemma gapH_identity', 48),
            ('high', 'DistillationPeakRest.lean', 'HighHomogeneous',
             'coefficients', 'lemma gapH_identity', 48),
        ]:
            with self.subTest(certificate=label):
                source, match = certificate_prefix(file, namespace, name, identity)
                good = self.lean(source, label + '-control')
                self.assertEqual(good.returncode, 0, good.stdout)
                entries = list(re.finditer(r'0x[0-9a-fA-F]+|\d+', match.group(1)))
                self.assertEqual(len(entries), length)
                selected = entries[length // 2]
                before = match.start(1) + selected.start()
                after = match.start(1) + selected.end()
                value = int(selected.group(), 16 if selected.group().startswith('0x') else 10)
                replacement = hex(value + 1) if selected.group().startswith('0x') else str(value + 1)
                mutant = source[:before] + replacement + source[after:]
                self.assert_identity_rejected(mutant, label + '-wrong-coefficient')

    def test_complete_factor_identity_rejects_wrong_scale_and_interval(self):
        text = (COMMON / 'DistillationPeakFirst.lean').read_text()
        end = text.index('\n\n', text.index('\n  ring1', text.index('private lemma SH_eval')))
        source = text[:end] + '\n\nend Sendov.PeakClosure\n'
        control = self.lean(source, 'factor-control')
        self.assertEqual(control.returncode, 0, control.stdout)
        self.assertIn('(15 : \u211d) ^ 1', source)
        self.assert_identity_rejected(source.replace('(15 : \u211d) ^ 1', '(16 : \u211d) ^ 1'),
                                      'factor-wrong-scale')
        self.assert_identity_rejected(source.replace('((17) - a)', '((18) - a)'),
                                      'factor-wrong-interval')


if __name__ == '__main__':
    unittest.main()
