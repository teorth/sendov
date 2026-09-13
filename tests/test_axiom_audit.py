"""Real offline Lean fixtures for the auditor, not proofs of Sendov."""
import os
from pathlib import Path
import re
import shutil
import subprocess
import tempfile
import unittest

REPO = Path(__file__).resolve().parents[1]
TOOLCHAIN = (REPO / 'lean-toolchain').read_text().strip()
ENV = dict(os.environ, ELAN_TOOLCHAIN=TOOLCHAIN)
ENV['PATH'] = str(Path.home() / '.elan/bin') + os.pathsep + ENV['PATH']
TARGETS = ['SendovConjecture.sendov', 'SendovConjecture.phelps_rodriguez', 'Sendov.distillFinite_components', 'Sendov.distillFinite_scalar', 'Sendov.distillFiniteTailBase', 'Sendov.distillComponents_lt_two_thirds', 'Sendov.distillScalar_lt_two_thirds', 'Sendov.polar_origin_incompatible']


def put(path, text):
    path.parent.mkdir(parents=True, exist_ok=True)
    path.write_text(text)

def command(cmd, cwd, log):
    run = subprocess.run(cmd, cwd=cwd, env=ENV, text=True,
                         stdout=subprocess.PIPE, stderr=subprocess.STDOUT)
    put(LOGS / log, '$ ' + ' '.join(cmd) + '\n' + run.stdout +
        f'\nPROCESS_EXIT={run.returncode}\n')
    return run.returncode, run.stdout

def fixture(name, mode, script_root, bad_target=None):
    project = ROOT / 'work' / name
    if project.exists():
        shutil.rmtree(project)
    project.mkdir(parents=True)
    put(project / 'lean-toolchain', TOOLCHAIN + '\n')
    put(project / 'lakefile.toml', '''name = "audit_fixture"
version = "0.0.0"
[[lean_lib]]
name = "Fixture"
roots = ["Dependency", "Solution", "Sendov.Common.DistillationFinite", "Sendov.LargeDegree.DistillationTailBound"]
''')
    dependency = 'theorem dependencyBridge : True := True.intro\n'
    if mode == 'external':
        dependency = ('axiom externalAssumption : True\n'
                      'theorem dependencyBridge : True := externalAssumption\n')
    elif mode == 'standard':
        dependency = '''theorem dependencyBridge : True :=
  Eq.mp (propext (Iff.rfl : True ↔ True))
    (Eq.mp (congrArg (fun _ : Quot (fun _ _ : Nat => True) => True)
      (Quot.sound (a := 0) (b := 1) (r := fun _ _ : Nat => True) True.intro))
      (Classical.choice (α := True) ⟨True.intro⟩))
'''
    put(project / 'Dependency.lean', dependency)
    modules = { 'Solution.lean': TARGETS[:2],
                'Sendov/Common/DistillationFinite.lean': TARGETS[2:4],
                'Sendov/LargeDegree/DistillationTailBound.lean': TARGETS[4:] }
    for module, targets in modules.items():
        text = 'import Dependency\n\n'
        for target in targets:
            if mode == 'missing' and target == bad_target:
                continue
            proof = ('dependencyBridge' if bad_target is None or target == bad_target
                     else 'True.intro')
            text += f'theorem {target} : True := {proof}\n'
        put(project / module, text)
    # Deliberate statement-only holes required by audit.sh step 2, not imported.
    put(project / 'Challenge.lean', 'theorem challengeA : True := by sorry\n'
                                  'theorem challengeB : True := by sorry\n')
    for file in ['audit.sh', 'axioms.lean']:
        put(project / 'scripts' / file, (script_root / 'scripts' / file).read_text())
    if mode == 'lean_error':
        with (project / 'scripts/axioms.lean').open('a') as f:
            f.write('\nexample : (0 : Nat) = 1 := by rfl\n')
    scanned = [project / 'Solution.lean', *project.glob('Sendov/**/*.lean')]
    assert not any(re.search(r'^\s*axiom\s', p.read_text(), re.M) for p in scanned)
    return project

def audit_case(name, mode, scripts, bad_target=None):
    project = fixture(name, mode, scripts, bad_target)
    code, output = command(['lake', 'build', 'Fixture'], project, name + '.build.log')
    assert code == 0, f'fixture build failed: {name}: {output}'
    return command(['sh', 'scripts/audit.sh'], project, name + '.audit.log')

class AxiomAuditTests(unittest.TestCase):
    @classmethod
    def setUpClass(cls):
        global ROOT, LOGS
        cls.temporary = tempfile.TemporaryDirectory(prefix='sendov-audit-test-')
        ROOT = Path(cls.temporary.name)
        LOGS = ROOT / 'logs'

    @classmethod
    def tearDownClass(cls):
        cls.temporary.cleanup()

    def test_empty_and_standard_axioms_pass(self):
        for mode in ['empty', 'standard']:
            with self.subTest(mode=mode):
                code, output = audit_case(mode, mode, REPO)
                self.assertEqual(code, 0, output)

    def test_every_target_rejects_an_imported_nonstandard_axiom(self):
        for i, target in enumerate(TARGETS):
            with self.subTest(target=target):
                code, output = audit_case(f'external-{i}', 'external', REPO, target)
                self.assertNotEqual(code, 0, output)
                self.assertIn(f'unexpected mathematical premise in {target}', output)
                self.assertIn('externalAssumption', output)

    def test_every_missing_target_and_real_lean_error_fail(self):
        for i, target in enumerate(TARGETS):
            with self.subTest(target=target):
                code, output = audit_case(f'missing-{i}', 'missing', REPO, target)
                self.assertNotEqual(code, 0, output)
                self.assertIn(f'missing audit declaration {target}', output)
        code, output = audit_case('lean-error', 'lean_error', REPO)
        self.assertNotEqual(code, 0, output)
        self.assertIn('Lean axiom query failed', output)

    def test_only_the_known_tactic_partial_signatures_are_allowed(self):
        for mode in ['known', 'extra', 'wrong-signature']:
            with self.subTest(mode=mode):
                project = fixture('partial-' + mode, 'empty', REPO)
                for rel in ['Sendov/Common/BernsteinCert.lean', 'Sendov/Common/BernsteinRing.lean']:
                    put(project / rel, (REPO / rel).read_text())
                if mode == 'extra':
                    put(project / 'Sendov/Unexpected.lean', 'partial def unexpected (n : Nat) : Nat := n\n')
                elif mode == 'wrong-signature':
                    path = project / 'Sendov/Common/BernsteinRing.lean'
                    path.write_text(path.read_text().replace('flatten (e : Expr) (op : Name)',
                                                            'flatten (e : Expr) (op : Nat)'))
                code, output = command(['lake', 'build', 'Fixture'], project, mode + '.build.log')
                self.assertEqual(code, 0, output)
                code, output = command(['sh', 'scripts/audit.sh'], project, mode + '.audit.log')
                if mode == 'known':
                    self.assertEqual(code, 0, output)
                else:
                    self.assertNotEqual(code, 0, output)
                    self.assertIn('partial def', output)

    def test_removing_the_allowlist_reopens_the_actual_false_green(self):
        mutant = ROOT / 'mutant'
        for name in ['audit.sh', 'axioms.lean']:
            put(mutant / 'scripts' / name, (REPO / 'scripts' / name).read_text())
        path = mutant / 'scripts/axioms.lean'
        source = path.read_text()
        old = 'unless axioms.all allowed.contains do'
        self.assertEqual(source.count(old), 1)
        path.write_text(source.replace(old, 'unless axioms.all (fun a => allowed.contains a || true) do'))
        code, output = audit_case('mutant-external', 'external', mutant)
        self.assertEqual(code, 0, output)
        self.assertIn('externalAssumption', output)

if __name__ == '__main__':
    unittest.main()
