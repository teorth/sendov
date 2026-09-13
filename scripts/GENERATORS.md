# Retained generation support

The alpha-53/47/47 certificates are self-contained Lean identities in
`DistillationPeakFirst.lean` and `DistillationPeakRest.lean`.
Their 150 ordered coefficients, 71 smaller factor coefficients, positive
scales and complete symbolic identities are checked by the kernel. They
do not need a separate generator or degree table.

The only retained generator is the useful global `sinh` proof generator.
Use Python 3.10+ with SymPy (tested with 1.13.1):

```sh
python3 -B scripts/gen_sinh.py --output /tmp/sendov-Sinh.lean
diff -u Sendov/Common/Sinh.lean /tmp/sendov-Sinh.lean
python3 -B -m unittest discover -s tests
```

Without `--output`, Sinh writes `Sendov/Common/Sinh.lean` relative to its own
repository, not the caller's cwd. Its atomic single-file writer replaces the
target only after complete rendering, preserving existing content on handled
write/rename errors. Imports perform no generation; `-B` suppresses bytecode.
This is not a power-loss durability or hostile-concurrency guarantee.

The degree-row table, validator, renderer, bundler, and tests exclusively
exercising those retired interfaces are removed. The remaining suite retains
Sinh relocation/digest/publication guarantees, the independent axiom auditor,
and actual full-alpha-identity mutation tests. Python generation is not Lean
acceptance:

```sh
lake build
lake env lean tests/NoFiniteRows.lean
sh scripts/audit.sh
```

Original headline types and independent exact-module kernel replay are
separate obligations, as described in `docs/getting-started.md`.

## Attribution

Sinh, its analytic tail and proof templates derive from Terence Tao's
development under Apache-2.0. The original notices and license copy remain.
The rational-envelope/two-chord mathematics is adapted from Senjian An,
*Proof Distillation for Sendov's Conjecture*, fixed revision
`e8ae601491ec171ab4f7f8456113dd6a047aa85d`, under CC BY 4.0.
The mathematical notice remains in `data/LICENSE-PAPER.txt`; no degree
table or separately MIT-licensed verification code remains in this tree.
