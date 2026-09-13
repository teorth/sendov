# Build and verification

## Pinned environment

Install Lean through elan and use this repository's `lean-toolchain` and
`lake-manifest.json`. Do not upgrade Mathlib as part of replaying these proofs.

```sh
lake exe cache get
lake build
lake env lean scripts/axioms.lean
sh scripts/audit.sh
lake env lean tests/NoFiniteRows.lean
python3 -B -m unittest discover -s tests
```

The default build includes `Sendov`, `Solution`, and the original `Challenge`
specification. `Solution.lean` supplies the two exact statement-of-record
declarations. The two intentional `Challenge.lean` holes are specification
placeholders, not imported proof dependencies.

## Independent kernel replay

A successful elaboration is not the same check as independent kernel replay.
After the build, the installed toolchain can replay each project module:

```sh
set -eu
python3 -c 'from pathlib import Path; print("\n".join(".".join(p.with_suffix("").parts) for p in sorted(Path("Sendov").rglob("*.lean"))))' |
while IFS= read -r module; do
  lake env leanchecker --verbose "$module" || exit 1
done
lake env leanchecker --verbose Solution
```

The import-only `Sendov.lean` facade has no local theorem to replay. Checking
`Solution` alone does not replay every imported project theorem, which is why
the loop covers the proof modules separately. These checks use the pinned
imported environment; they are not described as a fresh re-proof of Mathlib.

The final theorem types must also agree with the original specification.
[`comparator.json`](../comparator.json) records the public comparison targets.
Axiom checks, independent kernel replay, type comparison and actual proof
consumption address different questions and are not interchangeable.

## Reproducible certificates and regressions

The alpha-53/47/47 identities are self-contained Lean source, including every
coefficient and homogeneous factor. There is no finite-degree table or row
generator. No Python computation is a mathematical premise.

```sh
set -eu
for probe in tests/*.lean; do
  lake env lean -DwarningAsError=true "$probe"
done
python3 -B -m unittest discover -s tests
```

The full scalar domain is every real `m >= 5`, `0 < alpha <= 17`,
`2*alpha <= m`; there is no numerical degree base or finite tail cutoff.
`NoFiniteRows` checks complete recursive proof-value closures, requiring actual
small/middle/large-alpha consumption in all four roots. The Python suite
contains real Lean negative coefficient/scale/interval controls and the complete
independent auditor fixture matrix. Run compilers serially.
See [`scripts/GENERATORS.md`](../scripts/GENERATORS.md) for the retained global
`sinh` generator and its SymPy dependency.

If certificate data or generated proofs change, verify the complete affected
import cone, its kernel checks and final consumers. Do not count previously
compiled objects from a different source projection as a successful new build.

## Interpreting results

- A Python success means generation or a tool test succeeded.
- A Lean success means that particular source/module elaborated.
- A kernel success means the named module replayed over its imports.
- Full completion also requires both unchanged final contracts and their real
  proof dependencies, including all three full-degree-ray alpha estimates.

Lake enumerates every `Sendov` source module explicitly through its root glob,
including useful common mathematics outside the final theorem import cone.
Retired degree-row objects and sidecars must not be available as a fallback;
never delete dependency-package caches when retiring project artifacts.
