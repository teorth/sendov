# Build and verification

## Pinned environment

Install Lean through elan and use this repository's `lean-toolchain` and
`lake-manifest.json`. Do not upgrade Mathlib as part of replaying these proofs.

```sh
lake exe cache get
lake build
lake env lean scripts/axioms.lean
sh scripts/audit.sh
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

## Regenerate the selected finite certificates

Python prepares exact rational/integer data. It neither proves the final
inequalities nor replaces the Lean checks.

```sh
set -eu
out=$(mktemp -d)
python3 scripts/gen_distillation.py --output "$out/generated"
diff -ru Sendov/DistillationFinite "$out/generated/Sendov/DistillationFinite"
diff -u Sendov/Common/DistillationFinite.lean "$out/generated/Sendov/Common/DistillationFinite.lean"
python3 -m unittest discover -s tests
```

The output contains all 57 retained records (`m = 5..61`) in eight groups.
The finite aggregate consumes `m = 5..60`; the tail shares row 61 in the final
`Rows61_61` group. Use a fresh output root; generation must not replace a
nonempty directory. See [`scripts/GENERATORS.md`](../scripts/GENERATORS.md) for
the retained global `sinh` generator and its SymPy dependency.

If certificate data or generated proofs change, verify the complete affected
import cone, its kernel checks and final consumers. Do not count previously
compiled objects from a different source projection as a successful new build.

## Interpreting results

- A Python success means generation or a tool test succeeded.
- A Lean success means that particular source/module elaborated.
- A kernel success means the named module replayed over its imports.
- Full completion also requires both unchanged final contracts and their real
  proof dependencies, including every finite case and the infinite tail.

The active branch does not include the retired packed/moment/`R` certificate
system as a compatibility fallback.
