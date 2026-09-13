# Sendov's conjecture in Lean

This local development proves **Sendov's conjecture** and the full
**Phelps–Rodriguez equality classification**. The statements of record are
`SendovConjecture.sendov` and `SendovConjecture.phelps_rodriguez` in
[`Solution.lean`](Solution.lean), with the original specifications retained in
[`Challenge.lean`](Challenge.lean). The latter contains the original two
statement placeholders and is not imported by the proof.

For every complex polynomial of degree at least two whose zeros lie in the
closed unit disk, every zero has a critical point at distance at most one.
The distance is strictly less than one unless the distinguished zero lies on
the unit circle and the polynomial has the stated nonzero scalar-multiple
form. There is no extra numerical, genericity, degree-bound, or simple-root
hypothesis in either final theorem.

## One active proof route

The polynomial identities, analytic reduction, low-degree argument and boundary
classification start from Terence Tao's formalization.[1] The scalar endgame
here is a Lean implementation of Senjian An's rational-envelope and
low-degree critical-polynomial method, not an import of its Python checks as
trusted facts.[2]

| Part | Active source |
|---|---|
| Final statements and rotation | [`Solution.lean`](Solution.lean), [`Conjecture`](Sendov/Conjecture.lean) |
| Unit-circle boundary and equality case | [`Boundary`](Sendov/Boundary.lean) |
| Interior degrees `2 ≤ n ≤ 5` | [`LowDegree`](Sendov/Analytic/LowDegree.lean), [`Interior`](Sendov/Interior.lean) |
| Original polar/origin hypotheses → scalar domain and lower bound | [`CubicScalar`](Sendov/Reduction/CubicScalar.lean) |
| Strong hyperbolic bound and cubic polar envelope | [`DistillationHyperbolic`](Sendov/Common/DistillationHyperbolic.lean), [`CubicPolar`](Sendov/Reduction/CubicPolar.lean) |
| Two-chord integral estimate and regularized factors | [`TwoChord`](Sendov/Common/TwoChord.lean), [`DistillationMajorant`](Sendov/Common/DistillationMajorant.lean) |
| Finite critical-point certificates | [`DistillationFinite`](Sendov/Common/DistillationFinite.lean), [`generated modules`](Sendov/DistillationFinite) |
| Real-parameter tail using the actual base certificate | [`DistillationTailBound`](Sendov/LargeDegree/DistillationTailBound.lean) |
| Complete contradiction | [`DistillationBounds`](Sendov/Common/DistillationBounds.lean), [`Reduction/Main`](Sendov/Reduction/Main.lean) |

The convention is **`m = n - 1`**. The finite proof covers all `5 ≤ m ≤ 81`;
the tail is proved for every real `m ≥ 81` and uses the certified `m=81` case.
The final degree split uses the finite proof through `n=82`, then the tail.
Both are parts of the same scalar argument.

Each finite case uses the complete critical polynomials of degrees **7, 7, 4**.
Exact Bernstein identities prove derivative signs on the full outer intervals;
a mixed-endpoint estimate covers the central bracket. The proof does not assume
that a numerical root finder found all critical points. Closed endpoints and
empty outer intervals are handled explicitly.

The old `R`-based finite/large-degree certificate system and its specialized
generators are retired, not shipped as a second compatibility route. General
lemmas still used by the new proof remain. The mean/variance budget formulation
also incorporates an idea examined in Pickhardt's work; no conditional Sendov
claim or assumed threshold from that project is used.[3]

## Build and verify

Use the versions pinned by [`lean-toolchain`](lean-toolchain) and
[`lake-manifest.json`](lake-manifest.json):

```sh
lake exe cache get
lake build
lake env lean scripts/axioms.lean
```

The mathematical proof uses only `propext`, `Classical.choice`, and `Quot.sound`.
No project axiom, `sorry`, `native_decide`, or floating-point computation is used
in the proved library. Kernel replay, original headline-type comparison and
actual proof-dependency checks are separate acceptance steps; compilation alone
is not reported as all of them.

See [`docs/getting-started.md`](docs/getting-started.md) for verification and
[`scripts/GENERATORS.md`](scripts/GENERATORS.md) for reproducible generation.
The finite generator emits the entire table in one command to a fresh output
root. Python prepares exact data; Lean verifies the complete identities and
inequalities. A successful generator run is **not** a completed proof check.

## Provenance and scope

This is a local adaptation, not a claim that upstream maintainers reviewed or
endorsed these changes. The repository keeps the original Apache-2.0 code
license. The distilled mathematics and certificate table are attributed to
Senjian An's fixed source version; the source paper is CC BY 4.0.[2]
The retained generator entry points incorporate applicable portability fixes;
obsolete batch-specific tools are not retained merely to preserve a PR surface.[4]
Only contributions serving the active proof and its reproducibility are kept.
Unverified theorem corpora, numerical demonstrations, unrelated visualization
programs and obsolete generator interfaces are not part of the proof deliverable.

See [`docs/design.md`](docs/design.md) for the reduction contract and trust boundary.

## Sources

[1] https://github.com/teorth/sendov
[2] https://github.com/SJanPerth/Sendov-Proof-Distillation/tree/e8ae601491ec171ab4f7f8456113dd6a047aa85d
[3] https://github.com/pickhardt/sendov-explicit-threshold
[4] https://github.com/teorth/sendov/pull/1
