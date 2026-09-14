# Paper formalization acceptance ledger

Baseline: `0a4e966c41e1287f92d305d3bad8e70c8c295dde`.
Integration branch: `formalize/paper-results-20260914`.
Status: **IN PROGRESS**, not complete and not a uniform D proof.

## Checkpoint 2 — actual near-endpoint D, now wired into Solution

`PaperNearClosure.near_endpoint_D` proves the actual raw-polar integral
implication for every natural m≥7 and m(1-a)≤2/5, with strict gap >h/1000.
The two-endpoint integral bounds, sharp Laplace estimate, curvature secant
and its sufficient D gate, finite complex centered expansion, and optimized
coefficient bounds have also been integrated and freshly checked (24 gates).
The centered actual-coefficient budget and independent optimized coefficient
bound still need their common majorant interface; this is in the next batch.

`FirstOriginBudget.lower_budget` connects the scalar integral to actual Fprod.
`Interior` now branches into the new near-endpoint contradiction before
constructing the polynomial centroid and second-origin identities. Both
public Solution proof-value closures contain `near_endpoint_D`; the standalone
near contradiction's closure excludes all old centroid/second-origin/endgame
entries. Exact final sources passed the `near-wiring-clean` gates. The original
remaining-domain proof is retained; no all-a m≥256 Lean claim is made yet.

Next dispatched items: global polar endpoint/log bounds, quantitative tails,
ray geometry, centered majorant assembly, older stronger near margins, exact
full-complex-polar diagnostic, and independent semantic review of checkpoint2.

## Checkpoint 1 — integrated and freshly rechecked

Boundary rigidity and first-origin n=6/n=7 are now actual consumers of both
public Solution theorem proofs. The real-collinear moment theorem is exported
independently; it is not a proof dependency of the general complex theorem.
`PaperPolar`, `PaperTaylor`, and `PaperNearAlgebra` are now integrated, with
actual raw-integral domination, actual integral Taylor budget, and the full
rational near-endpoint rectangle respectively. Parent replay passed 60 gates
(34 elaborations, 26 independent kernel checks); the prior bulk module gates
are separate. Ten boundary/final theorem contracts match baseline exactly.
Near-endpoint D still requires endpoint decay and parameter assembly.

The initial task allocation below is retained as the acceptance inventory;
worker assignments marked there refer to the completed first dispatch, not
claims that all enclosing targets are finished.

## Acceptance units

- Existing boundary average-square rigidity: re-integrate refined production
  source and verify Solution/Conjecture consumers. Worker `existing`.
- Existing first-origin m=5,6: integrate production namespace and verify
  complete polar/first-origin contradiction, not only scalar lemmas. Worker `existing`.
- Existing real-split collinear reciprocal/moment results: integrate and verify;
  complex affine transport and general equality classification remain distinct
  unfinished mathematics, not previously completed formalizations. Worker `existing`.
- Raw polar geometry and stronger `b ≤ α/(3+α) ≤ λ/(3+λ)`: worker `polar`.
- Finite Taylor integral budget (T): worker `taylor`.
- Latest near-endpoint rational algebra: worker `near`; full near-endpoint
  result additionally needs Taylor, parameter conversions and integer endpoint
  decay. Do not count algebra alone as raw-polar D.
- Latest near-endpoint `m≥7, m(1-a)≤2/5`, gap `>(1-a)/1000`: pending assembly.
- Old narrower near-endpoint **stronger margins**: pending preservation.
  Round3 `λ≤1/10` gap `>h/5`; round5 `λ≤1/5` gap `>h/80`.
  Weaker old cutoffs can be corollaries; stronger margins cannot be discarded.
- Two-endpoint quadratic integral estimates, polar endpoint/log lower bounds,
  sharp Laplace estimate (S), finite-ray quantitative tails: pending.
- Round5 full `m≥256` all-a theorem: pending the above analytic inputs and
  finite-ray comparisons. The all-a theorem is NOT currently formalized.
- Round4 stronger bound `T<3/5` for m≥512: preserve separately; does not follow
  merely from the weaker round5 bound `T<2/3`.
- Curvature-corrected polar secant and rational sufficient gate F_sec: pending.
  Universal positivity of F_sec was never proved and is not an acceptance claim.
- Finite centered expansion including H terms, coefficient estimate from finite
  Fourier/AM-GM, C-budget: pending. Universal C-near was never proved.
- Exact full-polar mean-half counterexample: pending Lean translation; it is
  NOT a D or Sendov counterexample.
- Rational diagnostic certificates: keep distinct from universal proofs;
  scoped certified intervals are eligible theorems, floating grids are not.

## Accepted first independent module

`Sendov/Analytic/PaperBulkAlgebra.lean` contains:

- `Sendov.PaperBulk.middle_cubic_pos`: an explicit positive decomposition,
  avoiding differentiation/concavity infrastructure for the middle interval.
- `middle_budget`: for real m≥256 and 1/3≤a≤4/5,
  `16/(m*a²)+24/m < 1-a`.
- `direct_budget_middle`: converts the explicitly hypothesized analytic bound
  on T to D. This is an honest consumer, not a proof of its analytic premise.
- `large_ray_budget`: for m>0, a≥4/5 and m(1-a)≥49,
  `16/(m*a²)+24/m ≤ 1-a`.
- `direct_budget_small`: consumes T<2/3 for 0<a≤1/3.

Production module and `tests/PaperBulkAlgebra.lean` each compiled and passed
`leanchecker`, using actual project options and private project objects.
All five named theorem axiom closures are exactly Kernel3.
Receipts: `.lake/paper/logs/bulk-final-*`.
No production root is rewired to this module yet; no speedup or net compression
is claimed.

## Verification policy

Use direct pinned Lean via the read-only-package/private-object checker at
`../sendov-research-20260914-research/paper-formalization/check.py`.
Recompile exact changed prerequisites before consumers. No shared Lake writes.
No sorry/admit/new axiom/native_decide. No umbrella `import Mathlib`.
The final acceptance must reconcile every paper result with a theorem, an
explicit corollary, a corrected paper claim, or an accurate unfinished item.
