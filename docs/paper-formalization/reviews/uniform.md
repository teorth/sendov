# Independent semantic audit — PASS

**Exact commit:** `1108d11ee7e6c1d231d41c91607745e0330dcbc2`  
**Tree:** `b523f240810971abca6ff8eaa0ea500c242d3831`

## Verdict and evidence boundary

**PASS** for FULL natural `m ≥ 256` `uniform_D`, its actual large-degree first-origin consumption in `Interior → Conjecture → Solution`, historical `T < 3/5`, and the `m=5,6` norm-J margins. **No actual theorem mismatch found in these targets.**

All repository source inspected came from immutable `git show <exact-commit>:<path>` blobs. This was a read-only semantic review, not a new Lean build or kernel replay. The parent supplied successful exact-candidate compilation/kernel checks and Kernel3/proof-value independence results; I independently inspected theorem types, proof bodies, integral definitions, caller discharge, and the corresponding proof-value audit code. Exact rational arithmetic below was independently executed with Python `Fraction`. Repository status was empty before and after inspection; commit/tree identity was rechecked. No source, build, cache, or remote operation was performed by this review. The only authored file is this report.

## 1. Public D contract and actual integrals

`Sendov/Analytic/PaperUniform.lean:150–186` proves, for **every natural** `m ≥ 256`, all real `0 < a < 1` and `−1 ≤ x ≤ 1`, from `RawPolar m a x` alone:

`PaperTaylor.budget (m : ℝ) a x < 1 − (m : ℝ)*a/((m : ℝ)+1)`.

The definitions are literal, not assumed approximations:

- `PaperPolar.lean:24–38`: raw polar is `1 ≤ ∫₀¹ P(t)^(m/2) dt`, with `P(t)=a²+2a(1−a²)xt+(1−a²)²t²`; `raw_kernel_eq` and `rawPolar_iff` identify the existing `Sendov.Ppolar` exactly.
- `PaperTaylor.lean:19–24`: `β(t)=1−2axt+a²t²`; `T=β(1)^(m/2)+ma²∫₀¹ tβ(t)^((m−1)/2)dt`.
- `PaperTwoEnd.lean:24–45`: genuine substitution `u=at` proves `total_eq_budget`, including both factors of `a` from the Jacobian and weight. The endpoint is `Q(x,a)^(m/2)`, not an independently chosen scalar.
- `PaperLaplace.lean:74–126,146–271`: the first and cubic exponential moments have explicit finite-endpoint primitives; interval monotonicity and an actual split at `x/(2a)` establish the sharp bound on this same T. Continuity/integrability, split location, endpoint positivity, and cancellation factors are proved. Only the decaying majorants are extended/bounded, not a growing quadratic integrated to infinity.

There is no first-origin, polynomial existence, endpoint estimate, tail bound, finite-degree table, `α≤17`, `s<1`, or open-disk assumption in the public D type. Both x-boundaries are retained. Natural odd and even degrees, including exactly 256, use real exponents without parity substitution.

## 2. Complete all-a partition, including seams

The actual priority partition in `uniform_D` is:

| Region selected by the proof | Consumed closure |
|---|---|
| `a ≤ 1/3` | proved `T < 2/3`, then `PaperBulk.direct_budget_small` |
| `1/3 < a ≤ 4/5` | proved retained estimate `T < 16/(ma²)+24/m`, then positive middle cubic |
| `4/5 < a`, `49 ≤ λ` | retained estimate, `large_ray_budget`, and strict `1−a < B` |
| `4/5 < a`, `λ < 49`, `λ ≤ 2/5` | `near_endpoint_D`: `B−T > (1−a)/1000 > 0` |
| `4/5 < a`, `2/5 < λ < 49` | `finite_rays_D` |

Here `λ=m(1−a)>0`. Thus `a=1/3`, `a=4/5`, `λ=2/5`, and `λ=49` are included; no uncovered seam exists. `finite_rays_D` itself accepts the closed interval `[2/5,49]`, with branches ending at 1, 10, 25, 49. Its `[1,10]` lower-budget proof splits at 5, and the `[1,5]` helper splits at 2, also without an open gap.

**Intentional difference from round5, not a contract defect:** the first finite-ray interval is `[2/5,1]`, not the report's `[1/5,1]`. The separately proved near theorem covers everything through `2/5`, including the omitted `[1/5,2/5]`. The resulting full D domain is unchanged. This is explicitly documented in `PaperRayGeometry.lean:12–14,202–238`; it does not misstate the narrower helper as the original paper interval.

The retained middle cubic is proved positive on the entire closed `[1/3,4/5]`, using a positive polynomial decomposition (`PaperBulkAlgebra.lean:17–43`). Strictness is maintained even when the large-ray scalar comparison is non-strict.

## 3. Analytic estimates are discharged and genuinely consumed

The source proof chain is:

- `RawPolar → integral_le_exp / b_le_alpha / geometry` (`PaperPolar.lean:67–158`).
- Exact affine polar integration, logarithmic comparison, and small-delta rational bound prove the global endpoint `E≤4/(m+2)` and `mx²>19/2` (`PaperGlobalPolar.lean:24–79,148–227`). The small-delta branch does not assume an alpha cap.
- Two-endpoint integration proves separated and unrelaxed middle estimates (`PaperTwoEnd.lean:63–113,165–205,207–378`). `PaperUniform.middle_relax` weakens the unrelaxed exponent only under `m≥256`; it does not illicitly strengthen the historical `exp(−k/3)` estimate.
- Fixed rational Taylor lower certificates and proved exponential monotonicity supply the actual tails and global two-thirds/retained bounds (`PaperTail.lean:8–140`; `PaperUniform.lean:24–117`). These are uniform in degree, not sample checks.
- Finite-ray geometry derives its endpoint and x bounds from raw polar. Through λ=25 it uses the proved rational polar estimate; at 49 it proves an exponential integral obstruction and interpolates by convexity (`PaperRayGeometry.lean:38–184`). The altered rational geometry is a valid replacement for the paper's sinh-root route.
- `PaperTail.budget_region_one/two/three/four` apply the sharp Laplace theorem with proved geometry, then `finite_rays_D` composes those strict T upper bounds with independently proved bounds on the true scaled B. Generic helper premises are explicitly discharged at these calls.

Independent exact arithmetic confirmed all five consumed base budget gaps positive: `4179/164480`, `21851/328960`, `178589/197376`, `205583/263168`, `130417/131584`. The uniform separated/middle comparisons to `2/3` have positive rational gaps `374/2451` and `169/26448` respectively.

`tests/PaperUniform.lean:56–98` traverses opaque proof **values**, not just types/imports, from the expanded-integral wrapper, checks only standard logical axioms, and requires positive reachability of the global bounds, two-endpoint estimates, tails, bulk, near, all four finite-ray upper/lower consumers, and split geometry. The inspected source bodies establish those same substantive edges. Static scans of the project-local import closures of Uniform, HistoricalBounds, Margins and FirstOriginBudget found no `axiom`, `sorry`, `admit`, `sorryAx`, `native_decide`, `unsafe`, or `implemented_by` tokens outside comments; these scans are supplementary, not substitutes for the parent's kernel checks.

## 4. Actual Interior and final public wiring

`FirstOriginBudget.lean:79–99` is a real contradiction consumer:

1. From `n≥257`, `omega` proves `256≤n−1` in naturals.
2. `Nat.cast_sub` with proved `1≤n` establishes `((n−1 : ℕ) : ℝ)=(n : ℝ)−1`; no truncated-subtraction ambiguity remains.
3. `rawPolar_iff` transports the actual existing polar integral to `RawPolar (n−1) a x`.
4. `uniform_D` gives strict `T<B`; `lower_budget` gives `1≤T+a(n−1)/n`; rewriting `(n−1)+1=n` yields the contradiction.

The first-origin integral upper bound is an explicit premise of that *consumer*, but is **proved at the production call site**, not added to Sendov's public hypotheses. `Interior.lean:94–121` obtains full polar from the two polynomial factorizations and the closed-disk Möbius inequality, relaxes it by AM–GM, derives mean coordinates and `−1≤x≤1`, then calls `uniform_contradiction` when `257≤n`. The required upper bound comes from `FirstOriginSmall.norm_integral_Fprod_le_of_factorization`, which calls the proved first-origin identity and closed-disk product norm bounds (`FirstOriginSmall.lean:49–66,144–155`; `Counterexample/Identities.lean:201–281`).

The centroid coordinates used here are simply the q mean; they are not the polynomial centroid identity. Polynomial centroid/second-origin/old incompatibility are only constructed in the later remaining-region branch (`Interior.lean:130–141`). The standalone consumer independence audit checks their absence (`tests/FirstOriginBudget.lean:7–28`). The whole Solution still legitimately has the old branch for the residual degrees/radii; this does not contaminate the large-degree first-origin branch claim.

`tests/FirstOriginWiring.lean:14–36` traverses both final theorem proof values and requires `uniform_contradiction` and `uniform_D` as reachable constants. Actual calls run through `sendov_interior_real`, the rotation transport in `Conjecture.lean:113–126`, and `Solution.lean:30–42`.

Public conclusions remain exact:

- Interior: a critical point at **strict** distance `<1`.
- Phelps–Rodriguez: strict witness, or `‖a‖=1` and a nonzero scalar multiple of `X^n−a^n`.
- Sendov: a critical point at distance `≤1`.
- Solution hypotheses: `2≤p.natDegree`, all zeros in the **closed** unit disk, and `p.eval a=0`; no first-origin/raw-polar hypothesis escapes into them.

`Conjecture.lean` and `Solution.lean` are byte-identical to `120dd03`; all three public Interior theorem type texts are also unchanged.

## 5. Historical T and nonvacuous small-degree margins

**Historical PASS.** `PaperHistoricalBounds.budget_lt_three_fifths` (`:89–114`) states the actual T bound for all naturals `m≥512`, `0<a<1`, closed `−1≤x≤1`, and raw polar alone. It uses its own `mx²>32/3`, original `exp(−k/3)` relaxation at valid degrees, and strict fixed Taylor certificate; it is not an inference from the weaker conclusion `T<B`. `budget_lt_forty` retains the historical `a≥2/5` domain. The proof-value audit explicitly requires these quantitative dependencies and rejects `PaperUniform` dependencies (`tests/PaperHistoricalBoundsTests.lean:98–141`). A formal raw-feasible boundary witness `m=512,a=2/5,x=1` is present in that test. No added first-origin premise is involved.

**Margins PASS.** `FirstOriginMargins.norm_J_six` and `norm_J_seven` (`:242–282`) quantify only `0<a<1`, a multiset of respectively five/six closed-disk q values, and the full product-of-norms polar integral. They prove:

- `1+(3/40)(1−a) ≤ ‖6∫₀¹ Fprod(a,q,t)dt‖`;
- `1+(31/160)(1−a) ≤ ‖7∫₀¹ Fprod(a,q,t)dt‖`.

There is **no** first-origin identity, polynomial factorization, or `‖J‖≤1` premise. The quantitative proof derives the mean-half bound from polar, proves actual-T gaps from A5/A6 polynomial remainders, and uses `lower_budget_norm`, which retains the actual norm instead of assuming its upper bound. Exact coefficient conversion gives `(1/16)(6/5)=3/40` and `(93/560)(7/6)=31/160`. The public scalar T definitions retain the real exponents `5/2,2` and `3,5/2` in their proper places. The margin audit rejects first-origin/old contradiction consumers and positively requires the quantitative remainder chain (`tests/FirstOriginMargins.lean:75–140`).

Independent nonvacuity check: take `a=9/10`, every q equal to 1, and cardinality m. Then full polar equals `((a+1−a²)^(m+1)−a^(m+1))/((1−a²)(m+1))`. Exact rational computation gives `60297847939/60000000000 > 1` for m=5 and `7103906425351/7000000000000 > 1` for m=6. Their actual J norms are `111111/100000` and `1111111/1000000`, respectively, and satisfy the claimed margins. Thus these hypotheses have concrete closed-disk models and are not strengthened into a contradictory first-origin domain. The same a,x=1 gives raw-feasible examples at m=256 and m=512 as well.

## Scope conclusion

No blocker or theorem mismatch in the requested contracts. The difference in the first finite-ray boundary is compensated by a proved overlapping near region, not by an assumption. Historical and norm-J quantitative results remain substantive standalone theorems. This verdict does not assert completion of peripheral diagnostics/rates or the all-paper ledger, and requests no unrelated changes.
