# Generic endpoint-moment transfer — verified

## Result

Namespace: `Sendov.CenteredEndpointMoment`.

`real_mean_gt_of_endpoint_moment` proves, from **original FULLpolar**, the
pointwise bounds `∀ z ∈ q, ‖z‖ ≤ 1`, and the actual mean identity
`q.sum = q.card * μ`, that

```text
0 < q.card,  0 < a < 1,  0 < X,  (q.card : ℝ) ≤ U,
∫₀¹ [a² + 2a(1-a²)Xt + (1-a²)²t²]^(U/2) dt < 1
    ⟹ X < μ.re.
```

`U` is real, not necessarily an even integer. The requested additional assumption
`X < 1` is unnecessary for this implication, so the formal theorem is stronger.
There is no assumed desired mean bound, no assigned/saturated actual second
moment, and no replacement feasibility premise.

## Analytic dependency chain

1. Imported `CenteredActualPolar.actual_moment_of_fullpolar` supplies the actual
   moment lower bound directly from FULLpolar.
2. `actualKernel_nonneg` uses the exact mean-of-squared-norms identity.
3. `kernel_le_endpoint` uses only the contradictory assumption `μ.re ≤ X`,
   `secondMoment q ≤ 1` derived from the original pointwise bounds, and the
   nonnegative coefficients for `0 ≤ t ≤ 1`.
4. `integral_rpow_le` proves probability Jensen for `x ↦ x^r`, `0 ≤ r ≤ 1`, by
   integrating its supporting-line inequality obtained from weighted AM–GM:
   `f(t)^r J^(1-r) ≤ r f(t) + (1-r) J`, where `J = ∫₀¹ f`.
   Integration uses exactly the unit interval's mass one; cancellation gives
   `∫₀¹ f^r ≤ (∫₀¹ f)^r`. The helper assumes continuous nonnegative `f` is positive
   at some point, which proves `J > 0`. For the endpoint kernel this witness is
   `t = 0`, since `a² > 0`; it is not a feasibility or mean-bound hypothesis.
5. `moment_le_upper` substitutes `r = m/U`, proving the full Lyapunov inequality
   `N_m ≤ N_U^(m/U)`. `moment_lt_one_of_upper` makes it strict below one.
6. The lower and strict upper bounds contradict each other under `μ.re ≤ X`.

This closes exactly §2's basic endpoint-moment transfer, not the optional
actual-second-moment defect strengthening in equation (2.3).

## Generic Bernstein consumer and exact remaining interface

`bernsteinWeight N k r = (N.choose k : ℝ) * r^k * (1-r)^(N-k)`.
The module proves nonnegativity on `[0,1]` and partition of unity by the binomial
theorem. `weighted_sum_le` / `weighted_sum_neg_of_le` accept any finite
nonnegative weights summing to one and a common (strictly negative) coefficient
bound. `weighted_sum_neg` also accepts individually strict negative coefficients.

`lt_one_of_bernstein` proves `J h < 1` for **every real** `0 < h ≤ H` from an exact
Bernstein representation of `(J(h)-1)/h`, with its polynomial extension at zero.
No sampling is used. Continuity of `J` need not be separately assumed because
the exact identity is already stronger.

An instantiated polynomial proof must construct:

```lean
EndpointBernsteinCertificate (n N : ℕ) (X H : ℝ)
```

with exactly these fields:

```lean
coeff : ℕ → ℝ
coeff_neg : ∀ k ∈ Finset.range (N+1), coeff k < 0
integral_identity : ∀ h ∈ Set.Icc (0 : ℝ) H,
  (∫ t in (0 : ℝ)..1, endpointKernel (1-h) X t ^ n) =
    1 + h * ∑ k ∈ Finset.range (N+1),
      coeff k * bernsteinWeight N k (h/H)
```

The natural power makes exact polynomial expansion/integration available to the
future certificate generator. **Both** the exact integral identity and all finite
coefficient signs must be proved in Lean; a rational replay or a coefficient list
alone does not discharge the interface. The usual parameters may take `N=4*n-1`,
`H=1/10`, and rational `X`, but no such specialization is made here.

`C.upper_moment_lt_one hH h hh` bridges the natural power `n` to the real exponent
`(2*(n : ℝ))/2`. `real_mean_gt_of_bernstein` composes this with original FULLpolar
and proves `X < μ.re` uniformly for `0 < h ≤ H`, `h < 1`, and
`0 < q.card ≤ 2*n`. This is the ready-to-use end-to-end generic consumer.

No concrete endpoint certificate or degree-specific constants are included.

## Files and verification

- `Sendov/Analytic/CenteredEndpointMoment.lean`: Jensen/Lyapunov and FULLpolar transfer.
- `Sendov/Analytic/CenteredBernsteinMoment.lean`: finite-weight signs, real Bernstein
  weights, certificate structure, and end-to-end consumer.
- `Sendov/Analytic/CenteredMomentAudit.lean`: explicit axiom inventory.
- `check.py`: isolated full project object overlay seeded from round4/lean-polar;
  authenticates the actual-moment source/object against its compile and kernel
  receipts, and unlinks target artifacts before compilation.
- `verify.py`: fail-closed source/object/receipt and exact axiom-inventory audit.
- `receipts/`, `.lake/paper/logs/`: source/object hashes and actual check outputs.

All three Lean modules freshly compile without warnings and pass `leanchecker`.
`verify.py` returns `PASS`: three compile checks, three kernel checks, and sixteen
axiom queries, all using only `propext`, `Classical.choice`, and `Quot.sound`.
No prohibited proof shortcuts or custom axioms occur in owned Lean sources.

Reproduction (absolute paths):

```text
python3 /home/v-zhouziyu/work/sendov-paper-formalization-20260914-remaining-centered/research/centered-round5/lean-moment/check.py Sendov.Analytic.CenteredEndpointMoment
python3 /home/v-zhouziyu/work/sendov-paper-formalization-20260914-remaining-centered/research/centered-round5/lean-moment/check.py Sendov.Analytic.CenteredBernsteinMoment
python3 /home/v-zhouziyu/work/sendov-paper-formalization-20260914-remaining-centered/research/centered-round5/lean-moment/check.py Sendov.Analytic.CenteredMomentAudit
```

Repeat each check with `--kernel`, then run `verify.py` by its absolute path.

## Environment issue and reusable local approach

The pinned package cache lacks `Mathlib.Analysis.Convex.Integral`,
`Mathlib.Analysis.Convex.SpecificFunctions.Pow`, and
`Mathlib.RingTheory.Polynomial.Bernstein` objects. No external package/cache was
built or edited. The supporting-line proof uses the already available
`Mathlib.Analysis.MeanInequalities`; Bernstein weights and their partition of
unity are proved directly from `add_pow`. This provides the intended mathematics
without introducing an external build dependency. All deliberate writes are
inside this owned directory; no commit or push was performed.
