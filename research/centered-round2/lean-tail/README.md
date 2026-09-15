# Factorial-weighted finite tail — verified private stage

## Outcome and exact scope

`Sendov/Analytic/PaperFactorialTail.lean` contains 19 proved theorems in
`Sendov.PaperFactorialTail`, using only Mathlib imports. There is no dependency
on another research stage or on the root Sendov sources.

The strongest paper-facing theorem is `coefficient_tail_rpow`. For arbitrary
natural m,K with K≤m, real v,x,A,S, v≥0, x≥0, S≥0, and the honest hypotheses

```
∀ k ∈ Finset.Ico K (m+1),
  C k ^ 2 ≤ (2*(k:ℝ)+1) * (m.choose k:ℝ) * v^k

∑ k ∈ Finset.Ico K (m+1),
  (2*(k:ℝ)+1)/(k.descFactorial K:ℝ) ≤ S,
```

it proves

```
∑ k ∈ Finset.Ico K (m+1), C k * x^k * A^(m-k)
  ≤ sqrt(S * (m.descFactorial K:ℝ)) * (x*sqrt(v))^K
      * (A^2 + v*x^2)^((m-K:ℕ)/(2:ℝ)).
```

The exponent uses real division, not truncated natural division. Neither C nor
A needs a sign hypothesis. The statement includes v=0, x=0 and m=K.
`coefficient_tail_le` represents the final half-power as
`sqrt ((A^2+v*x^2)^(m-K))`; `sqrt_pow_eq_rpow` proves the equivalence.

`coefficient_tail3_le` and `coefficient_tail4_le` require **only** the coefficient
hypothesis in addition to m≥3/4, v≥0 and x≥0. They discharge the weight premise
with S3=9/4 and S4=5/9 respectively.

## Structural mathematics

* `descFactorial_mul_choose`: division-free factorial/binomial shift, all K≤k.
* `factorial_binomial_moment`: for all K≤m and arbitrary real X,Y,
  the finite sum of `(k)_K choose(m,k) X^k Y^(m-k)` is exactly
  `(m)_K X^K (Y+X)^(m-K)`.
* `factorial_weighted_cs`: squared Cauchy–Schwarz with reciprocal falling
  factorial weights, under an explicit uniform square-coefficient bound.
* `factorial_tail_sq`, `factorial_tail_le_sqrt`: combine that CS argument with
  the exact moment and an arbitrary certified upper weight bound S.
* `weight3_step`, `weight3_sum`, `weight3_sum_le`: uniform telescoping, giving
  `9/4 - 2/(m-1) - 1/(2*m*(m-1)) ≤ 9/4`.
* `weight4_step`, `weight4_sum`, `weight4_sum_le`: uniform telescoping, giving
  `5/9 - 1/((m-1)*(m-2)) - 1/(3*m*(m-1)*(m-2)) ≤ 5/9`.
* `rescale_coefficient_bound`: safely absorbs x^k into the supplied coefficient
  inequality, producing the moment variable X=v*x².

These are all-degree identities and inequalities, not evaluated degree tables.
General-K telescoping beyond K=3,4 is not claimed; the general tail theorem
accepts any separately proved finite weight bound.

## Verification and receipts

Run in place:

```
python3 /home/v-zhouziyu/work/sendov-paper-formalization-20260914-remaining-centered/research/centered-round2/lean-tail/verify.py
```

The final execution returned PASS:

* fresh main-module compile, exit 0;
* main-module `leanchecker`, exit 0;
* fresh `TailAudit` compile, exit 0;
* `TailAudit` `leanchecker`, exit 0;
* complete explicit inventory: all 19 theorem axiom sets are precisely subsets
  of `{propext, Classical.choice, Quot.sound}` (in this run all three occur);
* no `sorry`, `admit`, `native_decide`, or custom axiom in the theorem source.

`verification.json` records theorem names, source/object SHA-256 values and
these exact receipt paths:

```
.lake/paper/logs/final-Sendov.Analytic.PaperFactorialTail.json
.lake/paper/logs/final-Sendov.Analytic.PaperFactorialTail-kernel.json
.lake/paper/logs/final-TailAudit.json
.lake/paper/logs/final-TailAudit-kernel.json
```

Matching `.log` files retain real compiler/kernel output and printed contracts.
The main source SHA-256 at verification was
`2f5307297d5e0c91403842ba2ff7e0e7c298cf99f6a61687f8687c509eed2c19`.

All compilation used the requested pinned `check_paper.py`/config, a private
complete symlink object stage and one Lean thread. Final verification unlinks
all target output variants before writing. Imported cache files were read-only.
An attempted aggregate `Mathlib.Tactic` import was unavailable in the pinned
cache; focused tactic imports resolved this without a Lake build.

## Remaining assembly (parent-owned)

1. Copy the standalone source into the root at
   `Sendov/Analytic/PaperFactorialTail.lean`, then freshly recheck there.
2. Discharge `hcoeff` using the separate binomial-mode worker's result for the
   actual `PaperCenteredBound.C m k v`. This stage intentionally does not assume
   that result has already been integrated or verified.
3. Set x=a*t (or norm(a)*t for the existing complex-a norm formulation),
   A=norm(1-a*μ*t), v equal to actual centered variance.
4. Combine pointwise `coefficient_tail3_le`/`coefficient_tail4_le` (or
   `coefficient_tail_rpow`) with `PaperCenteredTail.majorant_block_le_integral`;
   interchange the finite sum and integral and factor the nonnegative constants.
   Supply continuity/integrability and use the actual-variance identity
   A²+v*(a*t)²=1-2*a*Re(μ)*t+a²*s*t² in the real-a case.
5. The resulting T3/T4 bound still does **not** prove the open uniform scalar
   consumer or the positive-variance C-near budget.

## Reusable proof workflow

Use `Finset.sum_sq_le_sum_mul_sum_of_sq_le_mul` directly on the original
summands: this avoids introducing square roots and division normalizations
inside the finite CS proof. Shift factorial/binomial coefficients via
`Nat.choose_mul`, and reindex using `Finset.sum_Ico_eq_sum_range` before
`add_pow`. For concrete reciprocal weights, use a discrete antiderivative and
`Finset.sum_Ico_sub`, normalizing shifted real denominators before
`field_simp`. Extract the final square root only after the squared structural
bound is established. Keep a square-root-of-natural-power formulation alongside
rpow so parity and endpoint continuity remain explicit.
