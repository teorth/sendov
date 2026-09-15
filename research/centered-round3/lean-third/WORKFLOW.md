# Reusable workflow: finite-weight near-regime extensions

This note is local to the owned stage; it does not modify another profile or a global skill.

## Preserve the analytic improvement through every interface

- Instantiate the generic factorial-tail theorem with the exact finite `weight3_sum`, not the convenient `9/4` upper bound. Otherwise eta disappears before the chord integral and cannot be recovered downstream.
- Reuse the original `C_sq_le_binomial` theorem to discharge the generic coefficient hypothesis; do not change `C` or replace its coefficients by actual coefficients.
- Retain `a^4` and the actual norm of the mean through the normalized-H integral and chord estimate. Only apply the joint eta/fourth-power saving at the scalar consumer.
- Use the actual moment inequality `u²+v≤1` when bounding `u*sqrt(v)`. A separate bound on `sqrt(v)` discards the gain needed at lambda=1/3.
- Keep `a=1-h` until the `m*(Q-a/2)` calculation. Freezing a at its global lower bound spends the finite-degree saving incorrectly.
- Keep the B₂ endpoint exponents separate for j=0,1,2. Replacing all of them by the smallest exponent gives a coarser base constant that need not meet the desired budget.

## Lean arithmetic lessons

- Normalize variable-denominator expressions consistently with `ring_nf at selected_hypotheses ⊢` before `nlinarith`; `4/(9*m)` and `(4/9)*(1/m)` otherwise become unrelated atoms to the tactic.
- Use `linear_combination` when the desired inequality is exactly the sum of scaled hypotheses containing divisions. Its ring normalization can close goals that a bare `nlinarith` misses.
- Supply explicit natural exponents to `pow_nonneg` inside unannotated `have` declarations, so Lean does not leave exponent metavariables unresolved.
- Rewrite a power via a local identity such as `rho^m = rho^(m-1)*rho`, rather than globally rewriting every occurrence of m. Global substitution also changes truncated-subtraction exponents and casts.

## Isolated verification

- Pin the original project path explicitly; do not infer it from the deeper stage nesting.
- Use the complete frozen object overlay as the base and private regular outputs for all new modules. Unlink each target's artifacts before compilation, never write through an imported-object symlink.
- Bind kernel receipts to both source and object hashes from a successful compilation receipt. A failed compile must not leave an old target object available to produce a misleading kernel success.
- Rebuild the small new DAG in topological order; no full-project rebuild is needed.
- Enumerate all new lemmas/theorems programmatically and require exact axiom-audit coverage. Verify every reported source hash and every frozen-manifest entry before claiming completion.
- Distinguish completed headline consumers from conditional scalar interfaces: this stage closes the FULLpolar consumer; its lower-level scalar hypotheses are all supplied in `C_near_raw_middle`.
