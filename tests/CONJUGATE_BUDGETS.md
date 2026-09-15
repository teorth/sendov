# DI03–DI07 exact conjugate budgets

**Accepted: 5. Incomplete: 0.**

| ID | m | a | x | Compile | Independent kernel |
|---|---:|---|---|---|---|
| DI03 | 6 | 9/10 | 49/50 | PASS | PASS |
| DI04 | 8 | 99/100 | 497/500 | PASS | PASS |
| DI05 | 20 | 9/10 | 83/100 | PASS | PASS |
| DI06 | 100 | 9/10 | 61/100 | PASS | PASS |
| DI07 | 100 | 99/100 | 22/25 | PASS | PASS |

`tests/PaperConjugateBudgets.lean` exports `Budgets.DI03_closed` through
`Budgets.DI07_closed` and `Budgets.all_datasets_closed`. The latter proves
acceptance for every entry of the exact rational input registry;
`Budgets.dataset_count` proves its length is five.

The common `Accepted` contract includes the actual family cardinality, all
pointwise norms equal to one, actual mean and centered variance, full complex
polar norm greater than one, literal `PaperCenteredBound.majorant_Efin + Gamma`
strictly below `1 - a * norm(mean)`, and the actual first-origin `norm J > 1`.
The full polar integral is evaluated exactly, not replaced by its AM–GM bound.
The m=8 exact integral and full-polar result are independently reusable as
`Sendov.PaperConjugate.DI04.polar_integral` and `.full_polar`.

## Certificate method

- `family n x` is the multiset containing n copies of each of
  `x ± i * sqrt(1 - x^2)`; multiplicities are never erased.
- `PaperConjugate.variance_family` proves the actual centered variance is
  `1 - x^2`; `budget_eq` binds the scalar arithmetic back to the literal PAPER
  square-root definition.
- Compute each real B endpoint by one binomial recurrence, checked in Lean.
  Retain `abs(1-B)` in every term, including k=m.
- Bound `sqrt(s) / d * abs(h)` by b using the exact rational certificate
  `s * h^2 ≤ (b*d)^2`, with `s ≥ 0`, `d > 0`, `b ≥ 0` proved in Lean.
  This eliminates the need for separately rounded square-root envelopes.
- All 224 finite-tail terms across the five families are checked. The chosen
  per-term bounds are deliberately coarser than the research script's displays;
  each final strict PAPER budget is nevertheless proved.
- Exact polynomial coefficients are generated, their expansions checked by
  `ring`, and their finite integrals proved by `integral_coeffs`.

The Python generator and `conjugate-data.json` are untrusted convenience data;
Lean does not read either. No new axiom, admission, native decision procedure,
or umbrella import is used. The 36 printed audit roots use only `propext`,
`Classical.choice`, and `Quot.sound`.

## Files and replay

Common helper: `Sendov/Analytic/PaperConjugate.lean`.
Generated certificates: `tests/PaperConjugateDI03.lean` through
`tests/PaperConjugateDI07.lean`.
Registry/contracts: `tests/PaperConjugateBudgets.lean`.
Generator: `tests/generate_conjugate_budgets.py`.

Run the generator from this checkout, then the supplied private-object runner
on the common helper, each generated module, and the aggregate module, in that
order. Run the same module list again with `--kernel`. Do not use Lake or alter
shared package caches.

Successful compile receipt tags in `.lake/paper/logs/`:

- helper: `conj-helper-4`
- DI03: `conj-di03-2`
- DI04: `conj-di04-1`
- DI05: `conj-di05-1`
- DI06: `conj-di06-1`
- DI07: `conj-di07-1`
- aggregate: `conj-aggregate-2`

Successful independent kernel receipt tags:

- helper: `conj-helper-k1`
- DI03, DI04, DI05: `conj-small-k1`
- DI06: `conj-di06-k1`
- DI07: `conj-di07-k1`
- aggregate: `conj-aggregate-k1`

All seven compilation exits and all seven kernel exits are zero. Generated
modules emit style warnings (long rational literals and option scoping), not
proof failures. No original project source, Lake configuration, research source,
remote, or shared cache was modified.

These finite diagnostic families cannot satisfy the first-origin bound together
with the corresponding root-disk information. They are not Sendov polynomial
counterexamples, and do not provide all-parameter coverage at any degree.
