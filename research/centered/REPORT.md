# Centered-route report

## Outcome

**Uniform positive-variance C-near remains OPEN. No certified counterexample was found.** In particular, this investigation does not establish that the actual square-root majorant is too strong, and does not replace the missing global inequality by a numerical degree table.

There are three new kernel-checked modules:

1. `Sendov/Analytic/PaperCenteredTail.lean`: cancellation of the inverse mean power for **all** k≤m, exact majorant-term norm identity, and finite integral envelopes for arbitrary high-degree blocks.
2. `Sendov/Analytic/PaperCenteredEndpoint.lean`: one-binomial-term endpoint estimates at arbitrary order; `|1-aμ|^(m+1)≤(1-a)/2` on RawPolar, m≥7, |μ|≤1, **all 0<a<1**; and the full C-near budget on the **zero actual variance** domain.
3. `Sendov/Analytic/PaperCenteredVarianceEndpoint.lean`: actual-data coupling `|1-aμ|²+a²v≤b` and `N a²v |1-aμ|^(2(N-1))≤b^N`, uniformly for natural N≥1.

All three compiled and passed `leanchecker`. The ten load-bearing theorem axiom probes returned only `[propext, Classical.choice, Quot.sound]`. The existing EX01 and conditional C_budget were not modified.

## Numerical and rational findings

The exact target was always PaperCenteredBound.majorant_Efin, computed from the actual mean and variance of each q family. The exploratory search included nonreal means, 2/3/4-modal families, unequal integer multiplicities, interior radii and unit-circle support, m=7,8 and larger degrees, and a approaching 1.

- **2,400** seeded boundary-family samples used the FULL complex polar integral, not merely RawPolar.
- **13,068** deterministic stochastic optimization evaluations targeted Efin/h, `(Efin+Γ)/(1-a|μ|)`, and `(Efin+Γ-(1-a|μ|))/h`. These are local search attempts, **not certified global maxima**.
- **34** selected cases were recalculated at two high precisions. The complex polar quadrature was cross-checked against the finite polynomial integral. Six nearly-a=1 float-boundary candidates were slightly FULLpolar-infeasible at high precision and are explicitly **not** certified witnesses.
- **10 rational complex witnesses** were rounded inward, checked pointwise by exact norm squares, and certified using exact FULLpolar polynomial integration and rational square-root brackets. Every one passes Efin≤h/2 and the original C-near budget. Largest certified Efin/h is approximately **0.3113551164**.
- Largest Efin/h among the two-precision diagnostic cases is approximately **0.3128250324**. This is a sampled value, not a uniform upper bound.
- Two additional large-degree cases are included within the 34: m=2048, with nonreal unbalanced actual means, at a=.9 and a=1-10^-12. The latter has numerical FULLpolar margin about 4.93×10^-19 and Efin/h about 3.64×10^-8. Its pointwise inputs are rational; its FULLpolar/majorant conclusions are high-precision evidence, not a rational interval certificate.

The separate RawPolar moment-disk scan has **7,777** points and is deliberately labelled a relaxation, not FULLpolar feasibility. Its largest sampled Efin/h is about 0.31284133. The scalar-envelope scan has **6,060** points, including degrees through 4096. Neither scan establishes coverage between samples or above its maximum degree.

## Structural high-k progress beyond diagnostics

`MATH_NOTE.md` gives an elementary uniform paper proof of

`C_(m,k)(v)^2 ≤ (2k+1) binom(m,k) v^k`,

using the binomial mode and its actual first moment. Factorial-weighted Cauchy–Schwarz then replaces the entire k≥K H-weighted tail by the single finite integral

`T_K = (m+1) a^(K+1) |μ| v^(K/2) sqrt(S_K (m)_K) ∫₀¹ t^K β_s(t)^((m-K)/2)dt`,

where `S_K=2/((K-2)(K-2)!)+1/((K-1)(K-1)!)`, so S₃=9/4 and S₄=5/9. It uses the identity `|1-aμt|²+a²vt²=β_s(t)` **before** any s≤1 relaxation.

The binomial-mode and factorial-Cauchy assembly are **not yet Lean formalized**. More importantly, a uniform scalar budget for this envelope remains missing:

- the sampled maximum of `(endpoint+T₃+Γ)/(1-a|μ|)` is about **0.345533**;
- retaining the exact k=3 majorant and bounding k≥4 structurally gives sampled maximum `(endpoint+term₃+T₄)/h` about **0.442459**.

These numbers identify a promising finite structural target. They are not the proof of that target. Since no genuine majorant counterexample was found, no ad hoc “corrected budget” or stronger premise is introduced.

## Important failed diagnostic and preserved regression

A naive descending complex-binomial sum manufactured a tail of **8.4921×10^116** at m=512. This was catastrophic cancellation, not a counterexample. The actual majorant is about **3.77788×10^-8** at 300 digits. `instability.py` and `instability_regression.json` preserve and replay that failure. Low-k H must be computed as 1-B_k, or by a stable integral/adequately precise calculation; the full downward tail is unsafe there.

## Replay

From this exact worktree:

```sh
python3 research/centered/verify.py                 # fast stored-evidence/Lean-receipt audit
python3 research/centered/search.py --count 60
python3 research/centered/optimize.py
python3 research/centered/scalar_scan.py
python3 research/centered/envelope.py
python3 research/centered/rational.py               # exact arithmetic; the 256 case takes longer
```

Use the provided read-only mpmath interpreter for:

```sh
MP=/home/v-zhouziyu/work/sendov-research-20260914-research/first-origin-uniform/.venv/bin/python
$MP research/centered/high_precision.py
$MP research/centered/large_precision.py
$MP research/centered/verify_optimization.py
$MP research/centered/instability.py
```

The raw scripts write JSON results; `verify.py` checks stored constraints, means, variances, counts, precision agreement and actual Lean receipts. Its fast mode does **not** recompute every rational integral. Full arithmetic replay is `rational.py` plus `verify_optimization.py`.

Lean verification uses the requested `scripts/check_paper.py`, this worktree, the provided config, one compiler at a time, and private `.lake/paper/objects`. Exact successful receipt paths and source SHA-256 values are in `RESULT.json`. The axiom audit is `tests/PaperCenteredVarianceAudit.lean`.

## Workspace/concurrency disclosure

HEAD stayed at `a28fce8f970c3c4f50a9f6e194e0491775e75d4b`; no remote, BASE, shared cache, Lake build or other worktree was modified. No commit was made.

Although the assignment described a private tree, another writer `20260914_201159_dabf2f` concurrently created `tests/PaperCenteredStructural.lean`, `research/centered/finalists.py`, `structural_replay.py`, and an earlier optimizer. The warning arrived after my write to `optimize.py`; my version replaced that prior optimizer and uses a different `optimization_results.json` schema. The older `finalists.py` therefore does not consume the current output. **Use `verify_optimization.py` for the current schema**; the other writer's files were preserved, not silently repaired or claimed as my verified artifacts. All reported numerical counts and current module checks refer to the current named scripts/results and receipts, not that older finalists path.

## Remaining mathematical blocker

The open domain is positive actual variance throughout m≥7, .9≤a<1 under the full original q conditions. A uniform C-near proof or a certified counterexample is still missing. The checked output is the all-degree cancellation, endpoint/variance structural lemmas, and the zero-variance domain—not the full requested theorem.
