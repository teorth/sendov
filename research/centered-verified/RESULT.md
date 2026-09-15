# RESULT

**Uniform positive-variance C-near: OPEN. No certified counterexample found.**

## Proved and checked

- All-degree complex H endpoint cancellation and its finite integral block bound.
- Uniform zeroth endpoint bound |1−aμ|^(m+1)≤(1−a)/2 on raw polar, m≥7, 0<a<1.
- Entire strict C-near budget when the actual centered variance is zero.
- Actual-variance/endpoint coupling and its finite binomial power bound.
- Three new Lean modules plus two audits/tests: ten compile/leanchecker checks passed on frozen sources; audited axioms are only propext, Classical.choice, Quot.sound.

## Evidence, not uniform proof

- 2,400 boundary-search records and 13,068 local-optimization evaluations.
- 30 cases at two precisions, including nonreal means at m=2048 and a=1−10⁻¹².
- 13 distinct exact rational FULLpolar/pointwise witnesses satisfy both E≤h/2 and C-near; maximum attained E/h≈0.3113551.
- Rounded floating candidates that failed exact premises were rejected, not silently repaired.

## New structural route

A binomial-mode bound C_k²≤(2k+1)binom(m,k)v^k and factorial-weighted Cauchy–Schwarz control the entire high-k tail by one actual-variance integral. This paper proof is in `MATH_NOTE.md`; it is not yet a Lean theorem. The resulting scalar budget remains unproved uniformly. Retaining k=3 before bounding k≥4 materially improves the envelope without altering any premise.

## Deliverables

`REPORT.md`, `MATH_NOTE.md`, `RESULT.json`, replay scripts and exact/high-precision JSON, frozen Lean sources, `lean_verification.json`, and final logs. `verify.py --full-rational` rebuilds all exact witnesses; `verify_lean.py` uses an isolated project-object stage.

No main theorem replacement, old-proof deletion, whole-repository release claim, commit, or remote publication was made.
