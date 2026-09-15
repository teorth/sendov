# Result

**OPEN:** uniform positive-variance C-near and Efin≤h/2. **No certified counterexample found.**

## Verified additions

- Three new Lean modules compile and pass `leanchecker`: `PaperCenteredTail`, `PaperCenteredEndpoint`, `PaperCenteredVarianceEndpoint`.
- Ten load-bearing axiom probes use only `propext`, `Classical.choice`, `Quot.sound`.
- Proved all-degree H/mean-power cancellation, actual variance/endpoint coupling and finite-order suppression, and the full C-near budget for zero actual variance (m≥7, all 0<a<1 under RawPolar).
- Derived a paper-level uniform factorial-Cauchy high-k envelope; its global scalar budget and Lean assembly remain open.

## Evidence, not global coverage

- 2,400 exploratory FULLpolar family samples; 13,068 local-optimization evaluations.
- 34 two-precision cases, through m=2048 and a=1-10^-12; six float-boundary candidates were rejected by high-precision FULLpolar.
- 10 exact rational FULLpolar/pointwise/actual-majorant witnesses all satisfy C-near and Efin≤h/2. Largest certified Efin/h ≈0.31135512.
- Stable high-precision sampled maximum Efin/h ≈0.31282503.
- Preserved a catastrophic-cancellation regression: naive floating tail ≈8.49e116 versus actual majorant ≈3.78e-8.

`verify.py` passed. The final optimizer replay preserved the source hash and reproduced the identical result hash `3534396b0b63e0404d0650c85ad4d4affa93e4ef225beeaa402e5bf80992c9bf`.

See `REPORT.md`, `MATH_NOTE.md`, and `RESULT.json` for precise premises, receipts, counts and replay commands. No remote/BASE/shared-cache edits or commit.

**Integration caveat:** the nominally private tree had another writer. My `optimize.py` replaced an earlier same-path optimizer; the other writer's `finalists.py` expects its old schema. Current results are independently replayed by `verify_optimization.py`. Other-writer files were preserved and are not included as my verified additions.
