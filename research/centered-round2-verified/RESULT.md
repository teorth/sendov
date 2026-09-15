# RESULT — round 2

**Uniform C-near remains OPEN. No certified counterexample is asserted.**

Let h=1-a and lambda=mh; v is the actual centered variance. Every conclusion retains original pointwise unit-disk and FULLpolar feasibility, with nonreal means permitted.

## Kernel-checked complete domains

- `lambda<=1/4`, all allowed variances:
  `E_fin+Gamma<=1-a|mu|-79h/504<1-a|mu|`.
- `v<=h/m²`, all lambda in the original a-range:
  `E_fin+Gamma<=1-a|mu|-19h/840<1-a|mu|`.

The final exports `C_near_fullpolar_quarter` and `C_near_fullpolar_strip` have no remaining error-budget or tail-bound premise. The quarter-domain first-origin norm obstruction is also exported.

The frozen source set includes the coefficient-mode, factorial-Cauchy, original-H integral, chord, scalar, and endpoint proofs. All 44 fresh compile/leanchecker checks passed; selected axiom audits use only propext, Classical.choice, Quot.sound.

## Independently checked paper extensions

- `lambda<=1/3`, all allowed variances, margin `37h/819`.
- `m>=45`, all original a and variances, margin `14h/15+9v/2000`.

These extensions are not newly kernel-checked. Their calculus/monotonicity arguments are fully written, and their exact arithmetic checkers passed 53, 48, and 62 checks. No degree table or random-grid proof is used.

## Exact residual paper domain

`7<=m<=44`, `1/3<lambda<=m/10`, `v>h/m²`, with all original feasibility conditions. Equivalently `9/10<=a<1-1/(3m)` and positive variance above that strip. In particular lambda<=22/5.

See REPORT.md, the three mathematical PROOF.md files, RESULT.json, receipts/, and logs/. Run `python3 verify_round2.py` for saved-receipt/arithmetic verification, or add `--rebuild` for fresh Lean execution against the documented compatible project/cache.

No main theorem replacement, old-proof removal, commit, or remote publication was performed.
