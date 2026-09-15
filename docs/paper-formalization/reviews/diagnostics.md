# Final diagnostic semantic audit — PASS

**Target:** immutable Git tree `1b08ca1ec9c505dbecffb6341b62dfde2fb5634d` in `/home/v-zhouziyu/work/sendov-paper-formalization-20260914`.

**Verdict: PASS for the requested semantic/source-binding audit. No concrete blocking finding.** Covers DI02–DI10 and DI15–DI17, the centered/conjugate/legacy helpers, both specified generators, and the five-dataset aggregate. This is **not** a claim that this reviewer compiled Lean or completed the parent's independent kernel replay.

## Boundary and verification performed

- Read formalization sources exclusively with `git show <target-tree>:<path>`, not from the changing working tree. Independently rehashed the raw Git tree object and recovered the exact requested OID.
- Executed both generator bodies in memory: replaced only `ROOT`/filesystem path operations with an in-memory read/write adapter; retained their arithmetic, assertions, templates and serialization. All assertions passed and **all 8 generated outputs matched the target blobs byte-for-byte**. Neither generator was allowed to write the checkout.
- Independently rebuilt the polar polynomials using a multinomial formula, integrated rational coefficients with `Fraction`, and compared against generated Lean literals and the paper JSON certificates. Independently evaluated the literal finite J polynomials as an additional nonvacuity check.
- Checked the 34-file in-tree import closure of the four diagnostic entry points for executable `axiom`, `sorry`, `admit`, `sorryAx`, `native_decide`, `implemented_by`, `unsafe`, and `extern` tokens after removing comments/strings: no findings. This is a source scan, not a replacement for `#print axioms` or kernel replay.
- HEAD remained `1108d11ee7e6c1d231d41c91607745e0330dcbc2`. Three untracked paths appeared concurrently (`docs/paper-formalization/modules.json`, `scripts/check_paper.py`, `scripts/verify_paper_results.py`); none was read as target source or created by this audit. They do not change the immutable review object.

## 1. Actual q, mean, variance, and actual complex integrals

**DI02 — PASS.** `tests/PaperCenteredHundred.lean:13–37` defines exactly 50 copies of `2/5` and 50 copies of `1`, as a **complex multiset**, and defines `r` by mapping subtraction of the same `μ`. It proves cardinality 100, mean `7/10`, actual variance and signed second moment `9/100`, and `Gamma = 1/539`. Multiplicity is not erased. Its pointwise theorem also supplies nonzero entries and norm at most one.

`tests/PaperCenteredHundred.lean:1993–1999,2003–2015,2064–2092` binds J and K to the literal complex product integrals of that q. K is not an AM–GM relaxation. The proof of full polar uses three positive rectangles plus the nonnegative initial interval and actual complex-to-real equality. Independent exact polynomial integration confirmed K>1 and J>1 (display only: K≈1.7305046879164039, J≈1.58437325574623).

**DI03–DI07 — PASS.** `Sendov/Analytic/PaperConjugate.lean:10–70` defines `x ± i sqrt(1-x²)` and exactly n copies of each. `card_family`, `sum_family`, `mean_family`, and `variance_family` prove the actual multiset facts. `pair_product`, `polar_product`, K/J definitions and `K_eq` at lines 72–106 bind the rational polar polynomial to the **same actual complex family**. Generated `expansion` proofs use `ring`; `integral_coeffs` at lines 108–120 proves finite integration with integrability obligations, rather than trusting a coefficient list.

The exact registry matches `first-origin/REPORT.md:259–269` and `first-origin/verify.py:174–185`:

| ID | m | a | x = actual mean | Actual centered variance | Checked C·H degrees |
|---|---:|---|---|---|---|
| DI03 | 6 | 9/10 | 49/50 | 99/2500 | 3–6 |
| DI04 | 8 | 99/100 | 497/500 | 2991/250000 | 3–8 |
| DI05 | 20 | 9/10 | 83/100 | 3111/10000 | 3–20 |
| DI06 | 100 | 9/10 | 61/100 | 6279/10000 | 3–100 |
| DI07 | 100 | 99/100 | 22/25 | 141/625 | 3–100 |

`tests/PaperConjugateBudgets.lean:26–80` has one `Accepted` proposition containing cardinality, pointwise norm, actual mean/variance, literal full polar, the paper majorant budget, and literal norm J>1. All five named closed instances feed `all_datasets_closed`; `dataset_count` proves length five. Programmatic enumeration confirmed five distinct IDs and the exact five triples, not merely five imports or duplicate rows.

## 2. All finite H terms, square roots, and the genuine majorant

**PASS.** The paper's E_fin is `PaperCenteredBound.majorant_Efin`, **not** `PaperCentered.Efin`:

- `Sendov/Analytic/PaperCenteredBound.lean:24–36,83–100` defines the interior square-root coefficient, explicit top branch `sqrt(v^m)`, and the sum over `Ico 3 (r.card+1)`. Every term multiplies the actual `‖H‖`. Its comparison with the independently defined actual-coefficient bound has the correct direction.
- `Sendov/Analytic/PaperConjugate.lean:123–145` proves exact BR/B and norm-H equalities and `budget_eq`, including the actual variance and `Gamma`. `scalarBudget` is therefore tied back to the literal majorant, not simply given a similar name.
- `sqrt_term_le` at lines 151–163 requires and consumes `s≥0`, **d>0**, b≥0, and `s*h²≤(b*d)²`. Generated term proofs discharge these with `norm_num`, retaining `abs(1-BR)` at every degree. The degree-100 proof explicitly uses `endpoint_100`, then `C_top` (`tests/PaperConjugateDI06.lean:1099–1103`, likewise DI07).
- Independent enumeration found **224 C·H term proofs** across the five conjugate modules, with endpoint ranges 0…m and term ranges 3…m exactly. The scalar summation consumer exhaustively invokes the corresponding terms, including term m, and the actual paper-budget and norm-J consumers follow (`DI06:1105–1231` is the degree-100 instance).
- DI02's `normalized_C_le` (`PaperCenteredCertificate.lean:64–79`) proves its normalization denominator positive from `choose_pos` and `u>0`, with an explicit top branch. There are **98 generic and 98 actual-coefficient rows**, each covering 3…100. Integer envelope sums are `453022083` and `10642552` over denominator `10^12`; their consumers prove the requested distinct bounds `<1/2000` and `<11/10^6` (`PaperCenteredHundred.lean:1948–1984`). No actual coefficients are substituted into the generic majorant proof.

For DI02 only, replacing each norm-H by its proved upper bound one is legitimate: its scale is proved to be the real `63/100`, and the proof first bounds the actual finite H terms (`PaperCenteredCertificate.lean:24–60`; `PaperCenteredHundred.lean:36–51`). This is expressly allowed for this dataset in `first-origin/REPORT.md:250–256`; it is not a false general complex-scale probability argument.

Both generators are stdlib-only untrusted witness producers. Their assertions are useful diagnostics, **not axioms**. The emitted Lean independently proves binomial constants, square inequalities, polynomial identities and integral values. Coarser generated envelopes differ from paper display-only decimal error estimates and DI02's original `10^35` rounding denominator, but preserve the exact required final bounds; they do not claim those displays are equal.

## 3. Nonvacuous norm-J conclusions

**PASS.** `PaperCenteredBound.C_budget:110–119` consumes the proved majorant budget and actual mean, forwarding to `PaperCentered.C_budget:332–360`. The latter derives its norm conclusion from the proved centered integral identity, not a hypothesized identity or a first-origin upper bound. The local `hJ : ‖J‖≤1` is introduced **only by negating the desired conclusion inside `by_contra`**; it is not an external first-origin premise.

Every DI02–DI07 final norm-J theorem is closed at its concrete inputs. The conjugate route is `scalar_budget → budget_implies_J → PaperCenteredBound.C_budget`, with `budget_eq` restoring the actual family. Independent exact J calculations also gave J>1 for every dataset (display only: DI03 1.14353584; DI04 1.0179691061941714; DI05 1.373591961593296; DI06 1.8543274511846286; DI07 1.1512506640471187). These are finite q diagnostics, not Sendov polynomial counterexamples.

## 4. DI08–DI10: rejected decimal, historical margin, and direct T

**PASS.** `tests/PaperLegacyCertificates.lean:22–32` preserves exactly `0.999999986596654 = 499999993298327/500000000000000`, `a=999999999/10^9`, upper endpoint `a+100h²`, and the distinct legacy witness `a+3h²`. The rejected value is neither repaired to a nearby root nor confused with binary64's exact binary fraction.

`PaperLegacyHelpers.lean:11–79` supplies actual indexed complex pairs, unit norms, actual mean real part, and K=R. `PaperLegacyExact.lean` and `PaperLegacyHundred.lean` prove their coefficient expansions and actual integrals. Independent multinomial reconstruction checked **every coefficient and integral** for rejected/lower/upper/legacy/twenty/hundred, and the exact values matched `first-origin-uniform/certificates.json` and `legacy_RESULT.json` (for gap fields, compared K−1 exactly).

`PaperLegacyCertificates.lean:46–80` proves rejected full K<1, strict raw and full-complex endpoint brackets, and D for **all** raw-feasible x in the stated domain, not just a replacement sample. `legacy_three_fifths:89–101` consumes the actual `PaperTaylor.budget_le` estimate and proves **B−T>3h/5**, not the weaker uniform h/3. Independent rational evaluation of that Taylor bound gave a margin/h of approximately 0.6590909064842657, strictly above 3/5.

DI10 uses the actual T integral (`PaperTaylor.budget:19–24`) through a finite split (`PaperLegacyHelpers.lean:95–148`), not a centered C-budget or uncorrected quadrature. Positivity, split endpoints, chord extension to its zero, and the direction of rounding the half-integer tail exponent downward are explicit. Independent rational checks confirmed both split majorants are below B, with positive displayed margins approximately 0.0159601261 and 0.0028272840. Full K and unit-circle facts are packaged alongside them (`PaperLegacyCertificates.lean:103–177`). Source-level proof-closure assertions at lines 188–230 require the relevant integral/T lemmas and forbid centered/near substitutes for the selected legacy roots.

Paper sources: `first-origin-uniform/REPORT.md:53–94`, `legacy_RESULT.md:19–25`. The original Simpson/displayed gaps are not asserted as equal to these new structural certificates.

## 5. DI15–DI17: intervals and correctly scoped countermodels

**PASS.** `tests/PaperPolarDomainWitnesses.lean:19–61,63–189` proves full complex polar throughout both **closed intervals**, using all-ones q for m=7 and exactly five conjugate pairs at x=93/100 for m=10. No raw-polar hypothesis or grid is substituted. Uniform lower-polynomial comparisons include coefficient positivity and integrability. Independent exact evaluation of the proof's lower certificates gave approximately 1.0783885631 and 1.0091408796, both >1. The latter is deliberately weaker than the paper's displayed >1.00927; the formal theorem claims full-polar nonvacuity, not that sharper display.

Lines 191–210 preserve the exact m=64,a=1/2,all-ones integral, prove alpha=24>17 and full K>1, and refute precisely pointwise+full-polar ⇒ alpha≤17. This does not assume first-origin/root-disk data.

Lines 215–317 define the actual polynomial `(X−1)^9*(X+1)`, prove its derivative and complete critical multiset (eight copies of 1, one of −4/5), and use that derivative-root multiset in the reciprocal-square sum. They prove the marked point −1/4 lies in the actual root convex hull **and is not a root**, sum `25488/3025<9`, and attained nearest distance `11/20<1`. Independent rational checks verified the moment, distances and barycentric combination. The final negation targets only the **nonroot convex-hull moment variant**, not a marked-root theorem or the nearest-critical-point bound.

Paper sources: `first-origin-uniform/round6/REPORT.md:135–146`, `round7/REPORT.md:73–80,171–181`. All exact input tokens agree.

## Style/performance, separately

Large rational literals, repeated per-degree statements, broad local arithmetic options, and coarse envelopes are readability/performance considerations, not semantic blockers. No Lean timing or memory performance was measured in this read-only audit. No additional scope or all-parameter theorem is demanded.

**Remaining verification boundary:** the parent's compile/kernel replay is separate and must be reported from its actual receipts. This audit created only this review file; it made no build, source, cache, Git-index, research-input, or remote writes.
