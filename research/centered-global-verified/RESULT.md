# RESULT

**Uniform original C-near is proved at reviewed paper level:**

    E_fin+Gamma <= 1-a|mu|-(1-a)/20 < 1-a|mu|

for every natural m>=7,9/10<=a<1, under the original complex FULLpolar and pointwise unit-disk constraints, with actual mean/variance. The square-root majorant, top coefficient branch and complex endpoints are unchanged. No paper parameter domain remains open. The stronger global E_fin<=h/2 assertion is not claimed.

The proof uses one generic analytic criterion across eight continuous residual degree bands, followed by reviewed cutoff arguments. This is finite-band exact polynomial certificate mathematics—not a per-degree original-majorant table and not a certificate-free formula.

**Not globally kernel-checked.** Complete Lean consumers cover lambda<=1/3 and the all-lambda actual-variance strip v<=h/m². General actual-C band, Jensen/Lyapunov, actual-moment and Bernstein consumers also compile, but concrete global certificates and the unbounded cutoff remain uninstantiated in Lean. See LEAN_VERIFICATION.json for real compile/kernel receipts.

A certified nonreal FULLpolar example disproves the whole-interval norm-chord budget, not original C-near. Retaining quadratic curvature repairs that example without changing C. A separate generic nonreal positive-variance family shows the literal gap has unattained supremum0 as a->1, using the reviewed theorem for its global upper bound.

REPORT.md contains definitions, evidence levels and replay instructions. Run `python3 -B verify.py`; add `--rebuild` for fresh Lean or `--full-rational` to reconstruct the13 historical exact families. All current paper/exact-example scripts are self-contained; Lean uses the compatible pinned project/cache. No commit, main-proof replacement or remote publication was performed.
