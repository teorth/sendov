# Result: original C-near residual closed at paper level

## Outcome

For the original square-root C majorant, original FULLpolar premise, actual
complex mean and actual variance, the new proof establishes

    E + Gamma <= 1 - a|mu| - (1-a)/20 < 1 - a|mu|

for every integer `7<=m<=34` and every `9/10<=a<1`. Thus it closes the whole
requested residual `lambda>1/3`, `v>h/m^2`, and also covers the near/strip parts
of this finite degree range without invoking their separate theorems.

Combined with the reviewed round3 cutoff35 and frozen cutoff45, there is no
remaining original C-near **paper** domain. This is not a claim of a completed
kernel theorem.

## Generic method, not per-degree certificates

One analytic criterion takes `(L,U,X)` and works continuously for `L<=m<=U`:

1. An endpoint polynomial `N_U(1-h,X,1)<1` on all `0<h<=1/10`, followed by Lp
   monotonicity, forces `x>X` throughout the degree band. The actual-s defect
   strengthening from round3 remains valid but is not needed.
2. Substitute `y=a*t` before bounding, canceling `a^4`. Retain the quadratic
   `1-2Xy+y^2` and integrate its lower endpoint exponent exactly.
3. Improve `u sqrt(v)<=1/2` to `u sqrt(v)<=X sqrt(1-X^2)` using actual
   `s=u^2+v<=1` and `X^2>=1/2`.
4. Retain every complex B2 term and use the actual-mean budget
   `1-au>=v/2+Xh`, then `v<=Uh/3`.

Eight continuous bands cover all 28 requested integer degrees:
`[7,8], [9,10], [11,12], [13,14], [15,18], [19,22], [23,28], [27,34]`.
Every band contains multiple degrees; there is no original majorant evaluation
or analytic certificate indexed by individual m. Finite exact Bernstein
certificates on the continuous h interval are used explicitly.

An important endpoint detail: `1-2aX+a^2` need not increase in a when X>9/10.
The proof correctly takes its convex endpoint maximum; the selected
`X<=19/20` guarantees the a=1 endpoint dominates the a=9/10 endpoint.

## Actual verification

Executed with Python standard library only:

- `python3 -B verify.py`: **PASS, 360 exact checks**.
- `python3 -B audit.py`: **PASS, 399 exact checks**.

Both reconstruct the polynomial signs, curved integrals, positive-square radical
bounds, rational margins, and degree cover. The second uses independent
trinomial expansions and a Horner Bernstein recurrence, without importing the
first checker. The weakest computed band margin is above `0.06889*h`; every
band is checked exactly against the common `h/20` margin. Decimal display is
not used in any acceptance assertion.

## Files

All created files are under the assigned `research/centered-round4/math-residual/`:

- `PROOF.md`: full quantified paper argument and exact band parameters.
- `REPORT.md`: this report.
- `verify.py`: primary exact reconstruction and source hashes.
- `audit.py`: independent exact reconstruction.
- `cache/exact-verification.json`, `cache/independent-audit.json`: exact receipts.
- `explore.py`, `explore.json`: clearly labeled floating reconnaissance, excluded
  from both proof checkers.

## Limitations / next boundary

The norm/Lp/integral arguments and the frozen original-C/raw-polar lemmas are
paper dependencies, not Python-kernel theorems. The new result still needs
parent/independent mathematical review and a Lean port if kernel closure is
required. No remaining scalar inequality on the requested residual is left by
this argument. No files outside the assigned directory were modified; no
commit or push was made.
