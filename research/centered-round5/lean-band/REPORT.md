# Generic curved-tail degree-band criterion — kernel-checked

## Outcome

The generic analytic bridge is complete, including the actual original-C tail,
not merely a scalar consumer. No degree-specific theorem or table was added.

Main theorem:

`Sendov.CenteredBand.C_near_fullpolar_band_of_certificate`

in `Sendov/Analytic/CenteredBandCertificate.lean`.

For arbitrary natural `L,U,p`, with `7 ≤ L`, `L = 2*p+3`, and
`L ≤ q.card ≤ U`, it consumes:

- Original complex unit-disk family `q`, actual mean identity
  `q.sum = q.card * μ`, and original FULLpolar product-integral premise.
- `9/10 ≤ a < 1`.
- A proved real-part bound `X ≤ μ.re`, with `0 < X`, `1/2 ≤ X^2`,
  and `X ≤ 19/20`.
- A scalar polynomial-integral certificate
  `curvedIntegral p X ≤ I`, `tailSquare U X I ≤ tau^2`, `0 ≤ tau`.
- Positivity of the explicit scalar margin below.

It returns all three conclusions, for the actual centered multiset
`r = q.map (fun z => z-μ)` and its actual variance `v`:

1. `majorantTail r μ (a*μ) ≤ tau*v`.
2. `majorant_Efin r μ (a*μ) + Gamma r μ ≤ 1-a*‖μ‖-delta*(1-a)`.
3. `majorant_Efin r μ (a*μ) + Gamma r μ < 1-a*‖μ‖`.

There is no premise equal to a C-near budget or original-C tail bound.
There is no real-mean restriction, saturation premise, positive-variance
restriction, lambda restriction, or per-degree coefficient hypothesis.

## Constants and paper correspondence

With `L = 2*p+3`:

- `curvedIntegral p X = ∫ y in 0..1, y^3*(1-2*X*y+y^2)^p`.
- `BConstant p U X = U^2 * (2*(1-X))^(p+1)`.
- `gammaConstant L X = 1/((L-1)*X^2)`.
- `K = tau + gammaConstant L X*(1+BConstant p U X)`.
- `delta = X - 1/15 - (U/3)*max 0 (K-1/2)`.
- `tailSquare U X I = S_U*(U+1)^2*(U.descFactorial 3)*I^2*X^2*(1-X^2)`.

`S_U` is the unchanged `CenteredThird.weightSum U`. For `U ≥ 3`, the imported
`PaperFactorialTail.cast_descFactorial_three` identifies the falling factorial
with `U*(U-1)*(U-2)`. Thus this is precisely the radical-free scalar quantity
from paper section 4, without evaluating any band or degree.

The scalar budget theorem itself accepts real `L,U,m`. The actual-tail and
original-family theorems use natural degrees and an odd lower endpoint so the
remaining integral is polynomial. No claim of formalizing arbitrary real
exponents or arbitrary real lower endpoints is made.

## What was proved

- `CenteredBandScalar`: actual-statistics curvature improvement
  `u*sqrt(v) ≤ X*sqrt(1-X^2)`; available budget; gamma bound; full scalar margin
  consumption; monotonicity of the exact finite weight `S_m`.
- `CenteredBandTail`: pointwise curved majorization and lower-degree exponent
  comparison; exact cancellation of `a^4` by `y=a*t`; nonnegative interval
  enlargement; finite-factor monotonicity; actual original-C tail bound.
- `CenteredBandEndpoint`: all three original complex B2 terms, with the
  uniform `U^2*(2*(1-X))^(p+1)` envelope. The endpoint comparison uses
  `(1-a)*(a+1-2*X) ≥ 0`, so it does not assume false monotonicity in `a`.
- `CenteredBandTheorem`: original statistics, endpoint error and variance cap
  are derived from existing verified source lemmas; raw and FULLpolar budget
  consumers are assembled without replacing the mean or variance.
- `CenteredBandCertificate`: radical-free scalar-certificate consumer and
  combined original-tail/budget/strict-margin theorem.

The actual-C link invokes the read-only baseline theorem
`CenteredThird.majorantTail_le_cubicIntegral_finite`. That baseline has already
majorized the actual second moment by its unit-disk bound inside beta; it does
not impose equality of the actual second moment with one. The new proof retains
actual variance and actual mean norm in the multiplicative factor throughout.

## Outstanding application interfaces

This is a complete generic criterion, not an instantiated global closure.
To apply it to a chosen degree band one still supplies:

1. A FULLpolar endpoint-moment proof of `X ≤ μ.re` (a strict `X < μ.re`
   proof is more than sufficient).
2. An exact bound/evaluation of the displayed polynomial integral and its
   scalar squared comparison to `tau^2`.
3. Positivity of the displayed rational margin.

The analytic comparison from the original-C integral to the band polynomial
integral is fully proved here; it is not an outstanding interface.
No endpoint-moment Bernstein certificate or numerical band table was copied.
The existing near-one-third theorem was not redone or modified.

## Verification and receipts

Executed successfully:

```text
python3 /home/v-zhouziyu/work/sendov-paper-formalization-20260914-remaining-centered/research/centered-round5/lean-band/verify.py
```

Result: all 6 modules compiled and independently passed `leanchecker`,
including the audit module. All 21 new lemmas/theorems were axiom-audited;
every list is exactly `[propext, Classical.choice, Quot.sound]`.
The forbidden-source-token scan was empty. Compilation emitted style and
unused-variable warnings only; no elaboration or kernel errors remain.

- `receipts/audit.json`: aggregate PASS, source/object/checker hashes,
  all compile/kernel receipts, all axiom lists, and resolved read-only baseline
  object hashes.
- `receipts/<module>.json`, `receipts/<module>-kernel.json`: per-module receipts.
- `.lake/paper/logs/`: exact Lean and kernel command logs.
- `tests/CenteredBandAudit.lean`: audits every new theorem and prints the
  combined theorem's complete type.

## Reusable isolated-stage workflow

`check.py` copies the full round3 integrated object layout as symlinks inside
this directory, unlinks only the owned target artifacts before compilation,
and rejects kernel checks without a matching successful own compile receipt
and matching source/object hashes. `verify.py` rebuilds in dependency order,
kernel-checks each owned output, then checks theorem audit coverage and hashes.
Do not replace this with an external-cache build or kernel-check an inherited
symlink as though it were the newly compiled source.

All task-created source, scripts, logs, objects and receipts are under this
owned `lean-band` directory. External project and package trees were read-only.
No commit or push was performed.
