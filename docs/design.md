# Proof design

The polynomial, analytic, low-degree and boundary arguments retain the original
meaning.[1] The scalar reduction uses Senjian An's rational envelope and
two-chord estimate.[2] Its upper bound now uses full-degree-ray estimates:
there are no finite degree certificates or later tail cutoff.

## Exact reduction contract

For interior degree `n >= 6`, put `m = M n = n - 1`.
`cubicScalar_constraints_of_polar_origin` derives, from the original geometric
hypotheses, `0 < alpha`, `2*alpha <= M n`, `alpha <= 17`, and
`1 <= scalarObstruction (M n) alpha (cubicPolarEnvelope alpha)`.
These are conclusions of the reduction, not additional conjecture hypotheses.
The original weak polar integral premise remains `1 <= I`.

`distillScalar_lt_one_real` proves `<1` for every real `m >= 5`,
`0 < alpha <= 17`, `2*alpha <= m`. It splits at alpha 2, not at any degree.
The original `distillScalar_lt_one` natural `n >= 6` signature is unchanged.
`polar_origin_incompatible` combines these bounds. Degrees 2 through 5 still
use the existing elementary integral proof; boundary equality classification
is separate. Neither final headline theorem is weakened or strengthened.
No minimality claim about the scalar starting value 5 is made.

## Small alpha

For `0 < alpha <= 7/5`, `DistillationTotalBound` uses the full chord:

```text
C(m,alpha) = E_budget(m)
  + (8/27) (alpha+3)^3 (m-2alpha)^2 / (m(m+3)(m+5)).
```

Degree factors cancel before estimation. A degree-five alpha identity with six
polynomial coefficients in `m-5` proves `C<1` on the entire unbounded strip;
the last two coefficients use explicit nonnegative-square decompositions.
There is no degree subdivision. The method does not extend automatically:
`C(25/2,17/12)=1+141383/711868500` and
`C(13,10/7)=1+426061/212373252`. These refute an enlarged chord majorant,
not the original scalar inequality.

## Faithful elementary term and middle alpha

For positive alpha, with `u=alpha/(alpha+3)` and `eta=u-u^3/30`,

```text
L = u^2/(180(1-eta)) + u(30+u-u^2)(1+1/m)/360
H = E_budget - L + kappa*J.
```

The exact loss bridge is actually consumed by
`distillScalar_le_elementary_components`. The unused total derivative and the
unused strict loss-positivity research lemma are retired, not the bridge.
`distillTotal`, `distillElementaryLoss`, the original raw scalar, and all
retained factor definitions keep their meanings.

For `7/5 <= alpha <= 2`, `DistillationMiddleEstimates` and
`DistillationMiddleAlpha` split alpha at `17/10`. The rational T0 estimate
retains `(m+3)(m+5)` and uses two positive sextics in `m-5` on the whole ray.
Mixed-alpha exponential estimates bound T1 and T2 on the same ray.
The component budgets are `221/660`, `13/50`, `7/30`, `1/6`.
All constants are discharged internally, with no assumed maximizer or bound.

## Large alpha

For `2 <= alpha <= 17`, `DistillationCorrelatedPeak` shifts by `m-2*alpha`,
not `m-34`, and bounds the full legal degree ray analytically.
`DistillationPeakRational` converts the exponential estimates to rational ones.
`DistillationPeakAlgebra`, `PeakFirst`, `PeakRest`, and `PeakClosure` close the
alpha inequality. The only additional split is alpha `5/2`, where
`max 5 (2*alpha)` changes formula.

The first peak uses an affine budget `(431-3*alpha)/2500` and a fourth-order
Taylor denominator; the second retains the sixth-order denominator. Three
full identities of degrees 53, 47, 47 contain respectively 54, 48, 48 ordered
integer coefficients, plus 71 coefficients in the smaller homogeneous factors.
The positive scales are `15^53`, `1`, and `29^47`. The complete identities,
factor ordering and scale obligations are explicit. They are not sampled
equalities or finite degree data.

The four large-alpha closure modules occupy 885 lines, including all 150 large
and 71 small factor coefficients, before counting the upstream same-alpha,
rational, middle, small-alpha and common-certificate helpers. The existing
`BernsteinList`, `BernsteinCert`, and `BernsteinRing` remain necessary.
No new generator is needed: the Lean identities are self-contained.
The stricter historical `<199/200` convenience is not imposed: the new
rational peak at alpha 17 lies between `199/200` and 1.

## Retirement boundary and endpoints

All degree rows, finite aggregates, critical-polynomial derivative machinery,
old degree-tail/interval modules, and their table/generator/bundler are retired.
The old compound scalar wrapper discarded elementary loss and has no remaining
consumer; it is replaced by the faithful elementary-component bridge.
`DistillationRegularity` preserves common compact forms, positivity and
continuity from the former critical module without retaining its row machinery.
The endpoint-only alpha-17 research theorem is superseded by the uniform strip.

The raw scalar at alpha zero is exactly `1/(2*m)`, not the continuous extension.
The positive-alpha theorem stays positive. `BoundaryConsumer` separately covers
raw zero, regularized T2 zero for every real `m>=5`, and legal `m=2*alpha`.
`NoFiniteRows` covers generic natural degrees, noninteger degrees, alpha
`7/5`, `2`, `17`, and the endpoint ray. Existing low-degree statements remain
unchanged. The raw scalar itself need not be antitone in degree:
`LocalTotalBound` retains the exact `H(5,1)<H(7,1)` regression.

## Trust and verification

`tests/NoFiniteRows.lean` recursively traverses actual proof values using
`ConstantInfo.value? (allowOpaque := true)` and `Expr.getUsedConstants`.
Traversal includes private and imported constants with no namespace pruning.
Each of the real scalar, natural wrapper and both final headline roots must
actually consume all three alpha regimes and the three large-alpha identities.
Old row/critical/tail helpers are rejected; imports and theorem types alone
are not evidence of proof consumption.

`scripts/axioms.lean` explicitly enumerates actual roots and both final results.
The Python auditor fixtures independently enumerate those targets and reject
unknown targets, imported `externalAssumption`, and real Lean errors.
Only `propext`, `Classical.choice`, and `Quot.sound` are permitted.
The shell scanner allows only the three original syntax-only partial tactic
signatures; generated proof terms are still kernel-checked. `Challenge.lean`
retains its two deliberate specification holes and is not imported by Solution.

Negative certificate tests compile unchanged controls, then mutate an interior
coefficient in each complete retained identity. They require exactly the algebraic
`ring failed, ring expressions not equal` error, not a timeout, missing import,
linter or type mismatch.
Smaller full-identity regressions also cover scale, ordering, truncation and
interval changes. Python success, elaboration, exact-module kernel replay,
original compiled-type comparison and proof consumption remain separate gates.
Retired private project objects must be absent during the final run.

## Sources

[1] https://github.com/teorth/sendov
[2] https://github.com/SJanPerth/Sendov-Proof-Distillation/tree/e8ae601491ec171ab4f7f8456113dd6a047aa85d
