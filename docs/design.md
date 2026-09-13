# Proof design

The active endgame implements the rational-envelope/critical-point method of
Senjian An on top of the existing polynomial and analytic reduction.[1][2]
It is a replacement for the old scalar certificate route, not an extra premise
added to the final statements.

## Reduction contract

For interior degree `n ≥ 6`, put `m = M n = n - 1`. The theorem
`cubicScalar_constraints_of_polar_origin` derives all four facts from the
original geometric hypotheses:

1. `0 < α`;
2. `2 * α ≤ M n`;
3. `α ≤ 17`;
4. `1 ≤ scalarObstruction (M n) α (cubicPolarEnvelope α)`.

The range and the scalar lower bound are conclusions, not inputs smuggled into
Sendov's conjecture. The original weak polar integral bound remains weak:
its left side is `1 ≤ I`, not an assumed stronger inequality.

`distillScalar_lt_one` proves a strict upper bound on exactly this domain.
`polar_origin_incompatible` combines the lower and upper bounds. The interior
proof covers degrees two through five with the already-proved elementary
integral argument; the unit-circle case and its equality classification stay
in the separate boundary proof.

## Scalar upper bound

The two-chord integral theorem gives

```text
raw cubic scalar obstruction ≤ E_budget(m) + T0(m,α) + T1(m,α) + T2(m,α).
```

For `5 ≤ m ≤ 54`, fixed rational budgets and critical brackets are checked for
every integer parameter; row 55 supplies a bounded real interval and row 61 the tail
base. The complete critical expressions are tied to the
actual derivatives of `T0`, `T1`, and `T2`. Their polynomial signs are certified
on entire outer intervals, while the middle interval uses monotone factors at
opposite endpoints. This establishes the bound without trusting a sampled
maximum or requiring a separate root-isolation oracle.

The coefficient-list frontend constructs the existing Bernstein addition tree.
Scale positivity, interval membership, both endpoint supports and the complete
polynomial equality remain explicit Lean obligations. The Python coefficient
calculation is not in the trusted base.

For all real `m ≥ 61`, proved parameter antitonicity reduces the four-component
bound to the existing finite `m=61` certificate. `DistillationTailBound` discharges
that base with its already-certified `<199/200` budget; no base or monotonicity
premise is left to the final caller. The rational component uses the actual
envelope-dependent denominator, with a split at `α=10`, rather than the old
independent worst-case bounds that required 81. The exponential components use
`η ≤ (21/22)^4`, hence `log η / 2 ≤ 2 log(21/22) ≤ -1/11`.
This dominates `1/60 + 2/27`, the kappa slope bound at 61, without assuming
a logarithmic estimate or derivative sign. Zero bases are handled separately.

For `55 ≤ m ≤ 61`, the rational component is already antitone. The parameterized
lemma `distillKappa_rpow_interval` bounds finite growth instead of asserting
antitonicity: if the logarithmic slope is at most `ε`, then
`f(m) (1 - ε (U-K)) ≤ f(K)` on `[K,U]`, provided the weight is positive.
It proves this by differentiating `f(m) (1 - ε (m-K))`; no exponential
comparison or derivative fact is left to the final caller. The node cap
`node(55,α) ≤ (979/1000)^10` gives `ε1=331/37800`, while the envelope cap gives
`ε2=95/4158`. Together with the original row-55 budgets `248,91,330` divided by
1000, the exact total is `58135011269/58896123000 < 199/200`.
The theorem covers real degrees and the entire closed alpha interval, without
a finite case split or new Bernstein certificates. The original correlation
`α ≤ min(m/2,17)` remains in the finite interface; for this interval it follows
from `m ≥ 55` and `α ≤ 17`.

The natural-number split `m < 61` versus `61 ≤ m` has no gap. The finite
aggregate proves exactly 5 through 60, and both it and the tail import the final
group `Rows61_61`; row 61 is emitted only once. The generator and validator share
an explicit retained range `5..55,61`, paired with both real theorems. They reject
missing55, missing61, reintroduced56, extra62, duplicated/reordered rows and mismatched components rather
than inferring a smaller cutoff from truncated data. Rows 62 through 81 and all
old row-81-only/two-thirds interfaces have been retired.

## Endpoints and definitions

The regularized components are continuous at `α=0` and their closed-interval
certificates include that endpoint. The raw scalar definition is **not** silently
replaced by a continuous extension there. The geometric reduction supplies
`α>0` where the raw scalar comparison is used.

The old specialized `c`, `Q`, `R` definitions and their moment/packed/batch
certificates are absent from the active source. `M`, `A`, `QQ`, the actual
coordinate identity `mul_eq_c`, the linear and cubic integral lemmas and the
global weak hyperbolic estimate remain because real consumers still need them.
A name containing `c` or a file containing `Tail` is not, by itself, a reason
to delete useful mathematics.

## Verification boundary

Acceptance distinguishes:

- exact source generation and input coverage;
- Lean elaboration with the pinned project options;
- independent kernel replay over the pinned imported environment;
- original final-theorem type preservation;
- actual value and type/value dependency checks for both final theorems.

The earlier-tail consumer test checks actual proof-value edges from both final
theorems through the geometric reduction and the tail to row 61. Its recursive
project-value audit requires rows 5 through 54 with their strict budgets and all
three row-55 components in the finite aggregate. Each final theorem additionally
consumes row 61 and its strict budget. The row-55 aggregate budget theorem is not
needed: the interval uses the three individual budgets with different growth weights.
Retired rows 56 through 60, 62 through 81 and tail interfaces must be absent from
both the imported environment and the actual value closure. Dependency checks
do not equate a module import with proof consumption.

Readability is the first selection criterion, measured compilation cost second,
and line count third. Source counts include the shared certificate frontend;
generator, template and input-table costs are reported separately rather than
hidden by moving text out of Lean files.

## Sources

[1] https://github.com/teorth/sendov
[2] https://github.com/SJanPerth/Sendov-Proof-Distillation/tree/e8ae601491ec171ab4f7f8456113dd6a047aa85d
