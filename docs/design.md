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

For `5 ≤ m ≤ 81`, fixed rational budgets and critical brackets are checked for
every integer parameter. The complete critical expressions are tied to the
actual derivatives of `T0`, `T1`, and `T2`. Their polynomial signs are certified
on entire outer intervals, while the middle interval uses monotone factors at
opposite endpoints. This establishes the bound without trusting a sampled
maximum or requiring a separate root-isolation oracle.

The coefficient-list frontend constructs the existing Bernstein addition tree.
Scale positivity, interval membership, both endpoint supports and the complete
polynomial equality remain explicit Lean obligations. The Python coefficient
calculation is not in the trusted base.

For all real `m ≥ 81`, proved parameter antitonicity reduces the four-component
bound to the actual finite `m=81` certificate. `DistillationTailBound` discharges
that base; it is not left as a hypothesis of the final upper bound.

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

Those dependency checks require all finite cases, the real tail base, the
geometric reduction and the certificate core, and reject the retired scalar
route. They do not equate a module import with proof consumption.

Readability is the first selection criterion, measured compilation cost second,
and line count third. Source counts include the shared certificate frontend;
generator, template and input-table costs are reported separately rather than
hidden by moving text out of Lean files.

## Sources

[1] https://github.com/teorth/sendov
[2] https://github.com/SJanPerth/Sendov-Proof-Distillation/tree/e8ae601491ec171ab4f7f8456113dd6a047aa85d
