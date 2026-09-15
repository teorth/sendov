# Quarter-regime endpoint and scalar stage

## Status

All four modules compile under the pinned Lean 4.34.0-rc1 configuration and pass independent `leanchecker` replay. The audit prints exactly `propext`, `Classical.choice`, and `Quot.sound` for all fourteen lemmas/theorems. No custom axioms, `sorry`, `admit`, or `native_decide` are used.

All new source and output files are confined to this directory. Baseline project objects are linked read-only by convention, with fresh, unlinked output names for the four new modules. No parent or sibling source/cache was changed.

## Integration

Copy these source modules, in dependency order, into the receiving tree and compile there:

1. `Sendov/Analytic/CenteredQuarterEndpoint.lean`
2. `Sendov/Analytic/CenteredQuarterScalar.lean`
3. `Sendov/Analytic/CenteredQuarterActual.lean`
4. `Sendov/Analytic/CenteredQuarterAudit.lean` (audit only)

Import `Sendov.Analytic.CenteredQuarterActual`. All declarations are in `Sendov.CenteredQuarter`.

### Primary actual-C interface

```lean
theorem actual_C_quarter_budget (q : Multiset ℂ) (hm : 7 ≤ q.card) (a : ℝ) (μ : ℂ)
    (ha0 : 0 < a) (ha1 : a < 1) (hmean : q.sum = q.card * μ)
    (hq : ∀ z ∈ q, ‖z‖ ≤ 1) (hx0 : -1 ≤ μ.re) (hx1 : μ.re ≤ 1)
    (hp : PaperPolar.RawPolar q.card a μ.re)
    (hl : PaperPolar.lambda q.card a ≤ 1 / 4)
    (htail : (∑ k ∈ Finset.Ico 3 (q.card + 1),
      (PaperCenteredBound.C q.card k (PaperCentered.variance (q.map (fun z => z - μ))) /
        ((q.card.choose k : ℝ) * ‖μ‖ ^ k)) * ‖PaperCentered.H q.card k ((a : ℂ) * μ)‖) ≤
      chordTail q.card a ‖μ‖ (PaperCentered.variance (q.map (fun z => z - μ)))) :
    PaperCenteredBound.majorant_Efin (q.map (fun z => z - μ)) μ ((a : ℂ) * μ) +
      PaperCentered.Gamma (q.map (fun z => z - μ)) μ ≤
        1 - a * ‖μ‖ - 79 * (1 - a) / 504
```

The only remaining analytic input is `htail`, namely the original finite C sum bounded by the explicit chord-tail scalar. It is not a hypothesis equal to the final desired budget. C, H, B, actual variance, Gamma, and the majorant are the original imported definitions.

```lean
def chordTail (m a u v : ℝ) : ℝ :=
  9 * a ^ 4 * u * Real.sqrt (v ^ 3) /
    ((13 / 18) ^ 4 * Real.sqrt (m * (m - 1) * (m - 2)))
```

The falling-factorial expression here uses real subtraction. A natural descending-factorial version requires the usual cast identity for `m ≥ 7`.

### Reusable interfaces

* `endpoint_quartic m hm b h hb0 hb1 hh hslope`:
  `b^(m+1) ≤ (4/9)*h^4`, from the imported `endpoint_power_order` at order 4.
* `endpoint_quadratic m hm w b h hw hb0 hb1 hh hslope hwb`:
  `w^(m+1) ≤ 2*h^2/3`, where `hslope : 3*b ≤ (m:ℝ)*h*(1-b)` and `hwb : w^2 ≤ b`.
* `norm_B_two_le m hm z hz hw`:
  `‖PaperCentered.B m 2 z‖ ≤ 1/50`, with `hz : ‖z‖ ≤ 1` and `hw : ‖1-z‖ ≤ 5/18`.
* `chordTail_le m a u v hm ha0 ha1 hu0 hu1 hv0 hv1`:
  `chordTail m a u v ≤ (109350/28561)*v/(m-1)`, for real `m ≥ 7`, `0 ≤ a,u ≤ 1`, and `0 ≤ v ≤ 1/13`.
* `scalar_budget` has real parameters `(m a h u v e0 B T)`, assumptions
  `7 ≤ m`, `0 ≤ h ≤ 1/28`, `a = 1-h`, `19/20 ≤ u`, `u^2+v ≤ 1`,
  `0 ≤ v ≤ 1/13`, `v ≤ m*h/3`, `e0 ≤ 2*h^2/3`, `B ≤ 1/50`,
  `T ≤ chordTail m a u v`, and concludes
  `e0 + v/((m-1)*u^2)*(1+B) + T ≤ 1-a*u-79*h/504`.
* `actual_quarter_facts` has the actual-C theorem's hypotheses through `hl` and returns
  `1-a ≤ 1/28`, `155/162 ≤ ‖μ‖`, `b ≤ 1/13`, actual `v ≤ 1/13`, actual `v ≤ m*(1-a)/3`, and `‖1-a*μ‖ ≤ 5/18`.
* `actual_endpoint_quadratic` has those actual hypotheses only through `hp` (no lambda cutoff), and concludes
  `‖1-a*μ‖^(q.card+1) ≤ 2*(1-a)^2/3`.

Full Lean-printed interfaces and axiom inventories are retained in
`.lake/paper/logs/audit-final-Sendov.Analytic.CenteredQuarterAudit.log`.

## Proof details

The B2 proof uses the slightly looser but simpler envelope
`((m^2+3m+4)/2)*(5/18)^(m-1)`. Its monotonicity is proved by induction for every `m ≥ 7`, followed by one exact rational base evaluation. There is no per-degree table.

The real scalar proof bounds the explicit chord tail, Gamma, their combined coefficient by 5, and then proves `5*v/(m-1) ≤ a*v/2 + 59*h/72`. Actual variance enters the target through `u^2+v ≤ 1`; no assumption `s=1` or real-valued mean is introduced.

The actual-statistics wrapper obtains `v ≤ b` from the genuine centered variance bound and `1-b ≤ ‖μ‖^2`, then combines this with the raw-polar slope. It obtains the lower mean norm from the real part, not by assuming `u^2 ≥ 1-v`.

## Receipts

Elaboration receipts: tags `endpoint-02`, `scalar-02`, `actual-01`, `audit-final`.
Kernel receipts: tag `kernel-final` for all four modules.
Failed exploratory elaboration receipts are preserved, not overwritten.
Only style/unused-binding linter warnings remain; no theorem or kernel errors remain.
