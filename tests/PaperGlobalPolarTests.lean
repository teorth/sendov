import Sendov.Analytic.PaperGlobalPolar

/-! Global polar regressions: exact public hypotheses, both sides of the delta
split, odd/even exponents, the strict degree base, and a proof-dependency audit. -/
namespace Sendov.PaperGlobalPolar.Tests
open MeasureTheory PaperPolar

-- The public estimate consumes raw polar only, not a logarithmic/chord assumption.
example {m : ℕ} {a x : ℝ} (hm : 7 ≤ m)
    (ha : 0 < a) (ha1 : a < 1) (hx0 : -1 ≤ x) (hx1 : x ≤ 1)
    (hr : 1 ≤ ∫ t in (0 : ℝ)..1,
      (a ^ 2 + 2 * a * (1 - a ^ 2) * x * t + (1 - a ^ 2) ^ 2 * t ^ 2) ^
        ((m : ℝ) / 2)) :
    (1 - 2 * a * x + a ^ 2) ^ ((m : ℝ) / 2) ≤ 4 / ((m : ℝ) + 2) :=
  endpoint_le hm ha ha1 hx0 hx1 hr

example {m : ℕ} {a x : ℝ} (hm : 256 ≤ m)
    (ha : 0 < a) (ha1 : a < 1) (hx0 : -1 ≤ x) (hx1 : x ≤ 1)
    (hr : RawPolar m a x) : (m : ℝ) * x ^ 2 > 19 / 2 :=
  degree_mul_sq_gt hm ha ha1 hx0 hx1 hr

-- Minimum odd degree: do not silently round the real exponent to a natural power.
example {a x : ℝ} (ha : 0 < a) (ha1 : a < 1) (hx0 : -1 ≤ x) (hx1 : x ≤ 1)
    (hr : RawPolar 7 a x) : b a x ^ ((7 : ℝ) / 2) ≤ 4 / 9 := by
  have h := endpoint_le (by norm_num : 7 ≤ 7) ha ha1 hx0 hx1 hr
  norm_num at h ⊢
  exact h

example {a x : ℝ} (ha : 0 < a) (ha1 : a < 1) (hx0 : -1 ≤ x) (hx1 : x ≤ 1)
    (hr : RawPolar 8 a x) : b a x ^ (4 : ℕ) ≤ 2 / 5 := by
  have h := endpoint_le (by norm_num : 7 ≤ 8) ha ha1 hx0 hx1 hr
  norm_num [Real.rpow_natCast] at h ⊢
  exact h

-- Exact lower split boundary belongs to the large-delta branch.
example : Real.log ((9 : ℝ) / 2) ≤ Real.log (((9 : ℝ) / 2) * (4 / 9)) / (4 / 9) :=
  log_mul_div_delta (by norm_num) (by norm_num) (by norm_num) (by norm_num)

example {a x : ℝ} (ha : 0 < a) (ha1 : a < 1) (hx0 : -1 ≤ x) (hx1 : x ≤ 1)
    (hr : RawPolar 7 a x) (hs : (9 : ℝ) / 2 * (1 - a ^ 2) < 2) :
    (3 : ℝ) / 5 < c a x := by
  exact three_fifths_lt_c (by norm_num) ha ha1 hx0 hx1 hr (by norm_num at *; exact hs)

-- The strict target holds at the stated base, not merely above it.
example {a x : ℝ} (ha : 0 < a) (ha1 : a < 1) (hx0 : -1 ≤ x) (hx1 : x ≤ 1)
    (hr : RawPolar 256 a x) : (19 : ℝ) / 2 < 256 * x ^ 2 := by
  simpa using degree_mul_sq_gt (by norm_num : 256 ≤ 256) ha ha1 hx0 hx1 hr

example : (24 : ℝ) / 5 < Real.log 129 := log_129_gt

-- Nonvacuity: an actual finite raw-polar instance, not an assumed scalar estimate.
theorem raw_feasible : RawPolar 16 (9 / 10) 1 := by
  rw [rawPolar_iff]
  change 1 ≤ PaperSecant.R 16 (9 / 10) 1
  rw [PaperSecant.R_one (by norm_num) (by norm_num)]
  norm_num [PaperSecant.U1]

example : b (9 / 10) 1 ^ ((16 : ℝ) / 2) ≤ 4 / 18 := by
  have h := endpoint_le (by norm_num : 7 ≤ 16) (by norm_num) (by norm_num)
    (by norm_num) (by norm_num) raw_feasible
  norm_num at h ⊢
  exact h

#print axioms integral_chord
#print axioms raw_integral_le_chord
#print axioms log_mul_delta_le
#print axioms log_mul_div_delta
#print axioms log_129_gt
#print axioms three_fifths_lt_c
#print axioms log_degree_le_c
#print axioms endpoint_le
#print axioms degree_mul_sq_gt
#print axioms raw_feasible

-- Both headline proofs must actually reach the finite chord, both branches,
-- and the established logarithmic certificate in their proof-value closure.
open Lean Elab Command in
run_cmd do
  let env := (← getEnv).setExporting false
  for root in #[`Sendov.PaperGlobalPolar.endpoint_le, `Sendov.PaperGlobalPolar.degree_mul_sq_gt] do
    let mut pending := [root]
    let mut visited : Std.HashSet Name := {}
    while !pending.isEmpty do
      let name := pending.head!
      pending := pending.tail!
      unless visited.contains name do
        visited := visited.insert name
        let some ci := env.find? name | throwError "missing declaration {name}"
        if let some value := ci.value? (allowOpaque := true) then
          for used in value.getUsedConstants do pending := used :: pending
    for target in #[`Sendov.PaperGlobalPolar.integral_chord,
        `Sendov.PaperGlobalPolar.raw_integral_le_chord,
        `Sendov.PaperGlobalPolar.log_mul_div_delta,
        `Sendov.PaperGlobalPolar.three_fifths_lt_c,
        `Sendov.PaperPolar.b_le_alpha, `Real.log_two_gt_d9] do
      unless visited.contains target do
        throwError "headline proof does not consume {root} -> {target}"
    if visited.contains `sorryAx then throwError "unexpected sorry dependency"
    logInfo m!"GLOBAL_POLAR_PROOF_CLOSURE_OK {root}"

end Sendov.PaperGlobalPolar.Tests
