import Sendov.Analytic.PaperHistoricalBounds

/-! Regressions for actual historical integral bounds, independently of uniform D. -/
namespace Sendov.PaperHistoricalBounds.Tests
open MeasureTheory PaperPolar

-- Fully expanded input and output: no assumed scalar approximation of the integral.
example {m : ℕ} {a x : ℝ} (hm : 512 ≤ m)
    (ha : 0 < a) (ha1 : a < 1) (hx0 : -1 ≤ x) (hx1 : x ≤ 1)
    (hr : 1 ≤ ∫ t in (0 : ℝ)..1,
      (a ^ 2 + 2 * a * (1 - a ^ 2) * x * t + (1 - a ^ 2) ^ 2 * t ^ 2) ^
        ((m : ℝ) / 2)) :
    (1 - 2 * a * x + a ^ 2) ^ ((m : ℝ) / 2) +
      m * a ^ 2 * ∫ t in (0 : ℝ)..1,
        t * (1 - 2 * a * x * t + a ^ 2 * t ^ 2) ^ (((m : ℝ) - 1) / 2) < 3 / 5 := by
  simpa [PaperTaylor.budget, PaperTaylor.beta] using
    budget_lt_three_fifths hm ha ha1 hx0 hx1 hr

example {m : ℕ} {a x : ℝ} (hm : 512 ≤ m)
    (ha : 0 < a) (ha1 : a < 1) (ha2 : 2 / 5 ≤ a)
    (hx0 : -1 ≤ x) (hx1 : x ≤ 1) (hr : RawPolar m a x) :
    PaperTwoEnd.total m a x < 40 / ((m : ℝ) * a ^ 2) := by
  rw [PaperTwoEnd.total_eq_budget ha]
  exact budget_lt_forty hm ha ha1 ha2 hx0 hx1 hr

-- Exact base and adjacent odd degree, with the actual half-integer exponents.
example {a x : ℝ} (ha : 0 < a) (ha1 : a < 1) (hx0 : -1 ≤ x) (hx1 : x ≤ 1)
    (hr : RawPolar 512 a x) : PaperTaylor.budget 512 a x < 3 / 5 :=
  budget_lt_three_fifths (by norm_num) ha ha1 hx0 hx1 hr

example {a x : ℝ} (ha : 0 < a) (ha1 : a < 1) (hx0 : -1 ≤ x) (hx1 : x ≤ 1)
    (hr : RawPolar 513 a x) : PaperTaylor.budget 513 a x < 3 / 5 :=
  budget_lt_three_fifths (by norm_num) ha ha1 hx0 hx1 hr

example {a x : ℝ} (ha : 0 < a) (ha1 : a < 1) (hx0 : -1 ≤ x) (hx1 : x ≤ 1)
    (hr : RawPolar 512 a x) : (32 : ℝ) / 3 < 512 * x ^ 2 := by
  simpa using degree_mul_sq_gt (by norm_num) ha ha1 hx0 hx1 hr

-- Original exponential relaxation starts at 9, not 7 or 8.
example {a x : ℝ} (ha : 0 < a) (ha1 : a < 1) (hx : 0 < x) (hx1 : x ≤ 1)
    (hxa : x < a) (hax : a < 3 * x / 2) :
    PaperTaylor.budget 9 a x < 4 / (9 * x ^ 2) +
      (1 + 5 * 9 * x ^ 2 / 8) * Real.exp (-(9 * x ^ 2) / 3) :=
  budget_lt_middle (by norm_num) ha ha1 hx hx1 hxa hax

-- Historical A5 and A5b really apply at 7 and 8; no degree-512 restriction.
example {a x : ℝ} (ha : 0 < a) (ha1 : a < 1) (hx0 : -1 ≤ x) (hx1 : x ≤ 1)
    (hr : RawPolar 7 a x) : PaperTaylor.budget 7 a x ≤
      100 * 7 / (9 * (7 + 1) * (7 + 3) * x ^ 2) + 116 / 9 := by
  convert budget_le_A5 (by norm_num) ha ha1 hx0 hx1 hr using 1 <;> norm_num

example {a x : ℝ} (ha : 0 < a) (ha1 : a < 1) (hx0 : -1 ≤ x) (hx1 : x ≤ 1)
    (hr : RawPolar 8 a x) : PaperTaylor.budget 8 a x ≤
      16 * 8 / ((8 + 1) * (8 + 3) * x ^ 2) + 52 / 10 := by
  convert budget_le_A5b (by norm_num) ha ha1 hx0 hx1 hr using 1 <;> norm_num

example {m : ℕ} {a x : ℝ} (hm : 7 ≤ m)
    (ha : 0 < a) (ha1 : a < 1) (hx0 : -1 ≤ x) (hx1 : x ≤ 1)
    (hr : RawPolar m a x) (hbulk : 116 ≤ (m : ℝ) * a ^ 2 * (1 - a)) :
    PaperTaylor.budget m a x < 1 - a :=
  budget_lt_one_sub_of_bulk116 hm ha ha1 hx0 hx1 hr hbulk

-- Exact nonvacuous base, radius boundary, and closed disk boundary x = 1.
theorem raw_feasible : RawPolar 512 (2 / 5) 1 := by
  rw [rawPolar_iff]
  change 1 ≤ PaperSecant.R 512 (2 / 5) 1
  rw [PaperSecant.R_one (by norm_num) (by norm_num)]
  norm_num [PaperSecant.U1]
  have h1 := pow_le_pow_right₀ (by norm_num : (1 : ℝ) ≤ 31 / 25) (by norm_num : 32 ≤ 513)
  have h2 := pow_le_pow_left₀ (by norm_num : (0 : ℝ) ≤ 2 / 5) (by norm_num : (2 / 5 : ℝ) ≤ 1) 513
  have hlarge : (900 : ℝ) ≤ (31 / 25) ^ (513 : ℕ) :=
    (by norm_num : (900 : ℝ) ≤ (31 / 25) ^ (32 : ℕ)).trans h1
  have hsmall : (2 / 5 : ℝ) ^ (513 : ℕ) ≤ 1 := by simpa only [one_pow] using h2
  apply (le_div_iff₀ (by norm_num : (0 : ℝ) < 10773 / 25)).mpr
  exact (by norm_num : (1 : ℝ) * (10773 / 25) ≤ 900 - 1).trans (sub_le_sub hlarge hsmall)

example : PaperTaylor.budget 512 (2 / 5) 1 < 3 / 5 :=
  budget_lt_three_fifths (by norm_num) (by norm_num) (by norm_num)
    (by norm_num) (by norm_num) raw_feasible

example : PaperTaylor.budget 512 (2 / 5) 1 < 40 / (512 * (2 / 5) ^ 2) :=
  budget_lt_forty (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num) (by norm_num) raw_feasible

example : (27 : ℝ) / 5 < Real.log 257 := log_257_gt
example : (512 : ℝ) * (1 + 512 / 40) * Real.exp (-512 / 75) < 24 := middle_tail (by norm_num)

#print axioms budget_lt_three_fifths
#print axioms budget_lt_forty
#print axioms budget_le_A5
#print axioms budget_le_A5b
#print axioms budget_lt_bulk116
#print axioms budget_lt_one_sub_of_bulk116
#print axioms budget_lt_one_sub_of_bulk40
#print axioms budget_lt_one_sub_of_small
#print axioms raw_feasible

-- Audit proof VALUES, not merely theorem signatures or imported names.
open Lean Elab Command in
run_cmd do
  let env := (← getEnv).setExporting false
  let roots := #[
    (`Sendov.PaperHistoricalBounds.budget_lt_three_fifths,
      #[`Sendov.PaperHistoricalBounds.log_257_gt,
        `Sendov.PaperHistoricalBounds.degree_mul_sq_gt,
        `Sendov.PaperHistoricalBounds.middle_base,
        `Sendov.PaperHistoricalBounds.budget_lt_middle,
        `Sendov.PaperTwoEnd.budget_lt_separated]),
    (`Sendov.PaperHistoricalBounds.budget_lt_forty,
      #[`Sendov.PaperHistoricalBounds.middle_tail,
        `Sendov.PaperTail.power_exp_antitone,
        `Sendov.PaperHistoricalBounds.budget_lt_middle,
        `Sendov.PaperTwoEnd.budget_lt_separated]),
    (`Sendov.PaperHistoricalBounds.budget_le_A5,
      #[`Sendov.PaperHistoricalBounds.integral_chord_le,
        `Sendov.PaperTwoEnd.integral_right_weight,
        `Sendov.PaperTwoEnd.integral_right_unweighted]),
    (`Sendov.PaperHistoricalBounds.budget_lt_bulk116,
      #[`Sendov.PaperHistoricalBounds.budget_le_A5b,
        `Sendov.PaperHistoricalBounds.integral_chord_le,
        `Sendov.PaperTwoEnd.integral_right_weight])]
  for (root, required) in roots do
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
    for target in required ++ #[`Sendov.PaperGlobalPolar.endpoint_le,
        `Sendov.PaperTwoEnd.total_eq_budget] do
      unless visited.contains target do
        throwError "historical proof missing required dependency {root} -> {target}"
    if visited.contains `sorryAx then throwError "unexpected proof hole"
    for name in visited.toList do
      if (`Sendov.PaperUniform).isPrefixOf name then
        throwError "historical stronger bound incorrectly depends on uniform D: {name}"
    logInfo m!"HISTORICAL_BOUND_PROOF_CLOSURE_OK {root}"

end Sendov.PaperHistoricalBounds.Tests
