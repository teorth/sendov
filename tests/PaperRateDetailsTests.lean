import Sendov.Analytic.PaperRateDetails

/-! Exact-contract, boundary, nonvacuity, and proof-value regressions for PO06,
HI04 and the missing first-ray component of RA04. -/
namespace Sendov.PaperRateDetails.Tests
open MeasureTheory PaperPolar

-- PO06: both the integral input and the delta-sensitive output are expanded.
example {m : ℕ} {a x : ℝ} (hm : 7 ≤ m)
    (ha : 0 < a) (ha1 : a < 1) (hx0 : -1 ≤ x) (hx1 : x ≤ 1)
    (hr : 1 ≤ ∫ t in (0 : ℝ)..1,
      (a ^ 2 + 2 * a * (1 - a ^ 2) * x * t + (1 - a ^ 2) ^ 2 * t ^ 2) ^
        ((m : ℝ) / 2))
    (hlarge : 2 ≤ (((m : ℝ) + 2) / 2) * (1 - a ^ 2)) :
    (1 - 2 * a * x + a ^ 2) ^ ((m : ℝ) / 2) ≤
      ((((m : ℝ) + 2) / 2) * (1 - a ^ 2)) ^
        (-(m : ℝ) / (((m : ℝ) + 2) * (1 - a ^ 2))) :=
  endpoint_delta_rate hm ha ha1 hx0 hx1 hr hlarge

-- The split is closed at N*delta=2, including the minimal odd degree.
example {a x : ℝ} (ha : 0 < a) (ha1 : a < 1) (hx0 : -1 ≤ x) (hx1 : x ≤ 1)
    (hr : RawPolar 7 a x) (heq : (9 : ℝ) / 2 * (1 - a ^ 2) = 2) :
    b a x ^ ((7 : ℝ) / 2) ≤
      ((9 : ℝ) / 2 * (1 - a ^ 2)) ^ (-(7 : ℝ) / (9 * (1 - a ^ 2))) := by
  simpa only [Nat.cast_ofNat, show (7 : ℝ) + 2 = 9 by norm_num] using
    endpoint_delta_rate (by norm_num) ha ha1 hx0 hx1 hr (by norm_num; linarith)

example {a x : ℝ} (ha : 0 < a) (ha1 : a < 1) (hx0 : -1 ≤ x) (hx1 : x ≤ 1)
    (hr : RawPolar 8 a x) (hlarge : 2 ≤ 5 * (1 - a ^ 2)) :
    b a x ^ (4 : ℝ) ≤
      (5 * (1 - a ^ 2)) ^ (-(8 : ℝ) / (10 * (1 - a ^ 2))) := by
  simpa only [Nat.cast_ofNat, show (8 : ℝ) + 2 = 10 by norm_num,
    show (10 : ℝ) / 2 = 5 by norm_num, show (8 : ℝ) / 2 = 4 by norm_num] using
    endpoint_delta_rate (by norm_num) ha ha1 hx0 hx1 hr (by norm_num; exact hlarge)

-- HI04: an upper ratio for the actual integral T, not an abstract scalar or D.
example {m : ℕ} {a x : ℝ} (hm : 100000 ≤ m)
    (ha : 0 < a) (ha2 : a ≤ 1 / 2) (hx0 : -1 ≤ x) (hx1 : x ≤ 1)
    (hr : 1 ≤ ∫ t in (0 : ℝ)..1,
      (a ^ 2 + 2 * a * (1 - a ^ 2) * x * t + (1 - a ^ 2) ^ 2 * t ^ 2) ^
        ((m : ℝ) / 2)) :
    ((1 - 2 * a * x + a ^ 2) ^ ((m : ℝ) / 2) +
      m * a ^ 2 * ∫ t in (0 : ℝ)..1,
        t * (1 - 2 * a * x * t + a ^ 2 * t ^ 2) ^ (((m : ℝ) - 1) / 2)) /
      (1 - a) < 83567 / 100000 := by
  simpa [PaperTaylor.budget, PaperTaylor.beta] using
    small_a_ratio_100000 hm ha ha2 hx0 hx1 hr

example {m : ℕ} {a x : ℝ} (hm : 10000 ≤ m)
    (ha : 0 < a) (ha2 : a ≤ 1 / 2) (hx0 : -1 ≤ x) (hx1 : x ≤ 1)
    (hr : 1 ≤ ∫ t in (0 : ℝ)..1,
      (a ^ 2 + 2 * a * (1 - a ^ 2) * x * t + (1 - a ^ 2) ^ 2 * t ^ 2) ^
        ((m : ℝ) / 2)) (hbulk : (m : ℝ) * a ^ 2 * (1 - a) < 116) :
    ((1 - 2 * a * x + a ^ 2) ^ ((m : ℝ) / 2) +
      m * a ^ 2 * ∫ t in (0 : ℝ)..1,
        t * (1 - 2 * a * x * t + a ^ 2 * t ^ 2) ^ (((m : ℝ) - 1) / 2)) /
      (1 - a) < 106 / 125 := by
  simpa [PaperTaylor.budget, PaperTaylor.beta] using
    small_a_ratio_10000 hm ha ha2 hx0 hx1 hr hbulk

-- Exact degree cutoffs, closed a=1/2, and the small-radius branch seam.
example {x : ℝ} (hx0 : -1 ≤ x) (hx1 : x ≤ 1) (hr : RawPolar 100000 (1 / 2) x) :
    PaperTaylor.budget 100000 (1 / 2) x / (1 - 1 / 2) < 83567 / 100000 :=
  small_a_ratio_100000 (by norm_num) (by norm_num) (by norm_num) hx0 hx1 hr

example {a x : ℝ} (ha : 0 < a) (ha2 : a ≤ 1 / 2) (hx0 : -1 ≤ x) (hx1 : x ≤ 1)
    (hr : RawPolar 10000 a x) (hbulk : 10000 * a ^ 2 * (1 - a) < 116) :
    PaperTaylor.budget 10000 a x / (1 - a) < 106 / 125 :=
  small_a_ratio_10000 (by norm_num) ha ha2 hx0 hx1 hr hbulk

example {x : ℝ} (hx0 : -1 ≤ x) (hx1 : x ≤ 1) (hr : RawPolar 100001 (1 / 5) x) :
    PaperTaylor.budget 100001 (1 / 5) x / (1 - 1 / 5) < 83567 / 100000 :=
  small_a_ratio_100000 (by norm_num) (by norm_num) (by norm_num) hx0 hx1 hr

-- RA04: expanded raw integral and B, on precisely the previously missing strip.
example {m : ℕ} {a x : ℝ} (hm : 256 ≤ m)
    (ha : 0 < a) (ha1 : a < 1) (hx0 : -1 ≤ x) (hx1 : x ≤ 1)
    (hr : 1 ≤ ∫ t in (0 : ℝ)..1,
      (a ^ 2 + 2 * a * (1 - a ^ 2) * x * t + (1 - a ^ 2) ^ 2 * t ^ 2) ^
        ((m : ℝ) / 2))
    (hl0 : 1 / 5 ≤ (m : ℝ) * (1 - a)) (hl1 : (m : ℝ) * (1 - a) < 2 / 5) :
    1 + 18 / (m : ℝ) <
      (m : ℝ) * x ^ 2 * (1 - (m : ℝ) * a / ((m : ℝ) + 1)) :=
  scaled_budget_lower_one hm ha ha1 hx0 hx1 hr hl0 (by unfold lambda; linarith)

example {m : ℕ} {a x : ℝ} (hm : 256 ≤ m)
    (ha : 0 < a) (ha1 : a < 1) (hx0 : -1 ≤ x) (hx1 : x ≤ 1)
    (hr : RawPolar m a x) (hl0 : 1 / 5 ≤ lambda m a) (hl1 : lambda m a ≤ 1) :
    (m : ℝ) / ((m : ℝ) + 1) * (1 + (24 / 49 - 8 / (m : ℝ)) / 5) ≤
      (m : ℝ) * x ^ 2 * (1 - (m : ℝ) * a / ((m : ℝ) + 1)) :=
  scaled_budget_paper_lower_one hm ha ha1 hx0 hx1 hr hl0 hl1

-- Both first-ray endpoints and the stitching point are retained at m=256.
example {a x : ℝ} (ha : 0 < a) (ha1 : a < 1) (hx0 : -1 ≤ x) (hx1 : x ≤ 1)
    (hr : RawPolar 256 a x) (hl : lambda 256 a = 1 / 5) :
    1 + 18 / (256 : ℝ) < 256 * x ^ 2 * PaperRayGeometry.B 256 a :=
  scaled_budget_lower_one (by norm_num) ha ha1 hx0 hx1 hr (by linarith) (by linarith)

example {a x : ℝ} (ha : 0 < a) (ha1 : a < 1) (hx0 : -1 ≤ x) (hx1 : x ≤ 1)
    (hr : RawPolar 256 a x) (hl : lambda 256 a = 2 / 5) :
    1 + 18 / (256 : ℝ) < 256 * x ^ 2 * PaperRayGeometry.B 256 a :=
  scaled_budget_lower_one (by norm_num) ha ha1 hx0 hx1 hr (by linarith) (by linarith)

example {a x : ℝ} (ha : 0 < a) (ha1 : a < 1) (hx0 : -1 ≤ x) (hx1 : x ≤ 1)
    (hr : RawPolar 256 a x) (hl : lambda 256 a = 1) :
    1 + 18 / (256 : ℝ) < 256 * x ^ 2 * PaperRayGeometry.B 256 a :=
  scaled_budget_lower_one (by norm_num) ha ha1 hx0 hx1 hr (by linarith) (by linarith)

-- Genuine nonvacuity at the least odd degree and the closed x=1 endpoint.
theorem raw_feasible : RawPolar 7 (3 / 5) 1 := by
  rw [rawPolar_iff]
  change 1 ≤ PaperSecant.R 7 (3 / 5) 1
  rw [PaperSecant.R_one (by norm_num) (by norm_num)]
  norm_num [PaperSecant.U1]

example : b (3 / 5) 1 ^ ((7 : ℝ) / 2) ≤
    ((9 : ℝ) / 2 * (1 - (3 / 5) ^ 2)) ^ (-(7 : ℝ) / (9 * (1 - (3 / 5) ^ 2))) := by
  simpa only [Nat.cast_ofNat, show (7 : ℝ) + 2 = 9 by norm_num] using
    endpoint_delta_rate (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) raw_feasible (by norm_num)

#print axioms endpoint_delta_rate
#print axioms small_a_ratio_100000
#print axioms small_a_ratio_10000
#print axioms scaled_budget_paper_lower_one
#print axioms scaled_budget_lower_one
#print axioms raw_feasible

-- Audit proof values, not just signatures. Forbid replacing rates with D.
open Lean Elab Command in
run_cmd do
  let env := (← getEnv).setExporting false
  let roots := #[
    (`Sendov.PaperRateDetails.endpoint_delta_rate,
      #[`Sendov.PaperGlobalPolar.log_mul_delta_le, `Sendov.PaperGlobalPolar.integral_chord]),
    (`Sendov.PaperRateDetails.small_a_ratio_100000,
      #[`Sendov.PaperHistoricalBounds.budget_lt_three_fifths,
        `Sendov.PaperHistoricalBounds.budget_lt_bulk116]),
    (`Sendov.PaperRateDetails.small_a_ratio_10000,
      #[`Sendov.PaperHistoricalBounds.budget_lt_three_fifths]),
    (`Sendov.PaperRateDetails.scaled_budget_lower_one,
      #[`Sendov.PaperRateDetails.product_lower_low_ray,
        `Sendov.PaperRayGeometry.product_lower_one,
        `Sendov.PaperPolar.b_le_alpha, `Sendov.PaperRay.ray_one])]
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
    for target in required do
      unless visited.contains target do
        throwError "rate proof missing required dependency {root} -> {target}"
    if visited.contains `sorryAx then throwError "unexpected proof hole"
    for name in visited.toList do
      if (`Sendov.PaperUniform).isPrefixOf name || (`Sendov.PaperNearClosure).isPrefixOf name then
        throwError "quantitative rate incorrectly depends on D closure: {name}"
    logInfo m!"PAPER_RATE_PROOF_CLOSURE_OK {root}"

end Sendov.PaperRateDetails.Tests
