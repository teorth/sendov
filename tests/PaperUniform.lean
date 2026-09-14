import Sendov.Analytic.PaperUniform

open MeasureTheory

namespace Sendov.PaperUniformAcceptance

/-- Exact public signature: no endpoint, tail, geometry or finite-table premises. -/
theorem exact_signature (m : ℕ) (a x : ℝ) (hm : 256 ≤ m)
    (ha : 0 < a) (ha1 : a < 1) (hx0 : -1 ≤ x) (hx1 : x ≤ 1)
    (hr : PaperPolar.RawPolar m a x) :
    PaperTaylor.budget (m : ℝ) a x < 1 - (m : ℝ) * a / ((m : ℝ) + 1) :=
  PaperUniform.uniform_D hm ha ha1 hx0 hx1 hr

/-- Both integrals expanded, retaining the actual unrelaxed exponent. -/
theorem expanded_integrals (m : ℕ) (a x : ℝ) (hm : 256 ≤ m)
    (ha : 0 < a) (ha1 : a < 1) (hx0 : -1 ≤ x) (hx1 : x ≤ 1)
    (hr : 1 ≤ ∫ t in (0 : ℝ)..1,
      (a ^ 2 + 2 * a * (1 - a ^ 2) * x * t + (1 - a ^ 2) ^ 2 * t ^ 2) ^
        ((m : ℝ) / 2)) :
    (1 - 2 * a * x + a ^ 2) ^ ((m : ℝ) / 2) + (m : ℝ) * a ^ 2 *
      (∫ t in (0 : ℝ)..1,
        t * (1 - 2 * a * x * t + a ^ 2 * t ^ 2) ^ (((m : ℝ) - 1) / 2)) <
      1 - (m : ℝ) * a / ((m : ℝ) + 1) := by
  change PaperPolar.RawPolar m a x at hr
  simpa only [PaperTaylor.budget, PaperTaylor.beta, mul_one, one_pow] using
    PaperUniform.uniform_D hm ha ha1 hx0 hx1 hr

/-- The cutoff itself, not just degrees strictly above it. -/
example (a x : ℝ) (ha : 0 < a) (ha1 : a < 1) (hx0 : -1 ≤ x) (hx1 : x ≤ 1)
    (hr : PaperPolar.RawPolar 256 a x) :
    PaperTaylor.budget 256 a x < 1 - 256 * a / 257 := by
  have h := PaperUniform.uniform_D (by norm_num : 256 ≤ 256) ha ha1 hx0 hx1 hr
  norm_num at h
  exact h

example (m : ℕ) (a x : ℝ) (hm : 256 ≤ m)
    (ha : 0 < a) (ha1 : a < 1) (hx0 : -1 ≤ x) (hx1 : x ≤ 1)
    (hr : PaperPolar.RawPolar m a x) : PaperTaylor.budget (m : ℝ) a x < 2 / 3 :=
  PaperUniform.budget_lt_two_thirds hm ha ha1 hx0 hx1 hr

example (m : ℕ) (a x : ℝ) (hm : 256 ≤ m)
    (ha : 0 < a) (ha1 : a < 1) (ha3 : 1 / 3 ≤ a) (hx0 : -1 ≤ x) (hx1 : x ≤ 1)
    (hr : PaperPolar.RawPolar m a x) :
    PaperTaylor.budget (m : ℝ) a x < 16 / ((m : ℝ) * a ^ 2) + 24 / (m : ℝ) :=
  PaperUniform.budget_lt_retained hm ha ha1 ha3 hx0 hx1 hr

#check @PaperUniform.uniform_D
#print axioms PaperUniform.exp_seventeen_fifths
#print axioms PaperUniform.budget_lt_two_thirds
#print axioms PaperUniform.budget_lt_retained
#print axioms PaperUniform.finite_rays_D
#print axioms PaperUniform.uniform_D
#print axioms exact_signature
#print axioms expanded_integrals

-- Audit proof values, not merely the import list or declaration types.
open Lean Elab Command in
run_cmd do
  let env := (← getEnv).setExporting false
  let mut pending := [`Sendov.PaperUniformAcceptance.expanded_integrals]
  let mut visited : Std.HashSet Name := {}
  while !pending.isEmpty do
    let name := pending.head!
    pending := pending.tail!
    unless visited.contains name do
      visited := visited.insert name
      let some ci := env.find? name | throwError "missing closure declaration {name}"
      if let .axiomInfo _ := ci then
        unless #[`propext, `Classical.choice, `Quot.sound].contains name do
          throwError "nonstandard axiom in uniform D: {name}"
      if let some v := ci.value? (allowOpaque := true) then
        for used in v.getUsedConstants do pending := used :: pending
  for target in #[`Sendov.PaperUniform.uniform_D,
      `Sendov.PaperUniform.budget_lt_two_thirds,
      `Sendov.PaperUniform.budget_lt_retained,
      `Sendov.PaperGlobalPolar.endpoint_le,
      `Sendov.PaperGlobalPolar.degree_mul_sq_gt,
      `Sendov.PaperUniform.exp_seventeen_fifths,
      `Sendov.PaperTwoEnd.budget_lt_separated,
      `Sendov.PaperTwoEnd.budget_lt_middle,
      `Sendov.PaperTail.middle_antitone,
      `Sendov.PaperTail.middle_tail,
      `Sendov.PaperBulk.middle_budget,
      `Sendov.PaperBulk.large_ray_budget,
      `Sendov.PaperNearClosure.near_endpoint_D,
      `Sendov.PaperTail.budget_region_one,
      `Sendov.PaperTail.budget_region_two,
      `Sendov.PaperTail.budget_region_three,
      `Sendov.PaperTail.budget_region_four,
      `Sendov.PaperRayGeometry.budget_lower_one,
      `Sendov.PaperRayGeometry.budget_lower_ten,
      `Sendov.PaperRayGeometry.budget_lower_twentyfive,
      `Sendov.PaperRayGeometry.budget_lower_fortynine,
      `Sendov.PaperRayGeometry.halfpoint_mem] do
    unless visited.contains target do
      throwError "missing uniform D proof-value dependency {target}"
    logInfo m!"UNIFORM_D_VALUE {target}"
  logInfo "UNIFORM_D_AXIOMS_ONLY propext Classical.choice Quot.sound"

end Sendov.PaperUniformAcceptance
