import Sendov.Common.DistillationPeakClosure
import Solution

namespace LocalPeakClosure

open Sendov

theorem uniform_alpha {α : ℝ} (hα : 2 ≤ α) (h17 : α ≤ 17) :
    distillRationalPeak α < 1 :=
  distillRationalPeak_lt_one hα h17

theorem original_real_ray {m α : ℝ} (hm : 5 ≤ m) (hα : 2 ≤ α)
    (h17 : α ≤ 17) (hhalf : 2 * α ≤ m) :
    scalarObstruction m α (cubicPolarEnvelope α) < 1 :=
  distillScalar_lt_one_peak_strip hm hα h17 hhalf

example : scalarObstruction 5 2 (cubicPolarEnvelope 2) < 1 :=
  original_real_ray (by norm_num) (by norm_num) (by norm_num) (by norm_num)

example : scalarObstruction 5 (5 / 2) (cubicPolarEnvelope (5 / 2)) < 1 :=
  original_real_ray (by norm_num) (by norm_num) (by norm_num) (by norm_num)

example : scalarObstruction 34 17 (cubicPolarEnvelope 17) < 1 :=
  original_real_ray (by norm_num) (by norm_num) (by norm_num) (by norm_num)

example : scalarObstruction (137 / 4) 17 (cubicPolarEnvelope 17) < 1 :=
  original_real_ray (by norm_num) (by norm_num) (by norm_num) (by norm_num)

example : ¬ 2 * (17 : ℝ) ≤ 5 := by norm_num

theorem strict_margin_needed : 199 / 200 < distillRationalPeak 17 := by
  norm_num [distillRationalPeak, distillElementary, distillPeak0, distillPeakD,
    distillRatio, cubicPolarEnvelope, distillRationalExpPeak, distillTaylor6,
    distillPeakRate1, distillPeakRate2, distillPeakShift1, distillPeakBoost1, distillPeakNode]

theorem lower_interval_obstruction : 1 < distillRationalPeak (19 / 10) := by
  norm_num [distillRationalPeak, distillElementary, distillPeak0, distillPeakD,
    distillRatio, cubicPolarEnvelope, distillRationalExpPeak, distillTaylor6,
    distillPeakRate1, distillPeakRate2, distillPeakShift1, distillPeakBoost1, distillPeakNode]

theorem upper_interval_obstruction : 1 < distillRationalPeak 18 := by
  norm_num [distillRationalPeak, distillElementary, distillPeak0, distillPeakD,
    distillRatio, cubicPolarEnvelope, distillRationalExpPeak, distillTaylor6,
    distillPeakRate1, distillPeakRate2, distillPeakShift1, distillPeakBoost1, distillPeakNode]

noncomputable def thirdOrderCandidate (α : ℝ) : ℝ :=
  distillElementary (max 5 (2 * α)) α + distillPeak0 α +
    (259 / 12500) * distillRatio α *
      ((27 * (249 / 5000) / distillPeakRate1 α ^ 3 +
          8 * α * (677 / 5000) / distillPeakRate1 α ^ 2) /
        (1 + distillPeakShift1 α + distillPeakShift1 α ^ 2 / 2 +
          distillPeakShift1 α ^ 3 / 6)) +
    (421 / 12500) * distillRatio α *
      distillRationalExpPeak α (distillPeakRate2 α) (distillPeakRate2 α * (2 * α - 3))

/-- Dropping one more Taylor term breaks this particular majorant at the endpoint. -/
theorem third_order_obstruction : 1 < thirdOrderCandidate 17 := by
  norm_num [thirdOrderCandidate, distillElementary, distillPeak0, distillPeakD,
    distillRatio, cubicPolarEnvelope, distillRationalExpPeak, distillTaylor6,
    distillPeakRate1, distillPeakRate2, distillPeakShift1, distillPeakBoost1, distillPeakNode]

theorem raw_zero_unchanged : scalarObstruction 5 0 (cubicPolarEnvelope 0) = 1 / 10 := by
  norm_num [scalarObstruction_zero]

open Polynomial in
example {p : ℂ[X]} (hdeg : 2 ≤ p.natDegree)
    (hzeroes : ∀ w : ℂ, p.eval w = 0 → ‖w‖ ≤ 1) {a : ℂ} (hpa : p.eval a = 0) :
    ∃ ζ : ℂ, (derivative p).eval ζ = 0 ∧ ‖ζ - a‖ ≤ 1 :=
  SendovConjecture.sendov hdeg hzeroes hpa

open Polynomial in
example {p : ℂ[X]} (hdeg : 2 ≤ p.natDegree)
    (hzeroes : ∀ w : ℂ, p.eval w = 0 → ‖w‖ ≤ 1) {a : ℂ} (hpa : p.eval a = 0) :
    (∃ ζ : ℂ, (derivative p).eval ζ = 0 ∧ ‖ζ - a‖ < 1) ∨
      (‖a‖ = 1 ∧ ∃ c : ℂ, c ≠ 0 ∧
        p = C c * (X ^ p.natDegree - C (a ^ p.natDegree))) :=
  SendovConjecture.phelps_rodriguez hdeg hzeroes hpa

end LocalPeakClosure

open Lean Elab Command in
run_cmd do
  let env := (← getEnv).setExporting false
  for (consumer, targets) in #[
      (`Sendov.PeakClosure.gap1_pos, #[`Sendov.PeakClosure.gap1_identity]),
      (`Sendov.PeakClosure.gapLow_pos, #[`Sendov.PeakClosure.LowHomogeneous.positive]),
      (`Sendov.PeakClosure.LowHomogeneous.positive,
        #[`Sendov.PeakClosure.LowHomogeneous.identity]),
      (`Sendov.PeakClosure.LowHomogeneous.identity,
        #[`Sendov.PeakClosure.LowHomogeneous.gapH_eval,
          `Sendov.PeakClosure.LowHomogeneous.gapH_identity]),
      (`Sendov.PeakClosure.gapHigh_pos, #[`Sendov.PeakClosure.HighHomogeneous.positive]),
      (`Sendov.PeakClosure.HighHomogeneous.positive,
        #[`Sendov.PeakClosure.HighHomogeneous.identity]),
      (`Sendov.PeakClosure.HighHomogeneous.identity,
        #[`Sendov.PeakClosure.HighHomogeneous.gapH_eval,
          `Sendov.PeakClosure.HighHomogeneous.gapH_identity]),
      (`Sendov.PeakClosure.peak1_lt_budget,
        #[`Sendov.PeakClosure.gap1_pos, `Sendov.PeakClosure.peak1_le_four]),
      (`Sendov.PeakClosure.rest_lt_budget,
        #[`Sendov.PeakClosure.gapLow_pos, `Sendov.PeakClosure.gapHigh_pos,
          `Sendov.PeakClosure.gapLow_eq, `Sendov.PeakClosure.gapHigh_eq,
          `Sendov.PeakClosure.peak2_eq]),
      (`Sendov.distillRationalPeak_lt_one,
        #[`Sendov.PeakClosure.peak1_lt_budget, `Sendov.PeakClosure.rest_lt_budget]),
      (`Sendov.distillScalar_lt_one_peak_strip,
        #[`Sendov.distillScalar_le_rationalPeak, `Sendov.distillRationalPeak_lt_one]),
      (`Sendov.distillScalar_lt_one_real,
        #[`Sendov.distillScalar_lt_one_peak_strip, `Sendov.distillScalar_lt_one_alpha_le_two]),
      (`Sendov.distillScalar_lt_one, #[`Sendov.distillScalar_lt_one_real]),
      (`Sendov.polar_origin_incompatible, #[`Sendov.distillScalar_lt_one]),
      (`Sendov.sendov_interior, #[`Sendov.polar_origin_incompatible]),
      (`Sendov.sendov_interior_real, #[`Sendov.sendov_interior]),
      (`Sendov.phelps_rodriguez, #[`Sendov.sendov_interior_real]),
      (`Sendov.sendov, #[`Sendov.phelps_rodriguez]),
      (`SendovConjecture.sendov, #[`Sendov.sendov]),
      (`SendovConjecture.phelps_rodriguez, #[`Sendov.phelps_rodriguez])] do
    let some info := env.find? consumer | throwError "missing declaration {consumer}"
    let some value := info.value? (allowOpaque := true) | throwError "missing proof {consumer}"
    for target in targets do
      unless value.getUsedConstants.contains target do
        throwError "not an actual value consumer: {consumer} -> {target}"
      logInfo m!"PEAK_CLOSURE_CONSUMER {consumer} -> {target}"
  for root in #[`Sendov.distillRationalPeak_lt_one, `Sendov.distillScalar_lt_one_peak_strip] do
    let mut pending := [root]
    let mut visited : Std.HashSet Name := {}
    while !pending.isEmpty do
      let name := pending.head!
      pending := pending.tail!
      unless visited.contains name do
        visited := visited.insert name
        let some info := env.find? name | throwError "missing closure declaration {name}"
        if let some value := info.value? (allowOpaque := true) then
          for used in value.getUsedConstants do
            pending := used :: pending
    for name in visited do
      let text := name.toString
      for forbidden in #["CriticalRow", "distillFinite", "DistillationTail",
          "interval_55_61", "_le_61", "_le_51", "_antitone_55"] do
        if (text.splitOn forbidden).length > 1 then
          throwError "old row/tail in new value closure: {root} -> {name}"
    logInfo m!"PEAK_CLOSURE_NO_ROWS_OR_OLD_TAIL {root}; full constants {visited.size}"
  for target in #[`Sendov.distillRationalPeak_lt_one, `Sendov.distillScalar_lt_one_peak_strip,
      `LocalPeakClosure.strict_margin_needed, `LocalPeakClosure.lower_interval_obstruction,
      `LocalPeakClosure.upper_interval_obstruction, `LocalPeakClosure.third_order_obstruction,
      `SendovConjecture.sendov, `SendovConjecture.phelps_rodriguez] do
    let axioms ← withEnv env <| Lean.collectAxioms target
    unless axioms.all (#[``propext, ``Classical.choice, ``Quot.sound].contains) do
      throwError "unexpected axiom in {target}: {axioms}"
    logInfo m!"PEAK_CLOSURE_AXIOMS {target}: {axioms}"
