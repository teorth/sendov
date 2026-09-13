import Sendov.Common.DistillationMiddleAlpha
import Solution

namespace LocalMiddleAlpha

open Sendov

theorem closed_real_strip {m α : ℝ} (hm : 5 ≤ m)
    (hα : 7 / 5 ≤ α) (hα2 : α ≤ 2) (hhalf : 2 * α ≤ m) :
    scalarObstruction m α (cubicPolarEnvelope α) < 1 :=
  distillScalar_lt_one_middle_alpha hm hα hα2 hhalf

theorem lower_endpoint_ray {m : ℝ} (hm : 5 ≤ m) :
    scalarObstruction m (7 / 5) (cubicPolarEnvelope (7 / 5)) < 1 :=
  closed_real_strip hm (by norm_num) (by norm_num) (by linarith)

theorem upper_endpoint_ray {m : ℝ} (hm : 5 ≤ m) :
    scalarObstruction m 2 (cubicPolarEnvelope 2) < 1 :=
  closed_real_strip hm (by norm_num) (by norm_num) (by linarith)

theorem split_endpoint_ray {m : ℝ} (hm : 5 ≤ m) :
    scalarObstruction m (17 / 10) (cubicPolarEnvelope (17 / 10)) < 1 :=
  closed_real_strip hm (by norm_num) (by norm_num) (by linarith)

theorem original_natural_degree {n : ℕ} (hn : 6 ≤ n) {α : ℝ}
    (hα : 7 / 5 ≤ α) (hα2 : α ≤ 2) (hhalf : 2 * α ≤ M n) :
    scalarObstruction (M n) α (cubicPolarEnvelope α) < 1 := by
  apply closed_real_strip _ hα hα2 hhalf
  have hnreal : (6 : ℝ) ≤ n := by exact_mod_cast hn
  unfold M
  linarith

theorem noninteger_degree_lower :
    scalarObstruction (11 / 2) (3 / 2) (cubicPolarEnvelope (3 / 2)) < 1 :=
  closed_real_strip (by norm_num) (by norm_num) (by norm_num) (by norm_num)

theorem noninteger_degree_upper :
    scalarObstruction (201 / 20) (19 / 10) (cubicPolarEnvelope (19 / 10)) < 1 :=
  closed_real_strip (by norm_num) (by norm_num) (by norm_num) (by norm_num)

theorem degree_five_lower :
    scalarObstruction 5 (7 / 5) (cubicPolarEnvelope (7 / 5)) < 1 :=
  lower_endpoint_ray (by norm_num)

theorem degree_five_upper : scalarObstruction 5 2 (cubicPolarEnvelope 2) < 1 :=
  upper_endpoint_ray (by norm_num)

theorem inherited_join {m α : ℝ} (hm : 5 ≤ m) (hα : 0 < α) (hα2 : α ≤ 2) :
    scalarObstruction m α (cubicPolarEnvelope α) < 1 :=
  distillScalar_lt_one_alpha_le_two hm hα hα2 (by linarith)

theorem old_whole_chord_counterexample :
    distillChordTotal 13 (10 / 7) = 1 + 426061 / 212373252 := by
  norm_num [distillChordTotal, distillEBudget]

theorem original_at_whole_chord_counterexample :
    scalarObstruction 13 (10 / 7) (cubicPolarEnvelope (10 / 7)) < 1 :=
  closed_real_strip (by norm_num) (by norm_num) (by norm_num) (by norm_num)

theorem old_rational_peak_lower_obstruction : 1 < distillRationalPeak (7 / 5) := by
  norm_num [distillRationalPeak, distillElementary, distillPeak0, distillPeakD,
    distillRatio, cubicPolarEnvelope, distillRationalExpPeak, distillTaylor6,
    distillPeakRate1, distillPeakRate2, distillPeakShift1, distillPeakBoost1, distillPeakNode]

theorem old_rational_peak_upper_obstruction : 1 < distillRationalPeak (19 / 10) := by
  norm_num [distillRationalPeak, distillElementary, distillPeak0, distillPeakD,
    distillRatio, cubicPolarEnvelope, distillRationalExpPeak, distillTaylor6,
    distillPeakRate1, distillPeakRate2, distillPeakShift1, distillPeakBoost1, distillPeakNode]

theorem raw_zero_unchanged (m : ℝ) :
    scalarObstruction m 0 (cubicPolarEnvelope 0) = 1 / (2 * m) :=
  scalarObstruction_zero m

theorem final_consumer_at_six :
    scalarObstruction (M 6) (19 / 10) (cubicPolarEnvelope (19 / 10)) < 1 :=
  distillScalar_lt_one (by norm_num) (by norm_num) (by norm_num) (by norm_num [M])

theorem retained_old_domain_at_six :
    scalarObstruction (M 6) (5 / 2) (cubicPolarEnvelope (5 / 2)) < 1 :=
  distillScalar_lt_one (by norm_num) (by norm_num) (by norm_num) (by norm_num [M])

end LocalMiddleAlpha

open Lean Elab Command in
run_cmd do
  let env := (← getEnv).setExporting false
  for (consumer, targets) in #[
      (`Sendov.distillScalar_lt_one_middle_alpha,
        #[`Sendov.distillScalar_le_elementary_components, `Sendov.distillElementary_le_middle,
          `Sendov.distillT0_le_middle, `Sendov.distillT1_le_middle, `Sendov.distillT2_le_middle]),
      (`Sendov.distillT0_le_middle, #[`Sendov.distillT0_le_mixed_rational]),
      (`Sendov.distillT1_le_middle,
        #[`Sendov.distillT1_le_mixed_peak, `Sendov.distill_mixed_peak1_le_linear]),
      (`Sendov.distillT2_le_middle,
        #[`Sendov.distillT2_le_mixed_peak, `Sendov.distill_mixed_peak2_le_linear]),
      (`Sendov.distillScalar_le_correlated_peak2,
        #[`Sendov.distillScalar_le_elementary_components]),
      (`Sendov.distillScalar_lt_one_alpha_le_two,
        #[`Sendov.distillScalar_lt_one_middle_alpha, `Sendov.distillScalar_lt_one_small_alpha]),
      (`Sendov.distillScalar_lt_one_real,
        #[`Sendov.distillScalar_lt_one_alpha_le_two, `Sendov.distillScalar_lt_one_peak_strip]),
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
        throwError "not an actual consumer: {consumer} -> {target}"
      logInfo m!"MIDDLE_ALPHA_CONSUMER {consumer} -> {target}"
  for root in #[`Sendov.distillScalar_lt_one_middle_alpha,
      `Sendov.distillScalar_lt_one_alpha_le_two, `LocalMiddleAlpha.original_natural_degree] do
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
      for forbidden in #["CriticalRow", "distillFinite", "DistillationFinite",
          "DistillationTail", "interval_55_61", "_le_61", "_antitone_55",
          "distillScalar_le_rationalPeak", "distillT0_le_peak"] do
        if (text.splitOn forbidden).length > 1 then
          throwError "forbidden proof-value dependency: {root} -> {name}"
    let axioms ← withEnv env <| Lean.collectAxioms root
    unless axioms.all (#[``propext, ``Classical.choice, ``Quot.sound].contains) do
      throwError "unexpected axioms for {root}: {axioms}"
    logInfo m!"MIDDLE_ALPHA_FULL_VALUE_CLOSURE {root}: {visited.size} declarations"
    logInfo m!"No namespace pruning; no rows, old interval/tail, or discarded-factor T0 peak"
    logInfo m!"MIDDLE_ALPHA_AXIOMS {root}: {axioms}"
  for root in #[`LocalMiddleAlpha.noninteger_degree_upper,
      `LocalMiddleAlpha.old_whole_chord_counterexample,
      `LocalMiddleAlpha.old_rational_peak_lower_obstruction,
      `LocalMiddleAlpha.old_rational_peak_upper_obstruction,
      `SendovConjecture.sendov, `SendovConjecture.phelps_rodriguez] do
    let axioms ← withEnv env <| Lean.collectAxioms root
    unless axioms.all (#[``propext, ``Classical.choice, ``Quot.sound].contains) do
      throwError "unexpected axioms for {root}: {axioms}"
    logInfo m!"MIDDLE_ALPHA_REGRESSION_AXIOMS {root}: {axioms}"
