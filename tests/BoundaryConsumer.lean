import Sendov.Common.DistillationBounds

namespace MathPolishBoundary
open Sendov

theorem raw_zero (m : ℝ) :
    scalarObstruction m 0 (cubicPolarEnvelope 0) = 1 / (2 * m) :=
  scalarObstruction_zero m

theorem component_zero {m : ℝ} (hm : 5 ≤ m) : distillT2 m 0 = 0 := by
  have hexp : (m - 3) / 2 ≠ 0 := by linarith
  simp [distillT2, cubicPolarEnvelope, Real.zero_rpow hexp]

theorem legal_right_endpoint {α : ℝ} (hα : 5 / 2 ≤ α) (h17 : α ≤ 17) :
    scalarObstruction (2 * α) α (cubicPolarEnvelope α) < 1 :=
  distillScalar_lt_one_real (by linarith) (by linarith) h17 le_rfl

example : scalarObstruction 5 0 (cubicPolarEnvelope 0) = 1 / 10 ∧ distillT2 5 0 = 0 := by
  constructor
  · norm_num [raw_zero]
  · exact component_zero le_rfl

end MathPolishBoundary

open Lean Elab Command in
run_cmd do
  let env := (← getEnv).setExporting false
  for (consumer, target) in #[
      (`MathPolishBoundary.raw_zero, `Sendov.scalarObstruction_zero),
      (`MathPolishBoundary.legal_right_endpoint, `Sendov.distillScalar_lt_one_real)] do
    let some info := env.find? consumer | throwError "missing consumer {consumer}"
    let some value := info.value? (allowOpaque := true) | throwError "missing proof value"
    unless value.getUsedConstants.contains target do
      throwError "not a real value consumer: {consumer} -> {target}"
    logInfo m!"BOUNDARY_VALUE_CONSUMER {consumer} -> {target}"
