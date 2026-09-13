import Lean
import Sendov.Common.DistillationCritical
import Sendov.LargeDegree.DistillationTail

namespace MathPolishBoundary

/-- The totalized raw obstruction retains its actual zero-endpoint value. -/
theorem raw_zero (m : ℝ) :
    Sendov.scalarObstruction m 0 (Sendov.cubicPolarEnvelope 0) = 1 / (2 * m) :=
  Sendov.scalarObstruction_zero m

/-- The tail component vanishes at the closed left endpoint. -/
theorem tail_zero {m : ℝ} (hm : 81 ≤ m) : Sendov.distillT2 m 0 = 0 :=
  Sendov.distillT2_zero hm

/-- Both boundary identities are consumed together at the real tail threshold. -/
theorem threshold_boundary :
    Sendov.scalarObstruction 81 0 (Sendov.cubicPolarEnvelope 0) = 1 / 162 ∧
      Sendov.distillT2 81 0 = 0 := by
  constructor
  · convert raw_zero 81 using 1
    norm_num
  · exact tail_zero (by norm_num)

end MathPolishBoundary

open Lean Elab Command in
run_cmd do
  let env := (← getEnv).setExporting false
  for (consumer, target) in #[
      (`MathPolishBoundary.raw_zero, `Sendov.scalarObstruction_zero),
      (`MathPolishBoundary.tail_zero, `Sendov.distillT2_zero)] do
    let some info := env.find? consumer | throwError "missing consumer {consumer}"
    let some value := info.value? (allowOpaque := true) | throwError "missing proof value"
    unless value.getUsedConstants.contains target do
      throwError "not a real value consumer: {consumer} -> {target}"
    logInfo m!"BOUNDARY_VALUE_CONSUMER {consumer} -> {target}"
  for target in #[`Sendov.distillComponents_le_of_mixed, `Sendov.distillL_eq,
      `Sendov.distillT0_nonneg, `Sendov.distillT1_nonneg, `Sendov.distillT2_nonneg,
      `Sendov.QQ_zero, `Sendov.QQ_le_one] do
    if env.contains target then throwError "retired declaration remains: {target}"
  logInfo "BOUNDARY_PASS: actual zero identities consumed; seven retired declarations absent"
