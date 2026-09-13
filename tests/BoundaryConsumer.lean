import Lean
import Sendov.Common.DistillationCritical
import Sendov.LargeDegree.DistillationTailBound

namespace MathPolishBoundary

/-- The totalized raw obstruction retains its actual zero-endpoint value. -/
theorem raw_zero (m : ℝ) :
    Sendov.scalarObstruction m 0 (Sendov.cubicPolarEnvelope 0) = 1 / (2 * m) :=
  Sendov.scalarObstruction_zero m

/-- The tail component vanishes at the closed left endpoint. -/
theorem tail_zero {m : ℝ} (hm : 64 ≤ m) : Sendov.distillT2 m 0 = 0 :=
  Sendov.distillT2_zero hm

/-- Both boundary identities are consumed together at the real tail threshold. -/
theorem threshold_boundary :
    Sendov.scalarObstruction 64 0 (Sendov.cubicPolarEnvelope 0) = 1 / 128 ∧
      Sendov.distillT2 64 0 = 0 := by
  constructor
  · convert raw_zero 64 using 1
    norm_num
  · exact tail_zero (by norm_num)

theorem closed_tail {m α : ℝ} (hm : 64 ≤ m) (hα : 0 ≤ α) (h17 : α ≤ 17) :
    Sendov.distillEBudget m + Sendov.distillT0 m α +
      Sendov.distillT1 m α + Sendov.distillT2 m α < 199 / 200 :=
  Sendov.distillComponents_lt_199_200 hm hα h17

end MathPolishBoundary

open Lean Elab Command in
run_cmd do
  let env := (← getEnv).setExporting false
  for (consumer, target) in #[
      (`MathPolishBoundary.raw_zero, `Sendov.scalarObstruction_zero),
      (`MathPolishBoundary.tail_zero, `Sendov.distillT2_zero),
      (`MathPolishBoundary.closed_tail, `Sendov.distillComponents_lt_199_200)] do
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
