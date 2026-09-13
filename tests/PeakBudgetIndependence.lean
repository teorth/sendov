import Sendov.Common.DistillationPeakRest

/-! The complementary budget must not import the first peak's heavy certificate. -/
open Sendov Sendov.PeakClosure

example (a : ℝ) : budget1 a = (431 - 3 * a) / 2500 := rfl

example {a : ℝ} (ha : 2 ≤ a) (h17 : a ≤ 17) :
    distillElementary (max 5 (2 * a)) a + distillPeak0 a +
        (421 / 12500) * distillRatio a *
          distillRationalExpPeak a (distillPeakRate2 a) (distillPeakRate2 a * (2 * a - 3)) <
      1 - budget1 a :=
  rest_lt_budget ha h17

open Lean Elab Command in
run_cmd do
  let env := (← getEnv).setExporting false
  if env.header.moduleNames.contains `Sendov.Common.DistillationPeakFirst then
    throwError "complementary budget still imports the first peak certificate"
  if env.contains `Sendov.PeakClosure.peak1_lt_budget then
    throwError "first peak certificate leaked into the complementary budget environment"
  let some idx := env.getModuleIdxFor? `Sendov.PeakClosure.budget1 |
    throwError "missing shared budget owner"
  unless env.header.moduleNames[idx.toNat]! == `Sendov.Common.DistillationPeakAlgebra do
    throwError "shared budget is not owned by the common algebra module"
  logInfo "PEAK_BUDGET_INDEPENDENT: original budget and rest type, without First"
