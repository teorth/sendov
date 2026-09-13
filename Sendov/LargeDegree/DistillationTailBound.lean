import Sendov.Common.DistillationMajorant
import Sendov.LargeDegree.DistillationTail
import Sendov.DistillationFinite.Row81

/-!
# The proved infinite tail

The critical-point certificate at `m = 81` closes the base required by the
real-degree antitonicity argument. No finite base or monotonicity is assumed.
The degree convention is `m = n - 1`: this tail starts at polynomial degree 82.
The underlying mathematical route is Senjian An's *Proof Distillation for Sendov's
Conjecture*, revision e8ae601491ec171ab4f7f8456113dd6a047aa85d, Sections 7--8
(CC BY 4.0, https://creativecommons.org/licenses/by/4.0/).
-/

namespace Sendov

/-- The regularized four-component bound is strictly below two thirds for every
real `m ≥ 81`, including alpha zero. The base is the actual critical certificate. -/
theorem distillComponents_lt_two_thirds {m α : ℝ} (hm : 81 ≤ m)
    (hα : 0 ≤ α) (h17 : α ≤ 17) :
    distillEBudget m + distillT0 m α + distillT1 m α + distillT2 m α < 2 / 3 := by
  exact distillComponents_lt_two_thirds_of_base
    (fun _ h0 hmax => distillFiniteTailBase h0 hmax) hm hα h17

/-- The raw scalar obstruction is bounded on the positive-alpha domain used by
actual polynomial data. This does not redefine its zero value by continuity. -/
theorem distillScalar_lt_two_thirds {m α : ℝ} (hm : 81 ≤ m)
    (hα : 0 < α) (h17 : α ≤ 17) :
    scalarObstruction m α (cubicPolarEnvelope α) < 2 / 3 := by
  have hm5 : 5 ≤ m := by linarith
  have hαm : 2 * α ≤ m := by linarith
  exact (distillScalar_le_majorant hm5 hα hαm).trans_lt
    (distillComponents_lt_two_thirds hm hα.le h17)

end Sendov
