import Sendov.Common.DistillationMajorant
import Sendov.LargeDegree.DistillationTail
import Sendov.DistillationFinite.Rows61_61

/-!
# The proved infinite tail

The existing critical-point row at `m = 61` supplies the earlier `<199/200`
tail, starting at polynomial degree 62. No finite base or monotonicity is assumed.
The underlying mathematical route is Senjian An's *Proof Distillation for Sendov's
Conjecture*, revision e8ae601491ec171ab4f7f8456113dd6a047aa85d, Sections 7--8
(CC BY 4.0, https://creativecommons.org/licenses/by/4.0/).
-/

namespace Sendov

/-- The existing finite row closes the earlier tail on the full closed alpha
domain, including zero. No stronger row certificate at m=61 is required. -/
theorem distillComponents_lt_199_200 {m α : ℝ} (hm : 61 ≤ m)
    (hα : 0 ≤ α) (h17 : α ≤ 17) :
    distillEBudget m + distillT0 m α + distillT1 m α + distillT2 m α < 199 / 200 :=
  (distillComponents_le_61 hm hα h17).trans_lt
    ((distillFinite_61 α hα h17).trans_lt distillFiniteBound_61)

/-- Earlier raw scalar tail. Positive alpha is intentional; all of `α ≤ 17`
is covered, and `2 * α ≤ m` follows from the degree threshold. -/
theorem distillScalar_lt_199_200 {m α : ℝ} (hm : 61 ≤ m)
    (hα : 0 < α) (h17 : α ≤ 17) :
    scalarObstruction m α (cubicPolarEnvelope α) < 199 / 200 := by
  exact (distillScalar_le_majorant (by linarith) hα (by linarith)).trans_lt
    (distillComponents_lt_199_200 hm hα.le h17)

end Sendov
