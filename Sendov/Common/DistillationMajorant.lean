import Sendov.Common.DistillationFactors
import Sendov.Common.TwoChord

/-!
# The proved scalar majorant

This joins the two-chord integral estimate to the regularized factors from
Senjian An's *Proof Distillation for Sendov's Conjecture*, revision
`e8ae601491ec171ab4f7f8456113dd6a047aa85d`, Section 4.
Mathematical source: https://github.com/SJanPerth/Sendov-Proof-Distillation
(CC BY 4.0; https://creativecommons.org/licenses/by/4.0/).
This is a new Lean formulation. The integral bound is proved, not an assumption.
The remaining finite and tail component bounds are separate theorems.
-/

namespace Sendov

/-- The complete two-chord upper bound for the cubic scalar obstruction.
Positive alpha is intentional: the raw scalar definition at zero is not its
continuous extension. No extra integrability or geometric feasibility is needed. -/
theorem distillScalar_le_majorant {m α : ℝ} (hm : 5 ≤ m) (hα : 0 < α)
    (hαm : 2 * α ≤ m) :
    scalarObstruction m α (cubicPolarEnvelope α) ≤
      distillEBudget m + distillT0 m α + distillT1 m α + distillT2 m α := by
  apply distillScalar_le_components hm hα
  simpa only [distillNode_eq] using
    integral_polarKernel_two_chord hm hα.le hαm
      (cubicPolarEnvelope_nonneg hα.le) (cubicPolarEnvelope_lt_one hα.le)

end Sendov
