import Sendov.Common.DistillationMiddleAlpha
import Sendov.Common.DistillationPeakClosure

/-!
# The complete scalar bound without finite degree certificates

Both alpha regions hold for every legal real degree m >= 5. The shared endpoint
alpha = 2 joins them without a degree split or a numerical base row.
-/
namespace Sendov

/-- The entire original scalar domain, with no finite-degree or tail premise. -/
theorem distillScalar_lt_one_real {m α : ℝ} (hm : 5 ≤ m)
    (hα : 0 < α) (h17 : α ≤ 17) (hhalf : 2 * α ≤ m) :
    scalarObstruction m α (cubicPolarEnvelope α) < 1 := by
  by_cases hlow : α ≤ 2
  · exact distillScalar_lt_one_alpha_le_two hm hα hlow hhalf
  · exact distillScalar_lt_one_peak_strip hm (by linarith) h17 hhalf

/-- The original geometric-reduction interface retains its literal contract. -/
theorem distillScalar_lt_one {n : ℕ} (hn : 6 ≤ n) {α : ℝ}
    (hα : 0 < α) (h17 : α ≤ 17) (hhalf : 2 * α ≤ M n) :
    scalarObstruction (M n) α (cubicPolarEnvelope α) < 1 := by
  have hm : 5 ≤ M n := by
    have hnR : (6 : ℝ) ≤ n := by exact_mod_cast hn
    unfold M
    linarith
  exact distillScalar_lt_one_real hm hα h17 hhalf

end Sendov
