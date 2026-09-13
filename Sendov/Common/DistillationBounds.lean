import Sendov.Common.DistillationFinite
import Sendov.LargeDegree.DistillationTailBound

/-!
# The complete scalar upper bound

The original degree is `n`; the scalar parameter is `m = n - 1`.
The scalar consumer uses finite rows for `5 ≤ m ≤ 63` and the real-degree
tail based on the existing row 64 for `m ≥ 64`. These disjoint ranges cover
every natural `m ≥ 5`; exactly the 60 records from 5 through 64 are retained.
-/
namespace Sendov

/-- The cubic scalar obstruction is strictly below one on the full domain
produced by the geometric reduction. No numerical or tail premise remains. -/
theorem distillScalar_lt_one {n : ℕ} (hn : 6 ≤ n) {α : ℝ}
    (hα : 0 < α) (h17 : α ≤ 17) (hhalf : 2 * α ≤ M n) :
    scalarObstruction (M n) α (cubicPolarEnvelope α) < 1 := by
  have hn1 : 1 ≤ n := by omega
  have hM : ((n - 1 : ℕ) : ℝ) = M n := by
    rw [Nat.cast_sub hn1]
    simp [M]
  have hm : 5 ≤ n - 1 := by omega
  rw [← hM] at hhalf ⊢
  by_cases hfinite : n - 1 < 64
  · exact (distillFinite_scalar hm (by omega) hα (by linarith) h17).trans (by norm_num)
  · have hlarge : (64 : ℝ) ≤ (n - 1 : ℕ) := by exact_mod_cast (show 64 ≤ n - 1 by omega)
    exact (distillScalar_lt_199_200 hlarge hα h17).trans (by norm_num)

end Sendov
