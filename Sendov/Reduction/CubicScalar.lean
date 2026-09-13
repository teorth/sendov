import Sendov.Reduction.Alpha17
import Sendov.Reduction.CubicPolar

/-!
# Raw polar and origin inequalities imply the cubic scalar obstruction

This is the geometric-to-scalar reduction for degrees at least six. It consumes
only the original weak polar integral and original origin inequality. In
particular, the alpha range and eta domain are conclusions, not extra inputs.

The analytic origin reduction remains `one_le_of_origin` in `Simplified`, via
`one_le_scalarObstruction_of_origin`, reusing the established eta domain.
The strict cubic polar bound and
eta monotonicity then enlarge the actual scalar obstruction. No finite-range
certificate, tail bound, or old `R` enlargement is used here.
-/

namespace Sendov

/-- The four facts required by the cubic finite/tail endgame, all derived from
raw geometric inputs. The final conjunction is a lower bound, not a premise. -/
theorem cubicScalar_constraints_of_polar_origin {n : ℕ} (hn : 6 ≤ n) {a x α : ℝ}
    (ha : 0 < a) (ha1 : a < 1) (hx : x ^ 2 ≤ 1)
    (hα : α = M n * (1 - a ^ 2) / 2)
    (hpolar : 1 ≤ ∫ t in (0 : ℝ)..1, Ppolar a x t ^ (((n : ℝ) - 1) / 2))
    (horigin : 2 * α + a * x ≤ (1 - x ^ 2) / (2 * M n)
      + a ^ 2 * n * M n * ∫ t in (0 : ℝ)..1,
        t * QQ (a * x) (a ^ 2) t ^ (((n : ℝ) - 2) / 2)) :
    (0 < α) ∧ (2 * α ≤ M n) ∧ (α ≤ 17) ∧
      (1 ≤ scalarObstruction (M n) α (cubicPolarEnvelope α)) := by
  have hn2 : 2 ≤ n := by omega
  have hn5 : 5 ≤ n := by omega
  have hm : 5 ≤ M n := by
    have hnR : (6 : ℝ) ≤ n := by exact_mod_cast hn
    unfold M
    linarith
  have hα0 := alpha_pos hn2 ha1 ha.le hα
  have hhalf : 2 * α ≤ M n := by linarith [alpha_le_half hn2 hα]
  have hη := actualEta_mem_Ico_of_polar hn2 ha.le ha1 hx hα hpolar
  have hlt := polar_exp hn2 hx hα hpolar
  have hbeta := beta_le hα0 hη.1 hlt
  have hlog := log_le_alpha_mul hα0 hη.2.le hlt
  have h17 := alpha_le_seventeen hn5 ha ha1 hx hα hbeta hlog horigin
  have hactual := one_le_scalarObstruction_of_origin hn5 ha ha1 hx hα hη.2 horigin
  have hcubic := eta_lt_cubicPolarEnvelope hα0 h17 hη.1 hη.2 hlt
  exact ⟨hα0, hhalf, h17, hactual.trans
    (scalarObstruction_mono_eta hm hα0 hη.1 hcubic.le (cubicPolarEnvelope_lt_one hα0.le))⟩

end Sendov
