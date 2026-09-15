import Sendov.Analytic.CenteredBandTail

noncomputable section
open scoped BigOperators
namespace Sendov.CenteredBand

def BConstant (p U : ℕ) (X : ℝ) : ℝ := (U:ℝ)^2*(2*(1-X))^(p+1)

/-- All three complex B_2 terms, uniformly in degree and radius. -/
theorem norm_B_two_le_power (m : ℕ) (hm : 7 ≤ m) (z : ℂ) (rho : ℝ)
    (hz : ‖z‖ ≤ 1) (hr0 : 0 ≤ rho) (hr1 : rho ≤ 1) (hw : ‖1-z‖ ≤ rho) :
    ‖PaperCentered.B m 2 z‖ ≤ (m:ℝ)^2*rho^(m-1) := by
  have hs : ‖PaperCentered.B m 2 z‖ ≤
      ∑ j ∈ Finset.range 3, ((m+1).choose j:ℝ)*rho^(m-1) := by
    unfold PaperCentered.B
    refine (norm_sum_le _ _).trans ?_
    apply Finset.sum_le_sum
    intro j hj
    have hj2 : j ≤ 2 := by have := Finset.mem_range.mp hj; omega
    have hpow : ‖1-z‖^(m+1-j) ≤ rho^(m-1) :=
      (pow_le_pow_left₀ (norm_nonneg _) hw _).trans
        (pow_le_pow_of_le_one hr0 hr1 (by omega))
    have hzpow := pow_le_one₀ (norm_nonneg z) hz (n := j)
    simp only [norm_mul, norm_pow, Complex.norm_natCast]
    calc
      _ = ((m+1).choose j:ℝ)*(‖z‖^j*‖1-z‖^(m+1-j)) := by ring
      _ ≤ ((m+1).choose j:ℝ)*(1*rho^(m-1)) :=
        mul_le_mul_of_nonneg_left
          (mul_le_mul hzpow hpow (pow_nonneg (norm_nonneg _) _) (by norm_num))
          (Nat.cast_nonneg _)
      _ = _ := by ring
  have hc : ((m+1).choose 2:ℝ) = (m:ℝ)*((m:ℝ)+1)/2 := by
    rw [Nat.cast_choose_two]; push_cast; ring
  have hsum : (∑ j ∈ Finset.range 3, ((m+1).choose j:ℝ)*rho^(m-1)) =
      (1+((m:ℝ)+1)+(m:ℝ)*((m:ℝ)+1)/2)*rho^(m-1) := by
    norm_num [Finset.sum_range_succ, Nat.choose_one_right, hc]
    ring
  rw [hsum] at hs
  apply hs.trans
  apply mul_le_mul_of_nonneg_right _ (pow_nonneg hr0 _)
  have hm7 : (7:ℝ) ≤ m := by exact_mod_cast hm
  nlinarith [sq_nonneg ((m:ℝ)-4)]

/-- The endpoint inequality uses the factor (1-a)(a+1-2X), not a false
monotonicity assertion when X exceeds 9/10. -/
lemma endpoint_quadratic_le (a x X : ℝ) (ha0 : 9/10 ≤ a) (ha1 : a ≤ 1)
    (hx : X ≤ x) (hX : X ≤ 19/20) : PaperPolar.b a x ≤ 2*(1-X) := by
  have hax := mul_le_mul_of_nonneg_left hx (show 0 ≤ a by linarith)
  have hprod := mul_nonneg (show 0 ≤ 1-a by linarith) (show 0 ≤ a+1-2*X by linarith)
  unfold PaperPolar.b
  nlinarith only [hax, hprod]

theorem norm_B_two_le_band (m p U : ℕ) (hm : 7 ≤ m) (hpm : 2*p+3 ≤ m)
    (hmU : m ≤ U) (z : ℂ) (X : ℝ) (hX0 : 1/2 ≤ X) (hX1 : X ≤ 1)
    (hz : ‖z‖ ≤ 1) (hw : ‖1-z‖^2 ≤ 2*(1-X)) :
    ‖PaperCentered.B m 2 z‖ ≤ BConstant p U X := by
  have hW : 0 ≤ 2*(1-X) := by linarith
  have hr : Real.sqrt (2*(1-X)) ≤ 1 :=
    (Real.sqrt_le_sqrt (show 2*(1-X) ≤ 1 by linarith)).trans_eq (by norm_num)
  have hwr : ‖1-z‖ ≤ Real.sqrt (2*(1-X)) := by
    nlinarith only [hw, Real.sq_sqrt hW, Real.sqrt_nonneg (2*(1-X)), norm_nonneg (1-z)]
  have hb := norm_B_two_le_power m hm z _ hz (Real.sqrt_nonneg _) hr hwr
  have hp := pow_le_pow_of_le_one (Real.sqrt_nonneg _) hr (show 2*(p+1) ≤ m-1 by omega)
  rw [pow_mul, Real.sq_sqrt hW] at hp
  have hmU' : (m:ℝ) ≤ U := by exact_mod_cast hmU
  have hsq := pow_le_pow_left₀ (Nat.cast_nonneg m) hmU' 2
  exact hb.trans (mul_le_mul hsq hp (pow_nonneg (Real.sqrt_nonneg _) _) (sq_nonneg _))

end Sendov.CenteredBand
