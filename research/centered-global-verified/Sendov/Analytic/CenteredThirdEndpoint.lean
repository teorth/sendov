import Sendov.Analytic.CenteredThirdScalar

noncomputable section
open scoped BigOperators
namespace Sendov.CenteredThird

def rho : ℝ := 19/60

def BEnvelope (m : ℕ) : ℝ :=
  (rho^2+((m:ℝ)+1)*rho+(m:ℝ)*((m:ℝ)+1)/2)*rho^(m-1)

lemma BEnvelope_decay (m : ℕ) (hm : 7 ≤ m) : BEnvelope m ≤ BEnvelope 7 := by
  induction m, hm using Nat.le_induction with
  | base => exact le_rfl
  | succ n hn ih =>
    have hnr : (7:ℝ) ≤ n := by exact_mod_cast hn
    apply le_trans _ ih
    unfold BEnvelope
    rw [show n+1-1 = (n-1)+1 by omega, pow_succ]
    push_cast
    calc
      _ = ((rho^2+((n:ℝ)+2)*rho+((n:ℝ)+1)*((n:ℝ)+2)/2)*rho)*rho^(n-1) := by ring
      _ ≤ _ := by
        apply mul_le_mul_of_nonneg_right _ (pow_nonneg (by norm_num [rho]) _)
        dsimp [rho]
        nlinarith [sq_nonneg (n:ℝ)]

/-- Every term of the original complex B_2 is retained. -/
theorem norm_B_two_le (m : ℕ) (hm : 7 ≤ m) (z : ℂ)
    (hz : ‖z‖ ≤ 1) (hw : ‖1-z‖ ≤ 19/60) :
    ‖PaperCentered.B m 2 z‖ ≤ 1/30 := by
  have hr0 : 0 ≤ rho := by norm_num [rho]
  have hs : ‖PaperCentered.B m 2 z‖ ≤
      ∑ j ∈ Finset.range 3, ((m+1).choose j : ℝ)*rho^(m+1-j) := by
    unfold PaperCentered.B
    refine (norm_sum_le _ _).trans ?_
    apply Finset.sum_le_sum
    intro j hj
    have hpow : ‖1-z‖^(m+1-j) ≤ rho^(m+1-j) :=
      pow_le_pow_left₀ (norm_nonneg _) hw _
    have hzpow := pow_le_one₀ (norm_nonneg z) hz (n := j)
    simp only [norm_mul, norm_pow, Complex.norm_natCast]
    calc
      _ = ((m+1).choose j : ℝ)*(‖z‖^j*‖1-z‖^(m+1-j)) := by ring
      _ ≤ ((m+1).choose j : ℝ)*(1*rho^(m+1-j)) :=
        mul_le_mul_of_nonneg_left
          (mul_le_mul hzpow hpow (pow_nonneg (norm_nonneg _) _) (by norm_num))
          (Nat.cast_nonneg _)
      _ = _ := by ring
  have hc : ((m+1).choose 2 : ℝ) = (m:ℝ)*((m:ℝ)+1)/2 := by
    rw [Nat.cast_choose_two]; push_cast; ring
  have hsum : (∑ j ∈ Finset.range 3, ((m+1).choose j : ℝ)*rho^(m+1-j)) = BEnvelope m := by
    norm_num [Finset.sum_range_succ, Nat.choose_one_right, BEnvelope, hc]
    have hp : rho^m = rho^(m-1)*rho := by
      conv_lhs => rw [show m = (m-1)+1 by omega]
      rw [pow_succ]
    rw [show m+1-2 = m-1 by omega, pow_succ, hp]
    ring
  rw [hsum] at hs
  exact (hs.trans (BEnvelope_decay m hm)).trans (by norm_num [BEnvelope, rho])

end Sendov.CenteredThird
