import Sendov.Analytic.PaperCenteredEndpoint

noncomputable section
open scoped BigOperators
namespace Sendov.CenteredQuarter

lemma choose_four (m : ℕ) (hm : 7 ≤ m) :
    ((m+1).choose 4 : ℝ) = ((m:ℝ)+1)*m*(m-1)*(m-2)/24 := by
  have hc := congrArg (fun n : ℕ => (n : ℝ))
    (Nat.descFactorial_eq_factorial_mul_choose (m+1) 4)
  norm_num [Nat.descFactorial_succ, Nat.descFactorial_zero] at hc
  push_cast [Nat.cast_sub (by omega : 2 ≤ m),
    Nat.cast_sub (by omega : 1 ≤ m)] at hc
  nlinarith only [hc]

/-- The fourth generic endpoint order gives quadratic decay in h. -/
theorem endpoint_quartic (m : ℕ) (hm : 7 ≤ m) (b h : ℝ)
    (hb0 : 0 ≤ b) (hb1 : b ≤ 1) (hh : 0 ≤ h)
    (hslope : 3*b ≤ (m:ℝ)*h*(1-b)) :
    b^(m+1) ≤ (4/9)*h^4 := by
  have hm7 : (7:ℝ) ≤ m := by exact_mod_cast hm
  have hm0 : (0:ℝ) < m := by linarith
  have hp := PaperCenteredEndpoint.endpoint_power_order m 4 (by omega) b
    ((m:ℝ)*h) hb0 hb1 (by positivity) hslope
  have hc : (m:ℝ)^4 ≤ 36*((m+1).choose 4 : ℝ) := by
    rw [choose_four m hm]
    have hn : 0 ≤ (m:ℝ)-7 := by linarith
    have ht : 0 ≤ ((m:ℝ)-7)^3 + 15*((m:ℝ)-7)^2 + 60*((m:ℝ)-7) + 34 := by positivity
    have ht' := mul_nonneg (le_of_lt hm0) ht
    nlinarith only [ht']
  have ht := mul_le_mul_of_nonneg_right hc (pow_nonneg hb0 (m+1))
  have hfin : (m:ℝ)^4*b^(m+1) ≤ (m:ℝ)^4*((4/9)*h^4) := by
    simp only [mul_pow] at hp
    norm_num at hp
    nlinarith only [ht, hp]
  exact (mul_le_mul_iff_right₀ (pow_pos hm0 4)).mp (by simpa only [mul_comm] using hfin)

/-- Scalar norm endpoint, with no restriction to a real complex mean. -/
theorem endpoint_quadratic (m : ℕ) (hm : 7 ≤ m) (w b h : ℝ)
    (hw : 0 ≤ w) (hb0 : 0 ≤ b) (hb1 : b ≤ 1) (hh : 0 ≤ h)
    (hslope : 3*b ≤ (m:ℝ)*h*(1-b)) (hwb : w^2 ≤ b) :
    w^(m+1) ≤ 2*h^2/3 := by
  have hp := pow_le_pow_left₀ (sq_nonneg w) hwb (m+1)
  have he : (w^2)^(m+1) = (w^(m+1))^2 := by
    rw [← pow_mul, ← pow_mul]; congr 1; omega
  rw [he] at hp
  have hb := endpoint_quartic m hm b h hb0 hb1 hh hslope
  nlinarith only [hp, hb, sq_nonneg h, pow_nonneg hw (m+1)]

def rho : ℝ := 5/18

def BEnvelope (m : ℕ) : ℝ := ((m:ℝ)^2 + 3*m + 4)/2 * rho^(m-1)

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
      _ = ((((n:ℝ)+1)^2+3*((n:ℝ)+1)+4)/2*rho)*rho^(n-1) := by ring
      _ ≤ _ := by
        apply mul_le_mul_of_nonneg_right _ (pow_nonneg (by norm_num [rho]) _)
        dsimp [rho]
        nlinarith [sq_nonneg (n:ℝ)]

/-- The original finite complex endpoint B_2, uniformly over every m≥7. -/
theorem norm_B_two_le (m : ℕ) (hm : 7 ≤ m) (z : ℂ)
    (hz : ‖z‖ ≤ 1) (hw : ‖1-z‖ ≤ 5/18) :
    ‖PaperCentered.B m 2 z‖ ≤ 1/50 := by
  have hr0 : 0 ≤ rho := by norm_num [rho]
  have hr1 : rho ≤ 1 := by norm_num [rho]
  have hs : ‖PaperCentered.B m 2 z‖ ≤
      ∑ j ∈ Finset.range 3, ((m+1).choose j : ℝ)*rho^(m-1) := by
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
      _ = ((m+1).choose j : ℝ)*(‖z‖^j*‖1-z‖^(m+1-j)) := by ring
      _ ≤ ((m+1).choose j : ℝ)*(1*rho^(m-1)) :=
        mul_le_mul_of_nonneg_left
          (mul_le_mul hzpow hpow (pow_nonneg (norm_nonneg _) _) (by norm_num))
          (Nat.cast_nonneg _)
      _ = _ := by ring
  have hc : ((m+1).choose 2 : ℝ) = (m:ℝ)*((m:ℝ)+1)/2 := by
    rw [Nat.cast_choose_two]; push_cast; ring
  have hsum : (∑ j ∈ Finset.range 3, ((m+1).choose j : ℝ)*rho^(m-1)) = BEnvelope m := by
    norm_num [Finset.sum_range_succ, Nat.choose_one_right, BEnvelope, hc]
    ring
  rw [hsum] at hs
  exact (hs.trans (BEnvelope_decay m hm)).trans (by norm_num [BEnvelope, rho])

end Sendov.CenteredQuarter
