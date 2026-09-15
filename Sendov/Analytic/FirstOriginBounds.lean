import Sendov.Analytic.FirstOriginAlgebra

/-! The raw polar mean bound and the complete T budgets on 0 < a < 1.
The five/six split is intentional; no extrapolation to larger degrees. -/

namespace Sendov.FirstOriginSmall

lemma sqrt_pow_eq_rpow {z : ℝ} (hz : 0 ≤ z) (k : ℕ) :
    (Real.sqrt z) ^ k = z ^ ((k : ℝ) / 2) := by
  rw [Real.sqrt_eq_rpow, ← Real.rpow_natCast, ← Real.rpow_mul hz]
  congr 1
  ring

lemma Ppolar_nonneg_small {a x t : ℝ} (ha : 0 ≤ a) (ha1 : a ≤ 1)
    (hx : -1 ≤ x) (ht : 0 ≤ t) : 0 ≤ Ppolar a x t := by
  have hd : 0 ≤ 1 - a ^ 2 := by nlinarith
  have hid : Ppolar a x t = (a - (1 - a ^ 2) * t) ^ 2 + 2 * a * (1 - a ^ 2) * t * (x + 1) := by
    unfold Ppolar; ring
  rw [hid]
  have : 0 ≤ x + 1 := by linarith
  positivity

lemma Ppolar_le_half {a x t : ℝ} (ha : 0 ≤ a) (ha1 : a ≤ 1)
    (hx : x ≤ (1 + a) / 2) (ht : 0 ≤ t) : Ppolar a x t ≤ Ppolar a ((1 + a) / 2) t := by
  have hd : 0 ≤ 1 - a ^ 2 := by nlinarith
  have hh : 0 ≤ (1 + a) / 2 - x := sub_nonneg.mpr hx
  have hp := mul_nonneg (mul_nonneg (mul_nonneg (by positivity : 0 ≤ 2 * a) hd) ht) hh
  unfold Ppolar
  nlinarith only [hp]

lemma polar_mean_gt_half_add_one {n : ℕ} (hn : n = 6 ∨ n = 7) {a x : ℝ}
    (ha0 : 0 < a) (ha1 : a < 1) (hx0 : -1 ≤ x)
    (hpolar : 1 ≤ ∫ t in (0 : ℝ)..1, Ppolar a x t ^ (((n : ℝ) - 1) / 2)) :
    (1 + a) / 2 < x := by
  by_contra hx
  have hx : x ≤ (1 + a) / 2 := le_of_not_gt hx
  have hcube := polar_cube_lt_one ha0 ha1
  have hcp : Continuous (fun t => Ppolar a ((1 + a) / 2) t ^ (3 : ℕ)) := by
    exact (continuous_Ppolar _ _).pow 3
  rcases hn with rfl | rfl
  · norm_num at hpolar
    have hcont : Continuous (fun t => Ppolar a x t ^ (5 / 2 : ℝ)) :=
      (continuous_rpow_const (by norm_num : (0 : ℝ) ≤ 5 / 2)).comp (continuous_Ppolar a x)
    have hi := intervalIntegral.integral_mono_on (μ := MeasureTheory.volume) (by norm_num : (0 : ℝ) ≤ 1)
      (hcont.intervalIntegrable 0 1)
      ((continuous_const.add (continuous_const.mul hcp)).intervalIntegrable 0 1)
      (show ∀ t ∈ Set.Icc (0 : ℝ) 1,
        Ppolar a x t ^ (5 / 2 : ℝ) ≤ (1 / 6 : ℝ) + (5 / 6 : ℝ) * Ppolar a ((1 + a) / 2) t ^ (3 : ℕ) from by
        intro t ht
        have hp0 := Ppolar_nonneg_small ha0.le ha1.le hx0 ht.1
        have hp1 := Ppolar_le_half ha0.le ha1.le hx ht.1
        have hz : 0 ≤ Ppolar a ((1 + a) / 2) t := hp0.trans hp1
        have hm := Real.rpow_le_rpow hp0 hp1 (by norm_num : (0 : ℝ) ≤ 5 / 2)
        have hf := fifth_sixth_majorant (Real.sqrt_nonneg (Ppolar a ((1 + a) / 2) t))
        rw [sqrt_pow_eq_rpow hz 5, sqrt_pow_eq_rpow hz 6] at hf
        norm_num [Real.rpow_natCast] at hf
        linarith)
    dsimp only [Pi.add_apply, Pi.mul_apply, Pi.pow_apply] at hi
    simp (disch := exact Continuous.intervalIntegrable (by fun_prop) _ _)
      only [intervalIntegral.integral_add, intervalIntegral.integral_const_mul,
        intervalIntegral.integral_const] at hi
    norm_num at hi
    linarith
  · norm_num [Real.rpow_natCast] at hpolar
    have hi := intervalIntegral.integral_mono_on (μ := MeasureTheory.volume) (by norm_num : (0 : ℝ) ≤ 1)
      (((continuous_Ppolar a x).pow 3).intervalIntegrable 0 1)
      (hcp.intervalIntegrable 0 1) (show ∀ t ∈ Set.Icc (0 : ℝ) 1,
        Ppolar a x t ^ (3 : ℕ) ≤ Ppolar a ((1 + a) / 2) t ^ (3 : ℕ) from by
        intro t ht
        exact pow_le_pow_left₀ (Ppolar_nonneg_small ha0.le ha1.le hx0 ht.1)
          (Ppolar_le_half ha0.le ha1.le hx ht.1) 3)
    dsimp only [Pi.pow_apply] at hi
    linarith

lemma beta_B_bounds {a x t : ℝ} (ha0 : 0 ≤ a) (ha1 : a ≤ 1)
    (hx : (1 + a) / 2 ≤ x) (hx1 : x ≤ 1) (ht0 : 0 ≤ t) (ht1 : t ≤ 1) :
    0 ≤ QQ (a * x) (a ^ 2) t ∧ QQ (a * x) (a ^ 2) t ≤ B a t ∧
      (1 - a * t) ^ 2 ≤ B a t ∧ B a t ≤ 1 ∧ 0 ≤ 1 - a * t := by
  have hat : a * t ≤ 1 := (mul_le_mul_of_nonneg_left ht1 ha0).trans (by simpa using ha1)
  have hq : QQ (a * x) (a ^ 2) t = (1 - a * t) ^ 2 + 2 * a * t * (1 - x) := by unfold QQ; ring
  have hb : B a t = (1 - a * t) ^ 2 + a * (1 - a) * t := by unfold B; ring
  have hdiff : B a t - QQ (a * x) (a ^ 2) t = 2 * a * t * (x - (1 + a) / 2) := by
    unfold B QQ; ring
  have hupper : 1 - B a t = a * t * (1 + a - a * t) := by unfold B; ring
  have hp : 0 ≤ a * (1 - a) * t := by positivity
  have hp2 : 0 ≤ 2 * a * t * (1 - x) := by positivity
  have hp3 : 0 ≤ 2 * a * t * (x - (1 + a) / 2) := by positivity
  have hp4 : 0 ≤ a * t * (1 + a - a * t) := by
    have : 0 ≤ 1 + a - a * t := by linarith
    positivity
  constructor
  · rw [hq]; positivity
  constructor
  · linarith
  constructor
  · linarith
  constructor <;> linarith

lemma B_five_halves {a t : ℝ} (ha0 : 0 ≤ a) (ha1 : a ≤ 1)
    (ht0 : 0 ≤ t) (ht1 : t ≤ 1) :
    B a t ^ (5 / 2 : ℝ) ≤ (1 - a * t) ^ 5 + (5 / 2 : ℝ) * a * (1 - a) * t * (1 - a * t) ^ 3 + (15 / 8 : ℝ) * a ^ 2 * (1 - a) ^ 2 * t ^ 2 := by
  obtain ⟨_, _, hu2, hb1, hu⟩ := beta_B_bounds ha0 ha1 (le_refl ((1 + a) / 2))
    (by linarith : (1 + a) / 2 ≤ 1) ht0 ht1
  have hb0 : 0 ≤ B a t := (sq_nonneg _).trans hu2
  have hsq := Real.sq_sqrt hb0
  have huw : 1 - a * t ≤ Real.sqrt (B a t) := by
    nlinarith [Real.sqrt_nonneg (B a t)]
  have hw1 : Real.sqrt (B a t) ≤ 1 := by
    nlinarith [Real.sqrt_nonneg (B a t)]
  have h := five_halves_majorant hu huw hw1
  rw [sqrt_pow_eq_rpow hb0 5, hsq] at h
  have he : B a t - (1 - a * t) ^ 2 = a * (1 - a) * t := by unfold B; ring
  rw [he] at h
  convert h using 1 <;> ring

lemma direct_budget_five {a x : ℝ} (ha0 : 0 < a) (ha1 : a < 1)
    (hx : (1 + a) / 2 ≤ x) (hx1 : x ≤ 1) :
    QQ (a * x) (a ^ 2) 1 ^ (5 / 2 : ℝ) + 5 * a ^ 2 * (∫ t in (0 : ℝ)..1, t * QQ (a * x) (a ^ 2) t ^ (2 : ℕ)) < 1 - 5 * a / 6 := by
  have hend := beta_B_bounds ha0.le ha1.le hx hx1 (by norm_num : (0 : ℝ) ≤ 1) le_rfl
  have heB : B a 1 = 1 - a := by unfold B; ring
  have he := Real.rpow_le_rpow hend.1 hend.2.1 (by norm_num : (0 : ℝ) ≤ 5 / 2)
  rw [heB] at he
  have he2 := Real.rpow_le_rpow_of_exponent_ge (by linarith : 0 < 1 - a)
    (by linarith : 1 - a ≤ 1) (by norm_num : (2 : ℝ) ≤ 5 / 2)
  norm_num [Real.rpow_natCast] at he2
  have hi : (∫ t in (0 : ℝ)..1, t * QQ (a * x) (a ^ 2) t ^ (2 : ℕ)) ≤
      ∫ t in (0 : ℝ)..1, t * (B a t) ^ 2 := by
    apply intervalIntegral.integral_mono_on (by norm_num)
      (Continuous.intervalIntegrable (by unfold QQ; fun_prop) _ _)
      (Continuous.intervalIntegrable (by unfold B; fun_prop) _ _)
    intro t ht
    have hb := beta_B_bounds ha0.le ha1.le hx hx1 ht.1 ht.2
    exact mul_le_mul_of_nonneg_left (pow_le_pow_left₀ hb.1 hb.2.1 2) ht.1
  have hmul := mul_le_mul_of_nonneg_left hi (by positivity : 0 ≤ 5 * a ^ 2)
  have hg := upper_five_gap ha0 ha1
  linarith

lemma direct_budget_six {a x : ℝ} (ha0 : 0 < a) (ha1 : a < 1)
    (hx : (1 + a) / 2 ≤ x) (hx1 : x ≤ 1) :
    QQ (a * x) (a ^ 2) 1 ^ (3 : ℕ) + 6 * a ^ 2 * (∫ t in (0 : ℝ)..1, t * QQ (a * x) (a ^ 2) t ^ (5 / 2 : ℝ)) < 1 - 6 * a / 7 := by
  have hend := beta_B_bounds ha0.le ha1.le hx hx1 (by norm_num : (0 : ℝ) ≤ 1) le_rfl
  have heB : B a 1 = 1 - a := by unfold B; ring
  have he := pow_le_pow_left₀ hend.1 hend.2.1 3
  rw [heB] at he
  have hi : (∫ t in (0 : ℝ)..1, t * QQ (a * x) (a ^ 2) t ^ (5 / 2 : ℝ)) ≤
      ∫ t in (0 : ℝ)..1, (t * (1 - a * t) ^ 5 + ((5 / 2 : ℝ) * a * (1 - a)) * (t ^ 2 * (1 - a * t) ^ 3) + ((15 / 8 : ℝ) * a ^ 2 * (1 - a) ^ 2) * t ^ 3) := by
    apply intervalIntegral.integral_mono_on (by norm_num)
      (by simpa only [pow_one] using
        (continuous_pow_mul_QQ (a * x) (a ^ 2) 1 (by norm_num : (0 : ℝ) ≤ 5 / 2)).intervalIntegrable 0 1)
      (Continuous.intervalIntegrable (by fun_prop) _ _)
    intro t ht
    have hb := beta_B_bounds ha0.le ha1.le hx hx1 ht.1 ht.2
    have hp := (Real.rpow_le_rpow hb.1 hb.2.1 (by norm_num : (0 : ℝ) ≤ 5 / 2)).trans
      (B_five_halves ha0.le ha1.le ht.1 ht.2)
    have hm := mul_le_mul_of_nonneg_left hp ht.1
    calc
      _ ≤ t * ((1 - a * t) ^ 5 + (5 / 2 : ℝ) * a * (1 - a) * t * (1 - a * t) ^ 3 + (15 / 8 : ℝ) * a ^ 2 * (1 - a) ^ 2 * t ^ 2) := hm
      _ = _ := by ring
  simp (disch := exact Continuous.intervalIntegrable (by fun_prop) _ _)
    only [intervalIntegral.integral_add, intervalIntegral.integral_const_mul, integral_pow] at hi
  norm_num at hi
  have hmul := mul_le_mul_of_nonneg_left hi (by positivity : 0 ≤ 6 * a ^ 2)
  have hg := upper_six_gap ha0 ha1
  nlinarith only [he, hmul, hg]

end Sendov.FirstOriginSmall
