import Sendov.Analytic.PaperLaplace
import Mathlib.Analysis.Calculus.Deriv.MeanValue

/-! Uniform real-degree tails and quantitative consequences of sharp Laplace.
All numerical certificates are fixed rational Taylor comparisons; there is no degree table. -/
namespace Sendov.PaperTail

/-- A polynomial times a decaying exponential is decreasing past its critical point. -/
lemma power_exp_antitone {c M d : ℝ} {n : ℕ} (hn : 1 ≤ n)
    (hM : 0 < M) (hc : 0 ≤ c) (hcrit : (n : ℝ) ≤ c * M) :
    AntitoneOn (fun t : ℝ => t ^ n * Real.exp (-c * (t - d))) (Set.Ici M) := by
  have hd (t : ℝ) : HasDerivAt (fun t : ℝ => t ^ n * Real.exp (-c * (t - d)))
      (((n : ℝ) * t ^ (n - 1) - c * t ^ n) * Real.exp (-c * (t - d))) t := by
    convert! ((hasDerivAt_pow n t).mul
      ((((hasDerivAt_id t).sub_const d).const_mul (-c)).exp)) using 1
    dsimp
    ring
  apply antitoneOn_of_deriv_nonpos (convex_Ici M) (by fun_prop)
  · intro t ht
    exact (hd t).differentiableAt.differentiableWithinAt
  · intro t ht
    rw [(hd t).deriv]
    have htM : M ≤ t := (interior_subset ht)
    have ht0 : 0 ≤ t := hM.le.trans htM
    have hct : (n : ℝ) ≤ c * t := hcrit.trans (mul_le_mul_of_nonneg_left htM hc)
    have heq : t ^ n = t ^ (n - 1) * t := by
      rw [← pow_succ]; congr 1; omega
    apply mul_nonpos_of_nonpos_of_nonneg _ (Real.exp_pos _).le
    rw [heq]
    nlinarith only [mul_nonneg (pow_nonneg ht0 (n - 1)) (sub_nonneg.mpr hct)]

lemma rpow_le_exp {r m : ℝ} (hr : 0 < r) (hm : 1 ≤ m) :
    r ^ ((m - 1) / 2) ≤ Real.exp (-((1 - r) / 2) * (m - 1)) := by
  rw [Real.rpow_def_of_pos hr]
  apply Real.exp_le_exp.mpr
  have h := mul_le_mul_of_nonneg_right (Real.log_le_sub_one_of_pos hr)
    (show 0 ≤ (m - 1) / 2 by linarith)
  nlinarith

/-- Generic fixed-endpoint tail certificate. -/
lemma tail_certificate {m r C : ℝ} {n : ℕ} (hm : 256 ≤ m) (hr : 0 < r)
    (hn : 1 ≤ n) (hr1 : r ≤ 1) (hcrit : (n : ℝ) ≤ (1 - r) / 2 * 256)
    (hbase : (129 / 256 : ℝ) * 256 ^ n < C * Real.exp ((1 - r) / 2 * 255)) :
    (129 / 256 : ℝ) * m ^ n * r ^ ((m - 1) / 2) < C := by
  have hm0 : 0 ≤ m := by linarith
  have hmono := power_exp_antitone (d := 1) hn (by norm_num : (0 : ℝ) < 256)
    (show 0 ≤ (1 - r) / 2 by linarith) hcrit
    (show (256 : ℝ) ∈ Set.Ici 256 by simp) hm hm
  have hpow := mul_le_mul_of_nonneg_left (rpow_le_exp hr (by linarith : 1 ≤ m))
    (show 0 ≤ (129 / 256 : ℝ) * m ^ n by positivity)
  have hbound : (129 / 256 : ℝ) * m ^ n * r ^ ((m - 1) / 2) ≤
      (129 / 256 : ℝ) * 256 ^ n * Real.exp (-((1 - r) / 2) * 255) := by
    have h := mul_le_mul_of_nonneg_left hmono (by norm_num : (0 : ℝ) ≤ 129 / 256)
    dsimp at h
    nlinarith only [hpow, h]
  apply hbound.trans_lt
  rw [show -((1 - r) / 2) * 255 = -((1 - r) / 2 * 255) by ring, Real.exp_neg]
  exact (div_lt_iff₀ (Real.exp_pos _)).mpr hbase |>.trans_eq (by ring)

/-- The radius `4/5` tail, uniformly in a real degree. -/
theorem tail_four_fifths {m : ℝ} (hm : 256 ≤ m) :
    (m ^ 2 / 2 + m) * (4 / 5 : ℝ) ^ ((m - 1) / 2) < 1 / m := by
  have he : (129 / 256 : ℝ) * 256 ^ (3 : ℕ) < Real.exp ((1 - 4 / 5) / 2 * 255) := by
    have h := Real.sum_le_exp_of_nonneg (by norm_num : (0 : ℝ) ≤ (1 - 4 / 5) / 2 * 255) 16
    norm_num [Finset.sum_range_succ, Nat.factorial_succ] at h ⊢
    linarith
  have h := tail_certificate (n := 3) (C := 1) hm (by norm_num : (0 : ℝ) < 4 / 5)
    (by norm_num) (by norm_num) (by norm_num) (by simpa using he)
  have hp := Real.rpow_nonneg (by norm_num : (0 : ℝ) ≤ 4 / 5) ((m - 1) / 2)
  have hm0 : 0 < m := by linarith
  apply (lt_div_iff₀ hm0).mpr
  have hc : (m ^ 2 / 2 + m) * m ≤ (129 / 256 : ℝ) * m ^ 3 := by
    nlinarith only [mul_nonneg (sq_nonneg m) (show 0 ≤ m - 256 by linarith)]
  nlinarith only [mul_le_mul_of_nonneg_right hc hp, h]

theorem tail_nine_tenths {m : ℝ} (hm : 256 ≤ m) :
    (m ^ 2 / 2 + m) * (9 / 10 : ℝ) ^ ((m - 1) / 2) < 1 / 4 := by
  have he : (129 / 256 : ℝ) * 256 ^ (2 : ℕ) <
      (1 / 4 : ℝ) * Real.exp ((1 - 9 / 10) / 2 * 255) := by
    have h := Real.sum_le_exp_of_nonneg (by norm_num : (0 : ℝ) ≤ (1 - 9 / 10) / 2 * 255) 16
    norm_num [Finset.sum_range_succ, Nat.factorial_succ] at h ⊢
    linarith
  have h := tail_certificate (n := 2) hm (by norm_num : (0 : ℝ) < 9 / 10)
    (by norm_num) (by norm_num) (by norm_num) he
  have hc : m ^ 2 / 2 + m ≤ (129 / 256 : ℝ) * m ^ 2 := by
    nlinarith only [mul_nonneg (show 0 ≤ m by linarith) (show 0 ≤ m - 256 by linarith)]
  exact (mul_le_mul_of_nonneg_right hc (Real.rpow_nonneg (by norm_num) _)).trans_lt h

theorem tail_twenty_three_twenty_fifths {m : ℝ} (hm : 256 ≤ m) :
    (m ^ 2 / 2 + m) * (23 / 25 : ℝ) ^ ((m - 1) / 2) < 2 := by
  have he : (129 / 256 : ℝ) * 256 ^ (2 : ℕ) <
      (2 : ℝ) * Real.exp ((1 - 23 / 25) / 2 * 255) := by
    have h := Real.sum_le_exp_of_nonneg (by norm_num : (0 : ℝ) ≤ (1 - 23 / 25) / 2 * 255) 16
    norm_num [Finset.sum_range_succ, Nat.factorial_succ] at h ⊢
    linarith
  have h := tail_certificate (n := 2) hm (by norm_num : (0 : ℝ) < 23 / 25)
    (by norm_num) (by norm_num) (by norm_num) he
  have hc : m ^ 2 / 2 + m ≤ (129 / 256 : ℝ) * m ^ 2 := by
    nlinarith only [mul_nonneg (show 0 ≤ m by linarith) (show 0 ≤ m - 256 by linarith)]
  exact (mul_le_mul_of_nonneg_right hc (Real.rpow_nonneg (by norm_num) _)).trans_lt h

/-- The middle-region correction is decreasing on the entire required range. -/
theorem middle_antitone : AntitoneOn
    (fun k : ℝ => (1 + 5 * k / 8) * Real.exp (-(11 / 30 : ℝ) * k))
    (Set.Ici (19 / 2)) := by
  have hd (k : ℝ) : HasDerivAt
      (fun k : ℝ => (1 + 5 * k / 8) * Real.exp (-(11 / 30 : ℝ) * k))
      ((5 / 8 - (11 / 30 : ℝ) * (1 + 5 * k / 8)) * Real.exp (-(11 / 30 : ℝ) * k)) k := by
    convert! (((((hasDerivAt_id k).const_mul 5).div_const 8).const_add 1).mul
      (((hasDerivAt_id k).const_mul (-(11 / 30 : ℝ))).exp)) using 1
    dsimp
    ring
  apply antitoneOn_of_deriv_nonpos (convex_Ici _) (by fun_prop)
  · intro k hk; exact (hd k).differentiableAt.differentiableWithinAt
  · intro k hk
    rw [(hd k).deriv]
    have hk' : 19 / 2 ≤ k := interior_subset hk
    exact mul_nonpos_of_nonpos_of_nonneg (by linarith) (Real.exp_pos _).le

/-- Real-degree middle-region tail, retaining its quadratic coefficient. -/
theorem middle_tail {m : ℝ} (hm : 256 ≤ m) :
    m * (1 + 5 * m / 162) * Real.exp (-22 * m / 1215) < 24 := by
  have h1 := power_exp_antitone (n := 1) (c := 22 / 1215) (d := 0)
    (by norm_num) (by norm_num : (0 : ℝ) < 256) (by norm_num) (by norm_num)
    (show (256 : ℝ) ∈ Set.Ici 256 by simp) hm hm
  have h2 := power_exp_antitone (n := 2) (c := 22 / 1215) (d := 0)
    (by norm_num) (by norm_num : (0 : ℝ) < 256) (by norm_num) (by norm_num)
    (show (256 : ℝ) ∈ Set.Ici 256 by simp) hm hm
  have he : (256 : ℝ) * (1 + 5 * 256 / 162) < 24 * Real.exp (22 * 256 / 1215) := by
    have h := Real.sum_le_exp_of_nonneg (by norm_num : (0 : ℝ) ≤ 22 * 256 / 1215) 16
    norm_num [Finset.sum_range_succ, Nat.factorial_succ] at h ⊢
    linarith
  have hbase : (256 : ℝ) * (1 + 5 * 256 / 162) * Real.exp (-22 * 256 / 1215) < 24 := by
    rw [show (-22 * 256 / 1215 : ℝ) = -(22 * 256 / 1215) by ring, Real.exp_neg, ← div_eq_mul_inv]
    exact (div_lt_iff₀ (Real.exp_pos _)).mpr he
  dsimp at h1 h2
  simp only [sub_zero, pow_one] at h1 h2
  have heq (t : ℝ) : -(22 / 1215 : ℝ) * t = -22 * t / 1215 := by ring
  simp only [heq] at h1 h2
  nlinarith only [h1, h2, hbase]

/-- Uniform rational control of the leading sharp-Laplace term. -/
lemma laplace_square {m : ℝ} (hm : 256 ≤ m) :
    m ^ 2 / (m - 1) ^ 2 ≤ 1 + 3 / m := by
  have hm0 : 0 < m := by linarith
  have hm1 : 0 < m - 1 := by linarith
  apply (div_le_iff₀ (sq_pos_of_pos hm1)).mpr
  apply (le_div_iff₀ hm0).mp
  field_simp
  simp only [npowRec] at *
  nlinarith only [sq_nonneg (m - 3), hm]

lemma laplace_cube {m : ℝ} (hm : 256 ≤ m) :
    m ^ 3 / (m - 1) ^ 3 ≤ (253 / 250 : ℝ) := by
  have hm1 : 0 < m - 1 := by linarith
  have hratio : m / (m - 1) ≤ (256 / 255 : ℝ) := by
    apply (div_le_iff₀ hm1).mpr
    linarith
  have h := pow_le_pow_left₀ (by positivity : 0 ≤ m / (m - 1)) hratio 3
  rw [div_pow] at h
  exact h.trans (by norm_num)

/-- The non-tail part of sharp Laplace, with a reusable lower bound on `x`. -/
lemma laplace_main_lt {m x q K : ℝ} (hm : 256 ≤ m) (hq : 0 < q) (hx : q ≤ x)
    (hK : 3 + (256 / 27 : ℝ) * (253 / 250) / q ^ 2 < K) :
    m ^ 2 / (m - 1) ^ 2 + (256 / 27 : ℝ) * m ^ 2 / ((m - 1) ^ 3 * x ^ 2) <
      1 + K / m := by
  have hm0 : 0 < m := by linarith
  have hx0 : 0 < x := hq.trans_le hx
  have hm1 : 0 < m - 1 := by linarith
  have hsq : q ^ 2 ≤ x ^ 2 := by nlinarith
  have hc : (256 / 27 : ℝ) * m ^ 2 / ((m - 1) ^ 3 * x ^ 2) ≤
      ((256 / 27 : ℝ) * (253 / 250) / q ^ 2) / m := by
    calc
      _ = (256 / 27 : ℝ) * (m ^ 3 / (m - 1) ^ 3) / x ^ 2 / m := by field_simp
      _ ≤ (256 / 27 : ℝ) * (253 / 250) / x ^ 2 / m := by
        exact div_le_div_of_nonneg_right (div_le_div_of_nonneg_right
          (mul_le_mul_of_nonneg_left (laplace_cube hm) (by norm_num)) (sq_nonneg x)) hm0.le
      _ ≤ _ := by gcongr
  have h := add_le_add (laplace_square hm) hc
  have hK' := (div_lt_div_iff_of_pos_right hm0).mpr hK
  rw [add_div] at hK'
  linarith only [h, hK']

/-- First quantitative region; endpoint assumptions refer to the actual kernel. -/
theorem budget_region_one {m a x : ℝ} (hm : 256 ≤ m)
    (ha : 0 < a) (ha1 : a < 1) (hx : 5 / 6 < x) (hx1 : x ≤ 1) (hxa : x < 2 * a)
    (hb : PaperTaylor.beta a x 1 ≤ 4 / 5) :
    m * x ^ 2 * PaperTaylor.budget m a x < 1 + 18 / m := by
  have hx0 : 0 < x := by linarith
  have hsplit : 1 - 3 * x ^ 2 / 4 ≤ (4 / 5 : ℝ) := by nlinarith
  have h := PaperLaplace.budget_le (by linarith : 1 < m) ha ha1 hx0 hx1 hxa hsplit hb (by norm_num)
  have hmain := laplace_main_lt (K := 17) hm (by norm_num : (0 : ℝ) < 5 / 6) hx.le (by norm_num)
  have ht := tail_four_fifths hm
  have hs := h.trans_lt (add_lt_add hmain ht)
  simp only [div_eq_mul_inv] at hs ⊢
  linarith only [hs]

/-- Second quantitative region. -/
theorem budget_region_two {m a x : ℝ} (hm : 256 ≤ m)
    (ha : 0 < a) (ha1 : a < 1) (hx : 7 / 12 < x) (hx1 : x ≤ 1) (hxa : x < 2 * a)
    (hb : PaperTaylor.beta a x 1 ≤ 4 / 5) :
    m * x ^ 2 * PaperTaylor.budget m a x < 1 + 33 / m := by
  have hx0 : 0 < x := by linarith
  have hsplit : 1 - 3 * x ^ 2 / 4 ≤ (4 / 5 : ℝ) := by nlinarith
  have h := PaperLaplace.budget_le (by linarith : 1 < m) ha ha1 hx0 hx1 hxa hsplit hb (by norm_num)
  have hmain := laplace_main_lt (K := 32) hm (by norm_num : (0 : ℝ) < 7 / 12) hx.le (by norm_num)
  have ht := tail_four_fifths hm
  have hs := h.trans_lt (add_lt_add hmain ht)
  simp only [div_eq_mul_inv] at hs ⊢
  linarith only [hs]

/-- Third quantitative region. -/
theorem budget_region_three {m a x : ℝ} (hm : 256 ≤ m)
    (ha : 0 < a) (ha1 : a < 1) (hx : 231 / 512 < x) (hx1 : x ≤ 1) (hxa : x < 2 * a)
    (hb : PaperTaylor.beta a x 1 ≤ 9 / 10) :
    m * x ^ 2 * PaperTaylor.budget m a x < 1 + 51 / m + 1 / 4 := by
  have hx0 : 0 < x := by linarith
  have hsplit : 1 - 3 * x ^ 2 / 4 ≤ (9 / 10 : ℝ) := by nlinarith
  have h := PaperLaplace.budget_le (by linarith : 1 < m) ha ha1 hx0 hx1 hxa hsplit hb (by norm_num)
  have hmain := laplace_main_lt (K := 51) hm (by norm_num : (0 : ℝ) < 231 / 512) hx.le (by norm_num)
  have ht := tail_nine_tenths hm
  linarith

/-- Fourth quantitative region. -/
theorem budget_region_four {m a x : ℝ} (hm : 256 ≤ m)
    (ha : 0 < a) (ha1 : a < 1) (hx : 207 / 512 < x) (hx1 : x ≤ 1) (hxa : x < 2 * a)
    (hb : PaperTaylor.beta a x 1 ≤ 23 / 25) :
    m * x ^ 2 * PaperTaylor.budget m a x < 1 + 62 / m + 2 := by
  have hx0 : 0 < x := by linarith
  have hsplit : 1 - 3 * x ^ 2 / 4 ≤ (23 / 25 : ℝ) := by nlinarith
  have h := PaperLaplace.budget_le (by linarith : 1 < m) ha ha1 hx0 hx1 hxa hsplit hb (by norm_num)
  have hmain := laplace_main_lt (K := 62) hm (by norm_num : (0 : ℝ) < 207 / 512) hx.le (by norm_num)
  have ht := tail_twenty_three_twenty_fifths hm
  linarith

end Sendov.PaperTail
