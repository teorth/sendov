import Sendov.Analytic.Origin

/-! Finite polynomial integrals and positive decompositions for degrees five and six.
No sampling, general Bernstein framework, or endpoint strictness assumptions. -/

namespace Sendov.FirstOriginSmall

noncomputable def B (a t : ℝ) : ℝ := 1 - a * (1 + a) * t + a ^ 2 * t ^ 2
noncomputable def Q (a : ℝ) : ℝ :=
  120 + 170 * a + 102 * a ^ 2 - 29 * a ^ 3 - 117 * a ^ 4 - 93 * a ^ 5 - 61 * a ^ 6 + 13 * a ^ 7 + 25 * a ^ 8 + 9 * a ^ 9 + a ^ 10

lemma integral_quadratic_cube (c d e : ℝ) :
    (∫ t in (0 : ℝ)..1, (c + d * t + e * t ^ 2) ^ 3) =
      c ^ 3 + 3 * c ^ 2 * d / 2 + (3 * c ^ 2 * e + 3 * c * d ^ 2) / 3 + (6 * c * d * e + d ^ 3) / 4 + (3 * c * e ^ 2 + 3 * d ^ 2 * e) / 5 + 3 * d * e ^ 2 / 6 + e ^ 3 / 7 := by
  have hex : (fun t : ℝ => (c + d * t + e * t ^ 2) ^ 3) =
      (fun t => c ^ 3 + (3 * c ^ 2 * d) * t ^ 1 + (3 * c ^ 2 * e + 3 * c * d ^ 2) * t ^ 2 + (6 * c * d * e + d ^ 3) * t ^ 3 + (3 * c * e ^ 2 + 3 * d ^ 2 * e) * t ^ 4 + (3 * d * e ^ 2) * t ^ 5 + e ^ 3 * t ^ 6) := by
    funext t; ring
  rw [hex]
  simp (disch := exact Continuous.intervalIntegrable (by fun_prop) _ _)
    only [intervalIntegral.integral_add, intervalIntegral.integral_const_mul,
      intervalIntegral.integral_const, integral_pow, integral_id]
  norm_num
  <;> ring

lemma integral_t_quadratic_sq (c d e : ℝ) :
    (∫ t in (0 : ℝ)..1, t * (c + d * t + e * t ^ 2) ^ 2) =
      c ^ 2 / 2 + 2 * c * d / 3 + (2 * c * e + d ^ 2) / 4 + 2 * d * e / 5 + e ^ 2 / 6 := by
  have hex : (fun t : ℝ => t * (c + d * t + e * t ^ 2) ^ 2) =
      (fun t => c ^ 2 * t ^ 1 + (2 * c * d) * t ^ 2 + (2 * c * e + d ^ 2) * t ^ 3 + (2 * d * e) * t ^ 4 + e ^ 2 * t ^ 5) := by
    funext t; ring
  rw [hex]
  simp (disch := exact Continuous.intervalIntegrable (by fun_prop) _ _)
    only [intervalIntegral.integral_add, intervalIntegral.integral_const_mul, integral_pow, integral_id]
  norm_num
  <;> ring

lemma integral_t_linear_fifth (a : ℝ) :
    (∫ t in (0 : ℝ)..1, t * (1 - a * t) ^ 5) =
      1 / 2 - 5 * a / 3 + 5 * a ^ 2 / 2 - 2 * a ^ 3 + 5 * a ^ 4 / 6 - a ^ 5 / 7 := by
  have hex : (fun t : ℝ => t * (1 - a * t) ^ 5) =
      (fun t => t + (-5 * a) * t ^ 2 + (10 * a ^ 2) * t ^ 3 + (-10 * a ^ 3) * t ^ 4 + (5 * a ^ 4) * t ^ 5 + (-a ^ 5) * t ^ 6) := by
    funext t; ring
  rw [hex]
  simp (disch := exact Continuous.intervalIntegrable (by fun_prop) _ _)
    only [intervalIntegral.integral_add, intervalIntegral.integral_const_mul, integral_pow, integral_id]
  norm_num
  <;> ring

lemma integral_sq_linear_cube (a : ℝ) :
    (∫ t in (0 : ℝ)..1, t ^ 2 * (1 - a * t) ^ 3) = 1 / 3 - 3 * a / 4 + 3 * a ^ 2 / 5 - a ^ 3 / 6 := by
  have hex : (fun t : ℝ => t ^ 2 * (1 - a * t) ^ 3) =
      (fun t => t ^ 2 + (-3 * a) * t ^ 3 + (3 * a ^ 2) * t ^ 4 + (-a ^ 3) * t ^ 5) := by
    funext t; ring
  rw [hex]
  simp (disch := exact Continuous.intervalIntegrable (by fun_prop) _ _)
    only [intervalIntegral.integral_add, intervalIntegral.integral_const_mul, integral_pow]
  norm_num
  <;> ring

lemma polar_cube_integral (a : ℝ) :
    1 - (∫ t in (0 : ℝ)..1, Ppolar a ((1 + a) / 2) t ^ (3 : ℕ)) = (1 - a) ^ 2 * Q a / 140 := by
  have hp : (fun t => Ppolar a ((1 + a) / 2) t) =
      (fun t => a ^ 2 + (a * (1 - a ^ 2) * (1 + a)) * t + (1 - a ^ 2) ^ 2 * t ^ 2) := by
    funext t; unfold Ppolar; ring
  simp_rw [hp]
  rw [integral_quadratic_cube]
  unfold Q
  ring

lemma Q_lower {a : ℝ} (ha0 : 0 ≤ a) (ha1 : a ≤ 1) : 92 ≤ Q a := by
  have h3 : a ^ 3 ≤ a ^ 2 := pow_le_pow_of_le_one ha0 ha1 (by omega : 2 ≤ 3)
  have h4 : a ^ 4 ≤ a ^ 2 := pow_le_pow_of_le_one ha0 ha1 (by omega : 2 ≤ 4)
  have h5 : a ^ 5 ≤ a ^ 2 := pow_le_pow_of_le_one ha0 ha1 (by omega : 2 ≤ 5)
  have h6 : a ^ 6 ≤ a ^ 2 := pow_le_pow_of_le_one ha0 ha1 (by omega : 2 ≤ 6)
  have h2 : a ^ 2 ≤ a := by nlinarith
  unfold Q
  nlinarith [pow_nonneg ha0 7, pow_nonneg ha0 8, pow_nonneg ha0 9, pow_nonneg ha0 10]

lemma polar_cube_lt_one {a : ℝ} (ha0 : 0 < a) (ha1 : a < 1) :
    (∫ t in (0 : ℝ)..1, Ppolar a ((1 + a) / 2) t ^ (3 : ℕ)) < 1 := by
  have hQ := Q_lower ha0.le ha1.le
  have h := polar_cube_integral a
  have hg : 0 < (1 - a) ^ 2 * Q a := mul_pos (sq_pos_of_pos (by linarith)) (by linarith)
  linarith

lemma fifth_sixth_majorant {y : ℝ} (hy : 0 ≤ y) : 6 * y ^ 5 ≤ 1 + 5 * y ^ 6 := by
  have hid : 1 + 5 * y ^ 6 - 6 * y ^ 5 = (y - 1) ^ 2 * (5 * y ^ 4 + 4 * y ^ 3 + 3 * y ^ 2 + 2 * y + 1) := by ring
  have hp : 0 ≤ (y - 1) ^ 2 * (5 * y ^ 4 + 4 * y ^ 3 + 3 * y ^ 2 + 2 * y + 1) := by positivity
  linarith

lemma five_halves_majorant {u w : ℝ} (hu : 0 ≤ u) (huw : u ≤ w) (hw : w ≤ 1) :
    w ^ 5 ≤ u ^ 5 + (5 / 2 : ℝ) * u ^ 3 * (w ^ 2 - u ^ 2) + (15 / 8 : ℝ) * (w ^ 2 - u ^ 2) ^ 2 := by
  have hid : u ^ 5 + (5 / 2 : ℝ) * u ^ 3 * (w ^ 2 - u ^ 2) + (15 / 8 : ℝ) * (w ^ 2 - u ^ 2) ^ 2 - w ^ 5 =
      (15 / 8 : ℝ) * (1 - w) * (w ^ 2 - u ^ 2) ^ 2 + (w - u) ^ 3 * (5 * u ^ 2 + (35 / 8 : ℝ) * u * (w - u) + (7 / 8 : ℝ) * (w - u) ^ 2) := by ring
  have hd : 0 ≤ w - u := sub_nonneg.mpr huw
  have hp : 0 ≤ (15 / 8 : ℝ) * (1 - w) * (w ^ 2 - u ^ 2) ^ 2 + (w - u) ^ 3 * (5 * u ^ 2 + (35 / 8 : ℝ) * u * (w - u) + (7 / 8 : ℝ) * (w - u) ^ 2) := by
    have : 0 ≤ 1 - w := sub_nonneg.mpr hw
    positivity
  linarith

lemma upper_five_gap {a : ℝ} (ha0 : 0 < a) (ha1 : a < 1) :
    (1 - a) ^ 2 + 5 * a ^ 2 * (∫ t in (0 : ℝ)..1, t * (B a t) ^ 2) < 1 - 5 * a / 6 := by
  have he : (fun t => B a t) = (fun t => 1 + (-a * (1 + a)) * t + a ^ 2 * t ^ 2) := by
    funext t; unfold B; ring
  simp_rw [he]
  rw [integral_t_quadratic_sq]
  have hh : 0 < 1 - a := by linarith
  have hp : 0 < a * (1 - a) * (14 * (1 - a) ^ 4 + 28 * a * (1 - a) ^ 3 + 12 * a ^ 2 * (1 - a) ^ 2 + 3 * a ^ 3 * (1 - a) + 6 * a ^ 4) / 12 := by positivity
  have hid : 1 - 5 * a / 6 - ((1 - a) ^ 2 + 5 * a ^ 2 * (1 ^ 2 / 2 + 2 * 1 * (-a * (1 + a)) / 3 + (2 * 1 * a ^ 2 + (-a * (1 + a)) ^ 2) / 4 + 2 * (-a * (1 + a)) * a ^ 2 / 5 + (a ^ 2) ^ 2 / 6)) =
      a * (1 - a) * (14 * (1 - a) ^ 4 + 28 * a * (1 - a) ^ 3 + 12 * a ^ 2 * (1 - a) ^ 2 + 3 * a ^ 3 * (1 - a) + 6 * a ^ 4) / 12 := by ring
  linarith

lemma upper_six_gap {a : ℝ} (ha0 : 0 < a) (ha1 : a < 1) :
    (1 - a) ^ 3 + 6 * a ^ 2 * ((∫ t in (0 : ℝ)..1, t * (1 - a * t) ^ 5) + (5 / 2 : ℝ) * a * (1 - a) * (∫ t in (0 : ℝ)..1, t ^ 2 * (1 - a * t) ^ 3) + (15 / 32 : ℝ) * a ^ 2 * (1 - a) ^ 2) < 1 - 6 * a / 7 := by
  rw [integral_t_linear_fifth, integral_sq_linear_cube]
  have hh : 0 < 1 - a := by linarith
  have hp : 0 < a * (1 - a) * (240 * (1 - a) ^ 5 + 768 * a * (1 - a) ^ 4 + 912 * a ^ 2 * (1 - a) ^ 3 + 593 * a ^ 3 * (1 - a) ^ 2 + 93 * a ^ 4 * (1 - a) + 68 * a ^ 5) / 112 := by positivity
  have hid : 1 - 6 * a / 7 - ((1 - a) ^ 3 + 6 * a ^ 2 * ((1 / 2 - 5 * a / 3 + 5 * a ^ 2 / 2 - 2 * a ^ 3 + 5 * a ^ 4 / 6 - a ^ 5 / 7) + (5 / 2 : ℝ) * a * (1 - a) * (1 / 3 - 3 * a / 4 + 3 * a ^ 2 / 5 - a ^ 3 / 6) + (15 / 32 : ℝ) * a ^ 2 * (1 - a) ^ 2)) =
      a * (1 - a) * (240 * (1 - a) ^ 5 + 768 * a * (1 - a) ^ 4 + 912 * a ^ 2 * (1 - a) ^ 3 + 593 * a ^ 3 * (1 - a) ^ 2 + 93 * a ^ 4 * (1 - a) + 68 * a ^ 5) / 112 := by ring
  linarith

end Sendov.FirstOriginSmall
