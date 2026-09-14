import Sendov.Analytic.PaperPolar
import Sendov.Analytic.PaperTaylor
import Sendov.Analytic.PaperNearAlgebra

/-!
# Near-endpoint closure of the actual paper D budget

The integer endpoint estimate has one geometric base case, at `m = 7`.
All scalar parameters and both Taylor errors are derived from raw polar.
-/

namespace Sendov.PaperNearClosure

lemma half_power_le : (2 / 17 : ℝ) ^ (1 / 2 : ℝ) ≤ 7 / 20 := by
  have hs : ((2 / 17 : ℝ) ^ (1 / 2 : ℝ)) ^ 2 = 2 / 17 := by
    rw [← Real.rpow_natCast _ 2, ← Real.rpow_mul (by norm_num : (0 : ℝ) ≤ 2 / 17)]
    norm_num
  nlinarith [Real.rpow_nonneg (by norm_num : (0 : ℝ) ≤ 2 / 17) (1 / 2 : ℝ)]

/-- One base case followed by a uniform geometric step, not a degree table. -/
lemma geometric_endpoint {m : ℕ} (hm : 7 ≤ m) :
    (m : ℝ) / 3 * (2 / 17 : ℝ) ^ (((m : ℝ) - 2) / 2) ≤ 49 / 4335 := by
  induction m, hm using Nat.le_induction with
  | base =>
    norm_num only [Nat.cast_ofNat]
    rw [show (5 : ℝ) / 2 = 2 + 1 / 2 by norm_num,
      Real.rpow_add (by norm_num : (0 : ℝ) < 2 / 17)]
    norm_num [Real.rpow_two]
    nlinarith [half_power_le]
  | succ k hk ih =>
    have hk' : (7 : ℝ) ≤ k := by exact_mod_cast hk
    have hp : 0 ≤ (2 / 17 : ℝ) ^ (((k : ℝ) - 2) / 2) :=
      Real.rpow_nonneg (by norm_num) _
    have he : (((k + 1 : ℕ) : ℝ) - 2) / 2 = ((k : ℝ) - 2) / 2 + 1 / 2 := by
      push_cast
      ring
    rw [he, Real.rpow_add (by norm_num : (0 : ℝ) < 2 / 17)]
    have hs := mul_le_mul_of_nonneg_left half_power_le
      (show 0 ≤ (((k + 1 : ℕ) : ℝ) / 3) * (2 / 17 : ℝ) ^ (((k : ℝ) - 2) / 2)
        by positivity)
    have hc : (((k + 1 : ℕ) : ℝ) / 3) * (7 / 20) ≤ (k : ℝ) / 3 := by
      push_cast
      linarith
    have ht := mul_le_mul_of_nonneg_right hc hp
    nlinarith only [hs, ht, ih]

/-- The actual endpoint term is uniformly less than one eightieth of `1-a`. -/
theorem endpoint_term_lt {m : ℕ} {a x : ℝ} (hm : 7 ≤ m)
    (ha0 : 0 < a) (ha1 : a < 1) (hx0 : -1 ≤ x) (hx1 : x ≤ 1)
    (hraw : PaperPolar.RawPolar m a x) (hnear : (m : ℝ) * (1 - a) ≤ 2 / 5) :
    PaperPolar.b a x ^ ((m : ℝ) / 2) / (1 - a) < 1 / 80 := by
  have hm' : (7 : ℝ) ≤ m := by exact_mod_cast hm
  have hh : 0 < 1 - a := by linarith
  have hl := PaperPolar.lambda_pos (by omega : 0 < m) ha1
  have hb0 := PaperPolar.b_pos ha0.le ha1 hx1
  have hb := (PaperPolar.endpoint_bounds hm ha0 ha1 hx0 hx1 hraw).1.trans
    (PaperPolar.endpoint_bounds hm ha0 ha1 hx0 hx1 hraw).2
  have hl2 : PaperPolar.lambda m a ≤ 2 / 5 := hnear
  have hb2 : PaperPolar.b a x ≤ 2 / 17 := by
    have ht := PaperPolar.rational_mono hl.le hl2
    norm_num at ht
    exact hb.trans ht
  have hb3 : PaperPolar.b a x ≤ (m : ℝ) * (1 - a) / 3 := by
    have hs : 0 < 3 + PaperPolar.lambda m a := by positivity
    have ht : PaperPolar.lambda m a / (3 + PaperPolar.lambda m a) ≤
        PaperPolar.lambda m a / 3 := by
      apply div_le_div_of_nonneg_left hl.le (by norm_num)
      linarith
    exact hb.trans ht
  have hpow := Real.rpow_le_rpow hb0.le hb2 (by linarith : 0 ≤ ((m : ℝ) - 2) / 2)
  have hsplit : PaperPolar.b a x ^ ((m : ℝ) / 2) =
      PaperPolar.b a x * PaperPolar.b a x ^ (((m : ℝ) - 2) / 2) := by
    rw [show (m : ℝ) / 2 = 1 + ((m : ℝ) - 2) / 2 by ring,
      Real.rpow_add hb0, Real.rpow_one]
  have hmul := mul_le_mul hb3 hpow
    (Real.rpow_nonneg hb0.le _) (by positivity : 0 ≤ (m : ℝ) * (1 - a) / 3)
  rw [← hsplit] at hmul
  apply (div_lt_iff₀ hh).2
  have hg := mul_le_mul_of_nonneg_right (geometric_endpoint hm) hh.le
  have hc : (49 / 4335 : ℝ) * (1 - a) < (1 / 80 : ℝ) * (1 - a) := by
    exact mul_lt_mul_of_pos_right (by norm_num) hh
  nlinarith only [hmul, hg, hc]

/-- Exact conversion of the first Taylor error to the correlated parameter `f`. -/
lemma first_error_le {m a d : ℝ} (hm : 7 ≤ m) (ha0 : 0 < a) (ha1 : a < 1)
    (hd : d ≤ m * (1 - a) / (3 + m * (1 - a))) :
    d / (a * (m - 2)) ≤ (1 - a) * PaperNear.f (1 / m) (m * (1 - a)) := by
  have hm0 : 0 < m := by linarith
  have hm2 : 0 < m - 2 := by linarith
  have hs : 0 < 3 + m * (1 - a) := by positivity
  have he1 : 1 - m * (1 - a) * (1 / m) = a := by field_simp; ring
  have he2 : 1 - 2 * (1 / m) = (m - 2) / m := by field_simp
  calc
    d / (a * (m - 2)) ≤ (m * (1 - a) / (3 + m * (1 - a))) / (a * (m - 2)) :=
      div_le_div_of_nonneg_right hd (by positivity)
    _ = (1 - a) * PaperNear.f (1 / m) (m * (1 - a)) := by
      unfold PaperNear.f PaperNear.P
      rw [he1, he2]
      field_simp

/-- Exact conversion of the second Taylor error; `a² ≤ 1` is proved, not assumed. -/
lemma second_error_le {m a d c : ℝ} (hm : 7 ≤ m) (ha0 : 0 < a) (ha1 : a < 1)
    (hd0 : 0 ≤ d) (hd : d ≤ m * (1 - a) / (3 + m * (1 - a)))
    (hc : 3 / (3 + m * (1 - a)) ≤ c) :
    12 * m * a ^ 2 * d ^ 2 / (c ^ 4 * (m + 1) * (m + 3)) ≤
      (1 - a) * PaperNear.g (1 / m) (m * (1 - a)) := by
  have hm0 : 0 < m := by linarith
  have hp1 : 0 < m + 1 := by linarith
  have hp3 : 0 < m + 3 := by linarith
  have hs : 0 < 3 + m * (1 - a) := by positivity
  have hc0 : 0 < 3 / (3 + m * (1 - a)) := by positivity
  have ha2 : a ^ 2 ≤ 1 := by nlinarith
  have hd2 : d ^ 2 ≤ (m * (1 - a) / (3 + m * (1 - a))) ^ 2 :=
    pow_le_pow_left₀ hd0 hd 2
  have hnum : 12 * m * a ^ 2 * d ^ 2 ≤
      12 * m * (m * (1 - a) / (3 + m * (1 - a))) ^ 2 := by
    have ht : a ^ 2 * d ^ 2 ≤ (m * (1 - a) / (3 + m * (1 - a))) ^ 2 := by
      calc
        a ^ 2 * d ^ 2 ≤ 1 * d ^ 2 := mul_le_mul_of_nonneg_right ha2 (sq_nonneg d)
        _ ≤ (m * (1 - a) / (3 + m * (1 - a))) ^ 2 := by simpa using hd2
    nlinarith only [mul_le_mul_of_nonneg_left ht (show 0 ≤ 12 * m by positivity)]
  have hden : (3 / (3 + m * (1 - a))) ^ 4 * (m + 1) * (m + 3) ≤
      c ^ 4 * (m + 1) * (m + 3) := by
    exact mul_le_mul_of_nonneg_right
      (mul_le_mul_of_nonneg_right (pow_le_pow_left₀ hc0.le hc 4) hp1.le) hp3.le
  calc
    _ ≤ (12 * m * (m * (1 - a) / (3 + m * (1 - a))) ^ 2) /
        ((3 / (3 + m * (1 - a))) ^ 4 * (m + 1) * (m + 3)) := by
      exact div_le_div₀ (by positivity) hnum (by positivity) hden
    _ = (1 - a) * PaperNear.g (1 / m) (m * (1 - a)) := by
      unfold PaperNear.g PaperNear.Q
      field_simp
      ring

/-- Both actual Taylor errors satisfy the correlated rational bounds. -/
theorem parameter_errors {m : ℕ} {a x : ℝ} (hm : 7 ≤ m)
    (ha0 : 0 < a) (ha1 : a < 1) (hx0 : -1 ≤ x) (hx1 : x ≤ 1)
    (hraw : PaperPolar.RawPolar m a x) :
    PaperTaylor.defect a x / (a * ((m : ℝ) - 2)) ≤
        (1 - a) * PaperNear.f (1 / (m : ℝ)) (PaperPolar.lambda m a) ∧
      12 * (m : ℝ) * a ^ 2 * PaperTaylor.defect a x ^ 2 /
          (PaperTaylor.chord a x ^ 4 * ((m : ℝ) + 1) * ((m : ℝ) + 3)) ≤
        (1 - a) * PaperNear.g (1 / (m : ℝ)) (PaperPolar.lambda m a) := by
  have hm' : (7 : ℝ) ≤ m := by exact_mod_cast hm
  have hb := (PaperPolar.endpoint_bounds hm ha0 ha1 hx0 hx1 hraw).1.trans
    (PaperPolar.endpoint_bounds hm ha0 ha1 hx0 hx1 hraw).2
  have hd : PaperTaylor.defect a x ≤ (m : ℝ) * (1 - a) / (3 + (m : ℝ) * (1 - a)) :=
    (PaperPolar.d_le_b a x).trans hb
  have hc : 3 / (3 + (m : ℝ) * (1 - a)) ≤ PaperTaylor.chord a x := by
    convert PaperPolar.c_lower_bound hm ha0 ha1 hx0 hx1 hraw using 1
    · rfl
    · unfold PaperTaylor.chord PaperPolar.c PaperPolar.b
      ring
  exact ⟨first_error_le hm' ha0 ha1 hd,
    second_error_le hm' ha0 ha1 (PaperTaylor.defect_nonneg ha0.le hx1) hd hc⟩

/-- The near-endpoint D theorem for the actual integral budget and raw polar input. -/
theorem near_endpoint_D {m : ℕ} {a x : ℝ} (hm : 7 ≤ m)
    (ha0 : 0 < a) (ha1 : a < 1) (hx0 : -1 ≤ x) (hx1 : x ≤ 1)
    (hraw : PaperPolar.RawPolar m a x) (hnear : (m : ℝ) * (1 - a) ≤ 2 / 5) :
    1 - (m : ℝ) * a / ((m : ℝ) + 1) - PaperTaylor.budget (m : ℝ) a x >
      (1 - a) / 1000 := by
  have hm' : (7 : ℝ) ≤ m := by exact_mod_cast hm
  have hm0 : (0 : ℝ) < m := by linarith
  have hp1 : (0 : ℝ) < (m : ℝ) + 1 := by positivity
  have hh : 0 < 1 - a := by linarith
  have ht0 : (0 : ℝ) ≤ 1 / (m : ℝ) := by positivity
  have ht7 : 1 / (m : ℝ) ≤ (1 / 7 : ℝ) := by
    exact one_div_le_one_div_of_le (by norm_num) hm'
  have hl := PaperPolar.lambda_pos (by omega : 0 < m) ha1
  have hc : 0 < PaperTaylor.chord a x := by
    have h := (PaperPolar.geometry hm ha0 ha1 hx0 hx1 hraw).2
    convert h using 1
    unfold PaperTaylor.chord PaperPolar.c PaperPolar.b
    ring
  have hbudget := PaperTaylor.budget_le hm' ha0 ha1 hx1 hc
  have herr := parameter_errors hm ha0 ha1 hx0 hx1 hraw
  have hend := (div_lt_iff₀ hh).mp (endpoint_term_lt hm ha0 ha1 hx0 hx1 hraw hnear)
  have he : PaperTaylor.beta a x 1 = PaperPolar.b a x := by
    simp [PaperTaylor.beta, PaperPolar.b]
  rw [he] at hbudget
  have hr := mul_lt_mul_of_pos_left
    (PaperNear.rational_remainder_gt (1 / (m : ℝ)) (PaperPolar.lambda m a)
      ht0 ht7 hl.le hnear) hh
  have hbase : 1 - (m : ℝ) * a / ((m : ℝ) + 1) - 1 / ((m : ℝ) + 1) =
      (1 - a) * (1 / (1 + 1 / (m : ℝ))) := by
    field_simp
    ring
  nlinarith only [hbudget, herr.1, herr.2, hend, hr, hbase]

end Sendov.PaperNearClosure
