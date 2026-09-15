import Sendov.Analytic.PaperRayGeometry
import Sendov.Analytic.PaperTail

/-!
# Historical quantitative bounds on wide rays

The conclusions concern the actual `PaperTaylor.budget`, under `RawPolar`.
They preserve HI01--HI03, not just the later conclusion `T < B`.

Sources: first-origin-uniform/REPORT.md §4.3; round3/REPORT.md §3;
round4/REPORT.md §5. The lower lambda cutoffs are retained in the historical
interfaces, although the upper estimates themselves do not need them.
HI01 follows from the sharp Laplace estimate on the *whole* lambda <= 400
band, including lambda < 1/10. No appeal to a whole-domain D theorem is made.

Numerical certificates are fixed rational Taylor sums at two endpoints.
Uniformity in degree comes from generic exponential-polynomial monotonicity.
-/
namespace Sendov.PaperWideRays

open PaperPolar

/-- Generic endpoint certificate, with arbitrary real cutoff and coefficient. -/
lemma tail_certificate {m M r A C : ℝ} {n : ℕ}
    (hM : 0 < M) (hm : M ≤ m) (hm1 : 1 ≤ m)
    (hr : 0 < r) (hr1 : r ≤ 1) (hA : 0 ≤ A) (hn : 1 ≤ n)
    (hcrit : (n : ℝ) ≤ (1 - r) / 2 * M)
    (hbase : A * M ^ n < C * Real.exp ((1 - r) / 2 * (M - 1))) :
    A * m ^ n * r ^ ((m - 1) / 2) < C := by
  have hmono := PaperTail.power_exp_antitone (d := 1) hn hM
    (show 0 ≤ (1 - r) / 2 by linarith) hcrit
    (show M ∈ Set.Ici M by simp) hm hm
  have hpow := mul_le_mul_of_nonneg_left (PaperTail.rpow_le_exp hr hm1)
    (show 0 ≤ A * m ^ n by positivity)
  have hbound : A * m ^ n * r ^ ((m - 1) / 2) ≤
      A * M ^ n * Real.exp (-((1 - r) / 2) * (M - 1)) := by
    have h := mul_le_mul_of_nonneg_left hmono hA
    dsimp at h
    nlinarith only [hpow, h]
  apply hbound.trans_lt
  rw [show -((1 - r) / 2) * (M - 1) = -((1 - r) / 2 * (M - 1)) by ring,
    Real.exp_neg]
  exact (div_lt_iff₀ (Real.exp_pos _)).mpr hbase |>.trans_eq (by ring)

/-- The complete right tail of the lambda <= 400 estimate. -/
lemma tail_10000 {m : ℝ} (hm : 10000 ≤ m) :
    (m ^ 2 / 2 + m) * (99 / 100 : ℝ) ^ ((m - 1) / 2) < 1 / m := by
  have he : (5001 / 10000 : ℝ) * 10000 ^ (3 : ℕ) <
      Real.exp ((1 - 99 / 100) / 2 * (10000 - 1)) := by
    have h := Real.sum_le_exp_of_nonneg
      (by norm_num : (0 : ℝ) ≤ (1 - 99 / 100) / 2 * (10000 - 1)) 16
    norm_num [Finset.sum_range_succ, Nat.factorial_succ] at h ⊢
    linarith
  have h := tail_certificate (n := 3) (C := 1) (by norm_num : (0 : ℝ) < 10000)
    hm (by linarith) (by norm_num : (0 : ℝ) < 99 / 100) (by norm_num)
    (by norm_num : (0 : ℝ) ≤ 5001 / 10000) (by norm_num) (by norm_num)
    (by simpa using he)
  have hc : (m ^ 2 / 2 + m) * m ≤ (5001 / 10000 : ℝ) * m ^ 3 := by
    nlinarith only [mul_nonneg (sq_nonneg m) (show 0 ≤ m - 10000 by linarith)]
  apply (lt_div_iff₀ (show 0 < m by linarith)).mpr
  nlinarith only [mul_le_mul_of_nonneg_right hc
    (Real.rpow_nonneg (by norm_num : (0 : ℝ) ≤ 99 / 100) ((m - 1) / 2)), h]

/-- The historical 1/32 tail, uniformly for every real m >= 512. -/
lemma tail_512 {m : ℝ} (hm : 512 ≤ m) :
    (m ^ 2 / 2 + m) * (15 / 16 : ℝ) ^ ((m - 1) / 2) < 1 / 32 := by
  have he : (257 / 512 : ℝ) * 512 ^ (2 : ℕ) <
      (1 / 32 : ℝ) * Real.exp ((1 - 15 / 16) / 2 * (512 - 1)) := by
    have h := Real.sum_le_exp_of_nonneg
      (by norm_num : (0 : ℝ) ≤ (1 - 15 / 16) / 2 * (512 - 1)) 20
    norm_num [Finset.sum_range_succ, Nat.factorial_succ] at h ⊢
    linarith
  have h := tail_certificate (n := 2) (by norm_num : (0 : ℝ) < 512)
    hm (by linarith) (by norm_num : (0 : ℝ) < 15 / 16) (by norm_num)
    (by norm_num : (0 : ℝ) ≤ 257 / 512) (by norm_num) (by norm_num) he
  have hc : m ^ 2 / 2 + m ≤ (257 / 512 : ℝ) * m ^ 2 := by
    nlinarith only [mul_nonneg (show 0 ≤ m by linarith) (show 0 ≤ m - 512 by linarith)]
  exact (mul_le_mul_of_nonneg_right hc (Real.rpow_nonneg (by norm_num) _)).trans_lt h

lemma exp_four_lt : Real.exp (4 : ℝ) < 68 := by
  have he : Real.exp (1 : ℝ) < 11 / 4 := Real.exp_one_lt_d9.trans (by norm_num)
  calc
    Real.exp (4 : ℝ) = Real.exp (1 : ℝ) ^ 4 := by rw [← Real.exp_nat_mul]; norm_num
    _ ≤ (11 / 4 : ℝ) ^ 4 := pow_le_pow_left₀ (Real.exp_nonneg _) he.le _
    _ < 68 := by norm_num

/-- Convexity in alpha extends this single endpoint check to 0 < alpha <= 400. -/
lemma fixed_400 :
    (∫ t in (0 : ℝ)..1, Real.exp (400 * (-1 + (2 - 99 / 100) * t))) < 1 := by
  rw [Sendov.integral_exp_eq' (by norm_num : (0 : ℝ) < 400)
    (by norm_num : (99 / 100 : ℝ) < 2)]
  norm_num
  have he := exp_four_lt
  have hp := Real.exp_pos (-400 : ℝ)
  linarith

lemma fixed_64 :
    (∫ t in (0 : ℝ)..1, Real.exp (64 * (-1 + (2 - 15 / 16) * t))) < 1 := by
  rw [Sendov.integral_exp_eq' (by norm_num : (0 : ℝ) < 64)
    (by norm_num : (15 / 16 : ℝ) < 2)]
  norm_num
  have he := exp_four_lt
  have hp := Real.exp_pos (-64 : ℝ)
  linarith

/-- Retained radius from a real lower degree bound and the actual lambda. -/
lemma a_lower {m : ℕ} {a M L : ℝ} (hM : 0 < M) (hm : M ≤ m)
    (ha1 : a < 1) (hl : lambda m a ≤ L) : 1 - L / M ≤ a := by
  have hh := mul_nonneg (sub_nonneg.mpr hm) (show 0 ≤ 1 - a by linarith)
  unfold lambda at hl
  have hdiv : 1 - a ≤ L / M := (le_div_iff₀ hM).mpr (by nlinarith)
  linarith

/-- Actual endpoint and x bounds over the entire wide band. -/
theorem geometry_400 {m : ℕ} {a x : ℝ} (hm : 10000 ≤ m)
    (ha : 0 < a) (ha1 : a < 1) (hx0 : -1 ≤ x) (hx1 : x ≤ 1)
    (hr : RawPolar m a x) (hl : lambda m a ≤ 400) :
    24 / 25 ≤ a ∧ 12 / 25 < x ∧ b a x < 99 / 100 := by
  have hm' : (10000 : ℝ) ≤ m := by exact_mod_cast hm
  have ha' := a_lower (by norm_num : (0 : ℝ) < 10000) hm' ha1 hl
  norm_num at ha'
  have hx := (geometry (by omega) ha ha1 hx0 hx1 hr).1
  exact ⟨ha', by linarith, PaperRayGeometry.b_lt_of_fixed (by omega) ha ha1 hx0 hx1 hr hl fixed_400⟩

/-- The full lambda <= 400 estimate; no artificial lower cutoff is needed. -/
theorem scaled_budget_lt_400 {m : ℕ} {a x : ℝ} (hm : 10000 ≤ m)
    (ha : 0 < a) (ha1 : a < 1) (hx0 : -1 ≤ x) (hx1 : x ≤ 1)
    (hr : RawPolar m a x) (hl : lambda m a ≤ 400) :
    (m : ℝ) * x ^ 2 * PaperTaylor.budget m a x < 1 + 46 / (m : ℝ) := by
  have hm' : (10000 : ℝ) ≤ m := by exact_mod_cast hm
  obtain ⟨ha', hx, hb⟩ := geometry_400 hm ha ha1 hx0 hx1 hr hl
  have h := PaperLaplace.sharp_laplace (by omega : 7 ≤ m) (by linarith : 1 / 2 < a)
    ha1 hx0 hx1 hr (by nlinarith : 1 - 3 * x ^ 2 / 4 ≤ (99 / 100 : ℝ)) hb.le
  have hmain := PaperTail.laplace_main_lt (K := 45) (by linarith : (256 : ℝ) ≤ m)
    (by norm_num : (0 : ℝ) < 12 / 25) hx.le (by norm_num)
  have ht := tail_10000 hm'
  have heq : 45 / (m : ℝ) + 1 / m = 46 / m := by ring
  linarith only [h, hmain, ht, heq]

/-- HI01: the exact historical constant, on its original closed lambda band. -/
theorem HI01 {m : ℕ} {a x : ℝ} (hm : 100000 ≤ m)
    (ha : 0 < a) (ha1 : a < 1) (hx0 : -1 ≤ x) (hx1 : x ≤ 1)
    (hr : RawPolar m a x) (_hl0 : 1 / 50 ≤ lambda m a) (hl1 : lambda m a ≤ 400) :
    (m : ℝ) * x ^ 2 * PaperTaylor.budget m a x < 5011 / 5000 := by
  have hm' : (100000 : ℝ) ≤ m := by exact_mod_cast hm
  have h := scaled_budget_lt_400 (by omega : 10000 ≤ m) ha ha1 hx0 hx1 hr hl1
  have hsmall : 46 / (m : ℝ) ≤ 46 / 100000 := by
    apply (div_le_div_iff₀ (by linarith) (by norm_num)).mpr
    linarith
  linarith

/-- HI02: the exact historical O(1/m) bound, not a statement of D. -/
theorem HI02 {m : ℕ} {a x : ℝ} (hm : 10000 ≤ m)
    (ha : 0 < a) (ha1 : a < 1) (hx0 : -1 ≤ x) (hx1 : x ≤ 1)
    (hr : RawPolar m a x) (_hl0 : 1 / 10 ≤ lambda m a) (hl1 : lambda m a ≤ 400) :
    (m : ℝ) * x ^ 2 * PaperTaylor.budget m a x < 1 + 46 / (m : ℝ) :=
  scaled_budget_lt_400 hm ha ha1 hx0 hx1 hr hl1

/-- HI03: the whole historical band through lambda=64 with its 1/32 tail. -/
theorem HI03 {m : ℕ} {a x : ℝ} (hm : 512 ≤ m)
    (ha : 0 < a) (ha1 : a < 1) (hx0 : -1 ≤ x) (hx1 : x ≤ 1)
    (hr : RawPolar m a x) (_hl0 : 5 ≤ lambda m a) (hl1 : lambda m a ≤ 64) :
    (m : ℝ) * x ^ 2 * PaperTaylor.budget m a x < 1 + 53 / (m : ℝ) + 1 / 32 := by
  have hm' : (512 : ℝ) ≤ m := by exact_mod_cast hm
  have ha' := a_lower (by norm_num : (0 : ℝ) < 512) hm' ha1 hl1
  norm_num at ha'
  have hb := PaperRayGeometry.b_lt_of_fixed (by omega : 0 < m) ha ha1 hx0 hx1 hr hl1 fixed_64
  -- Retain the endpoint information also in the x lower bound. This permits
  -- reuse of the existing general Laplace constants without a new cube bound.
  have hx' := PaperRayGeometry.x_lower_constant (by norm_num : (0 : ℝ) < 7 / 8)
    ha' (by norm_num : (0 : ℝ) ≤ 15 / 16) hb.le
  have hx : 9 / 20 ≤ x := by norm_num at hx'; linarith
  have h := PaperLaplace.sharp_laplace (by omega : 7 ≤ m) (by linarith : 1 / 2 < a)
    ha1 hx0 hx1 hr (by nlinarith : 1 - 3 * x ^ 2 / 4 ≤ (15 / 16 : ℝ)) hb.le
  have hmain := PaperTail.laplace_main_lt (K := 53) (by linarith : (256 : ℝ) ≤ m)
    (by norm_num : (0 : ℝ) < 9 / 20) hx (by norm_num)
  have ht := tail_512 hm'
  linarith only [h, hmain, ht]

/-- HI03's first retained small-ray band, including both seams. -/
theorem HI03_small_one {m : ℕ} {a x : ℝ} (hm : 512 ≤ m)
    (ha : 0 < a) (ha1 : a < 1) (hx0 : -1 ≤ x) (hx1 : x ≤ 1)
    (hr : RawPolar m a x) (_hl0 : 1 / 10 ≤ lambda m a) (hl1 : lambda m a ≤ 1) :
    (m : ℝ) * x ^ 2 * PaperTaylor.budget m a x < 1 + 18 / (m : ℝ) := by
  have hm' : (256 : ℝ) ≤ m := by exact_mod_cast (show 256 ≤ m by omega)
  have hx := PaperRayGeometry.geometry_one (by omega) ha ha1 hx0 hx1 hr hl1
  have hb := (PaperRayGeometry.geometry_ten (by omega) ha ha1 hx0 hx1 hr
    (by linarith : lambda m a ≤ 10)).1
  have ha' := PaperRayGeometry.a_lower (by omega) ha1 hl1
  have hb' : PaperTaylor.beta a x 1 ≤ 4 / 5 := by
    simpa [PaperTaylor.beta, b] using hb.le
  exact PaperTail.budget_region_one hm' ha ha1 hx hx1 (by linarith) hb'

/-- HI03's second retained small-ray band; the available 33/m is stronger. -/
theorem HI03_small_five {m : ℕ} {a x : ℝ} (hm : 512 ≤ m)
    (ha : 0 < a) (ha1 : a < 1) (hx0 : -1 ≤ x) (hx1 : x ≤ 1)
    (hr : RawPolar m a x) (_hl0 : 1 ≤ lambda m a) (hl1 : lambda m a ≤ 5) :
    (m : ℝ) * x ^ 2 * PaperTaylor.budget m a x < 1 + 34 / (m : ℝ) := by
  have hm' : (256 : ℝ) ≤ m := by exact_mod_cast (show 256 ≤ m by omega)
  obtain ⟨hb, hx⟩ := PaperRayGeometry.geometry_ten (by omega) ha ha1 hx0 hx1 hr
    (by linarith : lambda m a ≤ 10)
  have ha' := PaperRayGeometry.a_lower (by omega) ha1 hl1
  have hb' : PaperTaylor.beta a x 1 ≤ 4 / 5 := by
    simpa [PaperTaylor.beta, b] using hb.le
  have h := PaperTail.budget_region_two hm' ha ha1 hx hx1 (by linarith) hb'
  have hc : 33 / (m : ℝ) ≤ 34 / m :=
    div_le_div_of_nonneg_right (by norm_num) (by positivity)
  linarith only [h, hc]

end Sendov.PaperWideRays
