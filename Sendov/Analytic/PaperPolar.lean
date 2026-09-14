import Sendov.Reduction.BetaBound

/-!
# Raw polar input for the paper-level D problem

The degree parameter here is `m = n - 1`.  The only analytic hypothesis is
`RawPolar m a x`; in particular neither the rational endpoint bound nor an
upper bound on alpha is assumed.  We expose the actual pointwise exponential
majorant and its integral comparison before applying `Sendov.beta_le`.
-/

namespace Sendov.PaperPolar

open MeasureTheory

noncomputable def beta (a x t : ℝ) : ℝ := 1 - 2 * a * x * t + a ^ 2 * t ^ 2
noncomputable def b (a x : ℝ) : ℝ := 1 - 2 * a * x + a ^ 2
noncomputable def c (a x : ℝ) : ℝ := 1 - b a x
noncomputable def d (a x : ℝ) : ℝ := 2 * a * (1 - x)
noncomputable def alpha (m : ℕ) (a : ℝ) : ℝ := (m : ℝ) * (1 - a ^ 2) / 2
noncomputable def lambda (m : ℕ) (a : ℝ) : ℝ := (m : ℝ) * (1 - a)

/-- The raw integral, with exactly the polynomial in the paper. -/
def RawPolar (m : ℕ) (a x : ℝ) : Prop :=
  1 ≤ ∫ t in (0 : ℝ)..1,
    (a ^ 2 + 2 * a * (1 - a ^ 2) * x * t + (1 - a ^ 2) ^ 2 * t ^ 2) ^
      ((m : ℝ) / 2)

lemma raw_kernel_eq (a x t : ℝ) :
    a ^ 2 + 2 * a * (1 - a ^ 2) * x * t + (1 - a ^ 2) ^ 2 * t ^ 2 =
      Sendov.Ppolar a x t := by
  unfold Sendov.Ppolar
  ring

lemma rawPolar_iff (m : ℕ) (a x : ℝ) :
    RawPolar m a x ↔
      1 ≤ ∫ t in (0 : ℝ)..1, Sendov.Ppolar a x t ^ ((m : ℝ) / 2) := by
  simp only [RawPolar, raw_kernel_eq]

lemma beta_one (a x : ℝ) : beta a x 1 = b a x := by simp [beta, b]

lemma b_eq_QQ (a x : ℝ) : b a x = Sendov.QQ (a * x) (a ^ 2) 1 := by
  simp only [b, Sendov.QQ]
  ring

lemma x_sq_le_one {x : ℝ} (hx0 : -1 ≤ x) (hx1 : x ≤ 1) : x ^ 2 ≤ 1 := by
  nlinarith

lemma alpha_pos {m : ℕ} {a : ℝ} (hm : 0 < m) (ha0 : 0 < a) (ha1 : a < 1) :
    0 < alpha m a := by
  have hm' : (0 : ℝ) < m := by exact_mod_cast hm
  have hdelta : 0 < 1 - a ^ 2 := by nlinarith
  unfold alpha
  positivity

lemma lambda_pos {m : ℕ} {a : ℝ} (hm : 0 < m) (ha1 : a < 1) :
    0 < lambda m a := by
  have hm' : (0 : ℝ) < m := by exact_mod_cast hm
  unfold lambda
  positivity

lemma alpha_le_lambda (m : ℕ) (a : ℝ) : alpha m a ≤ lambda m a := by
  have h := mul_nonneg (Nat.cast_nonneg (α := ℝ) m) (sq_nonneg (1 - a))
  unfold alpha lambda
  nlinarith only [h]

/-- The quadratic is below its affine endpoint chord, then below an exponential.
This does not require any polar integral hypothesis. -/
lemma rpow_le_exp {m : ℕ} {a x t : ℝ} (hm : 0 < m)
    (hx0 : -1 ≤ x) (hx1 : x ≤ 1) (ht0 : 0 ≤ t) (ht1 : t ≤ 1) :
    Sendov.Ppolar a x t ^ ((m : ℝ) / 2) ≤
      Real.exp (alpha m a * (-1 + (2 - b a x) * t)) := by
  have hn : 2 ≤ m + 1 := by omega
  have he : ((m + 1 : ℕ) : ℝ) - 1 = (m : ℝ) := by push_cast; ring
  have hα : alpha m a = Sendov.M (m + 1) * (1 - a ^ 2) / 2 := by
    simp only [alpha, Sendov.M, he]
  simpa only [he, b_eq_QQ] using
    (Sendov.Ppolar_rpow_le hn (x_sq_le_one hx0 hx1) hα ht0 ht1)

/-- Actual domination of the raw integral, not a new assumption on its value. -/
theorem integral_le_exp {m : ℕ} {a x : ℝ} (hm : 0 < m)
    (hx0 : -1 ≤ x) (hx1 : x ≤ 1) :
    (∫ t in (0 : ℝ)..1, Sendov.Ppolar a x t ^ ((m : ℝ) / 2)) ≤
      ∫ t in (0 : ℝ)..1, Real.exp (alpha m a * (-1 + (2 - b a x) * t)) := by
  have he : 0 ≤ (m : ℝ) / 2 := by positivity
  refine intervalIntegral.integral_mono_on (by norm_num)
    (((continuous_rpow_const he).comp (Sendov.continuous_Ppolar a x)).intervalIntegrable _ _)
    ((by fun_prop : Continuous fun t : ℝ =>
      Real.exp (alpha m a * (-1 + (2 - b a x) * t))).intervalIntegrable _ _) ?_
  intro t ht
  exact rpow_le_exp hm hx0 hx1 ht.1 ht.2

/-- The exponential polar inequality is a consequence of raw polar. -/
theorem one_le_integral_exp {m : ℕ} {a x : ℝ} (hm : 0 < m)
    (hx0 : -1 ≤ x) (hx1 : x ≤ 1) (hraw : RawPolar m a x) :
    1 ≤ ∫ t in (0 : ℝ)..1, Real.exp (alpha m a * (-1 + (2 - b a x) * t)) :=
  ((rawPolar_iff m a x).mp hraw).trans (integral_le_exp hm hx0 hx1)

lemma b_eq_sq_add_d (a x : ℝ) : b a x = (1 - a) ^ 2 + d a x := by
  unfold b d
  ring

lemma d_nonneg {a x : ℝ} (ha0 : 0 ≤ a) (hx1 : x ≤ 1) : 0 ≤ d a x := by
  unfold d
  positivity

lemma d_le_b (a x : ℝ) : d a x ≤ b a x := by
  rw [b_eq_sq_add_d]
  nlinarith only [sq_nonneg (1 - a)]

lemma b_pos {a x : ℝ} (ha0 : 0 ≤ a) (ha1 : a < 1) (hx1 : x ≤ 1) :
    0 < b a x := by
  rw [b_eq_sq_add_d]
  have hd := d_nonneg ha0 hx1
  have hh : 0 < (1 - a) ^ 2 := sq_pos_of_pos (by linarith)
  linarith

lemma rational_mono {u v : ℝ} (hu : 0 ≤ u) (huv : u ≤ v) :
    u / (3 + u) ≤ v / (3 + v) := by
  have hv : 0 ≤ v := hu.trans huv
  apply (div_le_div_iff₀ (by positivity : 0 < 3 + u) (by positivity : 0 < 3 + v)).2
  nlinarith

/-- The stronger rational endpoint bound, with no upper bound on alpha. -/
theorem b_le_alpha {m : ℕ} {a x : ℝ} (hm : 0 < m)
    (ha0 : 0 < a) (ha1 : a < 1) (hx0 : -1 ≤ x) (hx1 : x ≤ 1)
    (hraw : RawPolar m a x) : b a x ≤ alpha m a / (3 + alpha m a) :=
  Sendov.beta_le (alpha_pos hm ha0 ha1) (b_pos ha0.le ha1 hx1).le
    (one_le_integral_exp hm hx0 hx1 hraw)

/-- Paper degree range: raw polar gives both rational endpoint bounds. -/
theorem endpoint_bounds {m : ℕ} {a x : ℝ} (hm : 7 ≤ m)
    (ha0 : 0 < a) (ha1 : a < 1) (hx0 : -1 ≤ x) (hx1 : x ≤ 1)
    (hraw : RawPolar m a x) :
    b a x ≤ alpha m a / (3 + alpha m a) ∧
      alpha m a / (3 + alpha m a) ≤ lambda m a / (3 + lambda m a) := by
  have hm0 : 0 < m := by omega
  exact ⟨b_le_alpha hm0 ha0 ha1 hx0 hx1 hraw,
    rational_mono (alpha_pos hm0 ha0 ha1).le (alpha_le_lambda m a)⟩

lemma b_lt_one {m : ℕ} {a x : ℝ} (hm : 0 < m)
    (ha0 : 0 < a) (ha1 : a < 1) (hx0 : -1 ≤ x) (hx1 : x ≤ 1)
    (hraw : RawPolar m a x) : b a x < 1 := by
  have hα := alpha_pos hm ha0 ha1
  refine (b_le_alpha hm ha0 ha1 hx0 hx1 hraw).trans_lt ?_
  apply (div_lt_one (by positivity : 0 < 3 + alpha m a)).2
  linarith

/-- The easy raw-polar geometry required by D. -/
theorem geometry {m : ℕ} {a x : ℝ} (hm : 7 ≤ m)
    (ha0 : 0 < a) (ha1 : a < 1) (hx0 : -1 ≤ x) (hx1 : x ≤ 1)
    (hraw : RawPolar m a x) : a / 2 < x ∧ 0 < c a x := by
  have hb := b_lt_one (by omega : 0 < m) ha0 ha1 hx0 hx1 hraw
  constructor
  · unfold b at hb
    nlinarith
  · unfold c
    linarith

/-- Quantitative positivity of the chord slope. -/
theorem c_lower_bound {m : ℕ} {a x : ℝ} (hm : 7 ≤ m)
    (ha0 : 0 < a) (ha1 : a < 1) (hx0 : -1 ≤ x) (hx1 : x ≤ 1)
    (hraw : RawPolar m a x) : 3 / (3 + lambda m a) ≤ c a x := by
  have hbounds := endpoint_bounds hm ha0 ha1 hx0 hx1 hraw
  have hb := hbounds.1.trans hbounds.2
  have hl := lambda_pos (by omega : 0 < m) ha1
  have hid : 3 / (3 + lambda m a) = 1 - lambda m a / (3 + lambda m a) := by
    field_simp
    ring
  rw [hid, c]
  linarith

/-- The quadratic beta lies below the chord joining 1 to b. -/
lemma beta_le_chord {a x t : ℝ} (ht0 : 0 ≤ t) (ht1 : t ≤ 1) :
    beta a x t ≤ 1 - c a x * t := by
  have h := mul_nonneg (sq_nonneg a) (mul_nonneg ht0 (sub_nonneg.mpr ht1))
  unfold beta c b
  nlinarith only [h]

/-- Positivity of beta on the integration interval. -/
lemma beta_pos {a x t : ℝ} (ha0 : 0 ≤ a) (ha1 : a < 1)
    (hx1 : x ≤ 1) (ht0 : 0 ≤ t) (ht1 : t ≤ 1) : 0 < beta a x t := by
  have hat : a * t < 1 := (mul_le_mul_of_nonneg_left ht1 ha0).trans_lt (by simpa using ha1)
  have hs : 0 < (1 - a * t) ^ 2 := sq_pos_of_pos (by linarith)
  have h := mul_nonneg (mul_nonneg ha0 ht0) (sub_nonneg.mpr hx1)
  unfold beta
  nlinarith only [hs, h]

end Sendov.PaperPolar
