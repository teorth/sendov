import Sendov.Analytic.CenteredQuarterEndpoint

noncomputable section
namespace Sendov.CenteredQuarter

/-- The explicit chord-integral tail; the original square-root C is not redefined. -/
def chordTail (m a u v : ℝ) : ℝ :=
  9*a^4*u*Real.sqrt (v^3) / ((13/18)^4*Real.sqrt (m*(m-1)*(m-2)))

lemma sqrt_fall_three (m : ℝ) (hm : 7 ≤ m) :
    (12/5)*(m-1) ≤ Real.sqrt (m*(m-1)*(m-2)) := by
  have hn : 0 ≤ m-7 := by linarith
  have ht : 0 ≤ (m-7)^2+(156/25)*(m-7)+11/25 := by positivity
  have ht' := mul_nonneg (by linarith : 0 ≤ m-1) ht
  apply Real.le_sqrt_of_sq_le
  nlinarith only [ht']

lemma chordTail_le (m a u v : ℝ) (hm : 7 ≤ m)
    (ha0 : 0 ≤ a) (ha1 : a ≤ 1) (hu0 : 0 ≤ u) (hu1 : u ≤ 1)
    (hv0 : 0 ≤ v) (hv1 : v ≤ 1/13) :
    chordTail m a u v ≤ (109350/28561)*v/(m-1) := by
  have hm1 : 0 < m-1 := by linarith
  have hD := sqrt_fall_three m hm
  have hD0 : 0 < Real.sqrt (m*(m-1)*(m-2)) := by nlinarith only [hD, hm1]
  have hs : Real.sqrt (v^3) ≤ (5/18)*v := by
    apply (Real.sqrt_le_iff).2
    constructor
    · positivity
    · have ht := mul_le_mul_of_nonneg_right hv1 (sq_nonneg v)
      nlinarith only [ht, sq_nonneg v]
  have ha4 := pow_le_one₀ ha0 ha1 (n := 4)
  have hau : a^4*u ≤ 1 := (mul_le_mul ha4 hu1 hu0 (by norm_num)).trans (by norm_num)
  have hn : 9*a^4*u*Real.sqrt (v^3) ≤ (5/2)*v := by
    have ht := mul_le_mul_of_nonneg_right hau (Real.sqrt_nonneg (v^3))
    nlinarith only [ht, hs]
  unfold chordTail
  calc
    _ ≤ ((5/2)*v)/((13/18)^4*Real.sqrt (m*(m-1)*(m-2))) :=
      div_le_div_of_nonneg_right hn (by positivity)
    _ ≤ ((5/2)*v)/((13/18)^4*((12/5)*(m-1))) := by
      apply div_le_div_of_nonneg_left (by positivity) (by positivity)
      exact mul_le_mul_of_nonneg_left hD (by positivity)
    _ = _ := by field_simp; ring

lemma gamma_le (m u v : ℝ) (hm : 7 ≤ m) (hu : 19/20 ≤ u) (hv : 0 ≤ v) :
    v/((m-1)*u^2) ≤ (10/9)*v/(m-1) := by
  have hm1 : 0 < m-1 := by linarith
  have hu0 : 0 < u := by linarith
  have hu2 : 9/10 ≤ u^2 := by nlinarith
  apply (div_le_iff₀ (mul_pos hm1 (sq_pos_of_pos hu0))).2
  have he : ((10/9)*v/(m-1))*((m-1)*u^2) = (10/9)*v*u^2 := by
    field_simp
  rw [he]
  nlinarith only [mul_le_mul_of_nonneg_left hu2 hv]

lemma five_variance_budget (m a h v : ℝ) (hm : 7 ≤ m)
    (ha : 27/28 ≤ a) (hv0 : 0 ≤ v) (hv : v ≤ m*h/3) :
    5*v/(m-1) ≤ a*v/2+59*h/72 := by
  have hm0 : 0 < m := by linarith
  have hm1 : 0 < m-1 := by linarith
  have hc : 5/(m-1) ≤ 27/56+59/(24*m) := by
    apply (div_le_iff₀ hm1).2
    have ht : 0 ≤ (m-7)*(81*m+59) := mul_nonneg (by linarith) (by linarith)
    apply (mul_le_mul_iff_right₀ (by positivity : 0 < 168*m)).mp
    field_simp
    nlinarith only [ht]
  have hc' := mul_le_mul_of_nonneg_right hc hv0
  have hvm : v/m ≤ h/3 := (div_le_iff₀ hm0).2 (by linarith only [hv])
  have hav := mul_le_mul_of_nonneg_right ha hv0
  have he : (27/56+59/(24*m))*v = (27/56)*v+(59/24)*(v/m) := by ring
  rw [he] at hc'
  have he' : 5/(m-1)*v = 5*v/(m-1) := by ring
  rw [he'] at hc'
  linarith

/-- Real scalar assembly from actual-statistic bounds and the explicit chord tail.
No hypothesis is a prepackaged E/Gamma budget. -/
theorem scalar_budget (m a h u v e0 B T : ℝ) (hm : 7 ≤ m)
    (hh0 : 0 ≤ h) (hh1 : h ≤ 1/28) (hah : a = 1-h)
    (hu : 19/20 ≤ u) (hstat : u^2+v ≤ 1)
    (hv0 : 0 ≤ v) (hv1 : v ≤ 1/13) (hv : v ≤ m*h/3)
    (he0 : e0 ≤ 2*h^2/3) (hB : B ≤ 1/50)
    (hT : T ≤ chordTail m a u v) :
    e0+v/((m-1)*u^2)*(1+B)+T ≤ 1-a*u-79*h/504 := by
  have ha0 : 0 ≤ a := by linarith
  have ha1 : a ≤ 1 := by linarith
  have ha : 27/28 ≤ a := by linarith
  have hu0 : 0 ≤ u := by linarith
  have hu1 : u ≤ 1 := by nlinarith
  have ht := hT.trans (chordTail_le m a u v hm ha0 ha1 hu0 hu1 hv0 hv1)
  have hg := gamma_le m u v hm hu hv0
  have hm1 : 0 ≤ m-1 := by linarith
  have hg0 : 0 ≤ v/((m-1)*u^2) := div_nonneg hv0 (mul_nonneg hm1 (sq_nonneg u))
  have hgb : v/((m-1)*u^2)*(1+B) ≤ (51/50)*((10/9)*v/(m-1)) := by
    have h1 := mul_le_mul_of_nonneg_left (show 1+B ≤ 51/50 by linarith) hg0
    have h2 := mul_le_mul_of_nonneg_left hg (by norm_num : (0:ℝ) ≤ 51/50)
    nlinarith only [h1, h2]
  have hvdiv : 0 ≤ v/(m-1) := div_nonneg hv0 (by linarith)
  have hcoef : (109350/28561:ℝ)+(51/50)*(10/9) ≤ 5 := by norm_num
  have hsum : v/((m-1)*u^2)*(1+B)+T ≤ 5*v/(m-1) := by
    have hc := mul_le_mul_of_nonneg_right hcoef hvdiv
    linear_combination hgb + ht + hc
  have hbudget := five_variance_budget m a h v hm ha hv0 hv
  have he : e0 ≤ h/42 := by
    have ht := mul_le_mul_of_nonneg_right hh1 hh0
    nlinarith only [he0, ht]
  have hvu : v ≤ 2*(1-u) := by nlinarith [sq_nonneg (u-1)]
  have htarget : h+a*v/2 ≤ 1-a*u := by
    have ht := mul_le_mul_of_nonneg_left hvu ha0
    nlinarith only [ht, hah]
  linarith

end Sendov.CenteredQuarter
