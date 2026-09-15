import Sendov.Analytic.CenteredEndpointMoment

/-! Generic Bernstein sign consumers on a continuous real interval.  No degree,
coefficient table, or sampled endpoint is built in. The binomial theorem proves
partition of unity directly, avoiding any need to build an external cache. -/
noncomputable section
open scoped BigOperators
open Set
namespace Sendov.CenteredEndpointMoment

/-- A convex combination cannot exceed a common upper bound on its coefficients. -/
theorem weighted_sum_le {ι : Type*} (s : Finset ι) (b w : ι → ℝ) (c : ℝ)
    (hw : ∀ i ∈ s, 0 ≤ w i) (hsum : ∑ i ∈ s, w i = 1)
    (hb : ∀ i ∈ s, b i ≤ c) : ∑ i ∈ s, b i * w i ≤ c := by
  calc
    ∑ i ∈ s, b i * w i ≤ ∑ i ∈ s, c * w i :=
      Finset.sum_le_sum fun i hi => mul_le_mul_of_nonneg_right (hb i hi) (hw i hi)
    _ = c := by rw [← Finset.mul_sum, hsum, mul_one]

/-- A strictly negative common coefficient bound yields a strict sign. -/
theorem weighted_sum_neg_of_le {ι : Type*} (s : Finset ι) (b w : ι → ℝ) (c : ℝ)
    (hw : ∀ i ∈ s, 0 ≤ w i) (hsum : ∑ i ∈ s, w i = 1)
    (hb : ∀ i ∈ s, b i ≤ c) (hc : c < 0) : ∑ i ∈ s, b i * w i < 0 :=
  (weighted_sum_le s b w c hw hsum hb).trans_lt hc

/-- It also suffices to check each coefficient strictly negative, without supplying
an explicit common margin. Some weight is positive because the weights sum to one. -/
theorem weighted_sum_neg {ι : Type*} (s : Finset ι) (b w : ι → ℝ)
    (hw : ∀ i ∈ s, 0 ≤ w i) (hsum : ∑ i ∈ s, w i = 1)
    (hb : ∀ i ∈ s, b i < 0) : ∑ i ∈ s, b i * w i < 0 := by
  have hex : ∃ i ∈ s, 0 < w i := by
    by_contra! h
    have hle : ∑ i ∈ s, w i ≤ 0 := Finset.sum_nonpos h
    linarith
  obtain ⟨i, hi, hwi⟩ := hex
  have hlt := Finset.sum_lt_sum
    (fun j hj => mul_nonpos_of_nonpos_of_nonneg (hb j hj).le (hw j hj))
    (show ∃ j ∈ s, b j * w j < 0 from ⟨i, hi, mul_neg_of_neg_of_pos (hb i hi) hwi⟩)
  simpa using hlt

/-- The real evaluation of the degree-N Bernstein basis polynomial. -/
def bernsteinWeight (N k : ℕ) (r : ℝ) : ℝ :=
  (N.choose k : ℝ) * r ^ k * (1-r) ^ (N-k)

lemma bernsteinWeight_nonneg (N k : ℕ) (r : ℝ) (hr : r ∈ Icc (0 : ℝ) 1) :
    0 ≤ bernsteinWeight N k r := by
  unfold bernsteinWeight
  exact mul_nonneg (mul_nonneg (Nat.cast_nonneg _) (pow_nonneg hr.1 _))
    (pow_nonneg (sub_nonneg.2 hr.2) _)

lemma sum_bernsteinWeight (N : ℕ) (r : ℝ) :
    ∑ k ∈ Finset.range (N+1), bernsteinWeight N k r = 1 := by
  calc
    ∑ k ∈ Finset.range (N+1), bernsteinWeight N k r = (r + (1-r)) ^ N := by
      rw [add_pow]
      apply Finset.sum_congr rfl
      intro k hk
      unfold bernsteinWeight
      ring
    _ = 1 := by simp

/-- Every real point of the unit interval, including the endpoints, is certified. -/
theorem bernstein_sum_neg (N : ℕ) (b : ℕ → ℝ)
    (hb : ∀ k ∈ Finset.range (N + 1), b k < 0) (r : ℝ) (hr : r ∈ Icc (0 : ℝ) 1) :
    ∑ k ∈ Finset.range (N+1), b k * bernsteinWeight N k r < 0 :=
  weighted_sum_neg _ b (fun k => bernsteinWeight N k r)
    (fun k _ => bernsteinWeight_nonneg N k r hr) (sum_bernsteinWeight N r) hb

/-- Continuous-parameter sign transfer from a Bernstein representation of `(J-1)/h`.
No continuity hypothesis on J is necessary once this exact representation is proved. -/
theorem lt_one_of_bernstein (J : ℝ → ℝ) (H : ℝ) (hH : 0 < H)
    (N : ℕ) (b : ℕ → ℝ) (hb : ∀ k ∈ Finset.range (N + 1), b k < 0)
    (hid : ∀ h ∈ Icc (0 : ℝ) H,
      J h = 1 + h * ∑ k ∈ Finset.range (N + 1), b k * bernsteinWeight N k (h / H))
    (h : ℝ) (hh : h ∈ Ioc (0 : ℝ) H) : J h < 1 := by
  have hr : h/H ∈ Icc (0 : ℝ) 1 :=
    ⟨div_nonneg hh.1.le hH.le, (div_le_one hH).2 hh.2⟩
  have hn := bernstein_sum_neg N b hb (h/H) hr
  rw [hid h ⟨hh.1.le, hh.2⟩]
  have := mul_neg_of_pos_of_neg hh.1 hn
  linarith

/-- Exact remaining interface for an instantiated endpoint polynomial certificate.
The identity is division-free at h=0 and uses a natural power inside the integral.
A generator must prove BOTH the integral/expansion identity and every coefficient sign. -/
structure EndpointBernsteinCertificate (n N : ℕ) (X H : ℝ) where
  coeff : ℕ → ℝ
  coeff_neg : ∀ k ∈ Finset.range (N+1), coeff k < 0
  integral_identity : ∀ h ∈ Icc (0 : ℝ) H,
    (∫ t in (0 : ℝ)..1, endpointKernel (1-h) X t ^ n) =
      1 + h * ∑ k ∈ Finset.range (N+1), coeff k * bernsteinWeight N k (h/H)

/-- Converts the certified even integer exponent to the real exponent used by Lyapunov. -/
theorem EndpointBernsteinCertificate.upper_moment_lt_one
    {n N : ℕ} {X H : ℝ} (C : EndpointBernsteinCertificate n N X H)
    (hH : 0 < H) (h : ℝ) (hh : h ∈ Ioc (0 : ℝ) H) :
    (∫ t in (0 : ℝ)..1, endpointKernel (1-h) X t ^ ((2*(n : ℝ))/2)) < 1 := by
  have he : (2*(n : ℝ))/2 = n := by ring
  simp only [he, Real.rpow_natCast]
  exact lt_one_of_bernstein (fun h => ∫ t in (0 : ℝ)..1, endpointKernel (1-h) X t ^ n)
    H hH N C.coeff C.coeff_neg C.integral_identity h hh

/-- End-to-end consumer from the original multiset and FULLpolar premises.
One certificate works for every positive degree at most 2n and every real h in (0,H]. -/
theorem real_mean_gt_of_bernstein
    {n N : ℕ} {X H : ℝ} (C : EndpointBernsteinCertificate n N X H)
    (hH : 0 < H) (hX : 0 < X)
    (q : Multiset ℂ) (hm : 0 < q.card) (hq : ∀ z ∈ q, ‖z‖ ≤ 1)
    (μ : ℂ) (hmean : q.sum = q.card * μ)
    (h : ℝ) (hh : h ∈ Ioc (0 : ℝ) H) (hh1 : h < 1)
    (hmn : (q.card : ℝ) ≤ 2 * (n : ℝ))
    (hp : 1 ≤ ‖∫ t in (0 : ℝ)..1,
      (q.map (fun z => ((1 - h : ℝ) : ℂ) + (t : ℂ) *
        (1 - ((1 - h : ℝ) : ℂ) ^ 2) * z)).prod‖) :
    X < μ.re := by
  exact real_mean_gt_of_endpoint_moment q hm hq μ hmean (1-h) X (2*(n : ℝ))
    (by linarith) (by linarith [hh.1]) hX hmn hp (C.upper_moment_lt_one hH h hh)

end Sendov.CenteredEndpointMoment
