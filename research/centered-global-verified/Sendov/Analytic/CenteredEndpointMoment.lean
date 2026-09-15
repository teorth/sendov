import Sendov.Analytic.CenteredActualPolar
import Mathlib.Analysis.MeanInequalities

/-! Endpoint-moment transfer.  The unit interval has mass one, so Jensen for
`x ↦ x^(m/U)` transfers one upper-exponent test to every positive lower degree.
All statistics in the FULLpolar consumer are those of the original multiset. -/
noncomputable section
open MeasureTheory Set
namespace Sendov.CenteredEndpointMoment

/-- Probability Jensen on the unit interval, proved using the supporting-line
inequality for the concave power (weighted AM-GM). Positive mass is sufficient;
no assertion about the moment being above one is used. -/
theorem integral_rpow_le (f : ℝ → ℝ) (hf : Continuous f)
    (hf0 : ∀ t ∈ Icc (0 : ℝ) 1, 0 ≤ f t)
    (hfpos : ∃ t ∈ Icc (0 : ℝ) 1, 0 < f t)
    (r : ℝ) (hr0 : 0 ≤ r) (hr1 : r ≤ 1) :
    (∫ t in (0 : ℝ)..1, f t ^ r) ≤ (∫ t in (0 : ℝ)..1, f t) ^ r := by
  let J := ∫ t in (0 : ℝ)..1, f t
  have hJ : 0 < J := intervalIntegral.integral_pos (by norm_num)
    hf.continuousOn (fun t ht => hf0 t ⟨ht.1.le, ht.2⟩) hfpos
  have hfi : IntervalIntegrable f volume 0 1 := hf.intervalIntegrable 0 1
  have hri : IntervalIntegrable (fun t => f t ^ r) volume 0 1 :=
    ((Real.continuous_rpow_const hr0).comp hf).intervalIntegrable 0 1
  have hpoint : ∀ t ∈ Icc (0 : ℝ) 1,
      f t ^ r * J ^ (1-r) ≤ r * f t + (1-r)*J := by
    intro t ht
    exact Real.geom_mean_le_arith_mean2_weighted hr0 (by linarith)
      (hf0 t ht) hJ.le (by ring)
  have hi := intervalIntegral.integral_mono_on (by norm_num : (0 : ℝ) ≤ 1)
    (hri.mul_const (J ^ (1-r))) (hfi.const_mul r |>.add (intervalIntegrable_const)) hpoint
  rw [intervalIntegral.integral_mul_const, intervalIntegral.integral_add
    (hfi.const_mul r) intervalIntegrable_const,
    intervalIntegral.integral_const_mul, intervalIntegral.integral_const] at hi
  have hprod : J ^ r * J ^ (1-r) = J := by
    rw [← Real.rpow_add hJ]
    norm_num
  have hright : r * (∫ t in (0 : ℝ)..1, f t) +
      (1 - (0 : ℝ)) • ((1-r)*J) = J := by dsimp [J]; simp; ring
  rw [hright] at hi
  exact (mul_le_mul_iff_left₀ (Real.rpow_pos_of_pos hJ (1-r))).1 (hi.trans_eq hprod.symm)

/-- Lyapunov's moment inequality for a continuous nonnegative kernel on `[0,1]`. -/
theorem moment_le_upper (f : ℝ → ℝ) (hf : Continuous f)
    (hf0 : ∀ t ∈ Icc (0 : ℝ) 1, 0 ≤ f t)
    (hfpos : ∃ t ∈ Icc (0 : ℝ) 1, 0 < f t)
    (m U : ℝ) (hm : 0 < m) (hmU : m ≤ U) :
    (∫ t in (0 : ℝ)..1, f t ^ (m/2)) ≤
      (∫ t in (0 : ℝ)..1, f t ^ (U/2)) ^ (m/U) := by
  have hU : 0 < U := hm.trans_le hmU
  have hr0 : 0 ≤ m/U := div_nonneg hm.le hU.le
  have hr1 : m/U ≤ 1 := (div_le_one hU).2 hmU
  have hj := integral_rpow_le (fun t => f t ^ (U/2))
    ((Real.continuous_rpow_const (by positivity : 0 ≤ U/2)).comp hf)
    (fun t ht => Real.rpow_nonneg (hf0 t ht) _)
    (by obtain ⟨t, ht, hpos⟩ := hfpos; exact ⟨t, ht, Real.rpow_pos_of_pos hpos _⟩)
    (m/U) hr0 hr1
  apply le_trans (le_of_eq ?_) hj
  apply intervalIntegral.integral_congr
  intro t ht
  dsimp only
  rw [← Real.rpow_mul (hf0 t (by simpa using ht))]
  congr 1
  field_simp

/-- An upper moment strictly below one forces every positive lower moment below one. -/
theorem moment_lt_one_of_upper (f : ℝ → ℝ) (hf : Continuous f)
    (hf0 : ∀ t ∈ Icc (0 : ℝ) 1, 0 ≤ f t)
    (hfpos : ∃ t ∈ Icc (0 : ℝ) 1, 0 < f t)
    (m U : ℝ) (hm : 0 < m) (hmU : m ≤ U)
    (hupper : (∫ t in (0 : ℝ)..1, f t ^ (U / 2)) < 1) :
    (∫ t in (0 : ℝ)..1, f t ^ (m/2)) < 1 := by
  have hU : 0 < U := hm.trans_le hmU
  have hnonneg : 0 ≤ ∫ t in (0 : ℝ)..1, f t ^ (U/2) :=
    intervalIntegral.integral_nonneg (by norm_num) (fun t ht =>
      Real.rpow_nonneg (hf0 t ht) _)
  exact (moment_le_upper f hf hf0 hfpos m U hm hmU).trans_lt
    (Real.rpow_lt_one hnonneg hupper (div_pos hm hU))

/-- The relaxed endpoint kernel uses a proposed real-mean threshold and only the
proved upper bound on the actual second moment; it is not an actual-statistic assignment. -/
def endpointKernel (a X t : ℝ) : ℝ :=
  a^2 + 2*a*(1-a^2)*X*t + (1-a^2)^2*t^2

lemma endpointKernel_nonneg (a X : ℝ) (ha0 : 0 ≤ a) (ha1 : a ≤ 1) (hX : 0 ≤ X)
    (t : ℝ) (ht : 0 ≤ t) : 0 ≤ endpointKernel a X t := by
  have hd : 0 ≤ 1-a^2 := by nlinarith
  unfold endpointKernel
  positivity

/-- Pointwise monotonicity in the actual real mean and second moment. -/
lemma kernel_le_endpoint (q : Multiset ℂ) (hm : 0 < q.card)
    (hq : ∀ z ∈ q, ‖z‖ ≤ 1) (μ : ℂ) (a X : ℝ)
    (ha0 : 0 ≤ a) (ha1 : a ≤ 1) (hx : μ.re ≤ X)
    (t : ℝ) (ht : 0 ≤ t) :
    CenteredActualPolar.kernel q a μ t ≤ endpointKernel a X t := by
  have hd : 0 ≤ 1-a^2 := by nlinarith
  have hs := CenteredActualPolar.secondMoment_le_one q hm hq
  have hx' := mul_le_mul_of_nonneg_left hx (show 0 ≤ 2*a*(1-a^2)*t by positivity)
  have hs' := mul_le_mul_of_nonneg_left hs (show 0 ≤ (1-a^2)^2*t^2 by positivity)
  unfold CenteredActualPolar.kernel endpointKernel
  nlinarith only [hx', hs']

/-- Nonnegativity comes from the original squared norms and actual mean identity. -/
lemma actualKernel_nonneg (q : Multiset ℂ) (hm : 0 < q.card) (μ : ℂ)
    (hmean : q.sum = q.card * μ) (a t : ℝ) :
    0 ≤ CenteredActualPolar.kernel q a μ t := by
  have hs := CenteredActualPolar.norm_square_mean q hm μ hmean a (t*(1-a^2))
  have he : a^2 + 2*a*(t*(1-a^2))*μ.re +
      (t*(1-a^2))^2*CenteredActualPolar.secondMoment q = CenteredActualPolar.kernel q a μ t := by
    unfold CenteredActualPolar.kernel
    ring
  rw [he] at hs
  rw [← hs]
  apply div_nonneg _ (Nat.cast_nonneg _)
  exact Multiset.sum_nonneg (by
    intro y hy
    obtain ⟨z, _, rfl⟩ := Multiset.mem_map.1 hy
    exact sq_nonneg _)

/-- Main FULLpolar consumer: one upper-exponent endpoint certificate gives a strict
bound on the real part of the actual complex mean for every positive degree `m ≤ U`.
The exponent `U` is real; evenness is needed only to construct a polynomial certificate. -/
theorem real_mean_gt_of_endpoint_moment
    (q : Multiset ℂ) (hm : 0 < q.card) (hq : ∀ z ∈ q, ‖z‖ ≤ 1)
    (μ : ℂ) (hmean : q.sum = q.card * μ) (a X U : ℝ)
    (ha0 : 0 < a) (ha1 : a < 1) (hX : 0 < X)
    (hmU : (q.card : ℝ) ≤ U)
    (hp : 1 ≤ ‖∫ t in (0 : ℝ)..1,
      (q.map (fun z => (a : ℂ) + (t : ℂ) * (1 - (a : ℂ) ^ 2) * z)).prod‖)
    (hupper : (∫ t in (0 : ℝ)..1, endpointKernel a X t ^ (U / 2)) < 1) :
    X < μ.re := by
  by_contra! hx
  have hmR : 0 < (q.card : ℝ) := by exact_mod_cast hm
  have hactual := CenteredActualPolar.actual_moment_of_fullpolar q hm μ hmean a hp
  have hmono : (∫ t in (0 : ℝ)..1, CenteredActualPolar.kernel q a μ t ^ ((q.card : ℝ)/2)) ≤
      ∫ t in (0 : ℝ)..1, endpointKernel a X t ^ ((q.card : ℝ)/2) := by
    apply intervalIntegral.integral_mono_on (by norm_num)
      (((Real.continuous_rpow_const (by positivity : 0 ≤ (q.card : ℝ)/2)).comp
        (by unfold CenteredActualPolar.kernel; fun_prop)).intervalIntegrable _ _)
      (((Real.continuous_rpow_const (by positivity : 0 ≤ (q.card : ℝ)/2)).comp
        (by unfold endpointKernel; fun_prop)).intervalIntegrable _ _)
    intro t ht
    exact Real.rpow_le_rpow (actualKernel_nonneg q hm μ hmean a t)
      (kernel_le_endpoint q hm hq μ a X ha0.le ha1.le hx t ht.1) (by positivity)
  have hlt := moment_lt_one_of_upper (endpointKernel a X)
    (by unfold endpointKernel; fun_prop)
    (fun t ht => endpointKernel_nonneg a X ha0.le ha1.le hX.le t ht.1)
    (by refine ⟨0, by norm_num, ?_⟩; simpa [endpointKernel] using sq_pos_of_pos ha0)
    q.card U hmR hmU hupper
  exact (not_lt_of_ge (hactual.trans hmono)) hlt

end Sendov.CenteredEndpointMoment
