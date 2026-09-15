import Sendov.Analytic.CenteredNearTheorem

/-! FULLpolar implies the norm-integral inequality with the actual second moment.
There is no saturation or pointwise-bound premise in the AM-GM step itself. -/
noncomputable section
namespace Sendov.CenteredActualPolar

/-- The uncentered second moment of the actual input multiset. -/
def secondMoment (q : Multiset ℂ) : ℝ :=
  (q.map (fun z => ‖z‖^2)).sum / q.card

def kernel (q : Multiset ℂ) (a : ℝ) (μ : ℂ) (t : ℝ) : ℝ :=
  a^2+2*a*(1-a^2)*μ.re*t+(1-a^2)^2*secondMoment q*t^2

lemma secondMoment_nonneg (q : Multiset ℂ) : 0 ≤ secondMoment q := by
  unfold secondMoment
  apply div_nonneg _ (Nat.cast_nonneg _)
  exact Multiset.sum_nonneg (by
    intro y hy
    obtain ⟨z, _, rfl⟩ := Multiset.mem_map.1 hy
    exact sq_nonneg _)

lemma secondMoment_le_one (q : Multiset ℂ) (hm : 0 < q.card)
    (hq : ∀ z ∈ q, ‖z‖ ≤ 1) : secondMoment q ≤ 1 := by
  have hcard : (0 : ℝ) < q.card := by exact_mod_cast hm
  unfold secondMoment
  apply (div_le_one hcard).2
  exact sum_norm_sq_le_card q hq

/-- An exact identity before the older relaxation secondMoment<=1. -/
lemma norm_square_mean (q : Multiset ℂ) (hm : 0 < q.card) (μ : ℂ)
    (hmean : q.sum = q.card*μ) (a c : ℝ) :
    (q.map (fun z => ‖(a : ℂ)+(c : ℂ)*z‖^2)).sum/(q.card : ℝ) =
      a^2+2*a*c*μ.re+c^2*secondMoment q := by
  have hcard : (q.card : ℝ) ≠ 0 := by exact_mod_cast hm.ne'
  have hx : (q.map (fun z => z.re)).sum = (q.card : ℝ)*μ.re := by
    have hre : (q.map (fun z => z.re)).sum = q.sum.re :=
      (map_multiset_sum Complex.reAddGroupHom q).symm
    rw [hre, hmean]
    simp
  unfold secondMoment
  rw [sum_norm_sq_split, hx]
  field_simp
  <;> ring

/-- Product-norm AM-GM, retaining the actual second moment exactly. -/
theorem prod_norm_le_kernel (q : Multiset ℂ) (hm : 0 < q.card) (μ : ℂ)
    (hmean : q.sum = q.card*μ) (a t : ℝ) :
    (q.map (fun z => ‖(a : ℂ)+(t : ℂ)*(1-(a : ℂ)^2)*z‖)).prod ≤
      kernel q a μ t ^ ((q.card : ℝ)/2) := by
  have hcard : (0 : ℝ) < q.card := by exact_mod_cast hm
  let c : ℝ := t*(1-a^2)
  have he : ∀ z : ℂ, (a : ℂ)+(t : ℂ)*(1-(a : ℂ)^2)*z = (a : ℂ)+(c : ℂ)*z := by
    intro z
    dsimp [c]
    push_cast
    ring
  simp only [he]
  let P := (q.map (fun z => ‖(a : ℂ)+(c : ℂ)*z‖)).prod
  have hP : 0 ≤ P := prod_map_norm_nonneg q _
  have hg := Multiset.prod_le_mean_pow (q.map (fun z => ‖(a : ℂ)+(c : ℂ)*z‖^2)) (by
    intro y hy
    obtain ⟨z, _, rfl⟩ := Multiset.mem_map.1 hy
    exact sq_nonneg _)
  rw [Multiset.card_map, prod_map_sq, norm_square_mean q hm μ hmean] at hg
  have hk : a^2+2*a*c*μ.re+c^2*secondMoment q = kernel q a μ t := by
    unfold kernel
    dsimp [c]
    ring
  rw [hk] at hg
  have hk0 : 0 ≤ kernel q a μ t := by
    rw [← hk, ← norm_square_mean q hm μ hmean a c]
    apply div_nonneg _ hcard.le
    exact Multiset.sum_nonneg (by
      intro y hy
      obtain ⟨z, _, rfl⟩ := Multiset.mem_map.1 hy
      exact sq_nonneg _)
  have hs : (kernel q a μ t ^ ((q.card : ℝ)/2))^2 = kernel q a μ t ^ q.card := by
    rw [← Real.rpow_natCast _ 2, ← Real.rpow_mul hk0, ← Real.rpow_natCast _ q.card]
    congr 1
    push_cast
    ring
  rw [← hs] at hg
  exact (sq_le_sq₀ hP (Real.rpow_nonneg hk0 _)).1 hg

/-- FULLpolar gives the stronger actual-moment norm integral. -/
theorem actual_moment_of_fullpolar (q : Multiset ℂ) (hm : 0 < q.card) (μ : ℂ)
    (hmean : q.sum = q.card*μ) (a : ℝ)
    (hp : 1 ≤ ‖∫ t in (0 : ℝ)..1,
      (q.map (fun z => (a : ℂ)+(t : ℂ)*(1-(a : ℂ)^2)*z)).prod‖) :
    1 ≤ ∫ t in (0 : ℝ)..1, kernel q a μ t ^ ((q.card : ℝ)/2) := by
  have hstar : 1 ≤ ∫ t in (0 : ℝ)..1,
      (q.map (fun z => ‖(a : ℂ)+(t : ℂ)*(1-(a : ℂ)^2)*z‖)).prod := by
    apply hp.trans
    apply (intervalIntegral.norm_integral_le_integral_norm (by norm_num : (0 : ℝ) ≤ 1)).trans_eq
    apply intervalIntegral.integral_congr
    intro t ht
    exact norm_prod_map q _
  apply hstar.trans
  apply intervalIntegral.integral_mono_on (by norm_num : (0 : ℝ) ≤ 1)
    ((continuous_prod_norm a q).intervalIntegrable _ _)
    (((Real.continuous_rpow_const (by positivity : 0 ≤ (q.card : ℝ)/2)).comp
      (by unfold kernel; fun_prop)).intervalIntegrable _ _)
  intro t ht
  exact prod_norm_le_kernel q hm μ hmean a t

/-- The actual second moment splits into the actual centered variance and mean. -/
theorem secondMoment_eq_variance (q : Multiset ℂ) (hm : 0 < q.card) (μ : ℂ)
    (hmean : q.sum = q.card * μ) :
    secondMoment q = PaperCentered.variance (q.map (fun z => z-μ)) + ‖μ‖^2 := by
  have hc : (q.card : ℝ) ≠ 0 := by exact_mod_cast hm.ne'
  have hs := PaperCoefficient.sum_norm_add_sq (q.map (fun z => z-μ)) μ
  rw [PaperCentered.centered_sum q μ hmean] at hs
  have hmap : (q.map (fun z => z-μ)).map (fun z => ‖μ+z‖^2) =
      q.map (fun z => ‖z‖^2) := by
    simp only [Multiset.map_map, Function.comp_def]
    congr 1
    funext z
    congr 2
    ring
  rw [hmap] at hs
  simp only [Multiset.card_map, map_zero, mul_zero, Complex.zero_re, add_zero] at hs
  unfold secondMoment PaperCentered.variance
  rw [Multiset.card_map]
  field_simp
  nlinarith only [hs]

/-- A consumer expressed directly through the actual centered variance. -/
theorem actual_variance_moment_of_fullpolar (q : Multiset ℂ) (hm : 0 < q.card) (μ : ℂ)
    (hmean : q.sum = q.card * μ) (a : ℝ)
    (hp : 1 ≤ ‖∫ t in (0 : ℝ)..1,
      (q.map (fun z => (a : ℂ) + (t : ℂ) * (1 - (a : ℂ)^2) * z)).prod‖) :
    1 ≤ ∫ t in (0 : ℝ)..1,
      (a^2 + 2*a*(1-a^2)*μ.re*t + (1-a^2)^2 *
        (PaperCentered.variance (q.map (fun z => z-μ)) + ‖μ‖^2)*t^2)^((q.card : ℝ)/2) := by
  simpa only [kernel, secondMoment_eq_variance q hm μ hmean] using
    actual_moment_of_fullpolar q hm μ hmean a hp

end Sendov.CenteredActualPolar
