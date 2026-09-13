import Sendov.Common.DistillationRegularity
import Sendov.Common.TwoChord

/-!
# Correlated scalar bounds

The elementary loss is retained exactly at positive alpha. A separate full-chord
majorant cancels the common degree factors before estimating the total. It proves
a real-degree tail from 5 on `0 < alpha <= 7/5`, not on the entire alpha domain.
Neither argument uses finite rows or the old degree-tail interfaces.
-/

namespace Sendov

open MeasureTheory

noncomputable def distillTotal (m α : ℝ) : ℝ :=
  distillEBudget m + distillT0 m α + distillT1 m α + distillT2 m α

noncomputable def distillElementaryLoss (m α : ℝ) : ℝ :=
  let u := α / (α + 3)
  u ^ 2 / (180 * (1 - cubicPolarEnvelope α)) +
    u * (30 + u - u ^ 2) / 360 * (1 + 1 / m)

/-- Unlike the raw zero endpoint, this identity requires positive alpha. -/
lemma distillScalar_eq_loss_integral {m α : ℝ} (hm : 0 < m) (hα : 0 < α) :
    scalarObstruction m α (cubicPolarEnvelope α) =
      distillEBudget m - distillElementaryLoss m α + distillKappa m α *
        ∫ t in (0 : ℝ)..1,
          t ^ 3 * polarKernel m α (cubicPolarEnvelope α) t ^ ((m - 3) / 2) := by
  have he : 1 - cubicPolarEnvelope α ≠ 0 :=
    (sub_pos.mpr (cubicPolarEnvelope_lt_one hα.le)).ne'
  have hE :
      cubicPolarEnvelope α / (2 * α * (1 - cubicPolarEnvelope α)) +
        cubicPolarEnvelope α / (4 * α) + 1 / (2 * m) +
        cubicPolarEnvelope α / (4 * α * m) =
      distillEBudget m - distillElementaryLoss m α := by
    have hrat :
        cubicPolarEnvelope α / (2 * α * (1 - cubicPolarEnvelope α)) +
          cubicPolarEnvelope α / (4 * α) + 1 / (2 * m) +
          cubicPolarEnvelope α / (4 * α * m) =
        distillRatio α / (2 * (1 - cubicPolarEnvelope α)) +
          distillRatio α / 4 + 1 / (2 * m) + distillRatio α / (4 * m) := by
      rw [distillRatio_eq hα]
      field_simp [hα.ne', hm.ne', he]
    rw [hrat]
    simp only [distillElementaryLoss, distillEBudget]
    have hr : distillRatio α =
        (1 - α / (α + 3)) * (1 - (α / (α + 3)) ^ 2 / 30) / 3 := rfl
    rw [hr]
    generalize hu : α / (α + 3) = u
    have heq : cubicPolarEnvelope α = u - u ^ 3 / 30 := by
      simp only [cubicPolarEnvelope, hu]
    rw [heq] at he ⊢
    generalize hd : 1 - (u - u ^ 3 / 30) = d at he ⊢
    field_simp [hm.ne', he]
    rw [← hd]
    ring
  unfold scalarObstruction
  rw [← distillKappa_eq hα, hE]

/-- A faithful improvement of S; the definitions of S and the raw scalar stay unchanged. -/
theorem distillScalar_le_total_sub_loss {m α : ℝ} (hm : 5 ≤ m)
    (hα : 0 < α) (hαm : 2 * α ≤ m) :
    scalarObstruction m α (cubicPolarEnvelope α) ≤
      distillTotal m α - distillElementaryLoss m α := by
  rw [distillScalar_eq_loss_integral (by linarith) hα]
  have hJ := integral_polarKernel_two_chord hm hα.le hαm
    (cubicPolarEnvelope_nonneg hα.le) (cubicPolarEnvelope_lt_one hα.le)
  have h := mul_le_mul_of_nonneg_left hJ (distillKappa_nonneg hm hα.le)
  simp only [← distillNode_eq] at h
  unfold distillTotal distillT0 distillT1 distillT2
  nlinarith only [h]

noncomputable def distillChordTotal (m α : ℝ) : ℝ :=
  distillEBudget m + (8 / 27) * (α + 3) ^ 3 * (m - 2 * α) ^ 2 /
    (m * (m + 3) * (m + 5))

private lemma integral_linear_envelope_chord {m α : ℝ} (hm : 5 ≤ m)
    (hα : 0 ≤ α) (hαm : 2 * α ≤ m) :
    (∫ t in (0 : ℝ)..1,
      t ^ 3 * polarKernel m α (cubicPolarEnvelope α) t ^ ((m - 3) / 2)) ≤
      96 * (α + 3) ^ 4 /
        (81 * ((m - 1) * (m + 1) * (m + 3) * (m + 5))) := by
  have hm0 : 0 < m := by linarith
  have hs : 0 < (m - 3) / 2 := by linarith
  let c := 3 / (α + 3)
  have hc : 0 < c := by dsimp [c]; positivity
  have hc1 : c ≤ 1 := (div_le_one (by linarith)).mpr (by linarith)
  have hstop : (1 : ℝ) ≤ 1 / c := (le_div_iff₀ hc).mpr (by simpa using hc1)
  have hcont : Continuous (fun t : ℝ => t ^ 3 * (1 - c * t) ^ ((m - 3) / 2)) :=
    (by fun_prop : Continuous fun t : ℝ => t ^ 3).mul
      ((continuous_rpow_const hs.le).comp (by fun_prop))
  have hfirst :
      (∫ t in (0 : ℝ)..1,
        t ^ 3 * polarKernel m α (cubicPolarEnvelope α) t ^ ((m - 3) / 2)) ≤
      ∫ t in (0 : ℝ)..1, t ^ 3 * (1 - c * t) ^ ((m - 3) / 2) := by
    refine intervalIntegral.integral_mono_on (by norm_num)
      ((continuous_cube_mul_polarKernel_rpow _ _ _ hs.le).intervalIntegrable _ _)
      (hcont.intervalIntegrable _ _) ?_
    intro t ht
    apply mul_le_mul_of_nonneg_left _ (pow_nonneg ht.1 3)
    apply Real.rpow_le_rpow (polarKernel_nonneg hm0.le hα
      (cubicPolarEnvelope_nonneg hα) ht) _ hs.le
    have he := mul_le_mul_of_nonneg_right (cubicPolarEnvelope_le_linear hα) ht.1
    have hq : 2 * α / m ≤ 1 := (div_le_one hm0).mpr hαm
    have htprod : 0 ≤ t * (1 - t) := mul_nonneg ht.1 (sub_nonneg.mpr ht.2)
    have hqt := mul_le_mul_of_nonneg_right hq htprod
    have hid : α / (α + 3) + c = 1 := by dsimp [c]; field_simp
    unfold polarKernel
    nlinarith
  have hrest : 0 ≤ ∫ t in (1 : ℝ)..1 / c,
      t ^ 3 * (1 - c * t) ^ ((m - 3) / 2) := by
    refine intervalIntegral.integral_nonneg hstop ?_
    intro t ht
    have hct := (le_div_iff₀ hc).mp ht.2
    exact mul_nonneg (pow_nonneg (by linarith [ht.1]) 3)
      (Real.rpow_nonneg (by nlinarith) _)
  have hadd := intervalIntegral.integral_add_adjacent_intervals (μ := volume)
    (hcont.intervalIntegrable 0 1) (hcont.intervalIntegrable 1 (1 / c))
  rw [integral_chord_pow hs hc] at hadd
  have heq : 6 / (c ^ 4 * (((m - 3) / 2 + 1) * ((m - 3) / 2 + 2) *
      ((m - 3) / 2 + 3) * ((m - 3) / 2 + 4))) =
      96 * (α + 3) ^ 4 /
        (81 * ((m - 1) * (m + 1) * (m + 3) * (m + 5))) := by
    have hp : ((m - 3) / 2 + 1) * ((m - 3) / 2 + 2) *
        ((m - 3) / 2 + 3) * ((m - 3) / 2 + 4) =
        ((m - 1) * (m + 1) * (m + 3) * (m + 5)) / 16 := by ring
    rw [hp]
    dsimp [c]
    have hm1 : 0 < m - 1 := by linarith
    field_simp
    ring
  rw [heq] at hadd
  linarith

/-- The shared `(m^2-1)` cancels before bounding the degree and alpha losses. -/
theorem distillScalar_le_chordTotal {m α : ℝ} (hm : 5 ≤ m)
    (hα : 0 < α) (hαm : 2 * α ≤ m) :
    scalarObstruction m α (cubicPolarEnvelope α) ≤ distillChordTotal m α := by
  have hm0 : 0 < m := by linarith
  have hm1 : 0 < m - 1 := by linarith
  have hr : distillRatio α ≤ 1 / (α + 3) := by
    rw [distillRatio_eq hα]
    apply (div_le_iff₀ hα).mpr
    simpa only [div_eq_mul_inv, one_mul, mul_comm] using cubicPolarEnvelope_le_linear hα.le
  have hmc : 0 ≤ (m ^ 2 - 1) / (4 * m) :=
    div_nonneg (by nlinarith) (by positivity)
  have hK : distillKappa m α ≤
      (m ^ 2 - 1) / (4 * m) * (1 / (α + 3)) * (m - 2 * α) ^ 2 := by
    unfold distillKappa
    exact mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hr hmc) (sq_nonneg _)
  have hJ := integral_linear_envelope_chord hm hα.le hαm
  have hI0 : 0 ≤ ∫ t in (0 : ℝ)..1,
      t ^ 3 * polarKernel m α (cubicPolarEnvelope α) t ^ ((m - 3) / 2) := by
    refine intervalIntegral.integral_nonneg (by norm_num) ?_
    intro t ht
    exact mul_nonneg (pow_nonneg ht.1 3)
      (Real.rpow_nonneg (polarKernel_nonneg hm0.le hα.le
        (cubicPolarEnvelope_nonneg hα.le) ht) _)
  have hKI := mul_le_mul hK hJ hI0
    (mul_nonneg (mul_nonneg hmc (by positivity)) (sq_nonneg _))
  have hid :
      ((m ^ 2 - 1) / (4 * m) * (1 / (α + 3)) * (m - 2 * α) ^ 2) *
        (96 * (α + 3) ^ 4 / (81 * ((m - 1) * (m + 1) * (m + 3) * (m + 5)))) =
      (8 / 27) * (α + 3) ^ 3 * (m - 2 * α) ^ 2 / (m * (m + 3) * (m + 5)) := by
    field_simp
    ring
  rw [hid] at hKI
  have hE := distillElementary_le_budget hm0 hα
  unfold scalarObstruction distillChordTotal
  rw [← distillKappa_eq hα]
  exact add_le_add hE hKI

private lemma chord_total_polynomial_pos {m α : ℝ} (hm : 5 ≤ m)
    (hα : 0 ≤ α) (hα1 : α ≤ 7 / 5) :
    0 < (81 * m - 63) * (m + 3) * (m + 5) -
      32 * (α + 3) ^ 3 * (m - 2 * α) ^ 2 := by
  have hx : 0 ≤ m - 5 := sub_nonneg.mpr hm
  have hr : 0 ≤ 7 - 5 * α := by linarith
  let x := m - 5
  let p0 := 81 * x ^ 3 + 936 * x ^ 2 + 3996 * x + 5760
  let p1 := 2025 * x ^ 3 + 17352 * x ^ 2 + 63612 * x + 113760
  let p2 := 20250 * x ^ 3 + 98928 * x ^ 2 + 301464 * x + 1159776
  let p3 := 101250 * x ^ 3 + 40144 * x ^ 2 + 260536 * x + 8048512
  let p4 := 3125 * (x + 2) * (9 * x - 32) ^ 2 +
    26590 * x ^ 2 + 21388 * x + 24752608
  let p5 := 3125 * (x + 3) * (9 * x - 66) ^ 2 +
    59725 * (x - 4) ^ 2 + 9340 * x + 2477844
  have hx0 : 0 ≤ x := hx
  have hp0 : 0 < p0 := by dsimp [p0]; positivity
  have hp1 : 0 < p1 := by dsimp [p1]; positivity
  have hp2 : 0 < p2 := by dsimp [p2]; positivity
  have hp3 : 0 < p3 := by dsimp [p3]; positivity
  have hp4 : 0 < p4 := by dsimp [p4]; positivity
  have hp5 : 0 < p5 := by dsimp [p5]; positivity
  -- Only alpha uses a degree-five interval identity; m is unbounded.
  have hid : 7 ^ 5 * ((81 * m - 63) * (m + 3) * (m + 5) -
      32 * (α + 3) ^ 3 * (m - 2 * α) ^ 2) =
      p0 * (7 - 5 * α) ^ 5 + p1 * α * (7 - 5 * α) ^ 4 +
      p2 * α ^ 2 * (7 - 5 * α) ^ 3 + p3 * α ^ 3 * (7 - 5 * α) ^ 2 +
      p4 * α ^ 4 * (7 - 5 * α) + p5 * α ^ 5 := by
    dsimp [p0, p1, p2, p3, p4, p5, x]
    ring
  have hpos : 0 < p0 * (7 - 5 * α) ^ 5 + p1 * α * (7 - 5 * α) ^ 4 +
      p2 * α ^ 2 * (7 - 5 * α) ^ 3 + p3 * α ^ 3 * (7 - 5 * α) ^ 2 +
      p4 * α ^ 4 * (7 - 5 * α) + p5 * α ^ 5 := by
    rcases eq_or_lt_of_le hα with heq | hpos
    · rw [← heq]
      positivity
    · positivity
  rw [← hid] at hpos
  exact pos_of_mul_pos_right hpos (by norm_num)

theorem distillChordTotal_lt_one {m α : ℝ} (hm : 5 ≤ m)
    (hα : 0 ≤ α) (hα1 : α ≤ 7 / 5) : distillChordTotal m α < 1 := by
  have hm0 : 0 < m := by linarith
  have hden : 0 < 108 * m * (m + 3) * (m + 5) := by positivity
  have hid : 1 - distillChordTotal m α =
      ((81 * m - 63) * (m + 3) * (m + 5) -
        32 * (α + 3) ^ 3 * (m - 2 * α) ^ 2) /
          (108 * m * (m + 3) * (m + 5)) := by
    unfold distillChordTotal distillEBudget
    field_simp
    ring
  have hpos := div_pos (chord_total_polynomial_pos hm hα hα1) hden
  rw [← hid] at hpos
  linarith

/-- A genuine continuous tail on the small-alpha strip, not a full-domain tail. -/
theorem distillScalar_lt_one_small_alpha {m α : ℝ} (hm : 5 ≤ m)
    (hα : 0 < α) (hα1 : α ≤ 7 / 5) :
    scalarObstruction m α (cubicPolarEnvelope α) < 1 :=
  (distillScalar_le_chordTotal hm hα (by linarith)).trans_lt
    (distillChordTotal_lt_one hm hα.le hα1)

end Sendov
