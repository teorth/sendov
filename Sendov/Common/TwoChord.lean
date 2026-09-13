/-
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Sendov.Common.Chord
import Sendov.Common.DistillationKernel
import Mathlib.Analysis.Convex.SpecificFunctions.Basic

/-!
# Two-chord integral bound on the enlarged scalar domain

Adapted mathematically from Senjian An, *Proof Distillation for Sendov's Conjecture*,
revision e8ae601491ec171ab4f7f8456113dd6a047aa85d, Section 4, equations (4.3)–(4.6)
(TEX lines 371–435). Paper licensed CC BY 4.0:
https://creativecommons.org/licenses/by/4.0/ . This is a new Lean proof, not upstream code.

The endpoint parameter is independent of alpha: both the original linear envelope and
its cubic improvement can use this API. No global geometric feasibility is required.
-/

namespace Sendov

open MeasureTheory

/-- The interior node stays strictly between zero and one, including degenerate parameters. -/
lemma polarKernel_three_fifths_mem {m α η : ℝ} (hm : 0 < m) (hα : 0 ≤ α)
    (hαm : 2 * α ≤ m) (hη : 0 ≤ η) (hη1 : η < 1) :
    polarKernel m α η (3 / 5) ∈ Set.Ioo (0 : ℝ) 1 := by
  have hratio : 0 ≤ 2 * α / m := div_nonneg (by positivity) hm.le
  have hratio1 : 2 * α / m ≤ 1 := (div_le_one hm).mpr hαm
  unfold polarKernel
  constructor <;> nlinarith

/-- First secant, without a geometric feasibility assumption. -/
lemma polarKernel_le_first_chord {m α η t : ℝ} (hm : 0 < m) (hαm : 2 * α ≤ m)
    (ht : t ∈ Set.Icc (0 : ℝ) (3 / 5)) :
    polarKernel m α η t ≤ 1 - ((1 - polarKernel m α η (3 / 5)) / (3 / 5)) * t := by
  have hA : 0 ≤ 1 - 2 * α / m := sub_nonneg.mpr ((div_le_one hm).mpr hαm)
  have h := QQ_le_secant (c := 1 - α / m - η / 2) hA
    (by norm_num : (0 : ℝ) < 3 / 5) ht
  simp only [← polarKernel_eq_QQ] at h
  have hzero : polarKernel m α η 0 = 1 := by simp [polarKernel]
  rw [hzero] at h
  convert h using 1; ring

/-- Second secant on its own interval. -/
lemma polarKernel_le_second_chord {m α η t : ℝ} (hm : 0 < m) (hαm : 2 * α ≤ m)
    (ht : t ∈ Set.Icc (3 / 5 : ℝ) 1) :
    polarKernel m α η t ≤ (1 - t) / (1 - 3 / 5) * polarKernel m α η (3 / 5) +
      (t - 3 / 5) / (1 - 3 / 5) * η := by
  have hA : 0 ≤ 1 - 2 * α / m := sub_nonneg.mpr ((div_le_one hm).mpr hαm)
  have h := QQ_le_secant (c := 1 - α / m - η / 2) hA
    (by norm_num : (3 / 5 : ℝ) < 1) ht
  simp only [← polarKernel_eq_QQ] at h
  have hone : polarKernel m α η 1 = η := by simp [polarKernel]
  rw [hone] at h
  convert h using 1; ring

/-- Convexity separates the endpoint powers on the second interval, also at zero endpoints. -/
lemma polarKernel_rpow_le_second_chord {m α η s t : ℝ} (hm : 0 < m)
    (hα : 0 ≤ α) (hαm : 2 * α ≤ m) (hη : 0 ≤ η) (hs : 1 ≤ s)
    (ht : t ∈ Set.Icc (3 / 5 : ℝ) 1) :
    polarKernel m α η t ^ s ≤
      (1 - t) / (1 - 3 / 5) * polarKernel m α η (3 / 5) ^ s +
      (t - 3 / 5) / (1 - 3 / 5) * η ^ s := by
  have hbase := polarKernel_nonneg hm.le hα hη
    (show t ∈ Set.Icc (0 : ℝ) 1 from ⟨by linarith [ht.1], ht.2⟩)
  refine (Real.rpow_le_rpow hbase (polarKernel_le_second_chord hm hαm ht)
    (by linarith)).trans ?_
  have hb := polarKernel_nonneg hm.le hα hη
    (show (3 / 5 : ℝ) ∈ Set.Icc (0 : ℝ) 1 by norm_num)
  have hw₀ : 0 ≤ (1 - t) / (1 - 3 / 5 : ℝ) :=
    div_nonneg (sub_nonneg.mpr ht.2) (by norm_num)
  have hw₁ : 0 ≤ (t - 3 / 5) / (1 - 3 / 5 : ℝ) :=
    div_nonneg (sub_nonneg.mpr ht.1) (by norm_num)
  have hw : (1 - t) / (1 - 3 / 5 : ℝ) + (t - 3 / 5) / (1 - 3 / 5 : ℝ) = 1 := by ring
  simpa only [smul_eq_mul] using (convexOn_rpow hs).2 hb hη hw₀ hw₁ hw

/-- Continuity provides all interval integrability used below. -/
lemma continuous_cube_mul_polarKernel_rpow (m α η : ℝ) {s : ℝ} (hs : 0 ≤ s) :
    Continuous (fun t : ℝ => t ^ 3 * polarKernel m α η t ^ s) := by
  simp only [polarKernel_eq_QQ]
  exact continuous_pow_mul_QQ _ _ _ hs

/-- First chord integrated exactly to its zero, never past a negative base. -/
lemma integral_first_chord_to_zero {b s : ℝ} (hb : b < 1) (hs : 0 < s) :
    (∫ t in (0 : ℝ)..(3 / 5) / (1 - b), t ^ 3 * (1 - ((1 - b) / (3 / 5)) * t) ^ s) =
      6 * (3 / 5) ^ 4 / ((s + 1) * (s + 2) * (s + 3) * (s + 4) * (1 - b) ^ 4) := by
  have hc : 0 < (1 - b) / (3 / 5 : ℝ) := by positivity
  have hend : (3 / 5 : ℝ) / (1 - b) = 1 / ((1 - b) / (3 / 5)) := by
    rw [one_div_div]
  rw [hend, integral_chord_pow hs hc]
  rw [div_pow, div_mul_eq_mul_div, div_div_eq_mul_div]
  ring

/-- Extending the first chord to its zero gives the beta-integral majorant. -/
lemma integral_polarKernel_first_chord {m α η s : ℝ} (hm : 0 < m)
    (hα : 0 ≤ α) (hαm : 2 * α ≤ m) (hη : 0 ≤ η) (hη1 : η < 1) (hs : 0 < s) :
    (∫ t in (0 : ℝ)..(3 / 5), t ^ 3 * polarKernel m α η t ^ s) ≤
      6 * (3 / 5) ^ 4 /
        ((s + 1) * (s + 2) * (s + 3) * (s + 4) * (1 - polarKernel m α η (3 / 5)) ^ 4) := by
  set b := polarKernel m α η (3 / 5)
  have hb := polarKernel_three_fifths_mem hm hα hαm hη hη1
  have hz : (3 / 5 : ℝ) ≤ (3 / 5) / (1 - b) := by
    apply (le_div_iff₀ (by dsimp [b]; linarith [hb.2])).mpr
    dsimp [b]
    nlinarith [hb.1]
  have hcont : Continuous (fun t : ℝ => t ^ 3 * (1 - ((1 - b) / (3 / 5)) * t) ^ s) :=
    (by fun_prop : Continuous fun t : ℝ => t ^ 3).mul
      ((continuous_rpow_const hs.le).comp (by fun_prop))
  have hfirst : (∫ t in (0 : ℝ)..(3 / 5), t ^ 3 * polarKernel m α η t ^ s) ≤
      ∫ t in (0 : ℝ)..(3 / 5), t ^ 3 * (1 - ((1 - b) / (3 / 5)) * t) ^ s := by
    refine intervalIntegral.integral_mono_on (by norm_num)
      ((continuous_cube_mul_polarKernel_rpow m α η hs.le).intervalIntegrable _ _)
      (hcont.intervalIntegrable _ _) ?_
    intro t ht
    apply mul_le_mul_of_nonneg_left _ (pow_nonneg ht.1 3)
    exact Real.rpow_le_rpow
      (polarKernel_nonneg hm.le hα hη ⟨ht.1, by linarith [ht.2]⟩)
      (polarKernel_le_first_chord hm hαm ht) hs.le
  have hrest : 0 ≤ ∫ t in (3 / 5 : ℝ)..(3 / 5) / (1 - b),
      t ^ 3 * (1 - ((1 - b) / (3 / 5)) * t) ^ s := by
    refine intervalIntegral.integral_nonneg hz ?_
    intro t ht
    have htz : ((1 - b) / (3 / 5)) * t ≤ 1 := by
      have ht' := (le_div_iff₀ (show 0 < 1 - b by dsimp [b]; linarith [hb.2])).mp ht.2
      nlinarith
    exact mul_nonneg (pow_nonneg (by linarith [ht.1]) 3)
      (Real.rpow_nonneg (sub_nonneg.mpr htz) s)
  have hadd := intervalIntegral.integral_add_adjacent_intervals (μ := volume)
    (hcont.intervalIntegrable 0 (3 / 5))
    (hcont.intervalIntegrable (3 / 5) ((3 / 5) / (1 - b)))
  rw [integral_first_chord_to_zero hb.2 hs] at hadd
  linarith

/-- The left endpoint's exact rational weight on the second interval. -/
lemma integral_second_chord_left_weight :
    (∫ t in (3 / 5 : ℝ)..1, t ^ 3 * ((1 - t) / (1 - 3 / 5))) = 259 / 3125 := by
  have heq : (fun t : ℝ => t ^ 3 * ((1 - t) / (1 - 3 / 5))) =
      fun t : ℝ => (5 / 2) * (t ^ 3 - t ^ 4) := by funext t; ring
  rw [heq, intervalIntegral.integral_const_mul,
    intervalIntegral.integral_sub
      ((continuous_pow 3).intervalIntegrable _ _) ((continuous_pow 4).intervalIntegrable _ _),
    integral_pow, integral_pow]
  norm_num

/-- The right endpoint's exact rational weight on the second interval. -/
lemma integral_second_chord_right_weight :
    (∫ t in (3 / 5 : ℝ)..1, t ^ 3 * ((t - 3 / 5) / (1 - 3 / 5))) = 421 / 3125 := by
  have heq : (fun t : ℝ => t ^ 3 * ((t - 3 / 5) / (1 - 3 / 5))) =
      fun t : ℝ => (5 / 2) * t ^ 4 - (3 / 2) * t ^ 3 := by funext t; ring
  rw [heq, intervalIntegral.integral_sub
      (((continuous_pow 4).const_mul (5 / 2)).intervalIntegrable _ _)
      (((continuous_pow 3).const_mul (3 / 2)).intervalIntegrable _ _),
    intervalIntegral.integral_const_mul, intervalIntegral.integral_const_mul,
    integral_pow, integral_pow]
  norm_num

/-- Integral of the separated endpoint powers. -/
lemma integral_second_chord_powers (b η s : ℝ) :
    (∫ t in (3 / 5 : ℝ)..1, t ^ 3 *
      ((1 - t) / (1 - 3 / 5) * b ^ s + (t - 3 / 5) / (1 - 3 / 5) * η ^ s)) =
      (259 / 3125) * b ^ s + (421 / 3125) * η ^ s := by
  have heq : (fun t : ℝ => t ^ 3 *
      ((1 - t) / (1 - 3 / 5) * b ^ s + (t - 3 / 5) / (1 - 3 / 5) * η ^ s)) =
      fun t : ℝ => (t ^ 3 * ((1 - t) / (1 - 3 / 5))) * b ^ s +
        (t ^ 3 * ((t - 3 / 5) / (1 - 3 / 5))) * η ^ s := by funext t; ring
  rw [heq, intervalIntegral.integral_add
      ((by fun_prop : Continuous (fun t : ℝ =>
        (t ^ 3 * ((1 - t) / (1 - 3 / 5))) * b ^ s)).intervalIntegrable _ _)
      ((by fun_prop : Continuous (fun t : ℝ =>
        (t ^ 3 * ((t - 3 / 5) / (1 - 3 / 5))) * η ^ s)).intervalIntegrable _ _),
    intervalIntegral.integral_mul_const, intervalIntegral.integral_mul_const,
    integral_second_chord_left_weight, integral_second_chord_right_weight]

/-- The second integral is bounded by its two endpoint powers. -/
lemma integral_polarKernel_second_chord {m α η s : ℝ} (hm : 0 < m)
    (hα : 0 ≤ α) (hαm : 2 * α ≤ m) (hη : 0 ≤ η) (hs : 1 ≤ s) :
    (∫ t in (3 / 5 : ℝ)..1, t ^ 3 * polarKernel m α η t ^ s) ≤
      (259 / 3125) * polarKernel m α η (3 / 5) ^ s + (421 / 3125) * η ^ s := by
  rw [← integral_second_chord_powers]
  refine intervalIntegral.integral_mono_on (by norm_num)
    ((continuous_cube_mul_polarKernel_rpow m α η (by linarith)).intervalIntegrable _ _)
    ((by fun_prop : Continuous (fun t : ℝ => t ^ 3 *
      ((1 - t) / (1 - 3 / 5) * polarKernel m α η (3 / 5) ^ s +
        (t - 3 / 5) / (1 - 3 / 5) * η ^ s))).intervalIntegrable _ _) ?_
  intro t ht
  exact mul_le_mul_of_nonneg_left (polarKernel_rpow_le_second_chord hm hα hαm hη hs ht)
    (pow_nonneg (by linarith [ht.1]) 3)

/-- Two-chord bound for any real exponent at least one. Integrability is automatic. -/
theorem integral_polarKernel_two_chord_rpow {m α η s : ℝ} (hm : 0 < m)
    (hα : 0 ≤ α) (hαm : 2 * α ≤ m) (hη : 0 ≤ η) (hη1 : η < 1) (hs : 1 ≤ s) :
    (∫ t in (0 : ℝ)..1, t ^ 3 * polarKernel m α η t ^ s) ≤
      6 * (3 / 5) ^ 4 /
        ((s + 1) * (s + 2) * (s + 3) * (s + 4) * (1 - polarKernel m α η (3 / 5)) ^ 4) +
      (259 / 3125) * polarKernel m α η (3 / 5) ^ s + (421 / 3125) * η ^ s := by
  have hcont := continuous_cube_mul_polarKernel_rpow m α η (show 0 ≤ s by linarith)
  rw [← intervalIntegral.integral_add_adjacent_intervals
    (hcont.intervalIntegrable 0 (3 / 5)) (hcont.intervalIntegrable (3 / 5) 1)]
  have hfirst := integral_polarKernel_first_chord hm hα hαm hη hη1 (show 0 < s by linarith)
  have hsecond := integral_polarKernel_second_chord hm hα hαm hη hs
  linarith

/-- The paper's two-chord estimate with real degree, arbitrary admissible eta, and all endpoints. -/
theorem integral_polarKernel_two_chord {m α η : ℝ} (hm : 5 ≤ m)
    (hα : 0 ≤ α) (hαm : 2 * α ≤ m) (hη : 0 ≤ η) (hη1 : η < 1) :
    (∫ t in (0 : ℝ)..1, t ^ 3 * polarKernel m α η t ^ ((m - 3) / 2)) ≤
      96 * (3 / 5) ^ 4 /
        ((m - 1) * (m + 1) * (m + 3) * (m + 5) * (1 - polarKernel m α η (3 / 5)) ^ 4) +
      (259 / 3125) * polarKernel m α η (3 / 5) ^ ((m - 3) / 2) +
      (421 / 3125) * η ^ ((m - 3) / 2) := by
  have h := integral_polarKernel_two_chord_rpow (by linarith : 0 < m) hα hαm hη hη1
    (by linarith : 1 ≤ (m - 3) / 2)
  have heq : ((m - 3) / 2 + 1) * ((m - 3) / 2 + 2) * ((m - 3) / 2 + 3) *
      ((m - 3) / 2 + 4) * (1 - polarKernel m α η (3 / 5)) ^ 4 =
      ((m - 1) * (m + 1) * (m + 3) * (m + 5) *
        (1 - polarKernel m α η (3 / 5)) ^ 4) / 16 := by ring
  rw [heq, div_div_eq_mul_div] at h
  convert h using 1; ring

end Sendov
