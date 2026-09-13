import Sendov.Common.DistillationCriticalFinite
import Sendov.Common.DistillationHyperbolic
import Sendov.Common.DistillationBounds

open Sendov

example {s c : ℝ} (hs : 0 < s) (hc : 0 < c) :
    (∫ t in (0 : ℝ)..1 / c, t * (1 - c * t) ^ s) =
      1 / (c ^ 2 * ((s + 1) * (s + 2))) :=
  integral_chord_lin hs hc

example {s c : ℝ} (hs : 0 < s) (hc : 0 < c) :
    (∫ t in (0 : ℝ)..1 / c, t ^ 3 * (1 - c * t) ^ s) =
      6 / (c ^ 4 * ((s + 1) * (s + 2) * (s + 3) * (s + 4))) :=
  integral_chord_pow hs hc

-- The split covers a vertex at one and a vertex beyond the integration interval.
example {r : ℝ} (hr : 0 < r) (k : ℕ) :
    (∫ t in (0 : ℝ)..1, t ^ k * QQ 1 1 t ^ r) ≤
      (∫ t in (0 : ℝ)..1, t ^ k * (1 - t) ^ r) + QQ 1 1 1 ^ r / (k + 1) := by
  simpa only [div_one, one_mul] using
    integral_le_tail_gen (c := 1) (A := 1) (by norm_num) (by norm_num) (by norm_num) hr k

example {r : ℝ} (hr : 0 < r) (k : ℕ) :
    (∫ t in (0 : ℝ)..1, t ^ k * QQ (1 / 2) (1 / 4) t ^ r) ≤
      (∫ t in (0 : ℝ)..2, t ^ k * (1 - (1 / 2) * t) ^ r) +
        QQ (1 / 2) (1 / 4) 1 ^ r / (k + 1) := by
  convert integral_le_tail_gen (c := 1 / 2) (A := 1 / 4)
    (by norm_num) (by norm_num) (by norm_num) hr k using 1
  norm_num

example {c A l r : ℝ} (hA : 0 ≤ A) (hlr : l < r) :
    QQ c A l ≤ ((r - l) * QQ c A l + (l - l) * QQ c A r) / (r - l) :=
  QQ_le_secant hA hlr ⟨le_rfl, hlr.le⟩

example : 0 ≤ cubicPolarEnvelope 0 := cubicPolarEnvelope_nonneg le_rfl

example {α : ℝ} (hα : 0 ≤ α) : cubicPolarEnvelope α ≤ α / (α + 3) :=
  cubicPolarEnvelope_le_linear hα

example {m : ℝ} (hm : 5 ≤ m) :
    ContinuousWithinAt (distillT0 m) (Set.Icc 0 (m / 2)) 0 :=
  distillT0_continuousOn hm 0 ⟨le_rfl, by linarith⟩

example {m : ℝ} (hm : 5 ≤ m) :
    ContinuousWithinAt (distillT2 m) (Set.Icc 0 (m / 2)) (m / 2) :=
  distillT2_continuousOn hm (m / 2) ⟨by linarith, le_rfl⟩

example {m α : ℝ} (hm : 5 ≤ m) (hα : 0 < α) (hαm : 2 * α < m) :
    deriv (distillT0 m) α ≤ 0 ↔ distillCritical0 m α ≤ 0 :=
  distillT0_deriv_nonpos_iff hm hα hαm

example {m α : ℝ} (hm : 5 ≤ m) (hα : 0 < α) (hαm : 2 * α < m) :
    deriv (distillT1 m) α ≤ 0 ↔ 0 ≤ distillCritical1 m α :=
  distillT1_deriv_nonpos_iff hm hα hαm

example {m α : ℝ} (hm : 5 ≤ m) (hα : 0 < α) (hαm : 2 * α < m) :
    deriv (distillT2 m) α ≤ 0 ↔ 0 ≤ distillCritical2 m α :=
  distillT2_deriv_nonpos_iff hm hα hαm

-- Neither square recovery nor the zero-base case requires a nonnegative coefficient.
example {a c : ℝ} (hc : 0 ≤ c) (hsq : a ^ 2 ≤ c ^ 2) :
    a * (0 : ℝ) ^ (((3 : ℝ) - 3) / 2) ≤ c := by
  apply distillMulRpow_le_of_sq 0 (by norm_num) hc (by norm_num)
  simpa only [pow_zero, mul_one] using hsq

example {a c : ℝ} (hc : 0 ≤ c) :
    a * (0 : ℝ) ^ (((4 : ℝ) - 3) / 2) ≤ c := by
  apply distillMulRpow_le_of_sq 1 (by norm_num) hc (by norm_num)
  simpa only [pow_one, mul_zero] using sq_nonneg c

example {f : ℝ → ℝ} {b : ℝ} (hc : ContinuousOn f (Set.Icc 0 0))
    (hb : f 0 ≤ b) : f 0 ≤ b := by
  apply distillPeak_le (l := 0) (r := 0) (d := 0) le_rfl le_rfl le_rfl hc
  · simp
  · simp
  · simp
  · simpa using hb
  · exact ⟨le_rfl, le_rfl⟩

example {m α : ℝ} (hm : 5 ≤ m) (hα : 0 < α) (hαm : 2 * α ≤ m) :
    scalarObstruction m α (cubicPolarEnvelope α) ≤
      distillEBudget m + distillT0 m α + distillT1 m α + distillT2 m α :=
  distillScalar_le_majorant hm hα hαm

example : Filter.Tendsto (fun z => Real.sinh z / z)
    (nhdsWithin 0 {(0 : ℝ)}ᶜ) (nhds 1) := by
  simpa [slope_fun_def, div_eq_inv_mul] using (Real.hasDerivAt_sinh 0).tendsto_slope

example : Real.sinh 0 ≤ 0 * Real.exp
    ((7 / 8 : ℝ) * (Real.sqrt (9 + (8 / 7 : ℝ) * 0 ^ 2) - 3)) :=
  DistillationHyperbolic.sinh_le_mul_exp le_rfl (by norm_num)

example : Real.log (Real.sinh 10 / 10) ≤
    (7 / 8 : ℝ) * (Real.sqrt (9 + (8 / 7 : ℝ) * 10 ^ 2) - 3) :=
  DistillationHyperbolic.log_sinh_div_le (by norm_num) le_rfl

example {m : ℝ} (hm : 61 ≤ m) : distillT2 m 0 = 0 := distillT2_zero hm

example {m : ℝ} (hm : 61 ≤ m) :
    distillEBudget m + distillT0 m 0 + distillT1 m 0 + distillT2 m 0 ≤
      distillEBudget 61 + distillT0 61 0 + distillT1 61 0 + distillT2 61 0 :=
  distillComponents_le_61 hm le_rfl (by norm_num)

example {m : ℝ} (hm : 61 ≤ m) :
    scalarObstruction m 17 (cubicPolarEnvelope 17) < 199 / 200 :=
  distillScalar_lt_199_200 hm (by norm_num) le_rfl

example {n : ℕ} (hn : 6 ≤ n) {α : ℝ} (hα : 0 < α) (h17 : α ≤ 17)
    (hhalf : 2 * α ≤ M n) :
    scalarObstruction (M n) α (cubicPolarEnvelope α) < 1 :=
  distillScalar_lt_one hn hα h17 hhalf
