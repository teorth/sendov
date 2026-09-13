import Sendov.Common.DistillationPeakRest

/-!
# Uniform same-alpha closure on `[2,17]`

The affine first-peak budget and its joint complementary budget sum to one.
There are no degree rows, finite degree intervals, or old asymptotic tails in
this proof. The raw consumer still requires the original legal domain `2 a ≤ m`.
-/

namespace Sendov

/-- A uniform inequality for the original rational peak, not just its endpoints. -/
theorem distillRationalPeak_lt_one {α : ℝ} (hα : 2 ≤ α) (h17 : α ≤ 17) :
    distillRationalPeak α < 1 := by
  have h1 := PeakClosure.peak1_lt_budget hα h17
  have hrest := PeakClosure.rest_lt_budget hα h17
  unfold distillRationalPeak
  linarith only [h1, hrest]

/-- The entire legal real-degree ray, uniformly in the closed alpha strip. -/
theorem distillScalar_lt_one_peak_strip {m α : ℝ} (hm : 5 ≤ m)
    (hα : 2 ≤ α) (h17 : α ≤ 17) (hαm : 2 * α ≤ m) :
    scalarObstruction m α (cubicPolarEnvelope α) < 1 :=
  (distillScalar_le_rationalPeak hm hα hαm).trans_lt (distillRationalPeak_lt_one hα h17)

end Sendov
