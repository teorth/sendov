import Sendov.Analytic.PaperCenteredEndpoint
import Sendov.Analytic.PaperCenteredCertificate

/-! Uniform scalar closure in the positive-variance small-lambda regime.
The analytic tail-to-scalar adapter is separate; no per-degree certificates. -/
noncomputable section
open scoped BigOperators
namespace Sendov.CenteredNearScalar

def rho : ℝ := 2 / 11

def tailScalar (M v : ℝ) : ℝ :=
  9 * Real.sqrt (v ^ 3 / (M * (M - 1) * (M - 2))) / (9 / 11 : ℝ) ^ 4

lemma rho_bounds : 0 < rho ∧ rho < 1 := by norm_num [rho]

/-- Rational polar turns a uniform lambda bound into a uniform endpoint radius. -/
theorem beta_le_rho_sq (m : ℕ) (hm : 7 ≤ m) (a x : ℝ)
    (ha0 : 0 < a) (ha1 : a < 1) (hx0 : -1 ≤ x) (hx1 : x ≤ 1)
    (hp : PaperPolar.RawPolar m a x) (hl : PaperPolar.lambda m a ≤ 4 / 39) :
    PaperPolar.b a x ≤ rho ^ 2 := by
  have hb := PaperPolar.endpoint_bounds hm ha0 ha1 hx0 hx1 hp
  have ht := PaperPolar.rational_mono (PaperPolar.lambda_pos (by omega) ha1).le hl
  exact (hb.1.trans hb.2).trans (by norm_num [rho] at *; exact ht)

/-- Exact scalar estimate for the cubic structural tail, uniform in real M≥7. -/
theorem tailScalar_le (M h v : ℝ) (hM : 7 ≤ M) (hh : 0 ≤ h)
    (hl : M * h ≤ 4 / 39) (hv0 : 0 ≤ v) (hv : v ≤ M * h / 3) :
    tailScalar M v ≤ 3 * h / 5 := by
  let D := M * (M - 1) * (M - 2)
  have hM0 : 0 < M := by linarith
  have hM1 : 0 < M - 1 := by linarith
  have hM2 : 0 < M - 2 := by linarith
  have hD0 : 0 < D := by dsimp [D]; positivity
  have hpoly : 30 * M ^ 3 ≤ 49 * D := by
    have hp := mul_nonneg (show 0 ≤ M by linarith)
      (mul_nonneg (show 0 ≤ M - 7 by linarith) (show 0 ≤ 19 * M - 14 by linarith))
    dsimp [D]
    nlinarith only [hp]
  have hsmall : h ≤ 4 / 273 := by
    have hp := mul_nonneg (show 0 ≤ M - 7 by linarith) hh
    nlinarith only [hl, hp]
  have hv3 := pow_le_pow_left₀ hv0 hv 3
  have hfirst : 81 * v ^ 3 ≤ 3 * M ^ 3 * h ^ 3 := by
    nlinarith only [hv3]
  have hsecond := mul_le_mul_of_nonneg_left hsmall
    (by positivity : 0 ≤ 3 * M ^ 3 * h ^ 2)
  have hthird := mul_le_mul_of_nonneg_right hpoly (sq_nonneg h)
  have hbase : 81 * v ^ 3 ≤ (14 / 195 : ℝ) * h ^ 2 * D := by
    nlinarith only [hfirst, hsecond, hthird]
  have hconstant : (14 / 195 : ℝ) ≤ (9 / 25 : ℝ) * (9 / 11 : ℝ) ^ 8 := by norm_num
  have hlast := mul_le_mul_of_nonneg_right hconstant (mul_nonneg (sq_nonneg h) hD0.le)
  have hcore : 81 * v ^ 3 ≤ (9 / 25 : ℝ) * (9 / 11 : ℝ) ^ 8 * h ^ 2 * D := by
    nlinarith only [hbase, hlast]
  have hs : Real.sqrt (v ^ 3 / D) ≤ (h / 15) * (9 / 11 : ℝ) ^ 4 := by
    apply (Real.sqrt_le_left (by positivity)).2
    apply (div_le_iff₀ hD0).2
    nlinarith only [hcore]
  unfold tailScalar
  change 9 * Real.sqrt (v ^ 3 / D) / (9 / 11 : ℝ) ^ 4 ≤ 3 * h / 5
  apply (div_le_iff₀ (by norm_num : 0 < (9 / 11 : ℝ) ^ 4)).2
  nlinarith only [hs]

/-- Scalar budget closure with explicit slack. The tail and endpoint hypotheses
are interfaces to independently derived estimates, not the C-near conclusion. -/
theorem budget_close (h Eend T G u a : ℝ) (hh : 0 < h) (ha : 0 ≤ a)
    (hu : u ≤ 1) (hhdef : h = 1 - a)
    (he : Eend ≤ h / 1000) (ht : T ≤ 3 * h / 5) (hg : G ≤ 7 * h / 18) :
    Eend + T + G < (99 / 100 : ℝ) * h ∧
      Eend + T + G < 1 - a * u := by
  have hs : Eend + T + G ≤ (8909 / 9000 : ℝ) * h := by linarith
  have hstrict : Eend + T + G < (99 / 100 : ℝ) * h := by linarith
  refine ⟨hstrict, ?_⟩
  have hu' := mul_le_mul_of_nonneg_left hu ha
  nlinarith only [hstrict, hu', hhdef, hh]

end Sendov.CenteredNearScalar
