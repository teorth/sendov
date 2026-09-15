import Sendov.Analytic.CenteredThirdTail

noncomputable section
namespace Sendov.CenteredBand

/-- The polynomial integral used for an odd lower band endpoint L=2p+3. -/
def curvedIntegral (p : ℕ) (X : ℝ) : ℝ :=
  ∫ y in (0:ℝ)..1, y^3 * (1-2*X*y+y^2)^p

def gammaConstant (L X : ℝ) : ℝ := 1 / ((L-1)*X^2)
def budgetCoefficient (L X B tau : ℝ) : ℝ := tau + gammaConstant L X*(1+B)
def margin (L U X B tau : ℝ) : ℝ :=
  X-1/15-(U/3)*max 0 (budgetCoefficient L X B tau-1/2)

/-- Curvature improvement, with no division by the actual variance. -/
theorem mean_sqrt_variance (X u v : ℝ) (hX : 0 ≤ X) (hhalf : 1/2 ≤ X^2)
    (hXu : X ≤ u) (hv : 0 ≤ v) (hstat : u^2+v ≤ 1) :
    u*Real.sqrt v ≤ X*Real.sqrt (1-X^2) := by
  have hu : 0 ≤ u := hX.trans hXu
  have hsq : X^2 ≤ u^2 := pow_le_pow_left₀ hX hXu 2
  have hX1 : 0 ≤ 1-X^2 := by linarith
  have hmono := mul_nonneg (sub_nonneg.mpr hsq) (show 0 ≤ u^2+X^2-1 by linarith)
  have hvprod := mul_le_mul_of_nonneg_left hstat (sq_nonneg u)
  have he1 : (u*Real.sqrt v)^2 = u^2*v := by rw [mul_pow, Real.sq_sqrt hv]
  have he2 : (X*Real.sqrt (1-X^2))^2 = X^2*(1-X^2) := by
    rw [mul_pow, Real.sq_sqrt hX1]
  have hn : 0 ≤ X*Real.sqrt (1-X^2) := by positivity
  nlinarith only [hmono, hvprod, he1, he2, hn]

/-- Available budget for actual nonsaturated statistics, not a feasibility assumption. -/
theorem available_budget (a X u v : ℝ) (ha : a ≤ 1) (hu0 : 0 ≤ u)
    (hu1 : u ≤ 1) (hXu : X ≤ u) (hstat : u^2+v ≤ 1) :
    v/2 + X*(1-a) ≤ 1-a*u := by
  have ht := mul_le_mul_of_nonneg_right hXu (sub_nonneg.mpr ha)
  nlinarith [sq_nonneg (1-u)]

/-- Uniform gamma comparison across a continuous degree band. -/
theorem gamma_le (L m X u v : ℝ) (hL : 1 < L) (hLm : L ≤ m)
    (hX : 0 < X) (hXu : X ≤ u) (hv : 0 ≤ v) :
    v/((m-1)*u^2) ≤ gammaConstant L X*v := by
  have hu : 0 < u := hX.trans_le hXu
  have hsq : X^2 ≤ u^2 := pow_le_pow_left₀ hX.le hXu 2
  have hd : (L-1)*X^2 ≤ (m-1)*u^2 :=
    mul_le_mul (by linarith) hsq (sq_nonneg X) (by linarith)
  have h := div_le_div_of_nonneg_left hv (mul_pos (by linarith) (sq_pos_of_pos hX)) hd
  simpa [gammaConstant, div_eq_mul_inv, mul_comm] using h

/-- All tail, endpoint and gamma estimates are consumed without a final-budget premise. -/
theorem scalar_budget (L U m a X u v e0 Bactual B tail tau : ℝ)
    (hL : 1 < L) (hLm : L ≤ m) (ha : a ≤ 1) (hX : 0 < X)
    (hu1 : u ≤ 1) (hXu : X ≤ u) (hv : 0 ≤ v) (hstat : u^2+v ≤ 1)
    (hcap : v ≤ (U/3)*(1-a)) (he0 : e0 ≤ (1-a)/15)
    (hBa0 : 0 ≤ Bactual) (hB : Bactual ≤ B) (htail : tail ≤ tau*v) :
    e0 + v/((m-1)*u^2)*(1+Bactual) + tail ≤
      1-a*u-margin L U X B tau*(1-a) := by
  have hg := gamma_le L m X u v hL hLm hX hXu hv
  have hm1 : 0 ≤ m-1 := by linarith
  have hg0 : 0 ≤ v/((m-1)*u^2) := by positivity
  have hB0 : 0 ≤ 1+B := by linarith
  have hgb := (mul_le_mul_of_nonneg_left (show 1+Bactual ≤ 1+B by linarith) hg0).trans
    (mul_le_mul_of_nonneg_right hg hB0)
  have hbudget := available_budget a X u v ha (hX.le.trans hXu) hu1 hXu hstat
  let K := budgetCoefficient L X B tau
  have hsmall : e0 + v/((m-1)*u^2)*(1+Bactual) + tail ≤ (1-a)/15+K*v := by
    dsimp [K, budgetCoefficient]
    nlinarith only [he0, hgb, htail]
  have hmax := mul_le_mul_of_nonneg_right (le_max_right 0 (K-1/2)) hv
  have huse := mul_le_mul_of_nonneg_left hcap (le_max_left 0 (K-1/2))
  change e0 + v/((m-1)*u^2)*(1+Bactual) + tail ≤
    1-a*u-(X-1/15-(U/3)*max 0 (K-1/2))*(1-a)
  nlinarith only [hsmall, hbudget, hmax, huse]

/-- Finite-factor monotonicity, retaining the exact S_m instead of 9/4. -/
theorem weightSum_mono (m U : ℕ) (hm : 3 ≤ m) (hmU : m ≤ U) :
    CenteredThird.weightSum m ≤ CenteredThird.weightSum U := by
  have hm3 : (3:ℝ) ≤ m := by exact_mod_cast hm
  have hmU' : (m:ℝ) ≤ U := by exact_mod_cast hmU
  have h1 := div_le_div_of_nonneg_left (by norm_num : (0:ℝ) ≤ 2)
    (show 0 < (m:ℝ)-1 by linarith) (show (m:ℝ)-1 ≤ (U:ℝ)-1 by linarith)
  have hd : 2*(m:ℝ)*((m:ℝ)-1) ≤ 2*(U:ℝ)*((U:ℝ)-1) := by
    apply mul_le_mul (by linarith) (by linarith) (by linarith) (by positivity)
  have hmpos : 0 < (m:ℝ)-1 := by linarith
  have h2 := div_le_div_of_nonneg_left (by norm_num : (0:ℝ) ≤ 1)
    (show 0 < 2*(m:ℝ)*((m:ℝ)-1) by positivity) hd
  unfold CenteredThird.weightSum
  linarith

end Sendov.CenteredBand
