import Sendov.Reduction.CubicScalar
import Sendov.Common.DistillationCriticalFinite

open Sendov Real

example {n : ℕ} {a x α : ℝ} (hn : 5 ≤ n)
    (ha : 0 < a) (ha1 : a < 1) (hx : x ^ 2 ≤ 1)
    (hα : α = M n * (1 - a ^ 2) / 2)
    (hbeta : QQ (a * x) (a ^ 2) 1 ≤ α / (3 + α))
    (hlogb : log α ≤ α * (1 - QQ (a * x) (a ^ 2) 1))
    (horigin : 2 * α + a * x ≤ (1 - x ^ 2) / (2 * M n)
      + a ^ 2 * n * M n * ∫ t in (0 : ℝ)..1,
        t * QQ (a * x) (a ^ 2) t ^ (((n : ℝ) - 2) / 2)) :
    α ≤ 17 :=
  alpha_le_seventeen hn ha ha1 hx hα hbeta hlogb horigin

example {n : ℕ} (hn : 6 ≤ n) {a x α : ℝ}
    (ha : 0 < a) (ha1 : a < 1) (hx : x ^ 2 ≤ 1)
    (hα : α = M n * (1 - a ^ 2) / 2)
    (hpolar : 1 ≤ ∫ t in (0 : ℝ)..1, Ppolar a x t ^ (((n : ℝ) - 1) / 2))
    (horigin : 2 * α + a * x ≤ (1 - x ^ 2) / (2 * M n)
      + a ^ 2 * n * M n * ∫ t in (0 : ℝ)..1,
        t * QQ (a * x) (a ^ 2) t ^ (((n : ℝ) - 2) / 2)) :
    (0 < α) ∧ (2 * α ≤ M n) ∧ (α ≤ 17) ∧
      (1 ≤ scalarObstruction (M n) α (cubicPolarEnvelope α)) :=
  cubicScalar_constraints_of_polar_origin hn ha ha1 hx hα hpolar horigin

example : (0 : ℝ) * (2 * (0 + 1) + 1 / 17) * exp (-(2.83 * 0)) ≤ 0.4118 :=
  tail_poly_bound le_rfl

-- Bernoulli's interface still permits a negative Q and a zero P.
example {p : ℝ} (hp : 1 ≤ p) :
    (2 + (-1) : ℝ) ^ p ≤ (2 : ℝ) ^ p + p * (-1) * (2 + (-1) : ℝ) ^ (p - 1) :=
  rpow_add_le_of_one_le (by norm_num) (by norm_num) hp

example {Q p : ℝ} (hQ : 0 < Q) (hp : 1 ≤ p) :
    (0 + Q) ^ p ≤ (0 : ℝ) ^ p + p * Q * (0 + Q) ^ (p - 1) :=
  rpow_add_le_of_one_le le_rfl (by simpa using hQ) hp

-- All three identities are symbolic polynomial equalities, not evaluations.
example (m α : ℝ) :
    distillCritical0 m α = distillK m α * distillD m α +
      4 * (m - 2 * α) * distillN α * distillRp m α :=
  distillCritical0_eq m α

example (m α : ℝ) :
    distillCritical1 m α = -2 * distillK m α * distillB m α -
      (m - 3) * (m - 2 * α) * distillN α * distillRp m α :=
  distillCritical1_eq m α

example (m α : ℝ) :
    distillCritical2 m α = -2 * α * distillK m α -
      (m - 3) * (m - 2 * α) * distillL α :=
  distillCritical2_eq m α

example (α : ℝ) : distillN α = 29 * α ^ 2 + 180 * α + 270 := rfl

example (x : ℝ) :
    DistillationHyperbolic.A x =
      x ^ 8 + 1430 * x ^ 6 + 289575 * x ^ 4 + 16081065 * x ^ 2 + 218243025 := rfl

example (x : ℝ) :
    DistillationHyperbolic.D x =
      55 * x ^ 8 + 25740 * x ^ 6 + 2837835 * x ^ 4 + 91891800 * x ^ 2 + 654729075 := rfl

example {m : ℝ} (hm : 0 < m) :
    distillD m 0 = 50 * m * (0 + 3) ^ 3 * (1 - distillNode m 0) :=
  distillD_eq hm le_rfl

example {m α : ℝ} (hm : 0 < m) (hα : 0 ≤ α) :
    distillD m α = 50 * m * (α + 3) ^ 3 * (1 - distillNode m α) :=
  distillD_eq hm hα

example {m : ℝ} (hm : 0 < m) :
    HasDerivAt (distillKappa m)
      (distillKappa m 0 * (distillK m 0 / ((0 + 3) * (m - 2 * 0) * distillN 0))) 0 :=
  hasDerivAt_distillKappa le_rfl (by simpa using hm)

example {m α : ℝ} (hm : 5 ≤ m) (hα : 0 < α) (hαm : 2 * α < m) :
    HasDerivAt (distillT0 m)
      (distillT0 m α * (distillCritical0 m α /
        ((α + 3) * (m - 2 * α) * distillN α * distillD m α))) α :=
  hasDerivAt_distillT0 hm hα hαm

example {m α : ℝ} (hm : 5 ≤ m) (hα : 0 < α) (hαm : 2 * α < m) :
    HasDerivAt (distillT1 m)
      (distillT1 m α * (-distillCritical1 m α /
        (2 * (α + 3) * (m - 2 * α) * distillN α * distillB m α))) α :=
  hasDerivAt_distillT1 hm hα hαm

example {m α : ℝ} (hm : 5 ≤ m) (hα : 0 < α) (hαm : 2 * α < m) :
    HasDerivAt (distillT2 m)
      (distillT2 m α * (-distillCritical2 m α /
        (2 * α * (α + 3) * (m - 2 * α) * distillN α))) α :=
  hasDerivAt_distillT2 hm hα hαm

example {m α : ℝ} (hm : 5 ≤ m) (hα : 0 < α) (hαm : 2 * α < m) :
    (deriv (distillT0 m) α ≤ 0 ↔ distillCritical0 m α ≤ 0) ∧
      (deriv (distillT1 m) α ≤ 0 ↔ 0 ≤ distillCritical1 m α) ∧
      (deriv (distillT2 m) α ≤ 0 ↔ 0 ≤ distillCritical2 m α) :=
  ⟨distillT0_deriv_nonpos_iff hm hα hαm, distillT1_deriv_nonpos_iff hm hα hαm,
    distillT2_deriv_nonpos_iff hm hα hαm⟩

example {m : ℝ} (hm : 5 ≤ m) :
    ContinuousWithinAt (distillT0 m) (Set.Icc 0 (m / 2)) 0 :=
  distillT0_continuousOn hm 0 ⟨le_rfl, by linarith⟩

example {m : ℝ} (hm : 5 ≤ m) :
    ContinuousWithinAt (distillT1 m) (Set.Icc 0 (m / 2)) 0 :=
  distillT1_continuousOn hm 0 ⟨le_rfl, by linarith⟩

example {m : ℝ} (hm : 5 ≤ m) :
    ContinuousWithinAt (distillT2 m) (Set.Icc 0 (m / 2)) (m / 2) :=
  distillT2_continuousOn hm (m / 2) ⟨by linarith, le_rfl⟩

example {x : ℝ} (hx : 0 ≤ x) :
    0 ≤ x ^ 2 * DistillationHyperbolic.A x * sinh x -
      DistillationHyperbolic.D x * (x * cosh x - sinh x) :=
  DistillationHyperbolic.pade_nonneg hx

example {x : ℝ} (hx : 0 ≤ x) (hx10 : x ≤ 10) :
    sqrt (9 + (8 / 7 : ℝ) * x ^ 2) * (x * cosh x - sinh x) ≤ x ^ 2 * sinh x :=
  DistillationHyperbolic.sqrt_mul_sub_le hx hx10

example : sinh 0 ≤ 0 * exp ((7 / 8 : ℝ) * (sqrt (9 + (8 / 7 : ℝ) * 0 ^ 2) - 3)) :=
  DistillationHyperbolic.sinh_le_mul_exp le_rfl (by norm_num)

example : log (sinh 10 / 10) ≤ (7 / 8 : ℝ) * (sqrt (9 + (8 / 7 : ℝ) * 10 ^ 2) - 3) :=
  DistillationHyperbolic.log_sinh_div_le (by norm_num) le_rfl

example {h : ℝ} (hh : 0 ≤ h) (hh10 : h ≤ 10) :
    sinh h ≤ h * exp ((7 / 8 : ℝ) * (sqrt (9 + (8 / 7 : ℝ) * h ^ 2) - 3)) :=
  DistillationHyperbolic.sinh_le_mul_exp hh hh10

-- Direct consumer of the original n >= 5 interface, without a polar premise.
example {n : ℕ} {a x α : ℝ} (hn : 5 ≤ n) (ha : 0 < a) (ha1 : a < 1) (hx : x ^ 2 ≤ 1)
    (hα : α = M n * (1 - a ^ 2) / 2) (hα0 : 0 < α)
    (hB1lt : QQ (a * x) (a ^ 2) 1 < 1)
    (horigin : 2 * α + a * x ≤ (1 - x ^ 2) / (2 * M n)
      + a ^ 2 * n * M n * ∫ t in (0 : ℝ)..1, t * QQ (a * x) (a ^ 2) t ^ (((n : ℝ) - 2) / 2)) :
    1 ≤ QQ (a * x) (a ^ 2) 1 / (2 * α * (1 - QQ (a * x) (a ^ 2) 1))
      + QQ (a * x) (a ^ 2) 1 / (4 * α)
      + 1 / (2 * M n)
      + QQ (a * x) (a ^ 2) 1 / (4 * α * M n)
      + (a ^ 2) ^ 2 * n * M n * ((n : ℝ) - 2) * QQ (a * x) (a ^ 2) 1 / (4 * α)
        * ∫ t in (0 : ℝ)..1, t ^ 3 * QQ (a * x) (a ^ 2) t ^ (((n : ℝ) - 4) / 2) :=
  one_le_of_origin hn ha ha1 hx hα hα0 hB1lt horigin
