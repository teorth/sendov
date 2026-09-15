import Sendov
import Solution

open Sendov Real

-- Cancellation must remain valid at alpha = 0; no division by alpha is justified.
example {n : ℕ} (hn : 2 ≤ n) (x t : ℝ) :
    polarKernel (M n) 0 (QQ x 1 1) t = QQ x 1 t := by
  simpa using polarKernel_actual (a := 1) (x := x) (α := 0) hn (by simp) t

example {n : ℕ} (hn : 2 ≤ n) (x : ℝ) :
    scalarObstruction (M n) 0 (QQ x 1 1) = 1 / (2 * M n) := by
  simpa using scalarObstruction_actual_eq (a := 1) (x := x) (α := 0) hn (by simp)

-- The opposite feasibility endpoint has a zero origin coefficient.
example {n : ℕ} (hn : 2 ≤ n) (t : ℝ) :
    polarKernel (M n) (M n / 2) 1 t = 1 := by
  simpa [QQ] using polarKernel_actual (a := 0) (x := 0) (α := M n / 2) hn (by simp) t

-- The chord bound covers both signs of x without a sign case split.
example {a : ℝ} (ha : 0 < a) (ha1 : a < 1) :
    0 < 1 - a * (-1) * 1 ∧ 0 < 1 - a * 1 * 1 := by
  constructor
  · exact one_sub_mul_pos ha ha1 (by norm_num) (by norm_num) le_rfl
  · exact one_sub_mul_pos ha ha1 (by norm_num) (by norm_num) le_rfl

example (a x : ℝ) :
    Ppolar a x 0 ≤ 1 + (1 - a ^ 2) * (-1 + (2 - QQ (a * x) (a ^ 2) 1) * 0) :=
  Ppolar_le_lin a x le_rfl (by norm_num)

example (a x : ℝ) :
    Ppolar a x 1 ≤ 1 + (1 - a ^ 2) * (-1 + (2 - QQ (a * x) (a ^ 2) 1) * 1) :=
  Ppolar_le_lin a x (by norm_num) le_rfl

-- Bernoulli's public interface does not require Q to be nonnegative.
example {p : ℝ} (hp : 1 ≤ p) :
    (2 + (-1) : ℝ) ^ p ≤ (2 : ℝ) ^ p + p * (-1) * (2 + (-1) : ℝ) ^ (p - 1) :=
  rpow_add_le_of_one_le (by norm_num) (by norm_num) hp

example : exp (-1) ≤ 1 / (1 - (-1)) :=
  exp_le_one_div_one_sub (by norm_num)

example : exp 0 ≤ 1 / (1 - 0) :=
  exp_le_one_div_one_sub (by norm_num)

example : scalarObstruction 5 17 0 ≤ scalarObstruction 5 17 (99 / 100) :=
  scalarObstruction_mono_eta (by norm_num) (by norm_num)
    (by norm_num) (by norm_num) (by norm_num)

example : (17 : ℝ) * (1 - cubicPolarEnvelope 17 / 2) < 10 :=
  cubicPolarEnvelope_center_lt_ten (by norm_num) le_rfl

example {α : ℝ} (hα : 0 < α)
    (h : 1 ≤ ∫ t in (0 : ℝ)..1, exp (α * (-1 + (2 - 2) * t))) : False :=
  (lt_irrefl (2 : ℝ)) (beta_lt_two hα h)

open Lean in
run_elab do
  let names : List Name := [
    `Sendov.M, `Sendov.A,
    `Sendov.Ppolar, `Sendov.Ppolar_eq, `Sendov.Ppolar_nonneg,
    `Sendov.continuous_Ppolar, `Sendov.A_eq_sq, `Sendov.mul_eq_c,
    `Sendov.alpha_pos, `Sendov.alpha_le_half,
    `Sendov.Ppolar_le_lin, `Sendov.Ppolar_rpow_le, `Sendov.polar_exp,
    `Sendov.integral_exp_mul, `Sendov.integral_exp_eq', `Sendov.integral_exp_eq,
    `Sendov.beta_lt_two, `Sendov.beta_le, `Sendov.log_le_alpha_mul,
    `Sendov.rpow_add_le_of_one_le, `Sendov.one_sub_mul_pos, `Sendov.beta_split,
    `Sendov.integral_beta_split, `Sendov.one_le_of_origin,
    `Sendov.integral_polarKernel_nonneg, `Sendov.scalarObstruction_prefactor_nonneg,
    `Sendov.scalarObstruction_mono_eta, `Sendov.polarKernel_actual,
    `Sendov.scalarObstruction_actual_eq, `Sendov.one_le_scalarObstruction_of_one_le,
    `Sendov.one_le_scalarObstruction_of_origin, `Sendov.actualEta_mem_Ico_of_polar,
    `Sendov.one_le_scalarObstruction_of_polar_origin,
    `Sendov.quartic_le_exp, `Sendov.log_le_div_exp_one, `Sendov.exp_le_one_div_one_sub,
    `Sendov.log_seventeen_ge, `Sendov.tail_poly_bound, `Sendov.alpha_le_seventeen,
    `Sendov.cubicPolarEnvelope_center_lt_ten, `Sendov.cubicPolarEnvelope_quadratic_pos,
    `Sendov.polar_le_log_sinh, `Sendov.eta_lt_cubicPolarEnvelope,
    `Sendov.actualEta_lt_cubicPolarEnvelope_of_polar,
    `Sendov.cubicScalar_constraints_of_polar_origin, `Sendov.polar_origin_incompatible,
    `Sendov.sendov_interior, `Sendov.sendov_center, `Sendov.sendov_interior_real,
    `Sendov.rotate, `Sendov.eval_rotate, `Sendov.natDegree_rotate,
    `Sendov.derivative_rotate, `Sendov.eval_derivative_rotate, `Sendov.rotate_rotate_inv,
    `Sendov.roots_rotate, `Sendov.phelps_rodriguez, `Sendov.sendov,
    `SendovConjecture.sendov, `SendovConjecture.phelps_rodriguez]
  for name in names do
    let info ← getConstInfo name
    logInfo m!"TYPE {name}: {repr info.type}"
  for name in [`Sendov.M, `Sendov.A, `SendovConjecture.sendov,
      `SendovConjecture.phelps_rodriguez] do
    let info ← getConstInfo name
    logInfo m!"VALUE {name}: {repr (info.value?)}"
