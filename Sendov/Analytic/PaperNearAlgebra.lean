import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Linarith
import Mathlib.Data.Real.Basic
import Mathlib.Tactic.Ring

/-! Rational algebra for round7, §§3 and 5. No polar or Taylor estimate is
asserted here: those are separate analytic inputs to the paper's gap argument. -/
namespace Sendov.PaperNear

noncomputable def A (τ : ℝ) : ℝ := 1 - 2 * τ / 5
noncomputable def C (τ : ℝ) : ℝ := 1 - 2 * τ
noncomputable def L (τ : ℝ) : ℝ := 1 + τ
noncomputable def H (τ : ℝ) : ℝ := 1 + 3 * τ
noncomputable def D (τ : ℝ) : ℝ := A τ * C τ * L τ * H τ
noncomputable def F (τ : ℝ) : ℝ :=
  A τ * C τ * H τ - (5 / 17 : ℝ) * L τ * H τ -
    (2312 / 3375 : ℝ) * A τ * C τ - D τ / 80
noncomputable def G (τ : ℝ) : ℝ :=
  1 / L τ - 5 / (17 * A τ * C τ) -
    (2312 / 3375 : ℝ) / (L τ * H τ) - 1 / 80

/-- The exact degree-four Bernstein certificate, with the paper's numerators. -/
theorem quartic_bernstein (u : ℝ) :
    F (u / 7) = (551821830 * (1-u)^4 +
      3025830066 * 4 * u * (1-u)^3 +
      3755012933 * 6 * u^2 * (1-u)^2 +
      2857448181 * 4 * u^3 * (1-u) + 450387360 * u^4) / 66123540000 := by
  unfold F D A C L H
  ring

/-- A uniform lower bound, not merely positivity at sampled points. -/
theorem quartic_lower (τ : ℝ) (hτ : 0 ≤ τ) (hτ7 : τ ≤ 1 / 7) :
    (450387360 / 66123540000 : ℝ) ≤ F τ := by
  have hu : 0 ≤ 7 * τ := by positivity
  have hv : 0 ≤ 1 - 7 * τ := by linarith
  have h0 : 0 ≤ (1 - 7 * τ)^4 := by positivity
  have h1 : 0 ≤ (7 * τ) * (1 - 7 * τ)^3 := by positivity
  have h2 : 0 ≤ (7 * τ)^2 * (1 - 7 * τ)^2 := by positivity
  have h3 : 0 ≤ (7 * τ)^3 * (1 - 7 * τ) := by positivity
  have hid : F τ - 450387360 / 66123540000 =
      (101434470 * (1-7*τ)^4 + 10301770824 * (7*τ) * (1-7*τ)^3 +
       19827753438 * (7*τ)^2 * (1-7*τ)^2 +
       9628243284 * (7*τ)^3 * (1-7*τ)) / 66123540000 := by
    unfold F D A C L H
    ring
  have hp : 0 ≤ (101434470 * (1-7*τ)^4 +
      10301770824 * (7*τ) * (1-7*τ)^3 +
      19827753438 * (7*τ)^2 * (1-7*τ)^2 +
      9628243284 * (7*τ)^3 * (1-7*τ)) / (66123540000 : ℝ) := by
    positivity
  linarith

theorem denominator_bounds (τ : ℝ) (hτ : 0 ≤ τ) (hτ7 : τ ≤ 1 / 7) :
    0 < D τ ∧ D τ ≤ 80 / 49 := by
  have ha : 0 < A τ := by unfold A; linarith
  have hc : 0 < C τ := by unfold C; linarith
  have hl : 0 < L τ := by unfold L; linarith
  have hh : 0 < H τ := by unfold H; linarith
  have ha1 : A τ ≤ 1 := by unfold A; linarith
  have hc1 : C τ ≤ 1 := by unfold C; linarith
  have hl8 : L τ ≤ 8 / 7 := by unfold L; linarith
  have hh10 : H τ ≤ 10 / 7 := by unfold H; linarith
  have hac : A τ * C τ ≤ 1 := by nlinarith
  have hlh : L τ * H τ ≤ 80 / 49 := by nlinarith
  constructor
  · unfold D; positivity
  · unfold D
    nlinarith [mul_pos ha hc, mul_pos hl hh,
      mul_nonneg (sub_nonneg.mpr hac) (mul_nonneg hl.le hh.le)]

theorem denominator_mul_G (τ : ℝ) (hτ : 0 ≤ τ) (hτ7 : τ ≤ 1 / 7) :
    D τ * G τ = F τ := by
  have ha : A τ ≠ 0 := by unfold A; linarith
  have hc : C τ ≠ 0 := by unfold C; linarith
  have hl : L τ ≠ 0 := by unfold L; linarith
  have hh : H τ ≠ 0 := by unfold H; linarith
  unfold G F D
  field_simp

/-- The paper's conservative positive margin, uniformly on the closed interval. -/
theorem G_lower (τ : ℝ) (hτ : 0 ≤ τ) (hτ7 : τ ≤ 1 / 7) :
    (312769 / 91838250 : ℝ) ≤ G τ := by
  obtain ⟨hd, hd2⟩ := denominator_bounds τ hτ hτ7
  have hf := quartic_lower τ hτ hτ7
  have he := denominator_mul_G τ hτ hτ7
  have hg : 0 ≤ G τ := by nlinarith
  nlinarith [mul_nonneg (show 0 ≤ 2 - D τ by linarith) hg]

theorem G_gt_one_thousandth (τ : ℝ) (hτ : 0 ≤ τ) (hτ7 : τ ≤ 1 / 7) :
    (1 / 1000 : ℝ) < G τ := by
  have := G_lower τ hτ hτ7
  norm_num at *
  linarith

noncomputable def P (τ ℓ : ℝ) : ℝ := (1 - ℓ * τ) * (1 - 2 * τ) * (3 + ℓ)
noncomputable def Q (τ : ℝ) : ℝ := (1 + τ) * (1 + 3 * τ)
noncomputable def f (τ ℓ : ℝ) : ℝ := 1 / P τ ℓ
noncomputable def g (τ ℓ : ℝ) : ℝ := (4 / 27 : ℝ) * ℓ * (3 + ℓ)^2 / Q τ

/-- Uniform denominator separation for the first rational error term. -/
theorem P_lower (τ ℓ : ℝ) (hτ : 0 ≤ τ) (hτ7 : τ ≤ 1 / 7)
    (hℓ : 0 ≤ ℓ) (hℓ2 : ℓ ≤ 2 / 5) : (99 / 49 : ℝ) ≤ P τ ℓ := by
  have hlt : ℓ * τ ≤ 2 / 35 := by nlinarith
  have ha : 33 / 35 ≤ 1 - ℓ * τ := by linarith
  have hc : 5 / 7 ≤ 1 - 2 * τ := by linarith
  have hac : (33 / 35 : ℝ) * (5 / 7) ≤ (1 - ℓ * τ) * (1 - 2 * τ) :=
    mul_le_mul ha hc (by norm_num) (by linarith)
  have hab : 0 ≤ (1 - ℓ * τ) * (1 - 2 * τ) := by positivity
  have hp := mul_le_mul_of_nonneg_left (show (3 : ℝ) ≤ 3 + ℓ by linarith) hab
  unfold P
  nlinarith

theorem Q_bounds (τ : ℝ) (hτ : 0 ≤ τ) (hτ7 : τ ≤ 1 / 7) :
    0 < Q τ ∧ Q τ ≤ 80 / 49 := by
  unfold Q
  constructor
  · positivity
  · nlinarith [sq_nonneg (τ - 1/7)]

/-- A finite-difference version of the paper's lower derivative bound for f.
It avoids differentiability hypotheses and includes the closed endpoints. -/
theorem f_difference_lower (τ x y : ℝ) (hτ : 0 ≤ τ) (hτ7 : τ ≤ 1 / 7)
    (hx : 0 ≤ x) (hxy : x ≤ y) (hy : y ≤ 2 / 5) :
    -(y-x) / 4 ≤ f τ y - f τ x := by
  have hy0 : 0 ≤ y := le_trans hx hxy
  have hx2 : x ≤ 2 / 5 := le_trans hxy hy
  have hpx := P_lower τ x hτ hτ7 hx hx2
  have hpy := P_lower τ y hτ hτ7 hy0 hy
  have hpx0 : P τ x ≠ 0 := by linarith
  have hpy0 : P τ y ≠ 0 := by linarith
  have hprod : 4 ≤ P τ x * P τ y := by nlinarith
  have htx : τ * x ≤ 2 / 35 := by nlinarith
  have hty : τ * y ≤ 2 / 35 := by nlinarith
  have hs0 : 0 ≤ 1 - 3*τ - τ*(x+y) := by nlinarith
  have hs1 : 1 - 3*τ - τ*(x+y) ≤ 1 := by nlinarith [mul_nonneg hτ (add_nonneg hx hy0)]
  have hc0 : 0 ≤ 1 - 2*τ := by linarith
  have hc1 : 1 - 2*τ ≤ 1 := by linarith
  have hcs : (1 - 2*τ) * (1 - 3*τ - τ*(x+y)) ≤ 1 := by nlinarith
  have hmul := mul_le_mul_of_nonneg_left hcs (sub_nonneg.mpr hxy)
  have hdiff : P τ y - P τ x ≤ y-x := by
    unfold P
    nlinarith only [hmul]
  have hid : (P τ x * P τ y) * (f τ y - f τ x) = P τ x - P τ y := by
    unfold f
    field_simp
  by_cases hsign : 0 ≤ f τ y - f τ x
  · linarith
  · have hn : 0 ≤ -(f τ y - f τ x) := by linarith
    have := mul_le_mul_of_nonneg_right hprod hn
    nlinarith

/-- A finite-difference version of ∂ℓ g ≥ 49/60. -/
theorem g_difference_lower (τ x y : ℝ) (hτ : 0 ≤ τ) (hτ7 : τ ≤ 1 / 7)
    (hx : 0 ≤ x) (hxy : x ≤ y) :
    (49 / 60 : ℝ) * (y-x) ≤ g τ y - g τ x := by
  have hy : 0 ≤ y := le_trans hx hxy
  obtain ⟨hq0, hq⟩ := Q_bounds τ hτ hτ7
  have hqn : Q τ ≠ 0 := ne_of_gt hq0
  have hid : Q τ * (g τ y - g τ x) =
      (4 / 27 : ℝ) * (y-x) * (9 + 6*(x+y) + x^2 + x*y + y^2) := by
    unfold g
    field_simp
    ring
  have hp : 0 ≤ (y-x) * (6*(x+y) + x^2 + x*y + y^2) := by positivity
  have hb : (4 / 3 : ℝ) * (y-x) ≤ Q τ * (g τ y - g τ x) := by
    nlinarith only [hid, hp]
  have hg0 : 0 ≤ g τ y - g τ x := by nlinarith
  have hm := mul_le_mul_of_nonneg_right hq hg0
  nlinarith

/-- Quantitative strict increase in ℓ on the entire near-endpoint rectangle. -/
theorem fg_difference_lower (τ x y : ℝ) (hτ : 0 ≤ τ) (hτ7 : τ ≤ 1 / 7)
    (hx : 0 ≤ x) (hxy : x ≤ y) (hy : y ≤ 2 / 5) :
    (17 / 30 : ℝ) * (y-x) ≤ (f τ y + g τ y) - (f τ x + g τ x) := by
  have hf := f_difference_lower τ x y hτ hτ7 hx hxy hy
  have hg := g_difference_lower τ x y hτ hτ7 hx hxy
  linarith

theorem fg_strictMonoOn (τ : ℝ) (hτ : 0 ≤ τ) (hτ7 : τ ≤ 1 / 7) :
    StrictMonoOn (fun ℓ => f τ ℓ + g τ ℓ) (Set.Icc 0 (2 / 5)) := by
  intro x hx y hy hxy
  have := fg_difference_lower τ x y hτ hτ7 hx.1 hxy.le hy.2
  linarith

theorem fg_le_endpoint (τ ℓ : ℝ) (hτ : 0 ≤ τ) (hτ7 : τ ≤ 1 / 7)
    (hℓ : 0 ≤ ℓ) (hℓ2 : ℓ ≤ 2 / 5) :
    f τ ℓ + g τ ℓ ≤ f τ (2 / 5) + g τ (2 / 5) := by
  have := fg_difference_lower τ ℓ (2/5) hτ hτ7 hℓ hℓ2 le_rfl
  linarith

/-- Strict positivity of the cleared quartic throughout the interval. -/
theorem quartic_pos (τ : ℝ) (hτ : 0 ≤ τ) (hτ7 : τ ≤ 1 / 7) : 0 < F τ := by
  have := quartic_lower τ hτ hτ7
  linarith

/-- Identifies the quartic consumer with the sum of the two endpoint errors. -/
theorem G_eq_endpoint (τ : ℝ) (hτ : 0 ≤ τ) (hτ7 : τ ≤ 1 / 7) :
    G τ = 1 / (1+τ) - (f τ (2/5) + g τ (2/5)) - 1/80 := by
  have ha : 1 - 2 * τ / 5 ≠ 0 := by linarith
  have hc : 1 - 2 * τ ≠ 0 := by linarith
  have hl : 1 + τ ≠ 0 := by linarith
  have hh : 1 + 3 * τ ≠ 0 := by linarith
  have ha' : 1 - (2 / 5 : ℝ) * τ ≠ 0 := by linarith
  unfold G f g P Q A C L H
  field_simp
  ring

/-- The full rational near-endpoint remainder, before analytic inputs are supplied. -/
theorem rational_remainder_gt (τ ℓ : ℝ) (hτ : 0 ≤ τ) (hτ7 : τ ≤ 1 / 7)
    (hℓ : 0 ≤ ℓ) (hℓ2 : ℓ ≤ 2 / 5) :
    (1 / 1000 : ℝ) < 1 / (1+τ) - (f τ ℓ + g τ ℓ) - 1/80 := by
  have hm := fg_le_endpoint τ ℓ hτ hτ7 hℓ hℓ2
  have hg := G_gt_one_thousandth τ hτ hτ7
  rw [G_eq_endpoint τ hτ hτ7] at hg
  linarith

end Sendov.PaperNear
