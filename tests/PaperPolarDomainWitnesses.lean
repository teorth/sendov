import Sendov.Analytic.PaperPolar
import Mathlib.Analysis.SpecialFunctions.Integrals.Basic
import Mathlib.Algebra.Polynomial.Derivative
import Mathlib.Algebra.Polynomial.FieldDivision
import Mathlib.Analysis.Convex.Hull

/-!
# Literal full-polar witnesses and domain countermodels (DI15–17)

The neighborhood assertions concern every real parameter in the indicated
closed intervals, not a grid and not a raw-feasibility hypothesis.
The last example refutes a convex-hull **nonroot** reciprocal-moment variant;
it does not refute the marked-root theorem, Sendov, or the nearest-point bound.
-/
namespace Sendov.PaperPolar.DomainWitnesses
open MeasureTheory
open scoped BigOperators

noncomputable def K {m : ℕ} (a : ℝ) (q : Fin m → ℂ) : ℂ :=
  ∫ t in (0 : ℝ)..1, ∏ j : Fin m, ((a : ℂ) + ((1 - a ^ 2) * t : ℝ) * q j)

lemma integral_affine_pow (m : ℕ) (a d : ℝ) (hd : d ≠ 0) :
    (∫ t in (0 : ℝ)..1, (a + d * t) ^ m) =
      ((a + d) ^ (m + 1) - a ^ (m + 1)) / (((m : ℝ) + 1) * d) := by
  rw [intervalIntegral.integral_comp_add_mul (fun y : ℝ => y ^ m) hd, integral_pow]
  simp only [mul_zero, add_zero, mul_one, smul_eq_mul]
  rw [mul_comm ((m : ℝ) + 1), ← div_div]
  ring

lemma K_one (m : ℕ) (a : ℝ) :
    K a (fun _ : Fin m => 1) =
      ((∫ t in (0 : ℝ)..1, (a + (1 - a ^ 2) * t) ^ m : ℝ) : ℂ) := by
  unfold K
  simp only [mul_one, Finset.prod_const, Finset.card_univ, Fintype.card_fin]
  simp_rw [← Complex.ofReal_add, ← Complex.ofReal_pow]
  rw [intervalIntegral.integral_ofReal]

lemma norm_K_one_lower (m : ℕ) {a l d : ℝ}
    (hl : 0 ≤ l) (hla : l ≤ a) (hd : 0 ≤ d) (hda : d ≤ 1 - a ^ 2) :
    (∫ t in (0 : ℝ)..1, (l + d * t) ^ m) ≤ ‖K a (fun _ : Fin m => 1)‖ := by
  rw [K_one, Complex.norm_real, Real.norm_eq_abs]
  apply le_trans _ (le_abs_self _)
  refine intervalIntegral.integral_mono_on (by norm_num)
    ((by fun_prop : Continuous fun t : ℝ => (l + d * t) ^ m).intervalIntegrable _ _)
    ((by fun_prop : Continuous fun t : ℝ => (a + (1 - a ^ 2) * t) ^ m).intervalIntegrable _ _) ?_
  intro t ht
  exact pow_le_pow_left₀ (add_nonneg hl (mul_nonneg hd ht.1))
    (add_le_add hla (mul_le_mul_of_nonneg_right hda ht.1)) m

/-- DI15: actual complex full polar throughout the degree-seven neighborhood. -/
theorem neighborhood_7 {a : ℝ}
    (ha : a ∈ Set.Icc (7999 / 10000) (8001 / 10000)) :
    (∀ _j : Fin 7, ‖(1 : ℂ)‖ = 1) ∧ 1 ≤ ‖K a (fun _ : Fin 7 => 1)‖ := by
  constructor
  · intro j; exact norm_one
  · have hd : (3598 : ℝ) / 10000 ≤ 1 - a ^ 2 := by
      have := ha.1; have := ha.2; nlinarith
    have h := norm_K_one_lower 7 (by norm_num : (0 : ℝ) ≤ 7999 / 10000)
      ha.1 (by norm_num : (0 : ℝ) ≤ 3598 / 10000) hd
    rw [integral_affine_pow 7 _ _ (by norm_num)] at h
    exact le_trans (by norm_num) h

noncomputable def x : ℝ := 93 / 100
noncomputable def y : ℝ := Real.sqrt (1 - x ^ 2)
noncomputable def plus : ℂ := ⟨x, y⟩
noncomputable def minus : ℂ := ⟨x, -y⟩
/-- Exactly five conjugate pairs. -/
noncomputable def q10 (j : Fin 10) : ℂ := if j.val % 2 = 0 then plus else minus

lemma y_sq : y ^ 2 = 1 - x ^ 2 := Real.sq_sqrt (by norm_num [x])

lemma norm_plus : ‖plus‖ = 1 := by
  have h : ‖plus‖ ^ 2 = 1 := by
    rw [Complex.sq_norm, Complex.normSq_apply]
    change x * x + y * y = 1
    nlinarith [y_sq]
  nlinarith [norm_nonneg plus]

lemma norm_minus : ‖minus‖ = 1 := by
  have h : ‖minus‖ ^ 2 = 1 := by
    rw [Complex.sq_norm, Complex.normSq_apply]
    change x * x + (-y) * (-y) = 1
    nlinarith [y_sq]
  nlinarith [norm_nonneg minus]

theorem norm_q10 (j : Fin 10) : ‖q10 j‖ = 1 := by
  unfold q10
  split <;> first | exact norm_plus | exact norm_minus

theorem mean_q10 : (∑ j : Fin 10, q10 j) / 10 = (x : ℂ) := by
  norm_num [q10, Fin.sum_univ_succ]
  apply Complex.ext <;> simp [plus, minus]
  ring

lemma pair_product (s r : ℝ) :
    ((s : ℂ) + r * plus) * (s + r * minus) =
      ((s ^ 2 + 2 * s * r * x + r ^ 2 : ℝ) : ℂ) := by
  apply Complex.ext <;>
    simp only [plus, minus, pow_two, Complex.mul_re, Complex.mul_im, Complex.add_re,
      Complex.add_im, Complex.ofReal_re, Complex.ofReal_im, Complex.ofReal_add,
      Complex.ofReal_mul, Complex.ofReal_ofNat, Complex.re_ofNat, Complex.im_ofNat,
      zero_mul, mul_zero, sub_zero, add_zero, zero_add]
  · have h := congrArg (fun z : ℝ => r ^ 2 * z) y_sq
    nlinarith only [h]
  · ring

lemma product_q10 (a t : ℝ) :
    (∏ j : Fin 10, ((a : ℂ) + ((1 - a ^ 2) * t : ℝ) * q10 j)) =
      (((a ^ 2 + 2 * a * (1 - a ^ 2) * x * t +
        (1 - a ^ 2) ^ 2 * t ^ 2) ^ 5 : ℝ) : ℂ) := by
  have hp := pair_product a ((1 - a ^ 2) * t)
  norm_num [q10, Fin.prod_univ_succ]
  calc
    _ = (((a : ℂ) + ((1 - a ^ 2) * t : ℝ) * plus) *
        ((a : ℂ) + ((1 - a ^ 2) * t : ℝ) * minus)) ^ 5 := by push_cast; ring
    _ = _ := by rw [hp]; push_cast; ring

noncomputable def fifthCoeffs (A B C : ℝ) : Fin 11 → ℝ :=
  ![A^5, 5*A^4*B, 10*A^3*B^2+5*A^4*C,
    10*A^2*B^3+20*A^3*B*C, 5*A*B^4+30*A^2*B^2*C+10*A^3*C^2,
    B^5+20*A*B^3*C+30*A^2*B*C^2,
    5*B^4*C+30*A*B^2*C^2+10*A^2*C^3,
    10*B^3*C^2+20*A*B*C^3, 10*B^2*C^3+5*A*C^4, 5*B*C^4, C^5]

lemma fifth_expansion (A B C t : ℝ) :
    (A + B * t + C * t ^ 2) ^ 5 =
      ∑ k : Fin 11, fifthCoeffs A B C k * t ^ k.val := by
  simp [fifthCoeffs, Fin.sum_univ_succ]
  ring

lemma integral_fifth (A B C : ℝ) :
    (∫ t in (0 : ℝ)..1, (A + B * t + C * t ^ 2) ^ 5) =
      ∑ k : Fin 11, fifthCoeffs A B C k / (k.val + 1) := by
  simp_rw [fifth_expansion]
  rw [intervalIntegral.integral_finsetSum]
  · apply Finset.sum_congr rfl
    intro k hk
    rw [intervalIntegral.integral_const_mul, integral_pow]
    simp
    ring
  · intro k hk
    exact ((continuous_const.mul (continuous_pow k.val))).intervalIntegrable _ _

lemma K_q10 (a : ℝ) : K a q10 =
    ((∫ t in (0 : ℝ)..1,
      (a ^ 2 + 2 * a * (1 - a ^ 2) * x * t + (1 - a ^ 2) ^ 2 * t ^ 2) ^ 5 : ℝ) : ℂ) := by
  unfold K
  simp_rw [product_q10]
  rw [intervalIntegral.integral_ofReal]

/-- DI15: no raw-polar hypothesis is used for the five-pair neighborhood. -/
theorem neighborhood_10 {a : ℝ}
    (ha : a ∈ Set.Icc (899999 / 1000000) (900001 / 1000000)) :
    (∀ j, ‖q10 j‖ = 1) ∧ 1 ≤ ‖K a q10‖ := by
  refine ⟨norm_q10, ?_⟩
  let l : ℝ := 89999 / 100000
  let d : ℝ := 18999 / 100000
  have hl : 0 ≤ l := by norm_num [l]
  have hd : 0 ≤ d := by norm_num [d]
  have hla : l ≤ a := by have := ha.1; dsimp [l]; linarith
  have hda : d ≤ 1 - a ^ 2 := by
    have := ha.1; have := ha.2; dsimp [d]; nlinarith
  have ha0 := hl.trans hla
  have hdelta := hd.trans hda
  have hA := pow_le_pow_left₀ hl hla 2
  have hB : 2 * l * d * x ≤ 2 * a * (1 - a ^ 2) * x := by
    exact mul_le_mul_of_nonneg_right
      (mul_le_mul (mul_le_mul_of_nonneg_left hla (by norm_num)) hda hd (by positivity))
      (by norm_num [x])
  have hC := pow_le_pow_left₀ hd hda 2
  have hi : (∫ t in (0 : ℝ)..1, (l ^ 2 + (2*l*d*x) * t + d ^ 2 * t ^ 2) ^ 5) ≤
      ∫ t in (0 : ℝ)..1,
        (a ^ 2 + 2*a*(1-a^2)*x*t + (1-a^2)^2*t^2)^5 := by
    refine intervalIntegral.integral_mono_on (by norm_num)
      ((by fun_prop : Continuous fun t : ℝ => (l^2+(2*l*d*x)*t+d^2*t^2)^5).intervalIntegrable _ _)
      ((by fun_prop : Continuous fun t : ℝ =>
        (a^2+2*a*(1-a^2)*x*t+(1-a^2)^2*t^2)^5).intervalIntegrable _ _) ?_
    intro t ht
    apply pow_le_pow_left₀
    · have hx : 0 ≤ x := by norm_num [x]
      have ht0 := ht.1
      positivity
    · exact add_le_add (add_le_add hA (mul_le_mul_of_nonneg_right hB ht.1))
        (mul_le_mul_of_nonneg_right hC (sq_nonneg t))
  have hlo : 1 ≤ ∫ t in (0 : ℝ)..1, (l ^ 2 + (2*l*d*x) * t + d ^ 2 * t ^ 2) ^ 5 := by
    rw [integral_fifth]
    norm_num [fifthCoeffs, Fin.sum_univ_succ, l, d, x]
  rw [K_q10, Complex.norm_real, Real.norm_eq_abs]
  exact (hlo.trans hi).trans (le_abs_self _)

/-- DI16: the literal all-ones complex integral, evaluated exactly. -/
theorem K_64_exact : K (1/2) (fun _ : Fin 64 => 1) =
    ((((5/4 : ℝ)^65 - (1/2 : ℝ)^65) / (65 * (3/4 : ℝ)) : ℝ) : ℂ) := by
  rw [K_one, integral_affine_pow 64 _ _ (by norm_num)]
  norm_num

theorem domain_64 : alpha 64 (1/2) = 24 ∧ 17 < alpha 64 (1/2) ∧
    (∀ _j : Fin 64, ‖(1 : ℂ)‖ = 1) ∧ 1 < ‖K (1/2) (fun _ : Fin 64 => 1)‖ := by
  refine ⟨by norm_num [alpha], by norm_num [alpha], fun _ => norm_one, ?_⟩
  rw [K_64_exact, Complex.norm_real, Real.norm_eq_abs]
  norm_num

/-- Full polar and the unit-disc pointwise bound alone do not imply alpha ≤ 17. -/
theorem not_polar_implies_alpha17 :
    ¬ (∀ (m : ℕ) (a : ℝ) (q : Fin m → ℂ), 7 ≤ m → 0 < a → a < 1 →
      (∀ j, ‖q j‖ ≤ 1) → 1 ≤ ‖K a q‖ → alpha m a ≤ 17) := by
  intro h
  have hh := h 64 (1/2) (fun _ => 1) (by norm_num) (by norm_num) (by norm_num)
    (fun j => (domain_64.2.2.1 j).le) domain_64.2.2.2.le
  exact (not_le_of_gt domain_64.2.1) hh

namespace Nonroot
open Polynomial

/-- A genuine degree-ten complex polynomial with two collinear unit roots. -/
noncomputable def p : ℂ[X] := (X - C 1)^9 * (X + C 1)
noncomputable def marked : ℂ := ((-1/4 : ℝ) : ℂ)

lemma derivative_eq : p.derivative = (X - C 1)^8 * (C 10 * X + C 8) := by
  simp [p, derivative_mul, derivative_pow, map_ofNat]
  ring

lemma linear_ne_zero : (C (10 : ℂ) * X + C 8 : ℂ[X]) ≠ 0 := by
  intro h
  have hh := congrArg (Polynomial.eval (0 : ℂ)) h
  norm_num at hh

/-- The complete critical multiset, including all eight repeated critical points. -/
theorem critical_roots : p.derivative.roots =
    8 • ({1} : Multiset ℂ) + {(-4/5 : ℂ)} := by
  rw [derivative_eq, roots_mul (mul_ne_zero (pow_ne_zero 8 (X_sub_C_ne_zero 1)) linear_ne_zero),
    roots_pow, roots_X_sub_C, roots_C_mul_X_add_C _ (by norm_num)]
  norm_num

theorem critical_multiplicities : p.derivative.rootMultiplicity 1 = 8 ∧
    p.derivative.rootMultiplicity (-4/5) = 1 ∧ p.derivative.roots.card = 9 := by
  rw [← count_roots, ← count_roots, critical_roots]
  norm_num

theorem root_multiset : p.roots = 9 • ({1} : Multiset ℂ) + {-1} := by
  have hn : (X + C (1 : ℂ) : ℂ[X]) ≠ 0 := by
    simpa only [C_neg, sub_neg_eq_add] using X_sub_C_ne_zero (-1 : ℂ)
  rw [p, roots_mul (mul_ne_zero (pow_ne_zero 9 (X_sub_C_ne_zero 1)) hn),
    roots_pow, roots_X_sub_C, roots_X_add_C]

lemma mem_roots_iff (z : ℂ) : z ∈ p.roots ↔ z = 1 ∨ z = -1 := by
  rw [root_multiset]
  simp

/-- The marked point is in the actual root convex hull, but is not a root. -/
theorem convex_hull_nonroot :
    marked ∈ convexHull ℝ {z : ℂ | z ∈ p.roots} ∧ ¬ p.IsRoot marked := by
  constructor
  · have hs : {z : ℂ | z ∈ p.roots} = {1, -1} := by
      ext z
      simp only [Set.mem_ofPred_eq, Set.mem_insert_iff, Set.mem_singleton_iff, mem_roots_iff]
    rw [hs, convexHull_pair]
    refine ⟨3/8, 5/8, by norm_num, by norm_num, by norm_num, ?_⟩
    apply Complex.ext <;> norm_num [marked, Complex.smul_re, Complex.smul_im]
  · norm_num [Polynomial.IsRoot, p, marked]

lemma distance_one : ‖marked - (1 : ℂ)‖ = 5/4 := by
  have he : marked - (1 : ℂ) = ((-5/4 : ℝ) : ℂ) := by
    dsimp [marked]; push_cast; ring
  rw [he, Complex.norm_real, Real.norm_eq_abs]
  norm_num

lemma distance_other : ‖marked - (-4/5 : ℂ)‖ = 11/20 := by
  have he : marked - (-4/5 : ℂ) = ((11/20 : ℝ) : ℂ) := by
    dsimp [marked]; push_cast; ring
  rw [he, Complex.norm_real, Real.norm_eq_abs]
  norm_num

/-- DI17: the reciprocal-square sum is over the actual derivative roots. -/
theorem reciprocal_square_exact :
    (p.derivative.roots.map (fun w => 1 / ‖marked - w‖ ^ 2)).sum = 25488/3025 := by
  rw [critical_roots]
  simp only [Multiset.map_add, Multiset.map_nsmul, Multiset.map_singleton,
    Multiset.sum_add, Multiset.sum_nsmul, Multiset.sum_singleton, distance_one, distance_other]
  norm_num

theorem reciprocal_square_lt_nine :
    (p.derivative.roots.map (fun w => 1 / ‖marked - w‖ ^ 2)).sum < 9 := by
  rw [reciprocal_square_exact]
  norm_num

/-- Exact minimum, expressed by a lower bound and an attained value. -/
theorem nearest_critical_distance :
    (∀ w ∈ p.derivative.roots, (11 : ℝ)/20 ≤ ‖marked - w‖) ∧
    (∃ w ∈ p.derivative.roots, ‖marked - w‖ = 11/20) ∧ (11 : ℝ)/20 < 1 := by
  constructor
  · intro w hw
    rw [critical_roots] at hw
    have hh : w = 1 ∨ w = -4/5 := by simpa using hw
    rcases hh with rfl | rfl
    · rw [distance_one]; norm_num
    · exact distance_other.ge
  · refine ⟨⟨-4/5, ?_, distance_other⟩, by norm_num⟩
    rw [critical_roots]
    simp

/-- All actual roots lie on the unit circle and in the real line. -/
theorem root_geometry : ∀ z ∈ p.roots, ‖z‖ = 1 ∧ z.im = 0 := by
  intro z hz
  rcases (mem_roots_iff z).mp hz with rfl | rfl <;> simp

/-- Only the NONroot convex-hull variant is refuted, not the marked-root theorem. -/
theorem not_convex_hull_nonroot_moment :
    ¬ (∀ (f : ℂ[X]) (a : ℂ), (∀ z ∈ f.roots, ‖z‖ = 1 ∧ z.im = 0) →
      a ∈ convexHull ℝ {z : ℂ | z ∈ f.roots} → ¬ f.IsRoot a →
      (f.derivative.roots.card : ℝ) ≤
        (f.derivative.roots.map (fun w => 1 / ‖a - w‖ ^ 2)).sum) := by
  intro h
  have hh := h p marked root_geometry convex_hull_nonroot.1 convex_hull_nonroot.2
  rw [critical_multiplicities.2.2] at hh
  norm_num only [Nat.cast_ofNat] at hh
  exact (not_le_of_gt reciprocal_square_lt_nine) hh

#print axioms derivative_eq
#print axioms critical_roots
#print axioms critical_multiplicities
#print axioms convex_hull_nonroot
#print axioms reciprocal_square_exact
#print axioms nearest_critical_distance
#print axioms not_convex_hull_nonroot_moment
end Nonroot

#print axioms neighborhood_7
#print axioms neighborhood_10
#print axioms domain_64
#print axioms not_polar_implies_alpha17
end Sendov.PaperPolar.DomainWitnesses
