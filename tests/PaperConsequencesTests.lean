import Sendov.Analytic.PaperConsequences

open Polynomial Filter
open Sendov Sendov.PaperConsequences

-- AS03: smallest allowed degree, then arbitrary fixed degree and all means.
example : Tendsto (PaperSecant.U1 1) (nhdsWithin 0 (Set.Ioi 0)) (nhds (1 / 2 : ℝ)) := by
  simpa only [Nat.cast_one, show (1 : ℝ) + 1 = 2 by norm_num] using tendsto_U1_zero_right 1

example : PaperSecant.U1 1 0 < 1 := by
  rw [U1_zero]
  norm_num

example (m : ℕ) (hm : 1 ≤ m) :
    ∃ ε > (0 : ℝ), ∀ a : ℝ, 0 < a → a < ε →
      ∀ x : ℝ, -1 ≤ x → x ≤ 1 → ¬ PaperPolar.RawPolar m a x :=
  exists_small_radius_not_rawPolar hm

-- Degree zero must not accidentally be excluded by the fixed-degree statement.
example : PaperSecant.U1 0 0 = 1 := by norm_num [U1_zero]

-- EX03: an actual polynomial, with the extra root-distance hypothesis at equality.
-- p=X(X-2), a=0, q={-1}; this separate theorem needs no unit-disk root hypothesis.
example {r : ℝ} (hr : 0 < r) :
    (1 : ℝ) ≤ (({-1} : Multiset ℂ).map (fun v => ‖v‖ ^ r)).sum := by
  have h := moment_ge_degree_of_root_distance_product
    (m := 1) (p := X * (X - C 2)) (c := 1) (a := 0)
    (q := {-1}) (z := {2}) (by omega) (by simp) (by simp)
    (by norm_num) (by simp) (by simp) (by
      norm_num [derivative_mul, derivative_sub, derivative_X, derivative_C, map_ofNat]
      ring) (by norm_num) hr
  simpa only [Nat.cast_one] using h

-- AM-GM permits every positive real exponent, not only natural powers or r≥1.
example (q : Multiset ℂ) (hp : 1 ≤ ‖q.prod‖) :
    (q.card : ℝ) ≤ (q.map (fun v => ‖v‖ ^ (1 / 2 : ℝ))).sum :=
  moment_ge_card_of_one_le_norm_prod q (by norm_num) hp

-- EX01/02: actual complex mean/variance, and the still-conditional finite majorant.
example (q : Multiset ℂ) {μ : ℂ} {a x : ℝ}
    (hm : 7 ≤ q.card) (ha : 0 < a) (ha1 : a < 1)
    (hmean : q.sum = q.card * μ) (hq : ∀ v ∈ q, ‖v‖ ≤ 1)
    (hx0 : -1 ≤ x) (hx1 : x ≤ 1) (hx : μ.re = x)
    (hr : PaperPolar.RawPolar q.card a x) :
    PaperCentered.Gamma (q.map (fun v => v - μ)) μ < 7 * (1 - a) / 18 :=
  Gamma_lt_seven_eighteenths q hm ha ha1 hmean hq hx0 hx1 hx hr

example (q : Multiset ℂ) {μ : ℂ} {a x : ℝ}
    (hm : 7 ≤ q.card) (ha : 0 < a) (ha1 : a < 1)
    (hmean : q.sum = q.card * μ) (hq : ∀ v ∈ q, ‖v‖ ≤ 1)
    (hx0 : -1 ≤ x) (hx1 : x ≤ 1) (hx : μ.re = x)
    (hr : PaperPolar.RawPolar q.card a x)
    (hfin : PaperCenteredBound.majorant_Efin (q.map (fun v => v - μ)) μ (a * μ) ≤
      (1 - a) / 2)
    (hJ : ‖(q.card + 1 : ℂ) *
      (∫ t in (0 : ℝ)..1, (q.map (fun v => 1 - (a : ℂ) * t * v)).prod)‖ ≤ 1) : False :=
  (not_lt_of_ge hJ) (norm_J_gt_one_of_majorant_half q hm ha ha1 hmean hq hx0 hx1 hx hr hfin)

-- AS05: arbitrary positive scale, and the endpoint x=1 is not discarded.
example {ℓ x : ℝ} (hℓ : 0 < ℓ) (hx0 : -1 ≤ x) (hx1 : x ≤ 1)
    (hG : 1 ≤ ∫ t in (0 : ℝ)..1, Real.exp (ℓ * (2 * x * t - 1))) :
    0 < (1 + ℓ) * x ^ 2 - 1 :=
  (limiting_exponential_model hℓ hx0 hx1 hG).2.2.2

example {ℓ : ℝ} (hℓ : 0 < ℓ)
    (hG : 1 ≤ ∫ t in (0 : ℝ)..1, Real.exp (ℓ * (2 * (1 : ℝ) * t - 1))) :
    0 < (1 + ℓ) * (1 : ℝ) ^ 2 - 1 :=
  (limiting_exponential_model hℓ (by norm_num) (by norm_num) hG).2.2.2

-- UN: all four retained historical cutoffs, with no extra radius restriction.
example {m : ℕ} {a x : ℝ} (hm : 512 ≤ m)
    (ha : 0 < a) (ha1 : a < 1) (hx0 : -1 ≤ x) (hx1 : x ≤ 1)
    (hr : PaperPolar.RawPolar m a x) :
    PaperTaylor.budget (m : ℝ) a x < 1 - (m : ℝ) * a / ((m : ℝ) + 1) :=
  old_all_a_cutoff (by norm_num : 256 ≤ 512) hm ha ha1 hx0 hx1 hr

example {m : ℕ} {a x : ℝ} (hm : 10000 ≤ m)
    (ha : 0 < a) (ha1 : a < 1) (hx0 : -1 ≤ x) (hx1 : x ≤ 1)
    (hr : PaperPolar.RawPolar m a x) :
    PaperTaylor.budget (m : ℝ) a x < 1 - (m : ℝ) * a / ((m : ℝ) + 1) :=
  old_all_a_cutoff (by norm_num : 256 ≤ 10000) hm ha ha1 hx0 hx1 hr

example {m : ℕ} {a x : ℝ} (hm : 100000 ≤ m)
    (ha : 0 < a) (ha1 : a < 1) (hx0 : -1 ≤ x) (hx1 : x ≤ 1)
    (hr : PaperPolar.RawPolar m a x) :
    PaperTaylor.budget (m : ℝ) a x < 1 - (m : ℝ) * a / ((m : ℝ) + 1) :=
  old_all_a_cutoff (by norm_num : 256 ≤ 100000) hm ha ha1 hx0 hx1 hr

example {m : ℕ} {a x : ℝ} (hm : 1000000 ≤ m)
    (ha : 0 < a) (ha1 : a < 1) (hx0 : -1 ≤ x) (hx1 : x ≤ 1)
    (hr : PaperPolar.RawPolar m a x) :
    PaperTaylor.budget (m : ℝ) a x < 1 - (m : ℝ) * a / ((m : ℝ) + 1) :=
  old_all_a_cutoff (by norm_num : 256 ≤ 1000000) hm ha ha1 hx0 hx1 hr

#print axioms tendsto_U1_zero_right
#print axioms exists_small_radius_not_rawPolar
#print axioms root_distance_product_identity
#print axioms moment_ge_degree_of_root_distance_product
#print axioms Gamma_lt_seven_eighteenths
#print axioms norm_J_gt_one_of_majorant_half
#print axioms limiting_exponential_model
#print axioms old_all_a_cutoff
