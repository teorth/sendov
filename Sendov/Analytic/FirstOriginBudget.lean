import Sendov.Analytic.FirstOriginSmall
import Sendov.Analytic.PaperNear
import Sendov.Analytic.PaperUniform

/-! Generic first-origin consumers of the scalar D estimates.
No second-origin or polynomial centroid identity is used in these proofs. -/
namespace Sendov.FirstOriginBudget

lemma beta_eq_QQ (a x t : ℝ) : PaperTaylor.beta a x t = QQ (a * x) (a ^ 2) t := by
  unfold PaperTaylor.beta QQ
  ring

/-- First-origin forces the opposite of D, in the closed pointwise disk domain. -/
theorem lower_budget {n : ℕ} (hn : 2 ≤ n) {a x y : ℝ} {q : Multiset ℂ}
    (ha : 0 < a) (ha1 : a < 1) (hx1 : x ≤ 1)
    (hqcard : q.card = n - 1) (hq1 : ∀ v ∈ q, ‖v‖ ≤ 1)
    (hx : (q.map (fun v => v.re)).sum = ((n : ℝ) - 1) * x)
    (hsum : q.sum = ((n : ℂ) - 1) * ((x : ℂ) + (y : ℂ) * Complex.I))
    (hfirst : ‖∫ t in (0 : ℝ)..1, Fprod a q t‖ ≤ 1 / (n : ℝ)) :
    1 ≤ PaperTaylor.budget ((n : ℝ) - 1) a x + a * ((n : ℝ) - 1) / (n : ℝ) := by
  have hnR : (2 : ℝ) ≤ n := by exact_mod_cast hn
  have hm0 : 0 ≤ (n : ℝ) - 1 := by linarith
  have hc : (q.card : ℝ) = (n : ℝ) - 1 := by
    rw [hqcard, Nat.cast_sub (by omega : 1 ≤ n)]
    norm_num
  have hq0 : q ≠ 0 := by
    intro h
    simp [h] at hqcard
    omega
  have hsumle := FirstOriginSmall.norm_sum_le_card q hq1
  rw [hc] at hsumle
  have ht := one_le_tri hn hqcard hq0 hq1 ha.le hx hsum
  have hβ : 0 ≤ QQ (a * x) (a ^ 2) 1 := by
    rw [← beta_eq_QQ]
    exact (PaperTaylor.beta_pos ha ha1 hx1 (by norm_num)).le
  have hf := FirstOriginSmall.norm_Fprod_le hn hqcard hq1 hx hβ
  have hcoef : ((n : ℂ) - 1) * (a : ℂ) * ((x : ℂ) + (y : ℂ) * Complex.I) =
      (a : ℂ) * q.sum := by rw [hsum]; ring
  rw [hcoef] at ht
  have hi : ‖(a : ℂ) * q.sum * (∫ t in (0 : ℝ)..1, Fprod a q t)‖ ≤
      a * ((n : ℝ) - 1) / (n : ℝ) := by
    rw [norm_mul, norm_mul, Complex.norm_real, Real.norm_eq_abs, abs_of_pos ha]
    have hmul := mul_le_mul (mul_le_mul_of_nonneg_left hsumle ha.le) hfirst
      (norm_nonneg _) (by positivity : 0 ≤ a * ((n : ℝ) - 1))
    simpa only [mul_one_div] using hmul
  have htri := norm_add_le (Fprod a q 1)
    ((a : ℂ) * q.sum * (∫ t in (0 : ℝ)..1, Fprod a q t))
  have hexp : (n : ℝ) - 1 - 1 = (n : ℝ) - 2 := by ring
  simp only [PaperTaylor.budget, beta_eq_QQ, hexp]
  nlinarith only [ht, hf, hi, htri]

/-- The near-endpoint raw-polar theorem is consumed without an analytic assumption. -/
theorem near_contradiction {n : ℕ} (hn : 8 ≤ n) {a x y : ℝ} {q : Multiset ℂ}
    (ha : 0 < a) (ha1 : a < 1) (hx0 : -1 ≤ x) (hx1 : x ≤ 1)
    (hqcard : q.card = n - 1) (hq1 : ∀ v ∈ q, ‖v‖ ≤ 1)
    (hx : (q.map (fun v => v.re)).sum = ((n : ℝ) - 1) * x)
    (hsum : q.sum = ((n : ℂ) - 1) * ((x : ℂ) + (y : ℂ) * Complex.I))
    (hraw : 1 ≤ ∫ t in (0 : ℝ)..1, Ppolar a x t ^ (((n : ℝ) - 1) / 2))
    (hnear : ((n : ℝ) - 1) * (1 - a) ≤ 2 / 5)
    (hfirst : ‖∫ t in (0 : ℝ)..1, Fprod a q t‖ ≤ 1 / (n : ℝ)) : False := by
  have hm : 7 ≤ n - 1 := by omega
  have hcast : ((n - 1 : ℕ) : ℝ) = (n : ℝ) - 1 := by
    rw [Nat.cast_sub (by omega : 1 ≤ n)]
    norm_num
  have hr : PaperPolar.RawPolar (n - 1) a x := by
    rw [PaperPolar.rawPolar_iff, hcast]
    exact hraw
  have hd := PaperNearClosure.near_endpoint_D hm ha ha1 hx0 hx1 hr
    (by simpa only [hcast] using hnear)
  have hl := lower_budget (by omega) ha ha1 hx1 hqcard hq1 hx hsum hfirst
  rw [hcast] at hd
  have he : (n : ℝ) - 1 + 1 = n := by ring
  rw [he] at hd
  have hh : 0 < (1 - a) / 1000 := by positivity
  rw [mul_comm a ((n : ℝ) - 1)] at hl
  linarith

/-- All degrees n≥257 close using only polar and the first-origin bound. -/
theorem uniform_contradiction {n : ℕ} (hn : 257 ≤ n) {a x y : ℝ} {q : Multiset ℂ}
    (ha : 0 < a) (ha1 : a < 1) (hx0 : -1 ≤ x) (hx1 : x ≤ 1)
    (hqcard : q.card = n - 1) (hq1 : ∀ v ∈ q, ‖v‖ ≤ 1)
    (hx : (q.map (fun v => v.re)).sum = ((n : ℝ) - 1) * x)
    (hsum : q.sum = ((n : ℂ) - 1) * ((x : ℂ) + (y : ℂ) * Complex.I))
    (hraw : 1 ≤ ∫ t in (0 : ℝ)..1, Ppolar a x t ^ (((n : ℝ) - 1) / 2))
    (hfirst : ‖∫ t in (0 : ℝ)..1, Fprod a q t‖ ≤ 1 / (n : ℝ)) : False := by
  have hm : 256 ≤ n - 1 := by omega
  have hcast : ((n - 1 : ℕ) : ℝ) = (n : ℝ) - 1 := by
    rw [Nat.cast_sub (by omega : 1 ≤ n)]
    norm_num
  have hr : PaperPolar.RawPolar (n - 1) a x := by
    rw [PaperPolar.rawPolar_iff, hcast]
    exact hraw
  have hd := PaperUniform.uniform_D hm ha ha1 hx0 hx1 hr
  have hl := lower_budget (by omega) ha ha1 hx1 hqcard hq1 hx hsum hfirst
  rw [hcast] at hd
  have he : (n : ℝ) - 1 + 1 = n := by ring
  rw [he] at hd
  rw [mul_comm a ((n : ℝ) - 1)] at hl
  linarith

end Sendov.FirstOriginBudget
