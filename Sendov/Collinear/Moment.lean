import Sendov.Collinear.Diameter
import Mathlib.Analysis.MeanInequalitiesPow

open Polynomial
open scoped BigOperators
namespace Collinear

/-- Uniform Jensen weights on occurrence indices, not on distinct values. -/
private theorem multiset_moment_bound (s : Multiset ℝ) (hs : 0 < s.card)
    (f : ℝ → ℝ) (hf : ∀ x ∈ s, 0 ≤ f x) (c : ℝ) (hc : 0 ≤ c)
    (hmean : (s.card : ℝ) * c ≤ (s.map f).sum) (r : ℝ) (hr : 1 ≤ r) :
    (s.card : ℝ) * c ^ r ≤ (s.map (fun x => f x ^ r)).sum := by
  classical
  have hcard : (0 : ℝ) < s.card := by exact_mod_cast hs
  have hj := Real.rpow_arith_mean_le_arith_mean_rpow
    (Finset.univ : Finset (Fin s.toList.length)) (fun _ => (s.card : ℝ)⁻¹)
    (fun i => f s.toList[i.val]) (fun _ _ => inv_nonneg.mpr hcard.le)
    (by simp [Multiset.length_toList, hcard.ne'])
    (fun i _ => hf _ (Multiset.mem_toList.mp (List.getElem_mem i.isLt))) hr
  simp only [← Finset.mul_sum, Fin.sum_univ_fun_getElem, Multiset.sum_map_toList] at hj
  rw [Fin.sum_univ_fun_getElem s.toList (fun x => f x ^ r), Multiset.sum_map_toList] at hj
  have hm : c ≤ (s.card : ℝ)⁻¹ * (s.map f).sum := by
    rw [← div_eq_inv_mul, le_div_iff₀ hcard]
    simpa [mul_comm] using hmean
  have hp := (Real.rpow_le_rpow hc hm (by linarith)).trans hj
  have h := mul_le_mul_of_nonneg_left hp hcard.le
  simpa only [← mul_assoc, mul_inv_cancel₀ hcard.ne', one_mul] using h

/-- All real exponents at least one, full derivative multiplicities.  The left
branch is essential: the real inverse at zero is not an infinite moment. -/
theorem diameter_moment (p : ℝ[X]) (hs : p.Splits) (hn : 2 ≤ p.natDegree)
    (A B : ℝ) (hAB : A < B) (hroots : ∀ x ∈ p.roots, x ∈ Set.Icc A B)
    (a : ℝ) (ha : a ∈ p.roots) (r : ℝ) (hr : 1 ≤ r) :
    p.derivative.eval a = 0 ∨
      (p.natDegree - 1 : ℝ) * (2 / (B - A)) ^ r ≤
        (p.derivative.roots.map (fun x => |a - x| ^ (-r))).sum := by
  rcases diameter_reciprocal p hs hn A B hAB hroots a ha with hd | hmass
  · exact Or.inl hd
  right
  have hcount : p.derivative.roots.card = p.natDegree - 1 := by
    rw [← (derivative_root_budget p hs (by omega)).1.natDegree_eq_card_roots,
      natDegree_derivative]
  have hcard : (p.derivative.roots.card : ℝ) = p.natDegree - 1 := by
    rw [hcount, Nat.cast_sub (by omega), Nat.cast_one]
  have hpos : 0 < p.derivative.roots.card := by rw [hcount]; omega
  have h := multiset_moment_bound p.derivative.roots hpos (fun x => 1 / |a - x|)
    (fun x _ => one_div_nonneg.mpr (abs_nonneg _)) (2 / (B - A)) (by positivity)
    (by rwa [hcard]) r hr
  simpa only [hcard, one_div, Real.inv_rpow (abs_nonneg _),
    Real.rpow_neg (abs_nonneg _)] using h

end Collinear
