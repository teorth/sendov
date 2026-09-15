import Sendov.Collinear.Mass

open Polynomial
namespace Collinear

/-- Logarithmic derivative balance at a simple marked root. -/
theorem reciprocal_balance (p : ℝ[X]) (hs : p.Splits) (hn : 0 < p.natDegree)
    (a : ℝ) (ha : a ∈ p.roots) (hd : p.derivative.eval a ≠ 0) :
    (p.derivative.roots.map (fun x => 1 / (a - x))).sum =
      2 * (p.roots.map (fun x => 1 / (a - x))).sum := by
  classical
  have hp : p ≠ 0 := ne_zero_of_mem_roots ha
  let g := p /ₘ (X - C a)
  have hfac : (X - C a) * g = p := mul_divByMonic_eq_iff_isRoot.mpr
    ((mem_roots hp).mp ha)
  have hg : g ≠ 0 := by intro h; simp [h] at hfac; exact hp hfac.symm
  have hgs : g.Splits := hs.of_dvd hp ⟨X - C a, by rw [mul_comm]; exact hfac.symm⟩
  have hder : p.derivative = g + (X - C a) * g.derivative := by
    rw [← hfac, derivative_mul]; simp
  have heval : p.derivative.eval a = g.eval a := by rw [hder]; simp
  have heval2 : p.derivative.derivative.eval a = 2 * g.derivative.eval a := by
    rw [hder, derivative_add, derivative_mul]; simp; ring
  have hroots : p.roots = {a} + g.roots := by
    rw [← hfac, roots_mul (mul_ne_zero (X_sub_C_ne_zero a) hg), roots_X_sub_C]
  rw [← (derivative_root_budget p hs hn).1.eval_derivative_div_eval_of_ne_zero hd,
    heval2, heval, mul_div_assoc,
    hgs.eval_derivative_div_eval_of_ne_zero (heval ▸ hd)]
  rw [hroots]
  simp only [Multiset.map_add, Multiset.map_singleton, Multiset.sum_add,
    Multiset.sum_singleton, sub_self, div_zero, zero_add]

/-- Strict-side decomposition; occurrences at the mark contribute zero. -/
theorem reciprocal_decomposition (s : Multiset ℝ) (a : ℝ) :
    (s.map (fun x => 1 / (a - x))).sum =
      ((s.filter (· < a)).map (fun x => 1 / (a - x))).sum -
      ((s.filter (a < ·)).map (fun x => 1 / (x - a))).sum ∧
    (s.map (fun x => 1 / |a - x|)).sum =
      ((s.filter (· < a)).map (fun x => 1 / (a - x))).sum +
      ((s.filter (a < ·)).map (fun x => 1 / (x - a))).sum := by
  classical
  induction s using Multiset.induction_on with
  | empty => simp
  | @cons x s ih =>
    simp only [Multiset.map_cons, Multiset.sum_cons, Multiset.filter_cons]
    rcases lt_trichotomy x a with h | rfl | h
    · simp only [h, not_lt.mpr h.le, ite_true, ite_false, zero_add,
        Multiset.map_add, Multiset.sum_add, Multiset.map_singleton, Multiset.sum_singleton,
        abs_of_pos (sub_pos.mpr h), ih.1, ih.2]
      constructor <;> ring
    · simpa only [lt_self_iff_false, ite_false, sub_self, abs_zero, div_zero, zero_add]
        using ih
    · have he : 1 / (a - x) = -(1 / (x - a)) := by rw [← neg_sub x a, div_neg]
      simp only [h, not_lt.mpr h.le, ite_true, ite_false, zero_add,
        Multiset.map_add, Multiset.sum_add, Multiset.map_singleton, Multiset.sum_singleton,
        abs_of_neg (sub_neg.mpr h), neg_sub, he, ih.1, ih.2]
      constructor <;> ring

/-- Signed balance plus interlacing controls each side by half the total mass. -/
theorem two_sided_mass (p : ℝ[X]) (hs : p.Splits) (hn : 0 < p.natDegree)
    (a : ℝ) (ha : a ∈ p.roots) (hd : p.derivative.eval a ≠ 0) :
    2 * ((p.roots.filter (· < a)).map (fun x => 1 / (a - x))).sum ≤
      (p.derivative.roots.map (fun x => 1 / |a - x|)).sum ∧
    2 * ((p.roots.filter (a < ·)).map (fun x => 1 / (x - a))).sum ≤
      (p.derivative.roots.map (fun x => 1 / |a - x|)).sum := by
  obtain ⟨hl, hr⟩ := signed_reciprocal_domination p hs hn a ha
  have hb := reciprocal_balance p hs hn a ha hd
  rw [(reciprocal_decomposition p.roots a).1,
    (reciprocal_decomposition p.derivative.roots a).1] at hb
  rw [(reciprocal_decomposition p.derivative.roots a).2]
  constructor <;> linarith

end Collinear
