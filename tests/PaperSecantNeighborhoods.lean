import Sendov.Analytic.PaperSecant

/-!
# Two continuous finite secant diagnostic neighborhoods

All bounds below are rational interval bounds on the whole closed interval,
not evaluations at sample points. These are only two local diagnostics;
no all-degree or all-parameter positivity of the secant gate is asserted.
-/
namespace Sendov.PaperSecant.Neighborhoods

/-- A closed rational enclosure, with endpoints kept as real numbers. -/
def Bounds (z l u : ℝ) : Prop := l ≤ z ∧ z ≤ u

namespace Bounds
variable {z w l u L U l' u' : ℝ}

lemma widen (h : Bounds z l u) (hl : l' ≤ l) (hu : u ≤ u') : Bounds z l' u' :=
  ⟨hl.trans h.1, h.2.trans hu⟩

lemma const (z : ℝ) : Bounds z z z := ⟨le_rfl, le_rfl⟩

lemma add (hz : Bounds z l u) (hw : Bounds w L U) : Bounds (z + w) (l + L) (u + U) :=
  ⟨add_le_add hz.1 hw.1, add_le_add hz.2 hw.2⟩

lemma sub (hz : Bounds z l u) (hw : Bounds w L U) : Bounds (z - w) (l - U) (u - L) :=
  ⟨sub_le_sub hz.1 hw.2, sub_le_sub hz.2 hw.1⟩

lemma mul (hz : Bounds z l u) (hw : Bounds w L U) (hl : 0 ≤ l) (hL : 0 ≤ L) :
    Bounds (z * w) (l * L) (u * U) := by
  exact ⟨mul_le_mul hz.1 hw.1 hL (hl.trans hz.1),
    mul_le_mul hz.2 hw.2 (hL.trans hw.1) (hl.trans (hz.1.trans hz.2))⟩

lemma div (hz : Bounds z l u) (hw : Bounds w L U) (hl : 0 ≤ l) (hL : 0 < L) :
    Bounds (z / w) (l / U) (u / L) := by
  have hw0 : 0 < w := hL.trans_le hw.1
  have hU : 0 < U := hw0.trans_le hw.2
  constructor
  · exact (div_le_div_iff₀ hU hw0).2
      (mul_le_mul hz.1 hw.2 hw0.le (hl.trans hz.1))
  · exact (div_le_div_iff₀ hw0 hL).2
      (mul_le_mul hz.2 hw.1 hL.le (hl.trans (hz.1.trans hz.2)))

lemma pow (hz : Bounds z l u) (hl : 0 ≤ l) (n : ℕ) :
    Bounds (z ^ n) (l ^ n) (u ^ n) :=
  ⟨pow_le_pow_left₀ hl hz.1 n, pow_le_pow_left₀ (hl.trans hz.1) hz.2 n⟩

end Bounds


/-- Uniform rational positivity on the report's degree-7 closed neighborhood. -/
theorem gate_7_lower {a : ℝ} (ha : Bounds a (7999 / 10000) (8001 / 10000)) :
    (21011 : ℝ) / 200000 ≤ Fsec 7 a := by
  let a2 : ℝ := a ^ 2
  have ha2 : Bounds a2 (3999 / 6250) (6401601 / 10000000) :=
    (ha.pow (by norm_num) 2).widen (by norm_num) (by norm_num)
  let delta : ℝ := (1 - a2)
  have hdelta : Bounds delta (3598399 / 10000000) (2251 / 6250) :=
    ((Bounds.const (1 : ℝ)).sub ha2).widen (by norm_num) (by norm_num)
  let top : ℝ := (a + delta)
  have htop : Bounds top (11597399 / 10000000) (58013 / 50000) :=
    (ha.add hdelta).widen (by norm_num) (by norm_num)
  let u1 : ℝ := ((top ^ 8 - a ^ 8) / (8 * delta))
  have hu1 : Bounds u1 (10775067 / 10000000) (2706667 / 2500000) :=
    (((htop.pow (by norm_num) 8).sub (ha.pow (by norm_num) 8)).div ((Bounds.const (8 : ℝ)).mul
      hdelta (by norm_num) (by norm_num)) (by norm_num) (by norm_num)).widen (by norm_num) (by
      norm_num)
  let u0 : ℝ := ((2 * (1 - a ^ 9)) / (9 * delta))
  have hu0 : Bounds u0 (1335257 / 2500000) (1069529 / 2000000) :=
    (((Bounds.const (2 : ℝ)).mul ((Bounds.const (1 : ℝ)).sub (ha.pow (by norm_num) 9)) (by
      norm_num) (by norm_num)).div ((Bounds.const (9 : ℝ)).mul hdelta (by norm_num) (by norm_num))
      (by norm_num) (by norm_num)).widen (by norm_num) (by norm_num)
  let v0 : ℝ := (u0 - (((7 / 12) * a ^ 5) * delta ^ 2))
  have hv0 : Bounds v0 (2546463 / 5000000) (2550147 / 5000000) :=
    (hu0.sub (((Bounds.const ((7 / 12) : ℝ)).mul (ha.pow (by norm_num) 5) (by norm_num) (by
      norm_num)).mul (hdelta.pow (by norm_num) 2) (by norm_num) (by norm_num))).widen (by
      norm_num) (by norm_num)
  let s : ℝ := ((a / 2) + (((1 - (a / 2)) * (1 - v0)) / (u1 - v0)))
  have hs : Bounds s (4563153 / 5000000) (2297309 / 2500000) :=
    ((ha.div (Bounds.const (2 : ℝ)) (by norm_num) (by norm_num)).add ((((Bounds.const (1 : ℝ)).sub
      (ha.div (Bounds.const (2 : ℝ)) (by norm_num) (by norm_num))).mul ((Bounds.const (1 : ℝ)).sub
      hv0) (by norm_num) (by norm_num)).div (hu1.sub hv0) (by norm_num) (by norm_num))).widen (by
      norm_num) (by norm_num)
  let c : ℝ := (a * ((2 * s) - a))
  have hc : Bounds c (1025033 / 1250000) (1038077 / 1250000) :=
    (ha.mul (((Bounds.const (2 : ℝ)).mul hs (by norm_num) (by norm_num)).sub ha) (by norm_num) (by
      norm_num)).widen (by norm_num) (by norm_num)
  let b : ℝ := ((1 - ((2 * a) * s)) + a2)
  have hb : Bounds b (211723 / 1250000) (1801337 / 10000000) :=
    (((Bounds.const (1 : ℝ)).sub (((Bounds.const (2 : ℝ)).mul ha (by norm_num) (by norm_num)).mul
      hs (by norm_num) (by norm_num))).add ha2).widen (by norm_num) (by norm_num)
  let d : ℝ := ((2 * a) * (1 - s))
  have hd : Bounds d (64853 / 500000) (699043 / 5000000) :=
    (((Bounds.const (2 : ℝ)).mul ha (by norm_num) (by norm_num)).mul ((Bounds.const (1 : ℝ)).sub
      hs) (by norm_num) (by norm_num)).widen (by norm_num) (by norm_num)
  let budget : ℝ := (1 - ((7 * a) / 8))
  have hbudget : Bounds budget (23993 / 80000) (24007 / 80000) :=
    ((Bounds.const (1 : ℝ)).sub (((Bounds.const (7 : ℝ)).mul ha (by norm_num) (by norm_num)).div
      (Bounds.const (8 : ℝ)) (by norm_num) (by norm_num))).widen (by norm_num) (by norm_num)
  let w : ℝ := ((((1 / 8) + b ^ 3) + (d / (a * 5))) + (((84 * a2) * d ^ 2) / ((c ^ 4 * 8) * 10)))
  have hw : Bounds w (58139 / 312500) (77943 / 400000) :=
    ((((Bounds.const ((1 / 8) : ℝ)).add (hb.pow (by norm_num) 3)).add (hd.div (ha.mul
      (Bounds.const (5 : ℝ)) (by norm_num) (by norm_num)) (by norm_num) (by norm_num))).add
      ((((Bounds.const (84 : ℝ)).mul ha2 (by norm_num) (by norm_num)).mul (hd.pow (by norm_num) 2)
      (by norm_num) (by norm_num)).div (((hc.pow (by norm_num) 4).mul (Bounds.const (8 : ℝ)) (by
      norm_num) (by norm_num)).mul (Bounds.const (10 : ℝ)) (by norm_num) (by norm_num)) (by
      norm_num) (by norm_num))).widen (by norm_num) (by norm_num)
  let f : ℝ := (budget - w)
  have hf : Bounds f (21011 / 200000) (1140427 / 10000000) :=
    (hbudget.sub hw).widen (by norm_num) (by norm_num)
  have hid : f = Fsec 7 a := by
    dsimp [f, w, budget, d, b, c, s, v0, u0, u1, top, delta, a2]
    norm_num [Fsec, B, Wsec, S, V0, U0, U1, PaperTaylor.beta,
      PaperTaylor.defect, PaperTaylor.chord]
  rw [← hid]
  exact hf.1

/-- Uniform rational positivity on the report's degree-10 closed neighborhood. -/
theorem gate_10_lower {a : ℝ} (ha : Bounds a (899999 / 1000000) (900001 / 1000000)) :
    (155747 : ℝ) / 10000000 ≤ Fsec 10 a := by
  let a2 : ℝ := a ^ 2
  have ha2 : Bounds a2 (4049991 / 5000000) (8100019 / 10000000) :=
    (ha.pow (by norm_num) 2).widen (by norm_num) (by norm_num)
  let delta : ℝ := (1 - a2)
  have hdelta : Bounds delta (1899981 / 10000000) (950009 / 5000000) :=
    ((Bounds.const (1 : ℝ)).sub ha2).widen (by norm_num) (by norm_num)
  let top : ℝ := (a + delta)
  have htop : Bounds top (10899971 / 10000000) (2725007 / 2500000) :=
    (ha.add hdelta).widen (by norm_num) (by norm_num)
  let u1 : ℝ := ((top ^ 11 - a ^ 11) / (11 * delta))
  have hu1 : Bounds u1 (10844569 / 10000000) (1355691 / 1250000) :=
    (((htop.pow (by norm_num) 11).sub (ha.pow (by norm_num) 11)).div ((Bounds.const (11 : ℝ)).mul
      hdelta (by norm_num) (by norm_num)) (by norm_num) (by norm_num)).widen (by norm_num) (by
      norm_num)
  let u0 : ℝ := ((2 * (1 - a ^ 12)) / (12 * delta))
  have hu0 : Bounds u0 (1258877 / 2000000) (3147287 / 5000000) :=
    (((Bounds.const (2 : ℝ)).mul ((Bounds.const (1 : ℝ)).sub (ha.pow (by norm_num) 12)) (by
      norm_num) (by norm_num)).div ((Bounds.const (12 : ℝ)).mul hdelta (by norm_num) (by
      norm_num)) (by norm_num) (by norm_num)).widen (by norm_num) (by norm_num)
  let v0 : ℝ := (u0 - (((5 / 6) * a ^ 8) * delta ^ 2))
  have hv0 : Bounds v0 (3082441 / 5000000) (6165079 / 10000000) :=
    (hu0.sub (((Bounds.const ((5 / 6) : ℝ)).mul (ha.pow (by norm_num) 8) (by norm_num) (by
      norm_num)).mul (hdelta.pow (by norm_num) 2) (by norm_num) (by norm_num))).widen (by
      norm_num) (by norm_num)
  let s : ℝ := ((a / 2) + (((1 - (a / 2)) * (1 - v0)) / (u1 - v0)))
  have hs : Bounds s (450311 / 500000) (281487 / 312500) :=
    ((ha.div (Bounds.const (2 : ℝ)) (by norm_num) (by norm_num)).add ((((Bounds.const (1 : ℝ)).sub
      (ha.div (Bounds.const (2 : ℝ)) (by norm_num) (by norm_num))).mul ((Bounds.const (1 : ℝ)).sub
      hv0) (by norm_num) (by norm_num)).div (hu1.sub hv0) (by norm_num) (by norm_num))).widen (by
      norm_num) (by norm_num)
  let c : ℝ := (a * ((2 * s) - a))
  have hc : Bounds c (8111177 / 10000000) (811367 / 1000000) :=
    (ha.mul (((Bounds.const (2 : ℝ)).mul hs (by norm_num) (by norm_num)).sub ha) (by norm_num) (by
      norm_num)).widen (by norm_num) (by norm_num)
  let b : ℝ := ((1 - ((2 * a) * s)) + a2)
  have hb : Bounds b (235789 / 1250000) (944421 / 5000000) :=
    (((Bounds.const (1 : ℝ)).sub (((Bounds.const (2 : ℝ)).mul ha (by norm_num) (by norm_num)).mul
      hs (by norm_num) (by norm_num))).add ha2).widen (by norm_num) (by norm_num)
  let d : ℝ := ((2 * a) * (1 - s))
  have hd : Bounds d (893173 / 5000000) (894403 / 5000000) :=
    (((Bounds.const (2 : ℝ)).mul ha (by norm_num) (by norm_num)).mul ((Bounds.const (1 : ℝ)).sub
      hs) (by norm_num) (by norm_num)).widen (by norm_num) (by norm_num)
  let budget : ℝ := (1 - ((10 * a) / 11))
  have hbudget : Bounds budget (454543 / 2500000) (1818191 / 10000000) :=
    ((Bounds.const (1 : ℝ)).sub (((Bounds.const (10 : ℝ)).mul ha (by norm_num) (by norm_num)).div
      (Bounds.const (11 : ℝ)) (by norm_num) (by norm_num))).widen (by norm_num) (by norm_num)
  let w : ℝ := ((((1 / 11) + b ^ 5) + (d / (a * 8))) + (((120 * a2) * d ^ 2) / ((c ^ 4 * 11) *
      13)))
  have hw : Bounds w (1660067 / 10000000) (66497 / 400000) :=
    ((((Bounds.const ((1 / 11) : ℝ)).add (hb.pow (by norm_num) 5)).add (hd.div (ha.mul
      (Bounds.const (8 : ℝ)) (by norm_num) (by norm_num)) (by norm_num) (by norm_num))).add
      ((((Bounds.const (120 : ℝ)).mul ha2 (by norm_num) (by norm_num)).mul (hd.pow (by norm_num)
      2) (by norm_num) (by norm_num)).div (((hc.pow (by norm_num) 4).mul (Bounds.const (11 : ℝ))
      (by norm_num) (by norm_num)).mul (Bounds.const (13 : ℝ)) (by norm_num) (by norm_num)) (by
      norm_num) (by norm_num))).widen (by norm_num) (by norm_num)
  let f : ℝ := (budget - w)
  have hf : Bounds f (155747 / 10000000) (39531 / 2500000) :=
    (hbudget.sub hw).widen (by norm_num) (by norm_num)
  have hid : f = Fsec 10 a := by
    dsimp [f, w, budget, d, b, c, s, v0, u0, u1, top, delta, a2]
    norm_num [Fsec, B, Wsec, S, V0, U0, U1, PaperTaylor.beta,
      PaperTaylor.defect, PaperTaylor.chord]
  rw [← hid]
  exact hf.1

/-- Positivity at every real parameter in this interval, including its endpoints. -/
theorem gate_7_interval {a : ℝ} (ha : a ∈ Set.Icc (7999 / 10000) (8001 / 10000)) :
    0 < Fsec 7 a :=
  lt_of_lt_of_le (by norm_num : (0 : ℝ) < 21011 / 200000) (gate_7_lower ha)

/-- D holds uniformly for every raw-polar feasible mean in this neighborhood. -/
theorem D_7_interval {a x : ℝ} (ha : a ∈ Set.Icc (7999 / 10000) (8001 / 10000))
    (hx0 : -1 ≤ x) (hx1 : x ≤ 1) (hr : PaperPolar.RawPolar 7 a x) :
    PaperTaylor.budget 7 a x < B 7 a := by
  have ha0 : 0 < a := by have := ha.1; linarith
  have ha1 : a < 1 := by have := ha.2; linarith
  exact gate_implies_D (by norm_num) ha0 ha1 hx0 hx1 hr (gate_7_interval ha)

/-- Positivity at every real parameter in this interval, including its endpoints. -/
theorem gate_10_interval {a : ℝ} (ha : a ∈ Set.Icc (899999 / 1000000) (900001 / 1000000)) :
    0 < Fsec 10 a :=
  lt_of_lt_of_le (by norm_num : (0 : ℝ) < 155747 / 10000000) (gate_10_lower ha)

/-- D holds uniformly for every raw-polar feasible mean in this neighborhood. -/
theorem D_10_interval {a x : ℝ} (ha : a ∈ Set.Icc (899999 / 1000000) (900001 / 1000000))
    (hx0 : -1 ≤ x) (hx1 : x ≤ 1) (hr : PaperPolar.RawPolar 10 a x) :
    PaperTaylor.budget 10 a x < B 10 a := by
  have ha0 : 0 < a := by have := ha.1; linarith
  have ha1 : a < 1 := by have := ha.2; linarith
  exact gate_implies_D (by norm_num) ha0 ha1 hx0 hx1 hr (gate_10_interval ha)

#print axioms gate_7_lower
#print axioms gate_10_lower
#print axioms gate_7_interval
#print axioms gate_10_interval
#print axioms D_7_interval
#print axioms D_10_interval

end Sendov.PaperSecant.Neighborhoods
