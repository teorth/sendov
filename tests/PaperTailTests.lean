import Sendov.Analytic.PaperTail

open Sendov

-- Real-degree contracts (not merely a natural-degree table).
example {m : ℝ} (hm : 256 ≤ m) :
    (m ^ 2 / 2 + m) * (4 / 5 : ℝ) ^ ((m - 1) / 2) < 1 / m :=
  PaperTail.tail_four_fifths hm

example {m : ℝ} (hm : 256 ≤ m) :
    (m ^ 2 / 2 + m) * (9 / 10 : ℝ) ^ ((m - 1) / 2) < 1 / 4 :=
  PaperTail.tail_nine_tenths hm

example {m : ℝ} (hm : 256 ≤ m) :
    (m ^ 2 / 2 + m) * (23 / 25 : ℝ) ^ ((m - 1) / 2) < 2 :=
  PaperTail.tail_twenty_three_twenty_fifths hm

example {m : ℝ} (hm : 256 ≤ m) :
    m * (1 + 5 * m / 162) * Real.exp (-22 * m / 1215) < 24 :=
  PaperTail.middle_tail hm

example {k l : ℝ} (hk : 19 / 2 ≤ k) (hkl : k ≤ l) :
    (1 + 5 * l / 8) * Real.exp (-(11 / 30 : ℝ) * l) ≤
      (1 + 5 * k / 8) * Real.exp (-(11 / 30 : ℝ) * k) :=
  PaperTail.middle_antitone hk (hk.trans hkl) hkl

-- The exact cutoff and a nonintegral degree are covered.
example : ((256 : ℝ) ^ 2 / 2 + 256) * (9 / 10 : ℝ) ^ (((256 : ℝ) - 1) / 2) < 1 / 4 :=
  PaperTail.tail_nine_tenths (m := 256) (by norm_num)

example : ((513 / 2 : ℝ) ^ 2 / 2 + 513 / 2) * (23 / 25 : ℝ) ^ (((513 / 2 : ℝ) - 1) / 2) < 2 :=
  PaperTail.tail_twenty_three_twenty_fifths (m := 513 / 2) (by norm_num)

section ActualBudget
variable {m a x : ℝ} (hm : 256 ≤ m) (ha : 0 < a) (ha1 : a < 1)
  (hx1 : x ≤ 1) (hxa : x < 2 * a)

example (hx : 5 / 6 < x) (hb : PaperTaylor.beta a x 1 ≤ 4 / 5) :
    m * x ^ 2 * PaperTaylor.budget m a x < 1 + 18 / m :=
  PaperTail.budget_region_one hm ha ha1 hx hx1 hxa hb

example (hx : 7 / 12 < x) (hb : PaperTaylor.beta a x 1 ≤ 4 / 5) :
    m * x ^ 2 * PaperTaylor.budget m a x < 1 + 33 / m :=
  PaperTail.budget_region_two hm ha ha1 hx hx1 hxa hb

example (hx : 231 / 512 < x) (hb : PaperTaylor.beta a x 1 ≤ 9 / 10) :
    m * x ^ 2 * PaperTaylor.budget m a x < 1 + 51 / m + 1 / 4 :=
  PaperTail.budget_region_three hm ha ha1 hx hx1 hxa hb

example (hx : 207 / 512 < x) (hb : PaperTaylor.beta a x 1 ≤ 23 / 25) :
    m * x ^ 2 * PaperTaylor.budget m a x < 1 + 62 / m + 2 :=
  PaperTail.budget_region_four hm ha ha1 hx hx1 hxa hb
end ActualBudget

#print axioms PaperTail.tail_four_fifths
#print axioms PaperTail.tail_nine_tenths
#print axioms PaperTail.tail_twenty_three_twenty_fifths
#print axioms PaperTail.middle_tail
#print axioms PaperTail.middle_antitone
#print axioms PaperTail.budget_region_one
#print axioms PaperTail.budget_region_two
#print axioms PaperTail.budget_region_three
#print axioms PaperTail.budget_region_four
