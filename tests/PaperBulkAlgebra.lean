import Sendov.Analytic.PaperBulkAlgebra

open Sendov.PaperBulk

example {m a : ℝ} (hm : 256 ≤ m) (ha : 1 / 3 ≤ a) (hb : a ≤ 4 / 5) :
    16 / (m * a ^ 2) + 24 / m < 1 - a := middle_budget hm ha hb

example {m a : ℝ} (hm : 0 < m) (ha : 4 / 5 ≤ a)
    (hscale : 49 ≤ m * (1 - a)) :
    16 / (m * a ^ 2) + 24 / m ≤ 1 - a := large_ray_budget hm ha hscale

#print axioms middle_cubic_pos
#print axioms middle_budget
#print axioms direct_budget_middle
#print axioms large_ray_budget
#print axioms direct_budget_small
