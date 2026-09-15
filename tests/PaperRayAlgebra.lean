import Sendov.Analytic.PaperRayAlgebra

open Sendov.PaperRay

example {m : ℝ} (hm : 256 ≤ m) :
    1 + 18 / m < m / (m + 1) * (1 + (24 / 49 - 8 / m) / 5) := ray_one hm
example {m : ℝ} (hm : 256 ≤ m) :
    1 + 62 / m + 2 < m / (m + 1) * (26 * (207 / 512) ^ 2) := ray_five hm

#print axioms compare_from_base
#print axioms ray_one
#print axioms ray_two
#print axioms ray_three
#print axioms ray_four
#print axioms ray_five
