import Sendov.Analytic.PaperWideRays

/-! Exact historical contracts and cutoff/seam regressions on the actual T. -/
namespace Sendov.PaperWideRaysTests

open PaperPolar PaperWideRays

-- Full contracts: no endpoint suppression, x lower bound, or desired T bound
-- is supplied as an assumption. Lambda is the actual m*(1-a).
example {m : ℕ} {a x : ℝ} (hm : 100000 ≤ m)
    (ha : 0 < a) (ha1 : a < 1) (hx0 : -1 ≤ x) (hx1 : x ≤ 1)
    (hr : RawPolar m a x) (hl0 : 1 / 50 ≤ (m : ℝ) * (1 - a))
    (hl1 : (m : ℝ) * (1 - a) ≤ 400) :
    (m : ℝ) * x ^ 2 * PaperTaylor.budget m a x < (5011 : ℝ) / 5000 :=
  HI01 hm ha ha1 hx0 hx1 hr hl0 hl1

example {m : ℕ} {a x : ℝ} (hm : 10000 ≤ m)
    (ha : 0 < a) (ha1 : a < 1) (hx0 : -1 ≤ x) (hx1 : x ≤ 1)
    (hr : RawPolar m a x) (hl0 : 1 / 10 ≤ (m : ℝ) * (1 - a))
    (hl1 : (m : ℝ) * (1 - a) ≤ 400) :
    (m : ℝ) * x ^ 2 * PaperTaylor.budget m a x < 1 + 46 / (m : ℝ) :=
  HI02 hm ha ha1 hx0 hx1 hr hl0 hl1

example {m : ℕ} {a x : ℝ} (hm : 512 ≤ m)
    (ha : 0 < a) (ha1 : a < 1) (hx0 : -1 ≤ x) (hx1 : x ≤ 1)
    (hr : RawPolar m a x) (hl0 : 5 ≤ (m : ℝ) * (1 - a))
    (hl1 : (m : ℝ) * (1 - a) ≤ 64) :
    (m : ℝ) * x ^ 2 * PaperTaylor.budget m a x < 1 + 53 / (m : ℝ) + 1 / 32 :=
  HI03 hm ha ha1 hx0 hx1 hr hl0 hl1

-- The HI01 lower seam lies below HI02's historical lower seam. The helper
-- really covers it; it does not silently assume lambda >= 1/10.
example {x : ℝ} (hx0 : -1 ≤ x) (hx1 : x ≤ 1)
    (hr : RawPolar 100000 (1 - (1 / 50) / 100000) x) :
    (100000 : ℝ) * x ^ 2 * PaperTaylor.budget 100000 (1 - (1 / 50) / 100000) x <
      5011 / 5000 := by
  apply HI01 (by norm_num) (by norm_num) (by norm_num) hx0 hx1 hr <;> norm_num [lambda]

example {x : ℝ} (hx0 : -1 ≤ x) (hx1 : x ≤ 1)
    (hr : RawPolar 100000 (1 - 400 / 100000) x) :
    (100000 : ℝ) * x ^ 2 * PaperTaylor.budget 100000 (1 - 400 / 100000) x <
      5011 / 5000 := by
  apply HI01 (by norm_num) (by norm_num) (by norm_num) hx0 hx1 hr <;> norm_num [lambda]

example {x : ℝ} (hx0 : -1 ≤ x) (hx1 : x ≤ 1)
    (hr : RawPolar 10000 (1 - (1 / 10) / 10000) x) :
    (10000 : ℝ) * x ^ 2 * PaperTaylor.budget 10000 (1 - (1 / 10) / 10000) x <
      1 + 46 / 10000 := by
  apply HI02 (by norm_num) (by norm_num) (by norm_num) hx0 hx1 hr <;> norm_num [lambda]

example {x : ℝ} (hx0 : -1 ≤ x) (hx1 : x ≤ 1)
    (hr : RawPolar 10000 (24 / 25) x) :
    (10000 : ℝ) * x ^ 2 * PaperTaylor.budget 10000 (24 / 25) x < 1 + 46 / 10000 := by
  apply HI02 (by norm_num) (by norm_num) (by norm_num) hx0 hx1 hr <;> norm_num [lambda]

example {x : ℝ} (hx0 : -1 ≤ x) (hx1 : x ≤ 1)
    (hr : RawPolar 512 (1 - 5 / 512) x) :
    (512 : ℝ) * x ^ 2 * PaperTaylor.budget 512 (1 - 5 / 512) x <
      1 + 53 / 512 + 1 / 32 := by
  apply HI03 (by norm_num) (by norm_num) (by norm_num) hx0 hx1 hr <;> norm_num [lambda]

example {x : ℝ} (hx0 : -1 ≤ x) (hx1 : x ≤ 1)
    (hr : RawPolar 512 (7 / 8) x) :
    (512 : ℝ) * x ^ 2 * PaperTaylor.budget 512 (7 / 8) x < 1 + 53 / 512 + 1 / 32 := by
  apply HI03 (by norm_num) (by norm_num) (by norm_num) hx0 hx1 hr <;> norm_num [lambda]

-- Odd degree: the proof keeps real powers and never relies on even m.
example {x : ℝ} (hx0 : -1 ≤ x) (hx1 : x ≤ 1)
    (hr : RawPolar 513 (1 - 64 / 513) x) :
    (513 : ℝ) * x ^ 2 * PaperTaylor.budget 513 (1 - 64 / 513) x <
      1 + 53 / 513 + 1 / 32 := by
  apply HI03 (by norm_num) (by norm_num) (by norm_num) hx0 hx1 hr <;> norm_num [lambda]

example {m : ℕ} {a x : ℝ} (hm : 512 ≤ m)
    (ha : 0 < a) (ha1 : a < 1) (hx0 : -1 ≤ x) (hx1 : x ≤ 1)
    (hr : RawPolar m a x) (hl0 : 1 / 10 ≤ lambda m a) (hl1 : lambda m a ≤ 1) :
    (m : ℝ) * x ^ 2 * PaperTaylor.budget m a x < 1 + 18 / (m : ℝ) :=
  HI03_small_one hm ha ha1 hx0 hx1 hr hl0 hl1

example {m : ℕ} {a x : ℝ} (hm : 512 ≤ m)
    (ha : 0 < a) (ha1 : a < 1) (hx0 : -1 ≤ x) (hx1 : x ≤ 1)
    (hr : RawPolar m a x) (hl0 : 1 ≤ lambda m a) (hl1 : lambda m a ≤ 5) :
    (m : ℝ) * x ^ 2 * PaperTaylor.budget m a x < 1 + 34 / (m : ℝ) :=
  HI03_small_five hm ha ha1 hx0 hx1 hr hl0 hl1

#print axioms Sendov.PaperWideRays.HI01
#print axioms Sendov.PaperWideRays.HI02
#print axioms Sendov.PaperWideRays.HI03
#print axioms Sendov.PaperWideRays.HI03_small_one
#print axioms Sendov.PaperWideRays.HI03_small_five
#print axioms Sendov.PaperWideRays.tail_certificate

end Sendov.PaperWideRaysTests
