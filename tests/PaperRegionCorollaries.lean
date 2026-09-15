import Sendov.Analytic.PaperRegionCorollaries

/-! Full-domain literal-contract tests for all eleven families, plus explicit
closed seams and the entire formerly omitted [1/5,2/5) strip. -/
namespace Sendov.PaperRegionCorollaries.Tests

open PaperPolar

/-- Full quantified contract: in02_two_end. -/
example {m : ℕ} {a x : ℝ} (hm : 7 ≤ m)
    (ha : 0 < a) (ha1 : a < 1) (hx0 : -1 ≤ x) (hx1 : x ≤ 1)
    (hr : RawPolar m a x) :
    (((1 - 2 * a * x + a ^ 2) ^ ((m : ℝ) / 2) +
      (m : ℝ) * a ^ 2 * ∫ t in (0 : ℝ)..1,
        t * (1 - 2 * a * x * t + a ^ 2 * t ^ 2) ^ (((m : ℝ) - 1) / 2)) ≤ 100 * (m : ℝ) /
      (9 * ((m : ℝ) + 1) * ((m : ℝ) + 3) * x ^ 2) +
      29 * (1 - 2 * a * x + a ^ 2) ^ ((m : ℝ) / 2)) ∧
    (((1 - 2 * a * x + a ^ 2) ^ ((m : ℝ) / 2) +
      (m : ℝ) * a ^ 2 * ∫ t in (0 : ℝ)..1,
        t * (1 - 2 * a * x * t + a ^ 2 * t ^ 2) ^ (((m : ℝ) - 1) / 2)) ≤ 16 * (m : ℝ) /
      (((m : ℝ) + 1) * ((m : ℝ) + 3) * x ^ 2) +
      13 * (1 - 2 * a * x + a ^ 2) ^ ((m : ℝ) / 2)) :=
  in02_two_end hm ha ha1 hx0 hx1 hr

/-- Full quantified contract: in04_middle. -/
example {m : ℕ} {a x : ℝ} (hm : 7 ≤ m)
    (ha : 0 < a) (ha1 : a < 1) (hx : 0 < x) (hx1 : x ≤ 1)
    (hxa : x < a) (hax : a < 3 * x / 2) :
    (((1 - 2 * a * x + a ^ 2) ^ ((m : ℝ) / 2) +
      (m : ℝ) * a ^ 2 * ∫ t in (0 : ℝ)..1,
        t * (1 - 2 * a * x * t + a ^ 2 * t ^ 2) ^ (((m : ℝ) - 1) / 2)) < 4 / ((m : ℝ) * x ^ 2) +
      (1 + 5 * ((m : ℝ) * x ^ 2) / 8) *
        Real.exp (-3 * ((m : ℝ) - 1) * ((m : ℝ) * x ^ 2) / (8 * (m : ℝ)))) ∧
    (9 ≤ m → ((1 - 2 * a * x + a ^ 2) ^ ((m : ℝ) / 2) +
      (m : ℝ) * a ^ 2 * ∫ t in (0 : ℝ)..1,
        t * (1 - 2 * a * x * t + a ^ 2 * t ^ 2) ^ (((m : ℝ) - 1) / 2)) < 4 / ((m : ℝ) * x ^ 2) +
      (1 + 5 * ((m : ℝ) * x ^ 2) / 8) * Real.exp (-((m : ℝ) * x ^ 2) / 3)) :=
  in04_middle hm ha ha1 hx hx1 hxa hax

/-- Full quantified contract: ne05_near. -/
example {m : ℕ} {a x : ℝ} (hm : 7 ≤ m)
    (ha : 0 < a) (ha1 : a < 1) (hx0 : -1 ≤ x) (hx1 : x ≤ 1)
    (hr : RawPolar m a x)
    (hl : lambda m a ≤ 3 / 10) :
    (1 - (m : ℝ) * a / ((m : ℝ) + 1)) - ((1 - 2 * a * x + a ^ 2) ^ ((m : ℝ) / 2) +
      (m : ℝ) * a ^ 2 * ∫ t in (0 : ℝ)..1,
        t * (1 - 2 * a * x * t + a ^ 2 * t ^ 2) ^ (((m : ℝ) - 1) / 2)) > (1 - a) / 1000 :=
  ne05_near hm ha ha1 hx0 hx1 hr hl

/-- Full quantified contract: un04_bulk40. -/
example {m : ℕ} {a x : ℝ} (hm : 512 ≤ m)
    (ha : 0 < a) (ha1 : a < 1) (hx0 : -1 ≤ x) (hx1 : x ≤ 1)
    (hr : RawPolar m a x)
    (ha2 : 2 / 5 ≤ a) :
    (((1 - 2 * a * x + a ^ 2) ^ ((m : ℝ) / 2) +
      (m : ℝ) * a ^ 2 * ∫ t in (0 : ℝ)..1,
        t * (1 - 2 * a * x * t + a ^ 2 * t ^ 2) ^ (((m : ℝ) - 1) / 2)) < 40 / ((m : ℝ) * a ^ 2)) ∧
    (40 ≤ (m : ℝ) * a ^ 2 * (1 - a) →
      ((1 - 2 * a * x + a ^ 2) ^ ((m : ℝ) / 2) +
      (m : ℝ) * a ^ 2 * ∫ t in (0 : ℝ)..1,
        t * (1 - 2 * a * x * t + a ^ 2 * t ^ 2) ^ (((m : ℝ) - 1) / 2)) <
      1 - a ∧ 1 - a < (1 - (m : ℝ) * a / ((m : ℝ) + 1))) :=
  un04_bulk40 hm ha ha1 hx0 hx1 hr ha2

/-- Full quantified contract: un05_bulk116. -/
example {m : ℕ} {a x : ℝ} (hm : 7 ≤ m)
    (ha : 0 < a) (ha1 : a < 1) (hx0 : -1 ≤ x) (hx1 : x ≤ 1)
    (hr : RawPolar m a x)
    (hbulk : 116 ≤ (m : ℝ) * a ^ 2 * (1 - a)) :
    ((1 - 2 * a * x + a ^ 2) ^ ((m : ℝ) / 2) +
      (m : ℝ) * a ^ 2 * ∫ t in (0 : ℝ)..1,
        t * (1 - 2 * a * x * t + a ^ 2 * t ^ 2) ^ (((m : ℝ) - 1) / 2)) <
      1 - a ∧ 1 - a < (1 - (m : ℝ) * a / ((m : ℝ) + 1)) :=
  un05_bulk116 hm ha ha1 hx0 hx1 hr hbulk

/-- Full quantified contract: un08_all_a_512. -/
example {m : ℕ} {a x : ℝ} (hm : 512 ≤ m)
    (ha : 0 < a) (ha1 : a < 1) (hx0 : -1 ≤ x) (hx1 : x ≤ 1)
    (hr : RawPolar m a x) :
    ((1 - 2 * a * x + a ^ 2) ^ ((m : ℝ) / 2) +
      (m : ℝ) * a ^ 2 * ∫ t in (0 : ℝ)..1,
        t * (1 - 2 * a * x * t + a ^ 2 * t ^ 2) ^ (((m : ℝ) - 1) / 2)) <
      (1 - (m : ℝ) * a / ((m : ℝ) + 1)) :=
  un08_all_a_512 hm ha ha1 hx0 hx1 hr

/-- Full quantified contract: un09_all_a_10000. -/
example {m : ℕ} {a x : ℝ} (hm : 10000 ≤ m)
    (ha : 0 < a) (ha1 : a < 1) (hx0 : -1 ≤ x) (hx1 : x ≤ 1)
    (hr : RawPolar m a x) :
    ((1 - 2 * a * x + a ^ 2) ^ ((m : ℝ) / 2) +
      (m : ℝ) * a ^ 2 * ∫ t in (0 : ℝ)..1,
        t * (1 - 2 * a * x * t + a ^ 2 * t ^ 2) ^ (((m : ℝ) - 1) / 2)) <
      (1 - (m : ℝ) * a / ((m : ℝ) + 1)) :=
  un09_all_a_10000 hm ha ha1 hx0 hx1 hr

/-- Full quantified contract: un10_all_a_100000. -/
example {m : ℕ} {a x : ℝ} (hm : 100000 ≤ m)
    (ha : 0 < a) (ha1 : a < 1) (hx0 : -1 ≤ x) (hx1 : x ≤ 1)
    (hr : RawPolar m a x) :
    ((1 - 2 * a * x + a ^ 2) ^ ((m : ℝ) / 2) +
      (m : ℝ) * a ^ 2 * ∫ t in (0 : ℝ)..1,
        t * (1 - 2 * a * x * t + a ^ 2 * t ^ 2) ^ (((m : ℝ) - 1) / 2)) <
      (1 - (m : ℝ) * a / ((m : ℝ) + 1)) :=
  un10_all_a_100000 hm ha ha1 hx0 hx1 hr

/-- Full quantified contract: un11_all_a_1000000. -/
example {m : ℕ} {a x : ℝ} (hm : 1000000 ≤ m)
    (ha : 0 < a) (ha1 : a < 1) (hx0 : -1 ≤ x) (hx1 : x ≤ 1)
    (hr : RawPolar m a x) :
    ((1 - 2 * a * x + a ^ 2) ^ ((m : ℝ) / 2) +
      (m : ℝ) * a ^ 2 * ∫ t in (0 : ℝ)..1,
        t * (1 - 2 * a * x * t + a ^ 2 * t ^ 2) ^ (((m : ℝ) - 1) / 2)) <
      (1 - (m : ℝ) * a / ((m : ℝ) + 1)) :=
  un11_all_a_1000000 hm ha ha1 hx0 hx1 hr

/-- Full quantified contract: ra03_scaled_upper. -/
example {m : ℕ} {a x : ℝ} (hm : 256 ≤ m)
    (ha : 0 < a) (ha1 : a < 1) (hx0 : -1 ≤ x) (hx1 : x ≤ 1)
    (hr : RawPolar m a x) :
    (lambda m a ∈ Set.Icc (1 / 5) (1) →
      (m : ℝ) * x ^ 2 * ((1 - 2 * a * x + a ^ 2) ^ ((m : ℝ) / 2) +
      (m : ℝ) * a ^ 2 * ∫ t in (0 : ℝ)..1,
        t * (1 - 2 * a * x * t + a ^ 2 * t ^ 2) ^ (((m : ℝ) - 1) / 2)) < 1 + 18 / (m : ℝ)) ∧
    (lambda m a ∈ Set.Icc (1) (10) →
      (m : ℝ) * x ^ 2 * ((1 - 2 * a * x + a ^ 2) ^ ((m : ℝ) / 2) +
      (m : ℝ) * a ^ 2 * ∫ t in (0 : ℝ)..1,
        t * (1 - 2 * a * x * t + a ^ 2 * t ^ 2) ^ (((m : ℝ) - 1) / 2)) < 1 + 33 / (m : ℝ)) ∧
    (lambda m a ∈ Set.Icc (10) (25) →
      (m : ℝ) * x ^ 2 * ((1 - 2 * a * x + a ^ 2) ^ ((m : ℝ) / 2) +
      (m : ℝ) * a ^ 2 * ∫ t in (0 : ℝ)..1,
        t * (1 - 2 * a * x * t + a ^ 2 * t ^ 2) ^ (((m : ℝ) - 1) / 2)) < 1 + 51 / (m : ℝ) + 1 / 4) ∧
    (lambda m a ∈ Set.Icc (25) (49) →
      (m : ℝ) * x ^ 2 * ((1 - 2 * a * x + a ^ 2) ^ ((m : ℝ) / 2) +
      (m : ℝ) * a ^ 2 * ∫ t in (0 : ℝ)..1,
        t * (1 - 2 * a * x * t + a ^ 2 * t ^ 2) ^ (((m : ℝ) - 1) / 2)) < 1 + 62 / (m : ℝ) + 2) :=
  ra03_scaled_upper hm ha ha1 hx0 hx1 hr

/-- Full quantified contract: ra04_scaled_lower. -/
example {m : ℕ} {a x : ℝ} (hm : 256 ≤ m)
    (ha : 0 < a) (ha1 : a < 1) (hx0 : -1 ≤ x) (hx1 : x ≤ 1)
    (hr : RawPolar m a x) :
    (lambda m a ∈ Set.Icc (1 / 5) (1) →
      1 + 18 / (m : ℝ) < (m : ℝ) / ((m : ℝ) + 1) * (1 + (24 / 49 - 8 / (m : ℝ)) / 5) ∧
      (m : ℝ) / ((m : ℝ) + 1) * (1 + (24 / 49 - 8 / (m : ℝ)) / 5) ≤
      (m : ℝ) * x ^ 2 * (1 - (m : ℝ) * a / ((m : ℝ) + 1))) ∧
    (lambda m a ∈ Set.Icc (1) (5) →
      1 + 33 / (m : ℝ) < (m : ℝ) / ((m : ℝ) + 1) * (1 + 6 / 25 - 24 / (m : ℝ)) ∧
      (m : ℝ) / ((m : ℝ) + 1) * (1 + 6 / 25 - 24 / (m : ℝ)) ≤
      (m : ℝ) * x ^ 2 * (1 - (m : ℝ) * a / ((m : ℝ) + 1))) ∧
    (lambda m a ∈ Set.Icc (5) (10) →
      1 + 33 / (m : ℝ) < (m : ℝ) / ((m : ℝ) + 1) * (6 * (7 / 12) ^ 2) ∧
      (m : ℝ) / ((m : ℝ) + 1) * (6 * (7 / 12) ^ 2) ≤
      (m : ℝ) * x ^ 2 * (1 - (m : ℝ) * a / ((m : ℝ) + 1))) ∧
    (lambda m a ∈ Set.Icc (10) (25) →
      1 + 51 / (m : ℝ) + 1 / 4 < (m : ℝ) / ((m : ℝ) + 1) * (11 * (231 / 512) ^ 2) ∧
      (m : ℝ) / ((m : ℝ) + 1) * (11 * (231 / 512) ^ 2) ≤
      (m : ℝ) * x ^ 2 * (1 - (m : ℝ) * a / ((m : ℝ) + 1))) ∧
    (lambda m a ∈ Set.Icc (25) (49) →
      1 + 62 / (m : ℝ) + 2 < (m : ℝ) / ((m : ℝ) + 1) * (26 * (207 / 512) ^ 2) ∧
      (m : ℝ) / ((m : ℝ) + 1) * (26 * (207 / 512) ^ 2) ≤
      (m : ℝ) * x ^ 2 * (1 - (m : ℝ) * a / ((m : ℝ) + 1))) :=
  ra04_scaled_lower hm ha ha1 hx0 hx1 hr

/-- The whole [1/5,2/5) strip, not a sampled point. -/
example {m : ℕ} {a x : ℝ} (hm : 256 ≤ m)
    (ha : 0 < a) (ha1 : a < 1) (hx0 : -1 ≤ x) (hx1 : x ≤ 1)
    (hr : RawPolar m a x)
    (hl0 : 1 / 5 ≤ lambda m a) (hl1 : lambda m a < 2 / 5) :
    (m : ℝ) * x ^ 2 * ((1 - 2 * a * x + a ^ 2) ^ ((m : ℝ) / 2) +
      (m : ℝ) * a ^ 2 * ∫ t in (0 : ℝ)..1,
        t * (1 - 2 * a * x * t + a ^ 2 * t ^ 2) ^ (((m : ℝ) - 1) / 2)) < 1 + 18 / (m : ℝ) ∧
    1 + 18 / (m : ℝ) < (m : ℝ) / ((m : ℝ) + 1) * (1 + (24 / 49 - 8 / (m : ℝ)) / 5) ∧
    (m : ℝ) / ((m : ℝ) + 1) * (1 + (24 / 49 - 8 / (m : ℝ)) / 5) ≤
      (m : ℝ) * x ^ 2 * (1 - (m : ℝ) * a / ((m : ℝ) + 1)) := by
  have hl : lambda m a ∈ Set.Icc (1 / 5) 1 := ⟨hl0, by linarith⟩
  exact ⟨(ra03_scaled_upper hm ha ha1 hx0 hx1 hr).1 hl,
    (ra04_scaled_lower hm ha ha1 hx0 hx1 hr).1 hl⟩

/-- Seam lambda=1 / 5: every adjacent original band applies. -/
example {m : ℕ} {a x : ℝ} (hm : 256 ≤ m)
    (ha : 0 < a) (ha1 : a < 1) (hx0 : -1 ≤ x) (hx1 : x ≤ 1)
    (hr : RawPolar m a x)
    (hl : lambda m a = 1 / 5) :
    (m : ℝ) * x ^ 2 * ((1 - 2 * a * x + a ^ 2) ^ ((m : ℝ) / 2) +
      (m : ℝ) * a ^ 2 * ∫ t in (0 : ℝ)..1,
        t * (1 - 2 * a * x * t + a ^ 2 * t ^ 2) ^ (((m : ℝ) - 1) / 2)) < 1 + 18 / (m : ℝ) ∧
    (1 + 18 / (m : ℝ) < (m : ℝ) / ((m : ℝ) + 1) * (1 + (24 / 49 - 8 / (m : ℝ)) / 5) ∧
      (m : ℝ) / ((m : ℝ) + 1) * (1 + (24 / 49 - 8 / (m : ℝ)) / 5) ≤
      (m : ℝ) * x ^ 2 * (1 - (m : ℝ) * a / ((m : ℝ) + 1))) := by
  exact ⟨(ra03_scaled_upper hm ha ha1 hx0 hx1 hr).1 (by rw [hl]; constructor <;> norm_num),
    (ra04_scaled_lower hm ha ha1 hx0 hx1 hr).1 (by rw [hl]; constructor <;> norm_num)⟩

/-- Seam lambda=2 / 5: every adjacent original band applies. -/
example {m : ℕ} {a x : ℝ} (hm : 256 ≤ m)
    (ha : 0 < a) (ha1 : a < 1) (hx0 : -1 ≤ x) (hx1 : x ≤ 1)
    (hr : RawPolar m a x)
    (hl : lambda m a = 2 / 5) :
    (m : ℝ) * x ^ 2 * ((1 - 2 * a * x + a ^ 2) ^ ((m : ℝ) / 2) +
      (m : ℝ) * a ^ 2 * ∫ t in (0 : ℝ)..1,
        t * (1 - 2 * a * x * t + a ^ 2 * t ^ 2) ^ (((m : ℝ) - 1) / 2)) < 1 + 18 / (m : ℝ) ∧
    (1 + 18 / (m : ℝ) < (m : ℝ) / ((m : ℝ) + 1) * (1 + (24 / 49 - 8 / (m : ℝ)) / 5) ∧
      (m : ℝ) / ((m : ℝ) + 1) * (1 + (24 / 49 - 8 / (m : ℝ)) / 5) ≤
      (m : ℝ) * x ^ 2 * (1 - (m : ℝ) * a / ((m : ℝ) + 1))) := by
  exact ⟨(ra03_scaled_upper hm ha ha1 hx0 hx1 hr).1 (by rw [hl]; constructor <;> norm_num),
    (ra04_scaled_lower hm ha ha1 hx0 hx1 hr).1 (by rw [hl]; constructor <;> norm_num)⟩

/-- Seam lambda=1: every adjacent original band applies. -/
example {m : ℕ} {a x : ℝ} (hm : 256 ≤ m)
    (ha : 0 < a) (ha1 : a < 1) (hx0 : -1 ≤ x) (hx1 : x ≤ 1)
    (hr : RawPolar m a x)
    (hl : lambda m a = 1) :
    (m : ℝ) * x ^ 2 * ((1 - 2 * a * x + a ^ 2) ^ ((m : ℝ) / 2) +
      (m : ℝ) * a ^ 2 * ∫ t in (0 : ℝ)..1,
        t * (1 - 2 * a * x * t + a ^ 2 * t ^ 2) ^ (((m : ℝ) - 1) / 2)) < 1 + 18 / (m : ℝ) ∧
    (m : ℝ) * x ^ 2 * ((1 - 2 * a * x + a ^ 2) ^ ((m : ℝ) / 2) +
      (m : ℝ) * a ^ 2 * ∫ t in (0 : ℝ)..1,
        t * (1 - 2 * a * x * t + a ^ 2 * t ^ 2) ^ (((m : ℝ) - 1) / 2)) < 1 + 33 / (m : ℝ) ∧
    (1 + 18 / (m : ℝ) < (m : ℝ) / ((m : ℝ) + 1) * (1 + (24 / 49 - 8 / (m : ℝ)) / 5) ∧
      (m : ℝ) / ((m : ℝ) + 1) * (1 + (24 / 49 - 8 / (m : ℝ)) / 5) ≤
      (m : ℝ) * x ^ 2 * (1 - (m : ℝ) * a / ((m : ℝ) + 1))) ∧
    (1 + 33 / (m : ℝ) < (m : ℝ) / ((m : ℝ) + 1) * (1 + 6 / 25 - 24 / (m : ℝ)) ∧
      (m : ℝ) / ((m : ℝ) + 1) * (1 + 6 / 25 - 24 / (m : ℝ)) ≤
      (m : ℝ) * x ^ 2 * (1 - (m : ℝ) * a / ((m : ℝ) + 1))) := by
  exact ⟨(ra03_scaled_upper hm ha ha1 hx0 hx1 hr).1 (by rw [hl]; constructor <;> norm_num),
    (ra03_scaled_upper hm ha ha1 hx0 hx1 hr).2.1 (by rw [hl]; constructor <;> norm_num),
    (ra04_scaled_lower hm ha ha1 hx0 hx1 hr).1 (by rw [hl]; constructor <;> norm_num),
    (ra04_scaled_lower hm ha ha1 hx0 hx1 hr).2.1 (by rw [hl]; constructor <;> norm_num)⟩

/-- Seam lambda=5: every adjacent original band applies. -/
example {m : ℕ} {a x : ℝ} (hm : 256 ≤ m)
    (ha : 0 < a) (ha1 : a < 1) (hx0 : -1 ≤ x) (hx1 : x ≤ 1)
    (hr : RawPolar m a x)
    (hl : lambda m a = 5) :
    (m : ℝ) * x ^ 2 * ((1 - 2 * a * x + a ^ 2) ^ ((m : ℝ) / 2) +
      (m : ℝ) * a ^ 2 * ∫ t in (0 : ℝ)..1,
        t * (1 - 2 * a * x * t + a ^ 2 * t ^ 2) ^ (((m : ℝ) - 1) / 2)) < 1 + 33 / (m : ℝ) ∧
    (1 + 33 / (m : ℝ) < (m : ℝ) / ((m : ℝ) + 1) * (1 + 6 / 25 - 24 / (m : ℝ)) ∧
      (m : ℝ) / ((m : ℝ) + 1) * (1 + 6 / 25 - 24 / (m : ℝ)) ≤
      (m : ℝ) * x ^ 2 * (1 - (m : ℝ) * a / ((m : ℝ) + 1))) ∧
    (1 + 33 / (m : ℝ) < (m : ℝ) / ((m : ℝ) + 1) * (6 * (7 / 12) ^ 2) ∧
      (m : ℝ) / ((m : ℝ) + 1) * (6 * (7 / 12) ^ 2) ≤
      (m : ℝ) * x ^ 2 * (1 - (m : ℝ) * a / ((m : ℝ) + 1))) := by
  exact ⟨(ra03_scaled_upper hm ha ha1 hx0 hx1 hr).2.1 (by rw [hl]; constructor <;> norm_num),
    (ra04_scaled_lower hm ha ha1 hx0 hx1 hr).2.1 (by rw [hl]; constructor <;> norm_num),
    (ra04_scaled_lower hm ha ha1 hx0 hx1 hr).2.2.1 (by rw [hl]; constructor <;> norm_num)⟩

/-- Seam lambda=10: every adjacent original band applies. -/
example {m : ℕ} {a x : ℝ} (hm : 256 ≤ m)
    (ha : 0 < a) (ha1 : a < 1) (hx0 : -1 ≤ x) (hx1 : x ≤ 1)
    (hr : RawPolar m a x)
    (hl : lambda m a = 10) :
    (m : ℝ) * x ^ 2 * ((1 - 2 * a * x + a ^ 2) ^ ((m : ℝ) / 2) +
      (m : ℝ) * a ^ 2 * ∫ t in (0 : ℝ)..1,
        t * (1 - 2 * a * x * t + a ^ 2 * t ^ 2) ^ (((m : ℝ) - 1) / 2)) < 1 + 33 / (m : ℝ) ∧
    (m : ℝ) * x ^ 2 * ((1 - 2 * a * x + a ^ 2) ^ ((m : ℝ) / 2) +
      (m : ℝ) * a ^ 2 * ∫ t in (0 : ℝ)..1,
        t * (1 - 2 * a * x * t + a ^ 2 * t ^ 2) ^ (((m : ℝ) - 1) / 2)) < 1 + 51 / (m : ℝ) + 1 / 4 ∧
    (1 + 33 / (m : ℝ) < (m : ℝ) / ((m : ℝ) + 1) * (6 * (7 / 12) ^ 2) ∧
      (m : ℝ) / ((m : ℝ) + 1) * (6 * (7 / 12) ^ 2) ≤
      (m : ℝ) * x ^ 2 * (1 - (m : ℝ) * a / ((m : ℝ) + 1))) ∧
    (1 + 51 / (m : ℝ) + 1 / 4 < (m : ℝ) / ((m : ℝ) + 1) * (11 * (231 / 512) ^ 2) ∧
      (m : ℝ) / ((m : ℝ) + 1) * (11 * (231 / 512) ^ 2) ≤
      (m : ℝ) * x ^ 2 * (1 - (m : ℝ) * a / ((m : ℝ) + 1))) := by
  exact ⟨(ra03_scaled_upper hm ha ha1 hx0 hx1 hr).2.1 (by rw [hl]; constructor <;> norm_num),
    (ra03_scaled_upper hm ha ha1 hx0 hx1 hr).2.2.1 (by rw [hl]; constructor <;> norm_num),
    (ra04_scaled_lower hm ha ha1 hx0 hx1 hr).2.2.1 (by rw [hl]; constructor <;> norm_num),
    (ra04_scaled_lower hm ha ha1 hx0 hx1 hr).2.2.2.1 (by rw [hl]; constructor <;> norm_num)⟩

/-- Seam lambda=25: every adjacent original band applies. -/
example {m : ℕ} {a x : ℝ} (hm : 256 ≤ m)
    (ha : 0 < a) (ha1 : a < 1) (hx0 : -1 ≤ x) (hx1 : x ≤ 1)
    (hr : RawPolar m a x)
    (hl : lambda m a = 25) :
    (m : ℝ) * x ^ 2 * ((1 - 2 * a * x + a ^ 2) ^ ((m : ℝ) / 2) +
      (m : ℝ) * a ^ 2 * ∫ t in (0 : ℝ)..1,
        t * (1 - 2 * a * x * t + a ^ 2 * t ^ 2) ^ (((m : ℝ) - 1) / 2)) < 1 + 51 / (m : ℝ) + 1 / 4 ∧
    (m : ℝ) * x ^ 2 * ((1 - 2 * a * x + a ^ 2) ^ ((m : ℝ) / 2) +
      (m : ℝ) * a ^ 2 * ∫ t in (0 : ℝ)..1,
        t * (1 - 2 * a * x * t + a ^ 2 * t ^ 2) ^ (((m : ℝ) - 1) / 2)) < 1 + 62 / (m : ℝ) + 2 ∧
    (1 + 51 / (m : ℝ) + 1 / 4 < (m : ℝ) / ((m : ℝ) + 1) * (11 * (231 / 512) ^ 2) ∧
      (m : ℝ) / ((m : ℝ) + 1) * (11 * (231 / 512) ^ 2) ≤
      (m : ℝ) * x ^ 2 * (1 - (m : ℝ) * a / ((m : ℝ) + 1))) ∧
    (1 + 62 / (m : ℝ) + 2 < (m : ℝ) / ((m : ℝ) + 1) * (26 * (207 / 512) ^ 2) ∧
      (m : ℝ) / ((m : ℝ) + 1) * (26 * (207 / 512) ^ 2) ≤
      (m : ℝ) * x ^ 2 * (1 - (m : ℝ) * a / ((m : ℝ) + 1))) := by
  exact ⟨(ra03_scaled_upper hm ha ha1 hx0 hx1 hr).2.2.1 (by rw [hl]; constructor <;> norm_num),
    (ra03_scaled_upper hm ha ha1 hx0 hx1 hr).2.2.2 (by rw [hl]; constructor <;> norm_num),
    (ra04_scaled_lower hm ha ha1 hx0 hx1 hr).2.2.2.1 (by rw [hl]; constructor <;> norm_num),
    (ra04_scaled_lower hm ha ha1 hx0 hx1 hr).2.2.2.2 (by rw [hl]; constructor <;> norm_num)⟩

/-- Seam lambda=49: every adjacent original band applies. -/
example {m : ℕ} {a x : ℝ} (hm : 256 ≤ m)
    (ha : 0 < a) (ha1 : a < 1) (hx0 : -1 ≤ x) (hx1 : x ≤ 1)
    (hr : RawPolar m a x)
    (hl : lambda m a = 49) :
    (m : ℝ) * x ^ 2 * ((1 - 2 * a * x + a ^ 2) ^ ((m : ℝ) / 2) +
      (m : ℝ) * a ^ 2 * ∫ t in (0 : ℝ)..1,
        t * (1 - 2 * a * x * t + a ^ 2 * t ^ 2) ^ (((m : ℝ) - 1) / 2)) < 1 + 62 / (m : ℝ) + 2 ∧
    (1 + 62 / (m : ℝ) + 2 < (m : ℝ) / ((m : ℝ) + 1) * (26 * (207 / 512) ^ 2) ∧
      (m : ℝ) / ((m : ℝ) + 1) * (26 * (207 / 512) ^ 2) ≤
      (m : ℝ) * x ^ 2 * (1 - (m : ℝ) * a / ((m : ℝ) + 1))) := by
  exact ⟨(ra03_scaled_upper hm ha ha1 hx0 hx1 hr).2.2.2 (by rw [hl]; constructor <;> norm_num),
    (ra04_scaled_lower hm ha ha1 hx0 hx1 hr).2.2.2.2 (by rw [hl]; constructor <;> norm_num)⟩

/-- The historical cutoff itself, with every radius 0<a<1. -/
example {a x : ℝ} (ha : 0 < a) (ha1 : a < 1) (hx0 : -1 ≤ x) (hx1 : x ≤ 1)
    (hr : RawPolar 512 a x) :
    ((1 - 2 * a * x + a ^ 2) ^ ((512 : ℝ) / 2) +
      (512 : ℝ) * a ^ 2 * ∫ t in (0 : ℝ)..1,
        t * (1 - 2 * a * x * t + a ^ 2 * t ^ 2) ^ (((512 : ℝ) - 1) / 2)) <
      (1 - (512 : ℝ) * a / ((512 : ℝ) + 1)) := by
  simpa only [Nat.cast_ofNat] using
    un08_all_a_512 (m := 512) (by omega) ha ha1 hx0 hx1 hr

/-- The historical cutoff itself, with every radius 0<a<1. -/
example {a x : ℝ} (ha : 0 < a) (ha1 : a < 1) (hx0 : -1 ≤ x) (hx1 : x ≤ 1)
    (hr : RawPolar 10000 a x) :
    ((1 - 2 * a * x + a ^ 2) ^ ((10000 : ℝ) / 2) +
      (10000 : ℝ) * a ^ 2 * ∫ t in (0 : ℝ)..1,
        t * (1 - 2 * a * x * t + a ^ 2 * t ^ 2) ^ (((10000 : ℝ) - 1) / 2)) <
      (1 - (10000 : ℝ) * a / ((10000 : ℝ) + 1)) := by
  simpa only [Nat.cast_ofNat] using
    un09_all_a_10000 (m := 10000) (by omega) ha ha1 hx0 hx1 hr

/-- The historical cutoff itself, with every radius 0<a<1. -/
example {a x : ℝ} (ha : 0 < a) (ha1 : a < 1) (hx0 : -1 ≤ x) (hx1 : x ≤ 1)
    (hr : RawPolar 100000 a x) :
    ((1 - 2 * a * x + a ^ 2) ^ ((100000 : ℝ) / 2) +
      (100000 : ℝ) * a ^ 2 * ∫ t in (0 : ℝ)..1,
        t * (1 - 2 * a * x * t + a ^ 2 * t ^ 2) ^ (((100000 : ℝ) - 1) / 2)) <
      (1 - (100000 : ℝ) * a / ((100000 : ℝ) + 1)) := by
  simpa only [Nat.cast_ofNat] using
    un10_all_a_100000 (m := 100000) (by omega) ha ha1 hx0 hx1 hr

/-- The historical cutoff itself, with every radius 0<a<1. -/
example {a x : ℝ} (ha : 0 < a) (ha1 : a < 1) (hx0 : -1 ≤ x) (hx1 : x ≤ 1)
    (hr : RawPolar 1000000 a x) :
    ((1 - 2 * a * x + a ^ 2) ^ ((1000000 : ℝ) / 2) +
      (1000000 : ℝ) * a ^ 2 * ∫ t in (0 : ℝ)..1,
        t * (1 - 2 * a * x * t + a ^ 2 * t ^ 2) ^ (((1000000 : ℝ) - 1) / 2)) <
      (1 - (1000000 : ℝ) * a / ((1000000 : ℝ) + 1)) := by
  simpa only [Nat.cast_ofNat] using
    un11_all_a_1000000 (m := 1000000) (by omega) ha ha1 hx0 hx1 hr

/-- Degree 7: original exponent is preserved. -/
example {a x : ℝ} (ha : 0 < a) (ha1 : a < 1) (hx : 0 < x) (hx1 : x ≤ 1)
    (hxa : x < a) (hax : a < 3 * x / 2) :
    ((1 - 2 * a * x + a ^ 2) ^ ((7 : ℝ) / 2) +
      (7 : ℝ) * a ^ 2 * ∫ t in (0 : ℝ)..1,
        t * (1 - 2 * a * x * t + a ^ 2 * t ^ 2) ^ (((7 : ℝ) - 1) / 2)) < 4 / ((7 : ℝ) * x ^ 2) +
      (1 + 5 * ((7 : ℝ) * x ^ 2) / 8) *
        Real.exp (-3 * ((7 : ℝ) - 1) * ((7 : ℝ) * x ^ 2) / (8 * (7 : ℝ))) := by
  simpa only [Nat.cast_ofNat] using
    (in04_middle (m := 7) (by omega) ha ha1 hx hx1 hxa hax).1

/-- Degree 8: original exponent is preserved. -/
example {a x : ℝ} (ha : 0 < a) (ha1 : a < 1) (hx : 0 < x) (hx1 : x ≤ 1)
    (hxa : x < a) (hax : a < 3 * x / 2) :
    ((1 - 2 * a * x + a ^ 2) ^ ((8 : ℝ) / 2) +
      (8 : ℝ) * a ^ 2 * ∫ t in (0 : ℝ)..1,
        t * (1 - 2 * a * x * t + a ^ 2 * t ^ 2) ^ (((8 : ℝ) - 1) / 2)) < 4 / ((8 : ℝ) * x ^ 2) +
      (1 + 5 * ((8 : ℝ) * x ^ 2) / 8) *
        Real.exp (-3 * ((8 : ℝ) - 1) * ((8 : ℝ) * x ^ 2) / (8 * (8 : ℝ))) := by
  simpa only [Nat.cast_ofNat] using
    (in04_middle (m := 8) (by omega) ha ha1 hx hx1 hxa hax).1

/-- Degree 9: relaxation begins at nine. -/
example {a x : ℝ} (ha : 0 < a) (ha1 : a < 1) (hx : 0 < x) (hx1 : x ≤ 1)
    (hxa : x < a) (hax : a < 3 * x / 2) :
    ((1 - 2 * a * x + a ^ 2) ^ ((9 : ℝ) / 2) +
      (9 : ℝ) * a ^ 2 * ∫ t in (0 : ℝ)..1,
        t * (1 - 2 * a * x * t + a ^ 2 * t ^ 2) ^ (((9 : ℝ) - 1) / 2)) < 4 / ((9 : ℝ) * x ^ 2) +
      (1 + 5 * ((9 : ℝ) * x ^ 2) / 8) * Real.exp (-((9 : ℝ) * x ^ 2) / 3) := by
  simpa only [Nat.cast_ofNat] using
    (in04_middle (m := 9) (by omega) ha ha1 hx hx1 hxa hax).2 (by omega)

#print axioms Sendov.PaperRegionCorollaries.in02_two_end
#print axioms Sendov.PaperRegionCorollaries.in04_middle
#print axioms Sendov.PaperRegionCorollaries.ne05_near
#print axioms Sendov.PaperRegionCorollaries.un04_bulk40
#print axioms Sendov.PaperRegionCorollaries.un05_bulk116
#print axioms Sendov.PaperRegionCorollaries.un08_all_a_512
#print axioms Sendov.PaperRegionCorollaries.un09_all_a_10000
#print axioms Sendov.PaperRegionCorollaries.un10_all_a_100000
#print axioms Sendov.PaperRegionCorollaries.un11_all_a_1000000
#print axioms Sendov.PaperRegionCorollaries.ra03_scaled_upper
#print axioms Sendov.PaperRegionCorollaries.ra04_scaled_lower

end Sendov.PaperRegionCorollaries.Tests
