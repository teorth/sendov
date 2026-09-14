import tests.PaperConjugateDI03
import tests.PaperConjugateDI04
import tests.PaperConjugateDI05
import tests.PaperConjugateDI06
import tests.PaperConjugateDI07

/-!
# Exact centered conjugate diagnostics DI03–DI07

All five requested families, including both m=100 cases, satisfy the literal
PAPER square-root budget with their actual mean and centered variance. Every
finite H endpoint is retained in the certificates. `K` is the complex product
integral, not the AM–GM relaxation; `J` is the actual first-origin integral.
These are finite diagnostic data, not Sendov polynomial counterexamples and
not all-parameter theorems for any of the degrees.

The generated modules share `Sendov.Analytic.PaperConjugate`. Each endpoint is
checked by one binomial recurrence; each C*H term is checked by a squared
rational inequality. The generator and JSON are untrusted convenience data:
Lean proves the statements without reading either file.
-/
noncomputable section
namespace Sendov.PaperConjugate.Budgets
open PaperCentered PaperCenteredBound

/-- A single acceptance contract, bound throughout to the same actual family. -/
def Accepted (m : ℕ) (a x : ℝ) : Prop :=
  let q := family (m / 2) x
  0 < a ∧ a < 1 ∧ q.card = m ∧
  (∀ w ∈ q, ‖w‖ = 1) ∧
  q.sum / q.card = (x : ℂ) ∧
  variance (q.map (fun w => w - (x : ℂ))) = 1 - x ^ 2 ∧
  1 < ‖K (m / 2) a x‖ ∧
  majorant_Efin (q.map (fun w => w - (x : ℂ))) (x : ℂ) ((a : ℂ) * x) +
    Gamma (q.map (fun w => w - (x : ℂ))) (x : ℂ) < 1 - a * ‖(x : ℂ)‖ ∧
  1 < ‖J (m / 2) a x‖

theorem DI03_closed : Accepted 6 (9 / 10) (49 / 50) :=
  ⟨by norm_num, by norm_num, DI03.cardinality, DI03.pointwise,
    DI03.mean, DI03.actual_variance, DI03.full_polar, DI03.paper_budget,
    DI03.norm_J_gt_one⟩

theorem DI04_closed : Accepted 8 (99 / 100) (497 / 500) :=
  ⟨by norm_num, by norm_num, DI04.cardinality, DI04.pointwise,
    DI04.mean, DI04.actual_variance, DI04.full_polar, DI04.paper_budget,
    DI04.norm_J_gt_one⟩

theorem DI05_closed : Accepted 20 (9 / 10) (83 / 100) :=
  ⟨by norm_num, by norm_num, DI05.cardinality, DI05.pointwise,
    DI05.mean, DI05.actual_variance, DI05.full_polar, DI05.paper_budget,
    DI05.norm_J_gt_one⟩

theorem DI06_closed : Accepted 100 (9 / 10) (61 / 100) :=
  ⟨by norm_num, by norm_num, DI06.cardinality, DI06.pointwise,
    DI06.mean, DI06.actual_variance, DI06.full_polar, DI06.paper_budget,
    DI06.norm_J_gt_one⟩

theorem DI07_closed : Accepted 100 (99 / 100) (22 / 25) :=
  ⟨by norm_num, by norm_num, DI07.cardinality, DI07.pointwise,
    DI07.mean, DI07.actual_variance, DI07.full_polar, DI07.paper_budget,
    DI07.norm_J_gt_one⟩

/-- The exact input registry. Its length and all entries are checked below. -/
def datasets : List (ℕ × ℚ × ℚ) :=
  [(6, 9 / 10, 49 / 50), (8, 99 / 100, 497 / 500),
   (20, 9 / 10, 83 / 100), (100, 9 / 10, 61 / 100),
   (100, 99 / 100, 22 / 25)]

theorem dataset_count : datasets.length = 5 := rfl

theorem all_datasets_closed :
    ∀ d ∈ datasets, Accepted d.1 (d.2.1 : ℝ) (d.2.2 : ℝ) := by
  intro d hd
  simp only [datasets, List.mem_cons, List.not_mem_nil, or_false] at hd
  rcases hd with rfl | rfl | rfl | rfl | rfl
  · simpa only [Rat.cast_div, Rat.cast_ofNat] using DI03_closed
  · simpa only [Rat.cast_div, Rat.cast_ofNat] using DI04_closed
  · simpa only [Rat.cast_div, Rat.cast_ofNat] using DI05_closed
  · simpa only [Rat.cast_div, Rat.cast_ofNat] using DI06_closed
  · simpa only [Rat.cast_div, Rat.cast_ofNat] using DI07_closed

-- Explicit rational variances, not a freely supplied variance parameter.
example : variance (DI03.q.map (fun w => w - (DI03.x : ℂ))) = 99 / 2500 := by
  rw [DI03.actual_variance]; norm_num [DI03.x]
example : variance (DI04.q.map (fun w => w - (DI04.x : ℂ))) = 2991 / 250000 := by
  rw [DI04.actual_variance]; norm_num [DI04.x]
example : variance (DI05.q.map (fun w => w - (DI05.x : ℂ))) = 3111 / 10000 := by
  rw [DI05.actual_variance]; norm_num [DI05.x]
example : variance (DI06.q.map (fun w => w - (DI06.x : ℂ))) = 6279 / 10000 := by
  rw [DI06.actual_variance]; norm_num [DI06.x]
example : variance (DI07.q.map (fun w => w - (DI07.x : ℂ))) = 141 / 625 := by
  rw [DI07.actual_variance]; norm_num [DI07.x]

#print axioms DI03_closed
#print axioms DI04_closed
#print axioms DI05_closed
#print axioms DI06_closed
#print axioms DI07_closed
#print axioms all_datasets_closed
end Sendov.PaperConjugate.Budgets
