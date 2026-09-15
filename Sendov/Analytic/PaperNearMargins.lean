import Sendov.Analytic.PaperNear

/-!
# Historical near-endpoint margins for the actual integral budget

Preserves first-origin-uniform/REPORT.md §4.2, round3 §2 and round5 §2:
`λ ≤ 1/50` gives `h/3`, `λ ≤ 1/10` gives `h/5`, and `λ ≤ 1/5`
gives `h/80`. The earlier legacy_RESULT.md `λ ≤ 1/100`, `h/3` result
is included as a corollary. These are not consequences of the weaker
`λ ≤ 2/5`, `h/1000` conclusion.

The stronger raw-polar parameter errors and the geometric endpoint bound
from `PaperNear` suffice. First move the correlated sum `f+g` to the
chosen cutoff; then elementary denominator bounds leave rational slack.
-/

namespace Sendov.PaperNearMargins

/-- Bound the first error at a fixed cutoff, uniformly in the degree. -/
lemma f_le_cutoff_bound {τ k : ℝ} (_hτ : 0 ≤ τ) (hτ7 : τ ≤ 1 / 7)
    (hk : 0 ≤ k) (hk2 : k ≤ 2 / 5) :
    PaperNear.f τ k ≤ 1 / ((1 - k / 7) * (5 / 7) * (3 + k)) := by
  have ha : 0 < 1 - k / 7 := by linarith
  have hc : 0 < 1 - 2 * τ := by linarith
  have hb : 1 - k / 7 ≤ 1 - k * τ := by nlinarith
  have hd : (5 / 7 : ℝ) ≤ 1 - 2 * τ := by linarith
  have hp := mul_le_mul hb hd (by norm_num : (0 : ℝ) ≤ 5 / 7) (by linarith)
  have hden := mul_le_mul_of_nonneg_right hp (by linarith : 0 ≤ 3 + k)
  unfold PaperNear.f PaperNear.P
  exact one_div_le_one_div_of_le (by positivity) hden

/-- Bound the second error at a fixed cutoff using `Q ≥ 1`. -/
lemma g_le_cutoff_bound {τ k : ℝ} (hτ : 0 ≤ τ) (hk : 0 ≤ k) :
    PaperNear.g τ k ≤ (4 / 27 : ℝ) * k * (3 + k) ^ 2 := by
  have hq : (1 : ℝ) ≤ PaperNear.Q τ := by
    unfold PaperNear.Q
    nlinarith [sq_nonneg τ]
  unfold PaperNear.g
  apply (div_le_iff₀ (by linarith : 0 < PaperNear.Q τ)).2
  simpa only [mul_one] using mul_le_mul_of_nonneg_left hq
    (show 0 ≤ (4 / 27 : ℝ) * k * (3 + k) ^ 2 by positivity)

/-- A reusable scalar certificate. The last hypothesis is just rational
arithmetic at the selected cutoff, not an assumption on the actual budget. -/
theorem rational_remainder_gt {τ ℓ k r : ℝ}
    (hτ : 0 ≤ τ) (hτ7 : τ ≤ 1 / 7) (hℓ : 0 ≤ ℓ) (hℓk : ℓ ≤ k)
    (hk2 : k ≤ 2 / 5)
    (hcert : r < 7 / 8 - 1 / ((1 - k / 7) * (5 / 7) * (3 + k)) -
      (4 / 27 : ℝ) * k * (3 + k) ^ 2 - 1 / 80) :
    r < 1 / (1 + τ) - (PaperNear.f τ ℓ + PaperNear.g τ ℓ) - 1 / 80 := by
  have hk : 0 ≤ k := hℓ.trans hℓk
  have hfg := PaperNear.fg_difference_lower τ ℓ k hτ hτ7 hℓ hℓk hk2
  have hf := f_le_cutoff_bound hτ hτ7 hk hk2
  have hg := g_le_cutoff_bound hτ hk
  have hbase : (7 / 8 : ℝ) ≤ 1 / (1 + τ) := by
    apply (le_div_iff₀ (by positivity : 0 < 1 + τ)).2
    linarith
  linarith

/-- Transfer any certified rational remainder to the actual raw-polar budget.
No Taylor error, chord positivity, or endpoint estimate is assumed. -/
theorem margin_of_rational {m : ℕ} {a x r : ℝ} (hm : 7 ≤ m)
    (ha0 : 0 < a) (ha1 : a < 1) (hx0 : -1 ≤ x) (hx1 : x ≤ 1)
    (hraw : PaperPolar.RawPolar m a x) (hnear : (m : ℝ) * (1 - a) ≤ 2 / 5)
    (hr : r < 1 / (1 + 1 / (m : ℝ)) -
      (PaperNear.f (1 / (m : ℝ)) (PaperPolar.lambda m a) +
       PaperNear.g (1 / (m : ℝ)) (PaperPolar.lambda m a)) - 1 / 80) :
    1 - (m : ℝ) * a / ((m : ℝ) + 1) - PaperTaylor.budget (m : ℝ) a x >
      (1 - a) * r := by
  have hm' : (7 : ℝ) ≤ m := by exact_mod_cast hm
  have hm0 : (0 : ℝ) < m := by linarith
  have hp1 : (0 : ℝ) < (m : ℝ) + 1 := by positivity
  have hh : 0 < 1 - a := by linarith
  have hc : 0 < PaperTaylor.chord a x := by
    have h := (PaperPolar.geometry hm ha0 ha1 hx0 hx1 hraw).2
    convert h using 1
    unfold PaperTaylor.chord PaperPolar.c PaperPolar.b
    ring
  have hbudget := PaperTaylor.budget_le hm' ha0 ha1 hx1 hc
  have herr := PaperNearClosure.parameter_errors hm ha0 ha1 hx0 hx1 hraw
  have hend := (div_lt_iff₀ hh).mp
    (PaperNearClosure.endpoint_term_lt hm ha0 ha1 hx0 hx1 hraw hnear)
  have he : PaperTaylor.beta a x 1 = PaperPolar.b a x := by
    simp [PaperTaylor.beta, PaperPolar.b]
  rw [he] at hbudget
  have hrem := mul_lt_mul_of_pos_left hr hh
  have hbase : 1 - (m : ℝ) * a / ((m : ℝ) + 1) - 1 / ((m : ℝ) + 1) =
      (1 - a) * (1 / (1 + 1 / (m : ℝ))) := by
    field_simp
    ring
  nlinarith only [hbudget, herr.1, herr.2, hend, hrem, hbase]

/-- Raw-polar closure from an explicit rational cutoff certificate. -/
theorem margin_of_cutoff {m : ℕ} {a x k r : ℝ} (hm : 7 ≤ m)
    (ha0 : 0 < a) (ha1 : a < 1) (hx0 : -1 ≤ x) (hx1 : x ≤ 1)
    (hraw : PaperPolar.RawPolar m a x) (hnear : (m : ℝ) * (1 - a) ≤ k)
    (hk2 : k ≤ 2 / 5)
    (hcert : r < 7 / 8 - 1 / ((1 - k / 7) * (5 / 7) * (3 + k)) -
      (4 / 27 : ℝ) * k * (3 + k) ^ 2 - 1 / 80) :
    1 - (m : ℝ) * a / ((m : ℝ) + 1) - PaperTaylor.budget (m : ℝ) a x >
      (1 - a) * r := by
  have hm' : (7 : ℝ) ≤ m := by exact_mod_cast hm
  have ht7 : 1 / (m : ℝ) ≤ (1 / 7 : ℝ) :=
    one_div_le_one_div_of_le (by norm_num) hm'
  exact margin_of_rational hm ha0 ha1 hx0 hx1 hraw (hnear.trans hk2)
    (rational_remainder_gt (by positivity) ht7
      (PaperPolar.lambda_pos (by omega : 0 < m) ha1).le hnear hk2 hcert)

/-- Original uniform thin layer: retain the strict `h/3` margin. -/
theorem near_endpoint_one_fiftieth {m : ℕ} {a x : ℝ} (hm : 7 ≤ m)
    (ha0 : 0 < a) (ha1 : a < 1) (hx0 : -1 ≤ x) (hx1 : x ≤ 1)
    (hraw : PaperPolar.RawPolar m a x) (hnear : (m : ℝ) * (1 - a) ≤ 1 / 50) :
    1 - (m : ℝ) * a / ((m : ℝ) + 1) - PaperTaylor.budget (m : ℝ) a x >
      (1 - a) / 3 := by
  simpa only [div_eq_mul_inv, one_mul] using
    margin_of_cutoff (r := 1 / 3) hm ha0 ha1 hx0 hx1 hraw hnear
      (by norm_num) (by norm_num)

/-- Round3: retain the strict `h/5` margin on the larger thin layer. -/
theorem near_endpoint_one_tenth {m : ℕ} {a x : ℝ} (hm : 7 ≤ m)
    (ha0 : 0 < a) (ha1 : a < 1) (hx0 : -1 ≤ x) (hx1 : x ≤ 1)
    (hraw : PaperPolar.RawPolar m a x) (hnear : (m : ℝ) * (1 - a) ≤ 1 / 10) :
    1 - (m : ℝ) * a / ((m : ℝ) + 1) - PaperTaylor.budget (m : ℝ) a x >
      (1 - a) / 5 := by
  simpa only [div_eq_mul_inv, one_mul] using
    margin_of_cutoff (r := 1 / 5) hm ha0 ha1 hx0 hx1 hraw hnear
      (by norm_num) (by norm_num)

/-- Round5: retain the strict `h/80` margin. -/
theorem near_endpoint_one_fifth {m : ℕ} {a x : ℝ} (hm : 7 ≤ m)
    (ha0 : 0 < a) (ha1 : a < 1) (hx0 : -1 ≤ x) (hx1 : x ≤ 1)
    (hraw : PaperPolar.RawPolar m a x) (hnear : (m : ℝ) * (1 - a) ≤ 1 / 5) :
    1 - (m : ℝ) * a / ((m : ℝ) + 1) - PaperTaylor.budget (m : ℝ) a x >
      (1 - a) / 80 := by
  simpa only [div_eq_mul_inv, one_mul] using
    margin_of_cutoff (r := 1 / 80) hm ha0 ha1 hx0 hx1 hraw hnear
      (by norm_num) (by norm_num)

/-- The precise earlier legacy_RESULT margin, inherited without weakening. -/
theorem near_endpoint_one_hundredth {m : ℕ} {a x : ℝ} (hm : 7 ≤ m)
    (ha0 : 0 < a) (ha1 : a < 1) (hx0 : -1 ≤ x) (hx1 : x ≤ 1)
    (hraw : PaperPolar.RawPolar m a x) (hnear : (m : ℝ) * (1 - a) ≤ 1 / 100) :
    1 - (m : ℝ) * a / ((m : ℝ) + 1) - PaperTaylor.budget (m : ℝ) a x >
      (1 - a) / 3 :=
  near_endpoint_one_fiftieth hm ha0 ha1 hx0 hx1 hraw (by linarith)

end Sendov.PaperNearMargins
