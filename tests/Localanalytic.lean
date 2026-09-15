import Sendov.Analytic.OriginExact
import Sendov.Analytic.LowDegree
import Sendov.Boundary

open Sendov

example (s : Multiset ℝ) (hs : ∀ b ∈ s, 0 ≤ b) :
    s.sum ^ 2 ≤ (s.card : ℝ) * (s.map (fun b => b ^ 2)).sum := by
  induction s using Quotient.inductionOn with
  | h l =>
    have h := Finset.sum_mul_sq_le_sq_mul_sq Finset.univ
      (fun _ : Fin l.length => (1 : ℝ)) l.get
    simpa [← List.sum_ofFn, List.ofFn_getElem_eq_map l (fun b : ℝ => b ^ 2)] using h

open scoped Classical in
example (s : Multiset ℂ) (hs : ∀ w ∈ s, w ≠ 0) :
    s.prod * (s.map (fun w => w⁻¹)).sum = sumEraseProd s := by
  rw [sumEraseProd, ← Multiset.sum_map_mul_left]
  refine congrArg Multiset.sum (Multiset.map_congr rfl ?_)
  intro w hw
  rw [← Multiset.prod_erase hw, mul_right_comm, mul_inv_cancel₀ (hs w hw), one_mul]

example {w : ℂ} (hw : ‖w‖ ≤ 1) :
    ‖w‖ * ‖w⁻¹ - (starRingEnd ℂ) w‖ ≤ 1 - ‖w‖ ^ 2 := by
  rcases eq_or_ne w 0 with rfl | hne
  · simp
  · have hkey : w * (w⁻¹ - (starRingEnd ℂ) w) = ((1 - ‖w‖ ^ 2 : ℝ) : ℂ) := by
      rw [mul_sub, mul_inv_cancel₀ hne, Complex.mul_conj, Complex.normSq_eq_norm_sq]
      push_cast
      rfl
    rw [← norm_mul, hkey, Complex.norm_real, Real.norm_eq_abs,
      abs_of_nonneg (sub_nonneg.2 (pow_le_one₀ (norm_nonneg w) hw))]

example {v : ℂ} (hre : v.re = 1) (hv : ‖v‖ ≤ 1) : v = 1 := by
  -- Migrate the existing scalar boundary consumer to the refined moment API.
  exact all_eq_one_of_sum_norm_sq_le_card (s := {v})
    (by simpa using pow_le_one₀ (norm_nonneg v) hv (n := 2))
    (by simp [hre]) v (by simp)

example (g f : ℂ → ℂ) : ∀ (s : Multiset ℂ), (∀ v ∈ s, ‖g v‖ ≤ 1) →
    ‖sumEraseProdC s g f‖ ≤ sumEraseProdMap s (fun v => ‖f v‖) := by
  classical
  intro s hg
  unfold sumEraseProdC sumEraseProdMap
  refine (norm_multiset_sum_le _).trans ?_
  rw [Multiset.map_map]
  refine Multiset.sum_map_le_sum_map _ _ ?_
  intro v hv
  dsimp only [Function.comp_def]
  rw [norm_mul, norm_prod_map]
  exact mul_le_of_le_one_left (prod_map_norm_nonneg _ _) (hg v hv)

example (a t : ℝ) : ∀ (q : Multiset ℂ),
    HasDerivAt (Fprod a q)
      (-(a : ℂ) * sumEraseProdC q id (fun v => 1 - (a : ℂ) * (t : ℂ) * v)) t := by
  intro q
  induction q using Multiset.induction_on with
  | empty =>
    have he : Fprod a 0 = fun _ : ℝ => (1 : ℂ) := by funext s; simp [Fprod]
    rw [he, sumEraseProdC_zero, mul_zero]
    exact hasDerivAt_const t 1
  | cons v r ih =>
    have h0 : HasDerivAt (fun s : ℝ => (s : ℂ)) 1 t := Complex.ofRealCLM.hasDerivAt
    have h1 : HasDerivAt (fun s : ℝ => 1 - (a : ℂ) * (s : ℂ) * v) (-((a : ℂ) * v)) t := by
      simpa using ((h0.const_mul (a : ℂ)).mul_const v).const_sub 1
    have hfun : Fprod a (v ::ₘ r)
        = fun s : ℝ => (1 - (a : ℂ) * (s : ℂ) * v) * Fprod a r s := by
      funext s
      simp only [Fprod, Multiset.map_cons, Multiset.prod_cons]
    rw [hfun, sumEraseProdC_cons, id_eq]
    apply (h1.mul ih).congr_deriv
    simp only [Fprod]
    ring

example {a t : ℝ} (ha0 : 0 ≤ a) (ha1 : a ≤ 1) (ht0 : 0 ≤ t) {v : ℂ}
    (hv : ‖v‖ ≤ 1) : ‖(a : ℂ) + (t : ℂ) * (1 - (a : ℂ) ^ 2) * v‖ ≤ lowX a t := by
  have hb : (0 : ℝ) ≤ 1 - a ^ 2 := by nlinarith
  have hcast : (a : ℂ) + (t : ℂ) * (1 - (a : ℂ) ^ 2) * v
      = ((a : ℝ) : ℂ) + ((t * (1 - a ^ 2) : ℝ) : ℂ) * v := by push_cast; ring
  rw [hcast]
  refine (norm_add_le _ _).trans ?_
  rw [norm_mul, Complex.norm_real, Complex.norm_real, Real.norm_eq_abs, Real.norm_eq_abs,
    abs_of_nonneg ha0, abs_of_nonneg (mul_nonneg ht0 hb)]
  simpa only [lowX, mul_comm t] using
    add_le_add_right (mul_le_of_le_one_right (mul_nonneg ht0 hb) hv) a

open Polynomial in
example (z : Multiset ℂ) :
    ((z.map (fun w => X - C w)).prod).eval 0 = (-1) ^ z.card * z.prod := by
  rw [eval_multiset_prod, Multiset.map_map]
  simpa only [Function.comp_apply, eval_sub, eval_X, eval_C, zero_sub] using prod_map_neg z

example {r x : ℝ} (hr : 0 < r) (h : r * x ≤ r) : x ≤ 1 := by
  exact (mul_le_mul_iff_right₀ hr).mp (by simpa only [mul_one] using h)

/-! Regression cases exercise the compiled declarations, including multiplicities and zeros. -/

example : (0 : Multiset ℂ).prod * ((0 : Multiset ℂ).map (fun w => w⁻¹)).sum
    = sumEraseProd 0 :=
  prod_mul_sum_inv 0 (by simp)

example :
    (2 ::ₘ 2 ::ₘ 0 : Multiset ℂ).prod *
        ((2 ::ₘ 2 ::ₘ 0 : Multiset ℂ).map (fun w => w⁻¹)).sum
      = sumEraseProd (2 ::ₘ 2 ::ₘ 0) :=
  prod_mul_sum_inv _ (by simp)

example : sumEraseProd (0 ::ₘ 1 ::ₘ 0 : Multiset ℂ) = 1 := by
  norm_num [sumEraseProd_cons]

example : sumEraseProd (0 ::ₘ 0 ::ₘ 1 ::ₘ 0 : Multiset ℂ) = 0 := by
  norm_num [sumEraseProd_cons]

example : ‖sumEraseProd (0 ::ₘ 1 ::ₘ 0 : Multiset ℂ)‖ ≤ 1 :=
  sumEraseProd_norm_le_one _ (by simp) (by simp)

example : ‖sumEraseProd (1 ::ₘ 0 ::ₘ 0 : Multiset ℂ)‖ ≤ 1 :=
  sumEraseProd_norm_le_one _ (by simp) (by simp)

example :
    ((0 ::ₘ 1 ::ₘ 0 : Multiset ℂ).map (fun z => ‖z‖)).prod *
        ((0 ::ₘ 1 ::ₘ 0 : Multiset ℂ).map (fun z => ‖z⁻¹ - (starRingEnd ℂ) z‖)).sum
      ≤ 1 - (((0 ::ₘ 1 ::ₘ 0 : Multiset ℂ).map (fun z => ‖z‖)).prod) ^ 2 :=
  defect _ (by simp)

example (s : Multiset ℝ) (hs : ∀ b ∈ s, 0 ≤ b) :
    s.sum ^ 2 ≤ (s.card : ℝ) * (s.map (fun b => b ^ 2)).sum :=
  sq_sum_le_card_mul_sum_sq s hs

example : (0 : Multiset ℝ).sum ^ 2 ≤ ((0 : Multiset ℝ).card : ℝ) *
    ((0 : Multiset ℝ).map (fun b => b ^ 2)).sum :=
  sq_sum_le_card_mul_sum_sq 0 (by simp)

example : (2 + 2 : ℝ) ^ 2 ≤ 2 * (2 ^ 2 + 2 ^ 2) := by
  simpa using sq_sum_le_card_mul_sum_sq (2 ::ₘ 2 ::ₘ 0) (by simp)

example :
    sumEraseProdMap (1 ::ₘ 1 ::ₘ 0 : Multiset ℂ) (fun _ => 2)
      = ((1 ::ₘ 1 ::ₘ 0 : Multiset ℂ).map (fun _ => (2 : ℝ))).esymm 1 := by
  simpa using sumEraseProdMap_eq_esymm (1 ::ₘ 1 ::ₘ 0 : Multiset ℂ)
    (fun _ => 2) (by simp)

example :
    ‖sumEraseProdC (1 ::ₘ 1 ::ₘ 0) (fun _ => 1) (fun _ => 0)‖
      ≤ sumEraseProdMap (1 ::ₘ 1 ::ₘ 0 : Multiset ℂ) (fun _ => ‖(0 : ℂ)‖) :=
  norm_sumEraseProdC_le (fun _ => 1) (fun _ => 0) (1 ::ₘ 1 ::ₘ 0) (by simp)

example (a t : ℝ) : HasDerivAt (Fprod a 0) 0 t := by
  simpa using hasDerivAt_Fprod a t 0

example : HasDerivAt (Fprod 1 (1 ::ₘ 1 ::ₘ 0)) 0 1 := by
  simpa [sumEraseProdC_cons] using hasDerivAt_Fprod 1 1 (1 ::ₘ 1 ::ₘ 0)

example : ‖sumEraseProd (0 ::ₘ 0 : Multiset ℂ)‖ ≤ 2 := by
  simpa [show (2 : ℝ) - 1 = 1 by norm_num] using
    Jsum_estimate (n := 2) (a := 2) (x := 1) (y := 0)
    (z := 0 ::ₘ 0) (q := 1 ::ₘ 0)
    (by decide) (by simp) (by simp) (by simp) (by norm_num) (by norm_num)

example :
    ‖(1 ::ₘ 0 : Multiset ℂ).prod * sumEraseProd (1 ::ₘ 0)
        - ((3 : ℂ) * (2 - 1) - 2 * (1 + 0 * Complex.I)) *
          ((1 ::ₘ 0 : Multiset ℂ).prod * (1 ::ₘ 0 : Multiset ℂ).prod)‖
      ≤ (2 : ℝ) / (2 - 1) *
        (1 - (‖(1 ::ₘ 0 : Multiset ℂ).prod‖ * ‖(1 ::ₘ 0 : Multiset ℂ).prod‖) ^ 2) :=
  Jsum_estimate (n := 2) (a := 3) (x := 1) (y := 0)
    (z := 1 ::ₘ 0) (q := 1 ::ₘ 0)
    (by decide) (by simp) (by simp) (by simp) (by norm_num) (by norm_num)

example : (0 : Multiset ℝ).prod ≤
    ((0 : Multiset ℝ).sum / (0 : Multiset ℝ).card) ^ (0 : Multiset ℝ).card :=
  Sendov.Multiset.prod_le_mean_pow 0 (by simp)

example (k : ℕ) (hk : 0 < k) :
    (Multiset.replicate k (0 : ℝ)).esymm (k - 1)
      ≤ k * ((Multiset.replicate k (0 : ℝ)).sum / k) ^ (k - 1) := by
  simpa using Sendov.Multiset.esymm_card_pred_le (Multiset.replicate k (0 : ℝ))
    (by
      intro b hb
      obtain ⟨_, rfl⟩ := Multiset.mem_replicate.mp hb
      exact le_rfl)
    (by
      intro h
      have hc := congrArg Multiset.card h
      simp only [Multiset.card_replicate, Multiset.card_zero] at hc
      omega)

example {a : ℝ} (ha0 : 0 < a) (ha1 : a < 1) :
    ∀ m ∈ Finset.Icc 1 4, lowJ m a < 1 := by
  intro m hm
  exact lowJ_lt_one ha0 ha1 (Finset.mem_Icc.mp hm).1 (Finset.mem_Icc.mp hm).2

example (t : ℝ) (ht : 0 ≤ t) : ‖(1 : ℂ) + (t : ℂ) * (1 - (1 : ℂ) ^ 2)‖ ≤ lowX 1 t := by
  simpa using norm_le_lowX (a := 1) (v := 1) (by norm_num) (by norm_num) ht (by norm_num)

example : 2 * (1 : ℝ) * 5 / (5 - 1) ≤ ‖Worigin 5 1 1 0‖ :=
  grow (by decide) (by norm_num) (by norm_num)

example :
    ((1 ::ₘ 0 : Multiset ℂ).map (fun v => v.re)).sum = (2 - 1 : ℝ) * 1
      ∧ (1 : ℝ) ^ 2 + 0 ^ 2 ≤ 1 :=
  xy_bounds (n := 2) (by decide) (by simp) (by simp) (by norm_num)

example : (1 : ℝ) / 2 ≤ (((1 : ℂ) - (-1))⁻¹).re :=
  half_le_re_inv_one_sub (by norm_num) (by norm_num)

open Polynomial in
example {p : ℂ[X]} (hdeg : p.natDegree = 2)
    (hroots : ∀ w ∈ p.roots, ‖w‖ ≤ 1) (hp1 : p.eval 1 = 0) :
    ∃ ζ : ℂ, (derivative p).eval ζ = 0 ∧ ‖ζ - 1‖ ≤ 1 :=
  sendov_boundary_one (by decide) hdeg hroots hp1

open Polynomial in
example {p : ℂ[X]} (hdeg : p.natDegree = 1)
    (hroots : ∀ w ∈ p.roots, ‖w‖ ≤ 1) {a : ℂ} (hpa : p.eval a = 0) :
    ∃ z : Multiset ℂ, z.card = 0 ∧ (∀ w ∈ z, ‖w‖ ≤ 1) ∧
      p = C p.leadingCoeff * ((X - C a) * (z.map (fun w => X - C w)).prod) :=
  exists_root_multiset (by decide) hdeg hroots hpa

open Polynomial in
example : ∃ ζ : ℂ, (derivative ((X - C 1) ^ 2 : ℂ[X])).eval ζ = 0 ∧ ‖ζ - 1‖ < 1 := by
  refine ⟨1, ?_, by norm_num⟩
  simp [derivative_pow, derivative_sub, derivative_X]
