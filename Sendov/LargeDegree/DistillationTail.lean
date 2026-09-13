import Sendov.Common.DistillationFactors

/-!
# Real-degree monotonicity and bounded growth of distillation components

New Lean adaptation of Senjian An, *Proof Distillation for Sendov's Conjecture*,
revision e8ae601491ec171ab4f7f8456113dd6a047aa85d, lines 898--950.
Paper: CC BY 4.0, https://creativecommons.org/licenses/by/4.0/ .
The m=61 reduction uses the actual dependence of the rational denominator
on alpha and the stronger decay from `cubicPolarEnvelope 17 <= (21/22)^4`.
The rational component is antitone already from 55; a finite-interval growth
lemma retains exponential decay even when a power component is not antitone.
Finite base certificates remain separate. No raw scalar value at alpha zero
is identified with a continuous extension.
-/

namespace Sendov

private lemma slope_mul {f g : ℝ → ℝ} {x u v : ℝ}
    (hf : HasDerivAt f (f x * u) x) (hg : HasDerivAt g (g x * v) x) :
    HasDerivAt (fun y => f y * g y) ((f x * g x) * (u + v)) x := by
  convert! hf.mul hg using 1
  ring

private lemma slope_div {f g : ℝ → ℝ} {x u v : ℝ}
    (hf : HasDerivAt f (f x * u) x) (hg : HasDerivAt g (g x * v) x)
    (hg0 : g x ≠ 0) :
    HasDerivAt (fun y => f y / g y) ((f x / g x) * (u - v)) x := by
  convert! hf.div hg hg0 using 1
  field_simp

private lemma slope_pow {f : ℝ → ℝ} {x u : ℝ} (n : ℕ)
    (hf : HasDerivAt f (f x * u) x) :
    HasDerivAt (fun y => f y ^ n) (f x ^ n * (n * u)) x := by
  convert! hf.pow n using 1
  cases n with
  | zero => simp
  | succ n => simp only [Nat.add_sub_cancel, pow_succ, Nat.cast_add, Nat.cast_one]; ring

private lemma slope_linear (x c : ℝ) (h : x + c ≠ 0) :
    HasDerivAt (fun y : ℝ => y + c) ((x + c) * (1 / (x + c))) x := by
  convert! (hasDerivAt_id' x).add_const c using 1
  exact mul_one_div_cancel h

private lemma tail_antitone {f f' : ℝ → ℝ} {K : ℝ}
    (hf : ∀ x : ℝ, K ≤ x → HasDerivAt f (f' x) x)
    (hn : ∀ x : ℝ, K ≤ x → f' x ≤ 0) : AntitoneOn f (Set.Ici K) := by
  exact antitoneOn_of_hasDerivWithinAt_nonpos (convex_Ici _)
    (fun x hx => (hf x hx).continuousAt.continuousWithinAt)
    (fun x hx => (hf x (interior_subset hx)).hasDerivWithinAt)
    (fun x hx => hn x (interior_subset hx))

lemma distillEBudget_antitone_on {K : ℝ} (hK : 0 < K) :
    AntitoneOn distillEBudget (Set.Ici K) := by
  intro m hm n _ hmn
  change K ≤ m at hm
  dsimp only [distillEBudget]
  apply add_le_add le_rfl
  exact div_le_div_of_nonneg_left (by norm_num)
    (by linarith : 0 < 12 * m) (by linarith)

lemma distillEBudget_antitone : AntitoneOn distillEBudget (Set.Ici 61) :=
  distillEBudget_antitone_on (by norm_num)

lemma cubicPolarEnvelope_le_five_sixths {α : ℝ} (hα : 0 ≤ α) (hα17 : α ≤ 17) :
    cubicPolarEnvelope α ≤ 5 / 6 := by
  calc
    cubicPolarEnvelope α ≤ cubicPolarEnvelope 17 := cubicPolarEnvelope_mono hα hα17
    _ ≤ 5 / 6 := by norm_num [cubicPolarEnvelope]

lemma cubicPolarEnvelope_le_decay_base {α : ℝ} (hα : 0 ≤ α) (hα17 : α ≤ 17) :
    cubicPolarEnvelope α ≤ (21 / 22) ^ 4 :=
  (cubicPolarEnvelope_mono hα hα17).trans (by norm_num [cubicPolarEnvelope])

lemma distillNode_antitone_degree_on {K α : ℝ} (hK : 0 < K) (hα : 0 ≤ α) :
    AntitoneOn (fun m => distillNode m α) (Set.Ici K) := by
  intro m hm n _ hmn
  change K ≤ m at hm
  dsimp only [distillNode]
  apply add_le_add le_rfl
  exact div_le_div_of_nonneg_left (by positivity : 0 ≤ 12 * α)
    (by linarith : 0 < 25 * m) (by linarith)

lemma distillNode_antitone_degree {α : ℝ} (hα : 0 ≤ α) :
    AntitoneOn (fun m => distillNode m α) (Set.Ici 61) :=
  distillNode_antitone_degree_on (by norm_num) hα

lemma distillNode_lt_four_fifths {m α : ℝ} (hm : 61 ≤ m)
    (hα : 0 ≤ α) (hα17 : α ≤ 17) : distillNode m α < 4 / 5 := by
  have he := cubicPolarEnvelope_le_five_sixths hα hα17
  have ht : 12 * α / (25 * m) ≤ 204 / 1525 := by
    apply (div_le_iff₀ (by linarith : 0 < 25 * m)).mpr
    linarith
  unfold distillNode
  linarith only [he, ht]

private lemma kappa_slope {m α : ℝ} (hm : 34 < m) (hα17 : α ≤ 17) :
    HasDerivAt (fun x => distillKappa x α)
      (distillKappa m α * (1 / (m - 1) + 1 / (m + 1) - 1 / m +
        2 / (m - 2 * α))) m := by
  have hm0 : m ≠ 0 := by linarith
  have hm1 : m - 1 ≠ 0 := by linarith
  have hmp1 : m + 1 ≠ 0 := by linarith
  have hma : m - 2 * α ≠ 0 := by linarith
  have h1 := slope_linear m (-1) (by linarith)
  have h2 := slope_linear m 1 hmp1
  have h3 := slope_linear m 0 (by simpa using hm0)
  have h4 := slope_pow 2 (slope_linear m (-2 * α) (by linarith))
  have hc := hasDerivAt_const m (distillRatio α / 4)
  have hc' : HasDerivAt (fun _ : ℝ => distillRatio α / 4)
      (distillRatio α / 4 * 0) m := by simpa using hc
  convert! slope_mul (slope_mul (slope_div (slope_mul h1 h2) h3
    (by simpa using hm0)) hc') h4 using 1
  · funext x
    dsimp [distillKappa]
    ring
  · dsimp [distillKappa]
    ring

private lemma kappa_slope_le {K m α : ℝ} (hK : 34 < K) (hm : K ≤ m)
    (hα17 : α ≤ 17) :
    1 / (m - 1) + 1 / (m + 1) - 1 / m + 2 / (m - 2 * α) ≤
      1 / (K - 1) + 2 / (K - 34) := by
  have h1 : 1 / (m - 1) ≤ 1 / (K - 1) :=
    div_le_div_of_nonneg_left (by norm_num) (by linarith) (by linarith)
  have h2 : 1 / (m + 1) ≤ 1 / m :=
    div_le_div_of_nonneg_left (by norm_num) (by linarith) (by linarith)
  have h3 : 2 / (m - 2 * α) ≤ 2 / (K - 34) :=
    div_le_div_of_nonneg_left (by norm_num) (by linarith) (by linarith)
  linarith only [h1, h2, h3]

/-- On a bounded degree interval, a small positive logarithmic slope consumes
only a linear budget. Unlike an infinite antitone tail, this permits growth. -/
lemma distillKappa_rpow_interval {K U m α z q ε : ℝ} (n : ℕ)
    (hK : 34 < K) (hm : m ∈ Set.Icc K U) (hε : 0 ≤ ε)
    (hroom : ε * (U - K) < 1)
    (hdecay : 1 / (K - 1) + 2 / (K - 34) ≤ n * (1 - q) / 2 + ε)
    (hα : 0 ≤ α) (hα17 : α ≤ 17) (hz : 0 ≤ z) (hq : 0 < q)
    (hzq : z ≤ q ^ n) :
    (distillKappa m α * z ^ ((m - 3) / 2)) * (1 - ε * (U - K)) ≤
      distillKappa K α * z ^ ((K - 3) / 2) := by
  rcases hz.eq_or_lt with rfl | hz
  · have hm' : (m - 3) / 2 ≠ 0 := by have := hm.1; linarith
    have hK' : (K - 3) / 2 ≠ 0 := by linarith
    simp [Real.zero_rpow hm', Real.zero_rpow hK']
  let f := fun t => distillKappa t α * z ^ ((t - 3) / 2)
  let w := fun t => 1 - ε * (t - K)
  have hf0 (t : ℝ) (ht : K ≤ t) : 0 ≤ f t :=
    mul_nonneg (distillKappa_nonneg (by linarith) hα) (Real.rpow_nonneg hz.le _)
  have hw (t : ℝ) (ht : t ≤ U) : 0 ≤ w t := by
    have := mul_le_mul_of_nonneg_left (sub_le_sub_right ht K) hε
    dsimp [w]
    linarith
  have hlog : Real.log z / 2 ≤ -(n * (1 - q) / 2) := by
    have hl := Real.log_le_log hz hzq
    rw [Real.log_pow] at hl
    have hqlog := mul_le_mul_of_nonneg_left (Real.log_le_sub_one_of_pos hq)
      (Nat.cast_nonneg n : (0 : ℝ) ≤ n)
    linarith
  let s := fun t => 1 / (t - 1) + 1 / (t + 1) - 1 / t +
    2 / (t - 2 * α) + Real.log z / 2
  have hs (t : ℝ) (ht : K ≤ t) : s t ≤ ε := by
    have := kappa_slope_le hK ht hα17
    dsimp [s]
    linarith
  have hd (t : ℝ) (ht : K ≤ t) :
      HasDerivAt (fun t => f t * w t) (f t * (s t * w t - ε)) t := by
    have hp : HasDerivAt (fun t : ℝ => z ^ ((t - 3) / 2))
        (z ^ ((t - 3) / 2) * (Real.log z / 2)) t := by
      convert! (hasDerivAt_const t z).rpow
        (((hasDerivAt_id' t).sub_const 3).div_const 2) hz using 1
      ring
    have hf := slope_mul (kappa_slope (hK.trans_le ht) hα17) hp
    have hw' := (((hasDerivAt_id' t).sub_const K).const_mul ε).const_sub 1
    convert! hf.mul hw' using 1
    dsimp [f, w, s]
    ring
  have hanti : AntitoneOn (fun t => f t * w t) (Set.Icc K U) := by
    apply antitoneOn_of_hasDerivWithinAt_nonpos (convex_Icc _ _)
      (fun t ht => (hd t ht.1).continuousAt.continuousWithinAt)
      (fun t ht => (hd t (interior_subset ht).1).hasDerivWithinAt)
    intro t ht
    have ht' : t ∈ Set.Icc K U := interior_subset ht
    apply mul_nonpos_of_nonneg_of_nonpos (hf0 t ht'.1)
    have hsw := mul_le_mul_of_nonneg_right (hs t ht'.1) (hw t ht'.2)
    have hprod : 0 ≤ ε * (ε * (t - K)) := by
      exact mul_nonneg hε (mul_nonneg hε (sub_nonneg.mpr ht'.1))
    dsimp [w] at *
    nlinarith
  have hstep := hanti ⟨le_rfl, hm.1.trans hm.2⟩ hm hm.1
  have hweight : 1 - ε * (U - K) ≤ w m := by
    dsimp [w]
    have := mul_le_mul_of_nonneg_left (sub_le_sub_right hm.2 K) hε
    linarith
  exact (mul_le_mul_of_nonneg_left hweight (hf0 m hm.1)).trans
    (by simpa [w, f] using hstep)

/-- A rational power cap retains stronger logarithmic decay without a log estimate
or a derivative sign as a caller premise. Since `K > 34`, the positive left side
of `hdecay` already forces `n > 0` and `q < 1`; no extra premises are needed. -/
lemma distillKappa_rpow_antitone_of_pow {K α z q : ℝ} (n : ℕ) (hK : 34 < K)
    (hdecay : 1 / (K - 1) + 2 / (K - 34) ≤ n * (1 - q) / 2)
    (hα : 0 ≤ α) (hα17 : α ≤ 17)
    (hz : 0 ≤ z) (hq : 0 < q) (hz1 : z ≤ q ^ n) :
    AntitoneOn (fun m => distillKappa m α * z ^ ((m - 3) / 2)) (Set.Ici K) := by
  rcases hz.eq_or_lt with rfl | hz
  · intro m hm n hn _
    have hm' : (m - 3) / 2 ≠ 0 := by change K ≤ m at hm; linarith
    have hn' : (n - 3) / 2 ≠ 0 := by change K ≤ n at hn; linarith
    simp only [Real.zero_rpow hm', Real.zero_rpow hn', mul_zero, le_refl]
  have hp (m : ℝ) : HasDerivAt (fun x : ℝ => z ^ ((x - 3) / 2))
      (z ^ ((m - 3) / 2) * (Real.log z / 2)) m := by
    convert! (hasDerivAt_const m z).rpow
      (((hasDerivAt_id' m).sub_const 3).div_const 2) hz using 1
    ring
  apply tail_antitone (fun m hm => slope_mul (kappa_slope (hK.trans_le hm) hα17) (hp m))
  intro m hm
  apply mul_nonpos_of_nonneg_of_nonpos
  · exact mul_nonneg (distillKappa_nonneg (by linarith) hα) (Real.rpow_nonneg hz.le _)
  · have hk := kappa_slope_le hK hm hα17
    have hl := Real.log_le_log hz hz1
    rw [Real.log_pow] at hl
    have hqlog := mul_le_mul_of_nonneg_left (Real.log_le_sub_one_of_pos hq)
      (Nat.cast_nonneg n : (0 : ℝ) ≤ n)
    linarith

/-- The original sufficient condition remains a special case. -/
lemma distillKappa_rpow_antitone_on {K α z : ℝ} (hK : 34 < K)
    (hdecay : 1 / (K - 1) + 2 / (K - 34) ≤ 1 / 12)
    (hα : 0 ≤ α) (hα17 : α ≤ 17)
    (hz : 0 ≤ z) (hz1 : z ≤ 5 / 6) :
    AntitoneOn (fun m => distillKappa m α * z ^ ((m - 3) / 2)) (Set.Ici K) :=
  distillKappa_rpow_antitone_of_pow 1 hK (by norm_num at *; exact hdecay)
    hα hα17 hz (by norm_num : (0 : ℝ) < 5 / 6) (by simpa using hz1)

private lemma kappa_rpow_antitone {α z : ℝ} (hα : 0 ≤ α) (hα17 : α ≤ 17)
    (hz : 0 ≤ z) (hz1 : z ≤ (21 / 22) ^ 4) :
    AntitoneOn (fun m => distillKappa m α * z ^ ((m - 3) / 2)) (Set.Ici 61) :=
  distillKappa_rpow_antitone_of_pow 4 (by norm_num) (by norm_num)
    hα hα17 hz (by norm_num : (0 : ℝ) < 21 / 22) hz1

/-- Real-degree antitonicity; the node itself also decreases with the degree. -/
lemma distillT1_antitone {α : ℝ} (hα : 0 ≤ α) (hα17 : α ≤ 17) :
    AntitoneOn (fun m => distillT1 m α) (Set.Ici 61) := by
  intro m hm n hn hmn
  have hm' : 61 ≤ m := hm
  have hn' : 61 ≤ n := hn
  have hz := distillNode_pos (by linarith : 0 < m) hα
  have hz1 : distillNode m α ≤ (21 / 22) ^ 4 :=
    (distillNode_lt_four_fifths hm' hα hα17).le.trans (by norm_num)
  have hpow := Real.rpow_le_rpow (distillNode_pos (by linarith : 0 < n) hα).le
    (distillNode_antitone_degree hα hm hn hmn) (by linarith : 0 ≤ (n - 3) / 2)
  have hstep := (mul_le_mul_of_nonneg_left hpow
    (distillKappa_nonneg (by linarith) hα)).trans
      (kappa_rpow_antitone hα hα17 hz.le hz1 hm hn hmn)
  have := mul_le_mul_of_nonneg_left hstep (by norm_num : (0 : ℝ) ≤ 259 / 3125)
  simpa only [distillT1, mul_assoc] using this

/-- The zero-alpha case is included by the zero-base real-power case. -/
lemma distillT2_antitone {α : ℝ} (hα : 0 ≤ α) (hα17 : α ≤ 17) :
    AntitoneOn (fun m => distillT2 m α) (Set.Ici 61) := by
  intro m hm n hn hmn
  have hstep := kappa_rpow_antitone hα hα17 (cubicPolarEnvelope_nonneg hα)
    (cubicPolarEnvelope_le_decay_base hα hα17) hm hn hmn
  have := mul_le_mul_of_nonneg_left hstep (by norm_num : (0 : ℝ) ≤ 421 / 3125)
  simpa only [distillT2, mul_assoc] using this

lemma distillT2_zero {m : ℝ} (hm : 61 ≤ m) : distillT2 m 0 = 0 := by
  have hs : (m - 3) / 2 ≠ 0 := by linarith
  simp [distillT2, cubicPolarEnvelope, Real.zero_rpow hs]

private def tailP (m α : ℝ) : ℝ :=
  7 * m ^ 4 - 30 * α * m ^ 3 - (8 * α ^ 2 + 96 * α + 105) * m ^ 2 +
    (90 * α - 128 * α ^ 2) * m - 360 * α ^ 2

private lemma tailP_pos {m α : ℝ} (hm : 55 ≤ m) (hα : 0 ≤ α) (hα10 : α ≤ 10) :
    0 < tailP m α := by
  have hm0 : 0 ≤ m := by linarith
  have hx : 0 ≤ m - 55 := by linarith
  have hgap : 0 ≤ 10 - α := by linarith
  have hid : tailP m α =
      7 * (m - 55) ^ 4 + 1240 * (m - 55) ^ 3 + 75685 * (m - 55) ^ 2 +
        1718950 * (m - 55) + 7809750 +
      (10 - α) * (α * (8 * m ^ 2 + 128 * m + 360) +
        30 * m ^ 3 + 176 * m ^ 2 + 1190 * m + 3600) := by
    dsimp [tailP]
    ring
  rw [hid]
  positivity

private noncomputable def tailQ (m α d : ℝ) : ℝ :=
  d * tailP m α / 7 + (21 / 25 - d) * (4 * α / 7) *
    ((3 * m - 2 * α) * m ^ 2 + 32 * (m - α) * m + (75 * m - 90 * α))

private lemma tailQ_cap_pos {m α : ℝ} (hm : 55 ≤ m) (hα : 0 ≤ α)
    (hα17 : α ≤ 17) : 0 < tailQ m α (39 / 100) := by
  have hm0 : 0 ≤ m := by linarith
  have hx : 0 ≤ m - 55 := by linarith
  have hgap : 0 ≤ 17 - α := by linarith
  have hid : tailQ m α (39 / 100) =
      (39 / 100) * (m - 55) ^ 4 + (141 / 2) * (m - 55) ^ 3 +
        (431967 / 100) * (m - 55) ^ 2 + (4544763 / 50) * (m - 55) +
        160893 / 2 +
      (17 - α) * (3 / 50) * (16 * α * m ^ 2 + 256 * α * m + 720 * α +
        15 * m ^ 3 + 224 * m ^ 2 + 3947 * m + 12240) := by
    dsimp [tailQ, tailP]
    ring
  rw [hid]
  positivity

private lemma tailQ_pos {m α d : ℝ} (hm : 55 ≤ m) (hα : 0 ≤ α)
    (hα17 : α ≤ 17) (hd : 0 < d) (hd1 : d ≤ 21 / 25)
    (hdα : 10 ≤ α → d ≤ 39 / 100) : 0 < tailQ m α d := by
  have hm0 : 0 ≤ m := by linarith
  have h1 : 0 ≤ 3 * m - 2 * α := by linarith
  have h2 : 0 ≤ m - α := by linarith
  have h3 : 0 ≤ 75 * m - 90 * α := by linarith
  have h4 : 0 ≤ 21 / 25 - d := by linarith
  by_cases hα10 : α ≤ 10
  · unfold tailQ
    exact add_pos_of_pos_of_nonneg (div_pos (mul_pos hd (tailP_pos hm hα hα10))
      (by norm_num)) (by positivity)
  · have hd2 : 0 ≤ 39 / 100 - d := sub_nonneg.mpr (hdα (by linarith))
    have hid : tailQ m α d = d * (100 / 39 * tailQ m α (39 / 100)) +
        (39 / 100 - d) * (16 * α / 13) *
          ((3 * m - 2 * α) * m ^ 2 + 32 * (m - α) * m + (75 * m - 90 * α)) := by
      dsimp [tailQ, tailP]
      ring
    rw [hid]
    exact add_pos_of_pos_of_nonneg
      (mul_pos hd (mul_pos (by norm_num) (tailQ_cap_pos hm hα hα17))) (by positivity)

private noncomputable def tailRational (m α d : ℝ) : ℝ :=
  m ^ 3 * (m - 2 * α) ^ 2 / ((m + 3) * (m + 5) * (d * m - 12 * α / 25) ^ 4)

private lemma tail_den_pos {m α d : ℝ} (hm : 55 ≤ m) (hα17 : α ≤ 17)
    (hd : 17 / 50 ≤ d) : 0 < d * m - 12 * α / 25 := by
  have hm0 : 0 ≤ m := by linarith
  have hd0 : 0 ≤ d - 17 / 50 := by linarith
  nlinarith [mul_nonneg hd0 hm0]

private lemma rational_slope {m α d : ℝ} (hm : 55 ≤ m) (hα17 : α ≤ 17)
    (hd : 17 / 50 ≤ d) :
    HasDerivAt (fun x => tailRational x α d)
      (tailRational m α d * (3 / m + 2 / (m - 2 * α) - 1 / (m + 3) -
        1 / (m + 5) - 4 * d / (d * m - 12 * α / 25))) m := by
  have hm0 : m ≠ 0 := by linarith
  have hma : m - 2 * α ≠ 0 := by linarith
  have hm3 : m + 3 ≠ 0 := by linarith
  have hm5 : m + 5 ≠ 0 := by linarith
  have hc : d * m - 12 * α / 25 ≠ 0 := (tail_den_pos hm hα17 hd).ne'
  have h1 := slope_pow 3 (slope_linear m 0 (by simpa using hm0))
  have h2 := slope_pow 2 (slope_linear m (-2 * α) (by linarith))
  have h3 := slope_linear m 3 hm3
  have h5 := slope_linear m 5 hm5
  have hd' : HasDerivAt (fun x : ℝ => d * x - 12 * α / 25)
      ((d * m - 12 * α / 25) * (d / (d * m - 12 * α / 25))) m := by
    convert! ((hasDerivAt_id' m).const_mul d).sub_const (12 * α / 25) using 1
    simp [← mul_div_assoc, hc]
  have hden := slope_mul (slope_mul h3 h5) (slope_pow 4 hd')
  convert! slope_div (slope_mul h1 h2) hden
    (mul_ne_zero (mul_ne_zero hm3 hm5) (pow_ne_zero 4 hc)) using 1
  · funext x
    dsimp [tailRational]
    ring
  · dsimp [tailRational]
    ring

private lemma rational_slope_neg {m α d : ℝ} (hm : 55 ≤ m) (hα : 0 ≤ α)
    (hα17 : α ≤ 17) (hd : 17 / 50 ≤ d) (hd1 : d ≤ 21 / 25)
    (hdα : 10 ≤ α → d ≤ 39 / 100) :
    3 / m + 2 / (m - 2 * α) - 1 / (m + 3) - 1 / (m + 5) -
      4 * d / (d * m - 12 * α / 25) < 0 := by
  have hm0 : 0 < m := by linarith
  have hma : 0 < m - 2 * α := by linarith
  have hm3 : 0 < m + 3 := by linarith
  have hm5 : 0 < m + 5 := by linarith
  have hc := tail_den_pos hm hα17 hd
  have hid : 3 / m + 2 / (m - 2 * α) - 1 / (m + 3) - 1 / (m + 5) -
      4 * d / (d * m - 12 * α / 25) =
      -tailQ m α d / (m * (m - 2 * α) * (m + 3) * (m + 5) *
        (d * m - 12 * α / 25)) := by
    generalize hdef : d * m - 12 * α / 25 = c at *
    field_simp
    rw [← hdef]
    dsimp [tailQ, tailP]
    ring
  rw [hid]
  exact div_neg_of_neg_of_pos
    (neg_neg_of_pos (tailQ_pos hm hα hα17 (by linarith) hd1 hdα))
    (by positivity)

private lemma tailRational_antitone {α d : ℝ} (hα : 0 ≤ α) (hα17 : α ≤ 17)
    (hd : 17 / 50 ≤ d) (hd1 : d ≤ 21 / 25) (hdα : 10 ≤ α → d ≤ 39 / 100) :
    AntitoneOn (fun m => tailRational m α d) (Set.Ici 55) := by
  apply tail_antitone (fun m hm => rational_slope hm hα17 hd)
  intro m hm
  have hm0 : 0 ≤ m := by linarith
  have hm3 : 0 ≤ m + 3 := by linarith
  have hm5 : 0 ≤ m + 5 := by linarith
  exact mul_nonpos_of_nonneg_of_nonpos (by unfold tailRational; positivity)
    (rational_slope_neg hm hα hα17 hd hd1 hdα).le

private lemma distillT0_eq_rational {m α : ℝ} (hm : 55 ≤ m)
    (hα : 0 ≤ α) (hα17 : α ≤ 17) :
    distillT0 m α = (24 * (3 / 5) ^ 4 * distillRatio α) *
      tailRational m α (21 / 25 - 3 / 5 * cubicPolarEnvelope α) := by
  have hm0 : m ≠ 0 := by linarith
  have hm1 : m - 1 ≠ 0 := by linarith
  have hmp1 : m + 1 ≠ 0 := by linarith
  have hm3 : m + 3 ≠ 0 := by linarith
  have hm5 : m + 5 ≠ 0 := by linarith
  have hn : 1 - distillNode m α ≠ 0 := by
    have := distillNode_lt_one (by linarith : 0 < m) hα (by linarith : α ≤ m / 2)
    linarith
  have hc : (21 / 25 - 3 / 5 * cubicPolarEnvelope α) * m - 12 * α / 25 ≠ 0 := by
    apply (tail_den_pos hm hα17 _).ne'
    have := cubicPolarEnvelope_le_five_sixths hα hα17
    linarith
  unfold distillT0 distillKappa tailRational
  have hnode : 1 - distillNode m α =
      ((21 / 25 - 3 / 5 * cubicPolarEnvelope α) * m - 12 * α / 25) / m := by
    unfold distillNode
    field_simp
    ring
  rw [hnode]
  field_simp
  ring

/-- Real-degree antitonicity of the regularized rational component, including alpha zero. -/
lemma distillT0_antitone_55 {α : ℝ} (hα : 0 ≤ α) (hα17 : α ≤ 17) :
    AntitoneOn (fun m => distillT0 m α) (Set.Ici 55) := by
  have he := cubicPolarEnvelope_nonneg hα
  have he1 := cubicPolarEnvelope_le_five_sixths hα hα17
  have hd : 17 / 50 ≤ 21 / 25 - 3 / 5 * cubicPolarEnvelope α := by linarith
  have hd1 : 21 / 25 - 3 / 5 * cubicPolarEnvelope α ≤ 21 / 25 := by linarith
  have hdα : 10 ≤ α → 21 / 25 - 3 / 5 * cubicPolarEnvelope α ≤ 39 / 100 := by
    intro h10
    have he10 := cubicPolarEnvelope_mono (by norm_num : (0 : ℝ) ≤ 10) h10
    have hval : cubicPolarEnvelope 10 = 4970 / 6591 := by norm_num [cubicPolarEnvelope]
    rw [hval] at he10
    linarith
  intro m hm n hn hmn
  change distillT0 n α ≤ distillT0 m α
  rw [distillT0_eq_rational hn hα hα17, distillT0_eq_rational hm hα hα17]
  exact mul_le_mul_of_nonneg_left (tailRational_antitone hα hα17 hd hd1 hdα hm hn hmn)
    (mul_nonneg (by norm_num) (distillRatio_nonneg hα))

lemma distillT0_antitone {α : ℝ} (hα : 0 ≤ α) (hα17 : α ≤ 17) :
    AntitoneOn (fun m => distillT0 m α) (Set.Ici 61) :=
  (distillT0_antitone_55 hα hα17).mono (Set.Ici_subset_Ici.mpr (by norm_num))

/-- The earlier pointwise reduction holds on the full closed alpha interval. -/
lemma distillComponents_le_61 {m α : ℝ} (hm : 61 ≤ m) (hα : 0 ≤ α) (hα17 : α ≤ 17) :
    distillEBudget m + distillT0 m α + distillT1 m α + distillT2 m α ≤
      distillEBudget 61 + distillT0 61 α + distillT1 61 α + distillT2 61 α := by
  exact add_le_add (add_le_add (add_le_add
    (distillEBudget_antitone (by simp) hm hm)
    (distillT0_antitone hα hα17 (by simp) hm hm))
    (distillT1_antitone hα hα17 (by simp) hm hm))
    (distillT2_antitone hα hα17 (by simp) hm hm)

end Sendov
