import Sendov.Common.DistillationFactors

/-!
# Real-degree monotonicity for the regularized distillation components

New Lean adaptation of Senjian An, *Proof Distillation for Sendov's Conjecture*,
revision e8ae601491ec171ab4f7f8456113dd6a047aa85d, lines 898--950.
Paper: CC BY 4.0, https://creativecommons.org/licenses/by/4.0/ .
The finite degree-81 certificate is a separate obligation. No raw scalar value
at alpha zero is identified with a continuous extension.
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

private lemma tail_antitone {f f' : ℝ → ℝ}
    (hf : ∀ x : ℝ, 81 ≤ x → HasDerivAt f (f' x) x)
    (hn : ∀ x : ℝ, 81 ≤ x → f' x ≤ 0) : AntitoneOn f (Set.Ici 81) := by
  apply antitoneOn_of_deriv_nonpos (convex_Ici _) (fun x hx =>
    (hf x hx).continuousAt.continuousWithinAt)
  · exact fun x hx => (hf x (interior_subset hx)).differentiableAt.differentiableWithinAt
  · intro x hx
    rw [(hf x (interior_subset hx)).deriv]
    exact hn x (interior_subset hx)

lemma distillEBudget_antitone : AntitoneOn distillEBudget (Set.Ici 81) := by
  intro m hm n _ hmn
  change 81 ≤ m at hm
  dsimp only [distillEBudget]
  apply add_le_add le_rfl
  exact div_le_div_of_nonneg_left (by norm_num)
    (by linarith : 0 < 12 * m) (by linarith)

lemma distillEBudget_le_81 {m : ℝ} (hm : 81 ≤ m) :
    distillEBudget m ≤ distillEBudget 81 :=
  distillEBudget_antitone (by simp) hm hm

lemma cubicPolarEnvelope_le_five_sixths {α : ℝ} (hα : 0 ≤ α) (hα17 : α ≤ 17) :
    cubicPolarEnvelope α ≤ 5 / 6 := by
  have h := cubicPolarEnvelope_mono hα hα17
  have h17 : cubicPolarEnvelope 17 = 199087 / 240000 := by
    norm_num [cubicPolarEnvelope]
  rw [h17] at h
  linarith

lemma distillNode_antitone_degree {α : ℝ} (hα : 0 ≤ α) :
    AntitoneOn (fun m => distillNode m α) (Set.Ici 81) := by
  intro m hm n _ hmn
  change 81 ≤ m at hm
  dsimp only [distillNode]
  apply add_le_add le_rfl
  exact div_le_div_of_nonneg_left (by positivity : 0 ≤ 12 * α)
    (by linarith : 0 < 25 * m) (by linarith)

lemma distillNode_lt_four_fifths {m α : ℝ} (hm : 81 ≤ m)
    (hα : 0 ≤ α) (hα17 : α ≤ 17) : distillNode m α < 4 / 5 := by
  have he := cubicPolarEnvelope_le_five_sixths hα hα17
  have ht : 12 * α / (25 * m) ≤ 68 / 675 := by
    apply (div_le_iff₀ (by linarith : 0 < 25 * m)).mpr
    linarith
  unfold distillNode
  linarith

private lemma kappa_slope {m α : ℝ} (hm : 81 ≤ m) (hα17 : α ≤ 17) :
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

private lemma kappa_slope_le {m α : ℝ} (hm : 81 ≤ m) (hα17 : α ≤ 17) :
    1 / (m - 1) + 1 / (m + 1) - 1 / m + 2 / (m - 2 * α) ≤
      1 / 80 + 2 / 47 := by
  have h1 : 1 / (m - 1) ≤ 1 / (80 : ℝ) :=
    div_le_div_of_nonneg_left (by norm_num) (by norm_num) (by linarith)
  have h2 : 1 / (m + 1) ≤ 1 / m :=
    div_le_div_of_nonneg_left (by norm_num) (by linarith) (by linarith)
  have h3 : 2 / (m - 2 * α) ≤ 2 / (47 : ℝ) :=
    div_le_div_of_nonneg_left (by norm_num) (by norm_num) (by linarith)
  linarith

private lemma kappa_rpow_antitone {α z : ℝ} (hα : 0 ≤ α) (hα17 : α ≤ 17)
    (hz : 0 ≤ z) (hz1 : z ≤ 5 / 6) :
    AntitoneOn (fun m => distillKappa m α * z ^ ((m - 3) / 2)) (Set.Ici 81) := by
  rcases hz.eq_or_lt with rfl | hz
  · intro m hm n hn _
    have hm' : (m - 3) / 2 ≠ 0 := by change 81 ≤ m at hm; linarith
    have hn' : (n - 3) / 2 ≠ 0 := by change 81 ≤ n at hn; linarith
    simp only [Real.zero_rpow hm', Real.zero_rpow hn', mul_zero, le_refl]
  have hp (m : ℝ) : HasDerivAt (fun x : ℝ => z ^ ((x - 3) / 2))
      (z ^ ((m - 3) / 2) * (Real.log z / 2)) m := by
    convert! (hasDerivAt_const m z).rpow
      (((hasDerivAt_id' m).sub_const 3).div_const 2) hz using 1
    ring
  apply tail_antitone (fun m hm => slope_mul (kappa_slope hm hα17) (hp m))
  intro m hm
  apply mul_nonpos_of_nonneg_of_nonpos
  · exact mul_nonneg (distillKappa_nonneg (by linarith) hα) (Real.rpow_nonneg hz.le _)
  · have hk := kappa_slope_le hm hα17
    have hl := Real.log_le_sub_one_of_pos hz
    linarith

/-- Real-degree antitonicity; the node itself also decreases with the degree. -/
lemma distillT1_antitone {α : ℝ} (hα : 0 ≤ α) (hα17 : α ≤ 17) :
    AntitoneOn (fun m => distillT1 m α) (Set.Ici 81) := by
  intro m hm n hn hmn
  have hm' : 81 ≤ m := hm
  have hn' : 81 ≤ n := hn
  have hz := distillNode_pos (by linarith : 0 < m) hα
  have hz1 : distillNode m α ≤ 5 / 6 := by
    have := distillNode_lt_four_fifths hm' hα hα17
    linarith
  have hpow := Real.rpow_le_rpow (distillNode_pos (by linarith : 0 < n) hα).le
    (distillNode_antitone_degree hα hm hn hmn) (by linarith : 0 ≤ (n - 3) / 2)
  have hstep := (mul_le_mul_of_nonneg_left hpow
    (distillKappa_nonneg (by linarith) hα)).trans
      (kappa_rpow_antitone hα hα17 hz.le hz1 hm hn hmn)
  have := mul_le_mul_of_nonneg_left hstep (by norm_num : (0 : ℝ) ≤ 259 / 3125)
  simpa only [distillT1, mul_assoc] using this

/-- The zero-alpha case is included by the zero-base real-power case. -/
lemma distillT2_antitone {α : ℝ} (hα : 0 ≤ α) (hα17 : α ≤ 17) :
    AntitoneOn (fun m => distillT2 m α) (Set.Ici 81) := by
  intro m hm n hn hmn
  have hstep := kappa_rpow_antitone hα hα17 (cubicPolarEnvelope_nonneg hα)
    (cubicPolarEnvelope_le_five_sixths hα hα17) hm hn hmn
  have := mul_le_mul_of_nonneg_left hstep (by norm_num : (0 : ℝ) ≤ 421 / 3125)
  simpa only [distillT2, mul_assoc] using this

lemma distillT1_le_81 {m α : ℝ} (hm : 81 ≤ m) (hα : 0 ≤ α) (hα17 : α ≤ 17) :
    distillT1 m α ≤ distillT1 81 α :=
  distillT1_antitone hα hα17 (by simp) hm hm

lemma distillT2_le_81 {m α : ℝ} (hm : 81 ≤ m) (hα : 0 ≤ α) (hα17 : α ≤ 17) :
    distillT2 m α ≤ distillT2 81 α :=
  distillT2_antitone hα hα17 (by simp) hm hm

lemma distillT2_zero {m : ℝ} (hm : 81 ≤ m) : distillT2 m 0 = 0 := by
  have hs : (m - 3) / 2 ≠ 0 := by linarith
  simp [distillT2, cubicPolarEnvelope, Real.zero_rpow hs]

/-- Exact positive tail certificate from the paper, valid for real degree. -/
lemma distillTail_polynomial_pos {m : ℝ} (hm : 81 ≤ m) :
    0 < 7 * m ^ 4 - 510 * m ^ 3 - 4049 * m ^ 2 - 35462 * m - 104040 := by
  have hx : 0 ≤ m - 81 := by linarith
  have hid : 7 * m ^ 4 - 510 * m ^ 3 - 4049 * m ^ 2 - 35462 * m - 104040 =
      7 * (m - 81) ^ 4 + 1758 * (m - 81) ^ 3 + 147583 * (m - 81) ^ 2 +
        4150618 * (m - 81) + 750186 := by ring
  rw [hid]
  positivity

private def tailP (m α : ℝ) : ℝ :=
  7 * m ^ 4 - 30 * α * m ^ 3 - (8 * α ^ 2 + 96 * α + 105) * m ^ 2 +
    (90 * α - 128 * α ^ 2) * m - 360 * α ^ 2

private lemma tailP_pos {m α : ℝ} (hm : 81 ≤ m) (hα : 0 ≤ α) (hα17 : α ≤ 17) :
    0 < tailP m α := by
  have hm0 : 0 ≤ m := by linarith
  have hgap : 0 ≤ 17 - α := by linarith
  have hid : tailP m α =
      (7 * m ^ 4 - 510 * m ^ 3 - 4049 * m ^ 2 - 35462 * m - 104040) +
      (17 - α) * (α * (8 * m ^ 2 + 128 * m + 360) +
        30 * m ^ 3 + 232 * m ^ 2 + 2086 * m + 6120) := by
    dsimp [tailP]
    ring
  rw [hid]
  exact add_pos_of_pos_of_nonneg (distillTail_polynomial_pos hm) (by positivity)

private noncomputable def tailQ (m α d : ℝ) : ℝ :=
  d * tailP m α / 7 + (21 / 25 - d) * (4 * α / 7) *
    ((3 * m - 2 * α) * m ^ 2 + 32 * (m - α) * m + (75 * m - 90 * α))

private lemma tailQ_pos {m α d : ℝ} (hm : 81 ≤ m) (hα : 0 ≤ α)
    (hα17 : α ≤ 17) (hd : 0 < d) (hd1 : d ≤ 21 / 25) : 0 < tailQ m α d := by
  have hm0 : 0 ≤ m := by linarith
  have h1 : 0 ≤ 3 * m - 2 * α := by linarith
  have h2 : 0 ≤ m - α := by linarith
  have h3 : 0 ≤ 75 * m - 90 * α := by linarith
  have h4 : 0 ≤ 21 / 25 - d := by linarith
  unfold tailQ
  exact add_pos_of_pos_of_nonneg (div_pos (mul_pos hd (tailP_pos hm hα hα17))
    (by norm_num)) (by positivity)

private noncomputable def tailRational (m α d : ℝ) : ℝ :=
  m ^ 3 * (m - 2 * α) ^ 2 / ((m + 3) * (m + 5) * (d * m - 12 * α / 25) ^ 4)

private lemma tail_den_pos {m α d : ℝ} (hm : 81 ≤ m) (hα17 : α ≤ 17)
    (hd : 17 / 50 ≤ d) : 0 < d * m - 12 * α / 25 := by
  have hm0 : 0 ≤ m := by linarith
  have hd0 : 0 ≤ d - 17 / 50 := by linarith
  nlinarith [mul_nonneg hd0 hm0]

private lemma rational_slope {m α d : ℝ} (hm : 81 ≤ m) (hα17 : α ≤ 17)
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

private lemma rational_slope_neg {m α d : ℝ} (hm : 81 ≤ m) (hα : 0 ≤ α)
    (hα17 : α ≤ 17) (hd : 17 / 50 ≤ d) (hd1 : d ≤ 21 / 25) :
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
  exact div_neg_of_neg_of_pos (neg_neg_of_pos (tailQ_pos hm hα hα17 (by linarith) hd1))
    (by positivity)

private lemma tailRational_antitone {α d : ℝ} (hα : 0 ≤ α) (hα17 : α ≤ 17)
    (hd : 17 / 50 ≤ d) (hd1 : d ≤ 21 / 25) :
    AntitoneOn (fun m => tailRational m α d) (Set.Ici 81) := by
  apply tail_antitone (fun m hm => rational_slope hm hα17 hd)
  intro m hm
  have hm0 : 0 ≤ m := by linarith
  have hm3 : 0 ≤ m + 3 := by linarith
  have hm5 : 0 ≤ m + 5 := by linarith
  exact mul_nonpos_of_nonneg_of_nonpos (by unfold tailRational; positivity)
    (rational_slope_neg hm hα hα17 hd hd1).le

private lemma distillT0_eq_rational {m α : ℝ} (hm : 81 ≤ m)
    (hα : 0 ≤ α) (hα17 : α ≤ 17) :
    distillT0 m α = (24 * (3 / 5) ^ 4 * distillRatio α) *
      tailRational m α (21 / 25 - 3 / 5 * cubicPolarEnvelope α) := by
  have hm0 : m ≠ 0 := by linarith
  have hm1 : m - 1 ≠ 0 := by linarith
  have hmp1 : m + 1 ≠ 0 := by linarith
  have hm3 : m + 3 ≠ 0 := by linarith
  have hm5 : m + 5 ≠ 0 := by linarith
  have hn : 1 - distillNode m α ≠ 0 := by
    have := distillNode_lt_four_fifths hm hα hα17
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
lemma distillT0_antitone {α : ℝ} (hα : 0 ≤ α) (hα17 : α ≤ 17) :
    AntitoneOn (fun m => distillT0 m α) (Set.Ici 81) := by
  have he := cubicPolarEnvelope_nonneg hα
  have he1 := cubicPolarEnvelope_le_five_sixths hα hα17
  have hd : 17 / 50 ≤ 21 / 25 - 3 / 5 * cubicPolarEnvelope α := by linarith
  have hd1 : 21 / 25 - 3 / 5 * cubicPolarEnvelope α ≤ 21 / 25 := by linarith
  intro m hm n hn hmn
  change distillT0 n α ≤ distillT0 m α
  rw [distillT0_eq_rational hn hα hα17, distillT0_eq_rational hm hα hα17]
  exact mul_le_mul_of_nonneg_left (tailRational_antitone hα hα17 hd hd1 hm hn hmn)
    (mul_nonneg (by norm_num) (distillRatio_nonneg hα))

lemma distillT0_le_81 {m α : ℝ} (hm : 81 ≤ m) (hα : 0 ≤ α) (hα17 : α ≤ 17) :
    distillT0 m α ≤ distillT0 81 α :=
  distillT0_antitone hα hα17 (by simp) hm hm

/-- Pointwise degree-81 reduction. This is not a certificate for the degree-81 base. -/
lemma distillComponents_le_81 {m α : ℝ} (hm : 81 ≤ m) (hα : 0 ≤ α) (hα17 : α ≤ 17) :
    distillEBudget m + distillT0 m α + distillT1 m α + distillT2 m α ≤
      distillEBudget 81 + distillT0 81 α + distillT1 81 α + distillT2 81 α := by
  exact add_le_add (add_le_add (add_le_add (distillEBudget_le_81 hm)
    (distillT0_le_81 hm hα hα17)) (distillT1_le_81 hm hα hα17))
      (distillT2_le_81 hm hα hα17)

/-- The finite worker supplies the only extra hypothesis: the global degree-81 base.
No monotonicity or infinite-tail assertion is assumed. -/
theorem distillComponents_lt_two_thirds_of_base
    (hbase : ∀ α : ℝ, 0 ≤ α → α ≤ 17 →
      distillEBudget 81 + distillT0 81 α + distillT1 81 α + distillT2 81 α < 2 / 3)
    {m α : ℝ} (hm : 81 ≤ m) (hα : 0 ≤ α) (hα17 : α ≤ 17) :
    distillEBudget m + distillT0 m α + distillT1 m α + distillT2 m α < 2 / 3 :=
  (distillComponents_le_81 hm hα hα17).trans_lt (hbase α hα hα17)

end Sendov
