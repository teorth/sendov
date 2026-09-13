import Sendov.Common.DistillationPeakRational

/-!
# Small exact factors for the uniform peak closure

All identities here are identities of the original rational peak, not samples.
`N / (30 S^3)` is the ratio, `F / (30 S^3)` is `1 - envelope`,
`G / (30 S^3)` is `1 + envelope`, and `D / (50 S^3)` is the T0 gap.
For T1 the rate is `C / (a V)` and the shift is `X / V`.
Keeping these factors opaque after their identities are proved avoids repeated
denominator expansion. Only T1 is enlarged, by dropping the fifth and sixth
nonnegative Taylor terms.
-/

namespace Sendov.PeakClosure

/-- Shared affine budget; neither complementary certificate depends on the other. -/
noncomputable def budget1 (a : ℝ) : ℝ := (431 - 3 * a) / 2500

def S (a : ℝ) : ℝ := a + 3
def N (a : ℝ) : ℝ := 29 * a ^ 2 + 180 * a + 270
def P (a : ℝ) : ℝ := 5 * a ^ 3 + 36 * a ^ 2 + 78 * a + 48
def W (a : ℝ) : ℝ := 95 * a ^ 3 + 774 * a ^ 2 + 2052 * a + 1782
def V (a : ℝ) : ℝ := 9 * P a * W a
def C (a : ℝ) : ℝ :=
  605 * a ^ 7 + 13426 * a ^ 6 + 113310 * a ^ 5 + 470394 * a ^ 4 +
    1001268 * a ^ 3 + 969084 * a ^ 2 + 174960 * a - 192456
def X (a : ℝ) : ℝ :=
  70 * a ^ 7 + 7769 * a ^ 6 + 85302 * a ^ 5 + 334746 * a ^ 4 +
    393390 * a ^ 3 - 616248 * a ^ 2 - 1758348 * a - 997272
def F (a : ℝ) : ℝ := a ^ 3 + 90 * a ^ 2 + 540 * a + 810
def G (a : ℝ) : ℝ := 59 * a ^ 3 + 450 * a ^ 2 + 1080 * a + 810
def D (a : ℝ) : ℝ := 13 * a ^ 3 + 198 * a ^ 2 + 864 * a + 1134
def J (a : ℝ) : ℝ := 97 * a ^ 3 + 2169 * a ^ 2 + 10827 * a + 15147

def t4 (x v : ℝ) : ℝ :=
  24 * v ^ 4 + 24 * x * v ^ 3 + 12 * x ^ 2 * v ^ 2 + 4 * x ^ 3 * v + x ^ 4
def t6 (x v : ℝ) : ℝ :=
  720 * v ^ 6 + 720 * x * v ^ 5 + 360 * x ^ 2 * v ^ 4 +
    120 * x ^ 3 * v ^ 3 + 30 * x ^ 4 * v ^ 2 + 6 * x ^ 5 * v + x ^ 6
noncomputable def taylor4 (x : ℝ) : ℝ :=
  1 + x + x ^ 2 / 2 + x ^ 3 / 6 + x ^ 4 / 24

lemma S_pos {a : ℝ} (ha : 0 ≤ a) : 0 < S a := by unfold S; positivity
lemma N_pos {a : ℝ} (ha : 0 ≤ a) : 0 < N a := distillN_pos ha
lemma P_pos {a : ℝ} (ha : 0 ≤ a) : 0 < P a := by unfold P; positivity
lemma W_pos {a : ℝ} (ha : 0 ≤ a) : 0 < W a := by unfold W; positivity
lemma V_pos {a : ℝ} (ha : 0 ≤ a) : 0 < V a := by
  unfold V
  exact mul_pos (mul_pos (by norm_num) (P_pos ha)) (W_pos ha)
lemma F_pos {a : ℝ} (ha : 0 ≤ a) : 0 < F a := by unfold F; positivity
lemma G_pos {a : ℝ} (ha : 0 ≤ a) : 0 < G a := by unfold G; positivity
lemma D_pos {a : ℝ} (ha : 0 ≤ a) : 0 < D a := by unfold D; positivity

lemma ratio_eq {a : ℝ} (ha : 0 ≤ a) : distillRatio a = N a / (30 * S a ^ 3) :=
  distillRatio_compact ha

lemma envelope_gap_eq {a : ℝ} (ha : 0 ≤ a) :
    1 - cubicPolarEnvelope a = F a / (30 * S a ^ 3) := by
  have hs := (S_pos ha).ne'
  unfold cubicPolarEnvelope F S at *
  field_simp
  ring

lemma envelope_sum_eq {a : ℝ} (ha : 0 ≤ a) :
    1 + cubicPolarEnvelope a = G a / (30 * S a ^ 3) := by
  have hs := (S_pos ha).ne'
  unfold cubicPolarEnvelope G S at *
  field_simp
  ring

lemma node_eq {a : ℝ} (ha : 0 ≤ a) :
    distillPeakNode a = 9 * P a / (50 * S a ^ 3) := by
  have hs := (S_pos ha).ne'
  unfold distillPeakNode cubicPolarEnvelope P S at *
  field_simp
  ring

lemma node_sum_eq {a : ℝ} (ha : 0 ≤ a) :
    1 + distillPeakNode a = W a / (50 * S a ^ 3) := by
  rw [node_eq ha]
  have hs := (S_pos ha).ne'
  unfold P W S at *
  field_simp
  ring

lemma rate1_eq {a : ℝ} (ha : 0 < a) :
    distillPeakRate1 a = C a / (a * V a) := by
  unfold distillPeakRate1
  rw [node_sum_eq ha.le, node_eq ha.le]
  have hs := (S_pos ha.le).ne'
  have hp := (P_pos ha.le).ne'
  have hw := (W_pos ha.le).ne'
  unfold V
  field_simp
  unfold C P W S
  ring

lemma shift1_eq {a : ℝ} (ha : 0 < a) :
    distillPeakShift1 a = X a / V a := by
  rw [distillPeakShift1, rate1_eq ha]
  unfold distillPeakBoost1
  rw [node_eq ha.le]
  have hs := (S_pos ha.le).ne'
  have hp := (P_pos ha.le).ne'
  have hw := (W_pos ha.le).ne'
  unfold V
  field_simp
  unfold C X W S
  ring

lemma C_pos {a : ℝ} (ha : 2 ≤ a) : 0 < C a := by
  have ha0 : 0 < a := by linarith
  have h := distillPeakRate1_pos (α := a) (by linarith)
  rw [rate1_eq ha0] at h
  exact (div_pos_iff_of_pos_right (mul_pos ha0 (V_pos ha0.le))).mp h

lemma X_pos {a : ℝ} (ha : 2 ≤ a) : 0 < X a := by
  have ha0 : 0 < a := by linarith
  have h := distillPeakShift1_pos ha
  rw [shift1_eq ha0] at h
  exact (div_pos_iff_of_pos_right (V_pos ha0.le)).mp h

lemma rate2_eq {a : ℝ} (ha : 0 ≤ a) : distillPeakRate2 a = F a / G a := by
  rw [distillPeakRate2, envelope_gap_eq ha, envelope_sum_eq ha]
  have hs := (S_pos ha).ne'
  field_simp

lemma peak0_eq {a : ℝ} (ha : 0 < a) :
    distillPeak0 a = 3000 * S a ^ 9 * N a * J a / (a * F a ^ 2 * D a ^ 3) := by
  have hd : distillPeakD a = D a / (50 * S a ^ 3) := by
    have hs := (S_pos ha.le).ne'
    unfold distillPeakD cubicPolarEnvelope D S at *
    field_simp
    ring
  have hsub : distillPeakD a - 6 / 25 = F a / (50 * S a ^ 3) := by
    rw [hd]
    have hs := (S_pos ha.le).ne'
    unfold D F S at *
    field_simp
    ring
  rw [distillPeak0, hsub, hd, ratio_eq ha.le]
  have hs := (S_pos ha.le).ne'
  have hf := (F_pos ha.le).ne'
  have hD := (D_pos ha.le).ne'
  field_simp
  unfold D J S
  ring

lemma elementary_eq {a m : ℝ} (ha : 0 ≤ a) :
    distillElementary m a =
      N a / (2 * F a) + N a / (120 * S a ^ 3) +
        (1 / 2 + N a / (120 * S a ^ 3)) / m := by
  rw [distillElementary, ratio_eq ha, envelope_gap_eq ha]
  have hs := (S_pos ha).ne'
  have hf := (F_pos ha).ne'
  field_simp
  ring

lemma t4_pos {x v : ℝ} (hx : 0 ≤ x) (hv : 0 < v) : 0 < t4 x v := by
  unfold t4
  positivity

lemma t6_pos {x v : ℝ} (hx : 0 ≤ x) (hv : 0 < v) : 0 < t6 x v := by
  unfold t6
  positivity

lemma taylor4_eq {x v : ℝ} (hv : v ≠ 0) :
    taylor4 (x / v) = t4 x v / (24 * v ^ 4) := by
  unfold taylor4 t4
  field_simp
  ring

lemma taylor6_eq {x v : ℝ} (hv : v ≠ 0) :
    distillTaylor6 (x / v) = t6 x v / (720 * v ^ 6) := by
  unfold distillTaylor6 t6
  field_simp
  ring

def numerator1 (a : ℝ) : ℝ :=
  259 * N a * a ^ 3 * V a ^ 6 * (6723 * V a + 5416 * C a)
def denominator1 (a : ℝ) : ℝ := 78125000 * S a ^ 3 * C a ^ 3 * t4 (X a) (V a)
def numerator2 (a : ℝ) : ℝ :=
  1263 * N a * G a ^ 8 * (6723 * G a + 5416 * a * F a)
def denominator2 (a : ℝ) : ℝ :=
  7812500 * S a ^ 3 * F a ^ 3 * t6 ((2 * a - 3) * F a) (G a)

lemma denominator1_pos {a : ℝ} (ha : 2 ≤ a) : 0 < denominator1 a := by
  have ha0 : 0 ≤ a := by linarith
  have := S_pos ha0
  have := C_pos ha
  have := t4_pos (X_pos ha).le (V_pos ha0)
  unfold denominator1
  positivity

lemma denominator2_pos {a : ℝ} (ha : 2 ≤ a) : 0 < denominator2 a := by
  have ha0 : 0 ≤ a := by linarith
  have := S_pos ha0
  have := F_pos ha0
  have := t6_pos (mul_nonneg (by linarith : 0 ≤ 2 * a - 3) (F_pos ha0).le) (G_pos ha0)
  unfold denominator2
  positivity

lemma peak1_le_four {a : ℝ} (ha : 2 ≤ a) :
    (259 / 12500) * distillRatio a *
        distillRationalExpPeak a (distillPeakRate1 a) (distillPeakShift1 a) ≤
      numerator1 a / denominator1 a := by
  have ha0 : 0 < a := by linarith
  have hx := (distillPeakShift1_pos ha).le
  have h4 : 0 < taylor4 (distillPeakShift1 a) := by unfold taylor4; positivity
  have h46 : taylor4 (distillPeakShift1 a) ≤ distillTaylor6 (distillPeakShift1 a) := by
    unfold taylor4 distillTaylor6
    have h5 := pow_nonneg hx 5
    have h6 := pow_nonneg hx 6
    linarith
  have hc := distillPeakRate1_pos (α := a) (by linarith)
  have hn : 0 ≤ 27 * (249 / 5000) / distillPeakRate1 a ^ 3 +
      8 * a * (677 / 5000) / distillPeakRate1 a ^ 2 := by positivity
  have h := mul_le_mul_of_nonneg_left (div_le_div_of_nonneg_left hn h4 h46)
    (mul_nonneg (by norm_num : (0 : ℝ) ≤ 259 / 12500) (distillRatio_nonneg ha0.le))
  unfold distillRationalExpPeak
  refine h.trans_eq ?_
  rw [ratio_eq ha0.le, rate1_eq ha0, shift1_eq ha0, taylor4_eq (V_pos ha0.le).ne']
  have hs := (S_pos ha0.le).ne'
  have hc := (C_pos ha).ne'
  have hv := (V_pos ha0.le).ne'
  have ht := (t4_pos (X_pos ha).le (V_pos ha0.le)).ne'
  unfold numerator1 denominator1
  field_simp
  ring

lemma peak2_eq {a : ℝ} (ha : 2 ≤ a) :
    (421 / 12500) * distillRatio a *
        distillRationalExpPeak a (distillPeakRate2 a) (distillPeakRate2 a * (2 * a - 3)) =
      numerator2 a / denominator2 a := by
  have ha0 : 0 ≤ a := by linarith
  have hs := (S_pos ha0).ne'
  have hf := (F_pos ha0).ne'
  have hg := (G_pos ha0).ne'
  have ht := (t6_pos
    (mul_nonneg (by linarith : 0 ≤ 2 * a - 3) (F_pos ha0).le) (G_pos ha0)).ne'
  unfold distillRationalExpPeak
  rw [ratio_eq ha0, rate2_eq ha0]
  have hid : F a / G a * (2 * a - 3) = ((2 * a - 3) * F a) / G a := by ring
  rw [hid, taylor6_eq hg]
  unfold numerator2 denominator2
  field_simp
  ring

end Sendov.PeakClosure
