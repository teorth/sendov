import Sendov.Analytic.PaperSecant
import Mathlib.Analysis.Complex.ExponentialBounds

/-!
# Global raw-polar endpoint estimates

Retain both endpoints of the affine polar chord.  With `N = (m+2)/2`
and `δ = 1-a²`, its exact integral supplies the logarithmic bound when
`N*δ ≥ 2`.  In the complementary region the already proved rational
bound gives `c > 3/5`.  Both branches yield `log N / N ≤ c`.
-/
namespace Sendov.PaperGlobalPolar

open MeasureTheory PaperPolar

/-- The quadratic lies below its affine endpoint chord. -/
lemma polar_le_chord {a x t : ℝ} (ht : t ∈ Set.Icc (0 : ℝ) 1) :
    Ppolar a x t ≤ a ^ 2 + (1 - a ^ 2) * (1 + c a x) * t := by
  have h := mul_nonneg (sq_nonneg (1 - a ^ 2))
    (mul_nonneg ht.1 (sub_nonneg.mpr ht.2))
  unfold Ppolar c b
  nlinarith only [h]

/-- Exact finite chord integral, with neither endpoint discarded. -/
theorem integral_chord {m : ℕ} {a x : ℝ} (ha : 0 < a) (ha1 : a < 1)
    (hc : 0 < c a x) :
    (∫ t in (0 : ℝ)..1,
      (a ^ 2 + (1 - a ^ 2) * (1 + c a x) * t) ^ ((m : ℝ) / 2)) =
      ((1 + (1 - a ^ 2) * c a x) ^ (((m : ℝ) + 2) / 2) -
        (a ^ 2) ^ (((m : ℝ) + 2) / 2)) /
        ((((m : ℝ) + 2) / 2) * (1 - a ^ 2) * (1 + c a x)) := by
  have hd := PaperSecant.delta_pos ha ha1
  have hs : 0 < (1 - a ^ 2) * (1 + c a x) := mul_pos hd (by linarith)
  rw [intervalIntegral.integral_comp_add_mul (fun y : ℝ => y ^ ((m : ℝ) / 2)) hs.ne',
    integral_rpow (Or.inl (by have := Nat.cast_nonneg (α := ℝ) m; linarith : -1 < (m : ℝ) / 2))]
  simp only [mul_zero, add_zero, mul_one, smul_eq_mul]
  rw [show a ^ 2 + (1 - a ^ 2) * (1 + c a x) = 1 + (1 - a ^ 2) * c a x by ring,
    show (m : ℝ) / 2 + 1 = ((m : ℝ) + 2) / 2 by ring]
  field_simp

/-- The raw integral is bounded by the exact finite chord integral. -/
theorem raw_integral_le_chord {m : ℕ} {a x : ℝ} (ha : 0 < a) (ha1 : a < 1)
    (hx0 : -1 ≤ x) (hx1 : x ≤ 1) (hc : 0 < c a x) :
    (∫ t in (0 : ℝ)..1, Ppolar a x t ^ ((m : ℝ) / 2)) ≤
      ((1 + (1 - a ^ 2) * c a x) ^ (((m : ℝ) + 2) / 2) -
        (a ^ 2) ^ (((m : ℝ) + 2) / 2)) /
        ((((m : ℝ) + 2) / 2) * (1 - a ^ 2) * (1 + c a x)) := by
  rw [← integral_chord ha ha1 hc]
  refine intervalIntegral.integral_mono_on (by norm_num) (PaperSecant.integrable_R m a x)
    (((continuous_rpow_const (by positivity : 0 ≤ (m : ℝ) / 2)).comp
      (by fun_prop)).intervalIntegrable _ _) ?_
  intro t ht
  exact Real.rpow_le_rpow (Ppolar_nonneg (x_sq_le_one hx0 hx1) a t)
    (polar_le_chord ht) (by positivity)

/-- Taking logarithms of the exact chord bound. -/
theorem log_mul_delta_le {m : ℕ} {a x : ℝ} (hm : 7 ≤ m)
    (ha : 0 < a) (ha1 : a < 1) (hx0 : -1 ≤ x) (hx1 : x ≤ 1)
    (hr : RawPolar m a x) :
    Real.log ((((m : ℝ) + 2) / 2) * (1 - a ^ 2)) ≤
      ((((m : ℝ) + 2) / 2) * (1 - a ^ 2)) * c a x := by
  have hc := (geometry hm ha ha1 hx0 hx1 hr).2
  have hd := PaperSecant.delta_pos ha ha1
  have hN : 0 < ((m : ℝ) + 2) / 2 := by positivity
  have hD : 0 < (((m : ℝ) + 2) / 2) * (1 - a ^ 2) := mul_pos hN hd
  have hden : 0 < (((m : ℝ) + 2) / 2) * (1 - a ^ 2) * (1 + c a x) :=
    mul_pos hD (by linarith)
  have h := ((rawPolar_iff m a x).mp hr).trans (raw_integral_le_chord ha ha1 hx0 hx1 hc)
  have hpow := (le_div_iff₀ hden).mp h
  have hnonneg := Real.rpow_nonneg (sq_nonneg a) (((m : ℝ) + 2) / 2)
  have hlower : (((m : ℝ) + 2) / 2) * (1 - a ^ 2) ≤
      (1 + (1 - a ^ 2) * c a x) ^ (((m : ℝ) + 2) / 2) := by
    nlinarith [mul_nonneg hD.le hc.le]
  have hp : 0 < 1 + (1 - a ^ 2) * c a x := by positivity
  have hlog := Real.log_le_log hD hlower
  rw [Real.log_rpow hp] at hlog
  have hu := Real.log_le_sub_one_of_pos hp
  have hmul := mul_le_mul_of_nonneg_left hu hN.le
  nlinarith

/-- The tangent bound at four and `log 2 > 1/2` control the lower endpoint. -/
lemma log_le_mul_log_two {N : ℝ} (hN : 4 ≤ N) :
    Real.log N ≤ N / 2 * Real.log 2 := by
  have hN0 : 0 < N := by linarith
  have h := Real.log_le_sub_one_of_pos (div_pos hN0 (by norm_num : (0 : ℝ) < 4))
  rw [Real.log_div hN0.ne' (by norm_num),
    show Real.log 4 = 2 * Real.log 2 by
      rw [show (4 : ℝ) = 2 ^ 2 by norm_num, Real.log_pow]; norm_num] at h
  have h2 := Real.log_two_gt_d9
  nlinarith [mul_nonneg (by linarith : 0 ≤ N - 4) (by linarith : 0 ≤ Real.log 2 - 1 / 2)]

/-- On `[2,N]`, concavity puts `log t` above `t * log N / N`. -/
lemma log_chord_lower {N t : ℝ} (hN : 4 ≤ N) (ht : 2 ≤ t) (htN : t ≤ N) :
    t * (Real.log N / N) ≤ Real.log t := by
  have hN0 : 0 < N := by linarith
  have hden : 0 < N - 2 := by linarith
  let u := (N - t) / (N - 2)
  let v := (t - 2) / (N - 2)
  have hu : 0 ≤ u := div_nonneg (sub_nonneg.mpr htN) hden.le
  have hv : 0 ≤ v := div_nonneg (by linarith) hden.le
  have huv : u + v = 1 := by dsimp [u, v]; field_simp; ring
  have htuv : u * 2 + v * N = t := by dsimp [u, v]; field_simp; ring
  have hconc := strictConcaveOn_log_Ioi.concaveOn.2
    (show (0 : ℝ) < 2 by norm_num) hN0 hu hv huv
  simp only [smul_eq_mul, htuv] at hconc
  have hend : 2 * Real.log N / N ≤ Real.log 2 := by
    apply (div_le_iff₀ hN0).2
    nlinarith [log_le_mul_log_two hN]
  calc
    t * (Real.log N / N) = u * (2 * Real.log N / N) + v * Real.log N := by
      dsimp [u, v]
      field_simp
      ring
    _ ≤ u * Real.log 2 + v * Real.log N :=
      add_le_add (mul_le_mul_of_nonneg_left hend hu) le_rfl
    _ ≤ Real.log t := hconc

/-- The logarithmic endpoint comparison holds uniformly in delta. -/
lemma log_mul_div_delta {N δ : ℝ} (hN : 4 ≤ N) (hδ : 0 < δ)
    (hδ1 : δ ≤ 1) (hlarge : 2 ≤ N * δ) :
    Real.log N ≤ Real.log (N * δ) / δ := by
  apply (le_div_iff₀ hδ).2
  have h := log_chord_lower hN hlarge
    (mul_le_of_le_one_right (by linarith : 0 ≤ N) hδ1)
  have hN0 : N ≠ 0 := by linarith
  have heq : N * δ * (Real.log N / N) = Real.log N * δ := by
    field_simp
  rwa [heq] at h

/-- A small, genuine logarithmic numerical certificate, not a hypothesis. -/
lemma log_129_gt : (24 : ℝ) / 5 < Real.log 129 := by
  have h := Real.log_two_gt_d9
  have he : Real.log 128 = 7 * Real.log 2 := by
    rw [show (128 : ℝ) = 2 ^ 7 by norm_num, Real.log_pow]
    norm_num
  have hmono : Real.log 128 ≤ Real.log 129 := Real.log_le_log (by norm_num) (by norm_num)
  rw [he] at hmono
  linarith

/-- A convenient uniform upper bound on `log N / N`. -/
lemma log_div_le_half {N : ℝ} (hN : 4 ≤ N) : Real.log N / N ≤ 1 / 2 := by
  have hN0 : 0 < N := by linarith
  apply (div_le_iff₀ hN0).2
  have h := log_le_mul_log_two hN
  have h2 := Real.log_le_sub_one_of_pos (by norm_num : (0 : ℝ) < 2)
  nlinarith [mul_nonneg hN0.le (by linarith : 0 ≤ 1 - Real.log 2)]

/-- The small-delta branch uses the stronger rational polar estimate. -/
theorem three_fifths_lt_c {m : ℕ} {a x : ℝ} (hm : 7 ≤ m)
    (ha : 0 < a) (ha1 : a < 1) (hx0 : -1 ≤ x) (hx1 : x ≤ 1)
    (hr : RawPolar m a x) (hsmall : (((m : ℝ) + 2) / 2) * (1 - a ^ 2) < 2) :
    (3 : ℝ) / 5 < c a x := by
  have hd := PaperSecant.delta_pos ha ha1
  have hα := PaperPolar.alpha_pos (by omega : 0 < m) ha ha1
  have hα2 : alpha m a < 2 := by unfold alpha; nlinarith
  have hb := b_le_alpha (by omega : 0 < m) ha ha1 hx0 hx1 hr
  have hfrac : alpha m a / (3 + alpha m a) < (2 : ℝ) / 5 := by
    apply (div_lt_iff₀ (by linarith : 0 < 3 + alpha m a)).2
    linarith
  unfold c
  linarith

/-- A global logarithmic bound derived solely from raw polar. -/
theorem log_degree_le_c {m : ℕ} {a x : ℝ} (hm : 7 ≤ m)
    (ha : 0 < a) (ha1 : a < 1) (hx0 : -1 ≤ x) (hx1 : x ≤ 1)
    (hr : RawPolar m a x) :
    Real.log (((m : ℝ) + 2) / 2) / (((m : ℝ) + 2) / 2) ≤ c a x := by
  have hm' : (7 : ℝ) ≤ m := by exact_mod_cast hm
  have hN : 4 ≤ ((m : ℝ) + 2) / 2 := by linarith
  have hN0 : 0 < ((m : ℝ) + 2) / 2 := by positivity
  have hd := PaperSecant.delta_pos ha ha1
  by_cases hlarge : 2 ≤ (((m : ℝ) + 2) / 2) * (1 - a ^ 2)
  · have hlog := log_mul_div_delta hN hd (by nlinarith [sq_nonneg a]) hlarge
    have hraw := log_mul_delta_le hm ha ha1 hx0 hx1 hr
    have hlog' := (le_div_iff₀ hd).mp hlog
    apply (div_le_iff₀ hN0).2
    nlinarith
  · have hc := three_fifths_lt_c hm ha ha1 hx0 hx1 hr (lt_of_not_ge hlarge)
    exact (log_div_le_half hN).trans (by linarith)

/-- Elementary endpoint suppression from the logarithmic bound. -/
lemma rpow_endpoint {N B : ℝ} (hN : 4 ≤ N) (hB : 0 < B)
    (hc : Real.log N / N ≤ 1 - B) : B ^ (N - 1) ≤ 2 / N := by
  have hN0 : 0 < N := by linarith
  have hlogB : Real.log B ≤ -(Real.log N / N) := by
    have h := Real.log_le_sub_one_of_pos hB
    linarith
  have hpow := mul_le_mul_of_nonneg_left hlogB (by linarith : 0 ≤ N - 1)
  have hexp : -(N - 1) * (Real.log N / N) = Real.log N / N - Real.log N := by
    field_simp
    ring
  have htwo : Real.log N / N ≤ Real.log 2 :=
    (log_div_le_half hN).trans (by linarith [Real.log_two_gt_d9])
  apply (Real.log_le_log_iff (Real.rpow_pos_of_pos hB _) (div_pos (by norm_num) hN0)).mp
  rw [Real.log_rpow hB, Real.log_div (by norm_num) hN0.ne']
  nlinarith

/-- The global endpoint estimate, for all real `a` in `(0,1)` and all degrees `m ≥ 7`. -/
theorem endpoint_le {m : ℕ} {a x : ℝ} (hm : 7 ≤ m)
    (ha : 0 < a) (ha1 : a < 1) (hx0 : -1 ≤ x) (hx1 : x ≤ 1)
    (hr : RawPolar m a x) : b a x ^ ((m : ℝ) / 2) ≤ 4 / ((m : ℝ) + 2) := by
  have hm' : (7 : ℝ) ≤ m := by exact_mod_cast hm
  have h := rpow_endpoint (N := ((m : ℝ) + 2) / 2) (by linarith)
    (b_pos ha.le ha1 hx1) (log_degree_le_c hm ha ha1 hx0 hx1 hr)
  rw [show ((m : ℝ) + 2) / 2 - 1 = (m : ℝ) / 2 by ring] at h
  calc
    b a x ^ ((m : ℝ) / 2) ≤ 2 / (((m : ℝ) + 2) / 2) := h
    _ = 4 / ((m : ℝ) + 2) := by field_simp; norm_num

/-- The second global endpoint estimate, with a strict degree-256 base. -/
theorem degree_mul_sq_gt {m : ℕ} {a x : ℝ} (hm : 256 ≤ m)
    (ha : 0 < a) (ha1 : a < 1) (hx0 : -1 ≤ x) (hx1 : x ≤ 1)
    (hr : RawPolar m a x) : (19 : ℝ) / 2 < (m : ℝ) * x ^ 2 := by
  have hm' : (256 : ℝ) ≤ m := by exact_mod_cast hm
  have hN : (129 : ℝ) ≤ ((m : ℝ) + 2) / 2 := by linarith
  have hN0 : 0 < ((m : ℝ) + 2) / 2 := by positivity
  have hlog : (24 : ℝ) / 5 < Real.log (((m : ℝ) + 2) / 2) :=
    log_129_gt.trans_le (Real.log_le_log (by norm_num) hN)
  have hc := (div_le_iff₀ hN0).mp (log_degree_le_c (by omega) ha ha1 hx0 hx1 hr)
  have hcx : c a x ≤ x ^ 2 := by unfold c b; nlinarith [sq_nonneg (x - a)]
  have hmul := mul_le_mul_of_nonneg_right hcx hN0.le
  have hx : 0 ≤ x ^ 2 := sq_nonneg x
  have hpositive : 0 < c a x := (geometry (by omega) ha ha1 hx0 hx1 hr).2
  have hscaled : (24 : ℝ) / 5 < (((m : ℝ) + 2) / 2) * x ^ 2 := by nlinarith
  have hfactor : (m : ℝ) + 2 ≤ (129 : ℝ) / 128 * m := by linarith
  have hlast := mul_le_mul_of_nonneg_right hfactor hx
  nlinarith

end Sendov.PaperGlobalPolar
