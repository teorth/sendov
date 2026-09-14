import Sendov.Analytic.PaperCenteredCertificate

/-!
# DI02: the actual repeated hundred-point multiset
The certificates are arithmetic witnesses, not assumptions about an unrelated
scalar bound. Both error definitions retain their actual complex endpoints.
-/
noncomputable section
open scoped BigOperators
namespace Sendov.PaperCenteredHundred
open PaperCentered PaperCenteredBound PaperCenteredCertificate

def a : ℝ := 9 / 10
def μ : ℂ := 7 / 10
def q : Multiset ℂ := Multiset.replicate 50 (2 / 5) + Multiset.replicate 50 1
def r : Multiset ℂ := q.map (fun w => w - μ)

@[simp] lemma q_card : q.card = 100 := by norm_num [q]
@[simp] lemma r_card : r.card = 100 := by simp [r]
lemma mean : q.sum = q.card * μ := by norm_num [q, μ]
lemma mean_div : q.sum / q.card = (7 / 10 : ℂ) := by norm_num [q]
lemma pointwise (w : ℂ) (hw : w ∈ q) : w ≠ 0 ∧ ‖w‖ ≤ 1 := by
  simp only [q, Multiset.mem_add, Multiset.mem_replicate] at hw
  rcases hw with ⟨_, rfl⟩ | ⟨_, rfl⟩ <;> norm_num [norm_div]
lemma deviations : r = Multiset.replicate 50 (-(3 / 10 : ℂ)) +
    Multiset.replicate 50 (3 / 10 : ℂ) := by
  norm_num [r, q, μ, Multiset.map_add, Multiset.map_replicate]
@[simp] lemma norm_mu : ‖μ‖ = (7 / 10 : ℝ) := by norm_num [μ, norm_div]
lemma variance_exact : variance r = 9 / 100 := by
  norm_num [variance, deviations, Multiset.map_add, Multiset.map_replicate,
    norm_div, norm_neg]
lemma kappa_exact : kappa r = 9 / 100 := by
  norm_num [kappa, deviations, Multiset.map_add, Multiset.map_replicate]
@[simp] lemma Gamma_exact : Gamma r μ = 1 / 539 := by
  norm_num [Gamma, variance_exact]
lemma scale : (a : ℂ) * μ = ((63 / 100 : ℝ) : ℂ) := by norm_num [a, μ]
lemma mu_ne : μ ≠ 0 := by norm_num [μ]

lemma norm_endpoints (k : ℕ) (hk : k ≤ 100) : ‖H 100 k ((a : ℂ) * μ)‖ ≤ 1 := by
  rw [scale]
  exact norm_H_ofReal_le_one _ _ _ hk (by norm_num) (by norm_num)

lemma low_endpoints :
    ‖1 - (a : ℂ) * μ‖ ^ (r.card + 1) + Gamma r μ * ‖B r.card 2 ((a : ℂ) * μ)‖ ≤
      (1 / 10^12 : ℝ) := by
  rw [scale, r_card, Gamma_exact, B_ofReal]
  have hn : ‖1 - ((63 / 100 : ℝ) : ℂ)‖ = (37 / 100 : ℝ) := by
    norm_num [norm_div]
  rw [hn, Complex.norm_real, Real.norm_eq_abs,
    abs_of_nonneg (realB_nonneg 100 2 (63/100) (by norm_num) (by norm_num))]
  norm_num [realB, Finset.sum_range_succ, Nat.choose]

lemma esymm_exact (k : ℕ) (hk : k ≤ 100) :
    r.esymm k = if 2 ∣ (100-k) then
      (-(3 / 10 : ℂ)^2) ^ (50-(100-k)/2) * ((50 : ℕ).choose ((100-k)/2) : ℂ) else 0 := by
  rw [deviations]
  exact esymm_opposite_replicate 50 k (3/10) hk

/-- Fixed-denominator outward envelopes for normalized coefficients. -/
def genericNumerator (k : ℕ) : ℕ :=
  if k = 3 then 410439009 else if k = 4 then 38153285 else
  if k = 5 then 3927325 else if k = 6 then 440942 else
  if k = 7 then 53400 else if k = 8 then 6917 else
  if k = 9 then 952 else if k = 10 then 139 else
  if k = 11 then 22 else if k = 12 then 4 else 1

def actualNumerator (k : ℕ) : ℕ :=
  if k % 2 = 1 then 0 else if k = 4 then 10539189 else
  if k = 6 then 101883 else if k = 8 then 1409 else if k = 10 then 26 else 1

-- BEGIN GENERATED COEFFICIENT CERTIFICATES
private lemma generic_3 : C 100 3 (9/100) /
    (((100 : ℕ).choose 3 : ℝ) * (7/10)^3) ≤ (genericNumerator 3 : ℝ) / 10^12 := by
  apply normalized_C_le 100 3 (9/100) (7/10) _ (by decide) (by decide)
    (by norm_num) (by positivity)
  have hc : (100 : ℕ).choose 3 = 161700 := by
    rw [Nat.choose_eq_factorial_div_factorial (by decide)]
    norm_num [Nat.factorial]
  norm_num [genericNumerator, hc]

private lemma actual_3 : ‖r.esymm 3‖ /
    (((100 : ℕ).choose 3 : ℝ) * (7/10)^3) ≤ (actualNumerator 3 : ℝ) / 10^12 := by
  rw [esymm_exact 3 (by decide)]
  norm_num [actualNumerator]

private lemma generic_4 : C 100 4 (9/100) /
    (((100 : ℕ).choose 4 : ℝ) * (7/10)^4) ≤ (genericNumerator 4 : ℝ) / 10^12 := by
  apply normalized_C_le 100 4 (9/100) (7/10) _ (by decide) (by decide)
    (by norm_num) (by positivity)
  have hc : (100 : ℕ).choose 4 = 3921225 := by
    rw [Nat.choose_eq_factorial_div_factorial (by decide)]
    norm_num [Nat.factorial]
  norm_num [genericNumerator, hc]

private lemma actual_4 : ‖r.esymm 4‖ /
    (((100 : ℕ).choose 4 : ℝ) * (7/10)^4) ≤ (actualNumerator 4 : ℝ) / 10^12 := by
  rw [esymm_exact 4 (by decide)]
  have hc : (100 : ℕ).choose 4 = 3921225 := by
    rw [Nat.choose_eq_factorial_div_factorial (by decide)]
    norm_num [Nat.factorial]
  have hd : (50 : ℕ).choose 48 = 1225 := by
    rw [Nat.choose_eq_factorial_div_factorial (by decide)]
    norm_num [Nat.factorial]
  norm_num [hc, hd, actualNumerator, norm_mul, norm_pow, norm_div]

private lemma generic_5 : C 100 5 (9/100) /
    (((100 : ℕ).choose 5 : ℝ) * (7/10)^5) ≤ (genericNumerator 5 : ℝ) / 10^12 := by
  apply normalized_C_le 100 5 (9/100) (7/10) _ (by decide) (by decide)
    (by norm_num) (by positivity)
  have hc : (100 : ℕ).choose 5 = 75287520 := by
    rw [Nat.choose_eq_factorial_div_factorial (by decide)]
    norm_num [Nat.factorial]
  norm_num [genericNumerator, hc]

private lemma actual_5 : ‖r.esymm 5‖ /
    (((100 : ℕ).choose 5 : ℝ) * (7/10)^5) ≤ (actualNumerator 5 : ℝ) / 10^12 := by
  rw [esymm_exact 5 (by decide)]
  norm_num [actualNumerator]

private lemma generic_6 : C 100 6 (9/100) /
    (((100 : ℕ).choose 6 : ℝ) * (7/10)^6) ≤ (genericNumerator 6 : ℝ) / 10^12 := by
  apply normalized_C_le 100 6 (9/100) (7/10) _ (by decide) (by decide)
    (by norm_num) (by positivity)
  have hc : (100 : ℕ).choose 6 = 1192052400 := by
    rw [Nat.choose_eq_factorial_div_factorial (by decide)]
    norm_num [Nat.factorial]
  norm_num [genericNumerator, hc]

private lemma actual_6 : ‖r.esymm 6‖ /
    (((100 : ℕ).choose 6 : ℝ) * (7/10)^6) ≤ (actualNumerator 6 : ℝ) / 10^12 := by
  rw [esymm_exact 6 (by decide)]
  have hc : (100 : ℕ).choose 6 = 1192052400 := by
    rw [Nat.choose_eq_factorial_div_factorial (by decide)]
    norm_num [Nat.factorial]
  have hd : (50 : ℕ).choose 47 = 19600 := by
    rw [Nat.choose_eq_factorial_div_factorial (by decide)]
    norm_num [Nat.factorial]
  norm_num [hc, hd, actualNumerator, norm_mul, norm_pow, norm_div]

private lemma generic_7 : C 100 7 (9/100) /
    (((100 : ℕ).choose 7 : ℝ) * (7/10)^7) ≤ (genericNumerator 7 : ℝ) / 10^12 := by
  apply normalized_C_le 100 7 (9/100) (7/10) _ (by decide) (by decide)
    (by norm_num) (by positivity)
  have hc : (100 : ℕ).choose 7 = 16007560800 := by
    rw [Nat.choose_eq_factorial_div_factorial (by decide)]
    norm_num [Nat.factorial]
  norm_num [genericNumerator, hc]

private lemma actual_7 : ‖r.esymm 7‖ /
    (((100 : ℕ).choose 7 : ℝ) * (7/10)^7) ≤ (actualNumerator 7 : ℝ) / 10^12 := by
  rw [esymm_exact 7 (by decide)]
  norm_num [actualNumerator]

private lemma generic_8 : C 100 8 (9/100) /
    (((100 : ℕ).choose 8 : ℝ) * (7/10)^8) ≤ (genericNumerator 8 : ℝ) / 10^12 := by
  apply normalized_C_le 100 8 (9/100) (7/10) _ (by decide) (by decide)
    (by norm_num) (by positivity)
  have hc : (100 : ℕ).choose 8 = 186087894300 := by
    rw [Nat.choose_eq_factorial_div_factorial (by decide)]
    norm_num [Nat.factorial]
  norm_num [genericNumerator, hc]

private lemma actual_8 : ‖r.esymm 8‖ /
    (((100 : ℕ).choose 8 : ℝ) * (7/10)^8) ≤ (actualNumerator 8 : ℝ) / 10^12 := by
  rw [esymm_exact 8 (by decide)]
  have hc : (100 : ℕ).choose 8 = 186087894300 := by
    rw [Nat.choose_eq_factorial_div_factorial (by decide)]
    norm_num [Nat.factorial]
  have hd : (50 : ℕ).choose 46 = 230300 := by
    rw [Nat.choose_eq_factorial_div_factorial (by decide)]
    norm_num [Nat.factorial]
  norm_num [hc, hd, actualNumerator, norm_mul, norm_pow, norm_div]

private lemma generic_9 : C 100 9 (9/100) /
    (((100 : ℕ).choose 9 : ℝ) * (7/10)^9) ≤ (genericNumerator 9 : ℝ) / 10^12 := by
  apply normalized_C_le 100 9 (9/100) (7/10) _ (by decide) (by decide)
    (by norm_num) (by positivity)
  have hc : (100 : ℕ).choose 9 = 1902231808400 := by
    rw [Nat.choose_eq_factorial_div_factorial (by decide)]
    norm_num [Nat.factorial]
  norm_num [genericNumerator, hc]

private lemma actual_9 : ‖r.esymm 9‖ /
    (((100 : ℕ).choose 9 : ℝ) * (7/10)^9) ≤ (actualNumerator 9 : ℝ) / 10^12 := by
  rw [esymm_exact 9 (by decide)]
  norm_num [actualNumerator]

private lemma generic_10 : C 100 10 (9/100) /
    (((100 : ℕ).choose 10 : ℝ) * (7/10)^10) ≤ (genericNumerator 10 : ℝ) / 10^12 := by
  apply normalized_C_le 100 10 (9/100) (7/10) _ (by decide) (by decide)
    (by norm_num) (by positivity)
  have hc : (100 : ℕ).choose 10 = 17310309456440 := by
    rw [Nat.choose_eq_factorial_div_factorial (by decide)]
    norm_num [Nat.factorial]
  norm_num [genericNumerator, hc]

private lemma actual_10 : ‖r.esymm 10‖ /
    (((100 : ℕ).choose 10 : ℝ) * (7/10)^10) ≤ (actualNumerator 10 : ℝ) / 10^12 := by
  rw [esymm_exact 10 (by decide)]
  have hc : (100 : ℕ).choose 10 = 17310309456440 := by
    rw [Nat.choose_eq_factorial_div_factorial (by decide)]
    norm_num [Nat.factorial]
  have hd : (50 : ℕ).choose 45 = 2118760 := by
    rw [Nat.choose_eq_factorial_div_factorial (by decide)]
    norm_num [Nat.factorial]
  norm_num [hc, hd, actualNumerator, norm_mul, norm_pow, norm_div]

private lemma generic_11 : C 100 11 (9/100) /
    (((100 : ℕ).choose 11 : ℝ) * (7/10)^11) ≤ (genericNumerator 11 : ℝ) / 10^12 := by
  apply normalized_C_le 100 11 (9/100) (7/10) _ (by decide) (by decide)
    (by norm_num) (by positivity)
  have hc : (100 : ℕ).choose 11 = 141629804643600 := by
    rw [Nat.choose_eq_factorial_div_factorial (by decide)]
    norm_num [Nat.factorial]
  norm_num [genericNumerator, hc]

private lemma actual_11 : ‖r.esymm 11‖ /
    (((100 : ℕ).choose 11 : ℝ) * (7/10)^11) ≤ (actualNumerator 11 : ℝ) / 10^12 := by
  rw [esymm_exact 11 (by decide)]
  norm_num [actualNumerator]

private lemma generic_12 : C 100 12 (9/100) /
    (((100 : ℕ).choose 12 : ℝ) * (7/10)^12) ≤ (genericNumerator 12 : ℝ) / 10^12 := by
  apply normalized_C_le 100 12 (9/100) (7/10) _ (by decide) (by decide)
    (by norm_num) (by positivity)
  have hc : (100 : ℕ).choose 12 = 1050421051106700 := by
    rw [Nat.choose_eq_factorial_div_factorial (by decide)]
    norm_num [Nat.factorial]
  norm_num [genericNumerator, hc]

private lemma actual_12 : ‖r.esymm 12‖ /
    (((100 : ℕ).choose 12 : ℝ) * (7/10)^12) ≤ (actualNumerator 12 : ℝ) / 10^12 := by
  rw [esymm_exact 12 (by decide)]
  have hc : (100 : ℕ).choose 12 = 1050421051106700 := by
    rw [Nat.choose_eq_factorial_div_factorial (by decide)]
    norm_num [Nat.factorial]
  have hd : (50 : ℕ).choose 44 = 15890700 := by
    rw [Nat.choose_eq_factorial_div_factorial (by decide)]
    norm_num [Nat.factorial]
  norm_num [hc, hd, actualNumerator, norm_mul, norm_pow, norm_div]

private lemma generic_13 : C 100 13 (9/100) /
    (((100 : ℕ).choose 13 : ℝ) * (7/10)^13) ≤ (genericNumerator 13 : ℝ) / 10^12 := by
  apply normalized_C_le 100 13 (9/100) (7/10) _ (by decide) (by decide)
    (by norm_num) (by positivity)
  have hc : (100 : ℕ).choose 13 = 7110542499799200 := by
    rw [Nat.choose_eq_factorial_div_factorial (by decide)]
    norm_num [Nat.factorial]
  norm_num [genericNumerator, hc]

private lemma actual_13 : ‖r.esymm 13‖ /
    (((100 : ℕ).choose 13 : ℝ) * (7/10)^13) ≤ (actualNumerator 13 : ℝ) / 10^12 := by
  rw [esymm_exact 13 (by decide)]
  norm_num [actualNumerator]

private lemma generic_14 : C 100 14 (9/100) /
    (((100 : ℕ).choose 14 : ℝ) * (7/10)^14) ≤ (genericNumerator 14 : ℝ) / 10^12 := by
  apply normalized_C_le 100 14 (9/100) (7/10) _ (by decide) (by decide)
    (by norm_num) (by positivity)
  have hc : (100 : ℕ).choose 14 = 44186942677323600 := by
    rw [Nat.choose_eq_factorial_div_factorial (by decide)]
    norm_num [Nat.factorial]
  norm_num [genericNumerator, hc]

private lemma actual_14 : ‖r.esymm 14‖ /
    (((100 : ℕ).choose 14 : ℝ) * (7/10)^14) ≤ (actualNumerator 14 : ℝ) / 10^12 := by
  rw [esymm_exact 14 (by decide)]
  have hc : (100 : ℕ).choose 14 = 44186942677323600 := by
    rw [Nat.choose_eq_factorial_div_factorial (by decide)]
    norm_num [Nat.factorial]
  have hd : (50 : ℕ).choose 43 = 99884400 := by
    rw [Nat.choose_eq_factorial_div_factorial (by decide)]
    norm_num [Nat.factorial]
  norm_num [hc, hd, actualNumerator, norm_mul, norm_pow, norm_div]

private lemma generic_15 : C 100 15 (9/100) /
    (((100 : ℕ).choose 15 : ℝ) * (7/10)^15) ≤ (genericNumerator 15 : ℝ) / 10^12 := by
  apply normalized_C_le 100 15 (9/100) (7/10) _ (by decide) (by decide)
    (by norm_num) (by positivity)
  have hc : (100 : ℕ).choose 15 = 253338471349988640 := by
    rw [Nat.choose_eq_factorial_div_factorial (by decide)]
    norm_num [Nat.factorial]
  norm_num [genericNumerator, hc]

private lemma actual_15 : ‖r.esymm 15‖ /
    (((100 : ℕ).choose 15 : ℝ) * (7/10)^15) ≤ (actualNumerator 15 : ℝ) / 10^12 := by
  rw [esymm_exact 15 (by decide)]
  norm_num [actualNumerator]

private lemma generic_16 : C 100 16 (9/100) /
    (((100 : ℕ).choose 16 : ℝ) * (7/10)^16) ≤ (genericNumerator 16 : ℝ) / 10^12 := by
  apply normalized_C_le 100 16 (9/100) (7/10) _ (by decide) (by decide)
    (by norm_num) (by positivity)
  have hc : (100 : ℕ).choose 16 = 1345860629046814650 := by
    rw [Nat.choose_eq_factorial_div_factorial (by decide)]
    norm_num [Nat.factorial]
  norm_num [genericNumerator, hc]

private lemma actual_16 : ‖r.esymm 16‖ /
    (((100 : ℕ).choose 16 : ℝ) * (7/10)^16) ≤ (actualNumerator 16 : ℝ) / 10^12 := by
  rw [esymm_exact 16 (by decide)]
  have hc : (100 : ℕ).choose 16 = 1345860629046814650 := by
    rw [Nat.choose_eq_factorial_div_factorial (by decide)]
    norm_num [Nat.factorial]
  have hd : (50 : ℕ).choose 42 = 536878650 := by
    rw [Nat.choose_eq_factorial_div_factorial (by decide)]
    norm_num [Nat.factorial]
  norm_num [hc, hd, actualNumerator, norm_mul, norm_pow, norm_div]

private lemma generic_17 : C 100 17 (9/100) /
    (((100 : ℕ).choose 17 : ℝ) * (7/10)^17) ≤ (genericNumerator 17 : ℝ) / 10^12 := by
  apply normalized_C_le 100 17 (9/100) (7/10) _ (by decide) (by decide)
    (by norm_num) (by positivity)
  have hc : (100 : ℕ).choose 17 = 6650134872937201800 := by
    rw [Nat.choose_eq_factorial_div_factorial (by decide)]
    norm_num [Nat.factorial]
  norm_num [genericNumerator, hc]

private lemma actual_17 : ‖r.esymm 17‖ /
    (((100 : ℕ).choose 17 : ℝ) * (7/10)^17) ≤ (actualNumerator 17 : ℝ) / 10^12 := by
  rw [esymm_exact 17 (by decide)]
  norm_num [actualNumerator]

private lemma generic_18 : C 100 18 (9/100) /
    (((100 : ℕ).choose 18 : ℝ) * (7/10)^18) ≤ (genericNumerator 18 : ℝ) / 10^12 := by
  apply normalized_C_le 100 18 (9/100) (7/10) _ (by decide) (by decide)
    (by norm_num) (by positivity)
  have hc : (100 : ℕ).choose 18 = 30664510802988208300 := by
    rw [Nat.choose_eq_factorial_div_factorial (by decide)]
    norm_num [Nat.factorial]
  norm_num [genericNumerator, hc]

private lemma actual_18 : ‖r.esymm 18‖ /
    (((100 : ℕ).choose 18 : ℝ) * (7/10)^18) ≤ (actualNumerator 18 : ℝ) / 10^12 := by
  rw [esymm_exact 18 (by decide)]
  have hc : (100 : ℕ).choose 18 = 30664510802988208300 := by
    rw [Nat.choose_eq_factorial_div_factorial (by decide)]
    norm_num [Nat.factorial]
  have hd : (50 : ℕ).choose 41 = 2505433700 := by
    rw [Nat.choose_eq_factorial_div_factorial (by decide)]
    norm_num [Nat.factorial]
  norm_num [hc, hd, actualNumerator, norm_mul, norm_pow, norm_div]

private lemma generic_19 : C 100 19 (9/100) /
    (((100 : ℕ).choose 19 : ℝ) * (7/10)^19) ≤ (genericNumerator 19 : ℝ) / 10^12 := by
  apply normalized_C_le 100 19 (9/100) (7/10) _ (by decide) (by decide)
    (by norm_num) (by positivity)
  have hc : (100 : ℕ).choose 19 = 132341572939212267400 := by
    rw [Nat.choose_eq_factorial_div_factorial (by decide)]
    norm_num [Nat.factorial]
  norm_num [genericNumerator, hc]

private lemma actual_19 : ‖r.esymm 19‖ /
    (((100 : ℕ).choose 19 : ℝ) * (7/10)^19) ≤ (actualNumerator 19 : ℝ) / 10^12 := by
  rw [esymm_exact 19 (by decide)]
  norm_num [actualNumerator]

private lemma generic_20 : C 100 20 (9/100) /
    (((100 : ℕ).choose 20 : ℝ) * (7/10)^20) ≤ (genericNumerator 20 : ℝ) / 10^12 := by
  apply normalized_C_le 100 20 (9/100) (7/10) _ (by decide) (by decide)
    (by norm_num) (by positivity)
  have hc : (100 : ℕ).choose 20 = 535983370403809682970 := by
    rw [Nat.choose_eq_factorial_div_factorial (by decide)]
    norm_num [Nat.factorial]
  norm_num [genericNumerator, hc]

private lemma actual_20 : ‖r.esymm 20‖ /
    (((100 : ℕ).choose 20 : ℝ) * (7/10)^20) ≤ (actualNumerator 20 : ℝ) / 10^12 := by
  rw [esymm_exact 20 (by decide)]
  have hc : (100 : ℕ).choose 20 = 535983370403809682970 := by
    rw [Nat.choose_eq_factorial_div_factorial (by decide)]
    norm_num [Nat.factorial]
  have hd : (50 : ℕ).choose 40 = 10272278170 := by
    rw [Nat.choose_eq_factorial_div_factorial (by decide)]
    norm_num [Nat.factorial]
  norm_num [hc, hd, actualNumerator, norm_mul, norm_pow, norm_div]

private lemma generic_21 : C 100 21 (9/100) /
    (((100 : ℕ).choose 21 : ℝ) * (7/10)^21) ≤ (genericNumerator 21 : ℝ) / 10^12 := by
  apply normalized_C_le 100 21 (9/100) (7/10) _ (by decide) (by decide)
    (by norm_num) (by positivity)
  have hc : (100 : ℕ).choose 21 = 2041841411062132125600 := by
    rw [Nat.choose_eq_factorial_div_factorial (by decide)]
    norm_num [Nat.factorial]
  norm_num [genericNumerator, hc]

private lemma actual_21 : ‖r.esymm 21‖ /
    (((100 : ℕ).choose 21 : ℝ) * (7/10)^21) ≤ (actualNumerator 21 : ℝ) / 10^12 := by
  rw [esymm_exact 21 (by decide)]
  norm_num [actualNumerator]

private lemma generic_22 : C 100 22 (9/100) /
    (((100 : ℕ).choose 22 : ℝ) * (7/10)^22) ≤ (genericNumerator 22 : ℝ) / 10^12 := by
  apply normalized_C_le 100 22 (9/100) (7/10) _ (by decide) (by decide)
    (by norm_num) (by positivity)
  have hc : (100 : ℕ).choose 22 = 7332066885177656269200 := by
    rw [Nat.choose_eq_factorial_div_factorial (by decide)]
    norm_num [Nat.factorial]
  norm_num [genericNumerator, hc]

private lemma actual_22 : ‖r.esymm 22‖ /
    (((100 : ℕ).choose 22 : ℝ) * (7/10)^22) ≤ (actualNumerator 22 : ℝ) / 10^12 := by
  rw [esymm_exact 22 (by decide)]
  have hc : (100 : ℕ).choose 22 = 7332066885177656269200 := by
    rw [Nat.choose_eq_factorial_div_factorial (by decide)]
    norm_num [Nat.factorial]
  have hd : (50 : ℕ).choose 39 = 37353738800 := by
    rw [Nat.choose_eq_factorial_div_factorial (by decide)]
    norm_num [Nat.factorial]
  norm_num [hc, hd, actualNumerator, norm_mul, norm_pow, norm_div]

private lemma generic_23 : C 100 23 (9/100) /
    (((100 : ℕ).choose 23 : ℝ) * (7/10)^23) ≤ (genericNumerator 23 : ℝ) / 10^12 := by
  apply normalized_C_le 100 23 (9/100) (7/10) _ (by decide) (by decide)
    (by norm_num) (by positivity)
  have hc : (100 : ℕ).choose 23 = 24865270306254660391200 := by
    rw [Nat.choose_eq_factorial_div_factorial (by decide)]
    norm_num [Nat.factorial]
  norm_num [genericNumerator, hc]

private lemma actual_23 : ‖r.esymm 23‖ /
    (((100 : ℕ).choose 23 : ℝ) * (7/10)^23) ≤ (actualNumerator 23 : ℝ) / 10^12 := by
  rw [esymm_exact 23 (by decide)]
  norm_num [actualNumerator]

private lemma generic_24 : C 100 24 (9/100) /
    (((100 : ℕ).choose 24 : ℝ) * (7/10)^24) ≤ (genericNumerator 24 : ℝ) / 10^12 := by
  apply normalized_C_le 100 24 (9/100) (7/10) _ (by decide) (by decide)
    (by norm_num) (by positivity)
  have hc : (100 : ℕ).choose 24 = 79776075565900368755100 := by
    rw [Nat.choose_eq_factorial_div_factorial (by decide)]
    norm_num [Nat.factorial]
  norm_num [genericNumerator, hc]

private lemma actual_24 : ‖r.esymm 24‖ /
    (((100 : ℕ).choose 24 : ℝ) * (7/10)^24) ≤ (actualNumerator 24 : ℝ) / 10^12 := by
  rw [esymm_exact 24 (by decide)]
  have hc : (100 : ℕ).choose 24 = 79776075565900368755100 := by
    rw [Nat.choose_eq_factorial_div_factorial (by decide)]
    norm_num [Nat.factorial]
  have hd : (50 : ℕ).choose 38 = 121399651100 := by
    rw [Nat.choose_eq_factorial_div_factorial (by decide)]
    norm_num [Nat.factorial]
  norm_num [hc, hd, actualNumerator, norm_mul, norm_pow, norm_div]

private lemma generic_25 : C 100 25 (9/100) /
    (((100 : ℕ).choose 25 : ℝ) * (7/10)^25) ≤ (genericNumerator 25 : ℝ) / 10^12 := by
  apply normalized_C_le 100 25 (9/100) (7/10) _ (by decide) (by decide)
    (by norm_num) (by positivity)
  have hc : (100 : ℕ).choose 25 = 242519269720337121015504 := by
    rw [Nat.choose_eq_factorial_div_factorial (by decide)]
    norm_num [Nat.factorial]
  norm_num [genericNumerator, hc]

private lemma actual_25 : ‖r.esymm 25‖ /
    (((100 : ℕ).choose 25 : ℝ) * (7/10)^25) ≤ (actualNumerator 25 : ℝ) / 10^12 := by
  rw [esymm_exact 25 (by decide)]
  norm_num [actualNumerator]

private lemma generic_26 : C 100 26 (9/100) /
    (((100 : ℕ).choose 26 : ℝ) * (7/10)^26) ≤ (genericNumerator 26 : ℝ) / 10^12 := by
  apply normalized_C_le 100 26 (9/100) (7/10) _ (by decide) (by decide)
    (by norm_num) (by positivity)
  have hc : (100 : ℕ).choose 26 = 699574816500972464467800 := by
    rw [Nat.choose_eq_factorial_div_factorial (by decide)]
    norm_num [Nat.factorial]
  norm_num [genericNumerator, hc]

private lemma actual_26 : ‖r.esymm 26‖ /
    (((100 : ℕ).choose 26 : ℝ) * (7/10)^26) ≤ (actualNumerator 26 : ℝ) / 10^12 := by
  rw [esymm_exact 26 (by decide)]
  have hc : (100 : ℕ).choose 26 = 699574816500972464467800 := by
    rw [Nat.choose_eq_factorial_div_factorial (by decide)]
    norm_num [Nat.factorial]
  have hd : (50 : ℕ).choose 37 = 354860518600 := by
    rw [Nat.choose_eq_factorial_div_factorial (by decide)]
    norm_num [Nat.factorial]
  norm_num [hc, hd, actualNumerator, norm_mul, norm_pow, norm_div]

private lemma generic_27 : C 100 27 (9/100) /
    (((100 : ℕ).choose 27 : ℝ) * (7/10)^27) ≤ (genericNumerator 27 : ℝ) / 10^12 := by
  apply normalized_C_le 100 27 (9/100) (7/10) _ (by decide) (by decide)
    (by norm_num) (by positivity)
  have hc : (100 : ℕ).choose 27 = 1917353200780443050763600 := by
    rw [Nat.choose_eq_factorial_div_factorial (by decide)]
    norm_num [Nat.factorial]
  norm_num [genericNumerator, hc]

private lemma actual_27 : ‖r.esymm 27‖ /
    (((100 : ℕ).choose 27 : ℝ) * (7/10)^27) ≤ (actualNumerator 27 : ℝ) / 10^12 := by
  rw [esymm_exact 27 (by decide)]
  norm_num [actualNumerator]

private lemma generic_28 : C 100 28 (9/100) /
    (((100 : ℕ).choose 28 : ℝ) * (7/10)^28) ≤ (genericNumerator 28 : ℝ) / 10^12 := by
  apply normalized_C_le 100 28 (9/100) (7/10) _ (by decide) (by decide)
    (by norm_num) (by positivity)
  have hc : (100 : ℕ).choose 28 = 4998813702034726525205100 := by
    rw [Nat.choose_eq_factorial_div_factorial (by decide)]
    norm_num [Nat.factorial]
  norm_num [genericNumerator, hc]

private lemma actual_28 : ‖r.esymm 28‖ /
    (((100 : ℕ).choose 28 : ℝ) * (7/10)^28) ≤ (actualNumerator 28 : ℝ) / 10^12 := by
  rw [esymm_exact 28 (by decide)]
  have hc : (100 : ℕ).choose 28 = 4998813702034726525205100 := by
    rw [Nat.choose_eq_factorial_div_factorial (by decide)]
    norm_num [Nat.factorial]
  have hd : (50 : ℕ).choose 36 = 937845656300 := by
    rw [Nat.choose_eq_factorial_div_factorial (by decide)]
    norm_num [Nat.factorial]
  norm_num [hc, hd, actualNumerator, norm_mul, norm_pow, norm_div]

private lemma generic_29 : C 100 29 (9/100) /
    (((100 : ℕ).choose 29 : ℝ) * (7/10)^29) ≤ (genericNumerator 29 : ℝ) / 10^12 := by
  apply normalized_C_le 100 29 (9/100) (7/10) _ (by decide) (by decide)
    (by norm_num) (by positivity)
  have hc : (100 : ℕ).choose 29 = 12410847811948286545336800 := by
    rw [Nat.choose_eq_factorial_div_factorial (by decide)]
    norm_num [Nat.factorial]
  norm_num [genericNumerator, hc]

private lemma actual_29 : ‖r.esymm 29‖ /
    (((100 : ℕ).choose 29 : ℝ) * (7/10)^29) ≤ (actualNumerator 29 : ℝ) / 10^12 := by
  rw [esymm_exact 29 (by decide)]
  norm_num [actualNumerator]

private lemma generic_30 : C 100 30 (9/100) /
    (((100 : ℕ).choose 30 : ℝ) * (7/10)^30) ≤ (genericNumerator 30 : ℝ) / 10^12 := by
  apply normalized_C_le 100 30 (9/100) (7/10) _ (by decide) (by decide)
    (by norm_num) (by positivity)
  have hc : (100 : ℕ).choose 30 = 29372339821610944823963760 := by
    rw [Nat.choose_eq_factorial_div_factorial (by decide)]
    norm_num [Nat.factorial]
  norm_num [genericNumerator, hc]

private lemma actual_30 : ‖r.esymm 30‖ /
    (((100 : ℕ).choose 30 : ℝ) * (7/10)^30) ≤ (actualNumerator 30 : ℝ) / 10^12 := by
  rw [esymm_exact 30 (by decide)]
  have hc : (100 : ℕ).choose 30 = 29372339821610944823963760 := by
    rw [Nat.choose_eq_factorial_div_factorial (by decide)]
    norm_num [Nat.factorial]
  have hd : (50 : ℕ).choose 35 = 2250829575120 := by
    rw [Nat.choose_eq_factorial_div_factorial (by decide)]
    norm_num [Nat.factorial]
  norm_num [hc, hd, actualNumerator, norm_mul, norm_pow, norm_div]

private lemma generic_31 : C 100 31 (9/100) /
    (((100 : ℕ).choose 31 : ℝ) * (7/10)^31) ≤ (genericNumerator 31 : ℝ) / 10^12 := by
  apply normalized_C_le 100 31 (9/100) (7/10) _ (by decide) (by decide)
    (by norm_num) (by positivity)
  have hc : (100 : ℕ).choose 31 = 66324638306863423796047200 := by
    rw [Nat.choose_eq_factorial_div_factorial (by decide)]
    norm_num [Nat.factorial]
  norm_num [genericNumerator, hc]

private lemma actual_31 : ‖r.esymm 31‖ /
    (((100 : ℕ).choose 31 : ℝ) * (7/10)^31) ≤ (actualNumerator 31 : ℝ) / 10^12 := by
  rw [esymm_exact 31 (by decide)]
  norm_num [actualNumerator]

private lemma generic_32 : C 100 32 (9/100) /
    (((100 : ℕ).choose 32 : ℝ) * (7/10)^32) ≤ (genericNumerator 32 : ℝ) / 10^12 := by
  apply normalized_C_le 100 32 (9/100) (7/10) _ (by decide) (by decide)
    (by norm_num) (by positivity)
  have hc : (100 : ℕ).choose 32 = 143012501349174257560226775 := by
    rw [Nat.choose_eq_factorial_div_factorial (by decide)]
    norm_num [Nat.factorial]
  norm_num [genericNumerator, hc]

private lemma actual_32 : ‖r.esymm 32‖ /
    (((100 : ℕ).choose 32 : ℝ) * (7/10)^32) ≤ (actualNumerator 32 : ℝ) / 10^12 := by
  rw [esymm_exact 32 (by decide)]
  have hc : (100 : ℕ).choose 32 = 143012501349174257560226775 := by
    rw [Nat.choose_eq_factorial_div_factorial (by decide)]
    norm_num [Nat.factorial]
  have hd : (50 : ℕ).choose 34 = 4923689695575 := by
    rw [Nat.choose_eq_factorial_div_factorial (by decide)]
    norm_num [Nat.factorial]
  norm_num [hc, hd, actualNumerator, norm_mul, norm_pow, norm_div]

private lemma generic_33 : C 100 33 (9/100) /
    (((100 : ℕ).choose 33 : ℝ) * (7/10)^33) ≤ (genericNumerator 33 : ℝ) / 10^12 := by
  apply normalized_C_le 100 33 (9/100) (7/10) _ (by decide) (by decide)
    (by norm_num) (by positivity)
  have hc : (100 : ℕ).choose 33 = 294692427022540894366527900 := by
    rw [Nat.choose_eq_factorial_div_factorial (by decide)]
    norm_num [Nat.factorial]
  norm_num [genericNumerator, hc]

private lemma actual_33 : ‖r.esymm 33‖ /
    (((100 : ℕ).choose 33 : ℝ) * (7/10)^33) ≤ (actualNumerator 33 : ℝ) / 10^12 := by
  rw [esymm_exact 33 (by decide)]
  norm_num [actualNumerator]

private lemma generic_34 : C 100 34 (9/100) /
    (((100 : ℕ).choose 34 : ℝ) * (7/10)^34) ≤ (genericNumerator 34 : ℝ) / 10^12 := by
  apply normalized_C_le 100 34 (9/100) (7/10) _ (by decide) (by decide)
    (by norm_num) (by positivity)
  have hc : (100 : ℕ).choose 34 = 580717429720889409486981450 := by
    rw [Nat.choose_eq_factorial_div_factorial (by decide)]
    norm_num [Nat.factorial]
  norm_num [genericNumerator, hc]

private lemma actual_34 : ‖r.esymm 34‖ /
    (((100 : ℕ).choose 34 : ℝ) * (7/10)^34) ≤ (actualNumerator 34 : ℝ) / 10^12 := by
  rw [esymm_exact 34 (by decide)]
  have hc : (100 : ℕ).choose 34 = 580717429720889409486981450 := by
    rw [Nat.choose_eq_factorial_div_factorial (by decide)]
    norm_num [Nat.factorial]
  have hd : (50 : ℕ).choose 33 = 9847379391150 := by
    rw [Nat.choose_eq_factorial_div_factorial (by decide)]
    norm_num [Nat.factorial]
  norm_num [hc, hd, actualNumerator, norm_mul, norm_pow, norm_div]

private lemma generic_35 : C 100 35 (9/100) /
    (((100 : ℕ).choose 35 : ℝ) * (7/10)^35) ≤ (genericNumerator 35 : ℝ) / 10^12 := by
  apply normalized_C_le 100 35 (9/100) (7/10) _ (by decide) (by decide)
    (by norm_num) (by positivity)
  have hc : (100 : ℕ).choose 35 = 1095067153187962886461165020 := by
    rw [Nat.choose_eq_factorial_div_factorial (by decide)]
    norm_num [Nat.factorial]
  norm_num [genericNumerator, hc]

private lemma actual_35 : ‖r.esymm 35‖ /
    (((100 : ℕ).choose 35 : ℝ) * (7/10)^35) ≤ (actualNumerator 35 : ℝ) / 10^12 := by
  rw [esymm_exact 35 (by decide)]
  norm_num [actualNumerator]

private lemma generic_36 : C 100 36 (9/100) /
    (((100 : ℕ).choose 36 : ℝ) * (7/10)^36) ≤ (genericNumerator 36 : ℝ) / 10^12 := by
  apply normalized_C_le 100 36 (9/100) (7/10) _ (by decide) (by decide)
    (by norm_num) (by positivity)
  have hc : (100 : ℕ).choose 36 = 1977204582144932989443770175 := by
    rw [Nat.choose_eq_factorial_div_factorial (by decide)]
    norm_num [Nat.factorial]
  norm_num [genericNumerator, hc]

private lemma actual_36 : ‖r.esymm 36‖ /
    (((100 : ℕ).choose 36 : ℝ) * (7/10)^36) ≤ (actualNumerator 36 : ℝ) / 10^12 := by
  rw [esymm_exact 36 (by decide)]
  have hc : (100 : ℕ).choose 36 = 1977204582144932989443770175 := by
    rw [Nat.choose_eq_factorial_div_factorial (by decide)]
    norm_num [Nat.factorial]
  have hd : (50 : ℕ).choose 32 = 18053528883775 := by
    rw [Nat.choose_eq_factorial_div_factorial (by decide)]
    norm_num [Nat.factorial]
  norm_num [hc, hd, actualNumerator, norm_mul, norm_pow, norm_div]

private lemma generic_37 : C 100 37 (9/100) /
    (((100 : ℕ).choose 37 : ℝ) * (7/10)^37) ≤ (genericNumerator 37 : ℝ) / 10^12 := by
  apply normalized_C_le 100 37 (9/100) (7/10) _ (by decide) (by decide)
    (by norm_num) (by positivity)
  have hc : (100 : ℕ).choose 37 = 3420029547493938143902737600 := by
    rw [Nat.choose_eq_factorial_div_factorial (by decide)]
    norm_num [Nat.factorial]
  norm_num [genericNumerator, hc]

private lemma actual_37 : ‖r.esymm 37‖ /
    (((100 : ℕ).choose 37 : ℝ) * (7/10)^37) ≤ (actualNumerator 37 : ℝ) / 10^12 := by
  rw [esymm_exact 37 (by decide)]
  norm_num [actualNumerator]

private lemma generic_38 : C 100 38 (9/100) /
    (((100 : ℕ).choose 38 : ℝ) * (7/10)^38) ≤ (genericNumerator 38 : ℝ) / 10^12 := by
  apply normalized_C_le 100 38 (9/100) (7/10) _ (by decide) (by decide)
    (by norm_num) (by positivity)
  have hc : (100 : ℕ).choose 38 = 5670048986634686922786117600 := by
    rw [Nat.choose_eq_factorial_div_factorial (by decide)]
    norm_num [Nat.factorial]
  norm_num [genericNumerator, hc]

private lemma actual_38 : ‖r.esymm 38‖ /
    (((100 : ℕ).choose 38 : ℝ) * (7/10)^38) ≤ (actualNumerator 38 : ℝ) / 10^12 := by
  rw [esymm_exact 38 (by decide)]
  have hc : (100 : ℕ).choose 38 = 5670048986634686922786117600 := by
    rw [Nat.choose_eq_factorial_div_factorial (by decide)]
    norm_num [Nat.factorial]
  have hd : (50 : ℕ).choose 31 = 30405943383200 := by
    rw [Nat.choose_eq_factorial_div_factorial (by decide)]
    norm_num [Nat.factorial]
  norm_num [hc, hd, actualNumerator, norm_mul, norm_pow, norm_div]

private lemma generic_39 : C 100 39 (9/100) /
    (((100 : ℕ).choose 39 : ℝ) * (7/10)^39) ≤ (genericNumerator 39 : ℝ) / 10^12 := by
  apply normalized_C_le 100 39 (9/100) (7/10) _ (by decide) (by decide)
    (by norm_num) (by positivity)
  have hc : (100 : ℕ).choose 39 = 9013924030034630492634340800 := by
    rw [Nat.choose_eq_factorial_div_factorial (by decide)]
    norm_num [Nat.factorial]
  norm_num [genericNumerator, hc]

private lemma actual_39 : ‖r.esymm 39‖ /
    (((100 : ℕ).choose 39 : ℝ) * (7/10)^39) ≤ (actualNumerator 39 : ℝ) / 10^12 := by
  rw [esymm_exact 39 (by decide)]
  norm_num [actualNumerator]

private lemma generic_40 : C 100 40 (9/100) /
    (((100 : ℕ).choose 40 : ℝ) * (7/10)^40) ≤ (genericNumerator 40 : ℝ) / 10^12 := by
  apply normalized_C_le 100 40 (9/100) (7/10) _ (by decide) (by decide)
    (by norm_num) (by positivity)
  have hc : (100 : ℕ).choose 40 = 13746234145802811501267369720 := by
    rw [Nat.choose_eq_factorial_div_factorial (by decide)]
    norm_num [Nat.factorial]
  norm_num [genericNumerator, hc]

private lemma actual_40 : ‖r.esymm 40‖ /
    (((100 : ℕ).choose 40 : ℝ) * (7/10)^40) ≤ (actualNumerator 40 : ℝ) / 10^12 := by
  rw [esymm_exact 40 (by decide)]
  have hc : (100 : ℕ).choose 40 = 13746234145802811501267369720 := by
    rw [Nat.choose_eq_factorial_div_factorial (by decide)]
    norm_num [Nat.factorial]
  have hd : (50 : ℕ).choose 30 = 47129212243960 := by
    rw [Nat.choose_eq_factorial_div_factorial (by decide)]
    norm_num [Nat.factorial]
  norm_num [hc, hd, actualNumerator, norm_mul, norm_pow, norm_div]

private lemma generic_41 : C 100 41 (9/100) /
    (((100 : ℕ).choose 41 : ℝ) * (7/10)^41) ≤ (genericNumerator 41 : ℝ) / 10^12 := by
  apply normalized_C_le 100 41 (9/100) (7/10) _ (by decide) (by decide)
    (by norm_num) (by positivity)
  have hc : (100 : ℕ).choose 41 = 20116440213369968050635175200 := by
    rw [Nat.choose_eq_factorial_div_factorial (by decide)]
    norm_num [Nat.factorial]
  norm_num [genericNumerator, hc]

private lemma actual_41 : ‖r.esymm 41‖ /
    (((100 : ℕ).choose 41 : ℝ) * (7/10)^41) ≤ (actualNumerator 41 : ℝ) / 10^12 := by
  rw [esymm_exact 41 (by decide)]
  norm_num [actualNumerator]

private lemma generic_42 : C 100 42 (9/100) /
    (((100 : ℕ).choose 42 : ℝ) * (7/10)^42) ≤ (genericNumerator 42 : ℝ) / 10^12 := by
  apply normalized_C_le 100 42 (9/100) (7/10) _ (by decide) (by decide)
    (by norm_num) (by positivity)
  have hc : (100 : ℕ).choose 42 = 28258808871162574166368460400 := by
    rw [Nat.choose_eq_factorial_div_factorial (by decide)]
    norm_num [Nat.factorial]
  norm_num [genericNumerator, hc]

private lemma actual_42 : ‖r.esymm 42‖ /
    (((100 : ℕ).choose 42 : ℝ) * (7/10)^42) ≤ (actualNumerator 42 : ℝ) / 10^12 := by
  rw [esymm_exact 42 (by decide)]
  have hc : (100 : ℕ).choose 42 = 28258808871162574166368460400 := by
    rw [Nat.choose_eq_factorial_div_factorial (by decide)]
    norm_num [Nat.factorial]
  have hd : (50 : ℕ).choose 29 = 67327446062800 := by
    rw [Nat.choose_eq_factorial_div_factorial (by decide)]
    norm_num [Nat.factorial]
  norm_num [hc, hd, actualNumerator, norm_mul, norm_pow, norm_div]

private lemma generic_43 : C 100 43 (9/100) /
    (((100 : ℕ).choose 43 : ℝ) * (7/10)^43) ≤ (genericNumerator 43 : ℝ) / 10^12 := by
  apply normalized_C_le 100 43 (9/100) (7/10) _ (by decide) (by decide)
    (by norm_num) (by positivity)
  have hc : (100 : ℕ).choose 43 = 38116532895986727945334202400 := by
    rw [Nat.choose_eq_factorial_div_factorial (by decide)]
    norm_num [Nat.factorial]
  norm_num [genericNumerator, hc]

private lemma actual_43 : ‖r.esymm 43‖ /
    (((100 : ℕ).choose 43 : ℝ) * (7/10)^43) ≤ (actualNumerator 43 : ℝ) / 10^12 := by
  rw [esymm_exact 43 (by decide)]
  norm_num [actualNumerator]

private lemma generic_44 : C 100 44 (9/100) /
    (((100 : ℕ).choose 44 : ℝ) * (7/10)^44) ≤ (genericNumerator 44 : ℝ) / 10^12 := by
  apply normalized_C_le 100 44 (9/100) (7/10) _ (by decide) (by decide)
    (by norm_num) (by positivity)
  have hc : (100 : ℕ).choose 44 = 49378235797073715747364762200 := by
    rw [Nat.choose_eq_factorial_div_factorial (by decide)]
    norm_num [Nat.factorial]
  norm_num [genericNumerator, hc]

private lemma actual_44 : ‖r.esymm 44‖ /
    (((100 : ℕ).choose 44 : ℝ) * (7/10)^44) ≤ (actualNumerator 44 : ℝ) / 10^12 := by
  rw [esymm_exact 44 (by decide)]
  have hc : (100 : ℕ).choose 44 = 49378235797073715747364762200 := by
    rw [Nat.choose_eq_factorial_div_factorial (by decide)]
    norm_num [Nat.factorial]
  have hd : (50 : ℕ).choose 28 = 88749815264600 := by
    rw [Nat.choose_eq_factorial_div_factorial (by decide)]
    norm_num [Nat.factorial]
  norm_num [hc, hd, actualNumerator, norm_mul, norm_pow, norm_div]

private lemma generic_45 : C 100 45 (9/100) /
    (((100 : ℕ).choose 45 : ℝ) * (7/10)^45) ≤ (genericNumerator 45 : ℝ) / 10^12 := by
  apply normalized_C_le 100 45 (9/100) (7/10) _ (by decide) (by decide)
    (by norm_num) (by positivity)
  have hc : (100 : ℕ).choose 45 = 61448471214136179596720592960 := by
    rw [Nat.choose_eq_factorial_div_factorial (by decide)]
    norm_num [Nat.factorial]
  norm_num [genericNumerator, hc]

private lemma actual_45 : ‖r.esymm 45‖ /
    (((100 : ℕ).choose 45 : ℝ) * (7/10)^45) ≤ (actualNumerator 45 : ℝ) / 10^12 := by
  rw [esymm_exact 45 (by decide)]
  norm_num [actualNumerator]

private lemma generic_46 : C 100 46 (9/100) /
    (((100 : ℕ).choose 46 : ℝ) * (7/10)^46) ≤ (genericNumerator 46 : ℝ) / 10^12 := by
  apply normalized_C_le 100 46 (9/100) (7/10) _ (by decide) (by decide)
    (by norm_num) (by positivity)
  have hc : (100 : ℕ).choose 46 = 73470998190814997343905056800 := by
    rw [Nat.choose_eq_factorial_div_factorial (by decide)]
    norm_num [Nat.factorial]
  norm_num [genericNumerator, hc]

private lemma actual_46 : ‖r.esymm 46‖ /
    (((100 : ℕ).choose 46 : ℝ) * (7/10)^46) ≤ (actualNumerator 46 : ℝ) / 10^12 := by
  rw [esymm_exact 46 (by decide)]
  have hc : (100 : ℕ).choose 46 = 73470998190814997343905056800 := by
    rw [Nat.choose_eq_factorial_div_factorial (by decide)]
    norm_num [Nat.factorial]
  have hd : (50 : ℕ).choose 27 = 108043253365600 := by
    rw [Nat.choose_eq_factorial_div_factorial (by decide)]
    norm_num [Nat.factorial]
  norm_num [hc, hd, actualNumerator, norm_mul, norm_pow, norm_div]

private lemma generic_47 : C 100 47 (9/100) /
    (((100 : ℕ).choose 47 : ℝ) * (7/10)^47) ≤ (genericNumerator 47 : ℝ) / 10^12 := by
  apply normalized_C_le 100 47 (9/100) (7/10) _ (by decide) (by decide)
    (by norm_num) (by positivity)
  have hc : (100 : ℕ).choose 47 = 84413487283064039501507937600 := by
    rw [Nat.choose_eq_factorial_div_factorial (by decide)]
    norm_num [Nat.factorial]
  norm_num [genericNumerator, hc]

private lemma actual_47 : ‖r.esymm 47‖ /
    (((100 : ℕ).choose 47 : ℝ) * (7/10)^47) ≤ (actualNumerator 47 : ℝ) / 10^12 := by
  rw [esymm_exact 47 (by decide)]
  norm_num [actualNumerator]

private lemma generic_48 : C 100 48 (9/100) /
    (((100 : ℕ).choose 48 : ℝ) * (7/10)^48) ≤ (genericNumerator 48 : ℝ) / 10^12 := by
  apply normalized_C_le 100 48 (9/100) (7/10) _ (by decide) (by decide)
    (by norm_num) (by positivity)
  have hc : (100 : ℕ).choose 48 = 93206558875049876949581681100 := by
    rw [Nat.choose_eq_factorial_div_factorial (by decide)]
    norm_num [Nat.factorial]
  norm_num [genericNumerator, hc]

private lemma actual_48 : ‖r.esymm 48‖ /
    (((100 : ℕ).choose 48 : ℝ) * (7/10)^48) ≤ (actualNumerator 48 : ℝ) / 10^12 := by
  rw [esymm_exact 48 (by decide)]
  have hc : (100 : ℕ).choose 48 = 93206558875049876949581681100 := by
    rw [Nat.choose_eq_factorial_div_factorial (by decide)]
    norm_num [Nat.factorial]
  have hd : (50 : ℕ).choose 26 = 121548660036300 := by
    rw [Nat.choose_eq_factorial_div_factorial (by decide)]
    norm_num [Nat.factorial]
  norm_num [hc, hd, actualNumerator, norm_mul, norm_pow, norm_div]

private lemma generic_49 : C 100 49 (9/100) /
    (((100 : ℕ).choose 49 : ℝ) * (7/10)^49) ≤ (genericNumerator 49 : ℝ) / 10^12 := by
  apply normalized_C_le 100 49 (9/100) (7/10) _ (by decide) (by decide)
    (by norm_num) (by positivity)
  have hc : (100 : ℕ).choose 49 = 98913082887808032681188722800 := by
    rw [Nat.choose_eq_factorial_div_factorial (by decide)]
    norm_num [Nat.factorial]
  norm_num [genericNumerator, hc]

private lemma actual_49 : ‖r.esymm 49‖ /
    (((100 : ℕ).choose 49 : ℝ) * (7/10)^49) ≤ (actualNumerator 49 : ℝ) / 10^12 := by
  rw [esymm_exact 49 (by decide)]
  norm_num [actualNumerator]

private lemma generic_50 : C 100 50 (9/100) /
    (((100 : ℕ).choose 50 : ℝ) * (7/10)^50) ≤ (genericNumerator 50 : ℝ) / 10^12 := by
  apply normalized_C_le 100 50 (9/100) (7/10) _ (by decide) (by decide)
    (by norm_num) (by positivity)
  have hc : (100 : ℕ).choose 50 = 100891344545564193334812497256 := by
    rw [Nat.choose_eq_factorial_div_factorial (by decide)]
    norm_num [Nat.factorial]
  norm_num [genericNumerator, hc]

private lemma actual_50 : ‖r.esymm 50‖ /
    (((100 : ℕ).choose 50 : ℝ) * (7/10)^50) ≤ (actualNumerator 50 : ℝ) / 10^12 := by
  rw [esymm_exact 50 (by decide)]
  have hc : (100 : ℕ).choose 50 = 100891344545564193334812497256 := by
    rw [Nat.choose_eq_factorial_div_factorial (by decide)]
    norm_num [Nat.factorial]
  have hd : (50 : ℕ).choose 25 = 126410606437752 := by
    rw [Nat.choose_eq_factorial_div_factorial (by decide)]
    norm_num [Nat.factorial]
  norm_num [hc, hd, actualNumerator, norm_mul, norm_pow, norm_div]

private lemma generic_51 : C 100 51 (9/100) /
    (((100 : ℕ).choose 51 : ℝ) * (7/10)^51) ≤ (genericNumerator 51 : ℝ) / 10^12 := by
  apply normalized_C_le 100 51 (9/100) (7/10) _ (by decide) (by decide)
    (by norm_num) (by positivity)
  have hc : (100 : ℕ).choose 51 = 98913082887808032681188722800 := by
    rw [Nat.choose_eq_factorial_div_factorial (by decide)]
    norm_num [Nat.factorial]
  norm_num [genericNumerator, hc]

private lemma actual_51 : ‖r.esymm 51‖ /
    (((100 : ℕ).choose 51 : ℝ) * (7/10)^51) ≤ (actualNumerator 51 : ℝ) / 10^12 := by
  rw [esymm_exact 51 (by decide)]
  norm_num [actualNumerator]

private lemma generic_52 : C 100 52 (9/100) /
    (((100 : ℕ).choose 52 : ℝ) * (7/10)^52) ≤ (genericNumerator 52 : ℝ) / 10^12 := by
  apply normalized_C_le 100 52 (9/100) (7/10) _ (by decide) (by decide)
    (by norm_num) (by positivity)
  have hc : (100 : ℕ).choose 52 = 93206558875049876949581681100 := by
    rw [Nat.choose_eq_factorial_div_factorial (by decide)]
    norm_num [Nat.factorial]
  norm_num [genericNumerator, hc]

private lemma actual_52 : ‖r.esymm 52‖ /
    (((100 : ℕ).choose 52 : ℝ) * (7/10)^52) ≤ (actualNumerator 52 : ℝ) / 10^12 := by
  rw [esymm_exact 52 (by decide)]
  have hc : (100 : ℕ).choose 52 = 93206558875049876949581681100 := by
    rw [Nat.choose_eq_factorial_div_factorial (by decide)]
    norm_num [Nat.factorial]
  have hd : (50 : ℕ).choose 24 = 121548660036300 := by
    rw [Nat.choose_eq_factorial_div_factorial (by decide)]
    norm_num [Nat.factorial]
  norm_num [hc, hd, actualNumerator, norm_mul, norm_pow, norm_div]

private lemma generic_53 : C 100 53 (9/100) /
    (((100 : ℕ).choose 53 : ℝ) * (7/10)^53) ≤ (genericNumerator 53 : ℝ) / 10^12 := by
  apply normalized_C_le 100 53 (9/100) (7/10) _ (by decide) (by decide)
    (by norm_num) (by positivity)
  have hc : (100 : ℕ).choose 53 = 84413487283064039501507937600 := by
    rw [Nat.choose_eq_factorial_div_factorial (by decide)]
    norm_num [Nat.factorial]
  norm_num [genericNumerator, hc]

private lemma actual_53 : ‖r.esymm 53‖ /
    (((100 : ℕ).choose 53 : ℝ) * (7/10)^53) ≤ (actualNumerator 53 : ℝ) / 10^12 := by
  rw [esymm_exact 53 (by decide)]
  norm_num [actualNumerator]

private lemma generic_54 : C 100 54 (9/100) /
    (((100 : ℕ).choose 54 : ℝ) * (7/10)^54) ≤ (genericNumerator 54 : ℝ) / 10^12 := by
  apply normalized_C_le 100 54 (9/100) (7/10) _ (by decide) (by decide)
    (by norm_num) (by positivity)
  have hc : (100 : ℕ).choose 54 = 73470998190814997343905056800 := by
    rw [Nat.choose_eq_factorial_div_factorial (by decide)]
    norm_num [Nat.factorial]
  norm_num [genericNumerator, hc]

private lemma actual_54 : ‖r.esymm 54‖ /
    (((100 : ℕ).choose 54 : ℝ) * (7/10)^54) ≤ (actualNumerator 54 : ℝ) / 10^12 := by
  rw [esymm_exact 54 (by decide)]
  have hc : (100 : ℕ).choose 54 = 73470998190814997343905056800 := by
    rw [Nat.choose_eq_factorial_div_factorial (by decide)]
    norm_num [Nat.factorial]
  have hd : (50 : ℕ).choose 23 = 108043253365600 := by
    rw [Nat.choose_eq_factorial_div_factorial (by decide)]
    norm_num [Nat.factorial]
  norm_num [hc, hd, actualNumerator, norm_mul, norm_pow, norm_div]

private lemma generic_55 : C 100 55 (9/100) /
    (((100 : ℕ).choose 55 : ℝ) * (7/10)^55) ≤ (genericNumerator 55 : ℝ) / 10^12 := by
  apply normalized_C_le 100 55 (9/100) (7/10) _ (by decide) (by decide)
    (by norm_num) (by positivity)
  have hc : (100 : ℕ).choose 55 = 61448471214136179596720592960 := by
    rw [Nat.choose_eq_factorial_div_factorial (by decide)]
    norm_num [Nat.factorial]
  norm_num [genericNumerator, hc]

private lemma actual_55 : ‖r.esymm 55‖ /
    (((100 : ℕ).choose 55 : ℝ) * (7/10)^55) ≤ (actualNumerator 55 : ℝ) / 10^12 := by
  rw [esymm_exact 55 (by decide)]
  norm_num [actualNumerator]

private lemma generic_56 : C 100 56 (9/100) /
    (((100 : ℕ).choose 56 : ℝ) * (7/10)^56) ≤ (genericNumerator 56 : ℝ) / 10^12 := by
  apply normalized_C_le 100 56 (9/100) (7/10) _ (by decide) (by decide)
    (by norm_num) (by positivity)
  have hc : (100 : ℕ).choose 56 = 49378235797073715747364762200 := by
    rw [Nat.choose_eq_factorial_div_factorial (by decide)]
    norm_num [Nat.factorial]
  norm_num [genericNumerator, hc]

private lemma actual_56 : ‖r.esymm 56‖ /
    (((100 : ℕ).choose 56 : ℝ) * (7/10)^56) ≤ (actualNumerator 56 : ℝ) / 10^12 := by
  rw [esymm_exact 56 (by decide)]
  have hc : (100 : ℕ).choose 56 = 49378235797073715747364762200 := by
    rw [Nat.choose_eq_factorial_div_factorial (by decide)]
    norm_num [Nat.factorial]
  have hd : (50 : ℕ).choose 22 = 88749815264600 := by
    rw [Nat.choose_eq_factorial_div_factorial (by decide)]
    norm_num [Nat.factorial]
  norm_num [hc, hd, actualNumerator, norm_mul, norm_pow, norm_div]

private lemma generic_57 : C 100 57 (9/100) /
    (((100 : ℕ).choose 57 : ℝ) * (7/10)^57) ≤ (genericNumerator 57 : ℝ) / 10^12 := by
  apply normalized_C_le 100 57 (9/100) (7/10) _ (by decide) (by decide)
    (by norm_num) (by positivity)
  have hc : (100 : ℕ).choose 57 = 38116532895986727945334202400 := by
    rw [Nat.choose_eq_factorial_div_factorial (by decide)]
    norm_num [Nat.factorial]
  norm_num [genericNumerator, hc]

private lemma actual_57 : ‖r.esymm 57‖ /
    (((100 : ℕ).choose 57 : ℝ) * (7/10)^57) ≤ (actualNumerator 57 : ℝ) / 10^12 := by
  rw [esymm_exact 57 (by decide)]
  norm_num [actualNumerator]

private lemma generic_58 : C 100 58 (9/100) /
    (((100 : ℕ).choose 58 : ℝ) * (7/10)^58) ≤ (genericNumerator 58 : ℝ) / 10^12 := by
  apply normalized_C_le 100 58 (9/100) (7/10) _ (by decide) (by decide)
    (by norm_num) (by positivity)
  have hc : (100 : ℕ).choose 58 = 28258808871162574166368460400 := by
    rw [Nat.choose_eq_factorial_div_factorial (by decide)]
    norm_num [Nat.factorial]
  norm_num [genericNumerator, hc]

private lemma actual_58 : ‖r.esymm 58‖ /
    (((100 : ℕ).choose 58 : ℝ) * (7/10)^58) ≤ (actualNumerator 58 : ℝ) / 10^12 := by
  rw [esymm_exact 58 (by decide)]
  have hc : (100 : ℕ).choose 58 = 28258808871162574166368460400 := by
    rw [Nat.choose_eq_factorial_div_factorial (by decide)]
    norm_num [Nat.factorial]
  have hd : (50 : ℕ).choose 21 = 67327446062800 := by
    rw [Nat.choose_eq_factorial_div_factorial (by decide)]
    norm_num [Nat.factorial]
  norm_num [hc, hd, actualNumerator, norm_mul, norm_pow, norm_div]

private lemma generic_59 : C 100 59 (9/100) /
    (((100 : ℕ).choose 59 : ℝ) * (7/10)^59) ≤ (genericNumerator 59 : ℝ) / 10^12 := by
  apply normalized_C_le 100 59 (9/100) (7/10) _ (by decide) (by decide)
    (by norm_num) (by positivity)
  have hc : (100 : ℕ).choose 59 = 20116440213369968050635175200 := by
    rw [Nat.choose_eq_factorial_div_factorial (by decide)]
    norm_num [Nat.factorial]
  norm_num [genericNumerator, hc]

private lemma actual_59 : ‖r.esymm 59‖ /
    (((100 : ℕ).choose 59 : ℝ) * (7/10)^59) ≤ (actualNumerator 59 : ℝ) / 10^12 := by
  rw [esymm_exact 59 (by decide)]
  norm_num [actualNumerator]

private lemma generic_60 : C 100 60 (9/100) /
    (((100 : ℕ).choose 60 : ℝ) * (7/10)^60) ≤ (genericNumerator 60 : ℝ) / 10^12 := by
  apply normalized_C_le 100 60 (9/100) (7/10) _ (by decide) (by decide)
    (by norm_num) (by positivity)
  have hc : (100 : ℕ).choose 60 = 13746234145802811501267369720 := by
    rw [Nat.choose_eq_factorial_div_factorial (by decide)]
    norm_num [Nat.factorial]
  norm_num [genericNumerator, hc]

private lemma actual_60 : ‖r.esymm 60‖ /
    (((100 : ℕ).choose 60 : ℝ) * (7/10)^60) ≤ (actualNumerator 60 : ℝ) / 10^12 := by
  rw [esymm_exact 60 (by decide)]
  have hc : (100 : ℕ).choose 60 = 13746234145802811501267369720 := by
    rw [Nat.choose_eq_factorial_div_factorial (by decide)]
    norm_num [Nat.factorial]
  have hd : (50 : ℕ).choose 20 = 47129212243960 := by
    rw [Nat.choose_eq_factorial_div_factorial (by decide)]
    norm_num [Nat.factorial]
  norm_num [hc, hd, actualNumerator, norm_mul, norm_pow, norm_div]

private lemma generic_61 : C 100 61 (9/100) /
    (((100 : ℕ).choose 61 : ℝ) * (7/10)^61) ≤ (genericNumerator 61 : ℝ) / 10^12 := by
  apply normalized_C_le 100 61 (9/100) (7/10) _ (by decide) (by decide)
    (by norm_num) (by positivity)
  have hc : (100 : ℕ).choose 61 = 9013924030034630492634340800 := by
    rw [Nat.choose_eq_factorial_div_factorial (by decide)]
    norm_num [Nat.factorial]
  norm_num [genericNumerator, hc]

private lemma actual_61 : ‖r.esymm 61‖ /
    (((100 : ℕ).choose 61 : ℝ) * (7/10)^61) ≤ (actualNumerator 61 : ℝ) / 10^12 := by
  rw [esymm_exact 61 (by decide)]
  norm_num [actualNumerator]

private lemma generic_62 : C 100 62 (9/100) /
    (((100 : ℕ).choose 62 : ℝ) * (7/10)^62) ≤ (genericNumerator 62 : ℝ) / 10^12 := by
  apply normalized_C_le 100 62 (9/100) (7/10) _ (by decide) (by decide)
    (by norm_num) (by positivity)
  have hc : (100 : ℕ).choose 62 = 5670048986634686922786117600 := by
    rw [Nat.choose_eq_factorial_div_factorial (by decide)]
    norm_num [Nat.factorial]
  norm_num [genericNumerator, hc]

private lemma actual_62 : ‖r.esymm 62‖ /
    (((100 : ℕ).choose 62 : ℝ) * (7/10)^62) ≤ (actualNumerator 62 : ℝ) / 10^12 := by
  rw [esymm_exact 62 (by decide)]
  have hc : (100 : ℕ).choose 62 = 5670048986634686922786117600 := by
    rw [Nat.choose_eq_factorial_div_factorial (by decide)]
    norm_num [Nat.factorial]
  have hd : (50 : ℕ).choose 19 = 30405943383200 := by
    rw [Nat.choose_eq_factorial_div_factorial (by decide)]
    norm_num [Nat.factorial]
  norm_num [hc, hd, actualNumerator, norm_mul, norm_pow, norm_div]

private lemma generic_63 : C 100 63 (9/100) /
    (((100 : ℕ).choose 63 : ℝ) * (7/10)^63) ≤ (genericNumerator 63 : ℝ) / 10^12 := by
  apply normalized_C_le 100 63 (9/100) (7/10) _ (by decide) (by decide)
    (by norm_num) (by positivity)
  have hc : (100 : ℕ).choose 63 = 3420029547493938143902737600 := by
    rw [Nat.choose_eq_factorial_div_factorial (by decide)]
    norm_num [Nat.factorial]
  norm_num [genericNumerator, hc]

private lemma actual_63 : ‖r.esymm 63‖ /
    (((100 : ℕ).choose 63 : ℝ) * (7/10)^63) ≤ (actualNumerator 63 : ℝ) / 10^12 := by
  rw [esymm_exact 63 (by decide)]
  norm_num [actualNumerator]

private lemma generic_64 : C 100 64 (9/100) /
    (((100 : ℕ).choose 64 : ℝ) * (7/10)^64) ≤ (genericNumerator 64 : ℝ) / 10^12 := by
  apply normalized_C_le 100 64 (9/100) (7/10) _ (by decide) (by decide)
    (by norm_num) (by positivity)
  have hc : (100 : ℕ).choose 64 = 1977204582144932989443770175 := by
    rw [Nat.choose_eq_factorial_div_factorial (by decide)]
    norm_num [Nat.factorial]
  norm_num [genericNumerator, hc]

private lemma actual_64 : ‖r.esymm 64‖ /
    (((100 : ℕ).choose 64 : ℝ) * (7/10)^64) ≤ (actualNumerator 64 : ℝ) / 10^12 := by
  rw [esymm_exact 64 (by decide)]
  have hc : (100 : ℕ).choose 64 = 1977204582144932989443770175 := by
    rw [Nat.choose_eq_factorial_div_factorial (by decide)]
    norm_num [Nat.factorial]
  have hd : (50 : ℕ).choose 18 = 18053528883775 := by
    rw [Nat.choose_eq_factorial_div_factorial (by decide)]
    norm_num [Nat.factorial]
  norm_num [hc, hd, actualNumerator, norm_mul, norm_pow, norm_div]

private lemma generic_65 : C 100 65 (9/100) /
    (((100 : ℕ).choose 65 : ℝ) * (7/10)^65) ≤ (genericNumerator 65 : ℝ) / 10^12 := by
  apply normalized_C_le 100 65 (9/100) (7/10) _ (by decide) (by decide)
    (by norm_num) (by positivity)
  have hc : (100 : ℕ).choose 65 = 1095067153187962886461165020 := by
    rw [Nat.choose_eq_factorial_div_factorial (by decide)]
    norm_num [Nat.factorial]
  norm_num [genericNumerator, hc]

private lemma actual_65 : ‖r.esymm 65‖ /
    (((100 : ℕ).choose 65 : ℝ) * (7/10)^65) ≤ (actualNumerator 65 : ℝ) / 10^12 := by
  rw [esymm_exact 65 (by decide)]
  norm_num [actualNumerator]

private lemma generic_66 : C 100 66 (9/100) /
    (((100 : ℕ).choose 66 : ℝ) * (7/10)^66) ≤ (genericNumerator 66 : ℝ) / 10^12 := by
  apply normalized_C_le 100 66 (9/100) (7/10) _ (by decide) (by decide)
    (by norm_num) (by positivity)
  have hc : (100 : ℕ).choose 66 = 580717429720889409486981450 := by
    rw [Nat.choose_eq_factorial_div_factorial (by decide)]
    norm_num [Nat.factorial]
  norm_num [genericNumerator, hc]

private lemma actual_66 : ‖r.esymm 66‖ /
    (((100 : ℕ).choose 66 : ℝ) * (7/10)^66) ≤ (actualNumerator 66 : ℝ) / 10^12 := by
  rw [esymm_exact 66 (by decide)]
  have hc : (100 : ℕ).choose 66 = 580717429720889409486981450 := by
    rw [Nat.choose_eq_factorial_div_factorial (by decide)]
    norm_num [Nat.factorial]
  have hd : (50 : ℕ).choose 17 = 9847379391150 := by
    rw [Nat.choose_eq_factorial_div_factorial (by decide)]
    norm_num [Nat.factorial]
  norm_num [hc, hd, actualNumerator, norm_mul, norm_pow, norm_div]

private lemma generic_67 : C 100 67 (9/100) /
    (((100 : ℕ).choose 67 : ℝ) * (7/10)^67) ≤ (genericNumerator 67 : ℝ) / 10^12 := by
  apply normalized_C_le 100 67 (9/100) (7/10) _ (by decide) (by decide)
    (by norm_num) (by positivity)
  have hc : (100 : ℕ).choose 67 = 294692427022540894366527900 := by
    rw [Nat.choose_eq_factorial_div_factorial (by decide)]
    norm_num [Nat.factorial]
  norm_num [genericNumerator, hc]

private lemma actual_67 : ‖r.esymm 67‖ /
    (((100 : ℕ).choose 67 : ℝ) * (7/10)^67) ≤ (actualNumerator 67 : ℝ) / 10^12 := by
  rw [esymm_exact 67 (by decide)]
  norm_num [actualNumerator]

private lemma generic_68 : C 100 68 (9/100) /
    (((100 : ℕ).choose 68 : ℝ) * (7/10)^68) ≤ (genericNumerator 68 : ℝ) / 10^12 := by
  apply normalized_C_le 100 68 (9/100) (7/10) _ (by decide) (by decide)
    (by norm_num) (by positivity)
  have hc : (100 : ℕ).choose 68 = 143012501349174257560226775 := by
    rw [Nat.choose_eq_factorial_div_factorial (by decide)]
    norm_num [Nat.factorial]
  norm_num [genericNumerator, hc]

private lemma actual_68 : ‖r.esymm 68‖ /
    (((100 : ℕ).choose 68 : ℝ) * (7/10)^68) ≤ (actualNumerator 68 : ℝ) / 10^12 := by
  rw [esymm_exact 68 (by decide)]
  have hc : (100 : ℕ).choose 68 = 143012501349174257560226775 := by
    rw [Nat.choose_eq_factorial_div_factorial (by decide)]
    norm_num [Nat.factorial]
  have hd : (50 : ℕ).choose 16 = 4923689695575 := by
    rw [Nat.choose_eq_factorial_div_factorial (by decide)]
    norm_num [Nat.factorial]
  norm_num [hc, hd, actualNumerator, norm_mul, norm_pow, norm_div]

private lemma generic_69 : C 100 69 (9/100) /
    (((100 : ℕ).choose 69 : ℝ) * (7/10)^69) ≤ (genericNumerator 69 : ℝ) / 10^12 := by
  apply normalized_C_le 100 69 (9/100) (7/10) _ (by decide) (by decide)
    (by norm_num) (by positivity)
  have hc : (100 : ℕ).choose 69 = 66324638306863423796047200 := by
    rw [Nat.choose_eq_factorial_div_factorial (by decide)]
    norm_num [Nat.factorial]
  norm_num [genericNumerator, hc]

private lemma actual_69 : ‖r.esymm 69‖ /
    (((100 : ℕ).choose 69 : ℝ) * (7/10)^69) ≤ (actualNumerator 69 : ℝ) / 10^12 := by
  rw [esymm_exact 69 (by decide)]
  norm_num [actualNumerator]

private lemma generic_70 : C 100 70 (9/100) /
    (((100 : ℕ).choose 70 : ℝ) * (7/10)^70) ≤ (genericNumerator 70 : ℝ) / 10^12 := by
  apply normalized_C_le 100 70 (9/100) (7/10) _ (by decide) (by decide)
    (by norm_num) (by positivity)
  have hc : (100 : ℕ).choose 70 = 29372339821610944823963760 := by
    rw [Nat.choose_eq_factorial_div_factorial (by decide)]
    norm_num [Nat.factorial]
  norm_num [genericNumerator, hc]

private lemma actual_70 : ‖r.esymm 70‖ /
    (((100 : ℕ).choose 70 : ℝ) * (7/10)^70) ≤ (actualNumerator 70 : ℝ) / 10^12 := by
  rw [esymm_exact 70 (by decide)]
  have hc : (100 : ℕ).choose 70 = 29372339821610944823963760 := by
    rw [Nat.choose_eq_factorial_div_factorial (by decide)]
    norm_num [Nat.factorial]
  have hd : (50 : ℕ).choose 15 = 2250829575120 := by
    rw [Nat.choose_eq_factorial_div_factorial (by decide)]
    norm_num [Nat.factorial]
  norm_num [hc, hd, actualNumerator, norm_mul, norm_pow, norm_div]

private lemma generic_71 : C 100 71 (9/100) /
    (((100 : ℕ).choose 71 : ℝ) * (7/10)^71) ≤ (genericNumerator 71 : ℝ) / 10^12 := by
  apply normalized_C_le 100 71 (9/100) (7/10) _ (by decide) (by decide)
    (by norm_num) (by positivity)
  have hc : (100 : ℕ).choose 71 = 12410847811948286545336800 := by
    rw [Nat.choose_eq_factorial_div_factorial (by decide)]
    norm_num [Nat.factorial]
  norm_num [genericNumerator, hc]

private lemma actual_71 : ‖r.esymm 71‖ /
    (((100 : ℕ).choose 71 : ℝ) * (7/10)^71) ≤ (actualNumerator 71 : ℝ) / 10^12 := by
  rw [esymm_exact 71 (by decide)]
  norm_num [actualNumerator]

private lemma generic_72 : C 100 72 (9/100) /
    (((100 : ℕ).choose 72 : ℝ) * (7/10)^72) ≤ (genericNumerator 72 : ℝ) / 10^12 := by
  apply normalized_C_le 100 72 (9/100) (7/10) _ (by decide) (by decide)
    (by norm_num) (by positivity)
  have hc : (100 : ℕ).choose 72 = 4998813702034726525205100 := by
    rw [Nat.choose_eq_factorial_div_factorial (by decide)]
    norm_num [Nat.factorial]
  norm_num [genericNumerator, hc]

private lemma actual_72 : ‖r.esymm 72‖ /
    (((100 : ℕ).choose 72 : ℝ) * (7/10)^72) ≤ (actualNumerator 72 : ℝ) / 10^12 := by
  rw [esymm_exact 72 (by decide)]
  have hc : (100 : ℕ).choose 72 = 4998813702034726525205100 := by
    rw [Nat.choose_eq_factorial_div_factorial (by decide)]
    norm_num [Nat.factorial]
  have hd : (50 : ℕ).choose 14 = 937845656300 := by
    rw [Nat.choose_eq_factorial_div_factorial (by decide)]
    norm_num [Nat.factorial]
  norm_num [hc, hd, actualNumerator, norm_mul, norm_pow, norm_div]

private lemma generic_73 : C 100 73 (9/100) /
    (((100 : ℕ).choose 73 : ℝ) * (7/10)^73) ≤ (genericNumerator 73 : ℝ) / 10^12 := by
  apply normalized_C_le 100 73 (9/100) (7/10) _ (by decide) (by decide)
    (by norm_num) (by positivity)
  have hc : (100 : ℕ).choose 73 = 1917353200780443050763600 := by
    rw [Nat.choose_eq_factorial_div_factorial (by decide)]
    norm_num [Nat.factorial]
  norm_num [genericNumerator, hc]

private lemma actual_73 : ‖r.esymm 73‖ /
    (((100 : ℕ).choose 73 : ℝ) * (7/10)^73) ≤ (actualNumerator 73 : ℝ) / 10^12 := by
  rw [esymm_exact 73 (by decide)]
  norm_num [actualNumerator]

private lemma generic_74 : C 100 74 (9/100) /
    (((100 : ℕ).choose 74 : ℝ) * (7/10)^74) ≤ (genericNumerator 74 : ℝ) / 10^12 := by
  apply normalized_C_le 100 74 (9/100) (7/10) _ (by decide) (by decide)
    (by norm_num) (by positivity)
  have hc : (100 : ℕ).choose 74 = 699574816500972464467800 := by
    rw [Nat.choose_eq_factorial_div_factorial (by decide)]
    norm_num [Nat.factorial]
  norm_num [genericNumerator, hc]

private lemma actual_74 : ‖r.esymm 74‖ /
    (((100 : ℕ).choose 74 : ℝ) * (7/10)^74) ≤ (actualNumerator 74 : ℝ) / 10^12 := by
  rw [esymm_exact 74 (by decide)]
  have hc : (100 : ℕ).choose 74 = 699574816500972464467800 := by
    rw [Nat.choose_eq_factorial_div_factorial (by decide)]
    norm_num [Nat.factorial]
  have hd : (50 : ℕ).choose 13 = 354860518600 := by
    rw [Nat.choose_eq_factorial_div_factorial (by decide)]
    norm_num [Nat.factorial]
  norm_num [hc, hd, actualNumerator, norm_mul, norm_pow, norm_div]

private lemma generic_75 : C 100 75 (9/100) /
    (((100 : ℕ).choose 75 : ℝ) * (7/10)^75) ≤ (genericNumerator 75 : ℝ) / 10^12 := by
  apply normalized_C_le 100 75 (9/100) (7/10) _ (by decide) (by decide)
    (by norm_num) (by positivity)
  have hc : (100 : ℕ).choose 75 = 242519269720337121015504 := by
    rw [Nat.choose_eq_factorial_div_factorial (by decide)]
    norm_num [Nat.factorial]
  norm_num [genericNumerator, hc]

private lemma actual_75 : ‖r.esymm 75‖ /
    (((100 : ℕ).choose 75 : ℝ) * (7/10)^75) ≤ (actualNumerator 75 : ℝ) / 10^12 := by
  rw [esymm_exact 75 (by decide)]
  norm_num [actualNumerator]

private lemma generic_76 : C 100 76 (9/100) /
    (((100 : ℕ).choose 76 : ℝ) * (7/10)^76) ≤ (genericNumerator 76 : ℝ) / 10^12 := by
  apply normalized_C_le 100 76 (9/100) (7/10) _ (by decide) (by decide)
    (by norm_num) (by positivity)
  have hc : (100 : ℕ).choose 76 = 79776075565900368755100 := by
    rw [Nat.choose_eq_factorial_div_factorial (by decide)]
    norm_num [Nat.factorial]
  norm_num [genericNumerator, hc]

private lemma actual_76 : ‖r.esymm 76‖ /
    (((100 : ℕ).choose 76 : ℝ) * (7/10)^76) ≤ (actualNumerator 76 : ℝ) / 10^12 := by
  rw [esymm_exact 76 (by decide)]
  have hc : (100 : ℕ).choose 76 = 79776075565900368755100 := by
    rw [Nat.choose_eq_factorial_div_factorial (by decide)]
    norm_num [Nat.factorial]
  have hd : (50 : ℕ).choose 12 = 121399651100 := by
    rw [Nat.choose_eq_factorial_div_factorial (by decide)]
    norm_num [Nat.factorial]
  norm_num [hc, hd, actualNumerator, norm_mul, norm_pow, norm_div]

private lemma generic_77 : C 100 77 (9/100) /
    (((100 : ℕ).choose 77 : ℝ) * (7/10)^77) ≤ (genericNumerator 77 : ℝ) / 10^12 := by
  apply normalized_C_le 100 77 (9/100) (7/10) _ (by decide) (by decide)
    (by norm_num) (by positivity)
  have hc : (100 : ℕ).choose 77 = 24865270306254660391200 := by
    rw [Nat.choose_eq_factorial_div_factorial (by decide)]
    norm_num [Nat.factorial]
  norm_num [genericNumerator, hc]

private lemma actual_77 : ‖r.esymm 77‖ /
    (((100 : ℕ).choose 77 : ℝ) * (7/10)^77) ≤ (actualNumerator 77 : ℝ) / 10^12 := by
  rw [esymm_exact 77 (by decide)]
  norm_num [actualNumerator]

private lemma generic_78 : C 100 78 (9/100) /
    (((100 : ℕ).choose 78 : ℝ) * (7/10)^78) ≤ (genericNumerator 78 : ℝ) / 10^12 := by
  apply normalized_C_le 100 78 (9/100) (7/10) _ (by decide) (by decide)
    (by norm_num) (by positivity)
  have hc : (100 : ℕ).choose 78 = 7332066885177656269200 := by
    rw [Nat.choose_eq_factorial_div_factorial (by decide)]
    norm_num [Nat.factorial]
  norm_num [genericNumerator, hc]

private lemma actual_78 : ‖r.esymm 78‖ /
    (((100 : ℕ).choose 78 : ℝ) * (7/10)^78) ≤ (actualNumerator 78 : ℝ) / 10^12 := by
  rw [esymm_exact 78 (by decide)]
  have hc : (100 : ℕ).choose 78 = 7332066885177656269200 := by
    rw [Nat.choose_eq_factorial_div_factorial (by decide)]
    norm_num [Nat.factorial]
  have hd : (50 : ℕ).choose 11 = 37353738800 := by
    rw [Nat.choose_eq_factorial_div_factorial (by decide)]
    norm_num [Nat.factorial]
  norm_num [hc, hd, actualNumerator, norm_mul, norm_pow, norm_div]

private lemma generic_79 : C 100 79 (9/100) /
    (((100 : ℕ).choose 79 : ℝ) * (7/10)^79) ≤ (genericNumerator 79 : ℝ) / 10^12 := by
  apply normalized_C_le 100 79 (9/100) (7/10) _ (by decide) (by decide)
    (by norm_num) (by positivity)
  have hc : (100 : ℕ).choose 79 = 2041841411062132125600 := by
    rw [Nat.choose_eq_factorial_div_factorial (by decide)]
    norm_num [Nat.factorial]
  norm_num [genericNumerator, hc]

private lemma actual_79 : ‖r.esymm 79‖ /
    (((100 : ℕ).choose 79 : ℝ) * (7/10)^79) ≤ (actualNumerator 79 : ℝ) / 10^12 := by
  rw [esymm_exact 79 (by decide)]
  norm_num [actualNumerator]

private lemma generic_80 : C 100 80 (9/100) /
    (((100 : ℕ).choose 80 : ℝ) * (7/10)^80) ≤ (genericNumerator 80 : ℝ) / 10^12 := by
  apply normalized_C_le 100 80 (9/100) (7/10) _ (by decide) (by decide)
    (by norm_num) (by positivity)
  have hc : (100 : ℕ).choose 80 = 535983370403809682970 := by
    rw [Nat.choose_eq_factorial_div_factorial (by decide)]
    norm_num [Nat.factorial]
  norm_num [genericNumerator, hc]

private lemma actual_80 : ‖r.esymm 80‖ /
    (((100 : ℕ).choose 80 : ℝ) * (7/10)^80) ≤ (actualNumerator 80 : ℝ) / 10^12 := by
  rw [esymm_exact 80 (by decide)]
  have hc : (100 : ℕ).choose 80 = 535983370403809682970 := by
    rw [Nat.choose_eq_factorial_div_factorial (by decide)]
    norm_num [Nat.factorial]
  have hd : (50 : ℕ).choose 10 = 10272278170 := by
    rw [Nat.choose_eq_factorial_div_factorial (by decide)]
    norm_num [Nat.factorial]
  norm_num [hc, hd, actualNumerator, norm_mul, norm_pow, norm_div]

private lemma generic_81 : C 100 81 (9/100) /
    (((100 : ℕ).choose 81 : ℝ) * (7/10)^81) ≤ (genericNumerator 81 : ℝ) / 10^12 := by
  apply normalized_C_le 100 81 (9/100) (7/10) _ (by decide) (by decide)
    (by norm_num) (by positivity)
  have hc : (100 : ℕ).choose 81 = 132341572939212267400 := by
    rw [Nat.choose_eq_factorial_div_factorial (by decide)]
    norm_num [Nat.factorial]
  norm_num [genericNumerator, hc]

private lemma actual_81 : ‖r.esymm 81‖ /
    (((100 : ℕ).choose 81 : ℝ) * (7/10)^81) ≤ (actualNumerator 81 : ℝ) / 10^12 := by
  rw [esymm_exact 81 (by decide)]
  norm_num [actualNumerator]

private lemma generic_82 : C 100 82 (9/100) /
    (((100 : ℕ).choose 82 : ℝ) * (7/10)^82) ≤ (genericNumerator 82 : ℝ) / 10^12 := by
  apply normalized_C_le 100 82 (9/100) (7/10) _ (by decide) (by decide)
    (by norm_num) (by positivity)
  have hc : (100 : ℕ).choose 82 = 30664510802988208300 := by
    rw [Nat.choose_eq_factorial_div_factorial (by decide)]
    norm_num [Nat.factorial]
  norm_num [genericNumerator, hc]

private lemma actual_82 : ‖r.esymm 82‖ /
    (((100 : ℕ).choose 82 : ℝ) * (7/10)^82) ≤ (actualNumerator 82 : ℝ) / 10^12 := by
  rw [esymm_exact 82 (by decide)]
  have hc : (100 : ℕ).choose 82 = 30664510802988208300 := by
    rw [Nat.choose_eq_factorial_div_factorial (by decide)]
    norm_num [Nat.factorial]
  have hd : (50 : ℕ).choose 9 = 2505433700 := by
    rw [Nat.choose_eq_factorial_div_factorial (by decide)]
    norm_num [Nat.factorial]
  norm_num [hc, hd, actualNumerator, norm_mul, norm_pow, norm_div]

private lemma generic_83 : C 100 83 (9/100) /
    (((100 : ℕ).choose 83 : ℝ) * (7/10)^83) ≤ (genericNumerator 83 : ℝ) / 10^12 := by
  apply normalized_C_le 100 83 (9/100) (7/10) _ (by decide) (by decide)
    (by norm_num) (by positivity)
  have hc : (100 : ℕ).choose 83 = 6650134872937201800 := by
    rw [Nat.choose_eq_factorial_div_factorial (by decide)]
    norm_num [Nat.factorial]
  norm_num [genericNumerator, hc]

private lemma actual_83 : ‖r.esymm 83‖ /
    (((100 : ℕ).choose 83 : ℝ) * (7/10)^83) ≤ (actualNumerator 83 : ℝ) / 10^12 := by
  rw [esymm_exact 83 (by decide)]
  norm_num [actualNumerator]

private lemma generic_84 : C 100 84 (9/100) /
    (((100 : ℕ).choose 84 : ℝ) * (7/10)^84) ≤ (genericNumerator 84 : ℝ) / 10^12 := by
  apply normalized_C_le 100 84 (9/100) (7/10) _ (by decide) (by decide)
    (by norm_num) (by positivity)
  have hc : (100 : ℕ).choose 84 = 1345860629046814650 := by
    rw [Nat.choose_eq_factorial_div_factorial (by decide)]
    norm_num [Nat.factorial]
  norm_num [genericNumerator, hc]

private lemma actual_84 : ‖r.esymm 84‖ /
    (((100 : ℕ).choose 84 : ℝ) * (7/10)^84) ≤ (actualNumerator 84 : ℝ) / 10^12 := by
  rw [esymm_exact 84 (by decide)]
  have hc : (100 : ℕ).choose 84 = 1345860629046814650 := by
    rw [Nat.choose_eq_factorial_div_factorial (by decide)]
    norm_num [Nat.factorial]
  have hd : (50 : ℕ).choose 8 = 536878650 := by
    rw [Nat.choose_eq_factorial_div_factorial (by decide)]
    norm_num [Nat.factorial]
  norm_num [hc, hd, actualNumerator, norm_mul, norm_pow, norm_div]

private lemma generic_85 : C 100 85 (9/100) /
    (((100 : ℕ).choose 85 : ℝ) * (7/10)^85) ≤ (genericNumerator 85 : ℝ) / 10^12 := by
  apply normalized_C_le 100 85 (9/100) (7/10) _ (by decide) (by decide)
    (by norm_num) (by positivity)
  have hc : (100 : ℕ).choose 85 = 253338471349988640 := by
    rw [Nat.choose_eq_factorial_div_factorial (by decide)]
    norm_num [Nat.factorial]
  norm_num [genericNumerator, hc]

private lemma actual_85 : ‖r.esymm 85‖ /
    (((100 : ℕ).choose 85 : ℝ) * (7/10)^85) ≤ (actualNumerator 85 : ℝ) / 10^12 := by
  rw [esymm_exact 85 (by decide)]
  norm_num [actualNumerator]

private lemma generic_86 : C 100 86 (9/100) /
    (((100 : ℕ).choose 86 : ℝ) * (7/10)^86) ≤ (genericNumerator 86 : ℝ) / 10^12 := by
  apply normalized_C_le 100 86 (9/100) (7/10) _ (by decide) (by decide)
    (by norm_num) (by positivity)
  have hc : (100 : ℕ).choose 86 = 44186942677323600 := by
    rw [Nat.choose_eq_factorial_div_factorial (by decide)]
    norm_num [Nat.factorial]
  norm_num [genericNumerator, hc]

private lemma actual_86 : ‖r.esymm 86‖ /
    (((100 : ℕ).choose 86 : ℝ) * (7/10)^86) ≤ (actualNumerator 86 : ℝ) / 10^12 := by
  rw [esymm_exact 86 (by decide)]
  have hc : (100 : ℕ).choose 86 = 44186942677323600 := by
    rw [Nat.choose_eq_factorial_div_factorial (by decide)]
    norm_num [Nat.factorial]
  have hd : (50 : ℕ).choose 7 = 99884400 := by
    rw [Nat.choose_eq_factorial_div_factorial (by decide)]
    norm_num [Nat.factorial]
  norm_num [hc, hd, actualNumerator, norm_mul, norm_pow, norm_div]

private lemma generic_87 : C 100 87 (9/100) /
    (((100 : ℕ).choose 87 : ℝ) * (7/10)^87) ≤ (genericNumerator 87 : ℝ) / 10^12 := by
  apply normalized_C_le 100 87 (9/100) (7/10) _ (by decide) (by decide)
    (by norm_num) (by positivity)
  have hc : (100 : ℕ).choose 87 = 7110542499799200 := by
    rw [Nat.choose_eq_factorial_div_factorial (by decide)]
    norm_num [Nat.factorial]
  norm_num [genericNumerator, hc]

private lemma actual_87 : ‖r.esymm 87‖ /
    (((100 : ℕ).choose 87 : ℝ) * (7/10)^87) ≤ (actualNumerator 87 : ℝ) / 10^12 := by
  rw [esymm_exact 87 (by decide)]
  norm_num [actualNumerator]

private lemma generic_88 : C 100 88 (9/100) /
    (((100 : ℕ).choose 88 : ℝ) * (7/10)^88) ≤ (genericNumerator 88 : ℝ) / 10^12 := by
  apply normalized_C_le 100 88 (9/100) (7/10) _ (by decide) (by decide)
    (by norm_num) (by positivity)
  have hc : (100 : ℕ).choose 88 = 1050421051106700 := by
    rw [Nat.choose_eq_factorial_div_factorial (by decide)]
    norm_num [Nat.factorial]
  norm_num [genericNumerator, hc]

private lemma actual_88 : ‖r.esymm 88‖ /
    (((100 : ℕ).choose 88 : ℝ) * (7/10)^88) ≤ (actualNumerator 88 : ℝ) / 10^12 := by
  rw [esymm_exact 88 (by decide)]
  have hc : (100 : ℕ).choose 88 = 1050421051106700 := by
    rw [Nat.choose_eq_factorial_div_factorial (by decide)]
    norm_num [Nat.factorial]
  have hd : (50 : ℕ).choose 6 = 15890700 := by
    rw [Nat.choose_eq_factorial_div_factorial (by decide)]
    norm_num [Nat.factorial]
  norm_num [hc, hd, actualNumerator, norm_mul, norm_pow, norm_div]

private lemma generic_89 : C 100 89 (9/100) /
    (((100 : ℕ).choose 89 : ℝ) * (7/10)^89) ≤ (genericNumerator 89 : ℝ) / 10^12 := by
  apply normalized_C_le 100 89 (9/100) (7/10) _ (by decide) (by decide)
    (by norm_num) (by positivity)
  have hc : (100 : ℕ).choose 89 = 141629804643600 := by
    rw [Nat.choose_eq_factorial_div_factorial (by decide)]
    norm_num [Nat.factorial]
  norm_num [genericNumerator, hc]

private lemma actual_89 : ‖r.esymm 89‖ /
    (((100 : ℕ).choose 89 : ℝ) * (7/10)^89) ≤ (actualNumerator 89 : ℝ) / 10^12 := by
  rw [esymm_exact 89 (by decide)]
  norm_num [actualNumerator]

private lemma generic_90 : C 100 90 (9/100) /
    (((100 : ℕ).choose 90 : ℝ) * (7/10)^90) ≤ (genericNumerator 90 : ℝ) / 10^12 := by
  apply normalized_C_le 100 90 (9/100) (7/10) _ (by decide) (by decide)
    (by norm_num) (by positivity)
  have hc : (100 : ℕ).choose 90 = 17310309456440 := by
    rw [Nat.choose_eq_factorial_div_factorial (by decide)]
    norm_num [Nat.factorial]
  norm_num [genericNumerator, hc]

private lemma actual_90 : ‖r.esymm 90‖ /
    (((100 : ℕ).choose 90 : ℝ) * (7/10)^90) ≤ (actualNumerator 90 : ℝ) / 10^12 := by
  rw [esymm_exact 90 (by decide)]
  have hc : (100 : ℕ).choose 90 = 17310309456440 := by
    rw [Nat.choose_eq_factorial_div_factorial (by decide)]
    norm_num [Nat.factorial]
  have hd : (50 : ℕ).choose 5 = 2118760 := by
    rw [Nat.choose_eq_factorial_div_factorial (by decide)]
    norm_num [Nat.factorial]
  norm_num [hc, hd, actualNumerator, norm_mul, norm_pow, norm_div]

private lemma generic_91 : C 100 91 (9/100) /
    (((100 : ℕ).choose 91 : ℝ) * (7/10)^91) ≤ (genericNumerator 91 : ℝ) / 10^12 := by
  apply normalized_C_le 100 91 (9/100) (7/10) _ (by decide) (by decide)
    (by norm_num) (by positivity)
  have hc : (100 : ℕ).choose 91 = 1902231808400 := by
    rw [Nat.choose_eq_factorial_div_factorial (by decide)]
    norm_num [Nat.factorial]
  norm_num [genericNumerator, hc]

private lemma actual_91 : ‖r.esymm 91‖ /
    (((100 : ℕ).choose 91 : ℝ) * (7/10)^91) ≤ (actualNumerator 91 : ℝ) / 10^12 := by
  rw [esymm_exact 91 (by decide)]
  norm_num [actualNumerator]

private lemma generic_92 : C 100 92 (9/100) /
    (((100 : ℕ).choose 92 : ℝ) * (7/10)^92) ≤ (genericNumerator 92 : ℝ) / 10^12 := by
  apply normalized_C_le 100 92 (9/100) (7/10) _ (by decide) (by decide)
    (by norm_num) (by positivity)
  have hc : (100 : ℕ).choose 92 = 186087894300 := by
    rw [Nat.choose_eq_factorial_div_factorial (by decide)]
    norm_num [Nat.factorial]
  norm_num [genericNumerator, hc]

private lemma actual_92 : ‖r.esymm 92‖ /
    (((100 : ℕ).choose 92 : ℝ) * (7/10)^92) ≤ (actualNumerator 92 : ℝ) / 10^12 := by
  rw [esymm_exact 92 (by decide)]
  have hc : (100 : ℕ).choose 92 = 186087894300 := by
    rw [Nat.choose_eq_factorial_div_factorial (by decide)]
    norm_num [Nat.factorial]
  have hd : (50 : ℕ).choose 4 = 230300 := by
    rw [Nat.choose_eq_factorial_div_factorial (by decide)]
    norm_num [Nat.factorial]
  norm_num [hc, hd, actualNumerator, norm_mul, norm_pow, norm_div]

private lemma generic_93 : C 100 93 (9/100) /
    (((100 : ℕ).choose 93 : ℝ) * (7/10)^93) ≤ (genericNumerator 93 : ℝ) / 10^12 := by
  apply normalized_C_le 100 93 (9/100) (7/10) _ (by decide) (by decide)
    (by norm_num) (by positivity)
  have hc : (100 : ℕ).choose 93 = 16007560800 := by
    rw [Nat.choose_eq_factorial_div_factorial (by decide)]
    norm_num [Nat.factorial]
  norm_num [genericNumerator, hc]

private lemma actual_93 : ‖r.esymm 93‖ /
    (((100 : ℕ).choose 93 : ℝ) * (7/10)^93) ≤ (actualNumerator 93 : ℝ) / 10^12 := by
  rw [esymm_exact 93 (by decide)]
  norm_num [actualNumerator]

private lemma generic_94 : C 100 94 (9/100) /
    (((100 : ℕ).choose 94 : ℝ) * (7/10)^94) ≤ (genericNumerator 94 : ℝ) / 10^12 := by
  apply normalized_C_le 100 94 (9/100) (7/10) _ (by decide) (by decide)
    (by norm_num) (by positivity)
  have hc : (100 : ℕ).choose 94 = 1192052400 := by
    rw [Nat.choose_eq_factorial_div_factorial (by decide)]
    norm_num [Nat.factorial]
  norm_num [genericNumerator, hc]

private lemma actual_94 : ‖r.esymm 94‖ /
    (((100 : ℕ).choose 94 : ℝ) * (7/10)^94) ≤ (actualNumerator 94 : ℝ) / 10^12 := by
  rw [esymm_exact 94 (by decide)]
  have hc : (100 : ℕ).choose 94 = 1192052400 := by
    rw [Nat.choose_eq_factorial_div_factorial (by decide)]
    norm_num [Nat.factorial]
  have hd : (50 : ℕ).choose 3 = 19600 := by
    rw [Nat.choose_eq_factorial_div_factorial (by decide)]
    norm_num [Nat.factorial]
  norm_num [hc, hd, actualNumerator, norm_mul, norm_pow, norm_div]

private lemma generic_95 : C 100 95 (9/100) /
    (((100 : ℕ).choose 95 : ℝ) * (7/10)^95) ≤ (genericNumerator 95 : ℝ) / 10^12 := by
  apply normalized_C_le 100 95 (9/100) (7/10) _ (by decide) (by decide)
    (by norm_num) (by positivity)
  have hc : (100 : ℕ).choose 95 = 75287520 := by
    rw [Nat.choose_eq_factorial_div_factorial (by decide)]
    norm_num [Nat.factorial]
  norm_num [genericNumerator, hc]

private lemma actual_95 : ‖r.esymm 95‖ /
    (((100 : ℕ).choose 95 : ℝ) * (7/10)^95) ≤ (actualNumerator 95 : ℝ) / 10^12 := by
  rw [esymm_exact 95 (by decide)]
  norm_num [actualNumerator]

private lemma generic_96 : C 100 96 (9/100) /
    (((100 : ℕ).choose 96 : ℝ) * (7/10)^96) ≤ (genericNumerator 96 : ℝ) / 10^12 := by
  apply normalized_C_le 100 96 (9/100) (7/10) _ (by decide) (by decide)
    (by norm_num) (by positivity)
  have hc : (100 : ℕ).choose 96 = 3921225 := by
    rw [Nat.choose_eq_factorial_div_factorial (by decide)]
    norm_num [Nat.factorial]
  norm_num [genericNumerator, hc]

private lemma actual_96 : ‖r.esymm 96‖ /
    (((100 : ℕ).choose 96 : ℝ) * (7/10)^96) ≤ (actualNumerator 96 : ℝ) / 10^12 := by
  rw [esymm_exact 96 (by decide)]
  have hc : (100 : ℕ).choose 96 = 3921225 := by
    rw [Nat.choose_eq_factorial_div_factorial (by decide)]
    norm_num [Nat.factorial]
  have hd : (50 : ℕ).choose 2 = 1225 := by
    rw [Nat.choose_eq_factorial_div_factorial (by decide)]
    norm_num [Nat.factorial]
  norm_num [hc, hd, actualNumerator, norm_mul, norm_pow, norm_div]

private lemma generic_97 : C 100 97 (9/100) /
    (((100 : ℕ).choose 97 : ℝ) * (7/10)^97) ≤ (genericNumerator 97 : ℝ) / 10^12 := by
  apply normalized_C_le 100 97 (9/100) (7/10) _ (by decide) (by decide)
    (by norm_num) (by positivity)
  have hc : (100 : ℕ).choose 97 = 161700 := by
    rw [Nat.choose_eq_factorial_div_factorial (by decide)]
    norm_num [Nat.factorial]
  norm_num [genericNumerator, hc]

private lemma actual_97 : ‖r.esymm 97‖ /
    (((100 : ℕ).choose 97 : ℝ) * (7/10)^97) ≤ (actualNumerator 97 : ℝ) / 10^12 := by
  rw [esymm_exact 97 (by decide)]
  norm_num [actualNumerator]

private lemma generic_98 : C 100 98 (9/100) /
    (((100 : ℕ).choose 98 : ℝ) * (7/10)^98) ≤ (genericNumerator 98 : ℝ) / 10^12 := by
  apply normalized_C_le 100 98 (9/100) (7/10) _ (by decide) (by decide)
    (by norm_num) (by positivity)
  have hc : (100 : ℕ).choose 98 = 4950 := by
    rw [Nat.choose_eq_factorial_div_factorial (by decide)]
    norm_num [Nat.factorial]
  norm_num [genericNumerator, hc]

private lemma actual_98 : ‖r.esymm 98‖ /
    (((100 : ℕ).choose 98 : ℝ) * (7/10)^98) ≤ (actualNumerator 98 : ℝ) / 10^12 := by
  rw [esymm_exact 98 (by decide)]
  have hc : (100 : ℕ).choose 98 = 4950 := by
    rw [Nat.choose_eq_factorial_div_factorial (by decide)]
    norm_num [Nat.factorial]
  have hd : (50 : ℕ).choose 1 = 50 := by
    rw [Nat.choose_eq_factorial_div_factorial (by decide)]
    norm_num [Nat.factorial]
  norm_num [hc, hd, actualNumerator, norm_mul, norm_pow, norm_div]

private lemma generic_99 : C 100 99 (9/100) /
    (((100 : ℕ).choose 99 : ℝ) * (7/10)^99) ≤ (genericNumerator 99 : ℝ) / 10^12 := by
  apply normalized_C_le 100 99 (9/100) (7/10) _ (by decide) (by decide)
    (by norm_num) (by positivity)
  have hc : (100 : ℕ).choose 99 = 100 := by
    rw [Nat.choose_eq_factorial_div_factorial (by decide)]
    norm_num [Nat.factorial]
  norm_num [genericNumerator, hc]

private lemma actual_99 : ‖r.esymm 99‖ /
    (((100 : ℕ).choose 99 : ℝ) * (7/10)^99) ≤ (actualNumerator 99 : ℝ) / 10^12 := by
  rw [esymm_exact 99 (by decide)]
  norm_num [actualNumerator]

private lemma generic_100 : C 100 100 (9/100) /
    (((100 : ℕ).choose 100 : ℝ) * (7/10)^100) ≤ (genericNumerator 100 : ℝ) / 10^12 := by
  apply normalized_C_le 100 100 (9/100) (7/10) _ (by decide) (by decide)
    (by norm_num) (by positivity)
  have hc : (100 : ℕ).choose 100 = 1 := by
    rw [Nat.choose_eq_factorial_div_factorial (by decide)]
    norm_num [Nat.factorial]
  norm_num [genericNumerator, hc]

private lemma actual_100 : ‖r.esymm 100‖ /
    (((100 : ℕ).choose 100 : ℝ) * (7/10)^100) ≤ (actualNumerator 100 : ℝ) / 10^12 := by
  rw [esymm_exact 100 (by decide)]
  have hc : (100 : ℕ).choose 100 = 1 := by
    rw [Nat.choose_eq_factorial_div_factorial (by decide)]
    norm_num [Nat.factorial]
  have hd : (50 : ℕ).choose 0 = 1 := by
    rw [Nat.choose_eq_factorial_div_factorial (by decide)]
    norm_num [Nat.factorial]
  norm_num [hc, hd, actualNumerator, norm_mul, norm_pow, norm_div]

lemma generic_rows (k : ℕ) (hk : k ∈ Finset.Ico 3 101) :
    C 100 k (9/100) / (((100 : ℕ).choose k : ℝ) * (7/10)^k) ≤
      (genericNumerator k : ℝ) / 10^12 := by
  obtain ⟨hlo, hhi⟩ := Finset.mem_Ico.mp hk
  interval_cases k
  · exact generic_3
  · exact generic_4
  · exact generic_5
  · exact generic_6
  · exact generic_7
  · exact generic_8
  · exact generic_9
  · exact generic_10
  · exact generic_11
  · exact generic_12
  · exact generic_13
  · exact generic_14
  · exact generic_15
  · exact generic_16
  · exact generic_17
  · exact generic_18
  · exact generic_19
  · exact generic_20
  · exact generic_21
  · exact generic_22
  · exact generic_23
  · exact generic_24
  · exact generic_25
  · exact generic_26
  · exact generic_27
  · exact generic_28
  · exact generic_29
  · exact generic_30
  · exact generic_31
  · exact generic_32
  · exact generic_33
  · exact generic_34
  · exact generic_35
  · exact generic_36
  · exact generic_37
  · exact generic_38
  · exact generic_39
  · exact generic_40
  · exact generic_41
  · exact generic_42
  · exact generic_43
  · exact generic_44
  · exact generic_45
  · exact generic_46
  · exact generic_47
  · exact generic_48
  · exact generic_49
  · exact generic_50
  · exact generic_51
  · exact generic_52
  · exact generic_53
  · exact generic_54
  · exact generic_55
  · exact generic_56
  · exact generic_57
  · exact generic_58
  · exact generic_59
  · exact generic_60
  · exact generic_61
  · exact generic_62
  · exact generic_63
  · exact generic_64
  · exact generic_65
  · exact generic_66
  · exact generic_67
  · exact generic_68
  · exact generic_69
  · exact generic_70
  · exact generic_71
  · exact generic_72
  · exact generic_73
  · exact generic_74
  · exact generic_75
  · exact generic_76
  · exact generic_77
  · exact generic_78
  · exact generic_79
  · exact generic_80
  · exact generic_81
  · exact generic_82
  · exact generic_83
  · exact generic_84
  · exact generic_85
  · exact generic_86
  · exact generic_87
  · exact generic_88
  · exact generic_89
  · exact generic_90
  · exact generic_91
  · exact generic_92
  · exact generic_93
  · exact generic_94
  · exact generic_95
  · exact generic_96
  · exact generic_97
  · exact generic_98
  · exact generic_99
  · exact generic_100

lemma actual_rows (k : ℕ) (hk : k ∈ Finset.Ico 3 101) :
    ‖r.esymm k‖ / (((100 : ℕ).choose k : ℝ) * (7/10)^k) ≤
      (actualNumerator k : ℝ) / 10^12 := by
  obtain ⟨hlo, hhi⟩ := Finset.mem_Ico.mp hk
  interval_cases k
  · exact actual_3
  · exact actual_4
  · exact actual_5
  · exact actual_6
  · exact actual_7
  · exact actual_8
  · exact actual_9
  · exact actual_10
  · exact actual_11
  · exact actual_12
  · exact actual_13
  · exact actual_14
  · exact actual_15
  · exact actual_16
  · exact actual_17
  · exact actual_18
  · exact actual_19
  · exact actual_20
  · exact actual_21
  · exact actual_22
  · exact actual_23
  · exact actual_24
  · exact actual_25
  · exact actual_26
  · exact actual_27
  · exact actual_28
  · exact actual_29
  · exact actual_30
  · exact actual_31
  · exact actual_32
  · exact actual_33
  · exact actual_34
  · exact actual_35
  · exact actual_36
  · exact actual_37
  · exact actual_38
  · exact actual_39
  · exact actual_40
  · exact actual_41
  · exact actual_42
  · exact actual_43
  · exact actual_44
  · exact actual_45
  · exact actual_46
  · exact actual_47
  · exact actual_48
  · exact actual_49
  · exact actual_50
  · exact actual_51
  · exact actual_52
  · exact actual_53
  · exact actual_54
  · exact actual_55
  · exact actual_56
  · exact actual_57
  · exact actual_58
  · exact actual_59
  · exact actual_60
  · exact actual_61
  · exact actual_62
  · exact actual_63
  · exact actual_64
  · exact actual_65
  · exact actual_66
  · exact actual_67
  · exact actual_68
  · exact actual_69
  · exact actual_70
  · exact actual_71
  · exact actual_72
  · exact actual_73
  · exact actual_74
  · exact actual_75
  · exact actual_76
  · exact actual_77
  · exact actual_78
  · exact actual_79
  · exact actual_80
  · exact actual_81
  · exact actual_82
  · exact actual_83
  · exact actual_84
  · exact actual_85
  · exact actual_86
  · exact actual_87
  · exact actual_88
  · exact actual_89
  · exact actual_90
  · exact actual_91
  · exact actual_92
  · exact actual_93
  · exact actual_94
  · exact actual_95
  · exact actual_96
  · exact actual_97
  · exact actual_98
  · exact actual_99
  · exact actual_100

-- END GENERATED COEFFICIENT CERTIFICATES

/-- The envelopes are summed as small integers before real division. -/
lemma generic_sum : (∑ k ∈ Finset.Ico 3 101, genericNumerator k) = 453022083 := by
  norm_num [Finset.sum_Ico_succ_top, genericNumerator]

lemma actual_sum : (∑ k ∈ Finset.Ico 3 101, actualNumerator k) = 10642552 := by
  norm_num [Finset.sum_Ico_succ_top, actualNumerator]

/-- REPORT §3.4, the actual square-root majorant, strictly below 1/2000. -/
theorem majorant_error : majorant_Efin r μ ((a : ℂ) * μ) < 1 / 2000 := by
  have h := majorant_le r μ ((a : ℂ) * μ) (1 / 10^12)
    (fun k => (genericNumerator k : ℝ) / 10^12) low_endpoints
    (by
      intro k hk
      apply norm_endpoints k
      simp only [r_card] at hk
      obtain ⟨_, _⟩ := Finset.mem_Ico.mp hk
      omega)
    (by
      intro k hk
      simpa only [r_card, variance_exact, norm_mu] using
        generic_rows k (by simpa using hk))
  simp only [r_card, Nat.reduceAdd, ← Finset.sum_div, ← Nat.cast_sum, generic_sum] at h
  linarith

/-- Independent sharper bound using the literal elementary coefficients. -/
theorem actual_error : Efin r μ ((a : ℂ) * μ) < 11 / 10^6 := by
  have h := actual_le r μ ((a : ℂ) * μ) (1 / 10^12)
    (fun k => (actualNumerator k : ℝ) / 10^12) low_endpoints
    (by
      intro k hk
      apply norm_endpoints k
      simp only [r_card] at hk
      obtain ⟨_, _⟩ := Finset.mem_Ico.mp hk
      omega)
    (by intro k hk; simpa only [r_card, norm_mu] using actual_rows k (by simpa using hk))
  simp only [r_card, Nat.reduceAdd, ← Finset.sum_div, ← Nat.cast_sum, actual_sum] at h
  linarith

theorem C_budget_exact : majorant_Efin r μ ((a : ℂ) * μ) + Gamma r μ <
    1 - a * ‖μ‖ := by
  rw [Gamma_exact, norm_mu]
  have h := majorant_error
  norm_num [a] at *
  linarith

def J : ℂ := (q.card + 1 : ℂ) *
  (∫ t in (0 : ℝ)..1, (q.map (fun w => 1 - (a : ℂ) * t * w)).prod)

/-- First-origin's closed-disk norm conclusion is impossible for these data. -/
theorem norm_J_gt_one : 1 < ‖J‖ := by
  exact PaperCenteredBound.C_budget q a μ (by simp) (by norm_num [a]) mean mu_ne
    C_budget_exact

/-- The literal polar product reduces to this real polynomial only because every
entry of this particular multiset is real. This is not the AM–GM relaxation. -/
def polarReal (t : ℝ) : ℝ :=
  ((a + (1 - a^2) * t * (2/5)) * (a + (1 - a^2) * t)) ^ 50

def K : ℂ := ∫ t in (0 : ℝ)..1,
  (q.map (fun w => (a : ℂ) + ((1-a^2)*t : ℝ) * w)).prod

lemma polar_product (t : ℝ) :
    (q.map (fun w => (a : ℂ) + ((1-a^2)*t : ℝ) * w)).prod = (polarReal t : ℂ) := by
  simp only [q, Multiset.map_add, Multiset.map_replicate, Multiset.prod_add,
    Multiset.prod_replicate, mul_one, ← mul_pow]
  unfold polarReal
  push_cast
  rfl

lemma polar_continuous : Continuous polarReal := by unfold polarReal; fun_prop

lemma polar_mono (s t : ℝ) (hs : 0 ≤ s) (hst : s ≤ t) :
    polarReal s ≤ polarReal t := by
  have ht : 0 ≤ t := hs.trans hst
  unfold polarReal
  apply pow_le_pow_left₀
  · apply mul_nonneg <;> norm_num [a] <;> nlinarith
  · apply mul_le_mul
    · norm_num [a]; linarith
    · norm_num [a]; linarith
    · norm_num [a]; nlinarith
    · norm_num [a]; nlinarith

lemma polar_at_four_fifths : (17/10 : ℝ) ≤ polarReal (4/5) := by
  norm_num [polarReal, a]
lemma polar_at_nine_tenths : (61/10 : ℝ) ≤ polarReal (9/10) := by
  norm_num [polarReal, a]
lemma polar_at_nineteen_twentieths : (117/10 : ℝ) ≤ polarReal (19/20) := by
  norm_num [polarReal, a]

/-- Three exact positive rectangles plus the nonnegative initial interval. -/
theorem polar_real_gt_one : 1 < ∫ t in (0 : ℝ)..1, polarReal t := by
  have hi (s t : ℝ) : IntervalIntegrable polarReal MeasureTheory.volume s t :=
    polar_continuous.intervalIntegrable s t
  have h0 : 0 ≤ ∫ t in (0 : ℝ)..(4/5), polarReal t := by
    apply intervalIntegral.integral_nonneg (by norm_num)
    intro t ht
    exact pow_nonneg (by
      apply mul_nonneg <;> norm_num [a] <;> nlinarith [ht.1]) 50
  have h1 := lower_rectangle polarReal (4/5) (9/10) (17/10) (by norm_num)
    (hi _ _) (by
      intro t ht
      exact polar_at_four_fifths.trans (polar_mono _ _ (by norm_num) ht.1))
  have h2 := lower_rectangle polarReal (9/10) (19/20) (61/10) (by norm_num)
    (hi _ _) (by
      intro t ht
      exact polar_at_nine_tenths.trans (polar_mono _ _ (by norm_num) ht.1))
  have h3 := lower_rectangle polarReal (19/20) 1 (117/10) (by norm_num)
    (hi _ _) (by
      intro t ht
      exact polar_at_nineteen_twentieths.trans (polar_mono _ _ (by norm_num) ht.1))
  have hadd1 := intervalIntegral.integral_add_adjacent_intervals (hi 0 (4/5)) (hi (4/5) (9/10))
  have hadd2 := intervalIntegral.integral_add_adjacent_intervals (hi 0 (9/10)) (hi (9/10) (19/20))
  have hadd3 := intervalIntegral.integral_add_adjacent_intervals (hi 0 (19/20)) (hi (19/20) 1)
  linarith

/-- Equality for the full complex K, prior to taking its norm. -/
theorem polar_complex : K = ((∫ t in (0 : ℝ)..1, polarReal t : ℝ) : ℂ) := by
  unfold K
  simp_rw [polar_product]
  exact intervalIntegral.integral_ofReal

theorem full_polar : 1 < ‖K‖ := by
  rw [polar_complex, Complex.norm_real, Real.norm_eq_abs,
    abs_of_pos (lt_trans (by norm_num) polar_real_gt_one)]
  exact polar_real_gt_one

theorem polar_re_gt_one : 1 < K.re := by
  rw [polar_complex, Complex.ofReal_re]
  exact polar_real_gt_one

theorem polar_im_zero : K.im = 0 := by rw [polar_complex, Complex.ofReal_im]

/-- Both actual error bounds and both literal complex integrals in one audit root. -/
theorem diagnostic_DI02 :
    q.card = 100 ∧ q.sum / q.card = (7 / 10 : ℂ) ∧
    variance r = 9 / 100 ∧ kappa r = 9 / 100 ∧ Gamma r μ = 1 / 539 ∧
    1 < K.re ∧ K.im = 0 ∧ 1 < ‖K‖ ∧
    majorant_Efin r μ ((a : ℂ) * μ) < 1 / 2000 ∧
    Efin r μ ((a : ℂ) * μ) < 11 / 10^6 ∧
    majorant_Efin r μ ((a : ℂ) * μ) + Gamma r μ < 1 - a * ‖μ‖ ∧
    1 < ‖J‖ :=
  ⟨q_card, mean_div, variance_exact, kappa_exact, Gamma_exact,
    polar_re_gt_one, polar_im_zero, full_polar, majorant_error, actual_error,
    C_budget_exact, norm_J_gt_one⟩

#print axioms diagnostic_DI02
#print axioms mean_div
#print axioms variance_exact
#print axioms kappa_exact
#print axioms Gamma_exact
#print axioms majorant_error
#print axioms actual_error
#print axioms C_budget_exact
#print axioms norm_J_gt_one
#print axioms polar_complex
#print axioms full_polar

end Sendov.PaperCenteredHundred
