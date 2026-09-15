import Sendov.Analytic.CenteredThirdTail

noncomputable section
namespace Sendov.CenteredThird

lemma eta_le (m : ℕ) (hm : 7 ≤ m) : eta m ≤ 1-4/(9*(m:ℝ)) := by
  have hm7 : (7:ℝ) ≤ m := by exact_mod_cast hm
  have hm0 : (0:ℝ) < m := by linarith
  have hm1 : 0 < (m:ℝ)-1 := by linarith
  have hs := weightSum_nonneg m (by omega)
  have he : (eta m)^2 = (4/9)*weightSum m := by
    unfold eta
    rw [mul_pow, Real.sq_sqrt hs]
    ring
  have hd : 2/(m:ℝ) ≤ 2/((m:ℝ)-1) :=
    div_le_div_of_nonneg_left (by norm_num) hm1 (by linarith)
  have hr : 0 ≤ 1/(2*(m:ℝ)*((m:ℝ)-1)) := by positivity
  have ht : 4/(9*(m:ℝ)) ≤ 1 := (div_le_one (by positivity)).2 (by linarith)
  unfold weightSum at he
  have hbound : (eta m)^2 ≤ 1-2*(4/(9*(m:ℝ))) := by
    ring_nf at he hd hr ⊢
    nlinarith only [he, hd, hr]
  have hn := eta_nonneg m
  nlinarith [sq_nonneg (4/(9*(m:ℝ)))]

lemma fourth_power_saving (a h : ℝ) (hh0 : 0 ≤ h) (hh1 : h ≤ 1/21)
    (hah : a = 1-h) : a^4 ≤ 1-(26/7)*h := by
  have hh2 := mul_le_mul_of_nonneg_right hh1 hh0
  have hh3 : 0 ≤ h^3*(4-h) := mul_nonneg (pow_nonneg hh0 _) (by linarith)
  rw [hah]
  nlinarith only [hh2, hh3]

/-- Finite-degree eta and the retained a^4 jointly save 13/(10m). -/
lemma eta_fourth_saving (m : ℕ) (a h : ℝ) (hm : 7 ≤ m)
    (hh0 : 0 ≤ h) (hh1 : h ≤ 1/21) (hah : a = 1-h)
    (hl : 1/4 ≤ (m:ℝ)*h) :
    eta m*a^4 ≤ 1-13/(10*(m:ℝ)) := by
  have hm7 : (7:ℝ) ≤ m := by exact_mod_cast hm
  have hm0 : (0:ℝ) < m := by linarith
  have hinv : 0 ≤ 1/(m:ℝ) := by positivity
  have hinv7 : 1/(m:ℝ) ≤ 1/7 :=
    div_le_div_of_nonneg_left (by norm_num) (by norm_num) hm7
  have hlow : 1/(4*(m:ℝ)) ≤ h := (div_le_iff₀ (by positivity)).2 (by nlinarith)
  have ha4 : a^4 ≤ 1-13/(14*(m:ℝ)) := by
    have h4 := fourth_power_saving a h hh0 hh1 hah
    ring_nf at h4 hlow ⊢
    nlinarith only [h4, hlow]
  have heta := eta_le m hm
  have heta0 : 0 ≤ 1-4/(9*(m:ℝ)) := (eta_nonneg m).trans heta
  have hprod := mul_le_mul heta ha4 (pow_nonneg (by linarith : 0 ≤ a) 4) heta0
  have hsq := mul_le_mul_of_nonneg_right hinv7 hinv
  have hid : (1-4/(9*(m:ℝ)))*(1-13/(14*(m:ℝ))) =
      1-(173/126)*(1/(m:ℝ))+(26/63)*(1/(m:ℝ))^2 := by ring
  rw [hid] at hprod
  ring_nf at hprod hsq hinv ⊢
  nlinarith only [hprod, hsq, hinv]

def A : ℝ := 9*(3/10)*(5/12)*(60/41)^4

def G : ℝ := (31/30)*(120/113)^2

def chordTail (m : ℕ) (a u v : ℝ) : ℝ :=
  9*eta m*a^4*u*Real.sqrt (v^3) /
    ((41/60)^4*Real.sqrt ((m:ℝ)*((m:ℝ)-1)*((m:ℝ)-2)))

lemma mean_sqrt_variance (u v : ℝ) (hu : 0 ≤ u) (hv0 : 0 ≤ v)
    (hv1 : v ≤ 1/10) (hstat : u^2+v ≤ 1) : u*Real.sqrt v ≤ 3/10 := by
  have hs := Real.sq_sqrt hv0
  have ht := mul_le_mul_of_nonneg_right hstat hv0
  have hvprod := mul_nonneg (sub_nonneg.mpr hv1) (by linarith : 0 ≤ 9/10-v)
  have he : (u*Real.sqrt v)^2 = u^2*v := by rw [mul_pow, hs]
  nlinarith only [ht, hvprod, he]

lemma chordTail_le (m : ℕ) (a h u v : ℝ) (hm : 7 ≤ m)
    (hh0 : 0 ≤ h) (hh1 : h ≤ 1/21) (hah : a = 1-h)
    (hl : 1/4 ≤ (m:ℝ)*h) (hu : 0 ≤ u) (hv0 : 0 ≤ v)
    (hv1 : v ≤ 1/10) (hstat : u^2+v ≤ 1) :
    chordTail m a u v ≤ A*(1-13/(10*(m:ℝ)))*v/((m:ℝ)-1) := by
  have hm7 : (7:ℝ) ≤ m := by exact_mod_cast hm
  have hm1 : 0 < (m:ℝ)-1 := by linarith
  have hD := CenteredQuarter.sqrt_fall_three (m:ℝ) hm7
  have hD0 : 0 < Real.sqrt ((m:ℝ)*((m:ℝ)-1)*((m:ℝ)-2)) := by nlinarith only [hD, hm1]
  have hs : u*Real.sqrt (v^3) ≤ (3/10)*v := by
    have he : Real.sqrt (v^3) = v*Real.sqrt v := by
      rw [show v^3 = v^2*v by ring, Real.sqrt_mul (sq_nonneg v), Real.sqrt_sq hv0]
    rw [he]
    nlinarith only [mul_le_mul_of_nonneg_right (mean_sqrt_variance u v hu hv0 hv1 hstat) hv0]
  have hsav := eta_fourth_saving m a h hm hh0 hh1 hah hl
  have heta := eta_nonneg m
  have hsav0 : 0 ≤ 1-13/(10*(m:ℝ)) :=
    (mul_nonneg heta (pow_nonneg (by linarith : 0 ≤ a) 4)).trans hsav
  have hn : 9*eta m*a^4*u*Real.sqrt (v^3) ≤ (27/10)*(1-13/(10*(m:ℝ)))*v := by
    have h1 := mul_le_mul_of_nonneg_left hs (mul_nonneg heta (pow_nonneg (by linarith : 0 ≤ a) 4))
    have h2 := mul_le_mul_of_nonneg_right hsav (mul_nonneg (by norm_num : (0:ℝ) ≤ 3/10) hv0)
    nlinarith only [h1, h2]
  unfold chordTail
  calc
    _ ≤ ((27/10)*(1-13/(10*(m:ℝ)))*v)/
        ((41/60)^4*Real.sqrt ((m:ℝ)*((m:ℝ)-1)*((m:ℝ)-2))) :=
      div_le_div_of_nonneg_right hn (by positivity)
    _ ≤ ((27/10)*(1-13/(10*(m:ℝ)))*v)/((41/60)^4*((12/5)*((m:ℝ)-1))) := by
      apply div_le_div_of_nonneg_left (by positivity) (by positivity)
      exact mul_le_mul_of_nonneg_left hD (by positivity)
    _ = _ := by unfold A; field_simp; ring

lemma gamma_B_le (m u v B : ℝ) (hm : 7 ≤ m) (hu : 113/120 ≤ u)
    (hv : 0 ≤ v) (hB : B ≤ 1/30) : v/((m-1)*u^2)*(1+B) ≤ G*v/(m-1) := by
  have hm1 : 0 < m-1 := by linarith
  have hu0 : 0 < u := by linarith
  have hu2 : (113/120)^2 ≤ u^2 := by nlinarith
  have hg : v/((m-1)*u^2) ≤ (120/113)^2*v/(m-1) := by
    apply (div_le_iff₀ (mul_pos hm1 (sq_pos_of_pos hu0))).2
    have he : ((120/113)^2*v/(m-1))*((m-1)*u^2) = (120/113)^2*v*u^2 := by field_simp
    rw [he]
    nlinarith only [mul_le_mul_of_nonneg_left hu2 hv]
  have hg0 : 0 ≤ v/((m-1)*u^2) := by positivity
  have h1 := mul_le_mul_of_nonneg_left (show 1+B ≤ 31/30 by linarith) hg0
  have h2 := mul_le_mul_of_nonneg_left hg (by norm_num : (0:ℝ) ≤ 31/30)
  unfold G
  linear_combination h1 + h2

/-- The lambda-dependent scalar budget; no division by v. -/
lemma coefficient_budget (m a h v : ℝ) (hm : 7 ≤ m) (hah : a = 1-h)
    (hl0 : 1/4 ≤ m*h) (hl1 : m*h ≤ 1/3) (hv0 : 0 ≤ v)
    (hv : v*(3+m*h) ≤ m*h) :
    (A*(1-13/(10*m))+G)*v/(m-1) ≤ a*v/2+(12/13)*h := by
  have hm0 : 0 < m := by linarith
  have hm1 : 0 < m-1 := by linarith
  let Q := (A*(1-13/(10*m))+G)/(m-1)
  have hid : m*(Q-a/2) = A+G+(G-(3/10)*A)/(m-1)-m/2+m*h/2 := by
    dsimp [Q]
    rw [hah]
    field_simp
    ring
  have hc1 : G ≤ (3/10)*A := by norm_num [G, A]
  have hc2 : A+G ≤ 19/3 := by norm_num [G, A]
  have hd : (G-(3/10)*A)/(m-1) ≤ 0 := div_nonpos_of_nonpos_of_nonneg (by linarith) hm1.le
  have hQ : Q-a/2 ≤ 3/m := by
    apply (le_div_iff₀ hm0).2
    nlinarith only [hid, hc2, hd, hm, hl1]
  have hvm : v/m ≤ (4/13)*h := by
    apply (div_le_iff₀ hm0).2
    have ht := mul_le_mul_of_nonneg_left hl0 hv0
    nlinarith only [hv, ht]
  have ht := mul_le_mul_of_nonneg_right hQ hv0
  change (A*(1-13/(10*m))+G)*v/(m-1) ≤ _
  have he : (A*(1-13/(10*m))+G)*v/(m-1) = Q*v := by dsimp [Q]; ring
  rw [he]
  linear_combination ht + 3*hvm

/-- Scalar C-near on the closed middle interval [1/4,1/3]. -/
theorem scalar_budget (m : ℕ) (a h u v e0 B T : ℝ) (hm : 7 ≤ m)
    (hh0 : 0 ≤ h) (hh1 : h ≤ 1/21) (hah : a = 1-h)
    (hl0 : 1/4 ≤ (m:ℝ)*h) (hl1 : (m:ℝ)*h ≤ 1/3)
    (hu : 113/120 ≤ u) (hstat : u^2+v ≤ 1)
    (hv0 : 0 ≤ v) (hv1 : v ≤ 1/10) (hv : v*(3+(m:ℝ)*h) ≤ (m:ℝ)*h)
    (he0 : e0 ≤ 2*h^2/3) (hB : B ≤ 1/30) (hT : T ≤ chordTail m a u v) :
    e0+v/(((m:ℝ)-1)*u^2)*(1+B)+T ≤ 1-a*u-37*h/819 := by
  have hm7 : (7:ℝ) ≤ m := by exact_mod_cast hm
  have ht := hT.trans (chordTail_le m a h u v hm hh0 hh1 hah hl0 (by linarith) hv0 hv1 hstat)
  have hg := gamma_B_le m u v B hm7 hu hv0 hB
  have hb := coefficient_budget m a h v hm7 hah hl0 hl1 hv0 hv
  have he : e0 ≤ (2/63)*h := by
    have hh2 := mul_le_mul_of_nonneg_right hh1 hh0
    nlinarith only [he0, hh2]
  have hvu : v ≤ 2*(1-u) := by nlinarith [sq_nonneg (u-1)]
  have htarget : h+a*v/2 ≤ 1-a*u := by
    have ht := mul_le_mul_of_nonneg_left hvu (by linarith : 0 ≤ a)
    nlinarith only [ht, hah]
  have hsum : v/(((m:ℝ)-1)*u^2)*(1+B)+T ≤ a*v/2+(12/13)*h := by
    have hid : (A*(1-13/(10*(m:ℝ)))+G)*v/((m:ℝ)-1) =
        A*(1-13/(10*(m:ℝ)))*v/((m:ℝ)-1)+G*v/((m:ℝ)-1) := by ring
    rw [hid] at hb
    linarith
  linarith

end Sendov.CenteredThird
