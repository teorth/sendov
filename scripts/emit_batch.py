import sys, io, pickle, sympy as sp
from pathlib import Path
sys.set_int_max_str_digits(50000000)
r = pickle.load(open(sys.argv[1],"rb"))
n0,n1,k,M0,M1 = r['n0'],r['n1'],r['k'],r['M0'],r['M1']
L,beta,tau,Nmom,mlen = r['L'],r['beta'],r['tau'],r['Nmom'],r['mlen']
cf,G,d,const,p = r['cf'],r['G'],r['d'],r['const'],r['p']
feas, cnum = r['feas'], r['cnum']
up, uq = r['up'], r['uq']
Us = f"{up} / {uq}" if uq != 1 else f"{up}"
LIN = f"({up} - {uq} * α)" if uq != 1 else f"({up} - α)"
# for a singleton batch `M_lo` and `M_hi` are the same rewrite, so listing both fails
MRW = "M_lo, M_hi" if n0 != n1 else "M_lo"
LIN0 = LIN[1:-1]  # `hu` states the bare linear form, without the wrapping parentheses
def poly(cs, var="α"):
    ts=[]
    for i,v in enumerate(cs):
        v=sp.Integer(v)
        if v==0: continue
        s=("+ " if v>0 else "- ")+str(abs(v))
        if i==1: s+=f" * {var}"
        elif i>1: s+=f" * {var} ^ {i}"
        ts.append(s)
    t=" ".join(ts); return t[2:] if t.startswith("+ ") else "-"+t[2:]
P = poly(cf); FE = poly(feas); CN = poly(cnum)
bern = " + ".join((f"{G[0]} * {LIN} ^ {d}" if j==0 else
                   f"{G[d]} * α ^ {d}" if j==d else
                   f"{G[j]} * α ^ {j} * {LIN} ^ {d-j}") for j in range(d+1))
haves = "\n".join(
  (f"  have h{j} : (0:ℝ) ≤ {G[0]} * {LIN} ^ {d} :=\n"
   f"    mul_nonneg (by norm_num) (pow_nonneg hu {d})" if j==0 else
   f"  have h{j} : (0:ℝ) ≤ {G[d]} * α ^ {d} :=\n"
   f"    mul_nonneg (by norm_num) (pow_nonneg hα {d})" if j==d else
   f"  have h{j} : (0:ℝ) ≤ {G[j]} * α ^ {j} * {LIN} ^ {d-j} :=\n"
   f"    mul_nonneg (mul_nonneg (by norm_num) (pow_nonneg hα {j})) (pow_nonneg hu {d-j})")
  for j in range(d+1))
src = f'''/-
Copyright (c) 2026 Terence Tao. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Terence Tao
-/
import Sendov.FiniteRange.Batch
import Sendov.FiniteRange.PackBridge

/-!
# The batch {n0} to {n1}

`Sendov.R_le_batch` bounds every `R n α` for `{n0} ≤ n ≤ {n1}` by the elementary part and
moment at `n₀ = {n0}` together with the prefactor at `n₁ = {n1}`, so one moment and one
certificate serve all {n1-n0+1} degrees.  The certificate has degree {d}, set by `n₀` rather
than `n₁`.

Feasibility at `n₀` is proved rather than assumed: for `n ≥ 36` it follows from
`0 ≤ α ≤ 17`, since `A - c²` increases with `n`.  This matters because feasibility propagates
*upward* in `n`, so it could not be inherited from the hypothesis at `n`.
-/

-- Generated numerals cannot be wrapped, so the long-line linter is off in this file.
set_option linter.style.longLine false
set_option maxRecDepth 4000000

namespace Sendov

namespace B{n0}_{n1}

lemma M_lo : M {n0} = {M0} := by norm_num [M]

lemma M_hi : M {n1} = {M1} := by norm_num [M]

lemma A_lo (α : ℝ) : A {n0} α = 1 - 2 * α / {M0} := by rw [A, M]; push_cast; ring

lemma A_hi (α : ℝ) : A {n1} α = 1 - 2 * α / {M1} := by rw [A, M]; push_cast; ring

lemma c_lo {{α : ℝ}} (hα : 0 ≤ α) : c {n0} α = ({CN}) / ({2*M0} * (3 + α)) := by
  have h3 : (3 : ℝ) + α ≠ 0 := (three_add_pos hα).ne'
  rw [c, M]
  push_cast
  field_simp
  ring

/-- `c` is nonnegative at `n₀` on the batch's `α`-range.  This replaces feasibility at `n₀`,
which for `n₀ < 36` does not follow from `α ≤ 17`. -/
lemma c_lo_nonneg {{α : ℝ}} (hα : 0 ≤ α) (hU : α ≤ {Us}) : 0 ≤ c {n0} α := by
  have h3 : (0 : ℝ) < 3 + α := three_add_pos hα
  rw [c_lo hα]
  apply div_nonneg _ (by positivity)
  nlinarith [mul_nonneg hα (sub_nonneg.2 hU), sq_nonneg α]

def Lc : ℤ := {L}

def betac : ℤ := {beta}

def tauc : ℤ := {tau}

/-- The moment numerator at `n₀ = {n0}`, `k = {k}`. -/
def Nmomc : List ℤ :=
  {Nmom}

theorem pev_Nmomc (α : ℝ) :
    pev Nmomc α = pev (wsum Lc 0 (qrow (gg0 {n0}) (gg1 {n0}) (gg2 {n0}) {k})) α := by
  refine pev_wsum_eq_of_packed (gg0 {n0}) (gg1 {n0}) (gg2 {n0}) {k} {mlen} Lc betac
    tauc Nmomc (by norm_num [betac]) (by norm_num [tauc]) ?_ ?_ ?_ ?_ ?_ ?_ α
  · refine rowZ_bound (gg0 {n0}) (gg1 {n0}) (gg2 {n0}) {k} 3 betac tauc
      (by norm_num [betac]) (by simp) (by simp) (by simp) ?_
    norm_num [gg0, gg1, gg2, l1, betac, tauc]
  · decide
  · refine wsum_bound (gg0 {n0}) (gg1 {n0}) (gg2 {n0}) {k} Lc betac
      (by norm_num [Lc]) ?_
    norm_num [gg0, gg1, gg2, l1, Lc, betac]
  · decide
  · exact wsum_length_le Lc _ 0
      (qrow_entry_length_le (gg0 {n0}) (gg1 {n0}) (gg2 {n0}) 3 (by simp) (by simp) (by simp) {k})
  · rfl

theorem integral_lo (α : ℝ) (hα : 0 ≤ α) :
    (∫ t in (0 : ℝ)..1, t ^ 3 * Q {n0} α t ^ {k})
      = pev Nmomc α / ((Lc : ℝ) * (2 * M {n0} * (3 + α)) ^ {k}) :=
  integral_moment_packed {n0} {k} (by norm_num) α hα Lc (by norm_num [Lc]) Nmomc
    (by decide) (pev_Nmomc α)

set_option maxHeartbeats 2000000 in
-- the degree-{d} Bernstein identity exceeds the default budget
/-- The certificate: `17 ^ {d} * P α` is a positive combination of `αʲ (17-α)^({d}-j)`. -/
lemma P_pos {{α : ℝ}} (hα : 0 ≤ α) (hα' : α ≤ {Us}) :
    0 < {P} := by
  have hu : (0 : ℝ) ≤ {LIN0} := by linarith
{haves}
  have hid : ({up} : ℝ) ^ {d} * ({P}) = {bern} := by
    ring
  rcases le_total α ({up} / (2 * {uq})) with h | h
  · have hpos : (0 : ℝ) < {G[0]} * {LIN} ^ {d} :=
      mul_pos (by norm_num) (pow_pos (by linarith) {d})
    linarith
  · have hpos : (0 : ℝ) < {G[d]} * α ^ {d} :=
      mul_pos (by norm_num) (pow_pos (by linarith) {d})
    linarith

set_option maxHeartbeats 2000000 in
-- clearing denominators across the batch identity exceeds the default budget
/-- **The batch `{n0} ≤ n ≤ {n1}`.** -/
theorem finite_range {{n : ℕ}} (h0 : {n0} ≤ n) (h1 : n ≤ {n1}) {{α : ℝ}}
    (hα : 0 ≤ α) (_hα' : α ≤ 17) (hfeas : c n α ^ 2 ≤ A n α) : R n α < 1 := by
  have h3 : (0 : ℝ) < 3 + α := three_add_pos hα
  have hMn := alpha_le_half_M (n := n) (by omega) hfeas
  -- feasibility caps α at M n / 2, which for a low batch is sharper than the ambient α ≤ 17
  have hUn : α ≤ {Us} := by
    have hcast : ((n : ℕ) : ℝ) ≤ ({n1} : ℝ) := by exact_mod_cast h1
    have hMle : M n ≤ ({n1} : ℝ) - 1 := by simp only [M]; linarith
    linarith [_hα']
  have hb := R_le_batch (n₀ := {n0}) (n := n) (n₁ := {n1}) (by norm_num) h0 h1 hα
    (c_lo_nonneg hα hUn) hfeas
  rw [show (({n0} : ℕ) : ℝ) - 4 = {n0-4} by norm_num] at hb
  rw [show ({n0-4} : ℝ) / 2 = (({k} : ℕ) : ℝ) by norm_num] at hb
  simp only [Real.rpow_natCast] at hb
  rw [integral_lo α hα, {MRW}, A_hi] at hb
  push_cast at hb
  have hid : (1 : ℝ) / 6 + 1 / (4 * (3 + α)) + 1 / (2 * {M0}) + 1 / (4 * {M0} * (3 + α))
      + (1 - 2 * α / {M1}) ^ 2 * {n1} * {M1} * ({n1} - 2) / (4 * (3 + α))
        * (pev Nmomc α / ((Lc : ℝ) * (2 * {M0} * (3 + α)) ^ {k}))
      = 1 - ({P}) / ({const} * (3 + α) ^ {p}) := by
    simp only [pev, Lc, Nmomc]
    push_cast
    field_simp
    ring
  rw [hid] at hb
  have hP := P_pos hα hUn
  have hq : 0 < ({P}) / ({const} * (3 + α) ^ {p}) := div_pos hP (by positivity)
  linarith

end B{n0}_{n1}

end Sendov
'''
out = Path(__file__).resolve().parents[1] / "Sendov" / "FiniteRange" / f"Degree{n0}_{n1}.lean"
out.parent.mkdir(parents=True, exist_ok=True)
out.write_text(src, encoding="utf-8", newline="\n")
print("written", out, len(src), "bytes")
