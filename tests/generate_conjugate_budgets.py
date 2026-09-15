#!/usr/bin/env python3
"""Generate exact conjugate diagnostics. All rational claims are replayed by Lean.
Uses squares of the complete normalized C*H term, so no irrational approximation
or omitted high endpoint enters the proof. Run only in this checkout.
"""
from fractions import Fraction as Q
from math import comb
from pathlib import Path
import json
ROOT = Path(__file__).resolve().parents[1]
DATA = [(3, 6, Q(9,10), Q(49,50), Q(1,250), Q(1,1000)),
        (4, 8, Q(99,100), Q(497,500), Q(1,2500), Q(1,10000)),
        (5, 20, Q(9,10), Q(83,100), Q(1,50), Q(7,1000)),
        (6, 100, Q(9,10), Q(61,100), Q(3,250), Q(33,10000)),
        (7, 100, Q(99,100), Q(22,25), Q(1,1000), Q(1,10000))]
def rat(x):
    x=Q(x)
    return str(x.numerator) if x.denominator==1 else f'({x.numerator} / {x.denominator})'
def multiply(p,q):
    out=[Q(0)]*(len(p)+len(q)-1)
    for i,a in enumerate(p):
        for j,b in enumerate(q):out[i+j]+=a*b
    return out
records=[]
for num,m,a,x,b,c in DATA:
    name=f'DI{num:02d}'; n=m//2; z=a*x; v=1-x*x
    endpoints=[sum((Q(comb(m+1,j))*z**j*(1-z)**(m+1-j) for j in range(k+1)),Q()) for k in range(m+1)]
    prefix=(1-z)**(m+1)+v/((m-1)*x*x)*endpoints[2]
    majorant=prefix+b+(m-3)*c
    assert majorant+v/((m-1)*x*x)<1-z
    lines=['import Sendov.Analytic.PaperConjugate', '', 'noncomputable section',
           'set_option maxRecDepth 10000', 'set_option maxHeartbeats 4000000',
           'set_option linter.style.whitespace false',
           'open scoped BigOperators', f'namespace Sendov.PaperConjugate.{name}',
           'open PaperCentered PaperCenteredBound',
           f'def a : ℝ := {rat(a)}', f'def x : ℝ := {rat(x)}',
           f'def q : Multiset ℂ := family {n} x', '']
    lines+= [f'theorem endpoint_0 : BR {m} 0 (a*x) = {rat(endpoints[0])} := by',
             '  norm_num [BR, a, x]', '']
    for k in range(1,m+1):
        lines += [f'theorem endpoint_{k} : BR {m} {k} (a*x) = {rat(endpoints[k])} := by',
                  f'  change BR {m} ({k-1}+1) (a*x) = _',
                  f'  rw [BR_succ, endpoint_{k-1}]',
                  '  norm_num [a, x, Nat.choose_eq_descFactorial_div_factorial]', '']
    for k in range(3,m+1):
        s=v**m if k==m else Q(m**m,k**k*(m-k)**(m-k))*v**k
        bound=b if k==3 else c
        assert s*(1-endpoints[k])**2 <= (bound*comb(m,k)*x**k)**2
        lines += [f'theorem term_{k} : term {m} {k} x (a*x) ≤ {rat(bound)} := by',
                  f'  unfold term', f'  rw [endpoint_{k}]',
                  ('  rw [C_top]' if k==m else '  rw [C_interior _ _ _ (by norm_num) (by norm_num)]'),
                  '  apply sqrt_term_le <;> norm_num [a, x, Nat.choose_eq_descFactorial_div_factorial]', '']
    lines += [f'theorem scalar_bound : scalarBudget {m} a x ≤ {rat(majorant)} := by',
              f'  have h := scalarBudget_le {m} (by norm_num) a x {rat(b)} {rat(c)} term_3 (by',
              '    intro k hk', '    obtain ⟨hlo, hhi⟩ := Finset.mem_Ico.mp hk', '    interval_cases k']
    lines += [f'    · exact term_{k}' for k in range(4,m+1)]
    lines[-1]+=')'
    lines += ['  rw [endpoint_2] at h', '  norm_num [a, x] at h ⊢', '  exact h', '',
              f'theorem scalar_budget : scalarBudget {m} a x + (1-x^2)/({m}-1)/x^2 < 1-a*x := by',
              f'  have h := scalar_bound', '  norm_num [a, x] at h ⊢', '  linarith', '',
              'theorem pointwise : ∀ w ∈ q, ‖w‖ = 1 := norm_family _ _ (by norm_num [x])',
              f'theorem cardinality : q.card = {m} := by simp [q]',
              'theorem mean : q.sum / q.card = (x : ℂ) := mean_family _ (by norm_num) _',
              'theorem actual_variance : variance (q.map (fun w => w-(x : ℂ))) = 1-x^2 :=',
              '  variance_family _ (by norm_num) _ (by norm_num [x])', '',
              'theorem paper_budget :',
              '    majorant_Efin (q.map (fun w => w-(x : ℂ))) (x : ℂ) ((a : ℂ)*x) +',
              '      Gamma (q.map (fun w => w-(x : ℂ))) (x : ℂ) < 1-a*‖(x : ℂ)‖ := by',
              f'  rw [show q = family {n} x from rfl, budget_eq _ (by norm_num) _ _ (by norm_num [x]) (by norm_num [x])]',
              f'  rw [Gamma, variance_family {n} (by norm_num) x (by norm_num [x])]',
              '  simpa [x, Complex.norm_real, Real.norm_eq_abs, div_mul_eq_div_div] using scalar_budget', '',
              f'theorem norm_J_gt_one : 1 < ‖J {n} a x‖ :=',
              '  budget_implies_J _ (by norm_num) _ _ (by norm_num [a])',
              '    (by norm_num [x]) (by norm_num [x]) scalar_budget', '']
    p=[Q(1)]
    for _ in range(n): p=multiply(p,[a*a,2*a*(1-a*a)*x,(1-a*a)**2])
    polar=sum((v/Q(k+1) for k,v in enumerate(p)),Q())
    assert polar>1
    lines += [f'def pc : Fin {m+1} → ℝ := !['+', '.join(rat(v) for v in p)+']',
              f'theorem expansion (t : ℝ) :',
              f'    (a^2+2*a*(1-a^2)*x*t+(1-a^2)^2*t^2)^{n} =',
              f'      ∑ k : Fin {m+1}, pc k*t^k.val := by',
              '  norm_num [a, x, pc, Fin.sum_univ_succ]', '  ring', '',
              f'theorem polar_integral : K {n} a x = ({rat(polar)} : ℝ) := by',
              '  rw [K_eq _ _ _ (by norm_num [x]), integral_coeffs _ pc _ expansion]',
              '  norm_num [pc, Fin.sum_univ_succ]', '',
              f'theorem full_polar : 1 < ‖K {n} a x‖ := by',
              '  rw [polar_integral]', '  norm_num [Complex.norm_real, Real.norm_eq_abs]', '',
              '#print axioms pointwise', '#print axioms mean', '#print axioms actual_variance',
              '#print axioms paper_budget', '#print axioms norm_J_gt_one', '#print axioms full_polar',
              f'end Sendov.PaperConjugate.{name}', '']
    path=ROOT/'tests'/f'PaperConjugate{name}.lean';path.write_text('\n'.join(lines))
    records.append(dict(id=name,m=m,a=str(a),x=str(x),terms=m-2,majorant_upper=str(majorant),polar=str(polar)))
(ROOT/'tests'/'conjugate-data.json').write_text(json.dumps(records,indent=2)+'\n')
print(json.dumps([dict(id=r['id'],m=r['m'],terms=r['terms']) for r in records]))
