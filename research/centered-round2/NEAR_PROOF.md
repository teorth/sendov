# Round 2: positive-variance small-lambda theorem

## New paper theorem

For every natural m≥7, every 0<a<1 with

    λ=m(1-a) ≤ 4/39,

and every actual m-element complex q family satisfying the original pointwise disk and FULLpolar conditions, the **original** square-root majorant satisfies

    E_fin + Γ < (99/100)(1-a) < 1-a|μ|.

The argument allows positive variance and nonreal mean; no additional q premise is imposed. This is a continuous uniform degree domain, not a degree certificate table. The region automatically lies in the requested near-a domain.

**Formalization status: complete for this small-lambda theorem.** `CenteredNearTheorem.C_near_fullpolar_small` composes the newly kernel-checked binomial-mode coefficient bound, factorial tail, actual H-integral adapter, beta/chord integration, and scalar/endpoints into the original pointwise + FULLpolar statement. No tail or error-budget hypothesis remains. `norm_J_gt_one_fullpolar_small` also derives the first-origin norm obstruction. The integrated axiom audit has only propext, Classical.choice, and Quot.sound.

## Proof

Write h=1-a, u=|μ|, x=Re μ, actual v=mean|q-μ|², b=1-2ax+a², and rho=2/11. Pointwise and full polar imply the accepted raw-polar bounds

    b ≤ λ/(3+λ) ≤ 4/121=rho²,
    v ≤ λ/3,
    Γ < 7h/18,
    |aμ|≤1,  |1-aμ|²≤b.

The actual-variance inequality v≤λ/3 follows directly from v≤1-u², 1-b≤u², and b≤λ/3. The latter is a relaxation of rational polar. No independently chosen variance is substituted.

### A. Cubic tail

Squared-norm convexity gives, for 0≤t≤1,

    β(t)=1-2axt+a²t² ≤ [1-(1-rho)t]² = [1-(9/11)t]².

One direct algebraic verification writes the difference as

    t²(rho²-b)+2t(1-t)[rho-(1-ax)] ≥0;

here (1-ax)²≤b and 0≤1-ax≤rho.

The exact finite beta integral therefore gives

    ∫₀¹ t³ β(t)^((m-3)/2)dt
      ≤ 6 / [(9/11)^4 (m+1)m(m-1)(m-2)].

Combining the previous finite structural T₃ estimate, with S₃=9/4, yields

    tail ≤ 9a⁴u v^(3/2) / [(9/11)^4 sqrt(m(m-1)(m-2))]
         ≤ tailScalar(m,v).

The last inequality uses only 0≤a,u≤1, where

    tailScalar(M,v)=9 sqrt(v³/[M(M-1)(M-2)])/(9/11)^4.

For every real M≥7, with Mh≤4/39 and 0≤v≤Mh/3,

    49 M(M-1)(M-2) ≥30M³,
    h≤4/273,

and hence

    (tailScalar/h)² ≤ (14/195)(11/9)^8
                    =3001024334/8394110595 <9/25.

Thus tail≤3h/5. The exact rational gap in the last comparison is

    9/25-(14/195)(11/9)^8 =104277401/41970552975 >0.

The factor inequality is exact:

    49M(M-1)(M-2)-30M³ = M(M-7)(19M-14) ≥0.

This whole scalar estimate is compiled in `CenteredNearScalar.tailScalar_le`; the beta-to-squared-chord and weighted integral inequalities compile in `CenteredNearChord`.

### B. Both finite endpoint terms

Let w=|1-aμ|≤rho and z=aμ. Expanding B₂ and taking norms gives

    |B₂(z)| ≤ (m+1)² rho^(m-1).

This keeps the actual finite endpoint; it does not replace B₂ by a probability. Since w²≤mh/3,

    w^(m+1) ≤ (mh/3)rho^(m-1).

The two elementary sequences are decreasing for m≥7:

    m rho^(m-1) ≤7rho⁶,
    (m+1)²rho^(m-1) ≤64rho⁶.

The successor inequalities are `(m+1)rho≤m` and `(m+2)²rho≤(m+1)²`; these are uniform algebra, not a table. Therefore

    E_end/h ≤ (7/3)rho⁶+(7/18)64rho⁶
            =15680/15944049 <1/1000.

`CenteredNearEndpoint.actual_endpoint_le` proves this on the actual centered multiset directly from pointwise, raw polar and λ≤4/39.

### C. Close the original budget

    E_fin+Γ ≤ E_end+tail+Γ
             < (1/1000+3/5+7/18)h
             = (8909/9000)h <(99/100)h <h≤1-au.

The scalar closure is compiled as `budget_close`. It is not a proof that E_fin≤h/2, nor is that stronger intermediate target required. No premise was adjusted to obtain this alternative sufficient budget.

## Remaining scope

The region λ>4/39 is not solved by this particular theorem. The final round2 integration additionally kernel-checks λ≤1/4 and the strip v≤h/m², with no remaining tail hypotheses. Independently checked paper arguments extend to λ≤1/3 and all m≥45; the exact remaining paper domain is 7≤m≤44, 1/3<λ≤m/10, v>h/m². See the final REPORT/RESULT for the authoritative evidence-level distinction. The previous-round frozen deliverable remains read-only.
