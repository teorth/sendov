# A degree-uniform scalar endgame for Sendov's conjecture

**Mathematical review note — not a standalone paper.**

**Local contribution: subfish-zhou (GitHub).** Original mathematical sources and authorship are credited below.

This note explains the scalar replacement in the mathematical source snapshot `c7f25171a07b916a678b0df1dbd32ee55eb5e4df`, relative to the fixed `teorth/sendov` base `1ddea92d89f951a0a7cbbffa6c267cf7e6640b1d`.[3] It is a reading guide, not a new standalone proof of the conjecture. Analytic lemmas not proved below are explicit inputs from the cited literature or named Lean results. The exact-arithmetic specification in §5 is self-contained with the adjacent `CERTIFICATES.json`; its scope is the three large-alpha identities, not all analytic implications.

## 1. The scalar theorem and its limits

For real parameters put

\[
u=\frac{\alpha}{\alpha+3},\qquad e(\alpha)=u-\frac{u^3}{30},\qquad
\beta_m(t;\alpha,\eta)=(1-t)^2+\eta t+\frac{2\alpha}{m}t(1-t),
\]
\[
\begin{aligned}
H_m(\alpha;\eta)={}&\frac{\eta}{2\alpha(1-\eta)}+\frac{\eta}{4\alpha}
+\frac1{2m}+\frac{\eta}{4\alpha m}\\
&+\frac{\eta(m^2-1)(m-2\alpha)^2}{4\alpha m}
\int_0^1t^3\beta_m(t;\alpha,\eta)^{(m-3)/2}\,dt.
\end{aligned}
\]

**Existing Lean result, in mathematical notation:**

\[
\boxed{m\in\mathbb R,\ m\ge5,\quad0<\alpha\le17,\quad2\alpha\le m
\quad\Longrightarrow\quad H_m(\alpha;e(\alpha))<1.}
\]

This is `Sendov.distillScalar_lt_one_real` in `Common/DistillationBounds.lean`. All source paths in this note omit the prefix `Sendov/` and refer to that mathematical source snapshot. The kernel and envelope definitions are in `Common/DistillationKernel.lean` and `Common/DistillationEnvelope.lean`.

The domain includes `2*alpha = m`; the integral prefactor then vanishes and is never cancelled as a nonzero quantity. No extra hypothesis from Tao's old linear-envelope tail is imposed. This is not interpolation between integer-degree rows. Nor does it assert that `H` is monotone in `m`, that its maximum has been found, that `5` is the smallest admissible real threshold, or that An's `<199/200` margin survives.[2]

**Zero is different.** Under Lean's totalized division, the raw expression at `alpha=eta=0` is `1/(2*m)` (`scalarObstruction_zero`). An's continuous extension along `eta=e(alpha)` has value

\[
\frac14+\frac7{12m}+\frac1{2(m-2)}.
\]

These are distinct definitions at zero.[2] The boxed result is a positive-alpha theorem; it makes no raw continuity claim.

## 2. What is inherited, and how the result is consumed

The geometric convention is **`m=n-1`**, with `n` the polynomial degree. In the normalized interior reduction, `alpha=m(1-a^2)/2`, where `a` is the real distinguished root, and `eta=beta(1)`. Tao's Lemma 6 and Propositions 10–11 supply the identity/reduction framework and `alpha<=17`; his Remark 8 records earlier sources of the identities.[1] An's §§2–4 give the scalar reformulation, its eta monotonicity, the cubic envelope and the two-chord majorization.[2]

The local `cubicScalar_constraints_of_polar_origin` derives `0<alpha<=17`, `2*alpha<=m`, and `1<=H_m(alpha;e(alpha))` from the original polar/origin hypotheses. `polar_origin_incompatible` combines that lower bound with the boxed theorem. The weak polar input remains `1<=I`; `eta_lt_cubicPolarEnvelope` proves the strict envelope bound from it. These inequalities are **derived**, not extra assumptions on a polynomial.

Degrees `n=2..5` still use `Analytic/LowDegree.lean`. The center, unit-circle boundary, rotation and equality classification stay on the existing route through `Interior`, `Boundary` and `Conjecture`. `Solution.lean` preserves both original `SendovConjecture.sendov` and `SendovConjecture.phelps_rodriguez` contracts. Nothing here is a first solution of either conjecture.

An is credited for `e`, the strong hyperbolic comparison, `h=3/5`, the two-chord constants and mixed endpoints.[2] The local hyperbolic formalization replaces An's coefficient argument with a derivative chain; this note **uses** that comparison and does not reproduce its proof. The already acknowledged Pickhardt mean/variance influence is not reassigned to this work.[4] Without a precise fixed-version literature location, it is excluded from novelty claims; no conditional threshold theorem from that project is used.

The local contribution relative to these inspected sources is the degree-ray assembly: retain the actual elementary term, keep the same alpha while eliminating degree dependence, and combine fixed alpha budgets. This is not a literature-wide priority claim.

## 3. Inputs and the three-region assembly

Set `eta=e(alpha)`, `r=e(alpha)/alpha` for positive alpha,

\[
K=\frac{m^2-1}{4m}\,r(m-2\alpha)^2,\qquad
q=\frac4{25}+\frac35e(\alpha)+\frac{12\alpha}{25m},\qquad s=\frac{m-3}{2},
\]
\[
E_m=\frac{e}{2\alpha(1-e)}+\frac{e}{4\alpha}
+\frac1{2m}+\frac{e}{4\alpha m},
\]
\[
T_0=K\frac{96(3/5)^4}{(m-1)(m+1)(m+3)(m+5)(1-q)^4},\quad
T_1=\frac{259}{3125}Kq^s,\quad
T_2=\frac{421}{3125}Ke^s.
\]

The bound `H<=E_m+T0+T1+T2` is the consumed input `distillScalar_le_elementary_components`, based on An's two-chord method and the exact elementary-term bridge.[2] The secant convexity step uses `s>=1`, which explains this proof's `m>=5` range without proving a minimality result. For the exact retained loss,

\[
E_m=\frac14+\frac7{12m}-L_m,\qquad
L_m=\frac{u^2}{180(1-e)}+
\frac{u(30+u-u^2)}{360}\left(1+\frac1m\right).
\]

This identity reorganizes existing rational expressions; the useful change is not discarding the loss before the final estimates.

| Region | Closure and explicit proof input |
|---|---|
| `0<alpha<=7/5` | A full chord, integrated only to its nonnegative zero, gives `H<=C<1`, where `C=1/4+7/(12m)+(8/27)(alpha+3)^3(m-2alpha)^2/[m(m+3)(m+5)]`. `distillScalar_lt_one_small_alpha` uses a fixed degree-five interval identity, with six polynomial coefficients in `m-5` and square decompositions. That identity is in `DistillationTotalBound`, not proved by this note. |
| `7/5<=alpha<=2` | Split alpha at `17/10`, not degree. Two positive sextics in `m-5` bound `T0`; mixed-endpoint exponential bounds control `T1,T2`. `distillScalar_lt_one_middle_alpha` combines `E<=221/660`, `T0<=13/50`, `T1<=7/30`, `T2<=1/6`, totaling `3283/3300<1`. Use `DistillationMiddleEstimates` and `DistillationMiddleAlpha` for the component proofs. |
| `2<=alpha<=17` | `DistillationCorrelatedPeak` and `DistillationPeakRational` give whole-ray peak bounds. First peak `<b(alpha)`, and elementary + zeroth + second peak `<1-b(alpha)`, with `b=(431-3alpha)/2500`. Three full alpha identities close these strict inequalities; the complementary bound splits at `5/2`, where `max(5,2alpha)` changes formula. |

Thus removal of degree tables does **not** remove subdivisions or all finite algebraic checks. An's real tail already covered `m>=81`; the new theorem covers the entire real range from `5`, including the nonintegers below `81` not supplied by his finite integer table.[2]

## 4. Why keep the same alpha?

With `t=m-2*alpha>=0`, `m(m-2alpha)^2=t^3+2alpha*t^2`. For `c>0`, the standard exponential peak inequality gives

\[
m(m-2\alpha)^2e^{-c(m-3)}
\le e^{-c(2\alpha-3)}
\left(\frac{27e^{-3}}{c^3}+\frac{8\alpha e^{-2}}{c^2}\right).
\]

This is `distill_degree_exp_le_peak`. The two terms peak separately; “same-alpha” does not assert a common optimizing degree.

For `T0`, let `d=21/25-3e/5`, `ell=(6/25)/d` and `z=(m-2alpha)/(m-2alpha*ell)`. The proof supplies the needed denominator and range facts and uses

\[
0\le z\le1,\qquad z^2(1-z)(1-\ell z)
\le(1-\ell)\frac4{27}+\frac{\ell}{16}.
\]

For `T1`, put `B=8/25+3e/5`,

\[
c_1=\frac{1-B}{1+B}+\frac{2(\alpha-1)}{25\alpha B},\qquad
v_1=\frac{6(\alpha-1)^2}{25\alpha B}.
\]

The proof of `distillNode_rpow_le_exp` bounds `q^s` by `exp(-c1*(m-3)+v1)`. Its algebraic remainder after the logarithmic bound is exactly

\[
\frac{2(m-3\alpha)^2}{25\alpha Bm}\ge0.
\]

The reciprocal correction has not been silently discarded. The elementary term is bounded at the **actual** degree floor `max(5,2alpha)`. Rationalization uses `exp(-2)<=677/5000`, `exp(-3)<=249/5000` and positive Taylor denominators. First-peak algebra deliberately drops nonnegative fifth/sixth Taylor terms, using a fourth-order denominator; the second peak keeps sixth order. This is a controlled relaxation, not pointwise superiority of every new bound.

The missing range, logarithmic and integral arguments are supplied by the named Lean results, not by the following numerical certificate specification.

## 5. Self-contained specification for the fixed identities

This section and `CERTIFICATES.json` specify an exact check without a numerical optimizer, root isolator, Lean parser or certificate search. All arithmetic is over arbitrary-precision integers/rationals. The JSON is a decimal transcription of the candidate's complete lists; strings must **not** be converted through floating point.

For this section only write `a=alpha` (not the geometric root of §2), and define these polynomials:

```text
S = a+3
N = 29*a^2+180*a+270
P = 5*a^3+36*a^2+78*a+48
W = 95*a^3+774*a^2+2052*a+1782
V = 9*P*W
C = 605*a^7+13426*a^6+113310*a^5+470394*a^4
    +1001268*a^3+969084*a^2+174960*a-192456
X = 70*a^7+7769*a^6+85302*a^5+334746*a^4
    +393390*a^3-616248*a^2-1758348*a-997272
F = a^3+90*a^2+540*a+810
G = 59*a^3+450*a^2+1080*a+810
D = 13*a^3+198*a^2+864*a+1134
J = 97*a^3+2169*a^2+10827*a+15147

t4(x,v) = 24*v^4+24*x*v^3+12*x^2*v^2+4*x^3*v+x^4
t6(x,v) = 720*v^6+720*x*v^5+360*x^2*v^4+120*x^3*v^3
          +30*x^4*v^2+6*x^5*v+x^6

A1 = 259*N*a^3*V^6*(6723*V+5416*C)
B1 = 78125000*S^3*C^3*t4(X,V)
A2 = 1263*N*G^8*(6723*G+5416*a*F)
B2 = 7812500*S^3*F^3*t6((2*a-3)*F,G)
Q  = a*S^3*F^3*D^3*t6((2*a-3)*F,G)
b  = (431-3*a)/2500
E(v) = N/(2*F)+N/(120*S^3)+(1/2+N/(120*S^3))/v
Z0 = 3000*S^9*N*J/(a*F^2*D^3)
```

Here `A1/B1` is the relaxed rational first-peak bound and `A2/B2` the rational second-peak bound; `Z0` is the zeroth-peak bound. This correspondence is an input from `PeakAlgebra.peak1_le_four`, `peak2_eq`, `peak0_eq`, and `elementary_eq`.

Construct the three polynomials by **exact rational cancellation**:

```text
gap1    = b*B1-A1
gapLow  = 7812500*Q*(1-b-E(5)-Z0-A2/B2)
gapHigh = 93750000*Q*(1-b-E(2*a)-Z0-A2/B2)
```

Require cancellation to leave a polynomial, not a sampled rational function. Equivalently, multiply denominators and check polynomial identities before cancellation. These are the budget-gap equalities `gap1_eq`, `gapLow_eq`, `gapHigh_eq`; their multipliers are part of the specification, not optional normalizations.

| JSON gap | Closed interval `[L,U]` | Degree `d` | Positive scale `s` | Ordered coefficient count | Lean identity |
|---|---|---:|---:|---:|---|
| `gap1` | `[2,17]` | 53 | `15^53` | 54 | `PeakClosure.gap1_identity` |
| `gapLow` | `[2,5/2]` | 47 | `1` | 48 | `PeakClosure.LowHomogeneous.identity` |
| `gapHigh` | `[5/2,17]` | 47 | `29^47` | 48 | `PeakClosure.HighHomogeneous.identity` |

For each record, index `i=0,...,d` means exactly

\[
\boxed{s\,\mathrm{gap}(a)=
\sum_{i=0}^d c_i(a-L)^i(U-a)^{d-i}.}
\]

There is **no additional binomial coefficient**. The lowest index is the `y^d` term, not the `x^d` term. The JSON also includes all 71 low-degree factor coefficients: First has 29, Low and High each have 21. The factor named `SH`, for example, means the homogeneous representation of `S`, and likewise `NH,PH,WH,CH,XH,FH,GH,DH,JH` where present. For factor degree `k`, check its listed `scale*f(a)` against the same ordered sum on that record's interval. `VH=9*PH*WH` is derived, not another stored coefficient list.

**Acceptance procedure:**

1. Require the exact three records, exact interval/degree/scale metadata above, and list lengths `54/48/48`. Check the 71 factor entries and their identities if checking the factored implementation as well as the target identities.
2. Independently construct all factors, rational budget differences, and resulting polynomials from the displayed formulas. Expand both sides of each boxed identity using exact polynomial addition, multiplication and nonnegative integer powers. Compare **every coefficient**, allowing only trailing zero padding; require degrees at most the specified `d`.
3. Require `s>0`, `L<U`, `c_i>=0` for every entry, and `c_0>0`, `c_d>0`. The supplied lists in fact have every coefficient positive. At an interior point both interval coordinates are positive; at either endpoint the appropriate axis coefficient is positive. This proves strict gap positivity on the whole closed interval.
4. Justify denominator signs separately before returning to rational inequalities. On `[2,17]`, `a,S,N,P,W,V,F,G,D` are positive; `C,X>0` are the sign lemmas `C_pos`, `X_pos` in `PeakAlgebra` (their positive homogeneous representations also permit an interval check here). Hence `B1,B2,Q>0`; `t4,t6` have positive constant terms in a positive second argument and nonnegative first argument. Therefore `gap1>0` proves `A1/B1<b`; `gapLow>0` or `gapHigh>0` proves the complementary bound with the correct degree floor.
5. Combine those budget inequalities only **after** invoking the analytic peak majorizations of §§3–4. Passing the finite identity check alone is not a proof of the integral inequality or the geometric reduction.

Checking positive entries without the full polynomial identity, evaluating at a mesh, checking only endpoints, using approximate coefficients, or truncating the vectors must be rejected. A useful implementation should also reject a changed interior coefficient, scale, interval, order or truncation; those are controls, not replacement proof obligations.

The initial transcription pass checked signs, counts and scales. A subsequent parent-side replay with `check_note_certificates.py` independently constructed the polynomials from the displayed formulas and checked all three complete identities, all 18 listed factor identities, and rejection of one changed interior coefficient in each large identity, using exact rational arithmetic with SymPy 1.13.1. The results are in `CERTIFICATE_REPLAY.json`. This is a new non-Lean algebraic check, not a new proof of the analytic majorizations; formal acceptance remains the R12/R13 evidence summarized in the pull-request description. The three lists contain integers of up to 98, 82 and 99 decimal digits, respectively. A uniform degree organization need not be a simpler hand calculation.

To replay this check in the documented SymPy environment, from `docs/degree-uniform`:

```sh
python check_note_certificates.py
```

## 6. Review boundary

Read `Reduction/CubicScalar` and `Common/DistillationBounds` first; follow the small/middle branch files, then `CorrelatedPeak -> PeakRational -> PeakAlgebra -> PeakFirst/PeakRest -> PeakClosure`. General certificate logic lives in `BernsteinList`, `BernsteinCert`, `BernsteinRing`. The complete source carries the proofs and the data; this short note intentionally does not repeat the original paper or hide unshown lemmas behind a claim of independent sufficiency.

An's table has 77 integer-degree rows and critical equations of degrees 7/7/4; the local retired intermediate table had 52 degree records; this endgame has three high-degree alpha identities.[2] These are different units. The claim is a whole-real-degree scalar assembly with fixed certificates, not an optimal, certificate-free, universally more hand-checkable proof.

No Lean build, benchmark or project test suite was rerun for this documentation pass; CI status is reported separately on the pull request. The original final contracts and reported trust base are described in the PR body, together with portable commands and the exact limitations of earlier verification. A publication-ready standalone exposition, literature-priority assessment and independent complete analytic review remain outside this draft's claims. The additional exact certificate replay is limited to the finite polynomial identities specified above.

## Sources

[1] https://terrytao.wordpress.com/2026/08/12/a-digestion-of-the-proof-of-sendovs-conjecture
[2] https://github.com/SJanPerth/Sendov-Proof-Distillation/blob/e8ae601491ec171ab4f7f8456113dd6a047aa85d/paper/Proof_Distillation_for_Sendovs_Conjecture.pdf
[3] https://github.com/teorth/sendov/tree/1ddea92d89f951a0a7cbbffa6c267cf7e6640b1d
[4] https://github.com/pickhardt/sendov-explicit-threshold
