# Uniform actual-mean C-near — reviewed paper proof and Lean evidence

## Verdict

**The original square-root-C majorant is sufficient throughout the requested domain.** The full paper proof has passed independent mathematical review and exact arithmetic reconstruction. Its quantitative conclusion is

    E_fin + Gamma <= 1-a|mu| - (1-a)/20 < 1-a|mu|.

The statement is for every natural m>=7, every9/10<=a<1, and every original feasible complex family. No mathematical parameter region remains open for this C-near statement at paper level.

**This is not a global Lean/kernel theorem.** The archive includes fully checked near/variance-strip theorems and generic structural consumers; the concrete global certificate instantiations and the unbounded-cutoff formalization remain open. The evidence map below distinguishes these levels.

## 1. Exact quantified statement

Let q_1,...,q_m be complex, with

    |q_j|<=1 for every j,
    |integral_0^1 product_j[a+(1-a²)t q_j]dt|>=1.

Set

    mu=mean(q_j), u=|mu|, s=mean(|q_j|²), v=mean(|q_j-mu|²)=s-u²,
    h=1-a, lambda=mh, z=a mu, w=|1-z|,
    Gamma=v/[(m-1)u²].

The hypotheses imply u>0. Retain the original coefficients and finite endpoints:

    C_(m,k)(v)²=m^m v^k/[k^k(m-k)^(m-k)] for0<k<m,
    C_(m,m)(v)²=v^m,
    B_(m,k)(z)=sum_(j=0)^k binom(m+1,j)z^j(1-z)^(m+1-j),
    H_(m,k)(z)=1-B_(m,k)(z),
    Tail=sum_(k=3)^m C_(m,k)(v)|H_(m,k)(z)|/[binom(m,k)u^k],
    E_fin=w^(m+1)+Gamma|B_(m,2)(z)|+Tail.

Then E_fin+Gamma<=1-au-h/20. The mean and variance come from these same q_j. Nonreal means, unbalanced/multimodal families, s<1, and v=0 are not excluded. FULLpolar is the norm of the complex integral, not an integral of norms used as a replacement premise. No first-origin identity, extra alpha cutoff, or real-mean/saturation hypothesis has been inserted.

This proves the requested alternative sufficient budget. It does **not** prove the stronger standalone assertion E_fin<=h/2 globally. No weakening of C or of the original target was necessary.

## 2. Why the structural route works

### The finite H normalization retains the actual mean

For complex mu!=0,

    H_(m,k)(a mu)/[binom(m,k)mu^k]
      =(m+1)a^(k+1)mu integral_0^1 t^k(1-a mu t)^(m-k)dt.

The inverse mean powers cancel before norms are taken. The binomial-mode bound

    C_(m,k)(v)²<=(2k+1)binom(m,k)v^k

and factorial-weighted Cauchy–Schwarz give a single tail integral with

    S_m=9/4-2/(m-1)-1/[2m(m-1)], D_m=m(m-1)(m-2),
    beta_s(t)=1-2a Re(mu)t+a²s t²,
    Tail<=sqrt(S_m)(m+1)a^4 u v^(3/2)sqrt(D_m)
          * integral_0^1 t³ beta_s(t)^((m-3)/2)dt.

This is the original C tail, including its top branch, not a bound for substituted actual coefficients.

### FULLpolar supplies stronger moment information

AM–GM on the actual squared factor norms yields

    1<=N_m(a,x,s)
      =integral_0^1[a²+2a(1-a²)xt+(1-a²)²s t²]^(m/2)dt.

A single upper-exponent moment below1 implies x>X for every smaller m through probability Jensen/Lyapunov. This is an integral inequality; pointwise comparison of powers across a kernel crossing1 would be invalid.

Endpoint moments are certified on the entire continuous h interval by exact Bernstein coefficient signs. These are polynomial identities and sign certificates, not quadrature or inference from a mesh.

### Keep curvature and spend the actual-mean budget

The substitution y=at cancels a^4 exactly. Keep the quadratic1-2xy+s y² instead of replacing its square root by a whole-interval norm chord. On a band with x>X>=1/sqrt2,

    u sqrt(v)<=X sqrt(1-X²),
    1-au=(1-u)+hu>=v/2+Xh.

These coupled bounds preserve the slack that coarse endpoint and h-only estimates lost. All three complex B2 terms are retained before justified triangle inequalities.

## 3. Coverage and methodological scope

The common h/20 margin follows by combining:

- natural7..34: one generic criterion applied to eight continuous degree bands, each with margin at least h/20;
- natural35..44: the reviewed curvature-preserving theorem, margin107h/250;
- naturalm>=45: the reviewed cutoff theorem, margin at least14h/15, including its unbounded high-degree argument.

The new residual bands are [7,8], [9,10], [11,12], [13,14], [15,18], [19,22], [23,28], and [27,34]. Their integer union is exactly7..34. Scalar inequalities hold throughout each closed real interval; no finite-product object with noninteger m is asserted.

**This is finite-band certificate mathematics.** It is not an independent original-majorant test or certificate for each degree. It is also not a certificate-free single formula: eight band-dependent parameter choices remain, and the first four bands each contain two integers. The generic analytic criterion, continuous polynomial signs, monotonicity and integer coverage—not passing a list of sample families—supply the proof.

The corrected cutoff35 source in this package changes only three intermediate strict inequalities after multiplication by v into weak inequalities. This removes the v=0 notation error; all constants, premises and final margins are unchanged. Original versions are preserved outside this frozen package.

## 4. What is and is not kernel-checked

### Complete original-constraint consumers

- `Sendov.CenteredThird.C_near_fullpolar_third`: all m>=7 with lambda<=1/3, margin37h/819, no tail-budget premise.
- `Sendov.CenteredThird.norm_J_gt_one_fullpolar_third`: the corresponding original complex-integral norm obstruction.
- `Sendov.CenteredThinVariance.C_near_fullpolar_strip`: all lambda in the original a-domain when the actual v<=h/m², margin19h/840.

### Checked general structural machinery

- All-degree original-H normalization and actual-C binomial/factorial tail bounds.
- Exact finite weight S_m and the retained a^4/variance improvements.
- `CenteredActualPolar.actual_variance_moment_of_fullpolar`: FULLpolar to the actual second-moment norm integral, with s computed as actual centered variance plus squared mean norm.
- `CenteredMeanBudget.Gamma_le_fullpolar_degree`: Gamma<=[(m+30)/(30(m-1))]v from the original data.
- `CenteredEndpointMoment.real_mean_gt_of_endpoint_moment`: generic Jensen/Lyapunov transfer from a certified upper moment.
- Generic Bernstein sign consumers and `EndpointBernsteinCertificate`.
- `CenteredBand.C_near_fullpolar_band_of_certificate`: the actual original-C tail, endpoints and final margin from explicit moment/integral/scalar certificates.

### Still open in Lean

The concrete Bernstein coefficients, their negative signs and exact integral/Bernstein identities must be instantiated and checked in Lean. The polynomial tail integrals and scalar comparisons must be connected to those instances. The reviewed unbounded-cutoff paper argument also remains to be formalized. A generic theorem accepting those explicit certificates is not a completed global instantiation.

The frozen bundle contains41 Lean modules, including previous dependencies and audit modules—not41 new theorems. All82 fresh compile/kernel invocations succeeded; the corrected aggregate audit verified111 distinct queried declarations using only the allowed axiom footprint. `LEAN_VERIFICATION.json` records the source/object receipts and axiom queries. The allowed footprint is propext, Classical.choice and Quot.sound. No custom axioms, sorry/admit, or native_decide are used. The final one-command exact/receipt verification, including full reconstruction of the13 historical rational families, exited0.

## 5. Counterexamples to bad envelopes, not to original C-near

At m=44,a=9/10, take22 copies each of

    q±=[(9999+200i)/10001]*[(21±20i)/29].

The actual mean is nonreal, every pointwise norm is exactly1, and rational complex integration proves FULLpolar. On this same literal family:

- the finite whole-interval norm-chord tail envelope alone exceeds2.0517 times the entire C-near budget;
- the original E_fin/h is exactly enclosed below0.236;
- retaining quadratic curvature gives an exactly certified total bound below0.175543 times the budget.

Thus finite endpoint retention alone does not repair the whole-interval chord loss. The preserved obstruction is to that auxiliary consumer, **not** to C or the original premises. No claim of a mathematically minimal replacement budget is made or needed.

The independent global audit additionally certifies a nonreal, s<1, positive-variance FULLpolar family at m=7,a=9/10, outside both prior kernel regimes, directly against the original C sum. Exact objects and radical intervals are in the audit evidence.

## 6. Diagnostics and the a->1 optimization issue

The historical archive retains the initial deterministic search and high-precision/rational diagnostics: m7,8 and larger degrees, nonreal means, unbalanced two-/three-/four-modal families, radial factors, and a approaching1. It includes13 distinct exact rational feasible families. The m2048 comparisons at a=0.9 and a=0.999999999999 are high-precision evidence, not rational interval certificates. Literal rounded candidates that failed pointwise/FULLpolar checks were rejected; they were not silently normalized.

New diagnostics distinguish rational moment, polar-chord and actual norm-integral relaxations. Their maxima are heuristic observations, not global optimizer certificates. The paper theorem supplies the genuine uniform negative gap bound.

For the precise unscaled objective

    g=E_fin+Gamma-(1-a|mu|),

an explicit m=7 family with six copies1 and

    q7=(1-h^4+2i h²)/(1+h^4)

has positive variance, a nonreal mean, and FULLpolar real part at least1+(337/125)h² for all0<h<=1/10. Its gap tends to0 as h->0. Combined with the reviewed global bound g<=-h/20<0, this proves **sup g=0, not attained**, even when positive variance and nonreal mean are required. This additional consequence is derived in `research/centered-round5/boundary-family/NOTE.md`; it is not a sharp normalized-gap result or a new Lean theorem.

## 7. Evidence and replay

The independent global audit reconstructs606 exact checks, including292 strictly negative Bernstein coefficients. It checks the whole Bernstein identity, not only signs at interpolation nodes. Independent cutoff35 review reconstructs1114 checks. Candidate residual replays reconstruct360 and399 checks by different polynomial methods. These counts overlap in mathematical content and are not counts of distinct theorems.

The complete paper sources, corrected cutoff35, audit reports, exact verifier scripts, source receipts and diagnostic reconstruction scripts are included. The historical nested archive's old OPEN status describes that earlier checkpoint and is superseded by this report; its numerical/exact input data remain useful.

Commands, from this directory:

    python3 -B verify.py

reconstructs all included current paper arithmetic/certificates and checks the stored Lean source/receipt/axiom evidence. It does not pretend those receipts are fresh compiler execution.

    python3 -B verify.py --rebuild

also freshly compiles and independently kernel-checks every bundled Lean module against the compatible project/cache.

    python3 -B verify.py --full-rational

also unpacks the historical archive into a temporary directory and reconstructs all13 original rational q families, full complex integrals and majorant radicals.

Paper and exact-example replay is self-contained and uses Python's standard library. Fresh Lean requires the documented original compatible project/cache and pinned config; set CENTERED_PROJECT and CENTERED_CONFIG to relocate them. The base project commit is a28fce8f970c3c4f50a9f6e194e0491775e75d4b, using Lean v4.34.0-rc1. Compiled outputs stay in the package's private stage. This is a research artifact, not a repository release: no old endgame was removed, no main theorem was replaced, and no commit or remote publication was performed.
