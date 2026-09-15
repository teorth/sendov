# Finite structural bounds retaining the actual mean and variance

## Status

The uniform positive-variance C-near assertion remains **open**. This note gives a finite high-degree envelope, not a proof that its scalar budget is uniformly positive. The all-degree endpoint cancellation and the endpoint/variance lemmas named below are Lean/kernel checked. The binomial-mode/factorial-weighted tail argument in §3 is a paper proof, not yet a Lean theorem.

## 1. Exact target and constraints

Let m≥7 be an integer, 9/10≤a<1, q=(q₁,…,qₘ)⊂ℂ, and require **each** |qⱼ|≤1. Put

- μ=m⁻¹Σqⱼ=x+iy, u=|μ|;
- rⱼ=qⱼ−μ, s=m⁻¹Σ|qⱼ|², v=m⁻¹Σ|rⱼ|²=s−u²;
- z=aμ, b₀=1−z, h=1−a;
- Bₘ,ₖ(z)=Σⱼ₌₀ᵏ binom(m+1,j)zʲ(1−z)ᵐ⁺¹⁻ʲ, Hₘ,ₖ=1−Bₘ,ₖ;
- Γ=v/((m−1)u²).

The feasibility constraint is the **complex integral**

    |K| ≥ 1,   K=∫₀¹ ∏ⱼ(a+(1−a²)tqⱼ) dt.

It is not replaced by ∫∏|…|≥1 in the actual-family diagnostics. The separate moment-disk scans deliberately use the weaker raw-polar condition and are labeled accordingly.

The actual square-root coefficient bound is

    Cₘ,ₖ(v)² = mᵐ vᵏ/[kᵏ(m−k)ᵐ⁻ᵏ]  (0<k<m),
    Cₘ,ₘ(v)² = vᵐ.

The investigated majorant is exactly

    E = |b₀|ᵐ⁺¹ + Γ|Bₘ,₂(z)|
        + Σₖ₌₃ᵐ Cₘ,ₖ(v)|Hₘ,ₖ(z)|/[binom(m,k)uᵏ].

The target is E+Γ<1−au. This is a sufficient budget, not an equivalent reformulation of Sendov. First-origin is **not** a feasibility premise for the search. A q-family violating this budget would disprove this sufficient target, not automatically provide a polynomial counterexample. Full polar and pointwise imply raw polar and x>a/2, hence μ≠0; no α upper bound is assumed.

## 2. All-degree endpoint cancellation — kernel checked

The finite beta identity implies, for every 0≤k≤m and μ≠0,

    Hₘ,ₖ(aμ)/[binom(m,k)μᵏ]
      = (m+1)aᵏ⁺¹ μ ∫₀¹ tᵏ(1−aμt)ᵐ⁻ᵏ dt.                 (2.1)

This cancels the inverse powers of μ **before taking norms**, at every degree, not only k=m. Therefore

    Cₘ,ₖ(v)|Hₘ,ₖ(aμ)|/[binom(m,k)uᵏ]
      ≤ (m+1)aᵏ⁺¹u Cₘ,ₖ(v)∫₀¹tᵏ|1−aμt|ᵐ⁻ᵏdt.         (2.2)

`PaperCenteredTail.normalized_H_integral`, `majorant_term_integral`, `majorant_term_le_integral`, and `majorant_block_le_integral` compile for arbitrary complex a and μ (with norms of a in the norm statements). The displayed real-a specialization is valid on the target domain.

This also supplies a stable numerical representation. A full descending complex binomial sum for small-k H can suffer catastrophic cancellation; evaluating small k as 1−B and large k from its finite tail, then replaying at higher precision, avoids the observed false alarm.

## 3. A single structural high-k envelope — paper proof

Write (j)ₖ=j(j−1)…(j−k+1). For every K≥3 and m≥K define

    S_K = 2/[(K−2)(K−2)!] + 1/[(K−1)(K−1)!].

In particular S₃=9/4 and S₄=5/9. Then the high-degree part satisfies

    Σₖ₌Kᵐ Cₘ,ₖ(v)|Hₘ,ₖ(aμ)|/[binom(m,k)uᵏ] ≤ T_K,

    T_K = (m+1)aᴷ⁺¹u vᴷᐟ² √[S_K (m)ᴷ]
          · ∫₀¹ tᴷ (1−2axt+a²s t²)^((m−K)/2) dt.        (3.1)

Here (m)ᴷ denotes the falling factorial, not m to the Kth power. Every statistic is actual. Since s≤1, replacing s by 1 on the right is a valid further upper bound.

### 3.1 Coefficient bound without Stirling or a per-degree table

For 0<k<m, let pⱼ=binom(m,j)(k/m)ʲ(1−k/m)ᵐ⁻ʲ. The adjacent ratio shows pₖ is a maximum, Σpⱼ=1, and Σj pⱼ=k.

For any distribution on nonnegative integers whose maximum mass is P and whose mean is k,

    k+1 = Σⱼ(2k+1−j)pⱼ
        ≤ Σⱼ₌₀²ᵏ(2k+1−j)pⱼ
        ≤ P(2k+1)(k+1).

Thus pₖ≥1/(2k+1), and consequently

    Cₘ,ₖ(v)² ≤ (2k+1)binom(m,k)vᵏ.                     (3.2)

The top degree follows directly from Cₘ,ₘ²=vᵐ. Zero variance is also immediate. This is a uniform argument; individual m,k evaluations are not premises.

### 3.2 Factorial-weighted Cauchy–Schwarz

Let A=|1−aμt| and D=a√v t, with 0≤t≤1. By (3.2),

    Σₖ₌Kᵐ Cₘ,ₖ(v)(at)ᵏ Aᵐ⁻ᵏ
      ≤ √[Σₖ₌Kᵐ (2k+1)/(k)ᴷ]
        √[Σₖ₌Kᵐ (k)ᴷ binom(m,k) D²ᵏ A²ᵐ⁻²ᵏ]
      ≤ √[S_K(m)ᴷ] Dᴷ(A²+D²)^((m−K)/2).

The second sum is exactly (m)ᴷD²ᴷ(A²+D²)ᵐ⁻ᴷ, by the finite binomial theorem. The first sum telescopes. Its exact finite value is

    S_K − 2/[(K−2)(m−1)ᴷ⁻²] − 1/[(K−1)(m)ᴷ⁻¹].

The superscripted factors in these denominators are again falling factorials. Finally,

    A²+D² = 1−2axt+a²(u²+v)t² = 1−2axt+a²s t²,

which is precisely where the **actual variance** matters. Integrating (2.2) gives (3.1). No complex H is interpreted as a probability.

### 3.3 Concrete scalar consumers, still open uniformly

Let

    E_end = |b₀|ᵐ⁺¹ + Γ|Bₘ,₂(z)|,
    Q₃ = Cₘ,₃(v)|Hₘ,₃(z)|/[binom(m,3)u³].

Then the following are sufficient:

- E_end+T₃+Γ<1−au; or
- E_end+Q₃+T₄≤h/2, followed by the existing Γ<7h/18 bound.

The first uses one integral envelope for the entire tail. The second retains one low coefficient and controls all k≥4 together. Neither condition has been proved uniformly here. The sampled maxima of the corresponding normalized envelopes are evidence only.

## 4. Uniform zeroth endpoint and a proved domain — kernel checked

Use the raw-polar rational bound β≤α/(3+α), where β=1−2ax+a² and α=m(1−a²)/2≤mh. Thus

    0≤β<1,   3β≤mh(1−β),   |b₀|²≤β.

A single term of (β+(1−β))ᵐ⁺¹=1 gives, for every 0≤L≤m+1,

    3ᴸ binom(m+1,L) βᵐ⁺¹ ≤ (mh)ᴸ.                     (4.1)

`PaperCenteredEndpoint.endpoint_power_order` is the division-free general statement. L=2 and binom(m+1,2)=m(m+1)/2 yield 4βᵐ⁺¹≤h². Hence

    |1−aμ|ᵐ⁺¹ ≤ h/2.

`norm_endpoint_half_of_rawPolar` proves this for **all 0<a<1**, m≥7, |μ|≤1, not just a≥9/10.

When the actual centered variance is zero, Γ=0 and all positive-degree C terms vanish. Therefore the **entire C-near budget is proved on v=0**:

    E+Γ = |1−aμ|ᵐ⁺¹ ≤ h/2 < h ≤ 1−a|μ|.

This is `zero_variance_C_near`. It does not prove the positive-variance domain.

As a paper corollary, L=4 in (4.1) gives |b₀|ᵐ⁺¹≤2h²/3 for m≥7. The needed coefficient inequality reduces to

    m³−6m²−3m+6 = (m−7)³+15(m−7)²+60(m−7)+34 ≥ 0.

The polynomial identity is exactly replayed in `structural_replay.py`; this sharper consumer is not separately formalized.

## 5. Actual variance also suppresses the second endpoint — kernel checked

It is invalid to maximize the variance and endpoint radius independently. Pointwise data give

    |1−aμ|² + a²v ≤ β.                                  (5.1)

For any integer N≥1, the first binomial term then gives

    N a²v |1−aμ|²ᴺ⁻² ≤ βᴺ.                             (5.2)

`PaperCenteredVarianceEndpoint.actual_variance_endpoint` proves (5.1) for the actual centered multiset; `actual_variance_endpoint_power` proves (5.2). These remove a misleading independent polynomial-in-m growth when treating ΓB₂. They remain building blocks, not a completed uniform estimate for E_end+T₃ or E_end+Q₃+T₄.

## 6. What is not proved

No global maximizer over all q is certified. No positive-variance interval in (m,a) is certified by the searches. Neither the uniform original majorant inequality nor the uniform scalar consumers in §3.3 are settled. No additional centroid identity, first-origin feasibility, α cutoff, real-mean restriction, or averaged-only replacement for pointwise was inserted to change that verdict.
