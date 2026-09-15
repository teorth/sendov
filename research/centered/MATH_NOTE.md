# Centered structural route: mathematical ledger

## Status and exact target

The positive-variance uniform C-near inequality remains **OPEN**. No certified counterexample to the actual square-root majorant was found. Nothing here replaces the original premises by RawPolar when claiming a feasible q witness, or treats a numerical maximum as a proof.

For an m-element complex multiset q, use its actual mean μ, u=|μ|, actual second moment s, centered variance v=s-u², z=aμ, w=|1-z|, h=1-a, and Γ=v/((m-1)u²). The target is

`majorant_Efin + Γ < 1-a u`, for m≥7, .9≤a<1, pointwise |q_j|≤1 and FULLpolar `|∫₀¹∏(a+(1-a²)t q_j)dt|≥1`.

The coefficient is exactly PaperCenteredBound.C, including its separate k=m branch, not |e_k| and not an arbitrarily chosen variance upper bound. The finite complex B and H endpoints are retained.

## 1. Kernel-checked all-degree endpoint cancellation

`PaperCenteredTail.normalized_H_integral` proves, for **every** 0≤k≤m and nonzero complex μ,

\[
\frac{H_{m,k}(a\mu)}{\binom mk\mu^k}
=(m+1)a^{k+1}\mu\int_0^1t^k(1-a\mu t)^{m-k}\,dt.
\]

This is the all-degree version of the earlier top-degree cancellation. In particular, with a≥0,

\[
\frac{C_{m,k}(v)|H_{m,k}(a\mu)|}{\binom mk u^k}
\le (m+1)a^{k+1}u C_{m,k}(v)
\int_0^1t^k|1-a\mu t|^{m-k}\,dt. \tag{1}
\]

The exact norm identity, inequality, and arbitrary finite high-degree block sum are all compiled and kernel-checked. No real-mean or positivity interpretation of complex H occurs.

## 2. Kernel-checked zeroth endpoint and a genuinely proved C-near domain

Let `b=1-2a Re μ+a²`. Accepted rational polar gives

`3b≤m h(1-b)`, `0≤b≤1`, and pointwise data give `w²≤b`.

For any integer 0≤j≤m+1, a single term of `(b+(1-b))^(m+1)=1` yields the **uniform finite-order identity/inequality**

\[
3^j\binom{m+1}j b^{m+1}\le(mh)^j. \tag{2}
\]

`PaperCenteredEndpoint.endpoint_power_order` proves this general statement with `L=mh`; it is not a degree table. Taking j=2 gives

\[
b^{m+1}\le\frac{2m}{9(m+1)}h^2\le h^2/4,
\qquad w^{m+1}\le h/2.
\]

`norm_endpoint_half_of_rawPolar` is compiled for m≥7 and **all** 0<a<1, |μ|≤1, and RawPolar m a (Re μ). The explicit bounds -1≤Re μ≤1 follow from |μ|≤1 in actual applications.

`zero_variance_C_near` proves the **entire original square-root budget** when the actual variance is zero: Γ=0, all positive-degree C vanish, and Efin=w^(m+1)≤h/2<h≤1-au. This is a nonempty full-degree domain, not a conditional restatement of the requested error bound. It does not resolve positive variance.

For context, j=4 in (2) also gives the paper-level sharper zeroth-endpoint estimate `w^(m+1)≤(2/3)h²` for m≥7: after squaring it suffices that

`m³-6m²-3m+6 = (m-7)³+15(m-7)²+60(m-7)+34 ≥0`.

The generic lemma (2) is kernel-checked; this last j=4 corollary is recorded algebraically here, not exported as a Lean theorem.

## 3. Kernel-checked actual variance / second-endpoint coupling

It is incorrect to maximize w and v independently. Pointwise disk information and the actual mean give

\[
w^2+a^2v\le b. \tag{3}
\]

`PaperCenteredVarianceEndpoint.actual_variance_endpoint` proves (3) directly from q, its mean equation, and pointwise |q_j|≤1. Moreover, for every integer N≥1,

\[
N a^2v\,w^{2(N-1)}\le b^N. \tag{4}
\]

`actual_variance_endpoint_power` proves (4), again by one finite binomial term and on the actual centered multiset. This is useful for ΓB₂: treating b^(m/2) and m²v independently leaves a spurious degree-growth problem, while (4) absorbs one factor of degree against variance. Neither (3) nor (4) asserts that the full second endpoint plus tail fits h/2.

## 4. Paper-proved finite structural high-k estimate (NOT yet a Lean theorem)

There is a compact replacement for summing independently optimized square roots degree by degree. The derivation below is elementary and uniform; its final scalar budget remains open.

### 4.1 A binomial mode/first-moment inequality

For 1≤k<m set `p_j=binom(m,j)(k/m)^j(1-k/m)^(m-j)`. Then ∑p_j=1, ∑j p_j=k, and the ratio

`p_(j+1)/p_j = (m-j)k / ((j+1)(m-k))`

is ≥1 for j<k and ≤1 for j≥k. Thus p_k is a mode.

For ANY finitely supported probability sequence of mean k and maximum mass M, set N=2k. Then

\[
k=N-\mathbb E j=\sum_j(N-j)p_j
\le M\sum_{j=0}^{N-1}(N-j)=M k(2k+1).
\]

Here terms j≥N are nonpositive and may be discarded; missing support indices are filled with zero. Since k>0, `M≥1/(2k+1)`. Applying this to the above binomial mode gives

\[
C_{m,k}(v)^2\le(2k+1)\binom mk v^k. \tag{5}
\]

For k=m, (5) follows immediately from the exact top branch C²=v^m. One can replace 2k+1 by `2 min(k,m-k)+1` by reflecting the binomial distribution; that strengthening is not used below.

### 4.2 Factorial-weighted Cauchy–Schwarz

Let `(k)_K=k(k-1)...(k-K+1)` and K≥3. A telescoping factorial sum gives

\[
\sum_{k=K}^{\infty}\frac{2k+1}{(k)_K}
=S_K:=\frac{2}{(K-2)(K-2)!}+\frac{1}{(K-1)(K-1)!}.
\]

In particular S₃=9/4 and S₄=5/9. For nonnegative A,B, (5) and Cauchy–Schwarz imply

\[
\sum_{k=K}^m C_{m,k}(v)(at)^k A^{m-k}
\le\sqrt{S_K(m)_K}\,(a\sqrt v\,t)^K
(A^2+a^2vt^2)^{(m-K)/2}. \tag{6}
\]

The second squared sum is exactly the Kth binomial factorial moment:

`∑_(k≥K) (k)_K binom(m,k) B^(2k) A^(2(m-k)) = (m)_K B^(2K)(A²+B²)^(m-K)`.

All sums are finite except the explicitly evaluated positive constant S_K. There is no infinite-degree approximation to H, no per-degree certificate, and no discarded endpoint.

### 4.3 Apply actual variance before scalar relaxation

With A=|1-aμt|, the actual-moment identity is

\[
A^2+a^2vt^2=1-2a(\Re\mu)t+a^2st^2=:\beta_s(t).
\]

Combining (1) and (6) gives the finite high-k structural envelope

\[
\boxed{\quad
\sum_{k=K}^m\frac{C_{m,k}(v)|H_{m,k}(a\mu)|}{\binom mk u^k}
\le T_K:=(m+1)a^{K+1}u\,v^{K/2}\sqrt{S_K(m)_K}
\int_0^1t^K\beta_s(t)^{(m-K)/2}\,dt.
\quad} \tag{7}
\]

For K>m the original block is empty and should be handled separately, rather than interpreting negative factorials. For 3≤K≤m formula (7) handles complex means and v=0 directly. Since s≤1, one may replace β_s by β_1, but the actual u and v should remain coupled.

Two explicit sufficient scalar goals are now:

- `w^(m+1)+Γ|B₂|+T₃+Γ < 1-au`;
- `w^(m+1)+Γ|B₂|+[C₃|H₃|/(binom(m,3)u³)]+T₄ ≤ h/2`.

The former is numerically considerably looser than the available C-budget. The latter retains only one additional exact square-root coefficient before a structural high-k estimate. **Neither displayed scalar goal has been proved uniformly.** A grid passing these goals is not a replacement for that proof.

## 5. Endpoint cancellation failure in floating arithmetic

A naive downward binomial summation for H₃ can first accumulate terms of enormous modulus and then cancel them. The stored regression has m=512, a=.95 and a nonreal nearly constant family. Binary64 reports a fictitious tail `8.4921e116`; 300-digit arithmetic gives the actual Efin about `3.77788e-8`.

The search now uses `1-B_k` for low k and the complementary finite tail for high k. Finalists are recomputed at two higher precisions, and selected witnesses are rationalized on/in the disk and certified by exact polynomial integration and squared rational square-root enclosures. This numerical failure is not evidence that the square-root majorant is too strong.

## 6. Still missing

1. Formalize the binomial mode/first-moment bound (5) and factorial-weighted sum (7), if they are to be consumed by Lean.
2. Prove a scalar budget for (7), using the coupled actual moments and endpoint suppression. The scripts provide target diagnostics only.
3. No global optimality certificate or certified C-near counterexample is present.
4. Positive-variance C-near and the uniform Efin≤h/2 remain open; no premise was silently strengthened to declare otherwise.
