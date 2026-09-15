# Independent audit of the proposed global original-C-near paper closure

## Verdict

**ACCEPT as a paper proof using the declared frozen dependencies. No blocking mathematical gap was found in the new eight-band argument.** This is not a Lean/kernel closure and not a certificate-free formula.

The new argument proves, for every integer `7<=m<=34`, every `9/10<=a<1`, and the original pointwise/FULLpolar feasible complex family with its actual statistics,

`E+Gamma <= 1-a|mu|-(1-a)/20 < 1-a|mu|`.

The reviewed cutoff-35 result gives the stronger `107(1-a)/250` margin for `35<=m<=44` (with the already documented weak-sign correction at v=0). The frozen cutoff-45 theorem gives at least `14(1-a)/15` for `m>=45`. Therefore their union proves the **same common `(1-a)/20` margin for every integer m>=7**, under the same original premises. The auxiliary near/thin-strip theorems are not needed for this union.

Independent execution passed **606 exact checks**, reconstructing **292 strictly negative Bernstein coefficients** across eight bands. Source replays passed **360**, **399**, **62**, and **48** checks respectively (new verifier, new audit, frozen cutoff45 verifier, frozen middle verifier). All 15 inspected source/provenance file hashes were unchanged. Source checkers that write caches were executed with their runtime `__file__` redirected into this owned directory; reviewed sources/caches were not written.

The conclusion is conditional on the explicitly imported raw-polar lemmas and the frozen unbounded cutoff, as any modular paper proof is. Those imports were read and their relevant uses reconstructed; this audit does not claim a new kernel verification of them or of the global theorem.

## 1. Original coefficients and the normalized complex H identity

The new proof uses exactly the original branches

- `C_(m,k)^2=m^m v^k/[k^k(m-k)^(m-k)]` for `0<k<m`;
- `C_(m,m)^2=v^m`.

The top branch is not obtained by evaluating an ambiguous `0^0`, and it is not replaced by actual elementary-symmetric coefficients. For interior k, the binomial mass at k with success probability k/m is the mode. The weighted-mean argument gives that mass at least `1/(2k+1)`, so `C^2 <= (2k+1) choose(m,k) v^k`. Top degree and v=0 follow directly.

The load-bearing normalization is correct for a general complex endpoint. Differentiating the finite binomial prefix telescopes to

`H'_(m,k)(z)=(m+1)choose(m,k) z^k(1-z)^(m-k)`, with `H(0)=0`.

Consequently

`H_(m,k)(a mu)/[choose(m,k)mu^k] = (m+1)a^(k+1)mu integral_0^1 t^k(1-a mu t)^(m-k)dt`.

Taking norms leaves the factor `(m+1)au` outside the sum. In factorial-weighted Cauchy--Schwarz the second square sum is

`m(m-1)(m-2)(a^2 v t^2)^3 (|1-a mu t|^2+a^2 v t^2)^(m-3)`.

Its base is exactly `1-2axt+a^2s t^2`, because **actual** `s=u^2+v`; nonreal mu is allowed. The first square sum telescopes to the finite constant `S_m=9/4-2/(m-1)-1/[2m(m-1)]`. This gives exactly the asserted prefactor `sqrt(S_m)(m+1)a^4 u v^(3/2)sqrt(D_m)`.

For redundant diagnostics, the independent script reconstructs the full H polynomial over the rational coefficient ring for selected m=7,16,34 and every corresponding tail k, including k=m; a polynomial identity applies at arbitrary complex z. It also checks the coefficient and factorial identities there. These selected diagnostics are **not** the all-degree proof or a degree-certificate table; the general argument above supplies that proof.

## 2. Actual moments, FULLpolar, and Lyapunov

Pointwise AM--GM is applied to the squared norms of the original factors. Their mean is precisely

`Q(t)=a^2+2a(1-a^2)xt+(1-a^2)^2 s t^2`.

Thus triangle inequality and AM--GM give `1<=N_m(a,x,s)`. This is a necessary consequence, not an assertion that norm relaxation is equivalent to FULLpolar. For arbitrary complex families, equality with the original integral is neither needed nor claimed.

If x<=X, `s<=1` yields `Q_(a,x,s)<=Q_(a,X,1)` pointwise. All relevant quadratics are nonnegative; the auxiliary quadratic is strictly positive. On the probability space [0,1], put `F=Q_(a,X,1)^(U/2)` and `r=m/U` in `(0,1]`. Concavity/Jensen gives

`integral F^r <= (integral F)^r`.

This proves exactly `N_m(a,X,1)<=J_(U,X)(h)^(m/U)`. **Pointwise power comparison would be invalid when Q crosses 1; the proof correctly uses the integral inequality instead.** Once J<1, the contradiction proves x>X for every m<=U to which the original family is applicable. The scalar Lyapunov comparison itself holds for real 0<m<=U.

The optional s-defect statement is also sound on the original m>=7 domain: for m>=2 and positive x, `g=Q^(m/2-1)` is increasing, and covariance under density 2t gives `integral t^2g >= (2/3) integral tg`. Therefore `N_s >= d N_x/(3a)`. On the path `(x-d(sigma-s)/(3a),sigma)` the moment is nondecreasing. The path stays positive and in the moment cone: x decreases but remains at least the positive crude bound `9/20-19/270`, while sigma increases. Applying the endpoint argument at sigma=1 proves the stated improvement. It is unused in the new tail/budget proof. Do not extend this covariance justification to m<2 without an additional argument.

Neither the auxiliary s=1 bound nor the scalar moment criterion resets the actual variance or drops Im(mu).

## 3. Continuous h certificate: independent reconstruction

The candidate's expansion of `R Q_(1-h,P/R,1)` has the correct coefficients at all five h powers. Its degree after raising to n is at most 4n, and integration does not increase this degree. The quotient `(J-1)/h` has degree at most 4n-1 and a removable value at h=0.

The independent script does not import either candidate reconstruction. It evaluates the exact t-polynomial integral at 4n+1 rational h nodes, then reconstructs the entire polynomial using Newton forward differences and the proved degree bound. This is **exact polynomial interpolation**, not a claim that negative mesh values imply a continuous sign. It then converts the quotient to Bernstein form and expands the entire Bernstein expression back to powers, checking equality of every coefficient. Only after the independent calculations are finished are the source coefficients compared.

For r=10h, the candidate's coefficient conversion is correct:

`b_k = sum_(j<=k) c_(j+1)10^(-j) choose(k,j)/choose(4n-1,j)`.

All 292 coefficients are strictly negative. Bernstein weights are nonnegative and sum to one on the full closed interval r in [0,1]. Thus `(J(h)-1)/h<0` on the polynomial extension interval, and J(h)<1 for every **positive** h<=1/10. In particular a=9/10 is included.

The least separated Bernstein maximum is in [9,10], approximately `-0.0001997801304984241`; it is nonetheless a strictly negative exact rational, not a floating sign. The full rational arrays are in `evidence.json`. At h=0, J=1, so the strict contradiction must not be asserted there. The candidate correctly assumes a<1 and hence h>0. Arbitrarily small positive h is covered without a mesh-size or roundoff limitation.

## 4. Curved tail, endpoint signs, and budget

The change of variables y=at cancels exactly: `a^4 t^3 dt=y^3 dy`. No a-factor is discarded before this cancellation.

The actual quadratic is nonnegative since `s>=u^2>=x^2`. It is bounded by `q_X(y)=1-2Xy+y^2`, which is strictly positive and at most one for y in [0,1] and the selected X. Increasing the base at fixed positive exponent and then decreasing the exponent to `(L-3)/2` are therefore both safe. Extending the integral from a to 1 adds a nonnegative integrand.

The prefactors are increasing continuously on m>=7. In particular

`S'_m=2/(m-1)^2+(2m-1)/[2m^2(m-1)^2]>0`,

and `D'_m=3(m-1)^2-1>0`. Their U values safely bound the whole real interval. The stronger actual-moment gain is correct because u>=x>X>=1/sqrt(2): the function t(1-t) decreases for t>=1/2, yielding `u sqrt(v)<=X sqrt(1-X^2)`.

The independent tail integral uses `z=y-X`, so the integrand becomes `(z+X)^3(z^2+1-X^2)^p`. Expanding this centered form and taking its antiderivative between -X and 1-X gives the same exact rational I as the candidate, by a different construction. Every squared radical comparison has positive sides. The resulting statement is `Tail<=tau v`, **weakly**, including v=0.

The endpoint bound deserves the attention the paper gives it. The quadratic `1-2aX+a^2` is not necessarily increasing in a. Its maximum on [9/10,1] is at an endpoint. Its a=9/10 value is bounded by its a=1 value precisely under `X<=19/20`, which all rows satisfy. Thus `w^2<=W_X=2(1-X)<1` is valid. All three complex B2 terms remain present before the triangle inequality. The bracket upper bound by m^2 follows from `m^2-3m-4>=0`; the exponent comparison to L then has the correct direction since W_X<1.

The original endpoint-power estimate gives `w^(m+1)<=2h^2/3<=h/15`. Its L=4 denominator and shifted cubic agree with the frozen derivation. Combining it with the tail and Gamma bounds yields `E+Gamma<=h/15+K v`.

Crucially the available budget uses the actual mean:

`1-au=(1-u)+hu >= v/2+Xh`.

The raw-polar consequence supplies `v<=mh u^2/3<=Uh/3`. For K<1/2 the excess term is nonpositive; it must be discarded rather than multiplied by the upper bound for v. The candidate's `max(0,K-1/2)` correctly handles both signs. Thus the final delta formula is correct.

The minimum reconstructed delta occurs in [15,18] and equals exactly

`250406772427238299 / 3634825195312500000`

(approximately `0.06889100822514516`), larger than 1/20. No division by v appears. At v=0 all positive-degree C terms and Gamma vanish; the endpoint h-bound still leaves the final positive h-margin. The new proof does **not** repeat cutoff35's intermediate `0<0` error.

## 5. Nonreal, positive-variance, actual-s diagnostic

The independent exact replay also checks a genuinely nonreal feasible family in the old residual, not just an s=1 or real-mean relaxation:

- m=7, a=9/10;
- three copies of `999/1000`;
- four copies of `959/1000+(7/25)i`;
- actual `mu=6833/7000+(4/25)i`;
- actual `s=6986327/7000000<1`, `v=24/1225>h/m^2`;
- lambda=7/10>1/3.

Every pointwise norm is at most one. Exact Gaussian-rational multiplication/integration proves the **original complex FULLpolar squared norm exceeds one**, not merely its norm-integral relaxation. The centered-variance identity is checked from the individual q values. Integer-square-root rational enclosures then certify the original C majorant itself below `1-a|mu|-h/20` on this family, including its top branch and complex H endpoints. Exact intervals are in `evidence.json`. This is a nonvacuity/normalization diagnostic, not a premise or a proof by testing families.

A separate exact q_j=1, m=7, a=9/10 feasible witness checks zero variance. Neither example replaces the quantified band proof.

## 6. Eight-band coverage and the global union

The bands are `[7,8]`, `[9,10]`, `[11,12]`, `[13,14]`, `[15,18]`, `[19,22]`, `[23,28]`, and `[27,34]`. Their integer union is exactly 7 through 34. They overlap at 27,28. They do not cover every real between 7 and 34: for example (8,9) is absent. This causes no gap for the original integer degree, and the candidate expressly acknowledges it.

Each scalar estimate is continuous across its own real interval, with one upper-degree moment and one lower-degree curved integral. The final union is:

1. new eight-band theorem: integer 7..34, margin h/20;
2. reviewed round3 theorem: integer 35..44, margin 107h/250;
3. frozen cutoff45: integer m>=45, margin at least 14h/15, itself extended past 170 by the frozen unbounded theorem.

All premises and original objects match. There is no boundary gap at 34/35, 44/45, or the imported 170 cutoff. The older cutoff35 intermediate strict inequalities should be read with the correction already documented by review35; its final h-margin and union are unaffected.

## 7. What kind of result this is

This is a **finite-band, exact polynomial certificate method with a generic continuous analytic criterion**. It is not a separate original-majorant check for each of 28 degrees. The first four bands do happen to contain only two integer degrees apiece; this makes the construction comparatively fine-grained, not certificate-free. The later bands genuinely cover several degrees with shared estimates. All-degree validity comes from Lyapunov, exponent/prefactor monotonicity, Bernstein positivity, and the final integer union—not from passing a list of original-degree tests.

If the user's exclusion means no per-degree testing/tables, this method meets that literal restriction. If it means no finite band-dependent certificates or no case-by-case constants at all, it does **not** meet that stronger methodological requirement. An unconditional claim of a certificate-free formula would be false.

No new Lean theorem, analytic formalization, kernel receipt, or global Sendov theorem is supplied here. The statement concerns the original sufficient C-near majorant budget. The exact FULLpolar chord obstruction from earlier rounds concerns a different upper-bound consumer and does not contradict this curvature-preserving proof.

## Artifacts and replay

All new artifacts are confined to `research/centered-round5/review-global/`:

- `AUDIT.md`, `ISSUES.md`;
- `independent_checks.py` (stdlib only);
- `evidence.json` (independent exact arrays, intervals, checks and provenance hashes);
- `source-replay.json` (captured source replay outputs);
- `cache/exact-verification.json`, `cache/independent-audit.json` (source outputs redirected here).

Replay:

`python3 -B /home/v-zhouziyu/work/sendov-paper-formalization-20260914-remaining-centered/research/centered-round5/review-global/independent_checks.py`

No dependency changes, outside-owned edits, commit, or push were made.
