# Independent audit: cutoff 35 and the actual-s moment consequence

## Verdict

**The new moment theorem and the cutoff-35 paper argument are sound**, using the explicitly imported raw-polar facts and frozen cutoff-45 theorem. I found no blocking mathematical gap. There is a minor strict-sign error in intermediate displays when v=0, documented in `ISSUES.md`; replacing those intermediate strict inequalities by weak ones gives exactly the claimed final theorem, including v=0.

The conclusions are:

- For integer 7<=m<=44, under the original pointwise/FULLpolar premises and actual statistics,
  `x > 7/10 + (1-a^2)(1-s)/(3a)`.
- For integer 35<=m<=44,
  `E+Gamma <= 1-au - (107/250)(1-a) < 1-au`.
- With the frozen m>=45 result this gives the **paper** cutoff m>=35.
- This is **not a new Lean/kernel proof**, not global closure, and not a proof of the residual `7<=m<=34`, `1/3<lambda<=m/10`, `v>h/m^2` intersected with FULLpolar feasibility.

`audit.py` ran successfully with **1114 exact checks**, separately from the reviewed script's **112 checks**. Counts include finite diagnostic checks of imported polynomial identities; those enumerations are audit redundancy, not additional premises for the uniform paper proof. All reconstructed rational evidence is in `evidence.json`. Source and source-cache hashes were unchanged across execution.

## 1. Scope and independent reconstruction

Read the reviewed `centered-round3/math-polar/PROOF.md` and `verify.py`, the frozen `math-cutoff45`, `math-middle`, and relevant `math-bound` proofs, and `centered-verified/MATH_NOTE.md`. The earlier unbounded cutoff theorem is treated as the declared frozen dependency, not advertised as freshly kernel-verified here. I checked the structural coefficient argument directly rather than treating its name as sufficient.

The independent arithmetic deliberately differs from the reviewed checker:

1. Integrate the t-multinomial expansion of Q^22 **first**. If i linear and j quadratic t-terms are selected, its contribution is
   `choose(22,i) choose(22-i,j) (2x)^i a^(44-i-2j) d^(i+2j)/(i+2j+1)`.
   Substitute `a=1-h`, `d=h(2-h)`, then expand the two univariate binomials. This does not reuse the source's hard-coded A polynomial or its repeated bivariate multiplication.
2. Obtain Bernstein coefficients by reconstructing the forward-difference rows. Expand the **entire** Bernstein polynomial back into power coefficients, not merely its two endpoints.
3. Integrate J16 after shifting `r=y-7/10`, using `q0=r^2+51/100`, on `[-7/10,3/10]`. This differs from the source's direct power expansion in y.
4. Reconstruct the exact conjugate-pair moment by a positive multinomial sum. For the chord integral use `r=1-ct` and the four-term antiderivative, rather than expanding `(1-ct)^41`.
5. Bound the original square-root-C sum itself on the obstruction family by rational square-root intervals obtained using integer square roots. Thus its success here is certified independently of the paper's decimal comparison script.

Only after those independent constructions were established were their values compared with the source functions. The source checker was executed with its runtime `__file__` redirected into this owned directory, so its cache writes did not touch the reviewed directory. No source files or caches were edited, and no commit/push was performed.

## 2. FULLpolar, actual-s, and covariance path

AM-GM applies pointwise to the m **squared** factor norms. Their mean is exactly `Q=a^2+2adxt+d^2st^2`, so triangle inequality yields `1<=N_m(a,x,s)`. This uses the actual s; it does not pretend the complex product integral equals its norm-product upper bound for arbitrary data. Equality is legitimate for the specified even conjugate-pair family.

On the stated domain, a,d>0, x>0, s>=0, and Q>=a^2>0. Differentiation under the integral causes no singularity, including noninteger scalar exponents. For m>=2, `g=Q^(m/2-1)` is nondecreasing. With probability density 2t, the covariance identity gives `int t^2 g >= (2/3) int t g`. The derivatives have ratio

`N_s/N_x = d/(2a) * (int t^2 g)/(int t g) >= d/(3a)`.

The reverse bound d/(2a) follows from t^2<=t. N_x>0, so the implicit-boundary slope assertion is valid wherever that positive-x boundary exists.

For k=d/(3a), the path `(x-k(sigma-s),sigma)` has derivative `N_s-kN_x>=0`. Its x-coordinate is positive: the crude uniform lower bound `9/20-19/270=41/108` suffices. It also stays in the physical moment cone: its positive x decreases and sigma increases, hence `x_sigma^2<=x^2<=s<=sigma`. No unrealizable negative norm-square is inserted. Therefore

`N_m(a,x-k(1-s),1)>=N_m(a,x,s)>=1`.

The auxiliary evaluation at s=1 is a proved domination, **not a replacement of the original actual s**. The covariance sign and the direction of the shift are correct.

The endpoint norm chord is independently legitimate because `s>=x^2`. FULLpolar forces R>1, division by R-a is safe, and the chord integral is strictly increasing in its endpoint R. The exact identity `R^2=1+d(s-B)` checks algebraically. The r_* endpoint-root statements are necessary consequences, not assumed sufficient feasibility tests.

## 3. Bernstein conversion and degree comparison

The independent reconstruction recovers c0=1 and c1=-66/5. The quotient `(J(h)-1)/h` is a genuine degree-87 polynomial with a removable value at h=0. For r=10h, the source coefficient formula contains the correct factor `10^(-j)` and the correct degree 87 denominator `choose(87,j)`.

All 88 Bernstein coefficients are <=-23/50. The maximum is at k=87:

`-0.46137353360777850736612063036306013389084663462842...`.

The full inverse-basis identity passed exactly. Bernstein weights on r in [0,1] are nonnegative and sum to one, proving `J(h)<=1-(23/50)h` uniformly in h, without sampled interpolation or a degree table.

The exponent step uses Jensen/Lyapunov on the probability space [0,1]: for 0<m<=44,

`int Q^(m/2) <= (int Q^22)^(m/44)`.

This is valid even though Q can exceed 1; a pointwise exponent comparison would NOT have been valid here. The paper uses the correct integral comparison. Positivity of shifted x supplies a well-defined nonnegative Q. Since original a<1 means h>0, J(h)<1, and the contradiction is strict. At h=0 the certificate remains true but the contradiction is deliberately not asserted.

## 4. Original-C consumer and retained curvature

The coefficient comparison is for the **original square-root C**, not actual elementary-symmetric coefficients. The binomial distribution with success probability k/m has mode k and mean k. Dropping the negative part of the weighted sum `(2k+1-j)p_j` gives mode mass at least 1/(2k+1), exactly the required coefficient bound. Top degree k=m and v=0 are handled directly.

Factorial-weighted Cauchy-Schwarz has the correct sum

`sum_{k=3}^m (2k+1)/(k(k-1)(k-2)) = 9/4-2/(m-1)-1/(2m(m-1))`.

The second square sum is `D_m V^6(A^2+V^2)^(m-3)`. Here `A^2+V^2=1-2axt+a^2s t^2` uses `s=u^2+v`, retaining nonreal means. The normalized H integral cancels the complex powers of mu before taking norms; the outside factor is `(m+1)au`. Combined with V^3 this gives exactly the stated a^4 and u v^(3/2), with no missing binomial or u power. The independent checks also reconstruct H as a polynomial in complex z, so the identity is not merely checked for real endpoints.

After y=at, `a^4 t^3 dt=y^3 dy` exactly. The actual quadratic is nonnegative since s>=x^2. It is bounded above by `q0=1-(7/5)y+y^2`. On [0,1], `51/100<=q0<=1`. Thus the two exponent comparisons are safe:

- Increase the base to q0 at the same positive exponent.
- Decrease the exponent `(m-3)/2` to 16 because q0<=1 and m>=35.

Extending the integral from a to 1 adds a nonnegative integrand. Bounding the positive prefactor at m=44 is safe. This is a uniform scalar bound across the band, not an assertion that a product over a noninteger number of factors is defined.

The independently reconstructed integral is exactly

`J16 = 16692872210712253 / 366870355224609375000`.

The resulting tail/v constant is

`0.43288988379664390731097759858187689456284004693573... < 433/1000`.

The exact positive-square comparison passed. For v=0 use the weak bound `Tail<=433v/1000`.

## 5. Endpoint and actual-mean budget

u>=x>7/10 implies `Gamma/v <=100/(49*34)` when v>0, with a weak multiplied inequality also valid when v=0. The constants reconstruct as

- Gamma coefficient: `0.0600240096038415366... < 61/1000`;
- Gamma B2 coefficient: `0.0196698755612298295... < 20/1000`.

The estimate `w^2<=1-(7/5)a+a^2<=3/5` is correct: the final quadratic increases on [9/10,1]. Every term of B2 is retained before bounding its bracket by m^2. The difference from that bracket upper bound is `(m^2-3m-4)/2`, nonnegative for m>=7. Since (m-1)/2>=17 and 3/5<1, the endpoint exponent comparison is in the correct direction.

The three coefficients sum to 257/500. Crucially, the right budget is consumed as

`1-au=(1-u)+hu >= v/2+(7/10)h`,

not by the weaker `h+(9/20)v`. The imported `v/u^2<=mh/3` gives `v<=44h/3`. Exact arithmetic then gives

`1/15-7/10+(257/500-1/2)*44/3 = -107/250`.

No division by v is needed, so the final positive h-margin survives v=0. All denominator assumptions hold: m-1>0, a>0, u>0. The imported endpoint estimate was checked against its L=4 derivation and nonnegative shifted cubic.

## 6. Chord obstruction and exact original-C replay

For the specified m=44, a=9/10, q_± family, the independently reconstructed exact FULLpolar integral is

`1.0014100154856307207512198857459085176020782314898... >1`.

Pointwise norms are exactly one, and actual s, u, v and the residual-strip conditions are correct. Both chord consumers genuinely fail on the original feasible family:

- finite chord tail lower bound: `0.9511606591185526772...`;
- extended chord tail lower bound: `0.9544132796217494090...`;
- entire target budget: `907/2500=0.3628`.

The radical lower and upper bounds have the appropriate signs; in particular c is positive and c<27/100. The finite lower integrand remains nonnegative on [0,1].

This is not a target counterexample. Independent **exact rational interval** evaluation of the original C gives tail upper endpoint approximately `0.02777305439209418978`, and total/target upper endpoint approximately `0.1403296125867108900<1`. Exact interval endpoints, not only these decimal displays, are saved in `evidence.json`.

## 7. Most useful next uniform extension: keep the s-defect and quadratic

Let e=1-s and k=d/(3a). The new moment theorem immediately supplies `c_e=7/10+k e < x`. Instead of throwing this away in §5, retain

`1-2xy+s y^2 <= q_e(y)=1-2c_e y+(1-e)y^2`

and integrate `y^3 q_e(y)^((m-3)/2)` on [0,a]. Its nonnegativity is guaranteed on feasible data: `c_e<x<=sqrt(s)`. Retain the finite S_m, degree exponent, and `u sqrt(v)=sqrt((s-v)v)` until the final scalar comparison. A useful simpler uniform refinement is `u sqrt(v)<=s/2`, not merely 1/2.

The right budget also retains the same defect:

`1-au >= (v+e)/2 + h(7/10+k e)`.

As an immediate paper corollary on the already proved band 35<=m<=44, even without integrating the improved q_e, the s/2 prefactor yields

`E+Gamma <= 1-au -(107/250)h - e[1/2+h k+(433/1000)v]`.

Indeed `Tail<=(433/1000)s v`, while the two endpoint coefficients remain 81/1000 in total; subtract the displayed defect-aware budget and use v<=44h/3 as before. This strengthens, rather than replaces, the established theorem.

For a new lower-degree band, use a **single upper-degree moment polynomial** for that band (e.g. exponent corresponding to its largest degree), derive its stronger uniform mean threshold, and bound the still-quadratic tail with continuous exponent/prefactor control. This is more useful than further refining the whole-interval norm chord, which the exact feasible obstruction rules out as a global consumer. A lower cutoff is a research target here, **not a result of this audit**; do not discard degree dependence at unrelated extreme endpoints without checking the resulting budget. If the whole structural tail remains too loose, retain original low C terms and apply the factorial-weighted envelope only above them.

## Artifacts / replay

All artifacts are under `research/centered-round4/review35/`:

- `AUDIT.md`: this independent mathematical audit;
- `ISSUES.md`: nonblocking zero-variance strict-sign issue and exact witness;
- `audit.py`: standard-library independent reconstructions and interval checks;
- `evidence.json`: exact independent coefficients, constants, witness intervals, checks, source/cache hashes;
- `source-replay.json`: captured source checker summary;
- `cache/exact-verification.json`: source checker output redirected to this owned directory.

Replay with:

`PYTHONDONTWRITEBYTECODE=1 python3 /home/v-zhouziyu/work/sendov-paper-formalization-20260914-remaining-centered/research/centered-round4/review35/audit.py`
