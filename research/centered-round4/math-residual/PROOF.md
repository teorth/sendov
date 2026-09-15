# Original C-near residual: complete continuous-band paper closure

## Result and status

Under the original pointwise complex and FULLpolar premises, for **every integer
`7 <= m <= 34`**, every `9/10 <= a < 1`, and every actual allowed mean and variance,

    E + Gamma <= 1 - a|mu| - (1/20)(1-a) < 1 - a|mu|.       (T)

In particular this closes the requested residual `lambda>1/3`, `v>h/m^2`;
neither restriction is needed by this proof. Combined with the reviewed
round3 cutoff at 35 and the frozen cutoff at 45, no original C-near paper
residual remains for `m>=7`.

The method is **one generic analytic degree-band criterion**, instantiated on
eight continuous degree intervals. Every interval contains multiple original
integer degrees. It uses eight endpoint-moment polynomial signs on the entire
continuous h interval and eight exact curved integrals; it is **not one theorem,
majorant evaluation, or data certificate per degree**. The criterion and all
comparisons in its degree parameter hold continuously. Only the original finite
complex product and the final coverage statement require m to be an integer.

This is a paper proof with exact rational replay, **not a Lean/kernel proof**.
Bernstein coefficients are finite exact polynomial sign certificates, not
numerical quadrature or sampling. If all such polynomial certificates are
forbidden (rather than just degree-wise certificates), that stronger requirement
is not claimed here.

## 1. Original setting, coefficients, and imported structural facts

Let `m>=7`, `9/10<=a<1`, `d=1-a^2`, and complex `q_1,...,q_m` satisfy

    |q_j| <= 1,
    |integral_0^1 product_j (a+d t q_j) dt| >= 1.           (FULLpolar)

Use the **actual** statistics and endpoints

    mu = mean(q_j) = x+i xi,     u=|mu|,
    s = mean(|q_j|^2),          v=s-u^2,
    h=1-a>0,                   lambda=mh,
    z=a mu,                    w=|1-z|,
    Gamma=v/((m-1)u^2).

The square-root majorant is unchanged:

    C_(m,k)(v)^2 = m^m v^k/[k^k (m-k)^(m-k)]  (0<k<m),
    C_(m,m)(v)^2 = v^m,
    B_(m,k)(z) = sum_(j=0)^k binom(m+1,j) z^j(1-z)^(m+1-j),
    H_(m,k)(z) = 1-B_(m,k)(z),
    Tail = sum_(k=3)^m C_(m,k)(v)|H_(m,k)(z)|/[binom(m,k)u^k],
    E+Gamma = w^(m+1)+Gamma(1+|B_(m,2)(z)|)+Tail.

The frozen sources establish, from exactly these premises,

    0<=v,  u^2+v=s<=1,  x>a/2>0,
    v/u^2 <= mh/3,
    w^(m+1) <= (2/3)h^2 <= h/15.                         (1.1)

Define

    S_m = 9/4 - 2/(m-1) - 1/[2m(m-1)],
    D_m = m(m-1)(m-2),
    beta_s(t)=1-2axt+a^2 s t^2.

Their factorial-weighted Cauchy--Schwarz argument, keeping its finite-m factor,
gives

    Tail <= sqrt(S_m)(m+1)a^4 u v^(3/2)sqrt(D_m)
              * integral_0^1 t^3 beta_s(t)^((m-3)/2) dt.   (1.2)

Specifically, the coefficient estimate is
`C_(m,k)^2 <= (2k+1)binom(m,k)v^k`, the exact weight sum is
`sum_(k=3)^m (2k+1)/[k(k-1)(k-2)] = S_m`, and the binomial factorial identity
sums the second squared factor to
`D_m (a^2 v t^2)^3 beta_s(t)^(m-3)`.
The normalized H integral cancels the complex powers of mu before norms are
taken. Thus (1.2) controls the original C and every complex H endpoint; it is
not a substitution of actual product coefficients.

Read-only dependencies:

* `research/centered-round2-verified/math-middle/PROOF.md`, §§1--2;
* `research/centered-round2-verified/math-cutoff45/PROOF.md`, §§1--2;
* `research/centered-round3/math-polar/PROOF.md`, §§2--4, for the moment method
  and the optional actual-s defect strengthening below.

Hashes of the exact inspected files, including round3's verifier, are emitted
by the new replay. The new proof does not need the numerical probes in round3.

## 2. A generic FULLpolar endpoint-moment criterion

For a real positive exponent M put

    Q_(a,x,s)(t)=a^2+2adxt+d^2 s t^2,
    N_M(a,x,s)=integral_0^1 Q_(a,x,s)(t)^(M/2) dt.

Triangle inequality followed by AM--GM of squared factor norms gives

    1 <= |integral product_j(a+dtq_j)|
      <= integral product_j|a+dtq_j|
      <= N_m(a,x,s).                                     (2.1)

This is only a necessary condition, derived from FULLpolar; no replacement
feasibility premise is made.

Fix an even integer `U=2n` and a rational `X` with `0<X<1`. Suppose

    J_(U,X)(h) := N_U(1-h,X,1) < 1,  0<h<=1/10.          (2.2)

If `0<m<=U` and an actual feasible family had `x<=X`, then `s<=1`, pointwise
monotonicity, and the probability-space Lp inequality would imply

    1 <= N_m(a,x,s)
      <= N_m(a,X,1)
      <= J_(U,X)(h)^(m/U) < 1,

a contradiction. Therefore **x>X for every m<=U**. This conclusion is uniform
in h and transfers a single endpoint polynomial to every degree in a band,
not merely to its integer endpoints.

One may retain the actual s-defect as well. The round3 derivative comparison
`N_s >= [d/(3a)]N_x` implies
`N_m(a,x-d(1-s)/(3a),1)>=1`. Applying exactly the same argument yields

    x > X + d(1-s)/(3a).                                 (2.3)

Only `x>X` is needed below. The auxiliary s=1 evaluation in (2.2) does not
assert that the actual s equals one; actual variance and complex mean are
retained in every statistic and budget.

### Exact continuous-h sign proof

Write `X=P/R` in lowest terms. With `a=1-h`, the integer bivariate polynomial is

    R Q_(1-h,X,1)(t)
      = R + (-2R+4Pt)h + (R-6Pt+4Rt^2)h^2
          +(2Pt-4Rt^2)h^3 + R t^2 h^4.                  (2.4)

Raise (2.4) to n and integrate each t monomial by exact rational division,
including the factor `R^(-n)`. If

    J_(U,X)(h)=sum_(j=0)^(4n) c_j h^j,

then `c_0=1`, `c_1=U(X-1)`, and

    (J_(U,X)(h)-1)/h = sum_(j=0)^(4n-1) c_(j+1)h^j.

At h=0 this denotes the polynomial extension. Set `r=10h`, `N=4n-1`. Its
Bernstein coefficients on `0<=r<=1` are

    b_k=sum_(j=0)^k c_(j+1)10^(-j) binom(k,j)/binom(N,j).

Consequently

    (J_(U,X)(h)-1)/h
      = sum_(k=0)^N b_k binom(N,k)r^k(1-r)^(N-k).

The Bernstein basis weights are nonnegative and sum to one. The exact replay
reconstructs all c and b and verifies **every b_k<0** for each of the eight
endpoint pairs used below. This proves (2.2) on the full continuous h interval.
It does not infer a sign from a mesh or from the value at h=1/10.

## 3. One generic curved-tail degree-band criterion

Let

    7<=L<=m<=U,
    1/sqrt(2)<=X<=19/20,
    p=(L-3)/2,

and suppose §2 has proved `x>X` uniformly on this degree band. Define

    q_X(y)=1-2Xy+y^2,
    I_(L,X)=integral_0^1 y^3 q_X(y)^p dy,
    T_(L,U,X)=sqrt(S_U)(U+1)sqrt(D_U) I_(L,X) X sqrt(1-X^2),
    G_(L,X)=1/[(L-1)X^2],
    W_X=2(1-X),
    B_(L,U,X)=U^2 W_X^((L-1)/2).

For any rational `tau>=T_(L,U,X)`, put

    K=tau+G_(L,X)(1+B_(L,U,X)),
    delta=X-1/15-(U/3)max(0,K-1/2).                      (3.1)

**Generic criterion.** If `delta>0`, then under the original premises,

    E+Gamma <= 1-au-delta h < 1-au.                       (3.2)

Here the integral and criterion make sense continuously in L,U,m. In the
replay we choose L odd so I is a rational polynomial integral and U even so
its endpoint moment is a rational polynomial in h.

### Proof of the criterion: retain curvature and cancel a before bounding

In (1.2) make the change of variables `y=at`. Exactly `a^4 t^3 dt=y^3 dy`, so

    Tail <= sqrt(S_m)(m+1)u v^(3/2)sqrt(D_m)
              * integral_0^a y^3(1-2xy+s y^2)^((m-3)/2)dy. (3.3)

The actual quadratic is nonnegative because

    1-2xy+s y^2=(1-xy)^2+(s-x^2)y^2,

where `s>=u^2>=x^2`. Since `s<=1` and `x>X`, it is at most q_X. Moreover

    q_X(y)=(y-X)^2+1-X^2>0,
    q_X(y)<=1  for 0<=y<=1,

using `X>=1/2`. Thus, for all real `L<=m<=U`,

    integral_0^a y^3(1-2xy+s y^2)^((m-3)/2)dy <= I_(L,X). (3.4)

This retains the quadratic curvature; there is no whole-interval norm chord.
The factors S_m, m+1, D_m are nonnegative and increasing for m>=7, so they
are bounded by their U values.

The stronger moment bound improves the previous generic `u sqrt(v)<=1/2`:

    u^2 v <= u^2(1-u^2) <= X^2(1-X^2),
    u sqrt(v) <= X sqrt(1-X^2).                           (3.5)

Indeed `u>=x>X>=1/sqrt(2)`, and `t(1-t)` is decreasing for `1/2<=t<=1`.
Combining (3.3)--(3.5) proves **Tail<=tau v**, including v=0 without division.

### All complex B2 endpoint terms

Since `u>=x>X`,

    Gamma <= G_(L,X) v.

Also

    w^2=1-2ax+a^2u^2 <= 1-2aX+a^2 <= W_X.                (3.6)

For the last inequality it is important not to assume that the quadratic
in a is increasing when X>9/10. It is convex, so its maximum on `[9/10,1]`
is at an endpoint. At a=1 the value is `2(1-X)`. At a=9/10 it is
`181/100-9X/5`, which is at most `2(1-X)` precisely when `X<=19/20`.
Every selected X meets this extra condition.

The complete three-term identity and triangle inequality give

    |B_(m,2)(z)|
      <= w^(m-1)[w^2+(m+1)au w+m(m+1)a^2u^2/2]
      <= m^2 w^(m-1)
      <= U^2 W_X^((L-1)/2)=B_(L,U,X).                   (3.7)

We used `au<=1`, `w<=1`, `m^2-3m-4>=0` for m>=7, and `0<W_X<1`.
No imaginary component of mu has been dropped or assumed zero.
Thus (1.1), (3.5), and (3.7) imply

    E+Gamma <= h/15+K v.                                 (3.8)

### Actual-mean budget consumption

The available budget is used as

    1-au=(1-u)+hu >= v/2+Xh,                              (3.9)

because `v<=1-u^2<=2(1-u)` and `u>=X`. The raw consequence in (1.1) gives
`v<=mh u^2/3<=Uh/3`. Therefore

    E+Gamma-(1-au)
      <= -(X-1/15)h+(K-1/2)v
      <= -[X-1/15-(U/3)max(0,K-1/2)]h
      = -delta h.

This proves the generic criterion. It holds throughout the original allowed
variance range and does not require the near or thin-strip theorems.

## 4. Eight continuous band applications and exact coverage

The chosen parameters are below. All X and tau entries are exact rationals;
the displayed decimals for delta are only readable summaries of rational
numbers stored in the exact replay output.

| Continuous degree band [L,U] | X | Moment exponent U/2 | Tail exponent (L-3)/2 | tau | delta (approx.) |
|---|---:|---:|---:|---:|---:|
| [7,8] | 473/500 | 4 | 2 | 535708/1000000 | 0.247440 |
| [9,10] | 921/1000 | 5 | 3 | 444574/1000000 | 0.517262 |
| [11,12] | 449/500 | 6 | 4 | 377455/1000000 | 0.800248 |
| [13,14] | 877/1000 | 7 | 5 | 327153/1000000 | 0.810333 |
| [15,18] | 421/500 | 9 | 6 | 506719/1000000 | 0.068891 |
| [19,22] | 203/250 | 11 | 8 | 361012/1000000 | 0.745333 |
| [23,28] | 31/40 | 14 | 10 | 407677/1000000 | 0.708333 |
| [27,34] | 149/200 | 17 | 12 | 438549/1000000 | 0.446048 |

For every row the checker proves, by exact rational comparisons,

    all moment Bernstein coefficients < 0,
    T_(L,U,X)^2 < tau^2,
    delta >= 1/20.

The second comparison is legitimate because both sides being square-rooted
are nonnegative. The integral I is reconstructed by expansion and rational
integration of `y^3(1-2Xy+y^2)^p`, not by quadrature. It computes

    T^2 = S_U (U+1)^2 D_U I^2 X^2(1-X^2)

exactly. No sampled original E or tail values enter these comparisons.

These intervals cover every requested integer m from 7 through 34. There are
real gaps between some intervals (for example `(8,9)`), but no integer gaps;
no claim about a finite product with noninteger degree is needed. Each scalar
bound applies to the full closed real interval displayed. This is eight
applications of a generic criterion, not a separate certificate for each of
28 degrees. The later bands cover four, six, or eight integer degrees at once.

By (3.2), each covered integer satisfies (T). The strict inequality in (T)
uses `h>0`, so it also covers zero variance and all near-boundary limits.

## 5. Replay, independent reconstruction, and remaining work

Run from any directory:

    python3 -B /home/v-zhouziyu/work/sendov-paper-formalization-20260914-remaining-centered/research/centered-round4/math-residual/verify.py
    python3 -B /home/v-zhouziyu/work/sendov-paper-formalization-20260914-remaining-centered/research/centered-round4/math-residual/audit.py

`verify.py` reconstructs all endpoint moment polynomials, all Bernstein signs,
all curved tail integrals, exact squared radical comparisons, and rational
budgets. Its only enumeration of individual integer degrees checks set
coverage, not an analytic inequality. It emits the full exact records under
this directory's `cache/`.

`audit.py` independently reconstructs moment coefficients by the closed
trinomial expansion of Q^n, converts to Bernstein form by a Horner recurrence,
and computes the tail integrals by a separate multinomial sum. It does not
import the first checker. It recomputes all signs, radical enclosures, margins,
and coverage; comparison to the first checker's records is additional evidence,
not its source of asserted bounds.

`explore.py` and `explore.json` are explicitly floating reconnaissance only and
have no role in either proof replay.

**Paper status:** the requested residual is closed; no remaining scalar consumer
on that domain is asserted. The result imports the frozen original-C structural
and raw-polar lemmas and uses quantified norm, Lp, and integral arguments proved
above. Exact Python is not a proof kernel. Lean formalization, independent
mathematical review of this new band argument, and any integration into the
parent paper/kernel are still separate work. No Lean files, immutable sources,
commits, or pushes were made; every new artifact is confined to `math-residual`.
