# Uniform C-near cutoff at m >= 45

## Result, scope, and independent verification

The proposed midpoint-chord improvement is sound. Under the original premises,
for every integer `m >= 45`,

    E + Gamma <= h/15 + (891/2000)v
              <= 1-au - (14/15)h - (9/2000)v
               < 1-au.                                           (T)

This covers every original `9/10 <= a < 1`, every actual complex mean, and every
allowed variance. The new argument below covers `45 <= m <= 170`; the existing
`m >= 170` theorem supplies the unbounded part. No variance restriction, real-mean
assumption, `s=1` assumption, first-origin condition, or extra feasibility premise
is used. This is a **paper proof with exact rational/algebra replay**, not a Lean
or kernel-checked proof. There is no grid, degree table, or quadrature certificate.

The only clarification to the proposed reasoning is notational: in the midpoint
tangent estimate, `rho=17/20` is a **root value**. The tangent point of the function
`sqrt(B)` is `B=rho^2=289/400`, not `B=17/20`. Equivalently, use directly

    sqrt(B) <= (B+rho^2)/(2rho),  B>=0, rho>0.

With this interpretation all proposed algebra, derivative signs, constants, and
interval domains check exactly; no correction to the cutoff is necessary.

Combining (T) with the proved near region `lambda<=1/3` and the proved thin strip
`v<=h/m^2`, the exact complement of these sufficient regions is

    integer 7 <= m <= 44,
    1/3 < lambda <= m/10,
    a = 1-lambda/m,
    v > h/m^2 = lambda/m^3,

**with all original pointwise and full-complex-polar feasibility premises retained.**
Equivalently its a-range is `9/10 <= a < 1-1/(3m)`. In particular
`lambda <= 22/5`. These are the remaining parameter restrictions, not a claim
that every such parameter tuple is feasible, or that the target fails anywhere
in the complement.

## 1. Exact original objects and the imported results

Let `m>=7` be an integer, `9/10<=a<1`, and let complex `q_1,...,q_m` satisfy

    |q_j| <= 1 for every j,
    | integral_0^1 product_(j=1)^m (a+(1-a^2)t q_j) dt | >= 1.       (1.1)

Define the actual statistics

    mu = mean(q_j) = x+iy,       u = |mu|,
    s = mean(|q_j|^2),          v = s-u^2,
    h = 1-a > 0,                lambda = mh,
    b = 1-2ax+a^2,              z = a mu,
    w = |1-z|,                  Gamma = v/((m-1)u^2).

Write

    B_(m,k)(z) = sum_(j=0)^k binom(m+1,j) z^j (1-z)^(m+1-j),
    H_(m,k)(z) = 1-B_(m,k)(z),

and retain exactly the original nonnegative square-root coefficients

    C_(m,k)(v)^2 = m^m v^k/[k^k (m-k)^(m-k)]   for 0<k<m,
    C_(m,m)(v)^2 = v^m.

The majorant under consideration is

    E = w^(m+1) + Gamma |B_(m,2)(z)| + Tail,
    Tail = sum_(k=3)^m C_(m,k)(v)|H_(m,k)(z)|/[binom(m,k)u^k].        (1.2)

In particular, it is not replaced by a bound on actual coefficients. All complex
H and B endpoints are retained up to explicitly justified triangle inequalities.

The source raw-polar lemmas, consequences of (1.1), give

    0 <= v,                u^2+v=s <= 1,
    0 <= b <= lambda/(3+lambda) < 1,
    v/u^2 <= lambda/3,      w^2+a^2 v <= b,
    x > a/2 > 0.                                                (1.3)

Thus `u>0`, so (1.2) and Gamma are defined. These are necessary consequences,
not replacements for the original feasibility premise. Since `h<=1/10`,

    lambda <= m/10,
    b <= m/(m+30).                                               (1.4)

From the actual-statistics constraint,

    u sqrt(v) <= 1/2,                                           (1.5)

because `u^2 v <= (1-v)v <= 1/4`. Also,

    1-au = h+a(1-u) >= h+(a/2)v >= h+(9/20)v.                    (1.6)

Indeed `v<=1-u^2=(1-u)(1+u)<=2(1-u)`. Neither deduction sets `s=1`.

The original endpoint power lemma states

    3^L binom(m+1,L) b^(m+1) <= (mh)^L.

At `L=4`, it implies

    b^(m+1) <= [24m^3/(81(m+1)(m-1)(m-2))]h^4 <= (4/9)h^4,

since the last comparison is equivalent to

    m^3-6m^2-3m+6
      = (m-7)^3+15(m-7)^2+60(m-7)+34 >= 0.

Consequently

    E0 := w^(m+1) <= (2/3)h^2 <= h/15.                          (1.7)

We import the following already-proved paper theorems, with exactly premise
(1.1), actual statistics, and the original majorant (1.2):

* `../math-middle/PROOF.md`, §§4–8: for every integer `m>=170`,
  `E+Gamma <= h/15+(891/2000)v`.
* The same source, §3: for `m>=7` and `lambda<=1/3`,
  `E+Gamma <= 1-au-(37/819)h`.
* `../math-bound/PROOF.md`, Theorem B: for `m>=7` and `v<=h/m^2`,
  `E+Gamma <= (821/840)h <= 1-au-(19/840)h`.

The first imported theorem is used only to extend the new finite-interval
argument to every `m>=45`. The latter two are used only when describing the
exact remaining domain. The original structural identity and raw-polar lemmas
are from these sources and `../../centered-verified/MATH_NOTE.md`. The complete
structural tail derivation needed for the new interval is recalled next.

## 2. A single structural integral for the original entire tail

Put

    D = m(m-1)(m-2),    p = (m-3)/2,
    beta_s(t) = 1-2axt+a^2 s t^2.

Then

    Tail <= (3/2)(m+1)a^4 u v^(3/2) sqrt(D)
                 integral_0^1 t^3 beta_s(t)^p dt.                (2.1)

Here is the uniform coefficient argument behind (2.1), without a degree table.
For `0<k<m`, the binomial distribution of parameters `(m,k/m)` has maximum mass
at k. If a probability distribution on nonnegative integers has mean k and
maximum mass P, then

    k+1 = sum_j (2k+1-j)p_j
        <= sum_(j=0)^(2k) (2k+1-j)p_j
        <= P(2k+1)(k+1).

Hence its maximum mass is at least `1/(2k+1)`. Applying this to the binomial
distribution gives

    C_(m,k)(v)^2 <= (2k+1)binom(m,k)v^k.

The top degree and zero variance follow directly. For
`A=|1-a mu t|` and `V=a sqrt(v)t`, factorial-weighted Cauchy–Schwarz gives

    sum_(k=3)^m C_(m,k)(v)(at)^k A^(m-k)
      <= sqrt(sum_(k=3)^m (2k+1)/[k(k-1)(k-2)])
           sqrt(sum_(k=3)^m k(k-1)(k-2)binom(m,k)V^(2k)A^(2m-2k))
      <= (3/2)sqrt(D)V^3(A^2+V^2)^p.

The first sum telescopes to
`9/4-2/(m-1)-1/(2m(m-1)) <= 9/4`, and the second sum equals
`D V^6(A^2+V^2)^(m-3)` by the binomial theorem. Since `A^2+V^2=beta_s(t)`,
the normalized finite-beta identity

    H_(m,k)(a mu)/[binom(m,k)mu^k]
      = (m+1)a^(k+1)mu integral_0^1 t^k(1-a mu t)^(m-k) dt

and the triangle inequality give (2.1). This cancels the powers of mu before
norms are taken, so no real-mean restriction has entered the argument.

## 3. The midpoint bound, with its a-dependence retained

For the remainder of the new proof assume `45<=m<=170`, and define

    r = m/(m+30),
    d = (18m+2040)/[85(m+30)],
    c = (10/9)a d.                                               (3.1)

In fact the midpoint construction below works for every real `m>=45`; only
later estimates on J and K use the upper endpoint 170. We have `0<d<=1/2`:
its numerator is positive, and

    1/2-d = (49m-1530)/[170(m+30)] > 0 for m>=45.

The actual quadratic satisfies

    beta_s(1/2)
      = (1+b)/2 - a^2(2-s)/4
      <= (1+r)/2 - a^2/4.                                      (3.2)

We claim

    sqrt(beta_s(1/2)) <= 1-(5/9)a d.                            (3.3)

First fix `a0=9/10`. The right side of (3.2) at `a0` is

    B0 = (319m+3570)/[400(m+30)]
       = 319/400-15/(m+30) > 0.

For `rho=17/20`, the elementary square inequality
`(sqrt(B0)-rho)^2>=0` gives

    sqrt(B0) <= (B0+rho^2)/(2rho) = 1-d/2
             = 1-(5/9)a0 d.                                  (3.4)

Thus no approximation of the radical is involved. To extend this to the
whole a-interval rather than freezing the a-factor, hold m fixed and let

    G(a) = [1-(5/9)a d]^2 - [(1+r)/2-a^2/4].

By (3.4), `G(a0)>=0`. Its exact derivative is

    G'(a) = a[1/2+(50/81)d^2]-(10/9)d
          >= 9/20+(5/9)d^2-(10/9)d
          >= 1/30 > 0.                                       (3.5)

For the last inequality, the quadratic in d has derivative
`(10/9)(d-1)<0` on `0<=d<=1/2`, and its value at `d=1/2` is `1/30`.
Therefore `G(a)>=0` for `a>=9/10`. The expression to be square-rooted on
the right is legitimate: `1-(5/9)a d >=13/18>0` for `a<=1,d<=1/2`.
Combining `G(a)>=0` with (3.2) proves (3.3).

The function `sqrt(beta_s(t))` is convex, since it is the Euclidean norm of

    (1-axt, a t sqrt(s-x^2)),

and `s>=u^2>=x^2`. Its chord from 0 to 1/2, together with (3.3), gives

    sqrt(beta_s(t)) <= 1-c t,       0<=t<=1/2.                  (3.6)

Here `0<c<=5/9`, so `1/c>1/2` and the chord is nonnegative on the entire
interval on which it will be integrated.

## 4. The first half of the integral and its exact a-cancellation

From (3.6), since `2p=m-3`,

    integral_0^(1/2) t^3 beta_s(t)^p dt
      <= integral_0^(1/c) t^3(1-c t)^(m-3) dt
       = 6/[c^4(m+1)D].                                      (4.1)

The last equality is the complete beta integral after `y=ct`; it also follows
by substituting `x=1-y`, expanding `(1-x)^3`, and using

    1/(m-2)-3/(m-1)+3/m-1/(m+1) = 6/[(m+1)D].

Multiplying (4.1) by the prefactor of (2.1) and using (1.5) gives a first-half
tail contribution at most `N(m)v`, where

    N(m) = 9(9/10)^4/[2 d^4 sqrt(D)].                           (4.2)

The a-factor cancels exactly:
`a^4/c^4=(9/10)^4/d^4`. Replacing `a^4` prematurely by 1 would lose this gain.
The argument uses no division by v, so it includes zero variance.

N is strictly decreasing for real `m>=45`. Indeed

    d'/d = -1500/[(m+30)(18m+2040)],

and hence

    (log N)' = 6000/[(m+30)(18m+2040)]
               -(1/2)[1/m+1/(m-1)+1/(m-2)]
             <= 6000/[(m+30)(18m+2040)]-3/(2m)
              = -3 Q_N/[2m(m+30)(18m+2040)] < 0,

where

    Q_N = 18m^2-1420m+61200
        = 18(m-40)^2+20m+32400 > 0.                            (4.3)

Two exact endpoint comparisons, squared only between positive quantities, give

    N(45) < 254/1000,
    N(50) < 247/1000.                                         (4.4)

Their rational replay is

    [9(9/10)^4/(2 d(n)^4)]^2/[n(n-1)(n-2)] < bound^2.

These two bases and (4.3), not an enumeration of degrees, prove the required
all-m estimates on the two continuous intervals.

## 5. The second half of the integral

At the midpoint, (3.2) gives `beta_s(1/2)<=B0`, and

    r-B0 = (81m-3570)/[400(m+30)] >= 0 for m>=45.                (5.1)

Precisely, this scalar endpoint comparison holds for real `m>=1190/27`; its
least integer is 45. At the other endpoint,

    beta_s(1)=1-2ax+a^2s <= b <= r.

The quadratic `beta_s` is convex because its second derivative is `2a^2s>=0`.
Consequently its chord between 1/2 and 1 gives

    beta_s(t) <= r,              1/2<=t<=1.                    (5.2)

Using `integral_(1/2)^1 t^3 dt=15/64<=1/4`, `a^4<=1`, (1.5), and
`sqrt(D)<=m^(3/2)` in the prefactor of (2.1), the second-half tail contribution
is at most `J(m)v`, where

    J(m) = (3/16)(1+1/m)m^(5/2) r^((m-3)/2).                   (5.3)

Here r depends on m; treating it as constant when differentiating would be
incorrect. We now bound J continuously, with that dependence retained.

### 5.1 Logarithmic convexity on 45<=m<=100

For `f=log J`, differentiation gives

    f' = 1/(m+1)+3/(2m)+(1/2)log r+15(m-3)/[m(m+30)],
    f'' = P/[2m^2(m+30)^2(m+1)^2],
    P = -5m^4+774m^3-3m^2+900m
      = m[(774-5m)m^2-3m+900].                                (5.4)

On `45<=m<=100`, `774-5m>=274` and `274m^2-3m>0`, so `P>0`.
Thus f is convex there. A convex function on a compact interval is at most
the larger of its two endpoint values. Since the exponential is increasing,
J is therefore at most its largest endpoint value on every subinterval of
`[45,100]`.

### 5.2 Monotonic increase for m>=100

For every `t>=0`,

    log(1+t) <= t-t^2/2+t^3/3.                                (5.5)

This is global, not a small-t Taylor assertion: the right side minus the left
vanishes at 0 and has derivative `t^3/(1+t)>=0`. Substitution of `t=30/m`
into (5.5), remembering `log r=-log(1+30/m)`, gives

    f' >= 1/(m+1)+3/(2m)+15(m-3)/[m(m+30)]
             -(1/2)(30/m-450/m^2+9000/m^3)
        = Q_J/[2m^3(m+1)(m+30)],

where

    Q_J = 5m^4-387m^3+4050m^2-265500m-270000.

At `m=100+t`, this polynomial is exactly

    Q_J = 126680000+8934500t+187950t^2+1613t^3+5t^4 > 0

for `t>=0`. Thus J is increasing for every `m>=100`. Only its interval up to
170 is needed here; this estimate is not an unbounded-degree smallness claim.

### 5.3 Endpoint bounds and interval conclusions

The exact squared formula is

    J(n)^2 = [(3/16)(n+1)/n]^2 n^5 [n/(n+30)]^(n-3).

The checker proves the rational comparisons

    J(45), J(50) < 29/500,
    J(100), J(170) < 23/250,
    29/500 < 23/250.                                          (5.6)

It follows from §5.1 that

    45<=m<=50:   J(m) <= max(J(45),J(50)) < 29/500.

For the other interval, apply §5.1 on `[50,100]` and §5.2 on `[100,170]`:

    50<=m<=170:  J(m) <= max(J(50),J(100),J(170)) < 23/250.     (5.7)

These are finitely many endpoints of proved continuous bounds, not degree-wise
certificates or samples supporting an unproved monotonicity assertion.

## 6. Gamma and every B_2 endpoint term

By `u>=x>a/2>=9/20`,

    Gamma <= 400v/[81(m-1)].                                  (6.1)

Also the exact complex formula

    B_(m,2)(z) = (1-z)^(m+1)+(m+1)z(1-z)^m
                 +m(m+1)z^2(1-z)^(m-1)/2

and `au<=1`, `w<=sqrt(b)<1` give

    |B_(m,2)(z)|
      <= w^(m-1)[w^2+(m+1)au w+m(m+1)a^2u^2/2]
      <= w^(m-1)[1+(m+1)+m(m+1)/2]
      <= m^2 b^((m-1)/2)
      <= m^2 b^((m-3)/2).                                     (6.2)

The penultimate inequality uses `m^2-3m-4>=0`, valid for `m>=7` by its shifted
form `(m-7)^2+11(m-7)+24>=0`. This also handles `b=0` since the exponents are
positive. Since `(400/81)m/(m-1)<6` for `m>=7`, (6.1)–(6.2) imply

    Gamma |B_(m,2)(z)| <= K(m)v,
    K(m) = 6m [m/(m+30)]^((m-3)/2).                           (6.3)

K decreases on the whole real interval `[45,170]`. The inequality

    log(1+t) >= 2t/(2+t),        t>=0,

follows by subtracting the right side: the difference vanishes at 0 and has
derivative `t^2/[(1+t)(2+t)^2]>=0`. Therefore

    (log K)' = 1/m+(1/2)log r+15(m-3)/[m(m+30)]
              <= 1/m-15/(m+15)+15(m-3)/[m(m+30)]
               = (m^2-225m-225)/[m(m+30)(m+15)] < 0.           (6.4)

Indeed the numerator equals `m(m-225)-225`, negative throughout this interval
because `m<=170<225`. The exact positive-square comparisons are

    K(45) < 6/1000,
    K(50) < 1/200,

using `K(n)^2=(6n)^2[n/(n+30)]^(n-3)`. Finally the coefficient in (6.1) decreases
with m, and exact rational comparisons give

    400/(81*44) < 113/1000,
    400/(81*49) < 101/1000.                                   (6.5)

## 7. Closing both continuous degree intervals

Combining (4.4), (5.7), and (6.3)–(6.5), for `45<=m<=50` we obtain

    Tail + Gamma(1+|B_(m,2)|)
      <= [254/1000+29/500+113/1000+6/1000]v
       = (431/1000)v.

For `50<=m<=170` the corresponding bound is

    Tail + Gamma(1+|B_(m,2)|)
      <= [247/1000+23/250+101/1000+1/200]v
       = (445/1000)v.

The displayed weak inequalities include `v=0`, despite strict inequalities
between some of the positive constants. Both coefficients are less than
`891/2000`. With (1.7), this proves (T) for every integer `45<=m<=170`.
The imported `m>=170` theorem has the same coefficient `891/2000`, so it proves
(T) for every remaining integer `m>=45`. Finally (1.6) yields exactly

    E+Gamma <= 1-au-(14/15)h-(9/2000)v < 1-au,

since `h>0`, even when `v=0`. This completes the uniform cutoff proof.

## 8. Exact remaining domain and what has not been proved

Taking the union of the proved regions

    {m>=45} OR {lambda<=1/3} OR {v<=h/m^2}

inside the original feasible domain leaves exactly

    7<=m<=44,  1/3<lambda<=m/10,  v>h/m^2,

with actual statistics and (1.1) still required. The boundary `m=45` is covered;
`lambda=1/3` is covered; and `v=h/m^2` is covered. The complement can equivalently
be written

    integer 7<=m<=44,
    9/10<=a<1-1/(3m),
    (1-a)/m^2 < v,

again intersected with the original feasible set. Necessary upper bounds such
as `v<=lambda/(3+lambda)` and `u^2+v<=1` remain consequences, not newly imposed
hypotheses. No proof of the original target on this complement is supplied here.
The bound is a sufficient majorant budget, not an equivalent statement of Sendov.

## 9. Exact checker, provenance, and limitations

Run

    PYTHONDONTWRITEBYTECODE=1 python3 /home/v-zhouziyu/work/sendov-paper-formalization-20260914-remaining-centered/research/centered-round2/math-cutoff45/verify.py

The replay uses only Python standard-library integers and `fractions.Fraction`.
It reconstructs formal multivariate rational expressions, differentiates their
polynomials, and checks identities by exact polynomial cross multiplication.
It checks every new midpoint identity, derivative numerator and shifted sign
polynomial above, the beta integral's rational identity, the two logarithmic
remainder derivatives, the rational endpoint squares, and the final budgets.
It performs no writes or local-module imports. The actual run passes **62 exact
rational/algebra checks**. The imported `math-middle/verify.py` was also run
read-only and passed its **48 exact rational checks**.

The checker does not mechanically prove quantified calculus or norm convexity,
and is not a kernel verifier. The sign, convexity, integral-comparison, and
interval-cover arguments are explicitly proved in the paper above. The original
raw-polar lemmas and imported theorems are source dependencies, not conclusions
of the new checker.

SHA-256 identities of the inspected read-only source proofs:

* `../math-middle/PROOF.md`:
  `41e381086f706a026b8d8bc223b179e4524bc542b1cc900bd8440b9824b05410`
* `../math-bound/PROOF.md`:
  `0f99ca32d0f4dc68a8ce2a1fa3c8784acd1e4a51accbf08fd5b4e50d0e4a291a`
* `../../centered-verified/MATH_NOTE.md`:
  `65d77a9a1ca9f668c8655a48b153438d109fe3409aafa1316711b8c2d274c66c`

All newly saved proof/checker artifacts are confined to `math-cutoff45`.
