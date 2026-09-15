# Three continuous positive-variance budgets for the original centered majorant

## Status and exact result

This is a paper proof, with exact rational/algebraic replay in `verify.py`, **not a Lean proof**. It uses the frozen `research/centered-verified/MATH_NOTE.md` and the raw-polar consequences stated there/in the task. It does not replace the square-root coefficient bound by actual coefficients, impose a real mean, impose s=1, or add first-origin feasibility.

For the actual statistics and original majorant E in the frozen note, each of the following is sufficient:

**Theorem A (all allowed variances in a continuous near-a=1 regime).** If

    m >= 7, 0 < a < 1, lambda = m(1-a) <= 1/4,

then

    E + Gamma <= 1 - a u - (79/504)(1-a) < 1-a u.

Thus in particular the original problem is settled for every integer m>=7 and every `1-1/(4m) <= a < 1`, with **no extra restriction on the positive variance**. The a>=9/10 premise is automatic in this regime.

**Theorem B (a positive-variance strip over the entire original (m,a) domain).** If

    m >= 7, 9/10 <= a < 1, 0 <= v <= (1-a)/m^2,

then

    E + Gamma <= (821/840)(1-a)
              <= 1-a u - (19/840)(1-a) < 1-a u.

**Theorem C (all variances in an unbounded-lambda regime).** If

    m >= 7, 9/10 <= a < 1, lambda = m(1-a) >= 100,

then

    E + Gamma <= h/15 + (157/1000)v
              <= 1-au - (14/15)h - (293/1000)v < 1-au.

There is **no extra variance restriction** in Theorem C, and no upper cutoff on lambda. Its proof uses a stronger necessary endpoint consequence of the raw-polar integral, beyond the frozen rational b bound.

All three statements include v=0 but are not restricted to it. An exact full-complex-integral feasible family with v>0 satisfying A and B is checked by `verify.py`; it is only a nonvacuity illustration, not a premise or a per-degree certificate.

The entire unrestricted positive-variance domain remains open. Theorem A improves the parent's lambda<=4/39 approach by using the variance contribution to the right-hand budget, not just h=1-a. Theorem B is independent of a lambda cutoff, and Theorem C covers all variances at arbitrarily large lambda.

## 1. Setting and imported polar facts

Let q_1,...,q_m be complex, each |q_j|<=1, and suppose

    | integral_0^1 product_j (a+(1-a^2)t q_j) dt | >= 1.

Set

    mu = x+iy = mean(q_j), u=|mu|,
    s=mean(|q_j|^2), v=s-u^2,
    h=1-a, lambda=mh, b=1-2ax+a^2,
    z=a mu, w=|1-z|, Gamma=v/((m-1)u^2).

Always 0<=v, u^2+v=s<=1. Full polar implies the raw-polar facts from the frozen source:

    0 <= b <= alpha/(3+alpha) <= lambda/(3+lambda) < 1,
    alpha=m(1-a^2)/2 <= lambda,
    v/u^2 <= alpha/3 <= lambda/3,
    w^2+a^2 v <= b,
    3^L binom(m+1,L) b^(m+1) <= lambda^L.

In particular b<1 gives x>a/2>0, so u>0. Also

    x = 1 + (h^2-b)/(2a) >= 1-lambda/(6a).

These are the only feasibility consequences used. The proof below therefore works on the corresponding larger raw-polar moment domain too, provided the displayed actual-statistic inequalities are retained.

Define

    B_2(z) = (1-z)^(m+1) + (m+1)z(1-z)^m
             + m(m+1)z^2(1-z)^(m-1)/2.

Let `Tail` denote the sum of the original square-root-C terms for k=3,...,m, so

    E+Gamma = w^(m+1) + Gamma(1+|B_2(z)|) + Tail.

## 2. A uniform endpoint bound

Take L=4 in the imported endpoint power inequality. For m>=7,

    b^(m+1) <= [24m^3 / (81(m+1)(m-1)(m-2))] h^4
             <= (4/9)h^4.

The second inequality is equivalent to

    m^3-6m^2-3m+6 >= 0,

which follows from the identity, with n=m-7>=0,

    m^3-6m^2-3m+6 = n^3+15n^2+60n+34.

Consequently, throughout all three domains,

    w^(m+1) <= b^((m+1)/2) <= (2/3)h^2.       (2.1)

## 3. Structural tail, and two integral bounds

Write (m)_3=m(m-1)(m-2). The structural argument of the frozen note gives

    Tail <= T_3
      = (3/2)(m+1)a^4 u v^(3/2) sqrt((m)_3)
          integral_0^1 t^3 beta_s(t)^((m-3)/2) dt,          (3.1)

where

    beta_s(t)=1-2axt+a^2 s t^2.

For completeness, the argument does not change C. For 0<k<m, the binomial distribution with success probability k/m has its maximum mass at k. If a nonnegative-integer distribution of mean k has maximum mass P, then

    k+1 = sum_j (2k+1-j)p_j
        <= P sum_(j=0)^(2k) (2k+1-j) = P(2k+1)(k+1),

so P>=1/(2k+1). This gives the original bound

    C_{m,k}(v)^2 <= (2k+1) binom(m,k) v^k;

k=m follows directly. For A=|1-a mu t|, D=a sqrt(v)t, factorial-weighted Cauchy--Schwarz then bounds the sum of the normalized integral integrands by

    sqrt( sum_(k=3)^m (2k+1)/(k)_3 )
      sqrt( sum_(k=3)^m (k)_3 binom(m,k) D^(2k) A^(2m-2k) )
    <= (3/2) sqrt((m)_3) D^3 (A^2+D^2)^((m-3)/2).

Here the first sum is exactly

    9/4 - 2/(m-1) - 1/(2m(m-1)) <= 9/4,

by telescoping; the second sum is `(m)_3 D^6(A^2+D^2)^(m-3)` by the binomial theorem. Since `A^2+D^2=beta_s(t)`, integrating the frozen all-degree normalized-H identity proves (3.1).

To bound its integral, observe that beta_s(t) is the squared Euclidean norm of

    (1-t)(1,0) + t(1-ax, a sqrt(s-x^2)).

This is legitimate because s>=u^2>=x^2. The endpoint has squared norm `1-2ax+a^2s<=b`. Thus, with d=1-sqrt(b)>0,

    sqrt(beta_s(t)) <= 1-dt <= 1,  0<=t<=1.               (3.2)

First, extending the nonnegative chord integrand to 1/d gives

    integral_0^1 t^3 beta_s(t)^((m-3)/2) dt
      <= integral_0^(1/d) t^3(1-dt)^(m-3) dt
       = 6/[d^4(m+1)m(m-1)(m-2)].

The last equality is the elementary beta integral (four integrations by parts suffice). Hence

    Tail <= 9 a^4 u v^(3/2) / [d^4 sqrt(m(m-1)(m-2))].   (3.3)

Second, the bound beta_s(t)<=1 directly gives

    Tail <= (3/8)(m+1) sqrt(m(m-1)(m-2)) v^(3/2)
          <= (3/7) m^(5/2) v^(3/2),                     (3.4)

using a^4u<=1, m+1<=8m/7, and sqrt(m(m-1)(m-2))<=m^(3/2).

## 4. Proof of Theorem A

Assume lambda<=1/4 and m>=7. Then

    h<=1/28,  a>=27/28,  b<=1/13.

The variance estimate and actual constraint s<=1 imply

    v <= (lambda/3)u^2 <= (lambda/3)(1-v),
    hence v <= lambda/(3+lambda) <= 1/13.                (4.1)

**Important:** this does NOT imply u^2>=12/13; s need not equal 1. We instead obtain the required lower bound from x:

    u >= x >= 1-lambda/(6a) >= 155/162 >= 19/20,
    hence 1/u^2 <= 400/361 < 10/9.                       (4.2)

Put r=5/18. Since 1/13<=r^2, both sqrt(b) and sqrt(v) are <=r, and d>=13/18. Also, for m>=7,

    sqrt(m(m-1)(m-2)) >= (12/5)(m-1).                  (4.3)

Indeed the square difference after dividing by m-1 is

    m(m-2)-(144/25)(m-1)
      = (m-7)^2 + (156/25)(m-7) + 11/25 >=0.

Combining (3.3), (4.1), and (4.3), with a^4u<=1, gives a bound linear in the **actual v**:

    Tail <= A v/(m-1),
    A = 9(5/18)(18/13)^4(5/12) = 109350/28561.           (4.4)

Next, by the exact B_2 formula and au<=1,

    |B_2| <= r^(m-1)[r^2+(m+1)r+m(m+1)/2] = D_m.

Each of its three summands decreases with m>=7: successive ratios are at most

    r,  r(9/8)=5/16,  r(9/7)=5/14,

respectively. The single rational base evaluation gives

    D_7 = r^6(r^2+8r+28) < 1/50,

so |B_2|<=1/50 for all m>=7. This is a monotonic proof, not a per-degree table. Therefore (4.2) and (4.4) show

    Tail + Gamma(1+|B_2|)
      <= [109350/28561 + (51/50)(10/9)] v/(m-1)
      < 5v/(m-1),                                     (4.5)

where the coefficient inequality is rational. We may replace the strict comparison by <=, including v=0.

The key budget improvement is

    1-au = h+a(1-u) >= h+(a/2)v,                       (4.6)

because `v<=1-u^2=(1-u)(1+u)<=2(1-u)`.

For every m>=7,

    5/(m-1) <= 27/56 + 59/(24m).                       (4.7)

Multiplying by 168m(m-1)>0 reduces this to

    (m-7)(81m+59)>=0.

Since a>=27/28 and v<=lambda/3=mh/3, (4.7) implies

    5v/(m-1) <= av/2 + 59h/72.                        (4.8)

Finally, (2.1) and h<=1/28 give w^(m+1)<=h/42. Thus

    E+Gamma <= av/2 + (59/72+1/42)h
             = av/2 + (425/504)h
             <= 1-au - (79/504)h.

This proves Theorem A, uniformly in all m and every allowed actual variance.

## 5. Proof of Theorem B

Now allow the entire original range 9/10<=a<1, but assume v<=h/m^2. Since x>a/2, we have

    u^2 > a^2/4 >= 81/400.

The bounds w<1 and au<=1 give

    1+|B_2| <= (m^2+3m+6)/2 <= m^2  (m>=7).

The last inequality follows from

    m^2-3m-6 = (m-7)^2+11(m-7)+22 >=0.

Consequently

    Gamma(1+|B_2|)
      <= 400m^2 v/[81(m-1)]
      <= 6mv <= 6h/m <= 6h/7,                          (5.1)

because m/(m-1)<=7/6 and (400/81)(7/6)=1400/243<6.

By (3.4) and the assumed variance bound,

    Tail <= (3/7)h sqrt(h/m) <= 3h/56,                 (5.2)

since h/m<=1/70<1/64. Equation (2.1), with h<=1/10, yields w^(m+1)<=h/15. Adding gives

    E+Gamma <= (1/15+6/7+3/56)h = (821/840)h
             <= 1-au-(19/840)h.

This proves Theorem B. No m-by-m estimates occur.

## 6. A stronger raw-polar endpoint consequence

Write d0=1-a^2 (distinct from the chord slope d in Section 3). From the actual complex-integral feasibility, triangle inequality, and arithmetic--geometric mean applied to the nonnegative squared factor norms,

    1 <= integral_0^1 [a^2+2a d0 x t+d0^2 s t^2]^(m/2) dt
       <= integral_0^1 [a^2+2a d0 x t+d0^2 t^2]^(m/2) dt.

The square root of the final quadratic is the norm of

    (a,0) + d0 t (x,sqrt(1-x^2)),

so it is convex and bounded above by its endpoint chord `a+(R-a)t`, where

    R^2 = a^2+2a d0 x+d0^2 = 1+d0(1-b).

Here |x|<=1, and b<1 implies R>1>a. Exact integration of the chord gives

    1 <= [R^(m+1)-a^(m+1)]/[(m+1)(R-a)],

and therefore, on writing L=(m+1)h,

    R^(m+1) >= (m+1)(R-a)+a^(m+1) >= L.                (6.1)

For L>=1 and 0<b<1, the elementary inequalities log(1+t)<=t and log b<=-(1-b) imply

    log L <= (m+1)d0(1-b)/2,
    b^((m-3)/2) <= L^(-(m-3)/((m+1)d0)).               (6.2)

If b=0, the last bound is immediate without taking log b. Thus (6.2) is a rigorous necessary consequence of the original complex-integral premise. Unlike the rational b bound, it retains logarithmic growth in mh.

## 7. Proof of Theorem C

Assume lambda>=100 and 9/10<=a<1. Then h<=1/10 and m>=1000. Put

    p=(m-3)/2,  y=1/(10h)>=1,

so m=10 lambda y. Since `(m-3)/(m+1)>=9/10` and `d0<=2h`, equation (6.2), with L>=lambda, yields

    b^p <= lambda^(-(9/2)y).

For lambda>=100,

    log lambda >= 1-1/lambda >= 99/100,
    (9/2)(y-1)log lambda >= 3(y-1) >= 3log y.

(The elementary inequality log y<=y-1 also holds at y=1.) Consequently

    b^p <= lambda^(-9/2) y^(-3),
    m^(5/2) b^p <= 10^(5/2) lambda^(-2)y^(-1/2)
                 <= 320/lambda^2.                    (7.1)

The final constant follows from sqrt(10)<=16/5. This is a uniform large-lambda bound, not an asymptotic approximation.

### 7.1 The tail near t=0

Split the structural integral (3.1) at t=1/4. Since x>a/2 and s<=1,

    beta_s(t) <= 1-a^2 t(1-t).

On 0<=t<=1/4 this is at most `1-(3a^2/4)t`. Using `1-r<=exp(-r)` and extending a nonnegative integral to infinity,

    integral_0^(1/4) t^3 beta_s(t)^p dt
      <= integral_0^infinity t^3 exp(-3a^2(m-3)t/8) dt
       = 6[8/(3a^2(m-3))]^4.

The integral is elementary, by repeated integration by parts. After multiplying the prefactor in (3.1), this tail piece is at most

    (4096/9) [(m+1)sqrt(m(m-1)(m-2)) / (a^4(m-3)^4)]
       u v^(3/2)
    <= R0 v,

where we used u<=1, sqrt(v)<=1, and

    R0 = (4096/9)(1001/1000)(10/9)^4(1000/997)^4 / 31000
       < 1/40.                                       (7.2)

Indeed m+1<=1001m/1000, m-3>=997m/1000, sqrt(m(m-1)(m-2))<=m^(3/2), and m^(3/2)>=1000*31 since 31^2<=1000.

### 7.2 The remainder of the tail

Convexity of the quadratic beta_s itself shows that its maximum on [1/4,1] is at an endpoint. Its first endpoint satisfies

    beta_s(1/4) <= 1-3a^2/16 <= 1357/1600 <= 17/20,

and beta_s(1)<=b. Hence for 1/4<=t<=1,

    beta_s(t)^p <= (17/20)^p+b^p.

We can bound the integral of t^3 over this interval by 1. The prefactor in (3.1) is at most `3 m^(5/2) v^(3/2)`, using m+1<=2m. For every integer m>=1000,

    m^(5/2)(17/20)^((m-3)/2) <= 1/100.                (7.3)

Here is an exact uniform proof of (7.3), without a degree table. Majorize m^(5/2) by m^3. The sequence `m^3(17/20)^((m-3)/2)` decreases for all m>=1000, since the square of its consecutive ratio is bounded by

    (1001/1000)^6(17/20) < 1.

At m=1000 its value is at most `1000^3(17/20)^498<1/100`, an exact rational comparison. This proves (7.3) for every degree.

Combining (7.1) and (7.3), and using sqrt(v)<=1, the remaining tail piece is at most

    3[1/100+320/lambda^2]v <= (63/500)v.                (7.4)

Together (7.2) and (7.4) give

    Tail <= (1/40+63/500)v = (151/1000)v.

### 7.3 Gamma and the endpoints

As before u^2>=81/400 and m>=1000, so

    Gamma <= 400v/[81(m-1)] <= v/200.                 (7.5)

The exact B_2 formula gives

    |B_2| <= w^(m-1)[1+(m+1)+m(m+1)/2]
           <= m^2 b^((m-1)/2) <= m^2 b^p,

where `(m^2+3m+4)/2<=m^2` for m>=7 and 0<=b<=1. Thus, as in (5.1),

    Gamma|B_2| <= 6m b^p v
      <= [6*320/(lambda^2 m^(3/2))]v
      <= [6*320/(100^2*1000)]v < v/1000.              (7.6)

Equations (7.2), (7.4)--(7.6) sum to

    Tail+Gamma(1+|B_2|) <= (157/1000)v.

Equation (2.1) gives `w^(m+1)<=h/15`. Finally the same actual-variance right-budget inequality (4.6) gives

    1-au >= h+(a/2)v >= h+(9/20)v,

and hence

    E+Gamma <= h/15+(157/1000)v
             <= 1-au-(14/15)h-(293/1000)v.

This proves Theorem C with a strict positive margin even at v=0.

## 8. Independent verification of the parent's 4/39 proof

The derivation supplied by the parent is valid on its stated domain. With rho=2/11 and lambda<=4/39,

    b <= lambda/(3+lambda) <= 4/121 = rho^2.

The same chord/beta integral estimate (3.3), v<=mh/3, and

    49m(m-1)(m-2)>=30m^3

imply

    (Tail/h)^2 <= (49/10)h(11/9)^8
                <= (14/195)(11/9)^8 < 9/25.

The all-degree factorial inequality reduces to

    (m-7)(19m-14)>=0.

For the zeroth endpoint, `w^(m+1)/h <= (m/3)rho^(m-1)` follows from w^2<=b<=mh/3. For B_2, its triangle bound is <=`(m+1)^2rho^(m-1)`, so Gamma<7h/18 yields

    E_end/h <= rho^(m-1)[m/3+(7/18)(m+1)^2].

Both sequences decrease for m>=7 by their consecutive ratios. Their m=7 sum is

    (245/9)rho^6 = 15680/15944049 < 1/1000.

Adding the strict Gamma bound gives exactly

    E+Gamma < (3/5+1/1000+7/18)h = (8909/9000)h < (99/100)h.

Every displayed numerical comparison is replayed in `verify.py`.

## 9. Exact verification and boundaries of the result

Run:

    python3 research/centered-round2/math-bound/verify.py

The script uses only standard-library integers and `fractions.Fraction`. It verifies every numerical constant, the polynomial identities/nonnegative shifted coefficients used for all-m assertions, and an exact rational positive-variance feasible family. It does not use floating-point grids, optimization, numerical quadrature, or claim to verify quantified analytic lemmas by finite sampling.

Analytic inputs not mechanically formalized by this script are the imported raw-polar implications, the all-degree H integral identity, the mode/Cauchy--Schwarz structural argument, norm convexity, the elementary beta integral, and the order reasoning written above. The endpoint/H facts are reported kernel checked in the frozen source; the structural-tail argument and the scalar consumer here are paper proofs.

**Remaining task:** cover the intermediate band `1/4 < lambda < 100` when `v>h/m^2`. The three theorems above prove the original target everywhere else in the requested domain. No counterexample is asserted on this complement. Theorem A's simple constants depend on lambda<=1/4; Theorem C's large-degree estimates depend on lambda>=100. Closing their intervening band, or sharpening the large-lambda constants until the arguments overlap, is not done here.

The script also checks a second nonvacuity witness: m=1000, a=9/10, 998 copies of q=1 and the pair q=i,-i. Its variance is 999/250000, so it belongs to C but not A or B. Its original integrand is real positive, `(a+(1-a^2)t)^998(a^2+(1-a^2)^2 t^2)`. On t in [99/100,1] it is at least `(81/100)(27/25)^998`, whence the exact lower bound `K >= (81/10000)(27/25)^998 > 1`. No surrogate feasibility test is used.
