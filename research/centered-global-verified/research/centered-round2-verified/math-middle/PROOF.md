# Near extension to lambda <= 1/3 and an analytic uniform cutoff m >= 170

## Result and status

Under exactly the original premises, the target

    E + Gamma < 1 - a |mu|

holds on each of the following domains:

1. **Near extension:** `m >= 7`, `lambda <= 1/3`, all allowed variances.
2. **Uniform degree cutoff:** `m >= 170`, `9/10 <= a < 1`, all lambda and all allowed variances.
3. The already-proved strip `v <= h/m^2`, throughout the original domain.

The first result extends the source's near cutoff `1/4`. The second is uniform in a and lambda, not just the requested middle band; in particular it replaces the need for a separate large-lambda case. There are no degree tables, numerical quadrature certificates, random searches, restrictions to a real mean, or alterations of the original coefficient majorant.

Quantitative conclusions are

    lambda <= 1/3:
        E + Gamma <= 1-au - (37/819)h;

    m >= 170:
        E + Gamma <= h/15 + (891/2000)v
                  <= 1-au - (14/15)h - (9/2000)v.

Here and throughout `h=1-a>0`, `lambda=mh`, and `u=|mu|`.

**Exact outstanding domain after combining these results with the source strip:**

    integer 7 <= m <= 169,
    1/3 < lambda <= m/10,
    a = 1-lambda/m,
    v > h/m^2,

with all original pointwise complex and full-polar feasibility premises retained. In particular `lambda <= 169/10` on this complement. This is an analytic uniform finite-m cutoff, not a proof of the entire complement and not a counterexample there.

This is a **paper proof with exact rational constant replay**, not a kernel-checked Lean proof. Analytic inequalities are proved below; `verify.py` checks their constants and the single-base/ratio comparisons. It does not replace quantified reasoning by sample evaluations.

### Source dependency

Read-only source:

    ../math-bound/PROOF.md

SHA-256 of the inspected source:

    0f99ca32d0f4dc68a8ce2a1fa3c8784acd1e4a51accbf08fd5b4e50d0e4a291a

We use its original-majorant identity, raw-polar implications, structural H-integral argument, endpoint estimate, and the already-proved near/strip theorems. The needed ingredients are restated below. No existing source or directory was edited.

## 1. Original setting and retained necessary consequences

Let `m >= 7`, `9/10 <= a < 1`, and complex `q_1,...,q_m` satisfy

    |q_j| <= 1,
    | integral_0^1 product_j (a+(1-a^2)t q_j) dt | >= 1.

Use the actual statistics

    mu = x+iy = mean(q_j),  u=|mu|,
    s=mean(|q_j|^2),  v=s-u^2,
    b=1-2ax+a^2,  z=a mu,  w=|1-z|,
    Gamma=v/((m-1)u^2).

In particular

    0 <= v,  u^2+v=s <= 1,
    0 <= b <= lambda/(3+lambda) < 1,
    v/u^2 <= lambda/3,
    w^2+a^2 v <= b,
    x > a/2 > 0,
    x >= 1-lambda/(6a).

Thus `u>0`. Two consequences used repeatedly are

    v <= lambda/(3+lambda),                              (1.1)
    u sqrt(v) <= 1/2.                                   (1.2)

For (1.1), combine `v <= (lambda/3)u^2` with `u^2 <= 1-v`. For (1.2), square and use `u^2 v <= v(1-v) <= 1/4`. Neither step assumes `s=1`.

The exact original-majorant decomposition is

    E+Gamma = w^(m+1) + Gamma(1+|B_2(z)|) + Tail,

where Tail is the original square-root coefficient majorant summed over all `k=3,...,m`, and

    B_2(z)=(1-z)^(m+1)+(m+1)z(1-z)^m
           +m(m+1)z^2(1-z)^(m-1)/2.

The source's L=4 endpoint estimate gives

    w^(m+1) <= (2/3)h^2 <= h/15.                         (1.3)

Indeed `b^(m+1) <= (4/9)h^4`; the needed polynomial inequality follows from

    m^3-6m^2-3m+6 = (m-7)^3+15(m-7)^2+60(m-7)+34.

The actual variance contributes to the right-hand side:

    1-au = h+a(1-u) >= h+(a/2)v >= h+(9/20)v.           (1.4)

## 2. Structural tail, retaining its finite-m improvement

Put

    F_m=m(m-1)(m-2),  p=(m-3)/2,
    beta_s(t)=1-2axt+a^2 s t^2,
    S_m=9/4-2/(m-1)-1/(2m(m-1)),
    eta_m=(2/3)sqrt(S_m) <= 1.

The source's factorial-weighted Cauchy--Schwarz argument actually proves the slightly sharper version of its displayed T_3 bound:

    Tail <= (3/2) eta_m (m+1)a^4 u v^(3/2) sqrt(F_m)
                   integral_0^1 t^3 beta_s(t)^p dt.     (2.1)

For clarity, its exact summation is

    sum_(k=3)^m (2k+1)/(k)_3 = S_m.

Combined with `C_{m,k}(v)^2 <= (2k+1) binom(m,k)v^k` and the factorial-weighted binomial identity, this gives (2.1) without changing C, discarding complex H endpoints, or substituting actual coefficients. The source's proof of the C inequality and normalized-H integral identity is the only imported coefficient argument.

The norm chord bound, for `d=1-sqrt(b)>0`, gives

    sqrt(beta_s(t)) <= 1-dt,
    Tail <= 9 eta_m a^4 u v^(3/2)/(d^4 sqrt(F_m)).       (2.2)

This follows by extending the chord integral to `1/d` and integrating:

    integral_0^(1/d) t^3(1-dt)^(m-3) dt
        = 6/[d^4(m+1)F_m].

Also, for every `m>=7`,

    sqrt(F_m) >= (12/5)(m-1),                           (2.3)

since the squared difference after division by `m-1` is

    m(m-2)-(144/25)(m-1)
      = (m-7)^2+(156/25)(m-7)+11/25 >= 0.

A useful finite-m saving is

    eta_m <= 1-4/[9(m-1)] <= 1-4/(9m).                 (2.4)

Indeed `eta_m^2 <= 1-8/[9(m-1)]`, and `sqrt(1-t)<=1-t/2` for `0<=t<=1`. This saving will be used only in the near extension; the cutoff proof may take `eta_m<=1`.

## 3. Near extension: 1/4 <= lambda <= 1/3

The source already proves `lambda<=1/4`, so it suffices to handle this closed interval. Here

    h <= 1/21,  a >= 20/21,
    b <= 1/10,  v <= 1/10,
    u >= x >= 1-(1/3)/(6(20/21)) = 113/120.

Since `v(1-v)` increases on `[0,1/10]`, the actual-statistics bound improves (1.2) to

    u sqrt(v) <= 3/10.                                 (3.1)

Choose the rational square-root enclosure

    r=19/60,  sqrt(b)<=r,  d>=41/60.

The B_2 triangle inequality, retaining all three complex endpoint terms, gives

    |B_2| <= r^(m-1)[r^2+(m+1)r+m(m+1)/2] = D_m.

The three summands decrease with m: their consecutive ratios are at most `r`, `9r/8`, and `9r/7`, respectively. One base comparison gives

    D_7=r^6(r^2+8r+28) < 1/30.

Consequently

    Gamma(1+|B_2|) <= G v/(m-1),
    G=(31/30)(120/113)^2.                              (3.2)

We also retain a useful a^4 factor. For `h<=1/21`,

    a^4=(1-h)^4 <= 1-4h+6h^2 <= 1-(26/7)h.

Since `lambda>=1/4`, this yields

    a^4 <= 1-13/(14m).

Combining with (2.4), with all factors nonnegative,

    eta_m a^4
      <= (1-4/(9m))(1-13/(14m))
      <= 1-13/(10m).                                  (3.3)

For the last comparison, use `1/m<=1/7` in the positive quadratic correction and check

    13/14+4/9-(13/14)(4/9)/7 >= 13/10.

Equations (2.2), (2.3), (3.1), and (3.3) now give

    Tail <= A(1-13/(10m)) v/(m-1),
    A=9(3/10)(5/12)(60/41)^4.                          (3.4)

The only constant comparisons needed to consume this bound are rational:

    G <= (3/10)A,
    A+G <= 19/3.                                      (3.5)

To avoid freezing away the lambda-dependent right-hand budget, let

    Q=[A(1-13/(10m))+G]/(m-1).

Then, using `a=1-lambda/m`,

    m(Q-a/2)
      = A+G + [G-(3/10)A]/(m-1)-m/2+lambda/2
      <= 19/3-7/2+1/6 = 3.                            (3.6)

Therefore, with no division by v (so v=0 is included),

    Tail+Gamma(1+|B_2|)
      <= av/2 + 3v/m
      <= av/2 + 3h/(3+lambda)
      <= av/2 + (12/13)h.                             (3.7)

The endpoint contribution is at most `(2/63)h` by (1.3) and `h<=1/21`. Hence

    E+Gamma <= av/2 + (12/13+2/63)h
            = av/2 + (782/819)h
            <= 1-au-(37/819)h.                        (3.8)

For `lambda<=1/4`, the source's margin `79/504` is larger than `37/819`. Thus (3.8), with that common margin, holds throughout `lambda<=1/3`.

## 4. Strong endpoint suppression in the high-b case

The cutoff proof splits b, not degrees, at

    r=43/50.

The high-b case is `b>r`. From `b<=lambda/(3+lambda)` one gets

    lambda > 3r/(1-r)=129/7,
    m >= 185,                                         (4.1)

because `lambda<=m/10` and m is an integer.

Here is a self-contained derivation of the stronger endpoint bound used in this case. Put `d0=1-a^2` and

    R^2=a^2+2a d0 x+d0^2 = 1+d0(1-b).

The original full-complex integral premise, triangle inequality, AM--GM for the squared factor norms, and `s<=1` imply

    1 <= integral_0^1 [a^2+2a d0 x t+d0^2 t^2]^(m/2) dt.

The square root is the Euclidean norm of `(a,0)+d0 t(x,sqrt(1-x^2))`. Its convex endpoint chord is `a+(R-a)t`. Since `b<1`, `R>1>a`, and exact chord integration yields

    R^(m+1) >= (m+1)(R-a)+a^(m+1) >= (m+1)h = L.

The inequalities `log(1+t)<=t` and `log b<=-(1-b)` therefore imply

    b^p <= exp[-(m-3) log L / ((m+1)d0)].              (4.2)

There is no logarithm at b=0 in this argument: the present case has b>r>0.

Set `M=(m+1)/10`. Since `(m+1)d0=(1+a)L<=2L` and, by (4.1),

    3 < L <= M,

we can use the fact that `log t/t` decreases on `[3,infinity)`. For an elementary justification, `log t>=2(t-1)/(t+1)` for `t>=1`, by differentiation, so `log 3>=1`; now differentiate `log t/t`. It follows that

    b^p <= exp[-(m-3)log L/(2L)]
         <= exp[-(m-3)log M/(2M)]
          = M^(-5(m-3)/(m+1)).                        (4.3)

For `m>=185`, certainly

    5(m-3)/(m+1) >= 19/4,
    M >= 186/10 >= 16.

Thus `M^(-1/4)<=1/2`, and

    b^p <= (1/2) M^(-9/2)
         <= (1/2) (m/10)^(-9/2)
         <= 16000/m^(9/2),                            (4.4)

using `sqrt(10)<=16/5`. In particular

    m^(3/2)b^p <= 16000/m^3.                          (4.5)

This argument is uniform in h, m, and lambda. Its direction is important: replacing L by its largest permitted value in `log L/L` weakens the endpoint estimate in the safe direction. No lambda upper cutoff is used.

## 5. Structural integral near zero

Assume now `m>=170`, with either b case. From `x>a/2` and `s<=1`,

    beta_s(t) <= 1-a^2 t(1-t).

On `[0,1/4]`, this is at most `1-(3a^2/4)t`, so

    integral_0^(1/4) t^3 beta_s(t)^p dt
       <= integral_0^infinity t^3 exp[-3a^2(m-3)t/8] dt
        = 6[8/(3a^2(m-3))]^4.

Multiply by the prefactor in (2.1), take `eta_m<=1`, and now use the actual-statistics gain `u sqrt(v)<=1/2`. The resulting tail piece is at most `N(m)v`, where

    N(m)=(4096/18)(1+1/m)(10/9)^4
                       (m/(m-3))^4 m^(-3/2).         (5.1)

Here we used `sqrt(F_m)<=m^(3/2)` and `a>=9/10`. Every positive m-dependent factor in N decreases for real `m>3`. Exact squared rational comparisons at the two relevant base points give

    m>=170:  N(m)<=17/100,
    m>=185:  N(m)<=3/20.                              (5.2)

These are base points for two continuous bounds, not a degree table.

## 6. Structural integral away from zero

The other endpoint at the split satisfies

    beta_s(1/4) <= 1-3a^2/16 <= 1357/1600 = c,
    beta_s(1) <= b.

The quadratic beta_s is convex. Consequently it lies below the affine chord between these two endpoint upper bounds on `[1/4,1]`.

### 6.1 Low b: b<=43/50

Since `c<r=43/50`, convexity gives `beta_s(t)<=r` throughout this interval. With `integral_(1/4)^1 t^3 dt<=1/4`, `a^4<=1`, and `u sqrt(v)<=1/2`, its tail contribution is at most `J(m)v`, where

    J(m)=(3/16)(1+1/m)m^(5/2) r^((m-3)/2).

This sequence decreases for integer `m>=170`: `1+1/m` decreases, and the square of the consecutive ratio of the other factor is at most

    (171/170)^5 r < 1.

The exact base comparison, squared to remove radicals, gives

    J(170) <= 121/500.                                (6.1)

Together with (5.2),

    Tail <= (17/100+121/500)v                         (6.2)

in the low-b case.

### 6.2 High b: b>43/50

Here `m>=185` by (4.1), and

    b-c >= r-c = 19/1600 = delta.

This is where exact integration of the endpoint chord improves on bounding the entire interval by b^p. Using `t^3<=1`,

    integral_(1/4)^1 t^3 beta_s(t)^p dt
      <= (3/4)(b^(p+1)-c^(p+1))/[(p+1)(b-c)]
      <= (3/2)b^p/[(m-1)delta].                       (6.3)

This retains a full inverse-degree factor at the endpoint. After multiplying by the structural prefactor and using `u sqrt(v)<=1/2`, the corresponding tail piece is at most

    (9/8)((m+1)/(m-1)) m^(3/2) b^p v / delta
      <= (9/8)((m+1)/(m-1)) 16000 v /(delta m^3)
      <= (49/200)v.                                  (6.4)

The last expression is decreasing in m, and its value at `m=185` is an exact rational comparison. With (5.2),

    Tail <= (3/20+49/200)v                            (6.5)

in the high-b case.

## 7. Gamma and all B_2 endpoint terms

Throughout the cutoff proof, `u>=x>a/2>=9/20`, so

    Gamma <= 400v/[81(m-1)].                          (7.1)

Thus

    m>=170: Gamma <= (3/100)v,
    m>=185: Gamma <= (27/1000)v.                      (7.2)

The original complex B_2 formula and `au<=1`, `w<=sqrt(b)<1` give

    |B_2| <= w^(m-1)[1+(m+1)+m(m+1)/2]
           <= m^2 b^((m-1)/2) <= m^2 b^p.

The middle inequality holds for all `m>=7`, since `m^2-3m-4>=0`; after shifting `m=7+n`, this is `n^2+11n+24>=0`. Since

    (400/81)m/(m-1) <= (400/81)(7/6) < 6,

we obtain the uniform endpoint estimate

    Gamma |B_2| <= 6m b^p v.                          (7.3)

For low b, the sequence `m r^((m-3)/2)` decreases for integer `m>=170`, by the squared ratio bound `(171/170)^2 r<1`. The squared rational base check gives

    Gamma |B_2| <= (7/2000)v.                         (7.4)

For high b, (4.4) gives

    Gamma |B_2| <= 96000 m^(-7/2) v <= (1/500)v,       (7.5)

where the last squared comparison is at `m=185` and the function is decreasing.

## 8. Uniform cutoff conclusion

In the low-b case, (5.2), (6.1), (7.2), and (7.4) sum to

    Tail+Gamma(1+|B_2|)
      <= (17/100+121/500+3/100+7/2000)v
       = (891/2000)v.

In the high-b case, (5.2), (6.4), (7.2), and (7.5) give the stronger bound

    Tail+Gamma(1+|B_2|)
      <= (3/20+49/200+27/1000+1/500)v
       = (53/125)v < (891/2000)v.

In either case, for every integer `m>=170`,

    E+Gamma <= h/15+(891/2000)v
            <= 1-au-(14/15)h-(9/2000)v < 1-au.

The strict conclusion includes v=0 because h>0. This completes the uniform cutoff proof.

## 9. What remains, and the exact outstanding scalar consumer

The unresolved original domain is precisely the complement stated at the start after taking the union of proved sufficient regimes. No claim of failure of the original target is made on it.

For a next structural attack, one can retain more information than the cutoff proof without introducing any new premise. Define, on actual feasible statistics,

    W=sqrt(b-a^2(1-u^2)) = w,
    q(t)=1-(1+a^2-b)t+a^2(u^2+v)t^2 = beta_s(t),
    I_m=integral_0^1 t^3 q(t)^((m-3)/2) dt,
    P=W^(m-1)[W^2+(m+1)au W+m(m+1)a^2u^2/2].

A still-outstanding, stronger-than-necessary scalar inequality sufficient to finish the residual band is

    W^(m+1)
      + [v/((m-1)u^2)](1+P)
      + sqrt(S_m)(m+1)a^4 u v^(3/2)sqrt(F_m) I_m
        < 1-au.                                      (R)

It must be proved over `7<=m<=169`, `1/3<lambda<=m/10`, `v>h/m^2`, with the original actual statistics and full-polar premise, or over a rigorously specified necessary moment relaxation of those premises. The quantities in (R) are not obtained by assuming a real mean or s=1: W and q retain the actual u, v, b. The triangle bound P retains every complex B_2 term, while the structural coefficient sum is unchanged.

(R) is an explicit unproved scalar consumer, not an asserted equivalence and not an established obstruction: its failure would not itself refute the original majorant inequality. Keeping the exact complex |B_2| or the original tail instead could weaken the required consumer further. The successful cutoff rests specifically on three improvements: `u sqrt(v)<=1/2`, exact integration of the high-b endpoint chord, and using the upper bound on `(m+1)h` in the logarithmic endpoint suppression. The near extension additionally retains eta_m and a^4 and uses the unfrozen `a=1-lambda/m` in the right-hand budget.

## 10. Replay and scope of verification

Run from any directory:

    python3 /home/v-zhouziyu/work/sendov-paper-formalization-20260914-remaining-centered/research/centered-round2/math-middle/verify.py

The actual run passes **48 exact rational checks**. It uses only standard-library integers and `fractions.Fraction`, with no floating-point dependency. Fractional-power base inequalities are checked by squaring positive quantities. Each all-m geometric estimate is justified by a single base comparison and a symbolic monotonic/ratio argument, not a finite degree enumeration.

The replay checks constants and algebra; it does not kernel-check convexity, integration, logarithmic monotonicity, the imported raw-polar consequences, or the original H identity. These analytic steps are the paper proof above and the explicitly identified source dependencies. All newly saved proof and verification artifacts are confined to this new `math-middle` directory.
