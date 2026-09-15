# FULLpolar moment consequences, a uniform cutoff at 35, and a tail-chord obstruction

## Results and status

Under the original pointwise and FULLpolar premises, with actual statistics and the original square-root-C majorant:

1. For every integer `7 <= m <= 44`, `9/10 <= a < 1`,

       x > 7/10 + (1-a^2)(1-s)/(3a).                         (M)

   In particular `x > 7/10`, with no real-mean or `s=1` premise.

2. Throughout the continuous degree band `35 <= m <= 44`,

       E + Gamma <= 1-au - (107/250)(1-a) < 1-au.            (T)

   The proof uses one endpoint moment inequality at exponent 44, one exact polynomial integral, and monotonic comparisons on the entire band. There is **no per-m certificate table**. Combining (T) with the frozen `m>=45` theorem gives a paper cutoff `m>=35`.

3. Neither the finite whole-interval tail norm chord nor its extended-to-zero version can close the entire residual, even after the FULLpolar premise itself is retained. An exact FULLpolar-feasible conjugate-pair family at `m=44`, `a=9/10` has target budget `0.3628`, whereas the finite-chord tail bound alone is greater than an exactly certified rational lower bound above `0.95`. The original C majorant satisfies the target on this family; this is an obstruction to those *upper-bound consumers*, not a counterexample to the original target.

The uniform moment statement is backed by **one rational Bernstein sign certificate in h**, for a single exponent-44 moment. Its 88 coefficient checks are not certificates indexed by the original degree m. The analytic parts are paper proofs, not Lean/kernel proofs. If “no certificates” is intended to exclude even a single continuous-endpoint polynomial sign certificate, (M)/(T) do not meet that stronger requirement; the generic consequences in §§2–3 and exact obstruction in §7 remain independent deliverables.

## 1. Setting and original majorant

Let `m>=7`, `9/10<=a<1`, `d=1-a^2`, and complex `q_1,...,q_m` satisfy

    |q_j|<=1,
    |int_0^1 product_j(a+d t q_j) dt| >= 1.                  (FULLpolar)

Use the actual statistics

    mu=x+iy=mean(q_j),  u=|mu|,
    s=mean(|q_j|^2),    v=s-u^2,
    h=1-a,             lambda=mh,
    z=a mu,            w=|1-z|,
    Gamma=v/((m-1)u^2).

The original C and endpoint polynomials are

    C_(m,k)(v)^2 = m^m v^k/[k^k(m-k)^(m-k)]  (0<k<m),
    C_(m,m)(v)^2 = v^m,
    B_(m,k)(z) = sum_(j=0)^k binom(m+1,j)z^j(1-z)^(m+1-j),
    H_(m,k)(z) = 1-B_(m,k)(z).

Exactly as in the frozen sources,

    E+Gamma = w^(m+1) + Gamma(1+|B_(m,2)(z)|) + Tail,
    Tail = sum_(k=3)^m C_(m,k)(v)|H_(m,k)(z)|/[binom(m,k)u^k].

We import from the frozen proofs the original structural-C inequality and raw consequences

    s=u^2+v<=1,  v>=0,  x>a/2,
    v/u^2 <= mh/3,
    w^(m+1) <= h/15.                                      (1.1)

The last endpoint estimate is their L=4 bound for `a>=9/10`. The structural inequality, with its finite-m constant retained, is

    Tail <= sqrt(S_m)(m+1)a^4 u v^(3/2) sqrt(D_m)
            * int_0^1 t^3 beta_s(t)^((m-3)/2) dt,           (1.2)

where

    D_m=m(m-1)(m-2),
    S_m=9/4-2/(m-1)-1/(2m(m-1)),
    beta_s(t)=1-2axt+a^2 s t^2.

This inequality controls the original square-root C, not the actual coefficients of the product. Its proof uses `C_(m,k)^2 <= (2k+1)binom(m,k)v^k`, factorial-weighted Cauchy–Schwarz, and the exact normalized H integral. See frozen `math-cutoff45/PROOF.md`, §2, and `math-middle/PROOF.md`, §2.

## 2. Stronger generic necessary conditions directly from FULLpolar

### 2.1 Actual norm integral

Define, without altering s,

    Q_(a,x,s)(t)=a^2+2adxt+d^2st^2,
    N_m(a,x,s)=int_0^1 Q_(a,x,s)(t)^(m/2) dt.

Pointwise AM–GM for the squared factor norms gives

    product_j |a+dtq_j| <= Q_(a,x,s)(t)^(m/2).

Triangle inequality for the complex integral therefore proves

    N_m(a,x,s) >= 1.                                      (2.1)

This is only a necessary moment condition in general. It retains x, actual s, nonreal means through `u^2=x^2+y^2`, and variance `v=s-u^2`.

The condition can be sharp: if m is even and there are m/2 copies each of `x+i sqrt(s-x^2)` and its conjugate, all factor norms are equal and paired products are positive. Then the FULLpolar integral equals `N_m(a,x,s)` exactly, provided `0<=s<=1` and `x^2<=s`. This sharpness observation does not assume that a general feasible family has that form.

### 2.2 Exact polar endpoint chord, with actual s retained

Write

    R = sqrt(a^2+2ad x+d^2s).

The square root of Q is the Euclidean norm of

    (a+dxt, dt sqrt(s-x^2)).

It is convex, so its endpoint chord gives

    sqrt(Q(t)) <= a+(R-a)t.

If `R<=1`, that chord is strictly below 1 on a set of positive measure, contradicting (2.1). Thus `R>1>a`, and exact integration gives

    R^(m+1) >= a^(m+1)+(m+1)(R-a).                        (2.2)

This is stronger than discarding the `R-a` and `a^(m+1)` dependence.

For fixed m,a let `r_*(m,a)>1` be the unique solution of

    int_0^1 (a+(r_*-a)t)^m dt=1.

Existence and uniqueness follow from strict increase in r, value below 1 at r=1, and divergence as r tends to infinity. Equation (2.2) is equivalent to `R>=r_*`.

Put `B=beta_s(1)=1-2ax+a^2s`, which is the **actual** tail norm endpoint. The exact identity

    R^2 = 1+d(s-B)

therefore gives the coupled necessary constraints

    B <= s-(r_*^2-1)/d,                                  (2.3)
    x >= (r_*^2-a^2-d^2s)/(2ad).                          (2.4)

In particular, lowering s by epsilon raises the right-hand side of (2.4) by `d epsilon/(2a)`. Replacing B by the old b and s by 1 before this step discards precisely this information. No numerical root is required to use the inequalities symbolically.

## 3. A generic quantitative s-defect consequence of the actual norm integral

For m>=2 and x>=0 the derivatives are

    N_x = mad int_0^1 t Q(t)^(m/2-1) dt,
    N_s = (m d^2/2) int_0^1 t^2 Q(t)^(m/2-1) dt.

The function `g(t)=Q(t)^(m/2-1)` is nondecreasing when x,s>=0. Under probability density `2t` on [0,1], the covariance of the increasing functions t and g is nonnegative. For completeness, this follows by integrating

    (t-r)(g(t)-g(r)) >= 0

against the product of the two probability measures and dividing by two. Since the expectation of t under density `2t` is 2/3,

    int t^2 g >= (2/3) int t g.

Consequently

    N_s >= [d/(3a)] N_x.                                 (3.1)

An upper counterpart follows from `t^2<=t`:

    N_s <= [d/(2a)] N_x.

On a regular norm-integral boundary `N_m(a,X(s),s)=1`, this proves

    d/(3a) <= -X'(s) <= d/(2a),                           (3.2)

wherever that boundary exists with positive x. This is a generic moment-boundary slope statement, not a sampled estimate.

For an actual feasible pair set `k=d/(3a)` and follow the path

    x_sigma=x-k(sigma-s),  s<=sigma<=1.

Here `x_sigma>0`: the imported `x>a/2`, `a>=9/10`, and `k<=19/270` already suffice. Differentiating along the path and using (3.1) gives

    d/dsigma N_m(a,x_sigma,sigma) = N_s-k N_x >=0.

Thus FULLpolar implies the stronger, actual-s-retaining condition

    N_m(a, x-d(1-s)/(3a), 1) >=1.                        (3.3)

This is a proved domination to an auxiliary s=1 evaluation, **not an s=1 premise about the original family**. The moment theorem below applies to the shifted x in (3.3).

## 4. One continuous-endpoint moment certificate gives (M) for every m<=44

Set `x0=7/10` and

    J(h)=int_0^1 Q_(1-h,x0,1)(t)^22 dt,
    0<=h<=1/10.

We prove the single endpoint inequality

    J(h) <= 1-(23/50)h.                                  (4.1)

It is an exact polynomial sign assertion on a continuous h interval, not numerical quadrature. Let

    A(h,t)=10 Q_(1-h,7/10,1)(t)
          =10+(-20+28t)h+(10-42t+40t^2)h^2
             +(14t-40t^2)h^3+10t^2h^4.

If `A(h,t)^22=sum_(i,j) A_(i,j) h^i t^j`, define the rational coefficients

    c_i=10^(-22) sum_j A_(i,j)/(j+1).

Then `c_0=1`, `J(h)=sum_(i=0)^88 c_i h^i`, and

    P(h)=(J(h)-1)/h=sum_(j=0)^87 c_(j+1)h^j.

The expression at h=0 is its polynomial extension. On writing `r=10h`, its degree-87 Bernstein coefficients are exactly

    b_k=sum_(j=0)^k c_(j+1)10^(-j) binom(k,j)/binom(87,j),
    k=0,...,87.

The standard basis conversion gives

    P(h)=sum_(k=0)^87 b_k binom(87,k) r^k(1-r)^(87-k).

`verify.py` reconstructs A^22 by integer polynomial multiplication, integrates all t monomials by rational division, reconstructs these b_k from scratch, and verifies

    b_k <= -23/50  for every k=0,...,87.                   (4.2)

The complete exact coefficients are emitted in `cache/exact-verification.json`; the checker does not read a saved asserted bound. Bernstein basis weights are nonnegative and sum to one, so (4.2) proves (4.1). The maximum coefficient is approximately `-0.4613735336077785`, strictly below `-23/50`; only exact rational comparisons are used for the proof.

Now suppose `m<=44` and `N_m(a,X,1)>=1` with X<=7/10. Pointwise monotonicity in X, followed by the probability-space Lp inequality, gives

    1 <= N_m(a,X,1)
       <= int_0^1 Q_(a,7/10,1)(t)^(m/2) dt
       <= J(h)^(m/44) <1,

a contradiction. The last strict inequality uses h>0 in (4.1). Applying this to (3.3) yields

    x-d(1-s)/(3a) > 7/10,

which proves (M). There is one moment certificate at exponent 44; Lyapunov/Hölder monotonicity covers the entire real range `0<m<=44` in the scalar comparison. No sequence of degree-wise tests has been used.

## 5. The original structural C tail on the entire band 35<=m<=44

Change variables `y=at` in (1.2). The fourth power of a cancels exactly:

    Tail <= sqrt(S_m)(m+1)u v^(3/2)sqrt(D_m)
            * int_0^a y^3 (1-2xy+s y^2)^((m-3)/2) dy.      (5.1)

Do not discard a^4 before this change of variables. For actual statistics,

    1-2xy+s y^2=(1-xy)^2+(s-x^2)y^2 >=0.

Here y is a bound real integration variable, not the imaginary coordinate in the definition of mu.

By (M), x>7/10, and s<=1. Define

    q0(y)=1-(7/5)y+y^2=(y-7/10)^2+51/100.

For `0<=y<=1`, `0<q0(y)<=1`, and the integrand quadratic in (5.1) is at most q0. Since a<=1 and `(m-3)/2>=16`,

    int_0^a y^3 (1-2xy+s y^2)^((m-3)/2)dy
       <= int_0^1 y^3 q0(y)^16dy = J16.                  (5.2)

This preserves the curvature of the norm square instead of replacing its square root by a whole-interval chord.

Also

    sqrt(S_m)<=3/2,
    (m+1)sqrt(D_m)<=45 sqrt(44*43*42),
    u sqrt(v)<=1/2.

The last inequality follows from `u^2 v <= (1-v)v<=1/4`, with actual s<=1. Hence

    Tail <= [(3/4)*45*sqrt(44*43*42)*J16] v
         <= (433/1000)v.                                 (5.3)

No division by v is used, so zero variance is covered. J16 is a rational polynomial integral; `verify.py` computes it by expansion and checks the positive-square inequality

    [(3/4)*45]^2 (44*43*42) J16^2 < (433/1000)^2.

All degree dependence was bounded continuously on `[35,44]`; there is just one polynomial integral at the lower exponent, not one integral per degree.

## 6. Endpoint terms and budget consumption

By u>=x>7/10 and m>=35,

    Gamma <= [100/(49*34)]v <= (61/1000)v.                 (6.1)

Moreover

    w^2=1-2ax+a^2u^2 <= 1-(7/5)a+a^2 <=3/5,

because the last quadratic increases on `[9/10,1]` and has value 3/5 at 1. The exact three-term B2 formula, `au<=1`, and `w<=1` imply for m>=7

    |B2| <= w^(m-1)[w^2+(m+1)au w+m(m+1)a^2u^2/2]
         <= m^2 w^(m-1).

The elementary polynomial comparison behind the second inequality is `m^2-3m-4>=0`. Consequently on `[35,44]`,

    Gamma|B2| <= [100/(49*34)]44^2(3/5)^17 v
              <= (20/1000)v.                             (6.2)

Combining (5.3), (6.1), (6.2), and (1.1) gives

    E+Gamma <= h/15+(257/500)v.                          (6.3)

Here the right-hand side must be consumed using the actual mean, not merely `h+(9/20)v`. Instead,

    1-au=(1-u)+hu >= v/2+(7/10)h,                        (6.4)

since `v<=1-u^2<=2(1-u)` and u>7/10. The raw consequence `v/u^2<=mh/3`, together with u<=1 and m<=44, gives

    v<=44h/3.

Therefore

    E+Gamma-(1-au)
      <= h/15-(7/10)h+(7/500)v
      <= [1/15-7/10+(7/500)(44/3)]h
       = -(107/250)h.

This proves (T), including v=0. Combining with the frozen cutoff45 theorem lowers the paper cutoff to m>=35. Combining further with the already-proved near region and strip leaves

    integer 7<=m<=34,
    1/3<lambda<=m/10,
    v>h/m^2,

still intersected with the original FULLpolar feasible set. The entire remaining domain is **not** solved here.

## 7. Exact obstruction to both whole-interval tail norm chords

Take m=44, a=9/10, and 22 copies each of

    q_+ = 177/250 + i sqrt(31171)/250,
    q_- = 177/250 - i sqrt(31171)/250.

These are exact algebraic numbers of norm one. Their actual statistics are

    mu=x=u=177/250,
    s=1,
    v=31171/62500,
    1-au=907/2500=0.3628.

Every conjugate pair contributes

    (a+dtq_+)(a+dtq_-)=a^2+2adxt+d^2t^2.

The full complex product is therefore a positive real polynomial and

    K=int_0^1 (a^2+2adxt+d^2t^2)^22dt
      =1.0014100154856307207512198857459085... >1.

`verify.py` expands and integrates this polynomial using rational arithmetic, proving the strict inequality without a numerical feasibility assumption. The family lies in the original residual (`lambda=22/5>1/3`, `v>h/m^2`).

Its actual beta endpoint and chord slope are

    B=beta_s(1)=1339/2500,
    c=1-sqrt(B).

Let `eta=(2/3)sqrt(S_44)`. The two tail upper bounds obtained by applying the norm chord are

    U_fin = (3/2)eta*45*a^4*u*v^(3/2)*sqrt(D_44)
            *int_0^1 t^3(1-ct)^41dt,

    U_ext = 9eta*a^4*u*v^(3/2)/(c^4 sqrt(D_44)).

The checker verifies exact rational enclosures

    eta>49/50,  sqrt(v)>7/10,
    sqrt(B)>73/100, hence c<27/100,
    281<sqrt(D_44)<282.

Thus

    U_ext > 9(49/50)a^4*u*v(7/10)/[(27/100)^4*282]
          > 0.9544 > 907/2500,

where the second comparison is an exact rational inequality, not a reliance on the displayed decimal. Likewise

    U_fin > (3/2)(49/50)*45*a^4*u*v(7/10)*281
             *int_0^1 t^3(1-(27/100)t)^41dt
           > 907/2500.

That last polynomial integral and comparison are also checked exactly. Therefore even either tail bound *alone* exceeds the entire target budget on a FULLpolar-feasible family. A theorem asserting that FULLpolar forces either whole-chord consumer below the target is false.

For comparison only, `compare.py` replays the original square-root-C sum, the exact-beta structural tail, and both chord tails at 90 and 160 decimal digits. It evaluates every H both by a positive finite binomial tail and the normalized integral identity, with agreement beyond 75 digits. The numerical results are:

| Tail / total | Value |
|---|---:|
| original C tail | 0.02777305439209419 |
| original-beta structural tail | 0.04328079161616759 |
| finite whole norm-chord tail | 0.9990377995014877 |
| extended norm-chord tail | 0.9997098448564159 |
| original `(E+Gamma)/(1-au)` | 0.1403296125867109 |
| structural-R total ratio | 0.1830742025097357 |
| finite-chord total ratio | 2.817465073196947 |
| extended-chord total ratio | 2.819317458408987 |

These decimal tail comparisons are high-precision evidence, not interval certificates. FULLpolar feasibility, the chord-consumer obstruction, and the continuous theorem are backed by exact rational checks plus the paper arguments above. The large loss here is the replacement of the actual beta curvature by the norm chord; extending its integral is not the main loss. This family is not a counterexample to the original target, which also follows from (T).

## 8. Replay, provenance, and scope

From any directory:

    python3 /home/v-zhouziyu/work/sendov-paper-formalization-20260914-remaining-centered/research/centered-round3/math-polar/verify.py

This standard-library-only replay reconstructs the moment polynomial and its Bernstein coefficients, the tail integral, all rational budgets, and the actual-family feasibility/obstruction. It performs no reads from an asserted certificate. Its exact records are emitted only to the owned `cache/` directory.

Optional numerical comparison:

    /home/v-zhouziyu/work/sendov-paper-formalization-20260914-remaining-centered/research/centered-round3/math-polar/.venv/bin/python /home/v-zhouziyu/work/sendov-paper-formalization-20260914-remaining-centered/research/centered-round3/math-polar/compare.py

The private venv supplies mpmath; scipy/numpy were used only in exploratory probes. `probe.py`, `chord_probe.py`, and `probe-results.json` are explicitly exploratory and are not invoked by the proof checker.

Read-only dependencies are the frozen proofs at:

* `research/centered-round2-verified/math-middle/PROOF.md`
* `research/centered-round2-verified/math-cutoff45/PROOF.md`
* their referenced original coefficient/raw-polar arguments.

No Lean work, source edits, commits, or pushes were performed. Every newly created artifact, dependency, and cache is under the task-owned `math-polar` directory.
