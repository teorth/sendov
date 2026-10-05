# Sendov finite-range formalization — design notes

A standing record of what this project is, what is proved, what is open, and why the
architecture is what it is.  Written to be read cold, including by a reviewer who has not
seen the code.  Numbers here were measured on this project's actual shapes, not estimated;
several of them overturned a design that looked obviously right on paper.

Machine: Windows 11, Lean 4.34.0-rc1, mathlib pinned in `lake-manifest.json`.  Timings
include Lean startup (~1.5–2 s) unless stated otherwise.

---

## 1. The claim

From the blog post [*A digestion of the proof of Sendov's conjecture*](https://terrytao.wordpress.com/2026/08/12/a-digestion-of-the-proof-of-sendovs-conjecture/).  After the polynomial
argument, one inequality — equation `stat` — remains unproved on a finite range.  Writing
`M = n-1`, `A = a² = 1 - 2α/M`, `c = 1 - α/M - α/(2(3+α))`, `Q(t) = 1 - 2ct + At²`,
`B = α/(3+α)`, the claim is that

```
R n α = 1/6 + 1/(4(3+α)) + 1/(2M) + 1/(4M(3+α))
          + A² n M (n-2)/(4(3+α)) · ∫₀¹ t³ Q(t)^((n-4)/2) dt
```

satisfies `R n α < 1` on `5 ≤ n ≤ 97`, `0 ≤ α ≤ 17`, subject to the feasibility constraint
`c² ≤ A`.  (`n ≥ 98` is handled by a separate analytic argument; see §6.)  The exponent is a
*real* exponent — half-integral for odd `n` — so `Real.rpow` is involved.

`Sendov/Defs.lean` fixes the notation; `Sendov/FiniteRange/Cover.lean` states the claim and
derives the `False` form in which it is applied.

**Numerically**, `R` attains max `0.8529` at `n = 53, α = 17`.  So a bound may lose ~15% and
still succeed — a fact that matters repeatedly below.

---

## 2. Status

| component | file | state |
|---|---|---|
| Definitions of `stat` | `Defs.lean` | definitions only |
| **The claim, degrees 5–100** | **`FiniteRange/Cover.lean`** | **proved** |
| Basic properties (shared A/B) | `Common/Basic.lean` | proved |
| Real powers, integrability (shared A/B) | `Common/Rpow.lean` | proved |
| Moment formula (M) | `FiniteRange/Moments.lean` | proved |
| Odd-degree bound | `FiniteRange/OddBound.lean` | proved |
| Per-degree reduction | `FiniteRange/Reduce.lean` | proved |
| Batching machinery | `FiniteRange/Batch.lean` | proved |
| Degrees 5, 6, 7, 8, 20 (single) | `FiniteRange/Degree*.lean` | proved, no `sorryAx` |
| 31 degree batches covering 6–100 | `FiniteRange/Degree{n₀}_{n₁}.lean` | proved |
| Moment recurrence | `FiniteRange/Recurrence.lean` | proved; too slow to use (§4) |
| Kronecker packing core | `FiniteRange/Pack.lean` | proved |
| Packing bridge | `FiniteRange/PackBridge.lean` | proved |
| Degree 20 via packing | `FiniteRange/Degree20Packed.lean` | proved, cross-checked |
| Degree 53 moment via packing | `FiniteRange/Degree53Packed.lean` | proved, 10 s |
| Degree 97 moments (k = 46, 47) | `FiniteRange/Degree97Packed.lean` | proved, 17 s |
| The quadratic `QQ c A t` (shared) | `Common/Quadratic.lean` | proved |
| Beta integrals and the split (shared) | `Common/Chord.lean` | proved |
| The sinh lemma (shared) | `Common/Sinh.lean` | proved |
| Tail bound `R ≤ U` (B2) | `LargeDegree/Tail.lean` | proved |
| Degree monotonicity of `U` (B3) | `LargeDegree/Monotone.lean` | proved |
| `Ut < 1`, degrees ≥ 101 (B4–B5) | `LargeDegree/Endgame.lean` | proved |
| **The claim, every degree** | **`Main.lean`** | **proved** |
| `(1Q) ⟹ (lt)` | `Reduction/Polar.lean` | proved |
| `(lt) ⟹ (beta-bound)` | `Reduction/BetaBound.lean` | proved |
| `(origin-exact) ⟹ (1le)` | `Reduction/Simplified.lean` | proved |
| `(1le)+(beta-bound) ⟹ stat` | `Reduction/Stat.lean` | proved |
| `⟹ α ≤ 17` | `Reduction/Alpha17.lean` | proved |
| **`(1Q)` and `(origin-exact)` incompatible** | **`Reduction/Main.lean`** | **proved** |
| Maclaurin's inequality (top case) | `Analytic/Maclaurin.lean` | proved |
| The defect lemma | `Analytic/Defect.lean` | proved |
| The two factorizations | `Counterexample/Factor.lean` | proved |
| The four identities (Lemma 1) | `Counterexample/Identities.lean` | proved |
| The polar branch point and `(1Q)` | `Analytic/Polar.lean` | proved |
| The error bound, `F'`, and `(tri)` | `Analytic/Origin.lean` | proved |
| The defect estimate for `J ∑ 1/zⱼ` | `Analytic/Jsum.lean` | proved |
| `(f1aq)`, `(grow)`, `(origin-exact)` | `Analytic/OriginExact.lean` | proved |
| Low degrees `2 ≤ n ≤ 5` (branch at `(⋆)`) | `Analytic/LowDegree.lean` | proved |
| The centre `a = 0` | `Interior.lean` | proved |
| **Conjecture `interior`, real `0 ≤ a < 1`** | **`Interior.lean`** | **proved** |
| **Rubinstein at `a = 1`, with equality case** | **`Boundary.lean`** | **proved** |
| Rotation normalization | `Conjecture.lean` | proved |
| **Sendov + Phelps–Rodriguez, full** | **`Conjecture.lean`** | **proved** |
| Certificate generators | `scripts/*.py` | untrusted, self-checking |
| Trust audit | `scripts/audit.sh` | passes |
| Mutation test | `scripts/mutation_test.sh` | passes |

Degree 20 has been reproduced through the packed path and cross-checked against the
multinomial route (`packed_agrees_twenty`), so the bridge is validated end to end.

**The claim is proved.**  `Sendov.stat_lt_one` gives `R n α < 1` for **every** `n ≥ 5` and
`0 ≤ α ≤ 17` under feasibility, so `Sendov.stat_contradiction` shows equation `stat` of the
blog post is unsatisfiable outright — there is no longer any range left open.  `scripts/audit.sh`
reports no forbidden tokens and

```
'Sendov.stat_lt_one' depends on axioms: [propext, Classical.choice, Quot.sound]
```

**The A track.**  `Sendov.finite_range_le_100` proves `R n α < 1` for every
`5 ≤ n ≤ 100`, `0 ≤ α ≤ 17` under feasibility, and `Sendov.finite_range` is the original
`n ≤ 97` challenge statement as a special case.  Coverage is not asserted anywhere: the case
split in `Cover.lean` is generated from the batch plan and would not compile if a degree were
skipped.  Three degrees beyond the original `97` were certified so that the finite range
meets the large-degree argument with room to spare (`U` has margin `0.122` at `n = 101`
against `0.048` at `n = 98`).

The seam is at `100/101`, not the blog post's `97/98`.

The hypotheses are all derivable by arithmetic rather than by computing `qrow`: coefficient
size from `l1row_qrow`, entry length from `qrow_entry_length_le` (an entry of the `k`-th row
has length at most `1 + G*k`), row length from `qrow_length`, and packed magnitude from
`abs_pevZ_le`; `rowZ_bound` and `wsum_bound` package these as numeric inequalities.
`Degree53Packed.lean` uses them and builds in **10 s** at `k = 24`, so the route is validated
at the numerically worst degree.  (`Degree20Packed.lean` still uses `decide`, which is
affordable at `k = 8` and exercises the same statements.)

Parameters from the *provable* bounds, and the measured cost:

| n | k | β | τ | `G^k` | build |
|---|---|---|---|---|---|
| 20 | 8 | 104 b | 1,735 b | 0.003 MB | 11 s |
| 53 | 24 | 327 b | 24,098 b | 1.17 Mb | 10 s |
| 97 | 46 | 659 b | 92,038 b | 8.53 Mb | — |
| 97 | 47 | 677 b | 96,593 b | 9.14 Mb | 17 s (both) |

`k = 47` is the largest exponent anywhere in `5 ≤ n ≤ 97`, so this is the worst case and it
costs seconds.

### Batching adjacent degrees

Every term of `R n α` is monotone in `n`: `base_n` decreases, the prefactor
`A_n² n (n-1) (n-2) / (4(3+α))` increases, and `I_n` decreases (since `Q_{n+1} ≤ Q_n`, and
the exponent grows while `Q ≤ 1`).  So for a batch `[n₀, n₁]`,

```
R n α ≤ base_{n₀}(α) + pref_{n₁}(α) · I_{n₀}(α)     for every n in the batch,
```

one moment and one certificate for the whole batch.  Taking `n₀` even makes `I_{n₀}` an exact
integer moment.  Crucially the certificate's degree is set by `n₀`, the *smallest* member, so
a batch is not merely fewer certificates but cheaper ones.

Measured, with certificate cost interpolated from (deg 18, 12 s), (deg 52, 99 s),
(deg 96, 129 s):

| range | individually | batched | saving |
|---|---|---|---|
| `n ∈ [6,40]` | 14.2 min | 3.5 min | 4× |
| `n ∈ [42,60]` | 28.3 min | 10.2 min | 2.8× |
| `n ∈ [62,97]` | 69.8 min | 5.6 min | **12.5×** |
| total | 115 min | 21 min | 5.5× |

Batch sizes track the slack: 2–3 through the tight middle around the `n = 53` peak, rising to
12 and 16 at the top.  The high degrees — 61% of the cost when done individually — batch best
precisely because `R n α` falls away from the peak, so they drop to 22% of the batched total.
21–26 batches cover `6 ≤ n ≤ 97` depending on how much margin is left.

Batches cannot be made arbitrarily large: the bound degrades as `pref_{n₁}/pref_{n₀}` grows
like `(n₁/n₀)³`, which the shrinking moment does not offset.  Ending at 97, the bound is
`0.66` for `[82,97]`, `0.91` for `[78,97]`, `1.95` for `[70,97]` and `4.78` for `[62,97]`.
So about 20 degrees is the ceiling at the top of the range; `[78,97]` is the largest batch
admitting a certificate, at degree 76.

**The plan must be driven by certificate feasibility, not by the numeric bound.**  These do
not track each other: `[34,36]` at bound `0.9348` admits no single all-positive Bernstein
certificate, while `[52,53]` at `0.9475` does.  So the generator should attempt a batch,
check the certificate, and shrink on failure — subdivision in `n`, which does pay, rather
than in `α`, which was shown unnecessary.  `scripts/plan_batches.py` does the search.

### Can degrees sharing a `k` share work?

Each `k` serves up to three degrees: `n = 2k+3` (as its upper index), `n = 2k+4` (even), and
`n = 2k+5` (as its lower index).  But the split is unfavourable:

* `k` only, shareable: `L = lcm(4 .. 2k+4)`, `mlen = 1 + 3k`, the divisibility obligation;
* `n` only: `L1 = 30(n-1) - 16`;
* **both**: `β`, `τ`, `Nmom`, and the row itself, since `g₀,g₁,g₂` depend on `n`.

The row is the expensive object, so three degrees sharing a `k` still need three separate
exponentiations.  Measured at `k = 47`: the packed check alone is essentially the entire
per-moment cost, the shared items together being a 136-bit numeral and a divisibility fact.
Factoring them out would save under a second per degree, so it is not worth a separate
`k`-indexed module.

(Treating `M = n-1` as a third Kronecker variable *would* let one computation serve all
degrees, but the row acquires an `M`-degree of `k`, making the packed object roughly `k`
times larger — about 430 Mbit at `k = 47`.  That trades a factor of `93/k ≈ 2` at best for a
much larger object, and loses outright at small `k`.)  `τ` exceeds the earlier estimate because the provable entry-length bound is
`1 + 3k` rather than the true `2k+1`; the multipliers have degree ≤ 2, so a sharper induction
would recover it, but the cost is a bigger `τ`, not a slower build.

---

## 3. The reduction chain

Each degree reduces to polynomial positivity in `α` alone:

1. **`R_le_of_integral_le`** — the coefficient of the integral in `R` is nonnegative, so any
   upper bound `J` for the integral bounds `R`.
2. **Even `n`** — `integral_eq_mom`: the integral *equals* the moment `mom n α k`, `k=(n-4)/2`.
   No hypotheses at all; it is a polynomial identity.
   **Odd `n`** — `integral_rpow_le`: `√q ≤ q/(2w) + w/2` (the tangent to `√·` at `q = w²`)
   turns `Q^(k+1/2)` into a combination of `mom n α k` and `mom n α (k+1)`, for any `w > 0`.
3. **`alpha_le_half_M`** — feasibility gives `α ≤ (n-1)/2`, the only numerical input needed.
4. Clear denominators: `1 - R n α = P n (α) / D n (α)` with `D > 0`, `deg P = n - 2`.
5. **Bernstein certificate** — `U^d · P(α) = Σⱼ Γⱼ αʲ (U-α)^(d-j)` with all `Γⱼ > 0`, whence
   `P > 0` on `[0, U]`.

### Simplifications found along the way

- **The tangent parameter `w` unifies degree 5.** The plan gave `n = 5` its own apparatus
  (chord bound, `H(B)` in half-integer powers of `B`, the substitution `α = 3r²/(1-r²)`)
  because bound (O) is too wasteful there. True — (O) gives `1.0625` at `α = 0`, proving
  nothing — but the cause is narrow: (O) is the tangent taken at `q = 1`, and in degree 5 the
  relevant `Q` values are small. Taking `w = 1/3` instead gives `0.737` against the exact
  `0.716`. All odd degrees now share one code path and no square roots survive.
- **No subdivision.** One Bernstein certificate on the whole interval has all coefficients
  positive at every degree tested (20, 53, 97). The plan's adaptive bisection is unnecessary.
- **No infeasibility branch.** Only the numerical step needs feasibility, and only as
  `α ≤ (n-1)/2`. The exact feasible region (cut out by a quartic) is never required. This is
  *not* the claim that `A ≥ 0` replaces feasibility: the odd-degree bound needs `0 ≤ Q` on
  `[0,1]`, which is `Q_nonneg` and uses the full `c² ≤ A`.
- **Beta, not Gamma.** For `n ≥ 98` the write-up bounds the tail by `Q ≤ exp(-ct)` and the
  Gamma integral. Keeping the chord as a *power* instead gives
  `∫₀¹ t³(1-t)ˢ dt = 6/((s+1)(s+2)(s+3)(s+4))` — no improper integral, no `Real.exp`, and
  strictly sharper, so every constant downstream survives unchanged.

---

## 4. Computing the moment: representation, not algorithm

`∫₀¹ t³ Qᵏ dt` is the bottleneck. The multinomial formula (M) has `Θ(k²)` terms and its
`simp` expansion dies around `k = 20` — at `n = 53` the 676-term expansion exhausts 2 M
heartbeats. `Recurrence.lean` replaces it with the coefficient recurrence
`R(k+1,j) = g₀R(k,j) + g₁R(k,j-1) + g₂R(k,j-2)`, where `D·Q = g₀ + g₁t + g₂t²` with
`D = 2(n-1)(3+α)` and the `gᵢ` integer polynomials in `α`. That is correct but still slow:

| representation | k=24 | k=32 | k=46 |
|---|---|---|---|
| `List (List ℤ)` (`Recurrence.lean`) | 120 s | >20 min | hours |
| 1-D packed, `List ℤ` | — | — | 158 s |
| 2-D packed, single `Nat` (`Pack.lean`) | — | — | ~0.5 s |

Kernel `Nat` arithmetic is GMP-backed — a 4000-digit multiplication and a 50th power are
milliseconds — while list recursion is interpreted at roughly 240 µs per coefficient
operation. `qrow` was never the wrong *algorithm*; it was the wrong *representation*. Under
Kronecker packing (evaluate at a base exceeding every coefficient) polynomial multiplication
becomes `Nat` multiplication and the whole recurrence becomes `base ^ k`, one exponentiation.

Measured end to end through the verified `unpackN`: one exponentiation to a 3,042,311-bit
number plus extraction of all 93 coefficients, **7 s**.

### Numerical parameters

Two bases are needed per degree: `β` packs a coefficient polynomial in `α`, `τ` packs the
resulting row in `t`.  With `L1 = 30(n-1) - 16` (the sum of `|coefficients|` of `g₀,g₁,g₂`,
which bounds every coefficient of the `k`-th power) and `L = lcm(4 .. 2k+4)` (clearing the
`1/(j+4)` weights):

```
β > 2 · (2k+1) · (L/4) · L1^k        -- fits the moment numerator's coefficients
τ > 2 · L1^k · (β^(2k+1) - 1)/(β-1)  -- fits the α-packed row entries
```

| n | k | L1 | L | β | τ | `G^k` |
|---|---|---|---|---|---|---|
| 20 | 8 | 554 | 28 b | 104 b | 1,735 b | 0.003 MB |
| 53 | 24 | 1544 | 72 b | 331 b | 16,107 b | 0.09 MB |
| 97 | 47 | 2864 | 136 b | 681 b | 64,554 b | 0.72 MB |

Verified at `n = 53` with the real `g` coefficients: the `τ` bound holds, and the kernel
computes `G^24` (788,991 bits) and extracts all 49 α-packed row entries in **9 s** including
Lean startup.

### The packing bound is essentially free

`unpackN_pow` requires `(npev p 1)ᵏ < b`, the sum of coefficients to the `k`-th power.
Against the true maximum coefficient:

| n | k | true max | bound `L1ᵏ` | slack | packed size |
|---|---|---|---|---|---|
| 53 | 24 | 249 b | 255 b | 6 b | 0.07 MB |
| 97 | 46 | 522 b | 529 b | 7 b | 0.54 MB |

5–7 bits, under 1.5% of block size. Take `B = bitlength(L1ᵏ) + 1` with `L1 = 30(n-1) - 16`;
no per-degree tuning, packed objects under 0.6 MB.

---

## 5. `ring` costs, and the build budget

| task | time | peak memory |
|---|---|---|
| Bernstein identity, degree 18 (n=20) | ~12 s | small |
| Bernstein identity, degree 52 (n=53) | ~99 s | — |
| Bernstein identity, degree 96 (n=97) | 129 s | ~4 GB |
| 8-chord moment identity, degree 48 (n=53) | never finished | >10 GB, killed |

`ring` handles the Bernstein identity at every degree needed, so the certificate layer needs
no packing. Two consequences: roughly **3 hours** for 93 degrees, and **4 GB peaks**, so
high-degree files must not compile in parallel.

The last row is why the moment is not expanded symbolically: Bernstein terms are
`Γⱼ αʲ (U-α)^(d-j)`, one binomial expansion each, whereas chord terms are products of two
different high-degree powers. Same degree, entirely different cost.

---

## 6. Approaches measured and rejected

- **Interval arithmetic in `α`.** Needs ~200 α-boxes at `n = 53` (`p=8,N=60` still gives
  1.0999); the `m`-th power amplifies interval loss.
- **Extending the analytic `n ≥ 98` argument downward.** Its bound bottoms out at exactly
  `n = 98`; the Beta improvement lowers `U₅₄` from 2.10 to 1.88, nowhere near 1.
- **Monotonicity `R_{n+2} ≤ R_n`.** True — verified over `53 ≤ n ≤ 95`, and `R_{n+1} ≤ R_n`
  too — but the minimum relative margin is **1.48%** at `(53, 17)`, while proving `R_n < 1`
  directly allows ~15%. Monotonicity demands ten times the sharpness of the actual goal, and
  a chord-based sufficient condition loses 10%. Rejected on those grounds, not on difficulty.
- **Endpoint-power chord integrals.** ~8× algorithmically, but introduces `v⁴` denominators,
  `v = 0` case splits *inside* the feasible region, and raises `deg P` from ~96 to ~164.
  Superseded by packing, which is faster and touches nothing.

---

## 6b. Next target: `{1Q}` and `{origin-exact}` are incompatible

*Done.*  `Sendov.polar_origin_incompatible` proves that **`{1Q}` and `{origin-exact}` are not
simultaneously satisfiable for `n ≥ 5`** — a statement with no complex numbers and no
polynomials in it, in the real variables `a ∈ (0,1)` and `x ∈ [-1,1]` alone.  Everything the
blog post leaves to computation is now formalized; what remains outside Lean is the
complex-analytic derivation of the two raw inequalities themselves.

The chain, all links checked numerically and symbolically before any Lean was written:

| link | status |
|---|---|
| `{1Q} ⟹ {lt}` | **proved**, `Sendov.polar_exp`.  The pointwise bound `(at)` is an *identity* up to `t² ≤ t`: rhs − lhs = `(2α/(n−1))²(t−t²)` |
| `{lt} ⟹ {beta-bound}` | **proved**, `Sendov.beta_le` |
| `{beta-bound}+{origin-exact} ⟹ {17}` | **proved**, `Sendov.alpha_le_seventeen` |
| `{origin-exact} ⟹ {1le}` | **proved**, `Sendov.one_le_of_origin` |
| `{1le}+{beta-bound} ⟹ {stat}` | **proved**, `Sendov.stat_of_one_le` |

Four deliberate deviations from the write-up:

* **`{17}` uses the Beta identity, not `∫₀^∞ t e^{-ct} dt`.**  The chord bound `β(t) ≤ 1-axt`
  plus `∫₀^{1/c} t(1-ct)^s dt = 1/(c²(s+1)(s+2))` reuses `LargeDegree` machinery, avoids an
  improper integral, and improves the margin from `1.948` to `1.817`.
* **Everything is non-strict.**  `{beta-bound}` is stated with `<`, but every downstream use
  needs only `≤`, so no strict integral monotonicity is required anywhere.  This removes the
  need to argue that the integrand of `(lt)` is strictly smaller on a set of positive measure.
* **The mean value theorem is replaced by Bernoulli.**  The write-up bounds
  `((1-axt)² + s)^{(n-2)/2}` by the MVT.  Dividing `(P+Q)^p ≤ P^p + pQ(P+Q)^{p-1}` through by
  `(P+Q)^p` turns it into `1 ≤ θ^p + p(1-θ)` at `θ = P/(P+Q)`, which is Mathlib's
  `one_add_mul_self_le_rpow_one_add` verbatim — no derivative, no differentiability side
  conditions.
* **The `sinh` lemma is proved differently** — see below.

### The `sinh` lemma (`Common/Sinh.lean`), *done*

`log(sinh h/h) ≤ √(h²+9) - 3` is the crux: it is what produces the constant `3` in
`β(1) ≤ α/(3+α)`, and it is sharp — at `β = α/(3+α)` the slack in the integral inequality is
`-α⁵/540 + α⁶/648`, so the bound is tight to *three* orders at `α = 0` and no lossy step is
available.  The write-up proves it from the Taylor expansion
`Σ_{k≥4} 2^{2k-3}(2k-1)(2k-6)²/(2k)! h^{2k}` (coefficients confirmed).

Formalizing a series with nonnegative coefficients is unpleasant.  Instead, with
`Φ(y) = e^{2y}(y³-10y²+36y-36) - e^y(y⁴+16y²-72) - (y³+10y²+36y+36)`:

* `Φ(2h) = 16 e^{2h} G(h)`, `G(h) = h⁴sinh²h - (h²+9)(h cosh h - sinh h)²` — algebra only;
* the family `e^{2y}u - e^y v - w` (`u`, `w` cubic, `v` quartic) is **closed under
  differentiation**, via `u ↦ 2u+u'`, `v ↦ v+v'`, `w ↦ w'`, so one `HasDerivAt` lemma with 13
  parameters covers all eight steps;
* `Φ⁽ʲ⁾(0) = 0` for `j ≤ 7`, and
  `Φ⁽⁸⁾(y) = 256e^{2y}(y³+2y²-2y+10) - e^y(y⁴+32y³+352y²+1600y+2504)`;
* dividing `Φ⁽⁸⁾` by `e^y` and using **three** terms `e^y ≥ 1+y+y²/2` leaves
  `128y⁵+511y⁴+480y³+928y²+448y+56`, every coefficient positive.

So: no certificate, no series manipulation, one `ring` identity and eight applications of
"vanishes at `0`, has nonnegative derivative".  The only analysis left is the limit
`sinh h/h → 1` at `0⁺`, which is just the derivative of `sinh` at `0` read through
`hasDerivAt_iff_tendsto_slope`.

---

## 6c. Conjecture `interior`: the complex-analytic half

The remaining target is Sendov's conjecture in the interior itself, for `n ≥ 5`: a counterexample
gives the four identities of the blog post's Lemma 1, those give `(1Q)` and `(origin-exact)`, and
`Sendov.polar_origin_incompatible` closes it.  The blog signposts the split — *"the polynomial `p`
will play no further role"* — so the interface between the two stages is a structure carrying the
identities and the disk hypotheses, and nothing else.

**Multisets throughout.**  Roots arrive from Mathlib as a `Multiset`, repeated roots must be
allowed, and the alternative — indexing by `Fin (n-1)` — pays a bookkeeping tax at every step.
This decision already paid off twice; see below.

### Constraints from the later stages

Two plans for later stages (`n ≤ 4`, and the boundary case `a = 1`) constrain how this stage
should be built, and both were read before any of it was written:

* The low-degree argument for `2 ≤ n ≤ 5` branches off **immediately after the exact polar
  identity**, using only the Möbius bound and the integral triangle inequality — not the
  `x`-relaxation.  So the polar channel must expose

    `1 ≤ ∫₀¹ ∏ⱼ |a + t(1-a²)qⱼ| dt`

  as a named intermediate: high degree relaxes it by AM–GM to `(1Q)`, low degree bounds each
  factor by `a + (1-a²)t`.  Do not fuse those steps.
* The boundary case must **not** be forced into a structure carrying `a < 1`, and does not use
  the polar identity at all (it degenerates at `a = 1`).  So the factorization layer — roots,
  critical points, `|zⱼ| ≤ 1`, `|1 - wⱼ| ≥ 1`, the two factorizations — must be
  hypothesis-light, with `a < 1` and `a ≠ 0` entering only above it.

Also worth knowing: the low-degree argument covers `2 ≤ n ≤ 5`, so degree 5 could eventually be
dropped from the finite-certificate machinery.

### Two informal proofs that got shorter

Both prerequisites turned out to need far less than the write-up suggests, and in both cases
because the multiset formulation made the right induction available.

* **Maclaurin's inequality** (`e_{N-1} ≤ N μ^{N-1}`) normally comes from Newton's inequalities,
  which need real-rootedness of derivatives via Rolle.  The top case does not: splitting off one
  element and applying the inductive hypothesis and AM–GM leaves `1 + N(w-1) ≤ wᴺ`, which is
  Bernoulli.  AM–GM for multisets is proved the same way rather than imported — Mathlib states it
  for `Finset`-indexed families — and its step is Bernoulli at exponent `N+1`, so the two proofs
  share their only ingredient and the file imports no AM–GM at all.
* **The defect lemma** is proved in the write-up by setting `‖wⱼ‖ = e^{-aⱼ}`, computing
  `‖wⱼ⁻¹ - conj wⱼ‖ = 2 sinh aⱼ` and using superadditivity of `sinh`.  Splitting off one point
  instead leaves `1 - r²P² - [P(1-r²) + r(1-P²)] = (1-r)(1-P)(1-rP) ≥ 0`.  No `sinh`, no
  logarithms.  The origin `wⱼ = 0`, which the informal proof reaches by a limiting argument, needs
  no separate treatment: the pointwise fact `‖w‖·‖w⁻¹ - conj w‖ ≤ 1 - ‖w‖²` is true there as an
  inequality, because the left side carries a factor `‖w‖` that kills Lean's junk `0⁻¹`.

Neither statement mentions anything Sendov-specific; both are candidates for upstreaming.

---

## 7. Open work

Items 1–4 (packing bridge, degrees 9–100, composition, the analytic `n ≥ 101` argument) are
all **done**; see §2.  What remains is assurance work, not mathematics:

1. **Mutation test** — *done*, `scripts/mutation_test.sh`.  Five load-bearing data are each
   corrupted in turn (a Bernstein identity coefficient, a coefficient of the certified
   polynomial, a moment datum, the endgame constant, a monotonicity coefficient) and every one
   breaks the build.  See §7b for what the first run got wrong.
2. **Clean rebuild** from the pinned toolchain in a fresh clone.
3. **Line-length and style lint** across the generated files (currently the generators emit
   some lines past 100 characters).

### The large-degree argument as actually taken

The informal write-up's §4–§7 were followed in outline but not in detail, because using the
*sharp* Beta constant `6/((r+1)(r+2)(r+3)(r+4))` instead of `6/r⁴` changes what has to be
proved — and makes almost all of it easier.

* With `r = (n-4)/2` the product is `(n-2) n (n+2)(n+4)/16`, and the `n(n-2)` cancels the
  `n(n-2)` in the prefactor of `R` **exactly**.  The first tail term collapses to the rational
  function `24 (n-1-2α)²/((3+α) c⁴ (n-1)(n+2)(n+4))`.  The write-up's degree-8 positivity
  certificate `(18)` is for the `6/r⁴` version and is not needed.
* The write-up's `(16)` claims the first tail term decreases outright.  It does not: at
  `α = 17` the factor `(n-1-2α)²/((n-1)(n+2)(n+4))` *increases* up to `n ≈ 108`, by 0.37%.
  It is `c⁴` in the denominator that pays for this — `c` rises from `0.405` to `0.416` over
  the same span, an 11% gain.  Rather than couple the two, a flat 1% allowance is taken and
  discharged by its own certificate (`tail1_poly`); the 1% costs `0.0018` of margin.
* The `√B` in the geometric step is replaced by the rational bound `√B ≤ 12/13`
  (since `B ≤ 17/20 ≤ (12/13)²`), which keeps the step ratio rational: `0.961 < 1`.  Writing
  `B^((n-4)/2)` as `(√B)^(n-4)`, a *natural* power, turns §4 into an ordinary induction on `n`
  with no `rpow` reasoning at all.
* §7's split of `[0,17]` at `α = 16` is unnecessary.  Clearing denominators by
  `865200 (3+α)^49 γ⁴`, `γ = 300 + 47α - α²`, makes the whole of `Ut α < 1` a single
  degree-58 polynomial positivity, and its Bernstein certificate on `[0,17]` has **all 59
  coefficients positive**.  One `ring` call and one case split.

Margins on the final bound: `Ut(0) = 0.3305`, `Ut(8) = 0.3456`, `Ut(16) = 0.7598`,
`Ut(17) = 0.9229`.  The peak is at the endpoint `α = 17`, with 7.7% of room — against the
0.15% the write-up's route leaves at the same point.

---

## 7a. What the two workstreams share

The finite range (A) and the large-degree argument (B) are independent strategies but rest on
the same foundation, now collected under `Sendov/Common/`:

* `Common/Basic.lean` — `Q_eq` (the sum-of-squares form) and `Q_nonneg` are exactly `(5)` of
  the large-degree write-up; `Q_one` is its `(6)`; and `R_le_of_integral_le` is the shape of
  *both* arguments, since each proceeds by bounding the integral and then bounding `R`.
* `Common/Rpow.lean` — `continuous_integrand` is used by A to compare integrals and is what B
  needs to split `∫₀¹` at the vertex of `Q`; `rpow_add_nat_pos` serves the Beta integral and
  the `B^((n-4)/2) = B^k √B` reduction alike; `rpow_le_rpow_of_le_one` drops the `√B`.

Before this was factored out, `LargeDegree/Beta.lean` imported `FiniteRange/Basic.lean` —
B depending on A, which is backwards.  Both now depend only on `Common`.

---

## 7b. Gotchas

Bugs met while building this, all of which produced *plausible-looking* wrong output.  They
are recorded because each cost real time and several would have silently corrupted a
certificate.

* **Python integer division in a symbolic expression.**  `1/(2*M0)` with `M0` a plain Python
  `int` is float division; sympy then carries floats through the whole computation.  Worse,
  `sp.Integer(x)` *truncates* a float without complaint, so the corrupted coefficients looked
  like clean integers and the Bernstein check still reported "all positive".  Caught only by
  asserting that the denominator had the expected form `C·(3+α)^p`.  Use `sp.Rational(1, 2*M0)`
  and assert `c.is_Rational` on every coefficient.

* **A dropped factor of `2ˡ`.**  In `(-2c)ˡ` the `2ˡ` cancels against the denominator of `c`,
  so the denominator is `Mⁱ`, not `(2M)ˡ M^(i-l)`.  The resulting `P` was wrong by sign and
  scale yet still admitted a Bernstein representation — with every coefficient negative.
  **Positivity of a certificate is not evidence that `P` is right.**

* **`sympy.simplify` returning a false mismatch.**  Comparing two large rational expressions,
  `simplify(lhs - rhs) == 0` reported `False` when they were in fact equal; it had simply
  failed to reduce.  A symbolic "not equal" from a CAS is weak evidence.  Numerical agreement
  at several points, or exact evaluation at several rational points, is strong.

* **`sympy.nsimplify` on an exact rational.**  Applied to a `Rational` it "simplified" it into
  radicals — `32768·2^(29/52)·3^(6/13)·…` — producing unparseable Lean.  Use `.p` and `.q`.

* **Comparing two routes with different denominators.**  The packed and multinomial routes
  carry different powers of `(3+α)`, so their numerators differ by a factor of `(3+α)`, not by
  a constant.  A "compare up to scale" check fails spuriously.

* **Shell and encoding.**  Backticks inside a docstring passed through `python -c "..."` are
  substituted by bash, mangling generated Lean.  Python on Windows writes CRLF unless
  `newline="
"` is given, and Lean rejects isolated carriage returns.  `/tmp` in Git Bash is
  not `/tmp` to Windows Python.

* **A certificate interval that the hypotheses do not justify.**  The batch generator fixed
  the Bernstein interval at `[0,17]`, but feasibility only gives `α ≤ (n-1)/2`, which is
  `2.5` for the `[6,6]` batch and `8.5` for `[16,18]`.  On `[0,17]` the polynomial genuinely
  is not positive there (`A₆(17) = -5.8`), so the low batches failed — correctly.  The
  interval must be `min(17, (n₁-1)/2)`, and the batch theorem must *derive* `α ≤ U` from
  `alpha_le_half_M` rather than from the ambient `α ≤ 17`.  Nothing unsound resulted, but the
  failure looked like a certificate-quality problem when it was a hypothesis-scope problem.

* **A hypothesis that propagates the wrong way.**  The batch bound was originally stated with
  feasibility `c² ≤ A` required *at `n₀`*.  Feasibility propagates *upward* in `n` (since `A`
  increases), so it cannot be inherited from the hypothesis at `n`, and for `n₀ ≲ 36` it does
  not follow from `α ≤ 17` either.  The fix was to weaken what is actually needed: `Q ≤ 1`
  only requires `0 ≤ c`, because `Q t - 1 = t(A t - 2c)` and `Q 1 = B < 1` already gives
  `A ≤ 2c`, whether or not `A ≥ 0`.  Nonnegativity of `Q` at `n₀` then comes free from
  `Q_anti`.  Worth generalising a lemma before generating thirty files that need it.

* **Memory, not time, is the build limit.**  Rebuilding all 31 batch files simultaneously
  makes Lean exit with `0xC0000409` and spurious `failed to read file ...olean` errors — an
  out-of-memory failure that reads like corruption.  Each file builds fine alone.  Lake in
  this toolchain has no `--jobs` flag, so the workaround is to build in explicit groups
  (`scripts/staged_build.sh`).  Note any edit to `Defs.lean`, even to a docstring,
  invalidates every one of them.

* **Backslashes vanishing between the shell and Python.**  Passing a Python patch script
  through a heredoc silently collapsed `\\n` to `\n`, so string replacements aimed at
  generator source either failed to match or wrote a literal newline into a string literal.
  The generated Lean then still compiled, with the wrong linear form in a certificate.
  Write patch scripts to a file rather than piping them through a shell.

* **Half of a generated certificate is inert.**  Each Bernstein coefficient `Gⱼ` appears twice:
  in `have hⱼ : 0 ≤ Gⱼ αʲ (U-α)^(d-j)` and in the identity `hid`.  Corrupting the *first* is
  undetectable — `linarith` uses those hypotheses only as "this quantity is nonnegative", and
  a positive rescaling of a nonnegative quantity is still nonnegative.  The first mutation
  test run reported two certificates as "not load-bearing" for exactly this reason; the
  content is all in `hid`.  (Module docstrings quoting a coefficient add a third occurrence,
  which is inert for the same trivial reason.)  `scripts/mutation_test.sh` therefore names the
  occurrence index, and a reviewer reading a generated file should know that the `have` block
  is bookkeeping, not evidence.

* **`field_simp` distributes across an integral.**  In `Reduction/Simplified.lean` the goal
  contained `∫₀¹ t³ β(t)^r dt` as an opaque atom multiplied by a rational coefficient.
  `field_simp` cleared denominators *through* the atom, producing a goal `ring` could not
  close and a several-hundred-character error that reads like a mismatch.  The fix is to
  prove the scalar identity separately and finish with a division-free `ring`, so the atom is
  only ever multiplied, never distributed over.  The same reflex applies to
  `LargeDegree/Endgame.lean`, where `field_simp` on `D(1 - Ut)` produced a degree-115 identity
  in place of the degree-58 one that was wanted.

* **A true rewrite that breaks a later match.**  `ax = 1 - β(1)/2 - α/(n-1)` is an identity,
  but `rw`-ing it into the origin inequality also rewrites the `a * x` *inside*
  `∫₀¹ t β(t)^r dt`.  The integral is then a different atom from the one in the bound being
  combined with it, and `linarith` fails with no indication why.  Passing the identity to
  `linarith` as a hypothesis instead leaves the integral opaque.  General rule: when an
  integral is being treated as an atom, rewrite *around* it, never *into* it.

* **A section `variable` can shadow a global definition.**  `variable {c A t : ℝ}` in
  `Common/Quadratic.lean` shadows `Sendov.c` and `Sendov.A`, so `Q n α t = QQ (c n α) (A n α) t`
  stops parsing — and reports "Function expected", not a name clash.  Any lemma mentioning the
  globals has to come before the `variable` line.

* **`norm_num` normalises a fraction out of matchable shape.**  `1/(c²((r+1)(r+2)))` becomes
  `(r+2)⁻¹(r+1)⁻¹(c²)⁻¹`, which no longer matches the lemma statement it came from.  Rewriting
  only the specific cast that needs it (`show ((1:ℕ):ℝ) + 1 = 2`) is stable where
  `norm_num at h` is not.

* **`hasDerivAt_id` produces `id`, not `fun x => x`.**  `simpa` then normalises the goal into
  point-free form (`(fun x ↦ exp x - 1) - id - …`) and fails to match.  `hasDerivAt_id'`
  together with `HasDerivAt.congr_deriv` is the robust idiom; probe it in a scratch file
  before generating 250 lines against it.

* **The editor competes with the build for memory.**  Beyond the batch-file case above: with
  `Common/Sinh.lean` open, the Lean LSP held 7.4 GB of 32 GB — it re-elaborates eight
  13-parameter `HasDerivAt` steps on every keystroke — and `lake build` began failing
  intermittently with `failed to read …olean.private` on *toolchain* files.  Same OOM, but it
  looks like a corrupted install.  A retry loop gets through it; restarting the Lean server
  fixes it properly.

* **`set` introduces a local *definition*, which `linarith` unfolds.**  After
  `set v := M n / (2*α) - 1`, goals that were linear in `v` became nonlinear in `α`, because
  `linarith`'s preprocessing zeta-reduces the binding.  `obtain ⟨v, hvdef⟩ : ∃ w, w = … :=
  ⟨_, rfl⟩` gives an opaque local instead.  The same binding also makes `rw … at h` appear to
  do nothing, since the term refolds.

* **`linarith` does not always evaluate `OfScientific` literals.**  `α / 2.7 ≤ 0.1852 * (2*α)`
  is linear in `α` with rational coefficients, but `linarith` failed on it; splitting out the
  numeric step with an explicit `div_le_iff₀` and letting `norm_num` see `2.7` on its own
  worked.  Decimal literals are fine inside `nlinarith` hint terms and in `norm_num` goals —
  it is the coefficient extraction that is fragile.

* **`rw` with a factorization loops against the thing being factored.**  `p = C p.leadingCoeff *
  (p.roots.map …).prod` cannot simply be rewritten into a goal that still mentions `p.roots` or
  `p.leadingCoeff` — the rewrite hits its own right-hand side.  Extracting the multiset first
  with `obtain ⟨z, hz⟩ : ∃ z, p.roots = a ::ₘ z := ⟨_, rfl⟩` gives an *opaque* local, after which
  the rewrite is one-directional and terminates.  `set` does not work here: it introduces a local
  definition that tactics unfold again — the same trap as in `Reduction/Alpha17.lean`, where it
  made `linarith` goals nonlinear.  `obtain … := ⟨_, rfl⟩` is the idiom in both cases.

* **Truncated `ℕ` subtraction inside an exponent.**  Stating the derivative evaluation as
  `(-1)^(card z - 1) * sumEraseProd z` is *wrong* at `card z = 1` and forces a case split at
  `z = 0`, because `card z - 1` truncates.  Writing it as `-((-1)^(card z) * sumEraseProd z)` —
  equal, since `((-1)^k)² = 1` — removes both, and the induction step closes by `ring`.

* **`convert` manufacturing instance goals that `exact` does not.**  Composing `HasDerivAt`
  across `ℝ → ℂ → ℂ` with `HasDerivAt.scomp` produces a derivative `f' • g'` and an
  `AddCommGroup ℂ` instance that is not syntactically the ambient one.  `convert … using 1`
  leaves both as goals; plain `exact` succeeds, because scalar multiplication of `ℂ` on `ℂ`
  *is* multiplication definitionally.  Try `exact` before reaching for `convert`.

* **`intervalIntegral.integral_congr` leaves a beta-redex.**  After `intro t _` the goal reads
  `(fun t ↦ …) t = (fun t ↦ …) t`, and `rw` will not match inside it.  `simp only []` beta-reduces
  and the rewrite then fires.  Relatedly, rewriting `← integral_const_mul` backwards leaves the
  constant as a metavariable and the instance search gets stuck; state the congruence as its own
  `have` and rewrite forwards.

The habit that caught all of these: validate generated data against an *independent*
computation — quadrature for moments, exact evaluation at several rational points for
identities — before writing any Lean.  `scripts/gen_moment.py` refuses to emit data that
fails its quadrature check.

## 8. Trust policy

No `sorry` (outside the stated goal), no `axiom`, no `native_decide`, no `unsafe`, no
floating point in any statement or proof. `maxHeartbeats` / `maxRecDepth` are raised in
generated files; these are resource knobs, not escape hatches, and are recorded here
deliberately.

`scripts/gen_degree.py` is untrusted: Lean re-derives `P n` and checks the Bernstein identity
with `ring`, so a corrupted coefficient fails the build. It writes `Degree{n}.lean` under
`Sendov/FiniteRange/` relative to the repo root, not the shell cwd. Its `--check` mode compares against
numerical quadrature, and that check has already caught a real bug — a dropped `2ˡ` in
`(-2c)ˡ` produced a `P` wrong by sign and scale which nevertheless admitted a Bernstein
representation, with every coefficient negative. **Positivity of a certificate is not
evidence that `P` is right**; only agreement with an independent evaluation is. Two
generators written in this project were silently wrong and caught only this way.
