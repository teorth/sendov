import io
from pathlib import Path
PLAN = [(6,6),(8,9),(10,11),(12,13),(14,15),(16,18),(18,20),(20,22),(22,24),(24,26),
        (26,27),(28,29),(30,31),(32,33),(34,35),(36,37),(38,39),(40,41),(42,43),(44,45),
        (46,47),(48,49),(50,51),(52,53),(54,55),(56,58),(58,60),(60,63),(64,69),(70,79),
        (80,100)]

# Each degree 5..100 must be covered; 5 and 7 come from the single-degree files.
cov = {5: "five", 7: "seven"}
for n0, n1 in PLAN:
    for n in range(n0, n1 + 1):
        cov.setdefault(n, (n0, n1))
missing = [n for n in range(5, 101) if n not in cov]
assert not missing, f"degrees not covered: {missing}"

# Walk 5..100 and collect maximal runs handled by the same source.
runs, cur = [], None
for n in range(5, 101):
    src = cov[n]
    if cur and cur[0] == src:
        cur[2] = n
    else:
        cur = [src, n, n]
        runs.append(cur)

L = []
for i, (src, lo, hi) in enumerate(runs):
    last = (i == len(runs) - 1)
    L.append(f"  -- degrees {lo}..{hi}")
    ind = "  " if last else "  · "
    cont = "  " if last else "    "
    if not last:
        L.append(f"  rcases Nat.lt_or_ge n {hi + 1} with h | h")
    if src in ("five", "seven"):
        L.append(f"{ind}obtain rfl : n = {lo} := by omega")
        L.append(f"{cont}exact finite_range_{src} hα hfeas")
    else:
        n0, n1 = src
        L.append(f"{ind}exact B{n0}_{n1}.finite_range (by omega) (by omega) hα hα' hfeas")

head = """/-
Copyright (c) 2026 Terence Tao. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Terence Tao
-/
"""
imports = ("import Sendov.FiniteRange.Degree5\nimport Sendov.FiniteRange.Degree7\n"
           + "".join(f"import Sendov.FiniteRange.Degree{a}_{b}\n" for a, b in PLAN))
doc = """
/-!
# The finite range `5 ≤ n ≤ 100`

This file does nothing but assemble the individual degree files and the degree *batches* into
a single statement.  Its only content is the case split, so it is also where the claim "every
degree in the range is covered" gets checked: the branches below are generated from the batch
plan, and the file would not compile if a degree were skipped.

Degrees `5` and `7` are handled one at a time (`Sendov.finite_range_five`,
`Sendov.finite_range_seven`); every other degree is covered by a batch `B n₀ n₁`, whose proof
is a single Bernstein certificate valid simultaneously for all `n₀ ≤ n ≤ n₁`.
-/

namespace Sendov

variable {α : ℝ}

/-- **The finite range.**  Every degree from `5` to `100` inclusive. -/
theorem finite_range_le_100 {n : ℕ} (h0 : 5 ≤ n) (h1 : n ≤ 100)
    (hα : 0 ≤ α) (hα' : α ≤ 17) (hfeas : c n α ^ 2 ≤ A n α) : R n α < 1 := by
"""
tail = '''

/-- **The finite-range claim.**  The right-hand side of equation `stat` of the blog post is
strictly less than `1` on the range of degrees and of `α` left open there, that is, on
`5 ≤ n ≤ 97`, `0 ≤ α ≤ 17`, subject to the feasibility constraint `c ^ 2 ≤ A`.

This is the original challenge statement.  It is a special case of `finite_range_le_100`,
which covers three more degrees: the finite certification was pushed from `97` to `100` so
that it meets the large-degree argument of `Sendov.LargeDegree` with room to spare. -/
theorem finite_range (n : ℕ) (α : ℝ) (hn : 5 ≤ n) (hn' : n ≤ 97)
    (hα : 0 ≤ α) (hα' : α ≤ 17) (hfeas : c n α ^ 2 ≤ A n α) :
    R n α < 1 :=
  finite_range_le_100 hn (by omega) hα hα' hfeas

/-- Equation `stat` of the blog post is infeasible on the range
`5 ≤ n ≤ 97`, `0 ≤ α ≤ 17`, `c ^ 2 ≤ A`.  This is the form in which the claim is used. -/
theorem finite_range_contradiction (n : ℕ) (α : ℝ) (hn : 5 ≤ n) (hn' : n ≤ 97)
    (hα : 0 ≤ α) (hα' : α ≤ 17) (hfeas : c n α ^ 2 ≤ A n α) (hstat : 1 ≤ R n α) :
    False :=
  absurd hstat (not_le.2 (finite_range n α hn hn' hα hα' hfeas))

end Sendov
'''
src = head + imports + doc + "\n".join(L) + tail
io.open(Path(__file__).resolve().parents[1] / "Sendov" / "FiniteRange" / "Cover.lean", "w",
        encoding="utf-8", newline="\n").write(src)
print(f"{len(runs)} branches covering degrees 5..100")
