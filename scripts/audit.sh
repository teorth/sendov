#!/bin/sh
# Trust audit for the Sendov development.  See docs/design.md for the policy.
#
#   1. no forbidden tokens anywhere in Sendov/ or in Solution.lean
#   2. Challenge.lean holds exactly the two deliberate holes it is supposed to
#   3. the top-level results depend on the three standard axioms only
#
# Resource knobs (maxHeartbeats / maxRecDepth) are listed, not flagged: they are recorded
# deliberately and are not escape hatches.
cd "$(dirname "$0")/.." || exit 1
rc=0

echo "=== 1. forbidden tokens ==="
# Challenge.lean is excluded here and audited separately in step 2: it is the Palomar
# statement of record, and Comparator requires its declarations to be deliberate holes.
hits=$(grep -rnE '\bsorry\b|^ *axiom |native_decide|\bunsafe \b|Float' \
         Sendov/ Solution.lean --include=*.lean | grep -vE ':[0-9]+: *--' | grep -vE '`sorry`')
# These pre-existing helpers manipulate Lean syntax only. Their generated proofs
# are checked by Lean; arbitrary mathematical partial definitions remain forbidden.
partial_hits=$(grep -rnE '\bpartial def\b' Sendov/ Solution.lean --include=*.lean | grep -vE \
'^(Sendov/Common/BernsteinRing\.lean:[0-9]+:private partial def flatten \(e : Expr\) \(op : Name\) : Array Expr :=|Sendov/Common/BernsteinCert\.lean:[0-9]+:private partial def factors \(e : Expr\) : Array Expr :=|Sendov/Common/BernsteinCert\.lean:[0-9]+:private partial def reify \(e x y : Expr\) : TacticM \(TSyntax `term × Nat\) := do)$')
if [ -n "$partial_hits" ]; then
  hits="${hits}${partial_hits}"
fi
if [ -n "$hits" ]; then
  echo "$hits"
  rc=1
else
  echo "none"
fi

echo
echo "=== 2. Challenge.lean: deliberate holes only ==="
# The Challenge states the result and does not prove it; Comparator checks that Solution
# supplies proofs of exactly these statements.  Two holes, one per compared theorem, and
# nothing else forbidden.
holes=$(grep -cE '\bsorry\b' Challenge.lean)
other=$(grep -nE '^ *axiom |native_decide|\bunsafe \b|\bpartial def\b|Float' Challenge.lean \
          | grep -vE ':[0-9]+: *--')
echo "deliberate holes: $holes (expected 2, one per compared theorem)"
if [ "$holes" != "2" ] || [ -n "$other" ]; then
  echo "$other"
  echo "!! Challenge.lean does not have exactly its two deliberate holes"
  rc=1
fi

echo
echo "=== 3. resource knobs in use (informational) ==="
grep -rn "set_option max" Sendov/ --include=*.lean \
  | sed 's/:.*set_option/  set_option/' | sort | uniq -c | sort -rn | head -20

echo
echo "=== 4. axioms of the top-level results ==="
if out=$(lake env lean scripts/axioms.lean 2>&1); then
  :
else
  echo "!! Lean axiom query failed"
  rc=1
fi
echo "$out"
if echo "$out" | grep -qE "sorryAx|ofReduceBool|ofReduceNat"; then
  echo "!! non-standard axiom present"
  rc=1
fi

echo
echo "=== audit finished (rc=$rc) ==="
exit $rc
