#!/usr/bin/env python3
"""Regenerate the bounded DI02 per-degree Lean arithmetic certificates.

The Fraction/sqrt code is an untrusted witness generator. Each emitted
row proves the binomial values, squared envelope, and actual coefficient bound in
Lean. No generated numerical result is accepted as an axiom.
"""
from fractions import Fraction as Q
from math import comb, isqrt
from pathlib import Path
import json

ROOT = Path(__file__).resolve().parents[1]


def coeff_bound_sq(m, k, v):
    if k == m:
        return v ** m
    return Q(m ** m, k ** k * (m - k) ** (m - k)) * v ** k


def sqrt_upper(x, den):
    assert x >= 0 and den > 0
    n = isqrt(x.numerator * den * den // x.denominator)
    if Q(n * n, den * den) < x:
        n += 1
    r = Q(n, den)
    assert r * r >= x
    return r

DEN = 10**12
rows = []
witnesses = []
for k in range(3, 101):
    divisor = comb(100, k) * Q(7, 10)**k
    sq = coeff_bound_sq(100, k, Q(9, 100)) / divisor**2
    envelope = sqrt_upper(sq, DEN)
    actual = Q(0) if k % 2 else Q(comb(50, k//2)) * Q(3, 10)**k / divisor
    rounded_actual = Q((actual.numerator * DEN + actual.denominator - 1)//actual.denominator, DEN)
    expected_g = {3:410439009, 4:38153285, 5:3927325, 6:440942, 7:53400,
                  8:6917, 9:952, 10:139, 11:22, 12:4}.get(k, 1)
    expected_a = 0 if k % 2 else {4:10539189, 6:101883, 8:1409, 10:26}.get(k, 1)
    assert envelope == Q(expected_g, DEN) and rounded_actual == Q(expected_a, DEN)
    witnesses.append(dict(k=k, normalized_C_square=str(sq), envelope=str(envelope),
                          actual=str(actual), actual_envelope=str(rounded_actual)))
    rows.append(f'''private lemma generic_{k} : C 100 {k} (9/100) /
    (((100 : ℕ).choose {k} : ℝ) * (7/10)^{k}) ≤ (genericNumerator {k} : ℝ) / 10^12 := by
  apply normalized_C_le 100 {k} (9/100) (7/10) _ (by decide) (by decide)
    (by norm_num) (by positivity)
  have hc : (100 : ℕ).choose {k} = {comb(100,k)} := by
    rw [Nat.choose_eq_factorial_div_factorial (by decide)]
    norm_num [Nat.factorial]
  norm_num [genericNumerator, hc]
''')
    actual_proof = f'''  rw [esymm_exact {k} (by decide)]
'''
    if k % 2:
        actual_proof += '  norm_num [actualNumerator]\n'
    else:
        actual_proof += f'''  have hc : (100 : ℕ).choose {k} = {comb(100,k)} := by
    rw [Nat.choose_eq_factorial_div_factorial (by decide)]
    norm_num [Nat.factorial]
  have hd : (50 : ℕ).choose {(100-k)//2} = {comb(50,(100-k)//2)} := by
    rw [Nat.choose_eq_factorial_div_factorial (by decide)]
    norm_num [Nat.factorial]
  norm_num [hc, hd, actualNumerator, norm_mul, norm_pow, norm_div]
'''
    rows.append(f'''private lemma actual_{k} : ‖r.esymm {k}‖ /
    (((100 : ℕ).choose {k} : ℝ) * (7/10)^{k}) ≤ (actualNumerator {k} : ℝ) / 10^12 := by
{actual_proof}''')

for kind in ['generic', 'actual']:
    numerator = 'C 100 k (9/100)' if kind == 'generic' else '‖r.esymm k‖'
    rows.append(f'''lemma {kind}_rows (k : ℕ) (hk : k ∈ Finset.Ico 3 101) :
    {numerator} / (((100 : ℕ).choose k : ℝ) * (7/10)^k) ≤
      ({kind}Numerator k : ℝ) / 10^12 := by
  obtain ⟨hlo, hhi⟩ := Finset.mem_Ico.mp hk
  interval_cases k
'''+''.join(f'  · exact {kind}_{k}\n' for k in range(3,101)))
assert len(witnesses) == 98 and len({w['k'] for w in witnesses}) == 98
path = ROOT/'tests/PaperCenteredHundred.lean'
text = path.read_text()
start = '-- BEGIN GENERATED COEFFICIENT CERTIFICATES\n'
end = '-- END GENERATED COEFFICIENT CERTIFICATES'
assert text.count(start) == 1 and text.count(end) == 1
path.write_text(text.split(start)[0]+start+'\n'.join(rows)+'\n'+end+text.split(end)[1])
manifest = ROOT/'tests/data/di02-witnesses.json'
manifest.parent.mkdir(parents=True, exist_ok=True)
manifest.write_text(json.dumps(dict(degrees=98, denominator=DEN,
    generic_sum=str(sum(Q(w['envelope']) for w in witnesses)),
    actual_sum=str(sum(Q(w['actual_envelope']) for w in witnesses)), rows=witnesses), indent=2)+'\n')
print(json.dumps(dict(degrees=len(witnesses), lean=str(path), manifest=str(manifest))))
