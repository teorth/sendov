"""Exact input validation for the selected finite certificate renderer.

The rational envelope checks adapt Senjian An's MIT-licensed verify_paper.py,
SJanPerth/Sendov-Proof-Distillation, e8ae601491ec171ab4f7f8456113dd6a047aa85d.
Copyright (c) 2026 Senjian An; see LICENSE-DISTILLATION-MIT.txt.
Schema/coverage validation and integration changes: Apache-2.0.
No sampled arithmetic and no Python assertions authorize generation.
"""
from fractions import Fraction as F
import json
from pathlib import Path


def require(condition, message):
    if not condition:
        raise ValueError(message)


def object_pairs(pairs):
    result = {}
    for key, value in pairs:
        require(key not in result, f'duplicate JSON key: {key}')
        result[key] = value
    return result


def reject_constant(value):
    raise ValueError(f'non-finite JSON constant: {value}')


def fields(obj, keys, context):
    require(type(obj) is dict and set(obj) == set(keys.split()),
            f'{context}: wrong object fields')


def rational(value):
    require(type(value) is str, 'rational must be a string')
    try:
        result = F(value)
    except (ValueError, ZeroDivisionError) as error:
        raise ValueError(f'invalid rational: {value}') from error
    require(str(result) == value, f'noncanonical rational: {value}')
    return result


def eta(a):
    u = a / (a + 3)
    return u - u**3 / 30


def candidate_squared(m, j, lo, hi):
    """The paper's exact squared bracket envelope, not a floating root check."""
    ratio = F(1, 3) if lo == 0 else eta(lo) / lo
    kappa = F(m*m - 1, 4*m) * ratio * (m - 2*lo)**2
    node = F(4, 25) + F(3, 5)*eta(hi) + F(12, 25*m)*hi
    require(0 < node < 1, 'invalid chord node')
    if j == 0:
        chord = 96*F(3, 5)**4 / ((m-1)*(m+1)*(m+3)*(m+5))
        return (kappa*chord / (1-node)**4)**2
    if j == 1:
        return (F(259, 3125)*kappa)**2 * node**(m-3)
    return (F(421, 3125)*kappa)**2 * eta(hi)**(m-3)


def load_table(path, coefficients):
    rows = json.loads(Path(path).read_text(encoding='utf-8'),
                      object_pairs_hook=object_pairs, parse_constant=reject_constant)
    require(type(rows) is list and len(rows) == 77, 'exactly 77 rows required')
    for m, row in zip(range(5, 82), rows):
        fields(row, 'm e components total', f'row {m}')
        require(type(row['m']) is int and row['m'] == m,
                'rows must be m=5..81 exactly once in order')
        e = rational(row['e'])
        require(e == F(1, 4) + F(7, 12*m), f'E budget mismatch at {m}')
        parts = row['components']
        require(type(parts) is list and len(parts) == 3, 'exactly three components required')
        total = e
        for j, part in enumerate(parts):
            fields(part, 'index k lo hi u sq sign_lo sign_hi', f'{m}, component {j}')
            require(type(part['index']) is int and part['index'] == j,
                    'components must be 0..2 exactly once in order')
            require(type(part['u']) is int and part['u'] > 0, 'positive integer budget required')
            require(type(part['k']) is str, 'bracket classification must be a string')
            lo, hi = rational(part['lo']), rational(part['hi'])
            require(0 <= lo <= hi <= min(F(17), F(m, 2)), 'bracket outside domain')
            boundary = m >= (49, 47, 57)[j]
            if boundary:
                require(part['k'] == 'B' and lo == hi == 17, 'boundary classification mismatch')
            else:
                k = rational(part['k'])
                require(k.denominator == 1 and lo == k/4 and hi == (k+1)/4,
                        'quarter bracket mismatch')
            p = coefficients(m, j)
            left = sum(c * lo**i for i, c in enumerate(p))
            right = sum(c * hi**i for i, c in enumerate(p))
            require(left == rational(part['sign_lo']) and right == rational(part['sign_hi']),
                    'stored sign-value mismatch')
            if boundary:
                require(left > 0 if j == 0 else left < 0, 'boundary sign mismatch')
            else:
                require((left > 0 and right < 0) if j == 0 else (left < 0 and right > 0),
                        'isolating sign mismatch')
            square = candidate_squared(m, j, lo, hi)
            require(square == rational(part['sq']), 'stored squared envelope mismatch')
            budget = F(part['u'], 1000)
            require(square < budget**2, 'component budget does not bound envelope')
            total += budget
        require(total == rational(row['total']), 'total budget mismatch')
        require(total < F(199, 200), 'finite bound failed')
        if m == 81:
            require(total < F(2, 3), 'tail base bound failed')
    return rows
