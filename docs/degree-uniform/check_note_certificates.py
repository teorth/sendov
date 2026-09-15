"""Exact replay of the note's displayed formulas and coefficient data.
Requires SymPy; does not read Lean or prove the analytic majorizations.
"""
import ast
import copy
import json
import re
from pathlib import Path
import sympy as s

ROOT = Path(__file__).resolve().parent
a = s.Symbol('a')
values = {'a': a}
functions = {}


def expression(node, env):
    if isinstance(node, ast.Constant) and type(node.value) is int:
        return s.Integer(node.value)
    if isinstance(node, ast.Name):
        return env[node.id]
    if isinstance(node, ast.UnaryOp) and isinstance(node.op, (ast.UAdd, ast.USub)):
        v = expression(node.operand, env)
        return v if isinstance(node.op, ast.UAdd) else -v
    if isinstance(node, ast.BinOp):
        x, y = expression(node.left, env), expression(node.right, env)
        if isinstance(node.op, ast.Add): return x + y
        if isinstance(node.op, ast.Sub): return x - y
        if isinstance(node.op, ast.Mult): return x * y
        if isinstance(node.op, ast.Div): return x / y
        if isinstance(node.op, ast.Pow):
            assert y.is_Integer and 0 <= y <= 60
            return x ** y
    if isinstance(node, ast.Call) and isinstance(node.func, ast.Name) and not node.keywords:
        names, body = functions[node.func.id]
        assert len(names) == len(node.args)
        local = dict(values)
        local.update(zip(names, [expression(v, env) for v in node.args]))
        return expression(body, local)
    raise ValueError(f'Unsupported formula syntax: {ast.dump(node)}')


note = (ROOT / 'MATHEMATICAL_NOTE.md').read_text()
blocks = re.findall(r'```text\n(.*?)```', note, re.S)
assert len(blocks) == 2
statements = []
for block in blocks:
    for line in block.splitlines():
        if not line.strip(): continue
        if line.startswith(' '):
            statements[-1] += ' ' + line.strip()
        else:
            statements.append(line)
for statement in statements:
    left, right = statement.split('=', 1)
    left = left.strip()
    tree = ast.parse(right.strip().replace('^', '**'), mode='eval').body
    function = re.fullmatch(r'(\w+)\(([^)]*)\)', left)
    if function:
        functions[function[1]] = ([x.strip() for x in function[2].split(',')], tree)
    else:
        assert left not in values
        values[left] = expression(tree, values)


def exact_identity(poly, coefficients, degree, lower, upper, scale):
    assert len(coefficients) == degree + 1
    lhs = s.Poly(scale * poly, a, domain=s.QQ)
    x, y = s.Poly(a - lower, a), s.Poly(upper - a, a)
    rhs = sum((s.Integer(c) * x**i * y**(degree-i)
               for i, c in enumerate(coefficients)), s.Poly(0, a))
    return (lhs - rhs).is_zero


def check(data):
    expected = [('gap1', 2, 17, 53, 15**53),
                ('gapLow', 2, s.Rational(5, 2), 47, 1),
                ('gapHigh', s.Rational(5, 2), 17, 47, 29**47)]
    assert len(data['certificates']) == len(expected)
    rows = []
    for record, (name, lo, hi, degree, scale) in zip(data['certificates'], expected):
        assert (record['gap'], s.Rational(record['lower']), s.Rational(record['upper']),
                record['degree'], int(record['scale'])) == (name, lo, hi, degree, scale)
        coefficients = [int(c) for c in record['coefficients']]
        assert all(c > 0 for c in coefficients)
        poly = s.Poly(s.cancel(values[name]), a, domain=s.QQ)
        assert exact_identity(poly.as_expr(), coefficients, degree, lo, hi, scale), name
        factors = record['low_degree_homogenizations']
        for factor, item in factors.items():
            assert factor.endswith('H')
            assert exact_identity(values[factor[:-1]], item['coefficients'],
                                  item['degree'], lo, hi, int(item['scale'])), factor
        rows.append({'gap': name, 'degree': degree, 'identity': True,
                     'coefficients': len(coefficients), 'factor_identities': len(factors),
                     'factor_coefficients': sum(len(x['coefficients']) for x in factors.values())})
    return rows


def main():
    data = json.loads((ROOT / 'CERTIFICATES.json').read_text())
    rows = check(data)
    rejected = []
    for i, record in enumerate(data['certificates']):
        mutant = copy.deepcopy(data)
        j = record['degree'] // 2
        mutant['certificates'][i]['coefficients'][j] = str(int(record['coefficients'][j]) + 1)
        try:
            check(mutant)
        except AssertionError:
            rejected.append(record['gap'])
        else:
            raise AssertionError('Interior-coefficient mutation was accepted')
    assert sum(x['coefficients'] for x in rows) == 150
    assert sum(x['factor_coefficients'] for x in rows) == 71
    result = {'status': 'PASS', 'sympy_version': s.__version__, 'identities': rows,
              'interior_coefficient_mutants_rejected': rejected,
              'scope': 'Exact rational polynomial identities from displayed note formulas and JSON; not an analytic proof or Lean replay.'}
    (ROOT / 'CERTIFICATE_REPLAY.json').write_text(json.dumps(result, indent=2) + '\n')
    print(json.dumps(result, indent=2))


if __name__ == '__main__':
    main()
