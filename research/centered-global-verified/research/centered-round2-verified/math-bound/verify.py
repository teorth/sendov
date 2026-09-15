#!/usr/bin/env python3
"""Exact constant/identity replay; NOT a numerical proof over a grid.

All arithmetic is integer or Fraction. The quantified analytic arguments are
in PROOF.md. No filesystem writes, imports of project caches, or dependencies.
"""
from fractions import Fraction as Q
from math import comb

checks = []


def check(name, proposition):
    if not proposition:
        raise AssertionError(name)
    checks.append(name)
    print('PASS:', name)


def add(a, b):
    c = [Q(0)] * max(len(a), len(b))
    for i, x in enumerate(a):
        c[i] += x
    for i, x in enumerate(b):
        c[i] += x
    return trim(c)


def mul(a, b):
    c = [Q(0)] * (len(a) + len(b) - 1)
    for i, x in enumerate(a):
        for j, y in enumerate(b):
            c[i+j] += x*y
    return trim(c)


def scale(a, x):
    return trim([x*y for y in a])


def trim(a):
    while len(a) > 1 and not a[-1]:
        a.pop()
    return a


def power(a, n):
    out = [Q(1)]
    for _ in range(n):
        out = mul(out, a)
    return out


def shift(a, x):
    out = [Q(0)]
    for k, coefficient in enumerate(a):
        out = add(out, scale(power([Q(x), Q(1)], k), coefficient))
    return out


def integrate01(a):
    return sum((x/Q(i+1) for i, x in enumerate(a)), Q(0))


def nonnegative_shift(name, polynomial, expected, origin=7):
    actual = shift(polynomial, origin)
    check(name + ' identity', actual == [Q(x) for x in expected])
    check(name + ' nonnegative coefficients', all(x >= 0 for x in actual))


# Structural coefficient sum telescopes: verify its general summand identity
# after multiplication by k(k-1)(k-2).
k = [Q(0), Q(1)]
km1, km2 = [Q(-1), Q(1)], [Q(-2), Q(1)]
lhs = add(scale(k, 2), [Q(1)])
rhs = add(add(scale(mul(k, km1), 2), scale(k, Q(1, 2))),
          add(scale(mul(k, km2), -2), scale(km2, Q(-1, 2))))
check('S3 telescoping general summand polynomial', lhs == rhs)
check('S3 initial telescoping endpoint', Q(2) + Q(1, 4) == Q(9, 4))

nonnegative_shift('order-4 endpoint', [6, -3, -6, 1], [34, 60, 15, 1])
nonnegative_shift('sqrt falling factorial bound',
                  [Q(144, 25), Q(-194, 25), 1],
                  [Q(11, 25), Q(156, 25), 1])
nonnegative_shift('variance right-budget comparison',
                  [-413, -508, 81], [0, 626, 81])
nonnegative_shift('global B2 polynomial bound', [-6, -3, 1], [22, 11, 1])

# Theorem A constants. Notice inverse u^2 uses x, NOT the false u^2>=1-v.
lam, r = Q(1, 4), Q(5, 18)
check('A maximum h and minimum a', lam/Q(7) == Q(1, 28))
check('A polar/variance upper bound', lam/(3+lam) == Q(1, 13))
check('A rational radius encloses sqrt(1/13)', r*r >= Q(1, 13))
check('A actual-mean lower bound', 1-lam/(6*Q(27, 28)) == Q(155, 162))
check('A mean bound dominates 19/20', Q(155, 162) >= Q(19, 20))
check('A reciprocal u^2 bound', Q(400, 361) < Q(10, 9))
check('A squared factorial comparison at m=7', Q(35, 6) > Q(144, 25))
A = 9*r*(1-r)**-4*Q(5, 12)
check('A tail linear coefficient', A == Q(109350, 28561))
D7 = r**6*(r*r+8*r+28)
check('A B2 monotonic ratios', r < 1 and r*Q(9, 8) == Q(5, 16)
      and r*Q(9, 7) == Q(5, 14) and Q(5, 16) < 1 and Q(5, 14) < 1)
check('A uniform B2 rational base bound', D7 < Q(1, 50))
combined = A+Q(51, 50)*Q(10, 9)
check('A combined variance coefficient', combined == Q(2125787, 428415) < 5)
check('A exact h margin', 1-Q(59, 72)-Q(1, 42) == Q(79, 504) > 0)

# Theorem B constants.
check('B uniform inverse mean square', Q(9, 10)**2/4 == Q(81, 400))
check('B Gamma(1+B2) coefficient', Q(400, 81)*Q(7, 6) == Q(1400, 243) < 6)
check('B sqrt(h/m) rational enclosure', Q(1, 70) < Q(1, 8)**2)
check('B exact h margin', Q(1, 15)+Q(6, 7)+Q(3, 56) == Q(821, 840)
      and 1-Q(821, 840) == Q(19, 840) > 0)

# Independent check of parent's lambda<=4/39 proof.
parent_lam, rho = Q(4, 39), Q(2, 11)
check('parent rho squared cutoff', parent_lam/(3+parent_lam) == rho*rho)
nonnegative_shift('parent falling factorial estimate', [98, -147, 19], [0, 119, 19])
parent_square = Q(14, 195)*Q(11, 9)**8
check('parent squared tail constant < 9/25', parent_square < Q(9, 25))
parent_endpoint = Q(245, 9)*rho**6
check('parent endpoint base constant', parent_endpoint == Q(15680, 15944049) < Q(1, 1000))
check('parent endpoint sequence ratios', rho*Q(8, 7) < 1 and rho*Q(9, 8)**2 < 1)
check('parent total and claimed .99h', Q(3, 5)+Q(1, 1000)+Q(7, 18)
      == Q(8909, 9000) < Q(99, 100))

# Theorem C, high-lambda global all-variance regime.
# Strong polar identity R^2 = 1 + (1-a^2)(1-b), b=1-2ax+a^2:
# checking coefficients in x leaves the following two polynomials in a.
d = [Q(1), Q(0), Q(-1)]
a2 = [Q(0), Q(0), Q(1)]
check('C strong polar identity, constant coefficient in x',
      add(a2, mul(d, d)) == add([Q(1)], scale(mul(d, a2), -1)))
check('C m-ratio at lower endpoint', Q(997, 1001) >= Q(9, 10))
check('C log(lambda) sufficient rational lower bound', Q(9, 2)*Q(99, 100) >= 3)
check('C 10^(5/2) upper enclosure', Q(16, 5)**2 >= 10 and 100*Q(16, 5) == 320)
check('C beta at t=1/4', 1-Q(3, 16)*Q(9, 10)**2 == Q(1357, 1600) <= Q(17, 20))
first = Q(4096, 9)*Q(1001, 1000)*Q(10, 9)**4*Q(1000, 997)**4/Q(31000)
check('C sqrt(1000) lower enclosure', 31**2 <= 1000)
check('C first integral coefficient', first < Q(1, 40))
check('C decreasing exponential sequence ratio squared',
      Q(1001, 1000)**6*Q(17, 20) < 1)
check('C single exponential sequence base bound',
      Q(1000)**3*Q(17, 20)**498 < Q(1, 100))
check('C second integral coefficient',
      3*(Q(1, 100)+Q(320, 100**2)) == Q(63, 500))
check('C Gamma coefficient', Q(400, 81*999) < Q(1, 200))
check('C Gamma B2 coefficient', 6*Q(320, 100**2*1000) < Q(1, 1000))
check('C combined variance coefficient', Q(1, 40)+Q(63, 500)+Q(1, 200)+Q(1, 1000)
      == Q(157, 1000) < Q(1, 5))
check('C exact margin', Q(9, 20)-Q(157, 1000) == Q(293, 1000))

# Exact actual-family positive-variance witness for A and B, not a table.
# Five q=1 and a conjugate stereographic pair, so every |q_j|=1.
m, a, t = 7, Q(99, 100), Q(1, 1000)
qx, qy = (1-t*t)/(1+t*t), 2*t/(1+t*t)
check('witness exact unit-circle pair', qx*qx+qy*qy == 1)
u = (5+2*qx)/7
v, h, d = 1-u*u, 1-a, 1-a*a
check('witness positive variance and both proved domains',
      0 < v <= h/(m*m) and m*h <= Q(1, 4))
# The two conjugate factors multiply to a real polynomial. Integrate the
# resulting original product exactly, not a norm-product or moment surrogate.
pair = [a*a, 2*a*d*qx, d*d]
product = mul(power([a, d], 5), pair)
K = integrate01(product)
check('witness full original complex integral is real and >1', K > 1)
print('WITNESS: m=7, a=99/100, q=(1,1,1,1,1,', qx, '+/- i*', qy, ')')
print('WITNESS: v =', v)
print('WITNESS: K-1 =', K-1)
# C-only actual-family witness: 998 q=1 and q=i,-i, all unit norm.
mC, aC = 1000, Q(9, 10)
hC, dC = 1-aC, 1-aC*aC
uC, vC = Q(998, 1000), 1-Q(998, 1000)**2
check('C-only witness variance and domain',
      vC == Q(999, 250000) > hC/(mC*mC) and mC*hC == 100)
check('C-only witness real-factor lower bound on [99/100,1]',
      aC+dC*Q(99, 100) > Q(27, 25))
check('C-only witness original integral rational lower bound >1',
      Q(81, 10000)*Q(27, 25)**998 > 1)
print('C-ONLY WITNESS: m=1000, a=9/10, q=(998 copies of 1, i, -i), v=999/250000')
print('C-ONLY WITNESS: K >= (81/10000)(27/25)^998 > 1 exactly')
print('A coefficient =', combined, '; A margin/h =', Q(79, 504))
print('B margin/h =', Q(19, 840))
print('C first-integral coefficient =', first)
print('C margins = 14h/15 + 293v/1000')
print('ALL', len(checks), 'EXACT CHECKS PASSED. No grid was used.')
