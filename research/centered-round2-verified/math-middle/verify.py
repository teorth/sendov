#!/usr/bin/env python3
"""Exact constant replay for PROOF.md; no grids, quadrature, or degree tables.

All operations are integers/Fraction. Quantified analytic arguments live in the
paper proof, not in this finite replay. Squaring is only applied to nonnegative
quantities. Each all-degree sequence uses one base and one ratio bound.
"""
from fractions import Fraction as F

checks = 0

def check(name, condition):
    global checks
    if not condition:
        raise AssertionError(name)
    checks += 1
    print('PASS:', name)

# Imported endpoint and all-degree factorial constants.
check('shifted endpoint polynomial coefficients', (1, 15, 60, 34) ==
      (1, 3*7-6, 3*7**2-12*7-3, 7**3-6*7**2-3*7+6))
check('factorial lower bound at m=7', 7*5-F(144,25)*6 == F(11,25))
check('factorial shifted linear coefficient', 2*7-2-F(144,25) == F(156,25))

# Near extension: 1/4 <= lambda <= 1/3.
r = F(19,60)
A = 9*F(3,10)*F(5,12)/(1-r)**4
G = F(31,30)*F(120,113)**2
check('b <= 1/10 <= r^2', F(1,10) <= r*r)
check('a >= 20/21', 1-F(1,3)/7 == F(20,21))
check('x >= 113/120', 1-F(1,3)/(6*F(20,21)) == F(113,120))
check('u sqrt(v) <= 3/10 square', F(1,10)*(1-F(1,10)) == F(3,10)**2)
check('B2 base at m=7', r**6*(r*r+8*r+28) < F(1,30))
check('B2 three sequence ratios', max(r, r*F(9,8), r*F(9,7)) < 1)
check('a^4 linear bound coefficient', 4-6*F(1,21) == F(26,7))
check('a^4 reduction from lambda >= 1/4', F(26,7)/4 == F(13,14))
check('combined mode and a^4 reduction', F(13,14)+F(4,9)-F(13,14)*F(4,9)/7 >= F(13,10))
check('near G <= 3 A/10', G <= F(3,10)*A)
check('near A+G <= 19/3', A+G <= F(19,3))
check('near m-budget <=3', F(19,3)-F(7,2)+F(1,6) == 3)
check('near variance-to-h budget', 3/(3+F(1,4)) == F(12,13))
check('near endpoint budget', F(2,3)*F(1,21) == F(2,63))
check('near final margin', 1-F(12,13)-F(2,63) == F(37,819))
check('old near regime implies new common margin', F(79,504) > F(37,819))

# Uniform cutoff: m >= 170, b split at r = 43/50.
r = F(43,50)
c = F(1357,1600)
check('quadratic value at t=1/4', 1-F(3,16)*F(9,10)**2 == c)
check('positive endpoint chord gap', r-c == F(19,1600))
check('high b forces lambda > 129/7', 3*r/(1-r) == F(129,7))
check('high b forces integer m >=185', 184 <= 10*F(129,7) < 185)
check('logarithm monotonicity domain', F(129,7) > 3)
check('high-b M >=16', F(186,10) >= 16)
check('endpoint exponent at m=185 >=19/4', 5*F(182,186) >= F(19,4))
check('endpoint exponent condition identity', 20*79-60 == 19*79+19)
check('fourth root of 16', 2**4 == 16)
check('sqrt(10) <=16/5', 10 <= F(16,5)**2)
check('high endpoint prefactor', F(1,2)*10000*F(16,5) == 16000)

# Near-integral coefficient N(m).  Its positive factors decrease with m.
def N_squared(m):
    return (F(4096,18)*F(m+1,m)*F(10,9)**4*F(m,m-3)**4)**2 / m**3

check('N(170) <=17/100 by squares', N_squared(170) <= F(17,100)**2)
check('N(185) <=3/20 by squares', N_squared(185) <= F(3,20)**2)

# Low-b remainder coefficient J(m)=(3/16)(1+1/m)m^(5/2)r^((m-3)/2).
# Square the single base comparison to avoid all radicals.
def J_squared(m):
    return (F(3,16)*F(m+1,m))**2 * m**5 * r**(m-3)

check('low-b J(170) <=121/500', J_squared(170) <= F(121,500)**2)
check('low-b all-degree ratio squared', F(171,170)**5*r < 1)

# High-b exact integral of the endpoint chord: b^(p+1) divided by p+1.
H185 = F(9,8)*F(186,184)/(r-c)*F(16000,185**3)
check('high-b remainder at m=185 <=49/200', H185 <= F(49,200))

# Gamma and Gamma B2, with the original complex endpoints retained.
check('Gamma coefficient at m=170', F(400,81*169) <= F(3,100))
check('Gamma coefficient at m=185', F(400,81*184) <= F(27,1000))
check('Gamma B2 coarse prefactor <=6', F(400,81)*F(7,6) < 6)
check('low-b Gamma B2 base square', (6*170)**2*r**167 <= F(7,2000)**2)
check('low-b Gamma B2 sequence ratio squared', F(171,170)**2*r < 1)
check('high-b Gamma B2 at m=185 square', F(6*16000,1)**2/F(185**7) <= F(1,500)**2)
check('B2 polynomial bound base and shift', 7**2-3*7-4 == 24 and 2*7-3 == 11)

low = F(17,100)+F(121,500)+F(3,100)+F(7,2000)
high = F(3,20)+F(49,200)+F(27,1000)+F(1,500)
check('low-b sum', low == F(891,2000))
check('high-b sum', high == F(53,125))
check('high-b covered by common budget', high < low)
check('cutoff variance margin', F(9,20)-low == F(9,2000))
check('cutoff h margin', 1-F(1,15) == F(14,15))
check('remaining lambda upper endpoint', F(169,10) < 100)

print(f'ALL {checks} EXACT RATIONAL CHECKS PASSED')
print('Certified paper domains: lambda <= 1/3; or m >= 170; plus imported v <= h/m^2.')
print('Outstanding: 7 <= m <= 169, 1/3 < lambda <= m/10, v > h/m^2.')
