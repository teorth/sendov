#!/usr/bin/env python3
"""Exact rational/algebra replay of the cutoff-45 paper proof.

Standard library only. No floats, samples, grids, degree enumeration, external
CAS, subprocesses, imports of local modules, or file writes. Symbolic identities
are checked by polynomial cross multiplication. Analytic implications (norm
convexity, integration, and calculus sign arguments) remain paper mathematics.
The finitely many power comparisons are endpoints of analytic intervals, not a
degree table. Run with PYTHONDONTWRITEBYTECODE=1 python3 verify.py.
"""
from fractions import Fraction as F

VARIABLES = ('m', 'a', 'd', 't')
ZERO: tuple[int, ...] = (0,) * len(VARIABLES)
checks = 0


def check(name, condition):
    global checks
    if not condition:
        raise AssertionError(name)
    checks += 1
    print('PASS:', name)


class Poly:
    """Small exact sparse polynomial ring Q[m,a,d,t]."""
    def __init__(self, terms: 'Poly | dict | int | F' = 0):
        if isinstance(terms, Poly):
            terms = terms.terms
        elif not isinstance(terms, dict):
            terms = {ZERO: F(terms)}
        self.terms = {e: F(c) for e, c in terms.items() if c}

    def __add__(self, other):
        terms = self.terms.copy()
        for e, c in Poly(other).terms.items():
            terms[e] = terms.get(e, F(0)) + c
        return Poly(terms)
    __radd__ = __add__

    def __neg__(self):
        return Poly({e: -c for e, c in self.terms.items()})

    def __sub__(self, other):
        return self + (-Poly(other))

    def __rsub__(self, other):
        return Poly(other) - self

    def __mul__(self, other):
        terms = {}
        for e, c in self.terms.items():
            for f, k in Poly(other).terms.items():
                ef = tuple(i+j for i, j in zip(e, f))
                terms[ef] = terms.get(ef, F(0)) + c*k
        return Poly(terms)
    __rmul__ = __mul__

    def __pow__(self, n):
        if not isinstance(n, int) or n < 0:
            raise ValueError('polynomial powers must be nonnegative integers')
        result = Poly(1)
        for _ in range(n):
            result *= self
        return result

    def __eq__(self, other):
        return self.terms == Poly(other).terms

    def diff(self, var):
        i = VARIABLES.index(var)
        terms = {}
        for e, c in self.terms.items():
            if e[i]:
                f = list(e)
                f[i] -= 1
                terms[tuple(f)] = c*e[i]
        return Poly(terms)

    def substitute(self, var, value):
        i = VARIABLES.index(var)
        result = Poly()
        for e, c in self.terms.items():
            f = list(e)
            f[i] = 0
            result += Poly({tuple(f): c}) * Poly(value)**e[i]
        return result


class Rat:
    """Formal rational functions; equality is exact cross multiplication."""
    def __init__(self, numerator: 'Rat | Poly | int | F' = 0,
                 denominator: 'Poly | int | F' = 1):
        if isinstance(numerator, Rat):
            if denominator != 1:
                raise ValueError('unexpected nested denominator')
            self.n, self.q = numerator.n, numerator.q
        else:
            self.n, self.q = Poly(numerator), Poly(denominator)
        if self.q == 0:
            raise ZeroDivisionError

    def __add__(self, other):
        other = Rat(other)
        return Rat(self.n*other.q + other.n*self.q, self.q*other.q)
    __radd__ = __add__

    def __neg__(self):
        return Rat(-self.n, self.q)

    def __sub__(self, other):
        return self + (-Rat(other))

    def __rsub__(self, other):
        return Rat(other) - self

    def __mul__(self, other):
        other = Rat(other)
        return Rat(self.n*other.n, self.q*other.q)
    __rmul__ = __mul__

    def __truediv__(self, other):
        other = Rat(other)
        return Rat(self.n*other.q, self.q*other.n)

    def __rtruediv__(self, other):
        return Rat(other)/self

    def __pow__(self, n):
        if n < 0:
            return Rat(self.q**(-n), self.n**(-n))
        return Rat(self.n**n, self.q**n)

    def __eq__(self, other):
        other = Rat(other)
        return self.n*other.q == other.n*self.q

    def diff(self, var):
        return Rat(self.n.diff(var)*self.q-self.n*self.q.diff(var), self.q**2)


def variable(name):
    e = [0]*len(VARIABLES)
    e[VARIABLES.index(name)] = 1
    return Rat(Poly({tuple(e): 1}))


m, a, d, t = map(variable, VARIABLES)
r = m/(m+30)
dm = (18*m+2040)/(85*(m+30))
D = m*(m-1)*(m-2)
B0 = (319*m+3570)/(400*(m+30))
rho = F(17,20)

# Foundational inequalities retained from the source.
check('endpoint polynomial shifted at 7',
      m**3-6*m**2-3*m+6 == (m-7)**3+15*(m-7)**2+60*(m-7)+34)
check('h endpoint coefficient', F(2,3)*F(1,10) == F(1,15))
check('target variance coefficient', F(9,10)/2 == F(9,20))
check('B2 quadratic shifted at 7',
      m**2-3*m-4 == (m-7)**2+11*(m-7)+24)
check('Gamma B2 coefficient bound', F(400,81)*F(7,6) < 6)

# Midpoint estimates, including their precise domains.
check('midpoint B0 identity', (1+r)/2-F(9,10)**2/4 == B0)
check('midpoint alternative identity', B0 == F(319,400)-15/(m+30))
check('r minus midpoint endpoint bound',
      r-B0 == (81*m-3570)/(400*(m+30)))
check('midpoint late comparison valid from m=45', 81*45-3570 == 75 > 0)
check('sqrt tangent identity at root rho=17/20',
      (B0+rho**2)/(2*rho) == 1-dm/2)
check('tangent sign: root rho positive', rho > 0)
check('d derivative', dm.diff('m') == -1500/(85*(m+30)**2))
check('d positive numerator at m=45', 18*45+2040 > 0)
check('d(45) strictly below 1/2', F(18*45+2040,85*(45+30)) < F(1,2))
check('d <=1/2 exact identity',
      F(1,2)-dm == (49*m-1530)/(170*(m+30)))
G = (1-F(5,9)*a*d)**2 - ((1+r)/2-a**2/4)
Gp = a*(F(1,2)+F(50,81)*d**2)-F(10,9)*d
check('squared-midpoint derivative in a', G.diff('a') == Gp)
q = F(9,20)+F(5,9)*d**2-F(10,9)*d
check('derivative lower-bound difference',
      Gp-q == (a-F(9,10))*(F(1,2)+F(50,81)*d**2))
check('derivative lower-bound polynomial decreases for d<=1/2',
      q.diff('d') == F(10,9)*(d-1))
check('midpoint derivative margin at d=1/2',
      F(9,20)+F(5,9)*F(1,2)**2-F(10,9)*F(1,2) == F(1,30))
check('midpoint squared RHS positive lower bound',
      1-F(5,9)*F(1,2) == F(13,18) > 0)
check('chord slope c <=5/9 <2', F(10,9)*F(1,2) == F(5,9) < 2)
check('chord slope gives exact a cancellation',
      a**4/(F(10,9)*a*d)**4 == F(9,10)**4/d**4)

# Complete beta integral: four-term rational identity for integer m>2.
# Expanding (1-y)^3 after y=1-ct gives this exact finite expression.
check('complete beta integral rational identity',
      1/(m-2)-3/(m-1)+3/m-1/(m+1) == 6/((m+1)*D))
check('tail prefactor after beta integration', F(3,2)*6*F(1,2) == F(9,2))
check('late integral actual value <=1/4',
      (1-F(1,2)**4)/4 == F(15,64) < F(1,4))
check('late prefactor', F(3,2)*F(1,2)*F(1,4) == F(3,16))

# N logarithmic derivative and global sign certificate.
logNprime = -4*dm.diff('m')/dm-F(1,2)*D.diff('m')/D
check('exact N logarithmic derivative',
      logNprime == 6000/((m+30)*(18*m+2040))
      -F(1,2)*(1/m+1/(m-1)+1/(m-2)))
upperN = 6000/((m+30)*(18*m+2040))-F(3,2)/m
QN = 18*m**2-1420*m+61200
check('N log derivative upper numerator',
      upperN == -3*QN/(2*m*(m+30)*(18*m+2040)))
check('N sign sum-of-positive-terms identity',
      QN == 18*(m-40)**2+20*m+32400)

def N_squared(n):
    dn = F(18*n+2040,85*(n+30))
    return (F(9,2)*F(9,10)**4/dn**4)**2 / (n*(n-1)*(n-2))

check('N(45) <254/1000 by squares', N_squared(45) < F(254,1000)**2)
check('N(50) <247/1000 by squares', N_squared(50) < F(247,1000)**2)

# f=log J. f'=R+(log r)/2, so f''=R'+r'/(2r).
R = 1/(m+1)+F(3,2)/m+15*(m-3)/(m*(m+30))
fsecond = R.diff('m')+r.diff('m')/(2*r)
P = -5*m**4+774*m**3-3*m**2+900*m
check('J second derivative numerator',
      fsecond == P/(2*m**2*(m+30)**2*(m+1)**2))
check('J convexity positive grouping',
      P == m*((774-5*m)*m**2-3*m+900))
check('J convexity cubic coefficient on m<=100', 774-5*100 == 274 > 0)
check('J convexity remaining quadratic positive on m>=45', 274*45-3 > 0)

# Analytic log inequalities are certified by derivative identities and value 0.
upper_log = t-t**2/2+t**3/3
check('upper-log remainder derivative',
      upper_log.diff('t')-1/(1+t) == t**3/(1+t))
lower_log = 2*t/(2+t)
check('lower-log remainder derivative',
      1/(1+t)-lower_log.diff('t') == t**2/((1+t)*(2+t)**2))
check('log polynomial bounds agree at t=0',
      upper_log.n.substitute('t',0) == 0 and lower_log.n.substitute('t',0) == 0)

flower = R-F(1,2)*(30/m-450/m**2+9000/m**3)
QJ = 5*m**4-387*m**3+4050*m**2-265500*m-270000
check('J first derivative lower numerator',
      flower == QJ/(2*m**3*(m+1)*(m+30)))
check('J positive shifted polynomial at m=100',
      QJ == 126680000+8934500*(m-100)+187950*(m-100)**2
      +1613*(m-100)**3+5*(m-100)**4)
check('J shifted coefficients all positive',
      min(126680000,8934500,187950,1613,5) > 0)

def J_squared(n):
    return (F(3,16)*F(n+1,n))**2*n**5*F(n,n+30)**(n-3)

check('J(45) <29/500 by squares', J_squared(45) < F(29,500)**2)
check('J(50) <29/500 by squares', J_squared(50) < F(29,500)**2)
check('29/500 <23/250', F(29,500) < F(23,250))
check('J(100) <23/250 by squares', J_squared(100) < F(23,250)**2)
check('J(170) <23/250 by squares', J_squared(170) < F(23,250)**2)

# K logarithmic derivative, with log(1+t)>=2t/(2+t).
check('K logarithm replacement', -F(1,2)*(2*(30/m)/(2+30/m)) == -15/(m+15))
upperK = 1/m+15*(m-3)/(m*(m+30))-15/(m+15)
check('K upper derivative numerator',
      upperK == (m**2-225*m-225)/(m*(m+30)*(m+15)))
check('K sign grouping on m<=170', m**2-225*m-225 == m*(m-225)-225)
check('K negative coefficient on m<=170', 170-225 == -55 < 0)

def K_squared(n):
    return (6*n)**2*F(n,n+30)**(n-3)

check('K(45) <6/1000 by squares', K_squared(45) < F(6,1000)**2)
check('K(50) <1/200 by squares', K_squared(50) < F(1,200)**2)
check('Gamma(45) coefficient <113/1000', F(400,81*44) < F(113,1000))
check('Gamma(50) coefficient <101/1000', F(400,81*49) < F(101,1000))

budget45 = F(254,1000)+F(29,500)+F(113,1000)+F(6,1000)
budget50 = F(247,1000)+F(23,250)+F(101,1000)+F(1,200)
check('45-to-50 total', budget45 == F(431,1000))
check('50-to-170 total', budget50 == F(445,1000))
check('both budgets below imported common coefficient',
      budget45 < budget50 < F(891,2000))
check('uniform variance margin', F(9,20)-F(891,2000) == F(9,2000))
check('uniform h margin', 1-F(1,15) == F(14,15))
check('integer complement largest degree', 45-1 == 44)
check('remaining lambda endpoint', F(44,10) == F(22,5))
check('remaining strict a upper bound expression',
      1-F(1,3)/m == (3*m-1)/(3*m))

print(f'ALL {checks} EXACT RATIONAL/ALGEBRA CHECKS PASSED')
print('New analytic domain: 45 <= m <= 170, all original a, means, and variances.')
print('With imported theorem: every integer m >=45.')
print('Remaining: 7 <=m <=44, 1/3 <lambda <=m/10, v >h/m^2, original feasibility.')
