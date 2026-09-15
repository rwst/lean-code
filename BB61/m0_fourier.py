#!/usr/bin/env python3
# (C) 2026 Ralf Stephan, in collaboration with Claude Code
# CC0 1.0 Universal (public domain dedication).
"""M0 sec 3 -- closed form of hat{F_*mu_p}(h) for Bernoulli(p) digit words.

  |hat F(h)| = prod_{j>=1} |1-p+p e(h(a-1)a^-j)| * prod_{m>=0} |1-p+p e(-h c_m)|,

the a.s. limit of the Weyl sums.  At p=1/2 the two factors are the two halves of the
doubly infinite Erdos product prod_{i in Z} |cos(pi h (a-1) a^i)|.
"""
from m0_engine import *
import numpy as np, math, mpmath as mp

def bern_abs(x, p):
    """|E e(x*eps)| for eps ~ Bernoulli(p) = sqrt(1 - 4p(1-p) sin^2(pi x))."""
    s = np.sin(np.pi * x)
    return np.sqrt(np.maximum(0.0, 1.0 - 4 * p * (1 - p) * s * s))

def Phi_parts(al: Alpha, h, p=0.5, tol=1e-18):
    """Returns (Phi1, Phi2) with
         Phi1 = prod_{j>=1} |E e(h(alpha-1)alpha^{-j} eps)|      (future digits, t_n)
         Phi2 = prod_{m>=0} |E e(-h c_m eps)|                    (past digits, S_n)
       and Phi = Phi1*Phi2 = lim_N |1/N sum_n e(h {xi alpha^n})| for a.e. Bernoulli(p) word."""
    a = al.a; am1 = a - 1.0
    # Phi1
    J = int(math.log(max(abs(h) * am1, 1.0) / tol) / math.log(a)) + 5
    js = np.arange(1, J + 1)
    x1 = h * am1 * a ** (-js.astype(float))
    P1 = float(np.prod(bern_abs(x1, p)))
    # Phi2
    M = int(math.log(max(abs(h), 1.0) * max(1.0, sum(abs(z - 1) for z in al.conj)) / tol) / math.log(1 / al.r)) + 5
    cm = np.array(al.c_m(M))
    P2 = float(np.prod(bern_abs(h * cm, p)))
    return P1, P2

def Phi(al, h, p=0.5):
    P1, P2 = Phi_parts(al, h, p)
    return P1 * P2

def Phi_doubly(al, y, p=0.5, tol=1e-18):
    """prod_{i in Z} |E e(y alpha^i eps)| -- the doubly infinite Erdos product."""
    a = al.a
    J = int(math.log(max(abs(y), 1e-300) / tol) / math.log(a)) + 5
    neg = np.array([y * a ** (-j) for j in range(1, J + 1)])
    P = float(np.prod(bern_abs(neg, p)))
    # positive side: y alpha^i mod 1 = -(sum_j sigma_j(y) alpha_j^i) if y in Z[alpha]
    i = 0; term = mp.mpf(1)
    yy = mp.mpf(y)
    return P

if __name__ == '__main__':
    al = Alpha([1, -2, -1], '1+sqrt2')
    print('alpha =', al.a, ' rho =', al.r)
    print('%6s %10s %10s %10s' % ('h', 'Phi1', 'Phi2', 'Phi'))
    for h in [1, 2, 3, 4, 5, 7, 17, 41, 99, 239, 577, 1393, 3363, 8119, 19601, 47321]:
        P1, P2 = Phi_parts(al, h)
        print('%6d %10.6f %10.6f %10.6f' % (h, P1, P2, P1 * P2))
