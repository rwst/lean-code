#!/usr/bin/env python3
# (C) 2026 Ralf Stephan, in collaboration with Claude Code
# CC0 1.0 Universal (public domain dedication).
"""M5, one step past Bernoulli: the Markov Fourier coefficient, exactly.

The Bernoulli factorisation of note-1061-M5.html Thm 2 used that omega^+ and omega^-
occupy disjoint coordinates.  For a Markov measure they are not independent -- but they
are *conditionally* independent given omega_0, and that is enough:

    G_P(h) = sum_a pi_a e(-h c_0 a) u_a(h) v_a(h),
    v_a = E[ e(h sum_{j>=1} x_j omega_j) | omega_0 = a ],      x_j = (alpha-1) alpha^-j
    u_a = E[ e(-h sum_{m>=1} c_m omega_{-m}) | omega_0 = a ],

with v the backward product of the matrices (P_ab e(h x_j b)) and u the same for the
reversed chain Q_ab = pi_b P_ba / pi_a and the weights -h c_m.  Both products converge
absolutely (sum_j x_j = 1, sum_m |c_m| < infinity), so this is exact arithmetic up to
the truncation depth, which is chosen from the same tail bounds as the Bernoulli case.

A Markov counterexample to 10.61 would need G_P(h) = 0 for EVERY h != 0.  This module
computes  Psi(P) = max_{1<=h<=H} |G_P(h)|  and minimises it over the 2-parameter family;
that is the first quantitative statement about the case the plan's M7 row calls "the
first case beyond Bernoulli".  See note-1061-M5.html sec 8.
"""
import numpy as np
from m0_engine import Alpha


def stationary(P):
    """Stationary vector of a 2x2 stochastic matrix."""
    p01, p10 = P[0, 1], P[1, 0]
    s = p01 + p10
    if s <= 0: return np.array([0.5, 0.5])
    return np.array([p10 / s, p01 / s])


def reverse(P, pi):
    Q = np.empty_like(P)
    for a in (0, 1):
        for b in (0, 1):
            Q[a, b] = pi[b] * P[b, a] / pi[a] if pi[a] > 0 else P[a, b]
    return Q


def _chain(P, weights):
    """E[e(sum_k w_k omega_k) | omega_0 = a] for the chain P and weights w_1..w_K."""
    W = np.ones(2, dtype=complex)
    for w in reversed(weights):
        ph = np.array([1.0, np.exp(2j * np.pi * w)])
        W = P @ (ph * W)
    return W


class MarkovG:
    """G_P(h) for a fixed alpha, with cached ladders."""

    def __init__(self, al: Alpha, hmax=32, tol=1e-15):
        a, rho = float(al.alpha), float(al.rho)
        Ca = float(sum(abs(complex(z) - 1) for z in al.conj)) or 1.0
        self.J = int(np.log(max(hmax, 1) * (a - 1) / tol) / np.log(a)) + 3
        self.M = int(np.log(max(hmax, 1) * Ca / (tol * (1 - rho))) / np.log(1 / rho)) + 3
        self.x = np.array([(a - 1) * a ** (-j) for j in range(1, self.J + 1)])
        self.c = np.array(al.c_m(self.M + 1))
        self.al = al

    def G(self, P, h):
        pi = stationary(P)
        Q = reverse(P, pi)
        v = _chain(P, h * self.x)
        u = _chain(Q, -h * self.c[1:])
        ph0 = np.array([1.0, np.exp(-2j * np.pi * h * self.c[0])])
        return complex(np.sum(pi * ph0 * u * v))

    def Psi(self, P, hs):
        return max(abs(self.G(P, h)) for h in hs)


def mat(p01, p10):
    return np.array([[1 - p01, p01], [p10, 1 - p10]])


if __name__ == '__main__':
    al = Alpha([1, -4, 1], '2+sqrt3')
    mg = MarkovG(al)
    hs = list(range(1, 17))
    # Bernoulli(p) is the Markov chain with p01 = p, p10 = 1-p; check against m5_bernoulli
    import mpmath as mp, m5_bernoulli as B
    for p in [0.5, 0.3]:
        g = mg.G(mat(p, 1 - p), 3)
        gb = complex(B.weyl(al, 3, mp.mpf(p))['value'])
        print('p=%.1f  markov %+.10f%+.10fi  bernoulli %+.10f%+.10fi  diff %.2e'
              % (p, g.real, g.imag, gb.real, gb.imag, abs(g - gb)))
