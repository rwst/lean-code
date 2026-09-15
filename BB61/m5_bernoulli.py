#!/usr/bin/env python3
# (C) 2026 Ralf Stephan, in collaboration with Claude Code
# CC0 1.0 Universal (public domain dedication).
"""M5 of plans/plan-1061.html -- Route E, the Bernoulli / a.e. statement.

Under the two-sided coding of note-1061-M1.html Lemma 6,

    F(omega) = t(omega^+) - S(omega^-),   t = (a-1) sum_{j>=1} omega_j a^{-j},
                                          S = sum_{m>=0} c_m omega_{-m},

the two halves are functions of disjoint blocks of coordinates, so under a Bernoulli(p)
product measure mu_p on {0,1}^Z the Fourier coefficients of F_* mu_p factor completely:

    G_p(h) := hat{F_* mu_p}(h) = prod_{j>=1} phi_p( h (a-1) a^{-j} )
                                 * prod_{m>=0} phi_p( -h c_m ),
    phi_p(x) = (1-p) + p e(x),   |phi_p(x)|^2 = 1 - 4p(1-p) sin^2(pi x).

By the trace identity of M1 Lemma 2 one has  h c_m = -h(a-1)a^m mod 1, so the second
product is the non-negative half of the doubly infinite Erdos product
prod_{i in Z} phi_p(h(a-1)a^i)  (M0 sec 3).  This module computes G_p(h) with a
*rigorous* truncation enclosure of its modulus:

    |G| = (finite part) * T,   1 - 4p(1-p) pi^2 (tail_f + tail_p) <= T <= 1,

using sin^2(pi x) <= pi^2 x^2 and prod(1-t_i) >= 1 - sum t_i, both valid termwise.
The finite parts are evaluated in mpmath at `DPS` digits from the exact conjugates.
"""
import math
import mpmath as mp
from m0_engine import Alpha

DPS = 50
mp.mp.dps = DPS


# ---------------------------------------------------------------- the factor phi
def phi(x, p):
    """E[e(x*eps)] for eps ~ Bernoulli(p), p = P(eps=1).  x may be mpf or float."""
    x = mp.mpf(x) if not isinstance(x, mp.mpf) else x
    return (1 - mp.mpf(p)) + mp.mpf(p) * mp.e**(2j * mp.pi * x)


def absphi(x, p):
    """|phi_p(x)| = sqrt(1 - 4p(1-p) sin^2(pi x)); depends on x mod 1 only."""
    s = mp.sin(mp.pi * mp.mpf(x))
    return mp.sqrt(1 - 4 * mp.mpf(p) * (1 - mp.mpf(p)) * s * s)


# ---------------------------------------------------------------- the two ladders
def future_args(al, h, J):
    """x_j = h (alpha-1) alpha^{-j},  j = 1..J."""
    a = al.alpha
    return [mp.mpf(h) * (a - 1) / a**j for j in range(1, J + 1)]


def past_args(al, h, M):
    """-h c_m,  m = 0..M-1, with c_m = sum_{j>=2} (alpha_j - 1) alpha_j^m."""
    cm = al.c_m_mp(M)
    return [-mp.mpf(h) * c for c in cm]


def depths(al, h, p, tol=mp.mpf('1e-40')):
    """Truncation depths J (future) and M (past) making the tail bound < tol."""
    a, rho = al.alpha, al.rho
    Ca = sum(abs(z - 1) for z in al.conj) if al.conj else mp.mpf(0)
    q = 4 * mp.mpf(p) * (1 - mp.mpf(p)) * mp.pi**2 * mp.mpf(h)**2
    J = 2
    while q * (a - 1)**2 * a**(-2 * J) / (a**2 - 1) > tol / 2:
        J += 1
    M = 1
    if al.conj:
        while q * Ca**2 * rho**(2 * M) / (1 - rho**2) > tol / 2:
            M += 1
    return J, M


def weyl(al, h, p=mp.mpf('0.5'), J=None, M=None, tol=mp.mpf('1e-40')):
    """G_p(h) with a rigorous enclosure of its modulus.

    Returns dict: value (complex, truncated), abs (modulus of the truncated product),
    lo, hi (rigorous enclosure of |G_p(h)|), tail (the bound 4p(1-p)pi^2 sum x^2),
    minfac (smallest single-factor modulus seen) and its location.
    """
    p = mp.mpf(p)
    if J is None or M is None:
        J0, M0 = depths(al, h, p, tol)
        J = J0 if J is None else J
        M = M0 if M is None else M
    a, rho = al.alpha, al.rho
    Ca = sum(abs(z - 1) for z in al.conj) if al.conj else mp.mpf(0)
    xs = future_args(al, h, J)
    cs = past_args(al, h, M)
    val = mp.mpc(1)
    minfac, where = mp.mpf(2), None
    for j, x in enumerate(xs, 1):
        f = phi(x, p); val *= f
        if abs(f) < minfac: minfac, where = abs(f), ('future', j, x)
    for m, x in enumerate(cs):
        f = phi(x, p); val *= f
        if abs(f) < minfac: minfac, where = abs(f), ('past', m, x)
    q = 4 * p * (1 - p) * mp.pi**2 * mp.mpf(h)**2
    tail = q * (a - 1)**2 * a**(-2 * J) / (a**2 - 1)
    if al.conj:
        tail += q * Ca**2 * rho**(2 * M) / (1 - rho**2)
    A = abs(val)
    return dict(value=val, abs=A, lo=A * max(mp.mpf(0), 1 - tail), hi=A,
                tail=tail, J=J, M=M, minfac=minfac, where=where)


def modulus(al, h, p=mp.mpf('0.5')):
    return weyl(al, h, p)['abs']


# ---------------------------------------------------------------- Theorem C checks
def vanishing_witness(al, h, p, J, M, eps=mp.mpf('1e-30')):
    """Report any factor that is (numerically) zero.  phi_p(x)=0 iff p=1/2, x=1/2 mod 1."""
    out = []
    for j, x in enumerate(future_args(al, h, J), 1):
        if absphi(x, p) < eps: out.append(('future', j, x))
    for m, x in enumerate(past_args(al, h, M)):
        if absphi(x, p) < eps: out.append(('past', m, x))
    return out


def future_halfinteger_candidates(al, h, jmax=None):
    """The finite list of j that Theorem C must rule out: h(a-1)a^{-j} in 1/2 + Z
    forces alpha^j <= 2|h|(alpha-1).  Returns those j with the value of 2h(a-1)a^{-j}."""
    a = al.alpha
    lim = 2 * abs(h) * (a - 1)
    if jmax is None:
        jmax = max(1, int(mp.floor(mp.log(lim) / mp.log(a))) + 1) if lim > 1 else 1
    out = []
    for j in range(1, jmax + 1):
        if a**j <= lim:
            out.append((j, 2 * mp.mpf(h) * (a - 1) / a**j))
    return out


# ---------------------------------------------------------------- derived constants
def best_h(al, p, H):
    """(h, |G_p(h)|) maximising the bias over 1 <= h <= H."""
    best = (0, mp.mpf(0))
    for h in range(1, H + 1):
        A = modulus(al, h, p)
        if A > best[1]: best = (h, A)
    return best


def discrepancy_floor(al, h, p):
    """liminf_N D_N^* >= |G_p(h)| / (4 sqrt2 h)   (Koksma, V(cos 2pi h x) = 4h)."""
    return modulus(al, h, p) / (4 * mp.sqrt(2) * h)


def entropy(p):
    p = mp.mpf(p)
    if p <= 0 or p >= 1: return mp.mpf(0)
    return -p * mp.log(p) - (1 - p) * mp.log(1 - p)


def h_min(al):
    """Ledrappier-Young floor of note-1061-M3.html Thm 11 (alpha a unit)."""
    la, lr = mp.log(al.alpha), mp.log(1 / al.rho)
    return la * lr / (la + lr)


def entropy_window(al):
    """The p-interval on which M3's floor does NOT already exclude Bernoulli(p):
    {p : H(p) >= h_min(alpha)}.  Empty iff h_min > log 2."""
    hm = h_min(al)
    if hm >= mp.log(2): return None
    lo = mp.findroot(lambda t: entropy(t) - hm, mp.mpf('0.1'))
    return (lo, 1 - lo, hm)


if __name__ == '__main__':
    for name, c in [('1+sqrt2', [1, -2, -1]), ('2+sqrt3', [1, -4, 1]),
                    ('(3+sqrt5)/2', [1, -3, 1]), ('X^3-4X^2-3X-1', [1, -4, -3, -1])]:
        al = Alpha(c, name)
        w = weyl(al, 1, mp.mpf('0.5'))
        print('%-14s alpha=%.6f  |G_{1/2}(1)| = %.10f   [%.10f, %.10f]  J=%d M=%d'
              % (name, float(al.alpha), float(w['abs']), float(w['lo']), float(w['hi']),
                 w['J'], w['M']))
        print('     min factor %.6f at %s' % (float(w['minfac']), w['where'][:2]))
