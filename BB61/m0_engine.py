#!/usr/bin/env python3
# (C) 2026 Ralf Stephan, in collaboration with Claude Code
# CC0 1.0 Universal (public domain dedication).
"""M0 of plans/plan-1061.html -- the orbit engine.

Realises the plan's sec 2.1 splitting {xi alpha^n} = {t_n - S_n} for xi in C(alpha),
by two stable recursions (backward for the future part t_n, one forward recursion per
conjugate for the past part S_n), plus a 200-dps direct evaluation to validate it.
See note-1061-M0.html sec 2.
"""
import numpy as np, itertools, math, mpmath as mp

mp.mp.dps = 60

def poly_roots_np(c):        # c = monic, highest first
    return np.roots(np.array(c, dtype=float))

def is_pisot(c, lo=None, hi=None, tol=1e-9):
    r = poly_roots_np(c)
    real = [x.real for x in r if abs(x.imag) < tol]
    big = [x for x in r if abs(x) > 1 + tol]
    if len(big) != 1: return None
    a = big[0]
    if abs(a.imag) > tol: return None
    a = a.real
    if a <= 1: return None
    if any(abs(abs(x) - 1) < 1e-7 for x in r): return None   # avoid borderline
    if lo is not None and a < lo: return None
    if hi is not None and a > hi: return None
    return a

def irreducible(c):
    import sympy as sp
    X = sp.symbols('X')
    p = sum(int(ci) * X**(len(c) - 1 - i) for i, ci in enumerate(c))
    return sp.Poly(p, X).is_irreducible

class Alpha:
    """A Pisot number with its minimal polynomial, conjugates, and derived data."""
    def __init__(self, coeffs, name=None):
        self.coeffs = [int(x) for x in coeffs]
        self.d = len(coeffs) - 1
        rts = mp.polyroots([mp.mpf(x) for x in self.coeffs], maxsteps=200, extraprec=200)
        rts = sorted(rts, key=lambda z: -abs(z))
        self.alpha = mp.re(rts[0])
        self.conj = rts[1:]                       # the d-1 conjugates, |.|<1
        self.rho = max(abs(z) for z in self.conj) if self.conj else mp.mpf(0)
        self.unit = abs(self.coeffs[-1]) == 1
        self.name = name or self.polystr()
        self.a = float(self.alpha); self.r = float(self.rho)
    def polystr(self):
        s = []
        for i, c in enumerate(self.coeffs):
            k = self.d - i
            if c == 0: continue
            t = ('X^%d' % k) if k > 1 else ('X' if k == 1 else '1')
            cc = '' if (c == 1 and k > 0) else ('-' if (c == -1 and k > 0) else str(c))
            s.append(('+' if c > 0 and s else '') + cc + (t if k > 0 else ''))
        return ''.join(s)
    # --- derived constants ---
    def c_m(self, M):
        """c_m = sum_{j>=2} (alpha_j - 1) alpha_j^m, m = 0..M-1 (real)."""
        return [float(mp.re(sum((z - 1) * z**m for z in self.conj))) for m in range(M)]
    def c_m_mp(self, M):
        return [mp.re(sum((z - 1) * z**m for z in self.conj)) for m in range(M)]
    def Delta(self):    # X7 window l^1 size
        return float(sum(abs(z - 1) / (1 - abs(z)) for z in self.conj))
    def gap(self):      # first gap of C(alpha)
        return float((self.alpha - 2) / self.alpha)
    def routeA(self):   # log2/log alpha + log2/log(1/rho) < 1 ?
        return float(mp.log(2) / mp.log(self.alpha) + mp.log(2) / mp.log(1 / self.rho))
    def trace(self, k):
        return int(mp.nint(mp.re(self.alpha**k + sum(z**k for z in self.conj))))

# ---------- orbit simulation ----------
def orbit(al: Alpha, eps, L=None):
    """eps: 0/1 int array of length N+L. Returns x_n = {xi alpha^n} for n=0..N-1."""
    eps = np.asarray(eps, dtype=np.float64)
    if L is None:
        L = int(math.ceil(60 / math.log10(al.a) / 1.0)) + 40   # alpha^-L < 1e-16 with slack
        L = max(L, int(math.ceil(40 * math.log(10) / math.log(al.a))) + 20)
    N = len(eps) - L
    assert N > 0
    a = al.a; am1 = a - 1.0
    # t_n by backward recursion: t_n = ((a-1) eps_{n+1} + t_{n+1}) / a
    t = np.empty(N + L + 1)
    t[N + L] = 0.0
    for n in range(N + L - 1, -1, -1):
        t[n] = (am1 * eps[n] + t[n + 1]) / a      # note: eps index shift, see below
    # careful: define t[n] = (a-1) sum_{j>=1} eps_{n+j} a^{-j}; with eps 0-indexed as eps[k]=eps_{k+1}
    # then t[n] = (a-1) sum_{j>=1} eps[n+j-1] a^{-j}; recursion t[n] = ((a-1) eps[n] + t[n+1])/a. OK.
    # S_n = sum_{m>=0} c_m eps_{n-m} = Re sum_{j>=2} (alpha_j-1) Q_n^{(j)},  Q_n = alpha_j Q_{n-1} + eps_n
    S = np.zeros(N)
    for z in al.conj:
        zz = complex(z)
        q = 0.0 + 0j
        out = np.empty(N, dtype=complex)
        for n in range(N):
            q = zz * q + eps[n]        # eps[n] = eps_{n+1}; Q at index n corresponds to A_{n+1}
            out[n] = q
        S += ((zz - 1) * out).real
    # index alignment: x_n for n=0..N-1 with x_0 = {xi} = {t_0}, S_0 = 0
    x = np.empty(N)
    x[0] = t[0] % 1.0
    x[1:] = (t[1:N] - S[:N-1]) % 1.0
    return x

def orbit_direct_mp(al: Alpha, eps, N, dps=200):
    """High-precision direct {xi alpha^n} for validation."""
    with mp.workdps(dps):
        a = mp.mpf(0)
        rts = mp.polyroots([mp.mpf(x) for x in al.coeffs], maxsteps=400, extraprec=400)
        alp = mp.re(sorted(rts, key=lambda z: -abs(z))[0])
        K = len(eps)
        xi = (alp - 1) * sum(mp.mpf(int(eps[k])) * alp**(-(k + 1)) for k in range(K))
        out = []
        p = mp.mpf(1)
        for n in range(N):
            out.append(float(mp.frac(xi * p)))
            p *= alp
        return np.array(out)
