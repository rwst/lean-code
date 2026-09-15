#!/usr/bin/env python3
# (C) 2026 Ralf Stephan, in collaboration with Claude Code
# CC0 1.0 Universal (public domain dedication).
"""M0 sec 9 -- exact hat{F_*nu}(h) for order-r Markov measures, and the adversary.

Conditioning on the r-block at time n makes past and future independent, so hat F is a
sum over block states of a future factor times a past factor, each from one backward
recursion (the past one along the reversed chain).
"""
from m0_engine import *
import numpy as np, math
from scipy.optimize import minimize

def blocks(r): return list(range(1 << r))

def chain(p, r):
    """p[s] = P(next digit = 1 | block s).  Returns block transition matrix T and stationary pi."""
    S = 1 << r
    T = np.zeros((S, S))
    for s in range(S):
        for b in (0, 1):
            s2 = ((s << 1) | b) & (S - 1)
            T[s, s2] += (p[s] if b else 1 - p[s])
    A = np.vstack([T.T - np.eye(S), np.ones(S)])
    b = np.zeros(S + 1); b[-1] = 1.0
    pi, *_ = np.linalg.lstsq(A, b, rcond=None)
    pi = np.maximum(np.real(pi), 0.0)
    s = pi.sum()
    pi = pi / s if s > 0 else np.full(S, 1.0 / S)
    return T, pi

def Fhat(al, h, p, r, tol=1e-14):
    S = 1 << r
    T, pi = chain(p, r)
    ss = np.arange(S)
    IDX0 = (ss << 1) & (S - 1); IDX1 = ((ss << 1) | 1) & (S - 1)
    JDX0 = (ss >> 1); JDX1 = (1 << (r - 1)) | (ss >> 1) if r > 0 else ss
    a = al.a; am1 = a - 1.0
    J = int(math.log(max(abs(h) * am1, 1) / tol) / math.log(a)) + 3
    # future: u_j(s) = sum_b P(s,b) e(h(a-1)a^{-j} b) u_{j+1}(shift(s,b))
    u = np.ones(S, dtype=complex)
    for j in range(J, 0, -1):
        x = h * am1 * a ** (-j)
        ph = np.exp(2j * np.pi * x)
        u = (1 - p) * u[IDX0] + p * ph * u[IDX1]
    # reversed chain Q(s -> a) = P(previous digit = a | block s)
    Q = np.zeros((S, 2))
    for s in range(S):
        w1 = s >> 1                      # w_1..w_{r-1}
        last = s & 1
        for aa in (0, 1):
            sp = (aa << (r - 1)) | w1    # block (a, w_1..w_{r-1})
            Q[s, aa] = pi[sp] * (p[sp] if last else 1 - p[sp])
        tot = Q[s].sum()
        Q[s] = Q[s] / tot if tot > 0 else np.array([.5, .5])
    Ksum = float(sum(abs(z - 1) for z in al.conj)) or 1.0
    M = int(math.log(max(abs(h), 1) * Ksum / tol) / math.log(1 / al.r)) + 3
    cm = al.c_m(M + 1)
    g = np.ones(S, dtype=complex)
    for m in range(M, r - 1, -1):
        ph = np.exp(-2j * np.pi * h * cm[m])
        g = Q[:, 0] * g[JDX0] + Q[:, 1] * ph * g[JDX1]
    B = np.empty(S, dtype=complex)
    for s in range(S):
        e = 0.0
        for i in range(r):
            bit = (s >> i) & 1           # s bit i  = w_{r-i} = eps_{n-i}
            e += cm[i] * bit
        B[s] = np.exp(-2j * np.pi * h * e) * g[s]
    return complex(np.sum(pi * u * B))

def obj(p, al, hs, r):
    return max(abs(Fhat(al, h, p, r)) for h in hs)

def adversary(al, hs, r, ntries=12, seed=0):
    rng = np.random.default_rng(seed)
    best = (1e9, None)
    S = 1 << r
    for t in range(ntries):
        x0 = np.full(S, 0.5) if t == 0 else rng.random(S) * 0.8 + 0.1
        f = lambda z: obj(np.clip(z, 1e-4, 1 - 1e-4), al, hs, r)
        res = minimize(f, x0, method='Nelder-Mead',
                       options=dict(maxiter=1500, xatol=1e-4, fatol=1e-7))
        if res.fun < best[0]: best = (float(res.fun), np.clip(res.x, 1e-4, 1 - 1e-4))
    return best
