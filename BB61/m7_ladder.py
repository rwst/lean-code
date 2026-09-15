#!/usr/bin/env python3
# (C) 2026 Ralf Stephan, in collaboration with Claude Code
# CC0 1.0 Universal (public domain dedication).
"""M7: the trace ladder as a two-band correlation, and the limit functionals.

Write y_p = (alpha-1) alpha^{-p}, p in Z.  M1 Lemma 2 (c_m + (alpha-1)alpha^m in Z)
says that the weight profile of h F is the single geometric sequence h y_p reduced
mod 1, on BOTH sides of the origin:

    h F(omega) = sum_{p in Z} omega_p * <h y_p>   (mod 1),    <x> = x - round(x).

For a *ladder* mode -- h_k = round(lam alpha^k) with lam in the codifferent, so that
h_k - lam alpha^k -> 0 -- the reduced profile is a fixed shape carried outward: it is
O(1) only in two thin bands at depths -k and +k and is exponentially small in the whole
bulk between them (verified in note-1061-M7.html sec 4).  Hence

    Phi_{h_k}(mu) = int (b o sigma^{2k}) a dmu + O(theta^k),

with a, b continuous and independent of k, so that for every mixing mu the ladder
Fourier coefficients converge to the product (int a dmu)(int b dmu).  That limit is the
plateau of M0 -- here shown to be a plateau for *every* mixing invariant measure, not
only for Bernoulli.
"""
import numpy as np
from m0_engine import Alpha


def profile(al, h, P=40, N=40):
    """The reduced two-sided weight profile <h y_p> for p = -N..P."""
    a = float(al.alpha)
    fut = np.array([(a - 1) * a ** (-p) for p in range(1, P + 1)])
    past = np.array(al.c_m(N + 1))                      # weight at p = -m is -c_m
    w = np.concatenate([(-past[::-1] * h), fut * h])    # p = -N..-0, 1..P
    return w - np.round(w)


def band_split(w, N, tol=1e-3):
    """Indices where the reduced profile is above tol, as (past band, future band)."""
    idx = np.where(np.abs(w) > tol)[0] - N              # p-coordinates, p=0 at index N
    return idx[idx <= 0], idx[idx > 0]


def multipliers(al, H=200000, rel=0.55, top=40):
    """Discover ladder multipliers lam from a Bernoulli mode scan.

    A ladder rung has h approx lam alpha^k, so h alpha^{-round(log h/log alpha)} is the
    same number for every rung; clustering those values recovers the multipliers.
    """
    from m3_entropy import bern_phi
    a = float(al.alpha)
    bp = bern_phi(al, H)
    cut = rel * float(np.sort(bp)[-3]) if len(bp) > 3 else 0.0
    hs = np.where(bp >= cut)[0] + 1
    lam = {}
    for h in hs:
        k = int(round(np.log(h) / np.log(a)))
        v = h / a ** k
        while v >= a ** 0.5:
            v /= a
        while v < a ** -0.5:
            v *= a
        key = round(float(v), 4)
        best = None
        for kk in lam:
            if abs(kk - key) < 1e-3:
                best = kk
                break
        if best is None:
            lam[key] = []
            best = key
        lam[best].append((int(h), float(bp[h - 1])))
    out = [(k, v) for k, v in lam.items() if len(v) >= 3]
    out.sort(key=lambda t: -max(x[1] for x in t[1]))
    return out[:top]


def rungs_from_seed(al, seed, kmax):
    """Every integer solution of the minimal-polynomial recurrence is a ladder.

    If alpha^d = a_1 alpha^{d-1} + ... + a_d then h_k = Tr(lam alpha^k) obeys the same
    recurrence for every lam in the codifferent, and lam <-> (h_0,...,h_{d-1}) is a
    bijection with Z^d.  So the ladders at alpha are exactly the integer sequences of
    that recurrence -- generated here exactly, with no rounding drift.
    """
    c = al.coeffs                      # monic, highest first: X^d + c_1 X^{d-1} + ...
    d = al.d
    rec = [-c[i] for i in range(1, d + 1)]        # h_{k} = sum_i rec[i-1] h_{k-i}
    h = list(seed)
    while len(h) <= kmax:
        h.append(sum(rec[i] * h[-1 - i] for i in range(d)))
    return h


def rung(al, lam, k):
    return int(round(lam * float(al.alpha) ** k))


def ladder_rungs(al, lam, kmax, kmin=2):
    return [rung(al, lam, k) for k in range(kmin, kmax + 1)]


def lam_of_seed(al, seed):
    """The codifferent element lam with Tr(lam alpha^k) = seed[k], k = 0..d-1."""
    import mpmath as mp
    r = [al.alpha] + list(al.conj)
    V = mp.matrix([[r[j] ** k for j in range(al.d)] for k in range(al.d)])
    b = mp.matrix([mp.mpf(s) for s in seed])
    return list(mp.lu_solve(V, b))


def limit_profile(al, lam, R=60):
    """The bi-infinite limit profile beta_i of a ladder band, i = 1-R .. R.

    Forward (i >= 1) it is <lam (alpha-1) alpha^{-i}>; backward the same expression is
    a huge number, and M1 Lemma 2 replaces it by minus the conjugate sum, which is what
    makes it computable at all (and small, by the Pisot property):
        beta_{-k} = < - sum_j lam_j (alpha_j - 1) alpha_j^k >,  k >= 0 .
    """
    import mpmath as mp
    a = al.alpha
    fut = []
    for i in range(1, R + 1):
        x = lam[0] * (a - 1) * a ** (-i)
        fut.append(float(x - mp.nint(x)))
    past = []
    for k in range(0, R):
        x = mp.re(-sum(lam[j + 1] * (al.conj[j] - 1) * al.conj[j] ** k
                       for j in range(al.d - 1)))
        past.append(float(x - mp.nint(x)))
    return np.array(past[::-1] + fut)          # i = 1-R .. R, index R-1 is i = 0


def bernoulli_band(al, lam, R=60):
    """|E b| for the fair coin: the Erdos product over the limit profile."""
    b = limit_profile(al, lam, R)
    return float(np.prod(np.abs(np.cos(np.pi * b))))
