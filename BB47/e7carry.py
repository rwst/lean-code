#!/usr/bin/env python3
# (C) 2026 Ralf Stephan, in collaboration with Claude Code.
# Released under CC0 1.0 Universal (public-domain dedication).
"""E7 of plans/report-sqrtnorm.html: carry statistics of the square of sqrt 2.

For a 0/1 digit sequence a_0 a_1 ... (x = sum a_i 2^-i) put
  r(n)  = #{(i, j) : i + j = n, a_i = a_j = 1}      (the carry-free square, c_k of I1 §4.1)
  T(R)  = sum_{m >= 1} r(m + R) 2^-m                 (the BBP tail = carry into position R)
  V(N)  = sum_{n <= N} r(n)                          (the restricted sumset, with multiplicity)
For x = sqrt 2, T(R) is a positive integer, T(R) = 2T(R-1) - r(R), and T(R) >= 2 off the
positions R = 2i, a_i = 1 [Van18, §6].  The rank-#4 question: is T(R) = 2 frequent, i.e. is
V(N) close to 2N?  And is any carry/sumset statistic of sqrt 2 away from random digits?

Usage: python3 -I e7carry.py [N] [samples]      (defaults 100000, 200)
"""
import json
import math
import sys
from math import isqrt

import numpy as np

EXTRA = 96  # digits beyond N for the backward recursion of T


def digits_sqrt(d, q, M):
    """Binary digits a_0..a_M of sqrt(d) / 2^q (assumed in [1, 2))."""
    y = isqrt(d << (2 * (M - q)))  # floor(2^(M-q) sqrt d) = floor(2^M x)
    s = bin(y)[2:]
    assert len(s) == M + 1, (d, q, len(s), M)
    return np.frombuffer(s.encode(), dtype=np.uint8) - 48


def conv(a):
    """r(n) for n = 0..len(a)-1 (exact, via float FFT + rounding, checked)."""
    n = len(a)
    L = 1 << (2 * n - 1).bit_length()
    f = np.fft.rfft(a.astype(np.float64), L)
    r = np.fft.irfft(f * f, L)[: 2 * n - 1]
    ri = np.rint(r).astype(np.int64)
    assert np.max(np.abs(r - ri)) < 0.2
    assert ri.sum() == int(a.sum()) ** 2
    return ri


def tails(r, M):
    """T(R), R = 0..M-1, by the stable backward recursion T(R-1) = (T(R) + r(R)) / 2."""
    T = np.empty(M + 1)
    T[M] = r[M]  # crude start; the error is halved at each step
    for R in range(M, 0, -1):
        T[R - 1] = (T[R] + r[R]) / 2
    return T


def exact_tails_sqrt2(r, N):
    """Exact integer tails of sqrt 2: T(0) = 2 - r(0), T(R) = 2T(R-1) - r(R)."""
    T = [2 - int(r[0])]
    for R in range(1, N + 1):
        T.append(2 * T[-1] - int(r[R]))
    return T


def stats(a, N):
    """Carry and sumset statistics of the digit sequence a (length >= N + EXTRA + 1)."""
    M = N + EXTRA
    a = a[: M + 1]
    rfull = conv(a)           # r(n) exact for n <= M
    T = tails(rfull, M)[: N + 1]
    r = rfull[: N + 1]
    E = np.flatnonzero(a[: N + 1])
    k = len(E)
    lo = N // 2
    Rs = np.arange(lo, N + 1)
    V = int(r.sum())
    rE = conv(a[: N + 1])     # full sumset multiplicities of E = A ∩ [0, N]
    out = {
        "k/sqrtN": k / math.sqrt(N),
        "density": k / (N + 1),
        "V/(2N)": V / (2 * N),
        "V/N^2": V / N ** 2,
        "frac T<=2": float(np.mean(T[1:] <= 2 + 1e-9)),
        "frac T<=3": float(np.mean(T[1:] <= 3 + 1e-9)),
        "min T/R (R>=N/2)": float(np.min(T[lo:] / Rs)),
        "mean 4T/R (R>=N/2)": float(np.mean(4 * T[lo:] / Rs)),
        "sd (T-R/4)/sqrtR": float(np.std((T[lo:] - Rs / 4) / np.sqrt(Rs))),
        "sd (r-n/4)/sqrtn": float(np.std((r[lo:] - Rs / 4) / np.sqrt(Rs))),
        "|E+E ∩ [0,N]|/N": float(np.count_nonzero(r) / (N + 1)),
        "|E+E|/2N": float(np.count_nonzero(rE) / (2 * N + 1)),
        "energy/k^3": float((rE.astype(np.float64) ** 2).sum() / k ** 3) if k else 0.0,
        "lag1 corr": float(np.corrcoef(a[: N], a[1 : N + 1])[0, 1]) if 0 < k < N else 0.0,
        "parity bias/sqrtk": (int(a[0 : N + 1 : 2].sum()) - int(a[1 : N + 1 : 2].sum()))
        / math.sqrt(max(k, 1)),
    }
    return out, T, r


def thue_morse(M):
    i = np.arange(M + 1)
    tm = np.array([bin(int(j)).count("1") & 1 for j in i], dtype=np.uint8)
    return 1 - tm  # a_0 = 1


def dubickas_extremal(M, N, w=1.6):
    """Dubickas' extremal set {ceil((n/w)^2)} (sumset step sharp), scaled so it has ~w sqrt N
    elements up to N; it makes V(N) ~ 2N.  a_0 = 1."""
    a = np.zeros(M + 1, dtype=np.uint8)
    n = 0
    while True:
        v = math.ceil((n / w) ** 2)
        if v > M:
            break
        a[v] = 1
        n += 1
    return a


def main():
    N = int(sys.argv[1]) if len(sys.argv) > 1 else 100_000
    S = int(sys.argv[2]) if len(sys.argv) > 2 else 200
    M = N + EXTRA
    rng = np.random.default_rng(20261015)

    seqs = {
        "sqrt2": digits_sqrt(2, 0, M),
        "4-2sqrt2 (zeros of sqrt2)": None,
        "sqrt3": digits_sqrt(3, 0, M),
        "sqrt5/2": digits_sqrt(5, 1, M),
        "sqrt7/2": digits_sqrt(7, 1, M),
        "Thue-Morse": thue_morse(M),
        "Dubickas extremal w=1.6": dubickas_extremal(M, N),
    }
    # 4 - 2 sqrt 2 = 2 (2 - sqrt 2): its ones are the zeros of sqrt 2 (complement, I1 §3.2)
    y = (4 << M) - isqrt(8 << (2 * M))
    s = bin(y)[2:]
    assert len(s) == M + 1
    seqs["4-2sqrt2 (zeros of sqrt2)"] = np.frombuffer(s.encode(), dtype=np.uint8) - 48

    # exactness check for sqrt 2: forward integer recursion == backward float recursion
    a2 = seqs["sqrt2"]
    r2 = conv(a2[: M + 1])
    Tex = exact_tails_sqrt2(r2, N)
    Tfl = tails(r2, M)[: N + 1]
    assert all(t > 0 for t in Tex), "a tail is <= 0: digits wrong"
    assert max(abs(Tex[R] - Tfl[R]) for R in range(0, N + 1, max(1, N // 1000))) < 1e-6
    exc = [R for R in range(1, N + 1) if Tex[R] <= 2]
    odd_ok = all(Tex[R] % 2 == 0 or (R % 2 == 0 and a2[R // 2] == 1) for R in range(1, N + 1))

    results = {name: stats(a, N)[0] for name, a in seqs.items()}

    # random digits, density 1/2, a_0 = 1
    keys = list(results["sqrt2"].keys())
    samples = {kk: [] for kk in keys}
    for _ in range(S):
        a = rng.integers(0, 2, M + 1, dtype=np.uint8)
        a[0] = 1
        st = stats(a, N)[0]
        for kk in keys:
            samples[kk].append(st[kk])
    mu = {kk: float(np.mean(v)) for kk, v in samples.items()}
    sd = {kk: float(np.std(v)) for kk, v in samples.items()}

    # dyadic-scale profile of sqrt 2: min T(R)/R and frac T(R) <= 3 on [2^j, 2^(j+1))
    prof = []
    j = 1
    while (1 << (j + 1)) <= N + 1:
        seg = range(1 << j, 1 << (j + 1))
        prof.append({
            "j": j,
            "min T": min(Tex[R] for R in seg),
            "min 4T/R": min(4 * Tex[R] / R for R in seg),
            "#T<=3": sum(1 for R in seg if Tex[R] <= 3),
        })
        j += 1

    report = {
        "N": N, "samples": S,
        "sqrt2 exact": {
            "tails positive integers": True,
            "parity rule [Van18 §6] holds": odd_ok,
            "R in [1,N] with T(R) <= 2": exc,
            "first tails T(0..20)": Tex[:21],
        },
        "dyadic profile sqrt2": prof,
        "random mean": mu, "random sd": sd,
        "sequences": results,
        "z vs random": {name: {kk: (st[kk] - mu[kk]) / sd[kk] if sd[kk] > 0 else None
                               for kk in keys} for name, st in results.items()},
    }
    print(json.dumps(report, indent=1))


if __name__ == "__main__":
    main()
