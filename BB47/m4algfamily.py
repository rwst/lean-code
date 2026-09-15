#!/usr/bin/env python3
# (C) 2026 Ralf Stephan, in collaboration with Claude Code. Released under CC0 1.0 Universal.
"""M4 (plan-1047): scan a family of algebraic irrationals for the skew normal form.

M3 Thm. C: in branch (b) of Theorem B, xi = rho + delta * sum_j b^{-t_j} with
t_{j+1}-t_j -> oo.  Equivalently (M3 Prop. 6.1) the lag-q break set
T_q = {k : w_{k+q} != w_k} has density 0 in the tail, for q the least period.
So a skew algebraic number would show, for some q, a lag-q break density near 0.

This scans every real root in (0,1) of an integer polynomial of degree 2 or 3 with
bounded height, and reports the family minimum of min_q density(T_q) and the family
maximum of the reach N - K(q) of the M3 Prop. 6.1 three-in-a-row certificate.

Usage: m4algfamily.py <base> <bits> <H2> <H3> [qmax]
"""
import sys, time, math
from fractions import Fraction
import gmpy2
from gmpy2 import mpfr, mpz
import numpy as np


def divisors(n):
    n = abs(n)
    if n == 0:
        return []
    return [d for d in range(1, n + 1) if n % d == 0]


def rational_roots(coeffs):
    """exact rational roots, by the rational root theorem (ascending coeffs)."""
    c = list(coeffs)
    while len(c) > 1 and c[-1] == 0:
        c.pop()
    if len(c) < 2:
        return set()
    out = set()
    while len(c) > 1 and c[0] == 0:       # divide out the factor x
        c.pop(0)
        out.add(Fraction(0))
    if len(c) < 2:
        return out
    a0, ad = c[0], c[-1]
    for u in divisors(a0) or [0]:
        for v in divisors(ad):
            for s0 in (1, -1):
                r = Fraction(s0 * u, v)
                if sum(Fraction(a) * r ** i for i, a in enumerate(c)) == 0:
                    out.add(r)
    return out


def roots01(coeffs):
    """real roots in (0,1) of the integer polynomial sum coeffs[i] x^i (ascending)."""
    c = np.array(coeffs, dtype=float)
    while len(c) > 1 and c[-1] == 0:
        c = c[:-1]
    if len(c) < 2:
        return []
    r = np.roots(c[::-1])
    rat = rational_roots(coeffs)
    keep = []
    for z in r:
        if abs(z.imag) > 1e-9 or not (1e-6 < z.real < 1 - 1e-6):
            continue
        if any(abs(float(q) - z.real) < 1e-9 for q in rat):   # rational: not an irrational target
            continue
        keep.append(float(z.real))
    return keep


def refine(coeffs, x0, bits):
    """Newton-refine a simple root to `bits` bits of precision, doubling as we go."""
    d = [i * coeffs[i] for i in range(1, len(coeffs))]
    prec = 64
    gmpy2.get_context().precision = prec
    x = mpfr(x0)
    while True:
        prec = min(2 * prec, bits + 64)
        gmpy2.get_context().precision = prec
        x = mpfr(x)
        for _ in range(2):
            f = mpfr(0); fp = mpfr(0)
            for a in reversed(coeffs):
                f = f * x + a
            for a in reversed(d):
                fp = fp * x + a
            if fp == 0:
                return None
            x -= f / fp
        if prec >= bits + 64:
            return x


def bits_of(x, base, nd):
    B = mpz(base) ** nd
    v = mpz(gmpy2.floor(x * mpfr(B)))
    if base == 2:
        raw = int(v).to_bytes((nd + 7) // 8, "big")
        a = np.unpackbits(np.frombuffer(raw, dtype=np.uint8))
        return a[len(a) - nd:]
    s = mpz(v).digits(base)
    a = np.frombuffer(s.encode(), dtype=np.uint8) - 48
    return np.concatenate([np.zeros(nd - len(a), dtype=np.uint8), a]) if len(a) < nd else a[-nd:]


def scan(a, qmax):
    """returns (min over q of tail break density, argmin q, max over q of reach N-K)."""
    N = len(a)
    half = a[N // 2:]
    bd, bq, reach = 1.0, -1, 0
    for q in range(1, qmax + 1):
        d = half[q:] != half[:-q]
        m = float(d.mean())
        if m < bd:
            bd, bq = m, q
        dd = a[q:] != a[:-q]
        run3 = dd[:-2] & dd[1:-1] & dd[2:]
        idx = np.flatnonzero(run3)
        k = int(idx[-1] + 1) if len(idx) else 0
        if N - k > reach:
            reach = N - k
    return bd, bq, reach


def main():
    base, bits, H2, H3 = (int(x) for x in sys.argv[1:5])
    qmax = int(sys.argv[5]) if len(sys.argv) > 5 else 256
    nd = bits if base == 2 else int(bits / math.log2(base))
    polys = []
    for a2 in range(1, H2 + 1):
        for b in range(-H2, H2 + 1):
            for c in range(-H2, H2 + 1):
                polys.append((c, b, a2))
    for a3 in range(1, H3 + 1):
        for b in range(-H3, H3 + 1):
            for c in range(-H3, H3 + 1):
                for d in range(-H3, H3 + 1):
                    polys.append((d, c, b, a3))
    seen, out, t0 = set(), [], time.time()
    for p in polys:
        for r0 in roots01(p):
            key = round(r0, 12)
            if key in seen:
                continue
            seen.add(key)
            x = refine(list(p), r0, bits + 64)
            if x is None:
                continue
            a = bits_of(x, base, nd)
            bd, bq, reach = scan(a, qmax)
            out.append((bd, bq, reach, p, float(r0)))
    out.sort()
    print("# ALGFAM base=%d nd=%d deg2H=%d deg3H=%d qmax=%d roots=%d  %.0fs"
          % (base, nd, H2, H3, qmax, len(out), time.time() - t0))
    print("# lowest lag-q break densities in the family (a skew number would have ~0):")
    for bd, bq, reach, p, r0 in out[:10]:
        print("ALGLOW\t%.6f\tq=%d\treach=%d\tpoly=%s\troot=%.12f" % (bd, bq, reach, p, r0))
    print("ALGMAXREACH\t%d" % max(o[2] for o in out))
    print("ALGMINDENS\t%.6f" % out[0][0])


if __name__ == "__main__":
    main()
