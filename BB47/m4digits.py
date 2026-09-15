#!/usr/bin/env python3
# (C) 2026 Ralf Stephan, in collaboration with Claude Code. Released under CC0 1.0 Universal.
"""M4 (plan-1047): generate base-b digit files for the constants under test.

Output format: one byte per digit, raw values 0..b-1 (not ASCII), fractional part only.
Usage: m4digits.py <name> <base> <ndigits> <outfile>
  name in {sqrt2, sqrt3, phi, sqrt5, pi}         -- algebraic / transcendental constants
       or {fib, skew, rand, planted:<P>:<name>}  -- synthetic control words (base 2 only)
"""
import sys, os, time
import gmpy2
import numpy as np


def frac_digits_int(name, base, nd):
    """floor(frac(x) * base**nd) as an mpz, for the named constant."""
    B = gmpy2.mpz(base) ** nd
    if name.startswith("sqrt"):
        m = int(name[4:])
        v = gmpy2.isqrt(gmpy2.mpz(m) * B * B)      # floor(sqrt(m)*base**nd)
    elif name == "phi":
        v = (B + gmpy2.isqrt(gmpy2.mpz(5) * B * B)) // 2
    elif name == "pi":
        gmpy2.get_context().precision = int(nd * gmpy2.log2(base)) + 64
        v = gmpy2.mpz(gmpy2.const_pi() * gmpy2.mpfr(B))
    else:
        raise ValueError(name)
    ip = v // B                                     # integer part
    return v - ip * B                               # fractional digits, nd of them


def to_bytes_digits(v, base, nd):
    if base == 2:
        nby = (nd + 7) // 8
        raw = int(v).to_bytes(nby, "big")
        bits = np.unpackbits(np.frombuffer(raw, dtype=np.uint8))
        return bits[len(bits) - nd:].copy()
    s = gmpy2.mpz(v).digits(base)
    a = np.frombuffer(s.encode("ascii"), dtype=np.uint8) - 48
    if len(a) < nd:                                 # leading zeros lost by digits()
        a = np.concatenate([np.zeros(nd - len(a), dtype=np.uint8), a])
    return a[len(a) - nd:].copy()


def sturmian(alpha, nd, rho=0.0):
    """Mechanical (Sturmian) word s_k = floor((k+1)a+r) - floor(ka+r), k=0..nd-1."""
    k = np.arange(nd + 1, dtype=np.float64)
    f = np.floor(k * alpha + rho)
    return (np.diff(f)).astype(np.uint8)


def fibword(nd):
    """Fibonacci word = Sturmian of slope 1/phi^2, by substitution 0->01, 1->0."""
    a = np.array([0], dtype=np.uint8)
    while len(a) < nd:
        out = np.empty(2 * len(a), dtype=np.uint8)
        out[0::2] = 0
        out[1::2] = 1
        keep = np.ones(2 * len(a), dtype=bool)
        keep[1::2] = (a == 0)
        a = out[keep]
    return a[:nd]


def skewword(nd, q=5, seed=1):
    """Branch-(b) control: eventually q-periodic both ways with one defect pair.
    Left ray period q pattern A, right ray the same period shifted by one -- i.e.
    x = ...AAA a b AAA... with exactly two consecutive break positions."""
    pat = np.array([0, 1, 1, 0, 1][:q], dtype=np.uint8)
    a = np.tile(pat, nd // q + 2)[:nd]
    mid = nd // 3
    a[mid] ^= 1                                     # one isolated defect
    return a


def main():
    name, base, nd, out = sys.argv[1], int(sys.argv[2]), int(sys.argv[3]), sys.argv[4]
    t = time.time()
    if name == "fib":
        a = fibword(nd)
    elif name.startswith("sturm:"):
        a = sturmian(float(name.split(":")[1]), nd)
    elif name == "skew":
        a = skewword(nd)
    elif name == "rand":
        a = np.random.default_rng(20260912).integers(0, base, nd, dtype=np.int64).astype(np.uint8)
    elif name.startswith("planted:"):
        _, P, host = name.split(":", 2)
        P = int(P)
        head = to_bytes_digits(frac_digits_int(host, base, P), base, P)
        tail = fibword(nd - P)
        a = np.concatenate([head, tail])
    else:
        a = to_bytes_digits(frac_digits_int(name, base, nd), base, nd)
    assert len(a) == nd and a.max() < base, (len(a), int(a.max()))
    a.tofile(out)
    print("%-18s b=%-3d N=%d  %.1fs  %s" % (name, base, nd, time.time() - t, out), flush=True)


if __name__ == "__main__":
    main()
