#!/usr/bin/env python3
# (C) 2026 Ralf Stephan, in collaboration with Claude Code.  CC0 1.0.
#
# xscan.py -- plan-dubC2 milestone M1, experiment X0 (= gate G-4(b)):
# the numeric falsification scan.
#
# For a candidate set P, hunt for real xi whose orbit  x_n = [ xi (p/q)^n + nu ]
# avoids every member of P for a long prefix.  Everything is computed from the
# DEFINITION with exact integer arithmetic -- no carries, no cells, no graph --
# so this is a genuinely independent probe of the engine's verdict:
#
#     U_0 = A p^0 nud + nun B q^0,   V_0 = B nud,   T_0 = nun B,
#     U_{n+1} = p U_n + (q - p) T_n,  V_{n+1} = q V_n,  T_{n+1} = q T_n,
#     x_n = U_n div V_n           for  xi = A/B.
#
# Three families of xi:
#   random    A/B with B ~ 10^6                       -- the null model
#   dyadic    A/2^j, A/3^j, ...                       -- the structured probes
#   shadow    rationals engineered to shadow a given periodic carry word for as
#             long as the precision allows            -- the adversarial probe
#
# If the engine says C_det(P) holds, no xi avoids P forever, and the only long
# prefixes must come from shadowing one of the finitely many periodic carry
# words the engine printed.  A long prefix from an UNSTRUCTURED xi would be
# evidence against the engine, i.e. a falsification.  (Nothing here can prove
# unavoidability: the question is about all xi.)
#
# Usage:
#   ./xscan.py --pq 3 2 --nu 1/2 --P 2,5,7,11 --n 400 --random 20000
#   ./xscan.py --pq 3 2 --nu 1/2 --P 2,5,7,11 --word 1,1,-1,-1 --shadow 60

import argparse
import random
import sys
from fractions import Fraction


def prefix_len(A, B, p, q, nun, nud, P, nmax):
    """Largest N <= nmax with x_0..x_N all coprime to every member of P
    (i.e. avoiding), computed from the definition."""
    U = A * nud + nun * B
    V = B * nud
    T = nun * B
    n = 0
    while n <= nmax:
        x = U // V
        for l in P:
            if x % l == 0:
                return n - 1
        U = p * U + (q - p) * T
        V = q * V
        T = q * T
        n += 1
    return nmax


def shadow_xi(word, p, q, nun, nud, reps):
    """A rational xi whose carry word starts with `word` repeated `reps` times.
    Invert the recurrence: the y-interval of a word is
        I(s_0..s_{m-1}) = { y : T_{s_0}...  admissible },
    computed backwards by  T_s^{-1}[a,b) = [ (q a + w + s)/p , (q b + w + s)/p ).
    Any y in the (nonempty) interval works; take its midpoint."""
    w = Fraction(p - q) * Fraction(nun, nud)
    lo, hi = Fraction(0), Fraction(1)
    for s in reversed(word * reps):
        dlo = max(Fraction(0), (Fraction(s) + w) / p)
        dhi = min(Fraction(1), (Fraction(s + q) + w) / p)
        lo2 = (q * lo + w + s) / p
        hi2 = (q * hi + w + s) / p
        lo, hi = max(lo2, dlo), min(hi2, dhi)
        if lo >= hi:
            return None
    return (lo + hi) / 2


def construct(word, m, p, q, nun, nud, P):
    """Build an explicit xi whose carry word begins with `word` repeated to
    length m, and whose orbit avoids P for as long as that lasts.

    With s_0..s_{m-1} fixed, q^n x_n = p^n x_0 + c_n,  c_n = sum_{i<n} p^{n-1-i} q^i s_i,
    so integrality of x_n pins x_0 modulo q^n:  x_0 = -p^{-n} c_n (mod q^n).
    The avoidance conditions at the primes l !| q are conditions on x_0 mod M,
    M = prod of them, and the two moduli are coprime -- so CRT gives x_0, and
    y_0 is any point of the word's (nonempty) y-interval.  Then xi = x_0 + y_0 - nu.

    Returns (xi, verified_prefix) with the prefix RE-MEASURED from the
    definition by prefix_len, so nothing here is taken on trust."""
    W = (word * (m // len(word) + 1))[:m]
    M = 1
    for l in P:
        if q % l != 0:
            M *= l
    # c_n and the forced class of x_0 mod q^m
    c = [0]
    for i in range(m):
        c.append(p * c[-1] + (q ** i) * W[i])
    qm = q ** m
    x0_q = (-pow(p, -m, qm) * c[m]) % qm if m else 0
    # allowed x_0 mod M
    ok = []
    for r in range(M):
        good = True
        for n in range(m + 1):
            xn = ((pow(p, n, M * q ** n) * r + c[n]) // 1) % (M * q ** n)
            xn = ((pow(p, n, M) * r + c[n] % M) * pow(q, -n, M)) % M
            if any(xn % l == 0 for l in P if q % l != 0):
                good = False
                break
        if good:
            ok.append(r)
    if not ok:
        return None, -1
    # CRT
    inv = pow(qm % M, -1, M)
    best = (None, -1)
    w = Fraction(p - q) * Fraction(nun, nud)
    lo, hi = Fraction(0), Fraction(1)
    for s in reversed(W):
        dlo = max(Fraction(0), (Fraction(s) + w) / p)
        dhi = min(Fraction(1), (Fraction(s + q) + w) / p)
        lo = max((q * lo + w + s) / p, dlo)
        hi = min((q * hi + w + s) / p, dhi)
        if lo >= hi:
            return None, -1
    y0 = (lo + hi) / 2
    for r in ok:
        t = ((r - x0_q) * inv) % M
        x0 = x0_q + qm * t
        if x0 <= 0:
            x0 += qm * M
        xi = Fraction(x0) + y0 - Fraction(nun, nud)
        L = prefix_len(xi.numerator, xi.denominator, p, q, nun, nud, P, m + 40)
        if L > best[1]:
            best = (xi, L)
    return best


def main():
    ap = argparse.ArgumentParser()
    ap.add_argument("--pq", nargs=2, type=int, default=[3, 2])
    ap.add_argument("--nu", default="1/2")
    ap.add_argument("--P", default="2,5,7,11")
    ap.add_argument("--n", type=int, default=400, help="prefix cap")
    ap.add_argument("--random", type=int, default=20000)
    ap.add_argument("--seed", type=int, default=20260819)
    ap.add_argument("--word", default="", help="carry word to shadow, comma sep")
    ap.add_argument("--shadow", type=int, default=40, help="repetitions")
    ap.add_argument("--construct", default="", help="lengths, e.g. 8,16,32,64")
    a = ap.parse_args()

    p, q = a.pq
    nu = Fraction(a.nu)
    nun, nud = nu.numerator, nu.denominator
    P = sorted(int(t) for t in a.P.split(","))
    rnd = random.Random(a.seed)

    print(f"# X0 falsification scan   base {p}/{q}   nu = {nu}   P = {P}"
          f"   prefix cap {a.n}")

    if a.word and a.construct:
        word = [int(t) for t in a.word.split(",")]
        print(f"# explicit construction: xi shadowing {word} for m steps")
        for m in [int(t) for t in a.construct.split(",")]:
            xi, L = construct(word, m, p, q, nun, nud, P)
            if xi is None:
                print(f"  m {m:>5}: no admissible x_0")
                continue
            print(f"  m {m:>5}: verified avoiding prefix {L:>5}   "
                  f"xi = {str(xi)[:70]}{'...' if len(str(xi)) > 70 else ''}")
        return

    if a.word:
        word = [int(t) for t in a.word.split(",")]
        print(f"# adversarial shadow of the periodic carry word {word}")
        for reps in range(1, a.shadow + 1):
            y = shadow_xi(word, p, q, nun, nud, reps)
            if y is None:
                print(f"  reps {reps:>3}: word not admissible")
                break
            # xi = x_0 + y - nu with x_0 ranging over the residues that matter
            best, bestx = -1, None
            for x0 in range(1, 4000):
                xi = Fraction(x0) + y - nu
                if xi <= 0:
                    continue
                L = prefix_len(xi.numerator, xi.denominator, p, q, nun, nud, P, a.n)
                if L > best:
                    best, bestx = L, x0
            print(f"  reps {reps:>3}: word length {len(word)*reps:>4}   "
                  f"best avoiding prefix {best:>4}  (x_0 = {bestx})")
        return

    hist = {}
    best, bestxi = -1, None
    for _ in range(a.random):
        A = rnd.randrange(1, 10 ** 6)
        B = rnd.randrange(1, 10 ** 6)
        L = prefix_len(A, B, p, q, nun, nud, P, a.n)
        hist[L] = hist.get(L, 0) + 1
        if L > best:
            best, bestxi = L, (A, B)
    print(f"# {a.random} random xi = A/B, A,B < 10^6")
    for L in sorted(hist):
        print(f"  prefix {L:>4} : {hist[L]:>8}")
    print(f"# longest random prefix {best}  at xi = {bestxi[0]}/{bestxi[1]}")

    print("# structured probes")
    best2, arg2 = -1, None
    for base in (2, 3, 5, 6, 7, 10, 11):
        for j in range(1, 14):
            for A in range(1, 200):
                L = prefix_len(A, base ** j, p, q, nun, nud, P, a.n)
                if L > best2:
                    best2, arg2 = L, (A, base, j)
    print(f"# longest structured prefix {best2}  at xi = {arg2[0]}/{arg2[1]}^{arg2[2]}")
    print("# integer and half-integer xi")
    best3, arg3 = -1, None
    for A in range(1, 20000):
        for den in (1, 2, 3, 4):
            L = prefix_len(A, den, p, q, nun, nud, P, a.n)
            if L > best3:
                best3, arg3 = L, (A, den)
    print(f"# longest small-denominator prefix {best3}  at xi = {arg3[0]}/{arg3[1]}")


if __name__ == "__main__":
    main()
