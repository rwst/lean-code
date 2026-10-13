#!/usr/bin/env python3
# (C) 2026 Ralf Stephan, in collaboration with Claude Code.  CC0 1.0.
#
# exact_words.py -- plan-dubC2 milestone M1: the CELL-FREE cross-check.
#
# joint.py / joint.c approximate the archimedean coordinate by a grid of D
# cells, which is what makes the state space finite and the certificate
# kernel-checkable -- but a grid over-approximates, and G-3 showed the
# over-approximation is visible (the "tube" around a periodic orbit).  This
# script removes the grid entirely:  it enumerates the admissible carry words
# directly, carrying with each word the EXACT rational interval of y-values
# that realize it, together with the exact residue vector of x.
#
#     word w = s_0..s_{n-1}  admissible  <=>  I(w) := { y : the branch
#     sequence T_{s_0}, ..., T_{s_{n-1}} is defined at y }  is nonempty,
#     and every x_i, i <= n, is coprime to every member of P.
#
# There is no rounding anywhere, so the counts below are the exact
# word-complexity  p_n  of the joint (archimedean x residue) system.  If p_n
# stabilizes, the language is a finite set of eventually periodic words and
# [DN05] Lemma 2 finishes; if p_n grows exponentially, log p_n / n is the
# honest entropy of the survivor subshift, i.e. the T5 ledger.
#
# Usage:  ./exact_words.py --pq 3 2 --nu 1/2 --P 2,5 --n 60 [--words]

import argparse
from fractions import Fraction


def main():
    ap = argparse.ArgumentParser()
    ap.add_argument("--pq", nargs=2, type=int, default=[3, 2])
    ap.add_argument("--nu", default="1/2")
    ap.add_argument("--P", default="2,5")
    ap.add_argument("--n", type=int, default=60)
    ap.add_argument("--words", action="store_true", help="print the survivors")
    a = ap.parse_args()

    p, q = a.pq
    nu = Fraction(a.nu)
    w = Fraction(p - q) * nu
    P = sorted(int(t) for t in a.P.split(","))
    QL = [l for l in P if q % l != 0]
    M = 1
    for l in QL:
        M *= l

    # alphabet and its domains, exactly
    letters = []
    for s in range(-(p + q + 2), p + q + 3):
        lo = max(Fraction(0), (Fraction(s) + w) / p)
        hi = min(Fraction(1), (Fraction(s + q) + w) / p)
        if lo < hi:
            letters.append((s, lo, hi))

    # avoidance at the primes dividing q: q x' = p x + s with x !== 0 mod q
    # forces s !== 0 mod q (p is invertible mod q), and conversely.
    if q in P:
        letters = [(s, lo, hi) for (s, lo, hi) in letters if s % q]

    qinv = [pow(q, -1, l) for l in QL]

    # states: (residue index mod M, interval).  Start: every x_0 class, y in [0,1).
    starts = [r for r in range(M) if all(r % l for l in QL)] or [0]
    cur = [(r, Fraction(0), Fraction(1), ()) for r in starts]
    print(f"# exact word census   base {p}/{q}   nu = {nu}   P = {P}   M = {M}")
    print(f"# alphabet {[s for s, _, _ in letters]}"
          f"   domains {[(str(lo), str(hi)) for _, lo, hi in letters]}")
    print(f"{'n':>4} {'p_n':>10} {'p_n/p_(n-1)':>12}   total measure")
    prev = len(cur)
    for n in range(1, a.n + 1):
        nxt = []
        for (r, lo, hi, wd) in cur:
            for (s, dlo, dhi) in letters:
                a2, b2 = max(lo, dlo), min(hi, dhi)
                if a2 >= b2:
                    continue
                if QL:
                    r2, ok = 0, True
                    rest, mul = r, 1
                    # r is a plain residue mod M; step it mod M by CRT-free arithmetic
                    r2 = 0
                    for l, qi in zip(QL, qinv):
                        v2 = (qi * (p * (r % l) + s)) % l
                        if v2 == 0:
                            ok = False
                            break
                    if not ok:
                        continue
                    # recombine mod M by CRT
                    r2 = 0
                    for l, qi in zip(QL, qinv):
                        v2 = (qi * (p * (r % l) + s)) % l
                        Ml = M // l
                        r2 = (r2 + v2 * Ml * pow(Ml, -1, l)) % M
                else:
                    r2 = 0
                nxt.append((r2, (p * a2 - w - s) / q, (p * b2 - w - s) / q, wd + (s,)))
        cur = nxt
        meas = sum(b - a for _, a, b, _ in cur)
        print(f"{n:>4} {len(cur):>10} {len(cur)/max(prev,1):>12.5f}   {float(meas):.6e}")
        prev = len(cur)
        if not cur:
            print("# language empty -- no orbit avoids P at all beyond this length")
            break
    if a.words and cur:
        seen = set()
        for (r, lo, hi, wd) in cur:
            if wd[-24:] not in seen:
                seen.add(wd[-24:])
        print(f"# {len(seen)} distinct length-{min(24, a.n)} suffixes:")
        for t in sorted(seen)[:40]:
            print("   ", "".join("A" if x < 0 else "B" for x in t), t)


if __name__ == "__main__":
    main()
