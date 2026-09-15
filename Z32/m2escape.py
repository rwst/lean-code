#!/usr/bin/env python3
"""R-5 bridge for plan-z32-transform milestone M2 (the quantitative escape bound, target T4).

Five independent checks of `Z32/EscapeBound.lean`:

  A  the certificate shapes (K = |levels|, L = |blocks|) used in the Lean instances are re-derived
     by parsing `Z32/BlockCert.lean` and `Z32/UnionRecord.lean`, not taken from the Lean statements;
  B  the escape bound is VALID: exact rational simulation of the orbit for a grid of xi in [1, X]
     never exceeds the certified bound, at three values of X;
  C  the endgame machinery: on each simulated confined prefix, the carry word really is P-periodic
     from t with t + P <= L, the ladder identity q*M_{n+1} = p*M_n holds, q^m divides M_t, and the
     dichotomy of `Z32.escape_endgame` holds at the escape time;
  D  the SECOND logarithm is necessary: at the two-cell entry the escape time of xi = 5^-k grows
     like log_{3/2}(1/(5 xi)), so no bound in X alone can exist;
  E  the depth-K schema front end: `escapeSteps p q (K+2) X L` bounds the true escape time of the
     window [s, s+1/p) at several (p,q,s,K).

Runs in a few seconds, single core, exact arithmetic only (fractions + integers).
"""
import re
import sys
import time
from fractions import Fraction as Fr
from math import ceil, log

SRC = ["BlockCert.lean", "UnionRecord.lean"]


# ---------------------------------------------------------------- A: parse the certificates

def parse_certs(paths):
    """Independent parse of `def certX : Cert where ...` blocks."""
    txt = "\n\n".join(open(p).read() for p in paths)
    certs = {}
    for m in re.finditer(r"^def (cert\w+) : Cert where\n(.*?)(?=\n\n|\n/--|\n@\[)", txt,
                         re.M | re.S):
        name, body = m.group(1), m.group(2)
        f = {}
        for key in ("D", "p", "q", "closed"):
            mm = re.search(rf"^  {key} := (.*)$", body, re.M)
            if mm:
                f[key] = mm.group(1).strip()
        f.setdefault("p", "3")
        f.setdefault("q", "2")
        f.setdefault("closed", "false")
        # U and levels are bracketed lists, possibly multi-line
        def grab(key):
            i = body.find(f"  {key} := ")
            if i < 0:
                return None
            j = body.index("[", i)
            depth, k = 0, j
            while True:
                if body[k] == "[":
                    depth += 1
                elif body[k] == "]":
                    depth -= 1
                    if depth == 0:
                        break
                k += 1
            return body[j:k + 1]
        U = grab("U")
        lv = grab("levels")
        st = grab("strata")
        pairs = lambda t: [tuple(int(x) for x in p.split(",")) for p in
                           re.findall(r"\((-?\d+,\s*-?\d+)\)", t)]
        levels = []
        if lv:
            # top-level split of `[ [..], [..] ]`
            inner, depth, cur = [], 0, ""
            for ch in lv[1:-1]:
                if ch == "[":
                    depth += 1
                if ch == "]":
                    depth -= 1
                cur += ch
                if depth == 0 and ch == "]":
                    inner.append(cur)
                    cur = ""
            levels = [pairs(x) for x in inner]
        strata = []
        if st:
            inner, depth, cur = [], 0, ""
            for ch in st[1:-1]:
                if ch == "[":
                    depth += 1
                if ch == "]":
                    depth -= 1
                cur += ch
                if depth == 0 and ch == "]":
                    inner.append(cur)
                    cur = ""
            strata = [pairs(x) for x in inner]
        certs[name] = dict(D=int(f["D"]), p=int(f["p"]), q=int(f["q"]),
                           closed=(f["closed"] == "true"), U=pairs(U),
                           levels=levels, strata=strata)
    return certs


# ---------------------------------------------------------------- the orbit and the window

def in_set(c, y):
    """y (a Fraction in [0,1)) lies in the certified set."""
    D = c["D"]
    for (a, b) in c["U"]:
        if a <= D * y and (D * y <= b if c["closed"] else D * y < b):
            return True
    return False


def escape_time(c, xi, cap):
    """First n with {xi (p/q)^n} outside the certified set, or None past `cap`."""
    p, q = c["p"], c["q"]
    z = Fr(xi)
    for n in range(cap + 1):
        y = z - (z.numerator // z.denominator)
        if not in_set(c, y):
            return n
        z = z * Fr(p, q)
    return None


def carry_word(p, q, xi, N):
    """s_n = q x_{n+1} - p x_n with x_n = floor(xi (p/q)^n)."""
    x = []
    z = Fr(xi)
    for n in range(N + 2):
        x.append(z.numerator // z.denominator)
        z = z * Fr(p, q)
    return [q * x[n + 1] - p * x[n] for n in range(N + 1)], x


# ---------------------------------------------------------------- the bound, transcribed

def escape_steps(p, q, A, X, Lo):
    """`Z32.escapeSteps`, transcribed."""
    a = max(0, ceil(log(X * (p / q) ** A + 1, q)))
    b = max(0, ceil(log(q / Lo, p / q)))
    return A + 1 + a + b


def min_alpha(p, q, L, X):
    """least alpha with X (p/q)^L + 1 <= q^alpha, by exact integer comparison."""
    al = 0
    while Fr(X) * Fr(p, q) ** L + 1 > Fr(q) ** al:
        al += 1
    return al


ENTRIES = [
    # (lean theorem, cert, K, L, beta, constant A of the Lean statement)
    ("escape_sixth_3_8",     "certWindow38",      8,  3, 2, 14),
    ("escape_frontier",      "certFrontier",     13,  2, 2, 18),
    ("escape_union_712",     "certUnion712",      7,  1, 2, 11),
    ("escape_union_23",      "certUnion23",       9, 12, 2, 24),
    ("escape_union_2536",    "certUnion2536",    11, 17, 2, 31),
    ("escape_two_cell_fifth", "certTwoCellFifth",  1,  2, 2,  6),
    ("escape_four_three",    "certFourThree",     5,  2, 4, 12),
    ("escape_five_two_fifth", "certFiveTwo",       1,  1, 1,  4),
    ("escape_union_7083",    "certUnion7083",    17, 100, 2, 120),
]


def main():
    t0 = time.time()
    certs = parse_certs(SRC)
    print("== M2: the quantitative escape bound (target T4), R-5 checks ==")
    print()

    # ---- A -------------------------------------------------------------
    print("A. certificate shapes, re-parsed from Z32/{BlockCert,UnionRecord}.lean")
    bad = 0
    for name, cert, K, L, beta, A in ENTRIES:
        c = certs[cert]
        blocks = c["levels"][-1] if c["levels"] else c["U"]
        ok = (len(c["levels"]) == K and len(blocks) == L and c["strata"] == []
              and A == K + L + 1 + beta)
        bad += 0 if ok else 1
        print("   %-22s %-18s p/q=%d/%d  K=%2d L=%2d strata=%d  beta=%d  A=%2d  %s"
              % (name, cert, c["p"], c["q"], len(c["levels"]), len(blocks),
                 len(c["strata"]), beta, A, "ok" if ok else "MISMATCH"))
        # beta must really satisfy q <= (p/q)^beta
        assert Fr(c["q"]) <= Fr(c["p"], c["q"]) ** beta, (name, "beta too small")
    print("   ranked certificate excluded from M2: certDub08 (strata=%d) -- see the scope note"
          % len(certs["certDub08"]["strata"]))
    print("   shape mismatches: %d" % bad)
    print()

    # ---- B -------------------------------------------------------------
    print("B. the bound is valid: exact simulation vs the certified bound")
    tot, viol = 0, 0
    for name, cert, K, L, beta, A in ENTRIES:
        c = certs[cert]
        for X in (10, 10 ** 3, 10 ** 6):
            al = min_alpha(c["p"], c["q"], L, X)
            bound = A + al
            worst, worst_xi = -1, None
            # a deterministic grid of rationals in [1, X], plus the integers 1..40
            grid = [Fr(1) + Fr(k * (X - 1), 400) for k in range(401)]
            grid += [Fr(k) for k in range(1, 41) if k <= X]
            grid += [Fr(X) - Fr(1, 7 ** j) for j in range(1, 8)]
            for xi in grid:
                if not (1 <= xi <= X):
                    continue
                tot += 1
                e = escape_time(c, xi, bound + 40)
                if e is None or e > bound:
                    viol += 1
                if e is not None and e > worst:
                    worst, worst_xi = e, xi
            print("   %-22s X=10^%d  alpha=%2d  bound=%3d  worst observed=%2d  slack=%3d"
                  % (name, len(str(X)) - 1, al, bound, worst, bound - worst))
    print("   points tested: %d, violations: %d" % (tot, viol))
    print()

    # ---- C -------------------------------------------------------------
    print("C1. the endgame on real carry words: every periodic run obeys the ladder, the")
    print("    divisibility and the dichotomy of `Z32.escape_endgame`")
    nlad, ndvd, ndic, cbad, nruns = 0, 0, 0, 0, 0
    for (p, q) in [(3, 2), (4, 3), (5, 2), (7, 2), (10, 3)]:
        for nu in [Fr(0), Fr(-1, 6), Fr(-1, 2), Fr(1, 3)]:
            for xi in [Fr(1), Fr(2), Fr(7, 3), Fr(22, 7), Fr(1, 5), Fr(97, 11), Fr(1000, 3),
                       Fr(-5, 2), Fr(-1), Fr(123, 4)]:
                NW = 60
                x = []
                z = Fr(xi)
                for n in range(NW + 2):
                    v = z + nu
                    x.append(v.numerator // v.denominator)
                    z = z * Fr(p, q)
                w = [q * x[n + 1] - p * x[n] for n in range(NW + 1)]
                for P in range(1, 7):
                    t = 0
                    while t + P + 1 <= NW:
                        T = t
                        while T + P + 1 <= NW and w[T + P] == w[T]:
                            T += 1
                        if T > t:
                            nruns += 1
                            N = T + P            # `hper` holds for t <= n, n+P+1 <= N
                            M = lambda n: x[n + P] - x[n]
                            for n in range(t, N - P):
                                nlad += 1
                                if q * M(n + 1) != p * M(n):
                                    cbad += 1
                            m = N - t - P
                            ndvd += 1
                            if M(t) != 0 and M(t) % q ** m != 0:
                                cbad += 1
                            ndic += 1
                            left = Fr(q) ** m <= abs(xi) * Fr(p, q) ** (t + P) + 1
                            right = abs(xi) * Fr(p, q) ** (N - P) * (Fr(p, q) - 1) < 1
                            if not (left or right):
                                cbad += 1
                            t = T
                        else:
                            t += 1
    print("   periodic runs found %d; ladder checks %d, divisibility %d, dichotomy %d"
          % (nruns, nlad, ndvd, ndic))
    print("   failures: %d" % cbad)
    print()

    print("C2. the block-itinerary front end: the first repeat has t + P <= |H|")
    c2n, c2bad, c2skip = 0, 0, 0
    for name, cert, K, L, beta, A in ENTRIES:
        c = certs[cert]
        p, q = c["p"], c["q"]
        blocks = c["levels"][-1] if c["levels"] else c["U"]
        for xi in [Fr(a, b) for b in (1, 3, 7, 11, 19, 37) for a in range(1, 120)]:
            e = escape_time(c, xi, 200)
            if e is None or e == 0:
                continue
            nconf = e - 1                     # last confined index
            N1 = nconf - K                    # blocks available on [0, N1]
            if N1 < L:
                c2skip += 1
                continue
            z = Fr(xi)
            ys = []
            for n in range(nconf + 1):
                ys.append(z - (z.numerator // z.denominator))
                z = z * Fr(p, q)

            def blk(n):
                for I in blocks:
                    if I[0] <= c["D"] * ys[n] and (c["D"] * ys[n] <= I[1] if c["closed"]
                                                   else c["D"] * ys[n] < I[1]):
                        return I
                return None
            it = [blk(n) for n in range(N1 + 1)]
            if any(b is None for b in it):
                c2bad += 1
                continue
            t = P = None
            for j in range(1, L + 1):
                for i in range(j):
                    if it[i] == it[j]:
                        t, P = i, j - i
                        break
                if P is not None:
                    break
            c2n += 1
            if P is None or t + P > L:
                c2bad += 1
                continue
            w, x = carry_word(p, q, xi, N1 + P + 2)
            for n in range(t, N1):
                if n + P + 1 <= N1 and w[n + P] != w[n]:
                    c2bad += 1
    print("   itineraries checked %d (skipped %d as too short for the funnel), failures: %d"
          % (c2n, c2skip, c2bad))
    # how deep can a real orbit actually go?  search the flagship window along its surviving
    # 3-cycle 4/19 -> 6/19 -> 9/19, with integer parts b*2^j (the divisibility ladder's own shape)
    c = certs["certWindow38"]
    deep, deepxi, ntry = -1, None, 0
    for y0 in (Fr(4, 19), Fr(6, 19), Fr(9, 19)):
        for j in range(26):
            for b in (1, 3, 5, 7, 9, 11, 13):
                ntry += 1
                e = escape_time(c, Fr(b * 2 ** j) + y0, 400)
                if e is not None and e > deep:
                    deep, deepxi = e, Fr(b * 2 ** j) + y0
    print("   deepest confinement found at [1/6,13/24): %d steps over %d orbits (xi = %s)"
          % (deep, ntry, deepxi))
    print()

    # ---- D -------------------------------------------------------------
    print("D. the second logarithm is necessary (two-cell entry [0,1/5) u [4/5,1) at 3/2)")
    c = certs["certTwoCellFifth"]
    print("   xi            escape time   ceil(log_{3/2}(1/(5 xi)))")
    dbad = 0
    for k in range(0, 13):
        xi = Fr(1, 5 ** k) if k else Fr(1)
        e = escape_time(c, xi, 400)
        pred = max(0, ceil(log(1 / (5 * float(xi)), 1.5))) if xi < Fr(1, 5) else None
        print("   5^-%-2d %-9s %5s        %s" % (k, "", e, pred))
        if pred is not None and e != pred:
            dbad += 1
    # and: the bound for X = 1 (i.e. xi = 1) is 6 + alpha, far below these
    print("   escape times are unbounded as xi -> 0 while floor(xi) = 0: a bound in X alone")
    print("   cannot exist.  mismatches against the closed form: %d" % dbad)
    print()

    # ---- E -------------------------------------------------------------
    print("E. the depth-K schema front end (window [s, s+1/p), bound escapeSteps p q (K+2) X L)")

    def schema_escape(p, q, s, xi, cap):
        """first n with fract(xi (p/q)^n - s) >= 1/p."""
        z = Fr(xi)
        for n in range(cap + 1):
            u = z - s
            fr = u - (u.numerator // u.denominator)
            if fr >= Fr(1, p):
                return n
            z = z * Fr(p, q)
        return None

    def marked_depth(p, q, eps, cap=60):
        """least K with the marked orbit in the hole (Z32.Escape)."""
        w = Fr(0)
        for K in range(cap + 1):
            if Fr(q) <= p * (w + eps) and w + eps <= 1:
                return K
            if p * (w + eps) < q:
                w = Fr(p) * (w + eps) / q
            elif 1 <= w + eps:
                w = Fr(p) * (w + eps - 1) / q
            else:
                return None
        return None

    ebad, etot = 0, 0
    for (p, q, s) in [(5, 2, Fr(1, 6)), (5, 2, Fr(1, 2)), (5, 2, Fr(4, 105)),
                      (7, 2, Fr(1, 6)), (3, 2, Fr(1, 2)), (9, 2, Fr(1, 6)),
                      (10, 3, Fr(1, 6)), (11, 3, Fr(1, 2)), (5, 2, Fr(8, 585))]:
        theta = (p - q) * s
        eps = theta - (theta.numerator // theta.denominator)
        K = marked_depth(p, q, eps)
        if K is None:
            print("   (%d,%d) s=%-8s eps=%-10s not certified at any depth <= 60" % (p, q, s, eps))
            continue
        X, Lo = 10 ** 3, 1
        bound = escape_steps(p, q, K + 2, X, Lo)
        worst = -1
        for k in range(0, 300):
            xi = Fr(1) + Fr(k * (X - 1), 299)
            e = schema_escape(p, q, s, xi, bound + 40)
            etot += 1
            if e is None or e > bound:
                ebad += 1
            elif e > worst:
                worst = e
        print("   (%d,%d) s=%-8s eps=%-10s K=%d  bound=%3d  worst observed=%2d"
              % (p, q, s, eps, K, bound, worst))
    print("   points tested: %d, violations: %d" % (etot, ebad))
    print()

    ok = (bad == 0 and viol == 0 and cbad == 0 and c2bad == 0 and dbad == 0 and ebad == 0)
    print("VERDICT: %s" % ("all checks pass" if ok else "FAILURES PRESENT"))
    print("elapsed %.1f s" % (time.time() - t0), file=sys.stderr)
    return 0 if ok else 1


if __name__ == "__main__":
    sys.exit(main())
