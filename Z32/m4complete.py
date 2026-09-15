#!/usr/bin/env python3
"""R-5 bridge for plan-z32-transform milestone M4 (completeness and the obstruction, target T5).

Six independent checks of `Z32/CertComplete.lean`:

  A  the five new closed-convention certificates are re-checked from scratch: the funnel condition
     `funnelOk` and the ranked determinism `funcOk` are re-implemented here from the definitions in
     `Z32/BlockCert.lean` and run on the certificate data parsed out of `Z32/CertComplete.lean` --
     no Lean, no `decide`, no trust in the generator;
  B  `Z32.step_unique`: over many bases and many rationals, a point of [0,1) whose denominator is
     coprime to q has EXACTLY ONE successor in [0,1) whose denominator is coprime to q (the Lean
     theorem claims "at most one"; the count is always 1, and the two-successor configuration that
     the closed convention would need is measured to be absent);
  C  `Z32.cyclePoint_eq_base` (C-2 at every base): every periodic point of the carry relation found
     by exhaustive search has denominator dividing p^P - q^P;
  D  the two-cell chain of `Z32.BlockCert.twoCellPt`/`twoCellOrbit`/`twoCellCarry`: the Lean
     definitions are re-evaluated here and checked to obey the recursion and to stay inside the
     CLOSED [0,1/5] u [4/5,1] -- and to leave the HALF-OPEN [0,1/5) u [4/5,1) at once, which is why
     the half-open entry certifies and the closed one needs ranks;
  E  the atlas survey: for each of the ten entries, in both conventions, the least funnel depth at
     which the exact funnel admits an unranked / a ranked certificate (the rank being
     |reachable set|, the function `Z32.CertComplete` shows always works when it works at all);
  F  the block bound of `Cert.eq_of_memI_block`: for every unranked atlas entry, the number of
     surviving funnel components is at most the number of blocks the Lean certificate uses.

Exact arithmetic throughout (fractions and integers).  Runs in a couple of minutes.
"""
import re
import sys
import time
from fractions import Fraction as Fr
from math import gcd, lcm

SRC = ["BlockCert.lean", "CertComplete.lean"]
CAP_UNION_CLOSED = 16          # depth cap for the three closed unions (they are refusals)
CAP = 22                       # depth cap everywhere else


# ------------------------------------------------------------------ parsing the Lean sources

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

        def pairs(t):
            return [tuple(int(x) for x in p.split(",")) for p in
                    re.findall(r"\((-?\d+,\s*-?\d+)\)", t)]

        def listlist(t):
            if t is None:
                return []
            inner, depth, cur = [], 0, ""
            for ch in t[1:-1]:
                if ch == "[":
                    depth += 1
                if ch == "]":
                    depth -= 1
                cur += ch
                if depth == 0 and ch == "]":
                    inner.append(cur)
                    cur = ""
            return [pairs(x) for x in inner]

        certs[name] = dict(D=int(f["D"]), p=int(f["p"]), q=int(f["q"]),
                           closed=(f["closed"] == "true"), U=pairs(grab("U")),
                           levels=listlist(grab("levels")), strata=listlist(grab("strata")))
    return certs


# ------------------------------------------- A: the two Bool checks, re-implemented from scratch

def carries(p, q):
    return list(range(1 - q, p))


def rle(cl, x, y):
    return x <= y if cl else x < y


def piece_ok(D, p, q, cl, nxt, I, J, s):
    """`Z32.BlockCert.pieceOk`, re-derived: the piece {y in J : (py-s)/q in I}, scaled by pD, is
    empty or inside a single interval of `nxt`."""
    A, C = q * I[0] + s * D, q * I[1] + s * D
    B, E = p * J[0], p * J[1]
    if rle(not cl, C, A) or rle(not cl, C, B) or rle(not cl, E, A) or rle(not cl, E, B):
        return True
    lo, hi = max(A, B), min(C, E)
    return any(p * K[0] <= lo and hi <= p * K[1] for K in nxt)


def funnel_ok(c):
    D, p, q, cl, U = c["D"], c["p"], c["q"], c["closed"], c["U"]
    cur = U
    for nxt in c["levels"]:
        for I in cur:
            for s in carries(p, q):
                for J in U:
                    if not piece_ok(D, p, q, cl, nxt, I, J, s):
                        return False
        cur = nxt
    return True


def blocks_of(c):
    return c["levels"][-1] if c["levels"] else c["U"]


def hits(D, p, q, cl, I, J, s):
    return (rle(cl, p * I[0], p * I[1]) and rle(cl, p * I[0], q * J[1] + s * D)
            and rle(cl, q * J[0] + s * D, p * I[1])
            and rle(cl, q * J[0] + s * D, q * J[1] + s * D))


def out_edges(c, I):
    D, p, q, cl = c["D"], c["p"], c["q"], c["closed"]
    H = blocks_of(c)
    return [(s, J) for s in carries(p, q) for J in H if hits(D, p, q, cl, I, J, s)]


def rank_of(strata, I):
    for k, st in enumerate(strata):
        if I in st:
            return k
    return len(strata)


def func_ok(c):
    st = c["strata"]
    for I in blocks_of(c):
        es = out_edges(c, I)
        if any(rank_of(st, J) > rank_of(st, I) for (s, J) in es):
            return False
        if len([1 for (s, J) in es if rank_of(st, J) == rank_of(st, I)]) > 1:
            return False
    return True


def cert_ok(c):
    return (c["D"] > 0 and 1 < c["q"] < c["p"] and gcd(c["p"], c["q"]) == 1
            and funnel_ok(c) and func_ok(c))


# ------------------------------------------------------- the exact funnel (engine-independent)

def norm(ivs, cl):
    out = [(a, b) for (a, b) in ivs if (a < b) or (cl and a == b)]
    out.sort()
    res = []
    for (a, b) in out:
        if res and a <= res[-1][1]:
            res[-1] = (res[-1][0], max(res[-1][1], b))
        else:
            res.append((a, b))
    return res


def inter(l1, l2, cl):
    out = []
    for (a, b) in l1:
        for (c, d) in l2:
            lo, hi = max(a, c), min(b, d)
            if (lo < hi) or (cl and lo == hi):
                out.append((lo, hi))
    return norm(out, cl)


def preimage(ivs, p, q, cl):
    out = []
    for (c, d) in ivs:
        for s in carries(p, q):
            lo, hi = (q * c + s) / Fr(p), (q * d + s) / Fr(p)
            if hi >= 0 and lo <= 1:
                out.append((lo, hi))
    return norm(out, cl)


def graph(H, p, q, cl):
    E = {}
    for i, I in enumerate(H):
        e = []
        for s in carries(p, q):
            for j, J in enumerate(H):
                a, b = p * I[0], p * I[1]
                u, v = q * J[0] + s, q * J[1] + s
                lo, hi = max(a, u), min(b, v)
                if (lo < hi) or (cl and lo <= hi):
                    e.append((s, j))
        E[i] = e
    return E


def reach_rank(E):
    R = {}
    for i in E:
        seen, st = {i}, [i]
        while st:
            u = st.pop()
            for (s, v) in E[u]:
                if v not in seen:
                    seen.add(v)
                    st.append(v)
        R[i] = seen
    vals = sorted({len(R[i]) for i in E})
    idx = {v: k for k, v in enumerate(vals)}
    return {i: idx[len(R[i])] for i in E}, R


def graph_func_ok(E, rk):
    for i in E:
        if any(rk[j] > rk[i] for (s, j) in E[i]):
            return False
        if len([1 for (s, j) in E[i] if rk[j] == rk[i]]) > 1:
            return False
    return True


def alive(E):
    live = set(E)
    changed = True
    while changed:
        changed = False
        for i in list(live):
            if not any(j in live for (s, j) in E[i]):
                live.discard(i)
                changed = True
    return live


def first_ok(U, p, q, cl, cap):
    """least funnel depth admitting an unranked / a ranked certificate on the exact funnel,
    with the component and stratum counts recorded at the ranked depth (at the cap if none)"""
    lev = norm(U, cl)
    U0 = lev
    ku = kr = None
    nc = ns = 0
    for K in range(cap + 1):
        E = graph(lev, p, q, cl)
        rk, _ = reach_rank(E)
        if ku is None and graph_func_ok(E, {i: 0 for i in E}):
            ku = K
        if kr is None and graph_func_ok(E, rk):
            kr = K
            nc, ns = len(lev), len(set(rk.values()))
        if ku is not None and kr is not None:
            return ku, kr, nc, ns
        if kr is None:
            nc, ns = len(lev), len(set(rk.values()))
        lev = inter(U0, preimage(lev, p, q, cl), cl)
    if kr is None:
        E = graph(lev, p, q, cl)
        rk, _ = reach_rank(E)
        nc, ns = len(lev), len(set(rk.values()))
    return ku, kr, nc, ns


# ------------------------------------------------------------------ the ten atlas entries

def IV(D, *xs):
    return [(Fr(xs[2 * i], D), Fr(xs[2 * i + 1], D)) for i in range(len(xs) // 2)]


ATLAS = [
    ("sixth_3_8   [1/6,13/24)", IV(24, 4, 13), 3, 2, "certWindow38"),
    ("frontier",                IV(3600, 961, 2427), 3, 2, "certFrontier"),
    ("union712    7/12",        IV(12, 0, 2, 3, 4, 5, 8, 9, 10), 3, 2, "certUnion712"),
    ("union23     2/3",         IV(18, 0, 2, 3, 8, 9, 10, 11, 14, 15, 16), 3, 2, "certUnion23"),
    ("union2536   25/36",       IV(36, 0, 3, 4, 11, 16, 24, 25, 27, 30, 32, 33, 36), 3, 2,
     "certUnion2536"),
    ("twoCell     2/5",         IV(5, 0, 1, 4, 5), 3, 2, "certTwoCellFifth"),
    ("dub08       20/39",       IV(39, 8, 18, 21, 31), 3, 2, "certDub08"),
    ("fourThree   7/24",        IV(24, 8, 15), 4, 3, "certFourThree"),
    ("fiveTwo     1/5",         IV(5, 1, 2), 5, 2, "certFiveTwo"),
]


# ------------------------------------------------------------------ the Lean definitions, re-run

def twoCellPt(k):
    return Fr(1, 5) * Fr(2, 3) ** k


def twoCellOrbit(j, n):
    if n <= j:
        return twoCellPt(j - n)
    return Fr(4, 5) if (n - j) % 2 == 1 else Fr(1, 5)


def twoCellCarry(j, n):
    if n < j:
        return 0
    return -1 if (n - j) % 2 == 0 else 2


def main():
    t0 = time.time()
    certs = parse_certs([f"{p}" for p in SRC])
    print("plan-z32-transform M4 (target T5): completeness, the obstruction, and the")
    print("closed-convention entries -- independent re-check of Z32/CertComplete.lean")
    print()

    # ---------------------------------------------------------------- A
    print("A. the five new closed certificates, re-checked from the definitions")
    NEW = ["certTwoCellFifthClosed", "certWindow38Closed", "certFrontierClosed",
           "certFourThreeClosed", "certFiveTwoClosed"]
    abad = 0
    for name in NEW:
        c = certs[name]
        ok = cert_ok(c)
        H = blocks_of(c)
        if not ok:
            abad += 1
        print("   %-24s p/q=%d/%d closed=%s D=%-8d K=%d blocks=%2d strata=%d  ok=%s"
              % (name, c["p"], c["q"], c["closed"], c["D"], len(c["levels"]), len(H),
                 len(c["strata"]), ok))
    # and the control: the same certificates with the strata thrown away must FAIL
    cbad = 0
    for name in NEW:
        c = dict(certs[name])
        if len(c["strata"]) <= 1:
            continue
        c["strata"] = []
        if cert_ok(c):
            cbad += 1
        print("   %-24s unranked control: ok=%s (must be False)" % (name, cert_ok(c)))
    print("   certificates re-checked: %d, failures: %d; unranked controls wrongly passing: %d"
          % (len(NEW), abad, cbad))
    print()

    # ---------------------------------------------------------------- B
    print("B. step_unique: successors with denominator coprime to q")
    bases = [(3, 2), (4, 3), (5, 2), (5, 3), (5, 4), (7, 2), (7, 3), (7, 4), (7, 5), (7, 6),
             (9, 2), (11, 3), (8, 3), (9, 4), (13, 5)]
    tot, bad, exactly_one, two_ends = 0, 0, 0, 0
    for (p, q) in bases:
        for D in range(1, 40):
            if gcd(D, q) != 1:
                continue
            for a in range(0, D):
                y = Fr(a, D)
                succ = []
                for s in range(-q - 1, p + 1):
                    z = (p * y - s) / q
                    if 0 <= z < 1 and gcd(z.denominator, q) == 1:
                        succ.append((s, z))
                tot += 1
                if len(succ) > 1:
                    bad += 1
                if len(succ) == 1:
                    exactly_one += 1
                # the closed-convention exception: y in [0,1] with p*y an integer
                zz = [(p * y - s) / q for s in range(-q - 1, p + 1)
                      if 0 <= (p * y - s) / q <= 1 and gcd(((p * y - s) / q).denominator, q) == 1]
                if len(zz) > 1:
                    two_ends += 1
                    if set(zz) != {Fr(0), Fr(1)}:
                        bad += 1
    print("   points tested: %d over %d bases; more than one coprime successor in [0,1): %d"
          % (tot, len(bases), bad))
    print("   exactly one coprime successor: %d (so the recurrent dynamics is a total function)"
          % exactly_one)
    print("   points of [0,1] with two coprime successors in [0,1] (the closed-convention"
          " exception, always {0,1}): %d" % two_ends)
    print()

    # ---------------------------------------------------------------- C
    print("C. C-2 at every base: periodic points have denominator dividing p^P - q^P")
    ctot, cbad2, cundef, cper = 0, 0, 0, {}
    for (p, q) in [(3, 2), (4, 3), (5, 2), (5, 3), (7, 2), (7, 4), (9, 2), (11, 3)]:
        for D in range(1, 121):
            if gcd(D, q) != 1:
                continue
            # the unique coprime-denominator successor is a map on {0,...,D-1}
            f = [0] * D
            for a in range(D):
                y = Fr(a, D)
                nxt = [(p * y - s) / q for s in range(-q - 1, p + 1)
                       if 0 <= (p * y - s) / q < 1
                       and gcd(((p * y - s) / q).denominator, q) == 1]
                if len(nxt) != 1:
                    cundef += 1
                    f[a] = a
                else:
                    f[a] = int(nxt[0] * D)
            colour, oncyc = [0] * D, [False] * D
            for a in range(D):
                if colour[a]:
                    continue
                path, seen, b = [], {}, a
                while colour[b] == 0 and b not in seen:
                    seen[b] = len(path)
                    path.append(b)
                    b = f[b]
                if colour[b] == 0:
                    for z in path[seen[b]:]:
                        oncyc[z] = True
                for z in path:
                    colour[z] = 1
            for a in range(D):
                if not oncyc[a]:
                    continue
                b, P = f[a], 1
                while b != a:
                    b, P = f[b], P + 1
                ctot += 1
                if (p ** P - q ** P) % Fr(a, D).denominator != 0:
                    cbad2 += 1
                cper[(p, q)] = max(cper.get((p, q), 0), P)
    print("   cycle points found: %d; denominator not dividing p^P - q^P: %d;"
          " undefined successors: %d" % (ctot, cbad2, cundef))
    print("   longest period per base: %s"
          % ", ".join("%d/%d:%d" % (a, b, P) for (a, b), P in sorted(cper.items())))
    print()

    # ---------------------------------------------------------------- D
    print("D. the two-cell chain of Z32.BlockCert.twoCellPt / twoCellOrbit / twoCellCarry")
    closed_U = [(Fr(0), Fr(1, 5)), (Fr(4, 5), Fr(1))]
    dbad = dmem = dopen = 0
    for j in range(0, 60):
        for n in range(0, 80):
            lhs = 2 * twoCellOrbit(j, n + 1)
            rhs = 3 * twoCellOrbit(j, n) - twoCellCarry(j, n)
            if lhs != rhs:
                dbad += 1
            y = twoCellOrbit(j, n)
            if not (0 <= y < 1):
                dbad += 1
            if not any(a <= y <= b for (a, b) in closed_U):
                dmem += 1
            if not any(a <= y < b for (a, b) in closed_U):
                dopen += 1
    print("   recursion 2*y(n+1) = 3*y(n) - w(n) over 60 chains x 80 steps: failures %d" % dbad)
    print("   points outside the CLOSED [0,1/5] u [4/5,1]: %d" % dmem)
    print("   points outside the HALF-OPEN [0,1/5) u [4/5,1): %d (the chain dies at 1/5)" % dopen)
    print("   twoCellPt injective on k <= 400: %s"
          % (len({twoCellPt(k) for k in range(401)}) == 401))
    print()

    # ---------------------------------------------------------------- E
    print("E. atlas survey: least exact-funnel depth admitting a certificate")
    print("   entry                     conv        unranked   ranked   comps  strata")
    print("   (comps/strata counted at the ranked depth; at the cap when there is none)")
    rows = []
    for (nm, U, p, q, cname) in ATLAS:
        for cl in (False, True):
            cap = CAP_UNION_CLOSED if (cl and "union" in nm) else CAP
            ku, kr, nc, ns = first_ok(U, p, q, cl, cap)
            rows.append((nm, cl, ku, kr, nc, ns, cap))
            print("   %-25s %-10s  %-9s  %-7s  %4d   %d"
                  % (nm, "closed" if cl else "half-open",
                     "-" if ku is None else str(ku), "-" if kr is None else str(kr), nc, ns))
    nclosed = sum(1 for r in rows if r[1] and r[3] is not None)
    print("   closed-convention entries with a ranked certificate: %d of %d"
          % (nclosed, sum(1 for r in rows if r[1])))
    print()

    # ---------------------------------------------------------------- F
    print("F. the block bound of Cert.eq_of_memI_block: surviving components vs Lean blocks")
    fbad = 0
    for (nm, U, p, q, cname) in ATLAS:
        c = certs[cname]
        if c["strata"]:
            print("   %-25s ranked (strata=%d) -- the bound does not apply"
                  % (nm, len(c["strata"])))
            continue
        lev = norm(U, False)
        U0 = lev
        for _ in range(len(c["levels"]) + 8):
            lev = inter(U0, preimage(lev, p, q, False), False)
        E = graph(lev, p, q, False)
        live = alive(E)
        nb = len(blocks_of(c))
        if len(live) > nb:
            fbad += 1
        print("   %-25s surviving components %2d <= blocks %2d : %s"
              % (nm, len(live), nb, len(live) <= nb))
    print("   violations of |hold set| <= |blocks|: %d" % fbad)
    print()

    ok = (abad == 0 and cbad == 0 and bad == 0 and cbad2 == 0 and cundef == 0
          and dbad == 0 and dmem == 0 and fbad == 0)
    print("VERDICT: %s" % ("all checks pass" if ok else "FAILURES PRESENT"))
    print("elapsed %.1f s" % (time.time() - t0), file=sys.stderr)
    return 0 if ok else 1


if __name__ == "__main__":
    sys.exit(main())
