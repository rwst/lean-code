#!/usr/bin/env python3
"""plan-z32-transform experiment X-U: union-pattern autopsy (decides conjecture C-8 / target T6).

C-8 reads: *the record unions remove eps-neighborhoods of the period-<=P cycle spine plus its
bounded backward tree; |U_P| >= 1 - C(q/p)^{cP} is achievable.*  This script tests both halves on
the four largeness records at base 3/2 -- 25/36 (36 cells), 17/24 (48), 43/60 (60), 89/120 (240) --
with exact arithmetic and no engine in the loop.

  A  the recurrent map in closed form.  M4's `Z32.step_unique` says a point of [0,1) whose
     denominator is coprime to q has exactly one successor of the same kind.  Here that map is
     identified: on the points of denominator D with gcd(D,q)=1 it is

         a/D  |-->  (p * a * q^{-1} mod D) / D,

     multiplication by the unit p/q of Z/D.  Checked against the brute-force successor rule.
     Two corollaries fall out, both checked: EVERY point with gcd(D,pq)=1 is periodic (so the
     recurrent set has no transients at all, only the q- and p-divisible denominators feed into
     it), and the period-P points are EXACTLY the points of denominator dividing p^P - q^P --
     the converse of C-2, which M4 proved in one direction only.

  B  the cycle census at 3/2 to period 14, from A: exact-period counts and orbit counts.

  C  the autopsy proper: for each record union U and each period P <= 14, which orbits survive
     (all their points in U) and which cells the spine occupies, against the cells U removes.
     C-8's descriptive half predicts removed ~ spine-neighborhood; M4's `Cert.eq_of_memI_block`
     predicts at most |blocks| survivors in total.

  D  the hold set of each record, computed independently from the exact funnel (surviving
     components), and compared with the surviving orbits of C.

  E  C-8's constructive half: hand-built U_P = complement of the grid cells meeting the
     period-<=P spine (optionally with m levels of its backward tree), fed to the same certifier.
     Reports |U_P| and the verdict for a grid of (P, m, N), against the climb records.

Exact arithmetic throughout.  Runs in about two minutes.
"""
import sys
from bisect import bisect_left, bisect_right
from fractions import Fraction as Fr
from math import gcd

P_MAX = 14           # census depth, as the plan's X-U row asks
CAP = 24             # funnel depth cap for the certifier
CAP_E = 45           # deeper cap in section E, where the question is whether depth is the issue
COMP_CAP = 30000     # component-count cap: bail out rather than thrash
RANK_CAP = 1500      # above this the |reachable set| rank is too slow to be worth computing


# --------------------------------------------------------------------- the exact funnel

def carries(p, q):
    return list(range(-q + 1, p))


def norm(ivs):
    """sort and coalesce, half-open convention"""
    out = sorted((a, b) for (a, b) in ivs if a < b)
    res = []
    for (a, b) in out:
        if res and a <= res[-1][1]:
            if b > res[-1][1]:
                res[-1] = (res[-1][0], b)
        else:
            res.append((a, b))
    return res


def inter(l1, l2):
    """l1 cap l2, both sorted disjoint lists; linear sweep"""
    out, i, j = [], 0, 0
    while i < len(l1) and j < len(l2):
        lo, hi = max(l1[i][0], l2[j][0]), min(l1[i][1], l2[j][1])
        if lo < hi:
            out.append((lo, hi))
        if l1[i][1] < l2[j][1]:
            i += 1
        else:
            j += 1
    return out


def preimage(ivs, p, q):
    """{ y : some successor of y lies in ivs } = union_s (q*ivs + s)/p, clipped to [0,1)"""
    out = []
    for (c, d) in ivs:
        for s in carries(p, q):
            lo, hi = (q * c + s) / Fr(p), (q * d + s) / Fr(p)
            lo, hi = max(lo, Fr(0)), min(hi, Fr(1))
            if lo < hi:
                out.append((lo, hi))
    return norm(out)


def graph(H, p, q):
    """out-edges of the block graph: (s,j) with image_s(H_i) meeting H_j.  H is sorted and
    disjoint, so the j's meeting an interval form a contiguous range -- found by bisection."""
    los = [a for (a, b) in H]
    his = [b for (a, b) in H]
    E = []
    for (a, b) in H:
        e = []
        for s in carries(p, q):
            lo, hi = (p * a - s) / Fr(q), (p * b - s) / Fr(q)
            j0 = bisect_right(his, lo)
            j1 = bisect_left(los, hi)
            for j in range(j0, j1):
                if max(lo, los[j]) < min(hi, his[j]):
                    e.append((s, j))
        E.append(e)
    return E


def reach_rank(E):
    """rank = |forward-reachable set|, compressed to 0..r; the rank M4 shows always works"""
    R = []
    for i in range(len(E)):
        seen, st = {i}, [i]
        while st:
            u = st.pop()
            for (s, v) in E[u]:
                if v not in seen:
                    seen.add(v)
                    st.append(v)
        R.append(len(seen))
    vals = sorted(set(R))
    idx = {v: k for k, v in enumerate(vals)}
    return [idx[r] for r in R]


def func_ok(E, rk):
    for i in range(len(E)):
        if any(rk[j] > rk[i] for (s, j) in E[i]):
            return False
        if sum(1 for (s, j) in E[i] if rk[j] == rk[i]) > 1:
            return False
    return True


def alive(E):
    """blocks with an infinite forward path -- the components that can hold an orbit"""
    live = set(range(len(E)))
    changed = True
    while changed:
        changed = False
        for i in list(live):
            if not any(j in live for (s, j) in E[i]):
                live.discard(i)
                changed = True
    return live


def blocks_fixpoint(S, p, q):
    """coalesce components into consecutive-run hulls until the hull transition relation is a
    partial function -- gencert.py's default mode, the one the climb records were found under"""
    blk = list(S)
    cs = carries(p, q)
    while True:
        los = [a for (a, b) in blk]
        his = [b for (a, b) in blk]
        mark = [False] * len(blk)
        changed = False
        for (a, b) in blk:
            for s in cs:
                lo, hi = (p * a - s) / Fr(q), (p * b - s) / Fr(q)
                j0, j1 = bisect_right(his, lo), bisect_left(los, hi)
                if j1 - j0 >= 2:
                    for j in range(j0, j1 - 1):
                        mark[j] = True
                    changed = True
        if not changed:
            return blk
        new, i = [], 0
        while i < len(blk):
            j = i
            while j < len(blk) - 1 and mark[j]:
                j += 1
            new.append((blk[i][0], blk[j][1]))
            i = j + 1
        blk = new


def outdeg(H, p, q):
    los = [a for (a, b) in H]
    his = [b for (a, b) in H]
    m = 0
    for (a, b) in H:
        d = 0
        for s in carries(p, q):
            lo, hi = (p * a - s) / Fr(q), (p * b - s) / Fr(q)
            d += max(0, bisect_left(los, hi) - bisect_right(his, lo))
        m = max(m, d)
    return m


def certify(U, p=3, q=2, cap=CAP, comp_cap=COMP_CAP, want_levels=False):
    """least funnel depth admitting a certificate, in the three modes that matter:
       kh  hull-merged blocks with out-degree <= 1   (gencert.py default; the records' mode)
       ku  raw components with out-degree <= 1       (`strata = []` on components)
       kr  raw components, rank = |reachable set|    (gencert.py --ranked)
    Also returns the per-level component counts and the alive-component count."""
    lev = norm(U)
    U0 = lev
    kh = ku = kr = None
    conv = None
    comps = [len(lev)]
    blocks = None
    for K in range(cap + 1):
        if not lev:
            kh = ku = kr = K
            break
        if len(lev) > comp_cap:
            break
        E = graph(lev, p, q)
        if ku is None and func_ok(E, [0] * len(E)):
            ku = K
        if kr is None and len(E) <= RANK_CAP and func_ok(E, reach_rank(E)):
            kr = K
        if kh is None:
            H = blocks_fixpoint(lev, p, q)
            if outdeg(H, p, q) <= 1:
                kh, blocks = K, len(H)
        if kh is not None and ku is not None and (kr is not None or len(E) > RANK_CAP):
            break
        nxt = inter(U0, preimage(lev, p, q))
        if conv is None and nxt == lev:
            conv = K                      # T_{k+1} = T_k: the funnel is at a fixed point
        lev = nxt
        comps.append(len(lev))
    na = None
    if lev and len(lev) <= comp_cap:
        na = len(alive(graph(lev, p, q)))
    return {"kh": kh, "ku": ku, "kr": kr, "blocks": blocks, "comps": comps, "nalive": na,
            "conv": conv, "level": lev if want_levels else None}


# --------------------------------------------------------------- A: the recurrent map

def successors(y, p, q):
    """all v in [0,1) with q*v = p*y - s, s an integer"""
    out = []
    s = -q + 1
    while s <= p - 1:
        v = (p * y - s) / Fr(q)
        if 0 <= v < 1:
            out.append((s, v))
        s += 1
    return out


def coprime_successor(y, p, q):
    """the unique successor whose denominator is coprime to q (M4 step_unique)"""
    return [(s, v) for (s, v) in successors(y, p, q) if gcd(v.denominator, q) == 1]


def check_A(out):
    out("A. the recurrent map is multiplication by p*q^{-1} in Z/D  (M4 step_unique in closed form)")
    bases = [(3, 2), (4, 3), (5, 2), (5, 3), (7, 2), (7, 4), (9, 2), (11, 3), (10, 3), (13, 2)]
    tested = bad_map = bad_uniq = 0
    for (p, q) in bases:
        for D in range(1, 60):
            if gcd(D, q) != 1:
                continue
            c = (p * pow(q, -1, D)) % D if D > 1 else 0
            for a in range(D):
                y = Fr(a, D)
                cs = coprime_successor(y, p, q)
                tested += 1
                if len(cs) != 1:
                    bad_uniq += 1
                    continue
                if cs[0][1] != Fr((c * a) % D, D):
                    bad_map += 1
    out(f"   points tested: {tested} over {len(bases)} bases, denominators D <= 59 with gcd(D,q)=1")
    out(f"   successors that are not unique: {bad_uniq};  "
        f"disagreements with a |-> p*a*q^(-1) mod D: {bad_map}")

    # corollary 1: every point with gcd(D,p*q)=1 is periodic, period = ord(p/q) mod D
    bad_per = 0
    checked = 0
    for (p, q) in bases:
        for D in range(1, 200):
            if gcd(D, p * q) != 1:
                continue
            c = (p * pow(q, -1, D)) % D if D > 1 else 0
            for a in (1, 2, D - 1) if D > 2 else range(D):
                a %= D
                x, n = (c * a) % D, 1
                while x != a and n < 5000:
                    x, n = (c * x) % D, n + 1
                checked += 1
                if x != a:
                    bad_per += 1
    out(f"   corollary 1 (no transients in the recurrent set): {checked} points with gcd(D,pq)=1, "
        f"non-periodic: {bad_per}")

    # corollary 2 (converse of C-2): period-P points are EXACTLY those of denominator | p^P - q^P
    bad_fwd = bad_bwd = 0
    for (p, q) in [(3, 2), (4, 3), (5, 2), (7, 2)]:
        for Pp in range(1, 8):
            D = p ** Pp - q ** Pp
            c = (p * pow(q, -1, D)) % D if D > 1 else 0
            for a in range(D):                       # every a/D has period dividing P
                x = a
                for _ in range(Pp):
                    x = (c * x) % D
                if x != a:
                    bad_fwd += 1
            for E in range(1, 400):                  # and no other denominator does
                if gcd(E, p * q) != 1 or D % E == 0:
                    continue
                cE = (p * pow(q, -1, E)) % E if E > 1 else 0
                x = 1
                for _ in range(Pp):
                    x = (cE * x) % E
                if x == 1 % E and E > 1:
                    bad_bwd += 1
    out(f"   corollary 2 (converse of C-2): points of denominator dividing p^P-q^P that are not "
        f"P-periodic: {bad_fwd}; P-periodic points of another denominator: {bad_bwd}")
    out("   all three are now Lean theorems: Z32.cycOrbit_rec, Z32.cycOrbit_periodic and")
    out("   Z32.exists_periodic_orbit in Z32/CycleTransversal.lean")
    out("")
    return bad_map + bad_uniq + bad_per + bad_fwd + bad_bwd


# --------------------------------------------------------- the records and the census

def cells_to_ivs(N, cells):
    """a sorted cell-index list -> merged half-open intervals, as (lo,hi) integer pairs over N"""
    out = []
    for c in sorted(cells):
        if out and out[-1][1] == c:
            out[-1][1] = c + 1
        else:
            out.append([c, c + 1])
    return [(a, b) for a, b in out]


def ivs_from_pairs(N, pairs):
    return [(Fr(a, N), Fr(b, N)) for (a, b) in pairs]


REC240_CELLS = sorted(set(
    list(range(0, 8)) + list(range(12, 32)) + list(range(36, 48)) + list(range(52, 88))
    + list(range(100, 104)) + list(range(108, 128)) + list(range(132, 152))
    + list(range(161, 184)) + [190] + list(range(192, 208)) + list(range(216, 224))
    + list(range(228, 237)) + [238]))

RECORDS = [
    ("25/36", 36, [(0, 3), (4, 11), (16, 24), (25, 27), (30, 32), (33, 36)]),
    ("17/24", 48, [(0, 2), (3, 9), (10, 11), (12, 16), (17, 18), (20, 21), (23, 34),
                   (36, 37), (38, 40), (41, 45), (46, 47)]),
    ("43/60", 60, [(0, 2), (3, 8), (9, 12), (13, 22), (25, 26), (27, 32), (33, 38),
                   (41, 46), (48, 52), (54, 56), (57, 59)]),
    ("89/120", 240, cells_to_ivs(240, REC240_CELLS)),
]


def pullback_mask(N, pairs, D):
    """bytearray m of length D with m[a] = 1 iff a/D lies in the union of the cells"""
    m = bytearray(D)
    one = b"\x01"
    for (c, d) in pairs:
        lo = -((-c * D) // N)          # ceil(c*D/N)
        hi = -((-d * D) // N)          # ceil(d*D/N)
        lo, hi = max(lo, 0), min(hi, D)
        if lo < hi:
            m[lo:hi] = one * (hi - lo)
    return m


def check_BC(out):
    out(f"B. the cycle census at 3/2 to period {P_MAX}  (from A: period-P points = a/(3^P-2^P))")
    out("   P   3^P-2^P   points of exact period P   orbits")
    counts = {}
    for Pp in range(1, P_MAX + 1):
        counts[Pp] = 3 ** Pp - 2 ** Pp
    exact = {}
    for Pp in range(1, P_MAX + 1):
        e = counts[Pp]
        for d in range(1, Pp):
            if Pp % d == 0:
                e -= exact[d]
        exact[Pp] = e
        out(f"  {Pp:2d}  {counts[Pp]:9d}   {e:22d}   {e // Pp if Pp else 0:8d}")
    tot = sum(exact.values())
    out(f"   total points of period <= {P_MAX}: {tot}, in "
        f"{sum(e // Pp for Pp, e in exact.items())} orbits")
    out("")

    out(f"C. the autopsy: which orbits of period <= {P_MAX} survive each record union")
    masks = {}
    for (name, N, pairs) in RECORDS:
        masks[name] = {}
    surv = {name: {} for (name, N, pairs) in RECORDS}
    survpts = {name: 0 for (name, N, pairs) in RECORDS}
    for Pp in range(1, P_MAX + 1):
        D = counts[Pp]
        c = (3 * pow(2, -1, D)) % D if D > 1 else 0
        ms = [(name, pullback_mask(N, pairs, D)) for (name, N, pairs) in RECORDS]
        seen = bytearray(D)
        for a0 in range(D):
            if seen[a0]:
                continue
            orb, x = [], a0
            while not seen[x]:
                seen[x] = 1
                orb.append(x)
                x = (c * x) % D
            if len(orb) != Pp:                  # exact period < P: counted at that P
                continue
            for (name, m) in ms:
                if all(m[y] for y in orb):
                    surv[name].setdefault(Pp, []).append(orb[0])
                    survpts[name] += Pp
    for (name, N, pairs) in RECORDS:
        tot_orb = sum(len(v) for v in surv[name].values())
        det = ", ".join(f"P={Pp}: {len(v)}" for Pp, v in sorted(surv[name].items()))
        out(f"   {name:7s} (N={N:3d}): surviving orbits of period <= {P_MAX}: {tot_orb}"
            + (f"  [{det}]" if det else ""))
        if tot_orb:
            for Pp, v in sorted(surv[name].items()):
                D = counts[Pp]
                for a0 in v[:4]:
                    orb, x = [], a0
                    for _ in range(Pp):
                        orb.append(Fr(x, D))
                        x = (3 * pow(2, -1, D) * x) % D if D > 1 else 0
                    out(f"       period {Pp}: " + " -> ".join(str(z) for z in orb))
    out(f"   total surviving periodic POINTS: "
        + ", ".join(f"{name} {survpts[name]}" for (name, N, pairs) in RECORDS))
    out("")
    return counts, exact, surv, survpts


def check_spine(out, counts):
    out("   spine coverage: cells of each record's grid that the period-<=P spine occupies,")
    out("   against the cells the record removes")
    out("   record   P   spine pts  cells hit  removed cells  hit&removed  removed with no spine pt")
    res = {}
    marks = [1, 2, 3, 4, 5, 6, 8, 10, 12, 14]
    for (name, N, pairs) in RECORDS:
        inU = set()
        for (a, b) in pairs:
            inU |= set(range(a, b))
        removed = set(range(N)) - inU
        hit = set()
        npts = 0
        for ell in range(1, max(marks) + 1):
            D = counts[ell]
            npts += D
            if len(hit) < N:
                for a in range(D):
                    hit.add(a * N // D)
            if ell in marks:
                res[(name, ell)] = (len(hit), len(hit & removed))
                out(f"   {name:7s} {ell:3d}  {npts:9d}  {len(hit):9d}  {len(removed):13d}  "
                    f"{len(hit & removed):11d}  {len(removed - hit):22d}")
        out("")
    return res


# ------------------------------------------------------------------ D: the hold set

def hold_structure(U, p=3, q=2, depth=40):
    """run the exact funnel to `depth`, then read the alive sub-graph: it is a function, so it
    splits into cycles (the surviving spine) and the components that feed into them (the tree)"""
    lev = norm(U)
    U0 = lev
    for _ in range(depth):
        lev = inter(U0, preimage(lev, p, q))
        if not lev:
            return {"alive": 0, "cycles": [], "tree": 0, "comps": 0, "meas": Fr(0)}
    E = graph(lev, p, q)
    al = alive(E)
    sub = {i: [j for (s, j) in E[i] if j in al] for i in al}
    if any(len(v) != 1 for v in sub.values()):
        return {"alive": len(al), "cycles": None, "tree": None, "comps": len(lev),
                "meas": sum(lev[i][1] - lev[i][0] for i in al)}
    f = {i: v[0] for i, v in sub.items()}
    seen, cycles = set(), []
    for i in al:
        if i in seen:
            continue
        path, x = [], i
        while x not in seen:
            seen.add(x)
            path.append(x)
            x = f[x]
        if x in path:
            cycles.append([lev[j] for j in path[path.index(x):]])
    return {"alive": len(al), "cycles": cycles, "comps": len(lev),
            "tree": len(al) - sum(len(c) for c in cycles),
            "meas": sum(lev[i][1] - lev[i][0] for i in al)}


def name_point(iv):
    """the rational of smallest denominator in a shrunken funnel component -- once the component
    is narrower than the gap between two candidates this names the hold point exactly"""
    def simplest(x, y):
        n = x.numerator // x.denominator
        if n == x:
            return Fr(n)
        if y.numerator // y.denominator > n:
            return Fr(n + 1)
        return n + 1 / simplest(1 / (y - n), 1 / (x - n))
    return simplest(Fr(iv[0]), Fr(iv[1]))


def check_D(out, surv, counts):
    out("D. the hold set of each record, read off the exact funnel (engine-independent)")
    out("   record     |U|      cert depth  blocks  components  hold points  spine cycles + tree")
    for (name, N, pairs) in RECORDS:
        U = ivs_from_pairs(N, pairs)
        r = certify(U, 3, 2, cap=34)
        h = hold_structure(U, 3, 2, depth=40 if N < 240 else 34)
        meas = sum(b - a for (a, b) in U)
        cyc = ("cycles " + "+".join(str(len(c)) for c in h["cycles"])
               + f", tree {h['tree']}") if h["cycles"] is not None else "not functional"
        out(f"   {name:8s} {str(meas):8s}  {str(r['kh']):10s}  {str(r['blocks']):6s}  "
            f"{r['comps'][-1]:10d}  {h['alive']:11d}  {cyc}")
        if h["cycles"]:
            for c in h["cycles"]:
                pts = [name_point(iv) for iv in c]
                inside = all(0 <= z < 1 for z in pts)
                out(f"       surviving cycle, length {len(c)}: "
                    + " -> ".join(str(z) for z in pts)
                    + ("" if inside else "   (limit outside [0,1): the funnel components shrink "
                                         "to the right endpoint, so this cycle holds no point)"))
        norb = sum(len(v) for v in surv[name].values())
        out(f"       census cross-check: surviving orbits of period <= {P_MAX} = {norb}")
    out("")


# ------------------------------------------------------------- E: C-8 as written

def spine_points(Pmax, counts):
    S = set()
    for ell in range(1, Pmax + 1):
        D = counts[ell]
        for a in range(D):
            S.add(Fr(a, D))
    return S


def backward(S, levels, p=3, q=2):
    cur, out = set(S), set(S)
    for _ in range(levels):
        nxt = set()
        for y in cur:
            for s in carries(p, q):
                u = (q * y + s) / Fr(p)
                if 0 <= u < 1 and u not in out:
                    nxt.add(u)
        out |= nxt
        cur = nxt
    return out


def check_E(out, counts):
    out("E. C-8 as written: U_P = complement of the grid cells meeting the period-<=P spine")
    out("   (plus m levels of its backward tree).  `converged d` means the exact funnel reaches a")
    out("   FIXED POINT T_{d+1} = T_d: every point of T_d then has a successor in T_d, so T_d is")
    out("   contained in the hold set, the hold set is infinite, and by Z32.BlockCert.Cert.")
    out("   ok_eq_false_of_infinite_hold NO certificate exists at ANY depth -- the refusal is")
    out("   structural, not a depth artifact (lesson L15).")
    out("    P   m     N   cells cut    |U_P|      verdict                        components")
    for Pp in (2, 3, 4, 5):
        S = spine_points(Pp, counts)
        for m in (0, 1, 2):
            T = backward(S, m) if m else S
            for N in (36, 60, 240, 720):
                hit = {int(y * N) for y in T}
                keep = sorted(set(range(N)) - hit)
                meas = Fr(len(keep), N)
                if not keep:
                    out(f"   {Pp:2d}  {m:2d}  {N:4d}  {len(hit):9d}  {'0':9s}  "
                        f"{'nothing left':30s}")
                    continue
                U = ivs_from_pairs(N, cells_to_ivs(N, keep))
                r = certify(U, 3, 2, cap=CAP_E)
                if r["kh"] is not None:
                    verd = f"CERTIFIES, hull depth {r['kh']}"
                elif r["conv"] is not None:
                    verd = f"NEVER (funnel converged d={r['conv']})"
                else:
                    verd = f"no certificate to depth {CAP_E}"
                out(f"   {Pp:2d}  {m:2d}  {N:4d}  {len(hit):9d}  {str(meas):9s}  {verd:30s}  "
                    f"{r['comps'][-1]:10d}")
        out("")
    out("   the best measure C-8's recipe ever certifies is 1/4, at grids where the greedy climb")
    out("   of x3climb.py reaches 43/60 and 3/4; every larger U_P it produces is refused, and")
    out("   refused for good (the funnel converges).")
    out("")


# ---------------------------------------------------- F: the refinement ladder (the rate)

LADDER = [
    (12, "7/12", 7), (16, "5/8", 10), (18, "2/3", 12), (20, "3/5", 12), (36, "25/36", 25),
    (48, "17/24", 34), (60, "43/60", 43), (240, "89/120", 178), (480, "179/240", 358),
    (720, "3/4", 540), (1440, "181/240", 1086),
]

NEW_RECORDS = {
    480: [(0, 16), (24, 64), (72, 96), (97, 98), (104, 176), (200, 208), (216, 256),
          (264, 304), (322, 368), (380, 382), (384, 416), (432, 448), (452, 453),
          (456, 474), (476, 478)],
    720: [(0, 24), (36, 96), (108, 144), (145, 148), (156, 264), (300, 312), (324, 384),
          (396, 456), (483, 552), (570, 573), (576, 624), (648, 672), (678, 680),
          (684, 711), (714, 717), (718, 719)],
    1440: [(0, 48), (72, 192), (216, 288), (290, 296), (297, 298), (312, 528), (600, 624),
           (648, 768), (792, 912), (966, 1104), (1123, 1124), (1140, 1146), (1152, 1248),
           (1296, 1344), (1350, 1351), (1355, 1360), (1368, 1422), (1423, 1424),
           (1428, 1434), (1436, 1439)],
}


def check_F(out):
    out("F. the largeness curve refined: three new climb records, and what they cost")
    out("   the plan's table stopped at 240 cells; x3climb.py was restarted from the refined")
    out("   240-record at 480, 720 and 1440 cells (search by atlas.c, verdict re-checked here)")
    out("      N      |U|        gain over the previous record   cert depth  blocks  hold points")
    prev = Fr(178, 240)
    for N in (240, 480, 720, 1440):
        pairs = NEW_RECORDS.get(N) or cells_to_ivs(240, REC240_CELLS)
        U = ivs_from_pairs(N, pairs)
        meas = sum(b - a for (a, b) in U)
        r = certify(U, 3, 2, cap=34)
        h = hold_structure(U, 3, 2, depth=34)
        gain = meas - prev
        out(f"   {N:6d}  {str(meas):9s}  {float(meas):.6f}   {'+' + str(gain) if N > 240 else '-':12s}"
            f"  {str(r['kh']):10s}  {str(r['blocks']):6s}  {h['alive']:6d}")
        prev = meas
    out("   each of the three passes bought exactly 1/240 = 0.4167% of measure -- a fact about")
    out("   this greedy search, not about the achievable supremum (which [KK18] Thm 5.9 puts at 1,")
    out("   non-constructively).  At that observed rate |U| = 0.99 is 60 further passes away.")
    out("")


# ---------------------------------------------- G: the two inequalities and the depth price

def sweep_inequalities(out, trials=400):
    """|f^{-1}(S)| >= |S| and  sum_s |g_s(S) cap [0,1)| = 2|S|, on random interval unions"""
    import random
    rng = random.Random(20260903)
    bad_sum = bad_ge = 0
    for _ in range(trials):
        N = rng.choice([12, 24, 36, 60, 120])
        cells = sorted(rng.sample(range(N), rng.randint(1, N)))
        S = ivs_from_pairs(N, cells_to_ivs(N, cells))
        mS = sum(b - a for (a, b) in S)
        tot = Fr(0)
        for (c, d) in S:
            for s in carries(3, 2):
                lo, hi = max((2 * c + s) / Fr(3), Fr(0)), min((2 * d + s) / Fr(3), Fr(1))
                if lo < hi:
                    tot += hi - lo
        if tot != 2 * mS:
            bad_sum += 1
        pre = preimage(S, 3, 2)
        if sum(b - a for (a, b) in pre) < mS:
            bad_ge += 1
    return bad_sum, bad_ge, trials


def check_G(out):
    out("G. the price of largeness: two exact facts and the lower bound they force")
    out("   (i)  sum over the carries s of |g_s(S) cap [0,1)| = 2|S| exactly, where g_s(v)=(2v+s)/3")
    out("   (ii) every y in [0,1) has exactly two successors, so the multiplicity is at most 2,")
    out("        hence |f^{-1}(S)| >= |S| -- the backward relation never loses measure")
    bad_sum, bad_ge, n = sweep_inequalities(out)
    out(f"   checked on {n} random interval unions: violations of (i): {bad_sum}, of (ii): {bad_ge}")
    out("   consequence: |T_{k+1}| = |U cap f^{-1}(T_k)| >= |T_k| - d  with d = 1 - |U|, so")
    out("   |T_k| >= 1 - (k+1)d; and past the certifying depth K the block map is a function, so")
    out("   |T_{K+j}| <= (2/3)^j * B with B the block count.  Together, for every j >= 0")
    out("        (K + j + 1) * d  >=  1 - (2/3)^j * B,")
    out("   i.e. K + log_{3/2}(B) >~ 1/d.  A certificate for a union of measure 1 - d therefore")
    out("   has depth-plus-log-blocks at least about 1/d, no matter how it is found.")
    out("      entry               |U|        d        1/d     K     B    K+log_1.5(B)   slack")
    from math import log
    rows = [("union712    ", 12, [(0, 2), (3, 4), (5, 8), (9, 10)]),
            ("union23     ", 18, [(0, 2), (3, 8), (9, 10), (11, 14), (15, 16)]),
            ("union2536   ", 36, RECORDS[0][2]),
            ("record 17/24", 48, RECORDS[1][2]),
            ("record 43/60", 60, RECORDS[2][2]),
            ("record 240  ", 240, RECORDS[3][2]),
            ("record 480  ", 480, NEW_RECORDS[480]),
            ("record 720  ", 720, NEW_RECORDS[720]),
            ("record 1440 ", 1440, NEW_RECORDS[1440])]
    for (nm, N, pairs) in rows:
        U = ivs_from_pairs(N, pairs)
        m = sum(b - a for (a, b) in U)
        d = 1 - m
        r = certify(U, 3, 2, cap=34)
        K, B = r["kh"], r["blocks"]
        lhs = K + log(B) / log(1.5)
        out(f"      {nm}  {str(m):9s}  {str(d):7s}  {float(1 / d):6.2f}  {K:3d}  {B:5d}   "
            f"{lhs:9.1f}     {lhs - float(1 / d):8.1f}")
    out("   the bound is far from tight at the measures reached today; it bites on C-8's target.")
    out("   C-8 asks for |U_P| >= 1 - C(2/3)^{cP}, i.e. d_P <= C(2/3)^{cP}, which forces")
    out("        K_P + log_{3/2}(B_P) >~ (1/C) (3/2)^{cP},")
    out("   exponential in P: the funnel denominator is G*3^K, so the certificate data for U_P is")
    out("   doubly exponential in P.  T6's `parametric certificate of bounded shape' is therefore")
    out("   not available; the derivation is elementary but is NOT machine-checked (its two inputs")
    out("   (i) and (ii) are, numerically, above).")
    out("")


def main():
    lines = []

    def out(s=""):
        lines.append(s)
        print(s)
        sys.stdout.flush()

    out("plan-z32-transform X-U (decides C-8 / target T6): union-pattern autopsy of the")
    out("largeness records at base 3/2 -- exact arithmetic, engines only as a search oracle")
    out("")
    bad = check_A(out)
    counts, exact, surv, survpts = check_BC(out)
    check_spine(out, counts)
    check_D(out, surv, counts)
    check_E(out, counts)
    check_F(out)
    check_G(out)
    out("VERDICT: " + ("all structural checks pass" if bad == 0 else f"{bad} FAILURES"))
    with open("data/transform/union_autopsy.txt", "w") as f:
        f.write("\n".join(lines) + "\n")
    return 0 if bad == 0 else 1


if __name__ == "__main__":
    sys.exit(main())
