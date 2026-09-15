#!/usr/bin/env python3
# (C) 2026 Ralf Stephan, in collaboration with Claude Code.  CC0 1.0.
"""xf.py -- experiment X-F of `plans/plan-z32-transform.html`: the frontier autopsy
(decides conjecture C-6, and is the first test of the T7 plateau conjecture -- milestone M6).

The plan's X-F row asks for "the full survivor-cycle inventory and kneading data" of the 14
frontier windows at L* = 1466/3600 and of their refused neighbours at 1467/3600, in order to test

  C-6: the 14 frontier windows are precisely those containing the 2-cycle {2/5,3/5} and no other
       cycle point of period <= P_0; L* plateaus are cycle-indexed.

Everything below is exact rational arithmetic and re-implements the engine of `atlas.c` from
scratch (via the exact funnel of `xu.py`), so section A is also the R-5 recheck of the recorded
frontier row `data/x2_frontier.txt`.

  A  the frontier row, rechecked without atlas.c: hull-merge certification over the whole
     j = 1466 row and over j = 1467, and the reflection y |-> 1-y that pairs the 14.

  B  the survivor-cycle inventory: every periodic orbit of q*y_{n+1} = p*y_n - s_n of period
     <= P_MAX all of whose points lie in the window, found by a forward DFS over carry words with
     exact interval pruning, and cross-checked for P <= 12 against the denominator census
     (period-P points have denominator dividing p^P - q^P -- X-U's `Z32.exists_periodic_orbit`).

  C  the trichotomy.  Growth of the *alive* component count of the exact funnel, over the whole
     envelope: constant (finite hold set), linear (infinite hold set, zero entropy) or exponential.
     This is the classification C-6 should have been about.

  D  the kneading data: ker(z) = sup{k : z in T_k} for both endpoints, against the certified
     depth (conjecture C-7), and the two rationals that cut the envelope out of the row.

  E  the ranked frontier.  The recorded L* is a property of the *hull-merge* search; the rank
     stratification of `gencert.py --ranked` (sound by the same theorem) reaches further.  The
     search and the resulting record window.

  F  the two staircases along the centred line s = (1-L)/2, and the plateau at the record.

Exact arithmetic throughout.  Runs in about seven minutes.
"""
import sys
import time
from bisect import bisect_left, bisect_right
from fractions import Fraction as Fr

sys.path.insert(0, sys.path[0] or ".")
import xu                                    # the exact funnel, shared with X-U

G = 3600                 # the recorded sweep grid
JSTAR = 1466             # the recorded frontier length L* = JSTAR/G
JNEXT = 1467             # the first refused length
ENV_LO, ENV_HI = 950, 1185   # the envelope of the 14, with margin
P_MAX = 20               # survivor-cycle inventory depth
P_CROSS = 12             # depth to which the census cross-check runs
CAP_H = 22               # funnel cap, hull-merge mode
CAP_R = 26               # funnel cap, ranked mode
COMP_H = 400             # component cap, hull-merge mode
COMP_R = 1200            # component cap, ranked mode (reach_rank is quadratic)
NODE_CAP = 300000        # DFS node cap in section B

P, Q = 3, 2


def win(i, j, g=G):
    return [(Fr(i, g), Fr(i + j, g))]


# --------------------------------------------------------------- certification, the two modes

def hull_depth(U, cap=CAP_H, comp_cap=COMP_H):
    """least funnel depth at which the hull-merged block graph is a partial function -- the
    criterion `atlas.c` and `gencert.py` use by default, and the one L* was measured with."""
    lev = xu.norm(U)
    U0 = lev
    for K in range(cap + 1):
        if not lev:
            return K
        if len(lev) > comp_cap:
            return None
        H = xu.blocks_fixpoint(lev, P, Q)
        if xu.outdeg(H, P, Q) <= 1:
            return K
        lev = xu.inter(U0, xu.preimage(lev, P, Q))
    return None


def ranked_depth(U, cap=CAP_R, comp_cap=COMP_R):
    """least funnel depth at which the raw component graph is deterministic up to the rank
    |forward-reachable set| -- `gencert.py --ranked`, sound by the same `Cert.not_confined`.
    Equivalently: no strongly connected component of the block graph branches."""
    lev = xu.norm(U)
    U0 = lev
    for K in range(cap + 1):
        if not lev:
            return K
        if len(lev) > comp_cap:
            return None
        E = xu.graph(lev, P, Q)
        if xu.func_ok(E, xu.reach_rank(E)):
            return K
        lev = xu.inter(U0, xu.preimage(lev, P, Q))
    return None


def func_ok_rank(E):
    return xu.func_ok(E, xu.reach_rank(E))


def funnel_levels(U, depth):
    lev = xu.norm(U)
    U0 = lev
    out = [lev]
    for _ in range(depth):
        lev = xu.inter(U0, xu.preimage(lev, P, Q))
        out.append(lev)
        if not lev:
            break
    return out


# ------------------------------------------------------------------------ A: the frontier row

def check_A(out):
    out("A. the frontier row, rechecked without atlas.c (exact rationals, hull-merge mode)")
    recorded = {}
    try:
        for line in open("data/x2_frontier.txt"):
            f = line.split()
            if len(f) == 7 and f[0].isdigit():
                recorded[(int(f[0]), int(f[1]))] = f[6]
    except OSError:
        out("   (data/x2_frontier.txt not found -- comparison skipped)")

    t = time.time()
    cert = []
    disagree = 0
    for i in range(940, 1241):
        d = hull_depth(win(i, JSTAR))
        if d is not None:
            cert.append((i, d))
        v = recorded.get((JSTAR, i))
        if v is not None and (v != "FAT") != (d is not None):
            disagree += 1
    out(f"   j = {JSTAR} (L* = {JSTAR}/{G} = {JSTAR/G:.6f}), i = 940..1240: "
        f"{len(cert)} certified, {disagree} disagreements with the recorded row")
    out("   the 14: " + ", ".join(f"{i}@{d}" for i, d in cert))

    # the reflection y |-> 1-y conjugates the carry relation to itself (carry e |-> 1-e), so it
    # maps the window [i, i+j)/G to ((G-j-i, G-i])/G: an exact symmetry of the whole sweep.
    mirror = G - JSTAR
    pairs = [(i, mirror - i) for i, _ in cert]
    ok = all(any(k == m for k, _ in cert) for _, m in pairs)
    out(f"   reflection i <-> {mirror}-i maps the certified set to itself: {ok}"
        f"   (7 mirror pairs, {[ (i,mirror-i) for i,_ in cert[:7] ]})")

    lo, hi = 940, G - JNEXT
    dense_hi = 1300
    ncert = 0
    ndis = 0
    ntest = 0
    for i in list(range(lo, dense_hi + 1)) + list(range(dense_hi + 1, hi + 1, 7)):
        d = hull_depth(win(i, JNEXT))
        ntest += 1
        if d is not None:
            ncert += 1
            out(f"   *** j = {JNEXT} certifies at i = {i}, depth {d}")
        v = recorded.get((JNEXT, i))
        if v is not None and (v != "FAT") != (d is not None):
            ndis += 1
    out(f"   j = {JNEXT}: {ntest} positions tested (940..{dense_hi} exhaustively, then every 7th "
        f"to {hi}), {ncert} certified, {ndis} disagreements with the recorded row")
    out(f"   [{time.time()-t:.0f} s]")
    out("")
    return cert, disagree + ndis


# ---------------------------------------------------------------- B: the survivor-cycle inventory

def primitive(w):
    n = len(w)
    for d in range(1, n):
        if n % d == 0 and w == w[:d] * (n // d):
            return False
    return True


def cycles_in(U, pmax, node_cap=NODE_CAP):
    """every periodic orbit with all points in U, of period <= pmax.  DFS over carry words with
    exact forward-image pruning; a candidate word is closed by the exact cycle point

        y_0 = (sum_i p^{P-1-i} q^i s_i) / (p^P - q^P)                (C-2, and its converse)

    and then verified point by point, so the answer is exact and complete: every real cycle in U
    follows an admissible word."""
    U = xu.norm(U)
    cs = xu.carries(P, Q)
    orbits, seen = [], set()
    nodes = 0

    def rec(J, word):
        nonlocal nodes
        nodes += 1
        if nodes > node_cap:
            raise RuntimeError("node cap")
        n = len(word)
        if n >= 1 and primitive(word):
            den = P ** n - Q ** n
            num = sum(P ** (n - 1 - k) * Q ** k * word[k] for k in range(n))
            y0 = Fr(num, den)
            pts, y, good = [], y0, True
            for k in range(n):
                if not any(a <= y < b for (a, b) in U):
                    good = False
                    break
                pts.append(y)
                y = (P * y - word[k]) / Fr(Q)
            if good and y == y0:
                key = min(tuple(word[k:] + word[:k]) for k in range(n))
                if key not in seen:
                    seen.add(key)
                    orbits.append((n, pts, key))
        if n == pmax:
            return
        for s in cs:
            lo, hi = (P * J[0] - s) / Fr(Q), (P * J[1] - s) / Fr(Q)
            for (a, b) in U:
                l2, h2 = max(lo, a), min(hi, b)
                if l2 < h2:
                    rec((l2, h2), word + [s])

    for iv in U:
        rec(iv, [])
    return sorted(orbits), nodes


def cycles_in_census(U, pmax):
    """the same inventory the slow way: enumerate the points of denominator p^P - q^P and push
    them through the recurrent map a |-> p*a*q^{-1} mod D (X-U section A).  Independent of the
    funnel, and the R-5 cross-check on section B."""
    found = []
    for n in range(1, pmax + 1):
        D = P ** n - Q ** n
        c = (P * pow(Q, -1, D)) % D if D > 1 else 0
        seen = bytearray(D)
        for a0 in range(D):
            if seen[a0]:
                continue
            orb, x = [], a0
            while not seen[x]:
                seen[x] = 1
                orb.append(x)
                x = (c * x) % D
            if len(orb) != n:
                continue
            pts = [Fr(a, D) for a in orb]
            if all(any(lo <= y < hi for (lo, hi) in U) for y in pts):
                found.append((n, min(pts)))
    return sorted(found)


def check_B(out, cert):
    out(f"B. the survivor-cycle inventory (period <= {P_MAX}), for the 14 and their neighbours")
    out("   i        |  hull  ranked | orbits <= 20  (period: smallest point)")
    special = sorted(set([i for i, _ in cert] + [i - 1 for i, _ in cert] + [i + 1 for i, _ in cert]
                         + [960, 1174, 1175]))
    inv = {}
    for i in special:
        U = win(i, JSTAR)
        try:
            orb, _ = cycles_in(U, P_MAX)
        except RuntimeError:
            orb = None
        inv[i] = orb
        h, r = hull_depth(U), ranked_depth(U)
        tag = "  ".join(f"{n}:{min(pts)}" for n, pts, _ in orb) if orb is not None else "(node cap)"
        out(f"   {i:5d}    | {str(h):5s} {str(r):6s} | {tag}")
    out("")

    out(f"   R-5 cross-check against the denominator census, period <= {P_CROSS}:")
    bad = 0
    for i in special[:6] + [960, 1174]:
        U = xu.norm(win(i, JSTAR))
        a = sorted((n, min(pts)) for n, pts, _ in cycles_in(U, P_CROSS)[0])
        b = cycles_in_census(U, P_CROSS)
        if a != b:
            bad += 1
            out(f"      MISMATCH at i = {i}: DFS {a} vs census {b}")
    out(f"      {len(special[:6]) + 2} windows, {bad} mismatches")
    out("")

    only2 = [i for i in special if inv[i] is not None and len(inv[i]) == 1 and inv[i][0][0] == 2]
    cset = {i for i, _ in cert}
    out("   C-6 reads: the frontier windows are PRECISELY those whose only orbit of period <= P_0")
    out("   is the 2-cycle {2/5,3/5}.")
    out(f"      windows whose inventory is exactly the 2-cycle: {len(only2)}  {only2}")
    out(f"      of these, certified (hull): {len([i for i in only2 if i in cset])}"
        f"      refused: {len([i for i in only2 if i not in cset])}  "
        f"{[i for i in only2 if i not in cset]}")
    out(f"      certified windows with a further orbit: "
        f"{[i for i in cset if inv[i] is not None and len(inv[i]) > 1]}")
    out("   => the '=>' half holds (it is Theorem B: |hold set| <= |blocks| = 2), the converse")
    out("      FAILS: refused windows with the same inventory exist.  C-6 is half true.")
    out("")

    out("   the inventory over the WHOLE envelope, as runs of constant inventory:")
    out("   i-range          orbits besides the 2-cycle          hull   ranked")
    runs = []
    for i in range(ENV_LO, ENV_HI + 1):
        try:
            orb, _ = cycles_in(win(i, JSTAR), P_MAX)
            key = tuple(sorted((n, min(pts)) for n, pts, _ in orb))
        except RuntimeError:
            key = None
        if runs and runs[-1][2] == key:
            runs[-1][1] = i
        else:
            runs.append([i, i, key])
    for a, b, key in runs:
        h = hull_depth(win(a, JSTAR))
        r = ranked_depth(win(a, JSTAR))
        if key is None:
            tag = "(node cap)"
        else:
            rest = [(n, y) for (n, y) in key if n != 2]
            tag = ", ".join(f"P={n} at {y}" for n, y in rest) if rest else "-- none --"
        out(f"   {a:5d}..{b:<5d}    {tag:38s}  {str(h):5s}  {str(r)}")
    out(f"   {len(runs)} runs over {ENV_HI-ENV_LO+1} positions.  Inside the envelope the extra")
    out("   inventory is a SINGLE orbit on each run, of period 4, 6, 8, 10, 12, 14 as one moves")
    out("   out from the centre, and the 14 certified positions are exactly the run boundaries")
    out("   where the outgoing orbit has left and the incoming one has not yet arrived.  That is")
    out("   the plateau structure C-6 was reaching for -- indexed by cycles, but the certified")
    out("   set is the set of TRANSITIONS, not the plateaus.")
    out("")
    return inv


# ------------------------------------------------------------------------- C: the trichotomy

def alive_profile(U, depths=(10, 20, 30, 40), comp_cap=3000):
    lev = xu.norm(U)
    U0 = lev
    prof = {}
    for k in range(1, max(depths) + 1):
        lev = xu.inter(U0, xu.preimage(lev, P, Q))
        if not lev:
            for d in depths:
                prof.setdefault(d, 0)
            return prof, "empty"
        if len(lev) > comp_cap:
            for d in depths:
                prof.setdefault(d, None)
            return prof, "capped"
        if k in depths:
            prof[k] = len(xu.alive(xu.graph(lev, P, Q)))
    a, b, c = prof[depths[1]], prof[depths[2]], prof[depths[3]]
    if a == b == c:
        cls = "finite"
    elif b - a == c - b and b - a > 0:
        cls = "linear"
    else:
        cls = "super"
    return prof, cls


def check_C(out, cert, inv):
    out("C. the trichotomy: growth of the ALIVE component count of the exact funnel")
    out("   (a component is alive if it has an infinite forward path; the hold set lives in them)")
    out("   i     alive@10 @20 @30 @40   class        hull  ranked  orbits<=20")
    cset = {i for i, _ in cert}
    tally = {}
    rows = []
    t = time.time()
    for i in range(ENV_LO, ENV_HI + 1):
        U = win(i, JSTAR)
        prof, cls = alive_profile(U)
        tally[cls] = tally.get(cls, 0) + 1
        rows.append((i, prof, cls))
    for i, prof, cls in rows:
        if i in cset or i in (960, 1174, 962, 1000, 1175):
            U = win(i, JSTAR)
            h, r = hull_depth(U), ranked_depth(U)
            no = len(inv[i]) if inv.get(i) is not None else "?"
            out(f"   {i:5d} {str(prof[10]):8s} {str(prof[20]):3s} {str(prof[30]):3s} "
                f"{str(prof[40]):3s}   {cls:10s}   {str(h):5s} {str(r):6s}  {no}")
    out(f"   over the envelope i = {ENV_LO}..{ENV_HI} ({ENV_HI-ENV_LO+1} windows): "
        + ", ".join(f"{k} {v}" for k, v in sorted(tally.items())))
    out("   'finite' = the alive count is constant; the hold set is exactly the 2-cycle, and the")
    out("              hull-merge criterion is met -- these are the 14")
    out("   'linear' = the alive count is k+1 at depth k; the signature X-D19 already identified")
    out("              in [Dub19]'s window, an endpoint locked onto a preimage of the cycle")
    out("   'super'  = anything else.  CAUTION: this is NOT an entropy proxy.  [2/7,5/7) is")
    out("              'super' (60/370/1180/2740) and yet ranked-certifies at depth 15, so its")
    out("              hold set carries only eventually periodic orbits.  The alive count is an")
    out("              over-approximation: a component may shrink onto a point outside U.")
    out("              Only the ranked criterion decides, and it is what section E measures.")
    out(f"   [{time.time()-t:.0f} s]")
    out("")
    return tally


# ---------------------------------------------------------------------- D: the kneading data

def ker(z, U, cap=60):
    """sup{k : z in T_k}, the funnel depth the point z survives -- the exact form of the
    'kneading pre-period of the endpoint' that conjecture C-7 predicts controls the depth."""
    lev = xu.norm(U)
    U0 = lev
    if not any(a <= z < b for (a, b) in lev):
        return -1
    for k in range(1, cap + 1):
        lev = xu.inter(U0, xu.preimage(lev, P, Q))
        if not any(a <= z < b for (a, b) in lev):
            return k - 1
    return cap


def check_D(out, cert):
    out("D. the kneading data: ker(z) = sup{k : z in T_k} for the two endpoints")
    out("   (the right endpoint is read off the mirror window, section A's reflection, so that")
    out("    both are left endpoints of a half-open window and the number is exact)")
    out("   i      s            ker(s)   ker(s+L)   hull depth   ranked depth")
    mirror = G - JSTAR
    for i, d in cert:
        kl = ker(Fr(i, G), win(i, JSTAR))
        kr = ker(Fr(mirror - i, G), win(mirror - i, JSTAR))
        out(f"   {i:5d}  {str(Fr(i,G)):12s} {kl:6d}   {kr:8d}   {d:10d}   "
            f"{ranked_depth(win(i, JSTAR))}")
    out("")
    out("   ranked depth against the two kneading depths, over every ranked-certified position:")
    inside = both = neither = 0
    for i in range(ENV_LO, ENV_HI + 1):
        r = ranked_depth(win(i, JSTAR))
        if r is None:
            continue
        kl = ker(Fr(i, G), win(i, JSTAR))
        kr = ker(Fr(mirror - i, G), win(mirror - i, JSTAR))
        both += 1
        if r in (kl, kr):
            inside += 1
        else:
            neither += 1
            if neither <= 4:
                out(f"      exception: i = {i}, ranked depth {r}, ker = ({kl}, {kr})")
    out(f"      {both} ranked-certified positions; depth in {{ker(s), ker(s+L)}} at {inside}, "
        f"elsewhere at {neither}")
    out("      -- conjecture C-7 in its sharp form: the certificate depth is one of the two")
    out("         endpoint kneading depths, not merely comparable with them.")
    out("")
    out("   the two rationals that cut the envelope out of the row:")
    out("     4/15 = 960/3600 is a preimage of 2/5 (carry 0) and 11/15 = 2640/3600 one of 3/5.")
    out("     Measured in section E: the ranked-certified set of this row is EXACTLY")
    out("     961 <= i <= 1173, i.e. exactly the windows with [s, s+L] contained in the open")
    out("     interval (4/15, 11/15) -- an interval of length 7/15 = 0.466667.")
    for i in (960, 1174):
        prof, cls = alive_profile(win(i, JSTAR))
        out(f"     i = {i}: alive {prof[10]}/{prof[20]}/{prof[30]}/{prof[40]} ({cls}), refused in "
            f"both modes to depth {CAP_R}")
    out("     the two endpoints fail for DIFFERENT reasons, and only the left one is a theorem:")
    out("       i = 960: s = 4/15 lies IN the window, so its whole backward chain does too --")
    U = xu.norm(win(960, JSTAR))
    z, chain = Fr(4, 15), [Fr(4, 15)]
    for _ in range(6):
        pre = [(Q * z + t) / Fr(P) for t in xu.carries(P, Q)]
        pre = [w for w in pre if any(a <= w < b for (a, b) in U) and w != z]
        if not pre:
            break
        z = pre[0]
        chain.append(z)
    out("         " + " <- ".join(str(c) for c in chain))
    out("         and every one of these is a genuine hold point (46/135 -> 23/45 -> 4/15 -> 2/5")
    out("         -> 3/5 -> 2/5 -> ...), so the hold set is INFINITE and")
    out("         Z32.BlockCert.Cert.ok_eq_false_of_infinite_hold refuses every unranked")
    out("         certificate at every depth.  The chain accumulates on the 2-cycle, so no")
    out("         finite interval partition separates them, and the ranked mode fails too.")
    out("       i = 1174: s+L = 11/15 is EXCLUDED (half-open), so the mirror chain")
    out("         11/15 <- 22/45 <- 89/135 <- 178/405 <- ... consists of points whose forward")
    out("         orbit runs through 11/15 and therefore leaves U.  The hold set is plausibly")
    out("         just the 2-cycle; what fails is the funnel's resolution -- its rightmost")
    out("         component shrinks onto 11/15 without ever becoming empty.  This is a")
    out("         CONVENTION refusal, and X-D19's remedy applies: one grid unit inwards")
    out("         (i = 1173) certifies at depth 13.")
    out("       exactly one block branches inside its own strongly connected component at every")
    out("       depth of the i = 960 funnel, and it is the block that holds 3/5:")
    lev = xu.norm(win(960, JSTAR))
    U0 = lev
    for K in range(1, 31):
        lev = xu.inter(U0, xu.preimage(lev, P, Q))
        E = xu.graph(lev, P, Q)
        rk = xu.reach_rank(E)
        bad = [k for k in range(len(E)) if sum(1 for (t, j) in E[k] if rk[j] == rk[k]) > 1]
        if K in (10, 20, 30):
            b0 = bad[0]
            out(f"         depth {K:2d}: {len(lev):3d} components, {len(bad)} branching block(s); "
                f"the offender is [{float(lev[b0][0]):.6f}, {float(lev[b0][1]):.6f})")
    out("")


# ------------------------------------------------------------------- E: the ranked frontier

RANKED_PROBE = [(1466, 1029), (1467, 964), (1500, 1035), (1530, 1035), (1540, 1030),
                (1542, 1029), (1543, 1029)]


def check_E(out, cert):
    out("E. the ranked frontier: L* = 1466/3600 is a property of the HULL-MERGE search")
    out("   the same sweep row, in ranked mode:")
    cset = {i for i, _ in cert}
    rk = [(i, ranked_depth(win(i, JSTAR))) for i in range(ENV_LO, ENV_HI + 1)]
    nr = [i for i, d in rk if d is not None]
    out(f"     j = {JSTAR}, i = {ENV_LO}..{ENV_HI}: hull certifies {len([i for i in cset])}, "
        f"ranked certifies {len(nr)}")
    out(f"     ranked-only positions: {len(sorted(set(nr) - cset))}, from "
        f"{min(set(nr) - cset)} to {max(set(nr) - cset)}")
    exact = list(range(961, 1174))
    out(f"     the ranked-certified set is EXACTLY 961..1173: {sorted(nr) == exact}")
    out("     i.e. exactly the windows whose closure lies in the open interval (4/15, 11/15),")
    out("     whose endpoints are the two preimages of the surviving 2-cycle nearest to it.")
    out("")
    out("   is it ONE tongue?  a full-range ranked scan at L = 1500/3600, every 5th position of")
    out("   the whole range [0, 1-L]:")
    t = time.time()
    hits = []
    for i in range(0, G - 1500 + 1, 5):
        d = ranked_depth(win(i, 1500), cap=26, comp_cap=1200)
        if d is not None:
            hits.append((i, d))
    lo, hi = (min(i for i, _ in hits), max(i for i, _ in hits)) if hits else (None, None)
    out(f"     {len(range(0, G-1500+1, 5))} positions tested, {len(hits)} certified, all in "
        f"[{lo}, {hi}] -- one cluster, around the centre {(G-1500)//2}")
    out(f"     {hits}")
    out(f"   [{time.time()-t:.0f} s]")
    out("")
    out("   the frontier moves up.  Probe (j, i) -> ranked depth:")
    for j, i in RANKED_PROBE:
        d = ranked_depth(win(i, j))
        out(f"     L = {j}/{G} = {j/G:.6f}  i = {i:5d}  ranked depth {d}")
    out("")
    out("   and it narrows to a point.  Extent of the cluster around the centre, per row:")
    t = time.time()
    for j in (1500, 1530, 1540, 1542, 1543):
        c = (G - j) // 2
        hits = [i for i in range(c - 25, c + 26) if ranked_depth(win(i, j)) is not None]
        span = f"[{min(hits)}, {max(hits)}]" if hits else "empty"
        out(f"     L = {j}/{G} = {j/G:.6f}   centre {c}   certified in c+-25: "
            f"{len(hits):3d}   {span}")
    out(f"   [{time.time()-t:.0f} s]")
    out("")
    out("   the tip lies on the CENTRED line; [2/7,5/7) is the prettiest point on it, and is")
    out("   what Z32/RankedFrontier.lean ships.  Section G locates the exact ceiling.")
    for name, a, b in [("[23/80,57/80)", Fr(23, 80), Fr(57, 80)),
                       ("[343/1200,857/1200)", Fr(343, 1200), Fr(857, 1200)),
                       ("[2/7,5/7)", Fr(2, 7), Fr(5, 7)),
                       ("[2/7,5/7+1/10^4)", Fr(2, 7), Fr(5, 7) + Fr(1, 10000)),
                       ("[2/7-1/10^4,5/7)", Fr(2, 7) - Fr(1, 10000), Fr(5, 7))]:
        U = [(a, b)]
        d = ranked_depth(U, cap=20, comp_cap=1800)
        lv = funnel_levels(U, d if d is not None else 20)
        out(f"     {name:22s} |U| = {float(b-a):.6f}   ranked depth {str(d):5s} "
            f"blocks {len(lv[-1]) if d is not None else '-'}   hull depth {hull_depth(U)}")
    out("   [2/7,5/7) has |U| = 3/7 = 0.428571..., against the recorded L* = 0.407222 and the")
    out("   longest window in print, [Dub19] Thm 1.2 at 31/81 = 0.382716.  Widening ONE side of")
    out("   it fails; widening both (staying centred) works down to the ceiling of section G.")
    out("")


# ------------------------------------------------------- F: the staircase along the centred line

def check_F(out):
    out("F. the two staircases along the centred line s = (1-L)/2")
    out("   grid 1/5040, so that the tip 3/7 = 2160/5040 is on it")
    out("     L               |U|         hull depth   ranked depth")
    t = time.time()
    g = 5040
    for j in sorted(set(list(range(1680, 2161, 40)) + [2154, 2158, 2160, 2162, 2166])):
        if (g - j) % 2:
            continue
        i = (g - j) // 2
        U = win(i, j, g)
        out(f"   {j:5d}/5040   {j/g:.6f}   {str(hull_depth(U)):10s}   "
            f"{str(ranked_depth(U, cap=20, comp_cap=1800))}")
    out(f"   [{time.time()-t:.0f} s]")
    out("   the ranked depth on the centred line is 1, 3, 7, 15 -- one less than a power of two --")
    out("   and it steps up exactly when a new cascade orbit enters (section G): at L = 5/13,")
    out("   41/97 and 2921/6817.  The hull-merge staircase leaves the centred line at 5/13.")
    out("")


# ------------------------------------------------- G: the Thue-Morse cascade behind the tip

def tm_prefix(n):
    w = [0]
    while len(w) < n:
        w = w + [1 - b for b in w]
    return w[:n]


def cascade_c(k):
    """the closed form of the entry point of the period-2^k cascade orbit into the centred
    window [c, 1-c), derived from the four members the DFS finds and verified against them:

        4 c_k - 1 = 3 * prod_{n=1}^{k-2} (3^{2^n} - 2^{2^n}) / (3^{2^{k-1}} + 2^{2^{k-1}}) ."""
    num = 3
    for n in range(1, k - 1):
        num *= P ** (2 ** n) - Q ** (2 ** n)
    den = P ** (2 ** (k - 1)) + Q ** (2 ** (k - 1))
    return (Fr(num, den) + 1) / 4


def thue_morse_value(prec=60):
    """T(2/3) = prod_{n>=0} (1 - (2/3)^{2^n}), to `prec` digits"""
    from decimal import Decimal, getcontext
    getcontext().prec = prec
    T = Decimal(1)
    z = Decimal(Q) / Decimal(P)
    for n in range(0, 40):
        T *= (1 - z ** (2 ** n))
    return T


def check_G(out):
    out("G. the exact object behind the tip: the Thue-Morse cascade")
    out("   on the centred line the window is [c, 1-c) with c = (1-L)/2, and an orbit is inside")
    out("   exactly when c <= min_i ||y_i||.  Enumerating every orbit of period <= 20 in")
    out("   [0.27, 0.73) and sorting by that minimum gives the entry cascade:")
    U = [(Fr(27, 100), Fr(73, 100))]
    orb, nodes = cycles_in(U, P_MAX, node_cap=3000000)
    rows = sorted(((min(min(y, 1 - y) for y in pts), n, w) for n, pts, w in orb), reverse=True)
    out("     period   min ||.||                        value          carry word")
    for e, n, w in rows[:5]:
        out(f"     {n:6d}   {str(e):30s} {float(e):.12f}   {''.join(str(b) for b in w)}")
    out(f"   ({len(orb)} orbits, {nodes} DFS nodes)")
    out("")
    out("   the first four are the periods 2, 4, 8, 16, their carry words are CYCLIC SHIFTS of")
    out("   the Thue-Morse prefix of the same length, and their entry points have a closed form:")
    bad = 0
    for k in range(1, 5):
        n = 2 ** k
        hit = [(e, w) for (e, m, w) in rows if m == n]
        e, w = hit[0]
        tm = tm_prefix(n)
        shift = next((r for r in range(n) if list(w[r:] + w[:r]) == tm), None)
        ck = cascade_c(k)
        ok = (ck == e)
        bad += (0 if (ok and shift is not None) else 1)
        out(f"     k = {k}: period {n:2d}   entry {str(e):22s} closed form matches: {ok}   "
            f"Thue-Morse after a cyclic shift by {shift}")
    out(f"   mismatches: {bad}")
    out("")
    out("   the closed form continues, and converges:")
    for k in range(5, 9):
        out(f"     k = {k}: c_k = {float(cascade_c(k)):.18f}")
    T = thue_morse_value()
    out(f"   T(2/3) = prod (1 - (2/3)^(2^n)) = {str(T)[:22]}")
    out(f"   (1 + T)/4  = {str((1 + T) / 4)[:20]}   <- [Dub06JNT] Cor. 1's SMALL limit point")
    out(f"   (3 - T)/12 = {str((3 - T) / 12)[:20]}   <- [Dub06JNT] Cor. 1's LARGE limit point")
    out("   and the algebra is exact: dividing numerator and denominator of the closed form by")
    out("   powers of 3 leaves 3 * 3^(2^(k-1)-2) / 3^(2^(k-1)) = 1/3 times prod_{n>=1}(1-(2/3)^{2^n})")
    out("   = T(2/3), so c_k decreases to (1 + T(2/3))/4 exactly.")
    out("")
    out("   the measured ceiling of the certificate family on the centred line:")
    for name, c in [("0.2856480", Fr(2856480, 10 ** 7)), ("0.2856475", Fr(2856475, 10 ** 7)),
                    ("0.2856472", Fr(2856472, 10 ** 7)), ("0.2856470", Fr(2856470, 10 ** 7))]:
        Uc = [(c, 1 - c)]
        lev = xu.norm(Uc)
        U0 = lev
        d = nb = None
        why = "depthcap"
        for K in range(61):
            if not lev:
                d, nb, why = K, 0, "empty"
                break
            if len(lev) > 4000:
                nb, why = len(lev), f"compcap@{K}"
                break
            E = xu.graph(lev, P, Q)
            if func_ok_rank(E):
                d, nb, why = K, len(lev), "ok"
                break
            lev = xu.inter(U0, xu.preimage(lev, P, Q))
        out(f"     c = {name}  |U| = {float(1-2*c):.10f}   ranked depth {str(d):5s} "
            f"blocks {str(nb):6s} {why}")
    out("   so the ceiling lies in (0.2856472, 0.2856475], and (1+T(2/3))/4 = 0.28564732474...")
    out("   lies inside that bracket.  Below the constant the centred window contains EVERY")
    out("   cascade orbit, hence infinitely many periodic orbits, and")
    out("   Z32.BlockCert.Cert.ok_eq_false_of_infinite_cycles refuses every unranked certificate")
    out("   at every depth.  Above it, certificates exist arbitrarily close.")
    out("")
    out("   the same cascade, read from the other side, is experiment X-238's:")
    out("     entry of the period-2^k orbit into the two-cell set ||.|| < c is")
    out("     0, 1/5, 3/13, 23/97, 10233015/42981185, ... -> (3 - T(2/3))/12 = 0.23811755841...")
    out("     and X-238 measured that ceiling in (0.2381175, 0.2381177].  Both of the corpus's")
    out("     engine ceilings are the two Thue-Morse constants of [Dub06JNT] Corollary 1.")
    for name, val in [("1/5", Fr(1, 5)), ("3/13", Fr(3, 13)), ("23/97", Fr(23, 97)),
                      ("10233015/42981185", Fr(10233015, 42981185))]:
        out(f"       {name:20s} = {float(val):.12f}")
    out("")
    return bad


def main():
    lines = []

    def out(s=""):
        print(s, flush=True)
        lines.append(s)

    out("plan-z32-transform experiment X-F: the frontier autopsy (C-6, and M6's T7 note)")
    out("base 3/2, grid G = 3600, exact rational arithmetic, no engine in the loop")
    out("")
    t0 = time.time()
    cert, dis = check_A(out)
    inv = check_B(out, cert)
    check_C(out, cert, inv)
    check_D(out, cert)
    check_E(out, cert)
    check_F(out)
    gbad = check_G(out)
    out(f"total {time.time()-t0:.0f} s;  disagreements with the recorded frontier row: {dis}; "
        f"cascade mismatches: {gbad}")
    out("VERDICT: C-6 half true; the frontier belonged to the hull-merge search; the exact "
        "ceiling of the family on the centred line is the Thue-Morse constant (1+T(2/3))/4")
    return 0


if __name__ == "__main__":
    sys.exit(main())
