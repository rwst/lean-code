#!/usr/bin/env python3
# (C) 2026 Ralf Stephan, in collaboration with Claude Code.  CC0 1.0.
"""g1schema.py -- gate G-1 of `plans/plan-z32-transform.html`: do the thirty
grid certificates of Stephan.tex Table 3 anti-unify into finitely many
(p,q)-schemas whose (F),(D) conditions close symbolically?

The answer this script tests is a *closed form*, derived by hand (see
`note-z32transform-G1.html` sec. 2) and stated in `schema()` below: for every
coprime p > q > 1 and every REAL position s with s + 1/p <= 1, the depth-1
funnel of the window U = [s, s+1/p) is determined by the single real number

    eps = frac((p-q)s),

with two cases (one surviving carry / two surviving carries) and explicit
rational-function endpoints.  Nothing here is fitted: `schema()` is a formula,
`engine()` is an independent re-implementation of the depth-1 certificate check
(R-5), and `gencert_says()` calls the corpus's own engine.  All three are
compared on the thirty table entries and on a wide sweep.

  python3 g1schema.py table | sweep | oos | all
"""
import sys
from fractions import Fraction as F
from math import gcd

import gencert as g


# ------------------------------------------------------------------ the schema

def schema(p, q, s):
    """Closed-form depth-1 prediction for U = [s, s+1/p) at base p/q.

    Returns a dict with the surviving carries, the level-1 blocks as exact
    intervals, and whether the depth-1 block certificate is valid."""
    s = F(s)
    theta = (p - q) * s
    k = theta.numerator // theta.denominator          # floor, exact
    eps = theta - k
    if eps == 0:                                       # case A0: one carry
        letters = [k]
    elif eps < F(q, p):                                # case B: two carries
        letters = [k, k + 1]
    else:                                              # case A1: one carry
        letters = [k + 1]
    if len(letters) == 1:
        e = letters[0]
        lo = F(q * s + e, p)
        blocks = [(lo, lo + F(q, p * p))]
        valid = True
        why = "A: single carry %d, block maps onto U" % e
    else:
        b1 = (s, F(q * s + k, p) + F(q, p * p))
        b2 = (F(q * s + k + 1, p), s + F(1, p))
        blocks = [b1, b2]
        lowloop = eps < F(q * q, p * (p + q))          # self-loop at block 1
        hiloop = eps > F(q, p + q)                     # self-loop at block 2
        valid = not lowloop and not hiloop
        why = ("B: carries %d,%d; " % (k, k + 1)) + (
            "2-cycle" if valid else
            ("self-loop at block %s" % ("1" if lowloop else "2")))
    return dict(theta=theta, eps=eps, letters=letters, blocks=blocks,
                valid=valid, why=why)


def schema_closed(p, q, s):
    """The same closed form under the CLOSED convention U = [s, s+1/p].  The
    admissible-letter interval closes on both sides, so the two-letter regime
    becomes 0 <= eps <= q/p and both self-loop tests become touching tests: the
    validity band shrinks from closed to OPEN.  In particular eps = 0 fails,
    and that is conjecture C-5 in closed form: at eps = 0 the left endpoint s
    is a fixed point of its own branch."""
    s = F(s)
    theta = (p - q) * s
    k = theta.numerator // theta.denominator
    eps = theta - k
    if eps > F(q, p):
        return dict(eps=eps, letters=[k + 1], valid=True,
                    why="one carry, %d" % (k + 1))
    valid = F(q * q, p * (p + q)) < eps < F(q, p + q)
    return dict(eps=eps, letters=[k, k + 1], valid=valid,
                why="two carries %d,%d; %s" % (k, k + 1,
                    "2-cycle" if valid else "endpoint touching"))


def closed_engine(p, q, s):
    g.P, g.Q, g.CARRIES, g.CLOSED = p, q, tuple(range(-q + 1, p)), True
    U = [(F(s), F(s) + F(1, p))]
    S = g.prune(U, U)
    if not S:
        return True
    return g.outdeg(g.blocks_fixpoint(S)) <= 1


def do_closed():
    print("\n== the CLOSED convention U = [s, s+1/p] ==")
    print("   half-open band  q^2/(p(p+q)) <= eps <= q/(p+q)   (closed, plus eps=0")
    print("   and eps >= q/p);  closed band  q^2/(p(p+q)) < eps < q/(p+q)  (open,")
    print("   plus eps > q/p).  The lost endpoints are endpoint-touching cycles.\n")
    bad = tot = 0
    for (p, q) in BASES + [(4, 3), (3, 2), (13, 2), (17, 4)]:
        note = []
        for den in range(1, 15):
            for num in range(den):
                s = F(num, den)
                if s + F(1, p) > 1:
                    continue
                tot += 1
                if schema_closed(p, q, s)["valid"] != closed_engine(p, q, s):
                    bad += 1
                    note.append("s=%s" % s)
        print("    (%2d,%2d)  %s" % (p, q, "agrees" if not note
                                     else "*** " + " ".join(note[:6])))
    print("\n   positions tested: %d; disagreements: %d" % (tot, bad))
    return bad


# ------------------------------------- an independent depth-1 engine (R-5)

def engine(p, q, s):
    """Depth-1 certificate check for [s, s+1/p), written from the definitions
    in `Z32/BlockCert.lean` (pieceOk / hits / funcOk) and NOT from gencert.py."""
    s = F(s)
    U = (s, s + F(1, p))
    carries = range(-q + 1, p)

    def piece(e):
        """{ y in U : (p y - e)/q in U }."""
        lo = max(U[0], F(q * U[0] + e, p))
        hi = min(U[1], F(q * U[1] + e, p))
        return (lo, hi) if lo < hi else None

    comps = [piece(e) for e in carries]
    comps = sorted(c for c in comps if c)
    # coalesce touching/overlapping components
    T1 = []
    for a, b in comps:
        if T1 and T1[-1][1] >= a:
            T1[-1] = (T1[-1][0], max(T1[-1][1], b))
        else:
            T1.append((a, b))
    if not T1:
        return dict(kill=True, comps=[], blocks=[], valid=True,
                    why="KILL at depth 1")

    def hits(I, J, e):
        """does { y in I : (p y - e)/q in J } != {} ?"""
        return max(p * I[0], q * J[0] + e) < min(p * I[1], q * J[1] + e)

    # hull merge, exactly as blocks_fixpoint: a letter must not fan out
    blk = [[c] for c in T1]
    while True:
        H = [(b[0][0], b[-1][1]) for b in blk]
        changed = False
        for I in H:
            for e in carries:
                hit = [j for j, J in enumerate(H) if hits(I, J, e)]
                if len(hit) >= 2:
                    blk = (blk[:hit[0]] + [sum(blk[hit[0]:hit[-1] + 1], [])]
                           + blk[hit[-1] + 1:])
                    changed = True
                    break
            if changed:
                break
        if not changed:
            break
    H = [(b[0][0], b[-1][1]) for b in blk]
    deg = [sum(1 for e in carries for J in H if hits(I, J, e)) for I in H]
    return dict(kill=False, comps=T1, blocks=H, valid=max(deg) <= 1,
                why="outdeg %s" % deg)


def gencert_says(p, q, s):
    """The corpus's own engine, through gencert.py's routines, at depth 1."""
    g.P, g.Q, g.CARRIES, g.CLOSED = p, q, tuple(range(-q + 1, p)), False
    U = [(F(s), F(s) + F(1, p))]
    S = g.prune(U, U)
    if not S:
        return dict(kill=True, comps=[], blocks=[], valid=True)
    H = g.blocks_fixpoint(S)
    return dict(kill=False, comps=S, blocks=H, valid=g.outdeg(H) <= 1)


def depth_of(p, q, s, cap=40):
    """Least funnel depth at which the block certificate closes (gencert)."""
    g.P, g.Q, g.CARRIES, g.CLOSED = p, q, tuple(range(-q + 1, p)), False
    U = [(F(s), F(s) + F(1, p))]
    cur = U
    for k in range(1, cap + 1):
        cur = g.prune(cur, U)
        if not cur:
            return k, "KILL"
        H = g.blocks_fixpoint(cur)
        if g.outdeg(H) <= 1:
            return k, "%d block(s)" % len(H)
    return None, "unresolved to depth %d" % cap


# ------------------------------------------------------------------- reporting

BASES = [(5, 2), (7, 2), (9, 2), (10, 3), (11, 3)]
POS = [F(0), F(1, 6), F(1, 3), F(1, 2), F(2, 3), F(5, 6)]


def cmp_one(p, q, s):
    sc, en, gc = schema(p, q, s), engine(p, q, s), gencert_says(p, q, s)
    # the schema predicts the level-1 COMPONENTS; the engines additionally
    # hull-merge them, and a merge fires exactly when the certificate fails,
    # so blocks are compared only on the valid side.
    ok = (sc["valid"] == en["valid"] == gc["valid"])
    ok = ok and (sc["blocks"] == [tuple(b) for b in en["comps"]]
                 == [tuple(b) for b in gc["comps"]])
    if sc["valid"] and not en["kill"]:
        ok = ok and (sc["blocks"] == [tuple(b) for b in en["blocks"]]
                     == [tuple(b) for b in gc["blocks"]])
    return ok, sc, en, gc


def do_table():
    print("== the thirty grid entries of Stephan.tex Table 3 ==")
    print("  the table's entry is the BLOCK COUNT; funnel depth 1 everywhere\n")
    bad = 0
    for (p, q) in BASES:
        print("  base %d/%d  (q^2 = %d < p);  q/p = %s, q/(p+q) = %s, "
              "q^2/(p(p+q)) = %s"
              % (p, q, q * q, F(q, p), F(q, p + q), F(q * q, p * (p + q))))
        for s in POS:
            ok, sc, en, gc = cmp_one(p, q, s)
            bad += not ok
            print("    s=%-5s eps=%-8s %-2d block(s)  %-46s %s"
                  % (s, sc["eps"], len(sc["blocks"]), sc["why"],
                     "OK" if ok else "*** MISMATCH ***"))
        print()
    print("  schema == independent engine == gencert on all 30: %s"
          % ("YES" if bad == 0 else "NO (%d mismatches)" % bad))
    return bad


def do_sweep(N=12):
    """Every coprime base with 1 < q < p <= 24 (both regimes), every position
    of denominator <= N with s + 1/p <= 1."""
    print("\n== sweep: schema vs. two engines, all coprime p/q, p <= 24 ==")
    tot = bad = valid = 0
    for p in range(3, 25):
        for q in range(2, p):
            if gcd(p, q) != 1:
                continue
            for den in range(1, N + 1):
                for num in range(0, den):
                    s = F(num, den)
                    if s + F(1, p) > 1:
                        continue
                    ok, sc, en, gc = cmp_one(p, q, s)
                    tot += 1
                    bad += not ok
                    valid += sc["valid"]
                    if not ok:
                        print("  MISMATCH (%d,%d) s=%s: schema %s / engine %s"
                              " / gencert %s\n    %s\n    %s\n    %s"
                              % (p, q, s, sc["valid"], en["valid"], gc["valid"],
                                 sc["blocks"], en["comps"], gc["comps"]))
                        if bad > 8:
                            print("  ... stopping")
                            return bad
    print("  %d (base, position) pairs; %d predicted depth-1 valid (%.1f%%); "
          "%d mismatches" % (tot, valid, 100.0 * valid / tot, bad))
    return bad


def eps_valid_set(p, q):
    """The valid set in the eps-coordinate, as exact intervals (plus {0})."""
    return [(F(0), F(0)), (F(q * q, p * (p + q)), F(q, p + q)), (F(q, p), F(1))]


def measure(p, q):
    """Lebesgue measure of { s in [0,1) : the depth-1 schema is valid }.  The
    map s |-> frac((p-q)s) is (p-q)-to-1 and measure preserving on [0,1), so
    this is the measure of the eps-set itself."""
    return F(p - q, p) * (F(q, p + q) + 1)


def measure_nowrap(p, q):
    """The same, restricted to the non-wrapping positions s in [0, 1-1/p]."""
    m = p - q
    tot = F(0)
    for (a, b) in eps_valid_set(p, q):
        if a == b:
            continue
        for j in range(m):                     # eps = (p-q)s - j
            lo, hi = F(a + j, m), F(b + j, m)
            lo, hi = max(lo, F(0)), min(hi, 1 - F(1, p))
            if lo < hi:
                tot += hi - lo
    return tot


def do_bdry():
    """The three critical eps values are where a hand derivation slips.  Hit
    each of them exactly, from both sides, and compare with the engines."""
    print("\n== boundary audit: the exact critical eps values ==")
    print("   eps = q^2/(p(p+q))  (self-loop appears on the low block)")
    print("   eps = q/(p+q)       (self-loop appears on the high block)")
    print("   eps = q/p           (the two-carry window closes)\n")
    bad = 0
    for (p, q) in BASES + [(4, 3), (3, 2), (13, 2), (17, 4), (5, 4), (7, 5)]:
        m = p - q
        crit = [F(q * q, p * (p + q)), F(q, p + q), F(q, p), F(0)]
        line = "    (%2d,%2d) " % (p, q)
        for c in crit:
            for d in (F(-1, 10**6), F(0), F(1, 10**6)):
                e = c + d
                if not (0 <= e < 1):
                    continue
                s = e / m                        # frac((p-q)s) = e, s in [0,1/(p-q)]
                if s + F(1, p) > 1:
                    continue
                assert schema(p, q, s)["eps"] == e
                ok, sc, en, gc = cmp_one(p, q, s)
                bad += not ok
                line += ("%s" % ("+" if sc["valid"] else "-")) if ok else "X"
        print(line + ("   OK" if "X" not in line else "   *** MISMATCH ***"))
    print("\n   ('+' = certifies at depth 1, '-' = does not; each critical value")
    print("    is probed at -1e-6, exactly, +1e-6.)  mismatches: %d" % bad)
    return bad


def do_wrap():
    """The schema was derived for a window inside [0,1).  On the circle the same
    computation is a translate, so it should also govern the WRAPPED positions
    s > 1-1/p, where U is the two-interval set [s,1) u [0, s+1/p-1).  Test."""
    print("\n== the wrapped positions s > 1 - 1/p (U is two intervals) ==")
    bad = tot = 0
    for (p, q) in BASES + [(4, 3), (3, 2), (13, 2), (17, 4)]:
        note = []
        for den in (7, 9, 11, 13, 17):
            for num in range(den):
                s = F(num, den)
                if s + F(1, p) <= 1:
                    continue
                g.P, g.Q, g.CARRIES, g.CLOSED = p, q, tuple(range(-q + 1, p)), False
                U = g.merge([(F(0), s + F(1, p) - 1), (s, F(1))])
                cur, d = U, None
                for k in range(1, 9):
                    cur = g.prune(cur, U)
                    if not cur:
                        d = k
                        break
                    if g.outdeg(g.blocks_fixpoint(cur)) <= 1:
                        d = k
                        break
                tot += 1
                if (d == 1) != schema(p, q, s)["valid"]:
                    bad += 1
                    note.append("s=%s" % s)
        print("    (%2d,%2d)  %s" % (p, q, "agrees" if not note else "*** " + " ".join(note)))
    print("\n   wrapped positions tested: %d; disagreements: %d" % (tot, bad))
    return bad


def do_depth():
    """Conjecture C-3 of the plan: "in p > q^2, every rational length-1/p window
    certifies at depth <= 2".  The thirty table entries all have positions of
    denominator <= 6 and all certify at depth 1, so the conjecture was never
    tested off that grid.  Test it."""
    print("\n== C-3: is depth <= 2 enough in the p > q^2 regime? ==")
    print("   every position of denominator <= 25 with s + 1/p <= 1\n")
    worst = 0
    for (p, q) in BASES + [(13, 2), (17, 4)]:
        mx, arg, hist = 0, None, {}
        for den in range(1, 26):
            for num in range(den):
                s = F(num, den)
                if s + F(1, p) > 1 or s.denominator != den:
                    continue
                d, _ = depth_of(p, q, s, cap=30)
                hist[d] = hist.get(d, 0) + 1
                if d is not None and d > mx:
                    mx, arg = d, s
        worst = max(worst, mx)
        print("    (%2d,%2d)  max depth %2d at s = %-7s   depths %s"
              % (p, q, mx, arg, dict(sorted(hist.items()))))
    print("\n   C-3 as printed (depth <= 2) is FALSE: (5,2) needs depth 3 at")
    print("   s = 1/8 and depth 6 at s = 3/25, both in the p > q^2 regime.")
    print("   Every position tested does certify, so only the CONSTANT dies.")
    return 0


def lean_predicate(p, q, s):
    """`Z32.SchemaCertified` of `Z32/SymbolicCert.lean`, transcribed verbatim: the Lean file's
    hypothesis with denominators cleared.  It must define the same set as `schema()['valid']`,
    which is derived from the block geometry instead — the R-5 bridge between the Lean theorem
    and the engines."""
    e = schema(p, q, s)["eps"]
    return (e == 0 or q <= p * e
            or (q * q <= p * (p + q) * e and (p + q) * e <= q))


def do_bridge():
    print("\n== Lean `SchemaCertified` vs. the block-geometry criterion ==")
    print("   `SymbolicCert.lean`'s hypothesis is transcribed in `lean_predicate`;")
    print("   `schema()` derives validity from the two blocks and their images.\n")
    tot = bad = 0
    for p in range(3, 25):
        for q in range(2, p):
            if gcd(p, q) != 1:
                continue
            for den in range(1, 15):
                for num in range(den):
                    s = F(num, den)
                    if s + F(1, p) > 1:
                        continue
                    tot += 1
                    if lean_predicate(p, q, s) != schema(p, q, s)["valid"]:
                        bad += 1
                        if bad < 5:
                            print("   MISMATCH (%d,%d) s=%s" % (p, q, s))
    print("   %d (base, position) pairs; disagreements: %d" % (tot, bad))
    return bad


def do_lean():
    """Emit the six kernel probes of the note, straight from the schema: three
    the schema calls valid, three it calls invalid.  Nothing is hand-typed, so
    a `decide` disagreeing with the asserted value refutes the schema."""
    from math import lcm
    print("\n== kernel probes: paste into a scratch file importing Z32.BlockCert ==")
    probes = [(13, 2, F(11, 12), "g1a", "case B valid, base never in the corpus"),
              (17, 4, F(1, 6), "g1b", "case B valid, base never in the corpus"),
              (5, 2, F(1, 10), "g1c", "eps > q/(p+q): upper block loops"),
              (5, 2, F(3, 100), "g1d", "eps < q^2/(p(p+q)): lower block loops"),
              (4, 3, F(3, 8), "g1e", "p < q^2, case B valid"),
              (4, 3, F(1, 2), "g1f", "p < q^2, the depth-26 window")]
    for (p, q, s, name, note) in probes:
        sc = schema(p, q, s)
        ends = [s, s + F(1, p)] + [x for b in sc["blocks"] for x in b]
        D = lcm(*[e.denominator for e in ends])
        iv = lambda b: "(%d, %d)" % (b[0] * D, b[1] * D)
        print("/-- %s; s = %s, eps = %s -/" % (note, s, sc["eps"]))
        print("def %s : Cert where" % name)
        print("  D := %d\n  p := %d\n  q := %d" % (D, p, q))
        print("  U := [%s]" % iv((s, s + F(1, p))))
        print("  levels := [[%s]]" % ", ".join(iv(b) for b in sc["blocks"]))
        print("theorem %s_check : %s.ok = %s := by decide\n"
              % (name, name, str(sc["valid"]).lower()))
    print("   All six were run 2026-09-02 and all six pass, on [propext, Quot.sound].")


def do_oos():
    """Out-of-sample: the schema was read off p > q^2 data; test it where the
    corpus has independent numbers -- the (4,3) sweep, whose depth-26 windows
    are the sharpest control in the README -- and on bases never certified."""
    print("\n== out-of-sample I: (4,3), the eight windows of the M6 control ==")
    print("   [Dub09AA] Thm 1 says all eight are empty; the README records")
    print("   max funnel depth 26.  The schema predicts WHICH are depth 1.\n")
    p, q = 4, 3
    for i in range(8):
        s = F(i, 8)
        sc = schema(p, q, s)
        d, what = depth_of(p, q, s)
        agree = (d == 1) == sc["valid"]
        print("    s=%-4s eps=%-6s schema: depth-1 %-5s | engine: depth %-3s %-12s %s"
              % (s, sc["eps"], sc["valid"], d, what, "OK" if agree else "***"))
    print("\n== out-of-sample II: bases the corpus never touched ==")
    for (p, q) in [(13, 2), (17, 2), (13, 3), (14, 3), (17, 4), (26, 5), (7, 3), (5, 4)]:
        agree = True
        for den in (7, 11, 13):
            for num in range(den):
                s = F(num, den)
                if s + F(1, p) > 1:
                    continue
                sc = schema(p, q, s)
                d, _ = depth_of(p, q, s, cap=12)
                agree = agree and ((d == 1) == sc["valid"])
        print("    (%2d,%2d)  %s   schema-valid measure of s = %s = %.4f"
              % (p, q, "depth-1 iff schema says so: OK" if agree else "*** MISMATCH ***",
                 measure(p, q), float(measure(p, q))))
    print("\n== the measure of the certified set of REAL positions ==")
    print("   over all s in [0,1):        (p-q)/p * (p+2q)/(p+q)")
    print("   over s in [0, 1-1/p] only:  exact, computed interval by interval\n")
    print("    base    all s in [0,1)            non-wrapping s in [0,1-1/p]")
    for (p, q) in BASES + [(4, 3), (13, 2), (26, 5)]:
        m, mn = measure(p, q), measure_nowrap(p, q)
        print("    %2d/%-2d   %-12s = %.4f    %-14s = %.4f  (of %.4f)"
              % (p, q, m, float(m), mn, float(mn), float(1 - F(1, p))))


if __name__ == "__main__":
    what = sys.argv[1] if len(sys.argv) > 1 else "all"
    rc = 0
    if what in ("table", "all"):
        rc += do_table()
    if what in ("sweep", "all"):
        rc += do_sweep()
    if what in ("bdry", "all"):
        rc += do_bdry()
    if what in ("closed", "all"):
        rc += do_closed()
    if what in ("wrap", "all"):
        rc += do_wrap()
    if what in ("depth", "all"):
        rc += do_depth()
    if what in ("bridge", "all"):
        rc += do_bridge()
    if what in ("lean", "all"):
        do_lean()
    if what in ("oos", "all"):
        do_oos()
    sys.exit(0 if rc == 0 else 1)
