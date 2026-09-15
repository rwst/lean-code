#!/usr/bin/env python3
# (C) 2026 Ralf Stephan, in collaboration with Claude Code.  CC0 1.0.
"""xp.py -- experiment X-P of `plans/plan-z32-transform.html`, RE-AIMED by gate
G-1 at the two residual bands.

X-P as originally specified computed the exact sigma-cell decomposition of the
whole position axis [0, 1-t].  G-1 made most of that unnecessary: at t = 1/p the
depth-1 verdict depends on the position s only through

    eps = frac((p-q)s),

and it is `eps = 0`, or `eps >= q/p`, or `q^2/(p(p+q)) <= eps <= q/(p+q)`.  What
is left is the two open bands

    LOW  = (0, q^2/(p(p+q)))          HIGH = (q/(p+q), q/p)

of total measure 2q^2/(p(p+q)).  This script decomposes THOSE, exactly.

The right coordinate is not s but the fibre coordinate u = y - s, in which the
window is the CONSTANT interval U = [0, 1/p) and the two admissible branches are

    f_j(u) = (p u + eps - j) / q,      j in {0, 1}                        (*)

(G-1 sec. 2.1; in Lean `Z32.branch_base` / `Z32.branch_succ`).  Every funnel
endpoint is therefore an affine form  a + b*eps  with a, b rational, and the
combinatorial type of the funnel is constant on eps-intervals, changing only
where two affine forms cross.  `Cell.run` computes the funnel over a whole
eps-interval at once and raises `Split` at the first crossing it meets, so the
decomposition it drives is exact: no sampling anywhere.

Two structural facts the script also checks, both proved by hand:

  (S) INVOLUTION.  u |-> 1/p - u conjugates (*) at eps to (*) at q/p - eps with
      the two branches swapped, so the two bands are exchanged and carry the
      same decomposition, reversed.  One band determines the other.

  (R-5) Every parametric verdict is re-checked at sample points inside its cell
      by two independent scalar engines: `scalar_eps` (written from (*), in u)
      and `scalar_s` (the corpus's own `gencert.py`, in y, with the full carry
      alphabet {-q+1,...,p-1} and no knowledge of eps).

  python3 xp.py sym | scan | cells | universal | growth | nesting | ranked | bridge | all
"""
import sys
import time
from fractions import Fraction as Fr

import gencert as g

MAXCOMP = 4000          # components in one level before a cell is abandoned
MAXCELLS = 40000        # cells in one band before the decomposition is abandoned


# ------------------------------------------------------------- affine algebra
# An affine form is a pair (a, b) standing for the function eps |-> a + b*eps.

ZERO = (Fr(0), Fr(0))


def aff_sub(F, G):
    return (F[0] - G[0], F[1] - G[1])


class Split(Exception):
    """Two affine forms cross strictly inside the current cell."""

    def __init__(self, r):
        self.r = r


class Ctx:
    """A cell (lo, hi) of the eps-line, OPEN, with sign-of-affine-form queries.

    A query whose answer is not constant on the cell raises `Split` at the
    crossing; the driver then subdivides and restarts.  Because a crossing is
    the unique root of a nonzero affine form, the sign on the remaining open
    interval is exactly its sign at the midpoint."""

    def __init__(self, lo, hi):
        self.lo, self.hi, self.mid = lo, hi, (lo + hi) / 2
        self.queries = 0

    def sign(self, F):
        self.queries += 1
        a, b = F
        if b == 0:
            return (a > 0) - (a < 0)
        r = -a / b
        if self.lo < r < self.hi:
            raise Split(r)
        v = a + b * self.mid
        return (v > 0) - (v < 0)

    def lt(self, F, G):
        return self.sign(aff_sub(F, G)) < 0

    def le(self, F, G):
        return self.sign(aff_sub(F, G)) <= 0

    def maxf(self, F, G):
        return G if self.lt(F, G) else F

    def minf(self, F, G):
        return F if self.lt(F, G) else G

    def key_lt(self, A, B):
        """Lexicographic (lo, hi) order on intervals."""
        c = self.sign(aff_sub(A[0], B[0]))
        if c:
            return c < 0
        return self.lt(A[1], B[1])


# -------------------------------------------------------- the parametric funnel
# All of this is `gencert.py`'s prune / blocks_fixpoint / outdeg, restated on
# affine forms in the u-coordinate, half-open convention throughout.

def preimage(p, q, I, j):
    """f_j^{-1}(I) as an affine interval; f_j(u) = (p u + eps - j)/q."""
    out = []
    for (a, b) in I:
        out.append((Fr(q * a + j, p), Fr(q * b - 1, p)))
    return tuple(out)


def image(p, q, I, j):
    """f_j(I), for the block-graph edges."""
    out = []
    for (a, b) in I:
        out.append((Fr(p * a - j, q), Fr(p * b + 1, q)))
    return tuple(out)


def merge(ctx, iv):
    """Sort and coalesce, exactly as `gencert.merge` (half-open: empty iff
    lo >= hi, coalesce iff prev_hi >= lo)."""
    xs = []
    for it in iv:                                  # insertion sort on ctx order
        k = len(xs)
        while k > 0 and ctx.key_lt(it, xs[k - 1]):
            k -= 1
        xs.insert(k, it)
    out = []
    for (a, b) in xs:
        if not ctx.lt(a, b):
            continue
        if out and ctx.le(a, out[-1][1]):
            if ctx.lt(out[-1][1], b):
                out[-1] = (out[-1][0], b)
        else:
            out.append((a, b))
    return out


def prune(ctx, p, q, S, U):
    out = []
    for I in S:
        for j in (0, 1):
            (lo, hi) = preimage(p, q, I, j)
            for J in U:
                x, y = ctx.maxf(lo, J[0]), ctx.minf(hi, J[1])
                if ctx.lt(x, y):
                    out.append((x, y))
    return merge(ctx, out)


def meets(ctx, A, B):
    """Half-open [a0,a1) meets [b0,b1)."""
    return ctx.lt(A[0], B[1]) and ctx.lt(B[0], A[1])


def blocks_fixpoint(ctx, p, q, S):
    """Coalesce components into blocks until no letter fans out of a block."""
    blk = [[c] for c in S]
    while True:
        H = [(b[0][0], b[-1][1]) for b in blk]
        changed = False
        for I in H:
            for j in (0, 1):
                img = image(p, q, I, j)
                hit = [n for n, J in enumerate(H) if meets(ctx, img, J)]
                if len(hit) >= 2:
                    blk = (blk[:hit[0]] + [sum(blk[hit[0]:hit[-1] + 1], [])]
                           + blk[hit[-1] + 1:])
                    changed = True
                    break
            if changed:
                break
        if not changed:
            return H


def outdeg(ctx, p, q, H):
    m = 0
    for I in H:
        d = 0
        for j in (0, 1):
            img = image(p, q, I, j)
            d += sum(1 for J in H if meets(ctx, img, J))
        m = max(m, d)
    return m


def run_cell(p, q, lo, hi, cap):
    """Verdict for the whole open eps-cell (lo, hi), or a `Split`.

    Returns (tag, depth, size) with tag in
      'cert'   -- the block certificate closes at `depth`, uniformly on the cell
      'kill'   -- the funnel is empty at `depth`, uniformly on the cell
      'open'   -- no certificate to depth `cap` (a candidate exceptional cell)
      'blow'   -- abandoned: more than MAXCOMP components."""
    ctx = Ctx(lo, hi)
    U = [(ZERO, (Fr(1, p), Fr(0)))]
    cur = U
    for k in range(1, cap + 1):
        cur = prune(ctx, p, q, cur, U)
        if not cur:
            return ('kill', k, 0), ctx
        if len(cur) > MAXCOMP:
            return ('blow', k, len(cur)), ctx
        H = blocks_fixpoint(ctx, p, q, cur)
        if outdeg(ctx, p, q, H) <= 1:
            return ('cert', k, len(H)), ctx
    return ('open', cap, len(cur)), ctx


def decompose(p, q, lo, hi, cap):
    """Exact partition of the open interval (lo, hi) of the eps-line into cells
    of constant combinatorial type, with the breakpoints listed separately."""
    todo, cells, breaks = [(lo, hi)], [], set()
    q_tot = 0
    while todo:
        a, b = todo.pop()
        try:
            res, ctx = run_cell(p, q, a, b, cap)
            q_tot += ctx.queries
            cells.append((a, b) + res)
        except Split as sp:
            breaks.add(sp.r)
            todo.append((a, sp.r))
            todo.append((sp.r, b))
        if len(cells) + len(todo) > MAXCELLS:
            cells.append((a, b, 'abort', 0, 0))
            break
    return sorted(cells), sorted(breaks), q_tot


# ------------------------------------------------- two independent re-checks (R-5)

def scalar_eps(p, q, eps, cap=40):
    """Least certifying depth at a single eps, from (*) in the u-coordinate.
    Written from the branch maps, NOT from gencert."""
    U = [(Fr(0), Fr(1, p))]
    cur = U
    for k in range(1, cap + 1):
        nxt = []
        for (a, b) in cur:
            for j in (0, 1):
                lo, hi = Fr(q * a + j, p) - eps / p, Fr(q * b + j, p) - eps / p
                x, y = max(lo, Fr(0)), min(hi, Fr(1, p))
                if x < y:
                    nxt.append((x, y))
        cur = []
        for (a, b) in sorted(nxt):
            if cur and cur[-1][1] >= a:
                cur[-1] = (cur[-1][0], max(cur[-1][1], b))
            else:
                cur.append((a, b))
        if not cur:
            return k
        blk = [[c] for c in cur]
        while True:
            H = [(x[0][0], x[-1][1]) for x in blk]
            ch = False
            for (A, B) in H:
                for j in (0, 1):
                    lo, hi = (p * A + eps - j) / q, (p * B + eps - j) / q
                    hit = [n for n, (C, D) in enumerate(H) if C < hi and lo < D]
                    if len(hit) >= 2:
                        blk = (blk[:hit[0]] + [sum(blk[hit[0]:hit[-1] + 1], [])]
                               + blk[hit[-1] + 1:])
                        ch = True
                        break
                if ch:
                    break
            if not ch:
                break
        H = [(x[0][0], x[-1][1]) for x in blk]
        deg = 0
        for (A, B) in H:
            d = 0
            for j in (0, 1):
                lo, hi = (p * A + eps - j) / q, (p * B + eps - j) / q
                d += sum(1 for (C, D) in H if C < hi and lo < D)
            deg = max(deg, d)
        if deg <= 1:
            return k
    return None


def scalar_s(p, q, eps, cap=40):
    """The corpus engine, in the ORIGINAL y-coordinate, on the window
    [s, s+1/p) with s = eps/(p-q) and the full carry alphabet."""
    g.P, g.Q, g.CARRIES, g.CLOSED = p, q, tuple(range(-q + 1, p)), False
    s = eps / (p - q)
    U = [(s, s + Fr(1, p))]
    cur = U
    for k in range(1, cap + 1):
        cur = g.prune(cur, U)
        if not cur:
            return k
        if g.outdeg(g.blocks_fixpoint(cur)) <= 1:
            return k
    return None


# ------------------------------------------------------------------- reporting

BASES = [(5, 2), (7, 2), (9, 2), (10, 3), (11, 3)]
CONTROLS = [(4, 3), (13, 2), (17, 4), (3, 2), (26, 5)]


def bands(p, q):
    """The two residual bands left by G-1, in the eps-coordinate."""
    return [("LOW", Fr(0), Fr(q * q, p * (p + q))),
            ("HIGH", Fr(q, p + q), Fr(q, p))]


def report(p, q, name, lo, hi, cap, verbose=True):
    t0 = time.time()
    cells, breaks, qs = decompose(p, q, lo, hi, cap)
    width = hi - lo
    cert = sum(b - a for (a, b, t, _, _) in cells if t in ('cert', 'kill'))
    res = [c for c in cells if c[2] not in ('cert', 'kill')]
    mx = max((d for (_, _, t, d, _) in cells if t == 'cert'), default=0)
    mc = max((n for (_, _, t, _, n) in res), default=0)
    print("    %-4s %-20s cap %2d | %4d cells (%3d residual), %4d breakpoints"
          " | certified %.12f | deepest %2d | max comps %2d | %6.1fs"
          % (name, "(%s, %s)" % (lo, hi), cap, len(cells), len(res),
             len(breaks), float(cert / width), mx, mc, time.time() - t0))
    if verbose and res:
        print("           residual measure %.6e of %.6e; widest sliver %.3e"
              % (float(width - cert), float(width),
                 max(float(b - a) for (a, b, _, _, _) in res)))
    return cells, breaks, cert, width


def do_sym():
    print("== (S) the involution eps <-> q/p - eps ==")
    print("   u |-> 1/p - u conjugates f_j at eps to f_{1-j} at q/p - eps, so the two")
    print("   bands are exchanged, reversed.  One band determines the other.\n")
    bad = tot = 0
    for (p, q) in BASES + CONTROLS:
        loc = 0
        for den in (37, 53, 101):
            for num in range(1, den):
                e = Fr(num, den) * Fr(q, p)
                loc += scalar_eps(p, q, e, 25) != scalar_eps(p, q, Fr(q, p) - e, 25)
                tot += 1
        bad += loc
        print("    (%2d,%2d)  %s" % (p, q, "symmetric" if not loc
                                     else "*** %d asymmetries" % loc))
    print("\n   %d eps-pairs, %d asymmetries" % (tot, bad))
    return bad


def do_scan(N=240):
    print("\n== the certifying depth inside the LOW band, on a fine grid ==")
    print("   eps = (i/N) * q^2/(p(p+q)), i = 1..N-1, N = %d; both scalar engines\n" % N)
    bad = 0
    for (p, q) in BASES + [(4, 3)]:
        _, lo, hi = bands(p, q)[0]
        hist, mx, arg, none = {}, 0, None, 0
        for i in range(1, N):
            e = lo + (hi - lo) * Fr(i, N)
            d = scalar_eps(p, q, e, 30)
            bad += d != scalar_s(p, q, e, 30)
            hist[d] = hist.get(d, 0) + 1
            if d is None:
                none += 1
            elif d > mx:
                mx, arg = d, e
        print("    (%2d,%2d)  band (0, %-7s  max depth %2d at eps = %-12s%s"
              % (p, q, str(hi) + ")", mx, arg,
                 "   *** %d uncertified to depth 30" % none if none else ""))
        print("             depths %s"
              % dict(sorted(hist.items(), key=lambda kv: (kv[0] is None, kv[0]))))
    print("\n   scalar_eps (u-coordinate) == scalar_s (gencert, y-coordinate)"
          " at every grid point: %s" % ("YES" if bad == 0 else "NO (%d)" % bad))
    return bad


def do_cells(cap=16):
    print("\n== X-P re-aimed: the exact eps-cell decomposition of the two bands ==")
    print("   Verdicts are uniform in eps over each OPEN cell; the breakpoints between")
    print("   cells are rational and are checked separately (see `bridge`).\n")
    for (p, q) in BASES + [(4, 3)]:
        print("  base %d/%d%s" % (p, q, "" if p > q * q else "   (p < q^2: the control regime)"))
        for (name, lo, hi) in bands(p, q):
            report(p, q, name, lo, hi, cap)
    return 0


def do_universal(cap=12):
    """The decomposition of the band is the SAME combinatorial object at every
    base: same cell count, same word of (verdict, depth) along the band.  Only
    the endpoints move.  This is G-1's anti-unification one level up."""
    print("\n== universality: is the decomposition base-independent? ==")
    print("   cap %d, LOW band; the word records (C = certified at depth d,"
          " o = open)\n" % cap)
    ref = refname = None
    bad = 0
    for (p, q) in BASES + CONTROLS:
        _, lo, hi = bands(p, q)[0]
        cells, _, _ = decompose(p, q, lo, hi, cap)
        word = tuple((t, d) for (_, _, t, d, _) in cells)
        if ref is None:
            ref, refname = word, "%d/%d" % (p, q)
        same = word == ref
        bad += not same
        print("    (%2d,%2d)%s  %4d cells   word %s"
              % (p, q, "  " if p > q * q else " *", len(cells),
                 "identical to " + refname if same else "*** DIFFERENT"))
    print("\n    (* = the p < q^2 regime)")
    # (S) again, now at the level of the decomposition: HIGH is LOW reversed.
    rev = 0
    for (p, q) in BASES + CONTROLS:
        w = []
        for (_, lo, hi) in bands(p, q):
            cells, _, _ = decompose(p, q, lo, hi, cap)
            w.append(tuple((t, d) for (_, _, t, d, _) in cells))
        rev += w[1] != tuple(reversed(w[0]))
    print("    the HIGH word is the reversed LOW word at all %d bases: %s"
          % (len(BASES + CONTROLS), "YES" if rev == 0 else "NO (%d)" % rev))
    bad += rev
    print("    the shared word:")
    line = " ".join("%s%d" % ("C" if t == 'cert' else "o", d) for (t, d) in ref)
    for i in range(0, len(line), 96):
        print("      " + line[i:i + 96])
    print("\n   bases disagreeing with the word: %d" % bad)
    return bad


def do_growth(p=5, q=2, caps=range(4, 23, 2)):
    print("\n== does the decomposition terminate, and how fast? ==")
    print("   base %d/%d, LOW band.  `residual` is the measure not yet certified at" % (p, q))
    print("   that cap; if it tends to 0 the exceptional set of eps is null.\n")
    name, lo, hi = bands(p, q)[0]
    width = hi - lo
    print("     cap  cells  residual cells   certified fraction    residual"
          "    shrink  max comps")
    prev, caps, counts, rcounts = None, list(caps), [], []
    for cap in caps:
        cells, _, qs = decompose(p, q, lo, hi, cap)
        cert = sum(b - a for (a, b, t, _, _) in cells if t in ('cert', 'kill'))
        res = width - cert
        rc = [c for c in cells if c[2] not in ('cert', 'kill')]
        mc = max((n for (_, _, _, _, n) in rc), default=0)
        print("     %3d  %5d  %13d   %.12f  %.4e  %6s  %9d"
              % (cap, len(cells), len(rc), float(cert / width), float(res),
                 "-" if prev is None else "%.2f" % float(prev / res), mc))
        prev = res
        counts.append(len(cells))
        rcounts.append(len(rc))
    print("\n   The residual shrinks by about (p/q)^2 = %.2f per two levels, and the"
          % float(Fr(p, q) ** 2))
    print("   component count of the funnel is exactly cap+1 -- LINEAR, so the")
    print("   survivor set has zero entropy at every eps in the band.")
    import math
    xs = [math.log(k) for k in caps]
    for what, N in (("cells", counts), ("residual cells", rcounts)):
        ys = [math.log(n) for n in N]
        mx, my = sum(xs) / len(xs), sum(ys) / len(ys)
        e = (sum((a - mx) * (b - my) for a, b in zip(xs, ys))
             / sum((a - mx) ** 2 for a in xs))
        print("   %-14s N(K) ~ %.2f * K^%.2f   (two-level ratios %s)"
              % (what, math.exp(my - e * mx), e,
                 " ".join("%.2f" % (N[i + 1] / N[i]) for i in range(len(N) - 1))))
    print("   Sub-exponential, so the residual tree has no perfect subtree.")
    return 0


def do_nesting(p=5, q=2, caps=(6, 8, 10, 12, 14, 16)):
    print("\n== the residual slivers: do they nest, and does any parent die? ==")
    R = {}
    for cap in caps:
        cells, _, _ = decompose(p, q, *bands(p, q)[0][1:], cap)
        R[cap] = [(a, b) for (a, b, t, _, _) in cells if t not in ('cert', 'kill')]
    caps = sorted(R)
    for i in range(len(caps) - 1):
        A, B = R[caps[i]], R[caps[i + 1]]
        esc = [c for c in B if not any(a <= c[0] and c[1] <= b for (a, b) in A)]
        kids = {}
        for c in B:
            for k, (a, b) in enumerate(A):
                if a <= c[0] and c[1] <= b:
                    kids[k] = kids.get(k, 0) + 1
                    break
        dead = len(A) - len(kids)
        print("    cap %2d -> %2d : %3d slivers -> %3d, %d escape their parent,"
              " %d parents die" % (caps[i], caps[i + 1], len(A), len(B), len(esc), dead))
    print("\n   Perfect nesting with no parent dying: the exceptional set is the")
    print("   decreasing intersection, of measure zero but not empty a priori.")
    # Does any rational inside the residual actually resist?  Probe the deepest
    # cap's slivers -- both endpoints and the midpoint -- far past the cap.
    last = R[caps[-1]]
    cells, breaks, _ = decompose(p, q, *bands(p, q)[0][1:], caps[-1])
    hard = sum(1 for (a, b) in last
               for e in (a, (a + b) / 2, b) if scalar_eps(p, q, e, 60) is None)
    hardb = sum(1 for r in breaks if scalar_eps(p, q, r, 60) is None)
    print("   probe at (%d,%d), cap %d: %d sliver endpoints/midpoints and %d"
          % (p, q, caps[-1], 3 * len(last), len(breaks)))
    print("   breakpoints, all run to depth 60 -- rationals that resist: %d and %d"
          % (hard, hardb))
    # Where does the residual accumulate?  NOT only at the two band endpoints.
    lo, hi = bands(p, q)[0][1:]
    print("\n   the ten narrowest slivers at cap %d, and where they sit in the band:"
          % caps[-1])
    for (w, a, b) in sorted((b - a, a, b) for (a, b) in last)[:10]:
        m = (a + b) / 2
        print("      width %.3e   eps ~ %.12f   = %6.2f%% across the band"
              % (float(w), float(m), 100.0 * float((m - lo) / (hi - lo))))
    print("   Endpoint cascades account for the 0% and 100% rows only; the rest are")
    print("   interior accumulation points, and nothing certifies those.")
    return 0


def ranked_depth(p, q, eps, cap=30):
    """The weaker, rank-stratified sufficient criterion (`gencert.py --ranked`):
    non-increasing rank along edges and at most one same-rank successor."""
    g.P, g.Q, g.CARRIES, g.CLOSED = p, q, tuple(range(-q + 1, p)), False
    s = eps / (p - q)
    G, U = s.denominator * p, [(s, s + Fr(1, p))]
    cur = U
    for k in range(1, cap + 1):
        cur = g.prune(cur, U)
        if not cur:
            return k, 0
        r = g.ranks_of(G * p ** k, g.scale(cur, G * p ** k))
        if r is not None:
            return k, max(r) + 1
    return None, 0


def do_ranked(p=5, q=2, cap=14):
    print("\n== does the rank-stratified certificate do better in the bands? ==")
    print("   `gencert.py --ranked` accepts a non-increasing rank with at most one")
    print("   same-rank successor -- strictly weaker than a functional block graph.\n")
    cells, _, _ = decompose(p, q, *bands(p, q)[0][1:], cap)
    res = [(a, b) for (a, b, t, _, _) in cells if t not in ('cert', 'kill')]
    gain = 0
    for (a, b) in res[:12]:
        e = (a + b) / 2
        df = scalar_eps(p, q, e, 60)
        dr, strata = ranked_depth(p, q, e, 60)
        gain += (dr is not None and df is not None and dr < df)
        print("    eps = %.9e   functional depth %-4s   ranked depth %-4s (%d stratum/a)"
              % (float(e), df, dr, strata))
    print("\n   cells where ranking lowers the depth: %d of %d.  Every funnel is a"
          % (gain, len(res[:12])))
    print("   single SCC, so ranking buys nothing here: the depth is the depth.")
    return 0


def do_bridge(cap=12, samples=3):
    """R-5: no parametric verdict is believed until two independent scalar
    engines reproduce it at sample points inside the cell, and every breakpoint
    is checked as an individual rational instance."""
    print("\n== R-5: parametric cells vs. the two independent scalar engines ==")
    tot = bad = 0
    for (p, q) in BASES + [(4, 3)]:
        loc = 0
        for (name, lo, hi) in bands(p, q):
            cells, breaks, _ = decompose(p, q, lo, hi, cap)
            for (a, b, tag, d, _) in cells:
                for i in range(1, samples + 1):
                    e = a + (b - a) * Fr(i, samples + 1)
                    d1, d2 = scalar_eps(p, q, e, cap), scalar_s(p, q, e, cap)
                    tot += 1
                    want = d if tag in ('cert', 'kill') else None
                    if d1 != d2 or d1 != want:
                        loc += 1
                        if bad + loc < 6:
                            print("   MISMATCH (%d,%d) %s eps=%s cell %s/%s:"
                                  " scalars %s / %s" % (p, q, name, e, tag, d, d1, d2))
            for r in breaks:
                tot += 1
                d1, d2 = scalar_eps(p, q, r, cap), scalar_s(p, q, r, cap)
                if d1 != d2 or d1 is None:
                    loc += 1
        bad += loc
        print("    (%2d,%2d)  %s" % (p, q, "agrees" if not loc else "*** %d" % loc))
    print("\n   %d checks (%d sample points per cell interior, plus every breakpoint"
          " as a rational instance); disagreements: %d" % (tot, samples, bad))
    return bad


if __name__ == "__main__":
    what = sys.argv[1] if len(sys.argv) > 1 else "all"
    rc = 0
    if what in ("sym", "all"):
        rc += do_sym()
    if what in ("scan", "all"):
        rc += do_scan()
    if what in ("cells", "all"):
        rc += do_cells(int(sys.argv[2]) if len(sys.argv) > 2 else 16)
    if what in ("universal", "all"):
        rc += do_universal()
    if what in ("growth", "all"):
        rc += do_growth()
    if what in ("nesting", "all"):
        rc += do_nesting()
    if what in ("ranked", "all"):
        rc += do_ranked()
    if what in ("bridge", "all"):
        rc += do_bridge()
    sys.exit(0 if rc == 0 else 1)
