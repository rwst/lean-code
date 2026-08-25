# (C) 2026 Ralf Stephan, in collaboration with Claude Code. Released under CC0 1.0 Universal.
#
# X2 for plan-dubD1O5 (milestone M1): the q >= 3 frontier.
#
# For alpha = m^(1/q) the reduction of plan 1.2 becomes (q-1)-dimensional.  With
# t_r := xi * alpha^r = 2 j_r + x_r  (r = 0..q-1, x_r in K_m) the constraints t_{r+1} = alpha t_r
# give q-1 linear equations
#
#       x_{r+1} - alpha x_r = v_r := 2 alpha j_r - 2 j_{r+1},      r = 0..q-2,
#
# and the greedy carries a residual vector rho in the box  B = prod_r [-alpha M, M].
# One step appends a digit tuple (a_0,..,a_{q-1}) in Ev_m^q and needs
#
#       m*rho - off  in  B,        off_r = a_{r+1} - alpha a_r.
#
# So the game is feasible iff the ceil(m/2)^q translates  off + B  cover  m*B.
# Volume budget:  ceil(m/2)^q >= m^(q-1)   (plan T3).
#
# This script:
#   H1  the exact integer budget table
#   H2  covering slack: for a large deterministic grid over m*B, is some offset admissible?
#       (a grid probe can refute a cover; it cannot prove one -- reported as such)
#   H3  the q-dim greedy itself, run from valid translates, many steps
#
# Arithmetic: scaled-integer enclosures with restart-on-ambiguity (no floats anywhere).

import math

class Restart(Exception):
    pass

DEN = 10 ** 80

def root(m, q):
    """enclosure [lo,hi] of m^(1/q) scaled by DEN, as integers"""
    lo = 0
    hi = m * DEN
    while lo + 1 < hi:                      # integer bisection on x^q vs m*DEN^q
        mid = (lo + hi) // 2
        if mid ** q <= m * DEN ** q:
            lo = mid
        else:
            hi = mid
    return lo, lo + 1

class E:
    __slots__ = ("lo", "hi")
    def __init__(self, lo, hi=None):
        self.lo = lo; self.hi = lo if hi is None else hi
    @staticmethod
    def num(n, d=1):
        return E((n * DEN) // d, -((-n * DEN) // d))
    def __add__(s, o): return E(s.lo + o.lo, s.hi + o.hi)
    def __sub__(s, o): return E(s.lo - o.hi, s.hi - o.lo)
    def k(s, c):
        return E(s.lo * c, s.hi * c) if c >= 0 else E(s.hi * c, s.lo * c)
    def sgn(s):
        if s.lo > 0: return 1
        if s.hi < 0: return -1
        raise Restart

def budget_table(qmax=6, mmax=60):
    rows = []
    for q in range(2, qmax + 1):
        for m in range(3, mmax + 1):
            if round(m ** (1.0 / q)) ** q == m:
                continue                                   # perfect q-th power: trivial
            h = (m + 1) // 2
            ok = h ** q >= m ** (q - 1)
            if ok and q >= 3:
                rows.append((m, q, h ** q, m ** (q - 1), m ** (1.0 / q)))
    return rows

def offsets(m, q, al):
    """all digit tuples and their offset vectors, as enclosures"""
    Ev = list(range(0, (m - 1 if m % 2 else m - 2) + 1, 2))
    out = []
    def rec(pref):
        if len(pref) == q:
            off = [E.num(pref[r + 1]) - al.k(pref[r]) for r in range(q - 1)]
            out.append((tuple(pref), off))
            return
        for a in Ev:
            rec(pref + [a])
    rec([])
    return Ev, out

def box(m, q, al, M):
    """B = prod [-alpha M, M]; returns (lowvec, highvec) as enclosures"""
    lo = E(0, 0) - al.k(1)                      # placeholder, replaced below
    return None

def _setup(m, q):
    al = E(*root(m, q))
    e = m - 1 if m % 2 else m - 2
    M = E.num(e, m - 1)
    Ev, offs = offsets(m, q, al)
    return al, M, Ev, offs

def in_Z(sig, al, M, q):
    """Is sig in the residual zonotope Z = {(tau_1 - al tau_0, ..., ) : tau_i in [0,M]}?

    tau_{r+1} = sig_r + al*tau_r, so forward-propagate the interval of reachable tau
    intersected with [0,M].  Nonempty at the end  <=>  sig in Z."""
    lo, hi = E(0, 0), M
    for r in range(q - 1):
        # al*[lo,hi] + sig_r, then clip to [0,M]
        nlo = E(al.lo * lo.lo // DEN, -((-al.hi * lo.hi) // DEN)) + sig[r]
        nhi = E(al.lo * hi.lo // DEN, -((-al.hi * hi.hi) // DEN)) + sig[r]
        lo = nlo if (nlo).sgn() >= 0 else E(0, 0)
        hi = nhi if (M - nhi).sgn() >= 0 else M
        if (hi - lo).sgn() < 0:
            return False
    return True

def grid_probe(m, q, steps_per_axis=40):
    """Deterministic grid over the bounding box; among points of m*Z, count uncovered.

    Correct region: the residuals live in the ZONOTOPE Z, not in the product box
    prod[-alpha M, M].  For q = 2 the two coincide; for q >= 3 the zonotope is strictly
    smaller, and it is the zonotope that must be covered."""
    al, M, Ev, offs = _setup(m, q)
    aM = E(al.lo * M.lo // DEN, -((-al.hi * M.hi) // DEN))
    blo = E(0, 0) - aM
    bhi = M
    mlo = blo.k(m); mhi = bhi.k(m)
    bad = tested = 0
    def covered(pt):
        for (_, off) in offs:
            try:
                if in_Z([pt[r] - off[r] for r in range(q - 1)], al, M, q):
                    return True
            except Restart:
                continue
        return False
    def rec(r, pt):
        nonlocal bad, tested
        if r == q - 1:
            try:
                # only points of m*Z matter: sig/m in Z
                if not in_Z([E(p.lo // m, -((-p.hi) // m)) for p in pt], al, M, q):
                    return
            except Restart:
                return
            tested += 1
            if not covered(pt):
                bad += 1
            return
        for i in range(steps_per_axis + 1):
            rec(r + 1, pt + [E(mlo.lo + (mhi.hi - mlo.lo) * i // steps_per_axis)])
    rec(0, [])
    return bad, tested

def greedy_q(m, q, nsteps=400, jvec=None):
    """Run the (q-1)-dimensional greedy on the zonotope; returns steps completed."""
    al, M, Ev, offs = _setup(m, q)
    best = None
    for cand in _vectors(q, 4):
        if all(c == 0 for c in cand):
            continue                      # xi = 0 is the degenerate solution, excluded
        sig = [al.k(2 * cand[r]) - E.num(2 * cand[r + 1]) for r in range(q - 1)]
        try:
            if in_Z(sig, al, M, q):
                best = (cand, sig); break
        except Restart:
            continue
    if best is None:
        return 0, None
    cand, sig = best
    for step in range(nsteps):
        target = [x.k(m) for x in sig]
        nxt = None
        for (_, off) in offs:
            cand_sig = [target[r] - off[r] for r in range(q - 1)]
            try:
                if in_Z(cand_sig, al, M, q):
                    nxt = cand_sig; break
            except Restart:
                continue
        if nxt is None:
            return step, cand
        sig = nxt
    return nsteps, cand

def _vectors(q, R):
    if q == 1:
        for a in range(0, R + 1):
            yield (a,)
        return
    for head in range(0, R + 1):
        for rest in _vectors(q - 1, R):
            yield (head,) + rest

def main():
    print("X2: the q >= 3 frontier for plan-dubD1O5 (M1).  Enclosures, no floats.")
    print()
    print("H1  dimension budget  ceil(m/2)^q >= m^(q-1)  (exact integers), alpha < 2 first")
    rows = budget_table(6, 60)
    sub2 = sorted([r for r in rows if r[4] < 2.0], key=lambda r: r[4])
    print(f"     candidates with alpha < 2 (m, q, budget, need, alpha):")
    for (m, q, b, n, a) in sub2[:12]:
        print(f"       m={m:3d} q={q}  {b:12d} >= {n:12d}   alpha={a:.6f}")
    print(f"     smallest such alpha: m={sub2[0][0]} q={sub2[0][1]}  alpha={sub2[0][4]:.6f}")
    print(f"     3^(1/3): budget {2**3} vs need {3**2}  ->  FAILS (the boundary heir)")
    print()

    print("H2  grid probe of the covering condition (refutation-only)")
    print("     CONTROL, q=2 (where the Cover Lemma is proved): expect 0 failures")
    for (m, q, g) in ((3, 2, 4000), (5, 2, 4000), (6, 2, 4000)):
        bad, tot = grid_probe(m, q, g)
        print(f"       m={m} q={q}: grid {tot:7d} points, uncovered {bad}")
    print("     the q>=3 candidates:")
    for (m, q, g) in ((5, 3, 60), (7, 3, 60), (13, 4, 14)):
        bad, tot = grid_probe(m, q, g)
        print(f"       m={m} q={q}: grid {tot:7d} points, uncovered {bad}"
              f"  ({100.0*bad/tot:.1f}% of the box)")
    print()

    print("H3  the (q-1)-dimensional greedy, run from a valid translate")
    for (m, q, n) in ((5, 3, 400), (7, 3, 400), (13, 4, 150)):
        got, cand = greedy_q(m, q, n)
        print(f"     m={m} q={q}: completed {got}/{n} steps"
              f"{'' if cand is None else f'  (j={cand})'}")

if __name__ == "__main__":
    main()
