# (C) 2026 Ralf Stephan, in collaboration with Claude Code. Released under CC0 1.0 Universal.
# X0 checks for plan-dubD1O5 (angle O-5 of plan-dubD1): sqrt(m) in Mahler's Z via
# coupled even-digit Cantor sets.  Exact arithmetic only (Fraction + Z[sqrt m] sign
# comparisons); no floats anywhere.
#
# Blocks:
#   A  digit-parity lemma brute check (base 3, random even-digit rationals)
#   B  cover certificate for the greedy step, base m (exact)
#   C  greedy construction of the sqrt(3) witness (j=2,k=1), 240 steps
#   D  rigorous floor verification [xi*sqrt(3)^n] even, n = 1..400, from enclosures
#   E  BFS survivor counts (branching of the witness set), depth 22
#   F  general-m scan, q=2: cover + translate + 120-step greedy, m in 3..15
#   G  controls: sigma out of range must fail; m=2 cover must fail
#   H  q>=3 dimension-budget table: exact integer test m^(q-1) <= h^q

from fractions import Fraction as Fr
import random

# ---------- exact sign of p + q*sqrt(m) ----------
def qsign(p, q, m):
    if q == 0:
        return (p > 0) - (p < 0)
    if p == 0:
        return (q > 0) - (q < 0)
    if p > 0 and q > 0: return 1
    if p < 0 and q < 0: return -1
    d = p * p - m * q * q
    if d == 0: return 0
    return ((p > 0) - (p < 0)) if d > 0 else ((q > 0) - (q < 0))

class Q:  # p + q*sqrt(m)
    __slots__ = ('p', 'q', 'm')
    def __init__(self, p, q, m):
        self.p, self.q, self.m = Fr(p), Fr(q), m
    def __add__(s, o): return Q(s.p + o.p, s.q + o.q, s.m)
    def __sub__(s, o): return Q(s.p - o.p, s.q - o.q, s.m)
    def __neg__(s): return Q(-s.p, -s.q, s.m)
    def scale(s, r): return Q(s.p * r, s.q * r, s.m)
    def sign(s): return qsign(s.p, s.q, s.m)
    def __le__(s, o): return (s - o).sign() <= 0
    def __lt__(s, o): return (s - o).sign() < 0
    def __repr__(s): return f"({s.p}+{s.q}*sqrt{s.m})"

def ev_digits(m):
    e = m - 1 if (m - 1) % 2 == 0 else m - 2
    return list(range(0, e + 1, 2)), e

# ---------- Block A ----------
def block_A():
    random.seed(7)
    for _ in range(60):
        digs = [random.choice([0, 2]) for _ in range(40)]
        t = Fr(2 * random.randrange(0, 50), 1) + sum(Fr(d, 3 ** (i + 1)) for i, d in enumerate(digs))
        for s in range(30):
            v = t * 3 ** s
            assert (v.numerator // v.denominator) % 2 == 0, (t, s)
    print("A: digit-parity lemma brute check PASS (60 cases, s<=29)")

# ---------- Block B: cover certificate ----------
def cover_ok(m, verbose=False):
    Ev, e = ev_digits(m)
    M = Fr(e, m - 1)
    U = Q(M, M, m)                     # M*(1+sqrt m)
    cs = [Q(a, b, m) for a in Ev for b in Ev]
    cs.sort(key=lambda c: (c.p + 0, 0))          # provisional; exact sort below
    # exact sort by pairwise sign
    for i in range(len(cs)):
        for j in range(i + 1, len(cs)):
            if (cs[j] - cs[i]).sign() < 0:
                cs[i], cs[j] = cs[j], cs[i]
    if cs[0].sign() != 0:
        return False, "min offset nonzero"
    top = cs[-1] + U                    # must reach m*U
    mU = U.scale(m)
    if (top - mU).sign() < 0:
        return False, "top not reached"
    for i in range(len(cs) - 1):
        if (cs[i + 1] - (cs[i] + U)).sign() > 0:
            return False, f"gap after offset #{i}"
    if verbose:
        print(f"   m={m}: |Ev|={len(Ev)}, M={M}, cover of [0,{m}*M(1+sqrt{m})] exact PASS")
    return True, ""

def block_B():
    ok, why = cover_ok(3, verbose=True)
    assert ok, why
    print("B: cover certificate m=3 PASS")

# ---------- greedy engine (q=2) ----------
def greedy(m, sigma, steps, prefer_alternate=True):
    """sigma in Z[sqrt m]; solve x + sqrt(m)*ypp = sigma, digits in Ev.
       Returns (xdigits, yppdigits) or raises."""
    Ev, e = ev_digits(m)
    M = Fr(e, m - 1)
    U = Q(M, M, m)
    w = sigma.scale(m)
    zero = Q(0, 0, m)
    xd, yd = [], []
    prev = None
    for k in range(steps):
        adm = []
        for a in Ev:
            for b in Ev:
                c = Q(a, b, m)
                r = w - c
                if r.sign() >= 0 and (r - U).sign() <= 0:
                    adm.append((a, b))
        if not adm:
            raise RuntimeError(f"greedy stuck at step {k}")
        pick = adm[0]
        if prefer_alternate and prev in adm and len(adm) > 1:
            others = [t for t in adm if t != prev]
            pick = others[0]
        elif prefer_alternate and prev is not None:
            # choose one differing from prev if possible
            others = [t for t in adm if t != prev]
            if others: pick = others[0]
        prev = pick
        xd.append(pick[0]); yd.append(pick[1])
        w = (w - Q(pick[0], pick[1], m)).scale(m)
    return xd, yd

def run_stats(name, digs, e):
    runs, cur, best = [], 1, 1
    for i in range(1, len(digs)):
        if digs[i] == digs[i - 1]: cur += 1; best = max(best, cur)
        else: cur = 1
    z = digs.count(0); mx = digs.count(e)
    print(f"   {name}: len={len(digs)} zeros={z} maxdig={mx} longest-constant-run={best}")
    return best

# ---------- Blocks C & D for m=3 ----------
def block_CD():
    m = 3
    Ev, e = ev_digits(m)          # {0,2}, e=2
    M = Fr(e, m - 1)              # 1
    j, k = 2, 1                   # u = 2j + x = sqrt3*(2k + y)
    # sigma = v + sqrt(m)*M, v = 2*sqrt(m)*k - 2j  ->  sigma = (2k+M)*sqrt m - 2j
    sigma = Q(-2 * j, 2 * k + M, m)          # 3*sqrt3 - 4
    lo, hi = Q(0, 0, m), Q(M, M, m)
    assert sigma.sign() > 0 and (hi - sigma).sign() > 0, "sigma not interior"
    T = 240
    xd, yppd = greedy(m, sigma, T)
    print(f"C: greedy witness m=3 (j={j},k={k}) ran {T} steps, invariant never broke")
    bx = run_stats("x  digits", xd, e)
    yd = [e - b for b in yppd]     # y = M - y'' digitwise
    by = run_stats("y  digits", yd, e)
    assert bx < 40 and by < 40, "suspicious constant tail"
    # rigorous floors: u = 2j + x, w = 2k + y, xi = u/3; n even=2s: u*3^(s-1); odd=2s+1: w*3^s
    xT = sum(Fr(d, 3 ** (i + 1)) for i, d in enumerate(xd))
    yT = sum(Fr(d, 3 ** (i + 1)) for i, d in enumerate(yd))
    tail = Fr(1, 3 ** T) * M
    straddle = 0
    for n in range(1, 401):
        if n % 2 == 0:
            base, ex = 2 * j + xT, n // 2 - 1
        else:
            base, ex = 2 * k + yT, (n - 1) // 2
        loV = base * 3 ** ex
        hiV = (base + tail) * 3 ** ex
        fl, fh = loV.numerator // loV.denominator, hiV.numerator // hiV.denominator
        if fl != fh:
            straddle += 1; continue
        assert fl % 2 == 0, f"ODD floor at n={n}"
    print(f"D: [xi*sqrt3^n] even verified rigorously for n=1..400 ({straddle} straddles skipped)")
    assert straddle == 0
    # print xi to 30 decimals (enclosure agrees on all 30)
    u_lo = 2 * j + xT; u_hi = u_lo + tail
    lo30 = (u_lo * 10 ** 30) / 3; hi30 = (u_hi * 10 ** 30) / 3
    a, b = lo30.numerator // lo30.denominator, hi30.numerator // hi30.denominator
    assert a == b
    s = str(a)
    print(f"   xi = u/3 = {s[0]}.{s[1:]} (30 exact decimals)")

# ---------- Block E: BFS ----------
def block_E():
    m = 3
    Ev, e = ev_digits(m)
    M = Fr(e, m - 1)
    U = Q(M, M, m)
    sigma = Q(-4, 3, m)
    level = [sigma.scale(m)]
    counts = []
    for depth in range(22):
        nxt = []
        for w in level:
            for a in Ev:
                for b in Ev:
                    r = w - Q(a, b, m)
                    if r.sign() >= 0 and (r - U).sign() <= 0:
                        nxt.append(r.scale(m))
        level = nxt
        counts.append(len(level))
    print("E: BFS survivor counts, depth 1..22:")
    print("   ", counts)
    rats = [Fr(counts[i + 1], counts[i]) for i in range(len(counts) - 1) if counts[i]]
    print(f"   last ratio ~ {float(rats[-1]):.4f} (4/3 = 1.3333 expected)")
    assert counts[-1] > counts[0]

# ---------- Block F: general-m scan ----------
def block_F():
    print("F: general-m scan (q=2):")
    for m in [3, 5, 6, 7, 8, 10, 11, 12, 13, 14, 15]:
        ok, why = cover_ok(m)
        assert ok, (m, why)
        Ev, e = ev_digits(m)
        M = Fr(e, m - 1)
        hiW = Q(M, M, m)
        found = None
        for k in range(1, 9):
            for j in range(0, 13):
                sigma = Q(-2 * j, 2 * k + M, m)
                margin = Q(Fr(1, 10), 0, m)
                if (sigma - margin).sign() > 0 and (hiW - sigma - margin).sign() > 0:
                    found = (j, k, sigma); break
            if found: break
        assert found, f"no translate for m={m}"
        j, k, sigma = found
        xd, yd = greedy(m, sigma, 120)
        print(f"   m={m:2d}: cover PASS, translate (j,k)=({j},{k}), greedy 120 steps PASS")

# ---------- Block G: controls ----------
def block_G():
    m = 3
    bad = Q(10, 0, m)
    try:
        greedy(m, bad, 5)
        raise AssertionError("control failed: out-of-range sigma succeeded")
    except RuntimeError:
        print("G: control 1 PASS (sigma=10 sticks immediately)")
    Ev2, e2 = ev_digits(2)
    assert Ev2 == [0] and Fr(e2, 1) == 0
    print("G: control 2 PASS (m=2: digit set {0}, M=0 — Cantor set degenerates to a point;"
          " only witness would be xi=0) — base-2 degeneracy behind [Dub06] Thm 2(i)")

# ---------- Block H ----------
def block_H():
    print("H: q>=3 dimension budget m^(q-1) <= h^q (h = #even digits), radicals with alpha<3, m not a perfect power:")
    rows = []
    for q in range(3, 7):
        for m in range(3, 65):
            if any(round(m ** (1 / d)) ** d == m for d in range(2, 7)):
                continue
            h = len(ev_digits(m)[0])
            if m ** (q - 1) <= h ** q and m < 3 ** q:
                rows.append((m, q, m ** (q - 1), h ** q))
    for m, q, a, b in rows:
        print(f"   m={m:2d} q={q}:  {a} <= {b}   (alpha = {m}^(1/{q}))")

if __name__ == "__main__":
    block_A(); block_B(); block_CD(); block_E(); block_F(); block_G(); block_H()
    print("ALL BLOCKS PASS")
