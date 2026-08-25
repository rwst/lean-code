# (C) 2026 Ralf Stephan, in collaboration with Claude Code. Released under CC0 1.0 Universal.
#
# X1 checks for plan-dubD1O5 (milestone M1).  R-6 SECOND IMPLEMENTATION: shares no code and
# no representation with SZ/checks/dubD1O5-x0-checks.py.
#
#   X0 represents states exactly as pairs in Z[sqrt m] (Fraction + p^2 vs m q^2 sign tests).
#   X1 represents every real as a SCALED-INTEGER ENCLOSURE [lo, hi] over a common denominator
#   10^P, with restart-on-ambiguity: any comparison whose sign the enclosure cannot decide
#   raises Restart, and the driver re-runs the whole block with more digits.  Nothing is ever
#   decided by a float, and nothing is decided by an exact algebraic identity either.
#
# Blocks:
#   A   greedy at m=3, 2000 steps, both preference strategies; run statistics
#   B   cross-check against X0: first 240 digit pairs must agree with the X0 greedy
#   C   rigorous floors [xi*sqrt(3)^n] even, n = 1..1000, from enclosures
#   D   L1 steering audit: consecutive stretches with a=0 unavailable / b=2 unavailable
#   E   L1 constructive strategy: alternate the two steering goals; both digits break runs
#   F   exhaustive m-scan 3..50: cover certificate, translate, 500-step greedy, escape constant
#   G   X3: rational-witness probe, xi = (a + b sqrt3)/c in Q(sqrt3)
#
# Usage: python3 dubD1O5-x1-checks.py

import math

class Restart(Exception):
    pass

# ---------------------------------------------------------------- enclosure layer
class Enc:
    """[lo, hi] / DEN, DEN a class-level power of ten.  All ints, no floats."""
    DEN = 10 ** 60

    __slots__ = ("lo", "hi")

    def __init__(self, lo, hi=None):
        self.lo = lo
        self.hi = lo if hi is None else hi

    @classmethod
    def exact(cls, num, den=1):
        # the rational num/den, rounded outward
        lo = (num * cls.DEN) // den
        hi = -((-num * cls.DEN) // den)
        return cls(lo, hi)

    @classmethod
    def sqrt(cls, m):
        s = math.isqrt(m * cls.DEN * cls.DEN)
        return cls(s, s + 1)

    def __add__(self, o):
        return Enc(self.lo + o.lo, self.hi + o.hi)

    def __sub__(self, o):
        return Enc(self.lo - o.hi, self.hi - o.lo)

    def scale(self, k):           # multiply by a non-negative integer
        return Enc(self.lo * k, self.hi * k)

    def __mul__(self, o):         # both operands assumed non-negative here
        return Enc(self.lo * o.lo // Enc.DEN, -((-self.hi * o.hi) // Enc.DEN))

    def sign(self):
        if self.lo > 0:
            return 1
        if self.hi < 0:
            return -1
        raise Restart                     # straddles zero: enclosure too coarse

    def ge(self, o):
        return (self - o).sign() >= 0

    def le(self, o):
        return (self - o).sign() <= 0

    def dec(self, k):
        """k exact decimals, only if the enclosure pins them."""
        a = self.lo * 10 ** k // Enc.DEN
        b = self.hi * 10 ** k // Enc.DEN
        if a != b:
            raise Restart
        return a

    def floor_exact(self):
        a, b = self.lo // Enc.DEN, self.hi // Enc.DEN
        if a != b:
            raise Restart
        return a

def with_precision(fn, *args, start=200, cap=40000):
    """Run fn at increasing precision until it completes without a Restart."""
    P = start
    while P <= cap:
        Enc.DEN = 10 ** P
        try:
            return fn(*args)
        except Restart:
            P *= 2
    raise RuntimeError("precision cap exceeded")

# ---------------------------------------------------------------- the model
def even_digits(m):
    e = m - 1 if m % 2 else m - 2
    return list(range(0, e + 1, 2)), e

def model(m):
    """Constants of the cover game at base m, as enclosures."""
    Ev, e = even_digits(m)
    rt = Enc.sqrt(m)
    M = Enc.exact(e, m - 1)
    U = M + M * rt                        # M*(1 + sqrt m)
    offs = []                             # (a, b, a + b*sqrt m)
    for a in Ev:
        for b in Ev:
            offs.append((a, b, Enc.exact(a) + rt.scale(b)))
    return Ev, e, rt, M, U, offs

def admissible(w, U, offs):
    """digit pairs (a,b) with 0 <= w - (a + b sqrt m) <= U"""
    out = []
    for (a, b, c) in offs:
        r = w - c
        if r.sign() >= 0 and r.le(U):
            out.append((a, b, c))
    return out

def start_state(m, j=None, k=1):
    """w_0 = m*sigma, sigma = (2k + M) sqrt m - 2j, with 2j chosen so 0 < sigma < U.

    The window (S - U, S) with S = (2k+M) sqrt m has length U > 2, so an even integer 2j
    always lies in it (this is the translate pigeonhole of plan 1.2)."""
    Ev, e, rt, M, U, offs = model(m)
    S = rt.scale(2 * k) + M * rt
    if j is None:
        # smallest even 2j with sigma = S - 2j < U, then check sigma > 0
        j = 0
        while True:
            sigma = S - Enc.exact(2 * j)
            if (U - sigma).sign() > 0:
                break
            j += 1
            if j > 4 * m + 8:
                raise RuntimeError("no translate found")
    sigma = S - Enc.exact(2 * j)
    if sigma.sign() <= 0 or (U - sigma).sign() <= 0:
        raise RuntimeError("sigma not interior")
    return sigma.scale(m), (Ev, e, rt, M, U, offs), sigma

def greedy(m, steps, rule, j=None, k=1):
    """rule(cands, prev, state) -> chosen candidate.  Returns (a-digits, b-digits)."""
    w, (Ev, e, rt, M, U, offs), sigma = start_state(m, j, k)
    if sigma.sign() <= 0 or not (U - sigma).sign() > 0:
        raise RuntimeError("sigma not interior")
    A, B, prev = [], [], None
    for _ in range(steps):
        cands = admissible(w, U, offs)
        if not cands:
            raise RuntimeError("greedy stuck")
        pick = rule(cands, prev, w)
        prev = (pick[0], pick[1])
        A.append(pick[0]); B.append(pick[1])
        w = (w - pick[2]).scale(m)
    return A, B

def rule_first(cands, prev, w):
    return cands[0]

def rule_prefer_a0(cands, prev, w):
    for c in cands:
        if c[0] == 0:
            return c
    return cands[0]

def rule_alternate(cands, prev, w):
    if prev is not None and len(cands) > 1:
        for c in cands:
            if (c[0], c[1]) != prev:
                return c
    return cands[0]

def runs(seq):
    best = cur = 1
    for i in range(1, len(seq)):
        cur = cur + 1 if seq[i] == seq[i - 1] else 1
        best = max(best, cur)
    return best

def tail_run(seq, val):
    n = 0
    for x in reversed(seq):
        if x != val:
            break
        n += 1
    return n

# ---------------------------------------------------------------- blocks
def block_A():
    out = {}
    for name, rule in (("first", rule_first), ("prefer-a0", rule_prefer_a0),
                       ("alternate", rule_alternate)):
        A, B = greedy(3, 2000, rule)
        Y = [2 - b for b in B]
        out[name] = (runs(A), runs(Y), tail_run(A, 2), tail_run(Y, 2),
                     A.count(0), B.count(0))
    return out

def block_B(x0_digits):
    A, B = greedy(3, 240, rule_alternate)
    xa, xb = x0_digits
    return (A[:240] == xa[:240], B[:240] == xb[:240])

def block_C(N=1000):
    T = 3000
    A, B = greedy(3, T, rule_alternate)
    Y = [2 - b for b in B]
    x = Enc(0); y = Enc(0)
    p = 1
    for i in range(T):
        p *= 3
        x = x + Enc.exact(A[i], p)
        y = y + Enc.exact(Y[i], p)
    tail = Enc.exact(1, 3 ** T)
    xhi = x + tail
    yhi = y + tail
    j, k = 2, 1
    odd_seen = 0
    for n in range(1, N + 1):
        if n % 2 == 0:
            lo, hi, ex = x, xhi, n // 2 - 1
            base = 2 * j
        else:
            lo, hi, ex = y, yhi, (n - 1) // 2
            base = 2 * k
        pw = 3 ** ex
        v = Enc((lo.lo + Enc.exact(base).lo) * pw, (hi.hi + Enc.exact(base).hi) * pw)
        f = v.floor_exact()
        if f % 2:
            odd_seen += 1
    u = Enc(x.lo + Enc.exact(4).lo, xhi.hi + Enc.exact(4).hi)
    xi = Enc(u.lo // 3, -((-u.hi) // 3))
    return odd_seen, xi.dec(30)

def block_D():
    """L1 steering audit on the 2000-step orbit: how long can a=0 or b=2 be unavailable?"""
    m = 3
    w, (Ev, e, rt, M, U, offs), sigma = start_state(m)
    twort = rt.scale(2)
    no_a0 = no_b2 = 0
    max_a0 = max_b2 = 0
    inL = 0
    for _ in range(2000):
        cands = admissible(w, U, offs)
        has_a0 = any(c[0] == 0 for c in cands)
        has_b2 = any(c[1] >= 2 for c in cands)
        no_a0 = 0 if has_a0 else no_a0 + 1
        no_b2 = 0 if has_b2 else no_b2 + 1
        max_a0 = max(max_a0, no_a0); max_b2 = max(max_b2, no_b2)
        if not has_b2:
            inL += 1
            # theory: b=2 unavailable  <=>  w < 2 sqrt m
            if not (twort - w).sign() > 0:
                raise RuntimeError("L characterisation violated")
        pick = rule_alternate(cands, None, w)
        w = (w - pick[2]).scale(m)
    return max_a0, max_b2, inL

def block_E():
    """The L1 strategy of the proof: alternate the two steering goals explicitly."""
    m = 3
    w, (Ev, e, rt, M, U, offs), sigma = start_state(m)
    A, B, goal = [], [], "b2"
    for _ in range(2000):
        cands = admissible(w, U, offs)
        pick = None
        if goal == "b2":
            for c in cands:
                if c[1] >= 2:
                    pick = c; goal = "a0"; break
        else:
            for c in cands:
                if c[0] == 0:
                    pick = c; goal = "b2"; break
        if pick is None:                       # goal unreachable this step: steer
            pick = cands[-1] if goal == "b2" else cands[0]
        A.append(pick[0]); B.append(pick[1])
        w = (w - pick[2]).scale(m)
    Y = [2 - b for b in B]
    return runs(A), runs(Y), A.count(0), B.count(2)

def block_F(mmax=50):
    bad, rows = [], []
    for m in range(3, mmax + 1):
        if math.isqrt(m) ** 2 == m:
            # perfect square: sqrt m is an integer >= 2, in Z trivially (xi = 2), and the
            # enclosure layer cannot decide the exact equality U = 2 that occurs at m = 4.
            continue
        Ev, e, rt, M, U, offs = model(m)
        # cover certificate: the three gap inequalities, as enclosures
        two = Enc.exact(2)
        ok = (U - two).sign() >= 0                       # consecutive-a gap
        ok &= (U - (rt.scale(2) - Enc.exact(e))).sign() >= 0   # run-to-run gap
        # exact top equality e(1+sqrt m) + U = m U.  An enclosure can never certify an
        # equality, so this one is checked as the integer identity it is:
        #   e + M = e + e/(m-1) = m e/(m-1) = m M,  hence (e+M)(1+sqrt m) = m U.
        ok &= (e * (m - 1) + e) * 1 == m * e
        # translate: feasibility window longer than the lattice spacing 2
        window = U
        ok2 = (window - two).sign() > 0
        # escape constant of the L1 lemma: is U - 2 >= 2/sqrt m ?
        one_step = ((U - two) * rt - two).sign() >= 0
        try:
            A, Bd = greedy(m, 500, rule_alternate)
            ran = 500
        except RuntimeError:
            ran = 0
        if not (ok and ok2 and ran == 500):
            bad.append(m)
        rows.append((m, ok, ok2, ran, one_step))
    return bad, rows

def floor_quad(A, B, c, m=3):
    """exact floor of (A + B*sqrt m)/c, c > 0, all integers."""
    S = 10 ** 30
    approx = (A * S + B * math.isqrt(m * S * S)) // (c * S)
    n = approx - 3
    while True:
        # test  (n+1)*c <= A + B*sqrt m   i.e.   D := (n+1)*c - A <= B*sqrt m
        D = (n + 1) * c - A
        if B >= 0:
            ok = D <= 0 or D * D <= m * B * B
        else:
            ok = D < 0 and D * D >= m * B * B
        if not ok:
            return n
        n += 1

def block_G(cmax=200, nmax=60):
    """X3: does any xi = (a + b sqrt3)/c in Q(sqrt3) witness sqrt3 in Z?

    Exact integer arithmetic (this block is an experiment, not a re-verification of X0).
    xi*sqrt3^n = (A_n + B_n sqrt3)/c with (A,B) -> (3B, A) at each step."""
    best = (0, None)
    hist = {}
    for c in range(1, cmax + 1):
        for a in range(-6 * c, 6 * c + 1):
            for b in range(-6 * c, 6 * c + 1):
                if a == 0 and b == 0:
                    continue
                if math.gcd(math.gcd(abs(a), abs(b)), c) != 1:
                    continue
                A, B = a, b
                good = 0
                for n in range(1, nmax + 1):
                    A, B = 3 * B, A                  # multiply by sqrt3
                    if floor_quad(A, B, c) % 2:
                        break
                    good = n
                hist[good] = hist.get(good, 0) + 1
                if good > best[0]:
                    best = (good, (a, b, c))
    return best, hist

# ---------------------------------------------------------------- driver
def main():
    print("X1 checks for plan-dubD1O5 (M1).  Scaled-integer enclosures, restart-on-ambiguity.")
    print()

    res = with_precision(block_A, start=1400, cap=200000)
    print("A  greedy m=3, 2000 steps, three preference rules")
    for name, (ra, ry, ta, ty, a0, b0) in res.items():
        print(f"     {name:10s} longest x-run={ra:3d}  longest y-run={ry:3d}  "
              f"tail(2) x={ta} y={ty}   #a=0:{a0}  #b=0:{b0}")
    print()

    print("D  L1 steering audit (2000 steps)")
    ma, mb, inL = with_precision(block_D, start=1400, cap=200000)
    print(f"     longest stretch with a=0 unavailable (theory: bounded, region F1) : {ma}")
    print(f"     longest stretch with b=2 unavailable (theory: bounded, region L)  : {mb}")
    print(f"     steps spent in L = [0, 2 sqrt 3)                                  : {inL}/2000")
    print()

    print("E  L1 constructive strategy (alternate the two steering goals)")
    ra, ry, na0, nb2 = with_precision(block_E, start=1400, cap=200000)
    print(f"     longest x-run={ra}  longest y-run={ry}   #a=0:{na0}  #b=2:{nb2}")
    print()

    print("C  rigorous floors from enclosures")
    odd, d30 = with_precision(block_C, start=2200, cap=200000)
    s = str(d30)
    print(f"     odd floors found in n=1..1000 : {odd}")
    print(f"     xi = {s[0]}.{s[1:]}  (30 exact decimals)")
    print()

    print("F  exhaustive m-scan 3..50")
    bad, rows = with_precision(block_F, start=400, cap=100000)
    print(f"     failures: {bad if bad else 'none'}")
    print(f"     non-squares scanned: {len(rows)} (m=3..50); perfect squares skipped (trivial)")
    print(f"     one-step L-escape (U-2 >= 2/sqrt m) FAILS only for m in "
          f"{[m for (m,o1,o2,r,one) in rows if not one]}")
    print()

    print("G  X3 rational-witness probe  xi=(a+b sqrt3)/c,  c<=40, |a|,|b|<=6c, n<=60 (exact)")
    (best, hist) = block_G(40, 60)
    print(f"     longest all-even prefix: n={best[0]}  at (a,b,c)={best[1]}")
    print(f"     prefix-length histogram (length: count): "
          f"{dict(sorted((k, v) for k, v in hist.items() if k >= 3))}")

if __name__ == "__main__":
    main()
