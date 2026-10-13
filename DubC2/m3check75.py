#!/usr/bin/env python3
# (C) 2026 Ralf Stephan, in collaboration with Claude Code.  CC0 1.0.
#
# m3check75.py -- independent cross-check of DubC2/Calibration75.lean and
# DubC2/SevenFifthsCore.lean, i.e. of [DN05] Theorem 4(iii):
#
#     for every real xi != 0, infinitely many of  [xi (7/5)^n + 1/2]
#     are divisible by 2, 3, 5 or 11.
#
# Nothing here imports from the repository: the orbit is recomputed from the
# definition  x_n = floor(xi (7/5)^n + 1/2)  in exact `fractions.Fraction`,
# and every interval constant, branch table, block bound, residue transition
# and peel step claimed in the Lean files is re-derived from scratch and
# compared.  Stdlib only.
#
#   python3 DubC2/m3check75.py

from fractions import Fraction as F
import random

P, Q = 7, 5
NU = F(1, 2)
FAIL = []

def chk(cond, msg):
    if not cond:
        FAIL.append(msg)

# ---------------------------------------------------------------- the model --

def orbit(xi, steps):
    """(x_n, y_n, s_n) for n < steps, straight from the definition."""
    xs, ys = [], []
    for n in range(steps + 1):
        z = xi * F(P, Q) ** n + NU
        x = z.numerator // z.denominator          # floor
        xs.append(x)
        ys.append(z - x)
    ss = [Q * xs[n + 1] - P * xs[n] for n in range(steps)]
    return xs, ys, ss

# ------------------------------------------------------- 1. alphabet + gap ---

def check_orbits(trials=4000, steps=60):
    seen_letters, runs = set(), []
    for _ in range(trials):
        xi = F(random.randint(-200000, 200000), random.randint(1, 99991))
        if xi == 0:
            continue
        xs, ys, ss = orbit(xi, steps)
        run = 0
        for n in range(steps):
            # the carry identity  s = 7 y_n - 5 y_{n+1} - 1
            chk(F(ss[n]) == 7 * ys[n] - 5 * ys[n + 1] - 1, f"carry identity n={n}")
            chk(-5 <= ss[n] <= 5, f"alphabet bound s={ss[n]}")
            av  = all(xs[n] % p for p in (2, 3, 5, 11))
            av1 = all(xs[n + 1] % p for p in (2, 3, 5, 11))
            if av and av1:
                seen_letters.add(ss[n])
                chk(ss[n] in (-4, -2, 2, 4), f"letter {ss[n]} survives {{2,5}}")
                # mod 3 selects the pair
                if ss[n] in (-4, 2):
                    chk(xs[n] % 3 == 2, "s in {-4,2} but x != 2 mod 3")
                else:
                    chk(xs[n] % 3 == 1, "s in {-2,4} but x != 1 mod 3")
                # letter <-> window
                chk((ss[n] == -4) == (xs[n] % 3 == 2 and ys[n] < F(2, 7)), "window A")
                chk((ss[n] == 2)  == (xs[n] % 3 == 2 and ys[n] >= F(3, 7)), "window C")
                chk((ss[n] == -2) == (xs[n] % 3 == 1 and ys[n] < F(4, 7)), "window B")
                chk((ss[n] == 4)  == (xs[n] % 3 == 1 and ys[n] >= F(5, 7)), "window D")
                # the forbidden gap, in the A,C orientation
                if xs[n] % 3 == 2:
                    chk(not (F(2, 7) <= ys[n] < F(3, 7)), "y in the gap [2/7,3/7)")
                else:
                    chk(not (F(4, 7) <= ys[n] < F(5, 7)), "y in the mirror gap")
                run += 1
            else:
                runs.append(run); run = 0
        runs.append(run)
    return seen_letters, max(runs)

# --------------------------------------------- 2. the interval constants -----

# the four branch maps, as (num_mul, num_add, den) acting on y
A = lambda y: (7 * y + 3) / 5
C = lambda y: (7 * y - 3) / 5

def check_intervals():
    two7, three7 = F(2, 7), F(3, 7)
    # C^4 is impossible on [0,1]
    y = F(1)
    for _ in range(4):
        y = C(y)
    chk(y < 0, "C^4 not impossible")
    chk(y == (2401 * F(1) - 2664) / 625, "C^4 closed form")
    # composite block maps
    for t, closed in ((F(1, 3), None),):
        pass
    blk1 = lambda t: (49 * t + 6) / 25          # A C
    blk2 = lambda t: (343 * t - 33) / 125       # A C C
    blk3 = lambda t: (2401 * t - 606) / 625     # A C C C
    for t in (F(0), F(1, 100), F(1, 7), F(2, 7)):
        chk(blk1(t) == C(A(t)), "AC closed form")
        chk(blk2(t) == C(C(A(t))), "ACC closed form")
        chk(blk3(t) == C(C(C(A(t)))), "ACCC closed form")
    # window thresholds solved for t
    chk(blk1(F(8, 343)) == two7, "blk1 t<=8/343  <-> y<=2/7")
    chk(blk1(F(33, 343)) == three7, "blk1 t>=33/343 <-> y>=3/7")
    chk(blk2(F(481, 2401)) == two7, "blk2 t<=481/2401 <-> y<=2/7")
    chk(blk2(F(606, 2401)) == three7, "blk2 t>=606/2401 <-> y>=3/7")
    # the 3-block image
    chk(blk3(F(606, 2401)) == 0, "blk3 lower end")
    chk(blk3(two7) == F(16, 125), "blk3 upper end = 16/125")
    # 16/125 sits strictly inside the block-2 exit window: block 3 cannot recur
    chk(F(16, 125) < F(481, 2401), "16/125 < 481/2401 (block 2 always ends)")
    chk(F(16, 125) < F(606, 2401), "16/125 < 606/2401 (AC^3 cannot follow AC^3)")
    chk(F(16, 125) <= two7, "16/125 <= 2/7 (n+4 is an A position)")
    # after AC^3 AC^2
    chk(blk2(F(16, 125)) == F(1363, 15625), "blk2(16/125) = 1363/15625")
    chk(F(1363, 15625) < F(33, 343), "1363/15625 < 33/343 (only AC can follow)")
    # after a block AC the value is >= 6/25, which forces a 3-position
    chk(blk1(F(0)) == F(6, 25), "blk1(0) = 6/25")
    chk(F(6, 25) > F(8, 343), "6/25 > 8/343")
    chk(F(6, 25) > F(481, 2401), "6/25 > 481/2401  (the look-ahead)")
    chk(F(6, 25) < F(606, 2401), "6/25 < 606/2401  (look-ahead is needed)")
    chk(blk1(F(8, 343)) == two7, "blk1(8/343) = 2/7")
    # the ACC fixed point, i.e. the (ACC)^oo orbit the no-3-position case gives
    chk(blk2(F(33, 218)) == F(33, 218), "ACC fixed point 33/218")
    chk(F(33, 343) <= F(33, 218) <= F(481, 2401), "33/218 in the block-2 window")

# ------------------------------------------------- 3. the x-chain mod 11 -----

def check_xchain():
    # 5^k x_{n+k} = 7^k x_n - c_k  along  A C C C A C  and  A C C C A C C A C
    for word, cs in (("ACCCAC", [4, 18, 76, 282, 4474, 25068]),
                     ("ACCCACCAC", [4, 18, 76, 282, 4474, 25068, 144226, 1322082, 8473324])):
        c = 0
        for k, ltr in enumerate(word):
            # 5 x' = 7 x + s  =>  5^{k+1} x_{k+1} = 7^{k+1} x_0 - (7 c - 5^k s)
            s = -4 if ltr == "A" else 2
            c = 7 * c - 5 ** k * s
            chk(c == cs[k], f"x-chain {word} step {k}: {c} != {cs[k]}")
    # residues:  x_{n+k} = a_k x_n + b_k  (mod 11)
    inv5 = pow(5, -1, 11)
    tbl, dead = {}, {}
    c = 0
    for k, ltr in enumerate("ACCCACCAC"):
        s = -4 if ltr == "A" else 2
        c = 7 * c - 5 ** k * s
        num, den = pow(7, k + 1, 11), pow(5, k + 1, 11)
        a = num * pow(den, -1, 11) % 11
        b = (-c) * pow(den, -1, 11) % 11
        tbl[k + 1] = (a, b)
        dead[k + 1] = [r for r in range(11) if (a * r + b) % 11 == 0]
    expect = {1: (8, 8), 2: (9, 5), 3: (6, 3), 4: (4, 9), 5: (10, 3),
              6: (3, 9), 7: (2, 2), 8: (5, 2), 9: (7, 1)}
    chk(tbl == expect, f"residue table {tbl} != {expect}")
    expect_dead = {1: [10], 2: [8], 3: [5], 4: [6], 5: [3],
                   6: [8], 7: [10], 8: [4], 9: [3]}
    chk({k: v for k, v in dead.items()} == expect_dead,
        f"death table {dead} != {expect_dead}")
    return tbl

# ---------------------------------------------- 4. the peel, exhaustively ----

def check_peel(tbl):
    """Every infinite (block, residue mod 11) path is V^oo at r=1 or U^oo at r=9."""
    aV, bV = tbl[6]        # r -> 3r+9
    aU, bU = tbl[9]        # r -> 7r+1
    deadV = [3, 5, 6, 8, 10]          # some intermediate of A C C C A C hits 0
    deadU = [3, 4, 5, 6, 8, 10]       # ... of A C C C A C C A C
    succ = {}
    for r in range(1, 11):
        out = []
        if r not in deadV:
            out.append((aV * r + bV) % 11)
        if r not in deadU:
            out.append((aU * r + bU) % 11)
        succ[r] = out
    # peel to the set of residues with an infinite forward path
    live = set(range(1, 11))
    while True:
        nxt = {r for r in live if any(t in live for t in succ[r])}
        if nxt == live:
            break
        live = nxt
    chk(live == {1, 9}, f"peel: live = {sorted(live)} != [1, 9]")
    chk(succ[1] == [1, 8] and 8 not in live, "r=1 must take V")
    chk(succ[9] == [3, 9] and 3 not in live, "r=9 must take U")
    # depth of the peel, i.e. how far the Lean chain has to look
    depth = {}
    for r in range(1, 11):
        d, front = 0, {r}
        while front and d < 6:
            front = {t for x in front if x not in (1, 9) for t in succ[x]}
            d += 1
            if not front:
                break
        depth[r] = d
    return succ, depth

# -------------------------------------------------------------- 5. mirror ----

def check_mirror():
    """B,D at y  is  A,C at yhat = 1-y, xhat = -x, shat = -s."""
    B = lambda y: (7 * y + 1) / 5
    D = lambda y: (7 * y - 5) / 5
    for y in (F(0), F(1, 3), F(1, 2), F(5, 7), F(9, 10), F(99, 100)):
        if y < F(4, 7):
            chk(1 - B(y) == C(1 - y), f"mirror B<->C at {y}")
        if y >= F(5, 7):
            chk(1 - D(y) == A(1 - y), f"mirror D<->A at {y}")
    # windows
    chk(1 - F(4, 7) == F(3, 7) and 1 - F(5, 7) == F(2, 7), "mirror windows")

# ------------------------------------------------------------------- main ----

if __name__ == "__main__":
    random.seed(20260819)
    check_intervals()
    tbl = check_xchain()
    succ, depth = check_peel(tbl)
    check_mirror()
    letters, longest = check_orbits()
    print(f"letters seen on avoiding pairs : {sorted(letters)}")
    print(f"longest avoiding run           : {longest}")
    print(f"residue map at 3-positions      : V r->3r+9, U r->7r+1")
    print(f"successors                      : "
          + ", ".join(f"{r}->{succ[r]}" for r in range(1, 11)))
    print(f"peel depth per residue          : "
          + ", ".join(f"{r}:{depth[r]}" for r in range(1, 11)))
    print(f"violations                      : {len(FAIL)}")
    for m in FAIL[:20]:
        print("   !", m)
