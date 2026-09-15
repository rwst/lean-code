#!/usr/bin/env python3
# (C) 2026 Ralf Stephan, in collaboration with Claude Code
# CC0 1.0 Universal (public domain dedication).
"""M4: the *window modelling* tables at alpha = 2 + sqrt 3, in exact Z[sqrt3].

`m4_lean_cert.py` produced the transfer certificate (t0/t1/w0/w1/v/a/b/W) that
`BB61/Pressure.lean` checks.  This script produces the data the *modelling* half needs,
i.e. what `BB61/Window.lean` consumes to prove

    exp (g omega) <= wB (stateOf omega) (coordPartition omega),

namely, for each of the 128 window words u:

  FP[u], FQ[u]   the exact window value  F(u) = FP + FQ sqrt3  (a sum of the seven weights
                 over the set bits of u);
  LL[u]          floor( 8 (F(u) - eps) ),   eps = 123 - 71 sqrt3;
  HH[u]          floor( 8 (F(u) + eps) ).

The Lean file checks four decidable facts per word, with no floor computation of its own:

  (1)  0 <= (8 FP - 984 - LL) + (8 FQ + 568) sqrt3           [8(F-eps) >= LL]
  (2)  0 <  (HH + 1 - 8 FP - 984) + (568 - 8 FQ) sqrt3       [8(F+eps) <  HH+1]
  (3)  LL <= HH <= LL + 1                                    [16 eps < 1]
  (4)  cw[LL mod 8] <= wcert[u]  and  cw[HH mod 8] <= wcert[u]

Together with |x - F(u)| <= eps these give floor(8x) in {LL, HH}, hence
cw[floor(8x) mod 8] <= wcert[u]: the cell weight of the true point is dominated by the
edge weight of its window word.  `wcert = w0 ++ w1` is exactly the table of
`BB61/Pressure.lean`, re-indexed by the word instead of by (state, symbol).

Bit convention (fixed by the transfer operator, which shifts states *down*): bit i of the
word is omega(i-6), so bit 6 -- the newest letter -- is omega(0) = the coordinate the
partition reads, and bits 0..5 are the state.  Position i of `m3_entropy.Window` is i-3,
so the window value approximates F at the point three steps in the past.

`BB61/Window.lean` consumes only LLL, HHL and cwL: it recomputes FP and FQ from the bits of the
word (`winP`, `winQ`), so the FPL/FQL literals below are for cross-checking, not for import.

Writes BB61/Window_data.txt (Lean literals) and cross-checks every entry against
BB61/m4_lean_cert.json.
"""
import json
import os

HERE = os.path.dirname(os.path.abspath(__file__))

# ---- exact Z[sqrt3]: a pair (p, q) means p + q sqrt3 -------------------------------
def mul(x, y):
    return (x[0] * y[0] + 3 * x[1] * y[1], x[0] * y[1] + x[1] * y[0])

def isqrt(n):
    return int(n) ** 0.5 if n < 0 else __import__('math').isqrt(int(n))

def ge0(A, B):
    """exact  A + B sqrt3 >= 0  for integers A, B."""
    if B >= 0:
        return A >= 0 or A * A <= 3 * B * B
    return A >= 0 and A * A >= 3 * B * B

def gt0(A, B):
    """exact  A + B sqrt3 > 0."""
    if B >= 0:
        return A > 0 or A * A < 3 * B * B
    return A > 0 and A * A > 3 * B * B

def ifloor(A, B):
    """floor(A + B sqrt3), exactly."""
    n = int((A + B * 3 ** 0.5) // 1) - 2
    while ge0(A - (n + 1), B):
        n += 1
    return n

# ---- the seven window weights -----------------------------------------------------
N = M = 3
L = N + M
B = 8
EPS = (123, -71)                                   # (2-sqrt3)^3 (3-sqrt3)

rho = (2, -1)
wt = [None] * (L + 1)
p = (1, 0)
for j in range(1, M + 1):                          # (alpha-1) alpha^-j = (1+sqrt3) rho^j
    p = mul(p, rho)
    wt[N + j] = mul((1, 1), p)
p = (1, 0)
for m in range(0, N + 1):                          # -c_m = -(beta-1) beta^m
    wt[N - m] = mul((-1, 1), p)
    p = mul(p, rho)

cert = json.load(open(os.path.join(HERE, 'm4_lean_cert.json')))
assert [list(z) for z in wt] == cert['wt'], (wt, cert['wt'])
assert list(EPS) == cert['eps']
cw = cert['w']
wcert = cert['w0'] + cert['w1']
assert len(wcert) == 128

# ---- per-word tables ---------------------------------------------------------------
FP, FQ, LL, HH = [], [], [], []
for u in range(1 << (L + 1)):
    x = (0, 0)
    for i in range(L + 1):
        if (u >> i) & 1:
            x = (x[0] + wt[i][0], x[1] + wt[i][1])
    FP.append(x[0]); FQ.append(x[1])
    lo = ifloor(B * x[0] - B * EPS[0], B * x[1] - B * EPS[1])
    hi = ifloor(B * x[0] + B * EPS[0], B * x[1] + B * EPS[1])
    LL.append(lo); HH.append(hi)

# ---- the four checks the Lean file will re-run by `decide` -------------------------
for u in range(128):
    assert ge0(8 * FP[u] - 984 - LL[u], 8 * FQ[u] + 568), u
    assert gt0(HH[u] + 1 - 8 * FP[u] - 984, 568 - 8 * FQ[u]), u
    assert LL[u] <= HH[u] <= LL[u] + 1, (u, LL[u], HH[u])
    assert cw[LL[u] % 8] <= wcert[u] and cw[HH[u] % 8] <= wcert[u], u
    # and the tables are exactly the ones m4_lean_cert.py used
    assert LL[u] % 8 == cert['lo'][u] and HH[u] % 8 == cert['hi'][u], u
    assert wcert[u] == max(cw[LL[u] % 8], cw[HH[u] % 8]), u
print('all 128 words: floors, cells, weights and certificate agree with m4_lean_cert.json')
print('LL range %d..%d   HH range %d..%d' % (min(LL), max(LL), min(HH), max(HH)))
print('split words (LL != HH): %d' % sum(1 for u in range(128) if LL[u] != HH[u]))

def lit(xs, per=18):
    out, row = [], []
    for z in xs:
        row.append(str(int(z)))
        if len(row) == per:
            out.append(', '.join(row)); row = []
    if row:
        out.append(', '.join(row))
    return '[' + ',\n   '.join(out) + ']'

with open(os.path.join(HERE, 'Window_data.txt'), 'w') as f:
    f.write('-- generated by BB61/m4_window_tables.py\n')
    f.write('def FPL : List Int := %s\n' % lit(FP))
    f.write('def FQL : List Int := %s\n' % lit(FQ))
    f.write('def LLL : List Int := %s\n' % lit(LL))
    f.write('def HHL : List Int := %s\n' % lit(HH))
    f.write('def cwL : List Nat := %s\n' % lit(cw))
print('wrote BB61/Window_data.txt')
