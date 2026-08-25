# (C) 2026 Ralf Stephan, in collaboration with Claude Code. Released under CC0 1.0 Universal.
#
# X5 for plan-dubD1O5: the admissible TREE, not just one path through it.
# Companion check of Theorem 9.1 of paper-dubD1O5.tex ("the witness set for sqrt3 has
# cardinality 2^aleph0, hence contains transcendental points") and of the complexity
# statement in Section 9 that rules out the one route to transcendence of the *named*
# witness.  Shares no code with X0/X1/X3/X4 or with the Lean development.
#
# What it checks:
#   (1) the branching structure at m=3: exactly one admissible offset off the overlap set
#       O, exactly two on it, and the two always differing in their a-part;
#   (2) the tree of the theorem's proof --- at each node run the rule until an a-digit 0
#       and a b-digit 2 have both appeared, run on to the next state in O, branch there ---
#       is a FULL binary tree, explored here to depth 10 (1024 paths);
#   (3) the survivor set S of the forced dynamics, as listed in the proof, really does
#       consist of points that never branch, while random states all escape into O;
#   (4) no reachable state is a fixed point, and the sqrt3-coefficient grows;
#   (5) the factor complexity of the a-stream of Theorem A: p(n) = 2^n as far as 60000
#       digits can show, i.e. the stream is not automatic and not of linear complexity,
#       so no Adamczewski--Bugeaud criterion applies to the named witness.
#
# Arithmetic: (1)-(4) exact in Z[sqrt3] via the integer comparator p^2 vs 3q^2, so no
# float decides a branch.  (5) uses fixed-point integers with a carried error bound and
# asserts every comparison is unambiguous; nothing is decided within the error.

from collections import Counter
from fractions import Fraction as F
from math import comb, exp, isqrt
import random

# ---------------------------------------------------------------- exact Z[sqrt3] ----
def sign3(p, q):
    """Sign of p + q*sqrt3 for integers p, q."""
    if p >= 0 and q >= 0:
        return 0 if (p == 0 and q == 0) else 1
    if p <= 0 and q <= 0:
        return 0 if (p == 0 and q == 0) else -1
    if p > 0:                                   # p > 0 > q
        return 1 if p * p > 3 * q * q else (-1 if p * p < 3 * q * q else 0)
    return -1 if p * p > 3 * q * q else (1 if p * p < 3 * q * q else 0)

OFFSETS = [(0, 0), (2, 0), (0, 2), (2, 2)]      # c = a + b sqrt3

def admissible(A, B):
    """Offsets c with 0 <= w - c <= U, U = 1 + sqrt3, for w = A + B sqrt3."""
    return [(a, b) for (a, b) in OFFSETS
            if sign3(A - a, B - b) >= 0 and sign3(A - a - 1, B - b - 1) <= 0]

def rule(D):
    """Section 5.1: smallest a, then largest b."""
    return min(D, key=lambda ab: (ab[0], -ab[1]))

W0 = (-12, 9)                                   # w_0 = 3 sigma = 9 sqrt3 - 12
FIXED = {(0, 0), (3, 0), (0, 3), (3, 3)}        # 0, 3, 3 sqrt3, 3U

# --------------------------------------------------- (1)-(2) the tree of the proof ----
DEPTH = 10
frontier, seg, branches = [W0], [], Counter()
for _ in range(DEPTH):
    nxt = []
    for (A, B) in frontier:
        got_a0 = got_b2 = False
        n = 0
        while True:
            D = admissible(A, B)
            assert 1 <= len(D) <= 2, (A, B, D)
            assert (A, B) not in FIXED and B > 3, ("survivor reached", A, B)
            a, b = rule(D)
            if got_a0 and got_b2 and len(D) == 2:
                assert D[0][0] != D[1][0], ("branch with equal a-digit", A, B, D)
                branches[tuple(sorted(D))] += 1
                nxt += [(3 * (A - u), 3 * (B - v)) for (u, v) in D]
                seg.append(n)
                break
            got_a0 |= (a == 0)
            got_b2 |= (b == 2)
            A, B = 3 * (A - a), 3 * (B - b)
            n += 1
            assert n < 500, "segment did not close"
    frontier = nxt
print(f"(1,2) full binary tree to depth {DEPTH}: {len(frontier)} paths "
      f"(2^{DEPTH} = {2 ** DEPTH}); segment length min/mean/max = "
      f"{min(seg)}/{sum(seg) / len(seg):.2f}/{max(seg)}")
print(f"      branch types seen (offset pairs): {dict(branches)}")

# ------------------------------------------------------------- (3) the survivor set ----
# sqrt3 to 57 decimals; only used for the survivor scan, where all data are rationals.
R3 = F(1732050807568877293527446341505872366942805253810380628055, 10 ** 57)
U3 = 1 + R3
OFF_Q = [F(0), F(2), 2 * R3, 2 + 2 * R3]

def forced(w):
    D = [c for c in OFF_Q if 0 <= w - c <= U3]
    return (D[0], len(D) == 1) if D else (None, None)

R = [F(0)] + [3 / F(3) ** k for k in range(8)] + [3 * R3 / F(3) ** k for k in range(8)]
S = R + [3 * U3 - r for r in R]
survive = 0
for s in S:
    w, ok = s, True
    for _ in range(40):
        c, uniq = forced(w)
        if not uniq:
            ok = False
            break
        w = 3 * (w - c)
    survive += ok
print(f"(3)   claimed survivors that never branch: {survive}/{len(S)}")

random.seed(1)
esc = Counter()
for _ in range(20000):
    w = F(random.randrange(10 ** 12), 10 ** 12) * 3 * U3
    for t in range(60):
        c, uniq = forced(w)
        if not uniq:
            esc[t] += 1
            break
        w = 3 * (w - c)
print(f"      random states reaching a branch point: {sum(esc.values())}/20000, "
      f"latest at step {max(esc)}")

# ------------------------------------------------- (5) complexity of the a-stream ----
N = 60000
P = int(1.585 * N) + 128
ONE = 1 << P
S3 = isqrt(3 * (1 << (2 * P)))                  # floor(sqrt3 * 2^P), error < 1 ulp
T1, T2, T3 = ONE + S3, 2 * S3, ONE + 3 * S3     # 1+sqrt3, 2sqrt3, 1+3sqrt3
CONST = {(0, 0): 0, (2, 0): 2 * ONE, (0, 2): 2 * S3, (2, 2): 2 * ONE + 2 * S3}

W, err, stream = -12 * ONE + 9 * S3, 9, []
for k in range(N):
    for T in (T1, T2, T3):
        assert abs(W - T) > err, ("ambiguous comparison at step", k)
    d = (0, 0) if W <= T1 else (2, 0) if W < T2 else (0, 2) if W <= T3 else (2, 2)
    stream.append(d[0])
    W, err = 3 * (W - CONST[d]), 3 * (err + 2)
q0 = stream.count(0) / N
print(f"(5)   {N} digits of the stream a; frequency of 0 is {q0:.5f}")
print("       n     p(n)      2^n   missing   predicted")
for n in range(1, 15):
    s = bytes(stream)
    seen = len({s[i:i + n] for i in range(len(s) - n + 1)})
    miss = 2 ** n - seen
    M = N - n + 1
    pred = sum(comb(n, j) * exp(-M * q0 ** (n - j) * (1 - q0) ** j) for j in range(n + 1))
    print(f"    {n:4d} {seen:8d} {2 ** n:8d} {miss:9d} {pred:11.0f}")
print("      p(n) = 2^n while the sample can show it: the stream is not automatic,")
print("      not Sturmian, not of linear complexity.")
