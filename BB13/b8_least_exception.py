#!/usr/bin/env python3
# (C) 2026 Ralf Stephan, in collaboration with Claude Code.
# Released under CC0 1.0 Universal (public-domain dedication).
# See https://creativecommons.org/publicdomain/zero/1.0/
"""
B8 -- Least-exception structure and the rounding recurrence.

Evidence for `BB13/LeastException.lean` and `plans/note-BB13-B8.html`.  Item B8 of
`plans/report3-BB13.html` (A2 strategies V and X, corrected by CB4; A4 P2.1's residue-class
residue).  Everything here is exact integer arithmetic -- no floats anywhere.

Objects (all exact):

    m_n = round((3/2)^n) = (2*3^n + 2^n) // 2^(n+1)
    k_n = 3^n - m_n*2^n                       (|k_n| <= 2^(n-1), with equality only at n = 1)
    c_n = 2*m_{n+1} - 3*m_n                   the carry of the rounding recurrence
    w_n = v_2(m_n)
    D(a) = max{ j >= 0 : 2^j*|k_a|*2^a < 3^a }   the dyadic surplus (-1 if a is not an exception)

Blocks:

  [A] the carry: alphabet, parity law, vanishing law, sign law; and the failure rate of the
      three naive recurrences m_{n+1} = floor/round/ceil(3*m_n/2)
  [B] the descent law and the step dichotomy; v_2 strictly decreasing above depth 1
  [C] the bottom lemma v_2(m_{a-1}) <= 1: violations, sharpness, and what it refutes
  [D] the fibre identity  a+d in fibre  <=>  d <= min(v_2(m_a), D(a))
  [E] the residue-class stratification, its gap, and the refutation of A4's converse
  [F] the bottom congruence m_{a-1} = +-3^{-1} or +-2*3^{-1}  (mod 2^H)
  [G] the price: tall bottoms and the absence of propagation
  [H] peaks: spacing, and the census of {a <= N : v_2(m_a) >= w}
  [I] the certificates behind the numerals in the Lean file

Runtime ~20 s at N = 4000.  Exit code 0 iff every assertion holds.
"""

import sys
from collections import Counter

N = 4000            # main range
NBIG = 20000        # cheap range for the v_2 census only

FAIL = 0


def check(label, ok, detail=""):
    global FAIL
    if not ok:
        FAIL += 1
        print("  !! FAIL  %s  %s" % (label, detail))
    return ok


def v2(x):
    c = 0
    while x % 2 == 0:
        x //= 2
        c += 1
    return c


print("=" * 78)
print("B8  least-exception structure and the rounding recurrence")
print("=" * 78)

print("\nbuilding the exact tables to n = %d ..." % N)
M = [(2 * 3 ** n + 2 ** n) // (2 ** (n + 1)) for n in range(N + 2)]
K = [3 ** n - M[n] * 2 ** n for n in range(N + 2)]
W = [v2(M[n]) for n in range(N + 2)]
C = [2 * M[n + 1] - 3 * M[n] for n in range(N + 1)]
print("done.")

# ---------------------------------------------------------------------------
# [A]  the carry
# ---------------------------------------------------------------------------
print("\n[A] the carry  c_n = 2*m_{n+1} - 3*m_n")

alphabet = Counter(C[1:N])
print("    alphabet over 1 <= n < %d : %s" % (N, dict(sorted(alphabet.items()))))
check("carry alphabet subset {-2..2}", set(alphabet) <= {-2, -1, 0, 1, 2})
check("all five carries occur", set(alphabet) == {-2, -1, 0, 1, 2})

first = {}
for n in range(1, 200):
    first.setdefault(C[n], n)
print("    first occurrence of each value: %s" % dict(sorted(first.items())))

# nearest-integer bound, and where it is not strict
loose = [n for n in range(1, N) if not abs(K[n]) < 2 ** (n - 1)]
print("    |k_n| < 2^(n-1) fails only at n in %s  (there |k_n| = 2^(n-1))" % loose)
check("nearest-integer bound 2|k_n| <= 2^n everywhere",
      all(2 * abs(K[n]) <= 2 ** n for n in range(1, N)))

bad_par = [n for n in range(1, N) if (C[n] - M[n]) % 2 != 0]
check("parity law  c_n = m_n (mod 2)", not bad_par, bad_par[:5])

bad_zero = [n for n in range(1, N)
            if M[n] % 2 == 0 and ((C[n] == 0) != (3 * abs(K[n]) < 2 ** n))]
check("vanishing law  (m_n even):  c_n = 0  <=>  3|k_n| < 2^n", not bad_zero, bad_zero[:5])

bad_sign = [n for n in range(1, N)
            if M[n] % 2 == 1 and C[n] != (1 if K[n] > 0 else -1)]
check("sign law  (m_n odd):  c_n = sign(k_n)", not bad_sign, bad_sign[:5])

bad_two = [n for n in range(1, N) if M[n] % 2 == 0 and C[n] not in (0, 2, -2)]
check("m_n even => c_n in {-2,0,2}", not bad_two, bad_two[:5])

# the three naive recurrences
naive = {
    "floor(3m/2)": lambda n: (3 * M[n]) // 2,
    "round(3m/2)": lambda n: (3 * M[n] + 1) // 2,      # halves round up, as Lean's `round`
    "ceil (3m/2)": lambda n: -((-3 * M[n]) // 2),
}
print("    failure rate of the naive recurrences on 1 <= n < %d:" % N)
for name, f in naive.items():
    bad = sum(1 for n in range(1, N) if f(n) != M[n + 1])
    print("      m_{n+1} = %s : %5d / %d  wrong  (%.1f%%)"
          % (name, bad, N - 1, 100.0 * bad / (N - 1)))
    check("naive recurrence %s is not an identity" % name, bad > 0)
# `round(3m/2)` amounts to the carry choice c_n = +1 for odd m_n and c_n = 0 for even m_n, so it
# is wrong exactly at the other three letters of the alphabet.
mismatch_round = set(C[n] for n in range(1, N) if naive["round(3m/2)"](n) != M[n + 1])
print("      round(3m/2) is wrong exactly at carries %s" % sorted(mismatch_round))
check("round(3m/2) wrong <=> c_n in {-2,-1,2}", mismatch_round == {-2, -1, 2})

# ---------------------------------------------------------------------------
# [B]  the descent law
# ---------------------------------------------------------------------------
print("\n[B] the descent law of the 2-adic arm")

bad_dich = [n for n in range(1, N) if W[n] >= 2 and not (W[n + 1] == W[n] - 1 or W[n + 1] == 0)]
check("dichotomy  w_n >= 2  =>  w_{n+1} in {w_n - 1, 0}", not bad_dich, bad_dich[:5])

bad_chain = [n for n in range(1, N)
             if W[n] >= 2 and (W[n + 1] == W[n] - 1) != (K[n + 1] == 3 * K[n])]
check("descent branch <=> k_{n+1} = 3 k_n (same line)", not bad_chain, bad_chain[:5])

bad_lt = [n for n in range(1, N) if W[n] >= 2 and not W[n + 1] < W[n]]
check("HEADLINE  w_n >= 2  =>  w_{n+1} < w_n", not bad_lt, bad_lt[:5])

rises = [n for n in range(2, N) if W[n] > W[n - 1]]
print("    rises of v_2 on 2 <= n < %d : %d, all from depth <= 1 : %s"
      % (N, len(rises), all(W[n - 1] <= 1 for n in rises)))
check("every rise starts from depth <= 1", all(W[n - 1] <= 1 for n in rises))
print("    depth reached by a rise: %s"
      % dict(sorted(Counter(W[n] for n in rises).items())))

# ---------------------------------------------------------------------------
# [C]  the bottom lemma
# ---------------------------------------------------------------------------
print("\n[C] the bottom lemma:  bottom with v_2(m_a) >= 1  =>  v_2(m_{a-1}) <= 1")

bottoms = [a for a in range(2, N) if W[a] >= 1 and K[a] != 3 * K[a - 1]]
viol = [(a, W[a - 1], W[a]) for a in bottoms if W[a - 1] > 1]
check("no bottom has v_2(m_{a-1}) >= 2", not viol, viol[:5])
dist = Counter(W[a - 1] for a in bottoms)
print("    %d bottoms; v_2(m_{a-1}) distribution: %s" % (len(bottoms), dict(sorted(dist.items()))))
check("A2 strategy X in its original form (v_2(m_{a-1}) = 0) is FALSE", dist.get(1, 0) > 0)
check("CB4's 'then v_2(m_{a-1}) is unconstrained' is FALSE", dist.get(2, 0) == 0)
print("    smallest bottom with v_2(m_{a-1}) = 1 : a = %s"
      % min([a for a in bottoms if W[a - 1] == 1], default=None))
print("    smallest bottom with v_2(m_{a-1}) = 0 : a = %s"
      % min([a for a in bottoms if W[a - 1] == 0], default=None))

# the linked-pair remark of CB4: for a >= 8 consecutive exceptions are on one line, so a least
# exception has a-1 outside E.  Vacuous here (E is finite), but check the inequality that drives it
check("2*(3/4)^n*3 <= 1 for n >= 7", all(2 * 3 ** (n + 1) <= 4 ** n for n in range(7, 60)))

# ---------------------------------------------------------------------------
# [D]  the fibre identity
# ---------------------------------------------------------------------------
print("\n[D] the fibre identity  a+d in fibre(a)  <=>  d <= min(v_2(m_a), D(a))")


def dyadic_surplus(a):
    """max j >= 0 with 2^j |k_a| 2^a < 3^a; -1 if a is not an exception."""
    j, lhs, rhs = -1, abs(K[a]) * 2 ** a, 3 ** a
    while lhs < rhs:
        j += 1
        lhs *= 2
    return j


def fibre_len(a):
    """largest t with k_{a+j} = 3^j k_a and a+j an exception, for all j <= t."""
    t = 0
    while a + t + 1 <= N:
        j = t + 1
        if K[a + j] != 3 ** j * K[a]:
            break
        if not abs(K[a + j]) * 2 ** (a + j) < 3 ** (a + j):
            break
        t = j
    return t


excs = [a for a in range(1, N) if abs(K[a]) * 2 ** a < 3 ** a]
print("    exception set E up to %d : %s" % (N, excs))
check("E = {1,2,3,4,7}", excs == [1, 2, 3, 4, 7])

rows = []
for a in excs:
    rows.append((a, W[a], dyadic_surplus(a), min(W[a], dyadic_surplus(a)), fibre_len(a)))
print("     a   v2  D(a)  min  fibre-1")
for a, w, D, mn, f in rows:
    print("    %2d   %2d   %2d   %3d   %5d   %s" % (a, w, D, mn, f, "ok" if mn == f else "MISMATCH"))
check("fibre = 1 + min(v_2, D) on every exception", all(mn == f for _, _, _, mn, f in rows))

# the identity as an iff, tested on every index with a nonnegative surplus
bad_iff = []
for a in range(3, 400):
    D = dyadic_surplus(a)
    if D < 0:
        continue
    for d in range(0, min(W[a], D) + 4):
        lhs = (K[a + d] == 3 ** d * K[a]) and abs(K[a + d]) * 2 ** (a + d) < 3 ** (a + d)
        rhs = d <= W[a] and 2 ** d * abs(K[a]) * 2 ** a < 3 ** a
        if lhs != rhs:
            bad_iff.append((a, d, lhs, rhs))
check("mem_lineFibre_add_iff on 3 <= a < 400", not bad_iff, bad_iff[:5])

# the a >= 3 threshold is a proof artefact: the numeric step 2*3^m <= 4^m needs m >= 3, but the
# equivalence itself is already true at a = 1, 2
bad_low = []
for a in (1, 2):
    for d in range(0, 6):
        lhs = (K[a + d] == 3 ** d * K[a]) and abs(K[a + d]) * 2 ** (a + d) < 3 ** (a + d)
        rhs = d <= W[a] and 2 ** d * abs(K[a]) * 2 ** a < 3 ** a
        if lhs != rhs:
            bad_low.append((a, d, lhs, rhs))
print("    the equivalence at a = 1, 2 (outside the Lean threshold): %s"
      % ("holds" if not bad_low else bad_low))
print("    2*3^m <= 4^m first holds at m = %s"
      % min(m for m in range(1, 30) if 2 * 3 ** m <= 4 ** m))
check("the a >= 3 threshold is exactly what the proof needs",
      2 * 3 ** 2 > 4 ** 2 and 2 * 3 ** 3 <= 4 ** 3)

# ---------------------------------------------------------------------------
# [E]  the stratification, and A4's converse
# ---------------------------------------------------------------------------
print("\n[E] residue-class stratification  k_a mod 2^M  ->  a mod 2^(M-2)")

ok = True
for Mo in range(3, 13):
    d = {}
    for a in range(Mo, N):
        d.setdefault(K[a] % 2 ** Mo, set()).add(a % 2 ** (Mo - 2))
    if any(len(v) > 1 for v in d.values()):
        ok = False
        print("    !! fails at M = %d" % Mo)
check("k_a mod 2^M determines a mod 2^(M-2) for M = 3..12", ok)

# the gap it buys
seen, reps = {}, []
for a in range(1, N):
    if K[a] in seen:
        reps.append((seen[K[a]], a))
    seen[K[a]] = a
print("    repeated residue values k_a = k_b : %s" % reps)
for a, b in reps:
    check("gap 2^(a-2) | b-a at (%d,%d)" % (a, b), (b - a) % 2 ** max(a - 2, 0) == 0)

# A4's converse: does a long fibre confine `a` to few classes mod 2^(H-2)?
print("    A4's converse -- classes mod 2^(H-2) hit by {a <= %d : v_2(m_a) >= H-1}:" % N)
print("      H   #indices   #classes   modulus   random model")
for H in range(4, 11):
    S = [a for a in range(1, N) if W[a] >= H - 1]
    mod = 2 ** (H - 2)
    hit = len(set(a % mod for a in S))
    expected = mod * (1.0 - (1.0 - 1.0 / mod) ** len(S)) if S else 0.0
    tag = "" if len(S) >= 20 else "   (sample too small to test)"
    print("      %2d   %8d   %8d   %7d   %10.1f%s" % (H, len(S), hit, mod, expected, tag))
    if len(S) >= 20 and mod >= 4:
        # a genuine confinement would give hit << expected; demand it does not
        check("no confinement at H = %d" % H, hit >= 0.7 * expected,
              "hit %d vs random %.1f" % (hit, expected))

# ---------------------------------------------------------------------------
# [F]  the bottom congruence
# ---------------------------------------------------------------------------
print("\n[F] the bottom congruence  m_{a-1} = +-3^{-1} or +-2*3^{-1}  (mod 2^(w+1))")

bad_cong, carries_at_bottom = [], Counter()
for a in bottoms:
    w = W[a]
    mod = 2 ** (w + 1)
    inv3 = pow(3, -1, mod)
    cand = {inv3 % mod, (-inv3) % mod, (2 * inv3) % mod, (-2 * inv3) % mod}
    if M[a - 1] % mod not in cand:
        bad_cong.append((a, w, M[a - 1] % mod, sorted(cand)))
    carries_at_bottom[C[a - 1]] += 1
check("bottom congruence holds at every bottom", not bad_cong, bad_cong[:3])
print("    carries at bottoms: %s" % dict(sorted(carries_at_bottom.items())))
check("no vanishing carry at a bottom", carries_at_bottom.get(0, 0) == 0)
for w in (4, 6, 8):
    mod = 2 ** (w + 1)
    inv3 = pow(3, -1, mod)
    cand = {inv3 % mod, (-inv3) % mod, (2 * inv3) % mod, (-2 * inv3) % mod}
    print("      w = %d : %d admissible classes out of %d  (density 2^%d)"
          % (w, len(cand), mod, 2 - (w + 1)))

# ---------------------------------------------------------------------------
# [G]  the price
# ---------------------------------------------------------------------------
print("\n[G] the price: the constraint sits on the predecessor and does not propagate")

tall = sorted([a for a in bottoms if W[a] >= 5], key=lambda a: -W[a])[:10]
print("      a     v2(m_a)  v2(m_{a-1})")
for a in tall:
    print("    %5d   %6d   %10d" % (a, W[a], W[a - 1]))
check("every tall bottom already satisfies the lemma", all(W[a - 1] <= 1 for a in tall))
print("    max v_2(m_a) over a <= %d : %d (at a = %d); the bottom lemma caps nothing"
      % (N, max(W[1:N]), max(range(1, N), key=lambda a: W[a])))

# ---------------------------------------------------------------------------
# [H]  peaks and the census
# ---------------------------------------------------------------------------
print("\n[H] peaks and the census of the 2-adic arm")

peaks = [a for a in range(2, N) if W[a] >= 2 and W[a - 1] != W[a] + 1]
print("      w   #peaks(>=w)   min gap   bound w-1")
for w in range(2, 10):
    P = [a for a in peaks if W[a] >= w]
    gaps = [P[i + 1] - P[i] for i in range(len(P) - 1)]
    g = min(gaps) if gaps else None
    print("     %2d   %10d   %7s   %8d" % (w, len(P), g, w - 1))
    if gaps:
        check("peaks of depth >= %d are >= %d apart" % (w, w - 1), g >= w - 1)

print("    census  #{a <= N : v_2(m_a) >= w}  against the heuristic N/2^w:")
Wbig = [v2((2 * 3 ** n + 2 ** n) // (2 ** (n + 1))) for n in range(1, 2001)]
for w in range(1, 12):
    c = sum(1 for x in Wbig if x >= w)
    print("      w = %2d : %6d   heuristic %8.1f" % (w, c, 2000.0 / 2 ** w))

# ---------------------------------------------------------------------------
# [I]  the certificates behind the Lean numerals
# ---------------------------------------------------------------------------
print("\n[I] certificates for BB13/LeastException.lean")

for n, want in [(1, -2), (2, 0), (3, 1), (9, 2), (13, -1)]:
    check("carry %d = %d" % (n, want), C[n] == want, "got %d" % C[n])
print("    carry_alphabet   : c_1 = %d, c_2 = %d, c_3 = %d, c_9 = %d, c_13 = %d"
      % (C[1], C[2], C[3], C[9], C[13]))

check("vTwo 8 = 1", W[8] == 1)
check("vTwo 9 = 1", W[9] == 1)
check("carry 8 != 0", C[8] != 0)
print("    bottom_pred_one  : v2(m_8) = %d, v2(m_9) = %d, c_8 = %d" % (W[8], W[9], C[8]))

check("vTwo 4 = 0", W[4] == 0)
check("vTwo 5 = 3", W[5] == 3)
check("carry 4 != 0", C[4] != 0)
print("    bottom_pred_zero : v2(m_4) = %d, v2(m_5) = %d, c_4 = %d" % (W[4], W[5], C[4]))

check("vTwo 62 = 0", W[62] == 0)
check("vTwo 63 = 5", W[63] == 5)
check("carry 62 != 0", C[62] != 0)
print("    tall_bottom_63   : v2(m_62) = %d, v2(m_63) = %d, c_62 = %d" % (W[62], W[63], C[62]))

check("two_mul_three_pow_le_four_pow at m = 3", 2 * 3 ** 3 <= 4 ** 3)
check("... and fails at m = 2", 2 * 3 ** 2 > 4 ** 2)
print("    two_mul_three_pow_le_four_pow : 2*27 = 54 <= 64 = 4^3, while 2*9 = 18 > 16 = 4^2")

# the order of 3 mod 2^M, reused from BB13/TwoAdicRigidity.lean
bad_ord = [Mo for Mo in range(3, 16)
           if pow(3, 2 ** (Mo - 2), 2 ** Mo) != 1 or pow(3, 2 ** (Mo - 3), 2 ** Mo) == 1]
check("ord(3 mod 2^M) = 2^(M-2) for M = 3..15", not bad_ord, bad_ord)

print("\n" + "=" * 78)
if FAIL:
    print("RESULT: %d assertion(s) FAILED" % FAIL)
    sys.exit(1)
print("RESULT: all assertions hold.")
print("""
Summary of B8.

  * The rounding recurrence is a PAIR recurrence.  `m_{n+1} = round(3 m_n / 2)` is false at
    roughly a third of all indices; the exact step is 2 m_{n+1} = 3 m_n + c_n with a carry
    c_n in {-2,-1,0,1,2} that is a function of k_n, not of m_n.  There is no autonomous
    recursion in m, so strategy V has no lever.

  * The 2-adic arm never rises except from depth <= 1 (block [B]): above depth 1 it descends
    by exactly one per step, and each descent walks down one line.  Hence the bottom lemma
    v_2(m_{a-1}) <= 1 (block [C]) -- A2's strategy X was right up to one unit, and CB4's
    "unconstrained" is wrong.  Both values 0 and 1 occur, so <= 1 is sharp.

  * The fibre is exactly 1 + min(v_2(m_a), D(a)) (block [D]): the report's computed formula
    is now an equivalence, with the two arms as the two ends of the interval.

  * The stratification is real but points the wrong way (block [E]): prescribing M low-order
    bits of k_a costs a gap 2^(M-2), while a fibre of height H prescribes the depth of m_a
    (a condition mod 2^(a+H)) and the HIGH bits of k_a.  A4's converse is refuted: the high-
    depth indices are spread over the classes mod 2^(H-2) exactly as a random set would be.

  * The price (blocks [F], [G]): a fibre of height H at the bottom a is the congruence
    m_{a-1} = +-3^{-1} or +-2*3^{-1} mod 2^H -- four classes out of 2^H, i.e. a condition on
    the binary window of 3^a at bit a.  That is B7's milestone 2, priced at 0%.  The lemma
    constrains the predecessor, never the bottom, and every tall bottom in the census already
    satisfies it.
""")
