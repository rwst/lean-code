#!/usr/bin/env python3
# (C) 2026 Ralf Stephan, in collaboration with Claude Code.
# Released under CC0 1.0 Universal (public-domain dedication).
# See https://creativecommons.org/publicdomain/zero/1.0/
"""
B9 -- Thin sets: meeting Q2.5's challenge on a subsequence.

Evidence for `BB13/ThinSets.lean` and `plans/note-BB13-B9.html`.  Item B9 of
`plans/report3-BB13.html` (A2's probe AK -- LTE on a = 2^l; A4's P2.5 -- arithmetic
progressions, automatic index sets, the density-1 target).  Everything here is exact integer
arithmetic -- no floats in any assertion.

Objects (all exact):

    m_n = round((3/2)^n) = (3^n + 2^(n-1)) >> n
    k_n = 3^n - m_n*2^n                       (|k_n| <= 2^(n-1))
    w_n = v_2(m_n)                            the v arm
    D(a) = max{ j >= 0 : 2^j*|k_a|*2^a < 3^a } the dyadic surplus (-1 if a is no exception)

Q2.5's precise challenge: exhibit an infinite A and a proof of min(v_2(m_a), D(a)) <= C on A
that does not go through a rate ||(3/2)^a|| > c^a with c > 2^(-0.8).

Blocks:

  [A] the three readings of the challenge: A inside E (vacuous), A inside N with the min
      (trivial, D(a) = -1 off E), and the v arm alone (the real one)
  [B] the delivered set  S = { n : v_2(m_n) <= 1 } : density, gaps, and the proved gap bound
  [C] counting: #(S cap [1,N]) against the proved log_2 N, and the dyadic-block statement
  [D] the rise/descent structure, and why no fixed C reaches density 1 through the v arm
  [E] the transport theorem  v_2(3^b - 3^a) = v_2(b-a) + 2  and the window it never reaches
  [F] residue classes mod 2^j: the pinned depth is exactly j+2, and no class is shallow
  [G] A2's probe AK, A = {2^l}: LTE gives exactly l+2 = log_2(a)+2 bits
  [H] automatic index sets: dense ones pin nothing, sparse ones pin log_2(a)+2 -- AK again;
      and the shallow set itself is at maximal factor complexity, so it is not automatic
  [I] the certificates behind the numerals in the Lean file

Runtime ~40 s at N = 20000.  Exit code 0 iff every assertion holds.
"""

import sys
from collections import Counter

N = 20000           # main range for the v_2 tables
NPAIR = 200         # exhaustive pair range for the transport identity
NCLASS = 20000      # range for the residue-class census

FAIL = 0


def check(label, ok, detail=""):
    global FAIL
    if not ok:
        FAIL += 1
        print("  !! FAIL  %s  %s" % (label, detail))
    return ok


def v2(x):
    if x == 0:
        return None
    x = abs(x)
    return (x & -x).bit_length() - 1


print("=" * 78)
print("B9  thin sets: Q2.5's challenge on a subsequence")
print("=" * 78)

print("\nbuilding the exact tables to n = %d ..." % N)
M = [1] * (N + 2)
K = [0] * (N + 2)
W = [0] * (N + 2)
p3 = 1
for n in range(1, N + 2):
    p3 *= 3
    M[n] = (p3 + (1 << (n - 1))) >> n
    K[n] = p3 - (M[n] << n)
    W[n] = v2(M[n])
print("done.")

# ---------------------------------------------------------------------------
# [A]  the three readings of Q2.5's challenge
# ---------------------------------------------------------------------------
print("\n[A] the three readings of the challenge")

# (i) A inside the exception set: E is finite (Mahler/Ridout), so no infinite A exists.
exceptions = [n for n in range(1, N + 1) if abs(K[n]) * (1 << n) < 3 ** n]
print("    E cap [1,%d] = %s   (finite by Mahler; the root's `failures_finite`)"
      % (N, exceptions))
check("census E = {1,2,3,4,7}", exceptions == [1, 2, 3, 4, 7])
print("    reading (i)  A subset E : VACUOUS -- no infinite A exists, unconditionally.")

# (ii) A inside N with the min: off E the dyadic surplus is negative, so the min is <= -1.


def dyadic_surplus(a):
    """max{ j >= 0 : 2^j |k_a| 2^a < 3^a }, or -1 if a is not an exception."""
    lhs = abs(K[a]) << a
    rhs = 3 ** a
    if not lhs < rhs:
        return -1
    j = 0
    while (lhs << (j + 1)) < rhs:
        j += 1
    return j


Dsmall = {a: dyadic_surplus(a) for a in range(1, 300)}
neg = [a for a in range(1, 300) if Dsmall[a] == -1]
print("    D(a) = -1 for %d of the first 299 indices; D(a) >= 0 exactly on %s"
      % (len(neg), [a for a in range(1, 300) if Dsmall[a] >= 0]))
check("D(a) >= 0 iff a is an exception",
      [a for a in range(1, 300) if Dsmall[a] >= 0] == [1, 2, 3, 4, 7])
print("    fibre data (v_2, D, min) on E: %s"
      % [(a, W[a], Dsmall[a], min(W[a], Dsmall[a])) for a in [1, 2, 3, 4, 7]])
check("fibre data matches the report's census",
      [(W[a], Dsmall[a]) for a in [1, 2, 3, 4, 7]] == [(1, 0), (1, 1), (0, 0), (0, 2), (0, 0)])
print("    reading (ii) A subset N with the min : TRIVIAL -- min <= -1 off E, and the")
print("                 complement of E has density 1 by the census alone.")
print("    reading (iii) the v arm alone, min replaced by v_2(m_a) : the real challenge.")

# ---------------------------------------------------------------------------
# [B]  the delivered set
# ---------------------------------------------------------------------------
print("\n[B] the delivered set  S = { n : v_2(m_n) <= 1 }")

S = [n for n in range(1, N + 1) if W[n] <= 1]
Sset = set(S)
print("    |S cap [1,%d]| = %d   (density %.4f)" % (N, len(S), len(S) / N))
dist = Counter(W[1:N + 1])
print("    v_2 distribution: %s" % dict(sorted(dist.items())))
print("    P(v_2 >= w) against 2^-w:")
for w in range(0, 9):
    cnt = sum(c for v, c in dist.items() if v >= w)
    print("      w = %d : %6d / %d = %.5f    2^-%d = %.5f"
          % (w, cnt, N, cnt / N, w, 2.0 ** (-w)))

# the proved gap bound: some n+j with j <= v_2(m_n) is shallow
bad = [n for n in range(1, N) if not any(W[n + j] <= 1 for j in range(0, W[n] + 1))]
check("proved gap bound: exists j <= v_2(m_n) with v_2(m_{n+j}) <= 1", not bad, bad[:5])

gaps = [S[i + 1] - S[i] for i in range(len(S) - 1)]
print("    measured gaps between consecutive shallow indices: max %d (at n = %d), mean %.3f"
      % (max(gaps), S[gaps.index(max(gaps))], sum(gaps) / len(gaps)))
print("    gap distribution: %s" % dict(sorted(Counter(gaps).items())))

# the effective elementary bound 41*v_2(m_n) <= 24n + 41
bad = [n for n in range(1, N + 1) if not 41 * W[n] <= 24 * n + 41]
check("41 v_2(m_n) <= 24 n + 41  (the 0.585 row for the v arm)", not bad, bad[:5])
worst = max(range(10, N + 1), key=lambda n: W[n] / n)
print("    sharpest ratio v_2(m_n)/n on [10,%d]: %.5f at n = %d (proved cap 24/41 = %.5f)"
      % (N, W[worst] / worst, worst, 24 / 41))
print("    measured max gap %d vs the proved gap bound v_2(m_n) <= 0.5854 n + 1 -- the")
print("    proof is astronomically loose, but it is the only unconditional one available.")
nmax = W.index(max(W[1:N + 1]))
print("    max v_2(m_n) = %d at n = %d;  log_2 n = %.2f"
      % (max(W[1:N + 1]), nmax, nmax.bit_length() - 1 + 0.0))

# ---------------------------------------------------------------------------
# [C]  counting
# ---------------------------------------------------------------------------
print("\n[C] counting: the dyadic-block statement and the proved log_2 N floor")

bad = []
for i in range(0, 14):
    lo, hi = 1 << i, 1 << (i + 1)
    if hi > N:
        break
    if not any(W[j] <= 1 for j in range(lo, hi)):
        bad.append(i)
check("every dyadic block [2^i, 2^(i+1)) contains a shallow index", not bad, bad)
print("    first shallow index of each block [2^i, 2^(i+1)):")
row = []
for i in range(0, 14):
    lo, hi = 1 << i, 1 << (i + 1)
    if hi > N:
        break
    row.append(next(j for j in range(lo, hi) if W[j] <= 1))
print("      %s" % row)
for Np in (16, 256, 4096, N):
    cnt = sum(1 for n in range(1, Np + 1) if W[n] <= 1)
    print("    #(S cap [1,%5d]) = %5d ;  proved floor  log_2 %d = %2d ;  ratio %.1f"
          % (Np, cnt, Np, Np.bit_length() - 1, cnt / max(1, Np.bit_length() - 1)))

# ---------------------------------------------------------------------------
# [D]  rises, descents, and the density-1 target
# ---------------------------------------------------------------------------
print("\n[D] rises and descents; the density-1 target")

A = [n for n in range(1, N) if W[n + 1] >= W[n]]
print("    A = { n : v_2(m_{n+1}) >= v_2(m_n) } has density %.4f on [1,%d)"
      % (len(A) / (N - 1), N))
bad = [n for n in A if W[n] > 1]
check("A is contained in S (the contrapositive of vTwo_succ_lt)", not bad, bad[:5])
rises = [n for n in range(1, N) if W[n + 1] > W[n]]
print("    strict rises: %d; all of them start from depth <= 1: %s"
      % (len(rises), all(W[n] <= 1 for n in rises)))
check("every rise starts from depth <= 1", all(W[n] <= 1 for n in rises))
bad = [n for n in range(1, N) if W[n] >= 2 and not W[n + 1] < W[n]]
check("vTwo_succ_lt : v_2(m_n) >= 2 => v_2(m_{n+1}) < v_2(m_n)", not bad, bad[:5])

print("    density of { n : v_2(m_n) >= C+1 } -- the obstruction to density 1 in the v arm:")
for C in range(0, 6):
    cnt = sum(1 for n in range(1, N + 1) if W[n] >= C + 1)
    print("      C = %d : %6d / %d = %.5f   (heuristic 2^-(C+1) = %.5f)"
          % (C, cnt, N, cnt / N, 2.0 ** (-(C + 1))))
print("    => no fixed C gives density 1 through the v arm; the density-1 target is")
print("       reachable only off E, where the min is trivially negative.")

# ---------------------------------------------------------------------------
# [E]  the transport theorem
# ---------------------------------------------------------------------------
print("\n[E] transport: what one index tells another")

bad = []
for b in range(1, NPAIR + 1):
    tb = 3 ** b
    for a in range(0, b):
        d = b - a
        got = v2(tb - 3 ** a)
        want = 1 if d % 2 else v2(d) + 2
        if got != want:
            bad.append((a, b, got, want))
check("v_2(3^b - 3^a) = v_2(b-a) + 2 (b-a even), = 1 (b-a odd)", not bad, bad[:3])
print("    verified on all %d pairs 0 <= a < b <= %d"
      % (NPAIR * (NPAIR + 1) // 2, NPAIR))

print("    the window at b needs depth b + H;  the deepest transport from ANY a < b is")
print("    log_2(b-a) + 2 <= log_2 b + 2:")
for b in (10, 100, 1000, 10000, 100000):
    best = max(v2(d) + 2 for d in range(2, b + 1, 2))
    print("      b = %6d : window depth b+2 = %6d ; best transported depth = %2d ; ratio %.5f"
          % (b, b + 2, best, best / (b + 2)))

# the reversal: a pinned index has a DEEP fibre
print("    the reversal -- if the window at b were pinned to a fixed c, then v_2(m_b) >= H:")
hits = []
for b in range(3, 400):
    c = K[b]                       # the only admissible c is k_b itself
    H = 0
    while (3 ** b - c) % (1 << (b + H + 1)) == 0:
        H += 1
    hits.append((b, H))
check("pinning depth at b equals v_2(m_b) exactly",
      all(H == W[b] for b, H in hits), [x for x in hits if x[1] != W[x[0]]][:3])
print("      2^(b+H) | 3^b - k_b  <=>  H <= v_2(m_b)  : verified for 3 <= b < 400")

# ---------------------------------------------------------------------------
# [F]  residue classes
# ---------------------------------------------------------------------------
print("\n[F] residue classes mod 2^j: exactly j+2 bits, and no class is shallow")

bad = []
for j in range(1, 9):
    for r in range(0, 1 << j):
        a, b = r, r + (1 << j)
        if (3 ** b - 3 ** a) % (1 << (j + 2)) != 0:
            bad.append(("pins", j, r))
        if (3 ** b - 3 ** a) % (1 << (j + 3)) == 0:
            bad.append(("pins more", j, r))
check("a = b mod 2^j pins exactly j+2 bits of 3^a (both directions)", not bad, bad[:3])

print("    class census on [1,%d] -- max and mean v_2(m_a) per class mod 2^j:" % NCLASS)
for j in (1, 2, 3, 4, 6, 8):
    mx, mn, mean = [], [], []
    for r in range(1 << j):
        vals = [W[a] for a in range(1, NCLASS + 1) if a % (1 << j) == r]
        mx.append(max(vals))
        mn.append(min(vals))
        mean.append(sum(vals) / len(vals))
    print("      j = %d : max over classes %2d..%2d, mean %.3f..%.3f  (global mean %.3f)"
          % (j, min(mx), max(mx), min(mean), max(mean),
             sum(W[1:NCLASS + 1]) / NCLASS))
    check("no class mod 2^%d is shallow (every class carries v_2 >= 2)" % j, min(mx) >= 2)

# ---------------------------------------------------------------------------
# [G]  A2's probe AK
# ---------------------------------------------------------------------------
print("\n[G] A2's probe AK: A = { 2^l }")

bad = []
for l in range(1, 13):
    e = v2(3 ** (1 << l) - 1)
    if e != l + 2:
        bad.append((l, e))
check("LTE: v_2(3^(2^l) - 1) = l + 2", not bad, bad[:3])
print("    v_2(3^(2^l) - 1) = l+2 for 1 <= l <= 12 : the class 2^l pins l+2 = log_2(a)+2 bits")
print("    v_2(m_a) at a = 2^l  (l = 1..14): %s"
      % [W[1 << l] for l in range(1, 15) if (1 << l) <= N])
print("    -- no pattern: the probe controls log_2(a) bits and the window needs a.")
print("    information ratio (l+2)/(2^l+2):")
for l in (4, 8, 12, 16, 20):
    print("      l = %2d : a = 2^l = %8d ; pinned %2d of %8d bits = %.3g %%"
          % (l, 1 << l, l + 2, (1 << l) + 2, 100.0 * (l + 2) / ((1 << l) + 2)))

# ---------------------------------------------------------------------------
# [H]  automatic index sets
# ---------------------------------------------------------------------------
print("\n[H] automatic index sets")


def pin_depth(seq):
    """min over pairs of v_2(3^b - 3^a) -- the depth the whole set pins."""
    best = None
    for i in range(len(seq)):
        for j in range(i + 1, len(seq)):
            d = seq[j] - seq[i]
            dep = 1 if d % 2 else v2(d) + 2
            best = dep if best is None else min(best, dep)
    return best


families = {
    "evil numbers (Thue-Morse 0), dense": [n for n in range(1, 200)
                                           if bin(n).count("1") % 2 == 0][:20],
    "odious numbers (Thue-Morse 1), dense": [n for n in range(1, 200)
                                             if bin(n).count("1") % 2 == 1][:20],
    "A = {2^l}  (pumped 1 0*)": [1 << l for l in range(1, 16)],
    "A = {(4^i-1)/3}  (pumped (01)*)": [(4 ** i - 1) // 3 for i in range(1, 12)],
    "A = {3*2^l + 1}  (pumped 11 0* 1)": [3 * (1 << l) + 1 for l in range(1, 15)],
}
for name, fam in families.items():
    dep = pin_depth(fam)
    top = max(fam)
    print("    %-38s pins %2d bits ; largest member %d (needs %d)"
          % (name, dep, top, top + 2))
check("dense automatic families pin only 1 bit",
      pin_depth([n for n in range(1, 200) if bin(n).count("1") % 2 == 0][:20]) == 1)

print("    factor complexity of the shallow word  s_n = [v_2(m_n) <= 1]  on [1,%d]:" % N)
word = "".join("1" if W[n] <= 1 else "0" for n in range(1, N + 1))
maxlen = 0
for L in range(1, 15):
    p = len(set(word[i:i + L] for i in range(len(word) - L + 1)))
    full = min(1 << L, len(word) - L + 1)
    print("      L = %2d : p(L) = %5d   (maximum possible %5d)%s"
          % (L, p, full, "  <- full" if p == full else ""))
    if p == full and p == (1 << L) and maxlen == L - 1:
        maxlen = L
check("the shallow word has full complexity 2^L up to L = 7", maxlen >= 7)
print("    every binary pattern of length %d occurs; p(L)/L climbs from %.1f at L = 7 to"
      % (maxlen, 128 / 7.0))
pL14 = len(set(word[i:i + 14] for i in range(len(word) - 13)))
print("    %.1f at L = 14, so the complexity is not linear on the measured range --" % (pL14 / 14.0))
print("    a 2-automatic sequence has p(L) = O(L).  The shallow set is not automatic.")

# ---------------------------------------------------------------------------
# [I]  certificates for the Lean numerals
# ---------------------------------------------------------------------------
print("\n[I] certificates for the Lean file")

print("    3^41 = %d" % 3 ** 41)
print("    2^65 = %d" % 2 ** 65)
check("3^41 <= 2^65", 3 ** 41 <= 2 ** 65)
print("    the elementary v-arm row: 41 v_2(m_n) <= 24 n + 41, i.e. v_2 <= 0.5854 n + 1")

print("    the first shallow index of each of the first eight dyadic blocks: %s"
      % [next(j for j in range(1 << i, 1 << (i + 1)) if W[j] <= 1) for i in range(8)])
print("    v_2(m_n) for n = 1..24: %s" % W[1:25])
print("    (5,37): v_2(37-5) + 2 = %d, while the window at 37 needs 39 bits"
      % (v2(32) + 2))
check("(5,37) transports 7 bits, not 39", v2(3 ** 37 - 3 ** 5) == 7)
print("    v_2(3^8 - 1) = %d  (LTE at l = 3: 3 + 2)" % v2(3 ** 8 - 1))
check("v_2(3^8 - 1) = 5", v2(3 ** 8 - 1) == 5)

print("\n" + "=" * 78)
if FAIL:
    print("RESULT: %d assertion(s) FAILED" % FAIL)
    sys.exit(1)
print("RESULT: all assertions hold.")
print("""
Summary of B9.

  * The challenge has three readings and only one is live (block [A]).  Inside E it is
    vacuous -- E is finite, so no infinite A exists.  With the min over all of N it is
    trivial -- D(a) = -1 off E, so min <= -1 on a set of density 1, and Mahler already
    supplies that.  The only content is the v arm: an infinite A with v_2(m_a) <= C.

  * That challenge is MET, with C = 1, rate-free (blocks [B], [C]).  B8's descent law
    v_2(m_n) >= 2 => v_2(m_{n+1}) < v_2(m_n) makes S = { n : v_2(m_n) <= 1 } infinite, with
    an effective gap bound: the next shallow index after n is at most n + v_2(m_n), hence at
    most (65/41) n, so every dyadic block contains one and #(S cap [1,N]) >= log_2 N.  No
    rate, no Diophantine input, no exception hypothesis.  Measured density 0.75.

  * The set is defined by the sequence, and no a-priori set can replace it (block [E]).
    Transport is exact: v_2(3^b - 3^a) = v_2(b-a) + 2, so the deepest fact about 3^b that any
    smaller index can supply sits at depth log_2(b) + 2, while the window that carries
    v_2(m_b) sits at depth b + H.  No pair of indices ever reaches the other's window.

  * The reversal (block [E]): if a set DID pin the window at b to a fixed value, then
    v_2(m_b) >= H at that b -- the pinned sets are exactly the deep ones.  The thin-set route
    and its target have opposite signs.

  * The three named candidates all die at the same bound.  A class mod 2^j pins exactly j+2
    bits (block [F]) and no class is shallow.  AK's probe A = {2^l} pins exactly l+2 bits by
    LTE (block [G]) -- it is the OPTIMAL instance of the residue-class idea, not a weak one.
    Automatic index sets (block [H]) split: dense ones pin one single bit, sparse ones are
    pumped 2-power families and pin log_2(a)+2 -- AK again.  And the shallow set itself has
    full factor complexity, so it is not automatic in any case.

  * Density 1 is out of reach through the v arm at every fixed C (block [D]): the density of
    { v_2(m_n) >= C+1 } is 2^-(C+1) > 0.  Off E the min is trivially negative, so the
    density-1 target is a statement about E, i.e. about Mahler, not about Problem 2.
""")
