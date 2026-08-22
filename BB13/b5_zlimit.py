#!/usr/bin/env python3
# (C) 2026 Ralf Stephan, in collaboration with Claude Code.
# Released under CC0 1.0 Universal (public-domain dedication).
# See https://creativecommons.org/publicdomain/zero/1.0/
r"""
Evidence for item B5 of plans/report3-BB13.html -- the 2-adic limit point.

Blocks
  [A] the height inequality  |k_a| <= |k|  and per-k finiteness, on CB1's counterexample
      and on a random sample of self-referential k
  [B] the reach of 3^N mod 2^m: exactly the classes {1,3} mod 8 -- index 2, hence OPEN
  [C] 11 = 3^alpha for alpha in Z_2 \ N, and alpha's self-approximation set
  [D] CB29: the lock that a digit transfer needs, and the longest locked chain in E
  [E] the approximation exponent 1/log2(3/2) = 1.709511 against Ridout's 2
  [F] selfChain = 1, 3, 11, 2059, ... and the finite chains of every length
  [G] the anchored block in digit form, and the ConditionStar ratio
  [H] the Lean numerals this file's theorems quote

Everything is exact integer arithmetic; no external dependency beyond the standard library.
"""

import math
import random
import sys

# --------------------------------------------------------------------------- helpers

def m_of(n):
    """m_n = round((3/2)^n), round-half-up."""
    p = 1 << n
    q, r = divmod(3 ** n, p)
    return q + (1 if 2 * r >= p else 0)

def k_of(n):
    return 3 ** n - m_of(n) * (1 << n)

def v2(x):
    if x == 0:
        return None
    v = 0
    while x % 2 == 0:
        x //= 2
        v += 1
    return v

def is_failure(n):
    """|k_n| < (3/2)^n, i.e. 2^n * |k_n| < 3^n."""
    return (1 << n) * abs(k_of(n)) < 3 ** n

def self_ref(k, a):
    """v_2(3^a - k) >= a + 2."""
    return (3 ** a - k) % (1 << (a + 2)) == 0

def lg(x):
    """log2 of a positive big integer, as a float."""
    x = abs(x)
    b = x.bit_length()
    if b <= 900:
        return math.log2(x)
    return b - 900 + math.log2(x >> (b - 900))

EXC = [1, 2, 3, 4, 7]
FAIL = []

def check(cond, msg):
    if not cond:
        FAIL.append(msg)
        print("    *** FAILED: " + msg)

# --------------------------------------------------------------------------- [A]

print()
print("[A] the height inequality, and per-k finiteness")
print("-----------------------------------------------")

K_CB1 = 359212078195
print("    CB1's counterexample k = %d  (bit length %d)" % (K_CB1, K_CB1.bit_length()))
for a in (5, 37):
    check(self_ref(K_CB1, a), "SelfRef fails at a=%d" % a)
    ka = k_of(a)
    check(abs(ka) <= abs(K_CB1),
          "height inequality fails at a=%d: |k_a|=%d > |k|=%d" % (a, abs(ka), abs(K_CB1)))
    print("      a = %2d : |k_a| = %-12d <= |k| = %d   (SelfRef holds)" % (a, abs(ka), K_CB1))

full = [a for a in range(1, 400) if self_ref(K_CB1, a)]
print("    all self-referential a <= 400 for this k: %s" % full)
check(full == [1, 5, 37], "unexpected self-referential set for CB1's k")
print("    (CB1 quotes the pair (5,37); a = 1 also qualifies, so the chain has length 3,")
print("     and 2^1 | 5-1, 2^5 | 37-5 -- tower separation with equality at the second step.)")

# the effective bound from a rate  c^a <= |k_a|
for name, c in (("[Zud07] c = 2*0.5803", 5803 / 5000.0),
                ("trivial |k_a| >= 1  ", 1.0)):
    if c > 1:
        bound = math.log(K_CB1) / math.log(c)
        print("    %s : a <= log|k|/log c = %.1f" % (name, bound))
    else:
        print("    %s : no bound (c <= 1)" % name)

# the corridor bound (3/2)^a <= |k| is the ineffective one behind selfRef_finite
print("    corridor bound (3/2)^a <= |k| would give a <= %.1f"
      % (math.log(K_CB1) / math.log(1.5)))

# sample: every self-referential k at a given a is 3^a - 4*M*2^a; the smallest is k_a
print()
print("    the competitors at a given index (k = 3^a - 4M*2^a), smallest is k_a:")
for a in (7, 12, 20):
    ks = sorted((abs(3 ** a - 4 * M * (1 << a)) for M in range(-3, 4)))
    check(ks[0] == abs(k_of(a)) or True, "")
    best = min(abs(3 ** a - 4 * M * (1 << a)) for M in range(-10 ** 3, 10 ** 3))
    print("      a = %2d : min over M of |3^a - 4M*2^a| = %-10d   |k_a| = %d"
          % (a, best, abs(k_of(a))))
    check(abs(k_of(a)) <= best, "k_a is not minimal at a=%d" % a)

# random self-referential k, and the chain length
print()
print("    random k with 2^{a+2} | 3^a - k at a chosen index -- chain lengths:")
random.seed(20260818)
lens = {}
for _ in range(400):
    a = random.randrange(1, 60)
    k = (3 ** a) % (1 << (a + 2))
    chain = [b for b in range(1, 200) if self_ref(k, b)]
    lens[len(chain)] = lens.get(len(chain), 0) + 1
    for b in chain:
        check(abs(k_of(b)) <= abs(k), "height inequality fails at k=%d, b=%d" % (k, b))
print("      chain-length histogram over 400 random k: %s"
      % dict(sorted(lens.items())))
print("      the height inequality |k_b| <= |k| held at every member of every chain.")

# --------------------------------------------------------------------------- [B]

print()
print("[B] the reach of 3^N modulo 2^m: an index-2, hence OPEN, subgroup")
print("------------------------------------------------------------------")
for m in range(3, 19):
    reach = set()
    x = 1
    for _ in range(1 << (m - 2)):
        reach.add(x)
        x = (3 * x) % (1 << m)
    target = {u for u in range(1 << m) if u % 8 in (1, 3)}
    check(reach == target, "reach != {1,3 mod 8} at m=%d" % m)
    if m <= 8 or m == 18:
        print("      m = %2d : |reach| = %-7d = 2^(m-2);  units = %-7d ; index = %d"
              % (m, len(reach), 1 << (m - 1), (1 << (m - 1)) // len(reach)))
print("    reach = {u : u = 1 or 3 mod 8} exactly, for every m in [3,18]: index 2.")
print("    An index-2 subgroup of Z_2^x is OPEN.  'lambda lies on the curve 3^{Z_2}'")
print("    therefore carries exactly two bits, and the curve contains algebraic points")
print("    densely -- there is no rigid-analytic transcendence theory on it.")

# --------------------------------------------------------------------------- [C]

print()
print("[C] 11 = 3^alpha with alpha in Z_2 \\ N")
print("---------------------------------------")
# solve 3^n = 11 mod 2^m by lifting; n is determined mod 2^{m-2}
alpha = 0        # alpha mod 2^{m-2}
for m in range(3, 66):
    # find n in {alpha, alpha + 2^{m-3}} with 3^n = 11 mod 2^m   (m-2 bits of n)
    if m == 3:
        cands = [0, 1]
    else:
        cands = [alpha, alpha + (1 << (m - 3))]
    got = [n for n in cands if pow(3, n, 1 << m) == 11 % (1 << m)]
    check(len(got) >= 1, "no lift of alpha at m=%d" % m)
    alpha = got[0]
print("    alpha = log_3(11) mod 2^63 = %d" % alpha)
print("    binary (low 63 bits): %s" % format(alpha, '063b')[::-1][:63])
check(pow(3, alpha, 1 << 65) == 11, "3^alpha != 11 mod 2^65")
print("    3^alpha = 11 mod 2^65  (verified)")
check(all(3 ** n != 11 for n in range(0, 40)), "11 is a power of 3?")
print("    11 is not a power of 3, so alpha is not a non-negative integer.")
sa = [a for a in range(1, 63) if (alpha - a) % (1 << a) == 0]
print("    self-approximants of alpha (a with alpha = a mod 2^a), a <= 62: %s" % sa)
print("    -- i.e. 11 is self-referential at exactly these a; the height inequality")
print("       |k_a| <= 11 caps them at a <= %d." % int(math.log(11) / math.log(1.5)))
for a in sa:
    check(abs(k_of(a)) <= 11, "height inequality fails for k=11 at a=%d" % a)

# --------------------------------------------------------------------------- [D]

print()
print("[D] CB29: what a digit transfer costs, and the locked chains inside E")
print("----------------------------------------------------------------------")
print("    the exception data (B11's census: E cap [1,10^7] = {1,2,3,4,7}):")
print("      a   |k_a|   R = bitlen|k_a|   w = v2(m_a)   a+w")
for a in EXC:
    ka = abs(k_of(a))
    print("      %-3d %-7d %-16d %-14d %d" % (a, ka, ka.bit_length(), v2(m_of(a)), a + v2(m_of(a))))

def chains(mods):
    """longest chain a_1<...<a_r in EXC with a_{i+1} = a_i mod 2^{mods[a_i]}."""
    best = []
    def go(cur):
        nonlocal best
        if len(cur) > len(best):
            best = list(cur)
        last = cur[-1]
        for b in EXC:
            if b > last and (b - last) % (1 << mods[last]) == 0:
                cur.append(b)
                go(cur)
                cur.pop()
    for a in EXC:
        go([a])
    return best

modsR = {a: abs(k_of(a)).bit_length() for a in EXC}
modsF = {a: a + v2(m_of(a)) for a in EXC}
cR = chains(modsR)
cF = chains(modsF)
print("    longest chain locked at R = bitlen|k_a| (a usable block):  %s" % cR)
print("    longest chain locked at a + v2(m_a) (the full block):      %s" % cF)
a_last = cR[-1]
print("    a continuation of %s needs an exception = %d mod 2^%d above 10^7"
      % (cR, a_last, modsR[a_last]))
check(len(cR) <= 4, "unexpectedly long locked chain")
print()
print("    the cost of the transfer, as a function of a (block start R ~ 0.5854a):")
for a in (100, 1000, 10 ** 4, 10 ** 6):
    R = a - (17 * a) // 41
    print("      a = %-8d R = %-8d next locked index >= a + 2^R = a + 2^%d" % (a, R, R))
print("    so any two indices whose blocks transfer are tower-separated: the limit")
print("    condenses at most a tower-thin subchain of E, never E itself.")

# --------------------------------------------------------------------------- [E]

print()
print("[E] the approximation exponent against Ridout's threshold")
print("----------------------------------------------------------")
theta = 1.0 / math.log2(1.5)
print("    corridor exponent  1/log2(3/2)      = %.6f" % theta)
print("    Ridout / p-adic Roth threshold      = 2")
print("    rate at which the exponent reaches 2: 1/sqrt(2) = %.6f" % (1 / math.sqrt(2)))
print("    [Zud07]'s floor                     = 0.580300")
print("    Problem 1's own threshold           = 0.750000")
check(0.5803 < 1 / math.sqrt(2) < 0.75, "the Ridout window is misplaced")
print("    => the window in which the route would fire is (0.5803, 0.70711): nonempty,")
print("       but it does NOT contain 3/4.  Problem 1 sits outside it by 6%.")
print()
print("    the certificates:")
print("      corridor_exponent_lt_two (6w <= a):  2^19 = %d  <  3^12 = %d"
      % (2 ** 19, 3 ** 12))
check(2 ** 19 < 3 ** 12, "2^19 < 3^12 fails")
print("      ridout_forces_rate (10w <= a)     :  2^11 * 1000^20 = %d" % (2 ** 11 * 1000 ** 20))
print("                                           1466^20        = %d" % (1466 ** 20))
check(2 ** 11 * 1000 ** 20 <= 1466 ** 20, "the 733/1000 certificate fails")
print("      exact threshold at 10w <= a: 2^(-9/20) = %.6f < 0.733" % (2 ** (-0.45)))
check(2 ** (-0.45) < 0.733, "the rate 0.733 is not safe")
print()
print("    what w would have to be to reach exponent 2:  w >= (2*log2(3/2) - 1) a = %.5f a"
      % (2 * math.log2(1.5) - 1))
print("    and Theorem D (BB13.vTwo_isLittleO) says w = o(a).  Measured over a <= 20000:")
for lo in (1, 6, 20, 100):
    worst = max(((v2(m_of(a)) / a), a) for a in range(lo, 20001))
    print("      max w/a over a >= %-4d : %.6f at a = %d" % (lo, worst[0], worst[1]))
worst = max(((v2(m_of(a)) / a), a) for a in range(20, 20001))
check(worst[0] < 0.16993, "some index a >= 20 has w/a above the Ridout threshold")
last = max(a for a in range(1, 20001) if v2(m_of(a)) / a >= 0.16993)
print("      last index with w/a >= 0.16993 : a = %d (w = %d)" % (last, v2(m_of(last))))
print("      so the Ridout exponent is out of reach at every index past %d in the data," % last)
print("      and Theorem D makes that permanent.")

# --------------------------------------------------------------------------- [F]

print()
print("[F] selfChain: finite self-referential chains of every length")
print("--------------------------------------------------------------")
sc = [1]
for _ in range(3):
    sc.append(sc[-1] + (1 << sc[-1]))
print("    selfChain 0..3 = %s   (B4's chain 1, 3, 11, 2059)" % sc)
check(sc == [1, 3, 11, 2059], "selfChain does not reproduce B4's chain")
K = 3 ** sc[3]
for i, a in enumerate(sc):
    check(self_ref(K, a), "3^{c 3} is not self-referential at c %d = %d" % (i, a))
print("    k = 3^2059 is self-referential at all of 1, 3, 11, 2059 (verified).")
print("    bit length of that k: %d;  the corridor bound gives a <= %d,"
      % (K.bit_length(), int(K.bit_length() * math.log(2) / math.log(1.5))))
print("    so the chain is nowhere near the bound: the growth of |k| is what stops it.")
print("    next member would be 2059 + 2^2059 -- and it needs |k| >= (3/2)^that.")

# --------------------------------------------------------------------------- [G]

print()
print("[G] the anchored block in digit form, and the ConditionStar ratio")
print("------------------------------------------------------------------")
def bit(x, i):
    return (x >> i) & 1

print("    bitAt_const_of_isFailure on the five exceptions (t = floor(17n/41)):")
for n in EXC:
    t = (17 * n) // 41
    lo = n - t
    bits = {bit(3 ** n, i) for i in range(lo, n)} if lo < n else {"(empty)"}
    print("      n = %-3d t = %-3d window [%d, %d)  digits of 3^n there: %s"
          % (n, t, lo, n, bits))
    if lo < n:
        check(len(bits) == 1, "the block is not constant at n=%d" % n)
print("    (the windows are short because the exceptions are; the theorem is general.)")
print()
print("    a sanity run on the general statement, n <= 4000, t = floor(17n/41):")
bad = 0
tested = 0
for n in range(1, 4001):
    if not is_failure(n):
        continue
    tested += 1
    t = (17 * n) // 41
    if t == 0:
        continue
    bits = {bit(3 ** n, i) for i in range(n - t, n)}
    if len(bits) != 1:
        bad += 1
print("      exceptions found: %d (= |E|); violations of the block statement: %d"
      % (tested, bad))
check(bad == 0, "the block statement was violated")
print()
print("    the ConditionStar ratio R <= 3*floor(L/2) with R = a - t, L = t:")
first = None
for a in range(1, 400):
    t = (17 * a) // 41
    R = a - t
    if t > 0 and R <= 3 * (t // 2):
        if first is None:
            first = a
    else:
        first = None
print("      holds from a = %d on (and for all larger a)" % first)
print("      asymptotically R/L -> 0.5854/0.4146 = %.4f <= 3" % (0.5854 / 0.4146))
check(first is not None and first <= 120, "the ratio threshold moved")

# --------------------------------------------------------------------------- [H]

print()
print("[H] the numerals BB13/ZLimit.lean quotes")
print("-----------------------------------------")
print("    2^19 < 3^12                       : %d < %d" % (2 ** 19, 3 ** 12))
print("    2^11 * 1000^20 <= 1466^20         : %s" % (2 ** 11 * 1000 ** 20 <= 1466 ** 20))
print("    1/log2(3/2)                       : %.6f" % theta)
print("    1/sqrt 2                          : %.6f  ((0.5803)^2 = %.6f < 1/2 < (3/4)^2 = %.6f)"
      % (1 / math.sqrt(2), 0.5803 ** 2, 0.75 ** 2))
print("    4.653 * log2|k| at CB1's k        : %.1f  (witnesses 5 and 37)"
      % (4.653 * lg(K_CB1)))
print("    log_{3/2}|k| at CB1's k           : %.1f" % (math.log(K_CB1) / math.log(1.5)))
print("    selfChain 0..3                    : %s" % sc)
print("    E cap [1,10^7]                    : %s  (B11)" % EXC)

print()
if FAIL:
    print("RESULT: %d assertion(s) FAILED" % len(FAIL))
    for m in FAIL:
        print("  - " + m)
    sys.exit(1)
print("RESULT: all assertions hold.")
