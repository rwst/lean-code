#!/usr/bin/env python3
"""
(C) 2026 Ralf Stephan, in collaboration with Claude Code.
Released under CC0 1.0 Universal (public-domain dedication).
See https://creativecommons.org/publicdomain/zero/1.0/

Numerical evidence for strategy **B6(iii)** of `plans/report3-BB13.html`:

    "Unconditional target: count quality->1.3 triples of the rigid shape 3^a - mu*2^m = k."

Companion of `BB13/RigidCount.lean` and `plans/note-BB13-B6iii.html`.

Blocks
------
[A] the dictionary constants (forward 15/41, backward 57/156, B7's 17/41, q*)
[B] the diagonal (frame) triples: quality, content, and the *powerful surplus* mu|k|/rad
[C] the general rigid family on the corridor: every triple of quality >= 13/10,
    and which of the two mechanisms produced it
[D] the forward ledger 41L >= 15a+147  ==>  rad^13 g^10 <= (3^a)^10
[E] the backward split  quality  ==>  3^{3a} |k|^13 <= 2^{13m+13} S^13
[F] the k = 1 family: one solution at every index (so fixing k finitises nothing)
[G] Bennett pricing: admissible (mu,k) pairs per index against the true corridor count
[H] the corridor is the only searchable part: cost of the census, per index
[I] certification of the numerals that appear in the Lean file

Runtime ~3 min.  Exact radicals throughout (Miller-Rabin + Pollard rho, each factor
of the triple factorised separately -- never the product).
"""
import sys
import random
from math import log, gcd

random.seed(20260818)

P = lambda *a: (print(*a), sys.stdout.flush())

# ------------------------------------------------------------------ factorisation
_SMALL = [2, 3, 5, 7, 11, 13, 17, 19, 23, 29, 31, 37, 41, 43, 47, 53, 59, 61, 67,
          71, 73, 79, 83, 89, 97]


def is_prime(n):
    if n < 2:
        return False
    for p in _SMALL:
        if n % p == 0:
            return n == p
    d, s = n - 1, 0
    while d % 2 == 0:
        d //= 2
        s += 1
    for a in (2, 3, 5, 7, 11, 13, 17, 19, 23, 29, 31, 37):
        x = pow(a, d, n)
        if x in (1, n - 1):
            continue
        for _ in range(s - 1):
            x = x * x % n
            if x == n - 1:
                break
        else:
            return False
    return True


def pollard(n):
    if n % 2 == 0:
        return 2
    while True:
        x = random.randrange(2, n)
        y = x
        c = random.randrange(1, n)
        d = 1
        while d == 1:
            x = (x * x + c) % n
            y = (y * y + c) % n
            y = (y * y + c) % n
            d = gcd(abs(x - y), n)
        if d != n:
            return d


def primes_of(n, out):
    """Collect the distinct primes of `n` into the set `out`."""
    n = abs(n)
    for p in _SMALL:
        while n % p == 0:
            out.add(p)
            n //= p
    stack = [n]
    while stack:
        t = stack.pop()
        if t == 1:
            continue
        if is_prime(t):
            out.add(t)
            continue
        d = pollard(t)
        stack.append(d)
        stack.append(t // d)


def rad_of(*parts):
    """Radical of the product of `parts`, each factorised on its own."""
    out = set()
    for t in parts:
        primes_of(t, out)
    r = 1
    for p in out:
        r *= p
    return r


def mnum(a):
    q, r = divmod(3 ** a, 2 ** a)
    return q + (1 if 2 * r >= 2 ** a else 0)


def triple(a, m, mu):
    """(k, content g, radical, C, quality) of the rigid triple 3^a = mu 2^m + k."""
    k = 3 ** a - mu * 2 ** m
    if k == 0 or mu < 1:
        return None
    g = gcd(mu, abs(k))
    R = rad_of(3, 2, mu, abs(k))
    C = 3 ** a // g
    if C <= 1:
        return None
    return k, g, R, C, log(C) / log(R)


# ===================================================================== [A]
P("=" * 74)
P("[A] the dictionary constants")
P("=" * 74)
P("  forward   15/41   = %.6f   (41L >= 15a + 147  ==>  quality >= 13/10)" % (15 / 41))
P("  backward  57/156  = %.6f   (from 3^12 >= 2^19)" % (57 / 156))
P("  sharp     3log2(3)/13 = %.6f" % (3 * log(3, 2) / 13))
P("  B7 exception block threshold 17/41 = %.6f" % (17 / 41))
P("  q* = log3/(2 log(3/2))  = %.6f  (asymptotic quality of the frame triples)"
  % (log(3) / (2 * log(1.5))))
P("  quality >= q  <==>  block of relative length >= (1 - 1/q) log2 3:")
for q in (1.3, 1.35476, 1.4, 1.5, 1.63):
    P("     q = %.5f  ->  %.6f a" % (q, (1 - 1 / q) * log(3, 2)))
assert 57 / 156 < 3 * log(3, 2) / 13 < 15 / 41 < 17 / 41
P("  CHECK  backward %.6f < sharp %.6f < forward %.6f < B7 %.6f: OK"
  % (57 / 156, 3 * log(3, 2) / 13, 15 / 41, 17 / 41))
qstar = log(3) / (2 * log(1.5))
assert abs((1 - 1 / qstar) * log(3, 2) - log(4 / 3, 2)) < 1e-12
P("  IDENTITY  (1 - 1/q*) log2 3 = log2(4/3) = eps* log2 3 = %.6f" % log(4 / 3, 2))
P("            -> quality >= q* IS the exception condition; B6(i)'s q* and B7's")
P("               17/41 = 0.414634 are the same constant, and 13/10 sits BELOW it.")

# ===================================================================== [B]
P("")
P("=" * 74)
P("[B] the diagonal (frame) triples 3^a = m_a 2^a + k_a, a <= 120")
P("=" * 74)
rows = []
maxsurp, argmaxsurp = 0.0, 0
for a in range(1, 121):
    t = triple(a, a, mnum(a))
    if t is None:
        continue
    k, g, R, C, q = t
    surp = mnum(a) * abs(k) / R
    if surp > maxsurp:
        maxsurp, argmaxsurp = surp, a
    rows.append((q, a, surp, g))
rows.sort(reverse=True)
P("  top qualities (q, a, surplus mu|k|/rad, content g):")
for r in rows[:8]:
    P("     q=%.4f  a=%3d  S=%9.2f  g=%d" % r)
P("  mean quality over a <= 120: %.4f" % (sum(r[0] for r in rows) / len(rows)))
P("  max surplus %.2f at a = %d;  #(a: S > 10) = %d,  #(a: S > 100) = %d"
  % (maxsurp, argmaxsurp, sum(1 for r in rows if r[2] > 10),
     sum(1 for r in rows if r[2] > 100)))
viol = [r[1] for r in rows if r[2] > 2 ** (r[1] // 8)]
P("  indices where the surplus exceeds the 2^(a/8) budget of `RigidDelta`: %s" % sorted(viol))
P("  quality >= 13/10 among the diagonal triples: %d of %d"
  % (sum(1 for r in rows if r[0] >= 1.3), len(rows)))
P("  the five known exceptions:")
for a in (1, 2, 3, 4, 7):
    k, g, R, C, q = triple(a, a, mnum(a))
    P("     a=%d  m_a=%d  k_a=%+d  g=%d  rad=%d  q=%.4f" % (a, mnum(a), k, g, R, q))

# ===================================================================== [C]
P("")
P("=" * 74)
P("[C] the general rigid family on the corridor, a <= 45: quality >= 13/10")
P("=" * 74)
AMAX_C = 45
hits = []
for a in range(1, AMAX_C + 1):
    N = 3 ** a
    for m in range(1, int(a * log(3, 2)) + 2):
        mu0 = N // 2 ** m
        for mu in (mu0, mu0 + 1):
            if mu < 1:
                continue
            t = triple(a, m, mu)
            if t is None:
                continue
            k, g, R, C, q = t
            if q >= 1.3:
                L = m - abs(k).bit_length()          # block length below bit m
                hits.append((q, a, m, mu, k, mu * abs(k) / R, L, 15 * a / 41))
hits.sort(reverse=True)
# a triple is determined by (a, k); the *primitive* triple, by (mu/g, k/g) -- writing
# `mu 2^m` with a smaller power of 2, or moving up a line, does not change it
seen_ak, seen_prim, uniq = set(), set(), []
for h in hits:
    q, a, m, mu, k, S, L, thr = h
    g = gcd(mu, abs(k))
    if (a, k) in seen_ak:
        continue
    seen_ak.add((a, k))
    uniq.append(h + (k // g, mu // g))
    seen_prim.add((mu // g, k // g))
P("  q       a   m  mu            k            surplus    L    15a/41")
for h in uniq:
    P("  %.4f %3d %3d %-13d %-12d %9.2f %4d %7.1f" % h[:8])
P("  raw hits %d; distinct (a,k) triples %d; distinct *primitive* triples %d"
  % (len(hits), len(uniq), len(seen_prim)))
P("  the %d primitive triples, and what produced them.  The line-invariant statistic is the"
  % len(seen_prim))
P("  *powerful part* P = mu1|k1| / (rad(mu1) rad(k1)) of the primitive triple (the raw surplus")
P("  mu|k|/rad is not a line invariant: it grows by 3^{2d} along a line).")
shown = {}
for h in sorted(uniq, key=lambda h: h[1]):          # least index first
    q, a, m, mu, k, S, L, thr = h[:8]
    g = gcd(mu, abs(k))
    if (mu // g, k // g) in shown:
        continue
    mu1, k1 = mu // g, abs(k) // g
    Pw = mu1 * k1 // (rad_of(mu1) * rad_of(k1))
    shown[(mu // g, k // g)] = Pw
    why = []
    if L >= 3 * log(3, 2) / 13 * a:
        why.append("APPROXIMATION (L=%d >= %.1f)" % (L, 3 * log(3, 2) / 13 * a))
    if Pw > 1:
        why.append("POWERFUL (P=%d)" % Pw)
    if not why:
        why.append("neither (P=%d, L=%d)" % (Pw, L))
    P("     3^%d %s %d = %d * 2^%d   q=%.4f   %s"
      % (a, "-" if k > 0 else "+", abs(k), mu, m, q, "; ".join(why)))
P("  primitive triples with a nontrivial powerful part: %d of %d (values %s)"
  % (sum(1 for v in shown.values() if v > 1), len(shown), sorted(shown.values())))
P("  by the *sharp* approximation rate L >= 0.36576a: %d of %d distinct (a,k) triples"
  % (sum(1 for h in uniq if h[6] >= 3 * log(3, 2) / 13 * h[1]), len(uniq)))
P("  by the ledger's sufficient condition 41L >= 15a+147: %d"
  % sum(1 for h in uniq if 41 * h[6] >= 15 * h[1] + 147))
P("  small terms |k| seen: %s" % sorted({abs(h[4]) for h in uniq}))
P("  max quality in the family: %.4f  (a=%d, m=%d, mu=%d, k=%+d)"
  % (uniq[0][0], uniq[0][1], uniq[0][2], uniq[0][3], uniq[0][4]))
exc = {1, 2, 3, 4, 7}
P("  indices carrying a hit: %s" % sorted(set(h[1] for h in uniq)))
P("  ... intersected with the exceptions {1,2,3,4,7}: %s"
  % sorted(set(h[1] for h in uniq) & exc))

# ===================================================================== [D]
P("")
P("=" * 74)
P("[D] forward ledger: 41L >= 15a + 147  ==>  rad^13 g^10 <= (3^a)^10")
P("=" * 74)
bad = 0
for a in range(1, 401):
    L = -(-(15 * a + 147) // 41)                       # least admissible block length
    if not (12 ** 13 * 3 ** (3 * a) <= 2 ** (13 * L)):
        bad += 1
        P("   CERTIFICATE FAILS a=%d L=%d" % (a, L))
P("  the certificate 12^13 * 3^(3a) <= 2^(13L) at the least admissible L,")
P("  a <= 400: %d failures  (this is `twelve_pow_le` at N=13, F=3a, G=13L)" % bad)
assert bad == 0
best = (0, 0, 0)
for a in range(1, 301):
    N = 3 ** a
    for m in range(1, int(a * log(3, 2)) + 2):
        r = min(N % 2 ** m, 2 ** m - N % 2 ** m)       # cres(3^a, m)
        L = m - max(r, 1).bit_length()
        if L > best[0]:
            best = (L, a, m)
P("  longest constant digit block of 3^a anywhere in the word, a <= 300:")
P("     L = %d at a = %d, m = %d;  required for quality 13/10: %.1f"
  % (best[0], best[1], best[2], 15 * best[1] / 41 + 147 / 41))
P("  -> the hypothesis of the forward ledger is met by NO index in range: blocks are")
P("     O(log a) in practice ([DD90]'s closing conjecture), the ledger needs 0.366a.")

# ===================================================================== [E]
P("")
P("=" * 74)
P("[E] backward split: rad^13 g^10 <= (3^a)^10  ==>  3^{3a}|k|^13 <= 2^{13m+13} S^13")
P("=" * 74)
bad = tested = 0
worstL = None
for a in range(1, 51):
    N = 3 ** a
    for m in range(1, int(a * log(3, 2)) + 2):
        for mu in (N // 2 ** m, N // 2 ** m + 1):
            if mu < 1 or N > 2 * (mu * 2 ** m):
                continue
            t = triple(a, m, mu)
            if t is None:
                continue
            k, g, R, C, q = t
            if R ** 13 * g ** 10 <= N ** 10:
                tested += 1
                S = -(-(mu * abs(k)) // R)                 # ceil(mu|k| / rad)
                if not (3 ** (3 * a) * abs(k) ** 13 <= 2 ** (13 * m + 13) * S ** 13):
                    bad += 1
                    P("   VIOLATION a=%d m=%d mu=%d" % (a, m, mu))
P("  tested %d triples of quality >= 13/10, violations %d" % (tested, bad))
assert bad == 0

# ===================================================================== [F]
P("")
P("=" * 74)
P("[F] the k = 1 family: 3^a = mu 2^m + 1 has a solution at *every* index")
P("=" * 74)
P("    a    m   mu odd   quality")
for a in (1, 2, 3, 5, 10, 20, 50, 100, 200):
    N = 3 ** a - 1
    m = 0
    t = N
    while t % 2 == 0:
        t //= 2
        m += 1
    R = rad_of(3, 2, t, 1)
    P("  %4d %4d   %-6s  %.4f" % (a, m, t % 2 == 1, log(3 ** a) / log(R)))
P("  -> fixing the small term k leaves an infinite family; its qualities tend to 1.")
P("  -> Bennett [Ben01] needs *both* mu and k fixed; the item names only k.")

# ===================================================================== [G]
P("")
P("=" * 74)
P("[G] Bennett pricing: pairs (mu,k) to be handled, against the true count")
P("=" * 74)
P("      a   log2 #(mu,k) with mu|k| <= 3^(10a/13)   corridor triples <= 1.585a+1")
for a in (10, 50, 100, 500, 1000):
    bits = 10 * a * log(3, 2) / 13
    P("   %5d          %12.1f                          %8d"
      % (a, bits, int(a * log(3, 2)) + 1))
P("  -> Bennett's uniformity is in the wrong variable: >= 2^(1.219a) applications,")
P("     each contributing at most 2 solutions, against a truth of O(a).")

# ===================================================================== [H]
P("")
P("=" * 74)
P("[H] why only the corridor is searchable")
P("=" * 74)
for a in (10, 50, 100):
    P("   a=%3d: corridor candidates (one mu per m)  = %4d" % (a, int(a * log(3, 2)) + 1))
    P("          quality-admissible (mu,k) region    ~ 2^%.1f" % (10 * a * log(3, 2) / 13))
P("  -> the census that settles Problem 1 below 10^6 (one candidate per index,")
P("     `pair_candidate_unique`) has no analogue for B6(iii)'s target set.")

# ===================================================================== [I]
P("")
P("=" * 74)
P("[I] the numerals of BB13/RigidCount.lean")
P("=" * 74)
assert 3 ** 10 - 29 * 2 ** 11 == -343 and 343 == 7 ** 3
P("  rigid_record_ten:  3^10 - 29*2^11 = %d = -7^3, gcd(29,343) = %d"
  % (3 ** 10 - 29 * 2 ** 11, gcd(29, 343)))
k, g, R, C, q = triple(10, 11, 29)
P("                     rad = %d, C = %d, quality = %.4f" % (R, C, q))
assert 3 ** 5 - 121 * 2 == 1
P("  rigid_k_one_five:  3^5 - 121*2^1 = %d" % (3 ** 5 - 121 * 2))
assert 2 ** 19 <= 3 ** 12 and 57 * 41 < 15 * 156 and 15 * 41 < 17 * 41
P("  slope order:       2^19 = %d <= 3^12 = %d;  57*41 = %d < 15*156 = %d < 17*156"
  % (2 ** 19, 3 ** 12, 57 * 41, 15 * 156))
assert 65 * 100 + 41 < 3 ** 76
P("  pricing at a=100:  corridor <= %d, pairs >= 3^76 = %.3e"
  % ((65 * 100 + 41) // 41, float(3 ** 76)))
assert 3 ** 41 <= 2 ** 65
P("  root certificate:  3^41 <= 2^65: OK")
P("")
P("all assertions passed.")
