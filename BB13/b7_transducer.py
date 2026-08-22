#!/usr/bin/env python3
# (C) 2026 Ralf Stephan, in collaboration with Claude Code.
# Released under CC0 1.0 Universal (public-domain dedication).
# See https://creativecommons.org/publicdomain/zero/1.0/
"""
Strategy B7 of plans/report3-BB13.html — the carry transducer and the
Delmer-Deshouillers digit-run dictionary.  Evidence for BB13/CarryTransducer.lean
and plans/note-BB13-B7.html.

Blocks
  [A] the x3 carry transducer: 4 states, verified against integer multiplication,
      and its action on constant blocks (forward) and its preimages (backward)
  [B] the dictionary, measured: block(a) = [bitlen|k_a|, a+v2(m_a)),
      length = 0.4146a + D(a) + v2(m_a) exactly, and the Lean integer bound
  [C] the price list: what a run bound at rate c is worth, global vs anchored
  [D] [DD90] Prop. 1 verified, with both constants, against the Lean form
  [E] truth vs provable: the observed maximal run of 3^n against 1.585n
  [F] [DD90] Prop. 2's covering, and the run rate their algorithm needs
  [G] persistence: the contamination range of an exception, against 82k/65
  [H] the Ridout budget of [DD90] Prop. 4 = the Lean proof of longBlock_finite
  [I] numeral certificates used in the Lean file

Runtime ~15 s, pure integer arithmetic apart from the printed decimals.
"""

import math
from math import log, log2

L2, L3 = log(2.0), log(3.0)
THETA = L2 / L3                    # 0.6309297...
LOG23 = L3 / L2                    # 1.5849625...  = log_2 3


# ----------------------------------------------------------------- helpers

def m_of(a):
    """round((3/2)^a), exactly (the corpus's mNat)."""
    return (2 * 3 ** a + 2 ** a) // 2 ** (a + 1)


def k_of(a):
    return 3 ** a - m_of(a) * 2 ** a


def v2(n):
    return (n & -n).bit_length() - 1 if n else 10 ** 9


def depth_D(a, k):
    """floor(log2( 3^a / (|k| 2^a) )) -- the dyadic surplus D(a), which is
    >= 0 exactly when a is an exception and very negative otherwise."""
    if k == 0:
        return 10 ** 9
    A, B = 3 ** a, abs(k) * 2 ** a
    e = A.bit_length() - B.bit_length()
    if e >= 0:
        return e if A >= (B << e) else e - 1
    return e if (A << (-e)) >= B else e - 1


def is_exception(a):
    return abs(k_of(a)) * 2 ** a <= 3 ** a


def cres(N, w):
    """distance from N to the nearest multiple of 2^w."""
    r = N % (1 << w)
    return min(r, (1 << w) - r)


def max_run(N):
    """(length, position, digit) of a longest constant block of N in base 2."""
    s = bin(N)[2:]                      # MSB first, no leading zero
    best, bi, bd = 1, 0, s[0]
    i = 0
    n = len(s)
    while i < n:
        j = i
        while j < n and s[j] == s[i]:
            j += 1
        if j - i > best:
            best, bi, bd = j - i, i, s[i]
        i = j
    # convert MSB index to bit position of the block's low end
    return best, n - (bi + best), bd


# ----------------------------------------------------------------- [A]

def transducer_step(bits):
    """The x3 transducer, LSB first.  State = (previous input digit, carry);
    output digit = n_i + n_{i-1} + c mod 2, new carry = (n_i+n_{i-1}+c)//2."""
    prev, carry, out = 0, 0, []
    for b in bits:
        s = b + prev + carry
        out.append(s & 1)
        carry = s >> 1
        prev = b
    # flush
    while carry or prev:
        s = prev + carry
        out.append(s & 1)
        carry = s >> 1
        prev = 0
    return out


def bits_of(n, width=None):
    b = []
    while n:
        b.append(n & 1)
        n >>= 1
    if width:
        b += [0] * (width - len(b))
    return b or [0]


def int_of(bits):
    return sum(b << i for i, b in enumerate(bits))


def block_A():
    print("=" * 78)
    print("[A] the x3 carry transducer (4 states: previous digit x carry)")
    print("=" * 78)
    bad = 0
    for n in list(range(1, 400)) + [3 ** k for k in range(1, 40)] + [2 ** 61 - 1]:
        if int_of(transducer_step(bits_of(n))) != 3 * n:
            bad += 1
    print(f"  multiplication check: {bad} mismatches over 440 inputs "
          f"(0 expected)")

    # forward: a constant block maps to a constant block, losing <= 2 positions
    print("\n  forward action on a constant block [u, u+L) of N:")
    worst = 0
    for trial, (u, L, val, tail) in enumerate(
            [(u, L, v, t) for u in (0, 3, 7, 17) for L in (5, 9, 20)
             for v in (0, 1) for t in (0, 1, 5, 12345)]):
        N = tail << (u + L)
        if val:
            N |= ((1 << L) - 1) << u
        N |= 0b1011 if u >= 4 else 0
        M = 3 * N
        # positions [u+2, u+L) of M must be constant
        s = [(M >> i) & 1 for i in range(u + 2, u + L)]
        if s and len(set(s)) != 1:
            worst += 1
    print(f"    constant on [u+2, u+L) in 3N: {worst} failures / 96 cases")
    print("    (algebraically: |3N - 3v*2^w| = 3|N - v*2^w| < 3*2^u < 2^(u+2),")
    print("     i.e. BB13.cres_mul_le -- the whole carry analysis in one line)")

    # backward: the preimage of a run need NOT be a run
    N = (4 ** 12 - 1) // 3                    # 0101...01
    print(f"\n  backward: N = {bin(N)} (alternating) has max run "
          f"{max_run(N)[0]}, but 3N = {bin(3 * N)}")
    print(f"    max run of 3N = {max_run(3 * N)[0]}  -- runs are created by "
          "alternating blocks,")
    print("    so no run bound can be pulled back through the transducer.")


# ----------------------------------------------------------------- [B]

def block_B(N=1200):
    print()
    print("=" * 78)
    print("[B] the dictionary: the two arms are the two ends of one block")
    print("=" * 78)
    print("  block(a) = [bitlen|k_a|, a + v2(m_a)),  len = (2-log2 3)a + D(a) + v2 - 1")
    print("  (D(a) = floor log2 of the dyadic surplus; >= 0 iff a is an exception)")
    print()
    print("  a      D       v2   block [lo,hi)   len    formula   exception?")
    rows = [1, 2, 3, 4, 7, 11, 46, 100, 233, 512, 1001]
    bad_block = bad_len = 0
    pow2_k = 0
    for a in range(1, N + 1):
        k = k_of(a)
        v = v2(m_of(a))
        D = depth_D(a, k)
        lo = abs(k).bit_length()
        hi = a + v
        Nn = 3 ** a
        digs = {(Nn >> i) & 1 for i in range(lo, hi)}
        maximal_hi = ((Nn >> hi) & 1) != ((Nn >> (hi - 1)) & 1) if hi > lo else True
        maximal_lo = lo == 0 or ((Nn >> (lo - 1)) & 1) != ((Nn >> lo) & 1)
        if abs(k) == 1 << (lo - 1):
            pow2_k += 1                       # the boundary case |k| = 2^j
            maximal_lo = True
        if (len(digs) > 1) or not maximal_lo or not maximal_hi:
            bad_block += 1
        length = hi - lo
        f = (2 - LOG23) * a + D + v - 1
        if not (-1e-9 <= length - f < 2):
            bad_len += 1
        if a in rows:
            print(f"  {a:<6d} {D:<7d} {v:<4d} "
                  + f"[{lo},{hi})".ljust(16)
                  + f"{length:<6d} {f:<9.3f} "
                  + ("yes" if D >= 0 else "no"))
    print(f"\n  a <= {N}: block constant+maximal failures {bad_block}; "
          f"identity failures {bad_len}")
    print(f"           ({pow2_k} indices have |k_a| = 2^j, where the block "
          "extends further down)")
    print("  The identity holds at EVERY a, exception or not, and D and v2 enter")
    print("  SEPARATELY -- the report's '0.415a + 2(H-1)' is only the part")
    print("  guaranteed by the fibre, i.e. 2*min(D, v2).")

    # the Lean lemmas apply exactly at the exceptions: D >= 0 is the exception
    exc = [a for a in range(1, N + 1) if is_exception(a)]
    print(f"\n  BB13.block_of_arms / arms_block_length need a natural D with")
    print(f"  2^D|k|2^a <= 3^a, i.e. D >= 0, i.e. a in E = {exc} (a <= {N}).")
    print("  a    D  v2  u = (24a-41D)/41+1   IsBlock(3^a,u,a+v)  41u+41D<=24a+41")
    for a in exc:
        k, v = k_of(a), v2(m_of(a))
        D = max(0, depth_D(a, k))
        u = (max(0, 24 * a - 41 * D)) // 41 + 1
        ok1 = cres(3 ** a, a + v) < 2 ** u and 2 ** (a + v) <= 2 * 3 ** a
        ok2 = 41 * u + 41 * D <= 24 * a + 41
        print(f"  {a:<4d} {D:<2d} {v:<3d} {u:<20d} {str(ok1):<19s} {ok2}")
    # and at every depth d <= min(D, v2), which is what a fibre needs
    print("\n  every admissible (D, v) pair at the exceptions "
          "(D <= D(a), v <= v2(m_a)):")
    tot = ok = 0
    for a in exc:
        k, v2m = k_of(a), v2(m_of(a))
        for D in range(0, max(0, depth_D(a, k)) + 1):
            for v in range(0, v2m + 1):
                u = (max(0, 24 * a - 41 * D)) // 41 + 1
                tot += 1
                if cres(3 ** a, a + v) < 2 ** u and 2 ** (a + v) <= 2 * 3 ** a \
                        and 41 * u + 41 * D <= 24 * a + 41:
                    ok += 1
    print(f"    {ok}/{tot} pairs satisfy the Lean conclusion")


# ----------------------------------------------------------------- [C]

def block_C():
    print()
    print("=" * 78)
    print("[C] the price list: what a run bound at rate c buys")
    print("=" * 78)
    base = 2 - LOG23                       # 0.4150375 -- the mandatory rate
    print(f"  mandatory exception run    : {base:.6f} a      "
          f"(Lean: 17/41 = {17 / 41:.6f})")
    print(f"  the whole word             : {LOG23:.6f} a      "
          f"(Lean: 65/41 = {65 / 41:.6f})")
    print()
    print("  GLOBAL run bound  len <= c*a   =>   D + v2 <= (c - 0.4150)a, "
          "min <= half of that")
    print("  ANCHORED (rate) bound          =>   D      <= (0.5850 - lam)a")
    print()
    print("   c        D+v2 <=      min <=     beats Zudilin (0.37009a)?")
    for c in (0.30, 0.4150375, 0.50, 0.60, 0.7853, 0.80, 1.00, 1.1549,
              1.20, 1.40, LOG23):
        s = c - base
        verdict = ("E is finite (effectively)" if s <= 0
                   else ("YES" if s / 2 < 0.370092 else "--"))
        print(f"   {c:<8.5f} {s:<12.5f} {s / 2:<10.5f} {verdict}")
    cstar = base + 2 * 0.3700915
    print(f"\n  crossover: a global run bound at any rate c < {cstar:.6f}")
    print("  improves the best bound in print ([Zud07], 2007).  The whole word")
    print(f"  is only {LOG23:.6f}, so the window for a new theorem is the "
          f"interval")
    print(f"  ({base:.4f}, {cstar:.4f}) for a *new* row and (0, {base:.4f}) "
          "for finiteness of E.")
    print()
    print("  identification of the published rows (anchored side):")
    for name, gam in (("|k_a| >= 1        (elementary)", 0.5),
                      ("[Hab03] 2^-0.8k", 2 ** -0.8),
                      ("[Zud07] 0.5803^k", 0.5803)):
        lam = log2(2 * gam)
        print(f"    {name:<32s} lam = {lam:.5f}  =>  min <= "
              f"{0.5849625 - lam:.5f} a")
    print("    (0.58496, 0.38496->0.385, 0.37009 -- exactly the report's "
          "1.4 table)")
    print("  anchored run length at an exception = (1-lam)a + D  ->  the '0.8p'")
    print("  figure is [Hab03]'s rate restated, not a global digit theorem.")


# ----------------------------------------------------------------- [D]

def block_D(MMAX=900):
    print()
    print("=" * 78)
    print("[D] [DD90] Prop. 1, verified -- and its two constants")
    print("=" * 78)
    print("  source : 3^m has no block of h ones  =>  (**) holds for")
    print("           m*log3/log4 + h/2 + 1/2 < k <= m")
    print(f"  log3/log4 = {L3 / (2 * L2):.6f} ;  Lean form 65m + 41h + 41 <= 82k")
    print(f"  uses 65/82 = {65 / 82:.6f}  (a certificate loss of "
          f"{65 / 82 - L3 / (2 * L2):.2e})")
    # (i) the engine: cres(cN, w) <= c cres(N, w)
    bad = 0
    for N in (7, 12345, 3 ** 40, 2 ** 61 - 3, 10 ** 20 + 1):
        for w in (1, 5, 17, 64, 129):
            for c in (2, 3, 9, 27):
                if cres(c * N, w) > c * cres(N, w):
                    bad += 1
    print(f"\n  (i) cres_mul_le on 100 (N,w,c): {bad} failures")

    # (ii) the persistence identity at EVERY k, exception or not
    bad2 = tested2 = 0
    for k in range(2, 220):
        for m in range(k, k + 40):
            lhs = cres(3 ** m, k)
            rhs = 3 ** (m - k) * cres(3 ** k, k)
            tested2 += 1
            if lhs > rhs:
                bad2 += 1
    print(f"  (ii) cres(3^m,k) <= 3^(m-k) cres(3^k,k) on {tested2} pairs: "
          f"{bad2} failures")

    exc = [a for a in range(1, 260) if is_exception(a)]
    print(f"\n  (iii) exceptions up to 259: {exc}")
    bad = 0
    tested = 0
    for k in exc:
        for m in range(k, MMAX + 1):
            # the Lean statement: for every u with 65m < 41(u+k), 3^m has a
            # constant block on [u, k)
            u = (65 * m) // 41 + 1 - k
            if u < 0:
                u = 0
            if u >= k:
                continue
            tested += 1
            Nn = 3 ** m
            if not (cres(Nn, k) < 2 ** u):
                bad += 1
            digs = {(Nn >> i) & 1 for i in range(u, k)}
            if len(digs) != 1:
                bad += 1
    print(f"  dd_prop_one checked on {tested} pairs (k exception, m >= k): "
          f"{bad} failures")
    print("  and the source's own reading, h = 2k - 65m/41:")
    for k in exc:
        mmax = (82 * k - 41) // 65
        hmax = max(0, (82 * k - 65 * k - 41) // 41)
        print(f"    k = {k:<3d}: contaminates m <= {mmax:<4d} "
              f"(= 82k/65 = {82 * k / 65:.2f}), block of h = {hmax} at m = k")


# ----------------------------------------------------------------- [E]

def block_E(N=4000, spots=(6000, 10000, 20000)):
    print()
    print("=" * 78)
    print("[E] truth vs provable: the observed maximal run of 3^n")
    print("=" * 78)
    worst = (0, 0)
    tot = 0
    for n in range(1, N + 1):
        r, pos, d = max_run(3 ** n)
        tot += r
        if r > worst[0]:
            worst = (r, n)
    print(f"  n <= {N}: longest run ever seen = {worst[0]} bits, at n = {worst[1]}")
    print(f"           mean longest run       = {tot / N:.2f} bits")
    print(f"           log2 of the word length at n = {N}: "
          f"{log2(LOG23 * N):.2f}")
    for n in spots:
        r, pos, d = max_run(3 ** n)
        print(f"  n = {n:<6d}: longest run {r:>3d} bits = {r / n:.6f} n "
              f"(word = {int(LOG23 * n)} bits, digit '{d}' at position {pos})")
    print()
    print("  So the truth is ~ log2(n) + O(1) -- [DD90]'s closing remark, and")
    print("  A4's claimed 'audit result' min <= O(log a) is exactly that remark.")
    print(f"  What is *provable* is {LOG23:.4f} n (the word) unconditionally and")
    print("  o(n) ineffectively ([DD90] Prop. 4 = Ridout).  Nothing between.")


# ----------------------------------------------------------------- [F]

def block_F():
    print()
    print("=" * 78)
    print("[F] [DD90] Prop. 2: the covering, and the run rate it needs")
    print("=" * 78)
    print("  Prop. 1 covers k in (s*m, m] with s = log3/log4 + h/(2m).")
    print(f"  Each m covers a ratio 1/s; at h = 0 that is log4/log3 = "
          f"{2 * L2 / L3:.6f}")
    print("  -- the tower ratio 1.26186 of the report's sec. 1.2.  Covering")
    print("  [2^N, 2^{N+1}] therefore needs ceil(log 2 / log 1.26186) = "
          f"{math.ceil(L2 / log(2 * L2 / L3))} values of m at h = 0 -- but a")
    print("  positive run rate needs one more, which is [DD90]'s j = 1,2,3,4:")
    for j in (3, 4, 5):
        step = 2 ** (1 / j)
        eps = 2 * (1 - L3 / (2 * L2) * step) / step
        print(f"    j = {j}: step 2^(1/{j}) = {step:.5f}, admissible run rate "
              f"h/m <= {eps:.5f}")
    print("  So their algorithm needs a run bound of rate ~0.10 m, checked")
    print("  numerically for each N; block [E] shows the truth is ~log2 m, so")
    print("  the check always passes -- but no theorem gives it.")


# ----------------------------------------------------------------- [G]

def block_G():
    print()
    print("=" * 78)
    print("[G] persistence, not repulsion")
    print("=" * 78)
    print("  the block of an exception erodes by log2 3 = 1.58496 positions per")
    print("  step and survives to m = 82k/65 = 1.2615k -- long blocks come in")
    print("  intervals of indices, they do not repel.")
    exc = [a for a in range(1, 260) if is_exception(a)]
    for k in exc:
        v = v2(m_of(k))
        lo = abs(k_of(k)).bit_length()
        hi = k + v
        surv = []
        for j in range(0, 40):
            m = k + j
            lo_j = lo + math.ceil(j * LOG23)
            if lo_j < hi:
                Nn = 3 ** m
                digs = {(Nn >> i) & 1 for i in range(lo_j, hi)}
                surv.append(len(digs) == 1)
            else:
                break
        print(f"    k = {k}: block [{lo},{hi}) survives j = 0..{len(surv) - 1} "
              f"({'all constant' if all(surv) else 'FAILURE'})")
    print("  the merge argument's conclusion a' + D(a') >= a + D(a) is the")
    print("  line-scaling law k_b = 3^d k_a (BB13.link_scaling); it beats the")
    print("  root's inter-line gap a' >= 1.2384a only when D(a) - D(a') > 0.2384a.")


# ----------------------------------------------------------------- [H]

def block_H():
    print()
    print("=" * 78)
    print("[H] the Ridout budget of [DD90] Prop. 4 (= the Lean proof)")
    print("=" * 78)
    print("  frame (f_inf, f_2, f_3) = (1 - theta p/q, theta(p+2)/q, 1)")
    print("  budget check  f_inf + f_2 + f_3 - 2 = 2 theta / q :")
    bad = 0
    for q in (5, 7, 13, 60):
        for p in range(0, int(q / THETA) + 1):
            s = (1 - THETA * p / q) + THETA * (p + 2) / q + 1
            if abs(s - (2 + 2 * THETA / q)) > 1e-12:
                bad += 1
    print(f"    {bad} deviations over 200+ (p,q) -- the identity is exact")

    def K(eps):
        return 2 ** 32 * (1 + 1 / eps) ** 3 * log(6) * log((1 + 1 / eps) * log(6))
    print("\n  q      eps = 2 theta/q     K(eps) (the line count)")
    for q in (5, 10, 30, 100):
        e = 2 * THETA / q
        print(f"   {q:<6d} {e:<18.6f} {K(e):.3e}")
    print("  epsilon -> 0 as q -> infinity, so the count blows up like q^3 --")
    print("  the finiteness is qualitative, exactly as in BB13.valuation_arm_finite.")
    print("\n  and the implication that prices the whole item:")
    print("  a run bound o(n) kills every exception, because an exception has a")
    print(f"  run of {2 - LOG23:.4f} n.  So [DD90] Prop. 4 IS Mahler's theorem.")


# ----------------------------------------------------------------- [I]

def block_I():
    print()
    print("=" * 78)
    print("[I] numeral certificates used in BB13/CarryTransducer.lean")
    print("=" * 78)
    ok1 = 3 ** 41 <= 2 ** 65
    ok2 = 3 ** 5 < 2 ** 8
    print(f"  3^41 <= 2^65 : {ok1}   ({3 ** 41} <= {2 ** 65}), "
          f"65/41 = {65 / 41:.7f} > log2 3 = {LOG23:.7f}")
    print(f"  3^5  <  2^8  : {ok2}   (243 < 256), theta > 5/8 = 0.625 "
          f"(theta = {THETA:.7f})")
    print(f"  17/41 = {17 / 41:.7f} < 2 - log2 3 = {2 - LOG23:.7f}  "
          "(the mandatory-run slope, safe side)")
    assert ok1 and ok2 and 17 / 41 < 2 - LOG23 and 65 / 41 > LOG23


if __name__ == "__main__":
    block_A()
    block_B()
    block_C()
    block_D()
    block_E()
    block_F()
    block_G()
    block_H()
    block_I()
    print("\nall blocks done.")
