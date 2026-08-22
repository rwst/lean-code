#!/usr/bin/env python3
# (C) 2026 Ralf Stephan, in collaboration with Claude Code
# CC0 1.0 Universal (public domain dedication).
"""B3 of plans/report3-BB13.html -- Corvaja-Zannier-style valuation bounds, measured.

Strategy B3 proposes to run the C-Z machine (the gcd(a^n-1, b^n-1) < e^{eps n}
model, [BCZ03]) on the frame congruence 3^a = mu * 2^{a+w} + k_a, and asks for a
dichotomy: either the cofactor mu = m_a/2^w has a large {2,3}-smooth part (then
"C-Z applies and bounds w"), or mu is multiplicatively rough, in which case the
report proposes to feed two exceptions with matched mu's into Subspace (the BE08
elimination, "dead within a line", untested across lines).

This script measures both branches in exact arithmetic.  Notation throughout:

    m_a = round((3/2)^a) = (2*3^a + 2^a) >> (a+1)        exact
    k_a = 3^a - m_a 2^a                 (|k_a| <= 2^{a-1} always)
    w   = v_2(m_a),  mu_a = m_a / 2^w   (the odd part)

Blocks
  [A] per-prime valuations v_p(m_a): what "smooth part" there is      (branch 1)
  [B] the {2,3}-smooth census: which m_a are S-units                  (branch 1)
  [C] the free 3-adic coupling 3^{v_3(m_a)} | k_a, and the fibre cap  (branch 1)
  [D] the cross-line eliminant: identity, vanishing <=> linked        (branch 2)
  [E] the matching budget: how large is gcd(m_a, m_b) off a line      (branch 2)
  [F] the effective corner: what a two-term collapse would buy        (branch 1)

Usage:  python3 BB13/b3_smooth.py [NMAX] [PAIRMAX]   (defaults 20000, 400)

The Lean side of the same work is BB13/SmoothArm.lean; its module docstring
quotes the numbers produced here.
"""
import sys
import time
from math import gcd, log, log2

L2, L3 = log(2), log(3)


def mnum(a):
    """round((3/2)^a), exactly: m_a = (2*3^a + 2^a) / 2^{a+1}, floored."""
    return (2 * 3 ** a + 2 ** a) >> (a + 1)


def resid(a, m=None):
    """k_a = 3^a - m_a 2^a."""
    return 3 ** a - (mnum(a) if m is None else m) * 2 ** a


def vp(n, p):
    v = 0
    while n and n % p == 0:
        n //= p
        v += 1
    return v


def main(nmax, pairmax):
    t0 = time.time()
    ms = [None] + [mnum(a) for a in range(1, nmax + 1)]

    # ---------------------------------------------------------------- [A]
    print(f"[A] per-prime valuations of m_a = round((3/2)^a),  a <= {nmax}")
    print(f"    {'p':>4} {'max v_p':>8} {'at a':>8} {'max v_p/a':>11}"
          f" {'trivial ceiling':>16} {'mean':>7} {'1/(p-1)':>8}")
    for p in (2, 3, 5, 7, 11, 13):
        best, tot = (0, 1), 0
        for a in range(1, nmax + 1):
            v = vp(ms[a], p)
            tot += v
            if v > best[0]:
                best = (v, a)
        print(f"    {p:4d} {best[0]:8d} {best[1]:8d} {best[0]/best[1]:11.6f}"
              f" {log(1.5)/log(p):16.4f} {tot/nmax:7.4f} {1/(p-1):8.4f}")
    print("    the trivial ceiling is v_p(m_a) <= log_p m_a ~ a log(3/2)/log p;")
    print("    Ridout (BB13.smooth_arm_finite) replaces every row by o(a), ineffectively.")

    # ---------------------------------------------------------------- [B]
    print(f"\n[B] the {{2,3}}-smooth census, a <= {nmax}")
    smooth, worst = [], (0.0, 1)
    for a in range(1, nmax + 1):
        w, t = vp(ms[a], 2), vp(ms[a], 3)
        r = (w * L2 + t * L3) / (a * log(1.5))
        if r > worst[0]:
            worst = (r, a)
        if ms[a] == 2 ** w * 3 ** t:
            smooth.append(a)
    print(f"    m_a is {{2,3}}-smooth exactly for a in {smooth}"
          f"   (m_a = {[ms[a] for a in smooth]})")
    print(f"    max log(smooth part)/log(m_a) = {worst[0]:.5f} at a = {worst[1]}"
          f"  -- for a >= 6 the smooth part is a vanishing share")

    # ---------------------------------------------------------------- [C]
    print("\n[C] the free 3-adic coupling:  3^{v_3(m_a)} | k_a  (elementary, no hypothesis)")
    bad = [a for a in range(1, min(nmax, 600) + 1)
           if resid(a, ms[a]) % 3 ** vp(ms[a], 3) != 0]
    print(f"    v_3(m_a) <= v_3(k_a) fails at: {bad if bad else 'never'}"
          f"  (checked a <= {min(nmax, 600)})")
    v3max = max((vp(ms[a], 3), a) for a in range(1, nmax + 1))
    share = max((1.585 * vp(ms[a], 3) / (0.585 * a), a) for a in range(6, nmax + 1))
    print(f"    max v_3(m_a) = {v3max[0]} at a = {v3max[1]};"
          f"  the cap 2^d 3^{{v_3}} < (3/2)^a then reads d < {0.585*v3max[1]-1.585*v3max[0]:.0f}"
          f" (vs 0.585a = {0.585*v3max[1]:.0f})")
    print(f"    max share of the D-arm budget eaten by v_3 (a >= 6):"
          f" {share[0]:.5f} at a = {share[1]}")
    print("    so the weighted cap B2 wanted at the place 2 exists free at the place 3,")
    print("    and is empty in practice: v_3(m_a) is O(1)-sized while D(a) ~ 0.585a.")

    # ---------------------------------------------------------------- [D]
    print(f"\n[D] the cross-line eliminant, exact:  3^a (nu' 2^d - nu 3^d) ="
          f" nu' 2^d k_a - nu k_b")
    print("    (nu = m_a/g, nu' = m_b/g for any common divisor g; b = a + d)")
    checked = 0
    for (a, b) in [(11, 17), (23, 40), (57, 91), (100, 137), (287, 344)]:
        ma, mb, d = mnum(a), mnum(b), b - a
        g = gcd(ma, mb)
        nu, nup = ma // g, mb // g
        lhs = 3 ** a * (nup * 2 ** d - nu * 3 ** d)
        rhs = nup * 2 ** d * resid(a, ma) - nu * resid(b, mb)
        assert lhs == rhs, (a, b)
        checked += 1
        delta = nup * 2 ** d - nu * 3 ** d
        linked = (3 ** d * ma == 2 ** d * mb)
        print(f"    (a,b)=({a:3d},{b:3d}) d={d:3d} g={g:6d}"
              f"  Delta {'= 0' if delta == 0 else '!= 0'}   linked: {linked}"
              f"   identity ok")
    print(f"    {checked} identities verified;  Delta = 0  <=>  3^d m_a = 2^d m_b  <=> linked.")

    # ---------------------------------------------------------------- [E]
    print(f"\n[E] the matching budget: gcd(m_a, m_b) over pairs a < b <= {pairmax}")
    ml = ms[:pairmax + 1] if pairmax <= nmax else [None] + [mnum(a) for a in range(1, pairmax + 1)]
    odd = [None] + [ml[a] >> vp(ml[a], 2) for a in range(1, pairmax + 1)]
    linked, best, coprime, npairs, matched = 0, (1, 0, 0), 0, 0, []
    for a in range(1, pairmax + 1):
        for b in range(a + 1, pairmax + 1):
            npairs += 1
            d = b - a
            if odd[a] == odd[b]:
                matched.append((a, b))
            if 3 ** d * ml[a] == 2 ** d * ml[b]:
                linked += 1
                continue
            g = gcd(ml[a], ml[b])
            if g == 1:
                coprime += 1
            if g > best[0]:
                best = (g, a, b)
    g, a, b = best
    print(f"    pairs: {npairs};  linked (Delta = 0, no information): {linked}")
    print(f"    max gcd over unlinked pairs: g = {g} at (a,b) = ({a},{b}),"
          f" log_3 g = {log(g)/L3:.3f}")
    print(f"    the reach extension it buys: log_3(g)/a = {log(g)/L3/a:.6f} of a")
    print(f"    coprime share {coprime/(npairs-linked):.4f} (random-integer model 0.6079)")
    print(f"    pairs with equal odd parts (mu_a = mu_b, BB13.matched_separation):"
          f" {matched if matched else 'none'}")
    print("    extending the gap principle from eps* a to (eps* + delta) a needs g >= 3^{delta a}:")
    for aa in (100, 400, 1000):
        print(f"       delta = 0.01, a = {aa:4d}:  g >= 3^{0.01*aa:.0f}"
              f" = {3 ** int(0.01 * aa)}")
    print("    while the observed off-line gcds are the random-integer ones, i.e. O(1) in a.")

    # ---------------------------------------------------------------- [F]
    print("\n[F] the effective corner: m_a = 2^w 3^t collapses to |3^{a-t} - 2^{a+w}| < 3^{a-t} 2^{-a}")
    for z, name in ((0.5803, "Zudilin  [Zud07]"), (0.57434, "Habsieger [Hab03]")):
        c = log2(3 / (2 * z))
        print(f"    {name}: ||(3/2)^A|| > {z}^A  =>  a <= {c:.4f}(a - t)"
              f"  =>  t <= {1 - 1/c:.4f} a,  effective")
    print("    Rhin [Rhi87] |u0 + u1 log2 + u2 log3| >= H^{-13.3}  =>  A >= 2^{(a-O(1))/13.3}:")
    print("    an exactly-matched pair (mu_a = mu_b) is separated exponentially, not linearly.")
    print(f"\n({time.time() - t0:.1f} s)")


if __name__ == "__main__":
    main(int(sys.argv[1]) if len(sys.argv) > 1 else 20000,
         int(sys.argv[2]) if len(sys.argv) > 2 else 400)
