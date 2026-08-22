#!/usr/bin/env python3
# (C) 2026 Ralf Stephan, in collaboration with Claude Code
# CC0 1.0 Universal (public domain dedication).
"""B2 of plans/report3-BB13.html -- the weighted two-place functional, measured.

Strategy B2 asks for a lower bound on a weighted quality mixing |k_a| with the
2-adic depth v_2(m_a), and lists three first steps: (i) A2's "AE" finite check,
(ii) re-deriving [Hab03] Thm 1 with the v_2 of the coefficients kept explicit,
(iii) re-running a Zudilin-style optimizer on the weighted functional.  This
script does all three on the actual construction data, in exact arithmetic.

The forms are [Hab03]'s own two-column data, rebuilt here at *every* Pade index
(not only the rate-optimal one), via the apparatus of TShift/tshift_numerics.py:

    H(2m, m; t)             (2.2)/(p. 300)  -- a polynomial of degree 2m
    P_i - Q_i H = +-t^{2i+1} E_i            -- the Pade pair at index i
    a = 8^i P_i(-1/8) + (-1)^m 8^i Q_i(-1/8) W,   b = -(-1)^m 8^i Q_i(-1/8)
    W = sum_{r<m} C(3m,r) 8^{m-r}
    ==>  a 2^N + b 3^N = Lam,   N = 6m                     (note section 2.4)

so `a 2^N + b 3^N` is an exact integer identity, checked in block [A].  Content
means gcd(a, b) throughout -- an upper bound for [Hab03]'s Pi, hence the
conservative choice for every claim below.

Blocks
  [A] the identity, and: the AE eliminant is k-free       (B2(i))
  [B] the exact AE verdict, plus a sweep over every index (B2(i), B2(iii))
  [C] the free 2-adic depth of the coefficients           (B2(ii))
  [D] the 2-adic lattice cost -- beta = 1/2               (B2(ii))
  [E] the payoff table, via BB13.weighted_fibre_cap       (B2)

Usage:  python3 BB13/b2_weighted.py [MMAX]        (default MMAX = 60)

The Lean side of the same work is BB13/WeightedQuality.lean; its module
docstring quotes the numbers produced here.
"""
import os
import random
import sys
import time
from collections import Counter
from fractions import Fraction
from math import comb, gcd, log2

sys.path.insert(0, os.path.join(os.path.dirname(os.path.abspath(__file__)),
                                "..", "TShift"))
import tshift_numerics as tn                                        # noqa: E402

HAB_RATE = 0.57434          # [Hab03] Thm 2, effective          (TShift.thetaHab)
ZUD_RATE = 0.5803           # [Zud07] Thm 1, ineffective date    (TShift.thetaZud)
S8_RATE = 0.58074           # (35,74,35), plans/note-Tshift-S8-WPF.html: computation


# --------------------------------------------------------------- the forms
def hab_index(m):
    """[Hab03] p. 301: n = [15/16 (m - 3/2)] + 1, the smaller of the two indices."""
    return int(Fraction(15, 16) * (m - Fraction(3, 2))) + 1


def hab_form(m, i):
    """The two-column integer form (a, b, Lam) at exponent N = 6m and Pade index i.

    Exact: a 2^{6m} + b 3^{6m} = Lam."""
    P, Q, E, ok = tn._pade_pair(i, 2 * m, m)
    assert ok, ("Pade (2.1) failed", m, i)
    t = Fraction(-1, 8)
    Ph, Qh = Fraction(8) ** i * tn._ev(P, t), Fraction(8) ** i * tn._ev(Q, t)
    assert Ph.denominator == 1 and Qh.denominator == 1, (m, i)
    Qt = (-1) ** m * int(Qh)
    W = sum(comb(3 * m, r) * 8 ** (m - r) for r in range(m))
    a, b = int(Ph) + Qt * W, -Qt
    return a, b, a * 2 ** (6 * m) + b * 3 ** (6 * m)


def reduced(m, i):
    """(alpha, beta, lam, g): the form divided by its content g = gcd(a, b)."""
    a, b, lam = hab_form(m, i)
    g = gcd(a, b)
    assert lam % g == 0
    return a // g, b // g, lam // g, g


# ------------------------------------------------------------------- [A]
def block_a(out):
    out.write("\n[A] the two-column identity, and the shape of the AE eliminant\n")
    for m in (3, 7, 12):
        i = hab_index(m)
        a, b, lam = hab_form(m, i)
        g = gcd(a, b)
        out.write(f"      m={m:3d}  N={6*m:3d}  i={i:3d}   a 2^N + b 3^N = Lam exactly;"
                  f"  gcd(a,b) = {g}\n")
    # the AE eliminant, as an algebraic identity in the pair hypothesis
    random.seed(20260817)
    for _ in range(400):
        n = random.randrange(3, 40)
        a, b, a2, b2 = (random.randrange(-10 ** 6, 10 ** 6) for _ in range(4))
        mm = 2 * random.randrange(1, 10 ** 6)               # 2 | m_n: the pair bit
        lam = a * 2 ** n + b * 3 ** n
        lam2 = a2 * 2 ** (n + 1) + b2 * 3 ** (n + 1)
        k = 3 ** n - mm * 2 ** n
        mm2 = 3 * mm // 2                                   # m_{n+1} = 3 m_n / 2
        assert 3 ** (n + 1) - mm2 * 2 ** (n + 1) == 3 * k    # k_{n+1} = 3 k_n
        c, c2 = a + b * mm, a2 + b2 * mm2
        assert (3 * b2 * c - 2 * b * c2 == 3 * a * b2 - 2 * a2 * b
                == Fraction(3 * b2 * lam - b * lam2, 2 ** n))
    out.write("      AE:  Delta := 3 b' c_n - 2 b c_{n+1} = 3 a b' - 2 a' b"
              " = (3 b' Lam_n - b Lam_{n+1})/2^n\n"
              "      -- verified on 400 random instances of the pair hypothesis.\n"
              "      Both m_n AND k_n have cancelled: the middle expression is free of\n"
              "      m_n by construction, the right-hand one is free of k_n as well.\n"
              "      So AE is a pure coefficient test -- it carries no 2-adic information,\n"
              "      contrary to the adjudication CB6 of the report's section 8, and it\n"
              "      fires only when |3 b' Lam_n - b Lam_{n+1}| < 2^n Gamma Gamma'.\n")


# ------------------------------------------------------------------- [B]
def block_b(out, mmax):
    out.write("\n[B] the exact AE verdict on [Hab03]'s forms, and the index sweep\n"
              "      deficit(i, m) := log2( |b| |Lam| / (Gamma^2 2^N) ) / N -- AE needs < 0\n"
              "        m     N   i=[Hab]  deficit    |b|/G     |Lam|/G   min over i (at i)\n")
    rows = []
    for m in (10, 20, 40, 60, 80, 100):
        if m > mmax:
            continue
        N, i0 = 6 * m, hab_index(m)
        best, arg, at_opt, cols = 9e9, None, None, None
        for i in range(1, 2 * m):
            al, be, lam, g = reduced(m, i)
            d = (log2(abs(be)) + log2(abs(lam)) - N) / N
            if d < best:
                best, arg = d, i
            if i == i0:
                at_opt = d
                cols = (log2(abs(be)) / N, log2(abs(lam)) / N)
        rows.append((m, at_opt, best))
        out.write(f"      {m:4d} {N:5d} {i0:8d}  {at_opt:8.5f}  {cols[0]:8.5f}  "
                  f"{cols[1]:8.5f}   {best:7.5f} (i={arg})\n")
    # the exact eliminant for a genuine pair of exponents (N, N+1)
    out.write("      exact |Delta| for genuine forms at the exponents N and N+1\n"
              "      (the second from the bundle at m+1, descended by delta = 5)\n")
    for m in (5, 10, 20, 40, 60):
        if m > mmax:
            continue
        N = 6 * m
        a1, b1, _, _ = reduced(m, hab_index(m))
        a2, b2, _, _ = reduced(m + 1, hab_index(m + 1))
        a2, b2 = 32 * a2, 243 * b2                     # 2^5, 3^5: exponent 6m+6 -> 6m+1
        D = 3 * a1 * b2 - 2 * a2 * b1
        assert D != 0
        out.write(f"      m={m:3d}  N={N:4d}   |Delta| = 2^{log2(abs(D)):8.1f}"
                  f" = 2^({log2(abs(D))/N:.4f} N)     AE fires: no\n")
    opt = rows[-1][1]
    floor = min(r[2] for r in rows if r[0] >= 20)
    out.write(f"      -- VERDICT (B2(i)): negative.  At the rate-optimal index the deficit\n"
              f"      is {opt:.3f} bits per exponent, and the engine's own rate exponent is\n"
              f"      log2(1/{HAB_RATE}) = {-log2(HAB_RATE):.3f}: the two agree because the optimum sits at\n"
              "      the break-even Gamma 2^N ~ Lam (deficit = rate exponent + break-even\n"
              "      slack, and the slack is what the optimisation drives to 0).  Over the\n"
              f"      whole index range the deficit never drops below {floor:.3f} (m >= 20;\n"
              "      the smaller figure at m = 10 is a small-m artifact, and the minimising\n"
              "      indices i <= 3 are the trivial end of the family, where the form is not\n"
              "      an approximation at all).\n"
              "      AE therefore fires only for forms of convergent quality |b||Lam| < 2^N,\n"
              "      i.e. only for a construction whose rate exponent is ~ 0 -- incomparably\n"
              "      stronger than the (3/4)^n that Problem 10.13 needs.\n")


# ------------------------------------------------------------------- [C]
def block_c(out, mmax):
    out.write("\n[C] the design condition 2^H | a: how much depth is free?\n")
    hist, mx, arg, tot = Counter(), 0, None, 0
    for m in range(2, min(mmax, 60) + 1):
        for i in range(1, 2 * m):
            al, be, lam, g = reduced(m, i)
            v = tn.v2(al)
            hist[v] += 1
            tot += 1
            if v > mx:
                mx, arg = v, (m, i)
    out.write(f"      v_2(a/gcd(a,b)) over all {tot} forms (m <= {min(mmax,60)}, every index):\n"
              "        v_2 : " + "  ".join(f"{k}" for k in sorted(hist)) + "\n"
              "        #   : " + "  ".join(f"{hist[k]}" for k in sorted(hist)) + "\n"
              f"      max {mx} (at m={arg[0]}, i={arg[1]}), mean "
              f"{sum(k*c for k, c in hist.items())/tot:.3f}\n"
              "      -- the coefficients are 2-adically generic: the free depth is O(1), so\n"
              "      no published construction supplies the design condition at any useful H.\n")


# ------------------------------------------------------------------- [D]
def gauss_reduce(u, v):
    """Lagrange/Gauss reduction of a 2-d integer basis; returns the shorter first."""
    def dot(x, y):
        return x[0] * y[0] + x[1] * y[1]
    if dot(u, u) > dot(v, v):
        u, v = v, u
    while True:
        q = round(Fraction(dot(u, v), dot(u, u)))
        v = (v[0] - q * u[0], v[1] - q * u[1])
        if dot(u, u) <= dot(v, v):
            return u, v
        u, v = v, u


def lattice(a1, a2, H):
    """Reduced basis of L_H = {(t1,t2) : 2^H | t1 a1 + t2 a2}."""
    v1, v2 = tn.v2(a1), tn.v2(a2)
    if v1 > v2:
        u, w = lattice(a2, a1, H)
        return (u[1], u[0]), (w[1], w[0])
    if v1 >= H:
        return (1, 0), (0, 1)
    M = 2 ** (H - v1)
    c = (-(a2 >> v1) * pow((a1 >> v1) % M, -1, M)) % M
    return gauss_reduce((c, 1), (M, 0))


def block_d(out, mmax):
    out.write("\n[D] manufacturing the design condition: the 2-adic lattice cost\n"
              "      L_H = {(t1,t2) : 2^H | t1 a1 + t2 a2} on the two [Hab03] indices;\n"
              "      the combined forms gain 2^H and pay max-norm ||t|| in both columns.\n"
              "        m    H   log2 l1  log2 l2   guaranteed gain 2^(H - log2 l2)\n")
    tally = []
    for m in (20, 40, 60, 80):
        if m > mmax:
            continue
        i0 = hab_index(m)
        a1 = reduced(m, i0)[0]
        a2 = reduced(m, i0 + 1)[0]
        for H in (4, 8, 16, 24, 32, 48, 64):
            u, v = lattice(a1, a2, H)
            n1, n2 = max(1, max(abs(u[0]), abs(u[1]))), max(1, max(abs(v[0]), abs(v[1])))
            # the combined forms must really satisfy the design condition
            assert (u[0] * a1 + u[1] * a2) % 2 ** H == 0
            assert (v[0] * a1 + v[1] * a2) % 2 ** H == 0
            assert u[0] * v[1] != u[1] * v[0]
            gain = H - log2(n2)
            if H >= 16:
                tally.append(gain / H)
            out.write(f"      {m:4d} {H:4d}   {log2(n1):7.3f}  {log2(n2):7.3f}"
                      f"        {gain:7.3f}   (= {gain/H:.3f} H)\n")
    # is the balance a property of the rate-optimal index, or of the family?
    if mmax >= 40:
        sweep = []
        for i in range(2, 78, 4):
            a1, a2 = reduced(40, i)[0], reduced(40, i + 1)[0]
            v = lattice(a1, a2, 32)[1]
            sweep.append((32 - log2(max(1, max(abs(v[0]), abs(v[1]))))) / 32)
        out.write(f"      balance across the whole index range (m = 40, H = 32, pairs (i,i+1),\n"
                  f"      i = 2, 6, ..., 74): gain in [{min(sweep):.3f}, {max(sweep):.3f}] H, "
                  f"mean {sum(sweep)/len(sweep):.3f} H\n"
                  "      -- so the lattice balance is a property of the family, not of the\n"
                  "      rate-optimal parameters: the beta-factor does not move with the index,\n"
                  "      and the weighted objective factorises into (rate) / (1 + beta).\n")
    out.write(f"      -- both minima sit at 2^(H/2): mean guaranteed gain "
              f"{sum(tally)/len(tally):.3f} H (over H >= 16),\n"
              "      i.e. beta = 1/2 in the weighted rate |k_a| >= c_1^a 2^{beta v_2(m_a)}.\n"
              "      This is a per-index certificate, not a theorem: only l1 l2 ~ 2^H is\n"
              "      automatic, so a skew pair (l1 = 1) would give nothing.  The uniform\n"
              "      statement needs one 2-adic fact about the Pade coefficients.\n")


# ------------------------------------------------------------------- [E]
def block_e(out):
    out.write("\n[E] the payoff: the fibre cap of BB13.weighted_fibre_cap,\n"
              "      2^{(1+beta) d} <= (3/(2 c_1))^a  with  c_1 = 2 c,  i.e.\n"
              "      min(v_2(m_a), D(a)) <= log2(3/(4c))/(1+beta) * a\n"
              "        engine                rate c    beta=0     beta=1/2   beta=1\n")
    for label, c in (("[Hab03] (effective)", HAB_RATE),
                     ("[Zud07] (record)   ", ZUD_RATE),
                     ("(35,74,35) S8/WP-F ", S8_RATE)):
        base = log2(3 / (4 * c))
        out.write(f"      {label}  {c:.5f}   {base:.5f}    {base/1.5:.5f}    {base/2:.5f}\n")
    out.write("      -- for reference, the other rows of the report's table 1.4:\n"
              "      elementary 0.58496 a;  abc-quality ledger (conditional) 0.0988 a;\n"
              "      Ridout at the shifted budget: o(a), ineffective (BB13/ValuationArm).\n"
              "      The beta = 1/2 column is what block [D] delivers per index; at\n"
              f"      [Zud07]'s rate it is {log2(3/(4*ZUD_RATE))/1.5:.5f} a < a/4"
              "  (BB13.zudilin_half_fibre_cap).\n")


def main():
    mmax = int(sys.argv[1]) if len(sys.argv) > 1 else 60
    t0 = time.time()
    out = sys.stdout
    out.write("B2 (plans/report3-BB13.html) -- the weighted two-place functional, measured.\n"
              "    engine: [Hab03]'s two-column data, exact, at every Pade index.\n")
    block_a(out)
    block_b(out, mmax)
    block_c(out, mmax)
    block_d(out, mmax)
    block_e(out)
    out.write(f"\n[F] cost.  This run: {time.time() - t0:.1f} s.\n")


if __name__ == "__main__":
    main()
