#!/usr/bin/env python3
# (C) 2026 Ralf Stephan, in collaboration with Claude Code.
# Released under CC0 1.0 Universal (public-domain dedication).
# See https://creativecommons.org/publicdomain/zero/1.0/
"""
Strategy B6(ii) of plans/report3-BB13.html -- the two-log + LLL cap.

Target as stated in the report: "explicit two-log forms (Laurent-Mignotte-Nesterenko)
plus a 2x2 LLL step that uses the extra smallness |k_a| < 2^{0.585a-H} as a second
approximation, aimed at a finite cap on a for fibres >= 2".

Blocks:
  [A] the explicit LMN Cor. 2 bound for the actual form, evaluated
  [B] the rate -> fibre price list (what any exponential lower bound buys)
  [C] the reduction step: control experiment on a genuine two-log problem, then BB13
  [D] census of fibres >= 2 and the matching heuristic
  [E] the delta = 2^{-H} reformulation, verified
  [F] the span-surplus lead (archimedean half of Thm D's stratification)
  [G] the integer certificates the Lean file uses

Run: python3 BB13/b6ii_twolog.py
"""

import math
import time
from decimal import Decimal, getcontext

L2 = math.log(2.0)
L3 = math.log(3.0)
L32 = L3 - L2
THETA = L2 / L3
EPSSTAR = math.log(4.0 / 3.0) / L3

SEP = "=" * 78


def head(t):
    print("\n" + SEP)
    print(t)
    print(SEP)


# ---------------------------------------------------------------- frame helpers

def frame(N):
    """Yield (a, k_a, m_a, v2(m_a)) for a = 1..N, exactly, in O(N^2/64) word ops."""
    p = 1
    for a in range(1, N + 1):
        p *= 3                                   # p = 3^a
        mask = (1 << a) - 1
        r = p & mask                             # 3^a mod 2^a
        if r > (1 << (a - 1)):
            k = r - (1 << a)
        else:
            k = r
        m = (p - k) >> a
        v2 = (m & -m).bit_length() - 1
        yield a, k, m, v2


def is_exception(a, k):
    """|k_a| < (3/2)^a, i.e. 2^a |k| < 3^a."""
    return (abs(k) << a) < 3 ** a


def fibre_extra(a, k, v2):
    """min(v2(m_a), D(a)): the number of further exceptions above a on its line."""
    if not is_exception(a, k):
        return -1
    # largest H with 2^H |k| 2^a <= 3^a
    D = 0
    t = abs(k) << a
    if t == 0:
        D = 10 ** 9
    else:
        while (t << (D + 1)) <= 3 ** a:
            D += 1
    return min(v2, D)


# ------------------------------------------------------------------- [A] LMN

def block_A():
    head("[A]  Laurent-Mignotte-Nesterenko, Cor. 2, applied to the actual form")
    print("""form:  Lambda_a = 1*log(m_a) - a*log(3/2),   b1 = a, b2 = 1, D = 1
       alpha_1 = 3/2  (h = log 3),  alpha_2 = m_a  (h = log m_a ~ a*log(3/2))
       h'_i    = max(h(alpha_i), |log alpha_i|/D, 1/D)
       b'      = b1/(D h'_2) + b2/(D h'_1)
       log|Lambda| >= -24.34 D^4 (max{log b' + 0.14, 21/D, 1/2})^2 h'_1 h'_2""")
    h1 = max(L3, L32, 1.0)
    print(f"\n  h'_1 = {h1:.6f}   (= log 3; the 1/D floor is not active)")
    print("\n     a        log m_a        b'      log b'+0.14   max{.}^2      C(a)")
    print("  " + "-" * 72)
    lim = None
    for a in [10, 10 ** 2, 10 ** 3, 10 ** 6, 10 ** 12]:
        hm = a * L32 - math.log(2.0)          # log m_a, m_a = round((3/2)^a)
        h2 = max(hm, hm, 1.0)
        bp = a / h2 + 1.0 / h1
        inner = max(math.log(bp) + 0.14, 21.0, 0.5)
        C = 24.34 * inner ** 2 * h1 * h2 / a  # the bound is  log|Lambda| >= -C*a
        lim = C
        print(f"  {a:>7} {hm:>13.4f} {bp:>10.5f} {math.log(bp)+0.14:>12.5f}"
              f" {inner**2:>11.1f} {C:>11.2f}")
    Casym = 24.34 * 441.0 * h1 * L32
    print(f"\n  asymptotic slope  C_LMN = 24.34 * 21^2 * log3 * log(3/2) = {Casym:.4f}")
    print(f"  (b' -> {1/L32 + 1/h1:.5f} is BOUNDED, so log b'+0.14 = "
          f"{math.log(1/L32+1/h1)+0.14:.4f} never reaches 21/D = 21)")

    print("\n  what the bound says about |k_a|:   |k_a| >= 3^a * exp(-C*a)")
    print("  thresholds on C, in the same units:")
    rows = [
        ("log 3   = vacuity: below the trivial |k_a| >= 1", L3),
        ("log(3/1.1606) = [Zud07]'s rate 0.5803", L3 - math.log(2 * 0.5803)),
        ("log 2   = Problem 2 (no exception at all)", L2),
    ]
    for name, C in rows:
        print(f"    C = {C:>9.5f}   {name}")
    print(f"\n    C_LMN = {Casym:.4f}")
    for name, C in rows:
        print(f"      misses '{name.split('=')[0].strip()}' by a factor "
              f"{Casym / C:>8.1f}")
    print(f"\n  at a = 100 the LMN bound reads  |k_a| >= 3^100 * exp(-{Casym:.0f}*100)"
          f" = 10^{100*L3/math.log(10) - Casym*100/math.log(10):.0f}")
    print("  i.e. the published two-log bound contributes ZERO bits: it is far below")
    print("  the trivial |k_a| >= 1, which alone gives the corridor slope 0.58496.")
    return Casym


# ----------------------------------------------------- [B] the rate price list

def block_B():
    head("[B]  Price list: what an exponential rate buys for the fibre")
    print("""hypothesis   ||(3/2)^a|| >= c^a          (equivalently |k_a| >= (2c)^a)
tower depth  d  needs  2^d |k_a| 2^a <= 3^a
=>           2^d (4c)^a <= 3^a,  i.e.  d <= a * log2(3/(4c))""")
    print("\n      c            slope        source / meaning")
    print("  " + "-" * 68)
    rows = [
        (0.5, "trivial |k_a| >= 1  (corridor saturation)"),
        (0.57434, "[BL96p]-style repo constant"),
        (0.5769, "[Beu81]"),
        (0.5770, "[Hab03]"),
        (0.5803, "[Zud07]  -- the report's 0.371a row"),
        (0.60, "hypothetical"),
        (2.0 / 3.0, "hypothetical"),
        (0.70, "hypothetical"),
        (0.74, "hypothetical"),
        (0.75, "Problem 2 itself"),
    ]
    for c, src in rows:
        slope = math.log(3.0 / (4.0 * c)) / L2
        print(f"   {c:<10.5f}  {slope:>10.6f}   {src}")
    Casym = 24.34 * 441.0 * L3 * L32
    print(f"\n   LMN:  c = 3e^-C/2 = e^-{Casym - L32:.1f}   slope = C/log2 - 1 = "
          f"{Casym / L2 - 1.0:.1f}   (vacuous: >> 0.585)")
    print("""
  Reading.  The slope is POSITIVE for every c < 3/4 and vanishes exactly at
  c = 3/4.  So an exponential rate bounds d in terms of a; it never bounds a.
  Turned around (d >= 1 for a fibre of size >= 2):

        1 <= a * log2(3/(4c))    =>    a >= 1/log2(3/(4c)),

  a LOWER bound on a.  The excluded set is an initial segment, never a tail.""")
    print("\n      c            a excluded up to")
    print("  " + "-" * 40)
    for c, _ in rows[:-1]:
        slope = math.log(3.0 / (4.0 * c)) / L2
        print(f"   {c:<10.5f}  a < {1.0/slope:.4f}  (i.e. a <= {math.ceil(1.0/slope)-1})")
    print("\n  [Zud07] therefore excludes fibres >= 2 only for a <= 2 -- and the one")
    print("  known pair sits at a = 2, below its own effective threshold.")


# ------------------------------------------------- [C] the reduction step

def cf_convergents(x_dec, n):
    """Continued fraction convergents of a Decimal x."""
    out, p0, q0, p1, q1 = [], 1, 0, 0, 1
    y = x_dec
    for _ in range(n):
        ai = int(y)
        p0, p1 = p1, ai * p1 + p0
        q0, q1 = q1, ai * q1 + q0
        out.append((ai, p1, q1))
        frac = y - ai
        if frac == 0:
            break
        y = 1 / frac
    return out


def block_C():
    head("[C]  The reduction step: control experiment, then BB13")
    getcontext().prec = 80
    alpha = Decimal(3).ln() / Decimal(2).ln()          # log_2 3
    conv = cf_convergents(alpha, 45)

    print("C1.  CONTROL -- a genuine two-log problem:  |3^a - 2^b| <= 1000.")
    print("     Both exponents are free, so a*log_2(3) - b is a multiple of a FIXED")
    print("     irrational minus an integer, and continued fractions apply.")
    K = 1000
    A = 10 ** 15
    print(f"\n     start from the (notional) Baker bound  a <= {A:.0e}")
    t0 = time.time()
    for rnd in range(1, 6):
        qs = [q for (_, _, q) in conv if q <= A]
        q = qs[-1]
        qnext = next(qq for (_, _, qq) in conv if qq > A)
        lb = 1.0 / (qnext + q)                          # min_{a<=A} ||a alpha||
        # ||a alpha|| <= 2.05 K / 3^a  =>  3^a <= 2.05 K (q_{n+1}+q_n)
        newA = int(math.log(2.05 * K * (qnext + q)) / L3)
        print(f"     round {rnd}: q_n = {q}, q_(n+1) = {qnext},"
              f" ||a.alpha|| >= {lb:.3e}  =>  a <= {newA}")
        if newA >= A:
            break
        A = newA
    ctrl_ms = 1000 * (time.time() - t0)
    print(f"     converged in {ctrl_ms:.2f} ms; now enumerate a <= {A}:")
    sols = []
    for a in range(1, A + 1):
        p = 3 ** a
        b = p.bit_length() - 1
        for bb in (b, b + 1):
            if bb >= 1 and abs(p - 2 ** bb) <= K:
                sols.append((a, bb, p - 2 ** bb))
    print(f"       solutions: {sols}")
    print("     => the machinery works: 10^15 -> a <= %d in three rounds." % A)

    print("\nC2.  BB13 -- the pair condition.  3^a - m*2^a = k, |k| < (1/2)(3/2)^a,")
    print("     2 | m.  The unknown is a COEFFICIENT, not an exponent: the quantity")
    print("     to be reduced is ||(3/2)^a||, a geometric sequence mod 1, not a*alpha")
    print("     mod 1.  There is no fixed irrational, so there is no convergent to")
    print("     reduce against, and the 2x2 lattice degenerates:")
    print("\n     for each a the affine line {(m,k) : m 2^a + k = 3^a} meets the")
    print("     corridor |k| < (3/2)^a in EXACTLY ONE point (BB13.corridor_candidate_unique),")
    print("     so the 'lattice step' has one candidate per a and its verdict is")
    print("     precisely the census bit.  Measured:")
    N = 4000
    t0 = time.time()
    cnt_pts, cnt_pairs = 0, 0
    for a, k, m, v2 in frame(N):
        # candidates on the line inside the half-corridor with m even
        lo = -((3 ** a) >> (a + 1))
        n_here = 0
        if abs(k) <= abs(lo) and m % 2 == 0:
            n_here = 1
        cnt_pts += n_here
        if fibre_extra(a, k, v2) >= 1:
            cnt_pairs += 1
    dt = time.time() - t0
    print(f"       a <= {N}: candidate points found = {cnt_pts}, "
          f"actual fibres >= 2 = {cnt_pairs}   (equal: {cnt_pts == cnt_pairs})")
    print(f"       cost {dt:.2f} s, i.e. Theta(N^2) bit operations -- the census cost.")
    print(f"\n     C1 clears a <= 10^15 in {ctrl_ms:.2f} ms of lattice work.")
    print(f"     C2 clears a <= {N} in {dt:.2f} s and offers no lattice shortcut at all;")
    print("     a <= 10^15 would cost Theta(10^30) bit operations.")
    print("     The reduction step gains everything in C1 and a factor 1 in C2.")


# ------------------------------------------------- [D] census and heuristic

def block_D(N=20000):
    head(f"[D]  Census of fibres and the matching heuristic, a <= {N}")
    t0 = time.time()
    exc, fib = [], {}
    v2hist = {}
    small = []      # (a, x_a, v2) with x_a = ||(3/2)^a|| for the independence test
    for a, k, m, v2 in frame(N):
        if is_exception(a, k):
            exc.append(a)
            h = fibre_extra(a, k, v2)
            fib[a] = h
        v2hist[v2] = v2hist.get(v2, 0) + 1
        if a <= 4000:
            # log2 of ||(3/2)^a|| = |k_a|/2^a, as an integer exponent
            small.append((a, abs(k).bit_length() - a, v2))
    dt = time.time() - t0
    print(f"  exceptions: {exc}")
    print(f"  fibre extra (min(v2,D)) at each: "
          f"{ {a: fib[a] for a in exc} }")
    print(f"  fibres >= 2: {[a for a in exc if fib[a] >= 1]}")
    print(f"  scan time {dt:.1f} s")

    print("\n  heuristic (k_a equidistributed in (-2^{a-1}, 2^{a-1}], 2-adic bit fair):")
    print("      P(exception at a)   ~ 2 (3/4)^a          sum = %.3f, observed %d"
          % (sum(2 * 0.75 ** a for a in range(1, N + 1)), len(exc)))
    for H in (1, 2, 3):
        s = sum(2.0 ** (1 - 2 * H) * 0.75 ** a for a in range(1, N + 1))
        obs = len([a for a in exc if fib[a] >= H])
        print("      P(fibre >= %d at a)  ~ 2^%d (3/4)^a       sum = %.4f, observed %d"
              % (H + 1, 1 - 2 * H, s, obs))
    print("\n  v2(m_a) distribution over a <= %d (expect 2^-(j+1)):" % N)
    for j in sorted(v2hist)[:8]:
        print("      v2 = %d : %6d   (%.4f vs %.4f)"
              % (j, v2hist[j], v2hist[j] / N, 2.0 ** (-(j + 1))))
    print("      max v2 observed: %d" % max(v2hist))

    print("\n  independence of the two arms (a <= 4000): P(2|m_a | ||(3/2)^a|| < 2^-j)")
    for j in range(1, 11):
        sel = [(a, x, v) for (a, x, v) in small if x <= -j]
        if len(sel) < 30:
            continue
        p = sum(1 for (_, _, v) in sel if v >= 1) / len(sel)
        print("      j = %2d : %5d samples, P = %.4f" % (j, len(sel), p))
    print("      (fair-coin value 0.5 throughout: the 2-adic bit carries no")
    print("       archimedean information, so no lattice can couple the two arms)")
    return exc, fib


# -------------------------------------------- [E] the delta = 2^-H reformulation

def block_E(N=3000):
    head("[E]  The h = H+1 problem IS the Mahler problem at delta = 2^-H")
    print("""claim   2^H | m_a  and  |k_a| <= 2^-H (3/2)^a
        <=>  || 2^-H (3/2)^a || <= 2^-2H (3/4)^a       (a large enough)

reason  if 2^H | m_a then 3^a/2^{a+H} = (m_a/2^H) + k_a/2^{a+H} with the second
        term < 1/2, so the distance to the nearest integer is exactly
        |k_a|/2^{a+H}; and |k_a| <= 2^-H (3/2)^a turns that into 2^-2H (3/4)^a.
        If 2^H does not divide m_a the distance is >= 2^-H - small, far larger.""")
    bad_id, bad_iff, tested = 0, 0, 0
    for a, k, m, v2 in frame(N):
        for H in range(0, min(v2, 6) + 1):
            # identity ||3^a/2^{a+H}|| = |k_a|/2^{a+H} when 2^H | m_a
            if m % (1 << H) == 0:
                num = 3 ** a
                den = 1 << (a + H)
                r = num % den
                dist = min(r, den - r)
                if dist != abs(k):
                    bad_id += 1
                tested += 1
        # the equivalence itself, both directions, at every H <= 8
        for H in range(0, 9):
            lhs = (m % (1 << H) == 0) and ((abs(k) << (a + H)) <= (3 ** a) << a)
            lhs = (m % (1 << H) == 0) and ((abs(k) << H) * (1 << a) <= 3 ** a)
            num = 3 ** a
            den = 1 << (a + H)
            r = num % den
            dist = min(r, den - r)          # 2^{a+H} * ||3^a/2^{a+H}||
            rhs = (dist << (2 * H)) * (4 ** a) <= (3 ** a) * (1 << (a + H))
            if lhs != rhs and a >= 8:
                bad_iff += 1
    print(f"\n  identity  ||3^a/2^{{a+H}}|| = |k_a|/2^{{a+H}}  under 2^H | m_a:")
    print(f"     {tested} instances tested (a <= {N}), mismatches = {bad_id}")
    print(f"  equivalence of the two forms of 'fibre >= H+1', a in [8,{N}], H <= 8:")
    print(f"     mismatches = {bad_iff}")
    print("""
  Consequence.  Problem 2' for h = 2 is not a new problem: it is the SAME Mahler
  problem for the shifted point (3/2)^a/2.  The root's general-delta package
  (BB13/MahlerFrame.lean, BB13/MahlerCount.lean) applies verbatim -- num(delta)=1,
  so the degeneracy 'q^a | num delta' recorded there cannot occur -- and returns
  the same line cover at the same epsilon*.  Circular, as A3 predicted, but now
  exactly: no independent input is created by passing to pairs.""")


# ------------------------------------------------ [F] the span-surplus lead

def K_BE(eps):
    """BE08 Cor. 5.2 line constant."""
    u = 1.0 + 1.0 / eps
    return 2 ** 32 * u ** 3 * math.log(6.0) * math.log(u * math.log(6.0))


def block_F():
    head("[F]  LEAD (not implemented): Thm D uses only half of the span surplus")
    print("""BB13/SpanStrata.lean stratifies by span: a tower of span d = gamma*a over a
gives 2^d | m_a, sharpening the 2-adic exponent from theta to theta(1+gamma):

        theta + theta(1+gamma) + 1 = 2 + (eps* + gamma*theta).

But the same tower ALSO gives the archimedean surplus: k_{a+d} = 3^d k_a and
|k_{a+d}| < (3/2)^{a+d} force |k_a| < 2^-d (3/2)^a -- which is exactly what
BB13.tower_arms already proves.  In units of 3^a that sharpens f_inf from theta
to theta(1+gamma) as well, and the budget becomes

        theta(1+gamma) + theta(1+gamma) + 1 = 2 + (eps* + 2*gamma*theta),

since 2*theta + 1 = 2 + eps*.  The file's own caveat ("it must sharpen f_2, not
f_inf") is about a FIXED absolute surplus 2^-d, whose archimedean version runs
the wrong way; a span-PROPORTIONAL surplus 2^-{gamma a} = 3^-{gamma theta a}
has exactly the right shape.  Numbers:""")
    print(f"\n  theta = {THETA:.6f}, eps* = {EPSSTAR:.6f}, "
          f"2 theta + 1 - 2 = eps* : {abs(2*THETA+1-2-EPSSTAR):.2e}")
    print("\n   gamma     eps*+g.th    K(eps*+g.th)     eps*+2g.th   K(eps*+2g.th)"
          "    ratio")
    print("  " + "-" * 76)
    for g in (0.0, 0.125, 0.25, 0.375, 0.5, 0.58496):
        e1, e2 = EPSSTAR + g * THETA, EPSSTAR + 2 * g * THETA
        k1, k2 = K_BE(e1), K_BE(e2)
        print(f"  {g:<8.5f} {e1:>10.6f} {k1:>16.0f} {e2:>13.6f} {k2:>15.0f}"
              f" {k1/k2:>8.2f}")
    print(f"\n  K(eps*) = {K_BE(EPSSTAR):.0f}  (paper Thm A: 1856360182227)")
    print(f"  paper Thm D at gamma=1/4: {K_BE(EPSSTAR+0.25*THETA):.0f}"
          f"  (paper: 537048098048)")
    print(f"  doubled:                  {K_BE(EPSSTAR+0.5*THETA):.0f}"
          f"   -- a further factor {K_BE(EPSSTAR+0.25*THETA)/K_BE(EPSSTAR+0.5*THETA):.2f}")
    gmax = L32 / L2
    print(f"\n  exact identity at the confinement ceiling gamma_max = log(3/2)/log2:")
    print(f"     eps* + 2 gamma_max theta = (2 theta - 1) + 2(1 - theta) = 1"
          f"   [computed {EPSSTAR + 2*gmax*THETA:.12f}]")
    print("""
  NOT implemented here: it changes Thm D of the shipped paper and
  BB13/SpanStrata.lean, which is outside B6(ii).  Flagged for decision.""")


# ------------------------------- [H] B4's absorbed half: the input is height-only

def block_H(N=260):
    head("[H]  B4's absorbed measure half: the two-log input is HEIGHT-ONLY")
    print("""The LMN bound depends on k_a only through |Lambda| ~ |k_a|/3^a -- the height.
BB13.measure_iff_problem_two says a height-only 2-adic measure quantified over
the corridor |k| < (3/2)^a IS Problem 2, and BB13.corridor_saturation says the
free reach is M ~ 0.585a.  So the two-log route enters exactly the window that
B4 closed.  Measured: number of k in the corridor with 2^M | 3^a - k.""")
    print("\n     a      M=floor(.585a)   #k at M    #k at a    exception?")
    print("  " + "-" * 62)
    for a in [2, 3, 4, 7, 10, 20, 40, 80, 160, 256, N]:
        span = 3 ** a // 2 ** a                       # (3/2)^a, floor
        M = int(a * L32 / L2)
        cnt = []
        for MM in (M, a):
            r = pow(3, a, 1 << MM)
            # k = r mod 2^MM, shifted into the corridor
            c = 0
            kk = r - (1 << MM) * ((r + (1 << (MM - 1))) >> MM)
            step = 1 << MM
            t = kk
            while t > -span:
                t -= step
            t += step
            while t <= span:
                c += 1
                t += step
            cnt.append(c)
        exc = (abs((pow(3, a, 1 << a) + (1 << (a - 1))) % (1 << a)
                   - (1 << (a - 1))) << a) < 3 ** a
        print(f"  {a:>5} {M:>12} {cnt[0]:>12} {cnt[1]:>10}      {exc}")
    print("""
  At M = floor(0.585a) the corridor always contains a candidate (free reach);
  at M = a the count is 1 exactly for the exceptions.  Every bit between the two
  columns is the content of Problem 2, and no height-only input -- Pade, Baker,
  or two-log -- produces any of it.  This is B4's verdict, inherited.""")


# ------------------------------------------- [G] certificates used by the Lean file

def block_G():
    head("[G]  Integer certificates used by BB13/TwoLogCap.lean")
    print("exponent transfer:  from 2^d P^a <= Q^a and Q^p <= 2^q P^p  infer p*d <= q*a")
    print("   (raise the first to the p-th power, substitute, cancel P^{ap})")

    print("\n1. trivial rate (c = 1/2, i.e. |k_a| >= 1):  2^d 4^a <= 6^a")
    print(f"   certificate  6^17 <= 2^10 * 4^17  <=>  3^17 <= 2^27 : "
          f"{3**17 <= 2**27}   ({3**17} <= {2**27})")
    print(f"   ratio log2(3/2)*17 = {L32/L2*17:.5f} <= 10")
    print(f"   => 17 d <= 10 a, i.e. d <= {10/17:.6f} a  (corridor value 0.584963)")

    print("\n2. [Zud07] rate c = 5803/10000:   2^d * 23212^a <= 30000^a")
    print("   i.e. 2^d * (4*5803)^a <= (3*10000)^a;  reduced: 2^d 5803^a <= 7500^a")
    p, q = 35, 13
    cert = 7500 ** p <= 2 ** q * 5803 ** p
    print(f"   certificate  7500^{p} <= 2^{q} * 5803^{p} : {cert}")
    print(f"   ratio log2(7500/5803)*{p} = {math.log(7500/5803)/L2*p:.5f} <= {q}")
    print(f"   digits: 7500^{p} has {len(str(7500**p))}, 2^{q}*5803^{p} has "
          f"{len(str(2**q*5803**p))} -- norm_num range")
    print(f"   => 35 d <= 13 a, i.e. d <= {13/35:.6f} a   (report's 0.371a row: "
          f"exact value {math.log(3/(4*0.5803))/L2:.6f})")
    for pp, qq in ((16, 6), (27, 10), (35, 13), (62, 23)):
        r = math.log(7500 / 5803) / L2 * pp
        print(f"     (p,q) = ({pp:>3},{qq:>3}): {r:8.5f} <= {qq} ? "
              f"{r <= qq}   slope {qq/pp:.6f}")

    print("\n3. LMN slope vs the vacuity threshold:")
    C = 24.34 * 441.0 * L3 * L32
    print(f"   log 3 = {L3:.6f} < C_LMN = {C:.4f} :", L3 < C)
    print(f"   crude route: log(3/2) >= 1/3, so C_LMN >= 24.34*441/3 = "
          f"{24.34*441/3:.2f} * log 3 > log 3")
    print(f"   6800 * log 2 = {6800*L2:.2f} < C_LMN = {C:.2f} :", 6800 * L2 < C)


def main():
    print(SEP)
    print("B6(ii): the two-log + LLL cap -- evidence for plans/note-BB13-B6ii.html")
    print(SEP)
    block_A()
    block_B()
    block_C()
    block_D()
    block_E()
    block_F()
    block_H()
    block_G()
    print("\n" + SEP)
    print("done")
    print(SEP)


if __name__ == "__main__":
    main()
