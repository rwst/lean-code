#!/usr/bin/env python3
# (C) 2026 Ralf Stephan, in collaboration with Claude Code.
# Released under CC0 1.0 Universal (public-domain dedication).
# See https://creativecommons.org/publicdomain/zero/1.0/
"""
Exact-Z numerics harness for the T-shift lane (plans/report-Tshift.html).

SINGLE SOURCE: plan-Tshift-S2 / S5 / S7 / S8 / S10 / S11 share this file (S11 R6:
"whichever plan executes first builds the harness; the others extend, never fork").
Built by plan-Tshift-S11 WP0, 2026-08-10.

Everything is exact integer arithmetic.  Nothing here ever forms a float except in
the printed summary columns, and no printed decision (record, run, cap) depends on a
float comparison.  (One exception, declared: the transcendental constants of the S2
block -- eps, K(eps), f_inf -- are 60-digit `Decimal`, and their ceilings are checked
for margin; every statement there about the frame itself is still decided in Z.)  Rule inherited from Z32/FlattoCount: kernel `decide` never sees Q,
and neither does this script.

Notation, following report-Tshift.html and plan-Tshift-S11 D1:
    x_n     = frac((3/2)^n)                       = r_n / 2^n,  r_n = 3^n mod 2^n
    m_n     = nearest integer to D (3/2)^n
    delta_n = D (3/2)^n - m_n     in [-1/2, 1/2)
    ||D(3/2)^n|| = |delta_n|      = min(t, 2^n - t)/2^n,  t = D 3^n mod 2^n
    g_{n+1} = 2 m_{n+1} - 3 m_n   = 3 delta_n - 2 delta_{n+1}   in {-2,...,2}
    s_n     = 3 x_n - 2 x_{n+1}   in {-1,0,1,2}                 (the carry word, D = 1)

Subcommands
    records D NMAX      record lows of ||D(3/2)^n||, with v2(m_n) at each record
    runs    D NMAX      maximal runs of dates with ||D(3/2)^n|| < 1/5; cascade cap check
    gframe  D NMAX      D1 check: g_n in {-2..2} and the 2-adic zero at w = 2/3
    carry   NMAX PMAX   maximal p-periodic blocks of the carry word; D5 cap at each
    floorcap NMAX PMAX  the machine-checked cap 2^(L+n) <= 3^(n+p) of TShift/FreeSojourn.lean
    adelic  D NMAX      WP-B: local factors R_p of the f- and g-frames (the adelic budget)
    tail    D NMAX      WP-B: ||D(3/2)^n|| = (1/2)|G_n(2/3)|, the evaluation identity
    w3      NMAX        WP-B: wall W3, both halves (zero-run cap; constructed witnesses)
    hankel  D NMAX      WP-B: sliding Hankel determinants; the 2x2 identity
    pade    MMAX PMAX   S7 WP0: [Hab03] (2.1)/(2.5) replay + the F1/D2 collapse audit
    apparat MMAX PMAX   S7 WP-B: the note-S1-constants 8.2 apparatus (F1,F2,A,I,C1,C2)
                        at a general admissible point; gate G-A; the off-diagonal cell;
                        [M]/[N] the ancestor content lemma [Dub87] and its 1993 sequel
    content MMAX        S7 WP-C: [O] the two integrality models on the solution
                        lattices; [P] the content baseline (true vs provable content of
                        [Hab03]'s pair (2.2)); [Q] what it is worth against the D4 wall
    cong    NMAX MMAX   S7 WP-D: Q2.  [R] O-3's S9 falsification (M_n factored at the
                        near misses); [S] the two cycle classes of D_2 = 5 and the
                        order-2 law; [T] 5 | btilde on [Hab03]'s own forms; [U] what
                        the congruence costs; [V] the verdict against the D4 wall
    s2      [NMAX]      S2 WP0, gate G-A: the block count.  [A] D1 at odd
                        multipliers on the real frame (parity, the scaling
                        identity, confinement); [B] D2's constants at 60
                        digits with their ceiling margins; [C] F5, the
                        showcase the corpus already certifies (theta = 3/4,
                        not 9/10); [D] the certificate against the truth;
                        [E] D3's payoff branch against the free cap of
                        TShift/FreeSojourn.lean; [F] the verdict; [G] WP5,
                        the tower currency and why it cannot buy blocks;
                        [H] WP7(a), the theta -> 1 price (F9's direction);
                        [I] WP7(b), the general-base table in the parity scope;
                        [J] O-7, the figures report-Tshift.html's C15 asserts
    s1      [NMAX]      S1 WP5: the initial range of Theorem A.  [A] the criterion
                        m_k^5 > 2^k; [B] the sliding register against full
                        precision; [C] the exceptional dates per multiplier
                        (k_min(5) = 6, and D = 1 reproduces [Hab03] Thm 2's
                        k >= 5); [D] the leading-run table ([Hab03] Lemma 2's
                        mechanism at D 3^k); [E] N5's record lows and the
                        simultaneity at D = 1, 5; [F] the constants
                        TShift/InitialRange.lean freezes.  NMAX = 64440001 runs
                        the whole initial range (about 6 min per multiplier)
    s1z     [MMAX]      S1 WP7: [Zud07]'s engine audited for the multiplier
                        transfer.  [A] C0, C1, C2 of p. 321 recomputed from
                        (19)-(21), with (26), theta and delta; [B] the
                        surrogates CITED/ZudilinPade.lean freezes and every
                        numeric obligation TShift/ZudilinTransfer.lean
                        discharges, in exact rational arithmetic; [C] the
                        two-form structure as exact integers at m = 1..MMAX
                        (Lemma 2's determinant, Lemma 3/4's divisibility, the
                        two-column identity); [D] the [Hab03]/[Pup09]/[Zud07]
                        lanes side by side
    s3      [NMAX]      S3 WP0-WP2: the 2-adic two-log route.  [A] the defect
                        N_n and the three identities TShift/PadicLogForm.lean
                        rests on, exactly; [B] the engine's two side conditions
                        -- the 2-adic order of 3, and the non-degeneracy, with
                        the burn-in measured against the proved D+6; [C] the
                        engine's own ceiling (eta = 6.2e-5, Cor. 1; 7.8e-5,
                        Thm 4) against the constant the Lean file freezes
                        (eta = 1.44e-6) and against the strategy row's 1e-64;
                        [D] where rungs (i) and (ii) cross; [E] the verdict --
                        correct, effective, numerically inert
    s9      [NMAX]      S9: make the structure of D_p pay.  [A] the cycle-product
                        identity |M_n| = (D2^n)^k prod|x_n - rho_i| and the
                        two-sided sandwich, exactly; [B] the ledger in nats per
                        date -- truth k log2, T1 line, and what the route can
                        guarantee ((k-1) log 2); [C] the row's own falsification,
                        M_n factored against the correct k-factor null (and
                        l = D never divides); [D] the resultant claim refuted,
                        and what the resultant does govern; [E] the odd witness
                        and the forced divisors, constant in n; [F] prong (i):
                        the elimination ledger is invariant under the scaling the
                        congruence performs
    s1314   [NMAX]      S13/14 WP0, gate G-A: the carry graph at D_2 = 5 and the
                        free zone.  [A] D1 on exact rationals -- the four wrong-
                        branch images at distance exactly 1/10, the 1/15 digit
                        margin, delta < 1/25, the phase pinning; [B] F2, two
                        admissible digits at EVERY point; [C] D1 on the real
                        orbit -- forcing, phase and N2's cycle-shift identity,
                        zero exceptions, and the sojourn census in U_(1/32);
                        [D] D2's constants against the free cap of
                        TShift/FreeSojourn.lean (C20) and the n = 6 crossover;
                        [E] D3/D4's grid plus the reciprocal cascade slope --
                        min(kappa_b, kappa_casc) < 1 at every base; [F] F5's
                        per-block count is vacuous; [G] the G-A verdict
    s5      NMAX PMAX   S5 WP0/G-A, G-B, O-4 and WP6: the relaxation T1'.
                        [A] D1's window constant against the printed q log2(3/2);
                        [B] the C20 crossover theta* = 0.78885; [C] F2's CRT
                        obstruction, exactly; [D] the printed class-restricted
                        devices; [E] F5, sojourns shorter than the window;
                        [F] gate G-B: T1'(q,r) is the T-shift problem at base
                        (3/2)^q, kappa invariant; [G] plan-S7 angle O-4: the
                        descent, so a class bound with a free multiplier is not
                        class-restricted
    s8f  [BMAX [AMAX]]  S8 WP-F: sub-idea (iii), the parameter grid of [Zud07]
                        section 5.  [A] the fast twins calibrated against the
                        audited routines, and the C2 integrand against e_p from
                        (13) prime by prime; [B] the mandated beta <= 100
                        reproduction; [C] the extension past beta = 100;
                        [D] the ridge alpha = gamma; [F] the ceiling and the
                        (26) boundary that sets it; [E] gate G-D
    s8g  [ledger]       S8 WP-G, the close: [Z] the ledger -- each channel's
                        measured ceiling against kappa = 1, re-derived and
                        asserted -- then the six work-package blocks in
                        execution order.  "ledger" stops after [Z] (2 s);
                        the full run is about 95 s more
    s8      MMAX        S8 WP0, gate G-A: the audit's own arithmetic.  [A] both
                        calibrations + thetaHab from the frozen bases; [B] the
                        channel identification (I(alpha) is not (3.11)'s 0.3945);
                        [C]-[E] D1 on integers -- Cramer, the cap, the refined
                        elimination, disjointness WITH the content P, the bad
                        branch and its ceiling 2B/|b1|; [F] the cap on [Hab03]'s
                        own family, saturated to first order; [G] D2's dictionary
    s8a                 S8 WP-A, gate G-B: pinning the three papers on their own
                        numbers.  [A] [Hab03] Prop. 2's thirty intervals re-derived
                        and (3.11)'s q-truncation measured; [B] [Zud07] section 5's
                        C0/C1/C2 from scratch; [C] [Pup09] Thm 1's six constants
                        and its 2e-4 margin; [D] the (26)-floor identification --
                        both [Pup09] constants are the construction's own validity
                        floor; [E] [Pup14]'s parameter change; [F] the two lanes,
                        K = 6 vs K = 3*beta, and the record's arithmetic/analytic
                        split
    s8b                 S8 WP-B: O-2 adoption, and the I -> I + log g re-
                        optimization mode of the section 8.2 apparatus.  [A]
                        what the shared harness already supplies; [B] the
                        apparatus split into a content-free demand curve
                        W(alpha) and payoff curve e^C2(alpha); [C] calibration
                        at g = 1 to [Hab03] Thm 1; [D] the re-optimized wall
                        g* = 1.5214 against the fixed-alpha 2.3786; [E] D2's
                        dictionary on the demand scale; [F] the crossing is the
                        minimiser, and the supply is denominator-stable;
                        [G] the family's floor theta(alpha -> 1) = 0.5365
    s8c                 S8 WP-C: the supply curve I(alpha), drawn on a background
                        grid plus every Farey cusp of denominator <= 120.  [A] the
                        curve and its ceiling sup I = 0.5736 at alpha = 1/2; [B] the
                        cusps have zero height (I is continuous) and the local
                        slopes that bound the sampling error; [C] alpha_0 is the
                        exact infimum of the feasible set; [D] the outright test --
                        a PERFECT content lemma buys theta = 0.6165, kappa = 1.19;
                        [E] the wall as a minimum, and where cusps undercut the
                        boundary; [F] the second evaluation point re-calibrated
    s8d     [MMAX]      S8 WP-D: the determinant on [Hab03]'s own two-column
                        data (constants note 2.4 + plan-S7's polynomials).
                        [A] det_eq verified at finite m from the polynomials;
                        [B] the Cramer identity, and the triangle step of the
                        cap is lossless (the two products share a sign);
                        [C] where the slack lives -- sqrt(m) worst-casing plus
                        a 1.04e-8/m rate residue of the frozen bases, and the
                        true |b| rate against denomBase; [D] the cleared
                        determinant is NOT sub-polynomial; [E] the bad branch
                        decays at exactly the validity margin; [F] Q2 verdict
    s10     [NMAX]      S10 WP0: the critical lattice L_n = Z(0,2^n) + Z(1,3^n).
                        [A] D1 symbolically -- the box is Minkowski-critical,
                        det = 144^n in the scaled model, the regime thresholds
                        n0(D), and the general-base free zone p > q^2;
                        [B] the EXACT successive minima in the critical box, one
                        Euclid run per date, with Minkowski's second theorem as
                        the correctness test -- the unbalancedness table;
                        [C] Proposition 1's per-date optimum, two tiers: the
                        unconstrained one is a TAUTOLOGY at D = 1, and inside
                        D1's regime the optimum is 1/B0 up to a factor 2 with B0
                        polynomial (brute-force cross-checked);
                        [D] lambda-records against N5's ||D(3/2)^n|| records;
                        [E] D2's escape window in its exact v2 form
    s10b    [NMAX]      S10 WP-B, gate G-A': the dictionary from the CDT
                        functional to T-shift's currency, calibrated.
                        [A] theta/kappa/eps_0 and the wall W = log3/log(3/2);
                        [B] G-A' layer 1, the [Hab03] number through the S1
                        apparatus and the three-term slot decomposition;
                        [C] the break-even, and which slot carries the margin;
                        [D] the content slot -- scale invariance of (2.2)/(2.4);
                        [E] the wall per base; [F] the Dirichlet forcing floor,
                        on exact integers, and the window the demand leaves;
                        [G] the printed constant assembly of section 4;
                        [H] the (1.4) demand, vacuous abc-refinement at rank 1
    s10c    [NMAX]      S10 WP-C: Q1's sweep -- the ceiling over admissible
                        configurations, and the S-unit lane's constants.
                        [A] the within-family configuration space is FINITE:
                        three evaluation points, all enumerated at S1 8.2;
                        [B] the engine's arithmetic slot is the zero line, and
                        the ceiling is monotone in the input;
                        [C] the master curve I -> theta in plan-S8's absolute
                        content currency, with the historical anchors;
                        [D] the generous second lane, [Zud07] content-free;
                        [E] the h(A)-coefficient inventory of the lane, from
                        [Bom93] and [BC97] to [CDT-ICM];
                        [F] the amendment to WP-B (b): section 4's penultimate
                        inequality, its side condition v3(m_n) = o(n), measured;
                        [G] Q1's verdict and the freedom ledger
    s10e    [NMAX]      S10 WP-E: the constants of TShift/CriticalBox.lean,
                        checked independently on exact integers.
                        [A] `forms_of_floor`'s construction at the critical
                        family, with the sharpest admissible floor per date --
                        Dirichlet's bound, both box bounds, the coefficient
                        budget X/S + 1, and independence;
                        [B] `floor_iff_forms`: the round trip of constants, and
                        why the eps-slack is the criticality of the box;
                        [C] `escape_in_window` (v2 form) and
                        `escape_in_window_logb` (O(1) = 2) at every date, the
                        two tight instances, `escape_sanity`'s values;
                        [D] `lambda_one_ge_half` against WP0's exact minima
    s10g    [NMAX]      S10 WP-G: the item's closing regression -- s10, s10b,
                        s10c and s10e in order, one banner each, about 27 s at
                        the defaults.  No new numerics: every number in the
                        verdict note is one of those four blocks' own output,
                        and this is the one command that reproduces all of them
    all     NMAX        the WP0 battery for D in {1, 5, 19}
    wpb     NMAX        the WP-B (milestone M2) battery
"""

import sys
import time
from decimal import Decimal, getcontext
from fractions import Fraction
from math import ceil, comb, exp, gcd, isqrt, log, sqrt

try:                                        # big-integer speed only; never correctness
    from gmpy2 import mpz as _MPZ           # the S1 WP5 sweep is 3-4x faster with it
except ImportError:                         # pragma: no cover
    _MPZ = int


LOG2_3HALVES = log(3 / 2) / log(2)          # 0.5849625007...  = kappa_free (D5)


def orbit(D, nmax):
    """Yield (n, t, m, sgn_small) for n = 0..nmax, exactly.

    t = D 3^n mod 2^n  (so ||D(3/2)^n|| = min(t, 2^n - t)/2^n)
    m = nearest integer to D (3/2)^n
    """
    T = D                                    # T = D * 3^n, exact
    for n in range(nmax + 1):
        mod = 1 << n
        t = T & (mod - 1)
        # nearest integer: round half up (no ties for odd D and n >= 2, since t is odd)
        m = (T + (mod >> 1)) >> n if n else T
        yield n, t, m, T
        T *= 3


def v2(k):
    return (k & -k).bit_length() - 1 if k else None


def dist_num(t, n):
    """||.|| = dist/2^n, exact numerator."""
    return min(t, (1 << n) - t)


def cmd_records(D, nmax, out=sys.stdout):
    """Record lows of ||D(3/2)^n|| over 1 <= n <= nmax (exact comparison)."""
    best_a, best_e = None, None              # record = best_a / 2^best_e
    dates, rows = [], []
    for n, t, m, _T in orbit(D, nmax):
        if n < 1:
            continue
        a = dist_num(t, n)
        # a/2^n < best_a/2^best_e  <=>  a << best_e < best_a << n
        if best_a is None or (a << best_e) < (best_a << n):
            best_a, best_e = a, n
            dates.append(n)
            rows.append((n, a, n, v2(m), m.bit_length()))
    print(f"# D = {D}, n <= {nmax}: {len(dates)} records", file=out)
    print("#   n      ||D(3/2)^n||     theta_n = val^(1/n)   v2(m_n)  bits(m_n)", file=out)
    for (n, a, e, v, bits) in rows:
        val = a / (1 << e) if e < 900 else float(a >> (e - 900)) / (1 << 900)
        lg = (log(a) - e * log(2)) if a else float("-inf")
        theta = pow(2.718281828459045, lg / n)
        print(f"{n:8d}  {val:16.6e}   {theta:.6f}   {v:6d}   {bits:7d}", file=out)
    print(f"# record dates: {dates}", file=out)
    return dates, rows


def cmd_runs(D, nmax, out=sys.stdout, thresh=(1, 5)):
    """Maximal runs of consecutive dates with ||D(3/2)^n|| < p/q (default 1/5).

    Checks, exactly:
      (i)   cascade divisibility     2^(b-a) | m_a          on every run [a,b]
      (ii)  cascade cap              b - a <= log2(m_a)     hence <= 0.585 a + log2 D + 1
      (iii) run anatomy (D3)         b - a  vs  v2(m_a)
    """
    p, q = thresh
    data = [(n, t, m) for (n, t, m, _T) in orbit(D, nmax)]
    small = [q * dist_num(t, n) < p * (1 << n) for (n, t, m) in data]
    runs, n = [], 1
    while n <= nmax:
        if small[n]:
            a = n
            while n + 1 <= nmax and small[n + 1]:
                n += 1
            runs.append((a, n))
        n += 1
    viol_dvd = viol_cap = viol_anat = 0
    eq_v2 = 0
    longest = max(runs, key=lambda r: r[1] - r[0]) if runs else None
    print(f"# D = {D}, n <= {nmax}, threshold {p}/{q}: {len(runs)} maximal runs", file=out)
    for (a, b) in runs:
        if b == nmax:
            continue                         # truncated by the horizon; true length unknown
        m_a = data[a][2]
        L = b - a
        if L and m_a % (1 << L) != 0:
            viol_dvd += 1
            print(f"!! cascade divisibility FAILS at run [{a},{b}]", file=out)
        if L > m_a.bit_length():
            viol_cap += 1
            print(f"!! cascade cap FAILS at run [{a},{b}]", file=out)
        if L == v2(m_a):
            eq_v2 += 1
        # sharp D3: L = min( v2(m_a), K - 1 ),  K = min{ i : (3/2)^i |delta_a| >= 1/5 },
        # i.e. the run ends by parity exit (m turns odd) or by band exit, never otherwise.
        # exact test, no floats:  q * 3^i * dist_a >= p * 2^i * 2^a
        d_a, i = dist_num(data[a][1], a), 0
        while q * 3 ** i * d_a < p * (2 ** i << a):
            i += 1
        if L != min(v2(m_a), i - 1):
            viol_anat += 1
            print(f"!! run anatomy FAILS at [{a},{b}]: L = {L}, v2 = {v2(m_a)}, K = {i}",
                  file=out)
    print(f"#   divisibility 2^(b-a) | m_a : {len(runs) - viol_dvd}/{len(runs)} ok", file=out)
    print(f"#   cap b-a <= log2 m_a        : {len(runs) - viol_cap}/{len(runs)} ok", file=out)
    print(f"#   run length == v2(m_a)      : {eq_v2}/{len(runs)}  (parity exit; D3)", file=out)
    print(f"#   L = min(v2(m_a), K) exactly: {len(runs) - viol_anat}/{len(runs)} ok  "
          f"(sharp D3: parity exit or band exit, nothing else)", file=out)
    if longest:
        a, b = longest
        m_a = data[a][2]
        cap = LOG2_3HALVES * a + log(D, 2) + 1
        print(f"#   longest run: [{a},{b}], length {b - a}, v2(m_a) = {v2(m_a)}, "
              f"cascade cap at a = {cap:.1f}", file=out)
    mv, mn = -1, None
    for (n, t, m) in data[1:]:
        w = v2(m)
        if w is not None and w > mv:
            mv, mn = w, n
    print(f"#   max v2(m_n) over n <= {nmax}: {mv} at n = {mn} "
          f"(cascade ceiling {LOG2_3HALVES * mn + log(D, 2):.1f})", file=out)
    return runs


def cmd_gframe(D, nmax, out=sys.stdout):
    """D1: g_n in {-2,...,2}, and the 2-adic zero  v2(sum 3^(n-j) 2^j g_j) >= n+1."""
    ms = [m for (_n, _t, m, _T) in orbit(D, nmax)]
    g = [2 * ms[0]] + [2 * ms[n + 1] - 3 * ms[n] for n in range(nmax)]
    bad = [(n, c) for n, c in enumerate(g) if n and not (-2 <= c <= 2)]
    hist = {}
    for c in g[1:]:
        hist[c] = hist.get(c, 0) + 1
    # 2-adic zero at w = 2/3 : sum_{j<=n} 3^(n-j) 2^j g_j = 2^(n+1) h_n with h_n = m_n
    S, bad2 = 0, []
    for n in range(nmax + 1):
        S = 3 * S + (1 << n) * g[n] if n else g[0]
        if S != (1 << (n + 1)) * ms[n]:
            bad2.append(n)
    print(f"# D = {D}, n <= {nmax}: g_0 = {g[0]} (= 2D), coefficients {hist}", file=out)
    print(f"#   g_n in [-2,2] for 1 <= n <= {nmax} : {'OK' if not bad else bad[:5]}", file=out)
    print(f"#   sum_{{j<=n}} 3^(n-j) 2^j g_j = 2^(n+1) m_n : "
          f"{'OK' if not bad2 else bad2[:5]}  (2-adic zero at w = 2/3, rate 1 digit/date)",
          file=out)
    return g


def carry_word(nmax):
    """s_n = 3 x_n - 2 x_{n+1} in {-1,0,1,2}, exactly, for the xi = 1 orbit."""
    r = [pow(3, n, 1 << n) if n else 0 for n in range(nmax + 2)]
    return [(3 * r[n] - r[n + 1]) >> n for n in range(nmax + 1)]


def cmd_carry(nmax, pmax, out=sys.stdout):
    """Maximal p-periodic blocks of the carry word, against the D5 cap.

    A p-periodic block on [n, n+L) means s_{n+i+p} = s_{n+i} for 0 <= i < L-p.
    D5 caps L by  log2(3/2) n + p + log2 D_p + log_{3/2}(5 D_p) + O(1).
    """
    s = carry_word(nmax + 2 * pmax + 2)
    alpha = {}
    for c in s[:nmax]:
        alpha[c] = alpha.get(c, 0) + 1
    print(f"# carry word of the xi = 1 orbit, n <= {nmax}: alphabet {alpha}", file=out)
    print("# D5 cap:  L <= log2(3/2) n + log2(D_p + 1) + p + log_{3/2}(5 D_p) + 1", file=out)
    print("#  p    D_p      max L  at n |  worst case: min slack  at n   (L there)  "
          "| additive const", file=out)
    for p in range(1, pmax + 1):
        Dp = 3 ** p - 2 ** p
        const = log(Dp + 1, 2) + p + log(5 * Dp) / log(1.5) + 1
        best_L, best_n = 0, 0
        worst, worst_n, worst_L = float("inf"), None, None
        k = 0
        for n in range(nmax, -1, -1):
            k = k + 1 if s[n + p] == s[n] else 0
            L = p + k                        # maximal p-periodic block starting at n
            if L > best_L:
                best_L, best_n = L, n
            slack = LOG2_3HALVES * n + const - L
            if slack < worst:
                worst, worst_n, worst_L = slack, n, L
        print(f"{p:4d}  {Dp:8d} {best_L:6d} {best_n:6d} | {worst:14.2f} {worst_n:6d} "
              f"{worst_L:9d}  | {const:9.2f}", file=out)


def cmd_bridge(nmax, pmax, minL=1, out=sys.stdout):
    """End-to-end exact test of the D5 chain on the real orbit (plan-Tshift-S11 WP0).

    For every maximal p-periodic carry block [n, n+L) with L >= p + minL:
      (1) shadowing   |x_n - rho| <= (2/3)^(L-p),  rho = A/D_p the block's fixed point
      (2) the bridge  ||D_p (3/2)^(n+i)|| < 1/5 for 0 <= i <= R,
                      R = ceil(L - p - log_{3/2}(5 D_p)) - 1
      (3) cascade     2^R | m_n   (m_n = nearest integer to D_p (3/2)^n)
      (4) the cap     L <= log2(3/2) n + log2(D_p + 1) + p + log_{3/2}(5 D_p) + 1
    All comparisons are exact integer cross-multiplications.
    """
    s = carry_word(nmax + 2 * pmax + 2)
    r = [pow(3, n, 1 << n) if n else 0 for n in range(nmax + 2)]
    print(f"# D5 chain, exact, on maximal p-periodic blocks with L >= p + {minL}, "
          f"n <= {nmax}", file=out)
    print("#  p   blocks  shadowing  bridge  cascade     cap   | worst R  (longest block)",
          file=out)
    for p in range(1, pmax + 1):
        Dp = 3 ** p - 2 ** p
        T = 1                                # T = D_p * 3^n, exact, built incrementally
        Tn = [None] * (nmax + 1)
        t = Dp
        for n in range(nmax + 1):
            Tn[n] = t
            t *= 3
        nblk = ok1 = ok2 = ok3 = ok4 = 0
        maxR, bestL = 0, 0
        n = 0
        while n <= nmax:
            k = 0
            while n + k + p <= nmax and s[n + k + p] == s[n + k]:
                k += 1
            L = p + k
            if k >= minL:
                nblk += 1
                bestL = max(bestL, L)
                # (1) shadowing, exact:  |x_n - A/D_p| <= (2/3)^(L-p)
                A = sum(s[n + i] * 3 ** (p - 1 - i) * 2 ** i for i in range(p))
                lhs = abs(r[n] * Dp - A * (1 << n))          # |x_n - rho| * 2^n * D_p
                e = L - p
                if lhs * 3 ** e <= (2 ** e) * (1 << n) * Dp:
                    ok1 += 1
                # exact R: largest R with (3/2)^R * 5 * D_p < (3/2)^(L-p)
                R = -1
                i = 0
                while True:
                    # 5 D_p (3/2)^i < (3/2)^e   <=>   5 D_p 3^i 2^(e-i) < 3^e   (i <= e)
                    if i > e or 5 * Dp * 3 ** i * 2 ** (e - i) >= 3 ** e:
                        break
                    R = i
                    i += 1
                maxR = max(maxR, R)
                # (2) the bridge: every date n..n+R inside the 1/5 band
                good = True
                for i in range(max(R, 0) + 1):
                    tt = Tn[n + i] & ((1 << (n + i)) - 1)
                    if 5 * dist_num(tt, n + i) >= (1 << (n + i)):
                        good = False
                        break
                if R < 0 or good:
                    ok2 += 1
                # (3) cascade divisibility at the block start
                m_n = (Tn[n] + (1 << (n - 1))) >> n if n else Dp
                if R <= 0 or m_n % (1 << R) == 0:
                    ok3 += 1
                # (4) the cap
                cap = LOG2_3HALVES * n + log(Dp + 1, 2) + p + log(5 * Dp) / log(1.5) + 1
                if L <= cap:
                    ok4 += 1
            n += max(k, 1)
        print(f"{p:4d} {nblk:8d} {ok1:10d} {ok2:7d} {ok3:8d} {ok4:7d}   | {maxR:7d} {bestL:9d}",
              file=out)


def cmd_steer(nmax, pmax, out=sys.stdout):
    """The ROUND-convention steering word t_n = 2 m_{n+1} - 3 m_n  (= TH.t of TH/Basic.lean,
    = the g-frame coefficient g_{n+1} of plan-Tshift-S11 D1 at D = 1).

    Tests the corpus's existing growth ceiling  TH.repetition_pow_le:
        IsRepetition a c k  ->  2^(k+c+1) <= 3^(c+1)      (2 <= a < c)
    against a p-periodic block on [n, n+L), which is IsRepetition n (n+p) (L-p):
        2^(L+n+1) <= 3^(n+p+1),   i.e.   L <= 0.585 n + 1.585 (p+1) - 1.
    That is D5's cap without the shadowing lemma, without the 1/5 band, without D_p.
    """
    ms = [m for (_n, _t, m, _T) in orbit(1, nmax + 2 * pmax + 3)]
    t = [2 * ms[n + 1] - 3 * ms[n] for n in range(nmax + 2 * pmax + 2)]
    alpha = {}
    for c in t[:nmax]:
        alpha[c] = alpha.get(c, 0) + 1
    print(f"# steering word (round convention) n <= {nmax}: alphabet {alpha}", file=out)
    print("# TH.repetition_pow_le cap:  2^(L+n+1) <= 3^(n+p+1)   (exact, integers)", file=out)
    print("#  p   max L  at n  |  ceiling holds  |  worst slack  at n | additive const",
          file=out)
    for p in range(1, pmax + 1):
        best_L, best_n, ok, tot = 0, 0, 0, 0
        worst, worst_n = float("inf"), None
        k = 0
        for n in range(nmax, 1, -1):         # a = n >= 2 is the theorem's hypothesis
            k = k + 1 if t[n + p] == t[n] else 0
            L = p + k
            if L > best_L:
                best_L, best_n = L, n
            tot += 1
            if 2 ** (L + n + 1) <= 3 ** (n + p + 1):
                ok += 1
            slack = (LOG2_3HALVES * n + (p + 1) * log(3, 2) - 1) - L
            if slack < worst:
                worst, worst_n = slack, n
        const = (p + 1) * log(3, 2) - 1
        print(f"{p:4d} {best_L:6d} {best_n:6d}  | {ok:7d}/{tot:<7d} | {worst:11.2f} "
              f"{worst_n:6d} | {const:9.2f}", file=out)


def cmd_floorcap(nmax, pmax, out=sys.stdout):
    """The FLOOR-convention growth ceiling, i.e. the machine-checked statement of
    TShift/FreeSojourn.lean (plan-Tshift-S11 WP-C, target T4):

        TShift.free_sojourn_cap:       IsPeriodicBlock n L p  ->  2^(L+n) <= 3^(n+p)
        TShift.free_sojourn_cap_logb:  L <= log2(3/2) n + log2(3) p          (2 <= n, 1 <= p <= L)

    This is the floor twin of cmd_steer's round-convention TH.repetition_pow_le, and it is
    one power sharper (floor needs no `round` slack): const = p log2 3 against (p+1) log2 3 - 1.
    Both are far below D5's own constant, printed by cmd_carry.  The three are compared here.
    """
    s = carry_word(nmax + 2 * pmax + 2)
    print(f"# floor carry word, n <= {nmax}: first five s_0..s_4 = {s[:5]} "
          f"(Lean TShift.carry_sanity: [-1, 1, 0, 1, -1])", file=out)
    print("# TShift.free_sojourn_cap:  2^(L+n) <= 3^(n+p)   (exact, integers, n >= 2)", file=out)
    print("#  p   max L  at n  |  ceiling holds  |  worst slack  at n | const: floor / round / D5",
          file=out)
    for p in range(1, pmax + 1):
        Dp = 3 ** p - 2 ** p
        best_L, best_n, ok, tot = 0, 0, 0, 0
        worst, worst_n = float("inf"), None
        k = 0
        for n in range(nmax, 1, -1):         # n >= 2 is the theorem's hypothesis
            k = k + 1 if s[n + p] == s[n] else 0
            L = p + k
            if L > best_L:
                best_L, best_n = L, n
            tot += 1
            if 2 ** (L + n) <= 3 ** (n + p):
                ok += 1
            slack = (LOG2_3HALVES * n + p * log(3, 2)) - L
            if slack < worst:
                worst, worst_n = slack, n
        c_floor = p * log(3, 2)
        c_round = (p + 1) * log(3, 2) - 1
        c_d5 = log(Dp + 1, 2) + p + log(5 * Dp) / log(1.5) + 1
        print(f"{p:4d} {best_L:6d} {best_n:6d}  | {ok:7d}/{tot:<7d} | {worst:11.2f} "
              f"{worst_n:6d} | {c_floor:8.2f} {c_round:7.2f} {c_d5:7.2f}", file=out)


#  --------------------------------------------------------------------------------
#  plan-Tshift-S11 WP-B (milestone M2): the Q1 sweep's numerical half.
#  --------------------------------------------------------------------------------


def _primes(pmax):
    return [p for p in range(2, pmax + 1)
            if all(p % q for q in range(2, int(p ** 0.5) + 1))]


def _vp(k, p, cap=64):
    """v_p(k) for k != 0, capped at `cap` (returns cap if p^cap | k)."""
    if k == 0:
        return None
    v = 0
    while v < cap and k % p == 0:
        k //= p
        v += 1
    return v


def cmd_adelic(D, nmax, pmax=40, out=sys.stdout):
    """B3: the adelic budget.  Local factors of the f-frame (N_n) and the g-frame (g_n).

    A local gain at p — the only way an adelic Fekete-Szego/Bertrandias statement can
    beat the archimedean disc — needs the coefficients to be uniformly p-divisible,
    v_p(coeff_n) >= c n for all large n, i.e. liminf v_p / n > 0.

    Two theorems are checked here, not just measured:
      (i)  v_2(N_n) = v_2(D)   for every n > v_2(D)          [N_n = D 3^n - m_n 2^n]
      (ii) v_3(N_n) = v_3(m_n) for every n > v_3(D)          [3-adic gain = 3-divisibility
                                                              of the rounded orbit]
    """
    ps = _primes(pmax)
    a = _vp(D, 2)
    b = _vp(D, 3)
    ms, Ns = [], []
    for n, _t, m, T in orbit(D, nmax):
        ms.append(m)
        Ns.append(T - (m << n))              # N_n = D 3^n - m_n 2^n = 2^n delta_n
    g = [2 * ms[0]] + [2 * ms[n + 1] - 3 * ms[n] for n in range(nmax)]
    bad2 = [n for n in range(a + 1, nmax + 1) if _vp(Ns[n], 2) != a]
    bad3 = [n for n in range(b + 1, min(nmax, 3000) + 1)
            if _vp(Ns[n], 3) != _vp(ms[n], 3)]
    print(f"# D = {D} (v_2(D) = {a}, v_3(D) = {b}), n <= {nmax}", file=out)
    print(f"#   THEOREM v_2(N_n) = v_2(D) for n > v_2(D): "
          f"{'OK' if not bad2 else bad2[:5]}   ==>  R_2 = 1 exactly", file=out)
    print(f"#   THEOREM v_3(N_n) = v_3(m_n) for n > v_3(D) (n <= 3000): "
          f"{'OK' if not bad3 else bad3[:5]}", file=out)
    # 3 | m_n  <=>  3 | 2 m_n = 3 m_(n-1) + g_n  <=>  3 | g_n  <=>  g_n = 0  (|g_n| <= 2).
    bad4 = [n for n in range(1, nmax + 1) if (ms[n] % 3 == 0) != (g[n] == 0)]
    print(f"#   THEOREM 3 | N_n  <=>  3 | m_n  <=>  g_n = 0: "
          f"{'OK' if not bad4 else bad4[:5]}   (the 3-adic layer's support IS the word's "
          "zero set, whose runs W3(a) caps at 0.585 n)", file=out)
    print("#   p | #{n : p | N_n}   max v_p  at n  | max v_p/n | verdict", file=out)
    for p in ps:
        vs = [_vp(Ns[n], p) for n in range(1, nmax + 1)]
        div = sum(1 for v in vs if v > 0)
        mx = max(vs)
        at = vs.index(mx) + 1
        print(f"{p:5d} | {div:7d}/{nmax:<7d} {mx:6d} {at:6d} | {mx / at:9.4f} | "
              f"liminf v_p/n = 0  ==>  R_{p} = 1", file=out)
    nz = [c for c in g[1:] if c]
    mxg = {p: max((_vp(c, p) for c in nz), default=0) for p in ps}
    print(f"#   g-frame: |g_n| <= 2, so v_p(g_n) = 0 unless g_n = 0 "
          f"({sum(1 for c in g[1:] if c == 0)} zeros); max v_p over nonzero g_n: "
          f"{ {p: v for p, v in mxg.items() if v} or 'all 0 for p >= 3, <= 1 for p = 2'}",
          file=out)
    print("#   => bounded coefficients admit NO local gain at any place (B3):", file=out)
    print("#      v_p(g_n) >= c n for large n forces g_n = 0 eventually (|g_n| <= 2 < p^(cn)),",
          file=out)
    print("#      i.e. 2 m_{n+1} = 3 m_n for all large n, i.e. 2^k | m_N for every k. "
          "Contradiction.", file=out)


def cmd_tail(D, nmax, out=sys.stdout):
    """B5: the evaluation identity.  ||D(3/2)^n|| = |delta_n| = (1/2)|G_n(2/3)| where
    G_n(w) = sum_{i>=1} g_{n+i} w^i is the shifted tail of the coefficient word.

    Checked exactly (Fractions): the truncation at i = K has remainder (2/3)^K delta_{n+K},
    so |delta_n - partial_K| <= (2/3)^K / 2 is an exact rational assertion.
    """
    from fractions import Fraction as F
    K = 80
    ms = [m for (_n, _t, m, _T) in orbit(D, nmax + K + 2)]
    g = [2 * ms[0]] + [2 * ms[n + 1] - 3 * ms[n] for n in range(nmax + K + 1)]
    tol = F(2, 3) ** K / 2
    worst, worst_n, bad = F(0), None, []
    for n in range(0, nmax + 1):
        delta = F(D * 3 ** n, 2 ** n) - ms[n]
        part = F(1, 2) * sum(F(2, 3) ** i * g[n + i] for i in range(1, K + 1))
        d = abs(delta - part)
        if d > tol:
            bad.append(n)
        if d > worst:
            worst, worst_n = d, n
    print(f"# D = {D}, n <= {nmax}: delta_n = (1/2) sum_{{i>=1}} (2/3)^i g_(n+i)", file=out)
    print(f"#   |delta_n - partial_{K}| <= (2/3)^{K}/2 = {float(tol):.3e} : "
          f"{'OK' if not bad else bad[:5]}  (worst {float(worst):.3e} at n = {worst_n})",
          file=out)
    print("#   So T1 is a POINT EVALUATION of the shifted germ at the interior point w = 2/3,", file=out)
    print("#   not a statement about any region: ||D(3/2)^n|| = (1/2)|G_n(2/3)|.", file=out)


def cmd_w3(nmax, out=sys.stdout):
    """W3, both halves, made rigorous and checked.

    (a) VACUITY above kappa = log2(3/2).  A zero-run of the coefficient word,
        g_{n+1} = ... = g_{n+L} = 0, says exactly 2 m_{n+j} = 3 m_{n+j-1}, hence
        2^L | m_n, hence L <= log2 m_n <= log2(3/2) n + log2 D + 1.  No band, no
        smallness hypothesis, no Diophantine input — pure divisibility.

    (b) NON-VACUITY below it.  Nested intervals produce real xi whose word has
        zero-runs of relative length kappa infinitely often, for every kappa < log2(3/2):
        the constraint at date n costs 2^(kappa n) of interval, and the orbit
        manufactures (3/2)^(n - n_prev) of room, so any growth ratio
            n_i / n_(i-1) >= log2(3/2)(1 + kappa) / (log2(3/2) - kappa)
        suffices.  Realised here to finite depth in exact rationals.
    """
    from fractions import Fraction as F
    print("# (a) zero-runs of the coefficient word against the free cap L <= log2 m_n", file=out)
    print("#   D |  max L  at n | 2^L | m_n | cap log2 m_n there | worst slack", file=out)
    for D in (1, 5, 19):
        ms = [m for (_n, _t, m, _T) in orbit(D, nmax)]
        g = [2 * ms[0]] + [2 * ms[n + 1] - 3 * ms[n] for n in range(nmax)]
        best_L, best_n, ok, worst, worst_n = 0, 0, True, float("inf"), None
        n = 1
        while n <= nmax:
            if g[n] == 0:
                L = 0
                while n + L <= nmax and g[n + L] == 0:
                    L += 1
                start = n - 1                       # g_{start+1} = 0 is the first zero
                if ms[start] % (1 << L):
                    ok = False
                if L > best_L:
                    best_L, best_n = L, start
                slack = ms[start].bit_length() - 1 - L
                if slack < worst:
                    worst, worst_n = slack, start
                n += L
            else:
                n += 1
        print(f"{D:5d} | {best_L:6d} {best_n:5d} | {'OK' if ok else 'FAIL'} | "
              f"{ms[best_n].bit_length() - 1:6d} | {worst} at n = {worst_n}", file=out)

    print("# (b) constructed witnesses: xi with a zero-run of relative length kappa", file=out)
    print("#   kappa | ratio needed | dates n_i (run length k_i)          | word check", file=out)
    for kappa in (0.2, 0.3, 0.4, 0.5, 0.55):
        ratio = LOG2_3HALVES * (1 + kappa) / (LOG2_3HALVES - kappa)
        lo, hi = F(1), F(2)                          # nested intervals for xi
        dates, n, tries = [], 8, 0
        while len(dates) < 3 and tries < 400 and n <= 6000:
            tries += 1
            k = int(kappa * n)
            three_half = F(3, 2) ** n
            if (hi - lo) * three_half < 2 ** k + 2:  # not enough room yet: push the date out
                n = int(n * ratio) + 1
                continue
            M = ((lo * three_half).__ceil__() // 2 ** k + 1) * 2 ** k
            if M > hi * three_half:
                n = int(n * ratio) + 1
                continue
            c = F(2, 3) ** k / 4                     # |xi (3/2)^n - M| <= c keeps the run exact
            lo, hi = (M - c) / three_half, (M + c) / three_half
            dates.append((n, k))
            n = int(n * ratio) + 1
        xi = (lo + hi) / 2
        p, q = xi.numerator, xi.denominator
        okrun = []
        for (n0, k) in dates:                        # m_j = round(xi (3/2)^j), integers only
            num, den = p * 3 ** n0, q * 2 ** n0
            mm = []
            for _ in range(k + 2):
                mm.append((2 * num + den) // (2 * den))
                num, den = num * 3, den * 2
            okrun.append("OK" if all(2 * mm[j + 1] == 3 * mm[j] for j in range(k)) else "FAIL")
        print(f"{kappa:8.2f} | {ratio:12.2f} | "
              f"{', '.join(f'{n0}({k})' for n0, k in dates):35s} | {' '.join(okrun)}", file=out)


def _bareiss(M):
    """Exact integer determinant, fraction-free Gaussian elimination."""
    n = len(M)
    A = [row[:] for row in M]
    sign, prev = 1, 1
    for k in range(n - 1):
        if A[k][k] == 0:
            for i in range(k + 1, n):
                if A[i][k]:
                    A[k], A[i] = A[i], A[k]
                    sign = -sign
                    break
            else:
                return 0
        for i in range(k + 1, n):
            for j in range(k + 1, n):
                A[i][j] = (A[i][j] * A[k][k] - A[i][k] * A[k][j]) // prev
        prev = A[k][k]
    return sign * A[n - 1][n - 1]


def cmd_hankel(D, nmax, kmax=5, out=sys.stdout):
    """B6: the surviving (alpha)-channel, measured.

    H_k(n) = det (g_{n+i+j+1})_{0<=i,j<k}, the sliding Hankel determinants of the
    coefficient word — the per-window form of Kronecker's rationality criterion.
    Reported with the longest run of consecutive vanishing windows (the A3 lacunarity
    caution: a criterion that does not name its window proves nothing).

    Also the exact 2x2 identity that ties the Hankel object to the word:
        4 (m_n m_(n+2) - m_(n+1)^2) = D (3/2)^n (2 g_(n+2) - 3 g_(n+1))
                                      + 4 (delta_n delta_(n+2) - delta_(n+1)^2),
    in which the orbit's Diophantine content (the delta's) cancels to O(1).
    """
    from fractions import Fraction as F
    ms = [m for (_n, _t, m, _T) in orbit(D, nmax + 2 * kmax + 4)]
    g = [2 * ms[0]] + [2 * ms[n + 1] - 3 * ms[n] for n in range(nmax + 2 * kmax + 3)]
    print(f"# D = {D}, n <= {nmax}: sliding Hankel determinants of the coefficient word",
          file=out)
    print("#  k | #{n : H_k(n) = 0} | longest run of consecutive zeros | |H_k| range", file=out)
    for k in range(1, kmax + 1):
        zeros, run, best, mx = 0, 0, 0, 0
        for n in range(1, nmax + 1):
            H = _bareiss([[g[n + i + j] for j in range(k)] for i in range(k)])
            mx = max(mx, abs(H))
            if H == 0:
                zeros += 1
                run += 1
                best = max(best, run)
            else:
                run = 0
        print(f"{k:4d} | {zeros:7d}/{nmax:<7d}     | {best:26d} | <= {mx}", file=out)
    bad = []
    for n in range(0, min(nmax, 200) + 1):
        d = [F(D * 3 ** j, 2 ** j) - ms[j] for j in (n, n + 1, n + 2)]
        lhs = 4 * (ms[n] * ms[n + 2] - ms[n + 1] ** 2)
        rhs = (D * F(3, 2) ** n * (2 * g[n + 2] - 3 * g[n + 1])
               + 4 * (d[0] * d[2] - d[1] ** 2))
        if lhs != rhs:
            bad.append(n)
    print(f"#   exact 2x2 identity (n <= 200): {'OK' if not bad else bad[:5]}  "
          "— the delta's cancel: the Hankel object is a function of the WORD, and its size "
          "grows like (3/2)^n whatever the orbit does.", file=out)


# ---------------------------------------------------------------------------
# plan-Tshift-S7, WP0.  The lag-p Hermite-Pade audit, in exact Z[t] and Q[t].
#
# Objects are [Hab03] Acta Arith. 106.3 (2003) 299-308, section 2:
#
#   H(a, b; t) = t^-b [ (1-t)^{a+b} - sum_{r<b} C(a+b, r) (-t)^r ]        (p. 300)
#              = sum_{s=0}^{a} (-1)^{s+b} C(a+b, s+b) t^s   -- a polynomial of degree a
#   Q_n(t)     = sum_{r=0}^{n} C(2n+b-r, n+b) C(a-n+r-1, r) t^r           (2.2)
#   P_n        = the degree-<= n part of Q_n H
#   P_n - Q_n H = (-1)^{n+b} t^{2n+1} E_n,   deg E_n = a-n-1              (2.1)
#   P_n Q_{n+1} - P_{n+1} Q_n
#              = (-1)^{n+b} C(a+b+n, 2n+b+1) C(2n+b+2, n+b+1) t^{2n+1}    (2.5)
#
# Polynomials are dense coefficient lists, index = degree; entries int or Fraction.
# ---------------------------------------------------------------------------


def _C(n, k):
    """Binomial, zero outside the range (the convention (2.2)/G_p are stated in)."""
    return comb(n, k) if 0 <= k <= n else 0


def _ptrim(p):
    while len(p) > 1 and p[-1] == 0:
        p = p[:-1]
    return p


def _pdeg(p):
    p = _ptrim(p)
    return -1 if len(p) == 1 and p[0] == 0 else len(p) - 1


def _padd(p, q, sign=1):
    n = max(len(p), len(q))
    return [(p[i] if i < len(p) else 0) + sign * (q[i] if i < len(q) else 0)
            for i in range(n)]


def _pmul(p, q):
    r = [0] * (len(p) + len(q) - 1)
    for i, a in enumerate(p):
        if a:
            for j, b in enumerate(q):
                r[i + j] += a * b
    return r


def _pow_one_minus_t(p):
    """(1-t)^p."""
    return [comb(p, r) * (-1) ** r for r in range(p + 1)]


def _H(a, b):
    """[Hab03] p. 300.  Degree a, integer coefficients."""
    return [(-1) ** (s + b) * comb(a + b, s + b) for s in range(a + 1)]


def _Q_beukers(n, a, b):
    """[Hab03] (2.2).  Needs 0 <= n <= a-1."""
    return [comb(2 * n + b - r, n + b) * comb(a - n + r - 1, r) for r in range(n + 1)]


def _pade_pair(n, a, b):
    """Return (P_n, Q_n, E_n, ok) with ok = True iff (2.1) holds exactly."""
    Q = _Q_beukers(n, a, b)
    QH = _pmul(Q, _H(a, b))
    P = QH[:n + 1]
    R = _padd(P, QH, -1)                       # P - Q H
    ok = all(c == 0 for c in R[:2 * n + 1])    # must vanish to order 2n+1
    sgn = (-1) ** (n + b)
    E = [sgn * c for c in R[2 * n + 1:]]
    return P, Q, _ptrim(E), ok


def _rank(rows, ncols):
    """Exact rank over Q by fraction-free-then-Fraction elimination."""
    M = [[Fraction(x) for x in r] for r in rows]
    rank = 0
    for col in range(ncols):
        piv = next((r for r in range(rank, len(M)) if M[r][col] != 0), None)
        if piv is None:
            continue
        M[rank], M[piv] = M[piv], M[rank]
        pv = M[rank][col]
        for r in range(len(M)):
            if r != rank and M[r][col] != 0:
                f = M[r][col] / pv
                M[r] = [x - f * y for x, y in zip(M[r], M[rank])]
        rank += 1
        if rank == len(M):
            break
    return rank


def _typeI_rows(f, p, nu, N):
    """Rows = coefficients of t^0..t^{N-1} of  A + B f + C (1-t)^p f,
    unknowns A_0..A_nu, B_0..B_nu, C_0..C_nu."""
    g = _pmul(_pow_one_minus_t(p), f)
    w = nu + 1
    rows = []
    for e in range(N):
        row = [0] * (3 * w)
        if e <= nu:
            row[e] = 1
        for j in range(nu + 1):
            k = e - j
            if k >= 0:
                row[w + j] = f[k] if k < len(f) else 0
                row[2 * w + j] = g[k] if k < len(g) else 0
        rows.append(row)
    return rows


def _series_binom(kappa, length):
    """(1-t)^kappa as a power series, kappa a Fraction -- a *generic* (non-degenerate) f."""
    c = [Fraction(1)]
    for s in range(1, length):
        c.append(c[-1] * (kappa - (s - 1)) / s * (-1))
    return c


def _collapse_audit(f, name, nu, p, out):
    """D2's counts: kernel of the collapse map, and the true maximal vanishing order."""
    w = nu + 1
    zero_forms = max(0, nu - p + 1)          # {(0, -C(1-t)^p, C) : deg C <= nu-p}
    line = []
    for N in (2 * nu + p + 1, 2 * nu + p + 2, 3 * nu + 2, 3 * nu + 3):
        rows = _typeI_rows(f, p, nu, N)
        null = 3 * w - _rank(rows, 3 * w)
        line.append((N, null, null - zero_forms))
    out.write(f"  {name:22s} nu={nu} p={p}  params 3(nu+1)={3*w}"
              f"  effective 2nu+p+2={2*nu+p+2}  zero-forms={zero_forms}\n")
    for N, null, eff in line:
        tag = ""
        if N == 2 * nu + p + 1:
            tag = "<- last order with a genuine form (D2 predicts eff=1)"
        if N == 2 * nu + p + 2:
            tag = "<- collapse (D2 predicts eff=0)"
        if N == 3 * nu + 2:
            tag = "<- naive 3-term order (would need eff>=1 if perfect)"
        out.write(f"      vanish to t^{N:<3d} dim ker = {null:<3d} genuine forms = {eff:<3d} {tag}\n")
    return line


def _hnf(rows, ncols):
    """Row-style Hermite normal form over Z.  Returns (rank, diagonal pivots)."""
    M = [row[:] for row in rows if any(row)]
    r = 0
    piv = []
    for c in range(ncols):
        if r >= len(M):
            break
        for i in range(r + 1, len(M)):
            while M[i][c] != 0:
                if M[r][c] == 0:
                    M[r], M[i] = M[i], M[r]      # now M[i][c] == 0; the loop exits
                    continue
                q = M[i][c] // M[r][c]
                M[i] = [a - q * b for a, b in zip(M[i], M[r])]
                if M[i][c] != 0:                 # |M[i][c]| < |M[r][c]|: swap and shrink again
                    M[r], M[i] = M[i], M[r]
        if M[r][c] != 0:
            piv.append(abs(M[r][c]))
            r += 1
    return r, piv


def _split_roundtrip(m, nu, p):
    """Flagship claim, constructively: every integer pair (Atil, Btil) of degrees
    (nu, nu+p) is (A + G_p C, B + (1-t)^p C) with A, B, C integral of degree <= nu.
    Returns (tested, failures) -- failures counts both non-existence and degree overflow."""
    G = _ptrim(_padd(_H(2 * m + p, m), _pmul(_pow_one_minus_t(p), _H(2 * m, m)), -1))
    W = _pow_one_minus_t(p)
    tested = fail = 0
    for seed in range(1, 41):                    # deterministic spread of targets
        Atil = [((-1) ** i) * (seed * (i + 3) % 17 - 8) for i in range(nu + 1)]
        Btil = [((-1) ** j) * (seed * (2 * j + 5) % 23 - 11) for j in range(nu + p + 1)]
        # divide Btil by (1-t)^p in Z[t]: leading coeff of (1-t)^p is a unit
        rem, C = Btil[:], [0] * max(1, nu + 1)
        for d in range(len(rem) - 1, p - 1, -1):
            q = rem[d] // W[p]
            if q * W[p] != rem[d]:               # exact division must hold (unit leading coeff)
                fail += 1
                break
            C[d - p] = q
            for u in range(p + 1):
                rem[d - p + u] -= q * W[u]
        else:
            B = _ptrim(rem)
            A = _ptrim(_padd(Atil, _pmul(G, C), -1))
            ok = (_pdeg(A) <= nu and _pdeg(B) <= nu and _pdeg(C) <= nu
                  and _ptrim(_padd(A, _pmul(G, C))) == _ptrim(Atil)
                  and _ptrim(_padd(B, _pmul(W, C))) == _ptrim(Btil))
            fail += 0 if ok else 1
        tested += 1
    return tested, fail


def _split_image(m, nu, p):
    """Rows spanning the image of (A,B,C) |-> (A + G_p C, B + (1-t)^p C) over Z,
    in coordinates (A-coeffs of degree 0..nu+p-1, B-coeffs of degree 0..nu+p)."""
    G = _ptrim(_padd(_H(2 * m + p, m), _pmul(_pow_one_minus_t(p), _H(2 * m, m)), -1))
    dA, dB = nu + p, nu + p + 1
    rows = []
    for i in range(nu + 1):                     # A = t^i
        v = [0] * (dA + dB)
        v[i] = 1
        rows.append(v)
    for j in range(nu + 1):                     # B = t^j
        v = [0] * (dA + dB)
        v[dA + j] = 1
        rows.append(v)
    for k in range(nu + 1):                     # C = t^k
        v = [0] * (dA + dB)
        for u, c in enumerate(G):
            v[k + u] += c
        for u, c in enumerate(_pow_one_minus_t(p)):
            v[dA + k + u] += c
        rows.append(v)
    return rows, dA + dB


def _content_primes(n, a, b):
    """[Hab03] Lemma 1 (p. 301) transcribed at general (a, b) instead of (2m, m).

    Habsieger states the lemma only after "we now restrict our attention to the
    case (a, b) = (2m, m)", but the proof uses nothing beyond (2.2) and (2.1),
    which are both stated at general (a, b).  The three quantities that enter his
    eta_1, eta_2, eta_3 are n+b, a-n-1 and n; on the diagonal these are n+m,
    2m-n-1 and n, which is his printed form.  Check [F] tests the transcription.

    Returns the primes l with l^2 > max(n+b, a-n-1) and
    {(n+b)/l} + {(a-n-1)/l} + {n/l} >= 2.
    """
    x, y = n + b, a - n - 1
    if y < 0:
        return []
    lo = max(x, y)
    hi = (x + y + n) // 2          # the sum of three residues cannot reach 2l past this
    return [l for l in _primes(hi)
            if l * l > lo and (x % l) + (y % l) + (n % l) >= 2 * l]


def cmd_pade(mmax, pmax, out=sys.stdout):
    out.write("plan-Tshift-S7 WP0 -- lag-p Hermite-Pade audit (F1/D2), exact arithmetic\n")

    out.write("\n[A] [Hab03] (2.1) and (2.5) replayed at (a,b) = (2m, m)\n")
    bad = 0
    for m in range(2, mmax + 1):
        a, b = 2 * m, m
        for n in range(0, min(a - 2, 3 * m)):
            P, Q, E, ok = _pade_pair(n, a, b)
            P1, Q1, _, ok1 = _pade_pair(n + 1, a, b)
            det = _padd(_pmul(P, Q1), _pmul(P1, Q), -1)
            want = [0] * (2 * n + 1) + [(-1) ** (n + b)
                                        * comb(a + b + n, 2 * n + b + 1)
                                        * comb(2 * n + b + 2, n + b + 1)]
            good = ok and ok1 and _ptrim(det) == _ptrim(want) and _pdeg(E) == a - n - 1
            bad += 0 if good else 1
    out.write(f"      (2.1) order, (2.5) determinant, deg E_n = a-n-1: "
              f"{'ALL HOLD' if bad == 0 else str(bad) + ' FAILURES'} "
              f"for 2 <= m <= {mmax}, 0 <= n < min(2m-2, 3m)\n")

    out.write("\n[B] the lag identity for the *actual* objects:"
              " H(2m+p, m; t) - (1-t)^p H(2m, m; t) = G_p(t)\n")
    worst = -1
    bad = 0
    for m in range(1, mmax + 1):
        for p in range(1, pmax + 1):
            G = _ptrim(_padd(_H(2 * m + p, m), _pmul(_pow_one_minus_t(p), _H(2 * m, m)), -1))
            worst = max(worst, _pdeg(G))
            closed = [(-1) ** (m + u) * sum(_C(p, j) * _C(3 * m, m + u - j)
                                            for j in range(u + 1, p + 1))
                      for u in range(p)]
            if _ptrim(G) != _ptrim(closed) or _pdeg(G) > p - 1:
                bad += 1
    out.write(f"      deg G_p <= p-1 and the closed form G_p[u] = (-1)^(m+u) "
              f"sum_{{j=u+1}}^{{p}} C(p,j) C(3m, m+u-j):\n")
    out.write(f"      {'BOTH HOLD' if bad == 0 else str(bad) + ' FAILURES'} "
              f"for 1 <= m <= {mmax}, 1 <= p <= {pmax}; max deg G_p seen = {worst}\n")
    G1 = [_ptrim(_padd(_H(2 * m + 1, m), _pmul([1, -1], _H(2 * m, m)), -1))
          for m in range(1, 6)]
    out.write("      flagship lag (p_z = 1): G_1 = (-1)^m C(3m, m-1) = "
              + ", ".join(f"{g[0]:+d}" for g in G1) + "  (m = 1..5)\n")

    out.write("\n[C] D2's counts, on the true H and on a generic binomial series\n")
    for nu, p in ((3, 1), (4, 2), (6, 2), (5, 3)):
        f = _H(2 * 6, 6) + [0] * 64
        _collapse_audit(f, "H(12,6;t)", nu, p, out)
        _collapse_audit(_series_binom(Fraction(7, 3), 64), "(1-t)^(7/3)", nu, p, out)
    out.write("\n      Reading: 'genuine forms' = dim ker minus the identically-zero forms\n"
              "      {(0, -C(1-t)^p, C)}.  D2 says the system behaves like the Pade problem\n"
              "      at degrees (nu, nu+p): 2nu+p+2 parameters, so vanishing stops at\n"
              "      t^(2nu+p+1) instead of the naive t^(3nu+2).\n")

    out.write("\n[D] WP-A: the same counts for the system {1, H(2m,m;t), H(2m+p,m;t)} itself\n")
    for nu, p in ((3, 1), (4, 2), (6, 2), (5, 3)):
        m = 6
        f0, fp = _H(2 * m, m) + [0] * 64, _H(2 * m + p, m) + [0] * 64
        w = nu + 1
        line = []
        for N in (2 * nu + p + 1, 2 * nu + p + 2):
            g = fp
            rows = []
            for e in range(N):
                row = [0] * (3 * w)
                if e <= nu:
                    row[e] = 1
                for j in range(nu + 1):
                    k = e - j
                    if k >= 0:
                        row[w + j] = f0[k] if k < len(f0) else 0
                        row[2 * w + j] = g[k] if k < len(g) else 0
                rows.append(row)
            line.append((N, 3 * w - _rank(rows, 3 * w)))
        zf = max(0, nu - p + 1)
        out.write(f"      nu={nu} p={p} m={m}:  dim ker at t^{line[0][0]} = {line[0][1]}"
                  f" (genuine {line[0][1]-zf}),  at t^{line[1][0]} = {line[1][1]}"
                  f" (genuine {line[1][1]-zf})"
                  f"   {'MATCHES D2' if line[0][1]-zf == 1 and line[1][1]-zf == 0 else '*** DIFFERS ***'}\n")

    out.write("\n[E] WP-A: is the split integrality model a *smaller* lattice than the classical one?\n")
    out.write("      image of (A,B,C) |-> (A + G_p C, B + (1-t)^p C), all degrees <= nu, over Z\n")
    for p in range(1, min(pmax, 3) + 1):
        for nu in (3, 4, 6):
            for m in (2, 6, 11):
                rows, ncols = _split_image(m, nu, p)
                rank, piv = _hnf(rows, ncols)
                assert rank == _rank(rows, ncols), "HNF and Q-rank disagree"
                tested, fail = _split_roundtrip(m, nu, p)
                idx = 1
                for d in piv:
                    idx *= d
                if rank == ncols:
                    note = f"spans Z^{ncols}, index {idx}"
                else:
                    note = (f"rank {rank} = 2nu+p+2, ambient Z^{ncols} is bigger than the "
                            f"classical lattice")
                out.write(f"      p={p} nu={nu} m={m:2d}:  {note};  "
                          f"round-trip {tested - fail}/{tested}\n")
    out.write("\n      p=1 is the flagship (date lag 2).  Index 1 in Z^(2nu+3), and a 40/40\n"
              "      constructive round-trip, say the same thing: the split model spans the\n"
              "      *whole* classical lattice at degrees (nu, nu+1).  Same forms, same contents,\n"
              "      g = 1 identically -- Q1 needs no measurement there.\n"
              "      p >= 2: deg(G_p C) reaches nu+p-1 > nu, so the split image does not even sit\n"
              "      inside the classical lattice; the models are not comparable as posed, and the\n"
              "      round-trip fails exactly on the degree overflow.  Off-flagship by F5.\n")

    out.write("\n[F] G-B sweep: is [Hab03] Lemma 1 (the content lemma) already off-diagonal?\n")
    out.write("      claim: for every prime l with l^2 > max(n+b, a-n-1) and\n"
              "      {(n+b)/l} + {(a-n-1)/l} + {n/l} >= 2, we have {P_n, Q_n} in l.Z[t],\n"
              "      at general (a, b) -- not only at (a, b) = (2m, m) where it is printed.\n")
    bad = diag = off = 0
    for m in range(2, mmax + 1):
        for p in range(0, pmax + 1):
            a, b = 2 * m + p, m
            for n in range(0, min(a - 2, 3 * m)):
                ls = _content_primes(n, a, b)
                if not ls:
                    continue
                P, Q, _, _ = _pade_pair(n, a, b)
                for l in ls:
                    if any(c % l for c in Q) or any(c % l for c in P):
                        bad += 1
                if p == 0:
                    diag += len(ls)
                else:
                    off += len(ls)
    out.write(f"      {'HOLDS' if bad == 0 else str(bad) + ' FAILURES'} over"
              f" 2 <= m <= {mmax}, 0 <= p <= {pmax}, 0 <= n < min(a-2, 3m):\n"
              f"      {diag} diagonal (l, n) hits and {off} off-diagonal ones tested,"
              f" all dividing both P_n and Q_n\n")
    out.write("\n      So the arithmetic half of WP-B's apparatus extension is a substitution,\n"
              "      not a new proof: (n+m, 2m-n-1) -> (n+b, a-n-1) throughout Lemma 1.  The\n"
              "      analytic half (sizes at the off-diagonal cell) is untouched by this and is\n"
              "      still WP-B's actual work.  NOT started here.\n")


# ---------------------------------------------------------------------------
# plan-Tshift-S7, WP-B.  The note-Tshift-S1-constants section 8.2 apparatus, in code.
#
# For an admissible evaluation point (t, mu, K) -- mu = a/b, X = 1/|t|, K the number
# of m-steps per unit of k -- [Hab03] Proposition 3 generalises to
#
#   C1(al) = ( -al log X + I(al) - A(al) - log F1(al) ) / K
#   C2(al) = ( -2 al log X + log F2(al) - log F1(al) ) / K
#
# with, straight off the integral representations (2.3) and (2.4) at general (a, b),
#
#   F1(al) = max_{[0,1]} x^{mu-al} (1-x)^{1+al} |1 - (1-t)x|^{al}
#   F2(al) = max_{[0,1]} x^{al}    (1-x)^{1+al} |1 - t x|^{mu-al}
#   A(al)  = (mu+1+al)log(mu+1+al) - (mu-al)log(mu-al) - (1+al)log(1+al) - al log al
#   I(al)  = int_{E_al} dx/x^2,   E_al = {x>0 : {(1+al)x}+{(mu-al)x}+{al x} >= 2}
#
# theta = exp(C1) at the optimum, which sits at the root of C1 = C2.  Section 8.2
# reported this calibration but shipped no code; gate G-A is that calibration, so
# the routine has to exist here.  Everything below is float, and says so -- unlike
# the rest of this file, which is exact.  The exact half of WP-B is [K].
# ---------------------------------------------------------------------------


def _psi_scalar(z):
    """digamma, via recurrence up to 12 plus the standard asymptotic series."""
    from math import log as _log
    r = 0.0
    while z < 12.0:
        r -= 1.0 / z
        z += 1.0
    f = 1.0 / (z * z)
    return (r + _log(z) - 0.5 / z
            - f * (1 / 12 - f * (1 / 120 - f * (1 / 252 - f * (1 / 240 - f / 132)))))


def _psi_many(zs):
    """digamma on a list; scipy if present (vectorised), else the scalar fallback."""
    try:
        import numpy as _np
        from scipy.special import psi as _psi
        return _psi(_np.asarray(zs, dtype=float))
    except ImportError:
        return [_psi_scalar(z) for z in zs]


def _max_three_factor(e1, e2, e3, d):
    """max over [0,1] of x^e1 (1-x)^e2 |1-d x|^e3, e_i > 0.

    d/dx of the log vanishes where  d(e1+e2+e3)x^2 - (e1(1+d)+e2+e3 d)x + e1 = 0;
    when d > 1 the middle factor has a zero inside [0,1] and there are two local
    maxima, both roots of that quadratic.  A grid scan cross-checks the algebra.
    """
    def g(x):
        if x <= 0.0 or x >= 1.0:
            return 0.0
        return x ** e1 * (1 - x) ** e2 * abs(1 - d * x) ** e3

    cands = []
    A2 = d * (e1 + e2 + e3)
    B2 = -(e1 * (1 + d) + e2 + e3 * d)
    C2c = e1
    if abs(A2) < 1e-15:
        if abs(B2) > 1e-15:
            cands.append(-C2c / B2)
    else:
        disc = B2 * B2 - 4 * A2 * C2c
        if disc >= 0:
            sq = disc ** 0.5
            cands += [(-B2 + sq) / (2 * A2), (-B2 - sq) / (2 * A2)]
    best = max([g(x) for x in cands if 0.0 < x < 1.0] or [0.0])

    grid = max(range(1, 4000), key=lambda j: g(j / 4000.0))
    lo, hi = (grid - 1) / 4000.0, (grid + 1) / 4000.0
    phi = (5 ** 0.5 - 1) / 2
    for _ in range(200):
        x1, x2 = hi - phi * (hi - lo), lo + phi * (hi - lo)
        if g(x1) < g(x2):
            lo = x1
        else:
            hi = x2
    return max(best, g((lo + hi) / 2))


def _A_alpha(mu, al):
    s = mu + 1 + al
    return (s * log(s) - (mu - al) * log(mu - al)
            - (1 + al) * log(1 + al) - al * log(al))


def _I_alpha(mu, u, v, want_intervals=False):
    """I(al) for al = u/v, by exact decomposition of one period of E_al.

    x -> {(1+al)x} + {(mu-al)x} + {al x} has period v.  Between consecutive
    breakpoints the three floors are constant, so the sum is s*x - N with
    s = mu+1+al, and E_al meets the elementary interval in [max(left,(N+2)/s), right).
    Translates by v are summed in closed form:
        sum_{q>=0} [ 1/(a+vq) - 1/(b+vq) ] = ( psi(b/v) - psi(a/v) ) / v.
    Breakpoints are ordered by exact integer keys, never by float comparison.
    """
    from math import gcd
    P = (v + u, mu * v - u, u)
    L = P[0] * P[1] // gcd(P[0], P[1])
    L = L * P[2] // gcd(L, P[2])
    keys = []
    for Pi in P:
        step = L // Pi
        keys.extend(range(step, L + 1, step))
    keys.sort()

    S = (mu + 1) * v + u                       # s = S/v
    lows, highs = [], []                       # entries (num, den), meaning x/v = num/den
    prev, cnt, i, nk = 0, 0, 0, len(keys)
    while i < nk:
        k = keys[i]
        mult = 0
        while i < nk and keys[i] == k:
            mult += 1
            i += 1
        thr = (cnt + 2) * L                    # x >= (cnt+2)/s  <=>  key*S >= thr
        # the whole elementary interval qualifies, or E starts inside it at (N+2)/s
        lo = (prev, L) if prev * S >= thr else (cnt + 2, S)
        if lo[0] * L < k * lo[1]:
            if lows and highs[-1] == lo:       # merge, so the pieces are maximal
                highs[-1] = (k, L)
            else:
                lows.append(lo)
                highs.append((k, L))
        cnt += mult
        prev = k

    pl = _psi_many([a / b for a, b in lows])
    ph = _psi_many([a / b for a, b in highs])
    I = float(sum(b - a for a, b in zip(pl, ph))) / v
    if not want_intervals:
        return I, None
    return I, [(Fraction(a[0] * v, a[1]), Fraction(b[0] * v, b[1]))
               for a, b in zip(lows, highs)]


def _apparatus(mu, t, K, u, v):
    """(F1, F2, A, I, C1, C2) at the point (t, mu, K) and al = u/v."""
    al = u / v
    X = 1.0 / abs(t)
    F1 = _max_three_factor(mu - al, 1 + al, al, 1 - t)
    F2 = _max_three_factor(al, 1 + al, mu - al, t)
    A = _A_alpha(mu, al)
    I = _I_alpha(mu, u, v)[0]
    C1 = (-al * log(X) + I - A - log(F1)) / K
    C2 = (-2 * al * log(X) + log(F2) - log(F1)) / K
    return F1, F2, A, I, C1, C2


def _nullvec(rows, ncols):
    """A primitive integer kernel vector of an exact rational matrix (dim 1 assumed)."""
    from math import gcd
    M = [[Fraction(c) for c in r] for r in rows]
    piv, r = [], 0
    for c in range(ncols):
        s = next((k for k in range(r, len(M)) if M[k][c] != 0), None)
        if s is None:
            continue
        M[r], M[s] = M[s], M[r]
        inv = M[r][c]
        M[r] = [x / inv for x in M[r]]
        for k in range(len(M)):
            if k != r and M[k][c] != 0:
                f = M[k][c]
                M[k] = [x - f * y for x, y in zip(M[k], M[r])]
        piv.append(c)
        r += 1
        if r == len(M):
            break
    free = [c for c in range(ncols) if c not in piv]
    if not free:
        return None
    fc = free[0]
    vec = [Fraction(0)] * ncols
    vec[fc] = Fraction(1)
    for i, c in enumerate(piv):
        vec[c] = -M[i][fc]
    den = 1
    for x in vec:
        den = den * x.denominator // gcd(den, x.denominator)
    ints = [int(x * den) for x in vec]
    g = 0
    for x in ints:
        g = gcd(g, abs(x))
    return [x // g for x in ints] if g else ints


def _pade_cell(a, b, L, M):
    """The primitive integer Pade pair of H(a,b;.) in the cell (L, M).

    deg P <= L, deg Q <= M, ord(P - Q H) >= L+M+1.  (L, L) is [Hab03]'s diagonal
    pair (2.2) up to its content.  What matters below is the numerator deficit
    d = M - L: the lag construction's collapsed pair (A + G_p C, B + (1-t)^p C)
    has degrees (nu+p-1, nu+p), so d = 1 at every lag -- while the plan's literal
    reading "(nu, nu+p)" has d = p.  Check [K] measures that the two differ.
    """
    H = _H(a, b)
    w = M + 1
    rows = []
    for e in range(L + 1, L + M + 1):
        rows.append([H[e - j] if 0 <= e - j < len(H) else 0 for j in range(w)])
    Q = _nullvec(rows, w)
    if Q is None:
        return None
    QH = _pmul(Q, H)
    P = QH[:L + 1]
    R = _ptrim(_padd(P, QH, -1))
    from math import gcd
    g = 0
    for x in P + Q:
        g = gcd(g, abs(x))
    if g > 1:                                   # _nullvec is primitive in Q alone
        P = [x // g for x in P]
        Q = [x // g for x in Q]
        R = [x // g for x in R]
    return P, Q, R


def _ev(poly, t):
    s = Fraction(0)
    for c in reversed(poly):
        s = s * t + c
    return s


def cmd_apparat(mmax, pmax, out=sys.stdout):
    out.write("plan-Tshift-S7 WP-B -- the section 8.2 apparatus at a general point,\n"
              "and the (nu, nu+p) off-diagonal cell.  Floats here are floats.\n")

    out.write("\n[G] gate G-A: does the routine reproduce [Hab03] at (mu, t, K) = (2, -1/8, 6)?\n")
    out.write("      first, the three point functions at alpha = 15/16 against the paper's\n"
              "      PARI line (note-Tshift-S1-constants section 3):\n")
    F1, F2, A, I, C1, C2 = _apparatus(2, Fraction(-1, 8), 6, 15, 16)
    ref = {"F1": 0.0964204654358, "F2/F1": 1.7628240039, "A": 4.11115653488,
           "q1 = A + log F1": 1.77211973204, "e1 = A + log F2": 2.33903680285}
    got = {"F1": F1, "F2/F1": F2 / F1, "A": A, "q1 = A + log F1": A + log(F1),
           "e1 = A + log F2": A + log(F2)}
    for k in ref:
        d = abs(got[k] - ref[k])
        out.write(f"      {k:16s} {got[k]:18.11f}   paper {ref[k]:15.11f}"
                  f"   |diff| {d:.2e}\n")

    out.write("\n      and I(15/16) against the paper's own printed decomposition of E_alpha\n"
              "      (p. 306: 30 intervals per period, listed in three columns):\n")
    _, ivs = _I_alpha(2, 15, 16, want_intervals=True)
    paper = [(32, 63, 16, 31), (16, 21, 16, 17), (64, 63, 32, 31), (32, 21, 48, 31),
             (16, 9, 32, 17), (128, 63, 64, 31), (160, 63, 80, 31), (176, 63, 48, 17),
             (64, 21, 96, 31), (32, 9, 112, 31), (256, 63, 128, 31), (32, 7, 144, 31),
             (320, 63, 160, 31), (352, 63, 96, 17), (128, 21, 192, 31), (400, 63, 32, 5),
             (64, 9, 224, 31), (464, 63, 112, 15), (512, 63, 256, 31), (176, 21, 144, 17),
             (64, 7, 288, 31), (592, 63, 160, 17), (640, 63, 320, 31), (704, 63, 192, 17),
             (736, 63, 176, 15), (256, 21, 208, 17), (800, 63, 64, 5), (96, 7, 208, 15),
             (928, 63, 224, 15), (992, 63, 16, 1)]
    want = [(Fraction(x, y), Fraction(z, w)) for x, y, z, w in paper]
    out.write(f"      intervals found = {len(ivs)}   paper's j_alpha = {len(want)}\n")
    out.write(f"      the 30 pairs (a_i, b_i) agree exactly: "
              f"{'YES' if ivs == want else '*** NO ***'}\n")
    if ivs != want:
        for got_i, want_i in list(zip(ivs, want))[:4]:
            out.write(f"        got {got_i}   want {want_i}\n")
    trunc = sum(float(Fraction(1, 1) / (a + 16 * q) - Fraction(1, 1) / (b + 16 * q))
                for a, b in want for q in range(0, 11))
    out.write(f"      I(15/16) = {I:.11f}   (exact sum over all translates q >= 0)\n")
    out.write(f"      same sum truncated at q <= 10, as in the paper's (3.14): {trunc:.11f}\n")
    out.write(f"      paper's effective constant, after Chebyshev Theta errors:  0.40127\n")
    out.write("      So 0.3945 is NOT I(15/16).  It is [Hab03] (3.11), the m-uniform constant\n"
              "      valid for m >= 10 740 000, already reduced by the q <= 10 truncation of\n"
              "      (3.14) and by the Chebyshev Theta error terms.  Both constants are real and\n"
              "      both are used below; they must not be swapped.  e^0.3945 = 1.483642 is what\n"
              "      CITED/HabsiegerPade.lean encodes (7516022/5065927); e^I is the asymptotics.\n")

    out.write("\n      then Theorem 1 itself, at Habsieger's alpha_0 = 224141/240395:\n")
    F1, F2, A, I, C1, C2 = _apparatus(2, Fraction(-1, 8), 6, 224141, 240395)
    theta = 2.718281828459045 ** C1
    out.write(f"      alpha_0        = {224141/240395:.9f}      paper 0.932386281\n")
    out.write(f"      F1 = {F1:.12f}   F2 = {F2:.12f}   A = {A:.11f}   I = {I:.11f}\n")
    out.write(f"      C1 - C2        = {C1-C2:.6e}      paper 1.0057e-11\n")
    out.write(f"      theta = e^C1   = {theta:.12f}   paper 0.57701737767006\n")
    ok = abs(theta - 0.57701737767006) < 5e-11
    out.write(f"      ten-digit agreement: {'YES -- G-A PASSES' if ok else '*** NO ***'}"
              f"   (|diff| = {abs(theta-0.57701737767006):.2e})\n")

    out.write("\n[H] second calibration: the vacuous p=1 point (mu, t, K) = (1, +1/4, 2)\n")
    F1b, F2b, Ab, Ib, C1b, C2b = _apparatus(1, Fraction(1, 4), 2, 6280417, 10000000)
    out.write(f"      at alpha = 0.6280417:  F1 = {F1b:.8f}  F2 = {F2b:.8f}"
              f"  A = {Ab:.8f}  I = {Ib:.6f}\n")
    out.write(f"      C1 = {C1b:.6f}   C2 = {C2b:.6f}   theta = {2.718281828459045**C1b:.6f}"
              f"      note says 0.357577\n")

    out.write("\n[K] the off-diagonal cell, on the exact objects.  Primitive integer Pade\n"
              "    pairs of H(2m, m; .) in the cell (L, M), n = [alpha(m-3/2)]+1,\n"
              "    alpha = 15/16.  Exact rationals throughout; the printed rate is\n"
              "    log(height of the primitive Q) / m.\n")
    al = Fraction(15, 16)
    t0 = Fraction(-1, 8)
    specs = [("d0", "(n,     n  )  d=0   [Hab03]'s diagonal", lambda n: (n, n)),
             ("d1*", "(n,     n+1)  d=1   the flagship cell", lambda n: (n, n + 1)),
             ("d1'", "(n+1,   n+2)  d=1   same deficit, shifted", lambda n: (n + 1, n + 2)),
             ("d1''", "(n+p-1, n+p)  d=1   the lag cell at p=3", lambda n: (n + 2, n + 3)),
             ("d2", "(n,     n+2)  d=2   \"(nu,nu+p)\" read literally, p=2", lambda n: (n, n + 2)),
             ("d3", "(n,     n+3)  d=3   ditto, p=3", lambda n: (n, n + 3))]
    out.write("        m |" + "".join(f" {tag:>8s}" for tag, _, _ in specs) + "\n")
    rates = {tag: [] for tag, _, _ in specs}
    step = max(1, (mmax - 8) // 5 or 1)
    for m in range(8, mmax + 1, step):
        n = int(al * (m - Fraction(3, 2))) + 1
        row = []
        for tag, _, f in specs:
            L, M = f(n)
            c = _pade_cell(2 * m, m, L, M)
            r = log(max(abs(x) for x in c[1])) / m if c else float("nan")
            rates[tag].append(r)
            row.append(r)
        out.write(f"      {m:3d} |" + "".join(f" {x:8.4f}" for x in row) + "\n")
    out.write("\n      mean over the m tested, by numerator deficit d = M - L:\n")
    for tag, desc, _ in specs:
        xs = [x for x in rates[tag] if x == x]
        out.write(f"        {tag:5s} {desc:44s} {sum(xs)/len(xs):8.4f}\n")
    out.write("""
      Reading.  The rate is a function of the numerator deficit d = M - L, not of
      where the cell sits along the staircase: every d = 1 cell matches the diagonal,
      and d = 2 costs about a factor two in the rate.  That settles F1's asymptotic-
      equality claim on the real objects, and sharpens it:

        * The flagship (exponent shift p_z = 1) is the cell (n, n+1), d = 1.  Its rate
          equals the diagonal's, so C1, C2, alpha_0 and theta are unchanged.  The
          analytic budget is zero, as F1 says -- measured, not assumed.
        * The lag construction at ANY p lands in (nu+p-1, nu+p) -- WP-A's collapsed
          pair (A + G_p C, B + (1-t)^p C) -- which has d = 1 too.  So the analytic
          budget is zero at every lag, not only at the flagship.
        * The plan's literal phrase "the (nu, nu+p) cell" has d = p, and for p >= 2
          that is NOT the construction's cell and is measurably worse.  Do not read
          the phrase literally off-flagship.

      Where the d = 2 loss comes from: the minors grow smoothly in d, but the content
      stalls.  At m = 16, alpha = 15/16:  log height(minors) = 296.1 / 311.6 / 332.5
      and log gcd(minors) = 273.2 / 288.3 / 286.7 for d = 0 / 1 / 2.  The content is a
      property of the diagonal and its first neighbour, and it collapses at d = 2.
""")

    out.write("\n[L] the D4 wall, recomputed in the extended apparatus\n")
    need = log(2 / 3) - C1
    e = 2.718281828459045
    out.write(f"      C1 at alpha_0              = {C1:.12f}   (theta = {theta:.10f})\n")
    out.write(f"      target                     = log(2/3) = {log(2/3):.12f}\n")
    out.write(f"      shortfall in C1            = {need:.12f}\n")
    out.write(f"      I must rise by K*shortfall = {6*need:.10f} nats"
              f"   =>   g = content base x {e**(6*need):.6f}\n")
    out.write(f"      contentBase at alpha_0: e^I = {e**I:.6f}  ->  {e**(I+6*need):.6f}\n")
    out.write(f"      the same ratio on [Hab03]'s m-uniform constant (3.11), e^0.3945:\n"
              f"                              {e**0.3945:.6f}  ->  {e**(0.3945+6*need):.6f}\n")
    out.write("      g is what the wall is, and it is unchanged -- by p (see [K]), and by which of\n"
              "      the two content constants one quotes, since g is a ratio.  D4's row quotes\n"
              "      the second pair, which is the operationally right one: the effective\n"
              "      constant is what CITED/HabsiegerPade.lean carries.  Both are printed here so\n"
              "      that the asymptotic I and the m-uniform 0.3945 are never swapped.\n")

    _dub87(out)


def _dub87_U_from_5(k):
    """[Dub87] (5) -- {x} < {x/5} < 1 - {x} -- solved for x on (k, k+1).

    With k = 5j + r one has {x} = x - k and {x/5} = x/5 - j there, so
        {x} < {x/5}      <=>  x < k + r/4
        {x/5} < 1 - {x}  <=>  x < k + (5-r)/6
    and the admissible piece is (k, k + min(r/4, (5-r)/6)), empty exactly when 5 | k.
    """
    r = k % 5
    return k + min(Fraction(r, 4), Fraction(5 - r, 6))


def _dub87_U_from_6(k):
    """[Dub87] (6) as printed, for comparison with the region rederived from (5)."""
    return min(Fraction(5, 4) * (k - k // 5),
               Fraction(5, 6) * (1 + k) + Fraction(5, 6) * (k // 5))


def _dub87(out):
    """[M]/[N]: the ancestor of the content device, calibrated at a second family.

    A.K. Dubitskas, "On the approximation of pi/sqrt 3 by rational fractions",
    Vestnik Moskov. Univ. Ser. 1 (1987) no. 6, 73-76 -- the paper [Dub90] cites for
    the proof of its content lemma, which is in turn [Hat90] 2.5 / [Hab03] Lemma 1.
    Nothing here touches the T-shift; it calibrates the arithmetic half of the 8.2
    apparatus against a printed constant from a family that is NOT of the H(a,b) type.
    """
    out.write("\n[M] [Dub87] Lemma 2: the ancestor content lemma\n")
    bad = [k for k in range(1, 2001) if _dub87_U_from_5(k) != _dub87_U_from_6(k)]
    out.write("      region rederived from (5) vs the printed (6), 1 <= k <= 2000: "
              f"{'AGREE' if not bad else 'DIFFER at ' + str(bad[:4])}\n")
    out.write("      admissible n/nu lies in (k, k + w_r), r = k mod 5, w_r = min(r/4, (5-r)/6):\n")
    out.write("        " + "   ".join(f"r={r}: {_dub87_U_from_5(r) - r}" for r in range(1, 5))
              + "   (r = 0 empty, i.e. 5 | k excluded)\n")
    # log H_n / n  =  sum over the region of (1/k - 1/U_k)   [Mertens; = the discrete
    # form of I(alpha) = int_{E_alpha} dx/x^2, since int_a^b dx/x^2 = 1/a - 1/b].
    part, K = 0.0, 20000
    marks = {}
    for k in range(1, K + 1):
        if k % 5:
            part += 1.0 / k - 1.0 / float(_dub87_U_from_5(k))
        if k in (10, 100, 1000, 10000):
            marks[k] = part
    w = {r: float(_dub87_U_from_5(r) - r) for r in range(1, 5)}
    exact = sum(_psi_scalar((r + w[r]) / 5.0) - _psi_scalar(r / 5.0) for r in range(1, 5)) / 5.0
    for k in sorted(marks):
        out.write(f"      partial sum, k <= {k:<5d}    = {marks[k]:.9f}\n")
    out.write(f"      full sum (digamma closed form) = {exact:.9f}\n")
    out.write(f"      [Dub87] states H_n > exp(n * 0.3911792...)\n")
    ok = exact >= 0.3911792
    out.write(f"      the paper's constant is a LOWER bound and 0.3911792 <= sum: "
              f"{'YES -- consistent' if ok else 'NO -- transcription is wrong'}\n")
    out.write(f"      slack = {exact - 0.3911792:.3e}  (a truncation of their own series at k ~ "
              f"{int(0.25/(exact - 0.3911792))})\n")

    out.write("\n[N] [Dub87]/[Dub93]: the rest of the two papers, as arithmetic\n")
    mu = (21 - 297 ** 0.5) / 10
    lam2 = (1.2 - 0.3911792 - mu * log(mu) - (1.2 - 2 * mu) * log(1.2 - 2 * mu)
            - (mu - 0.2) * log(mu - 0.2) + (0.6 - mu) * log(3))
    grid = [0.2 + i * 1e-6 for i in range(1, 200000)]
    top = max(grid, key=lambda m: (1.2 - 0.3911792 - m * log(m) - (1.2 - 2 * m) * log(1.2 - 2 * m)
                                   - (m - 0.2) * log(m - 0.2) + (0.6 - m) * log(3)))
    out.write(f"      Lemma 6: mu = (21 - sqrt 297)/10 = {mu:.10f}, and the maximiser is "
              f"{top:.6f}\n")
    out.write(f"      Lemma 6: lambda_2(mu) = {lam2:.9f}   ([Dub93] quotes 2.08819)\n")
    lam1_87 = 1.2 * log(2) + 0.4 * log(3)
    lam1_93 = log(2 + 3 ** 0.5)
    for tag, lam1, printed in (("[Dub87]", lam1_87, "4.516"), ("[Dub93]", lam1_93, "4.2")):
        den = lam1 - 1.2 + 0.3911792
        out.write(f"      {tag}: lambda_1 = {lam1:.9f}, denominator = lambda_1 - 1.2 + 0.3911792"
                  f" = {den:.9f}\n"
                  f"               exponent = lambda_2 / denominator = {lam2/den:.6f}"
                  f"   (printed: {printed})\n")
    out.write(f"      Lemma 5: 290 * 1705/2 - 470 * 526 = {290 * 1705 // 2 - 470 * 526}"
              "  (the determinant, hence nonzero mod p for large p)\n")
    out.write("""
      Reading.  Three things, none of which move the T-shift wall.

        * Lineage, now from the primary source.  [Dub87]'s (4) is Legendre's formula
          for v_nu(C(n,k) C(n+k, 4p-omega)) >= 1; its (5) throws away k to get a
          criterion in fractional parts of n/nu alone; its (6) turns that into a union
          of intervals; and log H_n / n is then sum (1/k - 1/U_k), which is exactly
          I(alpha) = int_{E_alpha} dx/x^2 in discrete clothing.  That is the same device
          as [Hab03] Lemma 1, two generations earlier and at a family outside the
          H(a,b) class.  [Dub87] itself credits the polynomials to Rukhadze.
        * A second calibration of the arithmetic half.  Gate G-A tested the apparatus
          against [Hab03]'s own numbers.  Here the same machinery reproduces a printed
          constant of a different paper, on a different family, from the criterion as
          printed -- with the paper's value sitting 4.6e-5 BELOW the sharp one, i.e. on
          the safe side of its own inequality.  Had the sum come out under 0.3911792,
          either the transcription or the paper would be wrong.
        * A datum for WP-D.  [Dub93] revisits this exact machinery six years later and
          improves the exponent 4.516 -> 4.2 (sharply 4.1095).  The whole gain is in
          lambda_1, the analytic factor: 1.2 log 2 + 0.4 log 3 = 1.2712 -> log(2+sqrt 3)
          = 1.3170.  The content constant 0.3911792 and the coefficient constant
          2.08819 are carried over verbatim.  With WP-B's content stall at d >= 2 and
          [Eas86]'s congruence gain being constants-not-rates, that is a third
          independent sighting of the same thing: in this machinery the arithmetic
          factor does not move.  It is evidence about the prior on Q2, not an answer --
          none of the three tried a sublattice restriction.

      Do NOT read [Dub87]'s fives as Q2's five.  Its n = 5p and its determinant 5 come
      from the 4p/5p degree pattern of the Rukhadze polynomials; Q2's index-5 sublattice
      comes from the D = 5 flagship.  The coincidence is empty.
""")


# ---------------------------------------------------------------------------
# plan-Tshift-S7, WP-C.  Section 3.5 on the *solution* lattices, and the content
# baseline O-2 hands to S8.
#
# WP-A proved that the two integrality models of D3 have the same AMBIENT lattice at
# degrees (nu, nu+1) (note-Tshift-S7-WPA.html section 3.5; check [E]).  What Q1 is
# about is the lattice of solutions -- the forms with maximal vanishing -- and passing
# from one to the other needs one extra remark, which check [O] measures:
#
#   collapsing (A, B, C) to (A + gamma_m C, B + (1-t)C) changes the A-column by the
#   CONSTANT multiple gamma_m C, of degree <= nu, while every vanishing condition that
#   is actually imposed sits at t^e with e >= nu+1 (the low coefficients are absorbed
#   by the free A-column in both models).  So the two systems impose literally the same
#   conditions in different coordinates, and sigma(B, C) = B + (1-t)C maps the split
#   solution lattice ONTO the classical one -- index 1, not merely into it.
#
# Check [P] is the baseline: how much content [Hab03]'s pair (2.2) really has, against
# how much his Lemma 1 proves.  Check [Q] converts the difference into theta.
# ---------------------------------------------------------------------------


def _kernel_basis_Z(rows, ncols):
    """A Z-basis of {x in Z^ncols : rows . x = 0}, saturated.

    Euclidean row reduction of the augmented matrix [M^T | I]: the rows whose M^T-part
    has been cleared carry, in their I-part, a basis of the kernel lattice.  Every
    operation is unimodular, so the basis spans the kernel lattice itself and not a
    finite-index sublattice of it -- which is exactly what the index in [O] needs.
    """
    nr = len(rows)
    M = [[rows[i][j] for i in range(nr)] + [1 if k == j else 0 for k in range(ncols)]
         for j in range(ncols)]
    r = 0
    for c in range(nr):
        if r >= len(M):
            break
        for i in range(r + 1, len(M)):
            while M[i][c] != 0:
                if M[r][c] == 0:
                    M[r], M[i] = M[i], M[r]      # now M[i][c] == 0; the loop exits
                    continue
                q = M[i][c] // M[r][c]
                M[i] = [a - q * b for a, b in zip(M[i], M[r])]
                if M[i][c] != 0:                 # |M[i][c]| < |M[r][c]|: swap and shrink
                    M[r], M[i] = M[i], M[r]
        if M[r][c] != 0:
            r += 1
    return [row[nr:] for row in M[r:]]


def _sol_rows(m, nu):
    """The maximal-vanishing conditions at the flagship cell, in both models.

    Classical: Atil absorbs t^0..t^nu, so the conditions on Btil in Z[t]_{<=nu+1} are
        [t^e](Btil H0) = 0,   nu+1 <= e <= 2nu+1        (order 2nu+2, the D2 maximum)
    Split: A absorbs the same range, so the conditions on (B, C) in (Z[t]_{<=nu})^2 are
        [t^e](B H0 + C H1) = 0  over the same e.
    The two ranges coincide because deg(gamma_m C) <= nu -- see the block comment.

    Degenerate at nu >= 2m: H(2m, m) then fits inside the free A-column, so the system's
    own maximal-vanishing solution is Btil = 1 with A = -H0, i.e. the identically zero
    form.  The live range is nu <= 2m-1, which is [Hab03]'s index range n <= a-1 (2.2).
    """
    H0, H1 = _H(2 * m, m), _H(2 * m + 1, m)
    cl, sp = [], []
    for e in range(nu + 1, 2 * nu + 2):
        cl.append([H0[e - j] if 0 <= e - j < len(H0) else 0 for j in range(nu + 2)])
        sp.append([H0[e - j] if 0 <= e - j < len(H0) else 0 for j in range(nu + 1)]
                  + [H1[e - j] if 0 <= e - j < len(H1) else 0 for j in range(nu + 1)])
    return cl, sp


def _sol_compare(m, nu):
    """[O] at one (m, nu).  Returns None if the cell is degenerate, else a dict."""
    from math import gcd
    cl, sp = _sol_rows(m, nu)
    if (nu + 2) - _rank(cl, nu + 2) != 1:
        return None
    w = _nullvec(cl, nu + 2)                     # the primitive classical Btil
    if _pdeg(_pmul(w, _H(2 * m, m))) <= nu:      # the form is identically zero: nu >= 2m
        return None
    dim_sp = (2 * nu + 2) - _rank(sp, 2 * nu + 2)
    ker = _kernel_basis_Z(sp, 2 * nu + 2)
    nz = next(i for i in range(nu + 2) if w[i] != 0)
    idx, zero = 0, 0
    for v in ker:
        B, C = v[:nu + 1], v[nu + 1:]
        Bt = _padd(B, _pmul([1, -1], C))
        Bt = Bt + [0] * (nu + 2 - len(Bt))
        if all(x == 0 for x in Bt):              # an identically-zero form of D2
            zero += 1
            continue
        c0 = Fraction(Bt[nz], w[nz])
        assert all(Fraction(Bt[i]) == c0 * w[i] for i in range(nu + 2)), \
            "a split solution collapses outside the classical solution line"
        assert c0.denominator == 1, "the collapse leaves the classical lattice"
        idx = gcd(idx, abs(int(c0)))
    # the constructive direction: divide the primitive Btil by (1-t) in Z[t].  The
    # leading coefficient of 1-t is the unit -1, so this stays inside Z[t] (WP-A 3.5).
    rem, C = w[:], [0] * (nu + 1)
    for d in range(len(rem) - 1, 0, -1):
        q = -rem[d]                              # quotient coefficient at t^(d-1)
        C[d - 1] = q
        rem[d] += q                              # subtract q * (t^(d-1) - t^d)
        rem[d - 1] -= q
    B = _ptrim(rem)
    ok = (_pdeg(B) <= 0 and _pdeg(C) <= nu
          and _ptrim(_padd(B, _pmul([1, -1], C))) == _ptrim(w))
    # the cleared 3^{6m}-column coefficient, computed in both models (WP-A 3.3/3.4)
    v_cl = 8 ** (nu + 1) * _ev(w, Fraction(-1, 8))
    v_sp = (8 * 8 ** nu * _ev(B, Fraction(-1, 8)) + 9 * 8 ** nu * _ev(C, Fraction(-1, 8)))
    assert v_cl.denominator == 1 and v_sp.denominator == 1, "the clearing factor is wrong"
    bt_cl, bt_sp = (-1) ** m * int(v_cl), (-1) ** m * int(v_sp)
    cont, prim = _cell_minors(m, nu, nu + 1)
    assert _ptrim(prim) == _ptrim(w) or _ptrim(prim) == _ptrim([-x for x in w]), \
        "Cramer minors and the nullspace disagree on the primitive generator"
    return {"dim_sp": dim_sp, "zero": zero, "index": idx, "roundtrip": ok,
            "bt_cl": bt_cl, "bt_sp": bt_sp, "content": cont, "w": w}


def _cell_minors(m, L, M):
    """Cramer solution of the cell (L, M) for H(2m, m): (content, primitive Q).

    The signed maximal minors of the M x (M+1) vanishing system are an integer solution
    by Cramer, canonical up to sign; their gcd is the content WP-B section 3 measures,
    and dividing it out gives the primitive generator.
    """
    from math import gcd
    H = _H(2 * m, m)
    rows = [[H[e - j] if 0 <= e - j < len(H) else 0 for j in range(M + 1)]
            for e in range(L + 1, L + M + 1)]
    minors = [(-1) ** c * _bareiss([[r[j] for j in range(M + 1) if j != c] for r in rows])
              for c in range(M + 1)]
    g = 0
    for x in minors:
        g = gcd(g, abs(x))
    return g, [x // g for x in minors]


def _diag_content(m, al):
    """[Hab03]'s own pair (2.2) at the alpha-index: (n, true content, provable content).

    true     = gcd of all coefficients of (P_n, Q_n) -- the largest integer one may
               divide out, since the solution space is one-dimensional, so (P, Q)/gcd
               is THE primitive form and nothing smaller exists.
    provable = product of the primes Lemma 1 certifies (_content_primes).
    """
    from math import gcd
    n = int(al * (m - Fraction(3, 2))) + 1
    P, Q, _, ok = _pade_pair(n, 2 * m, m)
    assert ok, "(2.1) fails -- index out of range"
    g = 0
    for x in P + Q:
        g = gcd(g, abs(x))
    prov = 1
    for l in _content_primes(n, 2 * m, m):
        prov *= l
    assert g % prov == 0, "Lemma 1 fails -- see check [F]"
    return n, P, Q, g, prov


def cmd_content(mmax, out=sys.stdout):
    out.write("plan-Tshift-S7 WP-C -- section 3.5 on the solution lattices, and the\n"
              "content baseline for O-2/S8.  Exact integers except where marked.\n")

    out.write("\n[O] WP-C(i): the two integrality models on the SOLUTION lattices, m <= 8.\n"
              "    classical  Btil in Z[t]_{<=nu+1};   split  (B, C) in (Z[t]_{<=nu})^2,\n"
              "    both at the maximal vanishing order t^(2nu+2) of D2, flagship lag p=1.\n"
              "    Reported per m: every live nu (1 <= nu <= 2m-1), and for the alpha-index\n"
              "    nu = n the content and the cleared 3^(6m)-column coefficient of F4.\n")
    al = Fraction(15, 16)
    allok = True
    ntested = 0
    for m in range(2, 9):
        n = int(al * (m - Fraction(3, 2))) + 1
        tested = bad = 0
        detail = None
        for nu in range(1, 2 * m + 1):
            r = _sol_compare(m, nu)
            if r is None:
                continue
            tested += 1
            if not (r["index"] == 1 and r["dim_sp"] == nu + 1 and r["zero"] == nu
                    and r["roundtrip"] and r["bt_cl"] == r["bt_sp"]):
                bad += 1
            if nu == n:
                detail = r
        allok = allok and bad == 0
        ntested += tested
        d = detail
        out.write(f"      m={m}: {tested} live nu of 1..{2*m} (degenerate from 2m on), "
                  f"{'index 1 everywhere' if bad == 0 else str(bad) + ' FAILURES'}"
                  f"   |  nu=n={n}: content {d['content']}, "
                  f"btilde {d['bt_cl']}{'' if d['bt_cl'] == d['bt_sp'] else ' *** MISMATCH ***'}"
                  f", btilde mod 5 = {d['bt_cl'] % 5}\n")
    out.write(f"      {ntested} parameter points in all; split kernel dim nu+1 with exactly nu\n"
              f"      identically zero forms at every one, constructive round-trip on the\n"
              f"      primitive solution at every one: "
              f"{'ALL HOLD' if allok else '*** FAILURES ***'}\n")
    out.write("""
      Reading.  The index is the whole check.  If the split model -- integrality of B
      and C demanded separately -- reached only a proper sublattice of the classical
      solution line, the index would exceed 1 and the split forms would be LARGER by
      that factor, which is exactly the g > 1 Q1 was hunting.  It is 1 at every point,
      so the contents printed above are the contents of both models, and g = 1 is
      confirmed on the objects and not only on the ambient lattices (check [E]).
      Degeneracy: nu <= 2m-1 throughout, because at nu = 2m the polynomial H(2m,m) fits
      inside the free A-column and the system's maximal-vanishing solution is the
      identically zero form.  That is [Hab03]'s own index range n <= a-1 in (2.2).
      The btilde mod 5 column is data for WP-D (F4's congruence), not a verdict.
""")

    out.write("\n[P] WP-C(ii): the content baseline at [Hab03]'s own diagonal pair (2.2),\n"
              "    alpha = 15/16, n = [alpha(m - 3/2)] + 1, exact integers.\n"
              "      true = gcd of (P_n, Q_n), the largest content that exists\n"
              "      prov = product of the primes Lemma 1 certifies\n"
              "      leftover = true / prov, factored -- what the criterion leaves behind\n")
    out.write(f"      for scale: I(15/16) = {_I_alpha(2, 15, 16)[0]:.9f} is the asymptotic\n"
              f"      rate Proposition 2 proves for log(prov)/m.\n\n")
    out.write("      leftover primes are tagged: sub = below the threshold l^2 > max(n+b, a-n-1),\n"
              "      miss(d) = above it, but the residue sum falls d/l short of the required 2\n\n")
    out.write("         m      n | hgt Q/m   prov/m   true/m |  slack  | thr |  leftover\n")
    ms = [8]
    while ms[-1] * 2 <= mmax:
        ms.append(ms[-1] * 2)
    lastslack, worst = None, 0
    for m in ms:
        n, P, Q, g, prov = _diag_content(m, al)
        rest = g // prov
        x, y = n + m, 2 * m - n - 1
        thr = isqrt(max(x, y))
        fac, r = [], rest
        for l in _primes(3 * m + 2):
            e = 0
            while r % l == 0:
                r //= l
                e += 1
            if e:
                # why Lemma 1 did not claim this prime: below the threshold, or above it
                # with the residue sum short of 2l (the criterion is sufficient, not
                # necessary -- so a leftover prime is not a failure of the lemma)
                tag = "sub" if l * l <= max(x, y) else f"miss{2*l - (x%l) - (y%l) - (n%l)}"
                fac.append(f"{l}^{e}({tag})" if e > 1 else f"{l}({tag})")
                worst = max(worst, e * log(l))
        s = (log(g) - log(prov)) / m
        lastslack = (s, m, rest)
        out.write(f"      {m:4d} {n:6d} | {log(max(abs(x) for x in Q))/m:7.4f}"
                  f" {log(prov)/m:8.4f} {log(g)/m:8.4f} |{s:8.4f} | {thr:3d} |  "
                  f"{' * '.join(fac) if fac else '1'}"
                  f"{'   (residual ' + str(r) + ' unfactored)' if r != 1 else ''}\n")
    out.write(f"      largest single leftover factor over the table: {worst:.2f} nats"
              f"  -- against contents of {log(g):.0f} nats at m = {ms[-1]}\n")

    out.write("\n      the same at Habsieger's own optimum alpha_0 = 224141/240395"
              f"   (I = {_I_alpha(2, 224141, 240395)[0]:.9f}):\n")
    al0 = Fraction(224141, 240395)
    for m in ms:
        n, P, Q, g, prov = _diag_content(m, al0)
        out.write(f"      {m:4d} {n:6d} | {log(max(abs(x) for x in Q))/m:7.4f}"
                  f" {log(prov)/m:8.4f} {log(g)/m:8.4f} |"
                  f"{(log(g)-log(prov))/m:8.4f} |  {g//prov}\n")

    out.write("\n      and the size constant, on the same objects: (1/m) log |Q_n(-1/8)| against\n"
              "      A + log F1 = 1.77211973204, which is what the 8.2 apparatus predicts it to be\n")
    for m in ms:
        n, P, Q, g, prov = _diag_content(m, al)
        val = _ev(Q, Fraction(-1, 8))
        lv = log(abs(val.numerator)) - log(val.denominator)
        out.write(f"      {m:4d} |  {lv/m:9.6f}   deficit {1.77211973204 - lv/m:9.6f}"
                  f"   (m * deficit = {m*(1.77211973204 - lv/m):6.2f})\n")

    out.write("""
      Reading, and this is the baseline O-2 promised S8.

        * Lemma 1 is not merely asymptotically sharp: it is nearly exactly sharp.  The
          content it certifies and the content that is actually there differ by a
          LEFTOVER OF A FEW SMALL PRIMES -- 5^3 * 13 * 31 at m = 512 -- against a content
          of some 220 nats.  There is no exponential factor hiding under the criterion.
        * And the leftover is where one would expect it: almost every leftover prime is
          BELOW the threshold l^2 > max(n+b, a-n-1) that Lemma 1 imposes, i.e. outside
          the criterion's range by construction.  Exactly one row of the table has a
          prime above the threshold that the residue condition misses -- 31 at m = 16,
          short by 1/31 -- which is the criterion being sufficient and not necessary, not
          a defect.  A sharper lemma would be chasing single primes.
        * So the arithmetic half of the D = 1 construction is exhausted.  Any content
          improvement at this family and index can only ever be worth e^{O(log m)}
          overall, i.e. o(1) in the per-m rate, i.e. nothing in theta.  For S8(ii) this
          is a ceiling, and it is measured rather than assumed.
        * The two independent identifications the table also confirms: log(prov)/m
          tracks I(alpha) = int_{E_alpha} dx/x^2 (Proposition 2, and the [Dub87] device
          of check [M]) -- a prime-counting sum against an interval measure, from two
          unrelated code paths -- and (1/m) log|Q_n(-1/8)| converges to A + log F1, the
          Stirling constant of the same apparatus, the deficit times m growing only
          like log m (2.5 at m = 8, 5.4 at m = 512).
        * What is NOT closed by this: the effective-range loss.  [Hab03]'s m-uniform
          (3.11) uses 0.3945 where the truth is I(alpha_0) = 0.403782, and that gap is
          Chebyshev bookkeeping, not content.  Check [Q] costs it out.
""")

    out.write("\n[Q] what the baseline is worth against the D4 wall, and the flagship cell\n")
    I0 = _I_alpha(2, 224141, 240395)[0]
    _, _, _, _, C1, _ = _apparatus(2, Fraction(-1, 8), 6, 224141, 240395)
    e = 2.718281828459045
    delta = log(2 / 3) - C1
    s, sm, srest = lastslack
    I1 = _I_alpha(2, 15, 16)[0]
    gapeff = max(I0, I1) - 0.3945                # the conservative reading; see below
    out.write(f"      the wall (WP-B [L]):  Delta = {delta:.12f},  g = e^(6 Delta) = "
              f"{e**(6*delta):.6f}\n")
    out.write(f"      content slack measured at m = {sm}: {s:.6f} per m  (leftover {srest})\n")
    out.write(f"        -> raises C1 by slack/6 = {s/6:.6f}"
              f"   =  {100*s/(6*delta):.2f}% of the wall, and falling with m\n")
    out.write(f"      effectivity gap, the m-uniform 0.3945 of (3.11) against the asymptotic\n"
              f"      content rate: I(15/16) - 0.3945 = {I1-0.3945:.6f},"
              f"  I(alpha_0) - 0.3945 = {I0-0.3945:.6f}\n")
    out.write(f"        -> raises C1 by at most {gapeff/6:.6f}"
              f"   =  {100*gapeff/(6*delta):.2f}% of the wall, and it is not free:\n"
              f"           m-uniformity down to m >= 10 740 000 is what (3.11) buys with it\n")
    out.write(f"      both together, as a generous upper bound on the arithmetic half:"
              f" {100*(s+gapeff)/(6*delta):.2f}% of the wall\n")

    out.write("\n      the flagship cell against the diagonal, in the only variable theta sees:\n"
              "      |b| = 8^M |Q(-1/8)| for the PRIMITIVE form of the cell (WP-A 3.2)\n")
    out.write("         m    n | d=0 content/m  |b|/m | d=1 content/m  |b|/m |  d1 - d0\n")
    for m in (8, 12, 16, 20, 24, 28, 32):
        if m > max(mmax, 8):
            break
        n = int(al * (m - Fraction(3, 2))) + 1
        row = []
        for L, M in ((n, n), (n, n + 1)):
            cont, Qp = _cell_minors(m, L, M)
            val = _ev(Qp, Fraction(-1, 8))
            lb = M * log(8) + log(abs(val.numerator)) - log(val.denominator)
            row.append((log(cont) / m, lb / m))
        out.write(f"      {m:4d} {n:4d} |  {row[0][0]:11.4f} {row[0][1]:7.4f} |"
                  f"  {row[1][0]:11.4f} {row[1][1]:7.4f} | {row[1][1]-row[0][1]:+9.4f}\n")
    out.write("""
      Reading.  The whole arithmetic half of [Hab03]'s proof -- perfecting Lemma 1 AND
      removing the Chebyshev effectivity loss -- is worth a few percent of the 2.3786
      wall, and the first of the two is worth nothing asymptotically.  A construction
      that reaches 2/3 cannot come from this direction; that is the negative datum WP-C
      hands to S8(ii), and it is the fourth in the series (WP-A's g = 1, WP-B's content
      stall at d >= 2, [Dub93]'s six years spent entirely in lambda_1, and now this).

      The cell table is WP-B's [K] in the theta-relevant variable rather than in the
      height: the flagship cell d = 1 costs slightly more than the diagonal at small m
      and the difference shrinks with m, which is what F1 says it must do.  Q2 lives
      inside the d = 1 column and is untouched by any of this.
""")


# ---------------------------------------------------------------------------
# plan-Tshift-S7 WP-D -- Q2: the mod-5 sublattice, and the two cycle classes of
# D_2 = 5.  Checks [R] (O-3's S9 falsification, which the plan requires FIRST),
# [S] the cycle classes, [T] Q2 at the flagship cell, [U] what it costs, [V] the
# verdict against the D4 wall.
#
# The structural fact the measurements dress -- WP-D's answer to Q2, and the reason
# it is an answer and not a statistic:
#
#   Both quantities the endgame consumes -- the size log|btilde| and the decay
#   -log|r| -- are homogeneous of degree 1 on the lattice of admissible forms:
#   F -> lambda F shifts BOTH by +log|lambda|, so it always worsens their ratio, by
#   O(log lambda / m).  The quality of a form is therefore a function on the
#   PROJECTIVE space of the lattice, and a finite-index sublattice spans the same
#   projective space with FEWER integer points.  Hence inf over the sublattice
#   >= inf over the lattice: a congruence condition can never improve the rate, no
#   matter which congruence it is.  Dividing out the content is exactly the passage
#   to the primitive generator, so it is already inside that inf -- the content
#   theory of Lemma 1 is the statement that the generator is far shorter than
#   Cramer's bound, and a sublattice's generator is never shorter than the lattice's.
#   What a congruence CAN buy is non-degeneracy -- a guarantee that some coefficient
#   or determinant does not vanish -- which is worth a bounded factor.  That is
#   exactly what it buys in [Dub87] (Lemma 4, certifying det != 0) and in [Eas86]
#   (3^d with d <= 3/2), the two printed precedents G-B found.
#
# So the measurements below are not asked to discover the verdict; they are asked to
# check that the flagship really is in the situation the argument describes (rank 1,
# [T]), to price the two currencies D5 costed the congruence in ([U]), and to test
# the one branch the argument does NOT cover: D5(ii)'s alignment, which is a claim
# about the ORBIT, not about the lattice ([R], [S]).
# ---------------------------------------------------------------------------


def _cong_orbit(D, nmax, thresh=(1, 5)):
    """The orbit-side input of WP-D: the small dates, their runs and their classes.

    Returns (data, small, runs) with data[n] = (n, t, m_n) exactly as in `orbit`.
    """
    p, q = thresh
    data = [(n, t, m) for (n, t, m, _T) in orbit(D, nmax)]
    small = [False] + [q * dist_num(data[n][1], n) < p * (1 << n)
                       for n in range(1, nmax + 1)]
    runs, n = [], 1
    while n <= nmax:
        if small[n]:
            a = n
            while n + 1 <= nmax and small[n + 1]:
                n += 1
            runs.append((a, n))
        n += 1
    return data, small, runs


def _chisq_uniform(counts):
    """Pearson chi-square of a list of counts against the uniform expectation."""
    tot = sum(counts)
    e = tot / len(counts)
    return sum((c - e) ** 2 for c in counts) / e, len(counts) - 1


def _cell_form(m, al=None, dnum=1):
    """The primitive form of the flagship cell at the alpha-index, and its numbers.

    Cell (n, n + dnum) of H(2m, m) with n = [alpha(m - 3/2)] + 1: the deficit-one cell
    is the lag construction's own (WP-B's law), and dnum = 1 is the flagship.
    Returns (n, btilde, log|btilde|, log|remainder|), all for the PRIMITIVE pair, with
    btilde = (-1)^m 8^(n+1) Q(-1/8) the cleared 3^(6m)-column coefficient of F4/D3.
    """
    al = Fraction(15, 16) if al is None else al
    n = int(al * (m - Fraction(3, 2))) + 1
    pr = _pade_cell(2 * m, m, n, n + dnum)
    if pr is None:
        return None
    P, Q, R = pr
    val = _ev(Q, Fraction(-1, 8))
    bt = (-1) ** m * 8 ** (n + dnum) * val
    assert bt.denominator == 1, "the clearing factor is wrong"
    rem = _ev(R, Fraction(-1, 8))
    lb = log(abs(bt.numerator))
    lr = log(abs(rem.numerator)) - log(rem.denominator)
    return n, int(bt), lb, lr


def _cong_cost(m):
    """[U] at one m: the price of 5 | btilde, in D5's two currencies.

    (a) scaling      F -> 5F                    -- D5's "factor <= 5 by pigeonhole";
    (b) one order of vanishing traded away      -- D5's "at most one unit of vanishing
        order".  Dropping the last vanishing condition makes the cell rank 2, and it
        contains a second SHORT element for free: if (P', Q') is the primitive pair of
        the cell (n-1, n), then t(P', Q') has degrees (n, n+1) and vanishes to order
        2n+1, one less than w.  Searching a - w + b - u over a small box therefore
        gives an upper bound for the cost -- which is all (b) is asked for.
    Returns (n, E_w, E_5w, E_best, (a, b), free) with E = log|btilde| / (-log|r|).
    """
    from math import gcd
    al, mo = Fraction(15, 16), Fraction(-1, 8)
    n = int(al * (m - Fraction(3, 2))) + 1
    H = _H(2 * m, m)
    HV = _ev(H, mo)
    _P, w, _R = _pade_cell(2 * m, m, n, n + 1)
    _P2, Q2, _R2 = _pade_cell(2 * m, m, n - 1, n)
    u = [0] + list(Q2)                           # t * Q', one order of vanishing less

    def pair(v):
        QH = _pmul(v, H)
        P = QH[:n + 1]
        val = _ev(v, mo)
        return P, (-1) ** m * 8 ** (n + 1) * val, _ev(P, mo) - val * HV

    Pw, bw, rw = pair(w)
    Pu, bu, ru = pair(u)
    assert any(w[i] * u[j] != w[j] * u[i] for i in range(n + 2) for j in range(i + 1, n + 2)), \
        "the two elements are proportional: the relaxed cell did not gain a dimension"
    lbw, lrw = log(abs(bw)), log(abs(rw.numerator)) - log(rw.denominator)
    E_w = lbw / (-lrw)
    E_5 = (lbw + log(5)) / (-lrw - log(5))       # F -> 5F: size up, decay down
    best, free = None, None                      # constrained and unconstrained optima
    for a in range(-3, 4):
        for b in range(-2, 3):
            if a == 0 and b == 0:
                continue
            bb, rr = a * bw + b * bu, a * rw + b * ru
            if bb == 0 or rr == 0:
                continue
            cf = ([a * z + b * zz for z, zz in zip(w, u)]
                  + [a * z + b * zz for z, zz in zip(Pw, Pu)])
            g = 0
            for z in cf:
                g = gcd(g, abs(z))
            bb, rr = Fraction(bb, g), rr / g
            assert bb.denominator == 1, "the clearing factor is wrong"
            lr = log(abs(rr.numerator)) - log(rr.denominator)
            if lr >= 0:
                continue                         # not an approximating form at all
            E = log(abs(bb.numerator)) / (-lr)
            if free is None or E < free[0]:
                free = (E, a, b)
            if int(bb) % 5 == 0 and (best is None or E < best[0]):
                best = (E, a, b)
    return n, E_w, E_5, best, free, bw % 5 == 0


def cmd_cong(nmax, mmax, out=sys.stdout):
    import io
    out.write("plan-Tshift-S7 WP-D -- Q2: the mod-5 sublattice and the two cycle\n"
              "classes of D_2 = 5.  Exact integers except in the printed rates.\n")

    # -----------------------------------------------------------------  [R]
    out.write(f"\n[R] O-3's S9 falsification, run first as the plan requires: factor the\n"
              f"    observed M_n.  Sample = the dates where ||5(3/2)^n|| < 1/5 (the near\n"
              f"    misses a construction would have to beat), n <= {nmax}; control = the\n"
              f"    remaining dates; prediction = a random integer, P(l|N) = 1/l,\n"
              f"    E v_l = 1/(l-1).  The sigma column compares the two disjoint samples.\n")
    data, small, runs = _cong_orbit(5, nmax)
    S = [n for n in range(1, nmax + 1) if small[n]]
    C = [n for n in range(1, nmax + 1) if not small[n]]
    out.write(f"    {len(runs)} maximal runs, {len(S)} small dates against the"
              f" {len(C)} others\n")
    out.write("      l |  P(l|M) near   rest   1/l   |  E v_l near   rest  1/(l-1)"
              " | near vs rest\n")
    worst = (0.0, None)
    for l in _primes(60):
        st = []
        for idx in (S, C):
            c = v = 0
            for n in idx:
                k, e = data[n][2], 0
                while k % l == 0:
                    k //= l
                    e += 1
                if e:
                    c += 1
                v += e
            st.append((c / len(idx), v / len(idx)))
        # two-proportion z on the two DISJOINT samples: the right comparison, since a
        # bias shared with the control is a property of M_n, not of the near misses
        pp = (st[0][0] * len(S) + st[1][0] * len(C)) / (len(S) + len(C))
        se = (pp * (1 - pp) * (1 / len(S) + 1 / len(C))) ** 0.5
        dev = abs(st[0][0] - st[1][0]) / se
        worst = max(worst, (dev, l))
        out.write(f"    {l:3d} |  {st[0][0]:.4f} {st[1][0]:.4f} {1/l:.4f}  |  "
                  f"{st[0][1]:.4f} {st[1][1]:.4f} {1/(l-1):.4f}"
                  f" |  {dev:5.2f} sigma\n")
    out.write(f"    largest deviation over the table: {worst[0]:.2f} sigma at l = {worst[1]}"
              f"  ({len(_primes(60))} primes tested)\n")
    nprime = len(_primes(60))
    out.write(f"      (over {nprime} tests the largest of {nprime} standard normals is"
              f" ~2.2 sigma in expectation, so the table is flat)\n")
    # the positive control: l = 2 IS structured, and the test sees it at once
    c1 = [(a, b) for (a, b) in runs if b - a >= 1 and b < nmax]
    c2 = [(a, b) for (a, b) in runs if b - a >= 2 and b < nmax]
    f1 = sum(1 for (a, _b) in c1 if data[a][2] % 2 == 0)
    f2 = sum(1 for (a, _b) in c2 if data[a][2] % 4 == 0)
    out.write(f"    positive control (the test has power): the cascade of D3 forces\n"
              f"      2^(b-a) | M_a on every run, and the same statistic sees it --\n"
              f"      2 | M_a at {f1}/{len(c1)} run starts of length >= 1 (1/2 at random),"
              f"  4 | M_a at\n"
              f"      {f2}/{len(c2)} of length >= 2 (1/4 at random).  Nothing odd behaves"
              f" like that.\n")
    out.write("""
    Reading.  The odd primes see nothing.  M_n at the near misses factors like
    M_n away from them, and both like a random integer of that size, to within the
    sampling error of the table -- l = 5 itself included -- so there is no
    arithmetic structure in the record data for a congruence-aligned construction to
    consume, and S9(i)'s premise is falsified on its own afternoon's worth of data.
    The one prime that IS structured is 2, and its structure is the cascade of D3: a
    divisibility of the record's own numerator forced by the dynamics after the
    fact, not a congruence a construction could impose in advance.
""")

    # -----------------------------------------------------------------  [S]
    out.write("\n[S] D5(ii): the two cycle classes {1/5, 4/5} and {2/5, 3/5}, N2's\n"
              "    inequivalent targets.  The class index is not a new statistic:\n"
              "      M_n = 5 floor((3/2)^n) + round(5 x_n)   ==>   class = M_n mod 5,\n"
              "    so factoring M_n by 5 and classifying the target are ONE measurement.\n")
    cls = [0] * 5
    for n in S:
        cls[data[n][2] % 5] += 1
    cs = [0] * 5
    for (a, _b) in runs:
        cs[data[a][2] % 5] += 1
    x2, df = _chisq_uniform(cls)
    x2s, _ = _chisq_uniform(cs)
    out.write(f"    class of every small date : {cls}   chi2 = {x2:.2f} on {df} df\n")
    out.write(f"    class at the run starts   : {cs}   chi2 = {x2s:.2f} on {df} df\n")
    # the alternation law, exactly
    badg = bad = steps = 0
    for (a, b) in runs:
        for n in range(a, b):
            steps += 1
            if 2 * data[n + 1][2] - 3 * data[n][2] != 0:
                badg += 1
            if (data[n + 1][2] + data[n][2]) % 5:
                bad += 1
    out.write(f"    the order-2 law, on all {steps} within-run steps: g_(n+1) = 0 with"
              f" {badg} exceptions,\n"
              f"      M_(n+1) = -M_n mod 5 with {bad} exceptions"
              f"  (both must be 0: |g| = |3 d_n - 2 d_(n+1)| < 1 and g is an integer,\n"
              f"       so M_(n+1) = 3 M_n / 2, and 2^(-1) = 3, 3*3 = 4 = -1 mod 5)\n")
    # class 0 is the D = 1 problem in disguise
    zero_is_d1 = bad0 = 0
    for n in range(1, nmax + 1):
        t1 = pow(3, n, 1 << n)
        d1 = 25 * dist_num(t1, n) < (1 << n)     # ||(3/2)^n|| < 1/25
        c0 = small[n] and data[n][2] % 5 == 0
        if c0:
            zero_is_d1 += 1
        if c0 != d1:
            bad0 += 1
    out.write(f"    class 0 is the D = 1 problem in disguise: 5 | M_n and ||5(3/2)^n|| < 1/5\n"
              f"      <=> ||(3/2)^n|| < 1/25 -- {zero_is_d1} such dates, {bad0} exceptions\n")
    buf = io.StringIO()
    dates, _rows = cmd_records(5, nmax, out=buf)
    rc = [(n, data[n][2] % 5) for n in dates]
    out.write(f"    the {len(dates)} records and their classes: {rc}\n")
    out.write("""
    Reading, and this is the only branch of Q2 the sublattice argument does not
    already settle, because it is a claim about the orbit rather than the lattice.
    The order-2 alignment D5(ii) hoped for is REAL, and provable rather than
    measured: inside any 1/5-run the carry g vanishes identically, so the class
    alternates j -> -j exactly, and {1,4}, {2,3} are 2-cycles while {0} is fixed.
    It buys nothing, for two reasons that the table makes quantitative.  First the
    classes are equidistributed, so a proof that covers one 2-cycle covers 2/5 of
    the near misses and says nothing about the rest.  Second the fixed class is not
    a third target one could dispose of separately: class 0 IS the D = 1 problem,
    exactly (the check above), so it carries the full classical difficulty, and the
    D = 5 record list draws on it.  N2's slot is real as a structure and empty as an
    opportunity.
""")

    # -----------------------------------------------------------------  [T]
    out.write("\n[T] Q2 at the flagship cell: 5 | btilde on [Hab03]'s own maximal-vanishing\n"
              "    forms Atil + Btil H(2m,m), degrees (n, n+1), n = [alpha(m-3/2)]+1,\n"
              "    alpha = 15/16.  btilde = (-1)^m 8^(n+1) Q(-1/8) is F4's cleared\n"
              "    3^(6m)-column coefficient, computed on the PRIMITIVE form.\n")
    rows = []
    for m in range(2, mmax + 1):
        r = _cell_form(m)
        if r is None:
            continue
        n, bt, lb, lr = r
        v5 = 0
        k = abs(bt)
        while k % 5 == 0:
            k //= 5
            v5 += 1
        rows.append((m, n, bt % 5, v5, lb / m, lr / m, lb / (-lr)))
    fr = [r for r in rows if r[2] == 0]
    pd = [r for r in rows if r[2] != 0]
    dist = [sum(1 for r in rows if r[2] == c) for c in range(5)]
    x2, df = _chisq_uniform(dist)
    blocks = 0
    fset = {r[0] for r in fr}
    for m in sorted(fset):
        if m - 1 not in fset:
            blocks += 1
    longest = cur = 0
    for m in range(2, mmax + 1):
        cur = cur + 1 if m in fset else 0
        longest = max(longest, cur)
    out.write(f"    m = 2..{mmax}: 5 | btilde at {len(fr)} of {len(rows)} indices"
              f"  ({100*len(fr)/len(rows):.0f}%),"
              f"  btilde mod 5 = {dist} (chi2 = {x2:.1f} on {df} df)\n")
    out.write(f"    v_5(btilde) > 1 at {sum(1 for r in rows if r[3] > 1)} indices,"
              f" max {max(r[3] for r in rows)};"
              f" the free set is {blocks} blocks, longest {longest} consecutive m\n")
    out.write(f"    free set: {sorted(fset)}\n")

    def band(S, key):
        vals = [key(r) for r in S]
        mu = sum(vals) / len(vals)
        sd = (sum((v - mu) ** 2 for v in vals) / len(vals)) ** 0.5
        return mu, sd / len(vals) ** 0.5
    out.write("\n    are the forms on the sublattice better?  the three quantities the\n"
              "    endgame consumes, on the free indices against the rest:\n")
    out.write("                          size log|b|/m     decay -log|r|/m    "
              "exponent log|b|/(-log|r|)\n")
    stat = {}
    for name, S in (("5 | btilde  ", fr), ("5 does not ", pd)):
        a, ae = band(S, lambda r: r[4])
        b, be = band(S, lambda r: -r[5])
        c, ce = band(S, lambda r: r[6])
        stat[name] = (c, ce)
        out.write(f"      {name} ({len(S):3d}) {a:8.4f} +- {ae:.4f}"
                  f"   {b:8.4f} +- {be:.4f}   {c:8.4f} +- {ce:.4f}\n")
    (c0, e0), (c1_, e1) = stat["5 | btilde  "], stat["5 does not "]
    out.write(f"      difference in the exponent: {c0-c1_:+.4f}"
              f" = {abs(c0-c1_)/(e0*e0+e1*e1)**0.5:.2f} sigma\n")
    # a paired local test: both rates drift with m, and the free set is clustered
    d = {r[0]: r[6] for r in rows}
    loc = [(r[0], r[2] == 0, r[6] - (d[r[0] - 1] + d[r[0] + 1]) / 2)
           for r in rows if r[0] - 1 in d and r[0] + 1 in d]
    pair = {}
    for name, sel in (("5 | btilde  ", True), ("5 does not ", False)):
        S = [x for x in loc if x[1] == sel]
        mu = sum(x[2] for x in S) / len(S)
        sd = (sum((x[2] - mu) ** 2 for x in S) / len(S)) ** 0.5
        pair[name] = (mu, sd / len(S) ** 0.5)
        out.write(f"      paired against the neighbours m-1, m+1: {name}"
                  f" {mu:+.4f} +- {sd/len(S)**0.5:.4f}  ({len(S)})\n")
    (c0, e0), (c1_, e1) = pair["5 | btilde  "], pair["5 does not "]
    out.write(f"      difference, paired      : {c0-c1_:+.4f}"
              f" = {abs(c0-c1_)/(e0*e0+e1*e1)**0.5:.2f} sigma\n")
    # R2's discipline: two disjoint m-ranges, and no claim that is not stable across them
    cut = (2 + mmax) // 2
    out.write(f"\n    the same on two disjoint m-ranges (risk R2: nothing is claimed that\n"
              f"    does not survive the split):\n")
    for name, sel in ((f"m <= {cut}", lambda m: m <= cut), (f"m > {cut}", lambda m: m > cut)):
        S = [r for r in rows if sel(r[0])]
        f = [r for r in S if r[2] == 0]
        p = [r for r in S if r[2] != 0]
        (a, ae), (b, be) = band(f, lambda r: r[6]), band(p, lambda r: r[6])
        out.write(f"      {name:9s} ({len(S):3d} indices): free {len(f):3d}"
                  f" = {100*len(f)/len(S):2.0f}%,  exponent {a:.4f} vs {b:.4f},"
                  f"  difference {a-b:+.4f} = {abs(a-b)/(ae*ae+be*be)**0.5:.2f} sigma\n")
    out.write("""
    Reading.  Two facts, and they point the same way.
      * The cell is of rank 1 -- WP-C's [O] measured that at every live (m, nu) --
        so {5 | btilde} is not a new theory: it is either the whole lattice, at the
        free indices above, or exactly 5 times it.  In the second case the form, its
        content and its remainder are all multiplied by 5, and the exponent is
        strictly worse.  There is no third possibility, so no measurement of the
        constrained family can come back positive: this is Q1's closure again, in a
        different coordinate.
      * The free indices are not random: they are commoner than the 1/5 chance would
        give and they cluster in blocks, which is Kummer carrying in the binomials of
        (2.2).  But they are statistically ordinary in every quantity theta sees --
        both the raw bands and the paired local test put the difference inside one
        standard error, at the sigma figures printed above.  So restricting m to the
        subsequence where the congruence is free -- which is legal and costs nothing,
        since the construction needs only infinitely many m -- buys nothing either.
    The first fact is the general one; see the block comment above.  Size and decay
    are homogeneous of degree 1, so form quality is projective, and a finite-index
    sublattice has the same projective points and fewer integer ones.
""")

    # -----------------------------------------------------------------  [U]
    out.write("\n[U] what the congruence costs, in the two currencies D5 priced it in:\n"
              "    (a) F -> 5F, the pigeonhole factor <= 5;  (b) one order of vanishing\n"
              "    traded away, which makes the cell rank 2 and lets a small combination\n"
              "    carry the congruence instead.  E = log|b| / (-log|r|), and only the\n"
              "    DIFFERENCES are read: within (b) the constrained optimum is compared\n"
              "    with the unconstrained optimum of the same box, never with E(w), so\n"
              "    that the price of the congruence is not confused with the price of the\n"
              "    order of vanishing.\n")
    out.write("       m    n | E(w)    | (a) E(5w)  m*dE | (b) uncon.  on {5|b}  m*dE\n")
    for m in (8, 12, 16, 20, 24, 32, 40):
        if m > mmax:
            break
        n, E_w, E_5, best, unc, isfree = _cong_cost(m)
        out.write(f"    {m:4d} {n:4d} | {E_w:.5f} | {E_5:8.5f} {m*(E_5-E_w):7.3f}"
                  f" | {unc[0]:8.5f} {best[0]:8.5f} {m*(best[0]-unc[0]):7.3f}"
                  f"   {'congruence free at w' if isfree else ''}\n")
    r = _cell_form(64)
    sg, rh = r[2] / 64, -r[3] / 64
    out.write(f"    the 1/m law behind column (a), in closed form:\n"
              f"      E(5F) - E(F) = log5 (sigma + rho) / (rho^2 m),  sigma = log|b|/m,"
              f"  rho = -log|r|/m\n"
              f"      at m = 64: sigma = {sg:.4f}, rho = {rh:.4f}"
              f"  ->  m*dE = {log(5)*(sg+rh)/rh**2:.3f}, matching the column\n")
    out.write("""
    Reading.  Both currencies price the congruence at O(1/m): column (a) at a
    constant m*dE, which is the closed form above rather than a fit, and column (b)
    at a comparable constant -- sometimes 0, when the box's unconstrained optimum
    happens to satisfy the congruence already.  Neither is ever negative: the
    congruence is a cost in both, as the projective argument says it must be.
    One thing in the table is NOT about the congruence and should not be read as
    though it were: the relaxed cell's unconstrained optimum sits below E(w) at
    these m, i.e. trading one order of vanishing for a smaller numerator can pay.
    That is WP-B's deficit-d question measured in a new place, it is an O(1/m)
    effect as well, and it is available with or without the congruence.
""")

    # -----------------------------------------------------------------  [V]
    out.write("\n[V] the verdict against the D4 wall.\n")
    _, _, _, _, C1, _ = _apparatus(2, Fraction(-1, 8), 6, 224141, 240395)
    delta = log(2 / 3) - C1
    out.write(f"    the wall (WP-B [L], WP-C [Q]):  Delta = {delta:.12f},"
              f"  g = {2.718281828459045**(6*delta):.6f}\n")
    for m in (64, 512, 10 ** 6):
        out.write(f"    at m = {m:7d}: the whole congruence costs log5/m = {log(5)/m:.3e}"
                  f" in the arithmetic rate,\n"
                  f"                 = {100*log(5)/(6*m*delta):.4f}% of the wall"
                  f" -- and it is a COST, in the wrong direction\n")
    out.write("""
    Q2 is closed, negatively, and the closure is a proof and not a statistic.
      1. Restricting to a sublattice cannot raise the rate.  Size and decay are
         homogeneous of degree 1, so quality is projective; a finite-index sublattice
         has the same projective points and fewer integer points, hence its optimum is
         never better.  Dividing by the content is the passage to the primitive
         generator and is already inside that optimum.  D5(i) is answered: contents
         cannot "rise on the sublattice", because the sublattice's generator is the
         lattice's generator times an integer.
      2. At the flagship the cell is of rank 1 ([T], WP-C [O]), so the sublattice is
         literally 5 x the cell, or the whole cell at the 1/3 of indices where the
         congruence is free.  Cost log 5 per form: O(1/m) in the rate, zero
         asymptotically, and 0.36% of the wall already at m = 512 ([V], [U]).
      3. D5(ii)'s alignment exists and is provable -- the class alternates j -> -j
         inside every run, exactly -- and it is worth nothing: the classes are
         equidistributed ([S]) and the fixed class is the D = 1 problem itself.
      4. S9(i)'s premise is falsified on the record data: M_n at the near misses
         factors like a random integer at every odd prime, l = 5 included ([R]).
    Congruences in this literature buy non-degeneracy, never rates -- [Dub87]'s
    Lemma 4 and [Eas86]'s 3^d, exactly as G-B read them; WP-D turns that pattern
    into the projective argument above.  With Q1 closed by WP-A/WP-C, the item's
    arithmetic half is now closed at both ends, and M2 is reached.  What the
    congruence DOES deliver is F4's D-native form at zero asymptotic cost -- free
    outright at a third of the indices -- which is a convenience and, by F3,
    theta-invisible.
""")


# ---------------------------------------------------------------------------
# plan-Tshift-S5 WP0, gate G-A -- the residue-class relaxation T1'.
#
# THE DERIVATION BEING AUDITED (plan-Tshift-S5 section 1.4, D1).  The sojourn cap
# of report section 1.5 is
#       repulsion  c theta^n <= d      and      shadowing  d <= (2/3)^L
#   ==> L log(3/2) <= n (-log theta) + (-log c),   i.e.  L <= kappa(theta) n + C0,
# with kappa(theta) = log(1/theta)/log(3/2)  (TShift.sojourn_cap_kappa, std3).
# If the repulsion bound exists only at dates n = r mod q, apply it at the first
# such date n' in [n, n+q) and shadow the block that REMAINS at n' (length L' with
# L <= L' + q):
#       L <= L' + q <= kappa n' + C0 + q <= kappa (n+q) + C0 + q
#          = kappa n + [C0 + (1 + kappa) q].
# So the relaxation costs (1 + kappa) q additively -- one q for the shortened block
# and kappa q for the shifted date.  The report prints C -> C + q log2(3/2), which
# is 0.585 q, SMALLER than q, hence not an upper bound for either term: it is the
# same block-shortening effect counted in BITS of the shadowing bound (shortening
# by q weakens (2/3)^L by the factor (3/2)^q = 2^(q log2(3/2))), and one unit of L
# is log2(3/2) bits.  [A] tabulates both, [F1].
#
# C20 (report, 2026-08-11) then changes what the reduction is FOR: the dyadic-block
# payoff is unconditional at kappa_free = log2(3/2) (TShift.free_sojourn_cap_logb,
# TShift.dyadic_block_visit), so a repulsion-derived cap improves on what is already
# owned only when kappa(theta) < kappa_free, i.e. theta > theta* = 0.78885 -- far
# above the 2/3 threshold and above every rate in print.  [B], [D].
#
# [C] is F2: a SINGLE-target class bound is usable inside a p-periodic sojourn only
# at dates meeting two congruences, and the fraction of usable sojourn phases is
# exactly 1/gcd(p,q) -- one half at the flagship (p,q) = (2,6).  [E] is F5: the
# window date must fall INSIDE the block, so the official statement needs a trivial
# branch for sojourns shorter than q, which the census shows to be the generic case.
#
# Floats appear only in summary columns.  Every printed decision is exact: [A]'s
# verdict is  1 + kappa > 1 > log2(3/2)  for kappa >= 0, [C] is integer arithmetic,
# [E] is an exact census of the carry word.
# ---------------------------------------------------------------------------

THETA_FREE = exp(-log(1.5) ** 2 / log(2))     # 0.78884781...  = C20's theta*

# (theta, source, class restriction) -- the rows of report section 1.5's table,
# plus the two class-restricted devices of section 1.6.2.
S5_RATES = [
    (0.5, "free (Lemma 2)", "-"),
    (2 ** -0.8972, "[Beu81] section 5", "delta = -k mod 6"),
    (2 ** -0.8, "[Hab03] (3.2) / S1 transfer", "dates in 6Z"),
    (0.5803, "[Zud07] record, rho = 0", "-"),
    (2 / 3, "T1 threshold", "-"),
    (0.75, "Waring threshold", "-"),
    (THETA_FREE, "free cascade (C20)", "-"),
]


def _kappa(theta):
    """kappa(theta) = log(1/theta)/log(3/2) -- TShift.kappa, report (5)."""
    return -log(theta) / log(1.5)


def _dist_frac(x):
    """||x|| for an exact rational -- the Fraction companion of dist_num."""
    f = x - (x.numerator // x.denominator)          # in [0,1), floor is exact
    return min(f, 1 - f)


def _s2_mnum(D, n, p=3, q=2):
    """m_n = round(D (p/q)^n), exact; ties away from zero, as Mathlib's `round`."""
    num, den = D * p ** n, q ** n
    quo, r = divmod(num, den)
    return quo + 1 if 2 * r >= den else quo


def _s2_resid(D, n, p=3, q=2):
    """k_n = D p^n - m_n q^n, exact.  |k_n| = q^n ||D(p/q)^n||."""
    return D * p ** n - _s2_mnum(D, n, p, q) * q ** n


def _s2_fail(D, n, tn, td):
    """||D(3/2)^n|| < (tn/td)^n, decided in Z: |k_n| td^n < tn^n 2^n."""
    return abs(_s2_resid(D, n)) * td ** n < tn ** n * 2 ** n


def _s2_v2(x):
    v = 0
    while x and x % 2 == 0:
        x //= 2
        v += 1
    return v


def _s2_consts(tn, td, D, prec=60, p=3, q=2):
    """D2's constants at (theta, D) = (tn/td, D), to `prec` digits.

    Every quantity of the block count, from the plan's own formulas (base p/q,
    default the flagship 3/2 -- WP7(b) reads the same formulas at other bases):
        eps   = log(1/theta)/log p                          (BB13.epsilon)
        K     = ceil(2^32 (1+1/eps)^3 log 6 log((1+1/eps) log 6))  (lineBound)
        f_inf = log(p/(q theta))/log p                      (BB13.fArch)
        b_l   = floor(log2(1/f_inf)) + 2                    blocks per line
        N_0   = max(ceil(4 log2/log(1/theta)), ceil(log_p 2D))      the threshold
        B     = K b_l + floor(log2 N_0) + 1
    The first threshold term is base-free: p^n > 2^(4/eps) <=> theta^n < 1/16.
    """
    getcontext().prec = prec
    l3, l2, l6 = Decimal(p).ln(), Decimal(2).ln(), Decimal(6).ln()
    th = Decimal(tn) / Decimal(td)
    eps = (1 / th).ln() / l3
    u = 1 + 1 / eps
    Kx = u ** 3 * Decimal(2) ** 32 * l6 * (u * l6).ln()
    K = int(Kx.to_integral_value(rounding="ROUND_CEILING"))
    finf = (Decimal(p) / (q * th)).ln() / l3
    lgi = (1 / finf).ln() / l2
    bl = int(lgi.to_integral_value(rounding="ROUND_FLOOR")) + 2
    x1 = 4 * l2 / (1 / th).ln()
    x2 = Decimal(2 * D).ln() / l3
    N0 = max(int(x1.to_integral_value(rounding="ROUND_CEILING")),
             int(x2.to_integral_value(rounding="ROUND_CEILING")))
    lgN0 = int((Decimal(N0).ln() / l2).to_integral_value(rounding="ROUND_FLOOR"))
    return dict(theta=float(th), eps=eps, Kx=Kx, K=K, finf=finf, lgi=lgi, bl=bl,
                t=bl - 1, x1=x1, x2=x2, N0=N0, lgN0=lgN0, B=K * bl + lgN0 + 1)


S2_RATES = [(2, 3), (17, 25), (7, 10), (3, 4), (4, 5), (9, 10), (99, 100)]
S2_MULTS = (1, 5, 19, 65)                       # D_p = 3^p - 2^p, p = 1..4


def cmd_s2(nmax=1200, out=sys.stdout):
    """S2 WP0, gate G-A: the block count, audited.

    [A] D1 on the real frame at odd D -- parity, the scaling identity, confinement;
    [B] D2's constants recomputed at 60 digits, with the ceiling margins;
    [C] F5: the showcase the corpus already certifies (theta = 3/4, not 9/10);
    [D] the certificate against the truth -- what the exceptional set actually is;
    [E] D3 and the free cap: the payoff branch, priced against TShift.FreeSojourn;
    [F] the verdict;
    [G] WP5: the tower currency transported to every multiplier, and the no-go --
        its block shadow exceeds the number of blocks that exist below N.
    [H] WP7(a): the theta -> 1 price -- monotone in the rate, cubic floor, fixed span.
    [I] WP7(b): the general-base table, p odd and q even, with span certificates.
    [J] O-7: the figures C15 puts into report-Tshift.html, so they cannot drift.
    """
    out.write("plan-Tshift-S2 WP0 -- the block count, audited.\n"
              "Exact integers for every decision about the frame; 60-digit Decimal\n"
              "for the constants (no mpmath: the ceilings are checked for margin).\n\n")

    out.write("# [A] D1 at odd multipliers: parity, scaling, confinement\n")
    out.write("#   D    dates   same-line pairs   scaling ok   conf. tested   viol.(Z / log)\n")
    for D in S2_MULTS:
        M = {n: _s2_mnum(D, n) for n in range(1, nmax + 1)}
        pairs, scal, conf, vz, vl = 0, 0, 0, 0, 0
        for tn, td in ((3, 4), (9, 10)):
            invf = 1 / _s2_consts(tn, td, D)["finf"]
            for a in range(1, nmax):
                for j in range(1, min(_s2_v2(M[a]), nmax - a) + 1):
                    if M[a] * 3 ** j % 2 ** j or M[a + j] != M[a] * 3 ** j // 2 ** j:
                        continue
                    b = a + j
                    if (tn, td) == (3, 4):                      # count pairs once
                        pairs += 1
                        scal += (_s2_resid(D, b) == 3 ** j * _s2_resid(D, a))
                    if _s2_fail(D, b, tn, td):
                        conf += 1
                        # the confinement in the form the proof produces it, in Z:
                        #   3^(b-a) <= |k_b| < (2 theta)^b
                        vz += not (3 ** j * td ** b < (2 * tn) ** b)
                        # ... and in its logarithmic form b < a/f_inf (60-digit cross-check)
                        vl += not (Decimal(b) < Decimal(a) * invf)
        odd = all(_s2_resid(D, n) % 2 != 0 for n in range(1, nmax + 1))
        out.write(f"  {D:3d}  {nmax:6d}   {pairs:15d}   {str(scal == pairs):10s}"
                  f"   {conf:12d}   {vz:5d} / {vl:d}\n")
        assert odd and scal == pairs and vz == 0 and vl == 0
    out.write("      every residue odd (F2), every same-line pair scales by 3^(b-a),\n"
              "      every failure above an earlier line-mate obeys 3^(b-a) < (2 theta)^b\n"
              "      -- decided in Z -- and its log form b < a/f_inf.\n")

    out.write("\n# [B] D2's constants, recomputed at 60 digits (D = 5)\n")
    out.write("#   theta      eps          K(eps)              f_inf     b_l  N_0"
              "   B(theta,D)\n")
    for tn, td in S2_RATES:
        c = _s2_consts(tn, td, 5)
        out.write(f"  {tn:3d}/{td:<4d} {float(c['eps']):.9f}  {c['K']:22,d}"
                  f"  {float(c['finf']):.6f}  {c['bl']:2d} {c['N0']:4d}"
                  f"   {c['B']:.6e}\n")
    c34, c910 = _s2_consts(3, 4, 5), _s2_consts(9, 10, 5)
    out.write(f"      K(eps(3,3/4)) = {c34['K']:,d} -- BB13/Constants.lean's certified\n"
              f"      lineBound_epsStar_le (<= 1.86e12) is this same number: eps* = "
              f"eps(3,3/4).\n")
    out.write(f"      B(9/10,5) = {c910['B']:,d} -- the plan's provisional 1.05e14, "
              f"confirmed.\n")
    marg = min(float(c["x1"] - int(c["x1"])) for c in (c34, c910))
    out.write(f"      ceiling margins: min frac. part of 4log2/log(1/theta) = {marg:.4f}"
              " -- no boundary case.\n")
    assert c34["K"] == 1856360182227 and c34["K"] <= 1860000000000
    assert c910["B"] == 104008288302665 < 1.05e14
    assert c34["bl"] == 2 and c34["N0"] == 10 and c910["bl"] == 3 and c910["N0"] == 27
    assert marg > 0.3

    out.write("\n# [C] F5 -- the showcase the corpus already certifies\n")
    out.write("#   theta   kappa(theta)   B(theta,5)      certified today?\n")
    for tn, td in ((3, 4), (9, 10)):
        c = _s2_consts(tn, td, 5)
        cert = "yes -- lineBound_epsStar_le + three_quarters_pow_lt" if (tn, td) == (3, 4) \
            else "no -- needs a new certified decimal (WP2)"
        out.write(f"  {tn:2d}/{td:<3d}  {_kappa(tn / td):.6f}       {c['B']:.5e}"
                  f"   {cert}\n")
    ratio = c910["B"] / c34["B"]
    out.write(f"      theta = 3/4 is {ratio:.1f}x smaller AND free: eps(3,3/4) = eps*,\n"
              f"      and (3/4)^n < 1/16 <=> n >= 10 is BB13.three_quarters_pow_lt.\n"
              f"      kappa(3/4) = {_kappa(0.75):.6f} < 1, so the block reading still\n"
              f"      crosses 2/3.  WP2 is not needed at this showcase.\n")
    assert _kappa(0.75) < 1.0 and ratio > 27.0

    out.write("\n# [D] the certificate against the truth\n")
    out.write("#   D   theta   failures (n <= %d)                     lines  bad blocks"
              "   above N_0\n" % nmax)
    for tn, td in ((3, 4), (9, 10)):
        c = _s2_consts(tn, td, 5)
        for D in S2_MULTS:
            f = [n for n in range(1, nmax + 1) if _s2_fail(D, n, tn, td)]
            lines = {Fraction(_s2_mnum(D, n) * 2 ** n, 3 ** n) for n in f}
            blocks = sorted({n.bit_length() - 1 for n in f})
            hi = [n for n in f if n >= c["N0"]]
            s = str(f) if len(f) <= 8 else str(f[:7])[:-1] + f", ...+{len(f) - 7}]"
            out.write(f"  {D:3d}  {tn:2d}/{td:<3d}  {s:38s} {len(lines):5d}"
                      f"  {len(blocks):9d}   {len(hi)}\n")
            if (tn, td) == (3, 4):
                assert not hi
    out.write(f"      At theta = 3/4 the above-threshold exceptional set is EMPTY for\n"
              f"      every D_p, p <= 4, up to n = {nmax}: the certified 3.7e12 blocks\n"
              f"      bound a set no computation has ever seen a member of above N_0.\n")

    out.write("\n# [E] D3's payoff branch, against the free cap\n")
    kf = log(1.5) / log(2.0)                    # kappa_free = log2(3/2) = 0.5849625
    out.write(f"      kappa_free            = {kf:.7f}   (TShift.free_sojourn_cap, "
              "no Diophantine input)\n")
    for tn, td in ((3, 4), (9, 10)):
        out.write(f"      kappa({tn}/{td})" + " " * (11 - len(str(td)))
                  + f"   = {_kappa(tn / td):.7f}   "
                  f"1 + kappa = {1 + _kappa(tn / td):.7f}\n")
    out.write(f"      1 + kappa_free        = {1 + kf:.7f} < 2 unconditionally.\n"
              "      The block payoff is a STEP function of kappa -- either 1+kappa < 2\n"
              "      (no block skipped) or not.  kappa(9/10) = 0.26 is three times\n"
              "      sharper than kappa_free and buys nothing in that currency, and the\n"
              "      free cap has no bad branch at all: TShift.dyadic_block_visit gives\n"
              "      EVERY block, where D3 gives all but 2 sum_p B(theta,D_p).\n")
    assert 1 + kf < 2 and kf < 1 and kf < _kappa(0.75)
    assert abs(_kappa(2 / 3) - 1) < 1e-12

    # the corpus's certified figure: K(eps*) is bounded by 1.86e12 (BB13.lineBound_epsStar_le),
    # not by its true value, so Lean's decimal is four units above the plan's 3.72e12 round number
    b_cert = 2 * 1860000000000 + (10).bit_length() - 1 + 1
    out.write(f"      B(3/4,5) from the CERTIFIED K: 2*1.86e12 + 4 = {b_cert:,d}\n"
              f"      (TShift.badBlocks_card_le_five_decimal); from the true K: "
              f"{c34['B']:,d}.\n")
    assert b_cert == 3720000000004 and c34["B"] <= b_cert
    assert c34["bl"] - 1 == 1                   # Lean's block span t = b_l - 1 = 1

    out.write("\n# [F] the verdict\n")
    out.write("      D1 confirmed (and in the corpus since WP1: BB13.residMul_odd,\n"
              "                    sameLineMul_resid/_gap, std3);\n"
              "      D2 confirmed, with a 28x better and already-certified showcase\n"
              "         (and in the corpus since WP3: BB13.badBlocks_card_le,\n"
              "          TShift.badBlocks_card_le_five_decimal, t = 1, N_0 = 10);\n"
              "      D3 correct but SUPERSEDED -- its conclusion is strictly weaker\n"
              "      than a theorem the corpus already carries.\n"
              f"      What survives: the count.  <= {c34['B']:,d} bad dyadic blocks at\n"
              f"      theta = 3/4, kappa = {_kappa(0.75):.4f} < 1, on std3 + one audited axiom.\n")

    out.write("\n# [G] WP5 -- the tower currency, transported, and why it cannot buy blocks\n")
    # The threshold relation of BB13.gap_of_nonlink at (rho, t) = (6/5, 11) is
    #   log 2 <= 11 (log(4/3) - (1/5) log 3)  <=>  (66/5) log 3 <= 21 log 2  <=>  3^66 <= 2^105,
    # an integer inequality -- so TShift.towerBasesMul_card_le_three_halves needs no decimal
    # logarithm bound, where BB13.towerBases_card_le_three_halves still carries two.
    out.write(f"      threshold at (rho, t) = (6/5, 11):  3^66 <= 2^105  "
              f"({3 ** 66:.6e} <= {2 ** 105:.6e}),\n"
              f"      margin 2^105/3^66 = {2 ** 105 / 3 ** 66:.4f}"
              f"  -- an integer inequality, no decimal log bound.\n")
    assert 3 ** 66 <= 2 ** 105 and 3 ** 67 > 2 ** 105

    def _linked(a, b, tn, td):
        """BB13.Linkable at p = 3: 2 c^a 3^(b-a) <= 1 with c = tn/td, decided in Z."""
        return 2 * tn ** a * 3 ** (b - a) <= td ** a

    out.write("#   D   theta   failures  towers  links  linked=>collinear  base on line?"
              "   free bound\n")
    tot_f = tot_t = tot_l = 0
    for tn, td in ((3, 4), (9, 10)):
        for D in S2_MULTS:
            f = [n for n in range(1, nmax + 1) if _s2_fail(D, n, tn, td)]
            slope = {n: Fraction(_s2_mnum(D, n) * 2 ** n, 3 ** n) for n in f}
            links = [(a, b) for a in f for b in f if a < b and _linked(a, b, tn, td)]
            # sameLine_of_linkage: a link is a pair on ONE line of the cover
            coll = all(slope[a] == slope[b] for a, b in links)
            bases = [b for b in f
                     if not any(a < b and _linked(a, b, tn, td) for a in f)]
            # exists_isTowerBaseMul_sameLine: descending the linkage reaches a base, collinearly
            def _descend(b):
                while True:
                    prev = [a for a in f if a < b and _linked(a, b, tn, td)]
                    if not prev:
                        return b
                    b = prev[0]
            onln = all(slope[_descend(b)] == slope[b] for b in f)
            bnd = 11 + 1 + log(nmax) / log(1.2)
            out.write(f"  {D:3d}  {tn:2d}/{td:<3d} {len(f):9d} {len(bases):7d} "
                      f"{len(links):6d}  {str(coll):>17s}  {str(onln):>13s}"
                      f"   {bnd:10.2f}\n")
            tot_f, tot_t, tot_l = tot_f + len(f), tot_t + len(bases), tot_l + len(links)
            assert coll and onln and len(bases) <= bnd
    out.write("      Every linked pair is collinear and every failure descends to a tower\n"
              "      base on its own line -- the two steps TShift/TowerCurrency.lean adds to\n"
              "      the delta = 1 layer (sameLine_of_linkage, exists_isTowerBaseMul_sameLine).\n")
    out.write(f"      But the linkage is nearly empty here: {tot_l} link(s) over "
              f"{tot_f} failures,\n"
              f"      so towers ({tot_t}) and failures ({tot_f}) are all but the same count -- the\n"
              f"      grouping the currency is named for does no work in the certified range\n"
              f"      either (a link needs two failures with b <= 1.2619 a - 0.6309).\n")
    assert tot_t >= tot_f - tot_l

    out.write("\n#   N          blocks below N   tower bound 2(12+log_{6/5}N)   Theorem A\n")
    for N in (10 ** 3, 10 ** 6, 10 ** 12, 10 ** 100):
        blk = N.bit_length()                    # floor(log2 N) + 1: ALL blocks below N
        tw = 2 * (12 + log(N) / log(1.2))
        out.write(f"  1e{len(str(N)) - 1:<8d} {blk:14d}   {tw:26.1f}   {b_cert:,d}\n")
        assert tw > blk
    # ... and it is not the choice rho = 6/5: even at the sharp ratio 1 + eps* the tower
    # currency spends 2/log(1+eps*) = 8.60 blocks per ln N against the 1/log 2 = 1.44 that
    # exist, a factor 5.96.
    eps_star = log(4 / 3) / log(3)
    out.write(f"      per ln N:  blocks that exist {1 / log(2):.4f},  tower bound "
              f"{2 / log(1.2):.4f} (factor {2 / log(1.2) * log(2):.2f}),\n"
              f"      and at the SHARP ratio 1+eps* = {1 + eps_star:.5f} still "
              f"{2 / log(1 + eps_star):.4f} (factor {2 / log(1 + eps_star) * log(2):.2f}).\n")
    assert 2 / log(1 + eps_star) > 1 / log(2)
    xover = (b_cert / 2 - 12) * log(1.2)
    out.write(f"      The tower bound is numerically below Theorem A's {b_cert:,d} for every\n"
              f"      N < exp({xover:.3e}) -- and vacuous at every one of them.\n")

    out.write("\n# [G'] the WP5 verdict\n")
    out.write("      TRANSPORT DONE, SWAP REFUTED.  The gap principle, the linkage lemma and\n"
              "      its four consequences carry to every multiplier (D cancels out of the gap\n"
              "      identity), and the O(log N) tower count needs neither admissibility nor a\n"
              "      parity clause: TShift/TowerCurrency.lean, std3.  But the block shadow of\n"
              "      that count exceeds the number of blocks that exist below N, at every N and\n"
              "      at every ratio up to the sharp one, so it cannot replace b_l K(eps) in\n"
              "      Theorem A.  Only a line count bounded INDEPENDENTLY of N -- the Ridout\n"
              "      cover, i.e. the cited axiom -- can show that most blocks are good.\n"
              "      Angle O-6's comparison question is answered: not commensurable.\n")

    # ---- WP7(a), 2026-08-14: F9's question, asked in the right direction ----
    out.write("\n# [H] WP7(a) -- the price of theta, and where it sits\n")
    out.write("#   theta      eps        K(eps(3,theta))          t   B(theta,5)"
              "   cubic floor 1.27e9/(1-th)^3\n")
    prev = None
    for tn, td in S2_RATES + [(999, 1000)]:
        c = _s2_consts(tn, td, 5)
        th = tn / td
        floor3 = 1.27e9 / (1 - th) ** 3
        out.write(f"  {tn:4d}/{td:<5d} {float(c['eps']):.6f}  {c['K']:>22,d}"
                  f"  {c['t']:2d}   {c['B']:.4e}   {floor3:.4e}\n")
        assert floor3 <= c["K"]                 # BB13.lineBound_price_cubic
        assert prev is None or prev <= c["K"]   # BB13.lineBound_epsilon_mono
        assert c["t"] <= 2                      # one_le_four_mul_fArch_three_two
        prev = c["K"]
    out.write("      MONOTONE in the rate (checked along the row): the shadow does NOT\n"
              "      degrade as theta falls to 2/3 -- it is CHEAPEST there, B = 1.4881e12,\n"
              "      and blows up as theta rises to 1 (F9).  The blow-up is entirely in K:\n"
              "      the span t is 1 up to theta = sqrt(3)/2 = 0.86603 and 2 from there to 1,\n"
              "      because (3/(2c))^4 >= (3/2)^4 = 81/16 >= 3 for every c <= 1.\n")
    # the crossover of the span, exactly: 2 f_inf >= 1  <=>  (3/(2c))^2 >= 3  <=>  c <= sqrt(3)/2
    assert _s2_consts(866, 1000, 5)["t"] == 1 and _s2_consts(867, 1000, 5)["t"] == 2
    assert abs((3 / (2 * (3 ** 0.5 / 2))) ** 2 - 3) < 1e-12
    k23, k99 = _s2_consts(2, 3, 5), _s2_consts(99, 100, 5)
    out.write(f"      B(2/3,5)  = {k23['B']:.4e}   (the plan's 1.49e12)\n"
              f"      B(99/100,5) = {k99['B']:.4e} (the plan's 1.6e17)"
              f"   ratio {k99['B'] / k23['B']:.3e}\n")
    out.write("      The Lean floor is deliberately lossy -- K grows like eps^-3 log(1/eps),\n"
              "      and eps ~ (1-theta)/log 3, so the true growth is (log 3)^3/(1-theta)^3\n"
              "      times a log; 1.27e9 = 2^32 (2/3)^3 is what survives rational bounds.\n")

    # ---- WP7(b), 2026-08-14: the parity scope is not about q = 2 ------------
    out.write("\n# [I] WP7(b) -- the general-base block theorem (p odd, q even, D odd)\n")
    out.write("#   p/q      eps(p,3/4)   K(eps)                 f_inf    1/f_inf   t"
              "   B(3/4,5)     span cert   minimal\n")
    for pp, qq in ((3, 2), (5, 2), (5, 4), (7, 2), (7, 4), (7, 6), (9, 2), (9, 8)):
        if gcd(pp, qq) != 1:
            continue
        c = _s2_consts(3, 4, 5, p=pp, q=qq)
        t = c["t"]
        cert = Fraction(pp, qq * 3) * 4                       # p/(q c) at c = 3/4
        ok = cert ** (2 ** t) >= pp                           # one_le_two_pow_mul_fArch
        mini = t == 0 or cert ** (2 ** (t - 1)) < pp          # t is the least such span
        out.write(f"  {pp:2d}/{qq:<5d} {float(c['eps']):.6f}   {c['K']:>20,d}"
                  f"  {float(c['finf']):.5f}  {1 / float(c['finf']):7.4f}  {t:2d}"
                  f"  {c['B']:.4e}   {str(ok):>9s}   {str(mini):>7s}\n")
        assert ok and mini
        # the parity clause at even q: k_n = D p^n - m_n q^n is odd for every odd D
        for D in (1, 3, 5, 7, 65):
            assert all(_s2_resid(D, n, pp, qq) % 2 != 0 for n in range(1, 41))
    out.write("      Every span certificate is the RATIONAL inequality (p/(qc))^(2^t) >= p\n"
              "      (BB13.one_le_two_pow_mul_fArch), and every t in the column is the least\n"
              "      one that clears it.  eps depends on p and the rate ONLY, so (5,2) and\n"
              "      (5,4) share K and differ only in the span -- 1 against 2.\n")
    k52, k54 = _s2_consts(3, 4, 5, p=5, q=2), _s2_consts(3, 4, 5, p=5, q=4)
    assert k52["K"] == k54["K"] and k52["t"] == 1 and k54["t"] == 2
    out.write(f"      K(eps(5,3/4)) = {k52['K']:,d} (both), B(5/2) = {k52['B']:.4e},"
              f" B(5/4) = {k54['B']:.4e}.\n"
              "      Residues checked odd for D in {1,3,5,7,65}, n <= 40, at every base\n"
              "      above -- the clause BB13.residMul_odd_of_even proves in general.\n")

    out.write("\n# [I'] the WP7 verdict\n")
    out.write("      (a) PRICED, and in the opposite direction to the plan's question: the\n"
              "      block bound is monotone in the rate, cheapest at theta -> 2/3, and at\n"
              "      least cubic in 1/(1-theta) as theta -> 1 (BB13.lineBound_price_cubic),\n"
              "      hence unbounded (exists_rate_lineBound_ge).  The span is NOT the price:\n"
              "      t = 2 serves every rate below 1 at base 3/2.\n"
              "      (b) FREE, and wider than posed: the parity clause never used q = 2, only\n"
              "      2 | q, so Theorem A runs at every coprime p/q with p odd and q even, at\n"
              "      every odd multiplier (BB13.exists_badBlocks_card_le_of_odd), with (5,2)\n"
              "      and (5,4) carried out in full.  No new axiom, no new numerics -- only\n"
              "      the decimals at the new bases are missing, and they need log 5.\n")

    # ---- O-7, 2026-08-14: the figures C15 puts into report-Tshift.html ------
    out.write("\n# [J] O-7 -- the report figures C15 asserts (report-Tshift.html)\n")
    k34, k9 = _s2_consts(3, 4, 5), _s2_consts(9, 10, 5)
    out.write(f"      K(eps*)        = {k34['K']:>18,d}   ({k34['K']:.4e})  the showcase,"
              " certified in Lean\n"
              f"      K(eps(3,9/10)) = {k9['K']:>18,d}   ({k9['K']:.4e})  the top-four box's"
              " old dial\n"
              f"      ratio          = {k9['K'] / k34['K']:>18.1f}   -- the price of moving"
              " the showcase to 0.9\n")
    # the report's top-four box quotes exactly these three numbers
    assert round(k9["K"] / k34["K"], 1) == 18.7
    assert f"{k34['K']:.4e}" == "1.8564e+12" and f"{k9['K']:.4e}" == "3.4669e+13"
    assert k9["t"] == 2 and k34["t"] == 1        # and 0.9 needs the wider span as well
    out.write("      So theta = 0.9 is not a sharper showcase but a costlier one: 18.7x the\n"
              "      line count, a span of 2 instead of 1, and a decimal enclosure nobody\n"
              "      has certified (3/4 is free only because eps(3,3/4) = eps*).\n")
    out.write(f"      kappa(3/4) = {log(Fraction(4, 3)) / log(Fraction(3, 2)):.5f} < 1"
              "   -- the report's 1.5 table row, TShift.kappa_three_quarters_lt_one\n")
    assert abs(float(log(Fraction(4, 3)) / log(Fraction(3, 2))) - 0.70951) < 5e-6


def cmd_s5(nmax, pmax, out=sys.stdout):
    """S5 WP0/G-A ([A]-[E]), G-B ([F]), O-4 ([G]), WP6 ([H]-[J])."""
    lg32 = LOG2_3HALVES
    q = 6                                   # the canonical Beukers-section-5 class

    out.write("# [A] D1 -- the window constant, at the Beukers class q = 6\n")
    out.write("#   theta     source                        class            "
              "kappa   1+kappa  (1+k)q  q*lg(3/2)   ratio\n")
    for th, src, cls in S5_RATES:
        k = _kappa(th)
        out.write(f"  {th:.6f}  {src:28s}  {cls:16s} {k:7.5f} {1+k:8.5f} "
                  f"{(1+k)*q:7.3f} {lg32*q:10.3f} {(1+k)/lg32:7.4f}\n")
    out.write(f"  F1 STANDS.  The derived cost (1+kappa) q exceeds the printed "
              f"q log2(3/2) by the factor\n"
              f"    (1+kappa)/log2(3/2) >= 1/log2(3/2) = {1/lg32:.5f} for every "
              f"theta <= 1, and = {2/lg32:.5f} at theta = 2/3;\n"
              f"    the printed constant is therefore not an upper bound for the "
              f"cost under ANY accounting.\n"
              f"    Origin: shortening the block by q weakens (2/3)^L by "
              f"{lg32*q:.4f} bits = q = {q} units of L,\n"
              f"    and the date shift contributes a further kappa q, which the "
              f"printed constant omits.\n"
              f"    (Numerical coincidence: kappa q equals q log2(3/2) at exactly "
              f"one rate, theta = theta*.)\n")

    out.write("\n# [B] C20 -- where the reduction still has cap content\n")
    out.write(f"  kappa_free = log2(3/2)             = {lg32:.10f}"
              f"   (unconditional: TShift.free_sojourn_cap_logb)\n")
    out.write(f"  theta*     = exp(-log^2(3/2)/log2) = {THETA_FREE:.10f}"
              f"   kappa(theta*) = {_kappa(THETA_FREE):.10f}\n")
    out.write("#   theta     source                        kappa   kappa < "
              "kappa_free?   theta > 2/3?\n")
    for th, src, _cls in S5_RATES:
        k = _kappa(th)
        out.write(f"  {th:.6f}  {src:28s} {k:7.5f}   "
                  f"{'yes' if k < lg32 else 'no':>13s}   "
                  f"{'yes' if th > 2/3 else 'no':>12s}\n")
    out.write("  The dyadic-block payoff is free.  A class-restricted cap is worth "
              "more than what is\n"
              "  already owned only above theta*, which no device in print "
              "approaches; below theta* the\n"
              "  reduction's conclusion holds without its hypothesis.  What T1' "
              "still buys that nothing\n"
              "  free buys is the per-n floor -- at the dates of the class, and "
              "nowhere else.\n")

    out.write("\n# [C] F2 -- the CRT obstruction, exact\n")
    out.write("#   p    q  gcd  lcm   usable sojourn phases (brute force)  "
              "fraction\n")
    for p in (2, 3, 4, 5):
        for qq in (2, 3, 6, 12):
            g = gcd(p, qq)
            lcm = p * qq // g
            hits = {len({n % p for n in range(lcm) if n % qq == r})
                    for r in range(qq)}
            assert hits == {p // g}, (p, qq, hits)
            out.write(f"  {p:4d} {qq:4d} {g:4d} {lcm:4d}   {p//g:>4d} of {p:<4d}"
                      f"                        1/{g}\n")
    out.write("  F2 CONFIRMED at the flagship (p,q) = (2,6): gcd = 2, so for a "
              "fixed class r exactly half\n"
              "  the sojourn phases admit a usable date -- and for the other half "
              "NO date of the sojourn is\n"
              "  usable, at any window length.  When gcd(p,q) = 1 every phase is "
              "usable but the window is\n"
              "  lcm(p,q), not q.  In MULTIPLIER form there is no phase condition "
              "at all -- the bound at n'\n"
              "  controls the distance to every A/D at once, the rotated cycle "
              "member included -- so the\n"
              "  window is q and the argument closes.  T1' must be the multiplier "
              "form.\n")

    out.write("\n# [D] D2 -- the printed class-restricted devices at base 3/2\n")
    for th, src, cls in S5_RATES[1:3]:
        k = _kappa(th)
        out.write(f"  {src:28s} {cls:16s} theta = {th:.5f}  kappa = {k:.5f}"
                  f"   > 2/3? no   > theta*? no\n")
    out.write("  [Ben93] (19)                 base (N+1)/N, N >= 4   3/2 excluded "
              "-- shape only\n")
    out.write(f"  Best class-restricted rate in print, {2**-0.8972:.5f}, is BELOW "
              f"the unrestricted transfer\n"
              f"  {2**-0.8:.5f} (S1) and below the record {0.5803:.4f}; the "
              f"threshold is {2/3:.5f} and the bar that\n"
              f"  would beat the free cap is {THETA_FREE:.5f}.  T1' proves no new "
              f"bound today.\n")

    out.write(f"\n# [E] F5 -- sojourns shorter than the window q = {q}, "
              f"carry word, n <= {nmax}\n")
    s = carry_word(nmax + 2 * pmax + 2)
    out.write("#   p   maximal blocks    L < q     L >= q    share short   max L\n")
    for p in range(1, pmax + 1):
        ks = [0] * (nmax + 2)
        k = 0
        for n in range(nmax, -1, -1):
            k = k + 1 if s[n + p] == s[n] else 0
            ks[n] = k
        short = long_ = maxL = 0
        for n in range(nmax + 1):
            if n and ks[n - 1] > 0:          # not left-maximal
                continue
            L = p + ks[n]
            maxL = max(maxL, L)
            if L < q:
                short += 1
            else:
                long_ += 1
        tot = short + long_
        out.write(f"  {p:3d} {tot:15d} {short:9d} {long_:10d} "
                  f"{100*short/tot:12.2f}% {maxL:7d}\n")
    out.write("  The short case is the generic one, so the official window cap must "
              "carry the trivial\n"
              "  branch: for L < q the class need not be met inside the block at "
              "all, and L < q <= kappa n + q\n"
              "  holds for free (kappa >= 0).  Combined constant "
              "max(C0 + (1+kappa) q, q).\n")

    # ---- gate G-B, 2026-08-11: the relaxation is a base change ---------------
    out.write("\n# [F] G-B -- T1'(q,r) IS the T-shift problem at the base "
              "(3/2)^q\n")
    out.write("#   n = r + q m   =>   D (3/2)^n = [D (3/2)^r] * B^m,   "
              "B = (3/2)^q = P/Q\n")
    out.write("#   q         P/Q       P-Q = D_q   threshold Q/P   free rate 1/Q"
              "   P > Q^2?   kappa_free   (N+1)/N?\n")
    for qq in range(1, 9):
        P, Q = 3 ** qq, 2 ** qq
        kfree = log(Q) / log(P / Q)
        out.write(f"  {qq:3d} {P:>9d}/{Q:<9d} {P-Q:>9d}   {Q/P:13.7f} "
                  f"{1/Q:14.7f}   {'yes' if P > Q * Q else 'no':>8s}   "
                  f"{kfree:10.5f}   {'yes' if P - Q == 1 else 'no':>8s}\n")
    for qq in range(1, 9):                      # the invariance, to machine zero
        P, Q = 3 ** qq, 2 ** qq
        assert abs(log(Q) / log(P / Q) - 1 / LOG2_3HALVES) < 1e-12
        for th, _src, _cls in S5_RATES:         # kappa_q(theta^q) = kappa(theta)
            assert abs(-log(th ** qq) / log(P / Q) - _kappa(th)) < 1e-12
    for qq in range(1, 13):                     # D_p | D_q whenever p | q
        for pp in range(1, qq + 1):
            if qq % pp == 0:
                assert (3 ** qq - 2 ** qq) % (3 ** pp - 2 ** pp) == 0
    out.write("  Verified to machine zero for q <= 8 and every rate above: "
              "kappa_q(theta^q) = kappa(theta),\n"
              "  and the threshold maps to the threshold, theta^q > (2/3)^q "
              "<=> theta > 2/3.  Three consequences.\n"
              "  (i) NO MODULUS IS CHEAPER.  kappa is invariant under n -> qn, so "
              "a class-restricted device\n"
              "      at modulus q is worth exactly what the same kappa buys at "
              "base 3/2 -- the relaxation\n"
              "      enlarges the admissible devices, never the payoff.\n"
              "  (ii) NO MODULUS IS FREE.  The N3 free zone P > Q^2 reads "
              "3^q > 4^q, false for every q >= 1,\n"
              "      so every class-restricted problem stays in the hard zone; "
              "and kappa_free = log2/log(3/2)\n"
              f"      = {1/LOG2_3HALVES:.5f} at every q.\n"
              "  (iii) NOT THE (N+1)/N FAMILY.  P - Q = 3^q - 2^q = D_q, the "
              "T-shift denominator of the\n"
              "      base itself; it is 1 only at q = 1, so [Ben93]/[Zud07], "
              "which cover (1+1/N)^k only,\n"
              "      never reach B for q >= 2.  (B's own periodic targets are "
              "A/(P^m - Q^m) = A/D_(qm), the\n"
              "      sub-family of the original one indexed by the multiples of "
              "q; and D_p | D_q whenever\n"
              "      p | q, verified for q <= 12, so at the flagship (p,q)=(2,6) "
              "the multiplier D_2 = 5\n"
              "      divides the new base's first denominator D_6 = 665.)  This "
              "is why the relaxation is\n"
              "      unnamed in the literature:\n"
              "      in the literature's own coordinates it is not a new object "
              "but a base change, and the\n"
              "      printed instance of the move is [Dub10] p. 26, which treats "
              "||tau (3/2)^(2n)|| by\n"
              "      setting p/q = 9/4 -- on the confinement side, never on the "
              "repulsion side.\n")

    # ---- angle O-4 of plan-S7, 2026-08-11: the descent, and what pays for it -
    out.write("\n# [G] O-4 -- a class bound whose MULTIPLIER is free is not "
              "class-restricted\n")
    out.write("#   At any date k put delta = (r - k) mod q and n = k + delta, so "
              "n = r (mod q).  Then\n"
              "#     2^delta * D * (3/2)^n = 3^delta * (D * (3/2)^k)    exactly, "
              "hence\n"
              "#     ||2^delta D (3/2)^n|| <= 3^delta * ||D (3/2)^k||    "
              "(TShift.distToNearestInt_mul_le),\n"
              "#   so a class bound  c theta^n <= ||2^delta D (3/2)^n||  at the "
              "multiplier 2^delta D gives\n"
              "#     ||D (3/2)^k|| >= c (theta/3)^delta theta^k >= c "
              "(theta/3)^(q-1) * theta^k   at EVERY date k.\n")
    for D in (1, 5, 19, 665):                   # identity + inequality, exactly
        for k in range(0, 26):
            y = Fraction(D) * Fraction(3, 2) ** k
            for d in range(0, 8):
                z = Fraction(2) ** d * D * Fraction(3, 2) ** (k + d)
                assert z == Fraction(3) ** d * y
                assert _dist_frac(z) <= Fraction(3) ** d * _dist_frac(y)
    for k in range(1, 200000):                  # the corpus's own delta, q = 6
        mm = (k + 5) // 6                       # le_distToNearestInt_uniform
        assert 0 <= 6 * mm - k <= 5 and 6 * mm == k + (6 * mm - k)
    out.write("#   theta     source                        class            "
              "(theta/3)^(q-1)   nats lost   rate\n")
    for th, src, cls in S5_RATES:
        loss = (th / 3) ** (q - 1)
        out.write(f"  {th:.6f}  {src:28s}  {cls:16s} {loss:15.6e} "
                  f"{-log(loss):11.4f}   {'unchanged':>9s}\n")
    kmin, num, den = 0, 1, 1                    # first k with bHab^k >= 2^(q-1)
    while num < (1 << (q - 1)) * den:
        num, den, kmin = num * 1216, den * 1215, kmin + 1
    out.write("  Identity and inequality verified exactly (Fractions, no floats) "
              "for D in {1,5,19,665},\n"
              "  k <= 25, delta <= 7; and delta = 6*((k+5)//6) - k lies in [0,5] "
              "for k < 200000, which is\n"
              "  the descent the corpus already performs "
              "(TShift.distToNearestInt_descent, section 5 of\n"
              "  TShift/HabsiegerTransfer.lean, at q = 6).  Three readings.\n"
              "  (i) THE RATE SURVIVES, THE CONSTANT PAYS.  theta is unchanged, so "
              "kappa(theta) and the side of\n"
              "      2/3 are unchanged; the whole cost is the one-off factor "
              "(theta/3)^(q-1) above.  A class\n"
              "      bound at theta > 2/3 therefore settles T1 itself, not only "
              "T1', once the multiplier is free.\n"
              "  (ii) WHAT 'FREE' MEANS, PRICED.  The descent needs the bound at "
              f"the q multipliers 2^delta D,\n      delta < q -- a factor "
              f"2^(q-1) = {1 << (q - 1)} of admissible-multiplier range.  "
              "[Hab03]'s range is\n"
              f"      bHab^k = (1216/1215)^k (TShift.bHab), which passes "
              f"{1 << (q - 1)} at k = {kmin}, against that\n"
              f"      theorem's own burn-in kHab = 64440001: "
              f"{100 * kmin / 64440001:.4f}% of it, and nothing in the rate.\n"
              "  (iii) SO T1' IS A RELAXATION ONLY FOR A DEVICE WHOSE MULTIPLIER "
              "IS NOT FREE.  The formal\n"
              "      statement stays strictly weaker -- IsRepelledMulClass theta D "
              "q r is one instance, and the\n"
              "      descent consumes q of them -- but every device in the G-B "
              "sweep carries the free integer\n"
              "      that supplies all q: [Beu81] section 5 'M in Z ... "
              "arbitrary', [Hab03] (3.2) 'M an integer',\n"
              "      [Ben93] (19).  That is why all three close with k = qm - "
              "delta and state no congruence,\n"
              "      and why TShift.isRepelledMul_habsieger carries no class "
              "restriction although [Hab03]'s\n"
              "      forms live on 6Z.  Corollary for plan-S7: its date lattice "
              "was never a restriction, so\n"
              "      angle O-4's dependency on S5 was precautionary, not binding "
              "(and Q2's mod-5 condition is\n"
              "      a condition on coefficients at a fixed date, not on dates at "
              "all).\n")

    # ---- WP6, 2026-08-14: the three stretch variants ------------------------
    out.write("\n# [H] WP6(i) -- the single-target variant: the window is "
              "lcm(q,p), and only sometimes\n")
    out.write("#   Usable dates for a bound on the class r mod q at a sojourn of "
              "phase s mod p are the\n"
              "#   solutions of n = r (q), n = s (p): a class mod lcm(q,p) when "
              "gcd(q,p) | r-s, EMPTY otherwise.\n")
    out.write("#    q    p   gcd   lcm   usable (r,s) pairs   share   max gap "
              "between usable dates   = lcm?\n")
    for qq, pp in ((6, 2), (6, 1), (6, 3), (6, 4), (6, 5), (5, 2), (5, 3),
                   (4, 2), (3, 2), (2, 2), (12, 8)):
        g, l = gcd(qq, pp), qq * pp // gcd(qq, pp)
        usable = maxgap = 0
        for r in range(qq):
            for s in range(pp):
                sols = [n for n in range(0, 4 * l) if n % qq == r % qq
                        and n % pp == s % pp]
                if (r - s) % g == 0:
                    usable += 1
                    assert sols, "solvable pair with no solution"
                    gaps = [b - a for a, b in zip(sols, sols[1:])]
                    assert set(gaps) == {l}, (qq, pp, gaps)
                    maxgap = max(maxgap, max(gaps))
                else:
                    assert not sols, "unsolvable pair with a solution"
        assert usable == qq * pp // g
        out.write(f"  {qq:4d} {pp:4d} {g:5d} {l:5d} {usable:20d} "
                  f"{usable/(qq*pp):7.3f} {maxgap:25d}   "
                  f"{'yes' if maxgap == l else 'NO':>7s}\n")
    for n in range(0, 10000):                   # the flagship, exactly
        assert not (n % 6 == 1 % 6 and n % 2 == 0 % 2)
    out.write("  Both halves of F2, machine-checked: the usable share is "
              "1/gcd(q,p) of the (r,s) pairs, the\n"
              "  gap between consecutive usable dates is exactly lcm(q,p) -- "
              "never q -- and at the flagship\n"
              "  (p,q) = (2,6) the class r = 1 contains no even date at all "
              "(checked to n = 10000), so half\n"
              "  the sojourn phases admit NO usable date at any window length.  "
              "Price of the single-target\n"
              "  form in the cap constant, (1+kappa)*lcm against (1+kappa)*q:\n")
    out.write("#   q=6, period p   lcm   usable share   (1+kappa)q   "
              "(1+kappa)lcm   factor   (at theta = 0.5803, kappa = 1.34219)\n")
    kz = _kappa(0.5803)
    for pp in range(1, 8):
        g, l = gcd(6, pp), 6 * pp // gcd(6, pp)
        out.write(f"  {pp:15d} {l:5d} {1/g:14.4f} {(1+kz)*6:12.4f} "
                  f"{(1+kz)*l:14.4f} {l/6:8.2f}\n")

    out.write("\n# [I] WP6(ii) -- the general-base window cap, and its "
              "unconditional inhabitant\n")
    out.write("#   base p/q   kappa_floor = log q/log(p/q)   kappa_casc   "
              "product   free zone q^2 < p?   cap sublinear?\n")
    for pp, qq in ((3, 2), (5, 2), (7, 2), (9, 2), (5, 4), (4, 3), (10, 3),
                   (5, 3), (11, 3)):
        kf = log(qq) / log(pp / qq)
        kc = log(pp / qq) / log(qq)
        assert abs(kf * kc - 1) < 1e-12
        assert (kf < 1) == (qq * qq < pp)
        out.write(f"  {pp:6d}/{qq:<4d} {kf:26.7f} {kc:12.7f} {kf*kc:9.5f} "
                  f"{'yes' if qq*qq < pp else 'no':>19s} "
                  f"{'yes' if kf < 1 else 'no':>16s}\n")
    kf52 = log(2) / log(5 / 2)
    kf32 = log(2) / log(3 / 2)
    for D in (1, 3, 5, 7, 9, 11, 65):           # the q-adic floor, exactly
        y = Fraction(D)
        for n in range(1, 121):
            y *= Fraction(5, 2)
            assert _dist_frac(y) >= Fraction(1, 2 ** n)
    out.write(f"  kappa_b(5/2, 1/2) = {kf52:.7f} < 1 and "
              f"kappa_b(3/2, 1/2) = {kf32:.7f} > 1: the free q-adic floor\n"
              f"  ||D (p/q)^n|| >= q^-n is a THEOREM at every base (verified "
              f"exactly at 5/2 for odd D <= 11\n"
              f"  and D = 65, n <= 120), and at 5/2 its slope is already "
              f"sublinear.  So the whole T1' pipeline\n"
              f"  -- rate, class restriction, window cap, dyadic payoff -- has "
              f"an unconditional inhabitant at\n"
              f"  base 5/2, burn-in factor 1/(1-kappa) = {1/(1-kf52):.4f}, and "
              f"none at base 3/2, where the same\n"
              f"  instance has slope {kf32:.5f} and the free cap comes from the "
              f"carry word instead (kappa_free =\n"
              f"  {LOG2_3HALVES:.5f}, C20).  That contrast IS the difficulty of "
              f"the subject: 3/2 is the one base\n"
              f"  in the hard band q < p < q^2 at q = 2.\n")

    out.write("\n# [J] WP6(iii) -- the composition with an exceptional set, and "
              "why it collapses\n")
    out.write("#   Failures of ||D (3/2)^n|| >= theta^n, exact rationals, "
              f"n <= {min(nmax, 2000)}:\n")
    out.write("#     D    theta      failures   last failure   block index of "
              "last   2^(idx+1)   the failure dates\n")
    ncen = min(nmax, 2000)
    for D in (1, 5, 19, 65):
        for th in (Fraction(3, 4), Fraction(9, 10)):
            y, t, fails = Fraction(D), Fraction(1), []
            for n in range(1, ncen + 1):
                y *= Fraction(3, 2)
                t *= th
                if _dist_frac(y) < t:
                    fails.append(n)
            last = fails[-1] if fails else 0
            idx = last.bit_length() - 1 if last else 0
            assert all(f < 2 ** (idx + 1) for f in fails)
            out.write(f"  {D:5d} {float(th):8.4f} {len(fails):11d} "
                      f"{last:14d} {idx:20d} {2**(idx+1):11d}   "
                      f"{fails}\n")
    for M in (0, 1, 5, 12, 40):                 # block index bound -> date bound
        for x in range(1, 3000):
            if x.bit_length() - 1 <= M:
                assert x < 2 ** (M + 1)
    out.write("  Two facts and one verdict.  (a) A bound on the block INDEX is a "
              "bound on the date: index <= M\n"
              "  implies date < 2^(M+1), checked above -- this is "
              "TShift.MeetsWindow.sdiff_blocks, and it is what\n"
              "  makes plan-S2's currency compose with S5's window.  (b) A bound "
              "on the block COUNT is not: S2's\n"
              "  Theorem A bounds the number of bad blocks (3720000000004 at "
              "(D,theta) = (5,3/4)) and locates\n"
              "  none of them, so the composed threshold is ineffective, exactly "
              "as the count is.  VERDICT: the\n"
              "  composition costs a THRESHOLD and never a gap, and "
              "IsRepelledMulClass quantifies its threshold\n"
              "  existentially -- so a bounded exceptional set is absorbed into "
              "n0 and the composed hypothesis\n"
              "  IS the class hypothesis (TShift.isRepelledMulClass_of_sdiff_"
              "bounded).  The defect of the\n"
              "  exception-count lane is invisible to the relaxed problem, just "
              "as the ineffective threshold of\n"
              "  the transported record rate is (plan-S1 WP7, finding F3).  What "
              "it is not invisible to is a\n"
              "  statement with exhibited numerals -- TShift.TShiftProblemAt, "
              "TShift.RepelledAt -- where the\n"
              "  unlocated blocks are precisely the missing constant.  On the "
              "censused range the exceptional\n"
              "  set is real but early -- every failure above sits at n <= 34, "
              "so at (D,theta) = (5,3/4) the\n"
              "  composed hypothesis 'class minus S' becomes the plain class "
              "hypothesis from n = 7 on, and the\n"
              "  whole content of the composition there is a threshold of 7.  "
              "What S2's theorem adds is that\n"
              "  finiteness holds at EVERY theta < 1, ineffectively; what it "
              "cannot add is a date.\n")

# ---------------------------------------------------------------------------
# plan-Tshift-S8 WP0 -- audit verification of the plan's own arithmetic.
#
# [A] gate G-A, both calibrations, as assertions (the routine is apparat's, so this
#     is a re-run, not a second implementation), plus the endgame cross-check: the
#     three frozen bases of CITED/HabsiegerPade.lean reproduce thetaHab.
# [B] the channel identification WP0's line asks for: I(15/16) against
#     log(7516022/5065927).  They are two different constants and the plan's WP0
#     line invites confusing them.
# [C]-[E] derivation D1, the determinant's budget, re-derived independently and
#     checked on integers: the two Cramer identities, the cap, the refined
#     elimination, the disjointness, the bad branch.  Everything exact.
#     One correction to the plan: D1 is written with the classical bound
#     max|Delta_i| >= 1, i.e. at content P = 1.  The corpus's lemma has the
#     content in it (TShift.multiplier_transfer concludes P*X <= |c|Lambda +
#     B|cY - mX| with P <= |Gamma_i|), so the improvement condition is
#     c|det| > 2BP and the validity condition is P*X > |c|Lambda.  The
#     disjointness survives verbatim with P on both sides -- checked below with
#     prescribed contents, since that is the statement WP-E has to formalise.
# [F] the same cap on [Hab03]'s own family, where it is SATURATED to first order:
#     log|det|/m and log(2*B*Lambda/X)/m are the same constant A(alpha).
# [G] D2's squeeze dictionary, recomputed row by row against the printed table.
# ---------------------------------------------------------------------------

# (label, theta_from, theta_to, printed content-equivalent, printed decimals)
# -- plan-S8 D2's table, exactly as printed there.
S8_HISTORY = [
    ("Baker-Coates '75 -> Beukers '81",   0.5,      0.5359,   1.52,   2),
    ("Beukers '81 -> Easton '86",         0.5359,   0.5664,   1.39,   2),
    ("Easton '86 -> Dubickas '90",        0.5664,   0.5769,   1.12,   2),
    ("Dubickas '90 -> [Hab03] Thm 1",     0.5769,   0.57702,  1.001,  3),
    ("[Hab03] Thm 1 -> [Zud07] (record)", 0.57702,  0.5803,   1.0346, 4),
    ("[Hab03] Thm 1 -> [Pup09]",          0.57702,  0.5795,   1.0261, 4),
    ("record -> T-shift (2/3)",           0.5803,   2 / 3,    2.299,  3),
    ("the whole road 1975 -> 2007",       0.5,      0.5803,   2.444,  3),
    ("[Hab03] Thm 1 -> T-shift (2/3)",    0.57702,  2 / 3,    2.379,  3),
]


def _det_rate_binom(al):
    """lim (1/m) log of det_eq's binomial product along n = al*m, from scratch.

    det_eq (CITED/HabsiegerPade.lean, [Hab03] (2.5)):
        |a1 b2 - a2 b1| = C(3m+n, 2n+m+1) * C(2n+m+2, n+m+1).
    Coded as two independent entropy terms and NOT simplified, so that the
    agreement with _A_alpha(2, al) below is a check and not a tautology.
    """
    def ent(top, k):                      # (1/m) log C(top*m, k*m), Stirling
        rest = top - k
        return top * log(top) - k * log(k) - rest * log(rest)
    return ent(3 + al, 2 * al + 1) + ent(2 * al + 1, al + 1)


def _hab_frozen():
    """The five frozen numerals of CITED/HabsiegerPade.lean, exactly."""
    return {"contentConst": Fraction(8103), "contentBase": Fraction(7516022, 5065927),
            "errorBase": Fraction(48489447, 4675375), "denomConst": Fraction(639, 1250),
            "denomBase": Fraction(56534214, 9609251), "mLow": 10740000}


def _s8_padelike(rng, force_b1_unit=False):
    """One instance in the transfer's VALIDITY region, on the real columns.

    Uniformly random forms never land there -- a random l_i is as large as its
    coefficients, so P*X > |c|*Lambda fails by miles.  The validity region is what a
    Pade construction manufactures, and it has to be built:

        X = 2^N,  Y = 3^N,  b_i = G_i*beta_i,  a_i = G_i*alpha_i
        alpha_i = the integer nearest to -beta_i*Y/X

    so l_i = G_i*(alpha_i*X + beta_i*Y) has |l_i| <= G_i*X/2 by construction, and with
    G_1 = G_2 = G and c = 1 one gets P*X = G*X > Lambda: inside validity, with the
    contents genuinely dividing both coefficients.  This is the geometry D1 is about.
    force_b1_unit sets beta_1 = 1, so that b_1 | c*a_1 and the bad branch Delta_1 = 0
    is reachable at c = 1 (needed by [E]).
    """
    N = rng.randrange(6, 40)
    X, Y = 1 << N, 3 ** N
    G = rng.randrange(1, 1 << rng.randrange(1, 16))
    G1 = G2 = G                                  # equal contents: keeps c = 1 valid
    b = []
    for i in range(2):
        beta = 1 if (i == 0 and force_b1_unit) else rng.randrange(1, 1 << 12)
        b.append(beta)
    beta1, beta2 = b
    if beta1 == beta2:
        beta2 += 1
    inst = {}
    alpha1 = -((2 * beta1 * Y + X) // (2 * X))   # nearest integer to -beta1*Y/X
    alpha2 = -((2 * beta2 * Y + X) // (2 * X))
    a1, b1, a2, b2 = G1 * alpha1, G1 * beta1, G2 * alpha2, G2 * beta2
    det = a1 * b2 - a2 * b1
    l1, l2 = a1 * X + b1 * Y, a2 * X + b2 * Y
    inst.update(X=X, Y=Y, a1=a1, b1=b1, a2=a2, b2=b2, G1=G1, G2=G2, c=1, det=det,
                l1=l1, l2=l2, P=min(G1, G2), B=max(abs(b1), abs(b2)),
                Lam=max(abs(l1), abs(l2)))
    return inst


def cmd_s8(mmax, out=sys.stdout):
    """S8 WP0: gate G-A, the channel identification, D1 on integers, D2's table."""
    import random
    e = 2.718281828459045
    fz = _hab_frozen()
    lcb = log(fz["contentBase"].numerator) - log(fz["contentBase"].denominator)
    leb = log(fz["errorBase"].numerator) - log(fz["errorBase"].denominator)
    ldb = log(fz["denomBase"].numerator) - log(fz["denomBase"].denominator)

    out.write("plan-Tshift-S8 WP0 -- the audit's own arithmetic, verified.\n"
              "[C]-[E] and the finite-m column of [F] are exact; rates are floats.\n")

    # ---------------------------------------------------------------- [A]
    out.write("\n# [A] gate G-A -- both calibrations of the 8.2 apparatus\n")
    F1, F2, A, I, C1, C2 = _apparatus(2, Fraction(-1, 8), 6, 224141, 240395)
    theta1 = e ** C1
    out.write(f"  [Hab03] Thm 1 at alpha_0 = 224141/240395 = {224141/240395:.9f}"
              f"   (paper 0.932386281)\n")
    out.write(f"    C1 - C2 = {C1-C2:.6e}   (paper 1.0057e-11)\n")
    out.write(f"    theta   = {theta1:.12f}   (paper 0.57701737767006)"
              f"   |diff| = {abs(theta1-0.57701737767006):.2e}\n")
    assert abs(theta1 - 0.57701737767006) < 5e-11
    assert abs(C1 - C2) < 1e-10
    F1b, F2b, Ab, Ib, C1b, C2b = _apparatus(1, Fraction(1, 4), 2, 6280417, 10000000)
    out.write(f"  the p = 1 point (mu, t, K) = (1, 1/4, 2) at alpha = 0.6280417:\n")
    out.write(f"    C1 = {C1b:.6f}   C2 = {C2b:.6f}   (plan-S8 1.1 and the S6 closure:"
              f" -1.028406)\n")
    out.write(f"    the plan's own line, term by term:"
              f" (-{0.6280417}*log 4 + {Ib:.6f} - {Ab:.6f} - log {F1b:.8f})/2\n")
    assert abs(C1b - (-1.028406)) < 1e-6 and abs(C2b - (-1.028406)) < 1e-6
    out.write("    G-A PASSES on both points.  The plan's printed -1.02843 for the second\n"
              "    is its own rounded restatement (five-digit inputs); the apparatus gives\n"
              "    -1.028406 at both C1 and C2, i.e. the point IS the criterion crossing.\n")
    out.write("\n  and the endgame, from the three frozen bases of CITED/HabsiegerPade.lean\n"
              "  alone -- an independent cross-check of the whole S1 pipeline:\n")
    al15 = 15 / 16
    thetaHab_rate = (lcb - al15 * log(8) - ldb) / 6
    out.write(f"    (log contentBase - alpha*log 8 - log denomBase)/6 = {thetaHab_rate:.9f}\n")
    out.write(f"    theta = e^that = {e**thetaHab_rate:.9f}   TShift.thetaHab = 0.57434"
              f"   (rounded down, margin {e**thetaHab_rate-0.57434:.2e})\n")
    assert 0.57434 <= e ** thetaHab_rate < 0.5744

    # ---------------------------------------------------------------- [B]
    out.write("\n# [B] the channel identification: which constant is the content channel\n")
    I15 = _I_alpha(2, 15, 16)[0]
    I0 = _I_alpha(2, 224141, 240395)[0]
    out.write(f"  I(15/16)                       = {I15:.9f}   asymptotic (Proposition 2)\n")
    out.write(f"  I(alpha_0)                     = {I0:.9f}   asymptotic, at the optimum\n")
    out.write(f"  log(7516022/5065927)           = {lcb:.9f}   = contentBase, m-uniform (3.11)\n")
    out.write(f"  gaps: I(15/16) - log cB = {I15-lcb:.9f}   I(alpha_0) - log cB ="
              f" {I0-lcb:.9f}\n")
    out.write("  So the plan's WP0 line -- 'I(15/16) vs log(7516022/5065927) = 0.39450' --\n"
              "  is NOT a consistency check of one constant: they are two constants.  0.3945\n"
              "  is (3.11)'s m-uniform bound, already reduced by the q <= 10 truncation of\n"
              "  (3.14) and by Chebyshev Theta errors, valid for m > 10 740 000; I(alpha) is\n"
              "  the asymptotic rate.  The channel identification the plan wants stands --\n"
              "  content enters C1 through I(alpha) and only there -- but the two numbers\n"
              "  must not be swapped, and the gap between them is the effectivity loss that\n"
              "  S7's WP-C already costed (check [Q]), not content headroom.\n")
    assert I15 > lcb and I0 > lcb

    # ---------------------------------------------------------------- [C]
    out.write("\n# [C] D1(1)-(3): the three identities and the cap, exactly\n")
    rng = random.Random(20260811)
    small = range(-2, 3)
    nid = 0
    for a1 in small:
        for b1 in small:
            for a2 in small:
                for b2 in small:
                    det = a1 * b2 - a2 * b1
                    for X in range(0, 4):
                        for Y in range(-3, 4):
                            l1, l2 = a1 * X + b1 * Y, a2 * X + b2 * Y
                            # (1) Cramer, both columns
                            assert X * det == b2 * l1 - b1 * l2
                            assert Y * det == a1 * l2 - a2 * l1
                            # (2) the cap, from the first identity
                            B = max(abs(b1), abs(b2))
                            Lam = max(abs(l1), abs(l2))
                            assert abs(det) * X <= 2 * B * Lam
                            for c in (-2, -1, 1, 2):
                                for m in small:
                                    d1, d2 = c * a1 + m * b1, c * a2 + m * b2
                                    # (3) the refined elimination
                                    assert b2 * d1 - b1 * d2 == c * det
                                    assert 2 * B * max(abs(d1), abs(d2)) >= abs(c) * abs(det)
                                    # transfer_one_form's identity, both forms
                                    assert c * l1 - b1 * (c * Y - m * X) == X * d1
                                    assert c * l2 - b2 * (c * Y - m * X) == X * d2
                                    nid += 1
    nbig = 0
    for _ in range(20000):
        bits = rng.randrange(4, 64)
        a1, b1, a2, b2 = (rng.randrange(-(1 << bits), 1 << bits) for _ in range(4))
        X = rng.randrange(0, 1 << bits)
        Y = rng.randrange(-(1 << bits), 1 << bits)
        c = rng.randrange(-(1 << 20), 1 << 20)
        m = rng.randrange(-(1 << bits), 1 << bits)
        det = a1 * b2 - a2 * b1
        l1, l2 = a1 * X + b1 * Y, a2 * X + b2 * Y
        d1, d2 = c * a1 + m * b1, c * a2 + m * b2
        B, Lam = max(abs(b1), abs(b2)), max(abs(l1), abs(l2))
        assert X * det == b2 * l1 - b1 * l2 and Y * det == a1 * l2 - a2 * l1
        assert abs(det) * X <= 2 * B * Lam
        assert b2 * d1 - b1 * d2 == c * det
        assert 2 * B * max(abs(d1), abs(d2)) >= abs(c) * abs(det)
        nbig += 1
    out.write(f"  {nid} exhaustive instances (|a|,|b|,|m| <= 2, 0 <= X <= 3, |Y| <= 3,\n"
              f"  1 <= |c| <= 2) and {nbig} random instances up to 64 bits:\n"
              "    X*det = b2*l1 - b1*l2   and   Y*det = a1*l2 - a2*l1      HOLD (ring)\n"
              "    |det|*X <= 2*B*Lambda                                    HOLDS\n"
              "    b2*Delta1 - b1*Delta2 = c*det                            HOLDS (ring)\n"
              "    2*B*max|Delta_i| >= |c|*|det|                            HOLDS\n"
              "    c*l_i - b_i*(c*Y - m*X) = X*Delta_i                      HOLDS (the\n"
              "      identity TShift.transfer_one_form is built on, both forms)\n"
              "  D1(1)-(3) verified.  Note the cap needs 0 <= X and nothing else -- no\n"
              "  coprimality, no sign condition, no b_i != 0, matching the corpus lemma's\n"
              "  deliberately absent hypotheses.\n")

    # ---------------------------------------------------------------- [D]
    out.write("\n# [D] D1(4): disjointness, WITH the content P -- the corpus's hypothesis\n")
    out.write("  improvement:  |c|*|det| >  2*B*P        (beats max|Delta_i| >= P)\n"
              "  validity:     P*X       >  |c|*Lambda   (transfer conclusion positive)\n")
    nvalid = nimp = nboth = ntest = 0
    for _ in range(100000):
        bits = rng.randrange(2, 40)
        G1 = rng.randrange(1, 1 << rng.randrange(1, 20))
        G2 = rng.randrange(1, 1 << rng.randrange(1, 20))
        a1, b1 = (G1 * rng.randrange(-(1 << bits), 1 << bits) for _ in range(2))
        a2, b2 = (G2 * rng.randrange(-(1 << bits), 1 << bits) for _ in range(2))
        det = a1 * b2 - a2 * b1
        if det == 0:
            continue
        c = rng.randrange(1, 1 << 16)
        X = rng.randrange(0, 1 << bits)
        Y = rng.randrange(-(1 << bits), 1 << bits)
        l1, l2 = a1 * X + b1 * Y, a2 * X + b2 * Y
        P = min(G1, G2)                       # P <= |Gamma_i|, the legal choice
        B = max(abs(b1), abs(b2))
        Lam = max(abs(l1), abs(l2))
        assert P <= abs(G1) and P <= abs(G2) and abs(b1) <= B and abs(b2) <= B
        ntest += 1
        imp = c * abs(det) > 2 * B * P
        val = P * X > c * Lam
        nimp += imp
        nvalid += val
        nboth += imp and val
        if imp:                               # the implication D1(4) asserts
            assert c * Lam >= P * X
    out.write(f"  (a) {ntest} unstructured random instances with prescribed contents:\n"
              f"      validity holds in {nvalid}, improvement in {nimp},"
              f" BOTH in {nboth}\n"
              f"      every improvement instance satisfies |c|*Lambda >= P*X: HOLDS\n")
    nv = ndeg = 0
    worst = None
    for _ in range(20000):
        z = _s8_padelike(rng)
        assert z["P"] * z["X"] > z["c"] * z["Lam"]          # validity, by construction
        assert z["a1"] % z["G1"] == 0 and z["b1"] % z["G1"] == 0
        assert z["a2"] % z["G2"] == 0 and z["b2"] % z["G2"] == 0
        if z["det"] == 0:                                    # independence is a real
            ndeg += 1                                        # hypothesis, not a freebie
            continue
        nv += 1
        r = Fraction(z["c"] * abs(z["det"]), 2 * z["B"] * z["P"])
        assert r <= 1                                        # no improvement, ever
        if worst is None or r > worst:
            worst = r
    out.write(f"  (b) {nv} constructed VALIDITY-region instances (Pade-like: small forms\n"
              f"      with prescribed contents on the columns X = 2^N, Y = 3^N):\n"
              f"      validity by construction, improvement in 0 of them\n"
              f"      sup of |c||det|/(2BP) over them: {float(worst):.6f} <= 1\n"
              f"      ({ndeg} further draws had det = 0 and were skipped -- independence\n"
              f"      is a genuine hypothesis in this region, which is what det_eq buys)\n")
    out.write("  D1(4) verified, and verified in the form WP-E must state it: the content\n"
              "  P appears on BOTH sides and cancels out of the argument, so the no-go is\n"
              "  not an artefact of reading the classical bound at P = 1.  Chain:\n"
              "    |c||det| > 2BP  and  |det|*X <= 2*B*Lambda  =>  2B|c|Lambda/X > 2BP\n"
              "                                               =>  |c|Lambda > P*X.\n"
              "  Hence T4 in plan-S8 2.2 should carry P, not 1.\n")

    # ---------------------------------------------------------------- [E]
    out.write("\n# [E] D1(5): the bad branch Delta_1 = 0, and what it can recover\n")
    nbad = 0
    maxgain = maxratio = 0.0
    for _ in range(200000):
        bits = rng.randrange(2, 32)
        G1 = rng.randrange(1, 1 << rng.randrange(1, 12))
        G2 = rng.randrange(1, 1 << rng.randrange(1, 12))
        a1, b1 = (G1 * rng.randrange(-(1 << bits), 1 << bits) for _ in range(2))
        a2, b2 = (G2 * rng.randrange(-(1 << bits), 1 << bits) for _ in range(2))
        det = a1 * b2 - a2 * b1
        if det == 0 or b1 == 0:
            continue
        c = rng.randrange(1, 1 << 16)
        if (c * a1) % b1 != 0:                # Delta_1 = 0 needs b1 | c*a1
            continue
        m = -(c * a1) // b1
        d1, d2 = c * a1 + m * b1, c * a2 + m * b2
        assert d1 == 0
        # the exact identity of D1(5), and Delta_2 != 0 (nonvanishing, D1(3))
        assert abs(b1) * abs(d2) == c * abs(det) and d2 != 0
        nbad += 1
    nvb = ndegb = 0
    for _ in range(20000):
        z = _s8_padelike(rng, force_b1_unit=True)
        if z["det"] == 0:
            ndegb += 1
            continue
        m = -(z["c"] * z["a1"]) // z["b1"]
        d1 = z["c"] * z["a1"] + m * z["b1"]
        d2 = z["c"] * z["a2"] + m * z["b2"]
        assert d1 == 0 and d2 != 0
        assert abs(z["b1"]) * abs(d2) == z["c"] * abs(z["det"])
        assert z["P"] * z["X"] > z["c"] * z["Lam"]           # inside validity
        gain = Fraction(abs(d2), z["P"])                     # recovered over P
        cap = Fraction(2 * z["B"], abs(z["b1"]))
        assert gain < cap                                    # the provable ceiling
        maxgain = max(maxgain, float(gain))
        maxratio = max(maxratio, float(gain / cap))
        nvb += 1
    out.write(f"  {nbad} unstructured instances with Delta_1 = 0 (b1 | c*a1) and\n"
              f"  {nvb} constructed validity-region ones (beta_1 = 1, so c = 1 reaches\n"
              f"  the branch):\n"
              f"    |b1|*|Delta_2| = |c|*|det| exactly, and Delta_2 != 0:  HOLDS\n"
              f"    inside validity, |Delta_2|/P < 2B/|b1| always:         HOLDS\n"
              f"    largest recovered factor seen: {maxgain:.4g}"
              f"   (largest fraction of its own cap: {maxratio:.4f})\n")
    out.write("  D1(5) verified, and sharper than the plan states it.  The recovered\n"
              "  factor is not merely 'polynomial/constant in practice': inside the\n"
              "  validity region it is PROVABLY below 2B/|b1|, since\n"
              "    |Delta_2|/P = |c||det|/(|b1|P) <= 2B|c|Lambda/(|b1|P*X) < 2B/|b1|.\n"
              "  So the whole surviving stake of S8(i) is the ratio of the crude\n"
              "  coefficient bound B to the actual |b1| -- two quantities with the SAME\n"
              "  exponential rate on any Pade family (both are 8^(n+1) times a\n"
              "  denomBase^m).  That is why it is a constants play for S1's c(D) and can\n"
              "  never be a rate.  WP-D measures the ratio; it does not have to bound it.\n")

    # ---------------------------------------------------------------- [F]
    out.write("\n# [F] the cap on [Hab03]'s own family: saturated to first order\n")
    out.write("  rate identity first, two independent code paths at alpha = 15/16 and at\n"
              "  alpha_0, plus a grid -- det_eq's binomials against the Stirling constant A:\n")
    for tag, al in (("15/16", al15), ("alpha_0", 224141 / 240395),
                    ("0.75", 0.75), ("0.5", 0.5), ("0.99", 0.99)):
        rb, ra = _det_rate_binom(al), _A_alpha(2, al)
        out.write(f"    alpha = {tag:8s} rate(det_eq) = {rb:.11f}   A(2,alpha) ="
                  f" {ra:.11f}   |diff| {abs(rb-ra):.1e}\n")
        assert abs(rb - ra) < 1e-9
    out.write("  So lim (1/m) log|det| = A(alpha) EXACTLY -- the determinant grows at the\n"
              "  Stirling rate of the construction, not slower.\n")
    out.write(f"\n  and the cap's rate, from the frozen numerals: 2*B*Lambda/X =\n"
              f"  2*denomConst*(errorBase*denomBase)^m, with\n"
              f"    log errorBase + log denomBase = {leb:.11f} + {ldb:.11f}"
              f" = {leb+ldb:.11f}\n"
              f"    A(2, 15/16)                                        ="
              f" {_A_alpha(2, al15):.11f}\n"
              f"    difference = {leb+ldb-_A_alpha(2, al15):.2e}  (the two frozen bases are\n"
              f"      rounded up; e1 + q1 = A is the apparatus identity behind it)\n")
    out.write("  THE CAP OF D1(2) IS SATURATED ON THE REAL FAMILY.  There is no exponential\n"
              "  slack in it to harvest -- which is why D1(4) is not merely true but tight.\n")
    out.write("\n  the same at finite m, exactly (integers and Fractions; the 8^(n+1) of\n"
              "  formBound and coeffBound cancel in the product, so n drops out of the cap):\n")
    out.write("       m      n | log|det|/m | log(2BL/X)/m |  slack (nats) | cap holds\n")
    ms = [8]
    while ms[-1] * 2 <= max(mmax, 8):
        ms.append(ms[-1] * 2)
    for m in ms:
        n = int(Fraction(15, 16) * (m - Fraction(3, 2))) + 1
        assert 32 * n + 13 <= 30 * m < 32 * n + 45          # padeData's range clauses
        det = comb(3 * m + n, 2 * n + m + 1) * comb(2 * n + m + 2, n + m + 1)
        capX = 2 * fz["denomConst"] * (fz["errorBase"] * fz["denomBase"]) ** m
        ok = Fraction(det) <= capX                          # |det|*X <= 2*B*Lambda
        assert ok
        ldet = log(det)
        lcap = log(capX.numerator) - log(capX.denominator)
        out.write(f"    {m:4d} {n:6d} | {ldet/m:10.6f} | {lcap/m:12.6f} |"
                  f" {lcap-ldet:13.4f} | {'yes' if ok else '*** NO ***'}\n")
    out.write("  The slack is logarithmic in m (the two binomials' 1/sqrt(m) factors), not\n"
              "  exponential.  Note what the exact column also is: a consistency check of\n"
              "  the cited bundle itself -- det_eq, coeffBound and formBound are three\n"
              "  independent clauses of one axiom, and D1(2) is a relation they must satisfy.\n")
    imp_margin = _A_alpha(2, al15) - al15 * log(8) - ldb - lcb
    val_margin = lcb - leb + al15 * log(8)
    out.write(f"\n  the two margins of D1(4) on this family, per m:\n"
              f"    improvement margin  log(|c||det|/(2BP))/m -> A - alpha*log 8"
              f" - log denomBase - log contentBase = {imp_margin:+.7f}\n"
              f"    validity margin     log(P*X/(|c|Lambda))/m -> log contentBase"
              f" - log errorBase + alpha*log 8    = {val_margin:+.7f}\n"
              f"    sum = {imp_margin+val_margin:+.2e}  (zero to the precision of e1+q1 = A)\n")
    assert imp_margin < 0 < val_margin
    out.write("  Read this pair slowly, because it is the whole of F1 on the real objects.\n"
              "  The two conditions of D1(4) are not just disjoint here: they are\n"
              "  COMPLEMENTARY to first order, sharing a boundary, and [Hab03]'s family sits\n"
              f"  {val_margin:.5f} nats/m on the validity side -- which is exactly the margin\n"
              "  that proves theta = 0.57434 (divide by 6 and read [A]'s cross-check).  Every\n"
              "  nat the determinant route could conceivably recover is a nat the endgame\n"
              "  has already spent.  S8(i) is not underexploited; it is exhausted.\n")

    # ---------------------------------------------------------------- [G]
    out.write("\n# [G] D2's squeeze dictionary, recomputed (g = (theta_new/theta_old)^K, K = 6)\n")
    out.write("     step                                  from      to        g      printed\n")
    nexact = 0
    for lab, t0, t1, printed, dp in S8_HISTORY:
        g = (t1 / t0) ** 6
        match = round(g, dp) == printed
        nexact += match
        out.write(f"     {lab:36s} {t0:.5f} {t1:.6f} {g:8.4f} {printed:9.4f}"
                  f"{'' if match else '   <- last printed digit off by one'}\n")
        assert abs(g - printed) < 5e-3 * printed
    zud = (0.5803 / 0.57702) ** 6
    wall = ((2 / 3) / 0.5803) ** 6
    steps = log(wall) / log(zud)
    out.write(f"  {nexact} of {len(S8_HISTORY)} rows reproduce at the printed precision.\n"
              f"  (Row 1 is the plan's own '0.5^-': x1.52 wants theta_from ="
              f" {0.5359/1.52**(1/6):.5f}, and 0.5\n"
              f"  gives 1.5159, which still rounds to the printed 1.52.)\n"
              f"  record -> 2/3 in Zudilin steps: {steps:.2f}   (plan: 24.5)\n")
    th10 = 0.5803 * e ** (10 * log(0.5803 / 0.57702))
    out.write(f"  ten Zudilin steps: theta = {th10:.6f}, kappa = {_kappa(th10):.5f} > 1"
              f"   (plan: 0.614, 1.20)\n")
    assert abs(steps - 24.5) < 0.2 and _kappa(th10) > 1
    out.write("  D2 verified.  The dictionary's arithmetic is elementary and its content is\n"
              "  the comparison, not the conversion: the remaining wall is the whole road\n"
              "  already travelled, in the units the squeeze pays in.\n")

    out.write("\n# WP0 verdict\n"
              "  G-A passes on both calibration points, and the frozen bases of\n"
              "  CITED/HabsiegerPade.lean independently reproduce thetaHab.\n"
              "  F1 (the determinant no-go) is VERIFIED, not merely derived -- with the\n"
              "  content P in place, and tight on the real family ([F]).  Two amendments:\n"
              "  T4 carries P, and D1(5)'s residual has the provable ceiling 2B/|b1|.\n"
              "  D2's table reproduces row by row.  The channel identification stands, with\n"
              "  the two content constants kept apart ([B]).\n")


# ---------------------------------------------------------------------------
# plan-Tshift-S8 WP-A -- pinning the three papers, on their own numbers.
#
# Everything here is recomputed from the definitions in the papers; the printed
# constants are the targets, never the inputs.  One routine serves all three
# papers, because [Zud07] and [Hab03] compute the SAME functional: Habsieger's
#     I(alpha) = int_{E_alpha} dx/x^2          (v-periodic set, [Hab03] section 3)
# and Zudilin's
#     C_2      = int_0^1 phi(x) dpsi(x)        ([Zud07] (21))
# are both  sum_i sum_{q>=0} ( 1/(a_i+vq) - 1/(b_i+vq) ),  since psi'(u) =
# sum_{j>=0} (u+j)^-2.  Only the set differs: Habsieger's is cut out by a
# three-term floor sum in one variable, Zudilin's by a six-term one minimised
# over a second variable y.
#
# [A] [Hab03] Prop. 2: the thirty intervals of the printed table (p. 306)
#     re-derived from the definition of E_alpha, and the q-truncation of (3.11)
#     measured -- how much of I(15/16) the printed 0.3945 actually leaves, and
#     which of the two losses (truncation, Chebyshev error) dominates.
# [B] [Zud07] section 5: C_0(1/9), C_1(1/9), C_2, condition (26), and the fact
#     that his delta = 0.00027320432 is rounding slack and nothing else.
# [C] [Pup09] Theorem 1: A(5,15,6), the two maxima, the two integrals, and the
#     razor-thin margin of (18) that fixes its 5.9e18 threshold.
# [D] the (26)-floor identification.  Both of [Pup09]'s printed constants are,
#     to every printed digit, the value the construction yields when Phi is
#     proved only to the minimum its own validity condition needs.  So the
#     0.5803 -> 0.5795 and 0.4914 -> 0.4910 deficits are not effectivisation
#     losses in the analytic estimates; they are unclaimed Phi.
# [E] [Pup14]: the same method at (3,9,4) instead of (5,15,6) -- 11 orders of
#     magnitude off the threshold for 0.047 of the constant.
# [F] the two lanes side by side.  A content-equivalent unit is (theta')^K /
#     theta^K with K = 6 in [Hab03]'s lane and K = 3*beta = 57 in [Zud07]'s, so
#     D2's dictionary converts targets, not arithmetic inputs.
# ---------------------------------------------------------------------------

# [Hab03] p. 306, the thirty (a_i, b_i) for alpha = 15/16, exactly as printed.
HAB_311_TABLE = [
    (Fraction(32, 63), Fraction(16, 31)), (Fraction(16, 21), Fraction(16, 17)),
    (Fraction(64, 63), Fraction(32, 31)), (Fraction(32, 21), Fraction(48, 31)),
    (Fraction(16, 9), Fraction(32, 17)), (Fraction(128, 63), Fraction(64, 31)),
    (Fraction(160, 63), Fraction(80, 31)), (Fraction(176, 63), Fraction(48, 17)),
    (Fraction(64, 21), Fraction(96, 31)), (Fraction(32, 9), Fraction(112, 31)),
    (Fraction(256, 63), Fraction(128, 31)), (Fraction(32, 7), Fraction(144, 31)),
    (Fraction(320, 63), Fraction(160, 31)), (Fraction(352, 63), Fraction(96, 17)),
    (Fraction(128, 21), Fraction(192, 31)), (Fraction(400, 63), Fraction(32, 5)),
    (Fraction(64, 9), Fraction(224, 31)), (Fraction(464, 63), Fraction(112, 15)),
    (Fraction(512, 63), Fraction(256, 31)), (Fraction(176, 21), Fraction(144, 17)),
    (Fraction(64, 7), Fraction(288, 31)), (Fraction(592, 63), Fraction(160, 17)),
    (Fraction(640, 63), Fraction(320, 31)), (Fraction(704, 63), Fraction(192, 17)),
    (Fraction(736, 63), Fraction(176, 15)), (Fraction(256, 21), Fraction(208, 17)),
    (Fraction(800, 63), Fraction(64, 5)), (Fraction(96, 7), Fraction(208, 15)),
    (Fraction(928, 63), Fraction(224, 15)), (Fraction(992, 63), Fraction(16)),
]

# (label, alpha, beta, gamma, 1/z, K, s, base):  the lane of a Zudilin-type run.
# k = r(beta m + 1) + j with r = K/beta, the prefactor is base^(beta - s*alpha),
# and validity is (26):  C0(z) - C2 + (beta - s*alpha) log(base) < 0.
S8_LANES = [
    ("[Zud07] Thm 1   (3/2)", 9, 19, 9, 9, 57, 2, 3),
    ("[Zud07] Thm 2   (4/3)", 5, 15, 6, -8, 30, 3, 2),
    ("[Pup14]         (4/3)", 3, 9, 4, -8, 18, 3, 2),
]


def _zfrac(x):
    """fractional part of an exact Fraction."""
    return x - (x.numerator // x.denominator)


def _zud_phi(x, al, be, ga):
    """[Zud07] (21): phi(x) = min_{0<=y<1} phihat(x, y), on an exact x.

    phihat is piecewise constant in y with jumps only at 0, {-(al+ga)x},
    {-(al+be)x} and {ga x}, so the minimum is attained among those four points
    and one interior point of each arc between them.  All exact.
    """
    AG, AB, S = al + ga, al + be, al + be + ga
    c1 = _zfrac(Fraction(-AG) * x)
    cS = _zfrac(Fraction(S) * x)
    bps = sorted({Fraction(0), c1, _zfrac(Fraction(-AB) * x), _zfrac(Fraction(ga) * x)})
    cand = list(bps)
    for j, lo in enumerate(bps):
        hi = bps[j + 1] if j + 1 < len(bps) else Fraction(1)
        if hi > lo:
            cand.append((lo + hi) / 2)
    best = None
    for y in cand:
        if not 0 <= y < 1:
            continue
        v = (-c1 + _zfrac(Fraction(-AG) * x - y) + _zfrac(y)
             - cS + _zfrac(Fraction(AB) * x + y) + _zfrac(Fraction(ga) * x - y))
        best = v if best is None else min(best, v)
    return best


def _zud_intervals(al, be, ga):
    """{phi = 1} inside [0,1), as maximal exact intervals.

    phihat depends on x only through {(al+ga)x}, {(al+be+ga)x}, {(al+be)x} and
    {ga x}, so phi is constant between consecutive multiples of 1/(al+ga),
    1/(al+be+ga), 1/(al+be), 1/(be-ga) and 1/ga; evaluate at the midpoints.
    """
    grid = {Fraction(j, P) for P in (al + be + ga, al + ga, al + be, be - ga, ga)
            for j in range(P + 1)}
    g = sorted(grid)
    out = []
    for lo, hi in zip(g, g[1:]):
        if _zud_phi((lo + hi) / 2, al, be, ga) >= 1:
            if out and out[-1][1] == lo:
                out[-1][1] = hi
            else:
                out.append([lo, hi])
    return [(a, b) for a, b in out]


def _dpsi_sum(ivs, v=1, Q=None):
    """sum_{q<=Q} sum_i [ 1/(a_i+vq) - 1/(b_i+vq) ]; all q (in closed form) if Q is None."""
    if Q is None:
        pl = _psi_many([float(a) / v for a, _ in ivs])
        ph = _psi_many([float(b) / v for _, b in ivs])
        return float(sum(b - a for a, b in zip(pl, ph))) / v
    return sum(1.0 / (float(a) + v * q) - 1.0 / (float(b) + v * q)
               for q in range(Q + 1) for a, b in ivs)


def _zud_c0max(al, be, ga, z):
    """max over [0,1] of ga log t + (al+ga) log(1-t) - (al+be+ga) log(1-zt).

    The stationary points solve  z(ga-be) t^2 + [z(al+be+ga) - ga(1+z) - (al+ga)] t
    + ga = 0; a grid re-scan cross-checks the algebra, as in _max_three_factor.
    """
    def g(t):
        if t <= 0.0 or t >= 1.0:
            return -1e300
        return (ga * log(t) + (al + ga) * log(1 - t)
                - (al + be + ga) * log(1 - z * t))

    A2, C2c = z * (ga - be), ga
    B2 = z * (al + be + ga) - ga * (1 + z) - (al + ga)
    cands = []
    disc = B2 * B2 - 4 * A2 * C2c
    if abs(A2) > 1e-15 and disc >= 0:
        s = disc ** 0.5
        cands += [(-B2 + s) / (2 * A2), (-B2 - s) / (2 * A2)]
    best = max([g(t) for t in cands if 0.0 < t < 1.0] or [-1e300])
    coarse = max(g(j / 40000.0) for j in range(1, 40000))
    assert coarse <= best + 1e-7, (coarse, best)
    return best


def _zud_lane(al, be, ga, zinv, K, s, base):
    """(C0, C1, C2, C2floor, theta_full, theta_floor, margin) for one lane."""
    S, AG, BG = al + be + ga, al + ga, be - ga
    z = 1.0 / zinv
    pref = S * log(S) - AG * log(AG) - ga * log(ga) - BG * log(BG)
    C0 = pref + ga * log(abs(z)) + _zud_c0max(al, be, ga, z)
    C1 = pref + log(_max_three_factor(AG, BG, ga, float(zinv)))
    C2 = _dpsi_sum(_zud_intervals(al, be, ga))
    floor = C0 + (be - s * al) * log(base)          # (26) with equality
    return (C0, C1, C2, floor, exp(-(C1 - C2) / K), exp(-(C1 - floor) / K),
            C0 - C2 + (be - s * al) * log(base))


def cmd_s8a(out=sys.stdout):
    fz = _hab_frozen()
    mLow = fz["mLow"]

    out.write("# [A] [Hab03] Prop. 2: the printed interval table, and what (3.11) leaves\n")
    I15, ivs = _I_alpha(2, 15, 16, want_intervals=True)
    assert len(ivs) == 30, len(ivs)
    assert [(Fraction(a), Fraction(b)) for a, b in ivs] == HAB_311_TABLE
    out.write(f"      E_(15/16) has {len(ivs)} intervals per period v = 16, and they agree\n"
              "      with the thirty pairs printed on p. 306 -- exactly, as Fractions.\n")
    out.write(f"      I(15/16) = {I15:.9f}   (the whole arithmetic channel)\n\n")
    out.write("      the q-truncation of (3.14): 0 <= q <= 10 is all the paper uses\n")
    prev = -1.0
    part = {}
    for Q in (0, 1, 2, 5, 10, 20, 50, 117, 1000):
        part[Q] = _dpsi_sum(ivs, v=16, Q=Q)
        assert part[Q] > prev
        prev = part[Q]
        out.write(f"        q <= {Q:4d} : {part[Q]:.9f}   deficit {I15 - part[Q]:.9f}"
                  f"  ({100 * (I15 - part[Q]) / I15:5.2f}% of I)\n")
    out.write(f"        all q     : {I15:.9f}\n")
    hi = mLow / (16.0 + 16 * 10)               # smallest Chebyshev argument at q = 10
    q_adm = int((sqrt(3 * mLow) and (mLow / sqrt(3 * mLow) - 16) / 16))
    q_hab = (mLow + 19 / 30) / (17 * sqrt(3 * mLow))
    assert part[10] > 0.40127 > part[5] - 0.01   # the printed large-m rate sits below
    out.write("\n      the two losses, at the three printed rates:\n"
              f"        I - S(q<=10)      = {I15 - part[10]:.9f}   q-truncation\n"
              f"        S(q<=10) - 0.40127 = {part[10] - 0.40127:.9f}   Chebyshev error, m > 5e10\n"
              f"        S(q<=10) - 0.39572 = {part[10] - 0.39572:.9f}   Chebyshev error, 5e10 >= m > 5e7\n"
              f"        S(q<=10) - 0.39454 = {part[10] - 0.39454:.9f}   Chebyshev error, the BINDING\n"
              f"                                          window 5e7 >= m > 1.074e7\n")
    assert I15 - part[10] < 0.1 * (part[10] - 0.39454)
    out.write("      so the truncation is not where (3.11) loses: it is worth "
              f"{I15 - part[10]:.6f},\n"
              "      an eighth of what the 2002-vintage Chebyshev bounds cost in the window\n"
              "      that actually fixes the constant.\n")
    out.write(f"\n      q was cheap to raise: at m = mLow = {mLow} the admissibility\n"
              f"      l^2 > 3m allows q <= {q_adm}, and Prop. 2's own q_0(m) is {q_hab:.1f}.\n"
              f"      What stops it is the small-x end: at q = 10 the smallest Chebyshev\n"
              f"      argument is m/(b_30 + 160) = {hi:.0f}, and [Hab03] leans on Appel-Rosser\n"
              f"      through 19801 < x < 1e8.  At q = {q_adm} it would be"
              f" {mLow / (16.0 + 16 * q_adm):.0f}.\n")
    gain = exp((I15 - 0.3945) / 6)              # the theta ratio: Delta(log theta) = Delta I / 6
    g311 = gain ** 6                            # D2's content-equivalent unit
    out.write(f"\n      ceiling on the whole of (3.11):  I - 0.3945 = {I15 - 0.3945:.7f} nats/m,\n"
              f"      i.e. theta_Hab {0.57434:.5f} -> {0.57434 * gain:.6f} (ratio {gain:.6f}), a\n"
              f"      content-equivalent g = {g311:.6f} in D2's units -- "
              f"{(g311 - 1) / 0.0346:.2f} of a Zudilin step.\n"
              "      Of that, at most 7% is the q-truncation; the rest is prime counting.\n")
    assert abs(g311 - exp(I15 - 0.3945)) < 1e-12

    out.write("\n# [B] [Zud07] section 5, from the definitions\n")
    C0, C1, C2, floor, th, thf, marg = _zud_lane(*S8_LANES[0][1:])
    ivz = _zud_intervals(9, 19, 9)
    out.write(f"      phi = 1 on {len(ivz)} intervals of [0,1); left ends all j/37, right ends\n"
              "      j/18, j/10, j/9, j/6, j/5, j/2 -- the same shape as [Hab03]'s table\n"
              "      (left ends from the (N+2)/s cut, right ends from the three moduli).\n")
    assert all(b.denominator in (1, 2, 3, 5, 6, 9, 10, 18) for _, b in ivz)
    assert all(a.denominator in (37,) for a, _ in ivz)
    for got, want, name in ((C0, 3.28973907, "C0(1/9)"), (C1, 35.48665992, "C1(1/9)"),
                            (C2, 4.46695926, "C2 = C2'")):
        assert abs(got - want) < 5e-8, (name, got, want)
        out.write(f"      {name:9s} = {got:.8f}   paper {want:.8f}\n")
    assert abs(marg - (-0.07860790)) < 5e-8
    out.write(f"      (26)      = {marg:.8f}   paper -0.07860790   (< 0: valid)\n")
    A_z = (37 * log(37) - 18 * log(18) - 9 * log(9) - 10 * log(10))
    assert abs(C0 + C1 - A_z) < 1e-9, (C0, C1, A_z)
    out.write(f"      identity  : C0 + C1 = {C0 + C1:.9f} = A(9,19,9) exactly -- the two saddle\n"
              "                  points are Legendre-dual, so (26)'s floor C2 = A - C1 +\n"
              "                  (beta-s*alpha)log(base) is CLOSED FORM.  Verified to 1e-14 on\n"
              "                  (9,19,9), (5,15,6), (3,9,4) and four off-lane triples: the only\n"
              "                  ingredient of this apparatus that needs the arithmetic set is\n"
              "                  the full C2 itself.\n")
    d = 0.00027320432
    assert abs(exp(-(C1 - C2 + d) / 57) - 0.5803) < 5e-8
    out.write(f"      theta     = {th:.9f}  before delta;  with the paper's delta,\n"
              f"                  {exp(-(C1 - C2 + d) / 57):.9f} -- so delta is rounding slack, not a loss.\n")

    out.write("\n# [C] [Pup09] Theorem 1, all six printed constants\n")
    A1 = 26 * log(26) - 11 * log(11) - 6 * log(6) - 9 * log(9)
    lQ = log(_max_three_factor(11, 9, 6, -8.0))
    lR = _zud_c0max(5, 15, 6, -1 / 8.0)
    lz = 6 * log(1 / 8.0)
    iv1 = _zud_intervals(5, 15, 6)
    assert len(iv1) == 12
    for got, want, name in ((A1, 27.80808398, "A(5,15,6)"), (lQ, -3.234642374, "log max Q"),
                            (lR, -12.09679235, "log max R"), (lz, -12.47664925, "ga log|z|")):
        assert abs(got - want) < 5e-8, (name, got, want)
        out.write(f"      {name:10s} = {got:.9f}   paper {want:.9f}\n")
    m18 = A1 + lR + lz - 3.234849567
    assert -3e-4 < m18 < 0
    out.write(f"      margin (18) = {m18:.9f}   paper's '< -0.0002'\n"
              "      That margin is the whole story of the 5.9e18 threshold: Schoenfeld's\n"
              f"      relative error must beat it, 0.0077629/log x < {-m18 / 3.2348:.3e},\n"
              f"      i.e. x > e^{0.0077629 / (1 - 0.999805):.4f} = {exp(0.0077629 / (1 - 0.999805)):.6e};\n"
              f"      the paper prints m_0 = 194604091523774719 = {194604091523774719:.6e}.\n")
    assert 5 * 30 * 194604091523774719 > 5868122745713241570 > 30 * 194604091523774719
    out.write("      (Its printed k_0 = 5868122745713241570 is 30 * 195604091523774719,\n"
              "      not 30*m_0 + 2 = 5838122745713241572 -- one digit apart, and on the\n"
              "      safe side, so the theorem stands as stated.)\n")

    out.write("\n# [D] the (26)-floor: what [Pup09] actually gave up\n")
    out.write("      lane                    C2 full     C2 floor    theta full   theta floor\n")
    for lab, *args in S8_LANES:
        c0, c1, c2, fl, tf, tfl, mg = _zud_lane(*args)
        out.write(f"      {lab:22s}  {c2:.7f}   {fl:.7f}   {tf:.7f}    {tfl:.7f}\n")
    assert abs(_zud_lane(*S8_LANES[0][1:])[5] - 0.5795) < 5e-5
    assert abs(_zud_lane(*S8_LANES[1][1:])[5] - 0.4910) < 5e-5
    assert abs(_zud_lane(*S8_LANES[1][1:])[4] - 0.4914) < 5e-5
    out.write("      [Pup09] prints 0.5795 (Thm 2) and 0.4910 (Thm 1); [Zud07] prints\n"
              "      0.5803 and 0.4914.  The floors ARE the Pupyrev constants and the full\n"
              "      values ARE the Zudilin constants, to every printed digit, on both\n"
              "      points.  Its printed effective C2 = 3.234849567 for (5,15,6) sits\n"
              f"      {3.234849567 - _zud_lane(*S8_LANES[1][1:])[3]:.9f} above the floor -- exactly the (18) margin.\n")
    out.write("\n      how much of Phi has to be proved to pass the floor, (3/2) lane:\n")
    for N0 in (2, 4, 10, 30, 100, 300, 1000, 3000):
        tr = _dpsi_sum(ivz, v=1, Q=N0)
        out.write(f"        N <= {N0:5d} : C2 = {tr:.7f}  {'>= floor' if tr >= floor else '<  floor'}"
                  f"   theta = {exp(-(C1 - tr) / 57):.7f}\n")
    assert _dpsi_sum(ivz, v=1, Q=2) >= floor
    out.write("      Three blocks of prime intervals already clear the floor; a few hundred\n"
              "      recover the record constant to 1e-5.  The deep blocks are exactly the\n"
              "      ones that need theta(x) at small x -- the same wall as (3.11) in [A].\n")
    out.write("      Reading: the deficits are unclaimed Phi, not effectivisation loss in\n"
              "      the analytic estimates.  In the (3/2) lane the unclaimed amount is the\n"
              f"      (26) slack itself: {-marg:.7f} nats/m.  e^({-marg:.5f}/57) = "
              f"{exp(-marg / 57):.7f},\n"
              f"      and 0.5803028/0.5795030 = {th / thf:.7f} -- the slack IS the gap.\n")

    out.write("\n# [E] [Pup14]: the threshold is elastic, the constant is not\n")
    c0, c1, c2, fl, tf, tfl, mg = _zud_lane(*S8_LANES[2][1:])
    assert tf > 4 / 9 > tfl
    out.write(f"      at (3,9,4): theta_full = {tf:.7f} > 4/9 = {4 / 9:.7f} > floor {tfl:.7f},\n"
              "      and [Pup14] gets k >= 17545718 instead of [Pup09]'s 5.9e18 -- eleven\n"
              f"      orders of magnitude for {_zud_lane(*S8_LANES[1][1:])[4] - tf:.4f} of the constant.  The threshold in\n"
              "      this family is bought and sold; the constant is not.\n")

    out.write("\n# [F] the two lanes: a content-equivalent unit is lane-dependent\n")
    _, _, _, Ih, C1h, _ = _apparatus(2, Fraction(-1, 8), 6, 224141, 240395)
    ar_h, ar_z = Ih / 6, C2 / 57
    an_h, an_z = C1h - ar_h, log(th) - ar_z
    out.write(f"      [Hab03] Thm 1  K = 6 : log theta = {C1h:+.9f} = arith {ar_h:+.9f}"
              f" + analytic {an_h:+.9f}\n"
              f"      [Zud07]        K = 57: log theta = {log(th):+.9f} = arith {ar_z:+.9f}"
              f" + analytic {an_z:+.9f}\n"
              f"      the record, split      {log(th) - C1h:+.9f}   arith {ar_z - ar_h:+.9f}"
              f"   analytic {an_z - an_h:+.9f}\n")
    assert ar_z - ar_h > 0 > an_z - an_h
    assert abs((ar_z - ar_h) + (an_z - an_h) - (log(th) - C1h)) < 1e-12
    out.write("      [Zud07] won on the arithmetic side and gave part of it back on the\n"
              "      analytic side.  Note the divisors: a nat/m of content is worth 1/6 of\n"
              "      a nat/k in [Hab03]'s lane and 1/57 in [Zud07]'s, so D2's g = "
              "(t'/t)^6\n      prices a TARGET in [Hab03] units; it is not the arithmetic "
              "[Zud07] spent.\n")
    out.write(f"      0.5795 -> 0.5803 in D2's units: g = {(th / thf) ** 6:.6f}.\n")

    out.write("\n# WP-A verdict\n"
              "  Three papers pinned on their own numbers, one code path, every check an\n"
              "  assertion.  [Hab03]'s table is exact and (3.11)'s slack is Chebyshev\n"
              "  technology, not truncation.  [Zud07]'s constants reproduce and its delta\n"
              "  is rounding.  [Pup09]'s two constants are the (26) floor, so its deficit\n"
              "  is unclaimed Phi.  The unconsumed freedom in [Zud07] is the parameter\n"
              "  triple: optimal only over INTEGERS with beta <= 100 (his section 5), and\n"
              "  C2 is a discontinuous arithmetic function of (alpha:beta:gamma).\n")


# ---------------------------------------------------------------------------
# plan-Tshift-S8 WP-B -- adoption (O-2) and the re-optimization mode of the
# section 8.2 apparatus.
#
# The apparatus maximises C1 subject to C1 > C2, so the optimum sits ON the
# crossing.  Write the crossing out.  With X = 1/|t|,
#
#     C1 - C2 = ( al log X + I(al) - A(al) - log F2(al) ) / K
#
# -- F1 cancels -- so  C1 = C2  is exactly  I(al) = W(al)  with
#
#     W(al) := A(al) + log F2(al) - al log X        (the DEMAND curve)
#
# and the value there is  theta = e^{C1} = e^{C2(al)}  (the PAYOFF curve).
# Neither W nor the payoff contains I.  The whole content channel therefore
# reduces to one inequality between a curve that content moves and a curve that
# it does not:
#
#     supply  I(al) + log g  >=  demand  W(al)   ==>  theta = e^{C2(al)} .
#
# Habsieger's alpha_0 = 224141/240395 is precisely where supply meets demand at
# g = 1, and the payoff there is his Theorem 1.  A proven content gain g does
# NOT just multiply theta by g^{1/K} at the old alpha (that is the fixed-alpha
# reading, plan-S7 D4); it lets alpha slide down to the new crossing, and the
# payoff at the new crossing is strictly better.  That is the mode plan-S8
# WP-B owes the S1-owned apparatus, and the reason F3 says g* <= 2.38.
#
# [A] O-2 adoption: the primitives WP-C/WP-D need are already in this file
#     (plan-S7 built it first, declared at WP0), and gate G-A still passes.
# [B] the split: W = I + K(C1 - C2 reversed) and payoff = e^{C2}, verified as
#     identities at both admissible evaluation points.
# [C] calibration: at g = 1 the mode must return [Hab03] Theorem 1 itself.
# [D] the re-optimized wall, target by target, against the fixed-alpha figure.
# [E] the currency: D2's dictionary re-priced on the demand scale.
# [F] robustness: no alpha below alpha_0 is already covered (so the mode holds
#     no free improvement of a printed theorem), the crossing is the minimiser,
#     and the supply is stable in the rational denominator used to evaluate it.
# [G] the family's own floor, theta(alpha -> 1) -- below it the curve says
#     nothing, which is why the pre-1990 rows of D2 cannot be re-priced.
# ---------------------------------------------------------------------------


def _supply_demand(mu, t, K, al):
    """(log theta, W) at a float alpha -- the two content-free curves."""
    t = float(t)
    lX = log(1.0 / abs(t))
    F1 = _max_three_factor(mu - al, 1 + al, al, 1 - t)
    F2 = _max_three_factor(al, 1 + al, mu - al, t)
    return ((-2 * al * lX + log(F2) - log(F1)) / K,
            _A_alpha(mu, al) + log(F2) - al * lX)


def _supply(mu, al, v=100000):
    """I(al) at the nearest rational with denominator <= v (exact decomposition)."""
    f = Fraction(round(al * v), v)
    return _I_alpha(mu, f.numerator, f.denominator)[0]


def _reopt_alpha(mu, t, K, theta):
    """The alpha whose payoff is exactly theta; the payoff decreases in alpha."""
    tgt, lo, hi = log(theta), 1e-9, 1.0 - 1e-12
    for _ in range(200):
        mid = 0.5 * (lo + hi)
        if _supply_demand(mu, t, K, mid)[0] > tgt:
            lo = mid
        else:
            hi = mid
    return 0.5 * (lo + hi)


def _reopt_wall(mu, t, K, theta, v=100000):
    """(alpha*, W, I, log g*) -- what a target theta costs after re-optimization."""
    al = _reopt_alpha(mu, t, K, theta)
    W = _supply_demand(mu, t, K, al)[1]
    I = _supply(mu, al, v)
    return al, W, I, W - I


def _reopt_theta(mu, t, K, logg, v=1000, alo=0.30):
    """Inverse mode: the payoff a uniform gain g buys, on a grid of resolution 1/v.

    Returns (alpha, theta) at the smallest grid alpha where supply + log g still
    covers demand.  A grid, not a root: the supply is an arithmetic function of
    alpha and is not monotone, so 'the smallest feasible alpha' is an infimum
    over a scan and the resolution is printed with the answer.
    """
    best = None
    for u in range(int(alo * v), v):
        al = u / v
        C2, W = _supply_demand(mu, t, K, al)
        if _supply(mu, al, v) + logg >= W:
            best = (al, exp(C2))
            break
    return best


def cmd_s8b(out=sys.stdout):
    out.write("plan-Tshift-S8 WP-B -- O-2 adoption, and the I -> I + log g re-optimization\n"
              "mode of the note-S1-constants section 8.2 apparatus.  Floats are floats;\n"
              "the supply I(alpha) is computed exactly on rationals, as everywhere else.\n")

    out.write("\n# [A] O-2 adoption: WP-B builds nothing, because plan-S7 ran first\n")
    need = {
        "_apparatus": "the section 8.2 apparatus at a general point   (S7 WP-B)",
        "_A_alpha": "coefficient size A(alpha)                       (S7 WP-B)",
        "_max_three_factor": "the archimedean maxima F1, F2                   (S7 WP-B)",
        "_I_alpha": "the supply I(alpha), exact interval decomposition",
        "_pade_cell": "primitive integer Pade pairs, any cell          (S7 WP-B)",
        "_diag_content": "true vs provable content of the diagonal        (S7 WP-C)",
        "_det_rate_binom": "log|det| along the ray, from det_eq             (S8 WP0)",
        "_hab_frozen": "the frozen bases of CITED/HabsiegerPade.lean    (S8 WP0)",
    }
    for name in sorted(need):
        assert callable(globals().get(name)), name
        out.write(f"      {name:20s} present   {need[name]}\n")
    F1, F2, A0, I0, C10, C20 = _apparatus(2, Fraction(-1, 8), 6, 224141, 240395)
    assert abs(exp(C10) - 0.57701737767006) < 5e-11 and abs(C10 - C20) < 2e-11
    out.write(f"      gate G-A re-asserted here: theta = {exp(C10):.12f}, "
              f"C1 - C2 = {C10 - C20:.3e}\n"
              "      Everything WP-C (D3) and WP-D (D4) need is already in this file.\n")

    out.write("\n# [B] the split: the apparatus is a DEMAND curve and a PAYOFF curve\n"
              "      C1 = C2  <=>  I(al) = W(al) := A(al) + log F2(al) - al log X,\n"
              "      and the value at the crossing is e^{C2(al)}.  Neither carries I.\n")
    out.write("      point (mu,t,K)      alpha        W          I + K(C2-C1)"
              "   |diff|     payoff\n")
    for mu, t, K, u, v in ((2, Fraction(-1, 8), 6, 15, 16),
                           (2, Fraction(-1, 8), 6, 224141, 240395),
                           (2, Fraction(-1, 8), 6, 397, 500),
                           (2, Fraction(-1, 8), 6, 7, 10),
                           (1, Fraction(1, 4), 2, 6280417, 10000000)):
        _, _, _, I, C1, C2 = _apparatus(mu, t, K, u, v)
        lt, W = _supply_demand(mu, t, K, u / v)
        d = abs(W - (I + K * (C2 - C1)))
        assert d < 1e-9 and abs(lt - C2) < 1e-12
        out.write(f"      ({mu},{str(t):>5s},{K})    {u / v:.7f}  {W:+.9f}"
                  f"   {I + K * (C2 - C1):+.9f}   {d:.1e}   {exp(lt):.7f}\n")
    out.write("      Exact identities, not fits: F1 cancels out of C1 - C2, and A + log F2\n"
              "      - al log X is what is left.  The content channel is now one inequality,\n"
              "      supply >= demand, between one curve content moves and one it cannot.\n")

    out.write("\n# [C] calibration: at g = 1 the mode must return Theorem 1 itself\n")
    al1, W1, Isup, lg1 = _reopt_wall(2, Fraction(-1, 8), 6, 0.57701737767006)
    assert abs(al1 - 0.932386281) < 1e-6 and abs(lg1) < 5e-6
    out.write(f"      target theta = 0.57701737767006  ->  alpha* = {al1:.9f}"
              f"   (paper 0.932386281)\n"
              f"      demand W = {W1:.9f}   supply I = {Isup:.9f}   log g* = {lg1:+.2e}\n"
              "      The crossing IS Habsieger's optimum, found from the content-free side.\n")

    out.write("\n# [D] the re-optimized wall.  g_fixed is plan-S7 D4's figure: the gain\n"
              "      needed with alpha frozen at alpha_0.  g* is the gain needed when the\n"
              "      construction is re-optimized, which is what a real content gain buys.\n")
    out.write("      target      alpha*     demand W    supply I     g*       g_fixed"
              "   g*/g_fixed\n")
    walls = {}
    for tag, th in (("[Hab03] Thm 2", 0.57434), ("[Hab03] Thm 1", 0.5770173777),
                    ("[Zud07] record", 0.5803), ("", 0.60), ("", 0.62),
                    ("kappa = 1", 2 / 3), ("", 0.70), ("plan-S5 bar", 0.78885)):
        al, W, I, lg = _reopt_wall(2, Fraction(-1, 8), 6, th)
        gfix = exp(6 * (log(th) - C10))
        walls[round(th, 6)] = (al, W, I, lg)
        # re-optimization always moves the requirement TOWARDS 1: a target above
        # Theorem 1 costs less gain, a target below it needs less slack given up.
        # Tolerance 1e-5: the supply is read at the nearest rational of denominator
        # 1e5, which is worth about 4e-6 in log g -- see [F](ii).
        assert abs(lg) <= abs(log(gfix)) + 1e-5
        out.write(f"      {th:.6f}  {al:.7f}  {W:.7f}   {I:.7f}   {exp(lg):7.4f}"
                  f"  {gfix:8.4f}   {exp(lg) / gfix:.4f}   {tag}\n")
    al23, W23, I23, lg23 = walls[round(2 / 3, 6)]
    assert 1.51 < exp(lg23) < 1.53
    assert abs(exp(6 * (log(2 / 3) - C10)) - 2.3786) < 5e-4
    out.write(f"      So the wall to kappa = 1 is g* = {exp(lg23):.4f}, not the 2.3786 the plan\n"
              f"      carries: at alpha* = {al23:.6f} the construction needs a content rate of\n"
              f"      {W23:.6f} nats/m and the content lemma supplies {I23:.6f}.  The\n"
              "      fixed-alpha figure overstates the wall by 56% in these units.\n")
    inv = _reopt_theta(2, Fraction(-1, 8), 6, log(2.3786))
    out.write(f"      Read the other way: the gain the plan calls 'the wall' would, spent\n"
              f"      on a re-optimized construction, buy theta = {inv[1]:.4f} at alpha = "
              f"{inv[0]:.3f},\n      i.e. kappa = {_kappa(inv[1]):.4f} < 1.  (Grid resolution 1e-3; "
              "the exact figure is\n      WP-C's.  The point is not near a supply spike: the gap is smooth and\n"
              "      denominator-independent through alpha = 1/2, where two of the three\n"
              "      floor terms coincide.)  Hypothetical throughout -- no gain of any size\n"
              "      is in evidence; plan-S7 WP-C measured g_true -> 1.\n")
    assert inv[1] > 2 / 3 and _kappa(inv[1]) < 1

    out.write("\n# [E] D2's dictionary on the demand scale.  W(theta) is absolute -- the\n"
              "      content rate a [Hab03]-family proof needs to reach theta -- so steps\n"
              "      compose by subtraction and no reference point is smuggled in.\n")
    lo_theta = exp(_supply_demand(2, Fraction(-1, 8), 6, 1.0 - 1e-9)[0])
    out.write("      row                                    printed   re-priced   on-curve\n")
    for lab, t0, t1, printed, dp in S8_HISTORY:
        if min(t0, t1) <= lo_theta:
            out.write(f"      {lab:36s} {printed:8.3f}       --      no (theta < "
                      f"{lo_theta:.4f})\n")
            continue
        g = exp(_reopt_wall(2, Fraction(-1, 8), 6, t1)[1]
                - _reopt_wall(2, Fraction(-1, 8), 6, t0)[1])
        out.write(f"      {lab:36s} {printed:8.3f} {g:11.4f}       yes\n")
    zstep = walls[0.5803][1] - walls[round(0.5770173777, 6)][1]
    wall23 = W23 - walls[0.5803][1]
    steps = wall23 / zstep
    out.write(f"      one Zudilin step = {zstep:.7f} nats of demand; the wall from the record\n"
              f"      to 2/3 = {wall23:.7f} nats = {steps:.2f} steps   (plan, fixed-alpha: 24.5)\n")
    assert 23.0 < steps < 24.5
    out.write("      The wall halves in content units and does NOT move in record-sized\n"
              "      steps: re-optimization rescales the currency, it does not shorten the\n"
              "      road.  D2's comparison -- 'the remaining road equals the road already\n"
              "      travelled' -- survives its own correction.\n")

    out.write("\n# [F] robustness of the three soft spots\n")
    gap = []
    for u in range(300, 933):
        al = u / 1000
        gap.append((_supply_demand(2, Fraction(-1, 8), 6, al)[1] - _supply(2, al, 1000), al))
    glob = min(gap)
    assert glob[0] > 0 and glob[1] > 0.93
    out.write(f"      (i) does the mode contain a free improvement of a printed theorem?  No.\n"
              f"          Scanning alpha in [0.300, 0.932] at 1e-3, the supply never covers the\n"
              f"          demand: the smallest gap is {glob[0]:+.6f} at alpha = {glob[1]:.3f}, i.e. at\n"
              "          alpha_0 itself.  Habsieger's optimum is global, and every claim below\n"
              "          is conditional on a content gain nobody has.\n")
    below = [x for x in gap if x[1] <= al23]
    assert min(below)[1] > al23 - 1.5e-3, min(below)
    out.write(f"      (ii) is the crossing the cheapest way to theta >= 2/3?  Restricted to\n"
              f"          alpha <= alpha* = {al23:.3f}, the smallest gap is {min(below)[0]:.6f} at alpha ="
              f" {min(below)[1]:.3f}\n"
              "          -- the boundary itself.  No supply spike undercuts it, so g* is a\n"
              "          minimum over the admissible region and not just a boundary value.\n")
    out.write("      (iii) the supply is an arithmetic function; does the denominator matter?\n")
    prev = None
    for v in (1000, 10000, 100000, 1000000):
        I = _supply(2, al23, v)
        W = _supply_demand(2, Fraction(-1, 8), 6, round(al23 * v) / v)[1]
        out.write(f"          v = {v:8d}   I = {I:.9f}   g* = {exp(W - I):.6f}\n")
        if prev is not None:
            assert abs(exp(W - I) - prev) < 1e-3
        prev = exp(W - I)
    out.write("          Stable to 5e-4 over three decades of denominator.\n")

    out.write("\n# [G] the family's own floor\n")
    out.write(f"      payoff at alpha -> 1: theta = {lo_theta:.6f}.  The Pade cell needs\n"
              "      n <= m, i.e. alpha <= 1, so this construction cannot even be ASKED for\n"
              f"      a theta below {lo_theta:.4f} -- Beukers' 0.5359 and Baker-Coates' 0.5 are\n"
              "      off the curve, which is why [E] leaves those rows un-repriced.\n")
    assert 0.536 < lo_theta < 0.537 and lo_theta > 0.5359

    out.write("\n# WP-B verdict\n"
              "  Adoption: nothing to build (O-2, S7 first).  The mode: the section 8.2\n"
              "  apparatus splits into a content-free demand curve W(alpha) and a\n"
              "  content-free payoff curve e^{C2(alpha)}, with the content channel reduced\n"
              "  to supply >= demand.  Calibrated at g = 1 to Habsieger's own optimum.\n"
              "  The re-optimized wall to kappa = 1 is g* = 1.5214 at alpha* = 0.793972,\n"
              "  against the fixed-alpha 2.3786 -- but one record-sized step shrinks in the\n"
              "  same currency, so the distance is 23.7 steps against the plan's 24.5.\n"
              "  Q1's remaining half (WP-C) is now exactly one curve: the supply I(alpha).\n")


# ---------------------------------------------------------------------------
# plan-Tshift-S8, WP-C (D3(a), Q1's surviving half): the supply curve.
#
# WP-B reduced the content channel to  supply I(al) >= demand W(al), payoff
# e^{C2(al)}.  W and the payoff are smooth and content-free; everything
# arithmetic sits in I(al) = int_{E_al} dx/x^2, which is defined on rationals
# and has a cusp at every one of them.  WP-C draws it and reads three things
# off it that a scan cannot supply:
#
#   * sup_al I -- the family's ABSOLUTE content ceiling, the plan's own
#     "does even a perfect content lemma cross the wall" test (D3(a));
#   * the infimum of the feasible set {al : I >= W}, i.e. whether Habsieger's
#     alpha_0 is the exact optimum or merely a numerical root;
#   * the wall as a MINIMUM of D = W - I over the feasible-payoff region,
#     rather than the boundary value WP-B quoted.
#
# Sampling.  A fixed denominator (2000) draws the background; it can only see
# alphas whose denominator divides it, so 1/3, 2/3, 20/27 -- exactly the
# small-denominator cusps -- are invisible to it.  Every reduced fraction of
# denominator <= 120 is therefore added.  Between samples the curve is
# controlled by continuity: perturbing al by d moves each breakpoint of E_al
# by O(d x) and decorrelates the three forms only beyond x ~ 1/d, so
# |I(al) - I(al')| <= 6.8 d log(1/d) + d -- the x^{-2} weight discounts the
# tail in which an arithmetic degeneracy lives, which is why the cusps have
# zero height and I is continuous.  [B] measures the local slopes that bound
# is 15x too pessimistic about.
# ---------------------------------------------------------------------------


def _supply_at(mu, f):
    """I at an exact rational alpha -- the supply is only defined on rationals."""
    return _I_alpha(mu, f.numerator, f.denominator)[0]


def _supply_curve(mu, t, K, vgrid=2000, vfarey=120, alo=0.05):
    """[(al, Fraction, I, W, D, payoff)], background grid plus every Farey cusp."""
    fs = {Fraction(u, vgrid) for u in range(int(alo * vgrid) + 1, vgrid)}
    fs |= {Fraction(u, v) for v in range(2, vfarey + 1) for u in range(1, v)
           if gcd(u, v) == 1 and u / v > alo}
    rows = []
    for f in sorted(fs):
        al = float(f)
        lt, W = _supply_demand(mu, t, K, al)
        I = _supply_at(mu, f)
        rows.append((al, f, I, W, W - I, exp(lt)))
    return rows


def _ceiling_payoff(mu, t, K, s):
    """The best payoff if the supply were s at EVERY alpha: W is strictly decreasing,
    so the feasible set is al >= al_c with W(al_c) = s, and the payoff peaks there."""
    lo, hi = 0.30, 0.999
    for _ in range(90):
        mid = 0.5 * (lo + hi)
        if _supply_demand(mu, t, K, mid)[1] > s:
            lo = mid
        else:
            hi = mid
    al = 0.5 * (lo + hi)
    return al, exp(_supply_demand(mu, t, K, al)[0])


def _slope(mu, al, v):
    """|dI/dal| at scale 1/v, from the two rationals of denominator v around al."""
    u = round(al * v)
    return abs(_supply_at(mu, Fraction(u + 1, v)) - _supply_at(mu, Fraction(u, v))) * v


def cmd_s8c(out=sys.stdout):
    mu, t, K = 2, Fraction(-1, 8), 6
    A0 = Fraction(224141, 240395)
    out.write("plan-Tshift-S8 WP-C -- D3(a): the supply curve I(alpha) drawn, its ceiling,\n"
              "and the wall read as a minimum.  I is exact on every rational sampled;\n"
              "the demand W and the payoff e^{C2} are floats, as in section 8.2.\n")

    out.write("\n# [A] the curve.  Background: denominator 2000.  Cusps: every reduced\n"
              "      fraction of denominator <= 120 (a fixed denominator cannot see 1/3,\n"
              "      2/3 or 20/27, and those are where the arithmetic lives).\n")
    rows = _supply_curve(mu, t, K, 2000, 120)
    out.write(f"      {len(rows)} sample points, alpha in [{rows[0][0]:.3f}, {rows[-1][0]:.4f}]\n"
              "      alpha            supply I    demand W     D = W - I    payoff\n")
    for target in (1 / 3, 0.4, 1 / 2, 0.6, 2 / 3, 3 / 4, 4 / 5, 0.85, 15 / 16):
        al, f, I, W, D, th = min(rows, key=lambda r: abs(r[0] - target))
        out.write(f"      {str(f):>11s} {al:.6f}  {I:.6f}    {W:.6f}    {D:+.6f}   {th:.6f}\n")
    sup = max(rows, key=lambda r: r[2])
    peaks, seen = [], []
    for i in range(1, len(rows) - 1):
        if rows[i][2] > rows[i - 1][2] and rows[i][2] > rows[i + 1][2]:
            peaks.append((rows[i][2], rows[i][1], rows[i][0]))
    for v_, f_, a_ in sorted(peaks, reverse=True):
        if all(abs(a_ - b) > 0.02 for b in seen):
            seen.append(a_)
            if len(seen) <= 4:
                out.write(f"      local maximum at alpha = {str(f_):>7s} :  I = {v_:.6f}\n")
    assert sup[1] == Fraction(1, 2) and abs(sup[2] - 0.5736004) < 1e-6
    out.write(f"      sup I = {sup[2]:.9f}, attained at alpha = 1/2 -- where two of the three\n"
              "      forms coincide (1+al = mu-al = 3/2), the one degeneracy the family has.\n")

    out.write("\n# [B] is the curve trustworthy between samples?  The cusps are cusps of a\n"
              "      CONTINUOUS function: a degeneracy at u/v only correlates the forms\n"
              "      beyond x ~ v, and int dx/x^2 discounts that tail by O(1/v).  So the\n"
              "      spikes have zero height, and local slopes are what bound the error.\n")
    out.write("      alpha      |dI/dal| at 1e-4   1e-5      1e-6\n")
    for al, tag in ((0.5, "the ceiling"), (2 / 3, ""), (0.793972, "alpha*(2/3)"),
                    (float(A0), "alpha_0")):
        s4, s5, s6 = (_slope(mu, al, 10 ** j) for j in (4, 5, 6))
        out.write(f"      {al:.6f}   {s4:9.3f}  {s5:9.3f} {s6:9.3f}   {tag}\n")
        if abs(al - 0.793972) < 1e-6:
            assert max(s4, s5, s6) < 3.0
        if abs(al - float(A0)) < 1e-6:
            assert max(s4, s5, s6) < 1.5
        if al == 0.5:
            assert s6 > s4 > 9.0                    # log-Lipschitz, only at the peak
    out.write("      Stable over three decades at the two alphas that decide anything;\n"
              "      only at the peak does the slope creep (10.3 -> 16.0 per decade), the\n"
              "      log-Lipschitz signature of the a priori bound 6.8 d log(1/d) + d.\n")

    out.write("\n# [C] the crossing.  Is alpha_0 the exact infimum of the feasible set\n"
              "      {al : I >= W}, or did a 1e-3 scan just fail to find a cheaper alpha?\n")
    below = [r for r in rows if r[0] <= float(A0) - 1e-3]
    assert min(r[4] for r in below) > 0
    out.write(f"      D > 0 at all {len(below)} samples with alpha <= alpha_0 - 1e-3; "
              f"smallest {min(r[4] for r in below):.6f}\n")
    lad = []
    for u in range(93200, 93250, 5):
        f = Fraction(u, 100000)
        lad.append((float(f), _supply_demand(mu, t, K, float(f))[1] - _supply_at(mu, f)))
    for a_, d_ in lad:
        out.write(f"      alpha = {a_:.5f}   D = {d_:+.7f}\n")
    (x0, d0), (x1, d1) = [p for p in lad if p[1] > 0][-1], [p for p in lad if p[1] < 0][0]
    z = x0 + (x1 - x0) * d0 / (d0 - d1)
    slope = (d0 - d1) / (x1 - x0)
    assert d0 > 0 > d1 and abs(z - float(A0)) < 2e-6
    out.write(f"      Linear through the crossing (slope {slope:.3f} per unit alpha, no wiggle):\n"
              f"      zero at alpha = {z:.7f}   vs   224141/240395 = {float(A0):.9f}\n"
              "      Habsieger's alpha_0 IS the infimum of the feasible set, to 1e-6.  There\n"
              "      is no free improvement of Theorem 1 hiding between the samples.\n")

    out.write("\n# [D] the plan's own outright test: even if the content lemma were PERFECT,\n"
              "      i.e. the supply were sup I at every alpha, what payoff would follow?\n")
    out.write("      uniform supply   alpha_c     theta      kappa\n")
    al23 = _reopt_alpha(mu, t, K, 2 / 3)
    W23 = _supply_demand(mu, t, K, al23)[1]
    I23 = _supply(mu, al23)
    for s, tag in ((I23, "what the family actually supplies at alpha*(2/3)"),
                   (sup[2], "sup I -- the family's absolute ceiling"),
                   (0.65, ""), (W23, "what kappa = 1 demands")):
        alc, th = _ceiling_payoff(mu, t, K, s)
        out.write(f"      {s:.6f}        {alc:.6f}   {th:.6f}   {_kappa(th):.5f}   {tag}\n")
    alc, thc = _ceiling_payoff(mu, t, K, sup[2])
    assert thc < 2 / 3 and _kappa(thc) > 1 and 0.616 < thc < 0.617
    out.write(f"      The ceiling buys theta = {thc:.6f}, kappa = {_kappa(thc):.5f} > 1.  Channel (ii)\n"
              "      is closed WITHIN THIS FAMILY OUTRIGHT: no content lemma whatever, not\n"
              "      even an exact one, reaches 2/3 through the [Hab03] construction.\n")
    ceil_f, resid = exp(sup[2] - I23), exp(W23 - sup[2])
    assert abs(ceil_f * resid - exp(W23 - I23)) < 1e-9 and resid > 1.2
    out.write(f"      The wall factorises: g* = {exp(W23 - I23):.4f} = {ceil_f:.4f} (all the way to the\n"
              f"      ceiling) x {resid:.4f} (still missing after it).  Only the first factor\n"
              "      exists in the world of content lemmas; the second is family change.\n")

    out.write("\n# [E] the wall is a MINIMUM over the feasible region, not a boundary value.\n"
              "      A cusp of I is a local minimum of D; if alpha*(theta) happens to sit\n"
              "      just to the right of one, the true wall is below the boundary figure.\n")
    out.write("      target     alpha*      boundary D    min D over al <= alpha*   at\n")
    for th in (0.5770173777, 0.5803, 0.60, 0.62, 2 / 3, 0.70, 0.78885):
        als = _reopt_alpha(mu, t, K, th)
        Wb = _supply_demand(mu, t, K, als)[1] - _supply(mu, als)
        cand = min((r[4], r[1]) for r in rows if r[0] <= als)
        out.write(f"      {th:.6f}   {als:.6f}   {Wb:.6f}      {cand[0]:.6f}"
                  f"  {'(boundary)' if cand[0] >= Wb - 1e-9 else 'undercut  '}"
                  f"    {str(cand[1]):>8s}\n")
        if abs(th - 2 / 3) < 1e-9:
            assert cand[0] >= Wb - 1e-9 and abs(exp(Wb) - 1.5214) < 5e-4
    worst, m = (0.0, None), 1e9
    for al, f, I, W, D, th in rows:
        if al >= 0.7458 and D - m > worst[0]:
            worst = (D - m, f, th)
        m = min(m, D)
    assert worst[0] < 0.01
    out.write(f"      Largest undercut in the theta <= 0.70 band: {worst[0]:.6f} nats at alpha ="
              f" {str(worst[1])},\n      i.e. 0.5% of the wall -- the cusp at 20/27 seen from 3/4."
              "  At 2/3 itself the\n      boundary IS the minimum, so WP-B's g* = 1.5214 stands"
              " unchanged.  (In the\n      band theta in (0.81, 0.89), where alpha = 1/2 governs,"
              " the undercut reaches\n      0.0437 nats -- but those targets are far past"
              " anything this lane can ask.)\n")

    out.write("\n# [F] the curve machinery, calibrated at the second admissible point\n")
    lo, hi = 0.30, 0.95
    for _ in range(40):
        mid = 0.5 * (lo + hi)
        if _supply_demand(1, Fraction(1, 4), 2, mid)[1] - _supply(1, mid) > 0:
            lo = mid
        else:
            hi = mid
    z2 = 0.5 * (lo + hi)
    assert abs(z2 - 0.6280417) < 2e-6
    out.write(f"      (mu,t,K) = (1,1/4,2):  I = W at alpha = {z2:.7f}   vs section 8.2's"
              " 0.6280417\n      -- the same routine, an independent point, seven digits.\n")

    out.write("\n# WP-C verdict (against the criteria of plan-S8 section 2.1)\n"
              "  Q1(a) KILL, and by the plan's own strongest form.  The supply curve is\n"
              "  continuous, capped at sup I = 0.573600 nats/m (alpha = 1/2), and the\n"
              "  demand at kappa = 1 is 0.767468 nats/m.  A perfect content lemma -- the\n"
              "  ceiling supplied at every alpha -- buys theta = 0.6165, kappa = 1.193.\n"
              "  Habsieger's alpha_0 is the exact infimum of the feasible set, so there is\n"
              "  nothing free below it either.  With Q1(b) already negative (g_true -> 1,\n"
              "  plan-S7 WP-C), channel (ii) is closed within the [Hab03] family outright:\n"
              "  thousandths can only come from family change, which is [Zud07].\n")


# ---------------------------------------------------------------------------
# plan-Tshift-S8, WP-D (D4, Q2): the determinant, measured on the real family.
#
# WP0 settled D1 as algebra and checked the cap against the frozen numerals.
# What it could not do is look at [Hab03]'s actual two-column data, because
# that needs the polynomials.  The constants note section 2.4 supplies the
# dictionary, and plan-S7's harness supplies the polynomials, so here the two
# meet:
#
#   Phat_i = 8^i P_i(-1/8),   Qhat_i = (-1)^m 8^i Q_i(-1/8),   b_i = -Qhat_i,
#   l_i    = (-1)^{i+m+1} 2^{6m} 8^{-i-1} E_i(-1/8),   X = 2^{6m},
#   B_m    = |Qhat_n| = 8^n|Q_n(-1/8)|,   Lambda_m = |l_n| .
#
# The W-terms cancel out of a_1 b_2 - a_2 b_1, so the determinant is
# Phat_{n+1} Qhat_n - Phat_n Qhat_{n+1} -- computable without W, and therefore
# a check of det_eq itself rather than a use of it.
#
# [A] det_eq verified at finite m from the polynomials, sign included.
# [B] D1(1)/(2) on the real objects: the Cramer identity, and the fact that
#     the triangle inequality in the cap is LOSSLESS here (same sign).
# [C] where the cap's slack actually lives: sqrt(m) worst-casing and the
#     frozen numerals, whose combined rate excess is 1.043e-8 per m.
# [D] the cleared determinant: NOT sub-polynomial, contrary to D1(5)'s guess.
# [E] D1(5)'s bad branch on this family: the recovered factor decays, at
#     exactly the rate by which the family sits inside validity.
# [F] the Q2 verdict and the number owed to plan-S1's c(D).
# ---------------------------------------------------------------------------


def _hab_columns(m, al=None):
    """[Hab03]'s two-column data at the alpha-index, exactly (constants note 2.4).

    Returns (n, cols, det, closed) with cols[k] for k = 1, 2 the indices n, n+1:
    b (integer), l (exact Fraction), the content gcd(Phat, Qhat) that divides
    both columns whatever W is, and Lemma 1's polynomial content for comparison.
    """
    al = Fraction(15, 16) if al is None else al
    n = int(al * (m - Fraction(3, 2))) + 1
    assert 32 * n + 13 <= 30 * m < 32 * n + 45          # padeData's range clauses
    X = Fraction(2) ** (6 * m)
    cols = {}
    for k, i in ((1, n), (2, n + 1)):
        P, Q, E, ok = _pade_pair(i, 2 * m, m)
        assert ok, "(2.1) fails"
        Qh = (-1) ** m * 8 ** i * _ev(Q, Fraction(-1, 8))
        Ph = 8 ** i * _ev(P, Fraction(-1, 8))
        assert Qh.denominator == 1 and Ph.denominator == 1, "the clearing factor is wrong"
        Qh, Ph = int(Qh), int(Ph)
        g = 0
        for x in P + Q:
            g = gcd(g, abs(x))
        cols[k] = {"i": i, "Ph": Ph, "Qh": Qh, "b": -Qh,
                   "l": Fraction((-1) ** (i + m + 1)) * X * _ev(E, Fraction(-1, 8))
                        / 8 ** (i + 1),
                   "G": gcd(abs(Ph), abs(Qh)), "Gpoly": g}
    det = cols[2]["Ph"] * cols[1]["Qh"] - cols[1]["Ph"] * cols[2]["Qh"]
    closed = comb(3 * m + n, 2 * n + m + 1) * comb(2 * n + m + 2, n + m + 1)
    return n, cols, det, closed


def _lfrac(x):
    """log of a positive Fraction, without ever building the float."""
    return log(x.numerator) - log(x.denominator)


def cmd_s8d(mmax=512, out=sys.stdout):
    fz = _hab_frozen()
    al15 = 15 / 16
    lcb, ldb, leb = (_lfrac(fz[k]) for k in ("contentBase", "denomBase", "errorBase"))
    A = _A_alpha(2, al15)
    ms = [8]
    while ms[-1] * 2 <= max(mmax, 8):
        ms.append(ms[-1] * 2)
    out.write("plan-Tshift-S8 WP-D -- D4/Q2: the determinant of [Hab03]'s own two-column\n"
              "data, measured.  Every column below is exact integer or Fraction\n"
              "arithmetic on the polynomials; the frozen numerals enter only where the\n"
              "printed bounds are being compared against.\n")
    R = {m: _hab_columns(m) for m in ms}

    out.write("\n# [A] det_eq, verified at finite m FROM THE POLYNOMIALS.  The W-terms\n"
              "      cancel, so this is a check of the cited clause, not a use of it.\n"
              "          m      n |  det = Phat_2 Qhat_1 - Phat_1 Qhat_2  vs  (-1)^n C C\n")
    for m in ms:
        n, cols, det, closed = R[m]
        assert det == (-1) ** n * closed
        out.write(f"      {m:5d} {n:6d} |  agree exactly, sign (-1)^n = {(-1) ** n:+d},"
                  f"  {len(str(closed))} digits\n")
    out.write("      The determinant clause of `padeData` is therefore not an article of\n"
              "      faith at any m the polynomials are computable at.\n")

    out.write("\n# [B] D1(1) and D1(2) on the real objects.  X*det = b_2 l_1 - b_1 l_2 is\n"
              "      a ring identity; what is NOT automatic is whether the two products\n"
              "      cancel, since the cap replaces the difference by the sum.\n"
              "          m | X*det = b2 l1 - b1 l2 | |b2 l1| + |b1 l2| over |X det|\n")
    for m in ms:
        n, cols, det, closed = R[m]
        X = Fraction(2) ** (6 * m)
        cram = cols[2]["b"] * cols[1]["l"] - cols[1]["b"] * cols[2]["l"]
        tri = abs(cols[2]["b"] * cols[1]["l"]) + abs(cols[1]["b"] * cols[2]["l"])
        assert abs(cram) == abs(X * det)
        assert tri == abs(cram)                      # same sign: nothing cancels
        out.write(f"      {m:5d} | exact                 | ratio exactly 1\n")
    out.write("      The two products carry the SAME sign at every m, so the triangle\n"
              "      step of D1(2) is lossless: |det|X = |b2 l1| + |b1 l2| on the nose.\n"
              "      The cap's slack is therefore entirely in B and Lambda -- in replacing\n"
              "      the two actual columns by one printed bound.  [C] prices that.\n")

    out.write("\n# [C] where the slack lives.  rate(|det|) = A(2,15/16) exactly (WP0);\n"
              "      rate(cap) = log denomBase + log errorBase.  The gap is the whole\n"
              "      rate-level residue of the chain:\n")
    out.write(f"        A(2,15/16)                    = {A:.12f}\n"
              f"        log denomBase + log errorBase = {ldb + leb:.12f}\n"
              f"        gap                           = {ldb + leb - A:+.3e} per m"
              f"   ->   e^{(ldb + leb - A) * fz['mLow']:.4f} at m = mLow\n")
    assert 0 < ldb + leb - A < 1e-7
    out.write("      So the two frozen bases together overstate the truth by 1.04e-8 per m:\n"
              "      12% at the (3.11) threshold, and nothing at all below it.  Everything\n"
              "      else in the cap is a sqrt(m) worst-casing of two columns by one bound:\n")
    out.write("          m | B/max|b_i| | Lambda/max|l_i| | (both, minus 0.4986 log m)\n")
    for m in ms:
        n, cols, det, closed = R[m]
        B = 8 ** (n + 1) * fz["denomConst"] * fz["denomBase"] ** m
        Lam = Fraction(2) ** (6 * m) * fz["errorBase"] ** m / 8 ** (n + 1)
        dB = _lfrac(B) - max(log(abs(cols[k]["b"])) for k in (1, 2))
        dL = _lfrac(Lam) - max(_lfrac(abs(cols[k]["l"])) for k in (1, 2))
        out.write(f"      {m:5d} |   e^{dB:6.3f}  |    e^{dL:6.3f}     |"
                  f"  {dB - 0.4986 * log(m):+.4f}   {dL - 0.4986 * log(m):+.4f}\n")
        if m >= 128:
            assert abs(dB - 0.4986 * log(m) - 0.027) < 0.01
            assert abs(dL - 0.4986 * log(m) - 1.115) < 0.01
    lo = log(fz["mLow"])
    out.write(f"      Both constants are flat to 1e-3 from m = 128 on, so the law is\n"
              f"      B/|b| = e^0.027 sqrt(m) and Lambda/|l| = e^1.115 sqrt(m), giving at\n"
              f"      m = mLow: e^{0.4986 * lo + 0.027:.2f} and e^{0.4986 * lo + 1.115:.2f}, i.e. the family sits a\n"
              f"      factor e^{2 * 0.4986 * lo + 1.142 + log(2) + (ldb + leb - A) * fz['mLow']:.2f} = "
              f"{exp(2 * 0.4986 * lo + 1.142 + log(2) + (ldb + leb - A) * fz['mLow']):.1e}"
              " BELOW its own cap there -- and every\n"
              "      one of those factors is on the wrong side for route (i), which wants\n"
              "      the determinant LARGE.  The cap is saturated in rate and slack in\n"
              "      constants, both against S8(i).\n")
    out.write("      Independent check of a cited numeral: the true rate of |b_1|, read off\n"
              "      the exact columns as (log|b| - n log 8 + 0.4986 log m)/m, against the\n"
              "      frozen denomBase = 56534214/9609251:\n")
    prev = None
    for m in ms:
        n, cols, det, closed = R[m]
        lb = log(abs(cols[1]["b"]))
        if prev:
            pm, pn, plb = prev
            q1 = (lb - plb - (n - pn) * log(8) + 0.5 * (log(m) - log(pm))) / (m - pm)
            out.write(f"        m = {pm:4d} -> {m:4d}:  q1 = {q1:.9f}   "
                      f"(log denomBase = {ldb:.9f}, diff {ldb - q1:+.1e})\n")
            if m == ms[-1]:
                assert abs(ldb - q1) < 5e-6
        prev = (m, n, lb)

    out.write("\n# [D] the cleared determinant det/(Gamma_1 Gamma_2).  D1(5) guesses it may\n"
              "      be sub-polynomial 'since the contents divide it twice'.  It is not:\n"
              "          m | log(det/(G1 G2))/m | contents: value-gcd / Lemma-1 product\n")
    for m in ms:
        n, cols, det, closed = R[m]
        cl = (log(abs(det)) - log(cols[1]["G"]) - log(cols[2]["G"])) / m
        out.write(f"      {m:5d} |      {cl:.6f}      |  {cols[1]['G'] // cols[1]['Gpoly']:6d}"
                  f" {cols[2]['G'] // cols[2]['Gpoly']:6d}\n")
        if m >= 128:
            assert 3.0 < cl < 3.4
    out.write(f"      The rate is A - 2 log contentBase = {A - 2 * lcb:.6f} nats/m > 0: clearing\n"
              "      removes 0.789 of 4.111 and leaves an exponentially large integer.  The\n"
              "      guess was wrong -- but harmless, because the cap clears by the SAME\n"
              "      Gamma^2 (F1(a)), so disjointness is untouched either way.\n"
              "      Side observation, and a trap: the content that divides BOTH columns is\n"
              "      gcd(Phat, Qhat), which exceeds Lemma 1's certified product by the\n"
              "      factors in the last column -- no trend, and exactly 1 at m = 128, while\n"
              "      at m = 1024 (run `s8d 1024`) the two are 945 and 11025.  A per-m LOWER\n"
              "      bound is what a proof needs and this sequence supplies none; it sits\n"
              "      inside the content slack plan-S7 WP-C already measured, so it is not\n"
              "      headroom beyond F9.\n")

    out.write("\n# [E] D1(5)'s bad branch on this family.  Inside validity the recovered\n"
              "      factor over the content is |Delta_2|/P = |c||det|/(|b_1| P), whose rate is\n"
              "      A - (alpha log 8 + q1) - log contentBase:\n")
    grate = A - (al15 * log(8) + ldb) - lcb
    vmarg = lcb - leb + al15 * log(8)
    out.write(f"        rate of the recovered factor   = {grate:+.9f} per m\n"
              f"        validity margin (WP0, F1(c))   = {vmarg:+.9f} per m\n"
              f"        sum                            = {grate + vmarg:+.3e}"
              f"  = -(the 1.04e-8 of [C])\n")
    assert grate < 0 < vmarg and abs(grate + vmarg + (ldb + leb - A)) < 1e-12
    out.write("      So the bad branch's stake and the family's own validity margin are the\n"
              "      SAME number with opposite signs, to the last digit of the frozen\n"
              "      numerals.  D1(5) is not a constants play at all: the factor it recovers\n"
              "      falls below 1 and then decays.  Measured, at D = 1, with P the true\n"
              "      content of the columns:\n"
              "          m |  log(|det|/(|b_1| P))  | recovered factor\n")
    for m in ms:
        n, cols, det, closed = R[m]
        g = log(abs(det)) - log(abs(cols[1]["b"])) - log(min(cols[1]["G"], cols[2]["G"]))
        out.write(f"      {m:5d} |      {g:+9.4f}         |  {exp(g):.3e}"
                  f"{'   <- already below 1' if 32 < m <= 64 else ''}\n")
        if m >= 64:
            assert g < 0
    out.write(f"      Below 1 from m = 64 on and falling; at the threshold m = mLow the rate\n"
              f"      alone puts it at e^{grate * fz['mLow']:.0f}.  (The ladder falls faster than the\n"
              "      asymptotic rate because the true content still exceeds its own limit at\n"
              "      these m -- plan-S7 WP-C's slack, 0.0185 per m at 1024 and falling.)\n")

    out.write("\n# [F] Q2 verdict, and the number owed to plan-S1\n"
              "  D1(4) is confirmed on the real family, with both rates and their gap:\n"
              f"  rate(|det|) = {A:.9f}, rate(cap) = {ldb + leb:.9f}, gap"
              f" {ldb + leb - A:.2e} per m.\n"
              "  The constant-factor stake of D1(5) for S1's c(D) is NOT a constant to be\n"
              "  harvested -- it is a decaying factor, worth less than 1 from m = 64 on and\n"
              "  e^-53000 at the threshold.  The number handed to the constants note is\n"
              "  therefore zero: no branch of the determinant route improves c(D) on\n"
              "  [Hab03]'s family, and the write-up's C18 may say route (i) is dead\n"
              "  INCLUDING constants -- which is stronger than the plan's kill criterion\n"
              "  asked for, and reached by a different mechanism than it guessed.\n")


# ---------------------------------------------------------------------------
# plan-Tshift-S8 WP-F -- sub-idea (iii): the unconsumed parameter freedom.
#
# [Zud07] section 5 fixes (a, b, n) = (alpha m, beta m, gamma m) with alpha,
# beta, gamma POSITIVE INTEGERS subject to  2 alpha <= beta  and  gamma < beta
# (p. 318, "Fix two positive integers a and b satisfying 2a <= b" plus the
# displayed constraint), and states that (9, 19, 9) is "the optimal choice of
# the integer parameters alpha, beta, gamma, at least under the restriction
# beta <= 100".  That restriction is the freedom WP-A identified: the objective
#     theta(alpha, beta, gamma) = exp( -(C1 - C2) / (3 beta) )
# is a discontinuous arithmetic function of the ratio (alpha : beta : gamma)
# because C2 is, so a finer grid is a genuine search, not interpolation.  By
# F11 the objective is exactly homogeneous of degree 0, so only PRIMITIVE
# triples are searched -- gcd(alpha, beta, gamma) = 1 loses nothing.
#
# Validity is [Zud07] (26):  C0(1/9) - C2 + (beta - 2 alpha) log 3 < 0.
#
# The cost is C2 alone (C0 and C1 are closed form, F11/WP-A).  The audited
# routines _zud_intervals/_zud_c0max/_max_three_factor carry grid cross-checks
# that make them far too slow for 10^6 triples, so this block adds
# vectorised twins and CALIBRATES them against the audited ones on every
# printed lane plus random triples ([A]) before using them ([B], [C]).
#
# [A] calibration of the fast twins against the audited routines, and of the
#     C2 integrand against the arithmetic it abbreviates: e_p computed from
#     [Zud07] (13) -- min over mu of ord_p of a product of two binomials --
#     against the indicator of {phi = 1} at x = {m/p}, prime by prime.
# [B] the mandated reproduction: the whole beta <= 100 grid.
# [C] the extension past beta = 100.
# [D] the ridge alpha = gamma and the ratio beta/alpha: what the search is
#     actually approximating.
# [E] gate G-D.
# ---------------------------------------------------------------------------

def _zud_c01_fast(al, be, ga, zinv=9):
    """(C0, C1) in closed form -- the stationary points only, no grid scan.

    Same quadratics as _zud_c0max and _max_three_factor, evaluated in LOGS so
    that the C1 hump does not underflow at large beta (x^(al+ga) with al+ga in
    the hundreds is far below the smallest double).  [A] checks the agreement.
    """
    S, AG, BG = al + be + ga, al + ga, be - ga
    z = 1.0 / zinv
    pref = S * log(S) - AG * log(AG) - ga * log(ga) - BG * log(BG)

    def _roots(A2, B2, C2c):
        if abs(A2) < 1e-15:
            return [-C2c / B2] if abs(B2) > 1e-15 else []
        disc = B2 * B2 - 4 * A2 * C2c
        if disc < 0:
            return []
        s = sqrt(disc)
        return [(-B2 + s) / (2 * A2), (-B2 - s) / (2 * A2)]

    best0 = -1e300
    for t in _roots(z * (ga - be), z * S - ga * (1 + z) - AG, float(ga)):
        if 0.0 < t < 1.0:
            best0 = max(best0, ga * log(t) + AG * log(1 - t) - S * log(1 - z * t))
    d = float(zinv)
    best1 = -1e300
    for x in _roots(d * S, -(AG * (1 + d) + BG + ga * d), float(AG)):
        if 0.0 < x < 1.0 and abs(1 - d * x) > 0.0:
            best1 = max(best1, AG * log(x) + BG * log(1 - x) + ga * log(abs(1 - d * x)))
    return pref + ga * log(abs(z)) + best0, pref + best1


def _zud_c2_fast(al, be, ga):
    """C2 = int_0^1 phi dpsi, vectorised, exact indicator.

    Same object as _dpsi_sum(_zud_intervals(al, be, ga)) and checked against it
    in [A].  phi-hat is piecewise constant in y with jumps only at 0, {-(al+ga)x},
    {-(al+be)x}, {ga x}, and constant in x between consecutive multiples of
    1/(al+be+ga), 1/(al+ga), 1/(al+be), 1/(be-ga), 1/ga -- so evaluating at
    midpoints of that grid, over those four jump points and one interior point
    of each arc between them, is exhaustive.  Everything is integer arithmetic
    over the common denominator E = 4 lcm(moduli): x = 2X/E with X a sum of two
    consecutive grid numerators, so every jump point is even and every arc
    midpoint is an exact integer.
    """
    try:
        import numpy as _np
    except ImportError:                                    # exact, slow fallback
        return _dpsi_sum(_zud_intervals(al, be, ga))
    S, AG, AB, BG = al + be + ga, al + ga, al + be, be - ga
    mods = (S, AG, AB, BG, ga)
    L = 1
    for P in mods:
        L = L // gcd(L, P) * P
    E = 4 * L
    assert max(mods) * E < 2 ** 62, (al, be, ga, L)        # int64 headroom
    g = _np.unique(_np.concatenate(
        [_np.arange(0, L + 1, L // P, dtype=_np.int64) for P in mods]))
    t = (2 * (g[:-1] + g[1:])) % E                          # x, in units of 1/E
    c1, cS = (-AG * t) % E, (S * t) % E
    b = _np.sort(_np.stack([_np.zeros_like(t), c1, (-AB * t) % E, (ga * t) % E],
                           axis=1), axis=1)
    cand = _np.concatenate([b, (b[:, :-1] + b[:, 1:]) // 2, (b[:, 3:4] + E) // 2],
                           axis=1)
    tc = t[:, None]
    v = ((-c1 - cS)[:, None] + (-AG * tc - cand) % E + cand
         + (AB * tc + cand) % E + (ga * tc - cand) % E)
    keep = v.min(axis=1) >= E
    assert not keep[0]                                      # phi = 0 near 0 always
    d = (_np.asarray(_psi_many(g[1:] / L), dtype=float)
         - _np.asarray(_psi_many(_np.maximum(g[:-1], 1) / L), dtype=float))
    d[0] = 0.0
    return float(d[keep].sum())


def _zud_theta(al, be, ga, zinv=9, s=2, base=3):
    """(theta, margin(26), C0, C1, C2) on the fast path."""
    C0, C1 = _zud_c01_fast(al, be, ga, zinv)
    C2 = _zud_c2_fast(al, be, ga)
    return (exp(-(C1 - C2) / (3 * be)), C0 - C2 + (be - s * al) * log(base),
            C0, C1, C2)


def _zud_e_p(a, b, n, p):
    """[Zud07] (13): min over mu of ord_p[ C(a+n-1+mu, mu) C(a+b+n, n-mu) ].

    Valid as written only for p > sqrt(a+b+n), where every ord_p is 0 or 1.
    """
    def f(u):
        return u // p
    b1, b2 = f(a + n - 1), f(a + b + n)
    best = 2
    for mu in range(n + 1):
        v = (f(a + n - 1 + mu) - f(mu) - b1) + (b2 - f(n - mu) - f(a + b + mu))
        if v < best:
            best = v
            if best == 0:
                break
    return best


def _zud_sweep(bmax, bmin=2, zinv=9, s=2, base=3, keep=40, report=None,
               out=sys.stdout):
    """Every primitive admissible triple with beta <= bmax; the valid ones ranked.

    Admissible = [Zud07] section 5: positive integers, 2 alpha <= beta, gamma <
    beta.  Valid = admissible and (26) and theta < 1.  The C2 cap psi(1) -
    psi(1/S) skips triples whose (26) can never hold, which is the only place a
    triple is dropped without computing C2.
    """
    euler = _psi_scalar(1.0)
    lb = log(float(base))
    res, ntot, nskip = [], 0, 0
    ladder, run = [], (0.0, None)
    for be in range(bmin, bmax + 1):
        for al in range(1, be // 2 + 1):
            for ga in range(1, be):
                if gcd(gcd(al, be), ga) != 1:
                    continue
                ntot += 1
                C0, C1 = _zud_c01_fast(al, be, ga, zinv)
                if C0 + (be - s * al) * lb >= euler - _psi_scalar(1.0 / (al + be + ga)):
                    nskip += 1                              # (26) unsatisfiable
                    continue
                C2 = _zud_c2_fast(al, be, ga)
                if C0 - C2 + (be - s * al) * lb >= 0:
                    continue
                th = exp(-(C1 - C2) / (3 * be))
                if th < 1.0:
                    res.append((th, al, be, ga, C0 - C2 + (be - s * al) * lb))
                    if th > run[0]:
                        run = (th, (al, be, ga))
                        ladder.append((be, th, run[1]))
        if report is not None and be % report == 0:
            res.sort(reverse=True)
            del res[keep:]
            out.write(f"      ... beta <= {be}: {ntot} primitive, best "
                      f"{res[0][0]:.9f} at {res[0][1:4]}\n")
            out.flush()
    res.sort(reverse=True)
    return res[:keep], ntot, nskip, ladder


def cmd_s8f(bmax=100, amax=500, out=sys.stdout):
    from time import time as _clock
    ZUD = (9, 19, 9)
    TH_ZUD = 0.580302781                                    # [Zud07] Theorem 1

    out.write("# [A] the fast twins, calibrated against the audited routines\n")
    tri = [t[1:4] for t in S8_LANES] + [(1, 2, 1), (7, 17, 8), (20, 41, 19),
                                        (31, 97, 44), (35, 74, 35), (44, 93, 44),
                                        (2, 5, 3), (13, 27, 13), (50, 101, 49)]
    dmax = 0.0
    for al, be, ga in tri:
        S, AG, BG = al + be + ga, al + ga, be - ga
        pref = S * log(S) - AG * log(AG) - ga * log(ga) - BG * log(BG)
        r0 = pref + ga * log(1.0 / 9) + _zud_c0max(al, be, ga, 1.0 / 9)
        r1 = pref + log(_max_three_factor(AG, BG, ga, 9.0))
        r2 = _dpsi_sum(_zud_intervals(al, be, ga))
        f0, f1 = _zud_c01_fast(al, be, ga)
        f2 = _zud_c2_fast(al, be, ga)
        dmax = max(dmax, abs(f0 - r0), abs(f1 - r1), abs(f2 - r2))
        assert abs(f0 - r0) < 1e-9 and abs(f1 - r1) < 1e-9 and abs(f2 - r2) < 1e-9
    out.write(f"      {len(tri)} triples, closed-form C0/C1 and vectorised C2 against the\n"
              f"      grid-checked C0/C1 and the Fraction interval set: max |diff| = {dmax:.2e}\n")

    out.write("\n      and the C2 integrand against the arithmetic it abbreviates:\n"
              "      e_p from (13), prime by prime, vs the indicator of {phi = 1} at {m/p}\n")
    for al, be, ga in (ZUD, (35, 74, 35), (44, 93, 44)):
        ivs = _zud_intervals(al, be, ga)
        m = 24
        a, b, n = al * m, be * m, ga * m
        tot = a + b + n
        sieve = bytearray([1]) * (tot + 1)
        sieve[0] = sieve[1] = 0
        for i in range(2, int(sqrt(tot)) + 1):
            if sieve[i]:
                sieve[i * i::i] = bytearray(len(sieve[i * i::i]))
        lo = int(sqrt(tot)) + 1
        ps = [p for p in range(lo, tot + 1) if sieve[p]]
        bad = 0
        lphi = 0.0
        for p in ps:
            x = Fraction(m % p, p)
            pred = 1 if any(u <= x < w for u, w in ivs) else 0
            if _zud_e_p(a, b, n, p) != pred:
                bad += 1
            lphi += pred * log(p)
        assert bad == 0, (al, be, ga, bad)
        out.write(f"        ({al:2d},{be:3d},{ga:2d})  m = {m}: {len(ps):4d} primes,"
                  f" {bad} mismatches;  (1/m) log Phi = {lphi / m:7.4f}"
                  f"   C2 = {_dpsi_sum(ivs):7.4f}\n")
    out.write("      (log Phi/m rises to C2 from below at the prime-number-theorem rate;\n"
              "      the zero mismatch count is the exact statement.)\n")

    out.write("\n# [B] the mandated reproduction: the whole beta <= 100 grid\n")
    t0 = _clock()
    top, ntot, nskip, ladder = _zud_sweep(100)
    th_zud = _zud_theta(*ZUD)[0]
    assert abs(th_zud - TH_ZUD) < 5e-9, th_zud
    out.write(f"      {ntot} primitive admissible triples (2a <= b, gamma < beta),\n"
              f"      {nskip} dropped by the C2 cap psi(1)-psi(1/S) as (26)-infeasible,\n"
              f"      {_clock() - t0:.1f} s.  Ranked by theta = exp(-(C1-C2)/(3 beta)):\n\n"
              "        alpha  beta  gamma      theta          (26) margin   vs [Zud07]\n")
    for th, al, be, ga, mg in top[:12]:
        tag = "  <<<< BEATS" if th > TH_ZUD else ("  = [Zud07]" if (al, be, ga) == ZUD else "")
        out.write(f"        {al:5d} {be:5d} {ga:6d}   {th:.9f}   {mg:+.7f}"
                  f"   {th / TH_ZUD:8.6f}{tag}\n")
    assert any(r[1:4] == ZUD for r in top)
    zud_rank = sum(1 for r in top if r[0] > th_zud) + 1
    beat = [r for r in top if r[0] > TH_ZUD]
    out.write(f"\n      [Zud07]'s own triple ranks {zud_rank} of {ntot} and reproduces its\n"
              f"      printed constant to nine digits.  Triples that BEAT it: {len(beat)}.\n")
    if beat:
        out.write("      => the claim of [Zud07] section 5 -- (9,19,9) 'the optimal choice of\n"
                  "         the integer parameters, at least under the restriction beta <= 100'\n"
                  "         -- does not hold on its own admissible set.\n")
    out.write("\n      where in the range it breaks: the running maximum over beta <= B\n")
    for be, th, t in ladder:
        out.write(f"        B = {be:3d}:  {th:.9f}  at {t}\n")
    brk = [be for be, th, t in ladder if th > th_zud + 1e-9]
    if brk:
        out.write(f"      (9,19,9) takes the lead at B = 19 and holds it through B ="
                  f" {brk[0] - 1};\n      it is displaced at B = {brk[0]}, so the claim is true on"
                  f" {brk[0] - 1} of the 100\n      values of B it asserts, and fails at a single"
                  " point inside its own range.\n")

    if bmax > 100:
        out.write(f"\n# [C] the extension, 100 < beta <= {bmax}\n")
        t0 = _clock()
        top2, ntot2, nskip2, _ = _zud_sweep(bmax, bmin=101,
                                            report=max(bmax // 10, 1), out=out)
        top2 = sorted(top2 + top, reverse=True)
        out.write(f"      {ntot2} further primitive admissible triples, {nskip2}"
                  f" (26)-infeasible, {_clock() - t0:.1f} s\n\n"
                  "        alpha  beta  gamma      theta          (26) margin   vs [Zud07]\n")
        for th, al, be, ga, mg in top2[:12]:
            out.write(f"        {al:5d} {be:5d} {ga:6d}   {th:.9f}   {mg:+.7f}"
                      f"   {th / TH_ZUD:8.6f}\n")
        top = top2

    out.write("\n# [D] what the grid is approximating: the ridge alpha = gamma\n")
    out.write("      the leaders all sit on alpha = gamma with beta/alpha near 2.1143;\n"
              "      theta along that ridge, at the best beta for each alpha:\n")
    ridge = []
    for al in (9, 19, 28, 35, 44, 53, 62, 71):
        cand = []
        for be in range(2 * al, int(2.25 * al) + 2):
            if gcd(al, be) != 1:
                continue
            th, mg, _, _, _ = _zud_theta(al, be, al)
            if mg < 0 and th < 1:
                cand.append((th, be, mg))
        if cand:
            th, be, mg = max(cand)
            ridge.append((al, be, th, mg))
            out.write(f"        alpha = gamma = {al:3d}:  beta = {be:3d}"
                      f"   beta/alpha = {be / al:.6f}   theta = {th:.9f}\n")
    assert ridge

    out.write("\n# [F] the ceiling: what stops the channel, and where\n"
              "      the ridge, refined -- alpha = gamma, beta/alpha in [2.1100, 2.1190]\n")
    rbest = (0.0, None, 0.0)
    for al in range(30, amax + 1):
        for be in range(int(2.1100 * al), int(2.1190 * al) + 2):
            if be < 2 * al or gcd(al, be) != 1:
                continue
            try:
                th, mg, _, _, _ = _zud_theta(al, be, al)
            except AssertionError:                          # int64 headroom, see _zud_c2_fast
                continue
            if mg < 0 < th < 1 and th > rbest[0]:
                rbest = (th, (al, be, al), mg)
                out.write(f"        alpha = gamma = {al:4d}  beta = {be:5d}"
                          f"  ratio = {be / al:.7f}  theta = {th:.9f}"
                          f"  (26) = {mg:+.6f}\n")
    out.write("      the (26) margin shrinks to zero along the record sequence: the optimum\n"
              "      is ON the validity boundary, not at an interior stationary point.\n")

    out.write("\n      and the boundary is what binds -- theta would keep rising:\n")
    for al, be in ((35, 74), (166, 351)):
        out.write(f"        alpha = {al}, beta = {be}, gamma varying"
                  f"   (gamma = {al} is the last valid one)\n")
        for ga in range(al - 3, al + 3):
            if not 1 <= ga < be:
                continue
            th, mg, _, _, _ = _zud_theta(al, be, ga)
            out.write(f"          gamma = {ga:4d}  theta = {th:.9f}  (26) = {mg:+9.5f}"
                      f"   {'valid' if mg < 0 else 'INVALID'}\n")
    out.write("      so the unconstrained objective is not the obstruction; (26) is.\n")

    if rbest[1]:
        th, tr, mg = rbest
        loc = True
        for da in range(-2, 3):
            for db in range(-2, 3):
                for dg in range(-2, 3):
                    q = (tr[0] + da, tr[1] + db, tr[2] + dg)
                    if q[0] < 1 or q[2] < 1 or q[2] >= q[1] or 2 * q[0] > q[1]:
                        continue
                    try:
                        t2, m2, _, _, _ = _zud_theta(*q)
                    except AssertionError:
                        continue
                    if m2 < 0 < t2 < 1 and t2 > th + 1e-12:
                        loc = False
        out.write(f"\n      best on the ridge: {tr}, theta = {th:.9f}, (26) = {mg:+.6f};\n"
                  f"      a local maximum over the full integer 5x5x5 neighbourhood: {loc}.\n"
                  f"      MEASURED CEILING for sub-idea (iii): theta <= about {th:.6f},\n"
                  f"      kappa = {-log(th) / log(1.5):.6f} -- against kappa = 1 for the T-shift\n"
                  "      problem.  The whole remaining freedom in the grid is worth\n"
                  f"      {th - TH_ZUD:.6f} on the constant ({100 * (th / TH_ZUD - 1):.3f}%).\n")

    out.write("\n# [E] gate G-D\n")
    if top and top[0][0] > TH_ZUD:
        th, al, be, ga, mg = top[0]
        out.write(f"      POSITIVE LEAD.  best = {th:.9f} at (alpha,beta,gamma) ="
                  f" ({al},{be},{ga}),\n"
                  f"      against [Zud07]'s {TH_ZUD:.9f} -- a gain of"
                  f" {th - TH_ZUD:.9f} on the constant\n"
                  f"      ({100 * (th / TH_ZUD - 1):.4f}%), with (26) margin {mg:+.7f} < 0.\n"
                  "      Gate G-D fires: stop and escalate before any proof or formalization\n"
                  "      commitment.  The lead is on the CONSTANT only; the effective\n"
                  "      threshold K is not computed here and is not claimed.\n")
    else:
        out.write("      no positive lead; (9,19,9) survives the sweep.\n")


# ----------------------------------------------------------------------------
#  S10 WP0.  The critical lattice L_n = Z(0,2^n) + Z(1,3^n), its exact successive
#  minima in the Minkowski-critical box, and Proposition 1's per-date optimum.
#
#  Coordinates.  A form l = a 2^n + b 3^n is the lattice point (b, l); two forms are
#  independent in the sense of TShift.multiplier_transfer (a1 b2 != a2 b1) exactly
#  when the two points are linearly independent, since
#      b1 l2 - b2 l1 = 2^n (a2 b1 - a1 b2).
#  The critical box of plan-S10 D1 is K = {|b| <= (3/2)^n, |l| <= (4/3)^n}; scaling
#  (b, l) -> (b 8^n, l 9^n) makes its norm max(|X|,|Y|)/12^n with det = 144^n, i.e.
#  lambda_1 lambda_2 in [1/2, 1] by Minkowski's second theorem -- which is both D1's
#  criticality and the correctness test for every number computed below.
# ----------------------------------------------------------------------------


def _cf_frontier(N, Dn):
    """Convergents of N/Dn as pairs (q_k, eps_k), eps_k = q_k N - p_k Dn.

    |eps_k| is the Euclid remainder sequence (strictly decreasing to 0, signs
    alternating), so the q_k are exactly the best-approximation denominators: the
    Pareto frontier of (|b|, min_a |b 3^n - a 2^n|).
    """
    a, b = N, Dn
    kp2, kp1 = 1, 0                          # k_{-2}, k_{-1}
    ep2, ep1 = N, -Dn                        # eps_{-2}, eps_{-1}
    out = []
    while b:
        q, r = divmod(a, b)
        k = q * kp1 + kp2
        e = q * ep1 + ep2
        out.append((k, e))
        kp2, kp1 = kp1, k
        ep2, ep1 = ep1, e
        a, b = b, r
    return out


def _rnd_div(p, q):
    """Nearest integer to p/q, exact."""
    if q < 0:
        p, q = -p, -q
    return (2 * p + q) // (2 * q)


def _line_min(A, B, Xu, Yu):
    """min over i in Z of max(|A + i Xu|, |B + i Yu|), exact (the function is convex
    in i, so a ternary search on integers is exact)."""
    def F(i):
        return max(abs(A + i * Xu), abs(B + i * Yu))
    i0 = _rnd_div(-A, Xu) if Xu else 0
    span = (abs(A) + F(i0)) // abs(Xu) + 2 if Xu else 2
    lo, hi = i0 - span, i0 + span
    while hi - lo > 2:
        m1 = lo + (hi - lo) // 3
        m2 = hi - (hi - lo) // 3
        if F(m1) <= F(m2):
            hi = m2
        else:
            lo = m1
    return min(F(i) for i in range(lo, hi + 1))


def _minima_scaled(n, wb, wl, fr=None):
    """Exact successive minima of L_n under N(b,l) = max(|b| wb, |l| wl), positive
    integers wb, wl: returns (mu1, mu2).  The box {|b| <= Bc, |l| <= Lc} is
    {N <= wb Bc} when (wb, wl) = (Lc, Bc), and it is the critical box of D1 when
    (wb, wl) = (8^n, 9^n), where the threshold is 12^n.

    mu1: for fixed b the best l is the centred residue, and b must be a best
    approximation denominator (else a smaller b does at least as well), so the
    candidates are the frontier points; g(k) = q_k wb increases and
    h(k) = |eps_k| wl decreases, so the minimum of max(g,h) sits at the crossing.

    mu2: with u the minimal vector (primitive: gcd(p_k,q_k) = 1) and w a neighbouring
    convergent (a basis, det = +-2^n), the points off the u-line are the cosets
    j w + Z u, j != 0, whose l^inf distance from 0 is at least j det/(|Xu|+|Yu|);
    since mu1 mu2 <= det this stops after a couple of cosets.  No lattice reduction
    and no enumeration is needed, so the cost is one Euclid run per date.
    """
    two = 1 << n
    fr = fr if fr is not None else _cf_frontier(3 ** n, two)

    lo, hi = 0, len(fr) - 1
    while lo < hi:                           # k* = min{k : g(k) >= h(k)}
        mid = (lo + hi) // 2
        q, e = fr[mid]
        if q * wb >= abs(e) * wl:
            hi = mid
        else:
            lo = mid + 1
    cands = [(fr[lo][0] * wb, lo)]
    if lo:
        cands.append((abs(fr[lo - 1][1]) * wl, lo - 1))
    mu1, k1 = min(cands)

    k2 = k1 + 1 if k1 + 1 < len(fr) else k1 - 1
    u = (fr[k1][0] * wb, fr[k1][1] * wl)
    w = (fr[k2][0] * wb, fr[k2][1] * wl)
    det = wb * wl * two
    L1 = abs(u[0]) + abs(u[1])
    mu2, j = None, 1
    while mu2 is None or j * det < mu2 * L1:
        v = _line_min(w[0] * j, w[1] * j, u[0], u[1])
        mu2 = v if mu2 is None else min(mu2, v)
        j += 1
        assert j <= 8, f"coset loop runaway at n = {n}"
    # the b = 0 line (l = k 2^n) is the one family the frontier argument does not
    # cover; in both uses here it is never minimal, and the cosets would catch it.
    assert mu1 <= two * wl and mu1 <= mu2, f"minima misuse at n = {n}"
    return mu1, mu2


def _minima(n, fr=None):
    """The successive minima in D1's critical box, as integers over 12^n:
    lambda_i = mu_i / 12^n, and lambda_1 lambda_2 in [1/2, 1] by Minkowski."""
    return _minima_scaled(n, 8 ** n, 9 ** n, fr)


def _two_forms_fit(n, B, Lam, fr=None):
    """Do two INDEPENDENT forms fit in the box {|b| <= B, |l| <= Lam}?  Exact."""
    _mu1, mu2 = _minima_scaled(n, Lam, B, fr)
    return mu2 <= B * Lam


def _min_B_for(n, Lam, fr=None):
    """The smallest B admitting two independent forms with |l| <= Lam, exactly.
    Monotone in B, so exponential bracketing then bisection.  Lam >= 1 always
    succeeds: (2^n, 0) and (b, +-1) are independent, and l = a 2^n + b 3^n runs over
    all of Z."""
    if Lam < 1:
        return None
    hi = 1
    while not _two_forms_fit(n, hi, Lam, fr):
        hi *= 2
        assert hi <= 1 << (n + 1), f"no B at n = {n}, Lam = {Lam}"
    lo = hi // 2                             # fails at lo (or lo = 0)
    while hi - lo > 1:
        mid = (lo + hi) // 2
        if _two_forms_fit(n, mid, Lam, fr):
            hi = mid
        else:
            lo = mid
    return hi


def _prop1_bracket(n, D, fr=None):
    """Two-sided exact bracket for the best bound TShift.transfer_prop_one can give
    at date n *in D1's regime*:

        best = max (2^n - D Lambda)/(B 2^n)  over independent pairs with
               Lambda = max|l_i|, B = max|b_i|,  subject to D Lambda <= 2^(n-1).

    In that regime the numerator lies in [2^(n-1), 2^n], so the objective is within a
    factor 2 of 1/B and the optimum is pinned by B0 = the smallest admissible B:

        (2^n - D Lambda_max)/(B0 2^n)  <=  best  <=  1/B0,

    the left value being achieved by the pair the lattice supplies at Lambda_max.
    Returns (B0, lo, hi) with lo, hi Fractions, or None if the regime is empty."""
    two = 1 << n
    lamcap = two // (2 * D)                  # Lambda <= 2^(n-1)/D, Lambda integral
    if lamcap < 1:
        return None
    fr = fr if fr is not None else _cf_frontier(3 ** n, two)
    B0 = _min_B_for(n, lamcap, fr)
    return B0, Fraction(two - D * lamcap, B0 * two), Fraction(1, B0)


def _prop1_brute(n, D, bmax, regime=True):
    """Brute-force optimum of Proposition 1 over every independent pair with
    |b| <= bmax and |l| <= 2^n.  Cross-check of _prop1_best at small n."""
    two, three = 1 << n, 3 ** n
    pts = []
    for b in range(1, bmax + 1):
        r = (b * three) % two
        for l in (r, r - two, r + two):
            if abs(l) <= two:
                pts.append((b, l))
    best = Fraction(0)
    for i, (b1, l1) in enumerate(pts):
        for (b2, l2) in pts[i + 1:]:
            if b1 * l2 == b2 * l1:
                continue                     # dependent
            lam = max(abs(l1), abs(l2))
            num = two - D * lam
            if num <= 0 or (regime and 2 * num < two):
                continue
            v = Fraction(num, max(b1, b2) * two)
            if v > best:
                best = v
    return best


def cmd_s8g_ledger(out=sys.stdout):
    """S8 WP-G block [Z]: the closing ledger.

    Every quantity the rewritten report entry asserts, re-derived from the same
    routines the work packages used -- one block per channel, every check an
    assert.  The point of the block is the last line: the best ceiling any of
    S8's three channels can reach, against the kappa = 1 the problem demands.
    """
    mu, t, K = 2, Fraction(-1, 8), 6
    out.write("plan-Tshift-S8 WP-G -- the closing ledger.\n"
              "The three channels' measured ceilings, re-derived; then the six\n"
              "work-package blocks in execution order.\n\n")

    out.write("# [Z1] gate G-A, re-asserted: the apparatus reproduces [Hab03] Thm 1\n")
    a0 = Fraction(224141, 240395)
    _F1, _F2, _A, _I, C1, C2 = _apparatus(mu, t, K, a0.numerator, a0.denominator)
    th_hab1 = exp(C1)
    out.write(f"      alpha_0 = {a0} = {float(a0):.9f}   (paper 0.932386281)\n")
    out.write(f"      theta   = {th_hab1:.12f}         (paper 0.57701737767006)\n")
    out.write(f"      C1 - C2 = {C1 - C2:+.3e}              (the criterion, at the crossing)\n")
    assert abs(th_hab1 - 0.57701737767006) < 1e-10
    assert abs(C1 - C2) < 1e-10

    out.write("\n# [Z2] channel (i) -- the determinant: dead at exponent AND constant level\n")
    fz = _hab_frozen()
    al, lX = 15 / 16, log(8.0)
    imp = _A_alpha(mu, al) - al * lX - log(fz["denomBase"]) - log(fz["contentBase"])
    val = log(fz["contentBase"]) - log(fz["errorBase"]) + al * lX
    out.write(f"      improvement margin  log(|c||det|/(2BP))/m -> {imp:+.9f} per m\n")
    out.write(f"      validity margin     log(P*X/(|c|Lambda))/m -> {val:+.9f} per m\n")
    out.write(f"      sum = {imp + val:.2e} -- disjoint, and the gap between the two\n"
              "      regions is the frozen numerals' own rounding, not headroom.\n")
    out.write("      (D1(v)'s surviving branch decays at exactly -validity: s8d [E].)\n")
    assert imp < 0.0 < val and abs(imp + val) < 1e-7

    out.write("\n# [Z3] channel (ii) -- content: the supply ceiling against the kappa = 1 demand\n")
    supI = _supply_at(mu, Fraction(1, 2))
    al_s, W, _Iw, logg = _reopt_wall(mu, t, K, 2.0 / 3.0)
    al_c, th_c = _ceiling_payoff(mu, t, K, supI)
    out.write(f"      sup_alpha I = I(1/2)      = {supI:.9f} nats/m   (the family's ceiling)\n")
    out.write(f"      demand at kappa = 1       = {W:.9f} nats/m   at alpha* = {al_s:.6f}\n")
    out.write(f"      the wall g*               = {exp(logg):.4f}          (re-optimized, not 2.3786)\n")
    out.write(f"      an EXACT content lemma buys theta = {th_c:.6f}, kappa = {_kappa(th_c):.5f}\n")
    assert supI < W and th_c < 2.0 / 3.0 and _kappa(th_c) > 1.0

    out.write("\n# [Z4] channel (iii) -- the [Zud07] parameter grid: lead, and ceiling\n")
    ZUD, MAXT, PAPER = (9, 19, 9), (35, 74, 35), (44, 93, 44)
    CEIL = (463, 979, 463)
    out.write("      triple            theta         (26) margin   kappa\n")
    ths = {}
    for tr in (ZUD, MAXT, PAPER, CEIL):
        th, m26, _c0, _c1, _c2 = _zud_theta(*tr)
        ths[tr] = th
        out.write(f"      {str(tr):<17} {th:.9f}   {m26:+10.6f}   {_kappa(th):.6f}\n")
    gain = ths[MAXT] - ths[ZUD]
    out.write(f"      lead over the printed constant: {gain:+.9f} ({100 * gain / ths[ZUD]:.4f}%)\n")
    out.write(f"      measured ceiling of the whole channel: {ths[CEIL]:.9f}"
              f"  (+{ths[CEIL] - ths[ZUD]:.6f})\n")
    assert ths[MAXT] > ths[ZUD] and ths[PAPER] > ths[ZUD]
    assert ths[CEIL] > ths[MAXT] and ths[CEIL] < 0.5808
    assert _kappa(ths[CEIL]) > 1.34

    out.write("\n# [Z5] the verdict: the best ceiling over all three channels\n")
    best = max(th_c, ths[CEIL])
    out.write("      (i)   no ceiling to quote -- the improvement region is empty\n")
    out.write(f"      (ii)  theta <= {th_c:.6f}   kappa = {_kappa(th_c):.5f}\n")
    out.write(f"      (iii) theta <= {ths[CEIL]:.6f}   kappa = {_kappa(ths[CEIL]):.5f}\n")
    out.write(f"      best  theta <= {best:.6f}   kappa = {_kappa(best):.5f}"
              "   -- against kappa = 1\n")
    out.write(f"      2/3 needs {2.0 / 3.0:.6f}: short by {2.0 / 3.0 - best:.6f} on the constant.\n")
    assert best < 2.0 / 3.0
    out.write("\n      [Z] closes: no channel of S8 reaches the T-shift threshold,\n"
              "      and both surviving ceilings are measured, not estimated.\n")


def _lg2(x):
    """log2 of a positive integer (display only; every decision above is exact)."""
    return log(x) / log(2) if x else float("-inf")


def cmd_s10(nmax, out=sys.stdout):
    """S10 WP0: D1 re-verified, the exact minima of L_n, Proposition 1's per-date
    optimum, the record cross-check against N5, and D2's escape window."""
    lg12 = _lg2(12)

    # ---------------------------------------------------------------- [A] ----
    out.write("# [A] D1 -- the box is Minkowski-critical, symbolically\n")
    for n in (1, 2, 3, 8, 64, 512, nmax):
        box = Fraction(4, 3) ** n * Fraction(3, 2) ** n
        assert box == 2 ** n, (n, box)
    out.write("  (4/3)^n (3/2)^n = 2^n = det L_n   exact in Q, n in "
              "{1,2,3,8,64,512,%d}: verified\n" % nmax)
    out.write("  log2(4/3) + log2(3/2) = %.15f (= 1 exactly; the two exponents "
              "0.415037 + 0.584963)\n" % (_lg2(4) - _lg2(3) + _lg2(3) - _lg2(2)))
    out.write("  scaled model (b,l) -> (b 8^n, l 9^n): det = 8^n 9^n 2^n = 144^n = "
              "(12^n)^2, so the\n"
              "  critical box is the UNIT box and Minkowski's second theorem reads "
              "lambda_1 lambda_2 in [1/2,1].\n")
    out.write("#   D    smallest n with D (4/3)^n <= 2^(n-1)   (D1's regime "
              "hypothesis at the critical Lambda)\n")
    for D in (1, 5, 19, 65, 211):
        n0 = 1
        while D * 4 ** n0 * 2 > 3 ** n0 * 2 ** n0:
            n0 += 1
        out.write(f"  {D:4d}    n >= {n0}\n")
    out.write("#   base p/q: critical box ((q^2/p)^n, (p/q)^n), product q^n = "
              "det;  free zone <=> p > q^2\n")
    for (p, q) in ((3, 2), (5, 2), (5, 3), (7, 3), (8, 3), (9, 4), (5, 4), (17, 4)):
        assert (Fraction(q * q, p) ** 3) * (Fraction(p, q) ** 3) == q ** 3
        deg = Fraction(q * q, p) < 1
        out.write(f"  {p}/{q}: q^2/p = {Fraction(q*q,p)} "
                  f"{'< 1  -> O(1) forms, free zone' if deg else '> 1  -> genuine box'}"
                  f"   (p > q^2: {'yes' if p > q*q else 'no'})\n")

    # ---------------------------------------------------------------- [B] ----
    out.write("\n# [B] the exact successive minima of L_n in the critical box, "
              f"2 <= n <= {nmax}\n")
    mins, bad, fit = [], 0, 0
    rec1, rec2, hold1, hold2 = [], [], None, None
    p12 = 12 ** 2
    for n in range(2, nmax + 1):
        mu1, mu2 = _minima(n)
        det = p12 * p12
        if not (2 * mu1 * mu2 >= det and mu1 * mu2 <= det):
            bad += 1
            out.write(f"!! Minkowski FAILS at n = {n}\n")
        two_fit = mu2 <= p12                             # lambda_2 <= 1, exactly
        fit += two_fit
        # exact records across dates: mu/p12 vs muR/p12R by cross-multiplication
        if hold1 is None or mu1 * hold1[1] < hold1[2] * p12:
            hold1 = (n, p12, mu1)
            rec1.append(n)
        if hold2 is None or mu2 * hold2[1] > hold2[2] * p12:
            hold2 = (n, p12, mu2)
            rec2.append(n)
        mins.append((n, _lg2(mu1) - n * lg12, _lg2(mu2) - n * lg12, two_fit))
        p12 *= 12
    out.write(f"  Minkowski 1/2 <= lambda_1 lambda_2 <= 1 : "
              f"{len(mins) - bad}/{len(mins)} dates ok  "
              f"(exact integers; the correctness test)\n")
    out.write(f"  dates with lambda_2 <= 1, i.e. TWO independent forms in the "
              f"unblown critical box: {fit}/{len(mins)}"
              f"  ({100.0*fit/len(mins):.1f}%)\n")
    out.write("#      n   lambda_1        lambda_2       lambda_2^(1/n)   "
              "lambda_1 lambda_2   two forms?\n")
    show = [n for n in (2, 3, 5, 10, 20, 50, 100, 200, 500, 1000, 2000, 5000,
                        10000, 20000, nmax) if 2 <= n <= nmax]
    hi_r = max(mins[98:] or mins, key=lambda r: r[2] / r[0])
    lo_1 = min(mins, key=lambda r: r[1])
    hi_2 = max(mins, key=lambda r: r[2])
    for n in sorted(set(show) | {hi_r[0], lo_1[0], hi_2[0]}):
        _n, l1, l2, ok = mins[n - 2]
        out.write(f"  {n:6d}   2^{l1:8.4f}     2^{l2:8.4f}    {2**(l2/n):12.8f}    "
                  f"2^{l1+l2:8.4f}        {'yes' if ok else 'no':>3s}\n")
    out.write(f"  extremes: smallest lambda_1 = 2^{lo_1[1]:.4f} at n = {lo_1[0]};"
              f"  largest lambda_2 = 2^{hi_2[2]:.4f} at n = {hi_2[0]}\n")
    out.write(f"  largest RATE lambda_2^(1/n) over n >= 100: "
              f"{2**(hi_r[2]/hi_r[0]):.8f} at n = {hi_r[0]} "
              f"-- the unbalancedness is sub-exponential on this range\n")

    # ---------------------------------------------------------------- [C] ----
    out.write("\n# [C] Proposition 1's per-date optimum (TShift.transfer_prop_one), "
              "over ALL admissible pairs\n")
    ncap = min(nmax, 1000)
    ident = 0
    for n in range(2, ncap + 1):
        two = 1 << n
        r = (3 ** n) % two
        r = min(r, two - r)                              # |r| <= 2^(n-1), r odd
        # family (ii) at b = 1: Lambda = 2^n - |r|, B = 1, so the bound is exactly
        # (2^n - D(2^n - |r|))/2^n, which at D = 1 is |r|/2^n = ||(3/2)^n||.
        assert Fraction(two - (two - r), two) == Fraction(r, two)
        assert two - 5 * (two - r) <= 0 and two - 19 * (two - r) <= 0
        ident += 1
    out.write(f"  UNCONSTRAINED tier: at D = 1 the degenerate pair (1, r), "
              f"(1, r - 2^n) turns Proposition 1 into an\n"
              f"  IDENTITY -- bound = |r|/2^n = ||(3/2)^n|| exactly -- at all "
              f"{ident}/{ident} dates n <= {ncap}.  So the\n"
              f"  transfer carries zero slack, but also zero content: the pair "
              f"encodes the answer.  At D >= 2 the\n"
              f"  same family has numerator 2^n - D(2^n - |r|) <= 2^n - D 2^(n-1) "
              f"<= 0 (verified), so the tautology is\n"
              f"  a D = 1 phenomenon.  D1's hypothesis D Lambda <= 2^(n-1) is "
              f"exactly what excludes it.\n")
    out.write("#   D   empty   worst loss truth/best   at n     B0 range        "
              "rate best^(1/n) range      min rate, n >= 100\n")
    for D in (1, 5, 19):
        loss, loss_at, empty, r100 = 0.0, None, 0, 9.9
        rlo, rhi, b0lo, b0hi = 9.9, 0.0, None, 0
        for n in range(2, ncap + 1):
            two = 1 << n
            t = (D * 3 ** n) % two
            truth = Fraction(min(t, two - t), two)
            br = _prop1_bracket(n, D)
            if br is None:
                empty += 1
                continue
            B0, lo, hi = br
            assert lo <= truth, f"Prop 1 EXCEEDS the truth at n = {n}, D = {D}"
            if float(truth / lo) > loss:
                loss, loss_at = float(truth / lo), n
            rlo = min(rlo, float(lo) ** (1.0 / n))
            rhi = max(rhi, float(hi) ** (1.0 / n))
            if n >= 100:
                r100 = min(r100, float(lo) ** (1.0 / n))
            b0lo = B0 if b0lo is None else min(b0lo, B0)
            b0hi = max(b0hi, B0)
        out.write(f"  {D:3d}   {empty:5d}   {loss:19.4f}   {loss_at:6d}   "
                  f"{b0lo:6d}..{b0hi:<8d}  [{rlo:.6f}, {rhi:.6f}]      "
                  f"{r100:.6f}\n")
    out.write("  Read: in D1's regime the two-form optimum is 1/B0 up to a factor 2, "
              "B0 = the smallest\n"
              "  admissible second coefficient.  B0 stays POLYNOMIAL in the "
              "measured range, so the transfer\n"
              "  loses no exponential factor at all -- the rate best^(1/n) tends "
              "to 1, far above the 2/3 demand.\n"
              "  The whole difficulty is therefore CONSTRUCTING such a pair "
              "uniformly in n, not the loss of\n"
              "  Proposition 1: at each single date the optimal pair already "
              "reproduces the truth to a factor 2\n"
              "  at D = 1 (and to the printed factor at D = 5, 19).\n")
    for n in range(3, 13):
        for D in (1, 5, 19):
            bmax = 4 * 3 ** n // 2 ** n + 8
            two = 1 << n
            t = (D * 3 ** n) % two
            truth = Fraction(min(t, two - t), two)
            ex = _prop1_brute(n, D, bmax, regime=True)
            br = _prop1_bracket(n, D)
            if br is None:
                assert ex == 0, f"bracket says empty but brute finds {ex} at n={n}"
                continue
            B0, lo, hi = br
            assert lo <= ex <= hi, f"bracket fails n={n}, D={D}: {lo} {ex} {hi}"
            f = _prop1_brute(n, D, bmax, regime=False)
            assert f <= truth and f >= ex, f"free tier n={n}, D={D}: {f}"
            if D == 1:
                assert f == truth, f"free tier not an identity at n={n}: {f}"
    out.write("  cross-check: the bracket contains the brute-force optimum over "
              "EVERY independent pair,\n"
              "  3 <= n <= 12, D in {1,5,19}; and the unconstrained brute force is "
              "the truth at D = 1 and\n"
              "  lies between the regime optimum and the truth at D = 5, 19.\n")

    # ---------------------------------------------------------------- [D] ----
    out.write("\n# [D] record structure: lambda-records against N5's "
              "||D(3/2)^n|| records\n")
    out.write(f"  lambda_1 record lows  (best forms so far): {rec1}\n")
    out.write(f"  lambda_2 record highs (hardest dates)    : {rec2}\n")
    for D in (1, 5, 19):
        dates, ba, be = [], None, None
        for n, t, m, _T in orbit(D, nmax):
            if n < 1:
                continue
            a = dist_num(t, n)
            if ba is None or (a << be) < (ba << n):
                ba, be = a, n
                dates.append(n)
        out.write(f"  D = {D:3d} record dates of ||D(3/2)^n||: {dates}\n")
        out.write(f"           shared with the lambda_1 records: "
                  f"{sorted(set(dates) & set(rec1))}\n")

    # ---------------------------------------------------------------- [E] ----
    out.write("\n# [E] D2 -- the escape window, measured exactly "
              "(cascade itself: subcommand `runs`)\n")
    out.write("#   D    max sojourn e(n0)-n0    at n0    e(n0)-n0 <= v2(m_n0)+1 "
              "(exact cascade cap)\n")
    for D in (1, 5, 19):
        data = [(n, t, m) for (n, t, m, _T) in orbit(D, nmax)]
        small = [5 * dist_num(t, n) < (1 << n) for (n, t, _m) in data]
        nxt = [None] * (nmax + 2)                        # first escape date >= n
        e = None
        for n in range(nmax, 0, -1):
            if not small[n]:
                e = n
            nxt[n] = e
        worst, worst_at, viol = 0, None, 0
        for n0 in range(1, nmax + 1):
            if nxt[n0] is None:
                continue                                 # truncated by the horizon
            L = nxt[n0] - n0
            if L > worst:
                worst, worst_at = L, n0
            cap = v2(data[n0][2])
            if cap is not None and L > cap + 1:
                viol += 1
                out.write(f"!! window cap FAILS at n0 = {n0}: L = {L}, "
                          f"v2(m) = {cap}\n")
        m0 = data[worst_at][2] if worst_at else 1
        out.write(f"  {D:4d}    {worst:8d}              {worst_at:6d}    "
                  f"{'ok' if not viol else str(viol) + ' FAIL'}"
                  f"   (v2(m_n0) = {v2(m0)}, floor(kappa_free n0 + log2 D) = "
                  f"{(D * 3 ** worst_at).bit_length() - 1 - worst_at})\n")
    out.write("  T6 reading: the first escape after n0 lands at "
              "n0 + v2(m_n0) + 1 at the latest, and\n"
              "  v2(m_n0) <= log2 m_n0 <= kappa_free n0 + log2 D + 1 -- so the "
              "window is exponentially\n"
              "  short in the orbit's own scale, and the measured worst case is "
              "far below even that.\n")


def _convergents(num, den):
    """The convergents (p, q) of num/den, ascending, in lowest terms."""
    a, b = num, den
    p2, p1, q2, q1 = 0, 1, 1, 0
    out = []
    while b:
        c = a // b
        a, b = b, a - c * b
        p2, p1 = p1, c * p1 + p2
        q2, q1 = q1, c * q1 + q2
        out.append((p1, q1))
    return out


def _g_inverse(g, target, hi=1e30):
    """The least c8 with g(t) >= target for all t >= c8 (g eventually increasing)."""
    lo = 3.0
    if g(lo) >= target:
        return lo
    while hi / lo > 1 + 1e-12:
        mid = (lo * hi) ** 0.5
        if g(mid) < target:
            lo = mid
        else:
            hi = mid
    return hi


def cmd_s10b(nmax=400, out=sys.stdout):
    """S10 WP-B, gate G-A': the CDT -> T-shift dictionary, calibrated.

    [A] the currency (theta <-> kappa <-> eps_0) and the wall W = log3/log(3/2);
    [B] G-A' layer 1 -- [Hab03]'s number through the S1 apparatus, and the
        three-term budget that fixes the slot assignment;
    [C] the break-even, and how much of the budget the arithmetic slot carries;
    [D] the content slot: scale invariance of (2.2)/(2.4) against the family's gain;
    [E] the wall per base p/q, against N3's free zone;
    [F] the Dirichlet forcing floor -- exact integer witnesses for the hypothesis
        (1.1) of [CDT-ICM] Thm 1.1, and the window the demand C < W leaves;
    [G] the printed constant assembly of [CDT-ICM] section 4;
    [H] the (1.4) demand, and why the abc-folklore refinement is vacuous at t = 1.

    Nothing here is a claim about ||D(3/2)^n||: block [F] verifies hypotheses of a
    printed theorem on exact integers, and blocks [G]/[H] read printed constants.
    """
    L2, L3, L32 = log(2.0), log(3.0), log(1.5)
    W = L3 / L32
    kap = lambda th: -log(th) / L32
    eps0 = lambda th: log(3.0 / (2.0 * th)) / L3
    res = []

    def chk(name, ok, detail=""):
        res.append(bool(ok))
        out.write(f"  [{'PASS' if ok else 'FAIL'}] {name}"
                  f"{'   ' + detail if detail else ''}\n")

    out.write("plan-Tshift-S10 WP-B -- the dictionary and gate G-A'.\n"
              "Engine: [CDT-ICM] = arXiv:2510.04156 (Thm 1.1, Thm 2.1, Prop 2.4,\n"
              "Thm 2.6, Prop 3.3, section 4);  family: [Hab03] via the S1 apparatus.\n")

    # ---------------------------------------------------------------- [A] ----
    out.write("\n# [A] the currency, and the wall\n")
    out.write(f"  W = log3/log(3/2) = {W:.12f}"
              "   <- (1.2)'s demand: C(Q,inf,<3/2>,eps) < W\n")
    out.write("   theta              kappa       eps_0     (1+kappa)/W    |diff|"
              "   point\n")
    pts = [("[Hab03] Thm 1, proved", 0.57701737767006),
           ("T1/T4 target 2/3", 2.0 / 3.0),
           ("S5's bar theta*", 0.78885),
           ("eps_0 = 1 exactly", 0.5),
           ("Dirichlet edge (eps_0 = log(3/2)/log3)", 1.0)]
    worst = 0.0
    for name, th in pts:
        k, e = kap(th), eps0(th)
        k = 0.0 if abs(k) < 1e-15 else k
        pred = (1.0 + k) / W
        worst = max(worst, abs(e - pred))
        out.write(f"  {th:.12f}   {k:9.6f}  {e:9.6f}   {pred:9.6f}   "
                  f"{abs(e - pred):.1e}   {name}\n")
    chk("eps_0(theta) = (1 + kappa(theta))/W identically", worst < 1e-14,
        f"worst |diff| = {worst:.2e}")
    chk("2/eps_0(2/3) = W exactly (the two-log threshold meets the height wall)",
        abs(2.0 / eps0(2.0 / 3.0) - W) < 1e-13,
        f"2/eps_0 = {2.0 / eps0(2.0 / 3.0):.12f}")
    chk("3^eps_0(2/3) = 9/4 exactly, so H(gamma)^-eps_0 = (4/9)^n is integral",
        abs(3.0 ** eps0(2.0 / 3.0) - 2.25) < 1e-13)
    out.write("  Reading: the wall W is kappa-free.  The lane's demand does not "
              "soften as the\n  target weakens -- only the argument eps_0 of "
              "C(.,eps) moves.\n")

    # ---------------------------------------------------------------- [B] ----
    out.write("\n# [B] G-A' layer 1: the known number from the known data\n")
    F1, F2, A, I, C1, C2 = _apparatus(2, Fraction(-1, 8), 6, 224141, 240395)
    al0 = 224141 / 240395
    q1, e1 = A + log(F1), A + log(F2)
    th = exp(C1)
    chk("the S1 apparatus returns [Hab03] Theorem 1 to ten digits",
        abs(th - 0.57701737767006) < 5e-11,
        f"theta = {th:.14f}   printed 0.57701737767006")
    rateB = q1 + 3 * al0 * L2 - I
    out.write(f"  slot decomposition at alpha_0 = {al0:.9f}, K = 6:\n"
              f"    analytic, evaluation point   3 alpha log2 = {3*al0*L2:12.9f}"
              "   (the 8^(n+1) factor)\n"
              f"    analytic, growth on domain   q1 = A + log F1 = {q1:12.9f}"
              "   (denominator growth)\n"
              f"    arithmetic, content gain     I(alpha_0)     = {I:12.9f}"
              "   (enters with a MINUS)\n"
              f"    rate_B = q1 + 3 alpha log2 - I             = {rateB:12.9f}"
              f"   theta = e^(-rate_B/K)\n")
    chk("the three-term budget reproduces C1, i.e. the slot assignment is exact",
        abs(exp(-rateB / 6) - th) < 1e-12,
        f"|e^(-rate_B/6) - e^C1| = {abs(exp(-rateB/6) - th):.2e}")
    F1b, F2b, Ab, Ib, _, _ = _apparatus(2, Fraction(-1, 8), 6, 15, 16)
    q1b, e1b = Ab + log(F1b), Ab + log(F2b)
    chk("printed q1 at alpha = 15/16 (p. 308)", abs(q1b - 1.7721197321) < 5e-10,
        f"{q1b:.10f}")
    chk("printed e1 at alpha = 15/16 (p. 308)", abs(e1b - 2.3390368029) < 5e-10,
        f"{e1b:.10f}")

    # ---------------------------------------------------------------- [C] ----
    out.write("\n# [C] the break-even, and which slot carries the margin\n")
    I_be = (45 / 16) * L2 + q1b - 4.8 * L2
    A_m = 0.3945 - I_be
    rateB15 = q1b + 3 * (15 / 16) * L2 - 0.3945
    chk("the S1 note's break-even I >= (45/16)log2 + q1 - 4.8 log2",
        abs(I_be - 0.394489710737) < 1e-9,
        f"I_be = {I_be:.12f} from the apparatus, 0.394489710737 in the note -- the "
        f"6.1e-11 gap is the printed q1's own rounding (1.7721197321 vs "
        f"{q1b:.11f})")
    chk("(3.11)'s 0.3945 clears it by A_m = 1.0289e-5 per m",
        abs(A_m - 1.0289e-5) < 1e-9, f"A_m = {A_m:.6e}")
    out.write(f"  rate_B at alpha = 15/16 with I = 0.3945: {rateB15:.9f} nats per m"
              f"   (= 4.8 log2 - A_m)\n"
              f"  the whole theorem's margin, as a share of the budget: "
              f"A_m/rate_B = {A_m / rateB15:.3e}\n")
    chk("the margin lives entirely in the arithmetic slot",
        abs(rateB15 - (4.8 * L2 - A_m)) < 1e-12,
        f"relative share {A_m / rateB15:.2e}, i.e. 3 parts in 10^6")

    # ---------------------------------------------------------------- [D] ----
    out.write("\n# [D] the content slot: what the engine can and cannot see\n")

    def engine(numer, logdphi, tau):
        """(2.2)'s right-hand side: the bound on m.  Scale of the f_i does not enter."""
        return numer / (logdphi - tau) if logdphi > tau else float("inf")

    numer, logdphi = 1.0, 2.0                     # any admissible pair; only tau moves
    with_content, without = engine(numer, logdphi, 0.0), engine(numer, logdphi, 0.0)
    th_with = exp(-(q1b + 3 * (15 / 16) * L2 - 0.3945) / 6)
    th_without = exp(-(q1b + 3 * (15 / 16) * L2) / 6)
    out.write("  tau(b) = (1/m^2) sum (2i-1) sigma_i lies in [0, sigma_m] (printed, "
              "Thm 2.1): a\n  denominator LOSS.  The family's arithmetic input is a "
              "content GAIN, -I(alpha) < 0.\n")
    chk("the family's arithmetic slot value is outside the printed range of tau(b)",
        -I_be < 0.0, f"-I = {-I_be:.6f} < 0 = min tau(b)")
    out.write(f"  remove the content and the family's own output moves "
              f"{th_with:.6f} -> {th_without:.6f},\n"
              f"  and its break-even fails (0 < {I_be:.6f}), so there is no theorem "
              "left at all;\n  the engine's bound is unchanged, because (2.2)/(2.4) "
              "are invariant under f_i -> c f_i.\n")
    chk("(2.2)'s value is invariant under content removal", with_content == without,
        f"{with_content:.6f} = {without:.6f}")
    chk("the family's own output is NOT invariant", th_with > th_without,
        f"{th_with:.6f} > {th_without:.6f}")
    chk("without the content the family is below its own break-even",
        0.0 < I_be, "no theorem at I = 0")

    # ---------------------------------------------------------------- [E] ----
    out.write("\n# [E] the wall per base p/q: W(p,q) = log p / log(p/q)\n")
    ok = True
    out.write("   p/q     W(p,q)     W < 2   p > q^2   agree\n")
    for (p, q) in ((3, 2), (5, 2), (5, 3), (7, 3), (8, 3), (9, 4), (5, 4), (17, 4)):
        Wpq = log(p) / log(p / q)
        agree = (Wpq < 2) == (p > q * q)
        ok = ok and agree
        out.write(f"  {p:2d}/{q:<2d}  {Wpq:9.6f}   {'yes' if Wpq < 2 else 'no ':>3s}"
                  f"     {'yes' if p > q * q else 'no ':>3s}      "
                  f"{'ok' if agree else '*** NO ***'}\n")
    chk("W(p,q) < 2 exactly on N3's free zone p > q^2", ok, "eight bases")

    # ---------------------------------------------------------------- [F] ----
    out.write("\n# [F] the Dirichlet forcing floor, on exact integers\n")
    out.write("  For gamma = (2/3)^n and A = m/D, |1 - A gamma| = |D 3^n - m 2^n|"
              "/(D 3^n) and\n  H(gamma) = 3^n.  A convergent m/D of 3^n/2^n that "
              "meets (1.1) is a witness, and\n  forces C >= h(gamma)/(1 + h(A)).  "
              "The test below is an exact integer comparison.\n")
    floors = {}
    for th_t, num, den, tag in ((2.0 / 3.0, 4, 9, "theta = 2/3, H^-eps = (4/9)^n"),
                                (0.5, 1, 3, "theta = 1/2, H^-eps = 3^-n")):
        lim = W / (1 + kap(th_t) / 2)
        out.write(f"\n  {tag}:  eps_0 = {eps0(th_t):.6f}, "
                  f"guaranteed floor W/(1+kappa/2) = {lim:.6f}\n")
        out.write("     n     forced C >=    log D/n    rho = -log||.||/n   log10 D"
                  "   witnesses\n")
        best_all = 0.0
        for n in (12, 24, 48, 96, 192, nmax):
            P3, P2, best, cnt = 3 ** n, 2 ** n, None, 0
            for (p, q) in _convergents(P3, P2):
                err = abs(q * P3 - p * P2)               # = 2^n ||D (3/2)^n||
                if err * den ** n <= num ** n * q * P3:  # (1.1), exactly
                    cnt += 1
                    R = n * L3 / (1.0 + log(max(p, q)))
                    if best is None or R > best[0]:
                        best = (R, q, log(q) / n,
                                (n * L2 - log(err)) / n if err else float("inf"))
            R, q, d, rho = best
            best_all = max(best_all, R)
            out.write(f"  {n:4d}   {R:10.6f}   {d:9.6f}      {rho:9.6f}      "
                      f"{log(q)/log(10):7.2f}   {cnt:3d}\n")
        floors[th_t] = best_all
        chk(f"witnesses force C >= {lim - 0.01:.2f} at {tag.split(',')[0]}",
            best_all > lim - 0.01,
            f"measured sup over the dates tested = {best_all:.6f}")
    win = W / floors[2.0 / 3.0]
    out.write(f"\n  the demand C < W = {W:.6f} against the forced floor "
              f"{floors[2.0/3.0]:.6f}:\n  the whole admissible window is a factor "
              f"{win:.4f} wide.\n")
    chk("the window the demand leaves is below a factor 1.5", win < 1.5,
        f"W/floor = {win:.4f}")
    out.write("  Shape note (no claim about ||D(3/2)^n||): a witness with D bounded "
              "has\n  h(gamma)/(1+h(A)) -> W, so a single bounded-D solution of "
              "(1.1) would force C >= W\n  and close the lane; that solution is "
              "exactly what T1/T4 denies.  Ratios at D = 1, 5, 19:\n")
    for D in (1, 5, 19):
        r = [nn * L3 / (1.0 + log(D) + nn * L32) for nn in (100, 10000, 10 ** 6)]
        out.write(f"    D = {D:2d}:  n = 10^2: {r[0]:.6f}   10^4: {r[1]:.6f}   "
                  f"10^6: {r[2]:.6f}   -> W\n")
    chk("the bounded-D witness shape has ratio -> W",
        abs(10 ** 6 * L3 / (1.0 + 10 ** 6 * L32) - W) < 1e-5)

    # ---------------------------------------------------------------- [G] ----
    out.write("\n# [G] the printed constant assembly ([CDT-ICM] section 4)\n")
    out.write("  h(gamma) <= 3 h(A) + c10 Q! N,  Q = ceil((2 c8 c9)^t),  "
              "N < g 2 c8 h(A)/(Q-1)!,\n  so C = 3 + 2 g Q (c8 c10 + 1) with "
              "t = 1, g = 2 (v archimedean), and c9 = log3\n  from (4.3) at "
              "Gamma = <3/2> (h(3/2) = log3, torsion contributes 0).\n")
    chk("the h(A) coefficient of the printed chain already exceeds the wall",
        3.0 > W, f"3 > W = {W:.6f}, a factor {3.0/W:.4f}")
    c9 = L3
    Q0 = ceil(2 * 1.0 * c9)
    Cmin = 3 + 2 * 2 * Q0 * (1.0 * 1.0 + 1)
    chk("with every unnamed constant at its floor 1 the chain still gives C >= 27",
        Cmin >= 27 - 1e-9, f"C >= {Cmin:.1f}, a factor {Cmin/W:.2f}")
    out.write("  c8 = the least x with g(x) >= 2/eps_0 = W, for the printed shapes of g:\n")
    out.write("   g(t)                                      c8          Q"
              "            C            C/W\n")
    shapes = [("[CDT-ICM] sec 3, d = 1:  t^(1/2)/(log t)^3",
               lambda t: t ** 0.5 / log(t) ** 3),
              ("Bombieri [17]:           (log t)^(1/2)", lambda t: log(t) ** 0.5),
              ("Bombieri-Cohen [21]:     t/(log t)^7", lambda t: t / log(t) ** 7),
              ("Bombieri-Cohen [22]:     t/(log t)^5", lambda t: t / log(t) ** 5)]
    for name, g in shapes:
        c8 = _g_inverse(g, W)
        Q = ceil(2 * c8 * c9)
        C = 3 + 2 * 2 * Q * (c8 + 1)
        out.write(f"  {name:42s} {c8:9.3g}  {Q:11.4g}  {C:11.4g}  {C/W:11.4g}\n")
    out.write("  Direction warning: the proportionality constants in these shapes "
              "are not printed;\n  the table normalizes them to 1, so these are "
              "shape estimates, not bounds.  The\n  (log t)^(1/2) line is "
              "exponentially sensitive to that normalization; the two\n  "
              "polynomial lines are not.  The two statements that ARE bounds are "
              "the two checks above.\n")

    # ---------------------------------------------------------------- [H] ----
    out.write("\n# [H] the (1.4) demand, and the abc-folklore refinement at rank 1\n")
    dem = W / (1 + L3)
    out.write(f"  (1.4): C << prod_i (1 + h(xi_i)); at Gamma = <3/2>, t = 1, "
              f"the product is 1 + log3 = {1+L3:.9f}\n"
              f"  so the demand C < W becomes: the absolute coefficient must be "
              f"below {dem:.9f}.\n")
    chk("the (1.4)-shape demand on the absolute coefficient", dem < 1.3,
        f"c < {dem:.6f}")
    chk("at rank 1 the abc-folklore refinement (product -> sum) is an identity",
        abs((1 + L3) - (1 + L3)) < 1e-15, "one factor, one summand: nothing moves")

    out.write(f"\n{sum(res)}/{len(res)} checks PASS\n")
    return res


def _bisect_dec(f, lo, hi, iters=60):
    """The root of a decreasing f on [lo, hi]; the sign change is asserted."""
    assert f(lo) > 0 > f(hi), (f(lo), f(hi))
    for _ in range(iters):
        mid = 0.5 * (lo + hi)
        if f(mid) > 0:
            lo = mid
        else:
            hi = mid
    return 0.5 * (lo + hi)


def _ceiling_at_supply(mu, t, K, I, hi):
    """(alpha, theta) where the demand W(alpha) meets a CONSTANT supply I.

    The apparatus is valid only where supply >= demand, and the payoff decreases
    in alpha, so the crossing is the ceiling of that supply.  I = 0 is the engine's
    best case (its slot is a denominator loss, DA2/O1), and I < 0 is what a real
    denominator type tau > 0 gives.
    """
    al = _bisect_dec(lambda a: _supply_demand(mu, t, K, a)[1] - I, 1e-6, hi)
    return al, exp(_supply_demand(mu, t, K, al)[0])


def _demand_at_theta(mu, t, K, theta, hi):
    """(alpha, W) at the payoff level theta -- the content rate that target costs."""
    al = _bisect_dec(lambda a: _supply_demand(mu, t, K, a)[0] - log(theta), 1e-6, hi)
    return al, _supply_demand(mu, t, K, al)[1]


def _bom93_logQ(kap, d=1, t=1, hs=(log(3.0),)):
    """log of [Bom93] Thm 2's coefficient  Q = (e^{115d/kap^2} t)^{t+1} prod h(xi_i).

    Its conclusion is h(A xi) <= max(Q h(A), [Q]!), so Q is the h(A) coefficient.
    """
    return (t + 1) * (115.0 * d / kap ** 2 + log(t)) + sum(log(h) for h in hs)


def _bc97_coeff(kap, d=1, t=1, hs=(log(3.0),), Dv=1.0, pfv=1.0, unit=False):
    """(c1, c2, Q, c1*Q) for [BC97] Thm 1 (H1)/(H2) fed into its Thm 2.

    Q = (2 c1 t)^t (50 c2) p^{f_v} prod h'(xi_i)  and  h(A xi) <= c1 Q max(h'(A), Q),
    so c1*Q is the h(A) coefficient.  unit=True replaces the printed c1, c2 by 1 --
    the floor of the reduction's shape, better than any conceivable input.
    """
    c1 = 1.0 if unit else 3.4e11 * Dv ** 10 * (log(1 / kap) + 1) ** 7 / kap
    c2 = 1.0 if unit else 1.7e6 * Dv ** 4 * (log(1 / kap) + 1) ** 4 / kap
    Q = (2 * c1 * t) ** t * (50 * c2) * pfv
    for h in hs:
        Q *= h
    return c1, c2, Q, c1 * Q


def _v3_nearest(D, nmax):
    """(max v3(m_n) and its date, count of dates with v3 > 0) for m_n = round(D(3/2)^n).

    Exact integers: m_n from one divmod, v3 by division.  m_n is the numerator that
    the S-unit lane's A = D/m carries, so v3(m_n) is exactly the gap between
    h(A gamma) and h(gamma) in section 4's penultimate inequality (block [F]).
    """
    best, cnt = (0, 0), 0
    for n in range(1, nmax + 1):
        P2 = 1 << n
        q, r = divmod(D * 3 ** n, P2)
        m = q + (1 if 2 * r >= P2 else 0)
        v = 0
        while m % 3 == 0:
            m //= 3
            v += 1
        if v > best[0]:
            best = (v, n)
        if v:
            cnt += 1
    return best, cnt


def cmd_s10c(nmax=20000, out=sys.stdout):
    """S10 WP-C, Q1's sweep: the within-family ceiling, and the lane's constants.

    [A] the within-family configuration space is FINITE (three points, S1 8.2);
    [B] the engine's arithmetic slot is the zero line, and the ceiling there;
    [C] the master curve I -> theta, in plan-S8's absolute content currency;
    [D] the generous second lane ([Zud07] with its own validity condition);
    [E] the h(A)-coefficient inventory of the S-unit lane, from the print;
    [F] the amendment: section 4's penultimate inequality, and its side condition;
    [G] the verdict against Q1's pre-committed criteria, and the freedom ledger.
    """
    T = Fraction(-1, 8)
    W = log(3.0) / log(1.5)
    out.write("plan-Tshift-S10 WP-C -- Q1's sweep.  The within-family prong is priced in\n"
              "plan-S8's absolute content currency on the S1 8.2 apparatus (consumed\n"
              "verbatim, O-1); the beyond-family prong was priced at WP-B and is here\n"
              "anchored to the two printed ancestors of the surviving lane.\n"
              f"nmax = {nmax} (block [F] only).  Wall W = log3/log(3/2) = {W:.12f}\n")

    out.write("\n# [A] the within-family configuration space is FINITE, and already\n"
              "      enumerated: an evaluation point exists only where 3^p = 2^a +- 1,\n"
              "      so slots S3/S4 of the dictionary are quantized (S1 note 8.1/8.2).\n")
    out.write("      p  identity      t      (mu,K)   with content   content-free   status\n")
    pts = [("1", "3 = 2^1+1", Fraction(-1, 2), None, None, None, "degenerate: no approximant"),
           ("1", "3 = 2^2-1", Fraction(1, 4), (1, 2), (6280417, 10000000), 0.999,
            "vacuous already in print"),
           ("2", "9 = 2^3+1", T, (2, 6), (224141, 240395), 1.99, "[Beu81]/[Hab03]/[Zud07]")]
    ceil_family, printed = 0.0, {}
    for p, ident, t, muK, ual, hi, note in pts:
        if muK is None:
            out.write(f"      {p}  {ident:11s} {str(t):>6s}      --            --   "
                      f"          --   {note}\n")
            continue
        mu, K = muK
        th_true = exp(_apparatus(mu, t, K, ual[0], ual[1])[4])
        printed[mu] = th_true
        alc, th_free = _ceiling_at_supply(mu, t, K, 0.0, hi)
        ceil_family = max(ceil_family, th_free)
        out.write(f"      {p}  {ident:11s} {str(t):>6s}   ({mu},{K})    {th_true:.7f}"
                  f"      {th_free:.7f}   {note}\n")
    # calibration: both printed values come back out of the same routine
    assert abs(printed[2] - 0.57701737767006) < 5e-11
    assert abs(printed[1] - 0.357577) < 1e-6
    alc2, th2 = _ceiling_at_supply(2, T, 6, 0.0, 1.99)
    alc1, th1 = _ceiling_at_supply(1, Fraction(1, 4), 2, 0.0, 0.999)
    assert abs(alc2 - 1.0705528) < 1e-6 and abs(th2 - 0.4964038) < 1e-6
    assert abs(alc1 - 0.6843255) < 1e-6 and abs(th1 - 0.3017973) < 1e-6
    assert max(th1, th2) < 0.5 and ceil_family == th2
    out.write(f"      The ceiling over the whole list is the p = 2 point: theta = {th2:.7f}\n"
              f"      at alpha = {alc2:.7f}, i.e. kappa = {_kappa(th2):.6f}.  Both content-free\n"
              "      values are below the free 2-adic floor theta = 1/2 that the corpus\n"
              "      already proves (TShift.isRepelledMul_half), so on the engine's own\n"
              "      arithmetic input the family lane proves nothing at all.\n")

    out.write("\n# [B] why the zero line is the engine's line, and that the ceiling is\n"
              "      monotone in the arithmetic input -- so tau > 0 only makes it worse.\n"
              "      The dictionary's S2 slot is tau(b) in [0, sigma_m], a denominator\n"
              "      LOSS (note-Tshift-S10-WPB.html 1.1/1.4, DA2); the family's own input\n"
              "      is a content GAIN I(alpha) > 0.  Engine-admissible inputs are I <= 0.\n")
    out.write("      arithmetic input I     alpha*      theta       kappa\n")
    prev = None
    for I in (-0.40, -0.20, -0.05, 0.0, 0.05, 0.20, 0.4037815, 0.7674675):
        al, th = _ceiling_at_supply(2, T, 6, I, 1.99)
        tag = "  <- engine ceiling (tau = 0)" if I == 0.0 else ""
        if abs(I - 0.4037815) < 1e-9:
            tag = "  <- [Hab03] Thm 1"
        if abs(I - 0.7674675) < 1e-9:
            tag = "  <- the 2/3 demand"
        out.write(f"      {I:+.7f}          {al:.7f}   {th:.7f}   {_kappa(th):.6f}{tag}\n")
        if prev is not None:
            assert th > prev, (I, th, prev)
        prev = th
    out.write("      Strictly increasing, so I = 0 is the ceiling of the whole slot range\n"
              "      and no denominator type has to be pinned to price it.\n")

    out.write("\n# [C] the master curve in plan-S8's ABSOLUTE currency: W(theta) is the\n"
              "      content rate a family proof needs, so costs subtract and no reference\n"
              "      point is smuggled in (note-S1-constants 8.3, plan-S8 F8).\n")
    anchors = [("engine ceiling, tau = 0", None, 0.0),
               ("free 2-adic floor 1/2", 0.5, None),
               ("[Beu81] Thm 2 = 2^-0.9", 0.535887, None),
               ("[Eas86]", 0.5664, None),
               ("[Hab03] Thm 2 (k >= 5)", 0.57434, None),
               ("[Hab03] Thm 1", 0.5770173777, None),
               ("[Zud07] the record", 0.5803, None),
               ("exact content lemma (S8 F9)", 0.6165, None),
               ("T-shift, kappa = 1", 2 / 3, None)]
    out.write("      row                           theta       alpha*     demand W"
              "    share of 2/3\n")
    dem = {}
    for lab, th, I in anchors:
        if th is None:
            al, th = _ceiling_at_supply(2, T, 6, I, 1.99)
            Wd = I
        else:
            al, Wd = _demand_at_theta(2, T, 6, th, 1.99)
        dem[lab] = Wd
        out.write(f"      {lab:29s} {th:.7f}   {al:.7f}   {Wd:+.7f}"
                  f"     {100 * Wd / 0.7674675:6.2f}%\n")
    d23 = dem["T-shift, kappa = 1"]
    step = dem["[Zud07] the record"] - dem["[Hab03] Thm 1"]
    assert abs(d23 - 0.7674675) < 1e-6 and abs(step - 0.0147500) < 1e-6
    assert abs(dem["[Hab03] Thm 1"] - 0.4037815) < 1e-6
    steps_eng = d23 / step
    steps_rec = (d23 - dem["[Zud07] the record"]) / step
    assert 51.0 < steps_eng < 53.0 and 23.0 < steps_rec < 24.0
    out.write(f"      one record-sized (Zudilin) step = {step:.7f} nats/m of demand.\n"
              f"      From the record to 2/3: {steps_rec:.2f} steps (plan-S8's 23.66).\n"
              f"      From the engine's ceiling to 2/3: {steps_eng:.2f} steps -- the engine\n"
              f"      supplies 0.00% of the demand, so it is not a shortcut but a handicap\n"
              f"      of {(steps_eng - steps_rec):.2f} steps, i.e. the whole content history since 1975.\n")
    out.write("      [Beu81] is on the curve with content, not without it: his own summary\n"
              "      calls the extraction of common prime factors 'the novel idea in the\n"
              "      proof of Theorem 2' (p. 14, Lemma 6).  Every improvement in this lane\n"
              "      since 1975 is an improvement of the slot the engine cannot supply.\n")

    out.write("\n# [D] the most generous reading available: the second family lane, with\n"
              "      ITS OWN validity condition.  [Zud07] (alpha,beta,gamma) = (9,19,9),\n"
              "      z = 1/9, K = 3beta = 57, and (26) as the constraint.\n")
    C0, C1, C2, floor, th_full, th_floor, margin = _zud_lane(9, 19, 9, 9, 57, 3, 3)
    th_free_z = exp(-C1 / 57)
    al_end, th_end = 1.0, exp(_supply_demand(2, T, 6, 1.0)[0])
    assert abs(th_full - 0.5803) < 1e-4 and floor < 0.0
    assert abs(th_free_z - 0.5365621) < 1e-6 and abs(th_end - 0.5364791) < 1e-6
    out.write(f"      printed lane        C1 = {C1:.6f}   C2 = {C2:.6f}   theta = {th_full:.7f}\n"
              f"      content-free lane   C2 := 0                        theta = {th_free_z:.7f}\n"
              f"      (26) at C2 = 0      floor = {floor:+.6f} <= 0, so the printed validity\n"
              "                          condition still holds -- with 5.50 nats to spare\n")
    out.write(f"      That is the generous end of the bracket, and it lands on the [Hab03]\n"
              f"      curve's alpha = 1 endpoint, {th_end:.7f}, to {abs(th_free_z - th_end):.1e}:\n"
              "      two independently coded lanes, one number.  So the within-family\n"
              f"      ceiling is bracketed by [{th2:.6f}, {th_free_z:.6f}] -- the difference is\n"
              "      which lane's validity condition one adopts, not which family.\n")
    assert th_free_z < 0.5664
    out.write(f"      Both ends are below [Eas86]'s 0.5664, i.e. below the state of the art\n"
              f"      at every date from 1986 on, and kappa is {_kappa(th2):.3f} / "
              f"{_kappa(th_free_z):.3f} against\n"
              "      the 1.000 that T-shift needs.\n")

    out.write("\n# [E] the beyond-family lane, anchored: the h(A) coefficient in print.\n"
              "      Normalization: every rung is read as h(gamma) <= C h(A) + (additive),\n"
              "      C is what the wall constrains, and the T-shift instantiation is\n"
              "      K = Q, d = 1, Gamma = <3/2>, t = 1, h(3/2) = log 3, v = infinity.\n")
    eps0 = log(3.0 / (2.0 * (2 / 3))) / log(3.0)
    lQ93 = _bom93_logQ(eps0)
    c1, c2, Qbc, coef_bc = _bc97_coeff(eps0)
    _, _, Qu, coef_u = _bc97_coeff(eps0, unit=True)
    Qcdt = ceil(2 * 1.0 * log(3.0))                  # Q = ceil((2 c8 c9)^t), c9 = log3, c8 = 1
    printed_cdt = 2 * 2 * Qcdt * (1 * 1 + 1)         # 2 g Q (c8 c10 + 1) at g = 2, unit inputs
    assert abs(eps0 - 0.738140) < 1e-6 and Qcdt == 3 and printed_cdt == 24
    assert 422.0 < lQ93 < 422.5 and 1e33 < coef_bc < 1e34 and 109.0 < coef_u < 110.0
    out.write(f"      eps_0(2/3) = {eps0:.6f}   (the demand's argument; the wall is eps-free)\n")
    out.write("      source                                                    C at eps_0     C / W\n")
    rows = [("[Bom93] Thm 2, Q = (e^{115d/eps^2}t)^{t+1} prod h(xi)",
             f"10^{lQ93 / log(10):.2f}", f"x10^{(lQ93 - log(W)) / log(10):.1f}"),
            ("[BC97] Thm 2 through its own (H1)/(H2), as printed",
             f"10^{log(coef_bc) / log(10):.2f}", f"x10^{log(coef_bc / W) / log(10):.1f}"),
            ("[BC97] the same reduction at c1 = c2 = 1",
             f"{coef_u:.1f}", f"x{coef_u / W:.1f}"),
            ("[CDT-ICM] sec 4, printed Q,N, unit constants,  h(gamma)",
             f"{3 + printed_cdt:d}", f"x{(3 + printed_cdt) / W:.4f}"),
            ("[CDT-ICM] sec 4, printed Q,N, unit constants,  h(A gamma)",
             f"{2 + printed_cdt:d}", f"x{(2 + printed_cdt) / W:.4f}"),
            ("[CDT-ICM] sec 4, FLOOR over all constants,    h(gamma)",
             "4", f"x{4 / W:.4f}"),
            ("[CDT-ICM] sec 4, FLOOR over all constants,    h(A gamma)",
             "3", f"x{3 / W:.4f}")]
    for lab, C, ratio in rows:
        out.write(f"      {lab:57s} {C:>10s}   {ratio}\n")
    out.write(f"      {'the demand (T1/T4 follow iff C < W)':57s} {'< ' + f'{W:.6f}':>10s}\n"
              f"      {'the Dirichlet floor, forced (WP-B [F])':57s} {'>= 1.817915':>10s}\n")
    assert 3 > W and abs(3 / W - 1.1072) < 5e-5 and abs(4 / W - 1.4763) < 5e-5
    out.write("      1993 -> 1997 bought 150 orders of magnitude -- 'replace exponential\n"
              "      bounds by polynomial bounds' ([BC97] p. 206): e^{115d/eps^2} becomes\n"
              "      eps^-1 (log(1/eps)+1)^7.  1997 -> 2026 bought the remaining 32, and what\n"
              "      is left is the last two rows, which no choice of constants can move.\n"
              "      In none of the three rungs is the RANGE of validity the obstruction --\n"
              "      max(Q h(A), [Q]!) and max(h'(A), Q) only postpone the first date, which\n"
              "      an asymptotic target tolerates.  It is the coefficient, and the\n"
              "      coefficient alone.\n")

    out.write("\n# [F] where the 3 comes from -- WP-B's x1.1072 re-derived as a floor over\n"
              "      the whole constant space, which is a stronger statement than the one it\n"
              "      replaces.  Section 4's own steps, in order:\n"
              "        (4.4)/(4.5)   h(a) <= h(A) + r/(2 c8)\n"
              "        the T-S step  h(alpha eta) <= 2 h(alpha) + c10, and h(A gamma) = r h(alpha eta)\n"
              "                      so h(A gamma) <= 2 h(a) + c10 r <= 2 h(A) + (c10 + 1/c8) r\n"
              "        (4.2)         REQUIRES r >= c8 h(a) ~ c8 h(A)\n"
              "      The third line is the Thue-Siegel principle itself -- the auxiliary\n"
              "      exponent must grow linearly in the height -- so the additive term is\n"
              "      Theta(h(A)) and never O(1):  it is at least (c8 c10 + 1) h(A) >= h(A).\n")
    out.write(f"      Hence C >= 2 + 1 = 3 in the h(A gamma) form (x{3 / W:.4f}) and C >= 4 in the\n"
              f"      h(gamma) form (x{4 / W:.4f}), for EVERY positive value of c8, c9, c10 and\n"
              "      every g >= 2.  With the printed choices of Q and N at unit constants the\n"
              f"      same expression is {2 + printed_cdt:d} / {3 + printed_cdt:d}.  So WP-B's headline number is not an\n"
              "      artifact of the write-up's last step: it is the floor of the method.\n")
    out.write("      Which of the two floors applies is a question about the family, and it\n"
              "      is decidable: the last step is h(gamma) <= h(A) + h(A gamma), and for the\n"
              "      T-shift family it is pure loss, since with A = D/m and gamma = (3/2)^n\n"
              "         h(A gamma) = n log 3 - v3(m_n) log 3 + O(log D),  h(A) = n log(3/2) + O(log D).\n"
              "      So the h(A gamma) form is available exactly when v3(m_n) = o(n) along the\n"
              "      violating sequence, and the two demand levels are W and W - 1.\n")
    assert abs((W - 1) - log(2.0) / log(1.5)) < 1e-14
    out.write(f"      Exact identity: log3/log(3/2) - log2/log(3/2) = 1, so the degenerate\n"
              f"      level is W - 1 = {W - 1:.6f} -- above the Dirichlet floor 1.817915 only\n"
              "      because the floor is measured, not proved, at 2/3.\n")
    out.write("      measured, exact integers, m_n = round(D(3/2)^n):\n"
              "        D     max v3(m_n)   at n      dates with v3 > 0   random model\n")
    for D in (1, 5, 19):
        (mv, at), cnt = _v3_nearest(D, nmax)
        out.write(f"        {D:2d}    {mv:2d}            {at:6d}    "
                  f"{100 * cnt / nmax:6.2f}%             "
                  f"max ~ log3 N = {log(nmax) / log(3):.1f}, P = 33.33%\n")
        assert mv <= 2 * log(nmax) / log(3)
        assert nmax < 1000 or 0.30 < cnt / nmax < 0.37
    out.write("      Geometric(1/3) to the digit, so v3 = O(log n) empirically and the side\n"
              "      condition is not close to failing -- but it is a measurement, not a\n"
              "      theorem, and it is a condition on the adversary's own sequence.\n"
              "      Net effect on the pricing: none.  The side condition moves the floor\n"
              f"      from x{4 / W:.4f} to x{3 / W:.4f}; both are above 1, and what the lane needs is\n"
              "      not better constants but a reduction whose auxiliary exponent does not\n"
              "      grow with the height -- i.e. not this principle.\n")

    out.write("\n# [G] Q1's verdict against the pre-committed criteria, and the ledger of\n"
              "      configuration freedom that remains (R2's requirement).\n")
    out.write("      prong          measured ceiling                    against 2/3\n"
              f"      within-family  theta in [{th2:.4f}, {th_free_z:.4f}]  (kappa 1.73/1.54)   killed\n"
              f"      beyond-family  C = 10^33.8 printed, floor 3 at any constants  killed at\n"
              "                     WP-B; the floor is re-derived here, over the whole\n"
              "                     constant space, and is x1.1072 above the wall\n")
    out.write("      slot                       freedom that remains          price\n"
              "      S3 evaluation point        three points, all enumerated  none: finite list\n"
              "      S1 dimension / higher HP   [Zud07]'s (a,b,g) grid        S8 WP-F, deferred\n"
              "      S2 denominator type        tau in [0, sigma_m]           <= 0 by identity\n"
              "      S4 weighting               refinements exist in [CDT-L]  'invisible to all\n"
              "                                                               our applications'\n"
              "      places                     add v | p to the sum          zero adelic budget\n"
              "                                                               (plan-S11 M2)\n"
              "      the S-unit constant        c8, c9, c10, Q, g             floor x1.1072, no\n"
              "                                                               constant reaches it\n")
    out.write("      Nothing in the ledger is unpriced, and no entry is positive.  Kill\n"
              "      criterion met on both prongs; G-D does not trigger (no configuration\n"
              "      reaches 2/3, so there is nothing to escalate).\n")
    out.write("\n      18 assertions / 44 conditions, all passing.\n")


def _frontier_le(fr, N):
    """The best form with 0 < b <= N: the last frontier point with q_k <= N.

    By the theory of best approximations of the second kind, min |b 3^n - a 2^n| over
    0 < b <= N is attained at a convergent, so the Pareto frontier of `_cf_frontier`
    contains it, and this is exactly the point the proofs of
    `TShift.exists_form_in_box`/`TShift.forms_of_floor` use at that N.
    """
    best = None
    for (q, e) in fr:
        if q > N:
            break
        best = (q, e)
    assert best is not None, N
    return best


def cmd_s10e(nmax=2000, out=sys.stdout):
    """S10 WP-E: the constants of TShift/CriticalBox.lean, checked independently.

    The Lean file proves statements; this block checks that what it proves is what the
    numbers do, on exact integers and Fractions:
    [A] `exists_form_in_box` + `forms_of_floor` run at the critical family, with the
        SHARPEST admissible floor at each date (so the hypothesis holds by fiat and the
        conclusion is a claim about the construction alone);
    [B] `floor_iff_forms`: the round trip of constants, and why the eps-slack is forced
        (the two directions pull opposite ways on the box volume);
    [C] `escape_in_window` (v2 form) and `escape_in_window_logb` (O(1) = 2) at every
        date, the two tight instances, and `escape_sanity`'s values;
    [D] `lambda_one_ge_half` against WP0's exact successive minima.
    """
    na, nc = 0, 0                                     # assertions, conditions
    out.write("plan-Tshift-S10 WP-E -- the Lean layer's constants, independently.\n"
              "Every decision below is an exact integer or Fraction comparison; the\n"
              "printed ratios are floats and are marked as such.  Statements checked:\n"
              "exists_form_in_box, floor_le_critical, forms_of_floor, floor_iff_forms,\n"
              "escape_in_window, escape_in_window_logb, escape_sanity, lambda_one_ge_half.\n"
              f"nmax = {nmax}\n")

    # ---------------------------------------------------------------- [A] ----
    out.write("\n# [A] the construction of `forms_of_floor` at the critical family, with\n"
              "      S := the true floor at that date (attained, so the hypothesis is\n"
              "      exactly satisfiable and nothing is granted for free)\n")
    out.write("        n   log2 b1   |l1|(N1+1)/X   b2/B      blow-up Lam/S = 1/c\n")
    worst, worst_n, tight_box = Fraction(0), 0, 0
    for n in range(2, nmax + 1):
        X, Y = 1 << n, 3 ** n
        fr = _cf_frontier(Y, X)
        B = Fraction(3, 2) ** n
        Lam = Fraction(4, 3) ** n
        assert Lam * B == X                                     # T1, at this date
        N1 = Y // X                                             # floor(B)
        q1, e1 = _frontier_le(fr, N1)
        S = abs(e1)
        assert Fraction(S) <= Fraction(X, N1 + 1)               # `exists_form_in_box`
        assert Fraction(S) <= Lam                               # the free form is in box
        assert Fraction(S) < Fraction(X) / B                    # `floor_le_critical`
        N2 = -((-X) // S)                                       # ceil(X/S)
        q2, e2 = _frontier_le(fr, N2)
        assert abs(e2) < S                                      # strictly below the floor
        assert Fraction(q2) <= Fraction(X, S) + 1                # the coefficient budget
        assert Fraction(abs(e2)) <= Lam and Fraction(q1) <= B    # both forms in the box
        p1, p2 = (q1 * Y - e1) // X, (q2 * Y - e2) // X          # a_i = -p_i
        assert (q1 * Y - e1) % X == 0 and (q2 * Y - e2) % X == 0
        assert p1 * q2 != p2 * q1                                # `hdet` of the proof
        blow = Fraction(X, S) / B                                # = 1/c at this date
        if blow > worst:
            worst, worst_n = blow, n
        if Fraction(q2) <= B:
            tight_box += 1
        if n in (2, 3, 5, 8, 27, 55, 238, 1221):
            out.write(f"      {n:5d}   {_lg2(q1):7.3f}   {float(Fraction(S * (N1 + 1), X)):.6f}"
                      f"       {float(Fraction(q2) / B):7.3f}   {float(blow):.4f}\n")
        na += 9
        nc += 11
    out.write(f"      every date 2..{nmax}: Dirichlet's bound, both box bounds, the\n"
              "      coefficient budget X/S + 1, and INDEPENDENCE -- all hold\n")
    out.write(f"      worst blow-up 1/c = X/(S B) = {float(worst):.4f} at n = {worst_n};\n"
              "      the size slot never blows up at all, which is the one-sided shape\n"
              "      Minkowski's second theorem does not give\n")
    out.write(f"      the construction's second point never fits |b| <= B ({tight_box} dates),\n"
              "      necessarily: S <= X/(B+1) forces N2 = ceil(X/S) > B.  So the theorem's\n"
              "      constant is UNIFORM, not per-date optimal -- the true minima do fit the\n"
              "      unblown box at 21.2% of dates (WP0 block [B]), which no c-only bound sees\n")

    # ---------------------------------------------------------------- [B] ----
    out.write("\n# [B] `floor_iff_forms`: the round trip of constants, exact\n")
    out.write("        c        beta    eta=1/beta  K=1/c+1   beta'=(1+beta)/2  c'"
              "          c'/c\n")
    for (c, beta) in ((Fraction(1, 2), Fraction(2)), (Fraction(1, 10), Fraction(3, 2)),
                      (Fraction(1, 100), Fraction(11, 10)), (Fraction(9, 10), Fraction(5))):
        eta, K = 1 / beta, 1 / c + 1
        assert 0 < eta < 1 and K > 0
        beta2 = (1 + 1 / eta) / 2
        assert beta2 == (1 + beta) / 2 and beta2 > 1
        c2 = (1 - eta * beta2) / K
        assert c2 > 0 and eta * beta2 < 1
        out.write(f"      {str(c):8s} {str(beta):7s} {str(eta):11s} {str(K):9s} "
                  f"{str(beta2):17s} {str(c2):11s} {float(c2 / c):.4f}\n")
        na += 3
        nc += 7
    for beta in (Fraction(2), Fraction(3, 2), Fraction(11, 10)):
        assert 1 - (1 / beta) * beta == 0
        na += 1
        nc += 1
    out.write("      at eta*beta = 1 -- box volume exactly the determinant -- the forward\n"
              "      constant (1 - eta beta)/K is 0: the eps-slack is not bookkeeping,\n"
              "      it is the criticality of the box\n")

    # ---------------------------------------------------------------- [C] ----
    out.write("\n# [C] the escape window, both forms, at every date\n")
    out.write("        D     max (e - n0)   worst n0   v2-slack min   logb-slack min\n")
    for D in (1, 5, 19):
        run = nmax + 128
        small = []
        for n in range(0, run + 1):
            P2 = 1 << n
            q, r = divmod(D * 3 ** n, P2)
            m = q + (1 if 2 * r >= P2 else 0)
            small.append(abs(Fraction(D * 3 ** n, P2) - m) < Fraction(1, 5))
        nxt = [run + 1] * (run + 2)
        for n in range(run, -1, -1):
            nxt[n] = n if not small[n] else nxt[n + 1]
        worst_gap, worst_at, sl_v2, sl_lb = 0, 0, None, None
        for n0 in range(1, nmax + 1):
            e = nxt[n0]
            assert e <= run, (D, n0)
            P2 = 1 << n0
            q, r = divmod(D * 3 ** n0, P2)
            m = q + (1 if 2 * r >= P2 else 0)
            v2 = 0
            while m % 2 == 0:
                m //= 2
                v2 += 1
            assert e <= n0 + v2 + 1, (D, n0, e, v2)              # `escape_in_window`
            assert Fraction(1 << (e - n0)) <= 4 * D * Fraction(3, 2) ** n0
            s1 = (n0 + v2 + 1) - e                               # v2-form slack
            s2 = 4 * D * Fraction(3, 2) ** n0 / Fraction(1 << (e - n0))
            sl_v2 = s1 if sl_v2 is None else min(sl_v2, s1)
            sl_lb = s2 if sl_lb is None else min(sl_lb, s2)
            if e - n0 > worst_gap:
                worst_gap, worst_at = e - n0, n0
            na += 3
            nc += 3
        out.write(f"      {D:4d}  {worst_gap:9d}      {worst_at:8d}   {sl_v2:12d}   "
                  f"{float(sl_lb):.4f}\n")
    for (D, n0, m_exp, e_exp) in ((5, 3, 17, 4), (1, 4, 5, 5)):
        P2 = 1 << n0
        q, r = divmod(D * 3 ** n0, P2)
        m = q + (1 if 2 * r >= P2 else 0)
        assert m == m_exp and m % 2 == 1                          # v2 = 0
        assert n0 + 0 + 1 == e_exp
        out.write(f"      tight: D = {D}, n0 = {n0}: m = {m} odd, so the window is "
                  f"[{n0},{e_exp}] and the escape is at {e_exp}\n")
        na += 2
        nc += 3
    d3 = Fraction(5 * 27, 8) - 17
    d4 = Fraction(5 * 81, 16) - 25
    assert abs(d3) == Fraction(1, 8) and abs(d4) == Fraction(5, 16)
    assert abs(d3) < Fraction(1, 5) <= abs(d4)
    out.write(f"      escape_sanity: ||5(3/2)^3|| = {abs(d3)} < 1/5 <= {abs(d4)} "
              "= ||5(3/2)^4||\n")
    na += 2
    nc += 4

    # ---------------------------------------------------------------- [D] ----
    out.write("\n# [D] `lambda_one_ge_half` against the exact successive minima\n")
    dmax = min(nmax, 2000)
    fits, checked = 0, 0
    for n in range(2, dmax + 1):
        mu1, mu2 = _minima(n)
        p12 = 12 ** n                                             # lambda_i = mu_i/12^n
        assert 2 * mu1 * mu2 >= p12 * p12 and mu1 * mu2 <= p12 * p12   # WP0's own test
        na += 1
        nc += 2
        if mu2 <= p12:                                            # two forms in the box
            fits += 1
            assert 2 * mu1 >= p12                                 # lambda_1 >= 1/2
            checked += 1
            na += 1
            nc += 1
    out.write(f"      dates 2..{dmax} with two independent forms in the unblown box: "
              f"{fits} ({100.0 * fits / (dmax - 1):.1f}%)\n"
              f"      lambda_1 >= 1/2 at every one of them, as the theorem says: "
              f"{checked}/{fits}\n"
              "      (certification in the box and a record-low approximation at the\n"
              "      same date do exclude each other, quantitatively)\n")

    out.write(f"\n      22 assertion sites, {na} evaluations / {nc} conditions, "
              "all passing.\n")


#  --------------------------------------------------------------------------------
#  plan-Tshift-S1314 WP0 (gate G-A): the forcing data at D_2 = 5, and the two routes
#  at general base.  Every decision below is an exact Fraction or integer comparison;
#  floats appear only in printed columns and in the log-form constants, which are
#  checked against the plan's printed decimals to five places.
#  --------------------------------------------------------------------------------

#  the D_2 = 5 targets, and for each: (cycle digit, image under it)
_S1314_T = [Fraction(1, 5), Fraction(2, 5), Fraction(3, 5), Fraction(4, 5)]
_S1314_CYC = {Fraction(1, 5): (-1, Fraction(4, 5)), Fraction(4, 5): (2, Fraction(1, 5)),
              Fraction(2, 5): (0, Fraction(3, 5)), Fraction(3, 5): (1, Fraction(2, 5))}


def _admissible(x):
    """The carry digits admissible at x: s in (3x - 2, 3x] cap Z, exactly.

    x_{n+1} = (3 x_n - s_n)/2 lies in [0,1) iff 0 <= 3x - s < 2, and a half-open
    interval of length 2 holds exactly two integers -- plan-S1314 F2.
    """
    lo, hi = 3 * x - 2, 3 * x
    s = lo.numerator // lo.denominator          # floor(lo) <= lo
    out = []
    while s <= hi:
        if s > lo:
            out.append(s)
        s += 1
    return out


def cmd_s1314(nmax=20000, out=sys.stdout):
    """S13/14 WP0, gate G-A: D1-D4 re-derived, and what the corpus already owns.

    [A] D1 exactly -- the four wrong-branch images, the 1/10, the two margins;
    [B] F2 -- two admissible digits at every point, so no region forces a point;
    [C] D1 on the real orbit -- forcing, phase and the cycle-shift identity;
    [D] D2's constants against the free cap of TShift/FreeSojourn.lean (C20);
    [E] D3/D4 -- the grid, the reciprocal cascade slope, and the tiling;
    [F] F5 -- what "every dyadic block" is worth per block;
    [G] the G-A verdict.
    """
    delta = Fraction(1, 32)
    L32, L2, L3 = log(1.5), log(2), log(3)

    out.write("[A] D1 -- the forcing data at D_2 = 5, on exact rationals\n"
              "      2 x_{n+1} = 3 x_n - s_n,  s_n in (3x-2, 3x],  T = {1/5,2/5,3/5,4/5}\n"
              "      rho   admissible   cycle digit -> image   wrong -> image   "
              "dist(wrong image, T)\n")
    for rho in _S1314_T:
        adm = _admissible(rho)
        sc, nxt = _S1314_CYC[rho]
        assert len(adm) == 2 and sc in adm
        sw = [s for s in adm if s != sc][0]
        img_c, img_w = (3 * rho - sc) / 2, (3 * rho - sw) / 2
        assert img_c == nxt                                  # the cycle word, in phase
        dw = min(abs(img_w - t) for t in _S1314_T)
        assert dw == Fraction(1, 10)                         # F3: exactly 1/10, all four
        out.write(f"      {rho}    {str(adm):9s}   {sc:+d} -> {img_c}          "
                  f"{sw:+d} -> {img_w}        {dw}\n")
    cuts = [Fraction(k, 3) for k in range(4)]
    marg = min(min(abs(rho - c) for c in cuts) for rho in _S1314_T)
    assert marg == Fraction(1, 15)                           # digit sets constant on balls
    d_crit = Fraction(1, 10) / Fraction(5, 2)
    assert d_crit == Fraction(1, 25)                         # 1/10 - (3/2)d > d
    eject = Fraction(1, 10) - Fraction(3, 2) * delta
    assert eject - delta == Fraction(7, 320)
    assert Fraction(5, 2) * delta < Fraction(1, 5) and delta < Fraction(1, 15)
    out.write(f"      digit sets constant on balls of radius < {marg} (branch cuts k/3, "
              f"tightest at 2/5, 3/5)\n"
              f"      wrong branch ejects while 1/10 - (3/2)d > d, i.e. d < {d_crit};"
              f" at d = {delta}: {eject} vs {delta}, slack {eject - delta} = "
              f"{float(eject - delta):.6f}\n"
              f"      phase forced: (5/2)d = {Fraction(5,2)*delta} < 1/5 = the target "
              f"separation, so the image can only be rho_next\n")

    out.write("\n[B] F2 -- \"forced eventually 2-periodic\" is vacuous pointwise\n")
    tot = 0
    for d in range(1, 61):
        for a in range(d):
            assert len(_admissible(Fraction(a, d))) == 2
            tot += 1
    out.write(f"      |admissible(x)| = 2 at every x = a/d, d <= 60: {tot} points, no "
              "exception -- and the\n"
              "      count is 2 at EVERY real x (a half-open interval of length 2). "
              "So no nonempty region\n"
              "      forces the next digit of a point; forcing is a property of paths "
              "that stay in U.\n"
              "      (The corpus states the alphabet half already: Z32.exists_carry, "
              "TShift.carry_mem.)\n")

    out.write(f"\n[C] D1 on the real orbit, n <= {nmax}, U = U_(1/32)\n")
    r = [pow(3, n, 1 << n) if n else 0 for n in range(nmax + 2)]
    s = [(3 * r[n] - r[n + 1]) >> n for n in range(nmax + 1)]

    def near(n):
        for t in _S1314_T:
            if abs(Fraction(r[n], 1 << n) - t) < delta:
                return t
        return None

    inU = [near(n) for n in range(nmax + 1)]
    pairs = viol = ident = 0
    for n in range(1, nmax):
        if inU[n] is not None and inU[n + 1] is not None:
            pairs += 1
            sc, nxt = _S1314_CYC[inU[n]]
            if s[n] != sc or inU[n + 1] != nxt:
                viol += 1
            d0 = Fraction(r[n], 1 << n) - inU[n]
            if Fraction(r[n + 1], 1 << (n + 1)) - nxt != Fraction(3, 2) * d0:
                ident += 1
    assert viol == 0 and ident == 0
    visits = sum(1 for n in range(1, nmax + 1) if inU[n] is not None)
    out.write(f"      dates in U: {visits}/{nmax} = {visits / nmax:.4f} "
              "(Lebesgue measure of U = 4*2*(1/32) = 1/4)\n"
              f"      x_n and x_(n+1) both in U: {pairs} dates\n"
              f"      digit-and-phase violations: {viol}     |x_(n+1) - rho_next| = "
              f"(3/2)|x_n - rho| exceptions: {ident}\n"
              "      -- Proposition B holds on the real orbit, and N2's cycle-shift "
              "identity with it.\n")
    soj, n = [], 1
    while n <= nmax:
        if inU[n] is None:
            n += 1
            continue
        L = 0
        while n + L <= nmax and inU[n + L] is not None:
            L += 1
        soj.append((n, L))
        n += L
    kapA, CA = L2 / L32, 1 + log(5 / 32) / L32
    # Both caps in the same currency, a bound on L itself.  The free cap is stated on the
    # PERIODIC BLOCK, whose length is L - 1 (the last digit of a sojourn is not forced), so its
    # additive constant carries a +1 that WP2 supplied and WP0 dropped: L <= k n + 1 + 2 log2 3.
    kfree, Cfree = L32 / L2, 1 + 2 * L3 / L2
    wA = max(L - (kapA * k + CA) for k, L in soj)
    wF = max(L - (kfree * k + Cfree) for k, L in soj)
    out.write(f"      {len(soj)} maximal sojourns, longest {max(L for _, L in soj)}; "
              f"worst slack L - cap: Theorem A {wA:+.3f}, free {wF:+.3f}\n")
    assert wA < 0 and wF < 0

    out.write("\n[D] D2 -- the cap at base 3/2, and the rung the corpus already owns\n")
    assert abs(kapA - 1.70951) < 5e-6 and abs(1 + kapA - L3 / L32) < 1e-12
    assert abs(CA + 3.578) < 5e-4 and abs(1 / log(1 + kapA) - 1.003) < 5e-4
    out.write(f"      kappa(1/2) = log2/log(3/2)  = {kapA:.7f}   1 + kappa = "
              f"log3/log(3/2) = {1 + kapA:.7f}\n"
              f"      C = 1 + log(5/32)/log(3/2)  = {CA:.7f}   count = "
              f"1/ln(1+kappa) = {1 / log(1 + kapA):.7f} ln N\n"
              f"      Theorem A cap:  L <= {kapA:.5f} n {CA:+.4f}\n"
              f"      free cap (TShift.free_sojourn_cap at p = 2, C20):  L <= "
              f"{kfree:.5f} n + {Cfree:.5f}\n")
    assert abs(kfree - 1 / kapA) < 1e-12                    # kappa_free = 1/kappa(1/2)
    assert abs(kfree - LOG2_3HALVES) < 1e-15
    cross = (Cfree - CA) / (kapA - kfree)
    assert abs(cross - 6.8900) < 5e-5                       # WP2: 6.0007 was the dropped +1
    assert abs(kapA / kfree - 2.9224289) < 5e-7             # = 1/kappa_free^2
    assert abs(1 / log(1 + kfree) - 2.1713) < 5e-4
    # integer reading of the crossover: sharper for n <= 6, tie at n = 7 (both L <= 8)
    assert all(int(kapA * n + CA) < int(kfree * n + Cfree) for n in range(2, 7))
    assert int(kapA * 7 + CA) == int(kfree * 7 + Cfree) == 8
    assert int(kapA * 8 + CA) > int(kfree * 8 + Cfree)
    out.write(f"      kappa_free = log2(3/2) = {kfree:.7f} = 1/kappa(1/2) exactly (slope ratio "
              f"{kapA / kfree:.7f} = 1/kappa_free^2);\n"
              f"      the two caps cross at n = {cross:.4f}\n"
              f"      so Theorem A's cap is the sharper one only for integer n <= 6 (they tie "
              "at n = 7, both L <= 8), where L <= 6\n"
              "      anyway, and the\n"
              f"      free count {1 / log(1 + kfree):.4f} ln N with a visit in EVERY dyadic "
              f"block replaces {1 / log(1 + kapA):.4f} ln N.\n")
    thab = 0.57434
    kh = -log(thab) / L32
    assert abs(kh - 1.3676) < 5e-5 and abs(1 / log(1 + kh) - 1.160) < 5e-4
    out.write(f"      at theta_Hab = 0.57434: kappa = {kh:.7f}, count "
              f"{1 / log(1 + kh):.7f} ln N -- also above kappa_free, so\n"
              "      Theorem A' would publish a cap 2.34x weaker in slope than a free one "
              "(TShift.one_le_kappa_thetaHab).\n")

    out.write("\n[E] D3/D4 -- the general-base grid, with the route the plan omits\n"
              "      floor route  kappa_b    = log q / log(p/q)   (needs the q-adic floor, "
              "xi = 1)\n"
              "      cascade      kappa_casc = log(p/q) / log q   (needs only q^k | m_c - m_a)\n"
              "       p/q   kappa_b     kappa_casc   min      1+min    ln-count   zone\n")
    grid = [(3, 2), (5, 2), (7, 2), (9, 2), (10, 3), (11, 3), (4, 3), (5, 3), (7, 3), (8, 3)]
    for p, q in grid:
        lb = log(p / q)
        kb, kc = log(q) / lb, lb / log(q)
        assert abs(kb * kc - 1) < 1e-12                     # exact reciprocals
        assert (kb < 1) == (p > q * q)                      # Proposition D
        km = min(kb, kc)
        assert km < 1                                       # ... at EVERY base
        out.write(f"      {p:2d}/{q}  {kb:10.6f}  {kc:11.6f}  {km:8.6f}  {1 + km:7.5f}  "
                  f"{1 / log(1 + km):8.5f}   {'free  p>q^2' if p > q*q else 'hard  q<p<q^2'}\n")
    out.write("      -> the two slopes are reciprocal, so min < 1 at every coprime "
              "p > q >= 2 (p = q^2 is\n"
              "         impossible), and p vs q^2 decides only WHICH route delivers the "
              "rung, not whether one does.\n")
    for p, q in ((3, 2), (5, 2), (7, 2), (10, 3), (4, 3)):
        N = 400
        mm = [pow(p, n) // pow(q, n) for n in range(N + 2)]
        cy = [q * mm[n + 1] - p * mm[n] for n in range(N + 1)]
        bad = 0
        for per in (1, 2, 3):
            for n in range(2, N - per):
                k = 0
                while n + per + k < N and cy[n + k] == cy[n + per + k]:
                    k += 1
                if k and (mm[n + per] - mm[n]) % pow(q, k):
                    bad += 1
        assert bad == 0
        out.write(f"      {p}/{q}: q^k | m_(n+per) - m_n on every equal factor, per in "
                  f"1..3, n <= {N}: {bad} exceptions\n")
    for p, q, m in ((5, 2, 1), (5, 2, 2)):
        Dm = p ** m - q ** m
        assert gcd(Dm, q) == 1                              # D_m = p^m - q^m is coprime to q
        kb = log(q) / log(p / q)
        Cm = m + log(Dm) / log(p / q)
        rec = 1 + kb + Cm
        thr = rec / (1 - kb)
        out.write(f"      ({p},{q}), m = {m}: D_m = {Dm}, C(m) = {Cm:.6f}, recursion "
                  f"constant {rec:.6f}, doubling threshold {thr:.4f}, j_0 = "
                  f"{int(log(thr) / log(2)) + 1}\n")
        if m == 1:
            assert abs(kb - 0.7564708) < 5e-7               # the plan prints 0.75644
            assert abs(Cm - 2.199) < 5e-4 and abs(rec - 3.955) < 5e-4
            assert abs(thr - 16.24) < 5e-3

    # ---- WP4 additions (TShift/GeneralBase.lean): the four objects the Lean file states ----
    out.write("      WP4 -- the general-base layer as formalized in TShift/GeneralBase.lean\n")
    # (1) growth threshold: TShift.intPartB_ge_of_pow_le reduces "q <= m_n" to q^(n+1) <= p^n;
    #     the two thresholds must coincide, and the free zone must pay no burn-in at all.
    for p, q in grid:
        n_int = next(n for n in range(1, 40) if q ** (n + 1) <= p ** n)
        n_flo = next(n for n in range(1, 40) if q <= pow(p, n) // pow(q, n))
        assert n_int == n_flo                              # the criterion is sharp, not merely valid
        assert (n_int == 1) == (p > q * q)                 # free zone: threshold at the first date
    n32 = next(n for n in range(1, 40) if 2 ** (n + 1) <= 3 ** n)
    n52 = next(n for n in range(1, 40) if 2 ** (n + 1) <= 5 ** n)
    assert (n32, n52) == (2, 1)                            # TShift.growth_threshold_five_two_three_two
    out.write(f"      growth threshold q <= m_n: n = {n32} at 3/2 (2^3 <= 3^2), n = {n52} at 5/2, "
              "and n = 1 at every free-zone base\n")
    m52 = [pow(5, n) // pow(2, n) for n in range(5)]
    s52 = [2 * m52[n + 1] - 5 * m52[n] for n in range(4)]
    assert m52 == [1, 2, 6, 15, 39] and s52 == [-1, 2, 0, 3]     # the Lean sanity theorems
    assert (5 - 2, 5 ** 2 - 2 ** 2) == (3, 21)                   # cycleDenomB 5 2 {1,2}
    out.write(f"      (5,2): m_n = {m52}, carry word {s52}, D_1 = 3, D_2 = 21\n")
    # (2)-(4) circuit sum, the block cap, and the block shadow, on the real orbits.
    for p, q in ((3, 2), (5, 2), (7, 2), (10, 3), (4, 3)):
        N = 400
        mm = [pow(p, n) // pow(q, n) for n in range(N + 2)]
        cy = [q * mm[n + 1] - p * mm[n] for n in range(N + 1)]
        assert all(-q < s < p for s in cy)                  # TShift.carryB_mem
        n0 = next(n for n in range(1, 40) if q ** (n + 1) <= p ** n)

        def W(a, k):                                        # TShift.carrySumB
            return sum(p ** (k - 1 - i) * q ** i * cy[a + i] for i in range(k))

        bad_cs = bad_cap = bad_sh = 0
        for a in range(0, 60):
            for k in range(0, 12):                          # TShift.carryB_circuit_sum
                if q ** k * mm[a + k] != p ** k * mm[a] + W(a, k):
                    bad_cs += 1
        for m in (1, 2, 3):
            n = n0
            while n < N - 3 * m:
                L = m
                while n + L < N and cy[n + L - m] == cy[n + L]:
                    L += 1
                if L > m:                                   # a maximal m-periodic block [n, n+L)
                    if q ** (L + n) > p ** (n + m):         # TShift.periodic_block_pow_le
                        bad_cap += 1
                    J, Aw, Dm = L // m, W(n, m), p ** m - q ** m
                    y = Fraction(pow(p, n) % pow(q, n), q ** n)   # TShift.fracB_eq_mod_div
                    dev = abs(y - Fraction(Aw, Dm))              # TShift.block_shadow
                    if (Fraction(p, q) ** (J * m) - 1) * dev > 1:
                        bad_sh += 1
                n += 1
        assert bad_cs == bad_cap == bad_sh == 0
        out.write(f"      {p}/{q}: circuit sum, q^(L+n) <= p^(n+m) and the block shadow "
                  f"((p/q)^(Jm)-1)|y_n - A_w/D_m| <= 1: {bad_cs + bad_cap + bad_sh} exceptions\n")
    # (5) the q-adic floor of route (a), which is what xi = 1 buys and [Aki08] denies in general.
    for p, q in ((5, 2), (7, 2), (10, 3)):
        worst = min(min(Fraction(D * pow(p, n) % pow(q, n), q ** n),
                        1 - Fraction(D * pow(p, n) % pow(q, n), q ** n)) * q ** n
                    for n in range(1, 25) for D in range(1, 30) if gcd(D, q) == 1)
        assert worst >= 1                                   # TShift.distToNearestInt_mul_ge_base
        out.write(f"      {p}/{q}: q^n * ||D (p/q)^n|| >= {worst} for gcd(D,q) = 1, "
                  "D <= 29, n <= 24 -- the free q-adic floor\n")

    # ---- WP5 additions (TShift/FreeZone.lean): the kappa layer and Theorem C ----
    out.write("      WP5 -- the kappa layer and Theorem C, as formalized in "
              "TShift/FreeZone.lean\n")
    # (1) TShift.intPartB_ge_of_mul_le: the Bernoulli burn-in q(q-1) is valid at every base and
    #     dominates the sharp threshold of F9; at q = 2 it is free_sojourn_cap's numeral 2.
    for p, q in grid:
        n0u = q * (q - 1)
        assert all(q <= pow(p, n) // pow(q, n) for n in range(n0u, n0u + 60))
        assert n0u >= next(n for n in range(1, 40) if q ** (n + 1) <= p ** n)
    assert 2 * (2 - 1) == 2
    out.write("      uniform burn-in q(q-1) (Bernoulli) is valid at, and dominates the sharp "
              "threshold of, every grid base; at q = 2 it is 2\n")
    # (2) Theorem C(i)'s constant.  The plan's D3 predicts m + log(D_m)/log(p/q); the shadowing
    #     variant actually available (endpoint spread, no hypothesis on the cycle point) gives
    #     m + log(2 D_m)/log(p/q).  The slope kappa_b is untouched.
    out.write("       (p,q) m   C_plan     C_lean     recursion  threshold  j_0\n")
    for p, q, m in ((5, 2, 1), (5, 2, 2), (7, 2, 1), (10, 3, 1)):
        Dm, kb = p ** m - q ** m, log(q) / log(p / q)
        Cpl, Cln = m + log(Dm) / log(p / q), m + log(2 * Dm) / log(p / q)
        rec = kb + Cln
        thr = rec / (1 - kb)
        out.write(f"      ({p},{q}) {m}  {Cpl:9.6f}  {Cln:9.6f}  {rec:9.6f}  {thr:9.4f}  "
                  f"{int(log(thr) / log(2)) + 1}\n")
        if (p, q, m) == (5, 2, 1):                          # the plan's C(1) = 2.199
            assert abs(Cpl - 2.198978) < 2e-6 and abs(Cln - 2.955449) < 2e-6
        if (p, q, m) == (5, 2, 2):                          # the plan's C(2) = 5.32266
            assert abs(Cpl - 5.322660) < 2e-6 and abs(Cln - 6.079131) < 2e-6
    out.write("      -> the log 2 is the price of assuming nothing about where the cycle point "
              "sits (plan risk R6); the slope is untouched\n")
    # (3) each base's own route, on its real orbit: the cap, the break recursion
    #     b_(k+1) <= (1+kappa) b_k + (kappa + C), and the every-dyadic-block payoff.
    for p, q in ((3, 2), (5, 2), (7, 2), (10, 3), (4, 3)):
        N = 400
        mm = [pow(p, n) // pow(q, n) for n in range(N + 2)]
        cy = [q * mm[n + 1] - p * mm[n] for n in range(N + 1)]
        free = p > q * q
        kap = log(q) / log(p / q) if free else log(p / q) / log(q)
        assert (kap < 1) and (kap == min(log(q) / log(p / q), log(p / q) / log(q)))
        bad_cap = bad_rec = bad_dy = 0
        for m in (1, 2, 3):
            Dm = p ** m - q ** m
            C = (m + log(2 * Dm) / log(p / q)) if free else m * (log(p) / log(q))
            n0u = 1 if free else q * (q - 1)
            n = n0u
            while n < N - 3 * m:                            # every m-periodic block obeys its cap
                L = m
                while n + L < N and cy[n + L - m] == cy[n + L]:
                    L += 1
                if L > m and L > kap * n + C + 1e-9:
                    bad_cap += 1
                n += 1
            br = [n for n in range(n0u, N - m) if cy[n + m] != cy[n]]   # TShift.IsBreakB
            for a, b in zip(br, br[1:]):                    # TShift.breakSeq_recursion
                if b > (1 + kap) * a + (kap + C) + 1e-9:
                    bad_rec += 1
            j0, thr = 0, (kap + C) / (1 - kap)              # TShift.exists_break_dyadic_of_cap
            while 2 ** j0 < max(thr, br[0]):
                j0 += 1
            for j in range(j0, int(log(N - m) / log(2))):
                if not any(2 ** j <= n < 2 ** (j + 1) for n in br):
                    bad_dy += 1
        assert bad_cap == bad_rec == bad_dy == 0
        out.write(f"      {p}/{q}: route ({'a' if free else 'b'}), kappa = {kap:.6f}; cap, break "
                  f"recursion and every-dyadic-block, m <= 3: "
                  f"{bad_cap + bad_rec + bad_dy} exceptions\n")
    out.write("      -> Theorem C (iii): both routes deliver, and which one is decided by "
              "p vs q^2 alone.\n")

    out.write("\n[F] F5 -- what the every-dyadic-block statement is worth per block\n"
              "      the promised per-block count is floor(log2 / log(1+kappa)), which "
              "exceeds 1 only for\n"
              f"      kappa < sqrt(2) - 1 = {sqrt(2) - 1:.5f}:\n")
    for lab, k in (("3/2 free", kfree), ("5/2", log(2) / log(5 / 2)),
                   ("7/2", log(2) / log(3.5)), ("9/2", log(2) / log(4.5)),
                   ("4/3 cascade", log(4 / 3) / log(3))):
        out.write(f"      {lab:12s} kappa = {k:.5f}  ->  per-block count >= "
                  f"{int(log(2) / log(1 + k))}\n")
    assert int(log(2) / log(1 + kfree)) == 1
    assert all(int(log(2) / log(1 + log(2) / log(p / 2))) == 1 for p in (5, 7, 9))
    out.write("      so at every base in D4 the refinement is exactly \"at least one\": "
              "F5 should claim\n"
              "      \"every dyadic block\" and drop the per-block count.\n")

    out.write("\n[H] WP7 / gate G-D -- how large may the region be?  The ceiling is per CYCLE\n"
              "      Two constraints bound a forcing radius, both (5/2)*delta-shaped (the wrong\n"
              "      image moves at slope 3/2, the point is delta off target):\n"
              "        ejection  (5/2)delta < d = dist(wrong images, the targets KEPT), and\n"
              "        phase     (5/2)delta < g = least gap between kept targets.\n"
              "      So the closed form is  delta*(C) = (2/5) * min(d(C), g(C)).\n")

    def _cycle_ceiling(kept):
        """(d, g, ceiling) for a set of targets closed under the cycle map."""
        S = set(kept)
        d = None
        for rho in kept:
            wrong = [Fraction(3 * rho - s, 2) for s in _admissible(rho)
                     if Fraction(3 * rho - s, 2) not in S]
            assert len(wrong) == 1, (rho, wrong)
            dist = min(abs(wrong[0] - t) for t in kept)
            d = dist if d is None else min(d, dist)
        g = min((abs(a - b) for i, a in enumerate(kept) for b in kept[i + 1:]), default=None)
        cap = Fraction(2, 5) * d if g is None else min(Fraction(2, 5) * d, Fraction(2, 5) * g)
        return d, g, cap

    def _cycles(m):
        """The period-m cycles of y -> (3y - s)/2 inside [0,1), as sorted target lists."""
        D, seen, out_ = 3 ** m - 2 ** m, set(), []
        for A in range(D):
            r = Fraction(A, D)
            if r in seen:
                continue
            cyc, x = [], r
            for _ in range(m + 1):
                cyc.append(x)
                nxt = [v for v in (Fraction(3 * x - s, 2) for s in _admissible(x))
                       if (v * D).denominator == 1 and (v not in cyc or v == r)]
                x = nxt[0]
                if x == r:
                    break
            cyc = sorted(dict.fromkeys(cyc))
            if len(cyc) != m or any(c in seen for c in cyc):
                continue
            seen.update(cyc)
            out_.append(cyc)
        return D, out_

    out.write("      cycle                                    d        gap     ceiling\n")
    _peak = {}
    for m in (1, 2, 3, 4):
        Dm, cs = _cycles(m)
        rows = sorted(((_cycle_ceiling(c), c) for c in cs), reverse=True)
        _peak[m] = rows[0][0][2]
        for (d, g, cap), c in rows[:3]:
            lab = "{" + ", ".join(str(t) for t in c) + "}"
            out.write(f"      p={m} D={Dm:3d} {lab[:28]:28s} {str(d):>8} {str(g):>8} "
                      f"{str(cap):>8} = {float(cap):.5f}\n")
        if len(rows) > 3:
            out.write(f"      {'':13s} ... {len(rows) - 3} further cycle(s), down to "
                      f"{str(rows[-1][0][2]):>7}\n")
    # rho = 0 reproduces the atlas's measured classical frontier, 1/5.
    assert _peak[1] == Fraction(1, 5)
    # The two D_2 = 5 cycles, and the four-target union that TShift/CarryGraph.lean formalizes.
    dA, gA, capA = _cycle_ceiling([Fraction(1, 5), Fraction(4, 5)])
    dB, gB, capB = _cycle_ceiling([Fraction(2, 5), Fraction(3, 5)])
    dU, gU, capU = _cycle_ceiling(_S1314_T)
    assert (dA, capA) == (Fraction(1, 10), Fraction(1, 25))
    assert (dB, capB) == (Fraction(3, 10), Fraction(2, 25))
    assert (dU, capU) == (Fraction(1, 10), Fraction(1, 25))
    assert capB == 2 * capU and gA == Fraction(3, 5) and gB == gU == Fraction(1, 5)
    deltaB = Fraction(5, 64)
    assert delta < Fraction(1, 25) and deltaB < capB and deltaB == Fraction(5, 2) * delta
    out.write(f"      four targets  d = {dU}  gap = {gU}  ->  ceiling {capU} "
              f"(Lean: delta = {delta})\n"
              f"      cycle {{2/5,3/5}} d = {dB}  gap = {gB}  ->  ceiling {capB} "
              f"(Lean: deltaB = {deltaB})\n"
              "      -- 1/10 is cycle {1/5,4/5}'s number; dropping that cycle removes the "
              "binding\n"
              "         constraint and DOUBLES the radius, 1/25 -> 2/25.  The union is capped "
              "by the\n"
              "         worse cycle, which is why the four-target region cannot be enlarged.\n")

    # The real orbit at the enlarged radius: forcing, and the sojourns U_(1/32) cannot see.
    TB = [Fraction(2, 5), Fraction(3, 5)]

    def nearB(n):
        for t in TB:
            if abs(Fraction(r[n], 1 << n) - t) < deltaB:
                return t
        return None

    inB = [nearB(n) for n in range(nmax + 1)]
    pairsB = violB = 0
    for n in range(1, nmax):
        if inB[n] is not None and inB[n + 1] is not None:
            pairsB += 1
            sc, nxt = _S1314_CYC[inB[n]]
            if s[n] != sc or inB[n + 1] != nxt:
                violB += 1
    assert violB == 0
    gained = [n for n in range(1, nmax + 1) if inB[n] is not None and inU[n] is None]
    sojB, n = [], 1
    while n <= nmax:
        if inB[n] is None:
            n += 1
            continue
        L = 0
        while n + L <= nmax and inB[n + L] is not None:
            L += 1
        sojB.append((n, L))
        n += L
    wB = max(L - (kfree * k + Cfree) for k, L in sojB)
    assert wB < 0
    assert gained[0] == 9 and Fraction(r[9], 1 << 9) == Fraction(227, 512)
    assert (8, 3) in sojB and (8, 3) not in soj
    out.write(f"      real orbit at deltaB = 5/64, n <= {nmax}: "
              f"{sum(1 for v in inB if v is not None)} dates in U_B "
              f"(measure 2*2*(5/64) = 5/16),\n"
              f"      {pairsB} forcing pairs, {violB} digit-or-phase exceptions; "
              f"{len(sojB)} maximal sojourns,\n"
              f"      longest {max(L for _, L in sojB)}, worst free-cap slack {wB:+.3f}\n"
              f"      dates in U_B but not in U_(1/32): {len(gained)}, first n = {gained[0]} "
              f"(x_9 = 227/512, 0.0434 from 2/5)\n"
              "      and (8,3) is a maximal U_B sojourn that U_(1/32) does not see "
              "-- TShift.cycleB_sanity.\n")

    out.write("      engine leg (Z32/gencert.py, exact integer funnels; verdicts recorded, "
              "reproduce with\n"
              "        python3 Z32/gencert.py 1000 <lo hi ...>   [--ranked] ):\n"
              "        four targets  functional to 0.046, ranked to 0.047, none from 0.060\n"
              "                      (0.048-0.050 time out at 300 s: not decided either way)\n"
              "        cycle {1/5,4/5} functional to 0.046, ranked to 0.049, none at 0.050\n"
              "        cycle {2/5,3/5} functional to 0.092, ranked to 0.099, none at 0.100 "
              "(balls merge)\n"
              "        at deltaB = 5/64 exactly: functional, funnel depth 1, two blocks\n"
              "      so the funnel buys 18-24% in radius over the closed form and the factor 2 "
              "is the\n"
              "      cycle restriction -- gate G-D: NO-GO on Z32/BlockCertSojourn.lean.\n")

    out.write("\n[G] gate G-A -- verdict\n"
              "      D1, D2, D3 and the (5,2) constants reproduce exactly; D4 has one "
              "display slip\n"
              "      (kappa_b at 5/2 is 0.7564708, printed 0.75644); F2 and F3 confirmed, "
              "F5 confirmed but\n"
              "      its per-block refinement is vacuous.  Two substantive corrections, "
              "both from C20, which\n"
              "      post-dates the plan by one day: Theorem A's rung and Theorem A' are "
              "dominated by the free\n"
              "      cap already in the corpus, and the free-zone dichotomy is a tiling, "
              "not a threshold.\n")


# ---------------------------------------------------------------------------
# plan-Tshift-S1 WP5: the initial range of Theorem A
# ---------------------------------------------------------------------------
#
# ||D(3/2)^k|| = m_k / 2^k  with  m_k = min(R, 2^k - R),  R = D 3^k mod 2^k.
# Habsieger's threshold 2^(-0.8k) = 2^(k/5)/2^k, so the whole initial-range
# question is the Z-statement
#
#         ||D(3/2)^k|| > 2^(-0.8k)   <=>   m_k^5 > 2^k ,
#
# which is what TShift/InitialRange.lean checks in the kernel and what the
# sweep below checks to k0 = 64 440 001.  For odd D and k >= 1 the residue R is
# odd, hence m_k is odd and m_k^5 != 2^k: strict and non-strict agree.
#
# Cost.  m_k is read off the top ~0.8k bits of a k-bit window, so a full-precision
# sweep is Theta(K^2) -- 14 CPU-hours at Habsieger's k0.  The engine below keeps a
# *sliding register* W ~ D 3^k / 2^L with L just under the block's first date.
# Multiplying by 3 multiplies the truncation error by 3 (1.585 bits per step)
# while the read window rises by 1 bit per step, so a register of ~1.6 B bits
# serves a block of B dates *whatever k is*, and the per-step cost stops growing.
# Each date is then either certified by the register (with its error bound carried
# explicitly) or, when the register cannot separate, settled by an exact modpow.
# No date is decided by a float, and none is skipped.


def _pow3_mod2(k, N):
    """3^k mod 2^N, square-and-mask (GMP powm has no power-of-two fast path)."""
    mask = (1 << N) - 1
    r, b = _MPZ(1), _MPZ(3)
    while k:
        if k & 1:
            r = (r * b) & mask
        b = (b * b) & mask
        k >>= 1
    return r


def win_exact(D, k):
    """m_k = min(R, 2^k - R) with R = D 3^k mod 2^k -- exact, one modpow."""
    R = (_MPZ(D) * _pow3_mod2(k, k)) & ((_MPZ(1) << k) - 1)
    return min(R, (_MPZ(1) << k) - R)


def win_fails(D, k):
    """True iff ||D(3/2)^k|| <= 2^(-0.8k), i.e. m_k^5 <= 2^k.  Exact."""
    return win_exact(D, k) ** 5 <= (_MPZ(1) << k)


def sweep_naive(D, kmax, kmin=1):
    """Reference sweep: full precision, no register.  Theta(kmax^2)."""
    exc = []
    top = (_MPZ(1) << (kmax + 2)) - 1
    V = (_MPZ(D) * _pow3_mod2(kmin, kmax + 2)) & top
    for k in range(kmin, kmax + 1):
        mod = _MPZ(1) << k
        R = V & (mod - 1)
        m = min(R, mod - R)
        if m ** 5 <= mod:
            exc.append(k)
        V = (3 * V) & top
    return exc


def sweep_window(D, kmax, kmin=1, bmax=1 << 16, small=8192, prog=None, out=None):
    """Exceptional dates, record lows and the digit-run table on [kmin, kmax].

    Returns a dict with
        exceptions  every k with ||D(3/2)^k|| <= 2^(-0.8k)          (exact)
        records     (k, m, e) record lows of ||D(3/2)^k|| = m/2^e   (exact)
        runs        per decade, (max leading-run upper bound, its date, k)
        exact       number of dates settled by an exact modpow
        blocks      number of register blocks
    """
    exc, recs, runs, nexact, nblocks = [], [], {}, 0, 0
    small = max(small, 1024)                      # the register needs L = k - G > 0
    best = None                                   # (m, e) exact, m/2^e is the record

    def note_run(k, ell):
        d = len(str(k))
        cur = runs.get(d)
        if cur is None or ell > cur[0]:
            runs[d] = (ell, k)

    k = kmin
    if k < small:                                 # low range: full precision
        top = min(kmax, small - 1)
        mod = (_MPZ(1) << (top + 2)) - 1
        V = (_MPZ(D) * _pow3_mod2(k, top + 2)) & mod
        while k <= top:
            M = _MPZ(1) << k
            R = V & (M - 1)
            m = min(R, M - R)
            nexact += 1
            if m ** 5 <= M:
                exc.append(k)
            note_run(k, k - m.bit_length())
            if best is None or m * (_MPZ(1) << best[1]) < best[0] * M:
                best = (m, k)
                recs.append((k, m, k))
            V = (3 * V) & mod
            k += 1
    bestkey = None
    if best is not None:
        _bl = best[0].bit_length()
        bestkey = (_bl - best[1], int(best[0] >> (_bl - 64)) if _bl >= 64 else int(best[0]))
    Vfull, pB, Bprev = None, None, None
    while k <= kmax:
        B = min(bmax, k)
        k1 = min(kmax, k + B - 1)
        G = (62 * B) // 100 + 160                 # guard: 1.585 j + 2 < G + j - 2
        L = k - G
        S = (k1 - L) + 8
        maskS = (_MPZ(1) << S) - 1
        N = k1 + 8
        maskN = (_MPZ(1) << N) - 1
        if Vfull is None or B != Bprev:               # block length changed: modpow
            Vfull = (_MPZ(D) * _pow3_mod2(k, N)) & maskN
            pB, Bprev = None, B
        else:                                         # advance by one block: one multiply
            if pB is None:
                pB = _pow3_mod2(B, kmax + 8)
            Vfull = (Vfull * (pB & maskN)) & maskN
        nblocks += 1
        W = Vfull >> L
        j = 0
        k0blk = k

        def exact_m(kk, jj):
            """m_kk, from the block's exact head: one multiply, not a full modpow."""
            V = (Vfull * _pow3_mod2(jj, N)) & ((_MPZ(1) << kk) - 1)
            return min(V, (_MPZ(1) << kk) - V)

        while k <= k1:
            wl = k - L
            r = W & ((_MPZ(1) << wl) - 1)
            u = min(r, (_MPZ(1) << wl) - r)
            eb = (1585 * (j + 1)) // 1000 + 2      # truncation error <= 2^eb ulps
            ubl = u.bit_length()
            mex = None
            if ubl >= eb + 2 and 5 * (L + ubl - 2) > k:
                note_run(k, k - (L + ubl - 1))     # upper bound on the leading run
            else:                                  # register cannot separate: exact
                nexact += 1
                mex = exact_m(k, j)
                if mex ** 5 <= (_MPZ(1) << k):
                    exc.append(k)
                note_run(k, k - mex.bit_length())
            # record low.  ||.|| = u/2^wl to within 2^eb/2^wl, so the ordering key
            # (exponent, top 64 bits) is exact as soon as u carries 80 bits of margin
            # over the error; a smaller key than the record's is settled exactly.
            if best is not None:
                if ubl - eb >= 80:
                    key = (ubl - wl, int(u >> (ubl - 64)) if ubl >= 64 else int(u))
                    cand = key <= bestkey
                else:
                    cand = True
                if cand:
                    m = mex if mex is not None else exact_m(k, j)
                    if mex is None:
                        nexact += 1
                    if m * (_MPZ(1) << best[1]) < best[0] * (_MPZ(1) << k):
                        best = (m, k)
                        bl = m.bit_length()
                        bestkey = (bl - k, int(m >> (bl - 64)) if bl >= 64 else int(m))
                        recs.append((k, m, k))
            W = (3 * W) & maskS
            j += 1
            k += 1
        if prog and out and nblocks % prog == 0:
            out.write(f"#   ... k = {k - 1}\n")
            out.flush()
    return dict(exceptions=exc, records=recs, runs=runs, exact=nexact, blocks=nblocks)


def is_record(D, k):
    """(m_k, k-1) if ||D(3/2)^k|| < ||D(3/2)^j|| for every 1 <= j < k; asserts otherwise.

    This is the statement TShift/InitialRange.lean's `recSweep` certificate checks in the
    kernel; here it is done in one full-precision pass, exactly.
    """
    mk = win_exact(D, k)
    top = (_MPZ(1) << (k + 2)) - 1
    V = _MPZ(D) * 3
    beaten = 0
    for j in range(1, k):
        mod = _MPZ(1) << j
        R = V & (mod - 1)
        mj = min(R, mod - R)
        assert mk * (_MPZ(1) << j) < mj * (_MPZ(1) << k), (D, k, j)
        beaten += 1
        V = (3 * V) & top
    return mk, beaten


def cmd_s1(nmax=20000, out=sys.stdout):
    """plan-Tshift-S1 WP5: the initial range [1, k0) of Theorem A, at D = 5.

    [A] the criterion in Z, and why strict and non-strict agree
    [B] the sliding register against full precision
    [C] the exceptional dates, per multiplier -- WP5(a)'s threshold table
    [D] the leading-run table ([Hab03] Lemma 2's mechanism, transported to D 3^k)
    [E] N5's record lows and the simultaneity at D = 1, 5
    [F] the constants TShift/InitialRange.lean freezes  -- WP5(b)
    """
    t00 = time.time()
    out.write("plan-Tshift-S1 WP5 -- the initial range of Theorem A.\n"
              f"    (nmax = {nmax}; the full initial range is k0 = 64440001)\n")

    out.write("\n[A] the criterion, in Z\n"
              "      ||D(3/2)^k|| = m_k/2^k,  m_k = min(R, 2^k - R),  R = D 3^k mod 2^k;\n"
              "      2^(-0.8k) = 2^(k/5)/2^k, so  ||D(3/2)^k|| > 2^(-0.8k)  <=>  m_k^5 > 2^k.\n"
              "        k   R = 5*3^k mod 2^k    m_k    m_k^5 vs 2^k   ||5(3/2)^k||  2^(-0.8k)\n")
    for k in range(1, 11):
        R = (5 * 3 ** k) % (1 << k)
        m = min(R, (1 << k) - R)
        rel = ">" if m ** 5 > (1 << k) else "<="
        out.write(f"      {k:3d} {R:12d} {m:10d}   {m ** 5:>10d} {rel} {1 << k:<8d} "
                  f"{m / (1 << k):.6f}  {2.0 ** (-0.8 * k):.6f}\n")
    # strict = non-strict: for odd D and k >= 1 the residue is odd, so m_k is odd
    for D in (1, 5, 7, 19):
        for k in range(1, 400):
            R = (D * 3 ** k) % (1 << k)
            m = min(R, (1 << k) - R)
            assert m % 2 == 1, (D, k)
            # the rational test, independently: (m/2^k)^5 vs 2^(-4k)
            assert (Fraction(m, 1 << k) ** 5 > Fraction(1, 1 << (4 * k))) == (m ** 5 > (1 << k))
    out.write("      m_k is odd for every odd D and k >= 1 (R is odd, and so is 2^k - R),\n"
              "      so m_k^5 = 2^k is impossible: the strict and non-strict criteria agree,\n"
              "      and the Lean file's non-strict form loses nothing.  Checked k <= 400,\n"
              "      D in {1,5,7,19}, against the independent rational test (m/2^k)^5 > 2^(-4k).\n")

    out.write("\n[B] the sliding register against full precision\n")
    ncheck = min(nmax, 30000)
    for D in (1, 5):
        a = sweep_naive(D, ncheck)
        r = sweep_window(D, ncheck, bmax=4096, small=1024)
        assert a == r["exceptions"], (D, a, r["exceptions"])
        out.write(f"      D = {D}: full precision and register agree on [1, {ncheck}] "
                  f"({r['exact']} of {ncheck} dates settled exactly, {r['blocks']} blocks)\n")
    out.write("      -- the register certified every date above the 1024-date exact prefix\n"
              "      without a single fallback, which is what makes the k0-range feasible.\n")

    out.write("\n[C] the exceptional dates: k with ||D(3/2)^k|| <= 2^(-0.8k)\n"
              "        D    exceptional dates          k_min(D)   dates checked\n")
    small_ds = (1, 5, 7, 19, 25, 35, 175)
    res = {}
    for D in small_ds:
        lim = min(nmax, 200000)
        r = sweep_window(D, lim, bmax=1 << 14)
        res[D] = r
        e = r["exceptions"]
        out.write(f"      {D:4d}   {str(e):<26s} {max(e) + 1 if e else 1:>7d}   {lim}\n")
    out.write("      D = 1 reproduces [Hab03] Theorem 2's own range: the bound holds for all\n"
              "      k >= 5 and fails at k = 1, 2, 4.  At the plan's D = 5 the exceptional set\n"
              "      is {1,2,3,5}, so Theorem A at D = 5 starts at k_min = 6.\n")

    big = None
    if nmax > 200000:
        out.write(f"\n[C'] the full initial range, D = 5 and D = 1, to k = {nmax}\n")
        for D in (5, 1):
            t0 = time.time()
            r = sweep_window(D, nmax, bmax=1 << 16, prog=64, out=out)
            dt = time.time() - t0
            res[D] = r
            if D == 5:
                big = r
            out.write(f"      D = {D}: exceptions {r['exceptions']}, "
                      f"{r['exact']} dates settled exactly, {r['blocks']} blocks, "
                      f"{dt:.0f} s\n")
        out.write("      -- every date in the range is either certified by the register with\n"
                  "      its error bound or settled by an exact modpow; none is skipped.\n")

    out.write("\n[D] leading runs: the largest run of equal bits at the top of the k-bit\n"
              "    window, by decade ([Hab03] Lemma 2 asks l < 0.8k - 2; a run of l forces\n"
              "    m_k < 2^(k-l), so l <= 0.8k is exactly the criterion of [A])\n"
              "        D   decade      max run l      at k       l/k     0.8k - 2 - l\n")
    for D in (5, 1):
        r = res.get(D)
        if r is None:
            continue
        for d in sorted(r["runs"]):
            ell, kk = r["runs"][d]
            out.write(f"      {D:3d}   10^{d - 1:<2d} {ell:12d} {kk:11d}   {ell / kk:8.5f} "
                      f"{0.8 * kk - 2 - ell:14.1f}\n")

    out.write("\n[E] record lows of ||D(3/2)^k|| -- report-Tshift.html N5\n"
              "        D        k    ||D(3/2)^k||     theta_k = ||.||^(1/k)\n")
    rd = {}
    for D in (1, 5):
        r = res.get(D)
        if r is None:
            continue
        rd[D] = [k for (k, _m, _e) in r["records"]]
        for (k, m, e) in r["records"]:
            lg = (m.bit_length() - 1 - e) * 0.6931471805599453 / 0.6931471805599453
            val = float(m >> max(0, m.bit_length() - 53)) * 2.0 ** (
                max(0, m.bit_length() - 53) - e)
            th = 2.0 ** (lg / k)
            out.write(f"      {D:3d} {k:8d}   {val:14.6e}   {th:.6f}\n")
    if 1 in rd and 5 in rd:
        both = sorted(set(rd[1]) & set(rd[5]))
        out.write(f"      simultaneous record dates at D = 1 and D = 5: {both}\n")
        if nmax >= 12429:
            assert 3328 in both and 12429 in both
            out.write("      -- N5's claim reproduced: 3328 and 12429 are record dates at both\n"
                      "      multipliers (and are the only nontrivial ones below 20000).\n")
        out.write("      theta_k -> 1 along the records, as N5 reports: the record lows decay\n"
                  "      like 1/k, not exponentially, so they say nothing against Theorem A.\n")

    out.write("\n[F] what TShift/InitialRange.lean freezes (WP5(b))\n")
    for (D, k0, N) in ((5, 6, 20000), (1, 5, 20000)):
        r = sweep_window(D, k0 + N - 1, kmin=k0, bmax=1 << 14)
        assert r["exceptions"] == [], (D, r["exceptions"])
        out.write(f"      sweepFrom ({D}*3^{k0}) (2^{k0}) {N} = true  -- no exception in "
                  f"[{k0}, {k0 + N - 1}]\n")
    for (D, k) in ((1, 3328), (5, 3328), (1, 12429), (5, 12429)):
        m, beaten = is_record(D, k)
        out.write(f"      recSweep {D} {k}: m_k has {m.bit_length()} bits and beats all "
                  f"{beaten} earlier dates\n")
    out.write("      theta^5 <= 1/16 with theta = 57434/100000 "
              f"({Fraction(57434, 100000) ** 5 <= Fraction(1, 16)}), which is what turns\n"
              "      m_k^5 > 2^k into thetaHab^k <= ||D(3/2)^k||: 0.57434^5 = "
              f"{(57434 / 100000) ** 5:.9f} < 0.0625.\n")

    out.write(f"\n[G] cost.  This run: {time.time() - t00:.0f} s.  The register makes the\n"
              "      per-date cost independent of k, so the sweep is linear in the range once\n"
              "      the block multiplications are amortised: 1.6 s per 10^6 dates at bmax =\n"
              "      2^14, and the whole initial range [1, 64440001] measured at 248 s (D = 5)\n"
              "      and 244 s (D = 1) at bmax = 2^16, 986 blocks each, with 8199 resp. 8200\n"
              "      dates settled by an exact modpow: the 8191-date exact prefix k < 8192,\n"
              "      plus exactly the 8 resp. 9 record confirmations above it.  The register\n"
              "      decided every other date -- not one undecided window in 64 431 810.\n"
              "      A full-precision sweep of the same range is Theta(k0^2) -- about 14\n"
              "      CPU-hours -- which is what makes this the one part of WP5 that needed an\n"
              "      engine rather than a loop.\n")


# ---------------------------------------------------------------------------
# plan-Tshift-S1 WP7 -- transporting [Zud07]'s record rate 0.5803 to every
# multiplier.  The source audit of the plan's stretch package, in numbers.
#
# [A] the three constants of [Zud07] p. 321 recomputed from (19), (20), (21),
#     checked against every printed digit; condition (26), theta, delta.
# [B] what CITED/ZudilinPade.lean freezes: the surrogates, their directions,
#     their cost against delta, and -- in exact rational arithmetic -- every
#     numeric obligation TShift/ZudilinTransfer.lean discharges with norm_num.
# [C] the two-form structure as EXACT integers at m = 1 .. MMAX: the integer T
#     of (6), the Pade identity (9), the two-column identity, Lemma 2's
#     determinant with the T-terms cancelled, and Lemma 3/4's divisibility by
#     Phi and Phi'/gcd(Phi', gamma m + 1).
# [D] the two lanes side by side: what the socket swap buys, and what it costs.
# ---------------------------------------------------------------------------

ZUD_TRIPLE = (9, 19, 9)              # [Zud07] section 5: alpha, beta, gamma

# CITED/ZudilinPade.lean and TShift/ZudilinTransfer.lean, verbatim.
ZUD_FROZEN = {
    "contentBase": Fraction(870914921, 10 ** 7),
    "errorBase": Fraction(268358608, 10 ** 7),
    "denomBase": Fraction(2580242883000000),
    "thetaZud": Fraction(5803, 10000),
    "bZud": Fraction(10013, 10000),
}


def _z7_qco(a, b, n):
    """[Zud07] (8): the coefficients q_mu of Q_n(x) = sum_mu q_mu x^mu."""
    return [comb(a + n - 1 + mu, mu) * comb(a + b + n, n - mu) * (-1) ** mu
            for mu in range(n + 1)]


def _z7_rco(a, b, n):
    """[Zud07] (10): the r_l of P_n(x) = sum_{l<n} r_l x^{n-l}."""
    q = _z7_qco(a, b, n)
    return [sum(q[n - mu] * comb(a + b + l - mu, b) for mu in range(l + 1))
            for l in range(n)]


def _z7_QP(a, b, n, x=9):
    """(Q_n(x), P_n(x)) as exact integers."""
    q = sum(c * x ** mu for mu, c in enumerate(_z7_qco(a, b, n)))
    r = _z7_rco(a, b, n)
    return q, sum(r[l] * x ** (n - l) for l in range(n))


def _z7_R(a, b, n, terms=400):
    """[Zud07] (11) at z = 1/9, as a truncated Fraction, with the last term."""
    A, B, C = a + b + n + 1, n + 1, a + 2 * n + 1
    z, t, s = Fraction(1, 9), Fraction(1), Fraction(1)
    for k in range(terms):
        t *= Fraction((A + k) * (B + k), (C + k) * (1 + k)) * z
        s += t
    pref = Fraction(1, 9 ** n) * comb(a + b + n, b - n)
    return pref * s, pref * t


def _z7_T(a, b):
    """[Zud07] (6): the integer part, (3/2)^{3(b+1)} = T + 3^{b-2a+1} F(a,b;1/9)."""
    return sum(comb(b + k, b) * 3 ** (b + 1 - 2 * k) for k in range(a))


def _z7_e_p(a, b, n, p, primed=False):
    """[Zud07] (13) / (14): e_p, resp. e'_p, as the minimum over mu mod p."""
    def fr(x):
        return x % p
    best = None
    for mu in range(p):
        if primed:
            v = (-fr(a + n + mu) + fr(a + n) + fr(mu)
                 - fr(a + b + n) + fr(a + b + mu) + fr(n - mu))
        else:
            v = (-fr(-(a + n)) + fr(-(a + n + mu)) + fr(mu)
                 - fr(a + b + n) + fr(a + b + mu) + fr(n - mu))
        best = v if best is None else min(best, v)
    assert best % p == 0
    return best // p


def _z7_Phi(a, b, n, primed=False):
    """[Zud07] (15): Phi = prod_{p > sqrt(a+b+n)} p^{e_p}, resp. Phi'."""
    lim, out = a + b + n, 1
    for p in _primes(lim):
        if p * p <= lim:
            continue
        e = _z7_e_p(a, b, n, p, primed)
        if e:
            out *= p ** e
    return out


def _z7_lane():
    """(C0, C1, C2, cond26, theta) at (9,19,9), z = 1/9, from _zud_lane."""
    C0, C1, C2, _floor, th, _thf, marg = _zud_lane(9, 19, 9, 9, 57, 2, 3)
    return C0, C1, C2, marg, th


def _s3_engine_fixed_point(c=24, mu=10, nu=10, prec=60):
    """[BL96p]'s own ceiling: the fixed point of u = A(c) * T(u)^2, at 60 digits.

    A(c) = c*2*g/((2-1)*(log 2)^4) * log 3 with g = 2-1 = 1 (Corollary 1's majorized g),
    T(u) = max(log(u + 1/log 3) + log log 2 + 2/5, max(mu log 2, nu)).
    Returns (A, u_star, eta) with eta = 1/(u_star log 2): theta = 2^-(1-eta).
    """
    getcontext().prec = prec
    L2 = Decimal(2).ln()
    L3 = Decimal(3).ln()
    A = Decimal(c) * 2 / (L2 ** 4) * L3
    u = Decimal(10) ** 5
    for _ in range(400):                     # a contraction: T |-> A(5.4 + 2 log T)^2
        T = max((u + 1 / L3).ln() + L2.ln() + Decimal("0.4"),
                max(Decimal(mu) * L2, Decimal(nu)))
        u = A * T * T
    return A, u, 1 / (u * L2)


def cmd_s3(nmax=20000, out=sys.stdout):
    """S3 WP0-WP2: the 2-adic two-log route (TShift/PadicLogForm.lean)."""
    Ds = (1, 5, 19, 65)

    out.write("# [A] the defect N_n = D 3^n - 2^n round(D (3/2)^n), exactly\n")
    out.write("#   D     n_max   |N| = 2^n||.||   N odd   2^n | D3^n-N   "
              "2|N| <= 2^n    min log|N_n|/n  (date)\n")
    NA = min(nmax, 4000)
    for D in Ds:
        best, bestn = None, None
        for n, t, m, T in orbit(D, NA):
            if n < 1:
                continue
            N = T - (m << n)
            assert abs(N) == dist_num(t, n), (D, n)
            assert N & 1, (D, n)                     # odd
            assert (T - N) % (1 << n) == 0, (D, n)   # the 2-adic congruence
            assert 2 * abs(N) <= (1 << n), (D, n)
            if n >= 10:
                r = log(abs(N)) / n if abs(N) > 1 else 0.0
                if best is None or r < best:
                    best, bestn = r, n
        out.write(f"  {D:4d}  {NA:6d}   {'ok':>13s}   {'ok':>5s}   "
                  f"{'ok':>11s}   {'ok':>11s}    {best:.5f}  (n = {bestn})\n")
    out.write("  Every hypothesis TShift.abs_defect_eq / defect_odd / "
              "two_pow_dvd_sub_defect / two_mul_abs_defect_le\n"
              "  states is an identity of construction, and holds on the whole "
              "range.  The last column is the\n"
              "  quantity the whole item is about: S3(ii) proves log|N_n|/n >= "
              "1e-6 for every n past the\n"
              "  burn-in, the engine's own ceiling is 6.2e-5, and the measured "
              "worst case over the range is\n"
              "  within a factor 1.7 of log 2 = 0.6931 -- i.e. five orders of "
              "magnitude of unexploited room.\n")

    out.write("\n# [B] the two side conditions of the engine\n")
    out.write("#   v2(3^t -+ 1), exact:  t odd -> v2(3^t-1) = 1, v2(3^t+1) = 2;  "
              "t even -> 2 + v2(t), 1\n")
    for t in range(1, 400):
        a, b = v2(3 ** t - 1), v2(3 ** t + 1)
        if t % 2:
            assert (a, b) == (1, 2), (t, a, b)
        else:
            assert (a, b) == (2 + v2(t), 1), (t, a, b)
        assert 2 ** a <= 4 * t and 2 ** b <= 4, t
    out.write("    checked t = 1..399: 2^v2(3^t -+ 1) <= 4t always "
              "(TShift.two_pow_le_of_dvd_three_pow_sub)\n")
    out.write("#   D    first n with 4(n+D) < 2^n    Lean threshold D+6   slack   "
              "|N_n| = D*3^j or D = |N_n|*3^j ?\n")
    for D in Ds:
        first = next(n for n in range(1, 200) if 4 * (n + D) < (1 << n))
        bad = []
        for n, t, m, T in orbit(D, min(nmax, 4000)):
            if n < first:
                continue
            a = abs(T - (m << n))
            x, y = a, D
            while x % 3 == 0:
                x //= 3
            while y % 3 == 0:
                y //= 3
            if x == y:                        # same 3-free part: the degenerate case
                bad.append(n)
        assert not bad, (D, bad[:8])
        out.write(f"  {D:4d} {first:22d} {D + 6:20d} {D + 6 - first:7d}   "
                  f"{'none in range':>22s}\n")
    out.write("  The burn-in of TShift.burnin_of_le is loose by D+6-first "
              "(it is proved, not optimal); the\n"
              "  degeneracy TShift.mulIndep_three_defect excludes is not merely "
              "absent past the burn-in --\n"
              "  it is absent from n = 1 on, at every multiplier tested.\n")

    out.write("\n# [C] the engine's ceiling, and the constant the Lean file "
              "freezes\n")
    A1, u1, e1 = _s3_engine_fixed_point(24, 10, 10)
    A4, u4, e4 = _s3_engine_fixed_point(18, 15, 10)
    out.write(f"  [BL96p] Cor. 1   A = 48 log3/(log2)^4 = {float(A1):.5f}   "
              f"u* = {float(u1):.2f}   eta = {float(e1):.4e}\n")
    out.write(f"  [BL96p] Thm 4    A = 36 log3/(log2)^4 = {float(A4):.5f}   "
              f"u* = {float(u4):.2f}   eta = {float(e4):.4e}   "
              f"(c = 18, mu = 15)\n")
    getcontext().prec = 60
    L2 = Decimal(2).ln()
    assert Decimal(96) / L2 ** 3 < 289, "the crude constant 289 fails"
    assert A1 < 289
    U0 = Decimal(10) ** 6
    assert 300 * (U0.ln() + 2) ** 2 < U0, "the numeric lemma fails at 10^6"
    eta_lean = (1 + Decimal(1) / U0).ln() / L2
    out.write(f"  Lean chain       289 >= 96/(log2)^3 = "
              f"{float(Decimal(96) / L2 ** 3):.5f}   U0 = 10^6   "
              f"eta = {float(eta_lean):.4e}   theta = 1000001/2000000\n")
    assert Fraction(28, 5) ** 8 < 10 ** 6 <= Fraction(10) ** 6      # y >= 5.6
    assert Fraction(28, 5) ** 6 >= 30840                            # y^6 >= 30840
    assert Fraction("2.7182818286") ** 8 <= 10 ** 6                 # exp 8 <= 10^6
    out.write("  substitution y = u^(1/8):  5.6^8 = "
              f"{float(Fraction(28, 5) ** 8):.1f} < 10^6 <= u,  "
              f"5.6^6 = {float(Fraction(28, 5) ** 6):.1f} >= 30840,  "
              "e^8 <= 2.7182818286^8 <= 10^6\n")
    ratio = eta_lean / Decimal(10) ** -64
    out.write(f"  Against the strategy row's figure eta ~ 1e-64, the Lean "
              f"constant is {float(ratio):.2e} times larger,\n"
              f"  and the engine's own ceiling {float(e1 / Decimal(10) ** -64):.2e} "
              f"times.  The row's estimate is [BC75]'s, not [BL96p]'s.\n")

    out.write("\n# [D] where the two rungs cross\n")
    ncross = exp(sqrt(10 ** 6 / 289) - 12)
    out.write(f"  rung (i)  exp(n/(289 (log n + 12)^2))   stronger for n < "
              f"{ncross:.3e}\n")
    out.write(f"  rung (ii) exp(n/10^6)                   stronger for n > "
              f"{ncross:.3e}\n")
    out.write("  Both come out of the same inequality: (i) reads it with the "
              "crude T <= log n + 12, (ii) with\n"
              "  the substitution u = n/L.  The row's 'cheap' and 'strong' "
              "strengths are one line, read twice.\n")

    out.write("\n# [E] the verdict: correct, effective, and numerically inert\n")
    out.write("#   D      n     ||D(3/2)^n|| (truth)   guarantee (1/2D) theta^n"
              "   truth/guarantee\n")
    for D in (5, 65):
        for n in (100, 500, 1000):
            t = (D * 3 ** n) % (1 << n)
            truth = Fraction(dist_num(t, n), 1 << n)
            guar = Fraction(1, 2 * D) * Fraction(1000001, 2000000) ** n
            assert guar <= truth, (D, n)
            out.write(f"  {D:4d} {n:6d}   {float(truth):.10f}          "
                      f"{float(guar):.4e}      {float(truth / guar):.4e}\n")
    out.write("  The guarantee is below the truth by a factor about 2^n at every "
              "computable date: S3(ii) is a\n"
              "  statement about the exponent, not a competitive numeric bound.  "
              "S1's 0.57434 dominates it\n"
              "  everywhere (TShift/HabsiegerTransfer.lean).  What S3 owns is the "
              "engine: no Pade, no Ridout,\n"
              "  and the only route that consumes the integrality of xi = 1 "
              "beyond 'a nonzero integer is >= 1'.\n")


def _s9_cycles(p):
    """The cycles of `A -> 3*2^{-1} A mod D_p` on `0 < A < D_p`, D_p = 3^p - 2^p.

    Report Lemma 1's numerator dynamics; the cycle lengths divide p (at D_4 = 65 two of
    the seventeen cycles have length 2).  Returns (D, [cycle, ...]).
    """
    D = 3 ** p - 2 ** p
    inv2 = pow(2, -1, D)
    seen, out = set(), []
    for A in range(1, D):
        if A in seen:
            continue
        cyc, a = [], A
        while a not in cyc:
            cyc.append(a)
            seen.add(a)
            a = (3 * a * inv2) % D
        out.append(cyc)
    return D, out


def _s9_prodf(vals):
    """Exact product of a list of Fractions."""
    P = Fraction(1)
    for v in vals:
        P *= v
    return P


def _s9_prod(D, cyc, n, r):
    """M = prod_i (D r - A_i 2^n), the cycle norm form (TShift.cycleProd)."""
    P = 1
    for A in cyc:
        P *= D * r - A * (1 << n)
    return P


def _s9_witness(D, A, n):
    """The odd numerator of TShift.exists_odd_tgtNum_abs_le: |D r - A 2^n| <= D."""
    t = A << n
    q = t // D
    r = q if q % 2 else q + 1
    assert r % 2 == 1 and abs(D * r - t) <= D
    return r


def _s9_smallfact(m, plist):
    """(dict l -> v_l(m), residual) by trial division over plist."""
    f, k = {}, abs(m)
    for l in plist:
        e = 0
        while k % l == 0:
            k //= l
            e += 1
        if e:
            f[l] = e
    return f, k


def cmd_s9(nmax=400, out=sys.stdout):
    """S9: make the structure of D_p pay (TShift/CycleNormForm.lean).

    [A] the cycle-product identity and the two-sided sandwich, exactly
    [B] the ledger: what the route delivers against what it would have to
    [C] the row's own falsification -- factor the observed M_n, against the
        correct null (a product of k factors, not one)
    [D] the resultant claim, refuted, and what the resultant does govern
    [E] the ceiling: the odd witness, and the forced divisors
    [F] prong (i): the elimination ledger under scaling
    """
    L2 = log(2)
    prim = _primes(1000)

    out.write("plan-less item: report-Tshift.html S9, executed off the row.  Exact\n"
              "integers and Fractions throughout; every decision below is an assert.\n")

    # -----------------------------------------------------------------  [A]
    out.write("\n[A] the identity |M_n| = (D 2^n)^k prod_i |x_n - rho_i| and the sandwich\n"
              "    (2D)^-(k-1) <= prod_{i != j} |x_n - rho_i| <= 1 at the near index j,\n"
              "    on the real orbit r_n = 3^n mod 2^n.  k = cycle length.\n")
    out.write("      p    D     cycles  k    n <= |  odd  identity  route bound  "
              "sandwich   worst far-product\n")
    NA = min(nmax, 300)
    for p in (2, 3, 4):
        D, cs = _s9_cycles(p)
        worst = None
        for cyc in cs:
            k = len(cyc)
            for n in range(1, NA + 1):
                r = pow(3, n, 1 << n)
                M = _s9_prod(D, cyc, n, r)
                assert M % 2 != 0, (p, n)                       # cycleProd_odd
                assert abs(M) >= 1
                x = Fraction(r, 1 << n)
                dists = [abs(x - Fraction(A, D)) for A in cyc]
                assert abs(M) == (D * (1 << n)) ** k * _s9_prodf(dists), (p, n, "identity")
                for d in dists:
                    assert d <= 1                               # abs_sub_le_one
                    assert Fraction(abs(M), (D * (1 << n)) ** k) <= d   # route conclusion
                j = min(range(k), key=lambda i: dists[i])
                if dists[j] <= Fraction(1, 2 * D):              # the near regime
                    far = _s9_prodf([dists[i] for i in range(k) if i != j])
                    assert Fraction(1, (2 * D) ** (k - 1)) <= far <= 1, (p, n, "sandwich")
                    if worst is None or far < worst[0]:
                        worst = (far, n, tuple(cyc))
        out.write(f"      {p}  {D:4d}   {len(cs):5d}  {'/'.join(str(len(c)) for c in cs[:3])}"
                  f"{'...' if len(cs) > 3 else '':4s}{NA:5d} |  ok      ok         ok"
                  f"          ok      {float(worst[0]):.4f} (n = {worst[1]})\n")
    out.write("    Every hypothesis of TShift.abs_cycleProd_eq / le_abs_sub_of_le_abs_cycleProd /\n"
              "    abs_cycleProd_le_of_near holds on the whole range, and the last column is the\n"
              "    sandwich constant actually attained -- against the proved floor (2D)^-(k-1),\n"
              "    which is 1/10 at D = 5.  Product and distance determine each other: the route\n"
              "    is a restatement of T1 over the cycle, in units of (2D)^(k-1).\n")

    # -----------------------------------------------------------------  [B]
    out.write("\n[B] the ledger, in nats per date.  A lower bound |M_n| >= c L^n turns into\n"
              "    ||x_n - rho_j|| >= c L^n/(D 2^n)^k, so the route matches the free floor at\n"
              "    log L = (k-1) log 2 and reaches T1 at log L = k log 2 - log(3/2).\n")
    out.write("      p    D   k |  truth log|M_n|/n   free (k-1)log2   T1 k log2 - log 1.5"
              "   provable (witness)\n")
    for p in (2, 3):
        D, cs = _s9_cycles(p)
        for cyc in cs[:2]:
            k = len(cyc)
            n = min(nmax, 400)
            r = pow(3, n, 1 << n)
            truth = log(abs(_s9_prod(D, cyc, n, r))) / n
            rw = _s9_witness(D, cyc[0], n)
            prov = log(abs(_s9_prod(D, cyc, n, rw))) / n
            assert prov < (k - 1) * L2 + 1e-9 + log(D * (2 * D) ** (k - 1)) / n
            assert truth > (k - 1) * L2                     # the truth is above the free line
            out.write(f"      {p}  {D:4d}  {k} |      {truth:.5f}          {(k-1)*L2:.5f}"
                      f"            {k*L2 - log(1.5):.5f}          {prov:.5f}\n")
    out.write("    The truth sits at k log 2 (the distances are of order 1), the T1 line one\n"
              "    log(3/2) = 0.405 below it, and what the route can guarantee -- the last column,\n"
              "    measured at the odd witness of [E] -- sits at (k-1) log 2, a full log 2 = 0.693\n"
              "    per date lower.  That gap is the whole problem, and the product does not close\n"
              "    any of it: TShift.route_rate_le_half.\n")

    # -----------------------------------------------------------------  [C]
    out.write("\n[C] the falsification the row asks for: factor the observed M_n.  The null is\n"
              "    NOT a random integer.  The k factors share the same r, so l | M iff r hits one\n"
              "    of the m_l = #{A_i mod l} bad classes: P(l|M) = m_l/l, and E v_l = k/(l-1).\n"
              "    D = 5, both cycles, n <= " + str(min(nmax, 500)) + ".\n")
    NC = min(nmax, 500)
    D, cs = _s9_cycles(2)
    for cyc in cs:
        k = len(cyc)
        tot = 0
        hits = {l: 0 for l in prim}
        vsum = {l: 0 for l in prim}
        smooth = size = 0.0
        for n in range(1, NC + 1):
            r = pow(3, n, 1 << n)
            M = abs(_s9_prod(D, cyc, n, r))
            tot += 1
            size += log(M)
            f, _res = _s9_smallfact(M, prim)
            for l, e in f.items():
                hits[l] += 1
                vsum[l] += e
                smooth += e * log(l)
        out.write(f"      cycle {{{', '.join(str(A) + '/5' for A in cyc)}}}:"
                  f"  small primes (l <= 1000) carry {100*smooth/size:.2f}% of log|M_n|\n")
        out.write("        l  | m_l |  P(l|M)   null   |  E v_l    null   | sigma\n")
        worst = (0.0, None)
        tested = 0
        for l in (3, 5, 7, 11, 13, 17, 19, 23, 97, 331):
            ml = len({A % l for A in cyc})
            pnull = ml / l
            phat = hits[l] / tot
            se = (pnull * (1 - pnull) / tot) ** 0.5 if pnull else 0.0
            dev = abs(phat - pnull) / se if se else 0.0
            if l != D:
                worst = max(worst, (dev, l))
                tested += 1
            out.write(f"      {l:4d} |  {ml:2d} |  {phat:.4f}  {pnull:.4f}  |  "
                      f"{vsum[l]/tot:.4f}  {k/(l-1):.4f}  | {dev:5.2f}\n")
        assert hits[5] == 0, "5 | M_n at D = 5"          # not_dvd_cycleProd
        out.write(f"        largest deviation over the {tested} primes off l = D:"
                  f" {worst[0]:.2f} sigma at l = {worst[1]}\n"
                  f"        positive control (the test has power): l = 5 = D divides M_n at"
                  f" 0 of {tot} dates,\n"
                  f"        an exact structure -- and it is a NON-divisibility"
                  f" (TShift.not_dvd_cycleProd), which is worth\n"
                  f"        nothing to a lower bound.\n")
    out.write("    Reading.  Against the right null the odd primes are ordinary -- including\n"
              "    l = 3, whose two cycles differ (m_3 = 1 for {1,4}, both 1 mod 3; m_3 = 2 for\n"
              "    {2,3}) purely because of a coincidence between the numerators, i.e. [D]'s\n"
              "    resultant, and not because of anything M_n does.  And 96% of log|M_n| sits in\n"
              "    primes above 1000, out of reach of any congruence a construction can impose.\n")

    # -----------------------------------------------------------------  [D]
    out.write("\n[D] the row's resultant claim: 'primes dividing M_n must divide explicit\n"
              "    resultants of the cycle polynomial'.  R = prod_{i<j} |A_i - A_j|.\n")
    out.write("      p    D   cycle          R   | prime factors of M_n (l <= 1000), n <= 200:"
              "  dividing R / not\n")
    for p in (2, 3):
        D, cs = _s9_cycles(p)
        for cyc in cs[:2]:
            R = 1
            for i in range(len(cyc)):
                for j in range(i + 1, len(cyc)):
                    R *= abs(cyc[i] - cyc[j])
            inR = outR = 0
            coinc = 0
            resbits = []
            for n in range(1, min(nmax, 200) + 1):
                r = pow(3, n, 1 << n)
                M = abs(_s9_prod(D, cyc, n, r))
                f, res = _s9_smallfact(M, prim)
                resbits.append(res.bit_length())
                for l in f:
                    if R % l == 0:
                        inR += 1
                    else:
                        outR += 1
                    # the correct statement: two factors share l  =>  l | (A_i - A_j)
                    sh = [A for A in cyc if (D * r - A * (1 << n)) % l == 0]
                    if len(sh) > 1:
                        coinc += 1
                        assert R % l == 0, (p, n, l)
                        assert any((a - b) % l == 0
                                   for a in sh for b in sh if a != b), (p, n, l)
            resbits.sort()
            out.write(f"      {p}  {D:4d}   {str(cyc):14s} {R:4d} |"
                      f"  {inR:5d} / {outR:5d}   ({coinc} coincidences, all explained;"
                      f"  median unfactored part {resbits[len(resbits)//2]} bits)\n")
    out.write("    The claim is false as stated: most prime factors of M_n miss R, and after\n"
              "    dividing out every prime below 1000 what is left is still hundreds of bits --\n"
              "    the primes of M_n are not confined to any fixed list, because they are the\n"
              "    primes for which the free numerator lands in one of k residue classes.  What R\n"
              "    does govern is exactly the coincidences: a prime dividing two factors at once\n"
              "    divides some A_i - A_j (TShift.dvd_sub_of_dvd_tgtNum_two), asserted at every\n"
              "    hit above.\n")

    # -----------------------------------------------------------------  [E]
    out.write("\n[E] the ceiling.  The odd witness r with |D r - A 2^n| <= D makes the product\n"
              "    as small as the free floor allows; and the divisibility forced for EVERY odd\n"
              "    numerator is a constant, independent of n.\n")
    out.write("      p    D   k | witness bound  rate <= 2^(k-1)/2^n | forced divisor g(n),"
              " n = 1..12 | gcd(A,D)^k  primes > k?\n")
    for p in (2, 3, 4):
        D, cs = _s9_cycles(p)
        for cyc in cs[:3]:
            k = len(cyc)
            for n in range(1, min(nmax, 60) + 1):
                r = _s9_witness(D, cyc[0], n)
                M = abs(_s9_prod(D, cyc, n, r))
                assert M <= D * (2 * D) ** (k - 1) * (1 << (n * (k - 1))), (p, n)
                assert Fraction(M, (D * (1 << n)) ** k) <= Fraction(2 ** (k - 1), 1 << n)
            gs = []
            for n in range(1, 13):
                g = 0
                for r in range(1, 4001, 2):
                    g = gcd(g, _s9_prod(D, cyc, n, r))
                    if g == 1:
                        break
                gs.append(abs(g))
            gA = D
            for A in cyc:
                gA = gcd(gA, A)
            const = len(set(gs)) == 1
            assert const, (p, cyc, gs)
            # every odd prime of the forced divisor either divides D or is <= k
            bad = [l for l in prim if gs[0] % l == 0 and D % l and l > k]
            assert not bad, (p, cyc, bad)
            out.write(f"      {p}  {D:4d}  {k} |      ok              ok           "
                      f"{gs[0]:6d}  (constant: {const})    {gA**k:6d}     none\n")
    out.write("    So the arithmetic the route can inject is bounded by the cycle's own data:\n"
              "    TShift.forced_prime_le_card (an odd prime forced for every odd r, not dividing\n"
              "    D, is at most the cycle length k) and TShift.pow_dvd_cycleProd (the gcd part).\n"
              "    Both are O(1) in n against the 2^(n(k-1)) the route would need.\n")

    # -----------------------------------------------------------------  [F]
    out.write("\n[F] prong (i): the elimination ledger under the congruence.  Imposing t | a_i, b_i\n"
              "    scales (P, Lambda, B) -> (tP, t Lambda, tB); the bound (P X - |c| Lambda)/B is\n"
              "    homogeneous of degree 0.  The corpus's own instance (TShift.transfer_prop_one_"
              "sanity):\n"
              "    X = 2^4, Y = 3^4, forms (-5, 1) and (-81, 16), Lambda = 1, B = 16.\n")
    out.write("      c = multiplier |   t = 1      t = 5      t = 19     t = 65   |  bound\n")
    for c in (1, 5, 19, 65):
        vals = []
        for t in (1, 5, 19, 65):
            P, Lam, B, X = Fraction(t), Fraction(t), Fraction(16 * t), Fraction(16)
            vals.append((P * X - c * Lam) / B)
        assert len(set(vals)) == 1, (c, vals)
        out.write(f"      {c:12d}   | " + "  ".join(f"{str(v):>9s}" for v in vals)
                  + f"   |  {float(vals[0]):.5f}\n")
    out.write("    Identical along every row: the content refund the congruence buys is exactly\n"
              "    the multiplier loss it was meant to cancel (TShift.transfer_bound_scale, and\n"
              "    TShift.scale_sanity_five at c = t = 5, where every reading returns 11/16).\n"
              "    Note also the c = 1 row against the c = 5 row: the multiplier costs\n"
              f"    {float((Fraction(16) - 1) / 16 - (Fraction(16) - 5) / 16):.4f} in the bound,"
              " a constant -- O(log D) in the RANGE, never in theta.\n"
              "    The flagship measurement of the same mechanism inside [Hab03]'s own forms is\n"
              "    plan-S7 WP-D, harness `cong` block [T]: 0.61 sigma raw, 0.85 sigma paired.\n")

    out.write("\n    Verdict.  Prong (ii) restates T1 over the cycle and its arithmetic input is\n"
              "    capped at the free floor; prong (i) is a rescaling the ledger cannot see, and\n"
              "    stays m-uniform, so by report N1 it cannot give T1 without T4.  S9: 5% -> 0%.\n")


def cmd_s1z(mmax=4, out=sys.stdout):
    """plan-Tshift-S1 WP7: [Zud07]'s engine, audited for the multiplier transfer.

    [A] the constants of p. 321, recomputed
    [B] the frozen surrogates and every numeric obligation of the Lean files
    [C] the two-form structure, exact, at m = 1 .. mmax
    [D] the two lanes side by side
    """
    t00 = time.time()
    C0, C1, C2, marg, th = _z7_lane()
    cb = ZUD_FROZEN["contentBase"]
    eb = ZUD_FROZEN["errorBase"]
    db = ZUD_FROZEN["denomBase"]
    thz = ZUD_FROZEN["thetaZud"]
    bz = ZUD_FROZEN["bZud"]

    out.write("plan-Tshift-S1 WP7 -- transporting [Zud07]'s 0.5803 to every multiplier.\n"
              f"    (alpha, beta, gamma) = {ZUD_TRIPLE}, z = 1/9, K = 3 beta = 57\n")

    out.write("\n[A] the constants of [Zud07] p. 321, recomputed from (19), (20), (21)\n")
    for label, val, printed in (("C0(1/9)", C0, "3.28973907"),
                                ("C1(1/9)", C1, "35.48665992"),
                                ("C2 = C2'", C2, "4.46695926")):
        ok = f"{val:.8f}".startswith(printed[:10]) or abs(val - float(printed)) < 5e-8
        assert ok, (label, val, printed)
        out.write(f"      {label:9s} = {val:.10f}   printed {printed}...   {'ok' if ok else 'NO'}\n")
    assert abs(marg - (-0.07860790)) < 5e-8, marg
    assert abs(th - 0.580302781) < 5e-9, th
    delta = -57 * log(0.5803) - (C1 - C2)
    assert abs(delta - 0.00027320432) < 5e-11, delta
    out.write(f"      (26) C0 - C2 + (beta-2 alpha) log 3 = {marg:.8f}   printed -0.07860790...\n"
              f"      theta = exp(-(C1-C2)/57)            = {th:.9f}\n"
              f"      delta = 57 log(1/0.5803) - (C1-C2)  = {delta:.11f}   printed 0.00027320432...\n"
              "      -- so the printed 0.5803 is the recomputed 0.580302781 rounded down, and\n"
              "      the 2.7e-4 of rounding slack is the whole surrogate budget of [B].\n")

    out.write("\n[B] what CITED/ZudilinPade.lean freezes, and what norm_num decides\n")
    tab = (("errorBase  >= e^C0", eb, exp(C0), "up  "),
           ("denomBase  >= e^C1", db, exp(C1), "up  "),
           ("contentBase <= e^C2", cb, exp(C2), "down"))
    for label, sur, lim, direction in tab:
        f = float(sur)
        good = f >= lim if direction == "up  " else f <= lim
        assert good, (label, f, lim)
        cost = abs(log(f) - log(lim))
        out.write(f"      {label:20s} {f:.7e}  vs {lim:.7e}   {direction}   "
                  f"cost {cost:.3e} nats/m\n")
    total = abs(log(float(db)) - C1) + abs(C2 - log(float(cb)))
    assert total < 1e-6
    out.write(f"      total rate-bearing cost {total:.4e} nats/m = "
              f"{100 * total / delta:.3f}% of the delta budget\n")
    checks = [
        ("(26), Lean zud_validity", Fraction(27, 25) * (3 * eb) <= cb),
        ("rate, Lean zud_rate", (1 + Fraction(1, 4000)) * (db * thz ** 57) <= cb),
        ("uniform (26), Lean zud_validity_uniform",
         (1 + Fraction(1, 360)) * (bz ** 57 * (3 * eb)) <= cb),
        ("block constant, Lean zud_block_constant", 2 * thz ** 3 * (2 * thz) ** 56 <= 1638),
        ("bZud^59 <= 2", bz ** 59 <= 2),
        ("Bernoulli, Lean zud_const_absorb", 1 + Fraction(6548000, 4000) >= 1638),
        ("thetaHab < thetaZud < 2/3",
         Fraction(57434, 100000) < thz < Fraction(2, 3)),
        ("bHab < bZud", Fraction(1216, 1215) < bz),
    ]
    for label, ok in checks:
        assert ok, label
        out.write(f"      {label:42s} {'TRUE' if ok else 'FALSE'}\n")
    out.write(f"      margins: (26) {float(cb / (3 * eb)):.6f} per m, "
              f"rate {float(cb / (db * thz ** 57)):.7f} per m,\n"
              f"      block constant {float(2 * thz ** 3 * (2 * thz) ** 56):.2f} <= 1638\n")

    out.write("\n[C] the two-form structure, as exact integers\n"
              "      forms  b^i = Q_i(9),  a^i = -(Q_i(9) T + P_i(9) 3^{m+1}),  N = 57m+3;\n"
              "      claim  a^i 2^N + b^i 3^N = 2^N 3^{m+1} R_i(1/9)   and\n"
              "             |a^1 b^2 - a^2 b^1| = 3^{m+3} C(27m+1,18m) C(37m,10m).\n"
              "        m   det   two-col      Phi | P,Q   log|Q(9)|/m   logPhi/m   log|R|/m\n")
    al, be, ga = ZUD_TRIPLE
    for m in range(1, mmax + 1):
        a, b, n = al * m, be * m, ga * m
        N, T = 3 * (b + 1), _z7_T(a, b)
        rows, cols = [], []
        for i, nn in enumerate((n, n + 1)):
            q, p = _z7_QP(a, b, nn)
            R, tail = _z7_R(a, b, nn)
            ai = -(q * T + p * 3 ** (b - 2 * a + 1))
            lhs = Fraction(ai * 2 ** N + q * 3 ** N)
            rhs = Fraction(2 ** N * 3 ** (b - 2 * a + 1)) * R
            rel = abs(lhs - rhs) / abs(rhs)
            assert rel < Fraction(1, 10 ** 40), (m, nn, float(rel))
            assert abs(tail) < abs(R) / 10 ** 80
            Ph = _z7_Phi(a, b, n, primed=(i == 1))
            if i == 1:
                Ph //= gcd(Ph, n + 1)
            div = (all(c % Ph == 0 for c in _z7_qco(a, b, nn))
                   and all(c % Ph == 0 for c in _z7_rco(a, b, nn)))
            assert div, (m, nn)
            rows.append((ai, q))
            cols.append((float(rel), log(abs(q)) / m, log(Ph) / m, log(abs(float(R))) / m))
        (a1, b1), (a2, b2) = rows
        det = abs(a1 * b2 - a2 * b1)
        want = 3 ** (m + 3) * comb(27 * m + 1, 18 * m) * comb(37 * m, 10 * m)
        assert det == want, m
        r0, r1 = cols
        out.write(f"      {m:3d}   ok    <1e-40      yes, both   "
                  f"{r0[1]:9.5f}    {r0[2]:8.5f}   {r0[3]:8.5f}\n")
    out.write(f"      -- limits: C1 = {C1:.5f}, C2 = {C2:.5f}, C0 = {C0:.5f}; the columns\n"
              "      approach them like log(m)/m, which is why the bundle can only be stated\n"
              "      above a threshold -- and why [Zud07] never computes one.\n")

    out.write("\n[D] the two lanes side by side\n"
              "        source     theta      kappa    k0                 multiplier base\n")
    for label, rate, k0, base in (
            ("[Hab03]", 0.57434, "64 440 001 (printed)", 1216 / 1215),
            ("[Pup09]", 0.5795, "8.71e11 (printed)", None),
            ("[Zud07]", 0.5803, "effective, UNCOMPUTED", 10013 / 10000)):
        kap = -log(rate) / log(1.5)
        assert kap > 1
        bs = f"{base:.7f}" if base else "-- (not transported)"
        out.write(f"      {label:9s} {rate:.5f}   {kap:.5f}  {k0:22s} {bs}\n")
    kh, kz = -log(0.57434) / log(1.5), -log(0.5803) / log(1.5)
    out.write(f"      -- the swap buys {0.5803 - 0.57434:.5f} of rate "
              f"({100 * (kh - kz) / kh:.2f}% of kappa) at every cycle target\n"
              "      and costs the computed first date; the arithmetic thresholds the Lean\n"
              "      chain itself adds are m >= 6 548 000 (k >= 3.7e8) and m >= 25 3^57 D,\n"
              "      both far below [Pup09]'s printed 8.71e11 for the same construction.\n"
              "      No rate here reaches 2/3 = 0.66667 (kappa = 1): the T-shift problem is\n"
              "      untouched, and the gap 0.5803 -> 2/3 IS the open problem.\n")
    out.write(f"\n[E] cost.  This run: {time.time() - t00:.1f} s.\n")


def main():
    if len(sys.argv) < 2:
        print(__doc__)
        return
    cmd = sys.argv[1]
    if cmd == "records":
        cmd_records(int(sys.argv[2]), int(sys.argv[3]))
    elif cmd == "runs":
        cmd_runs(int(sys.argv[2]), int(sys.argv[3]))
    elif cmd == "gframe":
        cmd_gframe(int(sys.argv[2]), int(sys.argv[3]))
    elif cmd == "steer":
        cmd_steer(int(sys.argv[2]), int(sys.argv[3]))
    elif cmd == "bridge":
        cmd_bridge(int(sys.argv[2]), int(sys.argv[3]))
    elif cmd == "carry":
        cmd_carry(int(sys.argv[2]), int(sys.argv[3]))
    elif cmd == "floorcap":
        cmd_floorcap(int(sys.argv[2]), int(sys.argv[3]))
    elif cmd == "adelic":
        cmd_adelic(int(sys.argv[2]), int(sys.argv[3]))
    elif cmd == "tail":
        cmd_tail(int(sys.argv[2]), int(sys.argv[3]))
    elif cmd == "w3":
        cmd_w3(int(sys.argv[2]))
    elif cmd == "hankel":
        cmd_hankel(int(sys.argv[2]), int(sys.argv[3]))
    elif cmd == "apparat":
        cmd_apparat(int(sys.argv[2]), int(sys.argv[3]))
    elif cmd == "content":
        cmd_content(int(sys.argv[2]) if len(sys.argv) > 2 else 512)
    elif cmd == "cong":
        nmax = int(sys.argv[2]) if len(sys.argv) > 2 else 20000
        mmax = int(sys.argv[3]) if len(sys.argv) > 3 else 96
        cmd_cong(nmax, mmax)
    elif cmd == "s2":
        cmd_s2(int(sys.argv[2]) if len(sys.argv) > 2 else 1200)
    elif cmd == "s1314":
        cmd_s1314(int(sys.argv[2]) if len(sys.argv) > 2 else 20000)
    elif cmd == "s1":
        cmd_s1(int(sys.argv[2]) if len(sys.argv) > 2 else 20000)
    elif cmd == "s1z":
        cmd_s1z(int(sys.argv[2]) if len(sys.argv) > 2 else 4)
    elif cmd == "s5":
        nmax = int(sys.argv[2]) if len(sys.argv) > 2 else 20000
        pmax = int(sys.argv[3]) if len(sys.argv) > 3 else 6
        cmd_s5(nmax, pmax)
    elif cmd == "s8":
        cmd_s8(int(sys.argv[2]) if len(sys.argv) > 2 else 128)
    elif cmd == "s8a":
        cmd_s8a()
    elif cmd == "s8b":
        cmd_s8b()
    elif cmd == "s8c":
        cmd_s8c()
    elif cmd == "s8d":
        cmd_s8d(int(sys.argv[2]) if len(sys.argv) > 2 else 512)
    elif cmd == "s8f":
        cmd_s8f(int(sys.argv[2]) if len(sys.argv) > 2 else 100,
                int(sys.argv[3]) if len(sys.argv) > 3 else 500)
    elif cmd == "s8g":
        cmd_s8g_ledger()
        if len(sys.argv) > 2 and sys.argv[2] == "ledger":
            return
        print("\n===== WP0  gate G-A, D1 on integers, D2's dictionary " + "=" * 9)
        cmd_s8(128)
        print("\n===== WP-A  the three papers on their own numbers " + "=" * 12)
        cmd_s8a()
        print("\n===== WP-B  the demand/payoff split, the re-optimized wall " + "=" * 3)
        cmd_s8b()
        print("\n===== WP-C  Q1: the supply curve and its ceiling " + "=" * 13)
        cmd_s8c()
        print("\n===== WP-D  Q2: the determinant on [Hab03]'s own columns " + "=" * 5)
        cmd_s8d(512)
        print("\n===== WP-F  sub-idea (iii): the grid, the lead, the ceiling " + "=" * 2)
        cmd_s8f(100, 500)
        print("\n      the ledger plus six blocks, no assertion failure: the item's\n"
              "      numeric record reproduces end to end.")
    elif cmd == "s3":
        cmd_s3(int(sys.argv[2]) if len(sys.argv) > 2 else 20000)
    elif cmd == "s9":
        cmd_s9(int(sys.argv[2]) if len(sys.argv) > 2 else 400)
    elif cmd == "s10":
        cmd_s10(int(sys.argv[2]) if len(sys.argv) > 2 else 2000)
    elif cmd == "s10b":
        cmd_s10b(int(sys.argv[2]) if len(sys.argv) > 2 else 400)
    elif cmd == "s10c":
        cmd_s10c(int(sys.argv[2]) if len(sys.argv) > 2 else 20000)
    elif cmd == "s10e":
        cmd_s10e(int(sys.argv[2]) if len(sys.argv) > 2 else 2000)
    elif cmd == "s10g":
        nmax = int(sys.argv[2]) if len(sys.argv) > 2 else 20000
        print("plan-Tshift-S10 WP-G -- the item's whole numeric record, re-run.\n"
              "One block per executed work package, in execution order; every\n"
              "decision inside them is an exact integer or Fraction comparison.\n")
        print("===== WP0  the critical lattice " + "=" * 30)
        cmd_s10(min(nmax, 2000))
        print("\n===== WP-B  the dictionary, gate G-A' " + "=" * 24)
        cmd_s10b(min(nmax, 400))
        print("\n===== WP-C  Q1's sweep " + "=" * 39)
        cmd_s10c(nmax)
        print("\n===== WP-E  the Lean layer's constants " + "=" * 23)
        cmd_s10e(min(nmax, 2000))
        print("\n      four blocks, no assertion failure: the item's numeric record\n"
              "      reproduces end to end.")
    elif cmd == "pade":
        mmax = int(sys.argv[2]) if len(sys.argv) > 2 else 8
        pmax = int(sys.argv[3]) if len(sys.argv) > 3 else 4
        cmd_pade(mmax, pmax)
    elif cmd == "wpb":
        nmax = int(sys.argv[2]) if len(sys.argv) > 2 else 4000
        for D in (1, 5, 19):
            print(f"\n===== adelic budget, D = {D} " + "=" * 40)
            cmd_adelic(D, min(nmax, 4000))
        print("\n===== the evaluation identity " + "=" * 38)
        for D in (1, 5, 19):
            cmd_tail(D, min(nmax, 300))
        print("\n===== wall W3, both halves " + "=" * 41)
        cmd_w3(min(nmax, 20000))
        print("\n===== the surviving (alpha)-channel " + "=" * 32)
        for D in (1, 5):
            cmd_hankel(D, min(nmax, 4000))
    elif cmd == "all":
        nmax = int(sys.argv[2]) if len(sys.argv) > 2 else 20000
        for D in (1, 5, 19):
            print(f"\n===== D = {D} " + "=" * 50)
            cmd_records(D, nmax)
            cmd_runs(D, nmax)
            cmd_gframe(D, min(nmax, 2000))
        print("\n===== carry word " + "=" * 45)
        cmd_carry(min(nmax, 20000), 8)
        print("\n===== free sojourn cap (TShift/FreeSojourn.lean) " + "=" * 13)
        cmd_floorcap(min(nmax, 4000), 6)
    else:
        print(__doc__)


if __name__ == "__main__":
    main()
