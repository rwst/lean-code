#!/usr/bin/env python3
# (C) 2026 Ralf Stephan, in collaboration with Claude Code.
# Released under CC0 1.0 Universal (public-domain dedication).
# See https://creativecommons.org/publicdomain/zero/1.0/
"""Numeric companion of `BB61/FullSupport.lean` (work package R0 of
`plan-BB61-counterexample.html`, note `note-1061-R0.html`).

`BB61/r0_support.py` checks the *mathematics* of R0 Theorem 1 and Corollary 3.  This
script checks the *Lean encoding*, which is not the same greedy: `FullSupport.lean`
takes the digit `min n floor(w)` at every step, where the note's script takes the
largest digit keeping the residual in `[0, L]`.  The two produce different words, so the
reconstruction has to be re-verified against M1's original definitions of `pi` and `w`.

Everything below mirrors the Lean declaration by declaration:

    covDigitAt n w   = min n (Nat.floor w)          `BB61.covDigitAt`
    covRes r n y 0   = y
    covRes r n y i+1 = (covRes .. i - covDigitAt n (covRes .. i)) / r
    loBit u i        = 1 <= u i                     `BB61.loBit`
    hiBit u i        = 2 <= u i                     `BB61.hiBit`
    consW b a        = b, a 0, a 1, ...             `BB61.consW`
    parityFlip a m   = a m (m even), not a m (m odd)`BB61.parityFlip`

and the two reconstructions are the ones inside `silver_Icc_subset_confSet` and
`goldenSq_Icc_subset_confSet`.  Verdicts are printed one per check; `BB61/r0_lean.json`
records them.
"""

import json
from mpmath import mp, mpf, sqrt, floor

mp.dps = 60

DEPTH = 400          # digits kept in the greedy
GRID = 801           # targets per alpha
TOL = mpf(10) ** (-40)

results = {}


def verdict(name, ok, detail=""):
    results[name] = {"ok": bool(ok), "detail": detail}
    print(f"{'OK  ' if ok else 'FAIL'}  {name}" + (f"   {detail}" if detail else ""))
    return ok


# ---------------------------------------------------------------- the greedy

def cov_digit_at(n, w):
    """`BB61.covDigitAt`: min n (Nat.floor w).  `Nat.floor` is 0 on negatives."""
    f = int(floor(w)) if w >= 0 else 0
    return min(n, f)


def cov_run(r, n, y, depth=DEPTH):
    """Return (digits, residuals) of `BB61.covDigit` / `BB61.covRes`."""
    digits, residuals = [], [y]
    w = y
    for _ in range(depth):
        u = cov_digit_at(n, w)
        digits.append(u)
        w = (w - u) / r
        residuals.append(w)
    return digits, residuals


def digit_sum(u, r):
    """sum_i u_i r^i, the tsum of `tsum_covDigit`."""
    s = mpf(0)
    for i in range(len(u) - 1, -1, -1):
        s = s * r + u[i]
    return s


# ------------------------------------------------------- M1's own definitions

def pi_val(alpha, eps, depth=DEPTH):
    """`piVal alpha eps = (alpha-1) * sum_{k>=0} eps_k alpha^{-(k+1)}`."""
    s = mpf(0)
    inv = 1 / alpha
    for k in range(depth - 1, -1, -1):
        s = s * inv + (1 if eps[k] else 0)
    return (alpha - 1) * s * inv


def w_val(beta, delta, depth=DEPTH):
    """`wVal delta = sum_{m>=0} (beta-1) beta^m delta_m`."""
    s = mpf(0)
    for m in range(depth - 1, -1, -1):
        s = s * beta + (1 if delta[m] else 0)
    return (beta - 1) * s


def lo_bit(u):
    return [x >= 1 for x in u]


def hi_bit(u):
    return [x >= 2 for x in u]


def cons_w(b, a):
    return [b] + list(a)


def parity_flip(a):
    return [a[m] if m % 2 == 0 else (not a[m]) for m in range(len(a))]


# ------------------------------------------------------------------ the two alphas

S2 = sqrt(2)
S5 = sqrt(5)

SILVER = dict(name="1+sqrt2", alpha=1 + S2, beta=1 - S2, rho=S2 - 1,
              lo=-S2 / 2, hi=2 + S2 / 2, L=2 + S2)
GOLDENSQ = dict(name="(3+sqrt5)/2", alpha=(3 + S5) / 2, beta=(3 - S5) / 2,
                rho=(3 - S5) / 2, lo=mpf(0), hi=mpf(2))
GOLDENSQ["L"] = 2 / (1 - GOLDENSQ["rho"])


# ------------------------------------------------------------------ check 1: setups

ok = True
for P in (SILVER, GOLDENSQ):
    a, b = P["alpha"], P["beta"]
    # alpha^2 = a*alpha + b with (a,b) = (2,1) resp. (3,-1)
    tr, nm = (2, 1) if P is SILVER else (3, -1)
    ok &= abs(a ** 2 - tr * a - nm) < TOL
    ok &= abs(b - (tr - a)) < TOL
    ok &= abs(a * abs(b) - 1) < TOL          # both are units
verdict("setups", ok, "alpha^2 = a alpha + b, beta = a - alpha, |N| = 1 at both")

# ------------------------------------------------------- check 2: covering condition

ok = True
for P in (SILVER, GOLDENSQ):
    rho, L = P["rho"], P["L"]
    ok &= abs(2 + rho * L - L) < TOL          # `hL`: n + rL = L at n = 2
    ok &= rho * L >= 1                        # `hrL`
verdict("covering_condition", ok,
        f"rho*L = {mp.nstr(SILVER['rho']*SILVER['L'], 10)} (silver), "
        f"{mp.nstr(GOLDENSQ['rho']*GOLDENSQ['L'], 10)} (goldenSq); both >= 1")

# ------------------------------------------------- check 3: the greedy invariant

ok = True
worst = mpf(0)
for P in (SILVER, GOLDENSQ):
    rho, L = P["rho"], P["L"]
    for j in range(GRID):
        t = L * mpf(j) / (GRID - 1)
        digits, residuals = cov_run(rho, 2, t, depth=120)
        ok &= all(0 <= d <= 2 for d in digits)
        for w in residuals:
            ok &= (w >= -TOL) and (w <= L + TOL)
            worst = max(worst, abs(w - min(max(w, mpf(0)), L)))
verdict("greedy_invariant", ok,
        f"digits in {{0,1,2}} and residual in [0,L] at every step; slack {mp.nstr(worst, 3)}")

# --------------------------------------------- check 4: tsum_covDigit reproduces y

ok = True
worst = mpf(0)
for P in (SILVER, GOLDENSQ):
    rho, L = P["rho"], P["L"]
    for j in range(GRID):
        t = L * mpf(j) / (GRID - 1)
        digits, _ = cov_run(rho, 2, t)
        err = abs(digit_sum(digits, rho) - t)
        worst = max(worst, err)
        ok &= err < TOL
verdict("tsum_covDigit", ok, f"max |sum u_i rho^i - t| = {mp.nstr(worst, 3)}")

# ------------------------------- check 5: the silver reconstruction (Theorem 1)

ok = True
worst = mpf(0)
alpha, beta, rho = SILVER["alpha"], SILVER["beta"], SILVER["rho"]
b_true_count = 0
for j in range(GRID):
    y = SILVER["lo"] + (SILVER["hi"] - SILVER["lo"]) * mpf(j) / (GRID - 1)
    w = (y + S2 / 2) / S2
    b = w > S2                                      # `decide (sqrt 2 < w)`
    b_true_count += 1 if b else 0
    d0 = mpf(1) if b else mpf(0)
    ok &= (0 <= w <= 1 + S2 + TOL)                  # `hw0`, `hw1`
    ok &= (-TOL <= w - d0 <= S2 + TOL)              # `hstep`
    t = (w - d0) / rho
    u, _ = cov_run(rho, 2, t)
    eps = lo_bit(u)
    a = cons_w(b, hi_bit(u))
    delta = parity_flip(a)
    err = abs(pi_val(alpha, eps) - w_val(beta, delta) - y)
    worst = max(worst, err)
    ok &= err < TOL
verdict("silver_reconstruction", ok,
        f"max |pi(eps) - w(delta) - y| = {mp.nstr(worst, 3)} over {GRID} targets; "
        f"top bit set at {b_true_count}/{GRID}")

# ----------------------------- check 6: the goldenSq reconstruction (Corollary 3)

ok = True
worst = mpf(0)
alpha, beta, rho = GOLDENSQ["alpha"], GOLDENSQ["beta"], GOLDENSQ["rho"]
for j in range(GRID):
    y = GOLDENSQ["lo"] + (GOLDENSQ["hi"] - GOLDENSQ["lo"]) * mpf(j) / (GRID - 1)
    t = y / (1 - rho)
    u, _ = cov_run(rho, 2, t)
    eps, delta = lo_bit(u), hi_bit(u)
    err = abs(pi_val(alpha, eps) - w_val(beta, delta) - y)
    worst = max(worst, err)
    ok &= err < TOL
verdict("goldenSq_reconstruction", ok,
        f"max |pi(eps) - w(delta) - y| = {mp.nstr(worst, 3)} over {GRID} targets")

# ------------------------------------------------- check 7: the window P and Q

def w_max_min(beta, depth=DEPTH):
    """`wMax = sum max(c_m,0)`, `wMin = sum min(c_m,0)` with c_m = (beta-1) beta^m."""
    hi = lo = mpf(0)
    for m in range(depth):
        c = (beta - 1) * beta ** m
        hi += max(c, mpf(0))
        lo += min(c, mpf(0))
    return hi, lo

hi_s, lo_s = w_max_min(SILVER["beta"])
hi_g, lo_g = w_max_min(GOLDENSQ["beta"])
ok = (abs(hi_s - S2 / 2) < TOL and abs(lo_s + 1 + S2 / 2) < TOL
      and abs(hi_g) < TOL and abs(lo_g + 1) < TOL)
verdict("window_endpoints", ok,
        f"silver P = {mp.nstr(hi_s, 10)} = sqrt2/2, Q = {mp.nstr(-lo_s, 10)} = 1+sqrt2/2; "
        f"goldenSq P = 0, Q = 1")

# --------------------------------------- check 8: the hull, and F1's sharpness

ok = True
for P, (hi_w, lo_w) in ((SILVER, (hi_s, lo_s)), (GOLDENSQ, (hi_g, lo_g))):
    ok &= abs(P["lo"] - (0 - hi_w)) < TOL           # -P
    ok &= abs(P["hi"] - (1 - lo_w)) < TOL           # 1+Q
    ok &= abs((P["hi"] - P["lo"]) - (1 + (hi_w - lo_w))) < TOL
    ok &= (P["hi"] - P["lo"]) > 1                   # onto the circle
verdict("hull_sharpness", ok,
        f"interval = [-P, 1+Q], length 1+diam K = "
        f"{mp.nstr(SILVER['hi']-SILVER['lo'], 10)} (silver), "
        f"{mp.nstr(GOLDENSQ['hi']-GOLDENSQ['lo'], 10)} (goldenSq); both > 1")

# ------------------------------------- check 9: the unit interval is inside both

ok = all(P["lo"] <= 0 and 1 <= P["hi"] for P in (SILVER, GOLDENSQ))
verdict("unit_interval_inside", ok,
        "[0,1] subset C-K at both, which is what `confCircle_eq_univ_of_Icc_subset` needs")

# ------------------------------------ check 10: the exact constant of (S2) at 1+sqrt2

rho = SILVER["rho"]
odd = sum(rho ** m for m in range(1, DEPTH, 2))
even = sum(rho ** m for m in range(0, DEPTH, 2))
ok = (abs(odd - mpf(1) / 2) < TOL
      and abs(odd - rho / (1 - rho ** 2)) < TOL
      and abs(even - (S2 + 1) / 2) < TOL)
verdict("silver_parity_constants", ok,
        f"sum_odd rho^m = {mp.nstr(odd, 20)} = 1/2 exactly; "
        f"sum_even rho^m = {mp.nstr(even, 12)} = (sqrt2+1)/2")

# ---------------------------------------------------------------------- summary

allok = all(v["ok"] for v in results.values())
print()
print(f"{sum(v['ok'] for v in results.values())}/{len(results)} checks OK"
      f" at mp.dps = {mp.dps}, depth {DEPTH}, {GRID} targets per alpha")
with open("BB61/r0_lean.json", "w") as f:
    json.dump(results, f, indent=1, sort_keys=True)
raise SystemExit(0 if allok else 1)
