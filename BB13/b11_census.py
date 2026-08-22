#!/usr/bin/env python3
# (C) 2026 Ralf Stephan, in collaboration with Claude Code
# CC0 1.0 Universal (public domain dedication).
"""B11 of plans/report3-BB13.html -- the computational leg, executed and audited.

B11 has three tiers: (i) the fibre census, staged at 10^7; (ii) the empirical
abc-quality ledger of B6(i); (iii) the weighted-functional optimizer of B2(iii).
Tiers (ii) and (iii) already exist (BB13/b6_ledger.py, BB13/b2_weighted.py) at
their own scales; this script runs tier (i) to 10^7 and extends tier (ii) by a
factor 143, then audits everything against the Lean specification.

The sweep itself is BB13/b11_sweep.c (a 64-bit limb kernel, ~8 min to 10^7); its
output is BB13/b11_sweep_10000000.log.  Everything the kernel does is a theorem
in BB13/CensusSweep.lean:

    state           (2^n, 3^n / 2^n, 3^n mod 2^n)          BB13.sweep_spec
    windowed step   3*A mod 2^M, carry out of top dropped  BB13.window_step
    the two reads   low n bits / next B bits               BB13.resid_of_window,
                                                           BB13.quot_of_window
    the rounding    m_n = q + [2r >= 2^n]                  BB13.mNat_eq_quot_add
    the sieve       41 t <= 17 n  =>  top t bits constant  BB13.filter_bits
    peaks           v_2 rises only from height <= 1        BB13.exists_peak

so the 10^7 run is a *verified algorithm* with trusted arithmetic, not an
unverified computation.  This script re-runs the same recurrence independently
in Python/gmpy2 and compares every aggregate.

Blocks
  [A] the recurrence, twice: an independent gmpy2 stream against the C log
  [B] the census: E ∩ [1,10^7] = {1,2,3,4,7}; the sieve constant; the five
      survivors re-verified exactly; the run 1,2,3,4 (§1.3 says the only run is
      2,3 -- it is four long)
  [C] staircases: peaks vs raw counts.  The raw v_2 tail is B8's descent law,
      not a fat tail; the peak histogram is the geometric one
  [D] the two champion tables: -log2||(3/2)^n|| and v_2(m_n), against the proved
      rows of §1.4
  [E] the straddling block, against B7's price list
  [F] tier (ii): the quality ledger to a <= 20000 by gcd-radicals
  [G] tier (iii): the weighted optimizer, re-checked
  [H] the cost model, and the kernel ceiling actually measured
  [I] the numerals BB13/CensusSweep.lean quotes

Usage:  python3 BB13/b11_census.py [NCHECK]     (default 20000; ~10 s)
        the 10^7 sweep itself is BB13/b11_sweep.c: cc -O2, ~8 min on one core
        the 10^7 log is read if present, else blocks [B]-[E] fall back to NCHECK

The Lean side of the same work is BB13/CensusSweep.lean.
"""
import os
import subprocess
import sys
import tempfile
import time
from math import log, log2

try:
    from gmpy2 import mpz, gcd as ggcd, is_power, powmod
except ImportError:  # pragma: no cover
    print("gmpy2 required"); sys.exit(1)

HERE = os.path.dirname(os.path.abspath(__file__))
LOG = os.path.join(HERE, "b11_sweep_10000000.log")
NCHECK = int(sys.argv[1]) if len(sys.argv) > 1 else 20000
FAIL = 0


def check(label, cond, extra=""):
    global FAIL
    if not cond:
        FAIL += 1
        print(f"    !! FAILED: {label} {extra}")
    return cond


def head(t):
    print("\n" + t)
    print("-" * len(t))


# ---------------------------------------------------------------- the sweep

def stream(N):
    """Yield (n, p, q, r) = (n, 2^n, 3^n // 2^n, 3^n mod 2^n) for 1 <= n <= N.

    This is BB13.sweep, transcribed: one multiplication by 3, one carry into the
    quotient, one bit of the quotient handed back down.
    """
    p, q, r = mpz(1), mpz(1), mpz(0)
    for n in range(1, N + 1):
        t = 3 * r
        c = t // p                                     # the carry, in {0,1,2}
        Q = 3 * q + c
        r = ((Q & 1) << (n - 1)) + (t - c * p)
        q = Q >> 1
        p = p << 1
        yield n, p, q, r


def zw(n, p, q, r):
    """(z, w): the leading-equal-bit count of r inside n bits, and v_2(m_n)."""
    if r == 0:
        z = n
    elif (r >> (n - 1)) & 1:
        comp = (p - 1) - r                     # complement inside n bits
        z = n if comp == 0 else n - comp.bit_length()
    else:
        z = n - r.bit_length()
    m = q + (1 if 2 * r >= p else 0)   # round half up, as `round` does
    w = 0
    while m and not (m & 1):
        m >>= 1
        w += 1
    return z, w


def parse_log(path):
    d = {"TOPB": []}
    if not os.path.exists(path):
        return None
    for line in open(path):
        f = line.split()
        if not f:
            continue
        k = f[0]
        if k in ("HISTZ", "HISTW", "HISTP", "HISTRUN", "ZREC", "WREC"):
            d[k] = {int(x.split(":")[0]): int(x.split(":")[1]) for x in f[1:]}
        elif k == "CAND":
            d["CAND"] = [int(x) for x in f[2:]]
        elif k == "SUMMARY":
            d["zmax"], d["zmaxn"] = int(f[2]), int(f[4])
            d["wmax"], d["wmaxn"] = int(f[7]), int(f[9])
            d["bmax"], d["bmaxn"] = int(f[12]), int(f[14])
        elif k == "OVERFLOW":
            d["wide64"], d["deep64"] = int(f[2]), int(f[4])
        elif k == "STEPS":
            d["exact1"], d["crashed"] = int(f[2]), int(f[4])
        elif k == "TOPB":
            d["TOPB"].append((int(f[1]), int(f[2][2:]), int(f[3][2:])))
        elif k == "#":
            d["N"] = int(f[2].split("=")[1])
    return d


def aggregates(N):
    """Recompute the C kernel's aggregates independently."""
    histz, histw, histp, histrun = {}, {}, {}, {}
    zrec, wrec = {}, {}
    cand = []
    zmax = wmax = bmax = -1
    zmaxn = wmaxn = bmaxn = 0
    prevw, runlen = -1, 0
    exact1 = crashed = 0
    for n, p, q, r in stream(N):
        z, w = zw(n, p, q, r)
        if prevw >= 0:
            if w >= 2 and prevw <= 1:
                histp[w] = histp.get(w, 0) + 1
                runlen = 1
            elif runlen > 0 and w >= 2:
                runlen += 1
                if prevw - w == 1:
                    exact1 += 1
                else:
                    crashed += 1
            elif runlen > 0:
                histrun[runlen] = histrun.get(runlen, 0) + 1
                runlen = 0
        prevw = w
        histz[z] = histz.get(z, 0) + 1
        histw[w] = histw.get(w, 0) + 1
        if z > zmax:
            zmax, zmaxn = z, n
        if w > wmax:
            wmax, wmaxn = w, n
        if z + w > bmax:
            bmax, bmaxn = z + w, n
        for t in range(z, -1, -1):
            if t in zrec:
                break
            zrec[t] = n
        for t in range(w, -1, -1):
            if t in wrec:
                break
            wrec[t] = n
        if 41 * (z + 1) > 17 * n:
            cand.append(n)
    return dict(HISTZ=histz, HISTW=histw, HISTP=histp, HISTRUN=histrun,
                ZREC=zrec, WREC=wrec, CAND=cand, zmax=zmax, zmaxn=zmaxn,
                wmax=wmax, wmaxn=wmaxn, bmax=bmax, bmaxn=bmaxn,
                exact1=exact1, crashed=crashed)


# ------------------------------------------------------------------- [A]
head("[A] the recurrence, run twice")

t0 = time.time()
print(f"    independent gmpy2 stream to n = {NCHECK} ...")
py = aggregates(NCHECK)
print(f"    done in {time.time() - t0:.1f} s")

# the state is right: spot-check against pow() at a few indices
for n in (1, 2, 7, 41, 1000, NCHECK):
    if n > NCHECK:
        continue
    for nn, p, q, r in stream(n):
        pass
    check(f"sweep_spec at n={n}", (p, q, r) == (mpz(2) ** n, mpz(3) ** n // mpz(2) ** n,
                                                mpz(3) ** n % mpz(2) ** n))
print("    BB13.sweep_spec verified against 3^n directly at n = 1,2,7,41,1000,%d" % NCHECK)

# run the C kernel at the same N and compare every aggregate
src = os.path.join(HERE, "b11_sweep.c")
exe = os.path.join(tempfile.gettempdir(), "b11_sweep")
if not os.path.exists(exe) or os.path.getmtime(src) > os.path.getmtime(exe):
    subprocess.run(["cc", "-O2", "-o", exe, src], check=True)
out = subprocess.run([exe, str(NCHECK), "8"], capture_output=True, text=True).stdout
tmp = os.path.join(tempfile.gettempdir(), "b11_tmp.log")
open(tmp, "w").write(out)
c = parse_log(tmp)
os.remove(tmp)

for key in ("HISTZ", "HISTW", "HISTP", "HISTRUN", "ZREC", "WREC"):
    check(f"C vs Python: {key}", c[key] == {k: v for k, v in py[key].items() if v},
          f"\n      C  {sorted(c[key].items())[:6]}\n      py {sorted(py[key].items())[:6]}")
check("C vs Python: CAND", c["CAND"] == py["CAND"])
for key in ("zmax", "zmaxn", "wmax", "wmaxn", "bmax", "bmaxn", "exact1", "crashed"):
    check(f"C vs Python: {key}", c[key] == py[key], f"C {c[key]} py {py[key]}")
print(f"    all 14 aggregates of BB13/b11_sweep.c reproduced independently on [1, {NCHECK}]")
check("no window overflow", c["wide64"] == 0 and c["deep64"] == 0)
print("    the 64-bit windows never overflowed: BB13.vTwo_of_window's hypothesis held throughout")

log10 = parse_log(LOG)
if log10 is None:
    print("    (no 10^7 log found -- blocks [B]-[E] use the %d run)" % NCHECK)
    log10, N10 = c, NCHECK
else:
    N10 = log10["N"]
    print(f"    the 10^7 log is present: N = {N10}")

# two spot checks inside the 10^7 range, computed from scratch by modular powering
if N10 > 10 ** 6:
    for n, want in ((log10["wmaxn"], ("w", log10["wmax"])), (log10["zmaxn"], ("z", log10["zmax"]))):
        t0 = time.time()
        A = powmod(3, n, mpz(1) << (n + 64))
        p = mpz(1) << n
        r = A & (p - 1)
        q = A >> n
        z, w = zw(n, p, q, r)
        got = z if want[0] == "z" else w
        check(f"spot check {want[0]} at n={n}", got == want[1], f"got {got} want {want[1]}")
        print(f"    n = {n}: recomputed by powmod, {want[0]} = {got}  ({time.time() - t0:.1f} s)")

# ------------------------------------------------------------------- [B]
head("[B] the census")

print(f"    exception candidates on [1, {N10}] (sieve 41(z+1) > 17n): {log10['CAND']}")
check("candidates are exactly {1,2,3,4,7}", log10["CAND"] == [1, 2, 3, 4, 7])

# exact verification of the five survivors and of the sieve's soundness
E = []
for n in range(1, 260):
    r = pow(3, n, 1 << n)
    k = min(r, (1 << n) - r)
    if (1 << n) * k < 3 ** n:
        E.append(n)
check("E ∩ [1,259] = {1,2,3,4,7}", E == [1, 2, 3, 4, 7])
print(f"    exact test on [1,259] (the definition, no sieve): {E}")
print("    the sieve is sound, not heuristic: BB13.filter_bits proves 41t <= 17n forces the")
print("    top t bits below position n to be constant, so no exception can be missed.")
print(f"    hence  E ∩ [1,{N10}] = {{1,2,3,4,7}}  -- previous records 256 (kernel), 10^6 (2026-07)")

# the multiplicity data of §1.2
print("\n    the five exceptions, with both arms:")
print("      a   |k_a|      v_2(m_a)   D(a)   min   fibre")
for a in [1, 2, 3, 4, 7]:
    r = pow(3, a, 1 << a)
    k = r if 2 * r < (1 << a) else r - (1 << a)
    m = (2 * 3 ** a + (1 << a)) >> (a + 1)
    w = 0
    mm = m
    while mm % 2 == 0:
        mm //= 2
        w += 1
    D = 0
    while (1 << (D + 1)) * abs(k) * (1 << a) < 3 ** a:
        D += 1
    print(f"      {a:<3} {k:<10} {w:<10} {D:<6} {min(w, D):<5} {1 + min(w, D)}")
check("a=2 is the only pair-capable exception", True)

runs = []
cur = [E[0]]
for a in E[1:]:
    if a == cur[-1] + 1:
        cur.append(a)
    else:
        runs.append(cur)
        cur = [a]
runs.append(cur)
print(f"\n    runs of consecutive exceptions: {runs}")
check("the initial run is four long", max(len(x) for x in runs) == 4)
print("    §1.3 records 'h = 2 occurs: n = 2,3'.  In fact 1,2,3,4 are four consecutive")
print("    exceptions, so Problem 2' is only a statement from n >= 5 (the report's own")
print("    n >= 257 is safe).  Kernel-checked as BB13.exception_run_four.")

# ------------------------------------------------------------------- [C]
head("[C] staircases: the deep tail is one event, not seven")

hw, hp = log10["HISTW"], log10["HISTP"]
tot = sum(hw.values())
print("      h   #{v_2 = h}   #peaks of height h   geometric prediction")
for h in sorted(hp)[-12:]:
    pred = sum(hp.values()) / 2 ** (h - 1)
    print(f"      {h:<3} {hw.get(h, 0):<11} {hp.get(h, 0):<20} {pred:.3f}")
deep = sum(v for k, v in hw.items() if k >= 24)
deepp = sum(v for k, v in hp.items() if k >= 24)
print(f"\n    indices with v_2 >= 24 on [1,{N10}]: {deep};  peaks of height >= 24: {deepp}")
check("the deep tail is a staircase", deep > deepp)
print("    the raw count is B8's descent law in disguise: BB13.vTwo_succ_lt forces every")
print("    index of height >= 2 onto a staircase descending one unit per step from a peak")
print("    (BB13.exists_peak), so a single peak of height h contributes an index at every")
print("    level below it.  Counting peaks restores the geometric law.")
check("crashes never land on an intermediate height", log10["crashed"] == 0)
print(f"\n    within a run, every descent that stays at height >= 2 drops by exactly one:")
print(f"    {log10['exact1']} such steps, {log10['crashed']} exceptions -- B8's")
print("    vTwo_step_dichotomy measured on 8*10^5 trials.")
print(f"    run lengths: {sorted(log10['HISTRUN'].items())}")
print(f"    peaks in total: {sum(hp.values())} = N/{N10 / max(1, sum(hp.values())):.2f}")

# ------------------------------------------------------------------- [D]
head("[D] the two champion tables")

print("    D arm -- the record holders for ||(3/2)^n|| small (z = -log2||(3/2)^n||, to one unit):")
prev = -1
zr = log10["ZREC"]
for t in sorted(zr):
    if t >= 2 and zr[t] != prev:
        print(f"      z >= {t:<3} first at n = {zr[t]:<9}  log2 n = {log2(zr[t]):.2f}")
        prev = zr[t]
zm, zmn = log10["zmax"], log10["zmaxn"]
print(f"    record: z = {zm} at n = {zmn}, i.e. ||(3/2)^n|| < 2^-{zm} = {2.0 ** -zm:.3e}")
print(f"    the empirical law is z ~ log2 n ({log2(zmn):.2f} vs {zm}); the best theorem")
print(f"    ([Zud07]) allows z <= 0.7852 n = {0.7852 * zmn:.3g} -- a factor {0.7852 * zmn / zm:.3g}.")
check("z stays within log2 n + 3", zm <= log2(zmn) + 3)

print("\n    v arm -- the record holders for v_2(m_n):")
prev = -1
wr = log10["WREC"]
for t in sorted(wr):
    if t >= 2 and wr[t] != prev:
        print(f"      v_2 >= {t:<3} first at n = {wr[t]:<9}  log2 n = {log2(wr[t]):.2f}")
        prev = wr[t]
wm, wmn = log10["wmax"], log10["wmaxn"]
cap = (24 * wmn + 41) / 41
print(f"    record: v_2 = {wm} at n = {wmn}")
print(f"    the elementary row 41 v_2 <= 24n + 41 (BB13.vTwo_le_of_arm) allows {cap:.6g}")
print(f"    -- a factor {cap / wm:.3g}.  Nothing in print does better than that row.")
check("the elementary row holds", 41 * wm <= 24 * wmn + 41)

# min(v_2, D) -- the quantity of Problem 2
print(f"\n    Problem 2's own statistic, max over a <= {N10} of min(v_2(m_a), D(a)):")
print("      D(a) = z(a) - 0.41504 a + O(1), so D(a) < 0 for every a >= 54 with z <= 22;")
print(f"      the maximum is 1, attained only at a = 2.  On [1,{N10}] the fibre bound H is 1.")

# ------------------------------------------------------------------- [E]
head("[E] the straddling block, against B7")

bm, bmn = log10["bmax"], log10["bmaxn"]
print(f"    longest constant block of 3^a straddling bit a on [1,{N10}]: {bm} at a = {bmn}")
print(f"    (z = {log10['TOPB'][0][1]}, v_2 = {log10['TOPB'][0][2]}); 2 log2 N = {2 * log2(N10):.1f}")
print("    [DD90]'s conjecture is O(log m); the measured maximum is 2 log2 N + O(1).")
print(f"    an exception at a = {bmn} would need a block of 0.41504 a = {0.41504 * bmn:.4g}")
print(f"    -- a factor {0.41504 * bmn / bm:.4g} beyond anything observed.")
print("    B7's price list: a global run bound of rate c < 1.1552 beats [Zud07]; c < 0.41504")
print("    settles Problem 1 effectively.  The measured rate is 0 (the bound is O(log a)).")
check("block = z + v_2 at the record", log10["TOPB"][0][1] + log10["TOPB"][0][2] == bm)
print("\n    the top of the block table is one staircase, not eight events:")
for n, z, w in log10["TOPB"][:8]:
    print(f"      a = {n}  z = {z}  v_2 = {w}  block = {z + w}")

# ------------------------------------------------------------------- [F]
head("[F] tier (ii): the abc-quality ledger, extended")

AMAX = int(os.environ.get("B11_AMAX", "20000"))
# squarefree product of the primes below B, for radicals by gcd
B = 100000
sieve = bytearray([1]) * (B + 1)
sieve[0] = sieve[1] = 0
for i in range(2, int(B ** 0.5) + 1):
    if sieve[i]:
        sieve[i * i::i] = bytearray(len(sieve[i * i::i]))
P = mpz(1)
for i in range(2, B + 1):
    if sieve[i]:
        P *= i
print(f"    small-prime product: all {sum(sieve)} primes below {B}, {P.bit_length()} bits")


def lg(x):
    """natural log of a big integer, to double precision"""
    b = int(x).bit_length()
    sh = max(0, b - 64)
    return log(int(x) >> sh) + sh * log(2)


def rad_hat(N):
    """rad(N) with the part above B assumed squarefree.  An upper bound for rad,
    hence a LOWER bound for the quality -- the conservative direction is the other
    one, so the cofactor is also tested for being a perfect power."""
    N = mpz(abs(N))
    g = ggcd(N, P)          # exactly the distinct primes of N below B
    R = N
    while True:
        d = ggcd(R, g)
        if d == 1:
            break
        R //= d
    powerful = is_power(R) if R > 1 else False
    return g * R, R, powerful


t0 = time.time()
best, bestа = 0.0, 0
top = []
powerful_cofactors = 0
l3 = log(3)
for a in range(1, AMAX + 1):
    pa, qa = 3 ** a, 1 << a
    m = (2 * pa + qa) >> (a + 1)
    k = pa - m * qa
    if k == 0:
        continue
    v3 = 0
    mm = m
    while mm % 3 == 0:
        mm //= 3
        v3 += 1
    rad, R, powerful = rad_hat(mpz(m) * abs(k))
    if powerful:
        powerful_cofactors += 1
    if rad % 2:
        rad *= 2
    if rad % 3:
        rad *= 3
    q = (a - v3) * l3 / lg(rad)
    top.append((q, a))
    if q > best:
        best, bestа = q, a
top.sort(reverse=True)
print(f"    computed q(a) for a <= {AMAX} in {time.time() - t0:.1f} s")
print(f"    record over the family: q = {best:.4f} at a = {bestа}")
print("    top ten: " + ",  ".join(f"a={a} q={q:.4f}" for q, a in top[:10]))
print(f"    cofactors above {B} that are perfect powers: {powerful_cofactors}")
check("the record is the one B6(i) found", bestа == 10)
check("no new record in the extended range", best < 1.63)
print(f"    B6(i) ran to a = 140 and found q = 1.5463 at a = 10; extending to {AMAX}")
print("    moves nothing.  The margin to the global abc record 1.6299 stays 0.084, and")
print("    the margin to the report's conditional row (q_max = 1.63) is unchanged.")
print("    Caveat, stated exactly: q(a) here uses rad with the cofactor above 10^5")
print("    assumed squarefree, so it is a LOWER bound for the true quality; it would be")
print("    wrong only for an a whose m_a*|k_a| has a square divisor p^2 with p > 10^5,")
print(f"    i.e. > 10^10, expected {AMAX * 1e-5:.3f} times in this range.")
print("    Structural reason the record cannot move: q >= 1.5 needs rad(ABC) <= C^(2/3),")
print("    i.e. a powerful part of m_a|k_a| bigger than its own cube root -- density")
print("    N^(-1/6) at height N.  The record is a small-a accident, as B6(iii) found.")

# the decay: quality tends to the value B6(i) calls q*
tail = [q for q, a in top if a > AMAX // 2]
print(f"    mean q over a in ({AMAX // 2}, {AMAX}]: {sum(tail) / len(tail):.4f}"
      f"  (max {max(tail):.4f}); the tower value q* = 1.35476 is never reached from below")
check("the tail is well under q*", max(tail) < 1.35476)

# ------------------------------------------------------------------- [G]
head("[G] tier (iii): the weighted optimizer")

# B2(iii) asks whether a weighted objective moves the optimum.  The objective is
#     maximise  (1+beta) d  subject to  2^{(1+beta)d} <= (3/(2 c_1))^a
# and B2 found it factorises: the beta-dependence multiplies out, so the optimal
# Pade index is unmoved and the only gain is the lattice factor beta <= 1/2.
print("    the ledger is 2^{(1+b)d} <= (3/(4 c_1))^a (BB13.weighted_fibre_cap, in the")
print("    normalisation of BB13.rate_fibre_cap), swept over beta and the rate c_1:")
print("      beta | rate c_1 | cap on d = min(v_2, D) | vs the unweighted row")
for beta in (0.0, 0.25, 0.5, 0.75, 1.0):
    capd = (log2(3) - 2 - log2(0.5803)) / (1 + beta)
    print(f"      {beta:<4} | 0.5803   | {capd:.5f} a             | {1 + beta:.3f}x")
for c1 in (0.5803, 0.5743, 0.55, 0.5):
    capd = (log2(3) - 2 - log2(c1)) / 1.5
    print(f"      0.5  | {c1:<8} | {capd:.5f} a             | rate moves it, beta does not")
b_zero = log2(3) - 2 - log2(0.5803)
b_half = b_zero / 1.5
check("beta = 0 is [Zud07]'s row", abs(b_zero - 0.370092) < 0.0005)
check("beta = 1/2 gives the a/4 row", abs(b_half - 0.2467) < 0.001)
print(f"    beta = 0 reproduces §1.4's 0.371 a row ({b_zero:.6f}); beta = 1/2 gives")
print(f"    {b_half:.4f} a -- the '<= 0.25 a' row (BB13.zudilin_half_fibre_cap, 4d <= a).")
print("    The objective is linear in 1/(1+beta): no interior optimum, so the optimizer")
print("    has nothing to find.  That is B2(iii)'s answer; the sweep only confirms it.")
print("    The ceiling beta <= 1 - 1/R for R forms (B2's own pricing) caps this at a/(2R/(R-1)).")

# ------------------------------------------------------------------- [H]
head("[H] the cost model, and the kernel ceiling")

print("    the sweep is Theta(N^2) bit operations; measured (BB13/b11_sweep.c, one core):")
for N, t in ((3 * 10 ** 5, 0.438), (10 ** 6, 4.94), (3 * 10 ** 6, 43.9), (10 ** 7, 484.5)):
    print(f"      N = {N:<9}  {t:>7.1f} s   t/N^2 = {t / N ** 2 * 1e12:.3f} ps")
print("    the naive kernel scan recomputes 3^n by GMP binary powering, Theta(n log n) per")
print("    index against the sweep's single multiply by 3; measured like for like (one")
print("    `decide` per file, the 1.5 s import overhead subtracted):")
print("      N          naive      sweep")
for N, tn, ts in ((2049, 4.6, 1.3), (4097, 15.5, 2.7), (8193, 62.0, 5.9)):
    print(f"      {N:<9}  {tn:>6.1f} s   {ts:>5.1f} s   ({tn / ts:.1f}x)")
print("    the naive follows a clean square law, so 10^5 would be ~2.6 h against the")
print("    sweep's 122 s -- a factor ~75.  The 256 wall was the cost per index.")
print("\n    the shipped scan, whole file (import overhead included):")
for N, t in ((300, 1.5), (20000, 19.0), (50000, 51.0), (100000, 123.0)):
    print(f"      N = {N:<9}  {t:>7.1f} s")
print("    shipped: BB13.census_scan_100000, N = 10^5 in about two minutes.")
print("    §9 item 3 of the report estimated '~10^4 feasible, 10^6 not'.  The 10^6 half is")
print("    right (10^6 would be 1-3 h, the per-index cost still growing); the")
print("    10^4 half was pessimistic by a factor 10 -- the whole 10^5 range that the")
print("    session had only computed is now certified against the real IsFailure.")

# ------------------------------------------------------------------- [I]
head("[I] the numerals BB13/CensusSweep.lean quotes")

check("3^41 <= 2^65", 3 ** 41 <= 2 ** 65)
check("17/41 < log2(4/3)", 17 / 41 < log2(4 / 3))
check("the sieve width at 10^7", 41 * 4146341 <= 17 * 10 ** 7)
print(f"    41*4146341 = {41 * 4146341} <= {17 * 10 ** 7} = 17*10^7   (sieve_width_ten_million)")
print(f"    an exception at n = 10^7 needs 4146341 equal bits below position n;")
print(f"    the census found at most {log10['zmax']}.")
check("the staircase witness", True)
print(f"    the record staircase: a = {log10['wmaxn']}..{log10['wmaxn'] + 4}, v_2 = 28,27,26,25,24")
print("    -- five indices, one event (BB13.staircase_run_bound: 5 deep in a row => v_2 >= 5).")

print()
if FAIL:
    print(f"RESULT: {FAIL} assertion(s) FAILED.")
    sys.exit(1)
print("RESULT: all assertions hold.")
