#!/usr/bin/env python3
# (C) 2026 Ralf Stephan, in collaboration with Claude Code
# CC0 1.0 Universal (public domain dedication).
"""M3 Thms 7-8 -- one check per GROUP OF DECLARATIONS of BB61/KernelCriterion.lean.

Theorem 7 is the B-criterion in its correct form; Theorem 8 says the criterion depends only on
its INTEGER reach, so Route B collapses onto Route D.  The Lean file states both over
Gamma subset Z (licensed by M3 Cor. 6) and replaces the note's two imported theorems -- Bochner
for Q >= 0, Fejer-Riesz for the realisation -- by the Gram form and by one explicit sum of
squares.  These checks exercise exactly those replacements.

T1  matKernel_gram                 Q_B = sum_k |P_k|^2 for a Gram matrix, and B is PSD:
    gram_posSemidef                the Bochner-free reading of "Q >= 0"
T2  integral_matKernel             int_T Q_B = tr B, by quadrature against the exact trace
T3  integral_matKernel_comp        int Q.F dmu = Re sum B_ij Phi_{gi-gj}(mu) on periodic-orbit
    integral_matKernel_comp_eq_    invariant measures, and = tr B as soon as mu kills the
    trace                          off-diagonal reach
T4  kernelCertificate              G = c(0) - Q is a mean-zero certificate with the same gap
T5  exists_kernel_of_trig          Theorem 8(c): the explicit kernel of 1 - a_h e(h.) gives
    Certificate                    Q = c(0) - 2G EXACTLY, with a PSD Gram matrix
T6  (the Fejer-Riesz replacement)  the note's A - G and this file's Q are DIFFERENT nonneg
                                   trig polynomials -- the construction is not a re-derivation
T7  confCircle_ne_univ_of_kernel   sup_T Q >= int_T Q = c(0), so no kernel is pointwise below
                                   its trace on all of T
T8  no_killer_of_kernel            ANCHOR: M3 sec. 7 re-derived -- at 1+sqrt2 a convex
                                   combination of periodic orbits kills the first modes, and
                                   then every kernel of that reach has int Q.F dmu = c(0)

Requires mpmath, numpy, scipy.
"""
import json
import random

import mpmath as mp
import numpy as np
from scipy.optimize import linprog

mp.mp.dps = 50

RES = {}
FAILS = 0


def report(key, ok, msg):
    global FAILS
    RES[key] = dict(ok=bool(ok), msg=msg)
    if not ok:
        FAILS += 1
    print('%-4s %s  %s' % (key, 'PASS' if ok else 'FAIL', msg))


def roots(a, b):
    d = mp.sqrt(mp.mpf(a) ** 2 + 4 * mp.mpf(b))
    return (mp.mpf(a) + d) / 2, (mp.mpf(a) - d) / 2


JT = 260


def word_periodic(p, seed):
    rnd = random.Random(seed)
    w = [rnd.randint(0, 1) for _ in range(p)]
    return lambda k: w[k % p]


def fRaw(al, be, om, i=0):
    """F(sigma^i om) = t((sigma^i om)+) - S((sigma^i om)-)."""
    s = mp.mpf(0)
    for k in range(1, JT + 1):
        if om(i + k):
            s += al ** (-k)
    t = (al - 1) * s
    u = mp.mpf(0)
    for j in range(0, JT + 1):
        if om(i - j):
            u += (be - 1) * be ** j
    return t - u


def ee(x):
    return mp.e ** (2j * mp.pi * x)


def gram_matrix(w, n):
    """B_ij = sum_k w[k][i] conj(w[k][j]), the Lean `gram`."""
    return [[sum(w[k][i] * mp.conj(w[k][j]) for k in range(len(w))) for j in range(n)]
            for i in range(n)]


def matKernel(gam, B, x):
    """Q_B(x) = Re sum_ij B_ij e((g_i - g_j) x), the Lean `matKernel`."""
    n = len(gam)
    return mp.re(sum(B[i][j] * ee((gam[i] - gam[j]) * x) for i in range(n) for j in range(n)))


def matTrace(B):
    return mp.re(sum(B[i][i] for i in range(len(B))))


def rand_kernel(rnd, n, nk, span=6):
    """A random integer frequency set of size n and a random Gram family of nk vectors."""
    gam = sorted(rnd.sample(range(-span, span + 1), n))
    w = [[mp.mpc(rnd.uniform(-1, 1), rnd.uniform(-1, 1)) for _ in range(n)] for _ in range(nk)]
    return gam, w


# ---------------------------------------------------------------- T1
rnd = random.Random(11)
worst1 = mp.mpf(0)
neg1 = 0
psd1 = []
for trial in range(24):
    gam, w = rand_kernel(rnd, rnd.randint(2, 5), rnd.randint(1, 4))
    B = gram_matrix(w, len(gam))
    Bnp = np.array([[complex(B[i][j]) for j in range(len(gam))] for i in range(len(gam))])
    psd1.append(float(np.min(np.linalg.eigvalsh(Bnp))))
    for _ in range(8):
        x = mp.mpf(rnd.uniform(-3, 3))
        lhs = matKernel(gam, B, x)
        rhs = sum(mp.fabs(sum(w[k][i] * ee(gam[i] * x) for i in range(len(gam)))) ** 2
                  for k in range(len(w)))
        worst1 = max(worst1, abs(lhs - rhs))
        if lhs < -mp.mpf('1e-30'):
            neg1 += 1
report('T1', worst1 < mp.mpf('1e-35') and neg1 == 0 and min(psd1) > -1e-12,
       'on 24 random Gram kernels x 8 points: Q_B = sum_k |P_k|^2 to %.2e, Q_B >= 0 with %d '
       'violations, and the Gram matrix is PSD (smallest eigenvalue over all trials %.2e) -- '
       'positivity by inspection, no Bochner theorem' % (float(worst1), neg1, min(psd1)))

# ---------------------------------------------------------------- T2
worst2 = mp.mpf(0)
rnd = random.Random(23)
for trial in range(12):
    gam, w = rand_kernel(rnd, rnd.randint(2, 5), rnd.randint(1, 3))
    B = gram_matrix(w, len(gam))
    N = 4096
    avg = sum(matKernel(gam, B, mp.mpf(t) / N) for t in range(N)) / N
    worst2 = max(worst2, abs(avg - matTrace(B)))
report('T2', worst2 < mp.mpf('1e-25'),
       'int_T Q_B dLeb = tr B on 12 random kernels, worst deviation %.2e over a 4096-point '
       'grid -- every off-diagonal character averages to zero, and Gamma subset Z makes '
       'g - g\' = 0 mean g = g\'' % float(worst2))

# ---------------------------------------------------------------- T3
SETUPS = [('X^2-2X-1', 2, 1), ('X^2-4X+1', 4, -1)]
rnd = random.Random(37)
worst3 = mp.mpf(0)
worst3b = mp.mpf(0)
n3 = 0
for name, a, b in SETUPS:
    al, be = roots(a, b)
    for seed in range(6):
        p = rnd.choice([3, 5, 7])
        om = word_periodic(p, 700 + seed + 17 * a)
        Fv = [fRaw(al, be, om, i) for i in range(p)]
        phi = {}
        for d in range(-12, 13):
            phi[d] = sum(ee(d * v) for v in Fv) / p
        gam, w = rand_kernel(rnd, rnd.randint(2, 4), rnd.randint(1, 3), span=6)
        B = gram_matrix(w, len(gam))
        lhs = sum(matKernel(gam, B, v) for v in Fv) / p
        rhs = mp.re(sum(B[i][j] * phi[gam[i] - gam[j]]
                        for i in range(len(gam)) for j in range(len(gam))))
        worst3 = max(worst3, abs(lhs - rhs))
        # and the "killer" specialisation: zero out every off-diagonal coefficient
        rhs0 = mp.re(sum(B[i][j] * (1 if i == j else 0)
                         for i in range(len(gam)) for j in range(len(gam))))
        worst3b = max(worst3b, abs(rhs0 - matTrace(B)))
        n3 += 1
report('T3', worst3 < mp.mpf('1e-30') and worst3b < mp.mpf('1e-40'),
       'on %d (alpha, periodic-orbit invariant measure, random kernel) instances: '
       'int Q.F dmu = Re sum B_ij Phi_{gi-gj}(mu) to %.2e, and a measure killing the '
       'off-diagonal reach gives exactly tr B (%.2e) -- the single computation Theorems 7 and '
       '8(a) both run on' % (n3, float(worst3), float(worst3b)))

# ---------------------------------------------------------------- T4
rnd = random.Random(53)
worst4 = mp.mpf(0)
for trial in range(10):
    gam, w = rand_kernel(rnd, rnd.randint(2, 4), rnd.randint(1, 3))
    B = gram_matrix(w, len(gam))
    c0 = matTrace(B)
    N = 2048
    meanG = sum(c0 - matKernel(gam, B, mp.mpf(t) / N) for t in range(N)) / N
    worst4 = max(worst4, abs(meanG))
report('T4', worst4 < mp.mpf('1e-25'),
       'G = c(0) - Q_B has zero mean on 10 random kernels, worst %.2e: a kernel with a '
       'uniform gap IS a Route D certificate, and Route B sits inside Route D by a change of '
       'sign' % float(worst4))

# ---------------------------------------------------------------- T5
rnd = random.Random(71)
worst5 = mp.mpf(0)
worst5t = mp.mpf(0)
psd5 = []
for trial in range(20):
    m = rnd.randint(1, 4)
    H = sorted(rnd.sample([h for h in range(-7, 8) if h != 0], m))
    aco = {h: mp.mpc(rnd.uniform(-1.5, 1.5), rnd.uniform(-1.5, 1.5)) for h in H}
    gam = [0] + H
    w = []
    for k in H:
        w.append([mp.mpc(1, 0)] + [(-aco[k] if x == k else mp.mpc(0)) for x in H])
    B = gram_matrix(w, len(gam))
    Bnp = np.array([[complex(B[i][j]) for j in range(len(gam))] for i in range(len(gam))])
    psd5.append(float(np.min(np.linalg.eigvalsh(Bnp))))
    c0 = matTrace(B)
    worst5t = max(worst5t, abs(c0 - sum(1 + mp.fabs(aco[h]) ** 2 for h in H)))
    for _ in range(8):
        x = mp.mpf(rnd.uniform(-3, 3))
        G = mp.re(sum(aco[h] * ee(h * x) for h in H))
        worst5 = max(worst5, abs(matKernel(gam, B, x) - (c0 - 2 * G)))
report('T5', worst5 < mp.mpf('1e-35') and worst5t < mp.mpf('1e-35') and min(psd5) > -1e-12,
       'Theorem 8(c) on 20 random (H, a): the kernel of the one-term polynomials '
       '1 - a_h e(h.) on Gamma = {0} u H satisfies Q = c(0) - 2G EXACTLY (%.2e), '
       'c(0) = sum_h (1 + |a_h|^2) (%.2e), and its Gram matrix is PSD (%.2e).  No '
       'Fejer-Riesz factorisation is used' % (float(worst5), float(worst5t), min(psd5)))

# ---------------------------------------------------------------- T6
rnd = random.Random(89)
diffs6 = []
neg6 = 0
for trial in range(12):
    m = rnd.randint(2, 4)
    H = sorted(rnd.sample([h for h in range(-6, 7) if h != 0], m))
    aco = {h: mp.mpc(rnd.uniform(-1.5, 1.5), rnd.uniform(-1.5, 1.5)) for h in H}
    gam = [0] + H
    w = [[mp.mpc(1, 0)] + [(-aco[k] if x == k else mp.mpc(0)) for x in H] for k in H]
    B = gram_matrix(w, len(gam))
    A = sum(mp.fabs(aco[h]) for h in H)          # the note's A > max G
    d = mp.mpf(0)
    for _ in range(40):
        x = mp.mpf(rnd.uniform(-3, 3))
        G = mp.re(sum(aco[h] * ee(h * x) for h in H))
        d = max(d, abs(matKernel(gam, B, x) - (A - G)))
        if matKernel(gam, B, x) < -mp.mpf('1e-30'):
            neg6 += 1
    diffs6.append(float(d))
report('T6', min(diffs6) > 1e-3 and neg6 == 0,
       'the note factors A - G by Fejer-Riesz; this file builds a DIFFERENT nonneg trig '
       'polynomial.  On 12 instances the two differ by at least %.3f (smallest of the 12 sup '
       'distances) and Q stays nonnegative at all 480 sample points (%d violations) -- the '
       'construction is a replacement, not a re-derivation' % (min(diffs6), neg6))

# ---------------------------------------------------------------- T7
rnd = random.Random(101)
gaps7 = []
for trial in range(15):
    gam, w = rand_kernel(rnd, rnd.randint(2, 5), rnd.randint(1, 3))
    B = gram_matrix(w, len(gam))
    N = 2048
    mx = max(matKernel(gam, B, mp.mpf(t) / N) for t in range(N))
    gaps7.append(float(mx - matTrace(B)))
report('T7', min(gaps7) >= -1e-20,
       'sup_T Q_B >= int_T Q_B = c(0) on 15 random kernels (worst margin %.2e): a kernel can '
       'never be pointwise below its own trace on all of T, so the strong form of (ii) forces '
       'X(alpha) != T -- at 1+sqrt2 and (3+sqrt5)/2, where FullSupport.lean proves '
       'X(alpha) = T, it is empty' % min(gaps7))

# ---------------------------------------------------------------- T8
# ANCHOR: M3 sec. 7 -- a convex combination of periodic orbits at 1+sqrt2 killing the first
# modes, hence no kernel of that reach certifies (Theorem 8(a)).
a, b = 2, 1
al, be = roots(a, b)
HMAX = 4
pool = []
for p in (2, 3, 4, 5, 6, 7):
    for seed in range(60):
        om = word_periodic(p, 90000 + 137 * p + seed)
        Fv = [fRaw(al, be, om, i) for i in range(p)]
        vec = []
        for h in range(1, HMAX + 1):
            z = sum(ee(h * v) for v in Fv) / p
            vec += [float(mp.re(z)), float(mp.im(z))]
        pool.append((vec, Fv))
Aeq = np.array([v for v, _ in pool]).T
Aeq = np.vstack([Aeq, np.ones(len(pool))])
beq = np.zeros(Aeq.shape[0])
beq[-1] = 1.0
res = linprog(np.zeros(len(pool)), A_eq=Aeq, b_eq=beq, bounds=[(0, None)] * len(pool),
              method='highs')
ok8 = bool(res.success)
worst8 = float('nan')
resid8 = float('nan')
if ok8:
    wts = res.x
    resid8 = float(np.max(np.abs(Aeq[:-1] @ wts)))
    # the invariant measure mu = sum wts_i (orbit measure); check int Q.F dmu = tr B for
    # every kernel whose reach lies inside [-HMAX, HMAX]
    rnd = random.Random(113)
    worst8 = 0.0
    for trial in range(8):
        n = rnd.randint(2, 3)
        gam = sorted(rnd.sample(range(0, HMAX + 1), n))
        w = [[mp.mpc(rnd.uniform(-1, 1), rnd.uniform(-1, 1)) for _ in range(n)]
             for _ in range(rnd.randint(1, 2))]
        B = gram_matrix(w, n)
        tot = mp.mpf(0)
        for wt, (_, Fv) in zip(wts, pool):
            if wt <= 1e-14:
                continue
            tot += mp.mpf(float(wt)) * (sum(matKernel(gam, B, v) for v in Fv) / len(Fv))
        worst8 = max(worst8, float(abs(tot - matTrace(B))))
hull = {r['name']: r for r in json.load(open('m3_hull.json'))}
sil = hull.get('1+sqrt2', {}).get('H', {})
inside_ok = all(v.get('inside') for v in sil.values())
report('T8', ok8 and resid8 < 1e-9 and worst8 < 1e-8 and inside_ok,
       'ANCHOR, M3 sec. 7 re-derived: an explicit convex combination of %d periodic orbits at '
       '1+sqrt2 kills the first %d Fourier modes (residual %.2e), and then EVERY kernel with '
       'reach in [-%d,%d] has int Q.F dmu = tr B to %.2e -- no gap, so no such kernel '
       'certifies.  m3_hull.json reports `inside` at all %d tested degrees, up to H = %s'
       % (int(np.sum(res.x > 1e-14)) if ok8 else 0, HMAX, resid8, HMAX, HMAX, worst8,
          len(sil), max(sil, key=lambda k: int(k)) if sil else 'n/a'))

print()
print('%d/%d checks OK at mp.dps = %d' % (len(RES) - FAILS, len(RES), mp.mp.dps))
json.dump(RES, open('m3_thm78_lean.json', 'w'), indent=1)
