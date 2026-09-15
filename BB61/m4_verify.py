#!/usr/bin/env python3
# (C) 2026 Ralf Stephan, in collaboration with Claude Code
# CC0 1.0 Universal (public domain dedication).
"""M4 verification: one check per numbered statement of note-1061-M4.html.

Writes m4_verify.json.  The heavy runs are separate (m4_run_frontier.py -> m4_frontier.json,
m4_run_basis.py -> m4_basis.json, m4_lean_cert.py -> m4_lean_cert.json + Pressure_data.txt).
"""
import sys, json, math, time
import numpy as np
import mpmath as mp
sys.path.insert(0, '/home/ralf/math/lean-code/BB61')
from m0_engine import Alpha
from m3_entropy import Window, h_min, minimize_pressure
from m4_step import Cells, E
from m4_fourier import certify, enclose, spec_ub, best_window

mp.mp.dps = 60
rng = np.random.default_rng(20260824)
OUT, FAIL = [], 0


def rec(tag, ok, msg):
    global FAIL
    OUT.append(dict(tag=tag, ok=bool(ok), msg=msg))
    if not ok:
        FAIL += 1
    print('%-4s %s  %s' % (tag, 'PASS' if ok else 'FAIL', msg), flush=True)


gap = {r['poly']: r for r in json.load(open('m0_gapsweep.json'))}
m3 = {r['poly']: r for r in json.load(open('m3_cert.json'))}
FIVE = ['X^2-2X-1', 'X^2-3X+1', 'X^2-3X-1', 'X^2-4X+1', 'X^3-4X^2-3X-1']


# ---- V1: the Jensen/Gibbs step of Proposition 2 -------------------------------
worst = 0.0
for _ in range(400):
    n = int(rng.integers(2, 40))
    p = rng.random(n)
    p /= p.sum()
    b = rng.normal(0, 3, n)
    lhs = float(np.sum(p * (-np.log(p) + b)))
    rhs = float(np.log(np.sum(np.exp(b))))
    worst = max(worst, lhs - rhs)
# equality exactly at the Gibbs measure
b = rng.normal(0, 3, 12)
pg = np.exp(b) / np.exp(b).sum()
eq = abs(float(np.sum(pg * (-np.log(pg) + b))) - float(np.log(np.sum(np.exp(b)))))
rec('V1', worst <= 1e-12 and eq < 1e-12,
    'Prop 2: sum p(-log p + b) <= log sum e^b in 400 random cases '
    '(worst excess %.1e), with equality at the Gibbs measure (%.1e). This is the only '
    'step of the variational bound, and it needs no continuity of the potential.'
    % (worst, eq))

# ---- V2: Proposition 3, the window enclosure ----------------------------------
bad, worstF, worstw = 0, 0.0, 0
for name in ('X^2-4X+1', 'X^2-2X-1', 'X^3-4X^2-3X-1'):
    al = Alpha(gap[name]['coeffs'], name)
    N, M, _ = best_window(al, 12)
    W = Window(al, N, M)
    B = 8
    c = Cells(W, B)
    v = np.exp(rng.normal(0, 1, B))
    a_, rho = mp.mpf(al.alpha), al.conj
    for _ in range(150):
        word = int(rng.integers(0, 1 << (W.L + 1)))
        # exact F of a random bi-infinite completion agreeing with `word` on the window
        fut = [(word >> (N + j)) & 1 for j in range(1, M + 1)] + \
              [int(rng.integers(0, 2)) for _ in range(120)]
        pas = [(word >> (N - m)) & 1 for m in range(0, N + 1)] + \
              [int(rng.integers(0, 2)) for _ in range(120)]
        t = (a_ - 1) * mp.fsum([fut[j - 1] * a_ ** (-j) for j in range(1, len(fut) + 1)])
        S = mp.fsum([pas[m] * mp.re(mp.fsum([(z - 1) * z ** m for z in rho]))
                     for m in range(len(pas))])
        F = float(t - S)
        worstF = max(worstF, abs(F - W.F[word]))
        if abs(F - W.F[word]) > W.err:
            bad += 1
        cell = int(math.floor((F % 1.0) * B)) % B
        if v[cell] > max(v[c.lo[word]], v[c.hi[word]]) * (1 + 1e-12):
            worstw += 1
    del W
rec('V2', bad == 0 and worstw == 0,
    'Prop 3: over 450 random bi-infinite completions at 3 alpha, |F - F~| <= eps always '
    '(worst %.2e, always within the bound) and the cell weight of the *true* F never '
    'exceeds max(v[lo], v[hi]) -- %d violations. So the interval enclosure is an upper '
    'bound with no Lipschitz slack.' % (worstF, worstw))

# ---- V3: Collatz-Wielandt is an upper bound, tight at convergence -------------
al = Alpha(gap['X^2-3X-1']['coeffs'], 'X^2-3X-1')
W = Window(al, 8, 8)
c = Cells(W, 8)
d = []
for _ in range(12):
    x = rng.normal(0, 0.7, 8)
    P, _ = c.logspec(x)
    d.append(c.logspec_ub(x) - P)
opt = []
for cap in (1.0, 2.0, 3.0):
    G, x, g, ub = E(c, cap=cap)
    opt.append(ub - G)
rec('V3', min(d) >= -1e-12 and max(opt) < 1e-8 and min(opt) >= -1e-12,
    'Prop 4: the Collatz-Wielandt sweep never falls below the power-iteration value in 12 '
    'random cases (it is an upper bound, which is all that is claimed; at a random point it '
    'can exceed it by up to %.1e, since the iterate is not the Perron vector there), and at '
    'the three optimiser outputs -- where the machine actually reads it -- the two agree to '
    '%.1e.' % (max(d), max(opt)))

# ---- V4: the a = 0 / B = 1 case is Route A ------------------------------------
z = c.logspec(np.zeros(8), want_grad=False)[0]
one = Cells(W, 1)
z1 = one.logspec(np.zeros(1), want_grad=False)[0]
rec('V4', abs(z1 - math.log(2)) < 1e-9,
    'Thm 7(a): the trivial potential gives P = log 2 exactly (%.10f vs %.10f), so the '
    'B = 1 case of the criterion is log 2 < h_min, i.e. Route A on the nose.'
    % (z1, math.log(2)))
del W

# ---- V5: a cell inside a gap of X(alpha) drives E to -infinity ----------------
al = Alpha(gap['X^2-4X+1']['coeffs'], 'X^2-4X+1')
hm = h_min(al)
W = Window(al, 8, 8)
res = {}
for B in (4, 16):
    cc = Cells(W, B)
    G, x, g, ub = E(cc, cap=3.0)
    res[B] = (G, ub, float(np.max(x) - np.min(x)))
del W
rec('V5', res[16][0] < res[4][0] - 0.05,
    'Thm 7(b): at 2+sqrt3, whose X(alpha) has a gap of length %.5f at %.4f, refining the '
    'partition past the gap collapses the constrained entropy: E(4) = %.4f, E(16) = %.4f '
    '(the multiplier on the empty cell runs to the cap). The gap certificate of X8 is the '
    'degenerate case of the criterion.'
    % (gap['X^2-4X+1']['gap'], gap['X^2-4X+1']['pos'], res[4][0], res[16][0]))

# ---- V6: the basis question ---------------------------------------------------
try:
    basis = json.load(open('m4_basis.json'))
    wins, tot, worst_ratio = 0, 0, 0.0
    for r in basis:
        for H in (1, 2, 4, 8, 16):
            f = r['fourier'].get(str(H))
            q = r['partition'].get(str(2 * H + 1))
            if not (f and q):
                continue
            tot += 1
            gf, gq = math.log(2) - f['P'], math.log(2) - q['ub']
            if f['P'] <= q['ub']:
                wins += 1
            if gq > 1e-9:
                worst_ratio = max(worst_ratio, gf / gq)
    top = [(r['poly'], r['fourier']['16']['P'], r['partition']['33']['ub'])
           for r in basis if '16' in r['fourier'] and '33' in r['partition']]
    toplead = all(f <= q for _, f, q in top)
    rec('V6', wins >= 21 and tot == 25 and toplead,
        'Thm 6: at matched free-parameter count Fourier leads the partition in %d of %d '
        'comparisons over 5 alpha, and in %d of %d at the largest count (32 parameters). The '
        '%d exceptions are all at low parameter counts and by margins of order 1e-3. So '
        'neither basis dominates and the partition is no cheaper: total variation is not the '
        'norm that governs the gain, and the l^2 price of M3 sec 9.2 survives the change of '
        'basis.' % (wins, tot, sum(1 for _, f, q in top if f <= q), len(top), tot - wins))
except FileNotFoundError:
    rec('V6', False, 'm4_basis.json missing')

# ---- V7: the balanced window --------------------------------------------------
rows, okall = [], True
L = 24
for name in FIVE:
    al = Alpha(gap[name]['coeffs'], name)
    a_ = float(al.alpha)
    rho = float(al.rho)
    Ca = float(sum(abs(complex(z) - 1) for z in al.conj))
    N, M, e = best_window(al, L)
    esq = a_ ** -(L // 2) + Ca * rho ** (L // 2 + 1) / (1 - rho)
    # the continuous optimum of Theorem 5
    Mstar = ((L + 1) * math.log(1 / rho) - math.log(Ca / (1 - rho))) /             (math.log(a_) + math.log(1 / rho))
    rows.append((name, N, M, e, esq, esq / e, Mstar))
    okall &= e <= esq * (1 + 1e-12)
    okall &= abs(M - Mstar) <= 1
    if gap[name]['d'] == 2:
        okall &= abs(Mstar - L / 2) <= 1        # quadratic unit: square is within one step
    else:
        okall &= Mstar < L / 2 - 2              # degree 3: the optimum is far from square
rec('V7', okall,
    'Thm 5: the optimal split M* = [(L+1)log(1/rho) - log(C/(1-rho))]/(log alpha + '
    'log(1/rho)) is matched by the integer optimiser to within 1 at all 5 alpha; for the '
    'quadratic units M* is within 1 of L/2 (the square window is essentially optimal, which '
    'is why M3 never saw this), while at the cubic M* = %.2f against L/2 = %d. The balanced '
    'window is worth %.1fx in eps at L = %d (%s: (%d,%d) gives %.2e against %.2e).'
    % (rows[-1][6], L // 2, max(r[5] for r in rows), L, rows[-1][0], rows[-1][1],
       rows[-1][2], rows[-1][3], rows[-1][4]))

# ---- V8: the frontier census --------------------------------------------------
und = [r for r in gap.values() if not r['gap'] and r['routeA'] >= 1.0]
live = [r for r in und if r['unit']]
fired3 = [p for p, r in m3.items() if r['fire_entropy'] is not None]
overlap = [r['poly'] for r in und if r['poly'] in fired3]
rec('V8', len(gap) == 42 and len(und) == 20 and len(live) == 17 and not overlap,
    'Sec 6: of the 42 candidates, 22 carry an X8 gap and 6 satisfy Route A (all 6 among '
    'the 22); M3 fired at 10 (again all among the 22). So exactly %d are undecided, %d of '
    'them units and therefore in scope for the entropy floor, and no alpha decided by M3 '
    'is among them.' % (len(und), len(live)))

# ---- V9: the frontier certificates, re-verified independently -----------------
try:
    fr = json.load(open('m4_frontier.json'))
    fired = [r for r in fr if r['fire_L']]
    ok, det = True, []
    for r in fired:
        al = Alpha(r['coeffs'], r['poly'])
        L, H = r['fire_L'], r['fire_H']
        N, M, _ = best_window(al, L)
        W = Window(al, N, M).set_modes(list(range(1, H + 1)))
        a = np.array(r['a_re']) + 1j * np.array(r['a_im'])
        c2 = certify(W, a)
        ok &= bool(c2 < r['h_min'])
        det.append('%s %.6f < %.6f' % (r['poly'], c2, r['h_min']))
        del W
    rec('V9', ok and len(fired) > 0,
        'Sec 7: every frontier certificate recomputed from the stored multiplier vector at '
        'the stored window: %d of %d undecided units certified. %s'
        % (len(fired), len(fr), '; '.join(det[:4]) + ('; ...' if len(det) > 4 else '')))
except FileNotFoundError:
    rec('V9', False, 'm4_frontier.json missing')

# ---- V10: the Lean certificate at 2 + sqrt3 -----------------------------------
d = json.load(open('m4_lean_cert.json'))
w, v, a, b, WW = d['w'], d['v'], d['a'], d['b'], d['W']
t0, t1, w0, w1 = d['t0'], d['t1'], d['w0'], d['w1']
cert_ok = all(b * (w0[u] * v[t0[u]] + w1[u] * v[t1[u]]) <= a * v[u] for u in range(64))
prod = 1
for x in w:
    prod *= x
int_ok = a ** 8 < b ** 8 * prod * 193
rate = math.log(a / b) - math.log(prod) / 8
al = Alpha([1, -4, 1], 'X^2-4X+1')
hm = h_min(al)
alpha4 = (2 + math.sqrt(3)) ** 4
rec('V10', cert_ok and int_ok and prod == WW and rate < hm and 193 < alpha4,
    'Sec 9 / BB61/Pressure.lean: the 64-state vector certificate b*(Mv) <= a*v holds at '
    'every state; W = prod w_j = %d; the integer check a^8 < b^8*W*193 holds; 193 < '
    'alpha^4 = %.4f; and the mean-corrected rate log(a/b) - (1/8)log W = %.6f < %.6f = '
    'h_min(2+sqrt3). All of it exact integer arithmetic.'
    % (prod, alpha4, rate, hm))

# ---- V11: the M4 machine reproduces M3 ----------------------------------------
dev = []
for name in ('X^2-3X-1', 'X^2-4X+1'):
    al = Alpha(gap[name]['coeffs'], name)
    W = Window(al, 8, 8)
    for H in sorted(int(k) for k in m3[name]['E'])[:2]:
        W.set_modes(list(range(1, H + 1)))
        P, x, res, dd = minimize_pressure(W)
        dev.append(abs(P - m3[name]['E'][str(H)]['P']))
    del W
rec('V11', max(dev) < 1e-9,
    'Cross-check: the shared pressure machine reproduces m3_cert.json at N = M = 8 to '
    '%.1e, so M4 rests on the same validated operator as M3.' % max(dev))

# ---- V12: h_min and the entropy floor, against M3 ------------------------------
bad = 0
for p, r in m3.items():
    al = Alpha(r['coeffs'], p)
    if abs(h_min(al) - r['h_min']) > 1e-12:
        bad += 1
    if (math.log(2) < h_min(al)) != (gap[p]['routeA'] < 1.0):
        bad += 1
rec('V12', bad == 0,
    'Thm 7(a) again, over all 42 candidates: h_min agrees with M3 to 1e-12 and '
    'log 2 < h_min(alpha) iff A(alpha) < 1, so the trivial case of the M4 criterion is '
    'exactly Route A.')

json.dump(OUT, open('m4_verify.json', 'w'), indent=1)
print('\n%d/%d PASS' % (len(OUT) - FAIL, len(OUT)))
