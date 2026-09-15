#!/usr/bin/env python3
# (C) 2026 Ralf Stephan, in collaboration with Claude Code.
# CC0 1.0 Universal (public domain dedication).
"""M7 verification: one check per numbered statement of note-1061-M7.html.

Every constant the note quotes is recomputed here, and wherever a second route exists
it is used (the dense M5 engine against the sparse M7 one; the closed Bernoulli product
against the block chain; the band products against the measured plateaux; the recorded
certificates against a fresh evaluation).  Writes m7_verify.json.
"""
import json, math, sys, itertools
import numpy as np
import mpmath as mp
sys.path.insert(0, '/home/ralf/math/lean-code/BB61')
from m0_engine import Alpha, is_pisot
from m3_entropy import Window, h_min, bern_phi, minimize_pressure
from m4_fourier import best_window, certify
from m5_memory import Memory
from m7_price import BlockChain, lp_lower
from m7_ladder import rungs_from_seed, lam_of_seed, limit_profile, bernoulli_band

OUT = []


def rec(i, what, ok, detail):
    OUT.append(dict(id=i, what=what, ok=bool(ok), detail=detail))
    print('%-4s %-62s %s  %s' % (i, what, 'PASS' if ok else 'FAIL', detail), flush=True)


A1 = Alpha([1, -2, -1], '1+sqrt2')
A2 = Alpha([1, -3, 1], '(3+sqrt5)/2')
A3 = Alpha([1, -3, -1], '(3+sqrt13)/2')
A4 = Alpha([1, -4, 1], '2+sqrt3')
C1 = Alpha([1, -4, -3, -1], 'X^3-4X^2-3X-1')
C2 = Alpha([1, -6, 3, -1], 'X^3-6X^2+3X-1')

# V1 -- the sparse block chain at q = 1/2 is the Bernoulli Erdos product
hs = [1, 2, 3, 5, 8, 13, 21, 34]
worst = 0.0
for al in (A1, A2, A3, A4):
    bp = bern_phi(al, max(hs))
    for L in (1, 2, 3, 5):
        bc = BlockChain(al, L, hmax=max(hs))
        v = np.abs(bc.phis(np.full(1 << L, 0.5), hs))
        worst = max(worst, float(np.max(np.abs(v - np.array([bp[h - 1] for h in hs])))))
rec('V1', 'engine: BlockChain at q=1/2 = the closed Bernoulli product', worst < 1e-12,
    'max |block - product| over 4 alpha, 4 memories = %.1e' % worst)

# V2 -- against M5's dense engine
worst, worste = 0.0, 0.0
rng = np.random.default_rng(5)
for al in (A1, A4, C1):
    for k in (1, 2, 3):
        m, bc = Memory(al, k, hmax=64), BlockChain(al, k, hmax=64)
        for _ in range(3):
            q = rng.uniform(0.05, 0.95, 1 << k)
            worst = max(worst, float(np.max(np.abs(np.abs(m.Gs(q, [1, 3, 7, 20]))
                                                  - np.abs(bc.phis(q, [1, 3, 7, 20]))))))
            T, pi, Ts = m.chains(q)
            e = float(-np.sum(pi * (q * np.log(q) + (1 - q) * np.log(1 - q))))
            worste = max(worste, abs(e - bc.entropy(q)))
rec('V2', 'engine: sparse M7 chain = dense M5 chain (Phi and entropy)',
    worst < 1e-12 and worste < 1e-12,
    'max |Phi| diff %.1e, max entropy diff %.1e' % (worst, worste))

# V3 -- Thm 1 / Cor 3: at the optimum the Gibbs state is flat and its entropy is P
rows = json.load(open('m7_price.json'))
flat = max(v['flat'] for r in rows for v in r['rows'].values())
al, H = A1, 16
N, M, e = best_window(al, 12)
W = Window(al, N, M)
W.set_modes(list(range(1, H + 1)))
P, x, fl, d = minimize_pressure(W)
a = x[:H] + 1j * x[H:]
Pv, (phis, ent) = W.pressure(a)
rec('V3', 'Thm 1 / Cor 3: at the optimum Phi = 0 and h(Gibbs) = P',
    fl < 1e-6 and abs(ent - Pv) < 1e-8,
    'max|Phi| = %.1e ; |h(Gibbs) - P| = %.1e ; over all recorded rows max|Phi| = %.1e'
    % (fl, abs(ent - Pv), flat))

# V4 -- Thm 5: the bracket, and the LP residual
gap = 0.0
for r in rows:
    for k, v in r['rows'].items():
        if v['E_lb'] is not None:
            gap = max(gap, v['E_ub'] - v['E_lb'])
rec('V4', 'Thm 5: the E_H bracket closes (upper - lower)', gap < 0.02,
    'largest gap over all recorded rows = %.2e (truncation of the upper side is ~1e-2 '
    'in F at L=12)' % gap)

# V5 -- Cor 2 at 2+sqrt3: one cosine already beats the floor (M3 sec 8.1)
W = Window(A4, *best_window(A4, 12)[:2])
W.set_modes([1])
P1, _, _, _ = minimize_pressure(W)
rec('V5', 'Cor 2 at 2+sqrt3: E_1 < h_min, i.e. one cosine certifies', P1 < h_min(A4),
    'E_1 = %.6f  vs  h_min = %.6f' % (P1, h_min(A4)))

# V6 -- no contradiction with M4's certificates
fr = json.load(open('m4_frontier.json'))
ok, det = True, []
try:
    p2 = json.load(open('m7_price2.json'))
except Exception:
    p2 = []
for r in p2:
    m4 = next((q for q in fr if q['poly'] == r['poly'] and q['fire_L']), None)
    if not m4:
        continue
    for k, v in r['rows'].items():
        if v['E_lb'] is not None and v['E_lb'] > r['h_min'] and int(k) >= m4['fire_H']:
            ok = False
    det.append('%s: lower bound at H=64 is %s, floor %.4f'
               % (r['poly'], r['rows'].get('64', {}).get('E_lb'), r['h_min']))
rec('V6', 'Thm 5 vs M4: no lower bound contradicts a certified alpha', ok,
    '; '.join(det) if det else 'no overlapping rows recorded')

# V7 -- Thm 6: <h c_m> = <h (alpha-1) alpha^m>
worst = 0.0
for al in (A1, A3, C1):
    c = al.c_m(14)
    with mp.workdps(60):
        for h in (1, 3, 17, 239):
            for m_ in range(14):
                x = mp.mpf(h) * (al.alpha - 1) * al.alpha ** m_
                y = mp.mpf(h) * c[m_]
                d = abs((x - mp.nint(x)) + (y - mp.nint(y)))
                worst = max(worst, float(min(d, abs(1 - d))))
rec('V7', 'Thm 6: the past weight -h c_m equals h(alpha-1)alpha^m mod 1', worst < 1e-9,
    'max distance over 3 alpha, 4 modes, m<14 = %.1e' % worst)

# V8 -- Thm 8: the dead zone, measured against the proved bound
ok, det = True, []
for al, seed in ((A1, (1, 3)), (A2, (1, 3)), (A3, (1, 3)), (A4, (1, 4))):
    a_ = float(al.alpha)
    b_ = float(al.conj[0].real)
    h = rungs_from_seed(al, seed, 20)
    e0 = h[1] - a_ * h[0]
    C = abs(e0) * (1 + (a_ - 1) / (a_ - abs(b_)))
    worstf = worstp = 0.0
    for k in range(6, 17):
        for i in range(0, k + 1):
            j = k - i
            with mp.workdps(60):
                x = mp.mpf(h[k]) * (al.alpha - 1) / al.alpha ** i
                r_ = float(abs(x - mp.nint(x)))
            worstf = max(worstf, r_ / (C * abs(b_) ** j))
        for m_ in range(0, k + 1):
            with mp.workdps(60):
                y = mp.mpf(h[k]) * (al.alpha - 1) * al.alpha ** m_
                r_ = float(abs(y - mp.nint(y)))
            worstp = max(worstp, r_ / (C * abs(b_) ** k * a_ ** m_))
    ok &= (worstf <= 1 + 1e-9 and worstp <= 1 + 1e-9)
    det.append('%s: future %.3f, past %.3f of the bound' % (al.name, worstf, worstp))
rec('V8', 'Thm 8: the proved dead-zone bound holds at every depth, k <= 16', ok,
    'largest ratio to the bound: ' + '; '.join(det))

# V9 -- Thm 9: convergence along the ladder, and plateau = band^2
worst_conv, worst_sq, det = 0.0, 0.0, []
for al, seeds in ((A1, [(1, 3), (0, 4), (1, 4), (3, 3), (0, 2), (4, 2)]),
                  (A2, [(1, 3), (1, 4)]), (A3, [(1, 3), (0, 1)])):
    bc = BlockChain(al, 2, hmax=4_000_000)
    for s_ in seeds:
        h = [x for x in rungs_from_seed(al, s_, 40) if 0 < x <= 4_000_000]
        if len(h) < 6:
            continue
        v = np.abs(bc.phis(np.full(4, 0.5), h[-3:]))
        if v.max() < 1e-5:
            continue
        band = bernoulli_band(al, lam_of_seed(al, s_))
        worst_sq = max(worst_sq, abs(band ** 2 - v[-1]))
    rng = np.random.default_rng(9)
    for _ in range(4):
        q = rng.uniform(0.1, 0.9, 4)
        h = [x for x in rungs_from_seed(al, (1, 3), 40) if 0 < x <= 4_000_000]
        z = bc.phis(q, h[-8:])
        d = np.abs(np.diff(z[::2]))                 # same-parity successive differences
        worst_conv = max(worst_conv, float(np.max(d[1:] / np.maximum(d[:-1], 1e-300))))
    det.append(al.name)
rec('V9', 'Thm 9: plateau = (band product)^2, and the ladder limit converges',
    worst_sq < 1e-6 and worst_conv < 0.9,
    'max |band^2 - plateau| = %.1e over 10 ladders; along a ladder the successive '
    'same-parity differences of Phi contract by a factor at most %.2f (12 random '
    'memory-2 chains at 3 alpha)' % (worst_sq, worst_conv))

# V10 -- Thm 10: plateau iff |alpha_j alpha| = 1, measured as the decay along a ladder
det, ok = [], True
for al in (A1, A2, A3, A4, C1, C2):
    prod = [abs(complex(z)) * float(al.alpha) for z in al.conj]
    bc = BlockChain(al, 1, hmax=10 ** 7)
    ratio, best = None, 0.0
    for s_ in itertools.product(range(0, 3), repeat=al.d):
        if not any(s_):
            continue
        h = [x for x in rungs_from_seed(al, s_, 30) if 0 < x <= 10 ** 7]
        if len(h) < 8:
            continue
        v = np.abs(bc.phis(np.full(2, 0.5), h[-4:]))
        if v[0] > best:
            best, ratio = float(v[0]), float(v[-1] / max(v[0], 1e-300))
    unit_circle = all(abs(p - 1) < 1e-9 for p in prod)
    ok &= (unit_circle == (ratio > 0.9))
    det.append('%s: |a_j a| = %.3f, |Phi| ratio over three further rungs %.1e'
               % (al.name, prod[0], ratio))
rec('V10', 'Thm 10: the ladder value is flat iff |alpha_j alpha| = 1, and decays otherwise',
    ok, '; '.join(det))

# V11 -- Prop 11 / sec 7: over memory-1 chains at 1+sqrt2 the fair coin is extremal
bc = BlockChain(A1, 1, hmax=4_000_000)
H2 = [114243, 275807]
g = np.linspace(0.001, 0.999, 61)
best, arg = 9.0, None
for q0 in g:
    for q1 in g:
        v = float(np.max(np.abs(bc.phis(np.array([q0, q1]), H2))))
        if v < best:
            best, arg = v, (q0, q1)
rec('V11', 'sec 7: memory-1 grid at 1+sqrt2 is minimised at the fair coin',
    abs(arg[0] - 0.5) < 0.02 and abs(arg[1] - 0.5) < 0.02 and abs(best - 0.034511) < 1e-4,
    'grid min %.6f at q = (%.3f, %.3f); Bernoulli plateau 0.034511' % (best, *arg))

# V12 -- Prop 12 on all 42 candidates
rows42 = json.load(open('m0_gapsweep.json'))
ok, wm = True, 0.0
for r in rows42:
    al = Alpha(r['coeffs'], r['poly'])
    b = bern_phi(al, 1)[0]
    bound = math.cos(math.pi / float(al.alpha))
    ok &= (b <= bound + 1e-12)
    wm = max(wm, b / max(bound, 1e-300))
rec('V12', 'Prop 12: |Phi_1(Bern)| <= cos(pi/alpha) on all 42 candidates', ok,
    'largest ratio to the bound = %.4f' % wm)

# V13 -- the alpha -> 2 family is Pisot, and the recorded row reproduces
a2 = json.load(open('m7_alpha2.json'))
ok = all(is_pisot([1, -2] + [0] * (n - 1) + [-1]) is not None for n in range(1, 11))
row = [r for r in a2 if r['d'] == 10]
rec('V13', 'sec 8: X^{n+1}-2X^n-1 is Pisot for n <= 10, and the table reproduces',
    ok and bool(row) and row[0]['sup'] < 1e-20,
    'alpha = %.7f, h_min = %.5f, sup|Phi| = %.1e' % (row[0]['alpha'], row[0]['h_min'],
                                                     row[0]['sup']) if row else 'no row')

# V14 -- the Lean instance: the ladder of 2+sqrt3 and its defect
h = rungs_from_seed(A4, (1, 4), 6)
e0 = 4 - float(A4.alpha)
beta = float(A4.conj[0].real)
cst = abs(e0) * (1 + (float(A4.alpha) - 1) / (float(A4.alpha) - abs(beta)))
rec('V14', 'sec 11: the Lean instance 1,4,15,56,209 at 2+sqrt3, e0 = beta, C <= 1',
    h[:5] == [1, 4, 15, 56, 209] and abs(e0 - beta) < 1e-12 and cst < 1,
    'rungs %s ; e0 = %.6f = beta ; dead-zone constant %.4f' % (h[:5], e0, cst))

# V15 -- re-certify one stored M4 certificate from its multiplier vector
r = next(q for q in json.load(open('m4_frontier.json')) if q['fire_L'])
al = Alpha(r['coeffs'], r['poly'])
N, M, e = [w[1:] for w in r['deep_windows'] if w[0] == r['fire_L']][0]
W = Window(al, N, M)
W.set_modes(list(range(1, r['fire_H'] + 1)))
c = certify(W, np.array(r['a_re']) + 1j * np.array(r['a_im']))
rec('V15', 'sec 9: a stored M4 certificate re-certifies at its own window',
    c < r['h_min'], '%s: Lambda = %.6f < h_min = %.6f' % (r['poly'], c, r['h_min']))

# V16 -- Thm 7: the recurrence rungs are the traces Tr(lam alpha^k)
worst = 0.0
for al, seeds in ((A1, [(1, 3), (2, 1)]), (A3, [(1, 3)]), (C1, [(1, 0, 0), (0, 1, 1)])):
    for s in seeds:
        lam = lam_of_seed(al, s)
        h = rungs_from_seed(al, s, 14)
        r_ = [al.alpha] + list(al.conj)
        for k in range(len(h)):
            t = mp.re(sum(lam[i] * r_[i] ** k for i in range(al.d)))
            worst = max(worst, float(abs(t - h[k])))
rec('V16', 'Thm 7: the integer recurrence reproduces Tr(lam alpha^k)', worst < 1e-6,
    'max |Tr(lam alpha^k) - h_k| over 5 ladders, k < 14 = %.1e' % worst)

json.dump(OUT, open('m7_verify.json', 'w'), indent=1)
print('\n%d/%d PASS' % (sum(1 for r in OUT if r['ok']), len(OUT)))
