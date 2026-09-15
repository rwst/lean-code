#!/usr/bin/env python3
# (C) 2026 Ralf Stephan, in collaboration with Claude Code
# CC0 1.0 Universal (public domain dedication).
"""M5: one numerical check per numbered statement of note-1061-M5.html.

Writes m5_verify.json; prints PASS/FAIL per item.  Nothing here proves anything -- the
proofs are in the note -- but every constant the note quotes is recomputed here from an
independent route wherever one exists (Monte-Carlo against closed form, orbit simulation
against Fourier coefficient, high-precision algebra against the trace identity).
"""
import json, math
import numpy as np
import mpmath as mp
from m0_engine import Alpha, orbit
import m5_bernoulli as B
from m5_markov import MarkovG, mat
from m5_memory import Memory

mp.mp.dps = 50
R = []
def rec(tag, ok, what, detail):
    R.append(dict(id=tag, ok=bool(ok), statement=what, detail=detail))
    print('%-5s %-4s %s -- %s' % (tag, 'PASS' if ok else 'FAIL', what, detail), flush=True)

AL = {n: Alpha(c, n) for n, c in
      [('X^2-2X-1', [1, -2, -1]), ('X^2-3X+1', [1, -3, 1]), ('X^2-4X+1', [1, -4, 1]),
       ('X^2-5X-2', [1, -5, -2]), ('X^3-4X^2-3X-1', [1, -4, -3, -1]),
       ('X^3-6X^2+3X-1', [1, -6, 3, -1])]}
half = mp.mpf('0.5')

# ---- V1  Theorem 1: orbit empirical average -> G_p(h), phase included
d = json.load(open('m5_direct.json'))
mx = max(r['err_scaled'] for r in d)
rec('V1', mx < 8.0, 'Thm 1+2: (1/N)sum e(h xi a^n) -> G_p(h) (m5_direct.json)',
    '%d comparisons, max |emp-G|*sqrt(N) = %.2f' % (len(d), mx))

# ---- V2  Theorem 2: the product formula against a direct Monte-Carlo of int e(hF) dmu_p
rng = np.random.default_rng(7)
worst = 0.0
for name in ['X^2-2X-1', 'X^3-4X^2-3X-1']:
    al = AL[name]; a = float(al.alpha)
    for p in [0.5, 0.35]:
        for h in [1, 3]:
            J, M = 60, 90
            xs = np.array([float(x) for x in B.future_args(al, 1, J)])
            cs = np.array([float(x) for x in B.past_args(al, 1, M)])
            S = 400000
            wf = (rng.random((S, J)) < p)
            wp = (rng.random((S, M)) < p)
            F = wf @ xs + wp @ cs                      # t - S  (past args carry the sign)
            emp = complex(np.mean(np.exp(2j * np.pi * h * F)))
            G = complex(B.weyl(al, h, mp.mpf(p))['value'])
            worst = max(worst, abs(emp - G) * math.sqrt(S))
rec('V2', worst < 8.0, 'Thm 2: product formula = Monte-Carlo of int e(hF) dmu_p',
    'max |MC - G|*sqrt(S) = %.2f over 8 cases, S=4e5' % worst)

# ---- V3  Theorem 3: the trace identity h c_m = -h(a-1)a^m mod 1, and the two mechanisms
err = mp.mpf(0)
for name, al in AL.items():
    for m in range(0, 12):
        v = al.c_m_mp(m + 1)[m] + (al.alpha - 1) * al.alpha**m
        err = max(err, abs(v - mp.nint(v)))
rec('V3a', err < mp.mpf('1e-30'), 'Thm 3(i): c_m + (a-1)a^m in Z (M1 Lemma 2)',
    'max distance to Z over 6 alpha, m<12: %.2e' % float(err))

rows = json.load(open('m0_gapsweep.json'))
ok, worst3 = True, None
for r in rows:
    a = mp.mpf(r['alpha'])
    x1 = (a - 1) / a
    x2 = (a - 1) / a**2
    if not (x1 > mp.mpf('0.5') and x1 < 1 and x2 > 0 and x2 < mp.mpf('0.5')):
        ok = False; worst3 = r['poly']
rec('V3b', ok, 'Thm 3(iii): (a-1)/a in (1/2,1) and (a-1)/a^2 in (0,1/2) for all 42 alpha',
    'all 42 pass' if ok else 'fails at ' + str(worst3))

x1_at_2 = mp.mpf(1) / 2
rec('V3c', abs(B.absphi(x1_at_2, half)) < mp.mpf('1e-40'),
    'Thm 3 remark: at alpha=2 the first future factor is exactly 0',
    '|phi_{1/2}(1/2)| = %.1e' % float(B.absphi(x1_at_2, half)))

mn = min(json.load(open('m5_bias.json')), key=lambda r: r['minfac'])
rec('V3d', mn['minfac'] > 0, 'Thm 3: no factor vanishes, but the bound is not uniform in h',
    'smallest single factor over 42 alpha, h<=64: %.6f at %s h=%d'
    % (mn['minfac'], mn['poly'], mn['minfac_h']))

# ---- V4  Corollary 4: the discrepancy floor  liminf D_N* >= |G|/(4 sqrt2 h)
al = AL['X^2-4X+1']
rng = np.random.default_rng(11)
N = 200000
eps = (rng.random(N + 200) < 0.5).astype(np.int64)
x = np.sort(orbit(al, eps, L=200))
i = np.arange(1, len(x) + 1)
D = float(max(np.max(i / len(x) - x), np.max(x - (i - 1) / len(x))))
flo = float(B.discrepancy_floor(al, 1, half))
rec('V4', D >= flo, 'Cor 4: D_N^* >= |G_p(1)|/(4 sqrt2)', 'D_N^* = %.5f, floor %.5f' % (D, flo))

# ---- V5  Corollary 5: independence of the word (a.e. statement)
sp = [r for r in d if r['poly'] == 'X^2-4X+1' and r['p'] == 0.5 and r['h'] == 1]
sprd = max(abs(complex(r['emp_re'], r['emp_im']) - complex(sp[0]['emp_re'], sp[0]['emp_im']))
           for r in sp) if sp else 0.0
rec('V5', sprd < 0.01, 'Cor 5: different Bernoulli words give the same limit',
    'spread over %d seeds: %.2e' % (len(sp), sprd))

# ---- V6  Theorem 7: folding at norm-one quadratic units
worst6, worst6n = mp.mpf(0), mp.mpf(0)
for r in rows:
    if r['d'] != 2: continue
    al = Alpha(r['coeffs'], r['poly'])
    cm = al.c_m_mp(14)
    if r['coeffs'][-1] == 1:
        for m in range(14):
            worst6 = max(worst6, abs(cm[m] + (al.alpha - 1) / al.alpha**(m + 1)))
    elif r['coeffs'][-1] == -1:
        for m in range(14):
            worst6n = max(worst6n, abs(cm[m] - (-1)**(m + 1) * (al.alpha + 1) / al.alpha**(m + 1)))
rec('V6a', worst6 < mp.mpf('1e-30'), 'Thm 7: N(a)=+1 quadratic unit => c_m = -(a-1)a^{-m-1}',
    'max error %.2e' % float(worst6))
rec('V6b', worst6n < mp.mpf('1e-30'), 'Thm 7 remark: N(a)=-1 => c_m = (-1)^{m+1}(a+1)a^{-m-1}',
    'max error %.2e' % float(worst6n))
al = AL['X^2-4X+1']
worst6c = 0.0
for h in range(1, 65):
    J, M = B.depths(al, h, half)
    fut = mp.mpf(1)
    for xx in B.future_args(al, h, J): fut *= B.absphi(xx, half)
    pas = mp.mpf(1)
    for xx in B.past_args(al, h, M): pas *= B.absphi(xx, half)
    worst6c = max(worst6c, float(abs(fut - pas)))
rec('V6c', worst6c < 1e-25, 'Thm 7: |G| is a perfect square at 2+sqrt3, every h<=64',
    'max |future - past| = %.2e' % worst6c)

# ---- V7  Theorem 8: the tail-event perturbation bound
worst7, ok7 = mp.mpf(0), True
with mp.workdps(200):                                    # (a-1)a^39 ~ 1e15: 50 dps leaves
    al7 = Alpha(AL['X^2-3X+1'].coeffs)                   # only 34 digits of the fraction
    a, rho = al7.alpha, al7.rho
    Ca = sum(abs(z - 1) for z in al7.conj)
    for m in range(0, 40):
        v = (a - 1) * a**m
        nrm = abs(v - mp.nint(v))
        ok7 &= nrm <= Ca * rho**m * (1 + mp.mpf('1e-20'))
        worst7 = max(worst7, nrm / (Ca * rho**m))
rec('V7', ok7, 'Thm 8: ||(a-1)a^m|| <= C_alpha rho^m (mpmath, 200 dps)',
    'max ratio to the bound over m<40: %.6f' % float(worst7))

# ---- V8  Proposition 11: the M3 subsumption window
bias = json.load(open('m5_bias.json'))
q = [r for r in bias if r['d'] == 2 and r['unit']]
bad = [r['poly'] for r in q if (r['p_window'] is None) != (r['alpha'] > 4.0)]
rec('V8', not bad, 'Prop 11: for quadratic units the window is empty iff alpha > 4',
    '%d quadratic units, %d subsumed, no mismatches' % (len(q), sum(1 for r in q if r['p_window'] is None))
    if not bad else 'mismatch at ' + ', '.join(bad))

# ---- V9  bi-Holder constants of M1 Lemma 1(iv) (used by Prop 12)
al = AL['X^2-4X+1']; a = float(al.alpha); g = (a - 2) / a
rng = np.random.default_rng(3)
ok9, lo9 = True, 9.0
for _ in range(2000):
    k = int(rng.integers(0, 20))
    w = rng.integers(0, 2, 40)
    w2 = w.copy(); w2[k] = 1 - w2[k]
    pi1 = (a - 1) * sum(int(w[i]) * a**(-(i + 1)) for i in range(40))
    pi2 = (a - 1) * sum(int(w2[i]) * a**(-(i + 1)) for i in range(40))
    dd = abs(pi1 - pi2) * a**k
    ok9 &= (g - 1e-12 <= dd <= 1 + 1e-12); lo9 = min(lo9, dd)
rec('V9', ok9, 'M1 Lemma 1(iv): g a^{-k} <= |pi(e)-pi(e\')| <= a^{-k}',
    'min |pi-pi\'| a^k = %.6f, gap g = %.6f' % (lo9, g))

# ---- V10 Theorem 13: the Markov formula, two independent implementations + Bernoulli
al = AL['X^2-4X+1']
mg, m1, m2 = MarkovG(al), Memory(al, 1), Memory(al, 2)
w10 = 0.0
for (u, v) in [(0.5, 0.5), (0.3, 0.7), (0.8, 0.2), (0.25, 0.9)]:
    q1 = np.array([u, 1 - v]); q2 = np.array([q1[b & 1] for b in range(4)])
    for h in [1, 3, 7]:
        g0 = mg.G(mat(u, v), h)
        w10 = max(w10, abs(m1.G(q1, h) - g0), abs(m2.G(q2, h) - g0))
        if abs(u + v - 1) < 1e-12:
            w10 = max(w10, abs(complex(B.weyl(al, h, mp.mpf(u))['value']) - g0))
rec('V10', w10 < 1e-12, 'Thm 13: memory-1 = memory-2 restricted = Bernoulli on its slice',
    'max discrepancy %.2e' % w10)

# ---- V11 the memory ladder: monotone in k, and which optima M3 already excludes
try:
    mk = json.load(open('m5_memory.json'))
except FileNotFoundError:
    mk = []
ok11, det, excl = True, [], []
for r in mk:
    al = AL.get(r['poly'])
    ks = sorted(int(x) for x in r['ladder'])
    vals = [r['ladder'][str(k)]['Psi'] for k in ks]
    mono = all(vals[i + 1] <= vals[i] * (1 + 1e-9) for i in range(len(vals) - 1))
    ok11 &= mono
    if not mono: det.append('%s NOT monotone: %s' % (r['poly'], vals))
    if al is not None and abs(al.coeffs[-1]) == 1:
        hm = float(B.h_min(al))
        for k in ks:
            e = r['ladder'][str(k)].get('entropy')
            if e is not None and e < hm: excl.append('%s k=%d' % (r['poly'], k))
rec('V11', ok11 and bool(mk), 'Sec 8: the memory ladder is monotone in k (it must be, by embedding)',
    ('%d alpha, %d rungs, all monotone; below M3 floor: %s'
     % (len(mk), sum(len(r['ladder']) for r in mk), ', '.join(excl) if excl else 'none'))
    if ok11 else '; '.join(det))

# ---- V12 X10 retirement: the second moment equals |G|^2 for an ergodic measure
sp = [r for r in d if r['poly'] == 'X^2-2X-1' and r['p'] == 0.5 and r['h'] == 3]
if sp:
    m2nd = np.mean([r['emp_re']**2 + r['emp_im']**2 for r in sp])
    tgt = sp[0]['absG']**2
    tol = 4 * sp[0]['absG'] / math.sqrt(sp[0]['N'] * len(sp))   # CLT size of the estimator
    rec('V12', abs(m2nd - tgt) < tol,
        'Sec 7: the second moment of the Weyl sum equals |G|^2 (X10 adds nothing)',
        'mean |emp|^2 = %.6f vs |G|^2 = %.6f (CLT tolerance %.6f)' % (m2nd, tgt, tol))

# ---- V13 the rigorous enclosure is consistent under deepening
al = AL['X^3-6X^2+3X-1']
w = B.weyl(al, 5, half)
w2 = B.weyl(al, 5, half, J=w['J'] + 20, M=w['M'] + 20)
rec('V13', w['lo'] <= w2['abs'] <= w['hi'] + 1e-30,
    'Sec 6: the truncation enclosure [lo,hi] contains the deeper value',
    'lo=%.12f val=%.12f deeper=%.12f' % (float(w['lo']), float(w['abs']), float(w2['abs'])))

# ---- V14 M0 sec 3 / plan X5 numbers reproduced
al = AL['X^2-2X-1']
g3 = float(B.modulus(al, 3, half))
lad = [1, 3, 7, 17, 41, 99, 239, 577, 1393, 3363, 8119, 19601]
pl = float(B.modulus(al, lad[-1], half))
rec('V14', abs(g3 - 0.045962) < 1e-6 and abs(pl - 0.0345113) < 1e-6,
    'X5 / M0 sec 3 reproduced at 1+sqrt2', '|G(3)| = %.6f (X5: 0.045962); ladder plateau '
    '|G(19601)| = %.7f (M0: 0.0345113)' % (g3, pl))

# ---- V15/V16 the two audits of the memory ladder
try:
    wd = json.load(open('m5_wide.json'))
except FileNotFoundError:
    wd = []
if wd:
    ok15, det15 = True, []
    for r in wd:
        for k, d in sorted(r['ladder'].items()):
            if d['Psi_wide_ent'] > d['Psi_wide'] * (1 + 1e-6):        # constraint binds
                ok15 &= d['entropy_wide_ent'] >= r['h_min'] - 1e-3
                det15.append('%s k=%s h=%.4f vs %.4f' % (r['poly'], k,
                                                         d['entropy_wide_ent'], r['h_min']))
    rec('V15', ok15, 'Sec 8(B): where the entropy penalty binds, the optimum sits on the floor',
        ('%d binding cells, all with h(mu) >= h_min: %s' % (len(det15), '; '.join(det15)))
        if det15 else 'no cell binds')

    ok16, grew = True, []
    for r in wd:
        for k, d in sorted(r['ladder'].items()):
            ok16 &= d['wide_at_old_opt'] >= d['Psi12'] - 1e-9
            if d['wide_at_old_opt'] > d['Psi12'] * 1.05:
                grew.append('%s k=%s: %.4f -> %.4f at h=%d'
                            % (r['poly'], k, d['Psi12'], d['wide_at_old_opt'], d['argmax']))
    rec('V16', ok16, 'Sec 8(A): the h<=12 optimum is worse on h<=32, and often by a lot',
        '%d of %d cells grow by >5%%; e.g. %s'
        % (len(grew), sum(len(r['ladder']) for r in wd), '; '.join(grew[:3])))

json.dump(R, open('m5_verify.json', 'w'), indent=1)
print('\n%d/%d PASS' % (sum(1 for r in R if r['ok']), len(R)))
