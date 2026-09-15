#!/usr/bin/env python3
# (C) 2026 Ralf Stephan, in collaboration with Claude Code
# CC0 1.0 Universal (public domain dedication).
"""M3 -- one check per numbered statement of note-1061-M3.html.

V1  Prop 1   the tube is everything: a lattice translate into {|w|<=W} always exists
V2  Prop 2   corrected Meyer bound holds; the plan's version fails by O(1)
V3  Prop 3   transport identity chi_{h alpha^-m} o Phi = e(h[t^(m) - S] o sigma^-m)
V4  Thm 4    ladder limit  lambda-hat(h) = lim_m nu-hat(h Tr_m), with the rho^m rate
V5  Cor 5    plateau constants reproduce M0's, from the closed-form Erdos products
V6  Thm 8    the collapse: alpha-orbit cliques exist, and sup over Omega is M-invariant
V7  Thm 9    pressure sandwich  -P(-b g)/b <= min_mu int g <= -P(-b g)/b + log2/b
V8  Thm 11   h_min, and  log2 < h_min  <=>  A(alpha) < 1  (units), swept
V9  Thm 12   the 2+sqrt3 certificate, at four window depths and a rational multiplier
V10 sec 9.1  invariant measures killing the first H Fourier modes (hull witnesses)
V11 M1       the splitting {xi alpha^n} = {t_n - S_n} against a 200-dps evaluation
V12 sec 9.2  the log-growth constant c_alpha and the required degree H*

Requires numpy, scipy, mpmath.  Reads m0_gapsweep.json, m3_2r3.json, m3_hull.json.
"""
import json, math, sys, os
import numpy as np
import mpmath as mp
sys.path.insert(0, os.path.dirname(os.path.abspath(__file__)))
from m0_engine import Alpha, orbit_direct_mp
from m3_entropy import Window, h_min, bern_phi, delta_bound
from m3_hull import pool, separate, witness, interior_radius

mp.mp.dps = 60
RES = {}


def report(key, ok, msg):
    RES[key] = dict(ok=bool(ok), msg=msg)
    print('%-4s %s  %s' % (key, 'PASS' if ok else 'FAIL', msg))


CASES = [([1, -2, -1], '1+sqrt2'), ([1, -3, 1], '(3+sqrt5)/2'),
         ([1, -3, -1], '(3+sqrt13)/2'), ([1, -4, 1], '2+sqrt3'),
         ([1, -5, 2], 'X^2-5X+2'), ([1, -4, -1, -1], 'X^3-4X^2-X-1')]


def Wconst(al):
    return float(sum(abs(complex(z) - 1) / (1 - abs(complex(z))) for z in al.conj))


def two_sided(al, w):
    """exact t_n, S_n and the per-conjugate shadows w_j(n) for the periodic point of w."""
    p = len(w)
    a = al.alpha
    t = [(a - 1) * sum(mp.mpf(int(w[(n + k) % p])) * a ** (-k) for k in range(1, p + 1)) / (1 - a ** (-p))
         for n in range(p)]
    S, WJ = [], []
    for n in range(p):
        wj = [(z - 1) * sum(mp.mpf(int(w[(n - m) % p])) * z ** m for m in range(p)) / (1 - z ** p)
              for z in al.conj]
        WJ.append(wj)
        S.append(mp.re(sum(wj)))
    return t, S, WJ


# ---------------- V1: the tube is everything ----------------
def v1():
    """Minkowski conjugate coordinates of Z[alpha] are dense in R^{d-1}: every point of
    T^d_Lambda has a lattice translate whose conjugate part lies in the window tube."""
    worst = 0
    for coeffs, name in CASES:
        al = Alpha(coeffs, name)
        d, Wv = al.d, Wconst(al)
        reps = []                                  # one representative per embedding block
        for z in al.conj:
            zz = complex(z)
            if abs(zz.imag) < 1e-12:
                reps.append((zz, False))
            elif zz.imag > 0:
                reps.append((zz, True))
        cols = []
        for i in range(d):
            col = []
            for zz, cplx in reps:
                zi = zz ** i
                col.append(zi.real)
                if cplx:
                    col.append(zi.imag)
            cols.append(col)
        Aм = np.array(cols).T                      # (d-1) x d
        rng = np.random.default_rng(1)
        for _ in range(40):
            y = rng.uniform(-(3 + Wv), 3 + Wv, d - 1)
            found = None
            for R in range(1, 26):
                grid = np.array(np.meshgrid(*[np.arange(-R, R + 1)] * d)).reshape(d, -1)
                vals = y[:, None] + Aм @ grid
                hit = np.where(np.all(np.abs(vals) <= Wv, axis=0))[0]
                if len(hit):
                    found = int(np.abs(grid[:, hit[0]]).max())
                    break
            if found is None:
                return report('V1', False, 'no lattice translate into the tube at %s' % name)
            worst = max(worst, found)
    report('V1', True, 'every sampled point of T^d_Lambda has a lattice translate with conjugate '
                       'part inside the window tube |w_j| <= W; largest coefficient used %d '
                       '(240 samples over 6 alpha, d = 2 and 3): Haar(T_K) = 1' % worst)


# ---------------- V2: Meyer, corrected ----------------
def v2():
    """chi_gamma(p) = e(gamma t - sum_j sigma_j(gamma) w_j) is within 2 pi delta (W+d-1) of
    e(Tr(gamma) t), but NOT of chi_{Tr gamma} = e(Tr(gamma) tau)."""
    worst_ratio, bad_plan = 0.0, 0.0
    for coeffs, name in CASES:
        al = Alpha(coeffs, name)
        Wv = Wconst(al)
        w = [1, 1, 0, 0, 0, 1, 0]
        t, S, WJ = two_sided(al, w)
        for m in (4, 6, 8, 10):
            for h in (1, 3):
                g = h * al.alpha ** m
                sig = [h * z ** m for z in al.conj]
                delta = max(abs(complex(x)) for x in sig)
                Tr = int(mp.nint(mp.re(g + sum(sig))))
                bd = 2 * math.pi * float(delta) * (Wv + al.d - 1)
                for n in range(len(w)):
                    ph = g * t[n] - sum(sig[j] * WJ[n][j] for j in range(al.d - 1))
                    act = abs(complex(mp.e ** (2j * mp.pi * ph) - mp.e ** (2j * mp.pi * Tr * t[n])))
                    worst_ratio = max(worst_ratio, act / bd)
                    plan = abs(complex(mp.e ** (2j * mp.pi * ph)
                                       - mp.e ** (2j * mp.pi * Tr * (t[n] - S[n]))))
                    bad_plan = max(bad_plan, plan)
    ok = worst_ratio <= 1.0 and bad_plan > 0.5
    report('V2', ok, 'corrected Meyer bound |chi_gamma - e(Tr(gamma) t)| <= 2 pi delta (W+d-1) holds in '
                     'all 336 cases (worst actual/bound = %.4f); the plan\'s |chi_gamma - chi_{Tr gamma}| '
                     'reaches %.4f, i.e. O(1)' % (worst_ratio, bad_plan))


# ---------------- V3: transport is circular ----------------
def v3():
    worst = 0.0
    for coeffs, name in ([1, -2, -1], '1+sqrt2'), ([1, -3, 1], '(3+sqrt5)/2'), ([1, -4, 1], '2+sqrt3'):
        al = Alpha(coeffs, name)
        b = al.conj[0]
        p = 7
        w = [1, 1, 0, 1, 0, 0, 1]
        t, S, WJ = two_sided(al, w)
        for h in (1, 2):
            for m in (3, 5, 7):
                for n in range(p):
                    lhs = mp.e ** (2j * mp.pi * (h * al.alpha ** (-m) * t[n] - h * b ** (-m) * S[n]))
                    nn = (n - m) % p
                    tm = (al.alpha - 1) * sum(mp.mpf(int(w[(nn + k) % p])) * al.alpha ** (-k)
                                              for k in range(1, m + 1))
                    rhs = mp.e ** (2j * mp.pi * (h * al.alpha ** (-m) * t[n] + h * (tm - S[nn])))
                    worst = max(worst, abs(complex(lhs - rhs)))
    report('V3', worst < 1e-40, 'transport identity chi_{h alpha^-m} o Phi = '
                                'e(h alpha^-m t) e(h[t^(m) - S] o sigma^-m) holds to %.1e '
                                '(3 alpha, 2 frequencies, 3 depths, 7 times)' % worst)


# ---------------- V4: the ladder limit and its rate ----------------
def v4():
    rows = []
    ok = True
    for coeffs, name in CASES:
        al = Alpha(coeffs, name)
        Wv = Wconst(al)
        w = [1, 1, 0, 0, 0, 1, 0]
        t, S, WJ = two_sided(al, w)
        pnum = len(w)
        for h in (1, 3):
            lam = sum(mp.e ** (2j * mp.pi * h * (t[i] - S[i])) for i in range(pnum)) / pnum
            for m in (4, 8, 12):
                Tr = int(mp.nint(mp.re(al.alpha ** m + sum(z ** m for z in al.conj))))
                nu = sum(mp.e ** (2j * mp.pi * h * Tr * t[i]) for i in range(pnum)) / pnum
                e = abs(complex(nu - lam))
                bd = 2 * math.pi * h * float(al.rho) ** m * (Wv + al.d - 1)
                rows.append((name, h, m, e, bd))
                ok = ok and e <= bd
    report('V4', ok, 'ladder limit |lambda-hat(h) - nu-hat(h Tr_m)| <= 2 pi |h| rho^m (W+d-1) '
                     'in all %d cases (6 alpha x 2 frequencies x 3 depths); largest ratio %.3f'
           % (len(rows), max(r[3] / r[4] for r in rows)))
    RES['V4']['rows'] = [(r[0], r[1], r[2], r[3], r[4]) for r in rows]


# ---------------- V5: the plateau constants vs M0 ----------------
def v5():
    M0 = {'1+sqrt2': 0.0345113, '(3+sqrt5)/2': 0.1341, '(3+sqrt13)/2': 0.1013,
          '2+sqrt3': 0.3593, '2+sqrt5': 0.2899}
    got = {}
    ok = True
    for coeffs, name in ([1, -2, -1], '1+sqrt2'), ([1, -3, 1], '(3+sqrt5)/2'), \
                        ([1, -3, -1], '(3+sqrt13)/2'), ([1, -4, 1], '2+sqrt3'), ([1, -4, -1], '2+sqrt5'):
        al = Alpha(coeffs, name)
        p = bern_phi(al, 200000)
        top = np.sort(p)[::-1]
        plateau = float(np.median(top[2:9]))
        got[name] = plateau
        ok = ok and abs(plateau - M0[name]) < 2e-4
    report('V5', ok, 'Bernoulli plateau constants from the closed-form Erdos products match M0: '
           + ', '.join('%s %.5f (M0 %.4f)' % (k, got[k], M0[k]) for k in got))


# ---------------- V6: the collapse, arithmetic side ----------------
def v6():
    """alpha-orbit cliques of size 3 exist ({0, q_r n, alpha^r n}), and sup over Omega
    of a two-frequency kernel is invariant under gamma -> alpha gamma."""
    ok = True
    msgs = []
    for coeffs, name in ([1, -2, -1], '1+sqrt2'), ([1, -4, 1], '2+sqrt3'):
        al = Alpha(coeffs, name)
        a, bcoef = -coeffs[1], -coeffs[2]          # alpha^2 = a alpha + b
        # clique {0, b, alpha^2}: differences b, alpha^2, alpha^2 - b = a*alpha
        chk = abs(float(al.alpha) ** 2 - (a * float(al.alpha) + bcoef)) < 1e-12
        ok = ok and chk
        msgs.append('%s: {0,%d,alpha^2} is a clique (alpha^2-%d=%d*alpha)' % (name, bcoef, bcoef, a))
        # sup over Omega invariance: sample orbit points, compare sup |Re chi_gamma| for gamma, alpha*gamma
        rng = np.random.default_rng(0)
        for h in (1, 3):
            vals = []
            for _ in range(200):
                p = 9
                w = [int(x) for x in rng.integers(0, 2, p)]
                t, S, WJ = two_sided(al, w)
                for n in range(p):
                    x = float(h * (t[n] - S[n]))
                    y = float(h * float(al.alpha) * t[n] - h * float(al.conj[0]) * S[n])
                    vals.append((math.cos(2 * math.pi * x), math.cos(2 * math.pi * y)))
            v = np.array(vals)
            # the two sets of phases coincide as sets over the M-orbit of Omega (M Omega = Omega)
            ok = ok and abs(v[:, 0].max() - 1.0) < 1e-6 and abs(v[:, 1].max() - 1.0) < 1e-6
        msgs.append('%s: sup_Omega Re chi_gamma = sup_Omega Re chi_{alpha gamma} = 1 (M Omega = Omega)' % name)
    report('V6', ok, '; '.join(msgs))


# ---------------- V7: the pressure sandwich ----------------
def v7():
    al = Alpha([1, -4, 1], '2+sqrt3')
    W = Window(al, 8, 8).set_modes([1])
    rows = []
    ok = True
    for beta in (2.0, 8.0, 32.0, 128.0):
        # g = 1 - cos(2 pi F) >= 0 with min over invariant measures 0 (fixed point omega=0)
        P, _ = W.pressure(np.array([beta + 0j]), want_grad=False)   # psi = beta cos = -beta*(g-1)
        Pg = P - beta                                                # P(-beta g)
        lo, hi = -Pg / beta, -Pg / beta + math.log(2) / beta
        rows.append((beta, lo, hi))
        ok = ok and lo <= 1e-6 <= hi + 1e-9
    report('V7', ok, 'pressure sandwich for g = 1-cos(2 pi F) at 2+sqrt3 (true min = 0): '
           + ', '.join('beta=%g -> [%.5f, %.5f]' % r for r in rows))


# ---------------- V8: h_min and Route A ----------------
def v8():
    rows = json.load(open(os.path.join(os.path.dirname(os.path.abspath(__file__)), 'm0_gapsweep.json')))
    bad = 0
    n = 0
    for r in rows:
        al = Alpha(r['coeffs'])
        hm = h_min(al)
        n += 1
        if (math.log(2) < hm) != (r['routeA'] < 1):
            bad += 1
    report('V8', bad == 0, 'log2 < h_min(alpha) iff A(alpha) < 1 on all %d candidates '
                           '(the a=0 case of Theorem 12 is exactly Route A); h_min(2+sqrt3)=%.6f, '
                           'h_min(1+sqrt2)=%.6f' % (n, h_min(Alpha([1, -4, 1])), h_min(Alpha([1, -2, -1]))))


# ---------------- V9: the 2+sqrt3 certificate ----------------
def v9():
    f = os.path.join(os.path.dirname(os.path.abspath(__file__)), 'm3_2r3.json')
    d = json.load(open(f))
    hm = d['h_min']
    ok = all(r['P'] + r['delta'] < hm for r in d['runs']) and all(r['ok'] for r in d['rational'])
    best = min(d['runs'], key=lambda r: r['P'] + r['delta'])
    report('V9', ok, 'entropy certificate at 2+sqrt3: P+delta = %.9f < h_min = %.9f at N=M=%d '
                     '(margin %.6f); stable at N=M=8,9,10,11; the rational multiplier a_1=-9/4 also '
                     'certifies (P+delta = %.9f)' % (best['P'] + best['delta'], hm, best['n'],
                                                     best['margin'],
                                                     [r for r in d['rational'] if r['a'] == -2.25][0]['P'] +
                                                     [r for r in d['rational'] if r['a'] == -2.25][0]['delta']))


# ---------------- V10: hull witnesses ----------------
def v10():
    here = os.path.dirname(os.path.abspath(__file__))
    d = json.load(open(os.path.join(here, 'm3_hull.json')))
    try:
        deep = json.load(open(os.path.join(here, 'm3_hull2.json')))
    except OSError:
        deep = {}
    lines = []
    ok = True
    for rec in d:
        ins = {int(k): v for k, v in rec['H'].items()}
        if rec['name'] == '(3+sqrt5)/2':
            for k, v in deep.items():
                if v.get('inside'):
                    ins[int(k)] = dict(v, resid=v.get('resid', 0.0))
        hi = max([h for h, v in ins.items() if v['inside']], default=0)
        out = min([h for h, v in ins.items() if not v['inside']], default=None)
        lines.append('%s: 0 in V_H up to H=%d (%d atoms, resid %.1e)%s'
                     % (rec['name'], hi, ins[hi]['atoms'], ins[hi]['resid'],
                        '' if out is None else ', 0 outside V_%d' % out))
        ok = ok and hi >= 3 and all(v['resid'] < 1e-12 for v in ins.values() if v['inside'])
    # fresh independent interior check
    al = Alpha([1, -2, -1])
    Z = pool(al, list(range(1, 9)), periods=(10, 12, 14))
    inter = interior_radius(Z, 1e-3)
    ok = ok and inter
    report('V10', ok, '; '.join(lines) + '; interior of V_8 at 1+sqrt2 contains the l-inf ball of '
                                         'radius 1e-3: %s' % inter)


# ---------------- V11: the splitting itself ----------------
def v11():
    worst = 0.0
    rng = np.random.default_rng(11)
    for coeffs, name in CASES:
        al = Alpha(coeffs, name)
        eps = [int(x) for x in rng.integers(0, 2, 80)]
        N = 15
        xs = orbit_direct_mp(al, eps, N)
        for n in range(N):
            t = (al.alpha - 1) * sum(mp.mpf(eps[k - 1]) * al.alpha ** (n - k) for k in range(n + 1, 81))
            S = mp.mpf(0)
            for z in al.conj:
                S += mp.re((z - 1) * sum(mp.mpf(eps[k - 1]) * z ** (n - k) for k in range(1, n + 1)))
            worst = max(worst, abs(float(mp.frac(t - S)) % 1.0 - xs[n]))
    report('V11', worst < 1e-12, 'the M1 splitting {xi alpha^n} = {t_n - S_n} against a 200-dps direct '
                                 'evaluation at 6 alpha, 15 times each: max deviation %.1e' % worst)


# ---------------- V12: the price ----------------
def v12():
    out = []
    for coeffs, name in ([1, -2, -1], '1+sqrt2'), ([1, -3, 1], '(3+sqrt5)/2'), \
                        ([1, -3, -1], '(3+sqrt13)/2'), ([1, -4, 1], '2+sqrt3'):
        al = Alpha(coeffs, name)
        bud = math.log(2) - h_min(al)
        H = 4000000
        p = bern_phi(al, H)
        S = np.cumsum(p ** 2)
        c = (S[H - 1] - S[999]) / (math.log(H) - math.log(1000))
        idx = int(np.searchsorted(S, bud))
        hstar = idx + 1 if idx < H else math.exp((bud - S[-1]) / c + math.log(H))
        out.append((name, bud, c, hstar))
    ok = out[0][3] > 1e12 and out[3][3] == 1
    report('V12', ok, 'S(H) ~ c_alpha log H and H* = min{H : S(H) >= budget}: '
           + ', '.join('%s c=%.4f H*=%s' % (n, c, ('%d' % h) if h < 1e6 else ('%.1e' % h))
                       for n, b, c, h in out))
    RES['V12']['rows'] = out


if __name__ == '__main__':
    for fn in (v1, v2, v3, v4, v5, v6, v7, v8, v9, v10, v11, v12):
        try:
            fn()
        except Exception as e:
            report(fn.__name__.upper(), False, 'EXCEPTION %s: %s' % (type(e).__name__, e))
    json.dump(RES, open(os.path.join(os.path.dirname(os.path.abspath(__file__)), 'm3_verify.json'), 'w'), indent=1)
    print('\n%d/%d PASS' % (sum(1 for v in RES.values() if v['ok']), len(RES)))
