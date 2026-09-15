#!/usr/bin/env python3
# (C) 2026 Ralf Stephan, in collaboration with Claude Code
# CC0 1.0 Universal (public domain dedication).
"""WP8 of plan_BB61_improve_m3_entropy.html -- the gates the rewrite has to pass.

The rewrite of `m3_entropy.py` touches the one file whose numbers the last three notes
report, so nothing new is to be believed until the old numbers come back out of it.

G1  bitwise      WP1/WP2 change no arithmetic: `Window` against a naive reference
G2  published    the recorded certificates recompute at their own windows
G3  accounting   every approximation is inside the enclosure (WP3, WP4, WP5)
G4  the box      no reported optimum sits on the multiplier cap
G5  convexity    WP6's bundle bracket really is a lower bound, and the audit fires
G6  the window   WP7's `window_eps`/`best_split` agree with what they replace
G7  steered pool WP9 turns a "pool too small" row of M7 sec 4 into a bound

G1 does not diff against a saved copy of the old file -- that would only prove the two
copies agree.  It re-implements the operator the slow, obvious way (four index arrays,
the mode loop, the iterate-difference stopping rule) and demands bitwise equality with
`Window` configured to take the same path: `stop='vector'`, `warm=False`, and the FFT
crossover disabled.  Anything but bitwise is a bug, since WP1 reorders no arithmetic.

Requires numpy, scipy.  Reads m3_2r3.json, m3_cert.json, m4_frontier.json,
m4_lean_cert.json, m7_price.json.  Writes m8_gates.json.
"""
import json, os, sys, time, warnings
import numpy as np

sys.path.insert(0, os.path.dirname(os.path.abspath(__file__)))
from m0_engine import Alpha
from m3_entropy import (Window, best_split, choose_window, delta_bound, h_min,
                        minimize_pressure, window_eps)
from m4_fourier import best_window, certify
from m7_price import BlockChain, cutting_plane_lower

RES = []


def rec(tag, what, ok, detail):
    RES.append(dict(id=tag, what=what, ok=bool(ok), detail=detail))
    print('%-4s %-58s %s  %s' % (tag, what, 'PASS' if ok else 'FAIL', detail), flush=True)


CASES = [([1, -4, 1], '2+sqrt3'), ([1, -2, -1], '1+sqrt2'),
         ([1, -3, 1], '(3+sqrt5)/2'), ([1, -3, -1], '(3+sqrt13)/2')]


# ---------------------------------------------------------------------------
# G1 -- the naive reference
# ---------------------------------------------------------------------------

def naive(W, a, iters=500, tol=1e-13, ub_iters=400, ub_tol=1e-14):
    """The operator written out the obvious way: index arrays, mode loop, iterate test.

    Deliberately slow and deliberately literal.  `word`, `tgt`, `qidx`, `sidx` are the
    four arrays WP1 removed; the potential is the `2H`-pass trigonometric loop WP3
    removed; `Phi_h` is the `H`-pass complex-exponential sum WP4 removed; and the
    stopping rule is the pre-WP2 iterate difference.  Returns (P, phis, entropy, ub).
    """
    L = W.L
    u = np.arange(1 << L, dtype=np.int64)
    word = [u, u | (1 << L)]
    tgt = [(u >> 1), (u >> 1) | (1 << (L - 1))]
    q = u & ((1 << (L - 1)) - 1)
    sb = u >> (L - 1)

    ph = 2 * np.pi * W.F
    lw = np.zeros_like(W.F)
    for i, h in enumerate(W.modes):
        lw += a[i].real * np.cos(h * ph) - a[i].imag * np.sin(h * ph)

    m = lw.max()
    w = np.exp(lw - m)
    w0, w1 = w[word[0]], w[word[1]]
    t0, t1 = tgt

    def power(mul, x0, norm, iters=iters, tol=tol):
        x, lam = x0, 1.0
        for it in range(iters):
            xn = mul(x)
            lam = xn.sum() / x.sum()
            xn = xn / (np.linalg.norm(xn) if norm == 'l2' else xn.max())
            done = it > 8 and np.max(np.abs(xn - x)) < tol
            x = xn
            if done:
                break
        return x, lam

    r, lam = power(lambda x: w0 * x[t0] + w1 * x[t1], np.ones(1 << L), 'l2')
    P = float(np.log(lam) + m)
    ws0 = np.where(sb == 0, w0[2 * q], w1[2 * q])
    ws1 = np.where(sb == 0, w0[2 * q + 1], w1[2 * q + 1])
    l, _ = power(lambda x: ws0 * x[2 * q] + ws1 * x[2 * q + 1], np.ones(1 << L), 'l2')
    mu = np.concatenate([l * w0 * r[t0], l * w1 * r[t1]])
    mu /= mu.sum()
    Fe = np.concatenate([W.F[word[0]], W.F[word[1]]])
    phis = np.array([np.sum(mu * np.exp(2j * np.pi * float(h) * Fe)) for h in W.modes])
    psi = np.concatenate([lw[word[0]], lw[word[1]]])
    ent = P - float(np.sum(mu * psi))

    rr, _ = power(lambda x: w0 * x[t0] + w1 * x[t1], np.ones(1 << L), 'max',
                  ub_iters, ub_tol)          # pressure_ub's own defaults, not pressure's
    ub = (float('inf') if rr.min() <= 0
          else float(np.log(((w0 * rr[t0] + w1 * rr[t1]) / rr).max()) + m))
    return P, phis, ent, ub


def gate1():
    rng = np.random.default_rng(7)
    n = bad = 0
    worst = []
    for coeffs, nm in CASES:
        al = Alpha(coeffs, nm)
        for N, M in [(4, 4), (6, 6), (8, 8)]:
            for H in [1, 2, 3, 8, 16]:
                W = Window(al, N, M, warm=False).set_modes(list(range(1, H + 1)))
                W.stop, W.fft_min_modes = 'vector', 10 ** 9
                for _ in range(4):
                    x = rng.normal(size=2 * H) * (0.7 / H)   # M4 sec 8's magnitude
                    a = x[:H] + 1j * x[H:]
                    P, (ph, en) = W.pressure(a)
                    ub = W.pressure_ub(a)
                    nP, nph, nen, nub = naive(W, a)
                    n += 1
                    okv = [P == nP, np.array_equal(ph, nph), en == nen, ub == nub]
                    if not all(okv):
                        bad += 1
                        worst.append('%s L=%d H=%d %s' % (nm, N + M, H,
                                     [k for k, v in zip('P phi ent ub'.split(), okv)
                                      if not v]))
    rec('G1', 'bitwise: Window == the naive reference (WP1 reorders nothing)',
        bad == 0, ('%d comparisons over %d alpha, 3 windows, 5 mode counts, all '
                   'identical to the last bit' % (n, len(CASES))) if bad == 0
        else '%d of %d differ: %s' % (bad, n, worst[:4]))


# ---------------------------------------------------------------------------
# G2 -- the published rows
# ---------------------------------------------------------------------------

def gate2():
    det, ok = [], True

    d = json.load(open('m3_2r3.json'))                    # M3 sec 8.1, the 2+sqrt3 rows
    al = Alpha([1, -4, 1], '2+sqrt3')
    worst = 0.0
    for row in d['runs']:
        W = Window(al, row['n'], row['n']).set_modes([1])
        a = np.array([row['a_re'] + 1j * row['a_im']])
        P, _ = W.pressure(a, want_grad=False)
        worst = max(worst, abs(P - row['P']), abs(delta_bound(W, a) - row['delta']))
        del W
    W = Window(al, 11, 11).set_modes([1])
    for row in d['rational']:
        a = np.array([row['a'] + 0j])
        P, _ = W.pressure(a, want_grad=False)
        worst = max(worst, abs(P - row['P']), abs(delta_bound(W, a) - row['delta']))
    ok &= worst < 1e-9
    det.append('m3_2r3.json: %d recorded (P, delta) pairs at their own windows, worst '
               'deviation %.1e' % (len(d['runs']) + len(d['rational']), worst))

    f = json.load(open('m4_frontier.json'))               # M4 sec 7, the certificates
    nc, wc = 0, 0.0
    for r in f:
        if not r.get('a_re'):
            continue
        a = np.array(r['a_re']) + 1j * np.array(r['a_im'])
        for key, c in r['cert'].items():
            W = Window(Alpha(r['coeffs'], r['poly']), c['N'], c['M'])
            W.set_modes(list(range(1, len(a) + 1)))
            wc = max(wc, abs(certify(W, a) - c['Lambda_ub']))
            nc += 1
            del W
    ok &= wc < 1e-9
    det.append('m4_frontier.json: %d stored certificates re-certified from their own '
               'multiplier and window, worst deviation %.1e' % (nc, wc))

    lc = json.load(open('m4_lean_cert.json'))             # M4 sec 9 / BB61/Pressure.lean
    a, b, Wp, B = lc['a'], lc['b'], lc['W'], lc['B']
    integer_ok = a ** B < b ** B * Wp * 193
    rate = np.log(a / b) - np.log(Wp) / B
    ok &= integer_ok and abs(rate - lc['rate']) < 1e-12 and rate < lc['h_min']
    det.append('m4_lean_cert.json: a^%d < b^%d W 193 is %s and the mean-corrected rate '
               '%.6f < h_min %.6f, in exact integer arithmetic'
               % (B, B, integer_ok, rate, lc['h_min']))

    p = json.load(open('m7_price.json'))                  # M7 sec 4, the brackets
    nb = 0
    for r in p:
        for k, v in r['rows'].items():
            if v['E_lb'] is not None:
                nb += 1
                ok &= v['E_lb'] <= v['E_ub'] + 2e-2       # the sec-4 truncation slack
    det.append('m7_price.json: all %d recorded brackets have E_lb <= E_ub within the '
               'section-4 truncation slack' % nb)

    rec('G2', 'the published rows recompute from their stored data', ok, ' ; '.join(det))


# ---------------------------------------------------------------------------
# G3 -- the accounting
# ---------------------------------------------------------------------------

def gate3():
    rng = np.random.default_rng(11)
    r3 = r4 = 0.0
    enclosed = eps_ok = True
    n = 0
    for coeffs, nm in CASES[:3]:
        al = Alpha(coeffs, nm)
        for N, M in [(6, 6), (9, 9)]:
            for H in [8, 32, 128]:
                Wf = Window(al, N, M).set_modes(list(range(1, H + 1)))
                We = Window(al, N, M, warm=False).set_modes(list(range(1, H + 1)))
                We.stop, We.fft_min_modes = 'vector', 10 ** 9
                G = Wf.grid
                eps_ok &= abs(Wf.eps - (Wf.err + (0.0 if G is None else 0.5 / G))) < 1e-18
                for _ in range(3):
                    x = rng.normal(size=2 * H) * (0.7 / H)
                    a = x[:H] + 1j * x[H:]
                    n += 1
                    P, (ph, _) = Wf.pressure(a)
                    enclosed &= Wf.pressure_ub(a) + delta_bound(Wf, a) >= P - 1e-12
                    if G is None:
                        continue
                    S1 = float(np.sum(Wf.modes * np.abs(a)))
                    r3 = max(r3, np.max(np.abs(Wf.weights(a) - We.weights(a)))
                             / (np.pi * S1 / G))          # WP3: Lip(psi)/2G, doubled
                    r4 = max(r4, np.max(np.abs(ph - Wf.phis_exact(Wf._mu)))
                             / (0.5 * (np.pi * H / G) ** 2))   # WP4: linear deposition
                del Wf, We
    ok = enclosed and eps_ok and r3 <= 1.0 and r4 <= 1.0
    rec('G3', 'every approximation is inside the enclosure (WP3, WP4, WP5)', ok,
        'over %d multipliers: pressure_ub + delta_bound encloses the reported pressure '
        'everywhere (%s); eps == err + 1/(2G) exactly (%s); the WP3 grid deviation is '
        '%.3f of pi S1/G and the WP4 coefficient deviation %.3f of (pi H/G)^2/2, both '
        'of which delta_bound already charges' % (n, enclosed, eps_ok, r3, r4))


# ---------------------------------------------------------------------------
# G4 -- the box
# ---------------------------------------------------------------------------

def gate4():
    det, ok = [], True
    f = json.load(open('m4_frontier.json'))
    mx = 0.0
    for r in f:
        if r.get('a_re'):
            mx = max(mx, float(np.abs(np.array(r['a_re'])
                                      + 1j * np.array(r['a_im'])).max()))
    ok &= mx < 8.0                                        # m4_run_frontier's own cap
    det.append('m4_frontier.json: max|a_h| over every stored certificate is %.4f, '
               'inside the cap 8 those runs used' % mx)

    al = Alpha([1, -4, 1], '2+sqrt3')
    W = Window(al, 8, 8).set_modes([1])
    minimize_pressure(W)
    ok &= not W.last_solve['box_active']
    det.append('a fresh 2+sqrt3 optimum reports max|a_h| = %.4f of cap %g, box inactive, '
               'so the value is E_H and not inf over a box'
               % (W.last_solve['amax'], W.last_solve['cap']))

    with warnings.catch_warnings(record=True) as caught:  # and it is loud when it is not
        warnings.simplefilter('always')
        minimize_pressure(W, cap=0.5)
        fired = any(issubclass(c.category, RuntimeWarning) for c in caught)
    raised = False
    try:
        minimize_pressure(W, cap=0.5, strict_box=True)
    except RuntimeError:
        raised = True
    ok &= W.last_solve['box_active'] and fired and raised
    det.append('at cap=0.5 the same run reports the box active, warns, and raises under '
               'strict_box')
    rec('G4', 'no reported optimum sits on the multiplier cap', ok, ' ; '.join(det))


# ---------------------------------------------------------------------------
# G5 -- WP6's convexity
# ---------------------------------------------------------------------------

def gate5():
    rng = np.random.default_rng(5)
    ok, det = True, []
    for coeffs, nm, H in [([1, -2, -1], '1+sqrt2', 8), ([1, -3, 1], '(3+sqrt5)/2', 8)]:
        al = Alpha(coeffs, nm)
        N, M, _ = best_split(al, 14)
        W = Window(al, N, M).set_modes(list(range(1, H + 1)))
        P, x, _, _ = minimize_pressure(W)
        ls = W.last_solve
        lo = np.inf
        for _ in range(25):                               # convexity: nothing in the
            y = np.clip(x + rng.normal(size=2 * H)        # box may beat the bracket
                        * rng.choice([0.05, 0.5, 3.0]), -ls['cap'], ls['cap'])
            lo = min(lo, W.pressure(y[:H] + 1j * y[H:], want_grad=False)[0])
        P2, _, _, _ = minimize_pressure(W, x0=x, maxiter=2000, gap_target=1e-9, rounds=6)
        ok &= (ls['lb_box'] <= P + 1e-9 and lo >= ls['lb_box'] - 1e-9
               and P2 >= ls['lb_box'] - 1e-9)
        det.append('%s H=%d: E_ub %.9f, bundle lb %.9f (gap %.1e); 25 box points and a '
                   'deeper restart all stay above it' % (nm, H, P, ls['lb_box'],
                                                         ls['gap']))
        del W
    rec('G5', "WP6's bundle bracket is a lower bound over the box", ok, ' ; '.join(det))


# ---------------------------------------------------------------------------
# G6 -- WP7's window arithmetic
# ---------------------------------------------------------------------------

def gate6():
    bad_e = bad_s = 0
    for coeffs in [[1, -4, 1], [1, -2, -1], [1, -3, 1], [1, -3, -1],
                   [1, -4, -1, -1], [1, -4, -3, -1]]:
        al = Alpha(coeffs)
        for N in range(1, 13):
            for M in range(1, 13):
                W = Window(al, N, M)
                bad_e += W.err != window_eps(al, N, M)
                del W
        for L in range(4, 27):
            bad_s += best_split(al, L) != best_window(al, L)
    al = Alpha([1, -3, 1], '(3+sqrt5)/2')
    c = choose_window(al, 0.7, 1e-3)
    ok = (bad_e == 0 and bad_s == 0 and 2 * np.pi * 0.7 * c['eps'] * 1.1 <= 1e-3)
    rec('G6', "WP7's window arithmetic reproduces what it factors out", ok,
        'window_eps == Window.err on 864 windows (%d bad); best_split == '
        'm4_fourier.best_window on 138 lengths (%d bad); choose_window at '
        '(3+sqrt5)/2, S1 = 0.7, budget 1e-3 gives L = %d, (N,M) = (%d,%d), eps = %.2e'
        % (bad_e, bad_s, c['L'], c['N'], c['M'], c['eps']))


# ---------------------------------------------------------------------------
# G7 -- WP9 on a row that read "pool too small"
# ---------------------------------------------------------------------------

def gate7():
    al = Alpha([1, -3, 1], '(3+sqrt5)/2')
    N, M, H = 5, 7, 1                                     # m7_price.json's own window
    W = Window(al, N, M).set_modes(list(range(1, H + 1)))
    bc = BlockChain(al, N + M, hmax=8)
    P, x, _, _ = minimize_pressure(W)
    r = cutting_plane_lower(W, bc, H, xstar=x, rounds=40)
    row = next(q for q in json.load(open('m7_price.json'))
               if q['poly'] == '(3+sqrt5)/2')['rows'][str(H)]
    ok = (row['E_lb'] is None and r['lb'] is not None
          and r['lb'] <= P + 1e-6 and r['gap_raw'] <= 1e-5)
    rec('G7', 'WP9 turns a "pool too small" row into a two-sided bound', ok,
        'M7 sec 4 records E_lb = infeasible at (3+sqrt5)/2, H = %d with a %d-vector '
        'pool; the steered pool reaches feasibility in %d rounds with %d columns and '
        'brackets E_%d in [%.9f, %.9f] (raw gap %.1e), against the optimiser\'s '
        '%.9f' % (H, row['pool'], r['rounds'], r['pool'], H, r['lb'], r['ub_raw'],
                  r['gap_raw'], P))


# ---------------------------------------------------------------------------

if __name__ == '__main__':
    only = set(sys.argv[1:])
    t0 = time.time()
    for name, fn in [('G1', gate1), ('G2', gate2), ('G3', gate3), ('G4', gate4),
                     ('G5', gate5), ('G6', gate6), ('G7', gate7)]:
        if only and name not in only:
            continue
        fn()
    n = sum(r['ok'] for r in RES)
    print('\n%d/%d PASS   (%.0fs)' % (n, len(RES), time.time() - t0))
    json.dump(RES, open('m8_gates.json', 'w'), indent=1)
