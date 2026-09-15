#!/usr/bin/env python3
# (C) 2026 Ralf Stephan, in collaboration with Claude Code
# CC0 1.0 Universal (public domain dedication).
"""R2c of plan-BB61-counterexample.html: M8's W4 deep-window enclosure at 1+sqrt2.

W4 (`m8_w4.py`, `m8_w4.log`) certified the two *middle* quadratic units, where 10.61
was already expected to fall.  It has never been run at the named case.  The folder's
only certified upper bound for `E_H(1+sqrt2)` is M4's `m4_frontier.json` row `24/16`,
`Lambda_enc = 0.689990` -- log 2 minus 0.0032, at H = 16, on a multiplier of norm
`sum_h h|a_h| = 0.73` that the search then never moved again: M4's whole ladder reads
0.689922 at H = 16, 24, 32, 48 and 64, to six decimals, at the same 0.73.

Why the search stalls, measured before it is re-run
---------------------------------------------------
`m4_fourier.search` minimises the surrogate  `P~(a) + 2 pi (sum_h h|a_h|) eps`, whose
penalty is the *uniform* Lipschitz charge -- M3's `delta_bound`, the thing M4 Prop. 3
was written to replace.  What is certified is the word-wise enclosure, which pays
`eps |g'(F~_u)|` where the Gibbs measure sits.  The two differ by a measured factor.
Reading it straight off W4's own twenty certificates,

    kappa_ww := (Lambda_enc - P_deep) / (2 pi S1 eps)  in  [0.042, 0.207],

i.e. the search is charged five to twenty-four times what the certificate pays.  At
the two middle units that is affordable -- the pressure falls fast enough there to buy
its way past the penalty.  At 1+sqrt2 it is not: R2a measured the constrained pressure
falling 3.3e-3 per doubling of H, thirteen times slower, so an over-charged penalty
freezes the multiplier at once.  That is the stall, and it is a property of the
surrogate, not of alpha.

So the ladder is run at a *grid* of penalty rates, `eps_target = kappa * eps(L=24)`
for kappa in {1, 1/4, 1/16, 0}, kappa = 1 being W4's own protocol and kappa = 0 the
unpenalised control; every winner is certified at every deep window.  This is sound
for the same reason W4's protocol is: `certify` is a Collatz-Wielandt bound valid for
whatever strictly positive vector it ends up holding, and it does not care which
search produced the multiplier handed to it.  Only the *claim* has to be certified.

The two moments the surrogate should have used
-----------------------------------------------
`enclose_blk2` returns, beside the enclosure itself, `sup_gp = max_u |g'(F~_u)|` and
`mean_gp = <|g'|>_mu` against the deep window's own Gibbs vector.  They factor the
over-charge into two independent losses,

    2 pi S1  --(kappa_sup)-->  max|g'|  --(kappa_mean)-->  <|g'|>_mu ,

and they make the enclosure *predictable*: to first order in eps the pressure of an
additively perturbed potential moves by the mu-integral of the perturbation, so

    Lambda_enc  =  P_deep + eps <|g'|>_mu + eps^2 M2 / 2 + O(eps^2)  ,

which self-check 16 tests and which is the surrogate the folder should be minimising.

Sub-commands
    r2c_deep.py checks          the 18 self-checks
    r2c_deep.py calib           kappa_ww off W4's stored certificates (no compute)
    r2c_deep.py repro           M4 sec 7's published 1+sqrt2 rows, re-run
    r2c_deep.py run             the kappa x H ladder and the L = 22 certificates
    r2c_deep.py deep            the L = 24 certificates for the selected rows
    r2c_deep.py table           the note's tables from the JSON
    r2c_deep.py bracket         the two-sided certified bracket on E_H
    r2c_deep.py modes           gate G-A1: the mode support of the optimum
    r2c_deep.py price           the degree axis, the window axis, the exponent
    r2c_deep.py one K H L       one (kappa, H, deep L) cell

Options   --out FILE  --hs 4,8,..  --kappas 1,0.25,..  --lsearch L  --cap C
          --maxiter N  --deep L  --samples N
"""
import os
import sys
import json
import time
import math

import numpy as np

HERE = os.path.dirname(os.path.abspath(__file__))
sys.path.insert(0, HERE)

from m0_engine import Alpha                                       # noqa: E402
from m3_entropy import (Window, best_split, delta_bound, h_min,   # noqa: E402
                        window_eps)
from m4_fourier import (search, certify, enclose, spec_ub,        # noqa: E402
                        best_window, pad)
import m8_w4                                                      # noqa: E402
from m8_w4 import enclose_blk, cw_ub, BLOCK                       # noqa: E402

KEY = '1+sqrt2'
COEFFS, POLY = [1, -2, -1], 'X^2-2X-1'
#: W4's `reproduce` is reused verbatim, and it is keyed off this table
m8_w4.CASES[KEY] = (COEFFS, POLY)

KAPPAS = (1.0, 0.25, 0.0625, 0.0)
HS = (4, 8, 16, 32, 64, 128, 256, 512)
LSEARCH = 18
LREF = 24                      # the penalty rate is kappa * eps(LREF)
LDEEP = (22, 24)
CAP = 20.0
MAXITER = 400
LOG2 = math.log(2.0)
OUT = os.path.join(HERE, 'r2c_deep.json')


def opt(name, default):
    return sys.argv[sys.argv.index(name) + 1] if name in sys.argv else default


def load(path=None):
    try:
        return json.load(open(path or OUT))
    except (IOError, ValueError):
        return {}


def save(d, path=None):
    p = path or OUT
    json.dump(d, open(p, 'w'), indent=1)
    return p


# ---------------------------------------------------------------------------
# the enclosure, with the two moments the surrogate should have used
# ---------------------------------------------------------------------------

def enclose_blk2(W, a, eps=None, mu=None):
    """`m8_w4.enclose_blk`, plus `sup |g'|` and `<|g'|>` over the same pass.

    Returns `(lw, stats)`.  `stats['mean_gp']` is the `mu`-weighted mean when a Gibbs
    vector is supplied and the flat mean otherwise.  The returned array is
    `enclose_blk(W, a, eps)` to the last bit -- same arithmetic, same order, same
    blocking -- which self-check 5 asserts; the moments are accumulated block by block
    so nothing of length `2^(L+1)` is held that `enclose_blk` did not already hold.
    """
    eps = W.err if eps is None else float(eps)
    modes, n = W.modes, W.F.size
    M2 = (2 * np.pi) ** 2 * float(np.sum(modes ** 2 * np.abs(a)))
    out = np.empty(n)
    sup, acc, wsum = 0.0, 0.0, 0.0
    for s in range(0, n, BLOCK):
        e = min(s + BLOCK, n)
        ph = 2 * np.pi * W.F[s:e]
        g = np.zeros(e - s)
        gp = np.zeros(e - s)
        for i, h in enumerate(modes):
            c, si = np.cos(h * ph), np.sin(h * ph)
            g += a[i].real * c - a[i].imag * si
            gp += 2 * np.pi * h * (-a[i].real * si - a[i].imag * c)
        out[s:e] = g + eps * np.abs(gp) + 0.5 * eps ** 2 * M2
        ag = np.abs(gp)
        sup = max(sup, float(ag.max()))
        if mu is None:
            acc += float(ag.sum())
            wsum += float(e - s)
        else:
            acc += float(np.dot(mu[s:e], ag))
            wsum += float(mu[s:e].sum())
    return out, dict(sup_gp=sup, mean_gp=acc / wsum, M2=M2, eps=eps)


# ---------------------------------------------------------------------------
# the ladder and the certificates
# ---------------------------------------------------------------------------

def ladder(al, kappa, Hs=HS, Ls=LSEARCH, eps_ref=None, cap=CAP, maxiter=MAXITER,
           log=print):
    """One warm-started H-ladder at penalty rate `kappa * eps_ref`."""
    Ns, Ms, es = best_split(al, Ls)
    eps_ref = best_split(al, LREF)[2] if eps_ref is None else float(eps_ref)
    tgt = kappa * eps_ref
    W = Window(al, Ns, Ms)
    out, xp, Hp = [], None, 0
    for H in Hs:
        W.set_modes(list(range(1, H + 1)))
        t0 = time.time()
        P, x, pen = search(W, tgt, x0=pad(xp, Hp, H), maxiter=maxiter, cap=cap)
        a = x[:H] + 1j * x[H:]
        S1 = float(np.sum(W.modes * np.abs(a)))
        xmax = float(np.abs(x).max())
        rec = dict(kappa=float(kappa), H=H, L=Ls, N=Ns, M=Ms, eps_search=es,
                   eps_target=float(tgt), P=float(P), pen=float(pen),
                   surrogate=float(P + pen), S1=S1, xmax=xmax, cap=float(cap),
                   box_active=bool(xmax >= cap * (1 - 1e-9)),
                   secs=round(time.time() - t0, 1), x=[float(v) for v in x])
        out.append(rec)
        log('  k=%-7g H=%-4d P~=%.6f  sum h|a|=%9.2f  surrogate=%.6f  max|x|=%.3f  '
            '%s %.0fs' % (kappa, H, P, S1, P + pen, xmax,
                          'BOX' if rec['box_active'] else '.', rec['secs']))
        xp, Hp = x, H
    del W
    return out


def certify_rows(al, rows, L, hm=None, want_mu=True, log=print):
    """Certify a list of ladder rows at the deep window `L`.

    Order differs from W4's in one harmless way: the pressure is taken first, so that
    its Gibbs vector is available for the moments and so that `pressure_ub` starts from
    a converged iterate.  Collatz-Wielandt is valid for *any* positive vector, so a
    better start can only tighten `Lambda_cw`; it never weakens the claim.
    """
    hm = h_min(al) if hm is None else hm
    N, M, e = best_split(al, L)
    t0 = time.time()
    Wd = Window(al, N, M)
    log('  deep window (%d,%d) L=%d err=%.4e  built in %.0fs'
        % (N, M, L, e, time.time() - t0))
    out = []
    for rec in rows:
        H = rec['H']
        Wd.set_modes(list(range(1, H + 1)))
        x = np.array(rec['x'])
        a = x[:H] + 1j * x[H:]
        t0 = time.time()
        Pd, _ = Wd.pressure(a, want_grad=want_mu)
        mu = Wd._mu if want_mu else None
        lw, st = enclose_blk2(Wd, a, mu=mu)
        mu = None
        lam_enc = cw_ub(Wd, lw)
        del lw
        d = delta_bound(Wd, a)
        lam_cw = Wd.pressure_ub(a) + d
        S1 = float(np.sum(Wd.modes * np.abs(a)))
        uni = 2 * np.pi * S1 * Wd.err
        twopiS1 = 2 * np.pi * S1
        pred = Pd + st['eps'] * st['mean_gp'] + 0.5 * st['eps'] ** 2 * st['M2']
        c = dict(kappa=rec['kappa'], H=H, L=L, N=N, M=M, err=Wd.err, eps=Wd.eps,
                 grid=Wd.grid, Lambda_enc=float(lam_enc), Lambda_cw=float(lam_cw),
                 P_deep=float(Pd), delta=float(d), S1=S1, uniform=uni,
                 sup_gp=st['sup_gp'], mean_gp=st['mean_gp'], M2=st['M2'],
                 pred=float(pred), h_min=hm, log2=LOG2,
                 k_ww=(lam_enc - Pd) / uni if uni > 0 else float('nan'),
                 k_sup=st['sup_gp'] / twopiS1 if S1 > 0 else float('nan'),
                 k_mean=st['mean_gp'] / twopiS1 if S1 > 0 else float('nan'),
                 margin_enc=hm - lam_enc, margin_cw=hm - lam_cw,
                 gain_log2=LOG2 - lam_enc, below_log2=bool(lam_enc < LOG2),
                 fires=bool(min(lam_enc, lam_cw) < hm),
                 encloses=bool(lam_enc >= Pd - 1e-12 and lam_cw >= Pd - 1e-12),
                 trust=float(2 * np.pi * H * Wd.err),
                 secs=round(time.time() - t0, 1))
        out.append(c)
        Wd.reset_iterates()
        log('    k=%-7g H=%-4d L=%d  Lambda_enc=%.6f  Lambda_cw=%.6f  P_deep=%.6f  '
            'log2-Lam=%+.5f  k_ww=%.4f  %s  %.0fs'
            % (rec['kappa'], H, L, lam_enc, lam_cw, Pd, LOG2 - lam_enc, c['k_ww'],
               'CERT' if c['fires'] else ('<log2' if c['below_log2'] else '.'),
               c['secs']))
    del Wd
    return out


# ---------------------------------------------------------------------------
# calibration: what the certificate actually pays, off W4's own certificates
# ---------------------------------------------------------------------------

def calib(log=print, extra=None):
    """`kappa_ww` for every certificate W4 stored, and for this run's own.

    Normalised by `err`, not by `eps`: the enclosure is evaluated from `W.F` by the
    trigonometric loop and never touches the WP3 grid, so the grid term `1/(2G)` that
    `W.eps` carries -- and that `delta_bound` rightly charges -- is not part of what
    `Lambda_enc` pays.  It is a 0.3 % correction at these windows and it is recorded
    because getting it the other way round would silently bias the constant this
    section is measuring.
    """
    rows = []
    runs = m8_w4._load('m8_w4.json,m8_w4_ext.json') or []
    for r in runs:
        al = Alpha(r['coeffs'], r['poly'])
        S1 = {v['H']: v['S1'] for v in r['ladder']}
        for t, c in r['cert'].items():
            L, H = map(int, t.split('/'))
            err = window_eps(al, c['N'], c['M'])
            uni = 2 * math.pi * S1[c['H']] * err
            rows.append(dict(key=r['key'], L=L, H=H, S1=S1[c['H']], err=err,
                             Lambda_enc=c['Lambda_enc'], P_deep=c['P_deep'],
                             uniform=uni, k_ww=(c['Lambda_enc'] - c['P_deep']) / uni,
                             src='W4'))
    for c in (extra or []):
        rows.append(dict(key=KEY, L=c['L'], H=c['H'], S1=c['S1'], err=c['err'],
                         Lambda_enc=c['Lambda_enc'], P_deep=c['P_deep'],
                         uniform=c['uniform'], k_ww=c['k_ww'], src='R2c'))
    rows.sort(key=lambda r: (r['key'], r['L'], r['H']))
    log('%-14s %-4s %4s %5s %10s %10s %11s %8s' %
        ('alpha', 'src', 'L', 'H', 'sum h|a|', 'Lambda_enc', '2pi S1 err', 'kappa_ww'))
    for r in rows:
        log('%-14s %-4s %4d %5d %10.2f %10.6f %11.6f %8.4f'
            % (r['key'], r['src'], r['L'], r['H'], r['S1'], r['Lambda_enc'],
               r['uniform'], r['k_ww']))
    ks = [r['k_ww'] for r in rows]
    log('  %d certificates: kappa_ww in [%.4f, %.4f], median %.4f -- the search is '
        'charged %.1f to %.1f times what the certificate pays'
        % (len(ks), min(ks), max(ks), sorted(ks)[len(ks) // 2],
           1 / max(ks), 1 / min(ks)))
    return rows


# ---------------------------------------------------------------------------
# the self-checks
# ---------------------------------------------------------------------------

def selfchecks(log=print, samples=40):
    al = Alpha(COEFFS, POLY)
    hm = h_min(al)
    ok, det = [], []

    def chk(name, cond, msg):
        ok.append(bool(cond))
        det.append(dict(n=len(ok), name=name, ok=bool(cond), detail=msg))
        log('  %2d %-4s %s -- %s' % (len(ok), 'ok' if cond else 'FAIL', name, msg))

    # 1 -----------------------------------------------------------------
    pub = next(r for r in json.load(open('m4_frontier.json')) if r['poly'] == POLY)
    c1 = (abs(float(al.alpha) - (1 + math.sqrt(2))) < 1e-15
          and abs(float(al.rho) - (math.sqrt(2) - 1)) < 1e-15
          and abs(hm - pub['h_min']) < 1e-15
          and abs((LOG2 - hm) - pub['budget']) < 1e-15)
    chk('alpha data', c1, 'alpha=%.15f rho=%.15f h_min=%.15f budget=%.15f, all four '
        'equal to m4_frontier.json to 1e-15' % (al.alpha, al.rho, hm, LOG2 - hm))

    # 2 -----------------------------------------------------------------
    bad = [L for L in range(10, 27) if best_split(al, L) != best_window(al, L)]
    chk('two window choosers agree', not bad,
        'best_split == m4_fourier.best_window at every L in 10..26 (balanced (L/2,L/2) '
        'throughout, rho = 1/alpha here)')

    # 3 -----------------------------------------------------------------
    import mpmath as mp
    mp.mp.dps = 40
    a_, rho_ = mp.mpf(1) + mp.sqrt(2), mp.sqrt(2) - 1
    Ca = mp.fsum([abs(mp.mpc(z) - 1) for z in al.conj])
    worst3 = 0.0
    for L in (16, 18, 20, 22, 24, 26):
        N, M, e = best_split(al, L)
        ex = a_ ** (-M) + Ca * rho_ ** (N + 1) / (1 - rho_)
        worst3 = max(worst3, abs(float(ex) - e) / e)
    chk('window_eps in mpmath', worst3 < 1e-14,
        'eps = alpha^-M + C_alpha rho^(N+1)/(1-rho) recomputed at 40 digits for '
        'L = 16..26: worst relative deviation %.2e' % worst3)

    # 4, 5, 6, 7 --------------------------------------------------------
    Ns, Ms, _ = best_split(al, 14)
    Ws = Window(al, Ns, Ms).set_modes(list(range(1, 9)))
    rng = np.random.default_rng(7)
    xs = rng.normal(scale=0.2, size=16)
    asr = xs[:8] + 1j * xs[8:]
    e0 = enclose(Ws, asr)
    e1 = enclose_blk(Ws, asr)
    e2, st = enclose_blk2(Ws, asr)
    chk('enclose_blk2 == m4_fourier.enclose', np.array_equal(e2, e0),
        'bitwise on 2^%d words, 8 modes' % (Ws.L + 1))
    chk('enclose_blk2 == m8_w4.enclose_blk', np.array_equal(e2, e1),
        'bitwise: the moments are accumulated beside the array, not from it')
    chk('cw_ub == m4_fourier.spec_ub', cw_ub(Ws, e2) == spec_ub(Ws, e2),
        'bitwise, same window (WP1 slices against the legacy gathers)')
    chk('certify == cw_ub(enclose_blk2)', certify(Ws, asr) == cw_ub(Ws, e2),
        'the published certifier and this file\'s route are the same number')

    # 8 -----------------------------------------------------------------
    d = delta_bound(Ws, asr)
    S1 = float(np.sum(Ws.modes * np.abs(asr)))
    G = Ws.grid
    c8 = (abs(d - 2 * math.pi * S1 * Ws.eps) < 1e-18
          and abs(Ws.eps - (Ws.err + (0.0 if G is None else 0.5 / G))) < 1e-18)
    chk('delta_bound identity', c8,
        'delta == 2 pi (sum h|a_h|) eps and eps == err + 1/(2G) to the last bit '
        '(grid %s)' % ('off' if G is None else G))

    # 9, 10, 11, 12 -----------------------------------------------------
    lam = cw_ub(Ws, e2)
    P, _ = Ws.pressure(asr, want_grad=False)
    ub = Ws.pressure_ub(asr)
    chk('the enclosure encloses', lam >= P - 1e-12 and ub + d >= P - 1e-12,
        'Lambda_enc = %.9f and Lambda_cw = %.9f both dominate P = %.9f'
        % (lam, ub + d, P))
    chk('word-wise beats uniform', lam <= ub + d,
        'Lambda_enc %.9f <= Lambda_cw %.9f: |g\'| <= 2 pi sum h|a_h| pointwise and '
        'Collatz-Wielandt is monotone' % (lam, ub + d))
    chk('sup |g\'| <= 2 pi sum h|a_h|', st['sup_gp'] <= 2 * math.pi * S1 * (1 + 1e-12),
        'measured sup %.4f against the uniform bound %.4f: kappa_sup = %.4f'
        % (st['sup_gp'], 2 * math.pi * S1, st['sup_gp'] / (2 * math.pi * S1)))
    P2, gr = Ws.pressure(asr, want_grad=True)
    mu = Ws._mu
    _, st2 = enclose_blk2(Ws, asr, mu=mu)
    chk('mean |g\'| <= sup |g\'|', st2['mean_gp'] <= st['sup_gp'],
        'Gibbs mean %.4f against sup %.4f: kappa_mean = %.4f, so the surrogate '
        'over-charges by %.1f x at this multiplier'
        % (st2['mean_gp'], st['sup_gp'], st2['mean_gp'] / (2 * math.pi * S1),
           2 * math.pi * S1 / st2['mean_gp']))

    # 13 ----------------------------------------------------------------
    chk('the Gibbs vector is a measure', abs(float(mu.sum()) - 1) < 1e-12
        and float(mu.min()) >= 0,
        'sum mu = %.15f, min mu = %.3e over 2^%d words'
        % (mu.sum(), mu.min(), Ws.L + 1))

    # 14 ----------------------------------------------------------------
    Nd, Md, ed = best_split(al, 22)
    Wd = Window(al, Nd, Md)
    rng = np.random.default_rng(11)
    worst, badn = 0.0, 0
    for _ in range(samples):
        word = int(rng.integers(0, 1 << (Wd.L + 1)))
        fut = [(word >> (Nd + j)) & 1 for j in range(1, Md + 1)] + \
              [int(rng.integers(0, 2)) for _ in range(150)]
        pas = [(word >> (Nd - m)) & 1 for m in range(0, Nd + 1)] + \
              [int(rng.integers(0, 2)) for _ in range(150)]
        t = (a_ - 1) * mp.fsum([fut[j - 1] * a_ ** (-j)
                                for j in range(1, len(fut) + 1)])
        S = mp.fsum([pas[m] * mp.re(mp.fsum([(mp.mpc(z) - 1) * mp.mpc(z) ** m
                                             for z in al.conj]))
                     for m in range(len(pas))])
        er = abs(float(t - S) - Wd.F[word])
        worst = max(worst, er)
        badn += er > Wd.err
    chk('M4 Prop. 3 at the deep window', badn == 0,
        '%d random bi-infinite completions at (%d,%d): |F - F~| <= %.2e = err always '
        '(worst %.2e)' % (samples, Nd, Md, Wd.err, worst))

    # 15 ----------------------------------------------------------------
    rng = np.random.default_rng(13)
    worst15 = 0.0
    for _ in range(2000):
        u = int(rng.integers(0, 1 << (Wd.L + 1)))
        s = sum(Wd.wt[i] for i in range(Wd.L + 1) if (u >> i) & 1)
        worst15 = max(worst15, abs(s - Wd.F[u]))
    chk('F is the subset sum of wt', worst15 < 1e-12,
        'F[u] = sum of wt[i] over the set bits of u, 2000 random words, worst %.2e'
        % worst15)
    del Wd

    # 16 ----------------------------------------------------------------
    Nm, Mm, em = best_split(al, 18)
    Wm = Window(al, Nm, Mm).set_modes(list(range(1, 17)))
    Wm.fft_min_modes = 10 ** 9          # both sides of the sandwich on the same g:
    Wm._G = None                        # no WP3 grid, so no 1/(2G) between them
    xs = rng.normal(scale=0.15, size=32)
    am = xs[:16] + 1j * xs[16:]
    Pm, _ = Wm.pressure(am, want_grad=True)
    lwm, stm = enclose_blk2(Wm, am, mu=Wm._mu)
    lm = cw_ub(Wm, lwm)
    predm = Pm + stm['eps'] * stm['mean_gp'] + 0.5 * stm['eps'] ** 2 * stm['M2']
    err16 = abs(lm - predm)
    tol16 = 10 * stm['eps'] ** 2 * stm['M2'] + 1e-9
    chk('the first-order predictor', err16 <= tol16,
        'Lambda_enc = %.9f against P + eps<|g\'|>_mu + eps^2 M2/2 = %.9f, difference '
        '%.2e inside the second-order allowance %.2e' % (lm, predm, err16, tol16))
    # 17 ----------------------------------------------------------------
    lo17 = Pm + stm['eps'] * stm['mean_gp'] + 0.5 * stm['eps'] ** 2 * stm['M2']
    hi17 = Pm + stm['eps'] * stm['sup_gp'] + 0.5 * stm['eps'] ** 2 * stm['M2']
    chk('the enclosure sandwich', lo17 <= lm + 1e-12 and lm <= hi17 + 1e-12,
        'Theorem 1: P + eps<|g\'|>_mu + eps^2M2/2 = %.9f <= Lambda_enc = %.9f <= '
        'P + eps sup|g\'| + eps^2M2/2 = %.9f, both halves from the finite-state '
        'variational principle' % (lo17, lm, hi17))
    del Wm

    # 18 ----------------------------------------------------------------
    worst17 = max(2 * math.pi * H * best_split(al, L)[2]
                  for H in HS for L in LDEEP)
    chk('the trust rule holds at every planned cell', worst17 < 1.0,
        'max 2 pi H eps over H <= %d and L in %s is %.4f < 1 (R2b\'s sharpened form; '
        'R2a\'s H eps <= 0.9 form gives %.4f)'
        % (max(HS), list(LDEEP), worst17, worst17 / (2 * math.pi)))

    log('  %d/%d self-checks pass' % (sum(ok), len(ok)))
    return det, all(ok)


# ---------------------------------------------------------------------------
# the run
# ---------------------------------------------------------------------------

def run(log=print):
    al = Alpha(COEFFS, POLY)
    hm = h_min(al)
    Hs = tuple(int(v) for v in opt('--hs', ','.join(str(h) for h in HS)).split(','))
    ks = tuple(float(v) for v in
               opt('--kappas', ','.join(str(k) for k in KAPPAS)).split(','))
    Ls = int(opt('--lsearch', LSEARCH))
    cap = float(opt('--cap', CAP))
    mx = int(opt('--maxiter', MAXITER))
    Ld = int(opt('--deep', LDEEP[0]))
    eref = best_split(al, LREF)[2]
    Ns, Ms, es = best_split(al, Ls)
    d = load()
    log('# R2c  %s  alpha=%.9f  h_min=%.6f  budget=%.4f  log2=%.6f'
        % (KEY, al.alpha, hm, LOG2 - hm, LOG2))
    log('  search (%d,%d) L=%d eps=%.3e;  penalty rate kappa * eps(L=%d) = kappa * '
        '%.3e;  deep L=%d' % (Ns, Ms, Ls, es, LREF, eref, Ld))
    lad = [r for r in d.get('ladder', []) if r['H'] not in Hs or r['kappa'] not in ks]
    cert = list(d.get('cert', []))
    for k in ks:
        log('# ladder at kappa = %g' % k)
        rows = ladder(al, k, Hs=Hs, Ls=Ls, eps_ref=eref, cap=cap, maxiter=mx, log=log)
        lad += rows
        d['ladder'] = lad
        d['meta'] = dict(key=KEY, poly=POLY, coeffs=COEFFS, alpha=float(al.alpha),
                         rho=float(al.rho), h_min=hm, log2=LOG2, budget=LOG2 - hm,
                         Ls=Ls, N=Ns, M=Ms, eps_search=es, LREF=LREF, eps_ref=eref,
                         kappas=list(ks), Hs=list(Hs), cap=cap, maxiter=mx)
        save(d)
        log('# certificates at L = %d' % Ld)
        cert = [c for c in cert
                if not (c['L'] == Ld and c['kappa'] == k and c['H'] in Hs)]
        cert += certify_rows(al, rows, Ld, hm=hm, log=log)
        d['cert'] = cert
        save(d)
    log('# wrote %s' % save(d))
    return d


def deep(log=print):
    """The L = 24 certificates for the rows worth the four-fold cost.

    Selection is explicit and logged: for every H the kappa that won at L = 22, plus
    W4's own protocol (kappa = 1) at the best H, so that the comparison the note makes
    is between two certificates at the same window and not across windows.
    """
    al = Alpha(COEFFS, POLY)
    hm = h_min(al)
    Ld = int(opt('--deep', LDEEP[1]))
    d = load()
    lad = d.get('ladder', [])
    prev = [c for c in d.get('cert', []) if c['L'] == LDEEP[0]]
    if not prev:
        log('nothing to select from: run the L=%d pass first' % LDEEP[0])
        return d
    if '--all' in sys.argv:
        sel = [(r['kappa'], r['H']) for r in lad
               if r['H'] >= int(opt('--hmin', 1))]
        log('# certifying all %d rows at L = %d' % (len(sel), Ld))
        rows = [next(r for r in lad if r['kappa'] == k and r['H'] == H)
                for k, H in sel]
        cert = [c for c in d.get('cert', [])
                if not (c['L'] == Ld and (c['kappa'], c['H']) in sel)]
        cert += certify_rows(al, rows, Ld, hm=hm, log=log)
        d['cert'] = cert
        log('# wrote %s' % save(d))
        return d
    best, sel = {}, []
    for c in prev:
        b = best.get(c['H'])
        if b is None or c['Lambda_enc'] < b['Lambda_enc']:
            best[c['H']] = c
    bh = min(best.values(), key=lambda c: c['Lambda_enc'])['H']
    for H in sorted(best):
        sel.append((best[H]['kappa'], H))
    if (1.0, bh) not in sel:
        sel.append((1.0, bh))
    log('# selected for L = %d: %s' % (Ld, ' '.join('k=%g/H=%d' % s for s in sel)))
    rows = [next(r for r in lad if r['kappa'] == k and r['H'] == H) for k, H in sel]
    cert = [c for c in d.get('cert', [])
            if not (c['L'] == Ld and (c['kappa'], c['H']) in sel)]
    cert += certify_rows(al, rows, Ld, hm=hm, log=log)
    d['cert'] = cert
    log('# wrote %s' % save(d))
    return d


def one(log=print):
    """`r2c_deep.py one KAPPA H L` -- one cell, appended to the JSON."""
    i = sys.argv.index('one')
    k, H, L = float(sys.argv[i + 1]), int(sys.argv[i + 2]), int(sys.argv[i + 3])
    al = Alpha(COEFFS, POLY)
    d = load()
    row = next((r for r in d.get('ladder', []) if r['kappa'] == k and r['H'] == H),
               None)
    if row is None:
        eref = best_split(al, LREF)[2]
        row = ladder(al, k, Hs=(H,), eps_ref=eref, log=log)[0]
        d.setdefault('ladder', []).append(row)
    cert = [c for c in d.get('cert', [])
            if not (c['L'] == L and c['kappa'] == k and c['H'] == H)]
    cert += certify_rows(al, [row], L, log=log)
    d['cert'] = cert
    log('# wrote %s' % save(d))
    return d


def repro(log=print):
    """M4 sec 7's own pipeline for 1+sqrt2, through W4's `reproduce` verbatim."""
    t0 = time.time()
    r = m8_w4.reproduce(KEY, log)
    d = load()
    d['repro'] = r
    pub = next(x for x in json.load(open('m4_frontier.json')) if x['poly'] == POLY)
    worst = max(abs(v['d']) for v in r['cert'].values()) if r['cert'] else float('nan')
    dP = max(abs(v['dP']) for v in r['ladder'].values())
    d['repro']['worst_cert'] = worst
    d['repro']['worst_P'] = dP
    d['repro']['published'] = {t: c['Lambda_ub'] for t, c in pub['cert'].items()}
    log('  worst certificate deviation %+.1e, worst ladder deviation %+.1e, %.0fs'
        % (worst, dP, time.time() - t0))
    log('# wrote %s' % save(d))
    return d


# ---------------------------------------------------------------------------
# the tables
# ---------------------------------------------------------------------------

def table(log=print):
    d = load()
    cert = d.get('cert', [])
    lad = d.get('ladder', [])
    if not cert:
        log('nothing recorded yet')
        return
    hm = d['meta']['h_min']
    log('# the ladder: the surrogate at four penalty rates')
    log('%-8s %5s %10s %11s %10s %8s' % ('kappa', 'H', 'P~', 'sum h|a|', 'max|x|',
                                         'secs'))
    for r in sorted(lad, key=lambda r: (-r['kappa'], r['H'])):
        log('%-8g %5d %10.6f %11.2f %10.3f %8.0f'
            % (r['kappa'], r['H'], r['P'], r['S1'], r['xmax'], r['secs']))
    for L in sorted({c['L'] for c in cert}):
        log('')
        log('# certificates at L = %d  (h_min = %.6f, log 2 = %.6f)' % (L, hm, LOG2))
        log('%-8s %5s %10s %10s %10s %9s %8s %8s %8s' %
            ('kappa', 'H', 'Lam_enc', 'Lam_cw', 'P_deep', 'log2-Lam', 'k_ww',
             'k_sup', 'k_mean'))
        for c in sorted((c for c in cert if c['L'] == L),
                        key=lambda c: (-c['kappa'], c['H'])):
            log('%-8g %5d %10.6f %10.6f %10.6f %+9.5f %8.4f %8.4f %8.4f'
                % (c['kappa'], c['H'], c['Lambda_enc'], c['Lambda_cw'], c['P_deep'],
                   LOG2 - c['Lambda_enc'], c['k_ww'], c['k_sup'], c['k_mean']))
        b = min((c for c in cert if c['L'] == L), key=lambda c: c['Lambda_enc'])
        log('  best: kappa=%g H=%d  Lambda_enc=%.6f  = log2 - %.5f = h_min + %.5f'
            % (b['kappa'], b['H'], b['Lambda_enc'], LOG2 - b['Lambda_enc'],
               b['Lambda_enc'] - hm))
    log('')
    log('# the predictor: Lambda_enc against P + eps<|g\'|>_mu + eps^2 M2/2')
    log('%-8s %5s %4s %12s %12s %10s' % ('kappa', 'H', 'L', 'Lam_enc', 'pred',
                                         'rel.err'))
    for c in sorted(cert, key=lambda c: (c['L'], -c['kappa'], c['H'])):
        g = c['Lambda_enc'] - c['P_deep']
        log('%-8g %5d %4d %12.6f %12.6f %10.2e'
            % (c['kappa'], c['H'], c['L'], c['Lambda_enc'], c['pred'],
               abs(c['Lambda_enc'] - c['pred']) / max(g, 1e-15)))


# ---------------------------------------------------------------------------
# the two-sided bracket, the mode support, and the price
# ---------------------------------------------------------------------------

def _lower_bounds():
    """The best certified lower bounds on `E_H(1+sqrt2)` the folder holds.

    R1b's interior-of-hull certificate on the M7 pool (`r1b_certify.json`) and R2d's
    on the union pool (`r2d_hull.json`); the certified bound is the larger of the two
    at each degree, and both are theorems, so taking the max is legitimate.
    """
    out = {}
    try:
        d = json.load(open('r1b_certify.json'))
        for k, r in d.items():
            if not k.startswith('1+sqrt2:'):
                continue
            H = int(k.split(':')[1])
            v = max((c[1]['h_lower'] for c in r['curve'] if c[1].get('delta', 0) > 0),
                    default=None)
            if v is not None:
                out[H] = max(out.get(H, -1e9), v), 'R1b'
    except (IOError, ValueError, KeyError):
        pass
    try:
        d = json.load(open('r2d_hull.json'))
        for r in d.get('ent', []):
            if r.get('name') != '1+sqrt2' or r.get('pool') != 'union':
                continue
            v, H = r['best']['h_lower'], r['H']
            if H not in out or v > out[H][0]:
                out[H] = (v, 'R2d union')
    except (IOError, ValueError, KeyError):
        pass
    return out


def bracket(log=print):
    """The first two-sided certified bracket on `E_H` at `1+sqrt2`."""
    d = load()
    hm = d['meta']['h_min']
    lo = _lower_bounds()
    up = {}
    for c in d.get('cert', []):
        b = up.get(c['H'])
        if b is None or c['Lambda_enc'] < b['Lambda_enc']:
            up[c['H']] = c
    log('# E_H(1+sqrt2), two-sided and certified   (h_min = %.6f, log 2 = %.6f)'
        % (hm, LOG2))
    log('%5s %14s %-11s %14s %-11s %11s %10s' %
        ('H', 'lower', 'source', 'upper', 'at', 'width', 'to h_min'))
    for H in sorted(set(lo) | set(up)):
        l = lo.get(H)
        u = up.get(H)
        log('%5d %14s %-11s %14s %-11s %11s %10s'
            % (H,
               '%.9f' % l[0] if l else '--', l[1] if l else '',
               '%.9f' % u['Lambda_enc'] if u else '--',
               ('k=%g L=%d' % (u['kappa'], u['L'])) if u else '',
               '%.3e' % (u['Lambda_enc'] - l[0]) if (l and u) else '--',
               '%+.5f' % (hm - u['Lambda_enc']) if u else '--'))
    log('  M4 m4_frontier.json 24/16 for comparison: 0.689990 at H = 16')
    return dict(lower={str(k): v for k, v in lo.items()},
                upper={str(k): (v['Lambda_enc'], v['kappa'], v['L'])
                       for k, v in up.items()})


def modes(log=print):
    """Gate G-A1 of `plan-BB61-1+sqrt2.html`: does the optimum use modes above 16?"""
    d = load()
    log('# the mode support of the optimum, against M4\'s H = 16 saturation')
    log('%-8s %5s %9s %9s %10s %10s' %
        ('kappa', 'H', 'max h', 'h(99%)', 'sum h|a|', 'max|a_h|'))
    out = []
    for r in sorted(d.get('ladder', []), key=lambda r: (-r['kappa'], r['H'])):
        H = r['H']
        x = np.array(r['x'])
        m = np.abs(x[:H] + 1j * x[H:])
        if m.max() <= 0:
            continue
        hi = int(max(h for h in range(1, H + 1) if m[h - 1] > 1e-3 * m.max()))
        w = np.arange(1, H + 1) * m
        h99 = int(np.searchsorted(np.cumsum(w) / w.sum(), 0.99) + 1)
        out.append(dict(kappa=r['kappa'], H=H, hmax=hi, h99=h99, S1=r['S1'],
                        amax=float(m.max())))
        log('%-8g %5d %9d %9d %10.2f %10.4f'
            % (r['kappa'], H, hi, h99, r['S1'], m.max()))
    log('  M4 sec 8: the ladder saturates at H = 16 with sum h|a_h| = 0.73')
    return out


def price(log=print):
    """The two axes of the price, both measured, and the exponent they share."""
    al = Alpha(COEFFS, POLY)
    d = load()
    hm = d['meta']['h_min']
    up = {}
    for c in d.get('cert', []):
        b = up.get((c['H'], c['L']))
        if b is None or c['Lambda_enc'] < b['Lambda_enc']:
            up[(c['H'], c['L'])] = c
    log('# the degree axis: the best certified Lambda_enc per doubling')
    for L in sorted({k[1] for k in up}):
        row = sorted((k[0], up[k]) for k in up if k[1] == L)
        log('  L=%d: ' % L + '  '.join('H=%d:%.6f' % (H, c['Lambda_enc'])
                                       for H, c in row))
        gains = [(row[i][1]['Lambda_enc'] - row[i + 1][1]['Lambda_enc'])
                 for i in range(len(row) - 1)]
        if gains:
            g = max(gains)
            log('    best gain per doubling %.2e; %.0f doublings from %.6f to '
                'h_min = %.6f' % (g, (row[-1][1]['Lambda_enc'] - hm) / g,
                                  row[-1][1]['Lambda_enc'], hm))
    log('# the window axis: eps ~ alpha^(-L/2), so 2^L ~ eps^(-2 log2/log alpha)')
    for k, c in [('1+sqrt2', COEFFS), ('(3+sqrt5)/2', [1, -3, 1]),
                 ('(3+sqrt13)/2', [1, -3, -1])]:
        a2 = Alpha(c, POLY if k == '1+sqrt2' else 'X')
        e = 2 * math.log(2) / math.log(float(a2.alpha))
        log('  %-14s alpha=%.6f  exponent 2log2/log alpha = %.4f' % (k, a2.alpha, e))
    log('# and what it costs to match the middle units at the same eps')
    for L in (20, 22, 24, 26):
        for k, c in (('(3+sqrt5)/2', [1, -3, 1]), ('(3+sqrt13)/2', [1, -3, -1])):
            t = best_split(Alpha(c, 'X'), L)[2]
            Lm = next(x for x in range(10, 60) if best_split(al, x)[2] <= t)
            log('  %-14s L=%2d eps=%.3e  ->  1+sqrt2 needs L=%d, %dx the states'
                % (k, L, t, Lm, 2 ** (Lm - L)))


def _sci(v):
    """`v` as the note writes it: \\(m\\cdot10^{-n}\\)."""
    e = int(math.floor(math.log10(abs(v)))) if v else 0
    return '\\(%.2f\\cdot10^{%d}\\)' % (v / 10.0 ** e, e)


def html(log=print):
    """The note's tables, as HTML rows -- so the note is transcribed by machine."""
    d = load()
    hm = d['meta']['h_min']
    cert = d.get('cert', [])
    lad = d.get('ladder', [])
    ks = sorted({r['kappa'] for r in lad}, reverse=True)
    Hs = sorted({r['H'] for r in lad})

    log('<!-- LADDER: P~ and sum h|a_h| at each penalty rate -->')
    log('<tr><th>\\(H\\)</th>' + ''.join(
        '<th>\\(\\kappa=%s\\)</th>' % ('0' if k == 0 else
                                            ('1' if k == 1 else '1/%g' % (1 / k)))
        for k in ks) + '</tr>')
    for H in Hs:
        cells = []
        for k in ks:
            r = next((r for r in lad if r['kappa'] == k and r['H'] == H), None)
            cells.append('<td>%s</td>' % ('&mdash;' if r is None else
                                          '%.6f <span class="small">(%.1f)</span>'
                                          % (r['P'], r['S1'])))
        log('<tr><td>\\(%d\\)</td>%s</tr>' % (H, ''.join(cells)))

    for L in sorted({c['L'] for c in cert}):
        log('<!-- CERTIFICATES at L = %d -->' % L)
        log('<tr><th>\\(H\\)</th>' + ''.join(
            '<th>\\(\\kappa=%s\\)</th>' % ('0' if k == 0 else
                                                ('1' if k == 1 else '1/%g' % (1 / k)))
            for k in ks) + '<th>best</th></tr>')
        for H in Hs:
            row = [c for c in cert if c['L'] == L and c['H'] == H]
            if not row:
                continue
            cells = []
            for k in ks:
                c = next((c for c in row if c['kappa'] == k), None)
                cells.append('<td>%s</td>' % ('&mdash;' if c is None
                                              else '%.6f' % c['Lambda_enc']))
            b = min(row, key=lambda c: c['Lambda_enc'])
            log('<tr><td>\\(%d\\)</td>%s<td><b>\\(%.6f\\)</b></td></tr>'
                % (H, ''.join(cells), b['Lambda_enc']))

    log('<!-- BRACKET -->')
    lo = _lower_bounds()
    up = {}
    for c in cert:
        b = up.get(c['H'])
        if b is None or c['Lambda_enc'] < b['Lambda_enc']:
            up[c['H']] = c
    for H in sorted(set(lo) | set(up)):
        l, u = lo.get(H), up.get(H)
        log('<tr><td>\\(%d\\)</td><td>%s</td><td>%s</td><td>%s</td><td>%s</td></tr>'
            % (H,
               '\\(%.9f\\)' % l[0] if l else '&mdash;',
               '\\(%.6f\\)' % u['Lambda_enc'] if u else '&mdash;',
               _sci(u['Lambda_enc'] - l[0]) if (l and u) else '&mdash;',
               '\\(%+.5f\\)' % (hm - u['Lambda_enc']) if u else '&mdash;'))

    log('<!-- KAPPA_WW, this run -->')
    for c in sorted(cert, key=lambda c: (c['L'], -c['kappa'], c['H'])):
        log('<tr><td>\\(%g\\)</td><td>\\(%d\\)</td><td>\\(%d\\)</td>'
            '<td>\\(%.4f\\)</td><td>\\(%.4f\\)</td><td>\\(%.4f\\)</td></tr>'
            % (c['kappa'], c['H'], c['L'], c['k_sup'], c['k_mean'], c['k_ww']))


def main():
    global OUT
    os.chdir(HERE)
    OUT = opt('--out', OUT)
    cmd = sys.argv[1] if len(sys.argv) > 1 else 'checks'
    if cmd == 'checks':
        det, ok = selfchecks(samples=int(opt('--samples', 40)))
        d = load()
        d['checks'] = det
        save(d)
        sys.exit(0 if ok else 1)
    elif cmd == 'calib':
        d = load()
        mine = [c for c in d.get('cert', [])]
        rows = calib(extra=mine)
        d['calib'] = rows
        save(d)
    elif cmd == 'run':
        run()
    elif cmd == 'deep':
        deep()
    elif cmd == 'one':
        one()
    elif cmd == 'repro':
        repro()
    elif cmd == 'table':
        table()
    elif cmd == 'bracket':
        d = load()
        d['bracket'] = bracket()
        save(d)
    elif cmd == 'modes':
        d = load()
        d['modes'] = modes()
        save(d)
    elif cmd == 'price':
        price()
    elif cmd == 'html':
        html()
    else:
        print(__doc__)


if __name__ == '__main__':
    main()
