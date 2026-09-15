#!/usr/bin/env python3
# (C) 2026 Ralf Stephan, in collaboration with Claude Code
# CC0 1.0 Universal (public domain dedication).
"""W5 of plan_BB61_improve_m3_entropy.html: the lower-bound side of the W4 rows.

W4 certified `(3+sqrt5)/2` at `H = 256` and `(3+sqrt13)/2` at `H = 1024`.  That is one
half of a threshold.  W5 is the other half: M7 Thm 5 gives

    E_H(alpha) >= max { sum_j lam_j h(nu_j) : lam in Delta, sum_j lam_j Phi_h(nu_j) = 0 },

a linear program over explicit invariant measures, and **a value above `h_min(alpha)`
proves that no trigonometric certificate of degree <= H exists at that alpha**.  Since
`E_H` is non-increasing in `H`, one such bound at the largest non-firing rung settles
every smaller degree at once.  So the two rows that matter are

    (3+sqrt5)/2   at H = 128   (W4 fires at 256, not at 128)
    (3+sqrt13)/2  at H = 512   (W4 fires at 1024, not at 512)

and if both clear, the certificate degree is pinned to `(128, 256]` and `(512, 1024]`.

Why this needs WP9 and not `lp_lower`
-------------------------------------
M7 sec 4 ran the LP over a 16H-vector pool of Gibbs measures at `a* +- t e_h` and
`a* +- i t e_h`, and five rows came back "pool too small": 0 was not in the convex hull
of the pool's `Phi`-vectors, which is a statement about the pool and not about `alpha`.
`(3+sqrt5)/2` at `H = 64` is one of them.  `cutting_plane_lower` steers instead of
enlarging -- Farkas separator while the hull misses 0, LP dual pricing once it does --
so the pool is grown in the direction the LP says it is missing.

The seed pool is M7's own construction at a single `t`, `1 + 4H` columns, which is
already twice the `2H + 1` that a hull containing 0 in `R^2H` generically needs; WP9
supplies the rest.  Every column is a genuine memory-`L` Markov measure whose `Phi_h`
come from the two exact ladders of `BlockChain.phis` -- computed with the true `F`, not
with the window truncation -- so the bound is rigorous, which is the point.

What is reported, and what is a theorem
---------------------------------------
`lb`        the LP value.  A rigorous lower bound for `E_H` **provided** the optimal
            mixture is flat: `lp_bound` carries an `l^1` slack and `resid` measures it,
            and by M7 Thm 5 a residual `eps` costs at most `eps * ||a||_1`.  Both are
            recorded, and `lb_safe = lb - resid * ||a||_1` is what the verdict uses.
`ub_enc`    W4's rigorous upper bound at the same `(alpha, H)`, from `m8_w4.json`.
            `lb <= ub_enc` must hold, and G-6 checks it: a lower bound above a valid
            upper bound would mean one of the two is wrong.
`verdict`   `NO CERTIFICATE OF DEGREE <= H` when `lb_safe > h_min`; `certificate exists`
            when W4 fired here; `inconclusive` otherwise.

Sub-commands
    m8_w5.py run [key ...]   the LP rows
    m8_w5.py gates           G-6 (consistency) and G-7 (M7 sec 4 revisited)

Options
    --H h,h,..  --L 14  --t 0.04,0.5  --rounds 150  --cap 60  --out FILE

`--L` is the memory of the Markov family *and* the depth of the window the pool is
centred on, and it is the single most important knob here.  M7 sec 4 used 12; at
`(3+sqrt5)/2, H = 32` that gives `lb = 0.562673` against `E_32 ~ 0.5937`, while `L = 14`
gives `0.591506` -- a gap of 2e-03 instead of 3e-02.  The reason is that
`BlockChain.phis` uses the **true** `F`, so however flat the centre is in the window's
own `Phi` (1e-08, by the first-order condition), its true flatness is only as good as
the window: 5.6e-03 at `L = 12` against 1.0e-03 at `L = 14`.  Cost is `O(2^L H)` per
column, so this is the quality/price dial.
"""
import sys
import json
import time
import math

import numpy as np

sys.path.insert(0, '/home/ralf/math/lean-code/BB61')
from m0_engine import Alpha
from m3_entropy import Window, best_split, h_min, minimize_pressure
from m7_price import (BlockChain, gibbs_columns, cutting_plane_lower, lp_bound,
                      real_pairing)

CASES = {
    '(3+sqrt5)/2': ([1, -3, 1], 'X^2-3X+1'),
    '(3+sqrt13)/2': ([1, -3, -1], 'X^2-3X-1'),
}
W4_FILES = 'm8_w4.json,m8_w4_ext.json'


def opt(name, default):
    return sys.argv[sys.argv.index(name) + 1] if name in sys.argv else default


def w4_rows(files=W4_FILES):
    """{key: {H: (x, Lambda_enc at the deepest L, h_min, fires)}} from W4's output."""
    out = {}
    for f in files.split(','):
        try:
            d = json.load(open(f.strip()))
        except (IOError, ValueError):
            continue
        for r in d['runs']:
            tab = out.setdefault(r['key'], {})
            best = {}
            for c in r['cert'].values():                 # deepest window per H wins
                if c['H'] not in best or c['L'] > best[c['H']]['L']:
                    best[c['H']] = c
            for v in r['ladder']:
                c = best.get(v['H'])
                tab[v['H']] = dict(x=v['x'], h_min=r['h_min'],
                                   ub_enc=(c['Lambda_enc'] if c else None),
                                   ub_L=(c['L'] if c else None),
                                   fires=bool(c['fires']) if c else False,
                                   P_search=v['P'], S1=v['S1'])
    return out


def pool_vectors(H, xstar, ts):
    """M7 sec 4's seed pool: `a*` and `a* +- t e_h`, `a* +- i t e_h`.  `1 + 4H|ts|`."""
    out = [np.asarray(xstar, dtype=float).copy()]
    for h in range(1, H + 1):
        for t in ts:
            for sgn in (1.0, -1.0):
                for im in (0, 1):
                    x = np.asarray(xstar, dtype=float).copy()
                    x[(h - 1) + im * H] += sgn * t
                    out.append(x)
    return out


def run_row(al, key, H, L, ts, rounds, cap, w4, log):
    hm = h_min(al)
    ref = (w4.get(key) or {}).get(H)
    N, M, e = best_split(al, L)
    W = Window(al, N, M).set_modes(list(range(1, H + 1)))
    bc = BlockChain(al, L, hmax=H)

    # The pool has to be centred where the LP can reach 0: at the minimiser of the
    # pressure *of this window*, whose first-order condition is exactly
    # `Phi_h(mu_{a*}) = 0` at the window's own truncation -- so the centre column is
    # already flat to the size of that truncation and the LP only has to mop up.
    # W4's multiplier is the wrong centre and it is not a close call: it minimises the
    # certifiable surrogate at L = 24, so at L = 12 its Gibbs measure is nowhere near
    # flat, and a 513-column pool then sits at an l^1 residual of 3.08 with the Farkas
    # separator frozen.  W4's multiplier is still the right *warm start* for the solve.
    t0 = time.time()
    x0 = np.array(ref['x']) if ref else None
    P0, x, flat, _ = minimize_pressure(W, x0=x0, cap=cap)
    log('  H=%-4d pool centre: P(L=%d) = %.9f, max|Phi_h| = %.2e  (%.0fs)'
        % (H, L, P0, flat, time.time() - t0))

    seeds = pool_vectors(H, x, ts)
    t0 = time.time()
    ent, phi = gibbs_columns(W, bc, H, seeds)
    tseed = time.time() - t0
    log('  H=%-4d seed pool %d/%d columns in %.0fs (chain memory %d, window (%d,%d))'
        % (H, len(ent), len(seeds), tseed, L, N, M))

    t0 = time.time()
    r = cutting_plane_lower(W, bc, H, xstar=x, ent=ent, phi=phi, rounds=rounds,
                            cap=cap, verbose=True)
    secs = time.time() - t0

    # the honest flatness of the mixture the LP actually returned, and M7 Thm 5's
    # degradation term for it
    val, lam, y, resid, atoms = lp_bound(r['ent'], r['phi'], H)
    a1 = float(np.sum(np.abs(x[:H] + 1j * x[H:])))
    corr = float(resid) * a1 if resid is not None else None
    lb = r['lb']
    lb_safe = None if lb is None else lb - (corr or 0.0)

    ub_enc = ref['ub_enc'] if ref else None
    rec_centre = dict(P_L=float(P0), flat=float(flat))
    fires = bool(ref['fires']) if ref else False
    if lb_safe is not None and lb_safe > hm:
        verdict = 'NO CERTIFICATE OF DEGREE <= %d' % H
    elif fires:
        verdict = 'certificate exists (W4)'
    else:
        verdict = 'inconclusive'

    rec = dict(key=key, H=H, L=L, h_min=hm, centre=rec_centre,
               lb=lb, lb_safe=lb_safe, lp_value=val,
               resid=(None if resid is None else float(resid)),
               a_l1=a1, corr=corr, ub_raw=r['ub_raw'], ub_lp=r['ub'],
               ub_enc=ub_enc, ub_L=(ref['ub_L'] if ref else None),
               margin_lb=(None if lb_safe is None else lb_safe - hm),
               bracket=(None if (lb is None or ub_enc is None) else ub_enc - lb),
               atoms=r['atoms'], pool=r['pool'], seed=len(ent), rounds=r['rounds'],
               feasible=r['feasible'], stalled=r['stalled'],
               converged=r['converged'], fires_w4=fires,
               secs=round(secs + tseed, 1))
    log('  H=%-4d lb=%s  (resid %.1e, ||a||_1 %.1f, corr %.1e)  h_min=%.6f  '
        'ub_enc=%s  pool %d atoms %d  %.0fs  ->  %s'
        % (H, ('%.9f' % lb) if lb is not None else 'infeasible',
           resid or 0.0, a1, corr or 0.0, hm,
           ('%.6f' % ub_enc) if ub_enc else 'n/a', r['pool'], r['atoms'],
           rec['secs'], verdict))
    rec['verdict'] = verdict
    del W, bc
    return rec


def run(keys, Hs, L, ts, rounds, cap, out, log):
    w4 = w4_rows()
    res = []
    for key in keys:
        coeffs, poly = CASES[key]
        al = Alpha(coeffs, poly)
        log('%s  alpha=%.9f  h_min=%.6f  budget=%.4f'
            % (key, float(al.alpha), h_min(al), math.log(2) - h_min(al)))
        for H in Hs:
            res.append(run_row(al, key, H, L, ts, rounds, cap, w4, log))
            json.dump(dict(when=time.strftime('%Y-%m-%d %H:%M'), L=L, ts=list(ts),
                           rounds=rounds, cap=cap, rows=res),
                      open(out, 'w'), indent=1)
    return res


# ---------------------------------------------------------------------------
# the gates
# ---------------------------------------------------------------------------

def gates(log, files='m8_w5.json,m8_w5_a.json,m8_w5_b.json,m8_w5_c.json'):
    rows = []
    for f in files.split(','):
        try:
            rows += json.load(open(f.strip()))['rows']
        except (IOError, ValueError):
            continue
    seen, keep = set(), []
    for r in sorted(rows, key=lambda r: -r['pool']):     # the deepest run of a row wins
        if (r['key'], r['H']) in seen:
            continue
        seen.add((r['key'], r['H']))
        keep.append(r)
    rows = sorted(keep, key=lambda r: (r['key'], r['H']))
    out = []
    if not rows:
        out.append(('G6', 'the two sides of the bracket are consistent', False,
                    'not run: none of %s present' % files))
        out.append(('G7', 'M7 sec 4\'s "pool too small" rows revisited', False,
                    'not run'))
    else:
        det, ok, n = [], True, 0
        worst = np.inf
        for r in rows:
            if r['lb'] is None or r['ub_enc'] is None:
                continue
            n += 1
            ok &= r['lb'] <= r['ub_enc'] + 1e-12
            worst = min(worst, r['ub_enc'] - r['lb'])
            ok &= (r['resid'] or 0.0) <= 1e-9
        det.append('%d rows carry both sides: the LP lower bound never exceeds W4\'s '
                   'rigorous upper bound (tightest bracket %.2e), and every mixture is '
                   'flat to <= 1e-9, so M7 Thm 5\'s degradation term is at most '
                   '%.1e' % (n, worst, max((r['corr'] or 0.0) for r in rows)))
        fired = [r for r in rows if r['verdict'].startswith('NO CERTIFICATE')]
        for r in fired:                                  # a no-go must not contradict W4
            ok &= not r['fires_w4']
        det.append('%d rows prove a no-go, and none of them is a row where W4 '
                   'certified -- the two halves of the threshold do not overlap'
                   % len(fired))
        out.append(('G6', 'the two sides of the bracket are consistent', ok,
                    ' ; '.join(det)))

        det, ok2 = [], True
        try:
            m7 = {r['poly']: r for r in json.load(open('m7_price.json'))}
        except (IOError, ValueError):
            m7 = {}
        n_new = 0
        for r in rows:
            row = (m7.get(r['key']) or {}).get('rows', {}).get(str(r['H']))
            if row is None:
                continue
            was = row.get('E_lb')
            if was is None and r['lb'] is not None:
                n_new += 1
                det.append('%s H=%d: M7 sec 4 records "pool too small" from a '
                           '%d-vector pool; the steered pool gives %.9f'
                           % (r['key'], r['H'], row.get('pool', 0), r['lb']))
            elif was is not None and r['lb'] is not None:
                ok2 &= r['lb'] >= was - 1e-6
                det.append('%s H=%d: M7 %.9f, this run %.9f (%+.1e)'
                           % (r['key'], r['H'], was, r['lb'], r['lb'] - was))
        out.append(('G7', 'M7 sec 4\'s "pool too small" rows revisited',
                    ok2 and (n_new > 0 or len(det) > 0),
                    ' ; '.join(det) or 'no overlapping (alpha, H) with m7_price.json'))

    for t, w, k, d in out:
        log('%-3s %-4s %s' % (t, 'PASS' if k else 'FAIL', w))
        log('       %s' % d)
    return [dict(gate=t, what=w, ok=bool(k), detail=d) for t, w, k, d in out]


def main():
    cmd = sys.argv[1] if len(sys.argv) > 1 and not sys.argv[1].startswith('-') \
        else 'run'
    keys = [a for a in sys.argv[1:] if a in CASES] or list(CASES)
    Hs = [int(v) for v in opt('--H', '64,128').split(',')]
    L = int(opt('--L', 14))
    ts = [float(v) for v in opt('--t', '0.04,0.5').split(',')]
    rounds = int(opt('--rounds', 150))
    cap = float(opt('--cap', 60.0))
    out = opt('--out', 'm8_w5.json')
    fh = open(out.replace('.json', '.log'), 'a')

    def log(s):
        print(s, flush=True)
        fh.write(s + '\n')
        fh.flush()

    t0 = time.time()
    if cmd == 'gates':
        log('# W5 gates  %s' % time.strftime('%Y-%m-%d %H:%M'))
        g = gates(log, files=opt('--rows',
                                 'm8_w5.json,m8_w5_a.json,m8_w5_b.json,m8_w5_c.json'))
        json.dump(dict(when=time.strftime('%Y-%m-%d %H:%M'), gates=g),
                  open('m8_w5_gates.json', 'w'), indent=1)
        log('wrote m8_w5_gates.json')
        return
    log('# W5  %s  keys %s  H %s  L=%d  t=%s  rounds %d  cap %g'
        % (time.strftime('%Y-%m-%d %H:%M'), keys, Hs, L, ts, rounds, cap))
    run(keys, Hs, L, ts, rounds, cap, out, log)
    log('total %.0f s' % (time.time() - t0))
    log('wrote %s' % out)


if __name__ == '__main__':
    main()
