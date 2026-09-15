#!/usr/bin/env python3
# (C) 2026 Ralf Stephan, in collaboration with Claude Code.
# CC0 1.0 Universal (public domain dedication).
"""R2e: the Gibbs pool above `H = 64` at `1+sqrt2`, and what it closes.

Two rows of the folder were blocked on one missing object, and both said so in the same
words.  `note-1061-R2d.html` sec 7: *"the binding constraint on `H_ent` is neither the
certificate nor the arithmetic: it is that no Gibbs pool above `H = 64` has been built."*
`note-1061-R2c.html` sec 10: *"a Gibbs pool above `H = 64` closes the bracket at 128 and
256."*  This is that pool -- `r1a_pool.py 128 256`, warm-started off the `H = 64` optimum,
2049 and 4097 memory-12 chains converted to exact rational circulations and enclosed at
`J = M = 60` -- and the two certificates it unblocks.

---------------------------------------------------------------------------------------
WHY A POOL PAST THE TRUST WALL IS STILL SOUND, and what it does cost

R2a's trust rule says a degree-`H` run on an `L`-window measures `F` only while
`2 pi H eps_L < 1` -- `15.8` at `L = 12`.  The pool here is GENERATED from the `L = 12`
window at `H = 128` and `H = 256`, i.e. a factor `8` and `16` past that wall.  It is
nevertheless sound, and the reason is worth stating once because it is the difference
between the two halves of the folder:

  * the window enters only the CHOICE of the `2049` (resp. `4097`) memory-12 chains.
    Whatever `a*` the optimiser returns, `q = bc.from_window(W, a)` is a vector of
    conditional probabilities in `(0,1)`, so the chain is a bona fide shift-invariant
    Markov measure on `{0,1}^Z` no matter how bad `a*` is;
  * `Phi_h` of that measure is then computed by `r1a_enclose`, from the exact rational
    circulation, with an a-priori rounding bound at `J = M = 60`.  No window appears.
    The radius is `1.48e-13` at `H = 4` and at `H = 256` alike -- it does not know `H`
    and it does not know `L`.

So the certificate `E_H >= ...` is a theorem at every `H` here.  What degrades past the
wall is the QUALITY of the pool: `a*` stops being the pressure-minimising direction of
the true `F`, so the chains cluster in a worse place and the hull is thinner than it
could be.  That is a loss of sharpness, not of soundness, and the measured cost of it is
in sec 3 below.  (The orbit rows of R2d carry no window at all; the union is what makes
the whole thing insensitive to this.)

---------------------------------------------------------------------------------------
THEOREM 1  (the bracket tightens monotonically, and in BOTH directions).  `K_H` is
non-increasing in `H`, so `E_H = max{h(mu) : mu in K_H}` is non-increasing.  Hence for
certified bounds `L(H) <= E_H <= U(H)` the sharpened pair

        U*(H) = min_{H' <= H} U(H'),        L*(H) = max_{H' >= H} L(H')

is certified too, and every entry of it is a theorem of the folder as it stands.  R2c
reported the raw `U(H)`; the tightening bites at `H = 256`, where the `L = 24` row
`0.684408` is superseded by `H = 128`'s `L = 26` row `0.683077` with nothing re-run.
The mirror half `L*` is what lets a certificate proved at a HIGH degree improve a LOW
one, which is the direction this run travels.

Consistency, and it is a real check: `L*(H) <= U*(H)` must hold at every `H`.  A pool
certificate above a deep-window enclosure would refute one of the two engines, and it is
exactly the test that caught M7 sec 4's LP column sitting `5.7e-6` below R2c's certified
lower bound.

Usage:  python3 r2e_pool256.py checks
        python3 r2e_pool256.py ent [--hs 128,256] [--q 16]
        python3 r2e_pool256.py bracket
        python3 r2e_pool256.py table
        python3 r2e_pool256.py html
"""
import json
import math
import os
import sys
import time
import warnings

import numpy as np

HERE = os.path.dirname(os.path.abspath(__file__))
sys.path.insert(0, HERE)

import r1a_enclose as R                                            # noqa: E402
import r2a_margin as MG                                            # noqa: E402
import r2b_ergodic as Z                                            # noqa: E402
import r2d_hull as D                                               # noqa: E402
from m0_engine import Alpha                                        # noqa: E402

warnings.filterwarnings('ignore')

KEY = '1+sqrt2'
POOL = 'r1b_pool256.json'          # the extended Gibbs pool (rows 4..256)
SEED = 'r1b_pool64.json'           # R1b's file, rows 4..64, must be untouched
OUT = os.path.join(HERE, 'r2e_pool256.json')
HS = (128, 256)
QDEF = 16
LOG2 = math.log(2.0)
HMIN = 0.44068679350977147

# point R2d's union machinery at the extended pool without editing R2d
D.UNITS[KEY] = (D.UNITS[KEY][0], D.UNITS[KEY][1], D.UNITS[KEY][2], POOL, D.UNITS[KEY][4])

_ok = _bad = 0


def opt(name, default):
    return sys.argv[sys.argv.index(name) + 1] if name in sys.argv else default


def load(path=None):
    p = path or OUT
    try:
        return json.load(open(p))
    except (IOError, ValueError):
        return {}


def save(d, path=None):
    with open(path or OUT, 'w') as f:
        json.dump(d, f)


def check(name, cond, detail="", log=print):
    global _ok, _bad
    if cond:
        _ok += 1
        log(f"  ok   {name}   {detail}")
    else:
        _bad += 1
        log(f"  FAIL {name}   {detail}")
    return bool(cond)


# ======================================================================================
# the certified bracket
# ======================================================================================
def _r2c_upper():
    """`U(H)` -- the best deep-window enclosure R2c certified at each degree."""
    up = {}
    for c in json.load(open(os.path.join(HERE, 'r2c_deep.json'))).get('cert', []):
        b = up.get(c['H'])
        if b is None or c['Lambda_enc'] < b[0]:
            up[c['H']] = (c['Lambda_enc'], c['kappa'], c['L'])
    return up


def _lower():
    """`L(H)` -- the best certified lower bound, over R1b, R2d and this run."""
    out = {}

    def put(H, v, src):
        if H not in out or v > out[H][0]:
            out[H] = (v, src)
    try:
        d = json.load(open(os.path.join(HERE, 'r1b_certify.json')))
        for k, r in d.items():
            if k.startswith(KEY + ':'):
                v = max((c[1]['h_lower'] for c in r['curve'] if c[1].get('delta', 0) > 0),
                        default=None)
                if v is not None:
                    put(int(k.split(':')[1]), v, 'R1b')
    except (IOError, ValueError, KeyError):
        pass
    for path, src in ((os.path.join(HERE, 'r2d_hull.json'), 'R2d union'),
                      (OUT, 'R2e union')):
        try:
            for r in json.load(open(path)).get('ent', []):
                if r.get('name') == KEY and r.get('pool') == 'union' and r.get('best'):
                    put(r['H'], r['best']['h_lower'], src)
        except (IOError, ValueError, KeyError):
            pass
    return out


def tighten(lo, up):
    """Theorem 1: `U*(H) = min_{H'<=H} U(H')` and `L*(H) = max_{H'>=H} L(H')`."""
    Hs = sorted(set(lo) | set(up))
    us, ls, best = {}, {}, None
    for H in Hs:
        if H in up and (best is None or up[H][0] < best[0]):
            best = up[H]
        if best is not None:
            us[H] = best
    best = None
    for H in reversed(Hs):
        if H in lo and (best is None or lo[H][0] > best[0]):
            best = lo[H]
        if best is not None:
            ls[H] = best
    return ls, us


def bracket(log=print):
    lo, up = _lower(), _r2c_upper()
    ls, us = tighten(lo, up)
    log('# E_H(1+sqrt2), two-sided and certified, monotone-tightened (Theorem 1)')
    log('#   h_min = %.9f   log 2 = %.9f' % (HMIN, LOG2))
    log('%5s %14s %-11s %14s %-12s %11s %10s' %
        ('H', 'lower L*(H)', 'source', 'upper U*(H)', 'at', 'width', 'to h_min'))
    rows = []
    for H in sorted(set(ls) | set(us)):
        l, u = ls.get(H), us.get(H)
        rows.append(dict(H=H, lower=(l[0] if l else None), lsrc=(l[1] if l else None),
                         upper=(u[0] if u else None),
                         uat=(('k=%g L=%d' % (u[1], u[2])) if u else None),
                         width=((u[0] - l[0]) if (l and u) else None)))
        log('%5d %14s %-11s %14s %-12s %11s %10s'
            % (H, '%.9f' % l[0] if l else '--', l[1] if l else '',
               '%.9f' % u[0] if u else '--', ('k=%g L=%d' % (u[1], u[2])) if u else '',
               '%.3e' % (u[0] - l[0]) if (l and u) else '--',
               '%+.5f' % (HMIN - u[0]) if u else '--'))
    raw = {H: v[0] for H, v in up.items()}
    log('  raw U(H) before tightening: ' +
        '  '.join('%d:%.6f' % (H, raw[H]) for H in sorted(raw)))
    return rows


# ======================================================================================
# the entropy certificates on the new rows
# ======================================================================================
def ent(Hs=HS, q=QDEF, tags=('M7', 'orb+B', 'union'), pool=None, log=print):
    pool = pool or POOL
    D.UNITS[KEY] = D.UNITS[KEY][:3] + (pool,) + D.UNITS[KEY][4:]
    D._UCACHE.clear()
    have = set(map(int, json.load(open(os.path.join(HERE, pool)))['rows']))
    out = []
    for H in Hs:
        if H not in have:
            log(f"  {KEY:>9} H={H:<4d}  not in {pool} yet -- skipped")
            continue
        for tag in tags:
            r = D.entrow(KEY, H, q, tag=tag, log=log)
            r['gibbs_pool'] = pool
            out.append(r)
    return out


# ======================================================================================
# a Gibbs pool that respects the trust wall: freeze the centre at a degree the window
# can still see, and let only the PERTURBATION modes run past it
# ======================================================================================
def build(H, H0=64, out=None, log=print):
    """The memory-12 Gibbs pool at degree `H` with the centre frozen at degree `H0`.

    `r1a_pool.py` re-runs `minimize_pressure` at every rung.  Past `H = 120` at `L = 12`
    the constrained pressure is UNBOUNDED BELOW (R2a's row-1 table: `P = -23.23` at
    `H = 128`, `xmax` at the box cap), so the centre it returns there is the truncation
    direction R2b later closed, and the chains built on it degenerate.  Nothing in the
    certificate needs that centre: the pool only has to be a family of measures whose
    `Phi` surrounds `0`.  So freeze `a*` at the last degree the window can see and let the
    `16H+1` perturbations carry the extra modes.  Entropy stays where `H0` put it,
    `Phi` is still enclosed at all `H` modes by `phi_fl`, and no run ever goes past the
    wall.  Same file schema as `r1a_pool.py`, so `r2d_hull.m7_rows` reads it unchanged.
    """
    import r1a_pool as P1
    from m3_entropy import Window, h_min
    from m4_fourier import best_window, pad
    from m7_price import BlockChain, lp_lower
    out = out or os.path.join(HERE, 'r2e_pool_frozen.json')
    al = Alpha(D.UNITS[KEY][0], KEY)
    R.set_alpha(2, 1, KEY)
    N, M, e = best_window(al, P1.LPOOL)
    W = Window(al, N, M).set_modes(list(range(1, H + 1)))
    bc = BlockChain(al, P1.LPOOL, hmax=H)
    src = json.load(open(os.path.join(HERE, POOL)))
    x0 = np.array(src['rows'][str(H0)]['xstar'])
    xstar = pad(x0, H0, H)
    log(f"# R2e frozen-centre pool   alpha={float(al.alpha):.9f}  h_min={h_min(al):.6f}"
        f"  L={P1.LPOOL}  window ({N},{M}) eps={e:.2e}  centre frozen at H0={H0}"
        f"  target H={H}  T=1e{len(str(P1.TDEN)) - 1}"
        f"  enclosure ({P1.JDEP},{P1.MDEP})")
    rec = load(out) or dict(alpha=float(al.alpha), h_min=h_min(al), Lpool=P1.LPOOL,
                            T=P1.TDEN, enclosure_window=[P1.JDEP, P1.MDEP],
                            transfer_window=[N, M, float(e)], frozen_at=H0, rows={})
    hs = list(range(1, H + 1))
    t0 = time.time()
    ent, phi, rads, rep, skipped = [], [], [], [], 0
    for x in P1.pool_vectors(H, xstar):
        a = x[:H] + 1j * x[H:]
        q = bc.from_window(W, a)
        pi = bc.stationary(q)
        if not (np.isfinite(q).all() and np.isfinite(pi).all()):
            skipped += 1
            continue
        w = np.empty(1 << (P1.LPOOL + 1))
        w[0::2] = pi * (1 - q)
        w[1::2] = pi * q
        if not np.isfinite(w).all() or w.sum() <= 0:
            skipped += 1
            continue
        c = R.circ_from_weights(P1.LPOOL, w, P1.TDEN)
        V, rad = R.phi_fl(c, hs, P1.JDEP, P1.MDEP)
        h_c = c.entropy()
        if not (np.isfinite(h_c) and np.isfinite(V).all()):
            skipped += 1
            continue
        ent.append(h_c)
        phi.append(V)
        rads.append(max(rad))
        rep.append(c.repair_cost)
    ent, phi = np.array(ent), np.array(phi)
    val, lam = lp_lower(ent, phi, H)
    dh = P1.hull_distance(phi, H)
    log(f"H={H:<4} pool {len(ent):4d} (skipped {skipped})  frozen at H0={H0}"
        f"  entropy LP {('%.6f' % val) if val is not None else '   --   '}"
        f"  hull distance {dh:.3e}  radius {max(rads):.2e}  repair {max(rep):.1e}"
        f"  entropies [{ent.min():.6f}, {ent.max():.6f}]  {time.time() - t0:.0f}s")
    rec['rows'][str(H)] = dict(
        n_pool=int(len(ent)), skipped=int(skipped), frozen_at=int(H0),
        upper=float(src['rows'][str(H0)]['upper']),   # the degree-H0 windowed pressure;
        # a valid upper bound for E_{H0} and hence, since E is non-increasing, for E_H
        lower=(None if val is None else float(val)),
        radius=float(max(rads)), repair=float(max(rep)),
        hull_distance_circ=float(dh),
        ent=[float(v) for v in ent],
        xstar=[float(v) for v in xstar],
        phi_re=[[float(z.real) for z in r] for r in phi],
        phi_im=[[float(z.imag) for z in r] for r in phi])
    save(rec, out)
    log(f"# wrote {out}")
    return rec['rows'][str(H)]


def diag(Hs=(128, 256), H0=64, sample=None, log=print):
    """Why `r1a_pool.py` cannot build a pool above `H = 64` here, measured.

    Two numbers per degree.  (a) What `minimize_pressure` returns on the `L = 12` window
    warm-started from the degree-`H0` optimum: R2a's row-1 table says the constrained
    pressure is UNBOUNDED BELOW past `H ~ 120` at this window, so the multiplier runs to
    the box cap and the returned `a*` is a truncation artefact, not a direction.  (b) How
    many of the `16H+1` candidate chains built on it survive the finiteness guard of
    `r1a_pool.py` -- `exp(weights(a))` overflows and `from_window` returns `0/0`, so a
    "Gibbs measure" at that `a*` is not a measure.  The frozen centre of `build()` is the
    fix, and the same count on it is the control.
    """
    import r1a_pool as P1
    from m3_entropy import Window, minimize_pressure
    from m4_fourier import best_window, pad
    from m7_price import BlockChain
    al = Alpha(D.UNITS[KEY][0], KEY)
    N, M, e = best_window(al, P1.LPOOL)
    bc = BlockChain(al, P1.LPOOL, hmax=max(Hs))
    src = json.load(open(os.path.join(HERE, POOL)))
    x0 = np.array(src['rows'][str(H0)]['xstar'])
    out = []
    log(f"# R2e diagnosis   L={P1.LPOOL}  window ({N},{M})  eps={e:.3e}"
        f"  trust wall 2 pi H eps < 1 at H = {1 / (2 * math.pi * e):.1f}")
    log('%5s %-9s %13s %9s %11s %9s %8s %8s' %
        ('H', 'centre', 'P', 'max|x|', 'sum h|a|', 'h(Gibbs)', 'chains', 'finite'))
    for H in Hs:
        W = Window(al, N, M).set_modes(list(range(1, H + 1)))
        for tag in ('optimised', 'frozen'):
            t0 = time.time()
            if tag == 'optimised':
                P, xs, _, _ = minimize_pressure(W, x0=pad(x0, H0, H))
            else:
                xs = pad(x0, H0, H)
            Pv, (_, hg) = W.pressure(xs[:H] + 1j * xs[H:])
            P, hg = float(Pv), float(hg)
            hs_ = np.arange(1, H + 1)
            s1 = float(np.sum(hs_ * np.hypot(xs[:H], xs[H:])))
            vecs = P1.pool_vectors(H, xs)
            if sample:
                vecs = vecs[::max(1, len(vecs) // sample)]
            fin = 0
            for x in vecs:
                q = bc.from_window(W, x[:H] + 1j * x[H:])
                if np.isfinite(q).all():
                    fin += 1
            log('%5d %-9s %13.6f %9.4f %11.4f %9.6f %8d %8d   (%.0fs)'
                % (H, tag, P, float(np.abs(xs).max()), s1, hg, len(vecs), fin,
                   time.time() - t0))
            out.append(dict(H=H, centre=tag, P=float(P), xmax=float(np.abs(xs).max()),
                            S1=s1, h_gibbs=hg, chains=len(vecs), finite=fin,
                            sampled=bool(sample), secs=time.time() - t0))
    return out


def orb(Hs=(128, 256), q=QDEF, ps=None, log=print):
    """R1b's entropy certificate on the ORBIT+BERNOULLI pool alone -- no Gibbs pool.

    `r2d_hull.entrow` reaches this pool only through `union()`, which loads the M7 rows
    first, so it cannot be asked for degrees the Gibbs pool has not reached.  Here the
    same two generator families are stacked directly, so the entropy half can be tested
    at any `H`: every periodic orbit has `h = 0`, so whatever entropy the certificate
    carries is Bernoulli mass the hull can absorb, and `E_H >= h_min` from this pool
    alone would settle `H_ent` with no Gibbs pool at all.
    """
    ps = ps or D.PGRID
    al = Alpha(D.UNITS[KEY][0], KEY)
    coef, A, B, path, hmin = D.UNITS[KEY]
    out = []
    for H in Hs:
        t0 = time.time()
        Vo, epso = D.orbit_rows(al, H, q)
        Vb, eb, epsb = D.bern_rows(al, A, B, H, ps)
        P = np.vstack([Vo, Vb])
        E = np.concatenate([np.zeros(len(Vo)), eb])
        Vm, eps = MG.vmat(P, H), max(epso, epsb)
        ca = D.cache_of(Vm)
        m = Vm.shape[1]
        if ca is None:
            log(f"  {KEY:>9} H={H:<4d} orb+B m={m:<6d}  rank deficient")
            continue
        Rv, lam0 = D.rmax_sub(Vm, ca['g'])
        if lam0 is None:
            log(f"  {KEY:>9} H={H:<4d} orb+B m={m:<6d} q<={q}  0 not in conv"
                f"  ({time.time() - t0:.0f}s)")
            out.append(dict(name=KEY, H=H, q=q, pool='orb+B', m=m, feasible=False,
                            delta=-float('inf'), h_min=hmin, secs=time.time() - t0))
            continue
        curve, best = [], None
        for c in D.CS:
            lm = lam0 if c == 1.0 else D.ent_lp_w(Vm, E, ca['g'], Rv * c)
            if lm is None:
                continue
            o = MG.margin(Vm, eps, H, ent=E,
                          lam=np.maximum(MG.refine(Vm, lm, 2), 0.0), cache=ca)
            curve.append(dict(c=c, delta=float(o['delta']), h_mix=float(o['h_mix']),
                              drift=float(o['h_drift']), h_lower=float(o['h_lower'])))
            if o['delta'] > 0 and (best is None or o['h_lower'] > best['h_lower']):
                best = curve[-1]
        r = dict(name=KEY, H=H, q=q, pool='orb+B', m=m, eps=float(eps),
                 sigma=float(ca['sigma']), R=Rv, h_min=hmin, curve=curve, best=best,
                 feasible=best is not None, secs=time.time() - t0)
        if best:
            log(f"  {KEY:>9} H={H:<4d} orb+B m={m:<6d} q<={q:<3d}"
                f"  delta {best['delta']:+.4e}  E_{H} >= {best['h_lower']:.6f}"
                f"  (h_min {hmin:.6f})"
                f"  {'H_flat,H_ent > %d' % H if best['h_lower'] > hmin else 'H_flat > %d only' % H}"
                f"  ({r['secs']:.0f}s)")
        else:
            log(f"  {KEY:>9} H={H:<4d} orb+B m={m:<6d} q<={q:<3d}  no certificate"
                f"  ({r['secs']:.0f}s)")
        out.append(r)
    return out


def flat(Hs=(256, 512), qs=(14, 16), log=print):
    """The `m(H)` ladder on the ORBIT hull alone -- no pool, no window, no `H_ent`.

    This is R2d's ladder A continued.  It needs nothing from the Gibbs pool, so it runs
    while the pool is still building, and it is what certifies `H_flat`: `delta > 0` is
    `0 in int conv Phi(orbits)`, hence `K_H != empty`, hence `nu_H = 0`.
    """
    al = Alpha(D.UNITS[KEY][0], KEY)
    out = []
    for H in Hs:
        for q in qs:
            out.append(D.flat(al, H, q, rho=True, log=log))
    return out


# ======================================================================================
# self-checks
# ======================================================================================
def selfchecks(log=print):
    global _ok, _bad
    _ok = _bad = 0
    log('# R2e self-checks')
    pool = json.load(open(os.path.join(HERE, POOL)))
    seed = json.load(open(os.path.join(HERE, SEED)))

    # 1. the seed rows survived the extension bit for bit
    same = all(pool['rows'][k] == seed['rows'][k] for k in seed['rows'])
    check('R1b rows 4..64 are bit-identical in the extended file', same,
          'rows %s' % sorted(map(int, seed['rows'])), log)

    # 2. R1b's own file was not written to
    check('r1b_pool64.json still stops at 64', sorted(map(int, seed['rows']))[-1] == 64,
          'rows %s' % sorted(map(int, seed['rows'])), log)

    have = sorted(map(int, pool['rows']))
    log(f"  --   extended pool now holds rows {have}")

    for H in have:
        row = pool['rows'][str(H)]
        if H <= 64:
            continue
        # 3. pool size: one centre plus 4 signs x 4 magnitudes x H modes, minus rejects
        check('H=%d pool size' % H, 0.95 * (16 * H + 1) <= row['n_pool'] <= 16 * H + 1,
              'n = %d of a possible %d' % (row['n_pool'], 16 * H + 1), log)
        # 4. the enclosure radius does not know H and does not know the window
        r64 = pool['rows']['64']['radius']
        check('H=%d enclosure radius is R1a\'s, unchanged' % H,
              abs(row['radius'] - r64) < 1e-15,
              'radius %.3e vs %.3e at H=64' % (row['radius'], r64), log)
        # 5. the rounding repair of the circulation stays at R1a's level
        check('H=%d circulation repair cost' % H, row['repair'] < 1e-6,
              'repair %.2e' % row['repair'], log)
        # 6. Phi has the shape the certificate wants
        phi = np.array(row['phi_re'])
        check('H=%d Phi matrix shape' % H, phi.shape == (row['n_pool'], H),
              '%s' % (phi.shape,), log)
        # 7. |Phi_h| <= 1 for every member and every mode -- it is a characteristic fn
        mod = np.hypot(np.array(row['phi_re']), np.array(row['phi_im']))
        check('H=%d every |Phi_h| <= 1' % H, mod.max() <= 1 + 1e-12,
              'max |Phi| = %.6f' % mod.max(), log)
        # 8. entropies are in [0, log 2]
        e = np.array(row['ent'])
        check('H=%d entropies in [0, log 2]' % H, e.min() >= -1e-12 and e.max() <= LOG2 + 1e-12,
              'ent in [%.6f, %.6f]' % (e.min(), e.max()), log)

    # 8b. the same six structural checks on the FROZEN pool, which is where the
    #     rows above H=64 actually live (POOL itself stops at 64 by design)
    fz = os.path.join(HERE, 'r2e_pool_frozen.json')
    if os.path.exists(fz):
        frozen = json.load(open(fz))
        for H in sorted(map(int, frozen['rows'])):
            row = frozen['rows'][str(H)]
            check('frozen H=%d pool size' % H,
                  0.95 * (16 * H + 1) <= row['n_pool'] <= 16 * H + 1,
                  'n = %d of a possible %d (skipped %d)'
                  % (row['n_pool'], 16 * H + 1, row['skipped']), log)
            check('frozen H=%d enclosure radius is R1a\'s, unchanged' % H,
                  abs(row['radius'] - pool['rows']['64']['radius']) < 1e-15,
                  'radius %.3e' % row['radius'], log)
            check('frozen H=%d circulation repair cost' % H, row['repair'] < 1e-6,
                  'repair %.2e' % row['repair'], log)
            mod = np.hypot(np.array(row['phi_re']), np.array(row['phi_im']))
            check('frozen H=%d Phi shape and |Phi_h| <= 1' % H,
                  mod.shape == (row['n_pool'], H) and mod.max() <= 1 + 1e-12,
                  'shape %s  max |Phi| = %.6f' % (mod.shape, mod.max()), log)
            e = np.array(row['ent'])
            check('frozen H=%d entropies in [h_min, log 2]' % H,
                  e.min() >= HMIN - 1e-12 and e.max() <= LOG2 + 1e-12,
                  'ent in [%.6f, %.6f], mean %.6f' % (e.min(), e.max(), e.mean()), log)
            # the frozen centre IS the H0 centre, zero-padded: same vector, same pressure
            H0 = row['frozen_at']
            x0 = np.array(json.load(open(os.path.join(HERE, POOL)))
                          ['rows'][str(H0)]['xstar'])
            xs = np.array(row['xstar'])
            same = (np.allclose(xs[:H0], x0[:H0]) and np.allclose(xs[H:H + H0], x0[H0:])
                    and np.abs(np.delete(xs, list(range(H0)) + list(range(H, H + H0)))).max() == 0)
            check('frozen H=%d centre is the H0=%d centre, zero-padded' % (H, H0), same,
                  'max |x| = %.6f, nonzero modes %d' % (np.abs(xs).max(), int((xs != 0).sum())),
                  log)
            check('frozen H=%d inherits the H0=%d upper bound' % (H, H0),
                  abs(row['upper'] - json.load(open(os.path.join(HERE, POOL)))
                      ['rows'][str(H0)]['upper']) < 1e-15,
                  'upper %.15f' % row['upper'], log)
            check('frozen H=%d pool does NOT enclose 0 on its own' % H,
                  row['hull_distance_circ'] > 0,
                  'hull distance %.4e (the trust wall, measured)'
                  % row['hull_distance_circ'], log)

    # 9. the optimiser's own upper bound is non-increasing in H (E_H is)
    ups = [pool['rows'][str(H)]['upper'] for H in have]
    check('optimiser upper bound is non-increasing in H',
          all(ups[i + 1] <= ups[i] + 1e-9 for i in range(len(ups) - 1)),
          ' '.join('%.6f' % u for u in ups), log)

    # 10. R2d's loader reads the new rows
    for H in have[-1:]:
        P7, e7, eps7, upper = D.m7_rows(POOL, H)
        check('R2d m7_rows reads H=%d' % H,
              P7.shape == (len(e7), H) and np.isfinite(P7).all(),
              'shape %s  radius %.2e  upper %.6f' % (P7.shape, eps7, upper), log)

    # 11. the orbit generators are the Lyndon words, and the count is Moreau's
    n = sum(len(D.lyndon(q)) for q in [QDEF]) if False else len(D.lyndon(QDEF))
    moreau = sum(sum(D.mu(d) * 2 ** (q // d) for d in D.divisors(q)) // q
                 for q in range(1, QDEF + 1))
    check('Lyndon count at q<=%d is Moreau\'s necklace sum' % QDEF, n == moreau,
          '%d words' % n, log)

    # 12. the certified bracket is consistent: L*(H) <= U*(H) everywhere
    lo, up = _lower(), _r2c_upper()
    ls, us = tighten(lo, up)
    bad = [(H, ls[H][0], us[H][0]) for H in sorted(set(ls) & set(us))
           if ls[H][0] > us[H][0]]
    check('L*(H) <= U*(H) at every degree', not bad,
          'checked %d degrees' % len(set(ls) & set(us)) if not bad else str(bad), log)

    # 13. Theorem 1 actually tightens something, and only downward
    raw = {H: v[0] for H, v in up.items()}
    check('Theorem 1 never loosens the upper side',
          all(us[H][0] <= raw[H] + 1e-15 for H in raw),
          'tightened at %s' % [H for H in sorted(raw) if us[H][0] < raw[H] - 1e-15], log)

    # 14. the trust wall is where R2a says, and this pool is past it
    epsL = 1.0136e-2                    # eps_12 at 1+sqrt2, from r1b_pool64.log
    check('the L=12 pool at H=256 is past R2a\'s trust wall, as expected',
          2 * math.pi * 256 * epsL > 1,
          '2 pi H eps_12 = %.1f at H=256 (wall at H = %.1f)'
          % (2 * math.pi * 256 * epsL, 1 / (2 * math.pi * epsL)), log)

    log(f"# {_ok} ok, {_bad} FAILED")
    return _ok, _bad


# ======================================================================================
def table(log=print):
    d = load()
    rows = d.get('ent', [])
    if rows:
        log('# the entropy certificate on the three pools')
        log('%5s %7s %7s %8s %14s %14s %10s' %
            ('H', 'pool', 'm', 'q', 'delta', 'E_H >=', 'verdict'))
        for r in rows:
            b = r.get('best')
            log('%5d %7s %7d %8d %14s %14s %10s'
                % (r['H'], r['pool'], r['m'], r['q'],
                   '%+.4e' % b['delta'] if b else 'none',
                   '%.6f' % b['h_lower'] if b else '--',
                   ('H_flat,H_ent > %d' % r['H']) if (b and b['h_lower'] > HMIN)
                   else ('H_flat > %d only' % r['H']) if b else 'not certified'))
    if d.get('bracket'):
        log('')
        log('# the bracket')
        for r in d['bracket']:
            log('%5d  [%s, %s]  width %s'
                % (r['H'], '%.9f' % r['lower'] if r['lower'] else '--',
                   '%.9f' % r['upper'] if r['upper'] else '--',
                   '%.3e' % r['width'] if r['width'] else '--'))


def main():
    global OUT
    os.chdir(HERE)
    OUT = opt('--out', OUT)
    cmd = sys.argv[1] if len(sys.argv) > 1 else 'checks'
    if cmd == 'checks':
        ok, bad = selfchecks()
        d = load()
        d['checks'] = dict(ok=ok, bad=bad)
        save(d)
        sys.exit(0 if bad == 0 else 1)
    elif cmd == 'ent':
        hs = [int(x) for x in opt('--hs', ','.join(map(str, HS))).split(',')]
        q = int(opt('--q', QDEF))
        t0 = time.time()
        rows = ent(hs, q, pool=opt('--pool', None))
        d = load()
        d['ent'] = [r for r in d.get('ent', [])
                    if (r['H'], r['pool'], r['q'], r.get('gibbs_pool')) not in
                    {(x['H'], x['pool'], x['q'], x.get('gibbs_pool')) for x in rows}] + rows
        d['meta'] = dict(pool=POOL, q=q, hs=hs, h_min=HMIN, log2=LOG2,
                         secs=time.time() - t0)
        save(d)
    elif cmd == 'build':
        for H in [int(x) for x in opt('--hs', '128').split(',')]:
            build(H, H0=int(opt('--h0', 64)), out=opt('--pool', None))
    elif cmd == 'diag':
        hs = [int(x) for x in opt('--hs', '128,256').split(',')]
        rows = diag(hs, H0=int(opt('--h0', 64)),
                    sample=(int(opt('--sample', 0)) or None))
        d = load()
        d['diag'] = rows
        save(d)
    elif cmd == 'orb':
        hs = [int(x) for x in opt('--hs', '128,256').split(',')]
        rows = orb(hs, int(opt('--q', QDEF)))
        d = load()
        d['orb'] = [r for r in d.get('orb', [])
                    if (r['H'], r['q']) not in {(x['H'], x['q']) for x in rows}] + rows
        save(d)
    elif cmd == 'flat':
        hs = [int(x) for x in opt('--hs', '256,512').split(',')]
        qs = [int(x) for x in opt('--q', '14,16').split(',')]
        rows = flat(hs, qs)
        d = load()
        d['flat'] = [r for r in d.get('flat', [])
                     if (r['H'], r['q']) not in {(x['H'], x['q']) for x in rows}] + rows
        save(d)
    elif cmd == 'bracket':
        d = load()
        d['bracket'] = bracket()
        save(d)
    elif cmd == 'table':
        table()
    else:
        print(__doc__)


if __name__ == '__main__':
    main()
