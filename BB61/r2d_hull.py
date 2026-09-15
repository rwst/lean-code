#!/usr/bin/env python3
# (C) 2026 Ralf Stephan, in collaboration with Claude Code.
# CC0 1.0 Universal (public domain dedication).
"""R2d of `plan-BB61-counterexample.html`: R1b's certificates and R2a's `m(H)` ladder,
re-run on the periodic-orbit hull instead of the M7 pool.

R2b showed that the hull of the periodic orbits certifies `K_H != empty` with a margin
`19.6x` M7's at `H = 64`, on generators that need no stationary solve, no rounding repair
and no window at all.  R2d asks what that buys: sec 12's row reads *"a better `m(H)`, and
`H_flat, H_ent` pushed past 64 at all three units"*.  Both halves are delivered, and the
second one only by a pool that is neither R2b's nor M7's.

---------------------------------------------------------------------------------------
THEOREM 1  (the generator set is the Lyndon words).  The shift-invariant measures carried
by a periodic orbit of period `<= q` are in bijection with the LYNDON words of length
`<= q`: an orbit is a rotation class of a PRIMITIVE word, and a rotation class of an
imprimitive word carries the same measure as its primitive root.  R2b's `necklaces(q)`
enumerates rotation classes of words of each length `<= q` separately, so it lists an
imprimitive word once for every length it divides -- 2616 rows at `q = 14` for 2538
measures, 8925 for 8800 at `q = 16`.

The duplicates are not free.  Theorem 1\' of `note-1061-R2a.html` certifies with
`R = min_j lam_j / g_j` under `sum_j lam_j = 1`, so `R <= 1 / sum_j g_j`: a repeated
column adds its own `g_j` to the ceiling while adding nothing to the hull.  Deduplicating
is worth `1.03x` at `H = 8` and `1.06x` at `H = 64` here -- small, but it is a strict
improvement obtained by DELETING rows, which is the opposite of what the M7 loop does.

---------------------------------------------------------------------------------------
THEOREM 2  (the two pools are unionable, and the orientation is pinned).  For every binary
word `w` and every `L >= len(w)`,

        orbit_phi_true(alpha, w, H)   ==   phi_fl(circ_from_word(L, w), 1..H, J, M)

to `6.2e-15` at all three units of M7 sec 4 -- two engines that share no code: a pair of
geometric series summed with `math.fsum`, against R1a's forward pass over the order-`L`
de Bruijn graph with its a-priori rounding bound.  On the REVERSED word the two differ by
`0.9`, so the agreement also pins the orientation of the orbit series: it is R1a's, and
the reversal R2b documented is between the orbit series and the WINDOW's block encoding,
not between the orbit series and the folder's enclosure engine.

Consequence: orbit rows, M7 rows and Bernoulli rows are coordinates of one convex
geometry in `R^{2H}` and may be stacked into a single pool, with `eps` the larger of the
two radii (`1.48e-13` for M7, `9.0e-14` per coefficient for the orbits at `H = 64`).

---------------------------------------------------------------------------------------
THEOREM 3  (complementarity, and why the union is not a convenience).  Write `rho(P)` for
the depth of `0` in `conv Phi(P)` and `E(P)` for the largest entropy of a mixture of `P`
that lands on `0`.  At the same `(alpha, H)` the orbit pool maximises the first and
ANNIHILATES the second -- every periodic orbit has `h = 0`, so `E(orbits + Bernoulli)` is
`log 2` times the Bernoulli weight the hull can absorb, and that weight is bounded by
`rho / (rho + |Phi(Bern)|_2)`, which is `0.11` at `(1+sqrt2, H=64)`.  The M7 pool does the
opposite: `rho` is `20x` smaller and every member has entropy within `0.15` of `log 2`.

So the two failures are disjoint, and the union repairs both at once.  The sharpest case
is the one R1b recorded as its single REFUTATION:

        (3+sqrt5)/2, H = 64:   M7 pool          0 not in conv, certified (gap 5.5e-2)
                               orbits+Bernoulli feasible, but E <= 0.0907 < h_min
                               UNION (q <= 18)  delta = 2.51e-6 > 0 and E_64 >= 0.483287
                                                > h_min = 0.481212

which is `H_flat((3+sqrt5)/2) > 64` AND `H_ent((3+sqrt5)/2) > 64`, the last of the three
units and the exact content of sec 12's R2d gate.

---------------------------------------------------------------------------------------
Two notes on what this does NOT say.

  * `H_ent > 64` is a measurement, not progress towards a proof.  `E_H <= h_min` is what
    would PROVE 10.61 at `alpha` (M3 Thm 12); pushing `H_ent` up raises the degree the
    certificate lane has to reach.  R2d makes the lane more expensive at `(3+sqrt5)/2`,
    and it does so by closing the one row where the folder could still have hoped the
    obstruction was an artefact of the pool.
  * The orbit ladder has NO window, so R2a's trust rule `2 pi H eps_L < 1` does not apply
    to it.  That is what lets `m(H)` be read past `H = 64`: `H_flat(1+sqrt2) > 128` is
    certified here with `eps = 3.5e-12`, where the M7 ladder at `L = 12` is already a
    factor 6 past its own horizon at `H = 512`.

Usage:  python3 r2d_hull.py --checks        # self-checks only
        python3 r2d_hull.py                 # self-checks, then the three ladders
        python3 r2d_hull.py --one NAME H q  # one union certificate
"""
import json
import math
import os
import sys
import time
import warnings
from fractions import Fraction as Fr

import numpy as np
from scipy.optimize import linprog

sys.path.insert(0, '/home/ralf/math/lean-code/BB61')
import r1a_enclose as R
import r2a_margin as MG
import r2b_ergodic as Z
from m0_engine import Alpha

warnings.filterwarnings('ignore')
BB = '/home/ralf/math/lean-code/BB61'
LOG2 = math.log(2.0)
INF = float('inf')
LPOPT = dict(primal_feasibility_tolerance=1e-10, dual_feasibility_tolerance=1e-10)
PGRID = (Fr(1, 2), Fr(9, 20), Fr(11, 20), Fr(2, 5), Fr(3, 5), Fr(7, 20), Fr(13, 20))
CS = (1.0, 0.3, 0.1, 1e-2, 1e-3, 1e-4, 1e-5, 1e-6)

# name -> (coefficients of x^2 - A x - B as m0_engine wants them, A, B, R1b pool, h_min)
UNITS = {
    '1+sqrt2': ([1, -2, -1], 2, 1, 'r1b_pool64.json', 0.44068679350977147),
    'golden2': ([1, -3, 1], 3, -1, 'r1b_pool_golden2.json', 0.48121182505960347),
    'root13': ([1, -3, -1], 3, 1, 'r1b_pool_root13.json', 0.5973816086435547),
}
_ok = _bad = 0


def check(name, cond, detail=""):
    global _ok, _bad
    if cond:
        _ok += 1
        print(f"  ok   {name}   {detail}")
    else:
        _bad += 1
        print(f"  FAIL {name}   {detail}")


# ======================================================================================
# the generators
# ======================================================================================
def lyndon(n):
    """Duval: every Lyndon word of length `<= n`, i.e. every distinct periodic orbit of
    period `<= n`, in `O(1)` amortised per word."""
    out, w = [], [-1]
    while w:
        w[-1] += 1
        m = len(w)
        if m <= n:
            out.append(tuple(w))
        while len(w) < n:
            w.append(w[len(w) - m])
        while w and w[-1] == 1:
            w.pop()
    return out


def orbit_rows(al, H, q):
    """`Phi(mu_w)` for every periodic orbit of period `<= q`, and the per-coefficient
    radius `margin` wants (it multiplies by `sqrt(H)` itself)."""
    V = np.array([Z.orbit_phi_true(al, w, H) for w in lyndon(q)])
    return V, Z.orbit_phi_radius(al, H) / math.sqrt(H)


def bern_rows(al, A, B, H, ps=PGRID, J=100, M=100):
    """Bernoulli(p) through R1a's own engine, so the radius is R1a's and not a new one."""
    R.set_alpha(A, B, al.name)
    hs = list(range(1, H + 1))
    V, ent, rad = [], [], 0.0
    for p in ps:
        c = R.circ_bernoulli(1, p)
        v, r = R.phi_fl(c, hs, J, M)
        V.append(np.asarray(v))
        ent.append(c.entropy())
        rad = max(rad, max(r))
    return np.array(V), np.array(ent), rad


def m7_rows(path, H):
    d = json.load(open(f'{BB}/{path}'))
    row = d['rows'][str(H)]
    phi = np.array(row['phi_re']) + 1j * np.array(row['phi_im'])
    return phi, np.array(row['ent']), float(row['radius']), float(row['upper'])


# ======================================================================================
# the two linear programmes.  Neither is ever trusted: `MG.margin` re-certifies in exact
# rational arithmetic.  Both are written in the `m`-free form -- R2a's
# `weighted_maximin_lp` builds a dense `m x (m+1)` block, which is 620 MB at `m = 8800`.
# ======================================================================================
def rmax_sub(Vm, g):
    """max `R` s.t. `V lam = 0`, `1^T lam = 1`, `lam >= R g`, in the variables `(R, s)`
    with `lam = R g + s`, `s >= 0`: `d+1` rows and `m+1` columns instead of `m` rows."""
    d, m = Vm.shape
    g = np.asarray(g, dtype=float)
    A = np.vstack([np.hstack([(Vm @ g)[:, None], Vm]),
                   np.append(g.sum(), np.ones(m))])
    b = np.append(np.zeros(d), 1.0)
    c = np.zeros(m + 1)
    c[0] = -1.0
    r = linprog(c, A_eq=A, b_eq=b, bounds=[(0, None)] * (m + 1), method='highs',
                options=LPOPT)
    if not r.success:
        return None, None
    Rv = float(r.x[0])
    return Rv, Rv * g + np.asarray(r.x[1:])


def ent_lp_w(Vm, ent, g, R0):
    """max `sum_j lam_j h_j` s.t. `V lam = 0`, `1^T lam = 1`, `lam_j >= R0 g_j` --
    R1b's `entropy_lp` with Theorem 1\'s row-norm floor in place of the uniform one."""
    d, m = Vm.shape
    A = np.vstack([Vm, np.ones((1, m))])
    b = np.append(np.zeros(d), 1.0)
    lo = R0 * np.asarray(g, dtype=float)
    r = linprog(-np.asarray(ent), A_eq=A, b_eq=b, bounds=list(zip(lo, [None] * m)),
                method='highs', options=LPOPT)
    return np.asarray(r.x) if r.success else None


def cache_of(Vm):
    """The parts of Theorem 1\' that depend on the pool and not on the weights."""
    m = Vm.shape[1]
    Wf = np.vstack([Vm, np.ones((1, m))])
    sig, lam_lo, lam0, dG = MG.sigma_min_lower(Wf)
    if sig <= 0:
        return None
    g, _ = MG.rowpinv_upper(Wf, lam_lo, dG)
    return dict(g=g, sigma=sig, lam_lo=lam_lo, lam0=lam0, dG=dG, e=MG._scale(Vm))


# ======================================================================================
# ladder A -- m(H) on the orbit hull alone, with no window anywhere in it
# ======================================================================================
def flat(al, H, q, rho=True, log=print):
    t0 = time.time()
    V, eps = orbit_rows(al, H, q)
    Vm = MG.vmat(V, H)
    ca = cache_of(Vm)
    if ca is None:
        log(f"  {al.name:>9} H={H:<4d} q<={q:<3d} m={Vm.shape[1]:<6d}  rank deficient")
        return dict(name=al.name, H=H, q=q, m=int(Vm.shape[1]), delta=-INF, feasible=False)
    Rv, lam = rmax_sub(Vm, ca['g'])
    if lam is None:
        ru, _ = (MG.depth_upper(Vm, starts=4, iters=20) if rho else (float('nan'), None))
        log(f"  {al.name:>9} H={H:<4d} q<={q:<3d} m={Vm.shape[1]:<6d} sigma {ca['sigma']:.3e}"
            f"  LP infeasible: 0 is not interior to this hull   rho_up {ru:.4e}"
            f"  ({time.time() - t0:.0f}s)")
        return dict(name=al.name, H=H, q=q, m=int(Vm.shape[1]), eps=eps,
                    sigma=float(ca['sigma']), delta=-INF, rho=float(ru), feasible=False,
                    secs=time.time() - t0)
    out = MG.margin(Vm, eps, H, lam=MG.refine(Vm, lam, 2), cache=ca)
    ru = float('nan')
    if rho:
        ru, _ = MG.depth_upper(Vm, starts=4, iters=20)
    r = dict(name=al.name, H=H, q=q, m=int(Vm.shape[1]), eps=float(eps),
             sigma=float(out['sigma']), R=float(out['R']), r2=float(out['r2']),
             e2=float(out['e2']), delta=float(out['delta']), rho=float(ru),
             feasible=bool(out['delta'] > 0), secs=time.time() - t0)
    log(f"  {al.name:>9} H={H:<4d} q<={q:<3d} m={r['m']:<6d} sigma {r['sigma']:.3e}"
        f"  delta {r['delta']:+.6e}  rho_up {ru:.4e}  e2 {r['e2']:.2e}"
        f"  {'K_H != empty' if r['feasible'] else 'NOT certified'}  ({r['secs']:.0f}s)")
    return r


# ======================================================================================
# ladder C -- R1b's entropy certificate on the union pool
# ======================================================================================
_UCACHE = {}


def union(name, H, q, ps=PGRID):
    key = (name, H, q)
    if key in _UCACHE:
        return _UCACHE[key]
    coef, A, B, path, hmin = UNITS[name]
    al = Alpha(coef, name)
    P7, e7, eps7, upper = m7_rows(path, H)
    Vo, epso = orbit_rows(al, H, q)
    Vb, eb, epsb = bern_rows(al, A, B, H, ps)
    P = np.vstack([P7, Vo, Vb])
    E = np.concatenate([e7, np.zeros(len(Vo)), eb])
    _UCACHE.clear()
    _UCACHE[key] = (al, MG.vmat(P, H), E, max(eps7, epso, epsb), hmin, upper,
                    len(P7), len(Vo))
    return _UCACHE[key]


def entrow(name, H, q, tag='union', ps=PGRID, log=print):
    t0 = time.time()
    al, Vm, E, eps, hmin, upper, n7, no = union(name, H, q, ps)
    if tag == 'M7':
        Vm, E = Vm[:, :n7], E[:n7]
    elif tag == 'orb+B':
        Vm, E = Vm[:, n7:], E[n7:]
    m = Vm.shape[1]
    ca = cache_of(Vm)
    if ca is None:
        log(f"  {name:>9} H={H:<4d} {tag:>6} m={m:<6d}  rank deficient")
        return dict(name=name, H=H, q=q, pool=tag, m=m, feasible=False, delta=-INF)
    Rv, lam0 = rmax_sub(Vm, ca['g'])
    if lam0 is None:
        log(f"  {name:>9} H={H:<4d} {tag:>6} m={m:<6d}  0 not in conv: NOT certified"
            f"  ({time.time() - t0:.0f}s)")
        return dict(name=name, H=H, q=q, pool=tag, m=m, feasible=False, delta=-INF,
                    h_min=hmin, upper=upper, secs=time.time() - t0)
    curve, best = [], None
    for c in CS:
        lm = lam0 if c == 1.0 else ent_lp_w(Vm, E, ca['g'], Rv * c)
        if lm is None:
            continue
        o = MG.margin(Vm, eps, H, ent=E, lam=np.maximum(MG.refine(Vm, lm, 2), 0.0),
                      cache=ca)
        curve.append(dict(c=c, delta=float(o['delta']), h_mix=float(o['h_mix']),
                          drift=float(o['h_drift']), h_lower=float(o['h_lower'])))
        if o['delta'] > 0 and (best is None or o['h_lower'] > best['h_lower']):
            best = curve[-1]
    r = dict(name=name, H=H, q=q, pool=tag, m=m, eps=float(eps), sigma=float(ca['sigma']),
             R=Rv, h_min=hmin, upper=upper, curve=curve, best=best,
             feasible=best is not None, secs=time.time() - t0)
    if best:
        ok = best['h_lower'] > hmin
        log(f"  {name:>9} H={H:<4d} {tag:>6} m={m:<6d} q<={q:<3d}"
            f"  delta {best['delta']:+.4e}  E_{H} >= {best['h_lower']:.6f}"
            f"  (h_min {hmin:.6f}, upper {upper:.6f})"
            f"  {'H_flat,H_ent > %d' % H if ok else 'H_flat > %d only' % H}"
            f"  ({r['secs']:.0f}s)")
    else:
        log(f"  {name:>9} H={H:<4d} {tag:>6} m={m:<6d} q<={q:<3d}  no certificate"
            f"  ({r['secs']:.0f}s)")
    return r


# ======================================================================================
# self-checks
# ======================================================================================
def selfchecks():
    print("# R2d self-checks")

    # 1-3. Theorem 1: Lyndon words are the distinct orbits, and `necklaces` over-counts
    for q in (8, 12, 14):
        L = lyndon(q)
        prim = {min(w[k:] + w[:k] for k in range(len(w))) for w in L}
        dup = [w for w in Z.necklaces(q)
               if any(w == w[:d] * (len(w) // d) for d in range(1, len(w)) if len(w) % d == 0)]
        exact = sum(sum(mu(d) * 2 ** (n // d) for d in divisors(n)) // n
                    for n in range(1, q + 1))
        check(f"lyndon({q}) = the aperiodic necklaces, count = Witt's formula",
              len(L) == len(prim) == exact and len(Z.necklaces(q)) == len(L) + len(dup),
              f"{len(L)} Lyndon, {len(Z.necklaces(q))} R2b rows, {len(dup)} imprimitive")

    # 4-6. Theorem 2: the orbit series is R1a's `phi_fl`, on the nose, and oriented.
    #      Reversal moves `Phi` at every unit EXCEPT the reciprocal one: at `golden2`,
    #      `x^2-3x+1` has `abar = 1/alpha`, so `c_m = (abar-1) abar^m = -(a-1) a^-(m+1)`
    #      and `F(omega) = sum_{j>=1} (a-1) a^-j (omega_j + omega_{1-j})`, which the flip
    #      `omega_i -> omega_{1-i}` fixes.  The check below asserts BOTH behaviours, so
    #      it would fail if the orientation of either engine ever moved.
    H, hs = 8, list(range(1, 9))
    for nm in UNITS:
        coef, A, B, _, _ = UNITS[nm]
        al = Alpha(coef, nm)
        R.set_alpha(A, B, nm)
        recip = (B == -1)
        fw = rv = 0.0
        for w in ((0, 1), (0, 0, 1), (0, 0, 1, 0, 1, 1, 1), (0, 1, 1, 0, 1, 0, 0, 0)):
            t = Z.orbit_phi_true(al, list(w), H)
            v1, _ = R.phi_fl(R.circ_from_word(len(w) + 2, list(w)), hs, 60, 60)
            v2, _ = R.phi_fl(R.circ_from_word(len(w) + 2, list(w)[::-1]), hs, 60, 60)
            fw = max(fw, float(np.abs(v1 - t).max()))
            rv = max(rv, float(np.abs(v2 - t).max()))
        check(f"orbit_phi_true == R1a phi_fl at {nm}; reversal "
              f"{'is a symmetry (abar = 1/alpha)' if recip else 'moves Phi'}",
              fw < 1e-13 and ((rv < 1e-13) if recip else (rv > 1e-2)),
              f"forward {fw:.2e}, reversed {rv:.2e}")

    # 6a. and the reciprocal identity itself, at the level of `F`
    al = Alpha(UNITS['golden2'][0], 'golden2')
    a = float(al.alpha)
    fut = np.array([(a - 1.0) * a ** (-j) for j in range(1, 121)])
    w = [0, 0, 1, 0, 1, 1, 1]
    q = len(w)
    Fs = Z.orbit_F_true(al, w)
    idx = np.arange(1, 121)
    rebuilt = [math.fsum(list(fut * np.array([w[(i + j) % q] for j in idx], float))
                         + list(fut * np.array([w[(i + 1 - j) % q] for j in idx], float)))
               for i in range(q)]
    check("golden2: F(omega) = sum_j (a-1)a^-j (omega_j + omega_{1-j}) -- the flip fixes F",
          float(np.abs(np.array(rebuilt) - Fs).max()) < 1e-12,
          f"worst {float(np.abs(np.array(rebuilt) - Fs).max()):.2e} over the 7 shifts")

    # 7. Bernoulli through both engines
    al = Alpha([1, -2, -1], '1+sqrt2')
    R.set_alpha(2, 1, '1+sqrt2')
    b1 = Z.bern_phi_true(al, H)
    b2, rad = R.phi_fl(R.circ_bernoulli(1, Fr(1, 2)), hs, 100, 100)
    check("bern_phi_true == phi_fl(circ_bernoulli)", float(np.abs(b1 - b2).max()) < 1e-14,
          f"diff {float(np.abs(b1 - b2).max()):.2e}, R1a radius {max(rad):.2e}")

    # 8. Bernoulli(p) entropy is the binary entropy of p
    worst = 0.0
    for p in PGRID:
        pf = float(p)
        worst = max(worst, abs(R.circ_bernoulli(1, p).entropy()
                               + pf * math.log(pf) + (1 - pf) * math.log(1 - pf)))
    check("circ_bernoulli(1,p).entropy() = H(p) on the whole grid", worst < 1e-14,
          f"worst {worst:.2e}")

    # 9. Theorem 1 has teeth: deduplication raises the certified margin
    al = Alpha([1, -2, -1], '1+sqrt2')
    gains = []
    for Hh in (8, 64):
        eps = Z.orbit_phi_radius(al, Hh) / math.sqrt(Hh)
        ds = []
        for words in (lyndon(14), [list(w) for w in Z.necklaces(14)]):
            Vm = MG.vmat(np.array([Z.orbit_phi_true(al, list(w), Hh) for w in words]), Hh)
            ca = cache_of(Vm)
            Rv, lm = rmax_sub(Vm, ca['g'])
            ds.append(MG.margin(Vm, eps, Hh, lam=MG.refine(Vm, lm, 2), cache=ca)['delta'])
        gains.append((Hh, ds[0], ds[1], ds[0] / ds[1]))
    check("Lyndon beats R2b's necklaces at both ends of the ladder",
          all(g[3] > 1.0 for g in gains),
          "; ".join(f"H={g[0]}: {g[1]:.4e} vs {g[2]:.4e} ({g[3]:.3f}x)" for g in gains))

    # 10. the R2b regression, run exactly as `r2b_orbits.certify` runs it -- R2b's rows,
    #     R2b's (sqrt(H)-conservative) radius and R2b's own maximin LP
    al = Alpha([1, -2, -1], '1+sqrt2')
    Vm = MG.vmat(np.array([Z.orbit_phi_true(al, list(w), 32) for w in Z.necklaces(14)]
                          + [Z.bern_phi_true(al, 32)]), 32)      # R2b's pool ends with Bern
    d = MG.margin(Vm, Z.orbit_phi_radius(al, 32), 32)['delta']
    rec = [r for r in json.load(open(f'{BB}/r2b_orbits.json'))
           if r['name'] == '1+sqrt2' and r['H'] == 32 and r['qmax'] == 14][0]
    check("R2b's (1+sqrt2, H=32, q<=14) delta reproduced bit-for-bit",
          d == rec['delta'], f"here {d:.12e}, r2b_orbits.json {rec['delta']:.12e}")

    # 10a. and the two corrections R2d makes to it, priced separately
    ca = cache_of(Vm)
    Rv, lm = rmax_sub(Vm, ca['g'])
    d_eps = MG.margin(Vm, Z.orbit_phi_radius(al, 32) / math.sqrt(32), 32,
                      lam=MG.refine(Vm, lm, 2), cache=ca)['delta']
    Vl = MG.vmat(np.array([Z.orbit_phi_true(al, list(w), 32) for w in lyndon(14)]
                          + [Z.bern_phi_true(al, 32)]), 32)
    cl = cache_of(Vl)
    Rl, ll = rmax_sub(Vl, cl['g'])
    d_lyn = MG.margin(Vl, Z.orbit_phi_radius(al, 32) / math.sqrt(32), 32,
                      lam=MG.refine(Vl, ll, 2), cache=cl)['delta']
    check("R2d's two corrections to R2b's row are both improvements, and both tiny",
          d_lyn > d_eps > 0 and d_lyn / d < 1.1,
          f"R2b {d:.6e} -> per-coefficient eps {d_eps:.6e} -> Lyndon {d_lyn:.6e} "
          f"({d_lyn / d:.4f}x); the enclosure was never the binding term")

    # 11. `rmax_sub` agrees with R2a's own maximin LP where the latter still fits in RAM
    Vm = MG.vmat(np.array([Z.orbit_phi_true(al, list(w), 8) for w in lyndon(10)]), 8)
    ca = cache_of(Vm)
    R1, l1 = rmax_sub(Vm, ca['g'])
    l2, R2 = MG.weighted_maximin_lp(Vm, ca['g'])
    check("rmax_sub == weighted_maximin_lp (the m-free reformulation)",
          abs(R1 - R2) < 1e-9 * max(R1, R2), f"{R1:.9e} vs {R2:.9e}, m={Vm.shape[1]}")

    # 12. the entropy LP returns a probability vector that lands on 0
    _, Vm, E, eps, hmin, upper, n7, no = union('1+sqrt2', 16, 12)
    ca = cache_of(Vm)
    Rv, _ = rmax_sub(Vm, ca['g'])
    lm = ent_lp_w(Vm, E, ca['g'], Rv * 1e-3)
    check("entropy LP: simplex, zero residual, floor respected",
          lm is not None and abs(lm.sum() - 1) < 1e-9 and float(np.abs(Vm @ lm).max()) < 1e-9
          and float(np.min(lm - Rv * 1e-3 * ca['g'])) > -1e-12,
          f"|sum-1| {abs(lm.sum() - 1):.1e}, |V lam|_inf {float(np.abs(Vm @ lm).max()):.1e}")

    # 13. Theorem 3, the arithmetic half: the Bernoulli weight an orbit hull can absorb
    rows = []
    for Hh in (8, 32, 64):
        eps = Z.orbit_phi_radius(al, Hh) / math.sqrt(Hh)
        Vm = MG.vmat(np.array([Z.orbit_phi_true(al, list(w), Hh) for w in lyndon(14)]), Hh)
        ca = cache_of(Vm)
        Rv, lm = rmax_sub(Vm, ca['g'])
        dd = MG.margin(Vm, eps, Hh, lam=MG.refine(Vm, lm, 2), cache=ca)['delta']
        b = Z.bern_phi_true(al, Hh)
        nb = float(np.linalg.norm(np.concatenate([b.real, b.imag])))
        rows.append((Hh, dd / (dd + nb) * LOG2))
    check("orbits + Bernoulli cannot reach h_min at 1+sqrt2 (0.4407) at any H here",
          all(r[1] < 0.44068679350977147 for r in rows),
          "; ".join(f"H={r[0]}: h <= {r[1]:.4f}" for r in rows))

    # 14. the union's entropy vector is what the three blocks say it is, and `margin`
    #     reads it affinely: `h_mix = sum_j lam_j (h_j - slack)` to the last bit
    _, Vm2, E2, eps2, _, _, n7b, nob = union('root13', 8, 10)
    ca2 = cache_of(Vm2)
    Rv2, lm2 = rmax_sub(Vm2, ca2['g'])
    lm2 = np.maximum(MG.refine(Vm2, lm2, 2), 0.0)
    o2 = MG.margin(Vm2, eps2, 8, ent=E2, lam=lm2, cache=ca2)
    a2 = np.array([float(x) for x in o2['lam']]) / o2['D']
    check("union entropy vector: orbits 0, Bernoulli H(p), M7 from the pool file; affine",
          float(np.abs(E2[n7b:n7b + nob]).max()) == 0.0
          and abs(E2[-len(PGRID)] - LOG2) < 1e-15
          and abs(o2['h_mix'] - float(np.dot(a2, E2 - MG.ENT_SLACK))) < 1e-12,
          f"{n7b} M7 rows, {nob} orbits at h=0, {len(PGRID)} Bernoulli; "
          f"h_mix {o2['h_mix']:.9f}")

    # 15. no window anywhere in the orbit pool: eps is 1e-12, not 1e-2
    e12 = Z.orbit_phi_radius(al, 128) / math.sqrt(128)
    check("the orbit ladder carries no truncation to trust-rule",
          e12 < 1e-11, f"eps(H=128) = {e12:.2e} per coefficient, vs eps_L(12) = 1.01e-2")

    print(f"# self-checks: {_ok} ok, {_bad} failed\n")


def divisors(n):
    return [d for d in range(1, n + 1) if n % d == 0]


def mu(n):
    r, p = 1, 2
    while p * p <= n:
        if n % p == 0:
            n //= p
            if n % p == 0:
                return 0
            r = -r
        p += 1
    return -r if n > 1 else r


# ======================================================================================
def run(log=print):
    out = dict(flat=[], qsweep=[], ent=[])
    log("=" * 100)
    log("R2d: R1b's certificates and R2a's m(H) ladder on the periodic-orbit hull")
    log("=" * 100)

    log("\n# ladder A -- m(H) on the orbit hull alone (Lyndon words, no window, no pool loop)")
    for nm in UNITS:
        al = Alpha(UNITS[nm][0], nm)
        for H in (4, 8, 16, 32, 64, 128):
            out['flat'].append(flat(al, H, 14, log=log))
        json.dump(out, open(f'{BB}/r2d_hull.json', 'w'), indent=1)
    log("\n# ladder B -- the pool-augmentation loop, replaced by one integer")
    for H in (32, 64):
        for q in (8, 10, 12, 14, 16):
            out['qsweep'].append(flat(al, H, q, rho=False, log=log))
            json.dump(out, open(f'{BB}/r2d_hull.json', 'w'), indent=1)

    log("\n# ladder C -- R1b's entropy certificate: M7 alone, orbits alone, and the union")
    for nm in UNITS:
        for H in (4, 8, 16, 32, 64):
            if str(H) not in json.load(open(f'{BB}/{UNITS[nm][3]}'))['rows']:
                continue
            for tag in ('M7', 'orb+B', 'union'):
                out['ent'].append(entrow(nm, H, 16, tag, log=log))
            json.dump(out, open(f'{BB}/r2d_hull.json', 'w'), indent=1)
    log("\n#   the one row that needs a deeper pool: R1b's refutation, at q <= 18")
    out['ent'].append(entrow('golden2', 64, 18, 'union', log=log))
    json.dump(out, open(f'{BB}/r2d_hull.json', 'w'), indent=1)

    log("\n# and past the M7 ladder's reach, by raising q instead of running a loop")
    for H, q in ((256, 14), (256, 16), (256, 18), (512, 18)):
        out['flat'].append(flat(al, H, q, rho=False, log=log))
        json.dump(out, open(f'{BB}/r2d_hull.json', 'w'), indent=1)
    log(f"\n# wrote {BB}/r2d_hull.json")
    return 0


def extra(log=print):
    """The rows the main ladder leaves open: the two harder units past `q = 14`, and the
    reason `golden2` is the hard one -- at a reciprocal unit the flip is a symmetry of `F`,
    so reversal-paired Lyndon words carry the SAME `Phi` and the pool is half the size it
    looks."""
    out = json.load(open(f'{BB}/r2d_hull.json'))
    out['extra'] = []
    log("\n# ladder A, continued: the two units the q<=14 hull does not reach")
    for nm, H, q in (('1+sqrt2', 256, 14), ('1+sqrt2', 256, 16), ('1+sqrt2', 256, 18),
                     ('golden2', 128, 16), ('golden2', 128, 18), ('golden2', 256, 18)):
        out['extra'].append(flat(Alpha(UNITS[nm][0], nm), H, q, rho=False, log=log))
        json.dump(out, open(f'{BB}/r2d_hull.json', 'w'), indent=1)

    log("\n# rho at R2a's own search budget (starts=8, iters=30), so the two ladders are")
    log("#   comparable line for line.  rho^ = sqrt(2H) rho is the scale-free reading.")
    out['rho'] = []
    for nm in UNITS:
        al3 = Alpha(UNITS[nm][0], nm)
        for H in (4, 8, 16, 32, 64, 128):
            V, _ = orbit_rows(al3, H, 14)
            Vm3 = MG.vmat(V, H)
            t0 = time.time()
            ru, _ = MG.depth_upper(Vm3)
            out['rho'].append(dict(name=nm, H=H, q=14, rho=float(ru),
                                   rhohat=float(math.sqrt(2 * H) * ru)))
            log(f"  {nm:>9} H={H:<4d} q<=14  rho_up {ru:.6e}  sqrt(2H) rho "
                f"{math.sqrt(2 * H) * ru:.4f}  ({time.time() - t0:.0f}s)")
            json.dump(out, open(f'{BB}/r2d_hull.json', 'w'), indent=1)

    log("\n# ladder B redone at 1+sqrt2 WITH the geometric side: the hull is monotone in")
    log("#   q, the certificate is not -- Theorem 1' has the ceiling R <= 1/sum_j g_j.")
    out['qsweep2'] = []
    al2 = Alpha(UNITS['1+sqrt2'][0], '1+sqrt2')
    for H in (32, 64):
        for q in (8, 10, 12, 14, 16):
            out['qsweep2'].append(flat(al2, H, q, rho=True, log=log))
            json.dump(out, open(f'{BB}/r2d_hull.json', 'w'), indent=1)

    log("\n# why golden2 is the hard unit: distinct Phi points among the Lyndon words")
    out['degen'] = []
    for nm in UNITS:
        al = Alpha(UNITS[nm][0], nm)
        W = lyndon(12)
        key = set()
        for w in W:
            r = tuple(reversed(w))
            key.add(min(min(w[k:] + w[:k] for k in range(len(w))),
                        min(r[k:] + r[:k] for k in range(len(r)))))
        V = np.array([Z.orbit_phi_true(al, list(w), 8) for w in W])
        u = len({tuple(np.round(v.view(float), 10)) for v in V})
        out['degen'].append(dict(name=nm, lyndon=len(W), bracelets=len(key), distinct=u))
        log(f"  {nm:>9} q<=12: {len(W)} Lyndon words, {len(key)} up to reversal, "
            f"{u} distinct Phi at H=8"
            f"   {'-> reversal IS a symmetry, the pool is half of what it looks' if u == len(key) else ''}")
    json.dump(out, open(f'{BB}/r2d_hull.json', 'w'), indent=1)
    log(f"\n# wrote {BB}/r2d_hull.json")
    return 0


def table(log=print):
    """The three tables the note quotes, read back out of the recorded json."""
    d = json.load(open(f'{BB}/r2d_hull.json'))
    log("\n# ladder A, in the scale-free normalisation rho^ = sqrt(2H) rho.  R2a read")
    log("#   `rho ~ H^-0.95` off the M7 pool; on a pool with no window and no loop the")
    log("#   exponent is 1/2, i.e. rho^ is CONSTANT and the hull does not thin at all.")
    log(f"  {'alpha':>9} {'H':>5} {'q':>4} {'delta':>14} {'rho (upper)':>13} "
        f"{'sqrt(2H) rho':>13} {'gamma_d':>8} {'gamma_r':>8}")
    prev = {}
    for r in d['flat'] + d.get('extra', []):
        if not r.get('feasible'):
            log(f"  {r['name']:>9} {r['H']:5d} {r['q']:4d} {'not certified':>14}")
            continue
        rho, nm = r.get('rho', float('nan')), r['name']
        gd = gr = float('nan')
        p = prev.get((nm, r['q']))
        if p and r['H'] > p['H']:
            lr = math.log(r['H'] / p['H'])
            gd = -math.log(r['delta'] / p['delta']) / lr
            if p.get('rho') == p.get('rho') and rho == rho:
                gr = -math.log(rho / p['rho']) / lr
        log(f"  {nm:>9} {r['H']:5d} {r['q']:4d} {r['delta']:14.6e} {rho:13.6e} "
            f"{math.sqrt(2 * r['H']) * rho:13.6f} {gd:8.3f} {gr:8.3f}")
        prev[(nm, r['q'])] = r
    if 'rho' in d:
        log("\n#   rho again at R2a's own search budget (starts=8, iters=30)")
        log(f"  {'alpha':>9} {'H':>5} {'rho (upper)':>13} {'sqrt(2H) rho':>13}")
        for r in d['rho']:
            log(f"  {r['name']:>9} {r['H']:5d} {r['rho']:13.6e} {r['rhohat']:13.4f}")
    log("\n# the M7 ladder of note-1061-R2a.html sec 7, in the same normalisation")
    for H, rho in ((4, 1.188349e-01), (8, 7.456049e-02), (16, 3.919952e-02),
                   (32, 2.249992e-02), (64, 8.470519e-03)):
        log(f"  {'1+sqrt2':>9} {H:5d} {'M7':>4} {'':>14} {rho:13.6e} "
            f"{math.sqrt(2 * H) * rho:13.6f}")

    log("\n# ladder B -- the loop, replaced by one integer.  `rho` grows with `q` (the hull)")
    log("#   while `delta` need not (the certificate): Theorem 1' pays 1/sum_j g_j per row.")
    for key, nm in (('qsweep2', '1+sqrt2'), ('qsweep', 'root13')):
        if key not in d:
            continue
        log(f"  {'alpha':>9} {'H':>5} {'q':>4} {'m':>7} {'delta':>14} {'rho (upper)':>13}")
        for r in d[key]:
            log(f"  {r.get('name', nm):>9} {r['H']:5d} {r['q']:4d} {r['m']:7d} "
                f"{(r['delta'] if r.get('feasible') else float('nan')):14.6e} "
                f"{r.get('rho', float('nan')):13.6e}")

    log("\n# ladder C -- E_H from below, by pool")
    log(f"  {'alpha':>9} {'H':>5} {'pool':>6} {'q':>4} {'m':>7} {'delta':>12} "
        f"{'E_H >=':>10} {'h_min':>9} {'upper':>9}  verdict")
    for r in d['ent']:
        b = r.get('best')
        if not b:
            log(f"  {r['name']:>9} {r['H']:5d} {r['pool']:>6} {r['q']:4d} {r['m']:7d} "
                f"{'no certificate':>12}")
            continue
        ok = b['h_lower'] > r['h_min']
        log(f"  {r['name']:>9} {r['H']:5d} {r['pool']:>6} {r['q']:4d} {r['m']:7d} "
            f"{b['delta']:12.4e} {b['h_lower']:10.6f} {r['h_min']:9.6f} "
            f"{r['upper']:9.6f}  "
            f"{'H_flat,H_ent > %d' % r['H'] if ok else 'H_flat > %d only' % r['H']}")
    return 0


def main():
    if '--table' in sys.argv:
        return table()
    if '--extra' in sys.argv:
        return extra()
    if '--one' in sys.argv:
        i = sys.argv.index('--one')
        entrow(sys.argv[i + 1], int(sys.argv[i + 2]), int(sys.argv[i + 3]))
        return 0
    if '--checks' in sys.argv or len(sys.argv) == 1:
        selfchecks()
    if '--checks' in sys.argv:
        return 0 if _bad == 0 else 1
    run()
    return 0 if _bad == 0 else 1


if __name__ == '__main__':
    sys.exit(main())
