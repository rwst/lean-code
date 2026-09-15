#!/usr/bin/env python3
# (C) 2026 Ralf Stephan, in collaboration with Claude Code.
# CC0 1.0 Universal (public domain dedication).
"""R2a, row 1 of the dichotomy: where does the constrained pressure go negative?

sec 6.3 of `plan-BB61-counterexample.html` reads three behaviours off the conditioned
margin `m(H)`, and the first is a proof: `m(H_0) = 0` with infeasibility certified means
`K_{H_0} = empty`, hence (M7 Cor. 2) 10.61 at `alpha`.  This file tests that row directly,
without any pool at all, on the following one-line remark.

    For `mu in K_H` every `Phi_h(mu)` vanishes for `h <= H`, so `int psi_a dmu = 0` for
    every multiplier vector `a`, and therefore `h(mu) = h(mu) + int psi_a dmu <= P(psi_a)`.
    Taking the supremum, `E_H <= P(psi_a)` FOR EVERY `a`.  Since `h >= 0`,

        P(psi_a) < 0  for a single `a`   ==>   E_H < 0   ==>   K_H = empty.       (F)

That is M7 Thm 5's own inequality with the threshold moved from `h_min` to `0`: `cert
< h_min` bounds `H_ent`, `cert < 0` bounds `H_flat`, and the two use the same machine.
`Window.pressure_ub` (Collatz-Wielandt, eigensolver-independent) and `delta_bound`
(`2 pi sum_h h|a_h| eps`, M3's truncation slack) make (F) a certificate:

    pressure_ub(a) < 0            ==>  K_H(F~) = empty   (the WINDOW's observable)
    pressure_ub(a) + delta(a) < 0 ==>  K_H(F)  = empty   ==>  10.61 holds at alpha.

`--sweep` walks `H` upward at fixed `L` and records both; `--ray` takes the direction the
optimiser runs off along and asks what it is worth at finer windows.  The answer to the
second is what decides G-2, so it is the point of the file.

Usage:  python3 r2a_flat.py                  # the recorded run: sweep + pin + ray
        python3 r2a_flat.py --sweep 12 14 16
"""
import json
import math
import os
import sys
import time
import warnings

import numpy as np

sys.path.insert(0, '/home/ralf/math/lean-code/BB61')
from m0_engine import Alpha
from m3_entropy import Window, delta_bound, h_min, minimize_pressure
from m4_fourier import best_window, pad

warnings.filterwarnings('ignore')
BB = '/home/ralf/math/lean-code/BB61'
CAP = 60.0
HS = (32, 64, 96, 112, 128, 160, 192, 224, 256, 320, 384, 448, 512, 640)


def windows(A, B, name, Ls):
    al = Alpha([1, -A, -B], name)
    out = {}
    for L in Ls:
        N, M, e = best_window(al, L)
        out[L] = (Window(al, N, M), float(e), N, M)
    return al, out


def one(W, H, x0=None, cap=CAP):
    """Minimise the pressure over `H` modes and certify the value that comes out."""
    W.set_modes(list(range(1, H + 1)))
    t0 = time.time()
    P, xs, flat, delta = minimize_pressure(W, x0=x0, cap=cap)
    a = np.asarray(xs)[:H] + 1j * np.asarray(xs)[H:]
    ub = W.pressure_ub(a)
    dl = delta_bound(W, a)
    ls = W.last_solve
    return dict(H=H, P=float(P), ub=float(ub), delta=float(dl), cert=float(ub + dl),
                box=bool(ls['box_active']), xmax=float(ls['xmax']),
                S1=float(np.sum(W.modes * np.abs(a))), x=[float(v) for v in xs],
                secs=time.time() - t0)


def gone(r):
    """The window's `K_H` has emptied: the minimiser has run to the box.

    `pressure_ub < 0` is the certificate (Remark F); it needs a good Collatz-Wielandt
    iterate, and a cold one at a nearly degenerate operator can be far too weak to see it.
    The runaway itself -- `P < 0`, or the multiplier pinned against `cap` -- is the robust
    indicator, and `--ray` then certifies one point of it."""
    return r['P'] < 0 or r['ub'] < 0 or r['xmax'] > 0.9 * CAP


def sweep(A, B, name, Ls, Hs=HS, log=print, stop_at_empty=True):
    """`H` upward at each `L`, stopping at the first `H` where the window's `K_H` empties."""
    al, wins = windows(A, B, name, Ls)
    rec = {}
    for L in Ls:
        W, e, N, M = wins[L]
        log(f"\n# L={L}  window ({N},{M})  eps={e:.4e}   alpha={float(al.alpha):.9f}"
            f"   h_min={h_min(al):.6f}")
        log(f"  {'H':>5} {'P':>13} {'pressure_ub':>13} {'delta':>11} {'cert':>13} "
            f"{'H*eps':>7} {'box':>5} {'xmax':>8}")
        rows, xp, Hp = [], None, 0
        for H in Hs:
            try:
                r = one(W, H, x0=pad(xp, Hp, H))
            except Exception as exc:          # the bundle LP chokes once the box is active
                log(f"  {H:5d}   solver gave up ({type(exc).__name__}); "
                    f"L={L} stops here")
                break
            r['L'], r['eps'], r['Heps'] = L, e, H * e
            rows.append(r)
            log(f"  {H:5d} {r['P']:13.6f} {r['ub']:13.6f} {r['delta']:11.3e} "
                f"{r['cert']:13.4e} {r['Heps']:7.3f} {str(r['box']):>5} "
                f"{r['xmax']:8.3f}"
                + ("   <-- K_H(window) EMPTY, certified" if r['ub'] < 0 else
                   "   <-- runaway: the constrained pressure is unbounded below"
                   if gone(r) else ""))
            if gone(r) and stop_at_empty:
                break
            if r['P'] > 0:
                xp, Hp = np.asarray(r['x']), H
        rec[L] = rows
    return rec


def pin(A, B, name, L, lo, hi, log=print):
    """Bisect for `H_0(L) = min{H : pressure_ub < 0}`, the ceiling of the pool ladder."""
    al, wins = windows(A, B, name, [L])
    W, e, N, M = wins[L]
    xp, Hp = None, 0
    while hi - lo > 1:
        mid = (lo + hi) // 2
        r = one(W, mid, x0=pad(xp, Hp, mid))
        log(f"    L={L} H={mid:<5} P {r['P']:12.6f}  pressure_ub {r['ub']:12.6f}  "
            f"xmax {r['xmax']:7.3f}   {'EMPTY' if gone(r) else 'ok'}")
        if gone(r):
            hi = mid
        else:
            lo, xp, Hp = mid, np.asarray(r['x']), mid
    return hi, e


def ray(A, B, name, L_from, H, Ls, cs=(0.05, 0.1, 0.2, 0.4, 0.7, 1.0), log=print):
    """Is the runaway direction real, or is it the window's?

    At `(L_from, H)` past the threshold the optimiser leaves along some `a`.  Evaluate the
    SAME `a` (and scalings of it) at finer windows.  Two readings:

      * `pressure_ub(c a)` at each `L`.  Negative means (F) fires for that window's `F~`;
        if it is negative only at the window that produced `a`, the runaway is truncation.
      * the entropy-free criterion of sec 6.3, along this one ray.  With
        `kappa = -max_mu int psi_ahat dmu` and `tau = 2 pi sum_h h|ahat_h| eps_L`,
        `max_mu int psi^true_ahat dmu <= -kappa + tau`, so `kappa > tau` would prove
        `K_H(F) = empty` for the true `F`.  `P(c) <= log 2 + c max int psi` gives the
        rigorous lower bound `kappa >= -pressure_ub(c ahat)/c`, and the bracket closes at
        rate `log 2 / c`."""
    al, wins = windows(A, B, name, sorted(set(Ls) | {L_from}))
    W0 = wins[L_from][0]
    r0 = one(W0, H)
    x = np.asarray(r0['x'])
    a0 = x[:H] + 1j * x[H:]
    nrm = float(np.linalg.norm(x))
    ah = a0 / nrm
    log(f"\n# the runaway at L={L_from}, H={H}: pressure_ub {r0['ub']:.4f}, "
        f"delta {r0['delta']:.3e}, cert {r0['cert']:.4e}, "
        f"|a|_2 {nrm:.3f}, |a|_inf {float(np.abs(a0).max()):.3f}")
    log("  the SAME multiplier vector, re-priced at finer windows (continuation in c,")
    log("  so each Collatz-Wielandt bound is warm-started at the previous one):")
    log(f"  {'L':>3} {'eps':>10} " + " ".join(f"{'P_ub(%gt)' % c:>12}" for c in cs) +
        f" {'tau':>10} {'kappa>=':>10} {'kappa/tau':>10}")
    out = []
    for L in Ls:
        W, e, N, M = wins[L]
        W.set_modes(list(range(1, H + 1)))
        W.reset_iterates()
        tau = float(2 * np.pi * np.sum(W.modes * np.abs(ah)) * W.eps)
        ubs, kap = [], float('-inf')
        for c in cs:
            v = float(W.pressure_ub(c * a0))
            ubs.append(v)
            if np.isfinite(v):
                kap = max(kap, -v / (c * nrm))     # P(c) <= log2 + c max int psi
        out.append(dict(L=L, eps=e, tau=tau, ub=ubs, kappa=kap,
                        ratio=(kap / tau if tau else None)))
        log(f"  {L:3d} {e:10.3e} " + " ".join(f"{v:12.4f}" for v in ubs) +
            f" {tau:10.4f} {kap:10.5f} {kap / tau:10.5f}")
    return out


def run():
    A, B, name = 2, 1, '1+sqrt2'
    out = {}
    print("=" * 88)
    print("R2a / row 1:  P(psi_a) < 0 proves K_H = empty.  Where does it happen, and to whom?")
    print("=" * 88)
    out['sweep'] = {str(k): v for k, v in
                    sweep(A, B, name, [12, 14, 16], Hs=HS).items()}
    print("\n# pinning H_0(L) = min{H : pressure_ub < 0}   (the ceiling of the pool ladder)")
    pins = {}
    for L, rows in out['sweep'].items():
        L = int(L)
        if not rows or not gone(rows[-1]):
            print(f"  H_0({L}) > {rows[-1]['H']}   (the sweep did not reach it)")
            continue
        hi = rows[-1]['H']
        lo = rows[-2]['H'] if len(rows) > 1 else 1
        H0, e = pin(A, B, name, L, lo, hi)
        pins[L] = dict(H0=H0, eps=e, prod=H0 * e)
        print(f"  H_0({L}) = {H0}   eps = {e:.4e}   H_0 * eps = {H0 * e:.4f}")
    if len(pins) > 1:
        pr = [v['prod'] for v in pins.values()]
        print(f"  H_0 * eps over the pinned L: {min(pr):.4f} .. {max(pr):.4f} "
              f"-- the threshold is the TRUNCATION SCALE, not a property of F")
    out['pin'] = {str(k): v for k, v in pins.items()}
    out['ray'] = ray(A, B, name, 12, 128, [12, 14, 16, 18])
    with open(f'{BB}/r2a_flat.json', 'w') as f:
        json.dump(out, f, indent=1)
    print(f"\n# wrote {BB}/r2a_flat.json")
    return 0


def main():
    if '--sweep' in sys.argv:
        i = sys.argv.index('--sweep')
        sweep(2, 1, '1+sqrt2', [int(x) for x in sys.argv[i + 1:]])
        return 0
    if '--ray' in sys.argv:
        i = sys.argv.index('--ray')
        ray(2, 1, '1+sqrt2', int(sys.argv[i + 1]), int(sys.argv[i + 2]),
            [int(x) for x in sys.argv[i + 3:]])
        return 0
    return run()


if __name__ == '__main__':
    sys.exit(main())
