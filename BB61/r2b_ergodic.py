#!/usr/bin/env python3
# (C) 2026 Ralf Stephan, in collaboration with Claude Code.
# CC0 1.0 Universal (public domain dedication).
"""R2b of `plan-BB61-counterexample.html` sec 6.3 -- the entropy-free dual minimiser.

sec 6.3's catch, in the plan's own words: `0 not in conv{Phi(nu_j)}` for the pool at hand
proves nothing, and reaching `K_H = empty` needs the dual object -- a mean-zero `G` of
degree `<= H` with `min_mu int G(F) dmu > 0` (M3 Thm 9), an ergodic-optimisation minimum
with no entropy in it.  This file builds that minimiser.  R2a supplied the criterion in
evaluable form and the finding that the pressure optimiser's own direction fails it by
`10^3`; the machine below does not evaluate a direction, it finds the best one.

The observable
--------------
For `mu` shift-invariant put `Phi_h(mu) = int e(h F) dmu` and

    nu_H  :=  min_{mu in M(sigma)}  max_{1 <= h <= H}  |Phi_h(mu)| / h .        (1)

THEOREM 1.  `nu_H` is non-decreasing in `H`; `nu_H > 0` if and only if `K_H = empty`; and
`nu_H > 0` for a single `H` proves 10.61 at `alpha`.

    The max is over more terms as `H` grows, so `nu` is non-decreasing.  `M(sigma)` is
    weak-* compact and `mu -> max_h |Phi_h(mu)|/h` is continuous, so the min is attained:
    `nu_H = 0` iff some invariant `mu` has `Phi_h(mu) = 0` for all `h <= H`, i.e. iff
    `K_H != empty`.  And `K_H = empty` forbids `F_* mu = Leb` (which would kill every
    `Phi_h`), which is 10.61 at `alpha` -- with no entropy, no `h_min`, no pressure and no
    Ledrappier-Young.  QED

The weights `1/h` are not cosmetic: they are exactly the shape of the truncation error,
which is what makes (1) the right observable rather than one of a family (Thm 3).

Why it is computable at all
---------------------------
Truncate `F` to the window `(-N .. M-1)`, `L = N+M`, `eps_L = ||F - F~||_inf`.  Then
`psi_a(F~)` is a function of the `(L+1)`-block alone, so it is a weight on the edges of
the order-`L` de Bruijn graph -- node `u` an `L`-block, edge `e` an `(L+1)`-block with
`tail(e) = e >> 1` and `head(e) = e mod 2^L`, which is exactly the graph
`m3_entropy.Window`'s transfer operator already runs on.

THEOREM 2 (the machine).  For an edge weight `w`,

    max_{mu in M(sigma)} int psi_a(F~) dmu  =  max over cycles of the mean of `w`,      (2)

and for any node potential `p`,  `lambda <= max_e (w_e + p_head(e) - p_tail(e))`,  with
equality for the max-plus eigenvector.  The max-plus power iteration

    v'(u) = max_{j in {0,1}} ( w(2u+j) + v((2u+j) mod 2^L) )                            (3)

brackets it from both sides at every step:  `min_u (v'-v) <= lambda <= max_u (v'-v)`.

    (2): a shift-invariant measure induces an edge-frequency vector obeying conservation,
    i.e. a circulation, and `int psi_a(F~) dmu = <w, circulation>`; conversely every
    circulation is realised by a Markov measure.  The circulation polytope's vertices are
    the normalised simple cycles, and a linear functional is maximised at a vertex.
    The upper bound: summing `w_e <= lambda + p_tail - p_head` around a cycle telescopes.
    The lower bound: if every node has an outgoing edge with `w_e + v(head) - v(tail) >= c`
    then following those edges closes a cycle of mean `>= c`.  QED

This is the SAME Collatz-Wielandt argument that makes `Window.pressure_ub` sound, in the
max-plus semiring instead of the usual one -- and it is sound for whatever vector the
iteration produced, warm starts included.  `howard()` then runs policy iteration from the
iterate and terminates at the exact `lambda`.

The transfer to the true `F`, and the criterion
-----------------------------------------------
THEOREM 3.  With `tau(a) = 2 pi (sum_h h |a_h|) eps_L` (`m3_entropy.delta_bound`) and
`kappa(a) = - max_mu int psi_a(F~) dmu`,

    kappa(a) > tau(a)   ==>   K_H(F) = empty   ==>   10.61 holds at alpha.             (4)

    `|e(hF) - e(hF~)| <= 2 pi h eps_L` pointwise, so `|int psi_a(F) dmu - int psi_a(F~)
    dmu| <= tau(a)` for every `mu`; hence `max_mu int psi_a(F) dmu <= -kappa + tau < 0`,
    while every `mu in K_H` has `int psi_a(F) dmu = Re sum_h a_h Phi_h(mu) = 0`.  QED

Both `kappa` and `tau` are homogeneous of degree one in `a`, so `kappa/tau` depends only on
the direction and the criterion is a statement about the unit sphere of `sum_h h|a_h|`.
On that sphere,

    max_a kappa(a)  =  nu~_H  :=  min_{mu} max_h |Phi~_h(mu)| / h ,                     (5)

by Sion's minimax on the bilinear pairing between the weighted-`l^1` ball and the rotation
set `R~ = {Phi~(mu)}` -- the dual of `sum_h h|a_h|` is `max_h |p_h|/h`.  So the SEARCH for
the best direction and the OBSERVABLE (1) are one convex problem, the criterion reads

    nu~_H  >  2 pi eps_L ,                                                              (6)

and `|nu_H - nu~_H| <= 2 pi eps_L` brackets the true observable from a window computation.

What this predicts before it is run
-----------------------------------
R1b proved `K_64(F) != empty` at `1+sqrt2` (18 certificates, true `Phi` to `1e-13`), so
`nu_64 = 0` and, by the bracket, `nu~_64 <= 2 pi eps_L` at EVERY window: (6) provably
cannot fire at `H <= 64`, however deep the window.  The machine has to be run past R1b's
ceiling, and there the trust rule bites in a sharper form than R2a's: mode `h` carries
information only while `2 pi h eps_L < 1`, i.e. `H < 1/(2 pi eps_L)` -- 15.8 at `L=12`,
38 at `L=14`, 91 at `L=16`, 221 at `L=18`.  That factor `2 pi` is the difference between
R2a's measured `H eps_L <~ 0.9` and what the dual criterion can actually use.

Finally, `int psi_a dmu <= h(mu) + int psi_a dmu <= P(psi_a)`, so `beta <= P` and (4)
fires no later than R2a's row-1 pressure test; the gap between them is exactly the entropy
the pressure route pays for and this one does not.

Usage
-----
    python3 r2b_ergodic.py --selfcheck
    python3 r2b_ergodic.py --ladder                # the recorded run
    python3 r2b_ergodic.py --nu L H [rounds]
"""
import json
import math
import os
import sys
import time
import warnings

import numpy as np
from scipy.optimize import linprog

sys.path.insert(0, '/home/ralf/math/lean-code/BB61')
import r1a_enclose as R
from m0_engine import Alpha
from m3_entropy import Window, delta_bound, h_min
from m4_fourier import best_window

warnings.filterwarnings('ignore')
BB = '/home/ralf/math/lean-code/BB61'
U = 2.0 ** -53


# ======================================================================================
# the graph
# ======================================================================================
def edges(L):
    """`(e0, e1, h0, h1)`: the two edges out of each `L`-block and where they land.

    Edge `e` is the `(L+1)`-block; `tail(e) = e >> 1`, `head(e) = e mod 2^L`.  This is
    `m3_entropy.Window`'s own indexing -- its operator reads
    `r'[2v+j] = w[2v+j] r[v] + w[2^L + 2v+j] r[v + 2^(L-1)]`, i.e. the edge index is the
    full `(L+1)`-block and the state index is the block with one bit dropped.
    """
    n, mask = 1 << L, (1 << L) - 1
    e0 = np.arange(n, dtype=np.int64) << 1
    e1 = e0 | 1
    return e0, e1, e0 & mask, e1 & mask


_EDGE_CACHE = {}


def graph(L):
    if L not in _EDGE_CACHE:
        _EDGE_CACHE[L] = edges(L)
    return _EDGE_CACHE[L]


# ======================================================================================
# the oracle:  max cycle mean
# ======================================================================================
def tropical(w, L, v=None, iters=4000, tol=1e-13):
    """Max-plus power iteration (3).  Returns `(lo, hi, v, best_it)`.

    `hi` is a RIGOROUS upper bound on the max cycle mean of `w` and `lo` a rigorous lower
    bound, for whatever `v` the iteration happens to hold -- Theorem 2.  Both are tracked
    as running best over the iterations, so a critical graph of period `> 1` (which makes
    `v' - v` cycle rather than converge) costs tightness, never soundness.
    """
    e0, e1, h0, h1 = graph(L)
    n = 1 << L
    v = np.zeros(n) if v is None or v.shape != (n,) or not np.isfinite(v).all() \
        else np.array(v, dtype=float)
    w0, w1 = w[e0], w[e1]
    lo, hi, best = -np.inf, np.inf, 0
    for it in range(iters):
        vn = np.maximum(w0 + v[h0], w1 + v[h1])
        d = vn - v
        a, b = float(d.min()), float(d.max())
        if b < hi:
            hi, best = b, it
        lo = max(lo, a)
        v = vn - vn.max()
        if b - a <= tol:
            break
    return lo, hi, v, best


def certify(w, L, v):
    """One pass: `max_e (w_e + v[head] - v[tail])`, with the float64 slack added on.

    Every term is two additions of quantities bounded by `W = max|w|` and `V = max|v|`,
    so the computed value is within `4 u (W + 2V)` of the exact one; the guard is added,
    never subtracted, so the return value is an upper bound on the exact certificate,
    which is itself an upper bound on the max cycle mean (Theorem 2).
    """
    e0, e1, h0, h1 = graph(L)
    r = np.maximum(w[e0] + v[h0], w[e1] + v[h1]) - v
    g = 4 * U * (float(np.max(np.abs(w))) + 2 * float(np.max(np.abs(v))))
    return float(r.max()) + g


def _eval_policy(succ, sw, n):
    """Gain and bias of a policy on a functional graph, exactly as policy iteration wants.

    Every node has out-degree one, so following `succ` from any node walks a tail into a
    cycle.  On the cycle the gain is the cycle mean and the bias solves
    `b[u] = sw[u] - g + b[succ[u]]` with one node pinned to zero; on the tail the gain is
    inherited and the same recursion runs backwards.
    """
    g = np.zeros(n)
    bi = np.zeros(n)
    color = bytearray(n)
    for s in range(n):
        if color[s]:
            continue
        path = []
        pos = {}
        v = s
        while color[v] == 0:
            color[v] = 1
            pos[v] = len(path)
            path.append(v)
            v = succ[v]
        if color[v] == 1:                       # a new cycle
            i = pos[v]
            cyc = path[i:]
            m = len(cyc)
            gm = math.fsum(sw[u] for u in cyc) / m
            g[cyc[0]] = gm
            bi[cyc[0]] = 0.0
            acc = 0.0
            for k in range(m - 1, 0, -1):
                acc += sw[cyc[k]] - gm
                bi[cyc[k]] = acc
                g[cyc[k]] = gm
            tail = path[:i]
        else:                                   # ran into settled ground
            tail = path
        for u in reversed(tail):
            t = succ[u]
            g[u] = g[t]
            bi[u] = sw[u] - g[t] + bi[t]
        for u in path:
            color[u] = 2
    return g, bi


def howard(w, L, pol=None, maxit=60):
    """Policy iteration for the max cycle mean.  Exact, and it terminates.

    Improvement is lexicographic in `(gain, bias)`, which is what handles a policy whose
    functional graph has several cycles of different means.  Returns
    `(lam, pol, v, iters)` with `v` the bias, so `certify(w, L, v)` prices the answer.
    """
    e0, e1, h0, h1 = graph(L)
    n = 1 << L
    w0, w1 = w[e0], w[e1]
    if pol is None or pol.shape != (n,):
        pol = (w1 > w0).astype(np.int8)
    for it in range(maxit):
        succ = np.where(pol == 1, h1, h0)
        sw = np.where(pol == 1, w1, w0)
        g, bi = _eval_policy(succ, sw, n)
        q0 = g[h0]
        q1 = g[h1]
        b0 = w0 - q0 + bi[h0]
        b1 = w1 - q1 + bi[h1]
        # lexicographic argmax over the two children, with a tolerance so that float
        # noise cannot make the policy oscillate for ever
        tg = 1e-13 * (1.0 + np.abs(q0) + np.abs(q1))
        tb = 1e-11 * (1.0 + np.abs(b0) + np.abs(b1))
        better = (q1 > q0 + tg) | ((np.abs(q1 - q0) <= tg) & (b1 > b0 + tb))
        worse = (q0 > q1 + tg) | ((np.abs(q1 - q0) <= tg) & (b0 > b1 + tb))
        new = np.where(better, 1, np.where(worse, 0, pol)).astype(np.int8)
        if np.array_equal(new, pol):
            return float(g.max()), pol, bi, it + 1
        pol = new
    return float(g.max()), pol, bi, maxit


def cycle_of(pol, L, start=0):
    """A cycle of the policy's functional graph, as the list of its edges."""
    _, _, h0, h1 = graph(L)
    seen = {}
    u = int(start)
    order = []
    while u not in seen:
        seen[u] = len(order)
        order.append(u)
        u = int(h1[u] if pol[u] else h0[u])
    cyc = order[seen[u]:]
    return [2 * v + int(pol[v]) for v in cyc]


def maxmean(W, a, v=None, pol=None, exact=True, iters=4000):
    """Rigorous bracket on `max_mu int psi_a(F~) dmu`, and a maximising cycle.

    `hi` is the certificate the criterion (4) reads; `lo` is what a concrete measure
    achieves, so `lo <= lambda <= hi` and the width is the machine's own honesty.
    """
    L = W.L
    w = W.weights(a)
    lo, hi, v, _ = tropical(w, L, v=v, iters=iters)
    hi = min(hi, certify(w, L, v))
    if exact:
        lam, pol, bi, nit = howard(w, L, pol=pol)
        hi = min(hi, certify(w, L, bi))
        lo = max(lo, lam - 1e-12)
        v = bi
    else:
        e0, e1, h0, h1 = graph(L)
        pol = ((w[e1] + v[h1]) > (w[e0] + v[h0])).astype(np.int8)
        lam = 0.5 * (lo + hi)
    cyc = cycle_of(pol, L)
    mean = float(np.mean(w[cyc]))
    lo = max(lo, mean - 1e-14 * (1 + abs(mean)))
    return dict(lo=lo, hi=hi, lam=lam, v=v, pol=pol, cycle=cyc, cycle_mean=mean)


def karp(w, L):
    """Karp's exact O(V E) minimum/maximum mean cycle, for the self-checks only."""
    e0, e1, h0, h1 = graph(L)
    n = 1 << L
    NEG = -np.inf
    d = np.full((n + 1, n), NEG)
    d[0, 0] = 0.0
    for k in range(1, n + 1):
        cur = d[k - 1]
        nxt = np.full(n, NEG)
        for e, hd in ((e0, h0), (e1, h1)):
            cand = cur + w[e]                       # tail = node index
            np.maximum.at(nxt, hd, cand)
        d[k] = nxt
    best = NEG
    for v in range(n):
        if d[n, v] == NEG:
            continue
        m = np.inf
        for k in range(n):
            if d[k, v] == NEG:                      # (d_n - d_k) = +inf: no constraint
                continue
            m = min(m, (d[n, v] - d[k, v]) / (n - k))
        best = max(best, m)
    return float(best)


# ======================================================================================
# points of the rotation set:  cycles and circulations
# ======================================================================================
def phi_cycle(W, cyc):
    """`Phi~_h` of the periodic measure on a cycle, for the window's `F~`."""
    F = W.F[np.asarray(cyc, dtype=np.int64)]
    md = W.modes.astype(float)
    out = np.zeros(md.size, dtype=complex)
    for s in range(0, F.size, 1 << 15):
        blk = F[s:s + (1 << 15)]
        out += np.exp(2j * np.pi * np.outer(md, blk)).sum(axis=1)
    return out / F.size


def phi_circ(W, p):
    """`Phi~_h` of an edge-weight vector `p` (a circulation), for the window's `F~`."""
    p = np.asarray(p, dtype=float)
    md = W.modes.astype(float)
    out = np.zeros(md.size, dtype=complex)
    nz = np.nonzero(p)[0]
    for s in range(0, nz.size, 1 << 15):
        j = nz[s:s + (1 << 15)]
        out += np.exp(2j * np.pi * np.outer(md, W.F[j])) @ p[j]
    return out / p.sum()


def word_cycle(L, word):
    """The cycle of `(L+1)`-blocks of a cyclic 0/1 word -- `r1a_enclose.circ_from_word`'s
    encoding, so that a seed cut here and a pool member there are the same object.

    CONVENTION.  `word[i]` lands in the block's MOST significant bit, while `Window.wt`
    indexes bit `b` by the position `b - N`; so the window reads the word in the opposite
    direction from the series of `orbit_F_true`, and `phi_orbit(lw, w)` is the true
    `Phi` of the orbit of the REVERSED word (up to a cyclic shift, which the orbit
    average kills).  Nothing downstream cares: reversal permutes the necklaces among
    themselves, so the hull of all periodic orbits of period `<= q` -- which is the only
    thing any result here uses -- is the same set either way, and Bernoulli is symmetric.
    The self-checks pin both halves of this."""
    T = len(word)
    out = []
    for i in range(T):
        v = 0
        for j in range(L + 1):
            v = (v << 1) | word[(i + j) % T]
        out.append(v)
    return out


def seed_cuts(W, qmax=8):
    """Bernoulli(1/2) and every periodic orbit of period `<= qmax`, as points of `R~`.

    Cheap, deterministic, and it puts the flattest measure anyone knows about together
    with the whole low-period skeleton into the hull before the oracle is asked for
    anything.  Any point of `R~` is a legitimate member -- the hull is what matters, not
    whether its generators are vertices."""
    L = W.L
    seen = set()
    out = [phi_circ(W, np.full(1 << (L + 1), 2.0 ** -(L + 1)))]   # Bernoulli(1/2)
    for q in range(1, qmax + 1):
        for m in range(1 << q):
            word = [(m >> (q - 1 - i)) & 1 for i in range(q)]
            key = min(tuple(word[k:] + word[:k]) for k in range(q))
            if key in seen:
                continue
            seen.add(key)
            out.append(phi_cycle(W, word_cycle(L, list(key))))
    return out


# ======================================================================================
# the direction search:  Frank-Wolfe against the truncation polydisc
# ======================================================================================
# Scaled coordinates.  Put `p^_h = Phi~_h / h`; the rotation set becomes
# `R^ = {Phi~(mu)/h}` and, writing `a^_h = h a_h`, the pairing is unchanged while
# `sum_h h|a_h| = sum_h |a^_h|`.  So (6) reads
#
#     nu~_H = min_{p^ in R^} max_h |p^_h|  >  r := 2 pi eps_L ,
#
# i.e. `R^` misses the polydisc `D_r = {|p^_h| <= r for every h}`.  That is decided by a
# single smooth convex programme,
#
#     minimise  f(p^) = 1/2 dist_2(p^, D_r)^2   over   p^ in R^ ,                       (7)
#
# whose value is zero exactly when the criterion cannot fire.  `r = 0` collapses `D_r` to
# the origin and (7) decides `K_H(F~) = empty` instead -- the window's own flatness, with
# no truncation charged.  The gradient is the componentwise soft-threshold, the linear
# minimisation oracle is `maxmean` (Theorem 2), and the vertex it returns is a periodic
# orbit, so every iterate is an explicit finite convex combination of periodic measures.
def pair(a, phi):
    """`int psi_a(F~) dmu = Re sum_h a_h Phi~_h(mu)` -- the pairing everything runs on."""
    return float(np.real(np.sum(np.asarray(a) * np.asarray(phi))))


def shrink(p, r):
    """`p - proj_{D_r}(p)`, componentwise: the gradient of `1/2 dist_2(., D_r)^2`."""
    m = np.abs(p)
    if r <= 0:
        return p.copy()
    f = np.where(m > r, 1.0 - r / np.where(m > 0, m, 1.0), 0.0)
    return p * f


def fval(p, r):
    m = np.abs(p)
    d = np.maximum(m - r, 0.0)
    return 0.5 * float(np.dot(d, d))


def _line(p, d, r, n=60):
    """Exact-enough 1-D minimisation of `f(p + g d)` on `[0, gmax]` (golden section)."""
    lo, hi = 0.0, 1.0
    gr = (math.sqrt(5) - 1) / 2
    x1, x2 = hi - gr * (hi - lo), lo + gr * (hi - lo)
    f1, f2 = fval(p + x1 * d, r), fval(p + x2 * d, r)
    for _ in range(n):
        if f1 < f2:
            hi, x2, f2 = x2, x1, f1
            x1 = hi - gr * (hi - lo)
            f1 = fval(p + x1 * d, r)
        else:
            lo, x1, f1 = x1, x2, f2
            x2 = lo + gr * (hi - lo)
            f2 = fval(p + x2 * d, r)
        if hi - lo < 1e-14:
            break
    return 0.5 * (lo + hi)


def fw_fixed(V, r, iters=400):
    """Min-`f` over the convex hull of a FIXED vertex list -- the warm start."""
    P = np.asarray(V, dtype=complex)
    k = P.shape[0]
    w = np.zeros(k)
    w[int(np.argmin([fval(v, r) for v in P]))] = 1.0
    p = w @ P
    for _ in range(iters):
        g = shrink(p, r)
        if not np.any(g):
            break
        sc = np.real(P @ np.conj(g))
        j = int(np.argmin(sc))
        ja = int(np.argmax(np.where(w > 0, sc, -np.inf)))
        d = P[j] - P[ja]
        if not np.any(d):
            break
        gam = min(w[ja], _line(p, d, r) * 1.0)
        gam = min(gam, w[ja])
        if gam <= 1e-16:
            break
        w[j] += gam
        w[ja] -= gam
        p = w @ P
    return p, w


def search(W, H, r, iters=300, exact_every=0, qmax=8, seeds=None, v=None, pol=None,
           log=print, tol=1e-14):
    """(7) by pairwise Frank-Wolfe with `maxmean` as the linear oracle.

    Returns the best CERTIFIED direction: `kappa = -maxmean(...)['hi']` for a direction
    with `sum_h h|a_h| = 1` exactly, so `kappa > 2 pi eps_L` is the criterion (6) and
    `kappa > 0` is `K_H(F~) = empty`.  The Frank-Wolfe run is only a generator; every
    number reported here is re-derived from a rigorous evaluation of the direction it
    produced, so an inexact oracle inside the loop costs iterations, never soundness.
    """
    W.set_modes(list(range(1, H + 1)))
    hs = np.arange(1, H + 1, dtype=float)
    V = [c / hs for c in (seeds if seeds is not None else seed_cuts(W, qmax=qmax))]
    p, w = fw_fixed(V, r)
    w = list(w)
    best = dict(kappa=-np.inf, S1=1.0, it=-1, hi=np.inf, lo=-np.inf, cyclen=0)
    t0 = time.time()
    stall = 0
    for it in range(iters):
        g = shrink(p, r)
        n1 = float(np.sum(np.abs(g)))
        if n1 <= 0:
            log(f"    it {it}: f = 0 -- the hull already meets the polydisc; "
                f"the criterion cannot fire at this window")
            best['feasible'] = True
            break
        a = -np.conj(g) / hs
        S1 = float(np.sum(hs * np.abs(a)))
        a = a / S1
        ex = exact_every and (it % exact_every == exact_every - 1)
        res = maxmean(W, a, v=v, pol=pol, exact=bool(ex))
        v, pol = res['v'], res['pol']
        kap = -res['hi']
        if kap > best['kappa']:
            best = dict(kappa=float(kap), S1=1.0, it=it, hi=float(res['hi']),
                        lo=float(res['lo']), a=a.copy(), cyclen=len(res['cycle']),
                        f=fval(p, r))
        q = phi_cycle(W, res['cycle']) / hs
        V.append(q)
        w.append(0.0)
        P = np.asarray(V)
        wa = np.asarray(w)
        sc = np.real(P @ np.conj(g))
        ja = int(np.argmax(np.where(wa > 0, sc, -np.inf)))
        d = P[-1] - P[ja]
        gam = min(wa[ja], _line(p, d, r))
        if gam <= 1e-15:
            stall += 1
            if stall > 8:
                log(f"    it {it}: pairwise step exhausted")
                break
        else:
            stall = 0
            wa[-1] += gam
            wa[ja] -= gam
            w = list(wa)
            p = wa @ P
        if (it % 20 == 0) or it == iters - 1:
            log(f"    it {it:<4d} f {fval(p, r):11.4e}  nu_up {float(np.max(np.abs(p))):10.4e}"
                f"  kappa {kap:12.5e}  best {best['kappa']:12.5e}"
                f"  |V| {len(V)}")
    # the final direction, certified exactly
    if best['it'] >= 0:
        res = maxmean(W, best['a'], v=v, pol=pol, exact=True)
        best['hi'] = min(best['hi'], float(res['hi']))
        best['kappa'] = -best['hi']
        best['lo'] = max(best['lo'], float(res['lo']))
    best['tau'] = float(2 * np.pi * W.eps)              # sum_h h|a_h| = 1
    best['ratio'] = best['kappa'] / best['tau']
    best['nu_up'] = float(np.max(np.abs(p)))
    best['eps'] = float(W.eps)
    best['r'] = float(r)
    best['nV'] = len(V)
    best['secs'] = time.time() - t0
    best['v'], best['pol'] = v, pol
    return best


# ======================================================================================
# the no-fire side, without a transfer operator
# ======================================================================================
# A witness needs no oracle: `mu` with `max_h |Phi~_h(mu)|/h <= 2 pi eps_L` proves that NO
# direction meets (6) at that `(H, L)`, since `kappa(a) <= <a, Phi~(mu)> + 0` would then
# force `kappa <= sum_h h|a_h| . 2 pi eps_L = tau`.  And `Phi~` of a Bernoulli or of a
# periodic measure is a product / a `q`-term sum over the window's weight vector, so the
# whole test costs `O(H L)` and the window may be taken as deep as one likes -- which is
# what turns "we could not fire at `L = 18`" into a statement about every `L`.
class LightWindow:
    """The window `(-N .. M-1)` as its weight vector alone: no `2^L` anything."""

    def __init__(self, al, L):
        N, M, eps = best_window(al, L)
        a = float(al.alpha)
        wt = np.zeros(N + M + 1)
        for j in range(1, M + 1):
            wt[N + j] = (a - 1.0) * a ** (-j)
        cm = [float(sum((complex(z) - 1.0) * complex(z) ** m for z in al.conj).real)
              for m in range(N + 1)]
        for m in range(N + 1):
            wt[N - m] -= cm[m]
        self.al, self.L, self.N, self.M, self.wt, self.eps = al, L, N, M, wt, eps
        self.r = 2 * np.pi * eps

    def F(self, blocks):
        b = np.asarray(blocks, dtype=np.int64)
        out = np.zeros(b.size)
        for i in range(self.L + 1):
            out += self.wt[i] * ((b >> i) & 1)
        return out


def phi_bern(lw, H, p=0.5):
    """`Phi~_h(Bernoulli(p))` in closed form: the bits are independent, so the expectation
    of `e(h F~) = prod_i e(h wt_i x_i)` factorises into `L+1` two-point averages."""
    hs = np.arange(1, H + 1, dtype=float)
    out = np.ones(H, dtype=complex)
    for w in lw.wt:
        out *= (1 - p) + p * np.exp(2j * np.pi * hs * w)
    return out


def phi_orbit(lw, word, H):
    """`Phi~_h` of the periodic measure on a cyclic 0/1 word."""
    F = lw.F(word_cycle(lw.L, list(word)))
    hs = np.arange(1, H + 1, dtype=float)
    return np.exp(2j * np.pi * np.outer(hs, F)).mean(axis=1)


def necklaces(qmax):
    out = []
    seen = set()
    for q in range(1, qmax + 1):
        for m in range(1 << q):
            word = tuple((m >> (q - 1 - i)) & 1 for i in range(q))
            key = min(word[k:] + word[:k] for k in range(q))
            if key not in seen:
                seen.add(key)
                out.append(key)
    return out


def light_seeds(lw, H, qmax=10, ps=(0.5,)):
    """Bernoulli(p) for each `p`, plus every periodic orbit of period `<= qmax`."""
    V = [phi_bern(lw, H, p) for p in ps]
    V += [phi_orbit(lw, wd, H) for wd in necklaces(qmax)]
    return V


def hull_nu(V, H, r=0.0, iters=3000):
    """`min over conv(V) of max_h |p_h|/h`, from above -- Frank-Wolfe against `D_r`.

    Called with `r = 2 pi eps_L` it answers the no-fire question; called with `r = 0` it
    measures how flat a convex combination of the generators can be made, which is an
    upper bound on `nu_H` itself and does not mention any window.
    """
    hs = np.arange(1, H + 1, dtype=float)
    P = [np.asarray(c) / hs for c in V]
    p, w = fw_fixed(P, r, iters=iters)
    return float(np.max(np.abs(p))), w


def nofire(lw, H, qmax=10, iters=3000, ps=(0.5,), slack=1e-6):
    """Search the hull of `light_seeds` for a witness inside the truncation polydisc.

    Returns `(ok, nu_up, weights, V)`; `ok` means the criterion (6) provably cannot fire
    at this `(H, L)`, whatever direction anyone produces.  The search targets a polydisc
    shrunk by `slack`, so a witness it accepts is strictly inside the real one and the
    verdict does not turn on the last bit of a float.
    """
    V = light_seeds(lw, H, qmax=qmax, ps=ps)
    nu, w = hull_nu(V, H, r=lw.r * (1 - slack), iters=iters)
    return nu <= lw.r, nu, w, V


# ======================================================================================
# the true `Phi`, with no window at all
# ======================================================================================
# Nothing above needs a window to say what a PERIODIC measure's moments are.  For `omega`
# of period `q`, `F(sigma^i omega) = sum_{j>=1} (alpha-1) alpha^-j omega_{i+j}
#   - sum_{m>=0} c_m omega_{i-m}`, `c_m = Re sum_z (z-1) z^m`, and both series converge
# geometrically, so `Phi_h` of the orbit measure is a `q`-term average of explicit
# numbers.  Bernoulli(1/2) factorises the same way.  This makes `nu_H^(q)` a statement
# about `F`, not about any `F~`.
def _series(al, J=200, Mp=200):
    a = float(al.alpha)
    fut = np.array([(a - 1.0) * a ** (-j) for j in range(1, J + 1)])
    past = np.array([float(sum((complex(z) - 1.0) * complex(z) ** m
                               for z in al.conj).real) for m in range(Mp + 1)])
    return fut, past


def orbit_F_true(al, word, J=200, Mp=200):
    """`F` at the `q` shifts of a periodic word, to float64 accuracy (the tails are
    `alpha^-J` and `C rho^(M+1)/(1-rho)`, both far below `2^-53` at `J = M = 200`)."""
    fut, past = _series(al, J, Mp)
    q = len(word)
    w = np.asarray(word, dtype=float)
    out = np.empty(q)
    jj = np.arange(1, J + 1)
    mm = np.arange(0, Mp + 1)
    for i in range(q):
        # math.fsum is correctly rounded, so each F carries ONE rounding of the sum of
        # moduli (below 5.2 here) rather than a summation-order-dependent 400 of them
        out[i] = math.fsum(list(fut * w[(i + jj) % q])
                           + list(-past * w[(i - mm) % q]))
    return out


def orbit_phi_radius(al, H, J=200, Mp=200):
    """A rigorous radius for `orbit_phi_true`, in the 2-norm over the `2H` real
    coordinates -- which is the `eps_2` Theorem 1\' of note-1061-R2a.html reads.

    Per coefficient the error is `2 pi h` times the error in `F` (one correctly-rounded
    `fsum` of terms whose moduli total `mag`, plus the two series tails), and summing the
    squares over `h <= H` gives the factor `sqrt(H)` below."""
    fut, past = _series(al, J, Mp)
    mag = float(np.sum(np.abs(fut)) + np.sum(np.abs(past)))
    a, rho = float(al.alpha), float(al.rho)
    Ca = float(sum(abs(complex(z) - 1.0) for z in al.conj))
    tail = a ** (-J) + Ca * rho ** (Mp + 1) / (1 - rho)
    errF = mag * 2.0 ** -53 + tail
    return math.sqrt(H) * (2 * np.pi * H * errF + 8 * 2.0 ** -53)


def orbit_phi_true(al, word, H, J=200, Mp=200):
    F = orbit_F_true(al, word, J, Mp)
    hs = np.arange(1, H + 1, dtype=float)
    return np.exp(2j * np.pi * np.outer(hs, F)).mean(axis=1)


def bern_phi_true(al, H, J=200, Mp=200):
    """`Phi_h(Bernoulli(1/2))` as the two Erdos products, complex."""
    fut, past = _series(al, J, Mp)
    hs = np.arange(1, H + 1, dtype=float)
    out = np.ones(H, dtype=complex)
    for g in fut:
        out *= 0.5 * (1 + np.exp(2j * np.pi * hs * g))
    for c in past:
        out *= 0.5 * (1 + np.exp(-2j * np.pi * hs * c))
    return out


def true_seeds(al, H, qmax=12):
    return [bern_phi_true(al, H)] + [orbit_phi_true(al, wd, H)
                                     for wd in necklaces(qmax)]


# ======================================================================================
# self-checks
# ======================================================================================
def _chk(name, cond, extra=""):
    print(f"  {'PASS' if cond else 'FAIL'}  {name}{'   ' + extra if extra else ''}")
    return bool(cond)


def selfchecks():
    print("R2b self-checks")
    ok = []
    al = Alpha([1, -2, -1], '1+sqrt2')
    rng = np.random.default_rng(20260827)

    # --- the graph -----------------------------------------------------------------
    L = 6
    e0, e1, h0, h1 = edges(L)
    n, mask = 1 << L, (1 << L) - 1
    ok.append(_chk("edge indexing: tail(e) = e>>1 for both children",
                   np.all(e0 >> 1 == np.arange(n)) and np.all(e1 >> 1 == np.arange(n))))
    ok.append(_chk("edge indexing: head(e) = e mod 2^L",
                   np.all(h0 == (e0 & mask)) and np.all(h1 == (e1 & mask))))

    # --- the oracle ----------------------------------------------------------------
    agree, worst = True, 0.0
    for LL in (3, 4, 6, 8):
        for _ in range(3):
            w = rng.normal(size=1 << (LL + 1))
            k = karp(w, LL)
            lam, pol, bi, _ = howard(w, LL)
            worst = max(worst, abs(k - lam))
            agree &= abs(k - lam) < 1e-9
    ok.append(_chk("Howard = Karp on 12 random graphs", agree, f"max |diff| {worst:.2e}"))

    tight, brack = True, True
    for LL in (4, 6, 8):
        w = rng.normal(size=1 << (LL + 1))
        lam, pol, bi, _ = howard(w, LL)
        tight &= abs(certify(w, LL, bi) - lam) < 1e-8
        lo, hi, v, _ = tropical(w, LL, iters=2000)
        brack &= (lo <= lam + 1e-9 <= 1e-9 + hi)
    ok.append(_chk("Howard's bias is an exact potential certificate", tight))
    ok.append(_chk("tropical bracket [lo, hi] contains the exact lambda", brack))

    LL, wz = 6, np.zeros(1 << 7)
    ok.append(_chk("a = 0 gives lambda = 0 exactly", howard(wz, LL)[0] == 0.0))

    # --- the window pairing ---------------------------------------------------------
    L = 10
    N, M, e = best_window(al, L)
    W = Window(al, N, M)
    H = 12
    W.set_modes(list(range(1, H + 1)))
    mask = (1 << L) - 1
    hom, chain, ident, bern_lb = True, True, True, True
    for _ in range(4):
        a = (rng.normal(size=H) + 1j * rng.normal(size=H)) / math.sqrt(2 * H)
        r = maxmean(W, a)
        cyc = r['cycle']
        chain &= all((cyc[i] & mask) == (cyc[(i + 1) % len(cyc)] >> 1)
                     for i in range(len(cyc)))
        w = W.weights(a)
        ident &= abs(float(np.mean(w[cyc])) - r['lam']) < 1e-11
        ident &= abs(pair(a, phi_cycle(W, cyc)) - r['lam']) < 1e-10
        t = 3.7
        W.reset_iterates()
        hom &= abs(maxmean(W, t * a)['lam'] - t * r['lam']) < 1e-9 * (1 + abs(r['lam']))
        pb = phi_circ(W, np.full(1 << (L + 1), 2.0 ** -(L + 1)))
        bern_lb &= pair(a, pb) <= r['lam'] + 1e-12
        W.reset_iterates()
    ok.append(_chk("the maximising cycle is a cycle", chain))
    ok.append(_chk("cycle mean = lambda = <a, Phi~(cycle)>", ident))
    ok.append(_chk("lambda(t a) = t lambda(a)", hom))
    ok.append(_chk("lambda >= <a, Phi~(Bernoulli)>", bern_lb))

    press = True
    for _ in range(4):
        a = (rng.normal(size=H) + 1j * rng.normal(size=H)) / math.sqrt(2 * H)
        W.reset_iterates()
        r = maxmean(W, a)
        W.reset_iterates()
        press &= r['hi'] <= W.pressure_ub(a) + 1e-9
    ok.append(_chk("lambda <= pressure_ub (beta <= P, the entropy the pressure pays)",
                   press))

    # --- the light window ------------------------------------------------------------
    lw = LightWindow(al, L)
    ok.append(_chk("LightWindow.wt = Window.wt", np.allclose(lw.wt, W.wt, atol=0, rtol=0)))
    pb1 = phi_circ(W, np.full(1 << (L + 1), 2.0 ** -(L + 1)))
    pb2 = phi_bern(lw, H)
    ok.append(_chk("phi_bern (closed form) = phi_circ (edge sum)",
                   float(np.abs(pb1 - pb2).max()) < 1e-13,
                   f"max diff {float(np.abs(pb1 - pb2).max()):.2e}"))
    wd = (1, 0, 0, 1, 1, 0)
    ok.append(_chk("phi_orbit = phi_cycle o word_cycle",
                   float(np.abs(phi_orbit(lw, wd, H)
                                - phi_cycle(W, word_cycle(L, list(wd)))).max()) < 1e-13))
    ok.append(_chk("necklace counts (1..8) = 2,3,4,6,8,14,20,36",
                   [len([x for x in necklaces(8) if len(x) == q]) for q in range(1, 9)]
                   == [2, 3, 4, 6, 8, 14, 20, 36]))

    # --- the geometry ----------------------------------------------------------------
    p = rng.normal(size=8) + 1j * rng.normal(size=8)
    rr = 0.7
    ok.append(_chk("fval = 1/2 |shrink|^2",
                   abs(fval(p, rr) - 0.5 * float(np.sum(np.abs(shrink(p, rr)) ** 2)))
                   < 1e-12))
    V = [rng.normal(size=6) + 1j * rng.normal(size=6) for _ in range(9)]
    pp, ww = fw_fixed(V, 0.0, iters=500)
    ok.append(_chk("fw_fixed returns a convex combination",
                   abs(ww.sum() - 1) < 1e-9 and ww.min() >= -1e-12
                   and float(np.abs(pp - ww @ np.asarray(V)).max()) < 1e-12))

    # --- the observable ---------------------------------------------------------------
    lw40 = LightWindow(al, 40)
    tabs = {}
    for q in (6, 10):
        for HH in (16, 64):
            tabs[(q, HH)] = hull_nu(light_seeds(lw40, HH, qmax=q), HH, r=0.0, iters=1500)[0]
    ok.append(_chk("nu^(q)_H non-decreasing in H",
                   tabs[(6, 16)] <= tabs[(6, 64)] + 1e-12
                   and tabs[(10, 16)] <= tabs[(10, 64)] + 1e-12))
    ok.append(_chk("nu^(q)_H non-increasing in q",
                   tabs[(10, 16)] <= tabs[(6, 16)] + 1e-12
                   and tabs[(10, 64)] <= tabs[(6, 64)] + 1e-12))

    lw12 = LightWindow(al, 12)
    bv = float(np.max(np.abs(phi_bern(lw12, 128)) / np.arange(1, 129)))
    ok.append(_chk("the Bernoulli veto at L=12", bv <= lw12.r,
                   f"{bv:.4e} <= 2 pi eps = {lw12.r:.4e}"))

    wd2 = (1, 1, 0, 1, 0, 0, 0)
    lw40 = LightWindow(al, 40)
    p40 = phi_orbit(lw40, wd2, 24)
    pt = orbit_phi_true(al, tuple(reversed(wd2)), 24)      # note the reversal, see below
    ok.append(_chk("orbit_phi_true(reverse w) = the L=40 window value of w, "
                   "inside 2 pi h eps_40",
                   bool(np.all(np.abs(p40 - pt)
                               <= 2 * np.pi * np.arange(1, 25) * lw40.eps)),
                   f"max diff {float(np.abs(p40 - pt).max()):.2e}"))
    nk = set(necklaces(9))
    rev_closed = all(min(tuple(reversed(w))[k:] + tuple(reversed(w))[:k]
                         for k in range(len(w))) in nk for w in nk)
    ok.append(_chk("the necklace set is closed under reversal, so the hull does not "
                   "depend on the convention", rev_closed))
    d24 = float(np.linalg.norm(orbit_phi_true(al, wd2, 24)
                               - orbit_phi_true(al, wd2, 24, J=400, Mp=400)))
    ok.append(_chk("orbit_phi_radius covers a J=200 vs J=400 re-evaluation",
                   d24 <= orbit_phi_radius(al, 24),
                   f"{d24:.2e} <= {orbit_phi_radius(al, 24):.2e}"))

    # the witness really does block EVERY direction, not just the ones we looked at
    okw, nu, ww, V = nofire(lw12, 64, qmax=8)
    hs = np.arange(1, 65, dtype=float)
    P = np.asarray([c / hs for c in V])
    pw = ww @ P
    blocked = True
    for _ in range(200):
        a = rng.normal(size=64) + 1j * rng.normal(size=64)
        S1 = float(np.sum(np.arange(1, 65) * np.abs(a)))
        ah = a / S1
        bhat = np.conj(ah) * 0 + ah * np.arange(1, 65)      # a^_h = h a_h
        blocked &= pair(bhat, pw) >= -lw12.r - 1e-12
    ok.append(_chk("the witness blocks 200 random directions (kappa <= tau)", blocked))

    print(f"\n  {sum(ok)}/{len(ok)} checks passed")
    return 0 if all(ok) else 1


# ======================================================================================
# the recorded run
# ======================================================================================
def price(al, nu, L0=12):
    """The window depth (6) needs, and its cost, for an observable of size `nu`.

    `eps_L` falls like `alpha^(-L/2)` at a quadratic unit, so `2 pi eps_L < nu` fixes
    `L` and the state count `2^L` grows like `nu^(-2 log 2 / log alpha)`.
    """
    lw0 = LightWindow(al, L0)
    rate = math.log(float(al.alpha)) / 2
    if nu <= 0:
        return float('inf'), float('inf'), 2 * math.log(2) / math.log(float(al.alpha))
    L = L0 + math.log(lw0.r / nu) / rate
    return L, 2.0 ** L, 2 * math.log(2) / math.log(float(al.alpha))


def reprice_r2a(al, H=128, Ls=(12, 14, 16, 18), log=print):
    """R2a sec 7's direction, priced by the exact oracle instead of by the pressure."""
    from r2a_flat import one
    N, M, e = best_window(al, 12)
    W0 = Window(al, N, M)
    r0 = one(W0, H)
    x = np.asarray(r0['x'])
    a0 = x[:H] + 1j * x[H:]
    nrm = float(np.linalg.norm(x))
    ah = a0 / nrm
    log(f"\n# R2a's row-1 direction at L=12, H={H}, reproduced: pressure_ub {r0['ub']:.4f},"
        f" |a|_2 {nrm:.3f}, |a|_inf {float(np.abs(a0).max()):.3f}")
    log(f"  {'L':>3} {'eps':>10} {'beta(a^) exact':>15} {'kappa':>10} {'tau':>10} "
        f"{'kappa/tau':>11} {'kappa (P_ub)':>13}")
    out = []
    for L in Ls:
        N, M, e = best_window(al, L)
        W = Window(al, N, M)
        W.set_modes(list(range(1, H + 1)))
        r = maxmean(W, ah)
        tau = delta_bound(W, ah)
        W.reset_iterates()
        kp = -np.inf
        for c in (0.05, 0.1, 0.2, 0.4, 0.7, 1.0):
            v = W.pressure_ub(c * a0)
            if np.isfinite(v):
                kp = max(kp, -v / (c * nrm))
        row = dict(L=L, eps=float(e), beta=float(r['lam']), kappa=float(-r['hi']),
                   tau=float(tau), ratio=float(-r['hi'] / tau), kappa_press=float(kp))
        out.append(row)
        log(f"  {L:3d} {e:10.3e} {r['lam']:15.6f} {-r['hi']:10.5f} {tau:10.4f} "
            f"{-r['hi'] / tau:11.6f} {kp:13.5f}")
        del W
    return out


def flat_threshold(al, L, Hs, log=print):
    """The entropy-free flatness threshold: the least `H` with `K_H(F~_L) = empty`.

    The pressure optimiser is used only as a direction GENERATOR; the verdict is the
    oracle's, and `beta <= P` means it can only fire earlier than R2a's row-1 test.
    """
    from m3_entropy import minimize_pressure
    from m4_fourier import pad
    N, M, e = best_window(al, L)
    W = Window(al, N, M)
    log(f"\n# entropy-free flatness at L={L} (eps {e:.4e}); the pressure route needs"
        f" H_0 = 120 here")
    log(f"  {'H':>5} {'P':>12} {'pressure_ub':>12} {'beta (exact)':>14} {'K_H(F~)':>10}")
    out, xp, Hp = [], None, 0
    for H in Hs:
        W.set_modes(list(range(1, H + 1)))
        try:
            P, xs, flat, dl = minimize_pressure(W, x0=pad(xp, Hp, H), cap=60.0)
        except Exception as exc:
            log(f"  {H:5d}   generator gave up ({type(exc).__name__})")
            continue
        a = np.asarray(xs)[:H] + 1j * np.asarray(xs)[H:]
        ub = float(W.pressure_ub(a))
        r = maxmean(W, a)
        empty = r['hi'] < 0
        out.append(dict(H=H, P=float(P), ub=ub, beta=float(r['hi']), empty=bool(empty)))
        log(f"  {H:5d} {P:12.6f} {ub:12.6f} {r['hi']:14.6f} "
            f"{'EMPTY' if empty else 'not shown':>10}")
        if P > 0:
            xp, Hp = np.asarray(xs), H
    return out


def run(log=print):
    al = Alpha([1, -2, -1], '1+sqrt2')
    out = {}
    log("=" * 92)
    log("R2b: the entropy-free dual minimiser at 1+sqrt2.  nu_H = min_mu max_h |Phi_h|/h.")
    log("=" * 92)

    out['reprice'] = reprice_r2a(al, log=log)

    log("\n# nu_H^(q): the observable from ABOVE, on the hull of Bernoulli(1/2) and the")
    log("#   periodic orbits of period <= q.  TRUE Phi (`orbit_phi_true`): no window.")
    qs = (4, 6, 8, 10, 12, 14)
    Hs = (8, 16, 32, 64, 128, 256, 512)
    log(f"  {'H':>6} " + " ".join(f"{'q<=' + str(q):>11}" for q in qs))
    tab = {}
    for H in Hs:
        row = []
        for q in qs:
            v, _ = hull_nu(true_seeds(al, H, qmax=q), H, r=0.0, iters=4000)
            row.append(float(v))
        tab[H] = row
        log(f"  {H:6d} " + " ".join(f"{v:11.4e}" for v in row))
    out['nu_q'] = dict(qs=list(qs), Hs=list(Hs), tab={str(k): v for k, v in tab.items()})

    log("\n# what that costs.  (6) needs a window with 2 pi eps_L < nu_H; at a quadratic")
    log("#   unit eps_L ~ alpha^(-L/2), so the state count grows like nu^(-2log2/log alpha).")
    _, _, expo = price(al, 1.0)
    log(f"  exponent 2 log 2 / log alpha = {expo:.4f}")
    log(f"  {'H':>6} {'nu_H <=':>11} {'L needed':>9} {'states':>12}   reading")
    pr = {}
    for H in Hs:
        nu = tab[H][-1]
        if nu < 1e-9:
            pr[H] = dict(nu=nu, L=None, states=None)
            log(f"  {H:6d} {nu:11.4e} {'--':>9} {'--':>12}   nu_H = 0: an explicit member"
                f" of K_H out of periodic orbits; (6) can NEVER fire at this H")
            continue
        L, st, _ = price(al, nu)
        pr[H] = dict(nu=nu, L=L, states=st)
        log(f"  {H:6d} {nu:11.4e} {L:9.1f} {st:12.3e}   necessary, not sufficient")
    out['price'] = {str(k): v for k, v in pr.items()}

    log("\n# R1b's own theorem, as a price.  Any mu in K_{H0} has |Phi_h| = 0 for h <= H0")
    log("#   and |Phi_h| <= 1 above it, so nu_H <= 1/(H0+1) for EVERY H.  Each degree at")
    log("#   which non-emptiness is certified raises this machine's entry price.")
    log(f"  {'H0':>6} {'nu_H <=':>11} {'L needed':>9} {'states':>12}")
    r1b = {}
    for H0 in (64, 128, 256, 512, 1024):
        nu = 1.0 / (H0 + 1)
        L, st, _ = price(al, nu)
        r1b[H0] = dict(nu=nu, L=L, states=st)
        log(f"  {H0:6d} {nu:11.4e} {L:9.1f} {st:12.3e}")
    out['r1b_price'] = {str(k): v for k, v in r1b.items()}

    log("\n# the no-fire certificate at the windows anyone can afford: an explicit measure")
    log("#   with max_h |Phi~_h|/h <= 2 pi eps_L blocks EVERY direction at that (H, L).")
    Lw = (12, 14, 16, 18, 20, 22, 24)
    log(f"  {'H':>6} " + " ".join(f"{'L=' + str(L):>9}" for L in Lw))
    nf = {}
    for H in (32, 64, 128, 256):
        row = []
        for L in Lw:
            lw = LightWindow(al, L)
            ok, nu, w, V = nofire(lw, H, qmax=14)
            row.append(bool(ok))
        nf[H] = row
        log(f"  {H:6d} " + " ".join(f"{('yes' if v else 'no'):>9}" for v in row))
    log("  ('yes' = the criterion provably cannot fire there, whatever direction is found)")
    out['nofire'] = {str(k): v for k, v in nf.items()}

    out['flat12'] = flat_threshold(al, 12, [64, 80, 96, 104, 112, 116, 120, 128], log=log)

    with open(f'{BB}/r2b_ergodic.json', 'w') as f:
        json.dump(out, f, indent=1)
    log(f"\n# wrote {BB}/r2b_ergodic.json")
    return 0


def main():
    if '--selfcheck' in sys.argv:
        return selfchecks()
    if '--nu' in sys.argv:
        i = sys.argv.index('--nu')
        al = Alpha([1, -2, -1], '1+sqrt2')
        L, H = int(sys.argv[i + 1]), int(sys.argv[i + 2])
        q = int(sys.argv[i + 3]) if len(sys.argv) > i + 3 else 12
        lw = LightWindow(al, L)
        ok, nu, w, V = nofire(lw, H, qmax=q)
        print(f"L={L} H={H} q<={q}: nu_up {nu:.6e}  2 pi eps {lw.r:.6e}  "
              f"{'NO-FIRE certified' if ok else 'no witness in this hull'}")
        return 0
    return run()


if __name__ == '__main__':
    sys.exit(main())
