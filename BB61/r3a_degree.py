#!/usr/bin/env python3
# (C) 2026 Ralf Stephan, in collaboration with Claude Code.
# CC0 1.0 Universal (public domain dedication).
"""R3a of `plan-BB61-counterexample.html`: the enclosure and plateau accounting at
degree `d = 3, 4`, so that the numbers of that plan's sec 7.2 become usable.

sec 7.2 reads a table off note-1061-M7.html sec 8 -- the degeneration family
`X^{n+1} - 2X^n - 1`, whose Pisot roots decrease to `2`, where 10.61 is false -- and
takes the column `sup_{h<=4096} |Phi_h(Bern_{1/2})|` as an *explicit small parameter*
for a Newton construction (sec 7.3).  Caveat (ii) of that section says the accounting
behind the column was written for quadratic units and has to be redone before the
numbers are used as more than a signpost.  This module redoes it.

Four things are re-derived, and each changes the reading.

(1) CERTIFIED CONJUGATES AT ANY DEGREE.  `r1a_enclose` carries the whole certified
    chain at `1+sqrt2` and is quadratic by construction (`ABAR = 1 - sqrt2`,
    `set_alpha(A, B)`).  At degree `d` the conjugates are not in a real quadratic
    field and there is no closed form.  Smith's theorem supplies what is needed: with
    `zhat_i` the approximate roots of the monic integer `p`, every root of `p` lies in
    some disc `D(zhat_i, r_i)`, `r_i = d |p(zhat_i)| / prod_{j!=i} |zhat_i - zhat_j|`,
    and a disc disjoint from the others holds exactly one.  At 200 digits the radii
    are `~1e-200` and the discs are disjoint at every degree here, so the conjugates
    become interval constants and everything downstream is an enclosure.

(2) THE WINDOW LAW.  The truncation bound of M4 Prop. 3, in the form R1a uses it, is

        |F - F~_{J,M}| <= alpha^-J + sum_{j>=2} |alpha_j - 1| |alpha_j|^{M+1}/(1-|alpha_j|)

    -- the *per-conjugate* past tail, not `C_alpha rho^{M+1}/(1-rho)`.  At degree two
    the two agree (one conjugate).  From degree four on the conjugate moduli differ and
    the per-conjugate form is up to `2.3x` tighter, which is worth two to three units
    of window depth.  The consequence that matters: the past depth needed for a target
    radius `tau` at mode `H` is `M ~ log(2 pi H sum_j |alpha_j-1| / tau) / log(1/rho)`,
    and `rho -> 1` down the family.  The folder's default enclosure window `(60,60)`
    delivers `2 pi H eps = 5.6e-19` at `1+sqrt2` and `9.9e-01` at `X^4-2X^3-1`: at
    degree four the folder's own default returns noise at `H = 4096`.

(3) THE PLATEAU IS GONE, AND WHAT REPLACES IT IS MEASURED.  M7 Thm 10 already proves
    the plateau exists exactly at quadratic units.  Thm 8's *future* half survives
    verbatim at any degree with `|e_0| |beta|^j` replaced by `E rho^j`,
    `E = sum_{i>=1} |lambda^(i)| |alpha_i - alpha|` (Theorem B below, verified here at
    `d = 2..5`).  Its *past* half used `alpha |beta| = 1`, which holds only at a
    quadratic unit; the past band's amplitude is `(alpha_j alpha)^k`, of modulus
    `(rho alpha)^k = 1.49^k` at `d=3` and `1.71^k` at `d=4`, so the band shape never
    stabilises and `|Phi_{h_k}|` dies geometrically along every ladder.

(4) WHAT THE COLUMN ACTUALLY IS.  Measured here at `H <= 16384`: for every `d >= 3`
    in the family the maximiser of `|Phi_h(Bern)|` is `h = 1`.  sec 7.2's "residual"
    is the first Fourier mode, not a sup, and it is `H`-independent for a reason that
    has nothing to do with the plateau.  Worse for the reading, the rest of the
    spectrum collapses far faster than the first mode: the certified concentration
    ratio `|Phi_1| / sup_{2<=h<=4096} |Phi_h|` runs `1.3, 3.7, 286, 5.7e2, ...`, so at
    `d >= 4` the Bernoulli residual is a rank-two vector in `R^{2H}`.

Usage:
    python3 r3a_degree.py checks | roots | enc | bern | plat | read | table | all
"""
import json
import math
import os
import sys
import time

import numpy as np
import mpmath as mp

HERE = os.path.dirname(os.path.abspath(__file__))
sys.path.insert(0, HERE)

from m0_engine import Alpha, is_pisot                                    # noqa: E402

DPS = 200
mp.mp.dps = DPS

OUT = os.path.join(HERE, 'r3a_degree.json')
HDEF = 4096
TAU = mp.mpf('1e-13')          # the enclosure radius R1a's gate asks for
FAMILY = [[1, -2] + [0] * (n - 1) + [-1] for n in range(1, 11)]
EXTRA = [([1, -2, -1], '1+sqrt2'), ([1, -3, 1], '(3+sqrt5)/2'),
         ([1, -3, -1], '(3+sqrt13)/2'), ([1, -4, 1], '2+sqrt3')]

FAIL = []
NCHECKS = [0]


def check(name, cond, extra=""):
    NCHECKS[0] += 1
    print("    [%s] %s%s" % ('ok ' if cond else 'FAIL', name, ('  ' + extra) if extra else ''))
    if not cond:
        FAIL.append(name)


# ======================================================================================
# (1) certified conjugates at any degree -- Smith discs
# ======================================================================================
class Field:
    """A Pisot number with *certified* conjugates.

    `alpha` is the real root above 1; `conj` the `d-1` others, each carried as a pair
    `(zhat, r)` meaning "the true root lies in the closed disc of radius r about zhat".
    `rad` is the largest r.  Smith's theorem: with `zhat_i` any d points and
    `r_i = d |p(zhat_i)| / prod_{j != i} |zhat_i - zhat_j|`, every root of the monic p
    lies in some `D(zhat_i, r_i)`, and a disc disjoint from all others contains exactly
    one.  `disjoint` records that the discs here are pairwise disjoint, so the labelling
    is a bijection and each `(zhat_i, r_i)` encloses one root.
    """

    def __init__(self, coeffs, name=None, dps=DPS):
        self.coeffs = [int(c) for c in coeffs]
        self.d = len(coeffs) - 1
        with mp.workdps(dps + 100):
            cf = [mp.mpf(c) for c in self.coeffs]
            rts = mp.polyroots(cf, maxsteps=600, extraprec=1200)
            rts = sorted(rts, key=lambda z: -abs(z))
            rad = []
            for i, z in enumerate(rts):
                den = mp.mpf(1)
                for j, w in enumerate(rts):
                    if j != i:
                        den *= abs(z - w)
                rad.append(self.d * abs(mp.polyval(cf, z)) / den)
            self.disjoint = all(abs(rts[i] - rts[j]) > rad[i] + rad[j]
                                for i in range(self.d) for j in range(i + 1, self.d))
        self.roots = [(mp.mpc(z), mp.mpf(r)) for z, r in zip(rts, rad)]
        self.alpha = mp.re(self.roots[0][0])
        self.alpha_r = self.roots[0][1]
        self.conj = self.roots[1:]
        self.rad = max(r for _, r in self.roots)
        self.mods = [abs(z) + r for z, r in self.conj]          # certified upper bounds
        self.rho = max(self.mods) if self.mods else mp.mpf(0)
        self.unit = abs(self.coeffs[-1]) == 1
        self.name = name or Alpha(self.coeffs).polystr()
        # C_alpha = sum |alpha_j - 1|, upper bound
        self.Ca = sum(abs(z - 1) + r for z, r in self.conj) if self.conj else mp.mpf(0)

    def c_m(self, M):
        """c_m = Re sum_{j>=2} (alpha_j - 1) alpha_j^m, m = 0..M-1, with a bound on the
        error committed by using the disc centres (first order in the radii, times a
        factor 2 for safety at these magnitudes)."""
        out, err = [], []
        pw = [mp.mpc(1)] * len(self.conj)
        for m in range(M):
            s = mp.mpf(0)
            e = mp.mpf(0)
            for i, (z, r) in enumerate(self.conj):
                s += mp.re((z - 1) * pw[i])
                e += 2 * r * (m + 1) * (abs(z) + r) ** max(m - 1, 0) * (abs(z - 1) + 1)
            out.append(s)
            err.append(e)
            for i, (z, _r) in enumerate(self.conj):
                pw[i] *= z
        return out, err

    def past_tail(self, M):
        """sum_{m > M} |c_m|, certified: sum_j |alpha_j-1| |alpha_j|^{M+1} / (1-|alpha_j|)."""
        t = mp.mpf(0)
        for (z, r), rho in zip(self.conj, self.mods):
            t += (abs(z - 1) + r) * rho ** (M + 1) / (1 - rho)
        return t

    def rangeF(self, M=400):
        """The total range of F = (a-1) sum_{k>=1} w_k a^-k - sum_{m>=0} c_m w_-m over
        {0,1}^Z: the future half contributes 1, the past half sum_m |c_m|."""
        c, _ = self.c_m(M)
        return mp.mpf(1) + sum(abs(x) for x in c) + self.past_tail(M)

    def eps(self, J, M):
        """sup_omega |F - F~_{J,M}|, certified (M4 Prop. 3, per-conjugate past tail)."""
        return self.alpha ** (-J) + self.past_tail(M)

    def eps_crude(self, J, M):
        """The bound M4 `best_window` uses: one rho for every conjugate."""
        return self.alpha ** (-J) + self.Ca * self.rho ** (M + 1) / (1 - self.rho)

    def need(self, H, tau=TAU, crude=False):
        """Smallest (J, M) with 2 pi H eps(J,M) <= tau, each half taking tau/2."""
        t = mp.mpf(tau) / (2 * mp.pi * H) / 2
        J = 1
        while self.alpha ** (-J) > t:
            J += 1
        M = 0
        f = (lambda m: self.Ca * self.rho ** (m + 1) / (1 - self.rho)) if crude else self.past_tail
        while f(M) > t:
            M += 1
        return J, M

    def best_window(self, L, crude=False):
        """The split of a memory-L window minimising eps; returns (eps, past, future)."""
        f = self.eps_crude if crude else self.eps
        best = None
        for Mf in range(1, L):
            e = f(Mf, L - Mf)
            if best is None or e < best[0]:
                best = (e, L - Mf, Mf)
        return best

    def gibbs_L(self, target, Lmax=4000):
        """Smallest memory L whose window observable resolves `target`: eps_L < target."""
        L = 2
        while L < Lmax and self.best_window(L)[0] >= target:
            L += 1
        return L


# ======================================================================================
# (2) the Bernoulli spectrum:  float scan, then certified enclosure
# ======================================================================================
def bern_scan(F, H, tol=1e-18):
    """|Phi_h(Bern_{1/2})|, h = 1..H, in float64: the two Erdos products.

    Used only to *locate*; every number reported is re-certified by `bern_cert`.
    Unlike `m7_alpha2.bern` the past product is not stopped at the first small |c_m|
    (at degree >= 3 the c_m oscillate and may vanish accidentally), only at the depth
    the tail law prescribes."""
    a, rho = float(F.alpha), float(F.rho)
    h = np.arange(1, H + 1, dtype=float)
    out = np.ones(H)
    j = 1
    while (a - 1.0) * a ** (-j) * H > tol:
        out *= np.abs(np.cos(np.pi * h * (a - 1.0) * a ** (-j)))
        j += 1
    M = int(math.log(tol / (H * max(float(F.Ca), 1e-9))) / math.log(rho)) + 2
    c, _ = F.c_m(max(M, 1))
    cf = np.array([float(x) for x in c])
    for m in range(len(cf)):
        out *= np.abs(np.cos(np.pi * h * cf[m]))
    return out, j - 1, len(cf)


def bern_cert(F, h, J=None, M=None, tau=mp.mpf('1e-40')):
    """Certified enclosure [lo, hi] of |Phi_h(Bern_{1/2})|.

    |Phi_h| = prod_{j=1}^{J} |cos(pi h (a-1) a^-j)| * prod_{m=0}^{M} |cos(pi h c_m)| * T,
    with the dropped factors satisfying  1 - pi^2 (tail_f + tail_p) <= T <= 1  by
    |cos(pi x)| >= 1 - pi^2 x^2 / 2 termwise and prod(1-t) >= 1 - sum t.  Here
    tail_f = h^2 (a-1)^2 a^{-2J}/(a^2-1) and tail_p = h^2 (sum_{m>M}|c_m|)^2, both
    certified.  The root radii enter through `c_m`'s own error and are ~1e-200.
    """
    a = F.alpha
    if J is None or M is None:
        Jn, Mn = F.need(max(h, 1), tau)
        J = Jn if J is None else J
        M = Mn if M is None else M
    val = mp.mpf(1)
    for j in range(1, J + 1):
        val *= abs(mp.cos(mp.pi * h * (a - 1) / a ** j))
    c, cerr = F.c_m(M + 1)
    for m in range(M + 1):
        x = mp.mpf(h) * c[m]
        e = mp.mpf(h) * cerr[m]
        val *= min(mp.mpf(1), abs(mp.cos(mp.pi * x)) + mp.pi * e)
    tf = mp.mpf(h) ** 2 * (a - 1) ** 2 * a ** (-2 * J) / (a ** 2 - 1)
    tp = mp.mpf(h) ** 2 * F.past_tail(M) ** 2
    T = max(mp.mpf(0), 1 - mp.pi ** 2 * (tf + tp))
    # arithmetic: (J+M+1) multiplications at DPS digits, generous 4x
    ar = 4 * (J + M + 2) * mp.mpf(10) ** (-DPS + 5)
    return val * T * (1 - ar), val * (1 + ar), J, M


def sup_cert(F, H, K=None):
    """Certified `sup_{h<=H} |Phi_h(Bern)|` with its maximiser, and the certified
    `sup_{2<=h<=H}` when the maximiser is h=1.

    Every factor has modulus <= 1, so *any* sub-product is an upper bound.  A short
    certified sub-product (K future and K past factors) is evaluated at all h; if its
    maximum away from the float argmax falls below the certified lower bound there,
    the argmax is proved and the sup is enclosed."""
    fl, _, _ = bern_scan(F, H)
    hstar = int(np.argmax(fl)) + 1
    lo, hi, J, M = bern_cert(F, hstar)
    a = float(F.alpha)
    hs = np.arange(1, H + 1, dtype=float)
    for K in ([K] if K else range(4, 200, 2)):
        ub = np.ones(H)
        for j in range(1, K + 1):
            ub *= np.abs(np.cos(np.pi * hs * (a - 1.0) * a ** (-j)))
        cs, _ = F.c_m(K)
        for m in range(K):
            ub *= np.abs(np.cos(np.pi * hs * float(cs[m])))
        ub *= 1 + 1e-12                       # float64 slack on a K-factor product
        rest = ub.copy()
        rest[hstar - 1] = 0.0
        if rest.max() < float(lo):
            break
    proved = rest.max() < float(lo)
    # The same device for the rest of the spectrum: a certified upper bound on
    # sup_{h != h*} |Phi_h|, which needs a longer sub-product than the argmax did.
    KMAX = 900
    cs2, _ = F.c_m(KMAX)
    cs2 = np.array([float(x) for x in cs2])
    ub2 = np.ones(H)
    K2, h2, lo2, hi2, r2 = 0, hstar, mp.mpf(0), mp.mpf(0), np.zeros(H)
    while K2 < KMAX:
        for _ in range(2):
            K2 += 1
            ub2 *= np.abs(np.cos(np.pi * hs * (a - 1.0) * a ** (-K2)))
            ub2 *= np.abs(np.cos(np.pi * hs * cs2[K2 - 1]))
        r2 = ub2 * (1 + 1e-12)
        r2[hstar - 1] = 0.0
        h2 = int(np.argmax(r2)) + 1
        lo2, hi2, _, _ = bern_cert(F, h2)
        if r2.max() <= float(hi2) * (1 + 1e-9):
            break
    second = dict(h=int(h2), lo=float(lo2), hi=float(hi2), K=int(K2),
                  ub_rest=float(r2.max()), proved=bool(r2.max() <= float(hi2) * (1 + 1e-9)))
    return dict(hstar=hstar, lo=float(lo), hi=float(hi), J=int(J), M=int(M), K=int(K),
                ub_rest=float(rest.max()), proved=bool(proved), float_val=float(fl.max()),
                second=second)


# ======================================================================================
# (3) ladders and the plateau, at any degree
# ======================================================================================
def ladder(F, seed, n):
    """The integer sequence h_{k+d} = a_1 h_{k+d-1} + ... + a_d h_k from an integer seed
    (M7 Thm 7: these are exactly the Tr(lambda alpha^k), lambda in the inverse different)."""
    a = [-c for c in F.coeffs[1:]]                      # X^d = a_1 X^{d-1} + ... + a_d
    h = list(int(x) for x in seed)
    while len(h) < n:
        h.append(sum(a[i] * h[-1 - i] for i in range(F.d)))
    return h[:n]


def lam(F, seed):
    """The coefficients lambda^(i) with h_k = sum_i lambda^(i) alpha_i^k (Vandermonde)."""
    V = mp.matrix(F.d, F.d)
    for k in range(F.d):
        for i, (z, _r) in enumerate(F.roots):
            V[k, i] = z ** k
    b = mp.matrix([mp.mpc(int(s)) for s in seed])
    return mp.lu_solve(V, b)


def thm_b(F, seed, n=40):
    """Theorem B (the dead zone at any degree).  With e_k = h_{k+1} - alpha h_k,
    |e_k| <= E rho^k, E = sum_{i>=1} |lambda^(i)| |alpha_i - alpha|, one has for i,j>=0

        | h_{i+j} (alpha-1) alpha^-i - (h_{j+1} - h_j) |  <=  E rho^j (1 + (alpha-1)/(alpha-rho)).

    Proof: h_{i+j} = alpha^i h_j + sum_{t=j}^{i+j-1} alpha^{i+j-1-t} e_t, so the left side is
    |-e_j + (alpha-1) sum_{t>=j} alpha^{j-1-t} e_t| <= E rho^j + (alpha-1) E rho^j/(alpha-rho).
    At degree two this is M7 Thm 8 with E = |e_0|, rho = |beta|.  Returns the worst
    measured ratio (left side)/(bound) over i+j <= n."""
    h = ladder(F, seed, 2 * n + 4)
    lm = lam(F, seed)
    E = sum(abs(lm[i]) * abs(F.roots[i][0] - F.alpha) for i in range(1, F.d))
    K = 1 + (F.alpha - 1) / (F.alpha - F.rho)
    worst, arg = mp.mpf(0), None
    for j in range(0, n):
        bnd = E * F.rho ** j * K
        for i in range(0, n - j):
            lhs = abs(mp.mpf(h[i + j]) * (F.alpha - 1) / F.alpha ** i - (h[j + 1] - h[j]))
            if bnd > 0 and lhs / bnd > worst:
                worst, arg = lhs / bnd, (i, j)
    return dict(E=float(E), K=float(K), worst=float(worst), arg=arg)


def past_band(F, seed, n=16):
    """The past-band amplitude sum_{j>=1} lambda^(j) (alpha_j alpha)^k of M7 Thm 10, and
    the measured |Phi_{h_k}(Bern)| along the same ladder."""
    lm = lam(F, seed)
    h = ladder(F, seed, n)
    amp = []
    for k in range(n):
        amp.append(float(abs(sum(lm[i] * (F.roots[i][0] * F.alpha) ** k
                                 for i in range(1, F.d)))))
    vals = []
    for k in range(n):
        if 1 <= h[k] <= 10 ** 7:
            lo, hi, _, _ = bern_cert(F, h[k])
            vals.append((h[k], float(lo), float(hi)))
        else:
            vals.append((h[k], None, None))
    return dict(h=h, amp=amp, rho_alpha=float(F.rho * F.alpha), phi=vals)


# ======================================================================================
# runs
# ======================================================================================
def run_roots(log=print):
    rows = []
    for coeffs in FAMILY:
        F = Field(coeffs)
        rows.append(dict(poly=F.name, d=F.d, alpha=float(F.alpha), rho=float(F.rho),
                         rad=float(F.rad), disjoint=bool(F.disjoint),
                         mods=[float(m) for m in F.mods], Ca=float(F.Ca),
                         rho_alpha=float(F.rho * F.alpha), unit=F.unit))
        r = rows[-1]
        log('%-14s d=%-3d alpha=%.9f  rho=%.9f  rho*alpha=%.5f  Smith radius %.2e  '
            'disjoint=%s  moduli %s'
            % (r['poly'], r['d'], r['alpha'], r['rho'], r['rho_alpha'], r['rad'],
               r['disjoint'], ' '.join('%.5f' % m for m in r['mods'])))
    return rows


def run_enc(log=print, H=HDEF):
    rows = []
    for coeffs in FAMILY[:7]:
        F = Field(coeffs)
        e60 = F.eps(60, 60)
        z60 = 2 * mp.pi * H * e60
        J, M = F.need(H)
        Jc, Mc = F.need(H, crude=True)
        s12 = F.best_window(12)
        c12 = F.best_window(12, crude=True)
        rows.append(dict(poly=F.name, d=F.d, alpha=float(F.alpha), rho=float(F.rho),
                         eps60=float(e60), rad60=float(z60), J=J, M=M, K=J + M + 1,
                         Jcrude=Jc, Mcrude=Mc, Kcrude=Jc + Mc + 1,
                         eps12=float(s12[0]), eps12_crude=float(c12[0]),
                         sharpen=float(c12[0] / s12[0]), rangeF=float(F.rangeF()),
                         eps12_frac=float(s12[0] / F.rangeF())))
        r = rows[-1]
        log('%-14s d=%-3d rho=%.6f | eps(60,60)=%.3e  2piH eps=%.3e  %-5s | need J=%-3d '
            'M=%-4d K=%-4d (crude K=%-4d) | eps at L=12: %.3e sharp (%.1f%% of range F = %.2f), '
            '%.3e crude (%.2fx)'
            % (r['poly'], r['d'], r['rho'], r['eps60'], r['rad60'],
               'OK' if r['rad60'] < 1e-13 else ('weak' if r['rad60'] < 1e-3 else 'NOISE'),
               r['J'], r['M'], r['K'], r['Kcrude'], r['eps12'], 100 * r['eps12_frac'],
               r['rangeF'], r['eps12_crude'], r['sharpen']))
    return rows


def run_bern(log=print, H=HDEF, Hs=(4, 16, 64, 256, 1024, 4096, 16384)):
    rows = []
    for coeffs in FAMILY[:7]:
        F = Field(coeffs)
        t0 = time.time()
        s = sup_cert(F, H)
        fl, nf, npast = bern_scan(F, max(Hs))
        argm = [int(np.argmax(fl[:h])) + 1 for h in Hs]
        supm = [float(fl[:h].max()) for h in Hs]
        blocks = []
        k = 0
        while 2 ** k < H:
            lo_, hi_ = 2 ** k, min(2 ** (k + 1), H)
            blocks.append([lo_, hi_, float(fl[lo_ - 1:hi_].max())])
            k += 1
        conc = s['lo'] / s['second']['ub_rest'] if s.get('second') else None
        rows.append(dict(poly=F.name, d=F.d, hstar=s['hstar'], lo=s['lo'], hi=s['hi'],
                         proved=s['proved'], K=s['K'], J=s['J'], M=s['M'],
                         ub_rest=s['ub_rest'], second=s['second'], conc=conc,
                         Hs=list(Hs), argmax=argm, sup=supm, blocks=blocks,
                         float_val=s['float_val'], secs=time.time() - t0))
        r = rows[-1]
        log('%-14s d=%-3d  sup|Phi| in [%.6e, %.6e] at h*=%-4d %-9s (K=%d, rest <= %.3e)'
            % (r['poly'], r['d'], r['lo'], r['hi'], r['hstar'],
               'PROVED' if r['proved'] else 'unproved', r['K'], r['ub_rest']))
        log('%-14s   argmax over H=%s : %s' % ('', list(Hs), argm))
        if r['second']:
            log('%-14s   sup_{h != h*} |Phi_h| <= %.4e (attained at h=%d, K=%d) %s ; '
                'concentration |Phi_{h*}|/sup_rest = %.4g'
                % ('', r['second']['ub_rest'], r['second']['h'], r['second']['K'],
                   'PROVED' if r['second']['proved'] else 'unproved', r['conc']))
    return rows


def run_plat(log=print):
    rows = []
    # trace ladder Tr(alpha^k) first (lambda = 1), then two other integer seeds; every
    # seed is chosen strictly positive so no rung lands on h = 0, where Phi_0 = 1.
    SEEDS = {}
    for c in FAMILY[:4]:
        Fx = Field(c)
        tr = tuple(Alpha(c).trace(k) for k in range(Fx.d))
        SEEDS[Fx.d] = [tr, tuple([1] * Fx.d), tuple(range(1, Fx.d + 1))]
    for coeffs in FAMILY[:4]:
        F = Field(coeffs)
        for seed in SEEDS[F.d]:
            b = thm_b(F, seed)
            pb = past_band(F, seed, n=12)
            good = [v for v in pb['phi'] if v[1] is not None]
            rows.append(dict(poly=F.name, d=F.d, seed=list(seed), rho=float(F.rho),
                             rho_alpha=pb['rho_alpha'], E=b['E'], K=b['K'],
                             worst=b['worst'], arg=b['arg'], amp=pb['amp'],
                             h=pb['h'], phi=pb['phi']))
            log('%-14s d=%-2d seed=%-12s | Thm B worst ratio %.4f at (i,j)=%s, E=%.4f K=%.4f | '
                'rho*alpha=%.4f | |Phi_{h_k}| %s'
                % (F.name, F.d, str(seed), b['worst'], b['arg'], b['E'], b['K'],
                   pb['rho_alpha'], ' '.join('%.2e' % v[1] for v in good[:8])))
    return rows


def run_read(log=print, H=HDEF):
    """The reading: what sec 7.2's column is worth once (1)-(3) are in."""
    rows = []
    for coeffs in FAMILY[:6]:
        F = Field(coeffs)
        s = sup_cert(F, H)
        r = s['lo']
        prop12 = float(mp.cos(mp.pi / F.alpha))
        L = F.gibbs_L(mp.mpf(r))
        e, past, fut = F.best_window(L)
        # R2a sec 8.1's own trust rule, `H eps_L <= 0.9`, at the folder's working
        # H = 64 and at this note's H.  R2a states the law in the abstract there --
        # "the reachable H is <~ 0.9/eps_L with eps_L ~ rho^{L/2}" -- and what follows
        # is that law instantiated at rho(d).
        Ltr64 = F.gibbs_L(mp.mpf('0.9') / 64)
        LtrH = F.gibbs_L(mp.mpf('0.9') / H)
        rows.append(dict(poly=F.name, d=F.d, residual_lo=s['lo'], residual_hi=s['hi'],
                         hstar=s['hstar'], prop12=prop12, slack=prop12 / r,
                         conc=(s['lo'] / s['second']['ub_rest']) if s.get('second') else None,
                         gibbsL=L, gibbs_eps=float(e), gibbs_split=[past, fut],
                         states=float(L * math.log10(2)),
                         Ltrust64=Ltr64, LtrustH=LtrH))
        q = rows[-1]
        log('%-14s d=%-3d | residual %.4e (h*=%d) | Prop.12 bound %.4f, slack %.3g | '
            'concentration %-9s | window L: trust rule %d (H=64) / %d (H=%d), residual scale %d '
            '(2^L = 1e%.1f, past %d / future %d)'
            % (q['poly'], q['d'], q['residual_lo'], q['hstar'], q['prop12'], q['slack'],
               ('%.4g' % q['conc']) if q['conc'] else '-', q['Ltrust64'], q['LtrustH'], H,
               q['gibbsL'], q['states'], past, fut))
    return rows


# ======================================================================================
def selfchecks(log=print):
    log('=== self-checks ===')
    F2 = Field([1, -2, -1], '1+sqrt2')
    s2 = mp.sqrt(2)
    check('d=2 alpha = 1+sqrt2', abs(F2.alpha - (1 + s2)) < mp.mpf('1e-190'),
          'alpha = %s' % mp.nstr(F2.alpha, 20))
    check('d=2 conjugate = 1-sqrt2, certified', abs(F2.conj[0][0] - (1 - s2)) < mp.mpf('1e-190')
          and F2.conj[0][1] < mp.mpf('1e-190'), 'Smith radius %.2e' % float(F2.rad))
    check('Smith discs disjoint at every degree in the family',
          all(Field(c).disjoint for c in FAMILY))
    # the cubic of the family is a unit with a complex pair, so rho = alpha^{-1/2}
    F3 = Field([1, -2, 0, -1])
    check('d=3: rho = alpha^{-1/2} (unit, one complex pair)',
          abs(F3.rho - F3.alpha ** mp.mpf('-0.5')) < mp.mpf('1e-30'),
          'rho = %.12f, alpha^-1/2 = %.12f' % (float(F3.rho), float(F3.alpha ** mp.mpf('-0.5'))))
    check('d=2 is the only member with rho*alpha = 1 (M7 Thm 10)',
          abs(F2.rho * F2.alpha - 1) < mp.mpf('1e-190')
          and all(Field(c).rho * Field(c).alpha > 1.4 for c in FAMILY[1:]))
    # (2) the window law reproduces R1a's degree-two eps_trunc exactly.  `r1a_enclose`
    # resets mp.mp.dps on import, so the working precision is restored afterwards.
    keep = mp.mp.dps
    import r1a_enclose as R
    mp.mp.dps = keep
    for J, M in ((10, 10), (40, 40), (60, 60)):
        mine = F2.eps(J, M)
        t = R.eps_trunc(J, M)
        ta, tb = mp.make_mpf(t._mpi_[0]), mp.make_mpf(t._mpi_[1])
        check('eps(%d,%d) matches r1a_enclose at 1+sqrt2' % (J, M),
              ta * (1 - mp.mpf('1e-25')) <= mine <= tb * (1 + mp.mpf('1e-25')),
              'mine %.6e, R1a [%.6e, %.6e]' % (float(mine), float(ta), float(tb)))
    check('per-conjugate tail <= max-rho tail, every degree',
          all(Field(c).eps(30, 30) <= Field(c).eps_crude(30, 30) * (1 + mp.mpf('1e-30'))
              for c in FAMILY))
    check('sharpening is strict from d=4 on',
          Field(FAMILY[3]).eps_crude(6, 6) > Field(FAMILY[3]).eps(6, 6) * mp.mpf('1.4'),
          'crude/sharp at L=12, d=4: %.3f'
          % float(Field(FAMILY[3]).eps_crude(6, 6) / Field(FAMILY[3]).eps(6, 6)))
    check("folder default (60,60) returns noise at d>=4, H=4096",
          2 * mp.pi * HDEF * Field(FAMILY[2]).eps(60, 60) > mp.mpf('0.9')
          and 2 * mp.pi * HDEF * Field(FAMILY[0]).eps(60, 60) < mp.mpf('1e-15'),
          '2piH eps = %.3e at d=4, %.3e at d=2'
          % (float(2 * mp.pi * HDEF * Field(FAMILY[2]).eps(60, 60)),
             float(2 * mp.pi * HDEF * Field(FAMILY[0]).eps(60, 60))))
    # (3) the certified Bernoulli value reproduces the float engine of M7 sec 8
    import m7_alpha2 as A
    for coeffs in FAMILY[:4]:
        F = Field(coeffs)
        al = Alpha(coeffs)
        fl, _, _ = A.bern(al, 512)
        h = int(np.argmax(fl)) + 1
        lo, hi, _, _ = bern_cert(F, h)
        check('d=%d certified |Phi_%d| brackets the M7 sec 8 float' % (F.d, h),
              lo <= mp.mpf(float(fl.max())) * (1 + mp.mpf('1e-12'))
              and mp.mpf(float(fl.max())) <= hi * (1 + mp.mpf('1e-12')),
              '[%.10e, %.10e] vs %.10e' % (float(lo), float(hi), fl.max()))
    check('enclosure is tight: relative width < 1e-20 at d=4, h=1',
          (lambda t: (t[1] - t[0]) / t[0] < mp.mpf('1e-20'))(bern_cert(Field(FAMILY[2]), 1)[:2]),
          'relative width %.2e'
          % float((lambda t: (t[1] - t[0]) / t[0])(bern_cert(Field(FAMILY[2]), 1)[:2])))
    # (4) Theorem B
    for coeffs, seed in ((FAMILY[0], (1, 3)), (FAMILY[1], (1, 0, 0)), (FAMILY[2], (1, 0, 0, 0))):
        F = Field(coeffs)
        b = thm_b(F, seed)
        check('Theorem B holds at d=%d (worst ratio <= 1)' % F.d, b['worst'] <= 1.0,
              'worst %.6f at (i,j)=%s' % (b['worst'], b['arg']))
    check('Theorem B is not vacuous (worst ratio > 0.01 somewhere)',
          thm_b(Field(FAMILY[0]), (1, 3))['worst'] > 0.01)
    # (5) the headline claims about sec 7.2's column
    F4 = Field(FAMILY[2])
    for coeffs in FAMILY[1:4]:
        F = Field(coeffs)
        fl, _, _ = bern_scan(F, 16384)
        check('d=%d: |Phi_h| is maximal at h=1 for every H <= 16384' % F.d,
              int(np.argmax(fl)) + 1 == 1,
              'argmax = %d, |Phi_1| = %.6e' % (int(np.argmax(fl)) + 1, fl[0]))
    fl2, _, _ = bern_scan(Field(FAMILY[0]), 16384)
    check('d=2: the maximiser is NOT h=1 (it is a ladder rung)',
          int(np.argmax(fl2)) + 1 == 3, 'argmax = %d' % (int(np.argmax(fl2)) + 1))
    check('R2a trust rule reproduces the folder\'s own L at 1+sqrt2, H=64',
          Field(FAMILY[0]).gibbs_L(mp.mpf('0.9') / 64) == 12,
          'L = %d' % Field(FAMILY[0]).gibbs_L(mp.mpf('0.9') / 64))
    check('the same rule asks for L=23 at d=3 and L=41 at d=4, H=64',
          Field(FAMILY[1]).gibbs_L(mp.mpf('0.9') / 64) == 23
          and F4.gibbs_L(mp.mpf('0.9') / 64) == 41)
    check('the L=12 window is 0.3% of range F at d=2 and 16% at d=4',
          Field(FAMILY[0]).best_window(12)[0] / Field(FAMILY[0]).rangeF() < mp.mpf('0.005')
          and F4.best_window(12)[0] / F4.rangeF() > mp.mpf('0.15'),
          '%.4f%% and %.2f%%' % (100 * float(Field(FAMILY[0]).best_window(12)[0]
                                             / Field(FAMILY[0]).rangeF()),
                                 100 * float(F4.best_window(12)[0] / F4.rangeF())))
    # the Pell ladder at 1+sqrt2 has ladder limit exactly 0: lambda(alpha-1) = 1/2
    a2 = F2.alpha
    check('Pell ladder at 1+sqrt2: lambda(alpha-1) = 1/2 exactly, so P(lambda) = 0',
          abs(1 / (2 * mp.sqrt(2)) * (a2 - 1) - mp.mpf('0.5')) < mp.mpf('1e-190'))
    log('# %d ok, %d FAILED' % (NCHECKS[0] - len(FAIL), len(FAIL)))
    return not FAIL


def main():
    cmd = sys.argv[1] if len(sys.argv) > 1 else 'all'
    out = {}
    if os.path.exists(OUT):
        try:
            out = json.load(open(OUT))
        except Exception:
            out = {}
    if cmd in ('checks', 'all'):
        out['checks'] = bool(selfchecks())
    if cmd in ('roots', 'all'):
        print('=== certified conjugates ===')
        out['roots'] = run_roots()
    if cmd in ('enc', 'all'):
        print('=== enclosure accounting ===')
        out['enc'] = run_enc()
    if cmd in ('bern', 'all'):
        print('=== the Bernoulli residual, certified ===')
        out['bern'] = run_bern()
    if cmd in ('plat', 'all'):
        print('=== the plateau, at degree d ===')
        out['plat'] = run_plat()
    if cmd in ('read', 'all'):
        print('=== the reading ===')
        out['read'] = run_read()
    out['meta'] = dict(dps=DPS, H=HDEF, tau=float(TAU), family=[str(c) for c in FAMILY])
    json.dump(out, open(OUT, 'w'), indent=1)
    print('-> %s' % OUT)
    return 1 if FAIL else 0


if __name__ == '__main__':
    sys.exit(main())
