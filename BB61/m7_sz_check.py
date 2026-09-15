#!/usr/bin/env python3
# (C) 2026 Ralf Stephan, in collaboration with Claude Code
# CC0 1.0 Universal (public domain dedication).
"""L0 batch 7 -- verification list for note-1061-L0-batch7.html.

Checks the five claims the note makes about [Ber92] Ch. 15 (the Salem-Zygmund
theorem) against this repo's own objects:

  V1  E_theta = (theta/(theta-1)) C(alpha)                     (Def. 15.3.1 vs the plan)
  V2  theta^j E_theta  subset  Lambda_theta + E_theta          (sec 15.4.3 = M1 Prop. 4)
  V3  Prop. 15.3.2: Gamma_theta decays iff theta is not Pisot  (= M3 sec 3.3)
  V4  Thm 15.5.1 (Senge-Strauss): Gamma_theta Gamma_phi -> 0 iff log ratio irrational
  V5  |Phi_h(mu_1/2)| = |Gamma_alpha(h(alpha-1)/alpha)| * |Gamma_alpha(h(alpha+e)/alpha)|
      with e = -1 at norm +1 (folding, M5 F5) and the alternating form at norm -1
"""
import sys
import numpy as np
from mpmath import mp, mpf, cos, pi, sqrt, log, fabs
from m0_engine import Alpha
from m3_entropy import bern_phi

mp.dps = 120
OK = []


def report(tag, ok, msg):
    OK.append(bool(ok))
    print('%-4s %s  %s' % (tag, 'PASS' if ok else 'FAIL', msg))


def Gamma(th, xi, K=400):
    """Gamma_theta(xi) = prod_{k>=0} cos(pi xi theta^{-k}), in high precision."""
    p, x = mpf(1), mpf(xi)
    for k in range(K):
        t = x / th**k
        if fabs(t) < mpf(10)**(-mp.dps + 20):
            break
        p *= cos(pi * t)
    return p


def Pn(th, u, n):
    """P_n(u) = prod_{k=0}^{n} cos(pi u theta^k)."""
    p, x = mpf(1), mpf(u)
    for k in range(n + 1):
        p *= cos(pi * x * th**k)
    return p


# ---------------------------------------------------------------- V1
def v1():
    worst = 0.0
    rng = np.random.default_rng(7)
    for coeffs in ([1, -2, -1], [1, -3, 1], [1, -4, 1], [1, -4, -3, -1]):
        al = Alpha(coeffs)
        th = mp.mpf(al.alpha)
        for _ in range(20):
            eps = rng.integers(0, 2, 200)
            # E_theta point: sum_{k>=0} eps_k theta^{-k}
            E = sum(mpf(int(e)) / th**k for k, e in enumerate(eps))
            # C(alpha) point on the shifted word: (alpha-1) sum_{j>=1} eps_{j-1} alpha^{-j}
            C = (th - 1) * sum(mpf(int(eps[j - 1])) / th**j for j in range(1, len(eps) + 1))
            worst = max(worst, float(fabs(E - th / (th - 1) * C)))
    report('V1', worst < 1e-90,
           'E_theta = (theta/(theta-1)) C(alpha) on 80 words, 4 alpha: max dev %.1e' % worst)


# ---------------------------------------------------------------- V2
def v2():
    worst, bad = 0.0, 0
    rng = np.random.default_rng(11)
    for coeffs in ([1, -2, -1], [1, -3, 1], [1, -4, 1], [1, -4, -3, -1], [1, -6, 3, -1]):
        al = Alpha(coeffs)
        th = mp.mpf(al.alpha)
        top = th / (th - 1)                       # sup E_theta
        for _ in range(10):
            eps = rng.integers(0, 2, 400)
            E = sum(mpf(int(e)) / th**k for k, e in enumerate(eps))
            for j in range(1, 25):
                lam = sum(mpf(int(eps[k])) * th**(j - k) for k in range(j))   # in Lambda_theta
                tail = th**j * E - lam
                if not (mpf(0) <= tail <= top + mpf(10)**(-80)):
                    bad += 1
                # tail must be the shifted E_theta point
                E2 = sum(mpf(int(eps[j + i])) / th**i for i in range(len(eps) - j))
                worst = max(worst, float(fabs(tail - E2)))
    report('V2', bad == 0 and worst < 1e-60,
           'theta^j E \\subset Lambda + E, j<=24, 50 words, 5 alpha: %d escapes, max dev %.1e'
           % (bad, worst))


# ---------------------------------------------------------------- V3
def v3():
    al = Alpha([1, -2, -1])
    th = mp.mpf(al.alpha)                                   # 1+sqrt2, Pisot
    s = sum(mp.sin(pi * th**k)**2 for k in range(1, 200))
    tail = sum(mp.sin(pi * th**k)**2 for k in range(100, 200))   # convergence, not smallness
    lo = min(float(fabs(Gamma(th, th**n))) for n in range(1, 40))
    ok1 = float(tail) < 1e-40 and lo > 1e-3

    nonpisot = mpf(5) / 2                                    # 2.5 > 2, not an algebraic integer
    us = [mpf(1) + mpf(i) * (nonpisot - 1) / 40 for i in range(41)]
    mx = [max(float(fabs(Pn(nonpisot, u, n))) for u in us) for n in (5, 10, 20, 40, 80)]
    ok2 = mx[-1] < 1e-6 and all(mx[i + 1] < mx[i] for i in range(len(mx) - 1))
    report('V3', ok1 and ok2,
           'Pisot: sum sin^2 = %.4f (tail k>=100: %.1e), inf_n |Gamma(theta^n)| = %.4f ; '
           'non-Pisot 5/2: max|P_n| = %s'
           % (float(s), float(tail), lo, ' '.join('%.1e' % m for m in mx)))


# ---------------------------------------------------------------- V4
def v4():
    th = mp.mpf(Alpha([1, -2, -1]).alpha)                  # theta = 1+sqrt2
    ph = th**2                                              # phi = theta^2, log ratio = 1/2
    vals = [float(fabs(Gamma(th, ph**r) * Gamma(ph, ph**r))) for r in range(1, 14)]
    ok1 = min(vals) > 1e-3

    ph2 = mp.mpf(Alpha([1, -3, 1]).alpha)                   # phi = (3+sqrt5)/2
    ratio = float(log(th) / log(ph2))
    mx = []
    for m in range(2, 9):
        U = [mpf(10)**m * (1 + mpf(i) / 400) for i in range(401)]
        mx.append(max(float(fabs(Gamma(th, u) * Gamma(ph2, u))) for u in U))
    ok2 = mx[-1] < mx[0] / 4
    report('V4', ok1 and ok2,
           'rational log-ratio: inf_r |Gamma_th Gamma_phi|(omega^r) = %.4f (r<=13); '
           'irrational (ratio %.4f): max over 10^m windows = %s'
           % (min(vals), ratio, ' '.join('%.1e' % m for m in mx)))


# ---------------------------------------------------------------- V5
def v5():
    H, worst_p, worst_m = 24, 0.0, 0.0
    lines = []
    for coeffs, nm in (([1, -3, 1], '(3+sqrt5)/2'), ([1, -4, 1], '2+sqrt3'),
                       ([1, -2, -1], '1+sqrt2'), ([1, -6, 1], '3+2sqrt2')):
        al = Alpha(coeffs)
        th = mp.mpf(al.alpha)
        norm = al.coeffs[-1] * (-1)**al.d          # N(alpha) = (-1)^d a_d
        phi = bern_phi(al, H)
        fut = np.array([float(fabs(Gamma(th, mpf(h) * (th - 1) / th))) for h in range(1, H + 1)])
        if norm > 0:                               # folding: past = future
            dev = float(np.max(np.abs(phi - fut**2)))
            worst_p = max(worst_p, dev)
            lines.append('%s N=+1 |Phi_h|=Gamma^2 dev %.1e' % (nm, dev))
        else:                                      # past uses (alpha+1)/alpha, alternating
            pst = np.array([float(fabs(Gamma(th, mpf(h) * (th + 1) / th))) for h in range(1, H + 1)])
            dev = float(np.max(np.abs(phi - fut * pst)))
            worst_m = max(worst_m, dev)
            lines.append('%s N=-1 |Phi_h|=Gamma((a-1)/a)Gamma((a+1)/a) dev %.1e' % (nm, dev))
    report('V5', worst_p < 1e-12 and worst_m < 1e-12, ' | '.join(lines))


if __name__ == '__main__':
    v1(); v2(); v3(); v4(); v5()
    print('\n%d/%d checks pass' % (sum(OK), len(OK)))
    sys.exit(0 if all(OK) else 1)
