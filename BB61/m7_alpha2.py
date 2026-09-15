#!/usr/bin/env python3
# (C) 2026 Ralf Stephan, in collaboration with Claude Code
# CC0 1.0 Universal (public domain dedication).
"""M7: what happens to the certificate as alpha decreases to 2.

alpha = 2 is where 10.61 is *false*: C(2) = [0,1] and the fair coin already pushes
forward to Lebesgue.  The Pisot numbers accumulate at 2 from above along
x^{n+1} - 2 x^n - 1 (all units), so the whole certificate machine can be watched
degenerating along a sequence of genuine instances of the problem.

Three quantities are followed:
  * the Ledrappier-Young floor h_min(alpha) -> 0 and hence the budget log 2 - h_min
    -> log 2, its largest possible value;
  * the Bernoulli bias S(H) = sum_{h<=H} |Phi_h(mu_{1/2})|^2, the second-order gain a
    degree-H potential can extract (M3 sec 9.2), which -> 0 at every fixed H;
  * the proved bound |Phi_1(mu_{1/2})| <= cos(pi/alpha) = sin(pi(alpha-2)/(2 alpha)),
    which is linear in alpha - 2 (note-1061-M7.html Prop 9).

Writes m7_alpha2.json.
"""
import json, math
import numpy as np
from m0_engine import Alpha, is_pisot
from m3_entropy import h_min

H = 4096
FAMILY = [[1, -2] + [0] * (n - 1) + [-1] for n in range(1, 11)]
EXTRA = [([1, -2, -1], '1+sqrt2'), ([1, -3, 1], '(3+sqrt5)/2'),
         ([1, -3, -1], '(3+sqrt13)/2'), ([1, -4, 1], '2+sqrt3')]


def cms(al, M):
    """c_m, m = 0..M-1, by one complex recursion per conjugate (float is ample)."""
    out = np.zeros(M)
    for z in al.conj:
        zz = complex(z)
        p = 1.0 + 0j
        for m in range(M):
            out[m] += ((zz - 1.0) * p).real
            p *= zz
    return out


def bern(al, H, tol=1e-16):
    """|Phi_h(Bernoulli(1/2))| for h = 1..H: the two Erdos products."""
    a, rho = float(al.alpha), float(al.rho)
    h = np.arange(1, H + 1, dtype=float)
    out = np.ones(H)
    j = 1
    while (a - 1.0) * a ** (-j) * H > tol:
        out *= np.abs(np.cos(np.pi * h * (a - 1.0) * a ** (-j)))
        j += 1
    Ca = float(sum(abs(complex(z) - 1.0) for z in al.conj))
    M = int(math.log(tol / (H * max(Ca, 1e-9))) / math.log(rho)) + 2 if rho > 0 else 1
    c = cms(al, max(M, 1))
    for m in range(len(c)):
        if abs(c[m]) * H < tol:
            break
        out *= np.abs(np.cos(np.pi * h * c[m]))
    return out, j - 1, len(c)


if __name__ == '__main__':
    rows = []
    for coeffs in FAMILY + [c for c, _ in EXTRA]:
        if is_pisot(coeffs) is None:
            continue
        al = Alpha(coeffs)
        hm = h_min(al)
        bp, nfut, npast = bern(al, H)
        S = float(np.sum(bp ** 2))
        rows.append(dict(poly=al.polystr(), d=al.d, alpha=float(al.alpha), rho=float(al.rho),
                         h_min=hm, budget=math.log(2) - hm,
                         A=float(al.routeA()), sup=float(bp.max()),
                         argmax=int(np.argmax(bp) + 1), phi1=float(bp[0]),
                         bound1=math.cos(math.pi / float(al.alpha)), S=S,
                         ratio=(math.log(2) - hm) / max(S, 1e-300),
                         future_terms=nfut, past_terms=npast, H=H))
        r = rows[-1]
        print('%-22s d=%-3d alpha=%.7f  h_min=%.5f budget=%.5f  sup|Phi|=%.3e (h=%d)  '
              'Phi_1=%.3e <= %.3e  S(%d)=%.3e  budget/S=%.3e'
              % (r['poly'], r['d'], r['alpha'], r['h_min'], r['budget'], r['sup'],
                 r['argmax'], r['phi1'], r['bound1'], H, r['S'], r['ratio']), flush=True)
    
    json.dump(rows, open('m7_alpha2.json', 'w'), indent=1)
    print('-> m7_alpha2.json')
