#!/usr/bin/env python3
# (C) 2026 Ralf Stephan, in collaboration with Claude Code
# CC0 1.0 Universal (public domain dedication).
"""M0 sec 3-4 -- vectorised mode scan and the trace ladder.

Finds the biased frequencies by evaluating the sec 3 closed form over h <= H, and
locates the plateaus along the integer solutions of alpha's linear recurrence
(= h_k = Tr(lambda alpha^k) for lambda in the codifferent).
"""
from m0_engine import *
import numpy as np, math, json

def Phi_vec(al, H, p=0.5, tol=1e-16):
    """Phi(h) for h = 1..H, vectorised.  Phi = Phi1*Phi2."""
    h = np.arange(1, H + 1, dtype=np.float64)
    a = al.a; am1 = a - 1.0
    J = int(math.log(H * am1 / tol) / math.log(a)) + 5
    P1 = np.ones(H)
    for j in range(1, J + 1):
        x = h * (am1 * a ** (-j))
        P1 *= np.sqrt(np.maximum(0.0, 1 - 4 * p * (1 - p) * np.sin(np.pi * x) ** 2))
    Ksum = float(sum(abs(z - 1) for z in al.conj)) or 1.0
    M = int(math.log(H * Ksum / tol) / math.log(1 / al.r)) + 5
    cm = al.c_m(M)
    P2 = np.ones(H)
    for c in cm:
        x = h * c
        P2 *= np.sqrt(np.maximum(0.0, 1 - 4 * p * (1 - p) * np.sin(np.pi * x) ** 2))
    return P1, P2

def ladder(al, lam_num, H):
    """integer solutions of alpha's linear recurrence: h_{k} = a1 h_{k-1} + ... (from minpoly)."""
    c = al.coeffs                      # X^d + c1 X^{d-1} + ... + cd
    d = al.d
    seq = list(lam_num)                # d initial integers
    while abs(seq[-1]) <= H:
        nxt = -sum(c[i + 1] * seq[-1 - i] for i in range(d))
        seq.append(nxt)
        if len(seq) > 200: break
    return [s for s in seq if 0 < s <= H]

CASES = [
    ([1,-2,-1], '1+sqrt2   (X^2-2X-1)'),
    ([1,-3, 1], '(3+sqrt5)/2 (X^2-3X+1)'),
    ([1,-3,-1], '(3+sqrt13)/2 (X^2-3X-1)'),
    ([1,-4, 1], '2+sqrt3   (X^2-4X+1)'),
    ([1,-4, 2], 'X^2-4X+2 (non-unit)'),
    ([1,-4,-1], '2+sqrt5   (X^2-4X-1)'),
    ([1,-1,-2,-1], 'X^3-X^2-2X-1'),
    ([1,-2, 0,-1], 'X^3-2X^2-1'),
    ([1,-3, 2,-1], 'X^3-3X^2+2X-1'),
    ([1,-2,-1,-1], 'X^3-2X^2-X-1'),
    ([1,-3, 0, 1], 'X^3-3X^2+1'),
    ([1,-3, 0,-1], 'X^3-3X^2-1'),
    ([1,-1,-2,-2], 'X^3-X^2-2X-2 (non-unit)'),
    ([1,-4, 0, 0,-1], 'X^4-4X^3-1'),
    ([1,-3], 'alpha=3 (integer, sanity)'),
]

if __name__ == '__main__':
    H = 200000
    out = []
    for coeffs, name in CASES:
        al = Alpha(coeffs, name)
        P1, P2 = Phi_vec(al, H)
        P = P1 * P2
        idx = np.argsort(-P)[:12]
        top = [(int(i + 1), float(P[i])) for i in idx]
        print('=' * 100)
        print('%-26s alpha=%.6f rho=%.5f d=%d unit=%d' % (name, al.a, al.r, al.d, al.unit))
        print('  top modes h<=%d : %s' % (H, ', '.join('%d:%.5f' % t for t in top[:8])))
        # ladders from small initial data
        best = None
        for init in [tuple(x) for x in np.ndindex(*([5] * al.d))]:
            if all(v == 0 for v in init): continue
            L = ladder(al, list(init), H)
            if len(L) < 6: continue
            v = float(P[L[-1] - 1]); v2 = float(P[L[-2] - 1])
            if abs(v - v2) < 5e-4 and (best is None or v > best[0]):
                best = (v, init, L[-6:])
        print('  best ladder    :', ('plateau=%.6f  init=%s  tail=%s' % best) if best else 'none')
        out.append(dict(coeffs=coeffs, name=name, alpha=al.a, rho=al.r, d=al.d, unit=al.unit,
                        top=top, plateau=(best[0] if best else None),
                        init=(list(best[1]) if best else None), tail=(best[2] if best else None)))
    json.dump(out, open('scan.json', 'w'))
