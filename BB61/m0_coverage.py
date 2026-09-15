#!/usr/bin/env python3
# (C) 2026 Ralf Stephan, in collaboration with Claude Code
# CC0 1.0 Universal (public domain dedication).
"""M0 sec 5 -- Pisot enumeration and the two coverage no-gos.

Enumerates Pisot numbers of degree 2,3,4 and measures, for each: Route A's criterion
A = log2/log alpha + log2/log(1/rho), the window diameter D = sum |c_m|, and X7's Delta.
Establishes numerically the sharpness of  A >= d log2/log alpha  and  D >= d-1 > g.
"""
import itertools, json, numpy as np, math

def is_pisot_np(c, lo, hi, tol=1e-9):
    r = np.roots(np.array(c, dtype=float))
    big = [x for x in r if abs(x) > 1 + tol]
    if len(big) != 1: return None
    a = big[0]
    if abs(a.imag) > tol: return None
    a = a.real
    if a < lo or a > hi: return None
    if any(abs(abs(x) - 1) < 1e-7 for x in r): return None
    return a, r

def enum_pisot(deg, lo, hi):
    out = []
    Cb = [math.comb(deg - 1, k) for k in range(deg)] + [0]
    bnd = [int(hi * Cb[k - 1] + Cb[k]) + 1 for k in range(1, deg + 1)]
    R = [range(-b, b + 1) for b in bnd]
    for cs in itertools.product(*R):
        if cs[-1] == 0: continue
        p2 = 2 ** deg + sum(c * 2 ** (deg - 1 - i) for i, c in enumerate(cs))
        if p2 >= 0: continue
        ph = hi ** deg + sum(c * hi ** (deg - 1 - i) for i, c in enumerate(cs))
        if ph <= 0: continue
        c = [1] + list(cs)
        res = is_pisot_np(c, lo, hi)
        if res is None: continue
        out.append((res[0], c, res[1]))
    out.sort(key=lambda t: t[0])
    return out

def stats(a, roots):
    conj = np.array([z for z in roots if abs(z) < 1])
    rho = float(np.max(np.abs(conj)))
    M = int(20 * math.log(10) / math.log(1 / rho)) + 50
    pw = np.ones(len(conj), dtype=complex)
    D = 0.0
    for m in range(M):
        D += abs(float(np.real(np.sum((conj - 1) * pw))))
        pw = pw * conj
    Delta = float(np.sum(np.abs(conj - 1) / (1 - np.abs(conj))))
    A = math.log(2)/math.log(a) + math.log(2)/math.log(1/rho)
    g = (a - 2)/a
    return rho, D, Delta, A, g

if __name__ == '__main__':
    rows = []
    for d, hi in ((2, 22.0), (3, 12.0), (4, 9.0)):
        L = enum_pisot(d, 2.0, hi)
        sub = []
        for a, c, roots in L:
            rho, D, Delta, A, g = stats(a, roots)
            sub.append(dict(d=d, a=a, coeffs=c, rho=rho, unit=abs(c[-1]) == 1,
                            A=A, D=D, g=g, Delta=Delta))
        rows += sub
        fire = [r for r in sub if r['A'] < 1]
        print('deg %d: %d Pisot in (2,%g)' % (d, len(sub), hi))
        print('   RouteA (A<1) fires for %d; smallest alpha: %s   [2^d = %d]' %
              (len(fire), ('%.5f (A=%.4f, coeffs %s)' % (fire[0]['a'], fire[0]['A'], fire[0]['coeffs'])) if fire else '---', 2**d))
        print('   min D/g  = %8.4f    min 2Delta/g = %8.4f' %
              (min(r['D']/r['g'] for r in sub), min(2*r['Delta']/r['g'] for r in sub)))
        print('   min A*log2(alpha) = %.6f   (claim >= d)   min D = %.4f' %
              (min(r['A']*math.log(r['a'])/math.log(2) for r in sub), min(r['D'] for r in sub)))
    json.dump(rows, open('coverage.json', 'w'))
    print('total', len(rows))
