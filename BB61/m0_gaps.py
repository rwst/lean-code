#!/usr/bin/env python3
# (C) 2026 Ralf Stephan, in collaboration with Claude Code
# CC0 1.0 Universal (public domain dedication).
"""M0 sec 6 -- certified gaps in the confinement set X(alpha) = (C - K) mod 1.

Over-approximates C and K by fattened interval unions, rasterises on a 2^21-bin circle
and circular-convolves by FFT; a zero run in the result is a genuine gap, hence a proof
that 10.61 holds at that alpha.  Sanity value: alpha = 3 returns 1/3, 1/9, 1/9.
"""
from m0_engine import *
import numpy as np, math, json

def C_points(al, M):
    """all partial sums (alpha-1) sum_{k=1}^{M} eps_k alpha^{-k}; tail error <= alpha^{-M}."""
    a = al.a
    v = np.zeros(1)
    for k in range(1, M + 1):
        v = np.concatenate([v, v + (a - 1) * a ** (-k)])
    return v, a ** (-M)

def K_points(al, M):
    """all partial sums sum_{m=0}^{M-1} c_m delta_m; tail error <= sum_{m>=M}|c_m|."""
    cm = al.c_m(M + 400)
    v = np.zeros(1)
    for m in range(M):
        v = np.concatenate([v, v + cm[m]])
    return v, float(sum(abs(c) for c in cm[M:]))

def support_gaps(al, G=1 << 21, maxpts=1 << 22):
    a = al.a
    M = min(int(math.log(G * 4) / math.log(a)) + 2, 22)
    Cv, Cerr = C_points(al, M)
    # choose K depth so that both the point count and the tail error are acceptable
    MK = 1
    while MK < 22:
        cm = al.c_m(MK + 400)
        tail = float(sum(abs(c) for c in cm[MK:]))
        if tail < 2.0 / G: break
        MK += 1
    if MK >= 22: return None, MK, None      # rho too close to 1 for this method
    Kv, Kerr = K_points(al, MK)
    if len(Cv) * 1.0 > maxpts or len(Kv) * 1.0 > maxpts: return None, MK, None
    err = Cerr + Kerr
    ib = int(math.ceil(err * G)) + 1
    mC = np.zeros(G, dtype=np.float32); mK = np.zeros(G, dtype=np.float32)
    np.add.at(mC, (np.round(Cv * G).astype(np.int64)) % G, 1.0)
    np.add.at(mK, (np.round((-Kv) * G).astype(np.int64)) % G, 1.0)
    S = np.fft.irfft(np.fft.rfft(mC) * np.fft.rfft(mK), G)
    occ = S > 1e-6 * max(1.0, S.max())
    # dilate by ib bins on both sides (over-approximation => a gap found is a true gap)
    k = 2 * ib + 1
    occ = np.convolve(np.concatenate([occ[-k:], occ, occ[:k]]).astype(np.float32),
                      np.ones(k, dtype=np.float32), 'same')[k:-k] > 0
    z = ~occ
    zz = np.concatenate([z, z])
    best = run = 0; pos = 0
    for i, v in enumerate(zz):
        run = run + 1 if v else 0
        if run > best: best, pos = run, i - run + 1
    return best / G, MK, (pos % G) / G

if __name__ == '__main__':
    CASES = [([1,-2,-1],'1+sqrt2'),([1,-3,1],'(3+sqrt5)/2'),([1,-3,-1],'(3+sqrt13)/2'),
             ([1,-4,1],'2+sqrt3'),([1,-4,2],'X^2-4X+2'),([1,-4,-1],'2+sqrt5'),([1,-5,1],'X^2-5X+1'),
             ([1,-3,2,-1],'X^3-3X^2+2X-1'),([1,-3,0,-1],'X^3-3X^2-1'),([1,-2,-1,-1],'X^3-2X^2-X-1'),
             ([1,-4,1,-1],'X^3-4X^2+X-1'),([1,-4,0,-1],'X^3-4X^2-1'),([1,-4,2,-1],'X^3-4X^2+2X-1'),
             ([1,-4,3,-1],'X^3-4X^2+3X-1'),([1,-5,4,-1],'X^3-5X^2+4X-1'),([1,-3],'alpha=3')]
    out=[]
    print('%-18s %9s %7s %7s %9s %10s %9s' % ('alpha','value','rho','Kdepth','gap len','gap at','routeA'))
    for c,n in CASES:
        al = Alpha(c,n)
        g,MK,pos = support_gaps(al)
        rA = al.routeA() if al.conj else 0.0
        print('%-18s %9.5f %7.4f %7d %9s %10s %9.4f' % (n, al.a, al.r, MK,
              ('%.5f'%g) if g is not None else 'n/a', ('%.4f'%pos) if pos is not None else '-', rA))
        out.append(dict(name=n,coeffs=c,alpha=al.a,rho=al.r,gap=g,pos=pos,routeA=rA))
    json.dump(out, open('gaps.json','w'))
