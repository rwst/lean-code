# (C) 2026 Ralf Stephan, in collaboration with Claude Code. Released under CC0 1.0 Universal.
"""M7: the dominant Fourier terms of beta_j and their chains (which k, how many near-zero steps)."""
import numpy as np, sys
for j in map(int, sys.argv[1:]):
    N = 1 << (j+1); inv3 = pow(3, -1, N)
    k = np.arange(1, N, 2, dtype=np.uint64); a = (k*np.uint64(inv3)) % np.uint64(N)
    lp = np.zeros(k.size); ph = np.zeros(k.size); sg = np.ones(k.size); nz = np.zeros(k.size, int)
    for s in range(j+1, 1, -1):
        th = a.astype(np.float64)/(1 << s); c = np.cos(np.pi*th)
        lp += np.log2(np.abs(c)); sg *= np.sign(c); ph += th/2; nz += (np.minimum(th, 1-th) < 0.08)
        if s > 2: a = (a*np.uint64(inv3)) % np.uint64(1 << (s-1))
    kk = k.astype(np.float64); h = 4/(N*(1-np.exp(-2j*np.pi*kk/N)))
    T = -0.5*h*sg*2.0**(lp+j)*np.exp(2j*np.pi*ph)
    o = np.argsort(-np.abs(T))[:6]
    ks = np.where(kk > N/2, kk-N, kk)
    print(f"j={j} beta={T.sum().real:.1f}")
    for i in o:
        print(f"   k={int(ks[i]):+9d}  |T|={abs(T[i]):7.1f}  Re T={T[i].real:+8.1f}  log2|P|={lp[i]+j:6.2f}  near-zero steps={nz[i]}/{j}  1/|k|-weight={abs(h[i]):.4f}")
