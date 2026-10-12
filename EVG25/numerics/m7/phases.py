# (C) 2026 Ralf Stephan, in collaboration with Claude Code. Released under CC0 1.0 Universal.
"""M7: is beta_j the size of a random-phase sum of its Fourier terms?  Compares |beta_j| with
R_j = sqrt(sum |T_k|^2) (T_k the terms of the Riesz formula) and with B_j = sum |T_k|."""
import numpy as np
rows = []
for j in range(10, 27):
    N = 1 << (j+1); inv3 = pow(3, -1, N)
    k = np.arange(1, N, 2, dtype=np.uint64); a = (k*np.uint64(inv3)) % np.uint64(N)
    lp = np.zeros(k.size); ph = np.zeros(k.size); sg = np.ones(k.size)
    for s in range(j+1, 1, -1):
        th = a.astype(np.float64)/(1 << s); c = np.cos(np.pi*th)
        lp += np.log2(np.abs(c)); sg *= np.sign(c); ph += th/2
        if s > 2: a = (a*np.uint64(inv3)) % np.uint64(1 << (s-1))
    kk = k.astype(np.float64); h = 4/(N*(1-np.exp(-2j*np.pi*kk/N)))
    T = -0.5*h*sg*2.0**(lp+j)*np.exp(2j*np.pi*ph)
    beta = T.sum().real; R = np.sqrt(np.sum(np.abs(T)**2)); B = np.abs(T).sum()
    rows.append((j, beta, R, B))
    print(f"j={j:2d} beta={beta:8.1f}  R_j={R:8.1f}  beta/R={beta/R:+.2f}  B_j={B:9.1f}  log2R/j={np.log2(R)/j:.3f}")
r = np.array([b/R for _, b, R, _ in rows]); print("rms(beta/R) =", np.sqrt(np.mean(r**2)))
