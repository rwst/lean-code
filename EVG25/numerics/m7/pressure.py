# (C) 2026 Ralf Stephan, in collaboration with Claude Code. Released under CC0 1.0 Universal.
"""M7: growth rates. Z_n = sum over chains (theta_2..theta_{n+1}) of prod|cos pi theta_s| (exact enumeration),
B_j = beta-majorant; rho = spectral radius of (Lf)(t) = sum_{children u of t} |cos pi u| f(u), children 3t/2, 3t/2+1/2,
computed via its adjoint, the IFS transfer operator (Pd)(x) = (2/3)|cos pi x| sum_{m=0,1,2} d((2x+m)/3), on a grid."""
import numpy as np
# rho by power iteration on a grid (piecewise-linear interpolation)
G = 1 << 16; x = (np.arange(G) + 0.5)/G; d = np.ones(G)
for it in range(200):
    nd = np.zeros(G)
    for m in range(3):
        y = ((2*x + m)/3) % 1.0
        nd += np.interp(y, x, d, period=1.0)
    nd *= (2/3)*np.abs(np.cos(np.pi*x))
    lam = nd.sum()/d.sum(); d = nd/nd.max()
print(f"rho ~ {lam:.6f}   log2 rho = {np.log2(lam):.5f}   4/pi = {4/np.pi:.6f}")
print(f"eigendensity h: max/min = {d.max()/d.min():.3f}, h(0)={np.interp(0.0,x,d,period=1):.3f}, h(1/3)={np.interp(1/3,x,d):.3f}, h(1/2)={np.interp(0.5,x,d):.3f}")
np.save('/home/ralf/.claude/jobs/903fe39f/tmp/h.npy', d)
# exact Z_n and B_j
for j in range(8, 25, 2):
    N = 1 << (j+1); inv3 = pow(3, -1, N)
    k = np.arange(1, N, 2, dtype=np.uint64); a = (k*np.uint64(inv3)) % np.uint64(N)
    la = np.zeros(k.size); th_end = a.astype(np.float64)/N
    for s in range(j+1, 1, -1):
        la += np.log2(np.abs(np.cos(np.pi*a.astype(np.float64)/(1 << s))))
        if s > 2: a = (a*np.uint64(inv3)) % np.uint64(1 << (s-1))
    P = 2.0**la; Z = P.sum()/2   # per root average (two roots)
    w = 1/np.abs(np.sin(3*np.pi*th_end))
    B = 0.5*np.sum(P*w)
    print(f"j={j:2d}  Z/rho^j={Z/lam**j:8.4f}  B_j={B:10.1f}  B/(Z)={B/Z:7.2f}  B/(Z j)={B/Z/j:.3f}")
