# (C) 2026 Ralf Stephan, in collaboration with Claude Code. Released under CC0 1.0 Universal.
"""M7: anatomy of the Riesz-product formula for beta_j.
For each odd k mod N=2^{j+1}: chain theta_s(k), s=2..j+1, product P(k)=prod (1+e(theta_s)),
weight hhat(k). Reports: beta_j (check), the bound B_j = 1/2 sum |hhat||P|, the share of beta_j
carried by |k| <= K, and max_k log2 prod |cos pi theta_s| (worst chain)."""
import numpy as np, sys
def run(j):
    N = 1 << (j+1); inv3 = pow(3, -1, N)
    k = np.arange(1, N, 2, dtype=np.uint64)
    a = (k * np.uint64(inv3)) % np.uint64(N)          # a_{j+1}
    logabs = np.zeros(k.size); phase = np.zeros(k.size)
    for s in range(j+1, 1, -1):
        th = a.astype(np.float64) / float(1 << s)
        c = np.cos(np.pi*th)
        logabs += np.log2(np.abs(c)); phase += th/2  # 1+e(th) = 2cos(pi th) e(th/2)
        if s > 2: a = (a * np.uint64(inv3)) % np.uint64(1 << (s-1))
    sign = np.sign(np.cos(np.pi*0))  # placeholder
    # recompute signed product exactly: prod 2cos * e(sum th/2)
    kk = k.astype(np.float64); ks = np.where(kk > N/2, kk - N, kk)   # symmetric rep
    h = 4/(N*(1-np.exp(-2j*np.pi*kk/N)))
    return k, ks, h, logabs, phase
def analyze(j):
    k, ks, h, logabs, phase = run(j)
    N = 1 << (j+1)
    # signed product needs sign of each cos: redo cheaply
    inv3 = pow(3, -1, N); a = (k*np.uint64(inv3)) % np.uint64(N); sg = np.ones(k.size)
    for s in range(j+1, 1, -1):
        sg *= np.sign(np.cos(np.pi*a.astype(np.float64)/(1 << s)))
        if s > 2: a = (a*np.uint64(inv3)) % np.uint64(1 << (s-1))
    P = sg * 2.0**(logabs + j) * np.exp(2j*np.pi*phase)
    terms = -0.5*h*P
    beta = terms.sum().real
    B = 0.5*np.sum(np.abs(h)*np.abs(P))
    order = np.argsort(np.abs(ks)); cum = np.cumsum(terms[order]).real
    share = {K: cum[np.searchsorted(np.abs(ks)[order], K, side='right')-1] for K in (1, 3, 9, 27, 81, 243, 729)}
    print(f"j={j:2d} beta={beta:9.2f}  B_j={B:12.1f} log2B/j={np.log2(B)/j:.3f}  max log2prod|cos|/j={logabs.max()/j:+.3f}"
          f"  partial sums |k|<=K: " + " ".join(f"{K}:{v:.0f}" for K, v in share.items()))
    return logabs.max()
for j in range(int(sys.argv[1]), int(sys.argv[2])+1):
    analyze(j)
