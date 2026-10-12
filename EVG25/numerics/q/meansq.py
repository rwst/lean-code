# (C) 2026 Ralf Stephan, in collaboration with Claude Code. Released under CC0 1.0 Universal.
"""Averaging route check.
(1) Parseval in the window variable: mean_{N0 mod 2^{j+1}} beta_j(N0)^2 = sum_{k odd} |g^(k)|^2 |S(k)|^2,
    verified against brute force for small j; then RMS_j and max_N0 |beta_j(N0)| vs |S(1)|/pi.
(2) single frequencies: log2 P_k(j) / j for fixed k up to j = 3000."""
import math, sys
def U(n): return 3*n//2 + 1
def S_abs(k, j):
    N = 1 << (j+1); inv3 = pow(3, -1, N); p = 1.0; x = inv3
    for t in range(j):
        p *= abs(2*math.cos(math.pi*k*x/N)); x = (2*x*inv3) % N
    return p
def g_abs(k, j):
    N = 1 << (j+1); return 1/(N*abs(math.sin(math.pi*k/N)))
def brute(j):
    N = 1 << (j+1); bits = []
    for n in range(N + (1 << j)):
        x = n
        for _ in range(j): x = U(x)
        bits.append(x & 1)
    b = [sum(bits[N0:N0 + (1 << j)]) - (1 << (j-1)) for N0 in range(N)]
    return sum(v*v for v in b)/N, max(map(abs, b))
for j in range(3, 13):
    ms, mx = brute(j)
    f = sum(g_abs(k, j)**2 * S_abs(k, j)**2 for k in range(1, 1 << (j+1), 2))
    print(f"j={j:2d} mean beta^2 brute={ms:.4f} fourier={f:.4f}   max|beta|={mx}  |S(1)|*|g(1)|={S_abs(1,j)*g_abs(1,j):.2f}")
print("RMS over windows (Fourier side):")
for j in (14, 16, 18, 20):
    f = sum(g_abs(k, j)**2 * S_abs(k, j)**2 for k in range(1, 1 << (j+1), 2))
    print(f"j={j:2d} RMS={math.sqrt(f):9.2f}  log2 RMS / j = {math.log2(math.sqrt(f))/j:.3f}   coin scale 2^(j/2)/2 -> {0.5 - 1/j:.3f}")
print("single frequencies, log2 P_k(j)/j:")
def logP(k, j):
    t = 0.0
    for s in range(2, j + 2):
        M = 1 << s; a = (k * pow(3, -(j + 2 - s), M)) % M
        t += math.log2(abs(math.cos(math.pi * (a / M))) + 1e-300)
    return t
for k in (1, -1, 5, 7, -7, 11):
    print(f"k={k:3d} " + " ".join(f"{logP(k, j)/j:6.3f}" for j in (50, 100, 200, 400, 800, 1600, 3000)))
