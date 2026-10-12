# (C) 2026 Ralf Stephan, in collaboration with Claude Code. Released under CC0 1.0 Universal.
"""Decay of the small-frequency chains, the only ones that matter after the Parseval split.
P_k(j) = prod_{s=2}^{j+1} |cos pi theta_s(k)|, theta_s(k) = (k 3^{-(j+2-s)} mod 2^s)/2^s.
Prints log2 max_{|k|<=K, k odd, 3 not| k} P_k(j) / j and the arg max."""
import math
def logP(k, j):
    t = 0.0
    for s in range(2, j + 2):
        M = 1 << s; a = (k * pow(3, -(j + 2 - s), M)) % M
        t += math.log2(abs(math.cos(math.pi * a / M)) + 1e-300)
    return t
for K in (64, 1024):
    print("K =", K)
    for j in (16, 24, 32, 48, 64, 96, 128, 192, 256):
        best = max((logP(s * k, j), s * k) for k in range(1, K + 1, 2) if k % 3 for s in (1, -1))
        print(f"  j={j:4d}  max log2 P = {best[0]:8.2f}  per step {best[0]/j:7.4f}  at k={best[1]}")
