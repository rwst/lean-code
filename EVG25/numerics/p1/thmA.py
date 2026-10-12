# (C) 2026 Ralf Stephan, in collaboration with Claude Code. Released under CC0 1.0 Universal.
"""P1 paper, Theorem A ingredients.
(G) beta = 3/2 itineraries d_k = floor(3 s_k/2), s_{k+1} = 3 s_k/2 - d_k, s in [0,1):
    (i) no 11; (ii) 101 is followed by 00000; max #1 in a window of length n <= (n+3)/3 (exhaustive over
    words obeying (i),(ii), and over itineraries of 20000 exact rational starting points).
(F1) U(n)+1 = V(n+1), V(m) = ceil(3m/2).   (F7) U^i(n+2^m) - U^i(n) = 3^i 2^(m-i), i <= m."""
from fractions import Fraction as F
import random
def U(n): return 3*n//2 + 1
def V(m): return -(-3*m//2)
assert all(U(n) + 1 == V(n + 1) for n in range(5000))
for m in range(1, 10):
    for n in range(300):
        a, b = n, n + 2**m
        for i in range(m + 1):
            assert b - a == 3**i * 2**(m - i); a, b = U(a), U(b)
print("F1, F7 ok")
# words obeying (i),(ii): max ones per length
best = {}
def dfs(w, ones):
    n = len(w); best[n] = max(best.get(n, 0), ones)
    if n == 26: return
    for c in (0, 1):
        x = w + [c]
        if len(x) >= 2 and x[-1] == x[-2] == 1: continue
        ok = True
        for p in range(len(x) - 2):          # 101 at p..p+2 must be followed by five 0s
            if x[p:p+3] == [1, 0, 1] and any(x[q] == 1 for q in range(p + 3, min(p + 8, len(x)))): ok = False; break
        if ok: dfs(x, ones + c)
dfs([], 0)
assert all(best[n] <= (n + 3) / 3 for n in best)
print("max ones (n: count):", {n: best[n] for n in range(0, 27, 3)}, " bound (n+3)/3 holds to n=26")
random.seed(1); worst = 0
for _ in range(20000):
    s = F(random.randrange(10**12), 10**12); d = []
    for _ in range(60):
        dk = (3 * s / 2) // 1; d.append(int(dk)); s = 3 * s / 2 - dk
    for k in range(59): assert not (d[k] == d[k+1] == 1)
    for k in range(52):
        if d[k:k+3] == [1, 0, 1]: assert d[k+3:k+8] == [0]*5
    for n in range(1, 61):
        for k in range(61 - n): worst = max(worst, sum(d[k:k+n]) - (n + 3) / 3)
print("itineraries: (i),(ii) hold; max(#ones - (n+3)/3) over all windows =", worst)
