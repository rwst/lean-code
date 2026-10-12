# (C) 2026 Ralf Stephan, in collaboration with Claude Code. Released under CC0 1.0 Universal.
"""M7: reconstruct an extremal chain (max prod |cos pi theta_s|, s=2..n) by beam search with exact ints."""
import math, sys
n, W = int(sys.argv[1]), int(sys.argv[2])
beam = [(math.log2(math.cos(math.pi/4)), 1, [1]), (math.log2(abs(math.cos(3*math.pi/4))), 3, [3])]
for s in range(2, n):
    M = 1 << (s+1); nxt = []
    for lp, a, path in beam:
        for e in (0, 1):
            b = (3*a + (e << s)) % M
            nxt.append((lp + math.log2(abs(math.cos(math.pi*b/M))), b, path + [b]))
    nxt.sort(key=lambda t: -t[0]); beam = nxt[:W]
lp, a, path = beam[0]
print(f"n={n} log2 max ~ {lp:.3f} ({lp/n:.4f}/step)")
cum = 0
for s, a in enumerate(path, start=2):
    th = a/2**s; d = min(th, 1-th); c = -math.log2(abs(math.cos(math.pi*th))); cum += c
    tag = '0' if d < 0.08 else ('1/3' if abs(th-1/3) < 0.04 or abs(th-2/3) < 0.04 else '')
    print(f"{s:3d} theta={th:.6f} ||.||={d:.2e} cost={c:.3f} cum={cum:.2f} {tag}")
