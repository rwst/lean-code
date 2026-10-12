# (C) 2026 Ralf Stephan, in collaboration with Claude Code. Released under CC0 1.0 Universal.
"""Independent exact-integer check of horizon.c (plan-EVGQ17-M0, M6, risk R-5/R-6).

Recomputes every statistic of horizon.c with Python big integers and the literal
definition U(n) = floor(3n/2) + 1 (no modular arithmetic), and compares field by field.
Usage: python3 crosscheck.py path/to/horizon j K [N0]
"""
import json, subprocess, sys

def stats(j, K, N0):
    R, half = 1 << j, 1 << (j - 1)
    odd = [0] * K; sD = [0] * (K + 1); sD2 = [0] * (K + 1); tail = [0] * (K + 1)
    xr = {d: [0] * (K - d) for d in (1, 2, 3)}; blk = [0] * 256; pair = 0
    for r in range(R):
        n = N0 + r; b = []
        for _ in range(K):
            b.append(n % 2); n = 3 * n // 2 + 1
        S = 0
        for i in range(K):
            S += b[i]; k = i + 1; D = 2 * S - k
            sD[k] += D; sD2[k] += D * D
            if 10 * abs(D) > 3 * k: tail[k] += 1
            odd[i] += b[i]
        for d in (1, 2, 3):
            for i in range(K - d): xr[d][i] += b[i] ^ b[i + d]
        blk[int("".join(map(str, b[j:j + 8])), 2)] += 1
        if r < half and b[j - 1] == (j & 1): pair += 2 * b[j] - 1
    out = dict(beta=odd[j] - half, pair=pair, odd=odd, sD=sD, sD2=sD2, tail=tail, blk=blk)
    for d in (1, 2, 3): out[f"xr{d}"] = xr[d]
    return out

exe, j, K = sys.argv[1], int(sys.argv[2]), int(sys.argv[3])
N0 = int(sys.argv[4]) if len(sys.argv) > 4 else 0
c = json.loads(subprocess.run([exe, str(j), str(K), str(N0), "2"], capture_output=True, text=True, check=True).stdout)
p = stats(j, K, N0)
bad = [f for f in p if [int(v) for v in (c[f] if isinstance(c[f], list) else [c[f]])] != (p[f] if isinstance(p[f], list) else [p[f]])]
print(f"j={j} K={K} N0={N0}: " + ("MATCH" if not bad else f"MISMATCH in {bad}"))
sys.exit(1 if bad else 0)
