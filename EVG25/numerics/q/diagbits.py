# (C) 2026 Ralf Stephan, in collaboration with Claude Code. Released under CC0 1.0 Universal.
"""k=1 core: theta at r = j+2-s is (3^{-r} mod 2^m)/2^m, m=j+2-r; ||theta||>=1/4 iff bits m-1, m-2 of the
2-adic integer 3^{-r} differ.  Prints the proportion of r<=j with differing 'diagonal' bits (random: 1/2)."""
for j in (100, 500, 1000, 2000, 4000):
    M = 1 << (j + 2); inv = pow(3, -1, M); x = 1; cnt = 0
    for r in range(1, j + 1):
        x = x * inv % M; m = j + 2 - r
        cnt += ((x >> (m - 1)) & 1) != ((x >> (m - 2)) & 1) if m >= 2 else 0
    print(f"j={j:5d}  proportion of differing diagonal bit pairs = {cnt / j:.4f}")
