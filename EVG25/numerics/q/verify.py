# (C) 2026 Ralf Stephan, in collaboration with Claude Code. Released under CC0 1.0 Universal.
"""Lemma Q route (plan-EVGQ17-M0, after M7): checks for Theorems A, B and the window formula.
(A) run lemma: a maximal run of steps with ||theta_s|| < 1/5 starting at s has length <= 1 + s*log2/log1.5;
    hence every chain has >= m(n) bad steps and prod|cos pi theta| <= cos(pi/5)^m(n).
(P) Parseval: subset sums sigma(v) are distinct mod 2^{j+1}; sum_k |S(k)|^2 = N 2^j.
(W) window formula: for n = N0 + r, r < 2^j,  b_j(n) = [ (n*(v) - N0) mod 2^{j+1} >= 2^j ],
    n*(v) = -sum_t (2 - v_t) 2^t 3^{-(t+1)}; so beta_j(N0) is the F1 count with a shift.
Usage: python3 verify.py"""
import math, itertools, cmath
from fractions import Fraction as Fr
ALPHA = math.log(2) / math.log(1.5)

def chains(n):
    """all chains theta_2..theta_{n+1} as numerators a_s/2^s (iterative DFS)"""
    stack = [(2, (1,)), (2, (3,))]
    while stack:
        s, path = stack.pop()
        if s == n + 1: yield path; continue
        a = path[-1]; b = (3 * a) % (1 << s)            # a_{s+1} = 3 a_s mod 2^s, plus 0 or 2^s
        stack.append((s + 1, path + (b,))); stack.append((s + 1, path + (b + (1 << s),)))

def dist(a, s):
    x = a / (1 << s); return min(x, 1 - x)

def m_lower(n):
    """guaranteed number of bad steps among s = 2..n+1 by the run lemma"""
    b, m = 2, 1
    while True:
        last = b + 1 + math.floor(1 + (b + 1) * ALPHA - 1e-12) - 1   # last index of longest run after b
        if last >= n + 1: return m
        b = last + 1; m += 1

def check_A(nmax=20):
    worst = 0
    for n in range(4, nmax + 1):
        best = 0.0; minbad = 10**9
        for ch in chains(n):
            s0 = 2; bad = 0; i = 0; P = 1.0
            run_start = None
            for idx, a in enumerate(ch):
                s = idx + 2; d = dist(a, s); P *= abs(math.cos(math.pi * a / (1 << s)))
                if d < 0.2:
                    if run_start is None: run_start = s
                    L = s - run_start + 1
                    worst = max(worst, (L - 1) / run_start)
                    assert L <= 1 + run_start * ALPHA + 1e-9, (n, ch, s)
                else:
                    run_start = None; bad += 1
            best = max(best, P); minbad = min(minbad, bad)
        m = m_lower(n)
        assert minbad >= m and best <= math.cos(math.pi / 5) ** m + 1e-12
        print(f"A n={n:2d}  min #bad={minbad:2d} >= m(n)={m}   max prod={best:.4g} <= cos(pi/5)^m={math.cos(math.pi/5)**m:.4g}")
    print(f"A worst (L-1)/start over all runs: {worst:.4f} (bound {ALPHA:.4f})")

def check_P(jmax=16):
    for j in range(2, jmax + 1):
        N = 1 << (j + 1); inv3 = pow(3, -1, N)
        xs = [(1 << t) * pow(inv3, t + 1, N) % N for t in range(j)]
        sums = {0}
        for x in xs: sums = sums | {(y + x) % N for y in sums}
        assert len(sums) == 1 << j
        # Parseval over odd k directly from the product form
        tot = 0.0
        for k in range(1, N, 2):
            p = 1.0
            for x in xs: p *= abs(2 * math.cos(math.pi * k * x / N))
            tot += p * p
        print(f"P j={j:2d}  distinct sums ok;  sum_odd |T_k|^2 / 2^(2j+1) = {tot / 2**(2*j+1):.4f}")

def U(n): return 3 * n // 2 + 1
def check_W(cases=((8, 0), (8, 12345), (10, 10**15 + 12345), (11, 2**100 + 77777777), (12, 987654321987))):
    for j, N0 in cases:
        N = 1 << (j + 1); inv3 = pow(3, -1, N); cnt = 0
        for r in range(1 << j):
            n = N0 + r; v = []; x = n
            for _ in range(j): v.append(x & 1); x = U(x)
            bj = x & 1
            nstar = -sum((2 - v[t]) * (1 << t) * pow(inv3, t + 1, N) for t in range(j)) % N
            assert bj == int((nstar - N0) % N >= (1 << j)), (j, N0, r)
            cnt += bj
        print(f"W j={j:2d} N0={N0}: window formula exact on all 2^j seeds; beta={cnt - (1 << (j-1))}")

if __name__ == "__main__":
    check_W(); check_P(); check_A()
