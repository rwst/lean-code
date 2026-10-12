# (C) 2026 Ralf Stephan, in collaboration with Claude Code. Released under CC0 1.0 Universal.
"""M7: check the exact reformulations of beta_j (plan-EVGQ17-M0, H_1).
(1) beta_j = sum_{v in {0,1}^j} (bit_j(z_v) - 1/2),  z_v = sum_t v_t 2^t 3^{-(t+1)} mod 2^{j+1}
(2) beta_j = -(1/2) sum_{k odd mod N} hhat(k) prod_{s=2}^{j+1} (1 + e(theta_s(k))),
    N = 2^{j+1}, hhat(k) = 4/(N(1-e(-k/N))), theta_s(k) = (k 3^{-(j+2-s)} mod 2^s)/2^s.
"""
import cmath, itertools
def U(n): return 3*n//2 + 1
def beta(j):
    c = 0
    for r in range(1 << j):
        x = r
        for _ in range(j): x = U(x)
        c += x & 1
    return c - (1 << (j-1))
def beta1(j):
    N = 1 << (j+1); inv3 = pow(3, -1, N)
    xs = [(1 << t) * pow(inv3, t+1, N) % N for t in range(j)]
    tot = 0
    for v in itertools.product((0,1), repeat=j):
        z = sum(x for x, b in zip(xs, v) if b) % N
        tot += (z >> j) & 1
    return tot - (1 << (j-1))
def e(x): return cmath.exp(2j*cmath.pi*x)
def beta2(j):
    N = 1 << (j+1); tot = 0
    for k in range(1, N, 2):
        h = 4/(N*(1-e(-k/N)))
        p = 1
        for s in range(2, j+2):
            th = (k * pow(3, -(j+2-s), 1 << s) % (1 << s)) / (1 << s)
            p *= 1 + e(th)
        tot += h*p
    return -tot/2
for j in range(2, 15):
    b, b1, b2 = beta(j), beta1(j), beta2(j)
    print(j, b, b1, round(b2.real, 6), round(b2.imag, 9))
