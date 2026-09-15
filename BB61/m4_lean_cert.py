#!/usr/bin/env python3
# (C) 2026 Ralf Stephan, in collaboration with Claude Code
# CC0 1.0 Universal (public domain dedication).
"""M4: generate the Lean-checkable pressure certificate at alpha = 2 + sqrt 3.

Everything in the window at this alpha lives in Z[sqrt 3] *exactly*, which is what makes
the certificate a finite list of integer facts:

  alpha = 2 + sqrt3,  alpha_2 = rho = 2 - sqrt3 = 1/alpha,  C_alpha = |alpha_2 - 1| = sqrt3 - 1,
  eps_{N,M} = alpha^-M + C_alpha rho^{N+1}/(1-rho) = (2-sqrt3)^3 + (2-sqrt3)^4
            = (2-sqrt3)^3 (3-sqrt3) = 123 - 71 sqrt3      (N = M = 3),

and each window weight is in Z[sqrt3] too:
  (alpha-1) alpha^-j  for j=1,2,3   = -1+sqrt3, -5+3sqrt3, -19+11sqrt3
  -c_m = -(alpha_2-1) alpha_2^m     = -1+sqrt3, -5+3sqrt3, -19+11sqrt3, -71+41sqrt3.

So the window value of every one of the 2^(L+1) = 128 words is an exact `A + B sqrt3`, the
cell it can occupy is decided by an integer comparison (square both sides), and the
transfer matrix has integer entries.  The certificate consumes
`ForMathlib/Combinatorics/PathGrowth.lean` (`psum`, `psum_le_pow`): a positive integer
vector `v` and a ratio `a/b` with `b * (M v) <= a * v` entrywise -- the elementary
Collatz-Wielandt shadow, already in the repo.

Criterion (note-1061-M4.html Theorem 1, mean-corrected form): with integer cell weights
`w_0..w_{B-1}` the potential is `g = log w_{cell}`, whose Lebesgue mean is
`(1/B) log W`, `W = prod w_j`, so 10.61 holds at alpha as soon as

    log(a/b) - (1/B) log W  <  h_min = (1/2) log alpha    <=>    (a/b)^B < W * alpha^{B/2}.

At B = 8 that is `a^8 < b^8 * W * alpha^4` with `alpha^4 = 97 + 56 sqrt3 > 193`, so the
sufficient integer check is `a^8 < b^8 * W * 193`.

Writes m4_lean_cert.json and BB61/Pressure_data.txt (the Lean literals).
"""
import sys, json
from fractions import Fraction as Fr
import numpy as np
sys.path.insert(0, '/home/ralf/math/lean-code/BB61')
from m0_engine import Alpha
from m3_entropy import Window, h_min
from m4_step import Cells, E

N = M = 3
L = N + M                      # 6 -> 64 states, 128 words
B = 8
SCALE = 24                     # integer cell weights w_j = round(SCALE * v_j)
KV = 400000                    # integer supereigenvector v = round(KV * perron)

# ---- exact Z[sqrt3] arithmetic: a pair (p, q) means p + q sqrt3 ----------------
def mul(x, y):
    return (x[0] * y[0] + 3 * x[1] * y[1], x[0] * y[1] + x[1] * y[0])

def add(x, y):
    return (x[0] + y[0], x[1] + y[1])

RT3 = 3 ** 0.5
def val(x):
    return x[0] + x[1] * RT3

rho = (2, -1)                                     # 2 - sqrt3
wt = [None] * (L + 1)
p = (1, 0)
for j in range(1, M + 1):                         # (alpha-1) alpha^-j = (1+sqrt3)(2-sqrt3)^j
    p = mul(p, rho)
    wt[N + j] = mul((1, 1), p)
p = (1, 0)
for m in range(0, N + 1):                         # -c_m = -(1-sqrt3)(2-sqrt3)^m
    wt[N - m] = mul((-1, 1), p)
    p = mul(p, rho)
EPS = (123, -71)                                  # (2-sqrt3)^3 (3-sqrt3)
assert abs(val(EPS) - ((2 - RT3) ** 3 + (2 - RT3) ** 4)) < 1e-12

def wordval(w):
    """exact window value of the (L+1)-bit word w, as an element of Z[sqrt3]."""
    x = (0, 0)
    for i in range(L + 1):
        if (w >> i) & 1:
            x = add(x, wt[i])
    return x

def cellfloor(x, k):
    """floor(B * (x + k*EPS)) by exact integer arithmetic (k = -1 or +1)."""
    y = add(x, (k * EPS[0], k * EPS[1]))
    z = (B * y[0], B * y[1])                      # z = P + Q sqrt3, want floor
    P, Q = z
    n = int(np.floor(P + Q * RT3))                # candidate, then certify exactly
    for cand in (n - 1, n, n + 1):
        if ge(z, cand) and not ge(z, cand + 1):
            return cand
    raise RuntimeError('floor failed')

def ge(x, n):
    """exact test  x[0] + x[1] sqrt3 >= n  for integers."""
    d = x[0] - n                                  # want d + x[1] sqrt3 >= 0
    if x[1] >= 0:
        return d >= 0 or d * d <= 3 * x[1] * x[1]
    return d >= 0 and d * d >= 3 * x[1] * x[1]

# ---- the float optimum, then integer weights ----------------------------------
al = Alpha([1, -4, 1], 'X^2-4X+1')
hm = h_min(al)
W = Window(al, N, M)
assert abs(W.err - val(EPS)) < 1e-12, (W.err, val(EPS))
cells = Cells(W, B)
for cap in (3.0, 6.0, 12.0):
    G, x, g, ub = E(cells, cap=cap)
    if np.isfinite(ub):
        break
print('float optimum: E=%.6f  ub=%.6f  h_min=%.6f' % (G, ub, hm))
w = [max(1, int(round(SCALE * float(np.exp(xx - x.min()))))) for xx in x]
print('integer cell weights:', w)

# ---- the exact transfer data --------------------------------------------------
lo = [cellfloor(wordval(word), -1) % B for word in range(1 << (L + 1))]
hi = [cellfloor(wordval(word), +1) % B for word in range(1 << (L + 1))]
assert lo == list(cells.lo) and hi == list(cells.hi), 'exact vs float cell mismatch'
print('cell tables agree with the float machine on all %d words' % (1 << (L + 1)))

t0 = [(u | (0 << L)) >> 1 for u in range(1 << L)]
t1 = [(u | (1 << L)) >> 1 for u in range(1 << L)]
w0 = [max(w[lo[u]], w[hi[u]]) for u in range(1 << L)]
w1 = [max(w[lo[u | (1 << L)]], w[hi[u | (1 << L)]]) for u in range(1 << L)]

# ---- Perron vector -> integer supereigenvector, then the ratio a/b ------------
r = np.ones(1 << L)
for _ in range(4000):
    rn = np.array([w0[u] * r[t0[u]] + w1[u] * r[t1[u]] for u in range(1 << L)])
    rn /= rn.max()
    if np.max(np.abs(rn - r)) < 1e-15:
        r = rn
        break
    r = rn
v = [max(1, int(round(KV * ri))) for ri in r]
S = [w0[u] * v[t0[u]] + w1[u] * v[t1[u]] for u in range(1 << L)]
ratio = max(Fr(S[u], v[u]) for u in range(1 << L))
b = 1 << 20
a = -((-ratio.numerator * b) // ratio.denominator)          # ceil(b * ratio)
assert all(b * S[u] <= a * v[u] for u in range(1 << L)), 'certificate fails'

Wprod = 1
for wj in w:
    Wprod *= wj
lam = a / b
rate = np.log(lam) - np.log(Wprod) / B
ok = a ** B < b ** B * Wprod * 193
print('a=%d  b=%d  lam=a/b=%.9f  W=%d' % (a, b, lam, Wprod))
print('certified rate = log(a/b) - (1/B) log W = %.6f   h_min = %.6f   margin %+.6f'
      % (rate, hm, hm - rate))
print('integer check  a^8 < b^8 * W * 193 :', ok)
print('   a^8      = %d' % a ** B)
print('   b^8*W*193= %d' % (b ** B * Wprod * 193))

json.dump(dict(alpha='2+sqrt3', N=N, M=M, L=L, B=B, eps=list(EPS), wt=[list(z) for z in wt],
               w=w, lo=lo, hi=hi, t0=t0, t1=t1, w0=w0, w1=w1, v=v, a=a, b=b, W=Wprod,
               rate=rate, h_min=hm, ok=bool(ok), float_E=G, float_ub=ub),
          open('m4_lean_cert.json', 'w'))

def lit(xs):
    return '#[' + ', '.join(str(int(z)) for z in xs) + ']'

with open('Pressure_data.txt', 'w') as f:
    f.write('-- generated by BB61/m4_lean_cert.py\n')
    f.write('def t0 : Array (Fin 64) := %s\n' % lit(t0))
    f.write('def t1 : Array (Fin 64) := %s\n' % lit(t1))
    f.write('def w0 : Array Nat := %s\n' % lit(w0))
    f.write('def w1 : Array Nat := %s\n' % lit(w1))
    f.write('def vv : Array Nat := %s\n' % lit(v))
    f.write('def aa : Nat := %d\ndef bb : Nat := %d\ndef WW : Nat := %d\n' % (a, b, Wprod))
    f.write('def cw : Array Nat := %s\n' % lit(w))
print('wrote m4_lean_cert.json and Pressure_data.txt')
