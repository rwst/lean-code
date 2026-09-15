#!/usr/bin/env python3
# (C) 2026 Ralf Stephan, in collaboration with Claude Code
# CC0 1.0 Universal (public domain dedication).
"""M5 sec 8: the memory ladder.  Markov measures of memory k on {0,1}^Z.

Same conditional-independence trick as m5_markov.py, one block wider: given the k-block
B = (omega_{-k+1},...,omega_0) at the origin, the future (omega_1,...) and the strict past
(omega_{-k},...) are independent, so

  G_P(h) = sum_B pi_B e(-h sum_{i<k} c_i B_i) u_B(h) v_B(h),

  v_B = E[ e(h sum_{j>=1} x_j omega_j) | B ]        (block chain, emits the new symbol)
  u_B = E[ e(-h sum_{m>=k} c_m omega_{-m}) | B ]    (reversed block chain).

Memory-k measures are weak-* dense in the invariant measures as k -> infinity, so
   Psi_k(alpha) := min over memory-k P of  max_{1<=h<=H} |G_P(h)|
is a decreasing sequence whose limit is 0 exactly when 10.61 fails at alpha (up to the
truncation of h).  Every computed value is a lower bound for sup over all h.
"""
import numpy as np
from m0_engine import Alpha


class Memory:
    """Block-chain machinery for memory k at a fixed alpha."""

    def __init__(self, al: Alpha, k=1, hmax=32, tol=1e-15):
        a, rho = float(al.alpha), float(al.rho)
        Ca = float(sum(abs(complex(z) - 1) for z in al.conj)) or 1.0
        self.k, self.n = k, 1 << k
        self.mask = self.n - 1
        self.J = int(np.log(max(hmax, 1) * (a - 1) / tol) / np.log(a)) + 3
        self.M = int(np.log(max(hmax, 1) * Ca / (tol * (1 - rho))) / np.log(1 / rho)) + 3 + k
        self.x = np.array([(a - 1) * a ** (-j) for j in range(1, self.J + 1)])
        self.c = np.array(al.c_m(self.M + 1))
        # forward: b -> b' = ((b<<1)|s) & mask, emitting s = b' & 1
        # backward: b -> b'' = (b>>1) | (r << (k-1)), emitting r = b'' >> (k-1)
        self.fwd = np.array([[((b << 1) | s) & self.mask for s in (0, 1)]
                             for b in range(self.n)])
        self.bwd = np.array([[(b >> 1) | (r << (k - 1)) for r in (0, 1)]
                             for b in range(self.n)])
        self.bit = np.array([[(b >> i) & 1 for i in range(k)] for b in range(self.n)])

    def chains(self, q):
        """q: array of 2^k probabilities P(next symbol = 1 | block).  Returns T, pi, Tstar."""
        n = self.n
        T = np.zeros((n, n))
        for b in range(n):
            T[b, self.fwd[b, 0]] += 1 - q[b]
            T[b, self.fwd[b, 1]] += q[b]
        w, V = np.linalg.eig(T.T)
        i = int(np.argmin(np.abs(w - 1.0)))
        pi = np.real(V[:, i]); pi = np.abs(pi); s = pi.sum()
        pi = pi / s if s > 0 else np.full(n, 1.0 / n)
        Ts = np.zeros((n, n))
        for b in range(n):
            if pi[b] > 0:
                Ts[b] = pi * T[:, b] / pi[b]
            else:
                Ts[b, b] = 1.0
        return T, pi, Ts

    def G(self, q, h, ch=None):
        n, k = self.n, self.k
        T, pi, Ts = ch if ch is not None else self.chains(np.asarray(q, dtype=float))
        emit_f = (np.arange(n) & 1)                       # symbol emitted entering b'
        emit_b = (np.arange(n) >> (k - 1)) & 1
        V = np.ones(n, dtype=complex)
        for j in range(self.J, 0, -1):
            V = T @ (np.exp(2j * np.pi * h * self.x[j - 1] * emit_f) * V)
        U = np.ones(n, dtype=complex)
        for m in range(self.M, k - 1, -1):
            U = Ts @ (np.exp(-2j * np.pi * h * self.c[m] * emit_b) * U)
        sh = np.exp(-2j * np.pi * h * (self.bit[:, :k] @ self.c[:k]))
        return complex(np.sum(pi * sh * U * V))

    def Gs(self, q, hs):
        """All of G_P(h), h in hs, at once: the block matrices do not depend on h, only
        the phases do, so one pass over the two ladders serves every mode."""
        n, k = self.n, self.k
        T, pi, Ts = self.chains(np.asarray(q, dtype=float))
        hs = np.asarray(hs, dtype=float)[:, None]
        ef = (np.arange(n) & 1)[None, :]
        eb = ((np.arange(n) >> (k - 1)) & 1)[None, :]
        V = np.ones((len(hs), n), dtype=complex)
        for j in range(self.J, 0, -1):
            V = (V * np.exp(2j * np.pi * hs * self.x[j - 1] * ef)) @ T.T
        U = np.ones((len(hs), n), dtype=complex)
        for m in range(self.M, k - 1, -1):
            U = (U * np.exp(-2j * np.pi * hs * self.c[m] * eb)) @ Ts.T
        sh = np.exp(-2j * np.pi * hs * (self.bit[:, :k] @ self.c[:k])[None, :])
        return (pi[None, :] * sh * U * V).sum(axis=1)

    def Psi(self, q, hs):
        return float(np.max(np.abs(self.Gs(q, hs))))

    def profile(self, q, hs):
        return [float(abs(z)) for z in self.Gs(q, hs)]


if __name__ == '__main__':
    # validation: memory 2 restricted to memory-1 dynamics must reproduce memory 1
    from m5_markov import MarkovG, mat
    al = Alpha([1, -4, 1], '2+sqrt3')
    m1, m2 = Memory(al, 1), Memory(al, 2)
    mg = MarkovG(al)
    for (p01, p10) in [(0.5, 0.5), (0.3, 0.7), (0.8, 0.2), (0.25, 0.9)]:
        q1 = np.array([p01, 1 - p10])                     # P(next=1 | omega_0 = 0 or 1)
        q2 = np.array([q1[b & 1] for b in range(4)])
        for h in [1, 3, 7]:
            g0 = mg.G(mat(p01, p10), h)
            g1, g2 = m1.G(q1, h), m2.G(q2, h)
            print('(%.2f,%.2f) h=%d  markov=%+.8f%+.8fi  mem1 diff %.2e  mem2 diff %.2e'
                  % (p01, p10, h, g0.real, g0.imag, abs(g1 - g0), abs(g2 - g0)))
