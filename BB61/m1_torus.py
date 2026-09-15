#!/usr/bin/env python3
# (C) 2026 Ralf Stephan, in collaboration with Claude Code
# CC0 1.0 Universal (public domain dedication).
"""M1 of plans/plan-1061.html -- the Minkowski torus T^d_Lambda = R^d / iota(Z[alpha]).

Builds the Minkowski embedding iota, the lattice Lambda = iota(Z[alpha]), the trace
character tau, the multiplication-by-alpha endomorphism Mbar, and the coding map Phi of
note-1061-M1.html sec 4.  Used by m1_verify.py for Prop 8-11.
"""
from m0_engine import Alpha
import numpy as np, itertools, mpmath as mp


class Torus:
    def __init__(self, al: Alpha):
        self.al = al
        d = al.d
        self.d = d
        rts = [al.alpha] + list(al.conj)
        real = [z for z in rts if abs(mp.im(z)) < 1e-25]
        cplx = [z for z in rts if mp.im(z) > 1e-25]          # one per conjugate pair
        assert len(real) + 2 * len(cplx) == d
        self.r1, self.r2 = len(real), len(cplx)
        self.real = [complex(z).real for z in real]
        self.cplx = [complex(z) for z in cplx]
        # tau(v) = sum of the real coords + 2 * sum of the Re-coords of the complex places
        self.tau_vec = np.zeros(d)
        self.tau_vec[:self.r1] = 1.0
        for k in range(self.r2):
            self.tau_vec[self.r1 + 2 * k] = 2.0
        # lattice basis: iota(alpha^i), i = 0..d-1
        self.B = np.column_stack([self.iota_pow(i) for i in range(d)])
        self.Binv = np.linalg.inv(self.B)
        # M in embedding coordinates: block diagonal
        M = np.zeros((d, d))
        for i, x in enumerate(self.real):
            M[i, i] = x
        for k, z in enumerate(self.cplx):
            i = self.r1 + 2 * k
            M[i, i] = z.real;      M[i, i + 1] = -z.imag
            M[i + 1, i] = z.imag;  M[i + 1, i + 1] = z.real
        self.M = M

    def iota(self, betas):
        """betas = [sigma_1(b), ..., sigma_d(b)] in the SAME root order as rts above."""
        raise NotImplementedError

    def iota_pow(self, i):
        v = np.zeros(self.d)
        for j, x in enumerate(self.real):
            v[j] = x ** i
        for k, z in enumerate(self.cplx):
            w = z ** i
            v[self.r1 + 2 * k] = w.real
            v[self.r1 + 2 * k + 1] = w.imag
        return v

    def iota_int(self, coords):
        """iota of beta = sum coords[i] alpha^i."""
        return sum(float(c) * self.iota_pow(i) for i, c in enumerate(coords))

    def tau(self, v):
        return float(self.tau_vec @ v)

    def reduce(self, v):
        """representative of v + Lambda with |B^-1 x| <= 1/2 componentwise."""
        y = self.Binv @ v
        return self.B @ (y - np.round(y))

    def dist(self, v, w=None):
        """distance to Lambda (w=None) or between v+Lambda and w+Lambda."""
        u = v if w is None else v - w
        y = self.Binv @ u
        base = np.round(y)
        best = np.inf
        for off in itertools.product((-1, 0, 1), repeat=self.d):
            z = self.B @ (y - base - np.array(off, dtype=float))
            best = min(best, float(np.linalg.norm(z)))
        return best

    # ---- the coding map Phi of sec 4 ----
    def w_vec(self, past, cm_depth=None):
        """window vector w(delta) = (0, sum_m (a_j - 1) a_j^m delta_m)_{j>=2}, delta = past."""
        v = np.zeros(self.d)
        for j, x in enumerate(self.real):
            if j == 0:
                continue
            s = 0.0
            p = 1.0
            for m, b in enumerate(past):
                if b:
                    s += (x - 1) * p
                p *= x
            v[j] = s
        for k, z in enumerate(self.cplx):
            s = 0j
            p = 1 + 0j
            for m, b in enumerate(past):
                if b:
                    s += (z - 1) * p
                p *= z
            v[self.r1 + 2 * k] = s.real
            v[self.r1 + 2 * k + 1] = s.imag
        return v

    def Phi(self, past, fut):
        """Phi(omega) = iota_R(t(omega+)) - w(omega-)  mod Lambda.
        past = (w_0, w_-1, ...), fut = (w_1, w_2, ...), both finite 0/1 lists."""
        a = self.al.a
        t = (a - 1) * sum(fut[j] * a ** (-(j + 1)) for j in range(len(fut)))
        v = np.zeros(self.d)
        v[0] = t                      # iota_R(t) = (t, 0, ..., 0)
        return self.reduce(v - self.w_vec(past))
