#!/usr/bin/env python3
# (C) 2026 Ralf Stephan, in collaboration with Claude Code
# CC0 1.0 Universal (public domain dedication).
"""M1 of plans/plan-1061.html -- exact arithmetic in Q(alpha), on the basis 1,a,...,a^(d-1).

Everything here is exact (fractions.Fraction), so the statements it checks -- the trace
form, the codifferent d^-1 = f'(a)^-1 Z[a], the companion matrix of multiplication by
alpha, its determinant N(alpha) -- are checked, not estimated.  Used by m1_verify.py
for Lemma 2, Prop 8 and Prop 13 of note-1061-M1.html.
"""
from fractions import Fraction as Fr


def companion(coeffs):
    """Matrix of multiplication by alpha on Z[alpha] in the basis 1,a,..,a^(d-1).
    coeffs = monic minimal polynomial, highest degree first."""
    d = len(coeffs) - 1
    # a^d = -(c_1 a^(d-1) + ... + c_d)
    tail = [Fr(-coeffs[d - i]) for i in range(d)]          # coefficient of a^i in a^d
    C = [[Fr(0)] * d for _ in range(d)]
    for i in range(d - 1):
        C[i + 1][i] = Fr(1)                                # a * a^i = a^(i+1)
    for i in range(d):
        C[i][d - 1] = tail[i]
    return C


def matmul(A, B):
    n, m, k = len(A), len(B[0]), len(B)
    return [[sum(A[i][t] * B[t][j] for t in range(k)) for j in range(m)] for i in range(n)]


def matvec(A, v):
    return [sum(A[i][j] * v[j] for j in range(len(v))) for i in range(len(A))]


def matpow(A, n):
    d = len(A)
    R = [[Fr(1) if i == j else Fr(0) for j in range(d)] for i in range(d)]
    for _ in range(n):
        R = matmul(A, R)
    return R


def mattrace(A):
    return sum(A[i][i] for i in range(len(A)))


def solve(A, b):
    """Exact Gaussian elimination, A square nonsingular over Q."""
    n = len(A)
    M = [[A[i][j] for j in range(n)] + [b[i]] for i in range(n)]
    for c in range(n):
        p = next(r for r in range(c, n) if M[r][c] != 0)
        M[c], M[p] = M[p], M[c]
        pv = M[c][c]
        M[c] = [x / pv for x in M[c]]
        for r in range(n):
            if r != c and M[r][c] != 0:
                f = M[r][c]
                M[r] = [x - f * y for x, y in zip(M[r], M[c])]
    return [M[i][n] for i in range(n)]


def det(A):
    n = len(A)
    M = [row[:] for row in A]
    s = Fr(1)
    for c in range(n):
        p = next((r for r in range(c, n) if M[r][c] != 0), None)
        if p is None:
            return Fr(0)
        if p != c:
            M[c], M[p] = M[p], M[c]
            s = -s
        s *= M[c][c]
        pv = M[c][c]
        M[c] = [x / pv for x in M[c]]
        for r in range(c + 1, n):
            if M[r][c] != 0:
                f = M[r][c]
                M[r] = [x - f * y for x, y in zip(M[r], M[c])]
    return s


class Field:
    """Q(alpha) with alpha a root of the monic irreducible `coeffs`."""

    def __init__(self, coeffs):
        self.coeffs = [int(c) for c in coeffs]
        self.d = len(coeffs) - 1
        self.C = companion(self.coeffs)
        self.tr = [mattrace(matpow(self.C, i)) for i in range(2 * self.d + 2)]  # Tr(a^i)

    def traces(self, n):
        """Tr(alpha^i), i = 0..n, by alpha's own linear recurrence (Newton)."""
        d, co = self.d, self.coeffs
        t = list(self.tr[:min(n + 1, len(self.tr))])
        while len(t) <= n:
            m = len(t) - d                       # Tr(a^{m+d}) = -sum_{i=1..d} c_i Tr(a^{m+d-i})
            t.append(-sum(Fr(co[i]) * t[m + d - i] for i in range(1, d + 1)))
        return t[:n + 1]

    def mul_matrix(self, b):
        """matrix of multiplication by beta = sum b_i a^i."""
        d = self.d
        R = [[Fr(0)] * d for _ in range(d)]
        P = [[Fr(1) if i == j else Fr(0) for j in range(d)] for i in range(d)]
        for i in range(d):
            if b[i] != 0:
                for r in range(d):
                    for c in range(d):
                        R[r][c] += b[i] * P[r][c]
            P = matmul(self.C, P)
        return R

    def trace(self, b):
        return sum(Fr(b[i]) * self.tr[i] for i in range(self.d))

    def norm(self, b):
        return det(self.mul_matrix([Fr(x) for x in b]))

    def inv(self, b):
        e = [Fr(1)] + [Fr(0)] * (self.d - 1)
        return solve(self.mul_matrix([Fr(x) for x in b]), e)

    def mul(self, b, c):
        return matvec(self.mul_matrix([Fr(x) for x in b]), [Fr(x) for x in c])

    def fprime(self):
        """coordinates of f'(alpha) in the basis 1,a,..,a^(d-1) (already reduced: deg < d)."""
        d = self.d
        v = [Fr(0)] * d
        for i, c in enumerate(self.coeffs):      # c * X^(d-i)
            k = d - i
            if k >= 1:
                v[k - 1] += Fr(k * c)
        return v

    def in_Zalpha(self, b):
        return all(Fr(x).denominator == 1 for x in b)

    def in_codifferent(self, b):
        """lambda in d^-1  <=>  Tr(lambda a^i) in Z for i = 0..d-1."""
        d = self.d
        lam = [Fr(x) for x in b]
        for i in range(d):
            t = self.trace(matvec(matpow(self.C, i), lam))
            if t.denominator != 1:
                return False
        return True
