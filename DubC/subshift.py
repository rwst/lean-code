#!/usr/bin/env python3
# (C) Ralf Stephan, in collaboration with Claude Code.  CC0 / public domain.
"""
X2 (plan-dubC1 §8) — reference implementation of the coprimality subshift of
[xi * 7^n], built clean-room from the definition in plan §4.

Setting.  x_{n+1} = 7 x_n + d_{n+1} with d_{n+1} in {0,...,6} the (n+1)-st
base-7 digit of xi.  For a finite prime set P with M = prod_{p in P} p, the
digit words for which x_n stays coprime to M for all n form a subshift of
finite type X_P:

    states       r in (Z/M)^*
    transitions  r --d--> (7r+d) mod M,  admissible iff gcd(7r+d, M) = 1.

lambda(P) = Perron root of the adjacency matrix; h_top = log lambda;
dim_H = log lambda / log 7 (plan T4).

Two models are implemented and cross-checked:

  FULL     the literal definition above, states = units mod M, digits 0..6.
  REDUCED  drop the coordinates p = 2 and p = 7.  Justification (verified
           numerically below): coprimality to 2 forces d even and coprimality
           to 7 forces d != 0, so the alphabet collapses to {2,4,6}; then
           r mod 2 == 1 is invariant and r mod 7 is *determined* by the last
           digit (7r+d == d mod 7) and never constrains admissibility.  Hence
           every FULL state (rho, r_2, r_7) has the same forward language as
           the REDUCED state rho, and the two models have identical Perron
           roots.  The reduced state space is Q = {p <= y} \\ {2,7}, of size
           prod_{p in Q} (p-1) = phi(M)/6.

Usage:   python3 subshift.py [ymax]
"""

import sys
from math import gcd, log

import numpy as np
from scipy.sparse import csr_matrix
from scipy.sparse.csgraph import connected_components

BASE = 7
DIGITS_FULL = list(range(BASE))          # 0..6
DIGITS_RED = [2, 4, 6]                   # after the mod-2 and mod-7 collapse


def primes_upto(y):
    return [p for p in range(2, y + 1) if all(p % q for q in range(2, p))]


# --------------------------------------------------------------------------
# FULL model: states are the units mod M = prod_{p<=y} p, digits 0..6.
# --------------------------------------------------------------------------
def build_full(y):
    ps = primes_upto(y)
    M = 1
    for p in ps:
        M *= p
    states = [r for r in range(M) if gcd(r, M) == 1]
    index = {r: i for i, r in enumerate(states)}
    rows, cols = [], []
    for i, r in enumerate(states):
        for d in DIGITS_FULL:
            s = (BASE * r + d) % M
            j = index.get(s)
            if j is not None:
                rows.append(i)
                cols.append(j)
    n = len(states)
    A = csr_matrix((np.ones(len(rows)), (rows, cols)), shape=(n, n))
    return states, A, M


# --------------------------------------------------------------------------
# REDUCED model: states are tuples (r mod p)_{p in Q}, Q = {p<=y} \ {2,7},
# each coordinate a unit; digits {2,4,6}.  Mixed-radix indexing, vectorised.
# --------------------------------------------------------------------------
class Reduced:
    def __init__(self, y):
        self.y = y
        self.ps = primes_upto(y)
        self.Q = [p for p in self.ps if p not in (2, BASE)]
        self.radix = [p - 1 for p in self.Q]          # coordinate c = r-1
        self.strides = []
        s = 1
        for m in self.radix:                          # least significant first
            self.strides.append(s)
            s *= m
        self.n = s

    def coords(self, idx):
        """idx: int64 array -> list of residue arrays r_p in 1..p-1."""
        out = []
        for m, st in zip(self.radix, self.strides):
            out.append((idx // st) % m + 1)
        return out

    def step(self, idx, d):
        """Successor index under digit d; -1 where inadmissible."""
        rs = self.coords(idx)
        new = np.zeros_like(idx)
        ok = np.ones(idx.shape, dtype=bool)
        for p, r, st in zip(self.Q, rs, self.strides):
            nr = (BASE * r + d) % p
            ok &= nr != 0
            new += (nr - 1) * st
        return np.where(ok, new, -1)

    def matrix(self):
        idx = np.arange(self.n, dtype=np.int64)
        rows, cols = [], []
        for d in DIGITS_RED:
            t = self.step(idx, d)
            m = t >= 0
            rows.append(idx[m])
            cols.append(t[m])
        rows = np.concatenate(rows)
        cols = np.concatenate(cols)
        A = csr_matrix((np.ones(len(rows)), (rows, cols)), shape=(self.n, self.n))
        return A

    def label(self, i):
        """CRT value of state i modulo prod(Q), for human-readable witnesses."""
        Mq = 1
        for p in self.Q:
            Mq *= p
        v = 0
        for p, st, m in zip(self.Q, self.strides, self.radix):
            r = (i // st) % m + 1
            # CRT
            co = Mq // p
            v += r * co * pow(co, -1, p)
        return v % Mq


# --------------------------------------------------------------------------
# Spectral radius of a nonnegative sparse 0-1 matrix, via per-SCC analysis.
# rho(A) = max over strongly connected components of rho(A restricted).
# --------------------------------------------------------------------------
def scc_analysis(A):
    n = A.shape[0]
    ncc, lab = connected_components(A, directed=True, connection="strong")
    sizes = np.bincount(lab, minlength=ncc)
    src, dst = A.nonzero()
    same = lab[src] == lab[dst]
    # in-component out-degree of each vertex
    outdeg = np.bincount(src[same], minlength=n)
    branching = np.zeros(ncc, dtype=bool)   # SCC contains two distinct cycles
    nontrivial = np.zeros(ncc, dtype=bool)  # SCC carries at least one cycle
    for c in range(ncc):
        pass
    # vectorised versions of the two loops above
    has_edge = np.bincount(lab[src[same]], minlength=ncc)
    nontrivial = has_edge > 0
    br = np.bincount(lab[src[same]][outdeg[src[same]] >= 2], minlength=ncc)
    branching = br > 0
    return lab, sizes, nontrivial, branching, outdeg, (src, dst, same)


def perron(A, lab, sizes, nontrivial, tol=1e-13, maxit=200000):
    """rho(A) = max over cyclic SCCs of the Perron root of that SCC block."""
    best, arg = 0.0, None
    order = np.argsort(-sizes)
    for c in order:
        if not nontrivial[c]:
            continue
        idx = np.flatnonzero(lab == c)
        B = A[idx][:, idx]
        if B.shape[0] == 1:
            r = float(B[0, 0] > 0)
        elif B.shape[0] <= 400:
            r = float(np.max(np.abs(np.linalg.eigvals(B.toarray()))))
        else:
            r = power_iterate(B, tol, maxit)
        if r > best:
            best, arg = r, c
    return best, arg


def power_iterate(B, tol=1e-13, maxit=200000):
    n = B.shape[0]
    v = np.ones(n)
    lam = 0.0
    for k in range(maxit):
        w = B.T @ v if False else B @ v
        s = w.sum()
        if s == 0:
            return 0.0
        new = s / v.sum()
        v = w / s * n
        if k > 20 and abs(new - lam) < tol * max(1.0, new):
            return new
        lam = new
    return lam


def collatz_wielandt(B, v):
    """Certified bracket min_i (Bv)_i/v_i <= rho(B) <= max_i (Bv)_i/v_i."""
    w = B @ v
    q = w / v
    return float(q.min()), float(q.max())


# --------------------------------------------------------------------------
def report(y, verbose=True, do_full=True):
    R = Reduced(y)
    A = R.matrix()
    lab, sizes, nontrivial, branching, outdeg, _ = scc_analysis(A)
    rho, arg = perron(A, lab, sizes, nontrivial)

    ps = primes_upto(y)
    lam_bar = float(BASE)
    for p in ps:
        lam_bar *= (1 - 1.0 / p)

    ncyc = int(nontrivial.sum())
    nbr = int(branching.sum())
    big = int(sizes[arg]) if arg is not None else 0

    print(f"y = {y:3d}   Q = {R.Q}")
    print(f"  states (reduced)      {R.n}")
    print(f"  SCCs with a cycle     {ncyc}   (of which branching: {nbr})")
    print(f"  largest cyclic SCC    {big}")
    print(f"  lambda(y)             {rho:.6f}")
    print(f"  dim = log l / log 7   {log(rho)/log(BASE):.6f}" if rho > 0 else "")
    print(f"  first moment lbar(y)  {lam_bar:.6f}   ratio l/lbar = {rho/lam_bar:.4f}")
    print(f"  C(P) [no SCC has two distinct cycles] : {'HOLDS' if nbr == 0 else 'FAILS'}")

    if verbose and R.n <= 64:
        print("  transition table (state = r mod %d):" % np.prod(R.Q))
        idx = np.arange(R.n, dtype=np.int64)
        for i in range(R.n):
            outs = []
            for d in DIGITS_RED:
                t = int(R.step(np.array([i], dtype=np.int64), d)[0])
                if t >= 0:
                    outs.append((d, R.label(t)))
            print("    r=%3d  ->  %s" % (R.label(i),
                  ", ".join(f"d={d}: {v}" for d, v in outs)))

    if do_full:
        states, AF, M = build_full(y)
        labF, sizesF, ntF, brF, _, _ = scc_analysis(AF)
        rhoF, argF = perron(AF, labF, sizesF, ntF)
        agree = "OK" if abs(rhoF - rho) < 1e-8 else "MISMATCH"
        print(f"  full model mod {M}: {len(states)} states, lambda = {rhoF:.6f}  [{agree}]")
    print()
    return rho


if __name__ == "__main__":
    ymax = int(sys.argv[1]) if len(sys.argv) > 1 else 17
    for y in [p for p in primes_upto(ymax) if p >= 7]:
        report(y, verbose=(y == 7), do_full=(y <= 13))
