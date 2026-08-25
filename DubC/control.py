#!/usr/bin/env python3
# (C) Ralf Stephan, in collaboration with Claude Code.  CC0 / public domain.
"""
Positive/negative controls for the C(P) certificate (plan-dubC1 §0-ter).

FULL model, arbitrary base b, no reduction: states = units mod M (M=prod p<=y),
digit alphabet 0..b-1, transition r --d--> (b r + d) mod M admissible iff the
target is a unit.  Prune to the bi-infinite core, then report the C(P) verdict
(does any SCC contain two distinct cycles) and lambda.

Point of the controls:
  * b in {3,4,5,6}: the chain hypothesis is PROVED (MPPSW Lemma A.1) -- every
    survivor is periodic -- so a CORRECT method must return C(P) HOLDS already
    at small y.  These test that the machinery does not spuriously report FAILS.
  * b = 7: must return FAILS at small y (positive entropy is real) and only flip
    to HOLDS at y=31.  Tests that it does not spuriously report HOLDS.
  * b = 10: open; expected FAILS at every reachable y (first moment crosses 1
    far out).  A HOLDS here at small y would signal a logic/model bug.
"""
import sys
from math import gcd, log
import numpy as np
from scipy.sparse import csr_matrix
from scipy.sparse.csgraph import connected_components


def primes_upto(y):
    return [p for p in range(2, y + 1) if all(p % q for q in range(2, p))]


def build(b, y):
    ps = primes_upto(y)
    M = 1
    for p in ps:
        M *= p
    states = [r for r in range(M) if gcd(r, M) == 1]
    idx = {r: i for i, r in enumerate(states)}
    rows, cols = [], []
    for i, r in enumerate(states):
        for d in range(b):
            s = (b * r + d) % M
            j = idx.get(s)
            if j is not None:
                rows.append(i); cols.append(j)
    n = len(states)
    A = csr_matrix((np.ones(len(rows)), (rows, cols)), shape=(n, n))
    return states, A, M


def prune_core(A):
    """Restrict to the bi-infinite core: iteratively drop vertices with
    out-degree 0 or in-degree 0.  Prunes on a fixed edge list (fast)."""
    n = A.shape[0]
    src, dst = A.nonzero()
    keep = np.ones(n, dtype=bool)
    while True:
        live = keep[src] & keep[dst]
        outd = np.bincount(src[live], minlength=n)
        ind = np.bincount(dst[live], minlength=n)
        dead = keep & ((outd == 0) | (ind == 0))
        if not dead.any():
            break
        keep[dead] = False
    return keep


def verdict(b, y):
    states, A, M = build(b, y)
    keep = prune_core(A.tocsr())
    core = np.flatnonzero(keep)
    if len(core) == 0:
        print(f"  b={b} y={y:2d}: core EMPTY  -> UNAVOIDABLE SET (lambda=0)")
        return
    B = A.tocsr()[core][:, core]
    ncc, lab = connected_components(B, directed=True, connection="strong")
    src, dst = B.nonzero()
    same = lab[src] == lab[dst]
    outdeg = np.bincount(src[same], minlength=len(core))
    # branching SCC: some vertex has >=2 successors inside its own SCC
    brc = np.unique(lab[src[same][outdeg[src[same]] >= 2]])
    cyc = np.unique(lab[src[same]])
    # lambda = max over cyclic SCCs of the block Perron root
    lam = 0.0
    for c in cyc:
        ii = np.flatnonzero(lab == c)
        Bc = B[ii][:, ii]
        r = 1.0 if Bc.shape[0] == 1 else float(np.max(np.abs(np.linalg.eigvals(Bc.toarray()))))
        lam = max(lam, r)
    holds = len(brc) == 0
    print(f"  b={b} y={y:2d}: core {len(core):6d}  SCCs {ncc:5d}  cyclic {len(cyc):4d}  "
          f"branching {len(brc):3d}  lambda={lam:.5f}  C(P) {'HOLDS' if holds else 'FAILS'}"
          + ("   <-- solved-at-this-y" if holds else ""))


if __name__ == "__main__":
    print("Controls: known-solved small bases must give C(P) HOLDS at small y;")
    print("b=7 must stay FAILS until it flips; b=10 must stay FAILS at reachable y.\n")
    plan = {3: [3, 5, 7], 4: [3, 5, 7], 5: [3, 5, 7, 11], 6: [5, 7, 11],
            7: [7, 11, 13, 17], 10: [7, 11, 13, 17]}
    for b in [3, 4, 5, 6, 7, 10]:
        for y in plan[b]:
            verdict(b, y)
        print()
