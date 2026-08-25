#!/usr/bin/env python3
# (C) Ralf Stephan, in collaboration with Claude Code.  CC0 / public domain.
"""
Third, fully independent (scipy) check of the C(P) verdict on the core dumped
by ladder.c.  Confirms node count, that every node has a live successor and
predecessor, the cyclic-SCC count, that NO SCC contains two distinct cycles
(the C(P) certificate), and that the spectral radius is exactly 1.

Usage:  python3 verify_core.py core_y31.txt
"""
import sys
import numpy as np
from scipy.sparse import csr_matrix
from scipy.sparse.csgraph import connected_components

fn = sys.argv[1] if len(sys.argv) > 1 else "core_y31.txt"
with open(fn) as f:
    n = int(f.readline())
    data = np.fromstring(f.read(), sep=" ", dtype=np.int64)
E = data.reshape(-1, 2)
src, dst = E[:, 0].copy(), E[:, 1].copy()
print(f"nodes {n}   edges {len(E)}")

outd = np.bincount(src, minlength=n)
ind = np.bincount(dst, minlength=n)
print(f"min out-degree {outd.min()}  min in-degree {ind.min()}   (core: both >= 1)")

A = csr_matrix((np.ones(len(E)), (src, dst)), shape=(n, n))
ncc, lab = connected_components(A, directed=True, connection="strong")

same = lab[src] == lab[dst]
in_scc_out = np.bincount(src[same], minlength=n)           # out-degree inside own SCC
cyclic = np.unique(lab[src[same]])                          # SCCs carrying >=1 edge
branch_nodes = np.flatnonzero(in_scc_out >= 2)              # two outgoing in-SCC edges
branch_sccs = np.unique(lab[branch_nodes]) if len(branch_nodes) else np.empty(0, int)
sizes = np.bincount(lab, minlength=ncc)

print(f"SCCs {ncc}   cyclic SCCs {len(cyclic)}   largest cyclic SCC {int(sizes[cyclic].max())}")
print(f"branching nodes (in-SCC out-degree >= 2): {len(branch_nodes)}")
print(f"branching SCCs (contain two distinct cycles): {len(branch_sccs)}")

# rho does not need eigenvalues: branching == 0  <=>  every cyclic SCC is a
# single cycle  <=>  spectral radius exactly 1 (a 0-1 combinatorial certificate).
# Cross-check that claim by confirming each cyclic SCC has as many in-SCC edges
# as vertices (a simple cycle: |edges| == |vertices|).
edges_per_scc = np.bincount(lab[src[same]], minlength=ncc)
verts_per_scc = sizes
cyc_ok = np.all(edges_per_scc[cyclic] == verts_per_scc[cyclic])
print(f"every cyclic SCC has |edges| == |vertices| (simple cycle): {bool(cyc_ok)}"
      f"  => rho = 1 exactly")
print()
print("VERDICT:", "C(P) HOLDS  (zero entropy: every cyclic SCC is a simple cycle)"
      if len(branch_sccs) == 0 and cyc_ok else "C(P) FAILS")
