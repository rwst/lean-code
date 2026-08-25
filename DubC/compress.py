#!/usr/bin/env python3
# (C) Ralf Stephan, in collaboration with Claude Code.  CC0 / public domain.
"""
Compress the y=31 core to the data a Lean certificate actually needs, and check
that data against the *Lean* conditions.

Input   core_y31_res.txt   (from ./cycles 31 2000 31): every core state of the
                           reduced model with its residue mod prodQ and its three
                           successors.
Output  core_y31_cycles.txt  the compressed core: one line per cycle, giving the
                           starting residue mod M = primorial31, the rank, and the
                           digit word.  Everything else is recomputed from it.

What is checked here (independently of the C run):
  1. the C output is internally consistent: succ residues really are 7r+d mod prodQ;
  2. every cyclic SCC is a simple cycle (the C(P) certificate, recomputed);
  3. K = the cycle states, lifted to the full modulus M = 2*7*prodQ, satisfies the
     Lean `CoreCertOK` conditions: rank non-increasing into K, <= 1 rank-preserving
     K-successor;
  4. how many membership queries a kernel check would need.
"""
import sys
from math import gcd
import numpy as np
from scipy.sparse import csr_matrix
from scipy.sparse.csgraph import connected_components

DIG = [2, 4, 6]
BASE = 7

fn = sys.argv[1] if len(sys.argv) > 1 else "core_y31_res.txt"
with open(fn) as f:
    n, prodQ = map(int, f.readline().split())
    raw = np.fromstring(f.read(), sep=" ", dtype=np.int64)
A = raw.reshape(n, 5)
assert (A[:, 0] == np.arange(n)).all(), "core file not in index order"
res = A[:, 1].copy()
succ = A[:, 2:5].copy()
M = 2 * BASE * prodQ                      # = primorial31
print(f"core states {n}   prodQ {prodQ}   M = 2*7*prodQ = {M}")

# ---- 1. the C output is internally consistent --------------------------------
for t, d in enumerate(DIG):
    m = succ[:, t] >= 0
    lhs = res[succ[m, t]]
    rhs = (BASE * res[m] + d) % prodQ
    assert (lhs == rhs).all(), f"successor residues wrong for digit {d}"
assert (np.gcd(res, prodQ) == 1).all(), "a core state is not a unit"
print("[1] successor residues and unit-ness verified against the residues themselves")

# ---- 2. every cyclic SCC is a simple cycle -----------------------------------
src = np.repeat(np.arange(n), 3)[succ.reshape(-1) >= 0]
dst = succ.reshape(-1)[succ.reshape(-1) >= 0]
G = csr_matrix((np.ones(len(src)), (src, dst)), shape=(n, n))
ncc, lab = connected_components(G, directed=True, connection="strong")
same = lab[src] == lab[dst]
cyclic = np.unique(lab[src[same]])
sizes = np.bincount(lab, minlength=ncc)
edges_in = np.bincount(lab[src[same]], minlength=ncc)
assert (edges_in[cyclic] == sizes[cyclic]).all(), "a cyclic SCC is not a simple cycle"
onc = np.zeros(n, dtype=bool)
onc[np.isin(lab, cyclic)] = True
K = int(onc.sum())
print(f"[2] SCCs {ncc}, cyclic {len(cyclic)} (all simple cycles), cycle states |K| = {K}")

# ---- on-cycle successor and incoming digit ----------------------------------
nxt = np.full(n, -1, dtype=np.int64)        # on-cycle successor
outd = np.full(n, -1, dtype=np.int64)       # digit of that step
for t, d in enumerate(DIG):
    m = onc & (succ[:, t] >= 0)
    m &= np.where(succ[:, t] >= 0, lab[np.maximum(succ[:, t], 0)] == lab, False)
    assert (nxt[m] == -1).all(), "two on-cycle successors: not a simple cycle"
    nxt[m] = succ[m, t]
    outd[m] = d
assert (nxt[onc] >= 0).all()
inc = np.full(n, -1, dtype=np.int64)        # on-cycle incoming digit
inc[nxt[onc]] = outd[onc]

# ---- 3. ranks (condensation height on the induced subgraph on K) -------------
# edges inside K between different cycles
ksrc, kdst, kdig = [], [], []
for t, d in enumerate(DIG):
    m = onc & (succ[:, t] >= 0) & np.isin(succ[:, t], np.flatnonzero(onc))
    for a, b in zip(np.flatnonzero(m), succ[m, t]):
        ksrc.append(a); kdst.append(b); kdig.append(d)
ksrc, kdst, kdig = map(np.array, (ksrc, kdst, kdig))
# only edges that land on the *lifted* K: incoming digit must match
lift_ok = kdig == inc[kdst]
cross = lab[ksrc] != lab[kdst]
print(f"[3] edges inside K: {len(ksrc)}  of which lift to K: {int(lift_ok.sum())}, "
      f"cross-cycle: {int((lift_ok & cross).sum())}")

# condensation height over cycles, using only lifted cross edges
cyc_id = {int(c): i for i, c in enumerate(cyclic)}
adj = [[] for _ in cyclic]
for a, b in zip(ksrc[lift_ok & cross], kdst[lift_ok & cross]):
    adj[cyc_id[int(lab[a])]].append(cyc_id[int(lab[b])])
rank_of_cycle = [0] * len(cyclic)
if any(adj):
    order, seen = [], [0] * len(cyclic)
    def dfs(v):
        stack = [(v, 0)]
        while stack:
            x, i = stack[-1]
            if i == 0:
                if seen[x]:
                    stack.pop(); continue
                seen[x] = 1
            if i < len(adj[x]):
                stack[-1] = (x, i + 1)
                if not seen[adj[x][i]]:
                    stack.append((adj[x][i], 0))
            else:
                order.append(x); stack.pop()
    for v in range(len(cyclic)):
        if not seen[v]:
            dfs(v)
    for x in order:                       # reverse topological order
        rank_of_cycle[x] = max((rank_of_cycle[y] + 1 for y in adj[x]), default=0)
maxrank = max(rank_of_cycle)
print(f"[3] distinct ranks needed: {len(set(rank_of_cycle))} (max rank {maxrank})")

# ---- 4. check the Lean CoreCertOK conditions on the lifted K -----------------
rank = np.zeros(n, dtype=np.int64)
for i, c in enumerate(cyclic):
    rank[lab == c] = rank_of_cycle[i]
queries = 0
for a in np.flatnonzero(onc):
    keep = 0
    for t, d in enumerate(DIG):
        b = succ[a, t]
        if b < 0:
            continue
        queries += 1
        if not onc[b] or inc[b] != d:     # successor not in the lifted K
            continue
        assert rank[b] <= rank[a], f"rank increases at {res[a]}"
        if rank[b] == rank[a]:
            keep += 1
    assert keep <= 1, f"two rank-preserving K-successors at {res[a]}"
print(f"[4] CoreCertOK verified on all {K} lifted cycle states "
      f"({queries} membership queries)")

# ---- emit the compressed core ------------------------------------------------
def crt_full(r_red, d_in):
    """lift to r mod M: r = 1 (2), r = d_in (7), r = r_red (prodQ)"""
    for x in range(M // prodQ):
        r = r_red + prodQ * x
        if r % 2 == 1 and r % 7 == d_in % 7:
            return r
    raise AssertionError

out, total = [], 0
for i, c in enumerate(cyclic):
    members = np.flatnonzero(lab == c)
    start = int(members[0])
    word, v = [], start
    while True:
        word.append(int(outd[v]))
        v = int(nxt[v])
        if v == start:
            break
    assert len(word) == len(members)
    total += len(word)
    out.append((crt_full(int(res[start]), int(inc[start])), rank_of_cycle[i], word))
assert total == K
out.sort()

with open("core_y31_cycles.txt", "w") as f:
    f.write(f"{M} {len(out)} {K}\n")
    for start, rk, word in out:
        f.write(f"{start} {rk} {''.join(str(d) for d in word)}\n")
print(f"[5] wrote core_y31_cycles.txt: {len(out)} cycles, {K} states, "
      f"{sum(len(w) for _, _, w in out)} digits")
