#!/usr/bin/env python3
# (C) Ralf Stephan, in collaboration with Claude Code.  CC0 / public domain.
"""
Search for the rank (condensation-height) certificates that DubC/Certificate.lean
feeds to `decide`, and check them against the CertOK conditions exactly as the Lean
definition states them.

CertOK a M rank:
  for every unit r mod M,
    (1) every admissible successor t = a*r+d (d < a, t a unit) has rank t <= rank r;
    (2) at most one admissible successor is rank-preserving.
"""
from math import gcd
from itertools import product


def units(M):
    return [r for r in range(M) if gcd(r, M) == 1]


def succs(a, M, r):
    """Admissible successors as (digit, target) pairs."""
    return [(d, (a * r + d) % M) for d in range(a) if gcd((a * r + d) % M, M) == 1]


def condensation_rank(a, M):
    """rank r = longest path from r's SCC in the condensation DAG (None if a cycle
    is reachable from itself through >1 distinct route, i.e. the DAG has a loop)."""
    U = units(M)
    idx = {r: i for i, r in enumerate(U)}
    n = len(U)
    adj = [[idx[t] for _, t in succs(a, M, r)] for r in U]
    # Tarjan SCC (iterative)
    index = [None] * n
    low = [0] * n
    onstk = [False] * n
    stk, out, comp, counter = [], [], [None] * n, [0]

    for root in range(n):
        if index[root] is not None:
            continue
        work = [(root, 0)]
        while work:
            v, pi = work[-1]
            if pi == 0:
                index[v] = low[v] = counter[0]
                counter[0] += 1
                stk.append(v)
                onstk[v] = True
            recurse = False
            for i in range(pi, len(adj[v])):
                w = adj[v][i]
                if index[w] is None:
                    work[-1] = (v, i + 1)
                    work.append((w, 0))
                    recurse = True
                    break
                elif onstk[w]:
                    low[v] = min(low[v], index[w])
            if recurse:
                continue
            if low[v] == index[v]:
                cid = len(out)
                members = []
                while True:
                    w = stk.pop()
                    onstk[w] = False
                    comp[w] = cid
                    members.append(w)
                    if w == v:
                        break
                out.append(members)
            work.pop()
            if work:
                u = work[-1][0]
                low[u] = min(low[u], low[v])
    # DAG heights over components (Tarjan emits reverse topological order)
    height = [0] * len(out)
    for cid, members in enumerate(out):
        h = 0
        for v in members:
            for w in adj[v]:
                if comp[w] != cid:
                    h = max(h, height[comp[w]] + 1)
        height[cid] = h
    return {r: height[comp[idx[r]]] for r in U}


def check(a, M, rank):
    """Verify CertOK exactly as Lean states it.  Returns (ok, witness)."""
    for r in units(M):
        keep = []
        for d, t in succs(a, M, r):
            if rank[t] > rank[r]:
                return False, f"rank increases: {r} -{d}-> {t}"
            if rank[t] == rank[r]:
                keep.append(t)
        if len(set(keep)) > 1:
            return False, f"two rank-preserving successors at {r}: {sorted(set(keep))}"
    return True, None


CASES = [
    (3, 6, "b=3, P={2,3}"),
    (4, 6, "b=4, P={2,3}"),
    (5, 30, "b=5, P={2,3,5}"),
    (6, 30, "b=6, P={2,3,5}"),
    (7, 30, "b=7, P={2,3,5} (must FAIL)"),
    (10, 30, "b=10, P={2,3,5} (open case, must FAIL)"),
]

for a, M, label in CASES:
    rank = condensation_rank(a, M)
    ok, why = check(a, M, rank)
    print(f"{label:34s} units={len(units(M)):3d}  C(P) {'HOLDS' if ok else 'FAILS'}"
          f"{'' if ok else '  (' + why + ')'}")
    if ok:
        print(f"{'':36s}rank = {{{', '.join(f'{r}:{v}' for r, v in sorted(rank.items()))}}}")
        # candidate closed forms to use in Lean
        for name, f in [
            ("0", lambda r: 0),
            ("if r%M==1 then 1 else 0", lambda r: 1 if r % M == 1 else 0),
            ("2*(4-r%5)+(1 if r%3==1 else 0)", lambda r: 2 * (4 - r % 5) + (1 if r % 3 == 1 else 0)),
        ]:
            cand = {r: f(r) for r in units(M)}
            okc, _ = check(a, M, cand)
            if okc:
                print(f"{'':36s}closed form OK:  rank r = {name}")
