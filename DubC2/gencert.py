#!/usr/bin/env python3
# (C) 2026 Ralf Stephan, in collaboration with Claude Code.  CC0 1.0.
#
# gencert.py -- plan-dubC2 milestone M2, experiment X3: certificate extraction.
#
# Builds, for x_n = floor(xi (p/q)^n + nu), nu = a/b, a divisor set P and a cell
# count D, EXACTLY the graph that DubC2/GenCert.lean checks:
#
#   vertices  (r, c),  r in [0, M)  (M = product of the l in P coprime to q),
#                       c in [0, D)  (the cell [c/D, (c+1)/D) of y_n = {xi(p/q)^n + nu})
#   edge (r,c) -s-> (r',c')  iff
#       (avoid)    l does not divide r, for every l in P with l | M,
#                  l does not divide s, for every l in P with l | q,
#                  l does not divide r'                     (target side)
#       (residue)  M | q r' - p r - s
#       (cell)     the two half-open integer intervals
#                     q b [c', c'+1)     and     p b [c, c+1) - K,   K = (p-q) a D + s b D
#                  overlap:  q b c' < p b (c+1) - K  and  p b c - K < q b (c'+1).
#
# and the subset construction from the FULL vertex set (no peel: the Lean side
# never has to prove anything about a core).  The certificate is
#
#   sets[i]    a list of vertices (sets[0] = everything, implicitly)
#   trans[i]   for each letter s of the alphabet, the index j with succ(sets[i], s) <= sets[j]
#              (or None if succ is empty)
#   rank[i]    nonincreasing along trans, and from each i at most ONE letter keeps the rank.
#
# Under these checks every infinite admissible path has an eventually periodic label word,
# which [DN05] Lemma 2 forbids.  The ranks are the topological order of the det SCCs; the
# "at most one rank-preserving letter" condition is exactly C_det.

import argparse
import json
import sys
from fractions import Fraction
from math import gcd

sys.setrecursionlimit(100000)


def parse_frac(s):
    f = Fraction(s)
    return f.numerator, f.denominator


class Model:
    def __init__(self, p, q, a, b, P, D):
        self.p, self.q, self.a, self.b, self.P, self.D = p, q, a, b, list(P), D
        self.Pq = [l for l in P if q % l == 0]
        self.PM = [l for l in P if q % l != 0]
        for l in self.PM:
            assert gcd(l, q) == 1, "every l in P must divide q or be coprime to q"
        for l in self.Pq:
            assert gcd(l, p) == 1
        M = 1
        for l in self.PM:
            M *= l
        self.M = M
        self.qinv = pow(q, -1, M) if M > 1 else 0
        # alphabet bounds: b s in ( -q b - (p-q) a , p b - (p-q) a )
        lo = Fraction(-q * b - (p - q) * a, b)
        hi = Fraction(p * b - (p - q) * a, b)
        import math
        self.sLo = math.floor(lo) + 1
        self.sHi = math.ceil(hi) - 1
        self.alph = [s for s in range(self.sLo, self.sHi + 1)
                     if all(s % l != 0 for l in self.Pq)]

    def vertices(self):
        return [(r, c) for r in range(self.M) if all(r % l for l in self.PM)
                for c in range(self.D)]

    def succ_v(self, v, s):
        r, c = v
        p, q, a, b, D, M = self.p, self.q, self.a, self.b, self.D, self.M
        if any(r % l == 0 for l in self.PM) or any(s % l == 0 for l in self.Pq):
            return []
        r2 = ((p * r + s) * self.qinv) % M if M > 1 else 0
        if any(r2 % l == 0 for l in self.PM):
            return []
        K = (p - q) * a * D + s * b * D
        lo = p * b * c - K          # interval [lo, hi) for q b Y'
        hi = p * b * (c + 1) - K
        out = []
        # c' with q b c' < hi and lo < q b (c'+1)
        c0 = max(0, lo // (q * b))
        c1 = min(D - 1, (hi - 1) // (q * b))
        for c2 in range(c0, c1 + 1):
            if q * b * c2 < hi and lo < q * b * (c2 + 1):
                out.append((r2, c2))
        return out

    def succ_set(self, S, s):
        out = set()
        for v in S:
            out.update(self.succ_v(v, s))
        return frozenset(out)


def forward_core(m, V):
    """vertices with an infinite forward path (used only to keep the det small)."""
    alive = set(V)
    succ = {v: set() for v in V}
    for v in V:
        for s in m.alph:
            for w in m.succ_v(v, s):
                succ[v].add(w)
    changed = True
    while changed:
        changed = False
        for v in list(alive):
            if not (succ[v] & alive):
                alive.discard(v)
                changed = True
    return alive


def determinize(m, start, limit=200000):
    idx = {start: 0}
    sets = [start]
    trans = []
    i = 0
    while i < len(sets):
        S = sets[i]
        row = {}
        for s in m.alph:
            T = m.succ_set(S, s)
            if not T:
                row[s] = None
                continue
            if T not in idx:
                idx[T] = len(sets)
                sets.append(T)
                if len(sets) > limit:
                    return None
            row[s] = idx[T]
        trans.append(row)
        i += 1
    return sets, trans


def tarjan(n, adj):
    index = [None] * n
    low = [0] * n
    on = [False] * n
    st = []
    comp = [None] * n
    cnt = [0]
    ncomp = [0]

    def strong(v0):
        stack = [(v0, iter(adj[v0]))]
        index[v0] = low[v0] = cnt[0]; cnt[0] += 1
        st.append(v0); on[v0] = True
        while stack:
            v, it = stack[-1]
            adv = False
            for w in it:
                if index[w] is None:
                    index[w] = low[w] = cnt[0]; cnt[0] += 1
                    st.append(w); on[w] = True
                    stack.append((w, iter(adj[w])))
                    adv = True
                    break
                elif on[w]:
                    low[v] = min(low[v], index[w])
            if adv:
                continue
            stack.pop()
            if stack:
                u = stack[-1][0]
                low[u] = min(low[u], low[v])
            if low[v] == index[v]:
                while True:
                    w = st.pop(); on[w] = False
                    comp[w] = ncomp[0]
                    if w == v:
                        break
                ncomp[0] += 1

    for v in range(n):
        if index[v] is None:
            strong(v)
    return comp, ncomp[0]


def certify(m, use_core=False, limit=200000):
    V = m.vertices()
    start = frozenset(forward_core(m, V)) if use_core else frozenset(V)
    r = determinize(m, start, limit)
    if r is None:
        return None, "det too large"
    sets, trans = r
    n = len(sets)
    adj = [[j for j in trans[i].values() if j is not None] for i in range(n)]
    comp, nc = tarjan(n, adj)
    # Tarjan numbers SCCs in reverse topological order: edges go comp[i] >= comp[j]
    rank = comp
    ok = True
    for i in range(n):
        same = [s for s, j in trans[i].items() if j is not None and rank[j] == rank[i]]
        if len(same) > 1:
            ok = False
        for j in trans[i].values():
            if j is not None:
                assert rank[j] <= rank[i]
    return dict(sets=sets, trans=trans, rank=rank, ok=ok), None


def main():
    ap = argparse.ArgumentParser()
    ap.add_argument("--pq", nargs=2, type=int, required=True)
    ap.add_argument("--nu", default="0")
    ap.add_argument("--P", required=True)
    ap.add_argument("--D", type=int, required=True)
    ap.add_argument("--core", action="store_true")
    ap.add_argument("--json", default=None)
    args = ap.parse_args()
    a, b = parse_frac(args.nu)
    P = [int(t) for t in args.P.split(",")]
    m = Model(args.pq[0], args.pq[1], a, b, P, args.D)
    cert, err = certify(m, args.core)
    if err:
        print(json.dumps(dict(ok=False, err=err)))
        return
    sizes = [len(S) for S in cert["sets"]]
    print(json.dumps(dict(ok=cert["ok"], det=len(cert["sets"]), total=sum(sizes),
                          maxset=max(sizes), M=m.M, D=m.D, alph=m.alph)))


if __name__ == "__main__":
    main()


# ---------------------------------------------------------------------------
# Lean emission: the EXACT semantics of DubC2/GenCert.lean (Params.succMask,
# peel, checkDet), on bitmask vertex sets k = r*D + c, r in [0,M), c in [0,D).

def fdiv(a, b):
    return a // b  # python floor division == Int.ediv for b > 0


class LeanModel:
    def __init__(self, p, q, a, b, P, D):
        self.p, self.q, self.a, self.b, self.D = p, q, a, b, D
        self.PM = [l for l in P if q % l != 0]
        self.Pq = [l for l in P if q % l == 0]
        M = 1
        for l in self.PM:
            M *= l
        self.M = M
        self.qinv = pow(q, -1, M) if M > 1 else 0
        lo = Fraction(-q * b - (p - q) * a, b)
        hi = Fraction(p * b - (p - q) * a, b)
        import math
        self.sLo = math.floor(lo) + 1
        self.nA = math.ceil(hi) - self.sLo
        self.nV = M * D
        self._sm = {}

    def letter(self, t):
        return self.sLo + t

    def succMask(self, k, s):
        key = (k, s)
        if key in self._sm:
            return self._sm[key]
        p, q, a, b, D, M = self.p, self.q, self.a, self.b, self.D, self.M
        r, c = k // D, k % D
        rn = (((p * r + s) * self.qinv) % M) if M > 0 else 0
        res = 0
        if (all(r % l != 0 for l in self.PM) and all(s % l != 0 for l in self.Pq)
                and all(rn % l != 0 for l in self.PM)):
            K = (p - q) * a * D + s * b * D
            lo = p * b * c - K
            hi = p * b * (c + 1) - K
            w = q * b
            cLo = max(0, fdiv(lo, w))
            cHi = min(D, max(0, fdiv(hi - 1, w) + 1))
            for c2 in range(cLo, cHi):
                if w * c2 < hi and lo < w * (c2 + 1):
                    res |= 1 << (rn * D + c2)
        self._sm[key] = res
        return res

    def bits(self, S):
        k = 0
        while S:
            if S & 1:
                yield k
            S >>= 1
            k += 1

    def peelStep(self, A):
        I = 0
        for k in self.bits(A):
            for t in range(self.nA):
                I |= self.succMask(k, self.letter(t))
        out = 0
        for k in self.bits(A):
            if not (I >> k) & 1:
                continue
            if any(self.succMask(k, self.letter(t)) & A for t in range(self.nA)):
                out |= 1 << k
        return out

    def image(self, A):
        I = 0
        for k in self.bits(A):
            for t in range(self.nA):
                I |= self.succMask(k, self.letter(t))
        return I

    def core(self):
        """the peel chain A_0 = all, A_{j+1} = peelStep A_j, to the fixpoint; and images."""
        A = (1 << self.nV) - 1
        peels, imgs = [], []
        while True:
            I = self.image(A)
            B = self.peelStep(A)
            if B == A:
                return A, len(peels), peels, imgs
            peels.append(B)
            imgs.append(I)
            A = B

    def detSucc(self, S, s):
        T = 0
        for k in self.bits(S):
            T |= self.succMask(k, s)
        return T

    def succList(self, k, s):
        m = self.succMask(k, s)
        return list(self.bits(m))

    def certificate(self, limit=20000):
        K, J, peels, imgs = self.core()
        core = list(self.bits(K))
        cidx = {v: i for i, v in enumerate(core)}
        succ = {}
        for v in core:
            for t in range(self.nA):
                msk = 0
                for w in self.succList(v, self.letter(t)):
                    if w in cidx:
                        msk |= 1 << cidx[w]
                succ[(cidx[v], t)] = msk
        full = (1 << len(core)) - 1
        sets = [full]
        idx = {full: 0}
        trans = []
        i = 0
        while i < len(sets):
            row = []
            for t in range(self.nA):
                T = 0
                for x in self.bits(sets[i]):
                    T |= succ[(x, t)]
                if T == 0:
                    row.append(None)
                else:
                    if T not in idx:
                        idx[T] = len(sets)
                        sets.append(T)
                        if len(sets) > limit:
                            return None
                    row.append(idx[T])
            trans.append(row)
            i += 1
        n = len(sets)
        adj = [[j for j in row if j is not None] for row in trans]
        comp, _ = tarjan(n, adj)
        ok = all(len([j for j in trans[i] if j is not None and comp[j] == comp[i]]) <= 1
                 for i in range(n))
        return dict(J=J, peels=peels, imgs=imgs, core=core, sets=sets, trans=trans, rank=comp,
                    ok=ok)

    def A(self, cert, j):
        return (1 << self.nV) - 1 if j == 0 else cert["peels"][j - 1]

    def lean(self, name, cert, Z=256, budget=30000):
        """Lean source: Params, Cert, and the Checked proof split into decide-pieces whose
        estimated kernel cost (succMask evaluations) stays under `budget`."""
        def opt(j):
            return "none" if j is None else f"some {j}"
        nB = (self.nV + Z - 1) // Z
        J = cert["J"]
        par = (f"/-- Parameters. -/\ndef {name}P : Params where\n  p := {self.p}\n  q := {self.q}\n"
               f"  a := {self.a}\n  b := {self.b}\n  D := {self.D}\n  M := {self.M}\n"
               f"  qinv := {self.qinv}\n  PM := {self.PM}\n  Pq := {self.Pq}\n"
               f"  sLo := {self.sLo}\n  nA := {self.nA}\n")
        L = lambda xs: "[" + ",\n    ".join(str(x) for x in xs) + "]"
        trans = "[" + ",\n    ".join("[" + ", ".join(opt(j) for j in row) + "]"
                                      for row in cert["trans"]) + "]"
        cer = (f"/-- Certificate. -/\ndef {name}C : Cert where\n  J := {J}\n  Z := {Z}\n  nB := {nB}\n"
               f"  peels := {L(cert['peels'])}\n  imgs := {L(cert['imgs'])}\n"
               f"  sets := {L(cert['sets'])}\n  trans := {trans}\n"
               f"  rank := {cert['rank']}\n")
        out = [par, cer]
        # cost model
        def round_cost(u):
            j, i = divmod(u, nB)
            blk = (self.A(cert, j) >> (i * Z)) & ((1 << Z) - 1)
            return 2 * self.nA * bin(blk).count("1") + Z // 16 + 1
        def det_cost(i):
            return self.nA * bin(cert["sets"][i]).count("1") + 1
        def pieces(kind, n, cost, fn):
            lems, lo, acc = [], 0, 0
            for u in range(n + 1):
                if u == n or (acc + cost(u) > budget and u > lo):
                    lems.append((lo, u - lo))
                    lo, acc = u, 0
                if u < n:
                    acc += cost(u)
            names = []
            for k, (a, m) in enumerate(lems):
                if m == 0:
                    continue
                nm = f"{name}_{kind}{k}"
                names.append((nm, a, m))
                out.append(f"theorem {nm} : (List.range' {a} {m}).all ({fn} {name}P {name}C) = true := by\n"
                           f"  decide +kernel\n")
            # glue
            expr = names[0][0]
            tot = names[0][2]
            for nm, a, m in names[1:]:
                expr = f"(all_range'_append {expr} {nm} rfl)"
                tot += m
            return expr, n
        rexpr, rn = pieces("r", J * nB, round_cost, "roundOK")
        dexpr, dn = pieces("d", len(cert["sets"]), det_cost, "detOK")
        out.append(f"theorem {name}_head : checkHead {name}P {name}C = true := by decide +kernel\n")
        out.append(f"/-- The certificate checks. -/\ntheorem {name}_checked : Checked {name}P {name}C where\n"
                   f"  head := {name}_head\n"
                   f"  rounds := by\n    rw [show {name}C.J * {name}C.nB = {rn} from rfl]\n    exact {rexpr}\n"
                   f"  det := by\n    rw [show {name}C.sets.length = {dn} from rfl]\n    exact {dexpr}\n")
        return "\n".join(out)


# ---------------------------------------------------------------------------
# Multi-module emission.  Kernel memory is not returned between declarations of one
# `lean` process, so a certificate is split over a LINEAR chain of modules
#   Data -> Part1 -> Part2 -> ... -> Main
# (each part imports the previous one, so lake can only build them one at a time),
# each part holding decide-pieces of total estimated cost <= module_budget.

HEADER = """/-
(C) 2026 Ralf Stephan, in collaboration with Claude Code.
Released under CC0 1.0 Universal (public-domain dedication).
See https://creativecommons.org/publicdomain/zero/1.0/
-/
"""


def frac_lean(a, b):
    return f"{a}" if b == 1 else f"{a} / {b}"


def emit_instance(m, cert, name, outdir, title, piece_budget=12000, module_budget=36000, Z=256,
                  ref="DN05", group="dubc2_atlas", status="research solved", prev=None,
                  modroot="DubC2.Atlas", member_budget=None):
    """`member_budget` (default `piece_budget`) caps the member-by-letter pieces of a split
    det state; each `decide` there holds its whole evaluation, on top of a ~4.6 GB baseline."""
    import glob
    import os
    os.makedirs(outdir, exist_ok=True)
    for old in glob.glob(os.path.join(outdir, "Part*.lean")):  # stale generated parts
        os.remove(old)
    mod = modroot + "." + name
    nB = (m.nV + Z - 1) // Z
    J = cert["J"]

    def opt(j):
        return "none" if j is None else f"some {j}"
    L = lambda xs: "[" + ",\n    ".join(str(x) for x in xs) + "]"
    blocks = lambda A: "[" + ", ".join(str((A >> (i * Z)) & ((1 << Z) - 1)) for i in range(nB)) + "]"
    LB = lambda As: "[" + ",\n    ".join(blocks(A) for A in As) + "]"
    trans = "[" + ",\n    ".join("[" + ", ".join(opt(j) for j in row) + "]"
                                  for row in cert["trans"]) + "]"
    data = (HEADER + f"import {prev or 'DubC2.GenSound'}\n\n"
            f"/-! Certificate data for `{mod}` — generated by `DubC2/gencert.py`; do not edit. -/\n\n"
            "namespace DubC2.Atlas\n\nopen DubC2.Gen\n\n"
            f"/-- Parameters. -/\ndef {name}P : Params where\n  p := {m.p}\n  q := {m.q}\n  a := {m.a}\n"
            f"  b := {m.b}\n  D := {m.D}\n  M := {m.M}\n  qinv := {m.qinv}\n  PM := {m.PM}\n"
            f"  Pq := {m.Pq}\n  sLo := {m.sLo}\n  nA := {m.nA}\n\n"
            f"set_option maxRecDepth 100000 in\n/-- Certificate. -/\ndef {name}C : Cert where\n  J := {J}\n  Z := {Z}\n  nB := {nB}\n"
            f"  peels := {LB(cert['peels'])}\n  imgs := {LB(cert['imgs'])}\n"
            f"  core := {cert['core']}\n"
            f"  sets := {L(cert['sets'])}\n  trans := {trans}\n  rank := {cert['rank']}\n\n"
            f"set_option maxRecDepth 100000 in\ntheorem {name}_head : checkHead {name}P {name}C = true := by decide +kernel\n\n"
            "end DubC2.Atlas\n")
    open(os.path.join(outdir, "Data.lean"), "w").write(data)

    def round_cost(u):
        j, i = divmod(u, nB)
        blk = (m.A(cert, j) >> (i * Z)) & ((1 << Z) - 1)
        return 4 * m.nA * bin(blk).count("1") + Z // 32 + 1

    def det_cost(i):
        S = cert["sets"][i]
        # each member costs a successor list plus linear scans of the core (contains / idxOf)
        return 2 * m.nA * (bin(S).count("1") * (len(cert["core"]) // 8 + 1) + S.bit_length() // 32) + 1

    def pieces(n, cost, budget=piece_budget):
        out, lo, acc = [], 0, 0
        for u in range(n + 1):
            if u == n or (acc + cost(u) > budget and u > lo):
                if u > lo:
                    out.append((lo, u - lo, acc))
                lo, acc = u, 0
            if u < n:
                acc += cost(u)
        return out

    items = [("r", a, k, c) for a, k, c in pieces(J * nB, round_cost)]
    # det rows: consecutive cheap states share a piece; a state too expensive for one `decide`
    # is split into member-by-letter pieces (`detRowOK`) and reassembled by `detOK_of_rows`
    mem_cost = 2 * (len(cert["core"]) // 8 + 1) + 1
    nS, lo, acc = len(cert["sets"]), 0, 0
    split = {}
    for i in range(nS + 1):
        c = det_cost(i) if i < nS else 0
        if i == nS or c > piece_budget or (acc + c > piece_budget and i > lo):
            if i > lo:
                items.append(("d", lo, i - lo, acc))
            lo, acc = i, 0
        if i < nS and c > piece_budget:
            Lm = bin(cert["sets"][i]).count("1")
            split[i] = Lm
            for a, k, cc in pieces(m.nA * Lm, lambda u: mem_cost, member_budget or piece_budget):
                items.append(("u", (i, a), k, cc))
            items.append(("x", i, 1, 1))
            lo = i + 1
        elif i < nS:
            acc += c
    # group into modules
    mods, cur, acc = [], [], 0
    for it in items:
        if cur and acc + it[3] > module_budget:
            mods.append(cur)
            cur, acc = [], 0
        cur.append(it)
        acc += it[3]
    if cur:
        mods.append(cur)
    def glue(lst):
        """balanced gluing with explicit numerals; returns (term, a, n)"""
        if len(lst) == 1:
            return lst[0][0], lst[0][1], lst[0][2]
        h = len(lst) // 2
        e1, a1, n1 = glue(lst[:h])
        e2, a2, n2 = glue(lst[h:])
        assert a2 == a1 + n1
        return f"(all_glue _ {a1} {n1} {n2} {n1 + n2} {e1} {e2} rfl)", a1, n1 + n2
    prev = mod + ".Data"
    names = {"r": [], "d": []}
    for k, group_items in enumerate(mods):
        body = [HEADER, f"import {prev}\n\n",
                f"/-! Certificate pieces for `{mod}`, part {k + 1}/{len(mods)} — generated; do not edit. -/\n\n",
                "namespace DubC2.Atlas\n\nopen DubC2.Gen\n\n"]
        for kind, a, cnt, c in group_items:
            if kind == "u":
                i, a = a
                nm = f"{name}_d{i}_u{a}"
                names.setdefault(("u", i), []).append((nm, a, cnt))
                body.append(f"theorem {nm} : (List.range' {a} {cnt}).all (detRowOK {name}P {name}C {i} "
                            f"{split[i]}) = true := by\n  decide +kernel\n\n")
                continue
            if kind == "x":
                nm = f"{name}_d{a}"
                names["d"].append((nm, a, 1))
                body.append(f"theorem {nm} : (List.range' {a} 1).all (detOK {name}P {name}C) = true :=\n"
                            f"  all_range'_one (detOK_of_rows (by decide +kernel) (by decide +kernel)\n"
                            f"    (by decide +kernel) {glue(names[('u', a)])[0]})\n\n")
                continue
            fn = "roundOK" if kind == "r" else "detOK"
            nm = f"{name}_{kind}{a}"
            names[kind].append((nm, a, cnt))
            body.append(f"theorem {nm} : (List.range' {a} {cnt}).all ({fn} {name}P {name}C) = true := by\n"
                        f"  decide +kernel\n\n")
        body.append("end DubC2.Atlas\n")
        open(os.path.join(outdir, f"Part{k + 1}.lean"), "w").write("".join(body))
        prev = f"{mod}.Part{k + 1}"

    P = sorted(m.PM + m.Pq)
    plist = "[" + ", ".join(str(l) for l in P) + "]"
    nu = frac_lean(m.a, m.b)
    base = f"(({m.p} : ℝ) / {m.q})"
    stmt = f"⌊ξ * {base} ^ n + {nu}⌋" if not (m.a == 0) else f"⌊ξ * {base} ^ n⌋"
    main = (HEADER + f"import {prev}\n\n"
            f"/-!\n# {title}\n\nGenerated by `DubC2/gencert.py` from the `(p/q, ν, 𝒫)` atlas of plan-dubC2 M2;\n"
            f"checked by `DubC2.Gen.divisor_set_of_checked`.  Graph: `D = {m.D}` cells, residues mod "
            f"`M = {m.M}`, {len(cert['core'])}-vertex core after `J = {J}` peeling rounds, "
            f"{len(cert['sets'])} determinized states.\n-/\n\n"
            "namespace DubC2.Atlas\n\nopen Filter DubC2.Gen\n\n"
            f"set_option maxRecDepth 100000 in\n"
            f"theorem {name}_checked : Checked {name}P {name}C where\n  head := {name}_head\n"
            f"  rounds := by\n    rw [show {name}C.J * {name}C.nB = {J * nB} by decide +kernel]\n"
            f"    exact {glue(names['r'])[0]}\n"
            f"  det := by\n    rw [show {name}C.sets.length = {len(cert['sets'])} by decide +kernel]\n"
            f"    exact {glue(names['d'])[0]}\n\n"
            f"/-- {title}: for every real `ξ ≠ 0`, infinitely many of `{stmt.replace('ξ', 'ξ')}` are "
            f"divisible by a member of `{plist}`. -/\n"
            f"@[category {status}, AMS 11 37, ref \"{ref}\", group \"{group}\"]\n"
            f"theorem {name} {{ξ : ℝ}} (hξ : ξ ≠ 0) :\n"
            f"    ∃ᶠ n in atTop, ∃ ℓ ∈ ({plist} : List ℤ), ℓ ∣ {stmt} := by\n"
            f"  refine (divisor_set_of_checked {name}_checked hξ).mono fun n ⟨ℓ, hℓ, hd⟩ => ⟨ℓ, ?_, ?_⟩\n"
            f"  · exact (by decide +kernel : ∀ l ∈ {name}P.PM ++ {name}P.Pq, (l : ℤ) ∈ ({plist} : List ℤ)) ℓ hℓ\n"
            f"  · simpa [{name}P, Z32.xInt, Z32.orb] using hd\n\n"
            "end DubC2.Atlas\n")
    open(os.path.join(outdir, "Main.lean"), "w").write(main)
    return len(mods)


# ---------------------------------------------------------------------------
# The atlas registry: instances are emitted in a fixed order and chained
# (instance k's Data imports instance k-1's Main), so the whole atlas is ONE linear
# import chain and lake can never build two certificate modules at once.

import json as _json
import os as _os

REG = _os.path.join(_os.path.dirname(_os.path.abspath(__file__)), "Atlas", "registry.json")


def load_registry():
    try:
        return _json.load(open(REG))
    except FileNotFoundError:
        return []


def save_registry(reg):
    _json.dump(reg, open(REG, "w"), indent=1)
    idx = HEADER + "".join(f"import DubC2.Atlas.{e['name']}.Main\n" for e in reg[-1:]) + (
        "\n/-!\n# The `(p/q, ν, 𝒫)` divisor-set atlas of plan-dubC2 (M2)\n\n"
        "Every entry is a machine-checked theorem of the form: for every real `ξ ≠ 0`, infinitely many\n"
        "of `⌊ξ(p/q)ⁿ + ν⌋` are divisible by a member of `𝒫`.  The entries form one linear import\n"
        "chain (see `DubC2/gencert.py`), so importing the last one imports them all:\n\n" +
        "".join(f"* `DubC2.Atlas.{e['name']}` — {e['title']}\n" for e in reg) + "-/\n")
    open(_os.path.join(_os.path.dirname(REG), "..", "Atlas.lean"), "w").write(idx)


def add_instance(p, q, nu, P, D, title, name=None, **kw):
    """certify, emit and register one atlas entry (appended at the end of the chain)."""
    from fractions import Fraction as _F
    f = _F(nu)
    m = LeanModel(p, q, f.numerator, f.denominator, sorted(P), D)
    cert = m.certificate()
    if cert is None or not cert["ok"]:
        raise ValueError("no certificate")
    if name is None:
        nus = (f"{f.numerator}_{f.denominator}" if f.denominator > 1 else f"{f.numerator}").replace("-", "m")
        name = f"b{p}_{q}_nu{nus}_P" + "_".join(str(l) for l in sorted(P))
    reg = load_registry()
    names = [e["name"] for e in reg]
    if name in names:
        pos = names.index(name)
        prev = f"DubC2.Atlas.{reg[pos - 1]['name']}.Main" if pos > 0 else None
    else:
        prev = f"DubC2.Atlas.{reg[-1]['name']}.Main" if reg else None
    nmod = emit_instance(m, cert, name, _os.path.join(_os.path.dirname(REG), name), title,
                         prev=prev, **kw)
    entry = dict(name=name, p=p, q=q, nu=str(f), P=sorted(P), D=D, title=title,
                 core=len(cert["core"]), det=len(cert["sets"]), J=cert["J"], parts=nmod)
    if name in names:
        reg[names.index(name)] = entry
    else:
        reg.append(entry)
    save_registry(reg)
    return entry


# ---------------------------------------------------------------------------
# Fast verdict for searching: same graph, same peel (to the fixpoint), same det-on-core
# criterion as LeanModel.certificate(), on Python sets instead of big-int bitmasks.

def fast_verdict(p, q, a, b, P, D, det_limit=3000):
    m = LeanModel(p, q, a, b, P, D)
    D_, M = m.D, m.M
    PM, Pq = m.PM, m.Pq
    w = q * b
    letters = [m.letter(t) for t in range(m.nA)]
    good_r = [r for r in range(M) if all(r % l for l in PM)]
    succ = {}
    pred = {}
    for r in good_r:
        for c in range(D_):
            k = r * D_ + c
            row = []
            for t, s in enumerate(letters):
                if any(s % l == 0 for l in Pq):
                    row.append(())
                    continue
                rn = ((p * r + s) * m.qinv) % M if M > 0 else 0
                if any(rn % l == 0 for l in PM):
                    row.append(())
                    continue
                K = (p - q) * a * D_ + s * b * D_
                lo = p * b * c - K
                hi = p * b * (c + 1) - K
                c0 = max(0, lo // w)
                c1 = min(D_, max(0, (hi - 1) // w + 1))
                tg = tuple(rn * D_ + c2 for c2 in range(c0, c1) if w * c2 < hi and lo < w * (c2 + 1))
                row.append(tg)
                for x in tg:
                    pred.setdefault(x, set()).add(k)
            succ[k] = row
    alive = set(succ)
    # alternating peel to the fixpoint (same fixpoint as the Lean chain)
    changed = True
    while changed:
        changed = False
        rm = [k for k in alive
              if not any(x in alive for tg in succ[k] for x in tg)
              or not any(u in alive for u in pred.get(k, ()))]
        if rm:
            changed = True
            alive.difference_update(rm)
    if not alive:
        return dict(ok=True, core=0, det=1)
    core = sorted(alive)
    start = frozenset(core)
    idx = {start: 0}
    sets = [start]
    trans = []
    i = 0
    while i < len(sets):
        row = []
        for t in range(m.nA):
            T = frozenset(x for k in sets[i] for x in succ[k][t] if x in alive)
            if not T:
                row.append(None)
                continue
            if T not in idx:
                idx[T] = len(sets)
                sets.append(T)
                if len(sets) > det_limit:
                    return None
            row.append(idx[T])
        trans.append(row)
        i += 1
    n = len(sets)
    adj = [[j for j in row if j is not None] for row in trans]
    comp, _ = tarjan(n, adj)
    ok = all(len([j for j in trans[i] if j is not None and comp[j] == comp[i]]) <= 1
             for i in range(n))
    return dict(ok=ok, core=len(core), det=n)
