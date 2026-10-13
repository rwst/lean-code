#!/usr/bin/env python3
# (C) 2026 Ralf Stephan, in collaboration with Claude Code.  CC0 1.0.
#
# xfcheck.py -- plan-dubC2-transform, T5(iv) on concrete cells: emit DubC2/FollowerAtlas.lean.
#
# Builds the follower automaton of a cell exactly as DubC2/FollowerCheck.lean encodes it
# (`DubC2.Gen.Follower.checkF`): one bitmask per prime of PM (root = all residues, the zero residue
# dropped by every step), the interval as numerators over a common denominator Q, the step in
# integers (`aedge`).  Labels = index of the strongly connected component in Tarjan's output order
# (sinks first), so labels never increase along an edge and stay equal exactly inside an SCC.
# The cell passes iff every state keeps its label along at most one letter (no branching state).
# States go into a balanced binary search tree under the order of `LTree.cmpK`.
#
# Usage:
#   xfcheck.py                     # report the cells
#   xfcheck.py --emit-dir DubC2/FollowerAtlas      (from the repo root)

import argparse
import math
import os
import sys
from fractions import Fraction

sys.setrecursionlimit(100_000)

CHUNK = 256

# (p, q, a, b, P, note): the certified frontier cells of note §11 (xz_frontier.jsonl), smallest F first.
CELLS = [
    (7, 5, 0, 1, [2, 3, 7, 11, 13], "not in [Oda26] or [DN05]"),
    (7, 5, 0, 1, [2, 3, 5, 11, 13], "[Oda26] Thm 1, re-checked"),
    (5, 4, -1, 1, [2, 3, 5, 7, 11, 13], "not in [Oda26] or [DN05]"),
    (5, 4, 0, 1, [2, 3, 7, 11, 13], "[DN05] Thm 1, re-checked"),
    (7, 5, 0, 1, [2, 3, 5, 11, 17], "not in [Oda26] or [DN05]"),
    (7, 5, 0, 1, [2, 3, 7, 11, 17], "not in [Oda26] or [DN05]"),
    (5, 4, 0, 1, [2, 3, 7, 11, 17], "not in [Oda26] or [DN05]"),
]


class Cell:
    def __init__(self, p, q, a, b, P):
        self.p, self.q, self.a, self.b, self.P = p, q, a, b, sorted(P)
        self.PM = [l for l in self.P if q % l]
        self.Pq = [l for l in self.P if q % l == 0]
        self.M = math.prod(self.PM)
        self.qinv = pow(q, -1, self.M)
        # checkParams: b(sLo - 1) <= -q b - (p - q) a  and  p b - (p - q) a <= b (sLo + nA)
        self.sLo = math.floor(Fraction(-q * b - (p - q) * a, b)) + 1
        self.nA = math.ceil(Fraction(p * b - (p - q) * a, b)) - self.sLo
        self.inv = {l: pow(q, -1, l) for l in self.PM}

    def name(self):
        nu = Fraction(self.a, self.b)
        nus = "nu0" if nu == 0 else ("num" + str(-nu.numerator) if nu < 0 and nu.denominator == 1
                                     else "nu%d_%d" % (nu.numerator, nu.denominator))
        return "b%d_%d_%s_P%s" % (self.p, self.q, nus, "_".join(map(str, self.P)))

    # ---------------------------------------------------------------- exact rational automaton
    def follower_q(self):
        """the automaton with rational endpoints; returns the lcm of the endpoint denominators"""
        p, q, c = self.p, self.q, Fraction((self.p - self.q) * self.a, self.b)
        root = (tuple((1 << l) - 1 for l in self.PM), Fraction(0), Fraction(1))
        seen, todo, den = {root}, [root], 1
        while todo:
            ms, lo, hi = todo.pop()
            den = math.lcm(den, lo.denominator, hi.denominator)
            for t in range(self.nA):
                s = self.sLo + t
                if any(s % l == 0 for l in self.Pq):
                    continue
                lo2 = max(Fraction(0), (p * lo - s - c) / q)
                hi2 = min(Fraction(1), (p * hi - s - c) / q)
                if not lo2 < hi2:
                    continue
                ms2 = self.msteps(ms, s)
                if ms2 is None:
                    continue
                y = (ms2, lo2, hi2)
                if y not in seen:
                    seen.add(y)
                    todo.append(y)
        return den

    def mstep(self, l, m, s):
        n, inv = 0, self.inv[l]
        for r in range(l):
            if m >> r & 1 and r != 0:
                r2 = (self.p * r + s) * inv % l
                if r2 != 0:
                    n |= 1 << r2
        return n

    def msteps(self, ms, s):
        out = tuple(self.mstep(l, m, s) for l, m in zip(self.PM, ms))
        return None if any(m == 0 for m in out) else out

    # ---------------------------------------------------------------- the Lean encoding
    def ufw(self, Q, A, s):
        p, q, a, b = self.p, self.q, self.a, self.b
        return p * b * A - (s * b + (p - q) * a) * Q

    def aedge(self, Q, k, s):
        """mirror of `aedge`: None = dies, else the successor key; raises if off the grid"""
        ms, A, B = k
        if any(s % l == 0 for l in self.Pq):
            return None
        w = self.q * self.b
        L = max(0, self.ufw(Q, A, s))
        H = min(w * Q, self.ufw(Q, B, s))
        if not L < H:
            return None
        ms2 = tuple(self.mstep(l, m, s) for l, m in zip(self.PM, ms))
        if any(m == 0 for m in ms2):
            return None
        assert L % w == 0 and H % w == 0, "endpoint off the grid"
        return (ms2, L // w, H // w)

    def build(self):
        Q = self.follower_q()
        root = (tuple((1 << l) - 1 for l in self.PM), 0, Q)
        idx, keys, adj = {root: 0}, [root], []
        i = 0
        while i < len(keys):
            e = []
            for t in range(self.nA):
                y = self.aedge(Q, keys[i], self.sLo + t)
                if y is None:
                    continue
                if y not in idx:
                    idx[y] = len(keys)
                    keys.append(y)
                e.append((t, idx[y]))
            adj.append(e)
            i += 1
        self.Q, self.keys, self.adj = Q, keys, adj
        self.lab = tarjan(len(keys), [[j for _, j in e] for e in adj])
        self.ok = all(sum(1 for _, j in adj[i] if self.lab[j] == self.lab[i]) <= 1
                      for i in range(len(keys)))
        assert all(self.lab[j] <= self.lab[i] for i in range(len(keys)) for _, j in adj[i])
        return self


def tarjan(n, adj):
    """SCC index per vertex, in Tarjan's output order (an SCC comes after every SCC it reaches)."""
    index, low, on, st, comp = [None] * n, [0] * n, [False] * n, [], [None] * n
    counter, ncomp = 0, 0
    for v0 in range(n):
        if index[v0] is not None:
            continue
        work = [(v0, 0)]
        while work:
            v, pi = work.pop()
            if pi == 0:
                index[v] = low[v] = counter
                counter += 1
                st.append(v)
                on[v] = True
            recurse = False
            for k in range(pi, len(adj[v])):
                w = adj[v][k]
                if index[w] is None:
                    work.append((v, k + 1))
                    work.append((w, 0))
                    recurse = True
                    break
                if on[w]:
                    low[v] = min(low[v], index[w])
            if recurse:
                continue
            if low[v] == index[v]:
                while True:
                    w = st.pop()
                    on[w] = False
                    comp[w] = ncomp
                    if w == v:
                        break
                ncomp += 1
            if work:
                u = work[-1][0]
                low[u] = min(low[u], low[v])
    return comp


# ---------------------------------------------------------------- Lean emission

def tree_lean(items, lo, hi):
    if lo >= hi:
        return ".leaf"
    mid = (lo + hi) // 2
    (ms, A, B), lab = items[mid]
    return "(.node %s [%s] %d %d %d %s)" % (tree_lean(items, lo, mid), ", ".join(map(str, ms)),
                                          A, B, lab, tree_lean(items, mid + 1, hi))


def split_tree(n, items, chunk):
    """the tree with every subtree of at most `chunk` nodes as its own definition.
    Returns (chunk defs [(name, body)], skeleton expression with `g` for the check of the top
    nodes, top expression of the tree)."""
    chunks, top = [], []

    def go(lo, hi):
        if lo >= hi:
            return ".leaf", "true"
        if hi - lo <= chunk:
            name = "%sT%d" % (n, len(chunks))
            chunks.append((name, tree_lean(items, lo, hi)))
            return name, "%s.all g" % name
        mid = (lo + hi) // 2
        (ms, A, B), lab = items[mid]
        tl, al = go(lo, mid)
        tr, ar = go(mid + 1, hi)
        key = "([%s], %d, %d)" % (", ".join(map(str, ms)), A, B)
        top.append((key, lab))
        return ("(.node %s [%s] %d %d %d %s)" % (tl, ", ".join(map(str, ms)), A, B, lab, tr),
                "(g %s %d && %s && %s)" % (key, lab, al, ar))

    expr, skel = go(0, len(items))
    return chunks, top, expr, skel


def nu_term(a, b):
    if a == 0:
        return ""
    return (" + %d" % a) if b == 1 else " + (%d : ℝ) / %d" % (a, b)


HEADER = ["/-",
          "(C) 2026 Ralf Stephan, in collaboration with Claude Code.",
          "Released under CC0 1.0 Universal (public-domain dedication).",
          "See https://creativecommons.org/publicdomain/zero/1.0/",
          "-/"]

DOC = ["For each cell: the follower automaton `F` as a search tree of encoded states with SCC",
       "labels, checked by the kernel (`DubC2.Gen.Follower.checkF`).  The check gives that `F` is",
       "finite and has no reachable branching state, so `DubC2.Gen.Follower.T5iv` applies: a",
       "certificate exists at `D = Q` (the common denominator of the endpoints).  The certificate is",
       "never built.  Its existence already gives the divisibility theorem through",
       "`DubC2.Gen.divisor_set_of_checked`."]


def cell_desc(c):
    Ps = "{" + ", ".join(map(str, c.P)) + "}"
    nu = Fraction(c.a, c.b)
    nus = str(nu) if nu >= 0 else "−" + str(-nu)
    return "Base %d/%d, ν = %s, 𝒫 = %s" % (c.p, c.q, nus, Ps)


def emit_dir(cells, d):
    """one file per cell in a linear import chain, and the umbrella file `d`.lean"""
    os.makedirs(d, exist_ok=True)
    mod = d.rstrip("/").replace("/", ".")
    prev = "DubC2.FollowerCheck"
    for c, note in cells:
        n = c.name()
        out = HEADER + ["import " + prev, "",
                        "/-! Follower automaton of `%s.%s` (%s) — generated by `DubC2/xfcheck.py`;"
                        % (mod, n, cell_desc(c)),
                        "do not edit.  %d states, %d strongly connected components, `Q = %d`. -/"
                        % (len(c.keys), len(set(c.lab)), c.Q), "",
                        "namespace DubC2.FollowerAtlas", "",
                        "open DubC2.Gen DubC2.Gen.Follower Filter", ""]
        out += emit_cell(c, note)
        out += ["end DubC2.FollowerAtlas", ""]
        with open(os.path.join(d, n + ".lean"), "w") as f:
            f.write("\n".join(out))
        prev = mod + "." + n
    out = HEADER + ["import " + prev, "",
                    "/-!",
                    "# Frontier cells certified through the follower automaton (generated)",
                    "",
                    "Generated by `DubC2/xfcheck.py --emit-dir`; do not edit."] + [""] + DOC + [
                    "",
                    "The cells form one linear import chain, so importing the last one imports them all:",
                    ""]
    for c, note in cells:
        out.append("* `%s.%s` — %s (%s)" % (mod, c.name(), cell_desc(c), note))
    out += ["-/", ""]
    with open(d.rstrip("/") + ".lean", "w") as f:
        f.write("\n".join(out))


def emit_cell(c, note):
    out = []
    if True:
        n = c.name()
        items = sorted(zip(c.keys, c.lab))
        Ps = "{" + ", ".join(map(str, c.P)) + "}"
        nu = Fraction(c.a, c.b)
        nus = str(nu) if nu >= 0 else "−" + str(-nu)
        out += ["/-- Parameters of `%d/%d`, `ν = %s`, `𝒫 = %s`, at `D = Q = %d`. -/" % (c.p, c.q, nus, Ps, c.Q),
                "def %sP : Params where" % n,
                "  p := %d" % c.p, "  q := %d" % c.q, "  a := %d" % c.a, "  b := %d" % c.b,
                "  D := %d" % c.Q, "  M := %d" % c.M, "  qinv := %d" % c.qinv,
                "  PM := [%s]" % ", ".join(map(str, c.PM)), "  Pq := [%s]" % ", ".join(map(str, c.Pq)),
                "  sLo := %d" % c.sLo, "  nA := %d" % c.nA,
                "",
                ]
        chunks, top, expr, skel = split_tree(n, items, CHUNK)
        for cn, body in chunks:
            out += ["set_option maxRecDepth 100000 in",
                    "/-- A subtree of the follower automaton. -/",
                    "def %s : LTree :=" % cn, "  " + body, ""]
        out += ["/-- The follower automaton: %d states, labelled by strongly connected component. -/" % len(items),
                "def %sT : LTree :=" % n, "  " + expr, "",
                "theorem %sT_all (g : Key → ℕ → Bool) : %sT.all g =" % (n, n),
                "    " + skel + " := rfl", ""]
        for cn, _ in chunks:
            out += ["theorem %s_ok : %s.all (nodeOK %sP %d %sT) = true := by decide +kernel" % (cn, cn, n, c.Q, n), ""]
        out += ["theorem %s_top : [%s].all (fun x => nodeOK %sP %d %sT x.1 x.2) = true := by decide +kernel"
                % (n, ", ".join("(%s, %d)" % t for t in top), n, c.Q, n), "",
                "theorem %s_head : (checkParams %sP && checkCRT %sP && decide (0 < %d) &&" % (n, n, n, c.Q),
                "    (%sT.find (rootKey %sP %d)).isSome) = true := by decide +kernel" % (n, n, c.Q), "",
                "theorem %s_checkF : checkF %sP %d %sT = true := by" % (n, n, c.Q, n),
                "  have ht := %s_top" % n,
                "  simp only [List.all_cons, List.all_nil, Bool.and_true, Bool.and_eq_true] at ht",
                "  rw [checkF, %s_head, %sT_all]" % (n, n),
                "  simp only [ht, %s, Bool.and_true]" % ", ".join(cn + "_ok" for cn, _ in chunks),
                "",
                ]
        out += [
                "/-- `%d/%d`, `ν = %s`, `𝒫 = %s`: the follower automaton is finite without branching, so all"
                % (c.p, c.q, nus, Ps),
                "four conditions of T5(iv) hold. -/",
                "@[category research solved, AMS 11 37, ref \"Oda26\", group \"dubc2_obstruction\"]",
                "theorem %s_T5iv : (∀ X, Reach %sP (root %sP) X → ¬ Branching %sP X) ∧ PolyGrowth %sP ∧"
                % (n, n, n, n, n),
                "    ∃ D C, Checked { %sP with D := D } C :=" % n,
                "  let ⟨_, h1, _, h3, h4⟩ := T5iv_of_checkF %s_checkF" % n,
                "  ⟨h3, h4, h1⟩",
                "",
                "/-- `%d/%d`, `ν = %s`, `𝒫 = %s` (%s): for every real `ξ ≠ 0`, infinitely many of" % (c.p, c.q, nus, Ps, note),
                "`⌊ξ(%d/%d)ⁿ + %s⌋` are divisible by a member of `%s`. -/" % (c.p, c.q, nus, Ps),
                "@[category research solved, AMS 11 37, ref \"Oda26\", group \"dubc2_atlas\"]",
                "theorem %s {ξ : ℝ} (hξ : ξ ≠ 0) :" % n,
                "    ∃ᶠ n in atTop, ∃ ℓ ∈ ([%s] : List ℤ), ℓ ∣ ⌊ξ * ((%d : ℝ) / %d) ^ n%s⌋ := by"
                % (", ".join(map(str, c.P)), c.p, c.q, nu_term(c.a, c.b)),
                "  obtain ⟨C, hC⟩ := exists_checked_of_checkF %s_checkF rfl" % n,
                "  refine (divisor_set_of_checked hC hξ).mono fun n ⟨ℓ, hℓ, hd⟩ => ⟨ℓ, ?_, ?_⟩",
                "  · exact (by decide +kernel : ∀ l ∈ %sP.PM ++ %sP.Pq, (l : ℤ) ∈ ([%s] : List ℤ)) ℓ hℓ"
                % (n, n, ", ".join(map(str, c.P))),
                "  · simpa [%sP, Z32.xInt, Z32.orb] using hd" % n,
                ""]
    return out


def main():
    ap = argparse.ArgumentParser()
    ap.add_argument("--emit-dir", default="", help="e.g. DubC2/FollowerAtlas (run from the repo root)")
    args = ap.parse_args()
    done = []
    for (p, q, a, b, P, note) in CELLS:
        c = Cell(p, q, a, b, P).build()
        print(c.name(), "states", len(c.keys), "edges", sum(map(len, c.adj)), "Q", c.Q,
              "sccs", len(set(c.lab)), "ok", c.ok, flush=True)
        if c.ok:
            done.append((c, note))
    if args.emit_dir:
        emit_dir(done, args.emit_dir)
        print("wrote", args.emit_dir)


if __name__ == "__main__":
    main()
