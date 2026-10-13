#!/usr/bin/env python3
# (C) 2026 Ralf Stephan, in collaboration with Claude Code.  CC0 1.0.
#
# xcensus.py -- plan-dubC2-transform, experiment X-C (claims C-3, C-8; lane alpha3).
#
# For each atlas cell (p/q, nu = a/b, P) of DubC2/Atlas/registry.json:
#
#  (1) det cycles: parse the checked certificate from Atlas/<name>/Data.lean (Params sLo,
#      Cert trans/rank) and list the non-trivial SCCs of the determinized core.  In a checked
#      certificate every state keeps its rank by at most one letter, so each such SCC is a
#      simple cycle; its label is a letter word.
#  (2) census: every periodic avoiding pseudo-orbit of period <= PMAX, exactly.  A pseudo-orbit
#      is a sequence (r_n, y_n, s_n) with r_n in Z/M avoiding PM, s_n in the alphabet avoiding
#      Pq, r_{n+1} = q^{-1}(p r_n + s_n) mod M avoiding PM, y_n in [0,1) and
#      q y_{n+1} = p y_n - s_n - (p-q) nu.  Depth-first over words with the exact half-open
#      interval of admissible y_0 (Fractions); at each depth the closing condition
#      r_P = r_0 and y* = beta_P / (1 - (p/q)^P) in the interval.  y* is checked to have
#      denominator dividing b (p^P - q^P).
#  (3) matching (C-3): det cycles vs. pseudo-orbits, by the primitive root of the letter word
#      up to rotation (= the y-cycle).  Pseudo-orbit => det cycle is a theorem (soundness); the
#      converse is the claim.  A literal bijection also needs no two det cycles on one word
#      (det_dupes = 0) and no y-cycle with two residue lifts (lifts = 0).
#  (4) balance (C-8): for each det cycle word, (i) the plan's literal form
#      max_letter #letter - min_letter #letter <= 1 over one period (letters that occur), and
#      (ii) Sturmian balance: for every letter and every length, cyclic factors differ by <= 1.
#  (5) alpha3 (--ladder): for the hand-chain cells, the certificate (gencert.LeanModel) at every
#      D <= DMAX: certified?, det-cycle roots == census roots?, peel depth J.
#
# Output: DubC2/data/transform/xc_census<tag>.jsonl (one row per cell), xc_ladder<tag>.jsonl.
# Reproduce: python3 DubC2/xcensus.py --ladder 120
#            python3 DubC2/xcensus.py --pmax 24 --ladder 120 --tag _p24 \
#              --only b3_2_nu0_P2_5_7_11,b5_2_nu1_2_P2_3_7_11,b3_2_nu0_P2_7_11_13,b3_2_nu0_P3_5_7_11

import argparse
import json
import os
import re
import sys
import time
from fractions import Fraction
from math import gcd

HERE = os.path.dirname(os.path.abspath(__file__))
sys.path.insert(0, HERE)
from gencert import LeanModel, tarjan  # noqa: E402

PMAX = 14
HAND = ["b3_2_nu1_2_P2_5", "b5_3_nu1_2_P2_3", "b7_5_nu1_2_P2_3_5_11", "b3_2_nu0_P2_5_7_11"]


# ---------------------------------------------------------------- words

def prim_root(w):
    w = tuple(w)
    n = len(w)
    for d in range(1, n + 1):
        if n % d == 0 and w == w[:d] * (n // d):
            return w[:d]
    return w


def canon(w):
    w = tuple(w)
    return min(w[i:] + w[:i] for i in range(len(w))) if w else w


def root_key(w):
    return canon(prim_root(w))


def balance(w):
    w = list(w)
    n = len(w)
    letters = sorted(set(w))
    cnt = [w.count(x) for x in letters]
    literal = max(cnt) - min(cnt) <= 1
    sturm = True
    ww = w + w
    for x in letters:
        for L in range(1, n):
            c = [sum(1 for t in ww[i:i + L] if t == x) for i in range(n)]
            if max(c) - min(c) > 1:
                sturm = False
                break
        if not sturm:
            break
    return literal, sturm


# ---------------------------------------------------------------- det cycles from Data.lean

def parse_data(path):
    src = open(path).read()

    def grab(key):
        m = re.search(r"\n  " + key + r" := (-?\d+)\n", src)
        return int(m.group(1))

    def grab_list(key):
        i = src.index("\n  " + key + " := [") + len("\n  " + key + " := ")
        depth, j = 0, i
        while True:
            ch = src[j]
            if ch == "[":
                depth += 1
            elif ch == "]":
                depth -= 1
                if depth == 0:
                    break
            j += 1
        txt = src[i:j + 1]
        txt = re.sub(r"some (\d+)", r"\1", txt).replace("none", "None")
        return eval(txt, {"__builtins__": {}}, {"None": None})

    return dict(sLo=grab("sLo"), nA=grab("nA"), D=grab("D"), M=grab("M"),
                trans=grab_list("trans"), rank=grab_list("rank"))


def det_cycles(trans, rank, sLo):
    """non-trivial SCCs (equal rank = same SCC); each must be a simple cycle."""
    n = len(trans)
    comps = {}
    for i in range(n):
        comps.setdefault(rank[i], []).append(i)
    out = []
    for c, nodes in comps.items():
        internal = {i: [(t, j) for t, j in enumerate(trans[i]) if j is not None and rank[j] == c]
                    for i in nodes}
        if not any(internal.values()):
            continue
        assert all(len(v) == 1 for v in internal.values()), "SCC is not a simple cycle"
        start = nodes[0]
        word, i = [], start
        while True:
            t, j = internal[i][0]
            word.append(sLo + t)
            i = j
            if i == start:
                break
        assert len(word) == len(nodes)
        out.append(word)
    return out


# ---------------------------------------------------------------- census

class Census:
    def __init__(self, p, q, a, b, P, pmax=PMAX, node_cap=20_000_000):
        self.p, self.q, self.a, self.b = p, q, a, b
        self.PM = [l for l in P if q % l != 0]
        self.Pq = [l for l in P if q % l == 0]
        M = 1
        for l in self.PM:
            M *= l
        self.M = M
        self.qinv = pow(q, -1, M) if M > 1 else 0
        nu = Fraction(a, b)
        self.c = (p - q) * nu
        lo = -q - self.c
        hi = p - self.c
        import math
        self.alph = [s for s in range(math.floor(lo) + 1, math.ceil(hi))
                     if all(s % l for l in self.Pq)]
        self.pmax, self.node_cap = pmax, node_cap
        self.nodes = 0
        self.found = {}

    def rnext(self, r, s):
        return ((self.p * r + s) * self.qinv) % self.M if self.M > 1 else 0

    def ok_r(self, r):
        return all(r % l for l in self.PM)

    def run(self):
        R = Fraction(self.p, self.q)
        for r0 in range(self.M):
            if not self.ok_r(r0):
                continue
            # stack: (r_k, alpha_k, beta_k, lo, hi, word)
            stack = [(r0, Fraction(1), Fraction(0), Fraction(0), Fraction(1), ())]
            while stack:
                r, al, be, lo, hi, w = stack.pop()
                self.nodes += 1
                if self.nodes > self.node_cap:
                    raise RuntimeError("node cap")
                k = len(w)
                if k >= 1:
                    ystar = be / (1 - al)
                    if lo <= ystar < hi:
                        self.record(w, ystar)
                if k == self.pmax:
                    continue
                for s in self.alph:
                    r2 = self.rnext(r, s)
                    if not self.ok_r(r2):
                        continue
                    al2 = al * R
                    be2 = (self.p * be - s - self.c) / self.q
                    # 0 <= al2 y0 + be2 < 1
                    lo2 = max(lo, -be2 / al2)
                    hi2 = min(hi, (1 - be2) / al2)
                    if lo2 < hi2:
                        stack.append((r2, al2, be2, lo2, hi2, w + (s,)))
        return self

    def classify(self, w):
        """why a det-cycle word w carries no periodic avoiding pseudo-orbit: the exact orbit of
        the fixed point of w either hits the excluded endpoint y = 1 ('boundary'), leaves
        [0,1) ('outside'), or is a y-cycle whose residues never close avoiding ('residue')."""
        w = tuple(w)
        P = len(w)
        R = Fraction(self.p, self.q)
        al, be = Fraction(1), Fraction(0)
        for s in w:
            al, be = al * R, (self.p * be - s - self.c) / self.q
        y = be / (1 - al)
        ys = []
        for s in w:
            ys.append(y)
            y = (self.p * y - s - self.c) / self.q
        if any(v == 1 for v in ys):
            return "boundary", [str(v) for v in ys]
        if any(v < 0 or v > 1 for v in ys):
            return "outside", [str(v) for v in ys]
        F = {r: self.one_pass(r, w) for r in range(self.M)}
        for r in range(self.M):
            x, k = r, 0
            while x is not None and k <= self.M:
                x, k = F[x], k + 1
            if x is not None:
                return "lifted?", [str(v) for v in ys]   # should not happen
        return "residue", [str(v) for v in ys]

    def one_pass(self, r, w):
        """residue after reading w from r, or None if some residue on the way is not avoiding."""
        if not self.ok_r(r):
            return None
        for s in w:
            r = self.rnext(r, s)
            if not self.ok_r(r):
                return None
        return r

    def record(self, w, ystar):
        """a y-cycle: primitive letter word w whose fixed point keeps every y_i in [0,1).
        Its residue lifts are the cycles of the one-pass residue map F on Z/M; a lift of
        length m is a periodic avoiding pseudo-orbit of period |w| m."""
        w = tuple(w)
        if prim_root(w) != w:
            return
        key = canon(w)
        if key in self.found:
            return
        P = len(w)
        den = self.b * (self.p ** P - self.q ** P)
        assert (ystar * den).denominator == 1, "cycle point denominator"
        i0 = next(i for i in range(P) if w[i:] + w[:i] == key)
        y = ystar
        for s in w[:i0]:
            y = (self.p * y - s - self.c) / self.q
        F = {r: self.one_pass(r, key) for r in range(self.M)}
        lifts, seen = [], set()
        for r in range(self.M):
            path, x = [], r
            while x is not None and x not in seen and x not in path:
                path.append(x)
                x = F[x]
            if x is not None and x in path:
                cyc = path[path.index(x):]
                lifts.append(dict(m=len(cyc), period=P * len(cyc), boundary=cyc))
            seen.update(path)
        self.found[key] = dict(P=P, word=list(key), y0=str(y), den=den, lifts=lifts)


# ---------------------------------------------------------------- driver

def frac(s):
    f = Fraction(s)
    return f.numerator, f.denominator


def cell_row(e, pmax):
    p, q, P = e["p"], e["q"], e["P"]
    a, b = frac(e["nu"])
    d = parse_data(os.path.join(HERE, "Atlas", e["name"], "Data.lean"))
    assert d["D"] == e["D"] and len(d["trans"]) == e["det"]
    cyc = det_cycles(d["trans"], d["rank"], d["sLo"])
    t0 = time.time()
    C = Census(p, q, a, b, P, pmax).run()
    ycyc = sorted(C.found.values(), key=lambda o: (o["P"], o["word"]))
    det_roots = [root_key(w) for w in cyc]
    orb_roots = [tuple(o["word"]) for o in ycyc if o["lifts"]]
    ghosts = [o for o in ycyc if not o["lifts"]]
    det_set, orb_set = set(det_roots), set(orb_roots)
    det_short = [w for w in cyc if len(prim_root(w)) <= pmax]
    sound = orb_set <= det_set                       # theorem direction
    realized = all(root_key(w) in orb_set for w in det_short)
    # C-3 at the level of y-cycles (= primitive letter roots up to rotation): set equality,
    # and the two ways a literal bijection fails -- several det cycles on one word
    # (det_dupes) and several residue lifts of one y-cycle (lifts)
    words_equal = det_set == orb_set
    det_dupes = len(det_roots) - len(det_set)
    n_orb = sum(len(o["lifts"]) for o in ycyc)
    lifts = n_orb - len(orb_set)
    bij = words_equal and det_dupes == 0 and lifts == 0 and len(det_short) == len(cyc)
    bal = [balance(w) for w in cyc]
    unreal = []
    for w in cyc:
        k = root_key(w)
        if k in orb_set:
            continue
        if len(k) > pmax:
            unreal.append(dict(word=list(k), why="longer than pmax"))
            continue
        why, ys = C.classify(k)
        unreal.append(dict(word=list(k), why=why, orbit=ys))
    rbal = [balance(k) for k in sorted(orb_set)]
    return dict(name=e["name"], p=p, q=q, nu=e["nu"], P=P, D=e["D"], J=e["J"],
                det=e["det"], alph=C.alph, M=C.M, pmax=pmax, nodes=C.nodes,
                secs=round(time.time() - t0, 2),
                det_cycles=[dict(len=len(w), word=w, root=list(root_key(w)),
                                 balanced_literal=bl[0], balanced_sturm=bl[1])
                            for w, bl in zip(cyc, bal)],
                ycycles=ycyc, n_det=len(cyc), n_orb=n_orb, n_ghost=len(ghosts),
                sound=sound, det_realized=realized, words_equal=words_equal,
                n_ycycles=len(orb_set), det_dupes=det_dupes, lifts=lifts, bijection=bij,
                det_longer_than_pmax=len(cyc) - len(det_short),
                unrealized=unreal,
                C8_literal=all(x[0] for x in bal), C8_sturm=all(x[1] for x in bal),
                C8_literal_realized=all(x[0] for x in rbal),
                C8_sturm_realized=all(x[1] for x in rbal),
                realized_words=[dict(word=list(k), balanced_literal=x[0], balanced_sturm=x[1])
                                for k, x in zip(sorted(orb_set), rbal)])


def ladder(e, census_roots, dmax, pmax):
    p, q, P = e["p"], e["q"], e["P"]
    a, b = frac(e["nu"])
    C = Census(p, q, a, b, P, pmax)
    cset = set(census_roots)
    rows = []
    for D in range(1, dmax + 1):
        m = LeanModel(p, q, a, b, P, D)
        if m.nV > 4000:
            rows.append(dict(D=D, skipped="nV"))
            continue
        cert = m.certificate(limit=20000)
        if cert is None:
            rows.append(dict(D=D, ok=False, err="det too large"))
            continue
        cyc = det_cycles([[j for j in row] for row in cert["trans"]], cert["rank"], m.sLo) \
            if cert["ok"] else []
        roots = sorted(set(root_key(w) for w in cyc))
        art = [r for r in roots if r not in cset and len(r) <= pmax
               and C.classify(r)[0] in ("boundary", "outside")]
        rows.append(dict(D=D, ok=cert["ok"], J=cert["J"], det=len(cert["sets"]),
                         n_cycles=len(cyc),
                         exact=cert["ok"] and set(roots) == cset and len(cyc) == len(roots),
                         exact_mod_artefacts=cert["ok"] and set(roots) - set(art) == cset,
                         artefacts=[list(r) for r in art],
                         cycles=[list(r) for r in roots] if cert["ok"] else None))
    return rows


def main():
    ap = argparse.ArgumentParser()
    ap.add_argument("--pmax", type=int, default=PMAX)
    ap.add_argument("--only", default=None)
    ap.add_argument("--ladder", type=int, default=0, help="D_max for the alpha3 ladder")
    ap.add_argument("--out", default=os.path.join(HERE, "data", "transform"))
    ap.add_argument("--tag", default="", help="suffix for the output file names")
    args = ap.parse_args()
    reg = json.load(open(os.path.join(HERE, "Atlas", "registry.json")))
    if args.only:
        reg = [e for e in reg if e["name"] in args.only.split(",")]
    os.makedirs(args.out, exist_ok=True)
    rows = []
    with open(os.path.join(args.out, f"xc_census{args.tag}.jsonl"), "w") as f:
        for e in reg:
            row = cell_row(e, args.pmax)
            rows.append(row)
            f.write(json.dumps(row) + "\n")
            f.flush()
            print(f"{row['name']:24s} det_cycles={row['n_det']:3d} orbits={row['n_orb']:3d} "
                  f"ycyc={row['n_ycycles']:3d} ghost={row['n_ghost']} sound={row['sound']} realized={row['det_realized']} "
                  f"dupes={row['det_dupes']} lifts={row['lifts']} bij={row['bijection']} "
                  f"unreal={[u['why'] for u in row['unrealized']]} "
                  f"C8(realized) lit={row['C8_literal_realized']} st={row['C8_sturm_realized']} nodes={row['nodes']} "
                  f"{row['secs']}s", flush=True)
    if args.ladder:
        with open(os.path.join(args.out, f"xc_ladder{args.tag}.jsonl"), "w") as f:
            for row in rows:
                if row["name"] not in HAND:
                    continue
                e = next(x for x in reg if x["name"] == row["name"])
                cr = sorted(tuple(o["word"]) for o in row["ycycles"] if o["lifts"])
                lad = ladder(e, cr, args.ladder, args.pmax)
                okD = [r["D"] for r in lad if r.get("ok")]
                exD = [r["D"] for r in lad if r.get("exact")]
                exA = [r["D"] for r in lad if r.get("exact_mod_artefacts")]
                summ = dict(name=row["name"], registry_D=e["D"],
                            min_D_certified=min(okD, default=None),
                            min_D_exact=min(exD, default=None),
                            min_D_exact_mod_artefacts=min(exA, default=None),
                            certified_Ds=okD, ladder=lad)
                f.write(json.dumps(summ) + "\n")
                f.flush()
                print(f"ladder {row['name']:24s} registry D={e['D']} min certified D="
                      f"{summ['min_D_certified']} min exact D={summ['min_D_exact']} "
                      f"(mod artefacts {summ['min_D_exact_mod_artefacts']})", flush=True)


if __name__ == "__main__":
    main()
