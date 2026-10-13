#!/usr/bin/env python3
# (C) 2026 Ralf Stephan, in collaboration with Claude Code.  CC0 1.0.
#
# certdb.py -- plan-dubC2-transform, experiment X-DB (target T7, lane delta).
#
# (1) DATABASE (plan sec. 7.1).  One table set under DubC2/data/transform/db/ (CSV per table plus
#     certdb.sqlite), regenerated from the sources below and never hand-edited:
#       Atlas/registry.json, Atlas/<cell>/Data.lean       the 16 kernel-checked certificates
#       atlas_out/atlas2.jsonl, atlas_out/shard*.jsonl     the scan: minimal P per (p/q, nu), refusals
#       atlas_out/obstruction.jsonl                        [Oda26] Thm 42 kills (ObstructionAtlas.lean)
#       data/transform/xs_num1.jsonl                       X-S: fixed P along the nu = -1 column
#       data/transform/xrf_*.jsonl                         residue-free nu-sweeps (xresfree.py)
#       data/transform/xc_census{,_p24}.jsonl, xc_ladder   X-C: det cycles, y-cycles, alpha3 ladder
#       HAND (below)                                       the hand chains' Lean files and grids
#     Tables: rows, verdicts, cells, cell_primes, cycles, ycycle_counts, thm42, nu_sweep.
#
# (2) MINER.  HR-style production rules over the tables (split, match, negate, exists, compose):
#       R1 containment   every minimal certified P of a split contains / avoids the prime l
#       R2 emptiness     no hit (or only hits) on a split of the 63+2 scan rows
#       R3 comparison    hit at nu1 => hit at nu2, |P_min(nu1)| <= |P_min(nu2)| on common bases
#       R4 kills         a small set S is killed by Thm 42 on every row of a split
#       R5 dependency    one discrete cell column determines another
#       R6 inequality    col_a <= col_b on every cell
#       R7 symmetry      a residue-free nu-sweep is invariant under nu -> c - nu
#     Each conjecture carries its support n and a surprise score  -log10 Pr[pattern | null], the
#     null being independent draws at the observed base rate (R1/R2/R4/R7) or a uniformly random
#     pairing of the columns (R3/R5/R6); score/complexity ranks the shortlist (plan L9, R-9).
#     Rules whose pattern is already a theorem of the corpus are tagged KNOWN, not dropped.
#
# (3) OEIS PASS.  Integer columns (y-cycle counts by period, det/core/J ladders) are looked up at
#     oeis.org; responses are cached in db/oeis_cache.json so a rerun is offline and byte-equal.
#
# Usage: certdb.py [--no-oeis] [--top 25]

import argparse
import csv
import glob
import itertools
import json
import math
import os
import sqlite3
import sys
import time
import urllib.parse
import urllib.request
from collections import Counter, defaultdict
from fractions import Fraction
from math import gcd

HERE = os.path.dirname(os.path.abspath(__file__))
sys.path.insert(0, HERE)
from xcensus import parse_data, det_cycles, root_key, balance  # noqa: E402
from gencert import tarjan  # noqa: E402

OUT = os.path.join(HERE, "data", "transform", "db")
SCAN_LADDER = "primes<=13, |P|<=4, D=p*b*2^j (j<=6), nV<=20000, det<=1500"
PRIMES = [2, 3, 5, 7, 11, 13]

# hand chains: Lean file, the exact grid D the hand proof works on (alpha3), block statement
HAND = {
    "b3_2_nu1_2_P2_5": ("Nearest.lean/NearestStep.lean", 216),
    "b5_3_nu1_2_P2_3": ("Calibration53.lean", 27),
    "b7_5_nu1_2_P2_3_5_11": ("SevenFifthsCore.lean", 2401),
    "b3_2_nu0_P2_5_7_11": ("FloorCore.lean", None),
}
# cells whose eventual-word statement is a Lean theorem (hand chains + GenBlocks/Blocks.lean)
WORDS_IN_LEAN = set(HAND) | {"b7_5_nu1_2_P2_3_5_13", "b3_2_nu0_P2_7_11_13",
                             "b3_2_nu0_P3_5_7_11"}


def fr(s):
    return Fraction(s)


# ------------------------------------------------------------------ prime roles (plan L20)

def window(p, q, nu):
    c = (p - q) * nu
    return list(range(math.floor(-q - c) + 1, math.ceil(p - c)))


def residue_sccs(p, q, l, L):
    """nontrivial SCCs of r -> q^{-1}(p r + s) mod l on (Z/l)^*, letters L; with internal labels."""
    qi = pow(q, -1, l)
    V = list(range(1, l))
    E = {r: [(s, (p * r + s) * qi % l) for s in L if (p * r + s) * qi % l] for r in V}
    adj = [[t - 1 for _, t in E[r]] for r in V]
    comp, _ = tarjan(len(V), adj)
    groups = defaultdict(list)
    for i, c in enumerate(comp):
        groups[c].append(i + 1)
    out = []
    for vs in groups.values():
        S = set(vs)
        lab = sorted({s for r in vs for s, t in E[r] if t in S})
        if lab:
            out.append((sorted(vs), lab))
    return sorted(out)


def longrun(p, q, l, L):
    return sorted({s for _, lab in residue_sccs(p, q, l, L) for s in lab})


def alphabet_fix(p, q, R, L):
    L = list(L)
    while True:
        L2 = L
        for l in R:
            L2 = [s for s in L2 if s in set(longrun(p, q, l, L2))]
        if L2 == L:
            return L
        L = L2


def prime_roles(p, q, nu, P):
    """alphabet(pq): l | pq (residue-free, ShiftSchema.eventually_avoids_iff);
    alphabet(res): l of PM whose residue graph alone shrinks the long-run letter set left by
    the other primes; orientation: l whose residue graph on the final letters has >= 2
    nontrivial SCCs with different letter sets (an orbit invariant selecting letters);
    invariant: >= 2 SCCs with equal letter sets; word: none of these (kills words only)."""
    pq = [l for l in P if (p * q) % l == 0]
    R = [l for l in P if (p * q) % l]
    L0 = [s for s in window(p, q, nu) if all(s % l for l in pq)]
    Lf = alphabet_fix(p, q, R, L0)
    roles = {}
    for l in pq:
        roles[l] = dict(role="alphabet(pq)", detail="divides " + ("q" if q % l == 0 else "p"))
    for l in R:
        Lm = alphabet_fix(p, q, [k for k in R if k != l], L0)
        shrinks = set(longrun(p, q, l, Lm)) < set(Lm)
        sc = residue_sccs(p, q, l, Lf)
        labs = [tuple(lab) for _, lab in sc]
        if len(sc) >= 2 and len(set(labs)) >= 2:
            r = "orientation"
        elif len(sc) >= 2:
            r = "invariant"
        else:
            r = "word"
        if shrinks:
            r = "alphabet(res)" + ("" if r == "word" else "+" + r)
        roles[l] = dict(role=r, detail=json.dumps([[vs, lab] for vs, lab in sc]))
    return L0, Lf, roles


# ------------------------------------------------------------------ build

def load_jsonl(path):
    return [json.loads(l) for l in open(path)] if os.path.exists(path) else []


def build():
    reg = json.load(open(os.path.join(HERE, "Atlas", "registry.json")))
    cen = {r["name"]: r for r in load_jsonl(os.path.join(HERE, "data/transform/xc_census.jsonl"))}
    for r in load_jsonl(os.path.join(HERE, "data/transform/xc_census_p24.jsonl")):
        cen[r["name"]] = r                                    # longer census where it exists
    lad = {r["name"]: r for r in load_jsonl(os.path.join(HERE, "data/transform/xc_ladder.jsonl"))}
    for r in load_jsonl(os.path.join(HERE, "data/transform/xc_ladder_p24.jsonl")):
        lad[r["name"]] = r
    scan = load_jsonl(os.path.join(HERE, "atlas_out/atlas2.jsonl"))
    shard = []
    for f in sorted(glob.glob(os.path.join(HERE, "atlas_out/shard*.jsonl"))):
        shard += load_jsonl(f)
    scanned = {(r["p"], r["q"], r["nu"]) for r in scan}
    obs = {(r["p"], r["q"], r["nu"]): r
           for r in load_jsonl(os.path.join(HERE, "atlas_out/obstruction.jsonl"))}
    xs = load_jsonl(os.path.join(HERE, "data/transform/xs_num1.jsonl"))
    T = defaultdict(list)

    # rows: one per scanned (p/q, nu)
    for src, rows in (("atlas2", scan), ("shard", shard)):
        for r in rows:
            p, q, nu = r["p"], r["q"], r["nu"]
            mins = [m["P"] for m in r["minimal"]]
            dup = src != "atlas2" and (p, q, nu) in scanned       # Thm 42 data once per row
            o = None if dup else obs.get((p, q, nu))
            kmax = []
            if o:
                ks = [tuple(k[0]) for k in o["killed"]]
                kmax = [list(k) for k in ks if not any(set(k) < set(j) for j in ks)]
            T["rows"].append(dict(
                p=p, q=q, nu=nu, ratio=round(p / q, 6), pmq=p - q, source=src,
                ladder=SCAN_LADDER if src == "atlas2" else "primes<=13, |P|<=4, budget (truncated)",
                truncated=bool(r.get("truncated")), hit=bool(mins), n_min=len(mins),
                min_size=min((len(m) for m in mins), default=None),
                min_sets=json.dumps(mins), thm42_n=o["nkilled"] if o else None,
                thm42_maximal=json.dumps(kmax) if o else None,
                alive_n=o["nalive"] if o else None))
            for m in r["minimal"]:
                T["verdicts"].append(dict(p=p, q=q, nu=nu, Pset=json.dumps(m["P"]), size=len(m["P"]),
                                          verdict="CERT", D=m["D"], core=m["core"], det=m["det"],
                                          nV=m.get("nV", m.get("total")), minimal=1, source=src))
            if o:
                for k in o["killed"]:
                    T["thm42"].append(dict(p=p, q=q, nu=nu, Pset=json.dumps(k[0]), size=len(k[0]),
                                           s0=k[1], c=k[2], residues=json.dumps(k[3])))
    for r in xs:
        c = r["cert"]
        T["verdicts"].append(dict(p=r["p"], q=r["q"], nu=r["nu"], Pset=json.dumps(r["P"]),
                                  size=len(r["P"]), verdict="CERT" if c else "NONE",
                                  D=c["D"] if c else r["Dlast"], core=c and c["core"],
                                  det=c and c["det"], nV=c and c["nV"], minimal=None,
                                  source="xs_num1"))
    for f in sorted(glob.glob(os.path.join(HERE, "data/transform/xrf_*.jsonl"))):
        for r in load_jsonl(f):
            T["nu_sweep"].append(dict(p=r["p"], q=r["q"], Pset=json.dumps(r["P"]), nu=r["nu"],
                                      letters=json.dumps(r["letters"]), cert_D=r["cert"],
                                      words=r["words"], wlen=r["wlen"], ratio=r["ratio"]))

    # cells: the 16 certificates
    for e in reg:
        name, p, q, P = e["name"], e["p"], e["q"], e["P"]
        nu = fr(e["nu"])
        d = parse_data(os.path.join(HERE, "Atlas", name, "Data.lean"))
        cyc = det_cycles(d["trans"], d["rank"], d["sLo"])
        c = cen[name]
        L0, Lf, roles = prime_roles(p, q, nu, P)
        for l, rr in sorted(roles.items()):
            T["cell_primes"].append(dict(cell=name, prime=l, role=rr["role"], sccs=rr["detail"]))
        realized = {tuple(w["word"]) for w in c["realized_words"]}
        unreal = {tuple(u["word"]): u for u in c["unrealized"]}
        yinfo = {tuple(o["word"]): o for o in c["ycycles"]}
        for w in cyc:
            k = root_key(w)
            o = yinfo.get(k)
            bl, bs = balance(k)
            den = fr(e["nu"]).denominator * (p ** len(k) - q ** len(k))
            T["cycles"].append(dict(
                cell=name, word=json.dumps(list(k)), period=len(k), det_len=len(w),
                realized=int(k in realized), why=unreal[k]["why"] if k in unreal else "",
                y0=o["y0"] if o else "", den_bound=den,
                den_divides=int(o is not None and den % fr(o["y0"]).denominator == 0),
                n_lifts=len(o["lifts"]) if o else 0,
                lift_periods=json.dumps([x["period"] for x in o["lifts"]]) if o else "[]",
                n_minus=sum(1 for s in k if s < 0), balanced_literal=int(bl),
                balanced_sturm=int(bs)))
        per = Counter(o["P"] for o in c["ycycles"])
        perl = Counter(o["P"] for o in c["ycycles"] if o["lifts"])
        for n in range(1, c["pmax"] + 1):
            T["ycycle_counts"].append(dict(cell=name, period=n, ycycles=per.get(n, 0),
                                           lifted=perl.get(n, 0)))
        roles_s = sorted(rr["role"] for rr in roles.values())
        lr = lad.get(name)
        rp = [len(w) for w in realized]
        T["cells"].append(dict(
            name=name, p=p, q=q, nu=e["nu"], pmq=p - q, Pset=json.dumps(P), size=len(P),
            D=e["D"], core=e["core"], det=e["det"], J=e["J"], parts=e["parts"],
            M=c["M"], res_free=int(all((p * q) % l == 0 for l in P)),
            Pq=json.dumps([l for l in P if q % l == 0]), Pp=json.dumps([l for l in P if p % l == 0]),
            PM=json.dumps([l for l in P if (p * q) % l]),
            window=len(window(p, q, nu)), letters_pq=json.dumps(L0), letters=json.dumps(Lf),
            n_letters=len(Lf),
            n_alphabet=sum(r.startswith("alphabet") for r in roles_s),
            n_orientation=sum("orientation" in r for r in roles_s),
            n_word=sum(r == "word" for r in roles_s),
            n_invariant=sum("invariant" in r for r in roles_s),
            roles=json.dumps({str(l): rr["role"] for l, rr in sorted(roles.items())}),
            n_det_cycles=len(cyc), n_det_roots=len({root_key(w) for w in cyc}),
            n_realized=len(realized), n_artefacts=len(unreal),
            artefact_kinds=json.dumps(sorted(Counter(u["why"] for u in unreal.values()).items())),
            det_dupes=c["det_dupes"], lifts=c["lifts"], bijection=int(c["bijection"]),
            min_period=min(rp, default=None), max_period=max(rp, default=None),
            periods=json.dumps(sorted(rp)), census_pmax=c["pmax"],
            n_ycycles_census=len(c["ycycles"]), n_ghost=c["n_ghost"],
            lambda_det=1 if cyc else 0,          # checked => SCCs are simple cycles
            minD=lr["min_D_certified"] if lr else None,
            minD_exact=lr["min_D_exact_mod_artefacts"] if lr else None,
            hand=int(name in HAND), hand_file=HAND[name][0] if name in HAND else "",
            hand_grid_D=HAND[name][1] if name in HAND else None,
            words_in_lean=int(name in WORDS_IN_LEAN), title=e["title"]))
    return T


# ------------------------------------------------------------------ miner

def lg(x):
    return -math.log10(x) if x > 0 else 99.0


def conj(T, rule, text, n, score, cx=1, known="", data=None):
    return dict(rule=rule, conjecture=text, support=n, surprise=round(score, 2),
                complexity=cx, rank_score=round(score / cx, 2), known=known,
                data=json.dumps(data) if data is not None else "")


def row_preds():
    P = {
        "nu=0": lambda r: r["nu"] == "0", "nu=1/2": lambda r: r["nu"] == "1/2",
        "nu=-1": lambda r: r["nu"] == "-1",
        "p-q=1": lambda r: r["pmq"] == 1, "p-q>=2": lambda r: r["pmq"] >= 2,
        "p-q>=3": lambda r: r["pmq"] >= 3,
        "q=2": lambda r: r["q"] == 2, "q>=3": lambda r: r["q"] >= 3,
        "p/q<2": lambda r: r["ratio"] < 2, "p/q>2": lambda r: r["ratio"] > 2,
        "p odd": lambda r: r["p"] % 2 == 1, "p even": lambda r: r["p"] % 2 == 0,
        "q odd": lambda r: r["q"] % 2 == 1, "q even": lambda r: r["q"] % 2 == 0,
        "p-q odd": lambda r: r["pmq"] % 2 == 1, "p-q even": lambda r: r["pmq"] % 2 == 0,
        "p<=7": lambda r: r["p"] <= 7, "p>=8": lambda r: r["p"] >= 8,
    }
    return P


def mine(T):
    C = []
    rows = [r for r in T["rows"] if r["source"] == "atlas2"]
    allrows = T["rows"]
    preds = row_preds()

    # R1 containment over minimal certified sets (atlas2 + shards: minimality is meaningful there)
    mins = [(r, m) for r in allrows for m in json.loads(r["min_sets"])]
    freq = {l: sum(l in m for _, m in mins) / len(mins) for l in PRIMES}
    splits = {"all": lambda r: True, **{k: preds[k] for k in ("nu=0", "nu=1/2", "nu=-1")}}
    splits["nu not in Z"] = lambda r: fr(r["nu"]).denominator > 1
    for sname, sp in splits.items():
        S = [(r, m) for r, m in mins if sp(r)]
        nrows = len({(r["p"], r["q"], r["nu"]) for r, _ in S})
        if nrows < 3:
            continue
        for l in PRIMES:
            if all(l in m for _, m in S):
                C.append(conj(T, "R1", f"[{sname}] every minimal certified P contains {l}",
                              nrows, nrows * lg(freq[l]), 1,
                              data=[[r["p"], r["q"], r["nu"], m] for r, m in S]))
            elif not any(l in m for _, m in S) and freq[l] > 0:
                C.append(conj(T, "R1", f"[{sname}] no minimal certified P contains {l}",
                              nrows, nrows * lg(1 - freq[l]), 1))

    # R2 emptiness / fullness on predicate splits (<= 2 predicates); a split contained in a
    # larger split with the same verdict is subsumed and dropped (HR subsumption)
    h = sum(r["hit"] for r in rows) / len(rows)
    cand = {}
    for k in (1, 2):
        for names in itertools.combinations(sorted(preds), k):
            S = [r for r in rows if all(preds[n](r) for n in names)]
            key = frozenset((r["p"], r["q"], r["nu"]) for r in S)
            if len(S) < 4 or key in cand:
                continue
            nh = sum(r["hit"] for r in S)
            if nh in (0, len(S)):
                cand[key] = (names, nh == 0, S)
    for key, (names, empty, S) in cand.items():
        if any(key < k2 and v2[1] == empty for k2, v2 in cand.items()):
            continue
        if empty:
            C.append(conj(T, "R2", f"[{' & '.join(names)}] no divisor set certifies (scan ladder)",
                          len(S), len(S) * lg(1 - h), len(names),
                          data=sorted([r["p"], r["q"], r["nu"]] for r in S)))
        else:
            C.append(conj(T, "R2", f"[{' & '.join(names)}] some divisor set certifies",
                          len(S), len(S) * lg(h), len(names),
                          data=sorted([r["p"], r["q"], r["nu"]] for r in S)))

    # R3 comparison across shifts on common bases
    by = defaultdict(dict)
    for r in rows:
        by[(r["p"], r["q"])][r["nu"]] = r
    for a, b in itertools.permutations(["0", "1/2", "-1"], 2):
        pairs = [(v[a], v[b]) for v in by.values() if a in v and b in v]
        ha = [x for x, y in pairs if x["hit"]]
        if len(ha) >= 3 and all(y["hit"] for x, y in pairs if x["hit"]):
            pb = sum(y["hit"] for _, y in pairs) / len(pairs)
            C.append(conj(T, "R3", f"hit at nu={a} => hit at nu={b} (same base)", len(ha),
                          len(ha) * lg(pb), 2,
                          data=[[x["p"], x["q"]] for x in ha]))
        both = [(x, y) for x, y in pairs if x["hit"] and y["hit"]]
        if len(both) >= 2 and all(x["min_size"] <= y["min_size"] for x, y in both):
            strict = sum(x["min_size"] < y["min_size"] for x, y in both)
            C.append(conj(T, "R3", f"|P_min(nu={a})| <= |P_min(nu={b})| where both certify",
                          len(both), len(both) * lg(0.5), 2,
                          known="C-2 form" if (a, b) == ("1/2", "0") else "",
                          data=[[x["p"], x["q"], x["min_size"], y["min_size"]] for x, y in both]))

    # R4 Thm 42 kills on every row of a split
    kills = defaultdict(set)
    for k in T["thm42"]:
        kills[(k["p"], k["q"], k["nu"])].add(k["Pset"])
    obsrows = [r for r in rows if r["thm42_n"] is not None]
    allS = Counter(s for v in kills.values() for s in v)
    for sname in ("all", "nu=0", "nu=1/2", "nu=-1"):
        sp = splits[sname]
        S = [r for r in obsrows if sp(r)]
        for s, cnt in allS.items():
            if len(json.loads(s)) > 2:
                continue
            base = cnt / len(obsrows)
            if all(s in kills[(r["p"], r["q"], r["nu"])] for r in S) and len(S) >= 4:
                C.append(conj(T, "R4", f"[{sname}] Thm 42 kills P={json.loads(s)} on every row",
                              len(S), len(S) * lg(base), len(json.loads(s)),
                              data=[[r["p"], r["q"]] for r in S]))
        # rows with no kill at all
        z = [r for r in S if r["thm42_n"] == 0]
        if sname != "all" and z and len(z) == len(S):
            C.append(conj(T, "R4", f"[{sname}] Thm 42 kills nothing", len(S), 1.0, 1))
    zero = {(r["p"], r["q"], r["nu"]) for r in obsrows if r["thm42_n"] == 0}
    if zero:
        for k in (1, 2):
            for names in itertools.combinations(sorted(preds), k):
                S = {(r["p"], r["q"], r["nu"]) for r in obsrows if all(preds[n](r) for n in names)}
                if S == zero:
                    C.append(conj(T, "R4", f"Thm 42 kills nothing  <=>  {' & '.join(names)}",
                                  len(obsrows), len(zero) * lg(len(zero) / len(obsrows)), k,
                                  known="witness shape: x* = s0/(p-q) + nu in [0,1] forces s0 = 0",
                                  data=sorted(zero)))
                    break
            else:
                continue
            break

    # R5 functional dependencies among discrete cell columns
    cells = T["cells"]
    disc = ["nu", "pmq", "q", "size", "res_free", "n_letters", "n_alphabet", "n_orientation",
            "n_word", "n_invariant", "n_realized", "n_artefacts", "min_period", "lifts", "det_dupes",
            "bijection", "hand", "J"]
    for a, b in itertools.permutations(disc, 2):
        va = [c[a] for c in cells]
        vb = [c[b] for c in cells]
        if len(set(vb)) < 2 or len(set(va)) >= len(cells) - 2 or len(set(va)) < 2:
            continue
        f = {}
        if all(f.setdefault(x, y) == y for x, y in zip(va, vb)):
            # chance that a random pairing is a function: product over classes
            groups = Counter(va)
            cnt = Counter(vb)
            pr = 1.0
            for g, m in groups.items():
                pr *= max(sum((k / len(cells)) ** m for k in cnt.values()), 1e-12)
            if len(set(va)) == len(cells):
                continue
            C.append(conj(T, "R5", f"cells: {a} determines {b}", len(cells), lg(pr), 2,
                          data=sorted({str(x): y for x, y in zip(va, vb)}.items())))

    # R6 inequalities among numeric cell columns (same-kind columns only: graph sizes, word
    # data, alphabet data; cross-kind comparisons like n_letters <= D are scale artefacts)
    num = ["size", "n_letters", "n_realized", "n_det_cycles", "min_period", "max_period", "J",
           "det", "core", "M"]
    trivial = {("min_period", "max_period"), ("n_realized", "n_det_cycles"),
               ("n_det_cycles", "det"), ("max_period", "det"), ("min_period", "det"),
               ("J", "det"), ("J", "core")}
    for a, b in itertools.permutations(num, 2):
        pts = [(c[a], c[b]) for c in cells if c[a] is not None and c[b] is not None]
        if len(pts) < 8 or not all(x <= y for x, y in pts):
            continue
        eq = sum(x == y for x, y in pts)
        if eq == len(pts):
            continue
        # null: a uniformly random pairing of the two columns respects the order; count the
        # admissible pairings greedily from the largest x down
        xs = sorted((x for x, _ in pts), reverse=True)
        ys = [y for _, y in pts]
        pr = 1.0
        for i, x in enumerate(xs):
            pr *= max(sum(1 for y in ys if y >= x) - i, 0) / (len(ys) - i)
        if pr >= 0.05:
            continue
        kn = "trivial / theorem" if (a, b) in trivial else ""
        C.append(conj(T, "R6", f"cells: {a} <= {b} (equality {eq}/{len(pts)})", len(pts),
                      lg(pr), 2, known=kn))

    # R7 mirror symmetry of residue-free nu-sweeps
    sw = defaultdict(dict)
    for r in T["nu_sweep"]:
        sw[(r["p"], r["q"], r["Pset"])][fr(r["nu"])] = r["cert_D"] is not None
    for (p, q, Ps), V in sorted(sw.items()):
        P = json.loads(Ps)
        per = math.prod(P)
        nus = sorted(V)
        rate = sum(V.values()) / len(V)
        best = None
        for cc in sorted({(a + b) for a in nus for b in nus}):
            matched = [(v, (cc - v) % per) for v in nus if (cc - v) % per in V]
            if len(matched) < len(nus) * 0.9:
                continue
            ncert = sum(V[v] for v, _ in matched)
            if all(V[v] == V[w] for v, w in matched) and 3 <= ncert <= len(matched) - 3:
                best = (cc % per, len(matched), ncert)
                break
        if best:
            cc, nm, ncert = best
            pr = (rate ** 2 + (1 - rate) ** 2) ** (nm / 2)
            C.append(conj(T, "R7", f"{p}/{q}, P={P}: certified nu-set invariant under nu -> {cc} - nu "
                          f"(mod {per}); {ncert}/{nm} grid points certified",
                          nm, lg(pr), 2, data=[str(cc)]))
    # tags: patterns that are theorems already
    for c in C:
        t = c["conjecture"]
        if "Thm 42 kills P=[2] on every row" in t and ("nu=0" in t or "nu=-1" in t):
            c["known"] = "theorem: Gen.not_checked_two_of_int (ObstructionTwo.lean)"
        if "Thm 42 kills P=[3] on every row" in t and ("nu=0" in t or "nu=-1" in t):
            c["known"] = "theorem: Gen.not_checked_three_of_int (ObstructionTwo.lean)"
        if "invariant under nu" in t:
            c["known"] = c["known"] or "theorem: Mirror.frequently_mirror_iff (Mirror.lean), xi -> -xi"
        if "n_realized <= n_det_cycles" in t:
            c["known"] = "theorem (soundness + X-C)"
    C.sort(key=lambda c: (-c["rank_score"], -c["support"], c["conjecture"]))
    return C


# ------------------------------------------------------------------ OEIS

def oeis_candidates(T):
    seqs = []
    by = defaultdict(list)
    for r in T["ycycle_counts"]:
        by[r["cell"]].append(r)
    for cell, rs in by.items():
        rs.sort(key=lambda r: r["period"])
        for col in ("ycycles", "lifted"):
            s = [r[col] for r in rs]
            while s and s[0] == 0:
                s = s[1:]
            if len([x for x in s if x]) >= 6 and len(set(s)) >= 3:
                seqs.append((f"{cell}:{col}", s))
    for col in ("det", "core", "J", "D"):
        s = sorted({c[col] for c in T["cells"]})
        if len(s) >= 6:
            seqs.append((f"cells:{col} (sorted distinct)", s))
    return seqs


def oeis(seqs, cache_path, online):
    cache = json.load(open(cache_path)) if os.path.exists(cache_path) else {}
    out = []
    for tag, s in seqs:
        key = ",".join(map(str, s))
        if (key not in cache or isinstance(cache[key], dict)) and online:
            url = "https://oeis.org/search?fmt=json&q=" + urllib.parse.quote(key)
            try:
                req = urllib.request.Request(url, headers={"User-Agent": "curl/8.0"})
                with urllib.request.urlopen(req, timeout=20) as f:
                    js = json.loads(f.read().decode() or "null")
                hits = js if isinstance(js, list) else (js or {}).get("results") or []
                cache[key] = [dict(A="A%06d" % h["number"], name=h["name"][:120]) for h in hits[:5]]
            except Exception as ex:                                  # noqa: BLE001
                cache[key] = dict(error=str(ex))
            time.sleep(1.0)
        res = cache.get(key)
        out.append(dict(tag=tag, seq=key, n_terms=len(s),
                        hits=json.dumps(res) if res is not None else "not queried"))
    json.dump(cache, open(cache_path, "w"), indent=1, sort_keys=True)
    return out


# ------------------------------------------------------------------ output

def write(T, C, O):
    os.makedirs(OUT, exist_ok=True)
    dbp = os.path.join(OUT, "certdb.sqlite")
    if os.path.exists(dbp):
        open(dbp, "w").close()                       # truncate (no rm in this environment)
    con = sqlite3.connect(dbp)
    tables = dict(T)
    tables["conjectures"] = C
    tables["oeis"] = O
    for name, rows in tables.items():
        if not rows:
            continue
        cols = list(rows[0].keys())
        con.execute(f"DROP TABLE IF EXISTS {name}")
        con.execute(f"CREATE TABLE {name} ({', '.join(cols)})")
        con.executemany(f"INSERT INTO {name} VALUES ({', '.join('?' * len(cols))})",
                        [[r[c] for c in cols] for r in rows])
        with open(os.path.join(OUT, f"{name}.csv"), "w", newline="") as f:
            w = csv.DictWriter(f, fieldnames=cols, lineterminator="\n")
            w.writeheader()
            w.writerows(rows)
    con.commit()
    con.close()


def main():
    ap = argparse.ArgumentParser()
    ap.add_argument("--no-oeis", action="store_true")
    ap.add_argument("--top", type=int, default=25)
    args = ap.parse_args()
    T = build()
    C = mine(T)
    O = oeis(oeis_candidates(T), os.path.join(OUT, "oeis_cache.json"), not args.no_oeis) \
        if os.path.isdir(OUT) or os.makedirs(OUT) is None else []
    write(T, C, O)
    with open(os.path.join(OUT, "shortlist.txt"), "w") as f:
        f.write("# X-DB ranked shortlist (certdb.py); KNOWN/trivial patterns listed after\n")
        for c in [c for c in C if not c["known"]] + [c for c in C if c["known"]]:
            f.write(f"{c['rank_score']:6.2f}  {c['rule']}  n={c['support']:3d}  {c['conjecture']}"
                    + (f"  [KNOWN: {c['known']}]" if c["known"] else "") + "\n")
    for k, v in T.items():
        print(f"table {k:14s} {len(v):5d} rows")
    print(f"conjectures {len(C)}; top {args.top}:")
    for c in C[:args.top]:
        print(f"  {c['rank_score']:6.2f} {c['rule']} n={c['support']:3d} {c['conjecture']}"
              + (f"  [{c['known']}]" if c["known"] else ""))
    for o in O:
        print("oeis", o["tag"], o["seq"][:60], o["hits"][:200])


if __name__ == "__main__":
    main()
