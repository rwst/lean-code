#!/usr/bin/env python3
# (C) 2026 Ralf Stephan, in collaboration with Claude Code.  CC0 1.0.
#
# xhorse.py -- plan-dubC2-transform, experiment X-H (target T5(ii),(iii); seed C-5).
#
# Horseshoe search on the residue pseudo-orbit model of a cell (p/q, nu = a/b, P):
#   residues r_n mod M = prod(PM) avoiding PM, letters s_n avoiding Pq,
#   r_{n+1} = q^{-1}(p r_n + s_n) mod M,  y_n in [0,1),  q y_{n+1} = p y_n - s_n - (p-q) nu
# (DubC2.Gen.PseudoOrbit, DubC2/Obstruction.lean).  A HORSESHOE WITNESS is a residue r0, two
# letter words W1, W2 with W1 W2 != W2 W1, and a closed rational interval K in [0,1) such that
#   * reading Wi from r0 visits avoiding residues only and returns to r0, and
#   * the inverse composition h_Wi = h_{s_1} o ... o h_{s_L},  h_s(y) = (q y + s + (p-q) nu)/p,
#     maps K into K with every partial image h_{s_j} o ... o h_{s_L}(K) inside [0,1).
# Then every infinite concatenation of W1, W2 is the letter word of an avoiding pseudo-orbit
# (nested compact intervals), and the concatenations include aperiodic ones; a checked
# certificate makes every pseudo-orbit eventually periodic (PseudoOrbit.eventuallyPeriodic), so
# NO certificate exists for P, nor for any P' contained in P, at any D and M.
#
# Search: depth-first over letter words with the exact cylinder of y0 (as in xcensus.py) and,
# per prime l of PM, the affine residue map r -> A r + B (mod l) with the bitmask of start
# residues that stayed avoiding.  The conditions decouple over the primes (CRT), so a word Wi
# returns r0 iff r0 mod l lies in the fixed set S_l(Wi) for every l.  Every word of length
# <= LMAX with a fixed point y* = the periodic point of W in its cylinder is recorded; pairs
# with S_l(W1) & S_l(W2) != 0 for all l are tried with K = [min y*, max y*].
#
# G-4: each witness is rechecked by recheck() (independent code: exact forward simulation of
# random block concatenations, residues by brute-force division mod M); and on the certified
# atlas cells (and supersets of their sets) no witness may exist (--controls).
#
# Usage:
#   xhorse.py --controls                       # G-4(a): certified cells must yield no witness
#   xhorse.py --rows 6/5,7/6,5/4 --nu 1/2      # X-H on the N-2 rows, primes <= 17, downward
#   xhorse.py --extend --nodes 5000000         # 6/5, 7/6 beyond 17; the 5/4 survivors, L <= 24
#   xhorse.py --deep                           # the 5/4 sets still open, L <= 40
#   xhorse.py --emit DubC2/HorseshoeAtlas.lean # the maximal witnesses as Lean data
# A witness is accepted only if recheck() passes; engine_check() (G-4(c)) additionally walks it
# through gencert.LeanModel.succMask when M*D <= 6e6.
# Output: DubC2/data/transform/xh/xh_<tag>.jsonl

import argparse
import itertools
import json
import os
import random
import sys
import time
from fractions import Fraction

HERE = os.path.dirname(os.path.abspath(__file__))
OUT = os.path.join(HERE, "data", "transform", "xh")


def primes_upto(n):
    return [k for k in range(2, n + 1) if all(k % d for d in range(2, int(k ** 0.5) + 1))]


class Model:
    def __init__(self, p, q, nu, P):
        self.p, self.q, self.nu = p, q, Fraction(nu)
        self.P = sorted(P)
        self.PM = [l for l in self.P if q % l]
        self.Pq = [l for l in self.P if q % l == 0]
        self.c = (p - q) * self.nu
        lo, hi = -q - self.c, p - self.c          # s in (lo, hi) for some y in [0,1)
        import math
        self.alph = [s for s in range(math.floor(lo) + 1, math.ceil(hi))
                     if all(s % l for l in self.Pq)]
        self.qi = {l: pow(q, -1, l) for l in self.PM}
        self.full = {l: ((1 << l) - 1) & ~1 for l in self.PM}   # nonzero residues

    def step_masks(self, st, s):
        """per prime: (A, B, alive) -> after letter s."""
        out = []
        for (l, (A, B, alive)) in zip(self.PM, st):
            qi = self.qi[l]
            A2 = self.p * A * qi % l
            B2 = (self.p * B + s) * qi % l
            # kill the starts r with A2 r + B2 = 0
            m = alive
            for r in range(1, l):
                if (m >> r) & 1 and (A2 * r + B2) % l == 0:
                    m &= ~(1 << r)
            if not m:
                return None
            out.append((A2, B2, m))
        return tuple(out)

    def fixed_sets(self, st):
        S = []
        for (l, (A, B, alive)) in zip(self.PM, st):
            m = 0
            for r in range(1, l):
                if (alive >> r) & 1 and (A * r + B) % l == r:
                    m |= 1 << r
            if not m:
                return None
            S.append(m)
        return tuple(S)

    def words(self, lmax, node_cap):
        """all words W, |W| <= lmax, with a periodic point y* in the cylinder and a residue
        fixed set S_l(W) != 0 for every l: list of (W, y*, S)."""
        R = Fraction(self.p, self.q)
        st0 = tuple((1, 0, self.full[l]) for l in self.PM)
        stack = [(st0, Fraction(1), Fraction(0), Fraction(0), Fraction(1), ())]
        found, nodes = [], 0
        while stack:
            st, al, be, lo, hi, w = stack.pop()
            nodes += 1
            if nodes > node_cap:
                return found, nodes, True
            if w:
                ys = be / (1 - al)
                if lo <= ys < hi:
                    S = self.fixed_sets(st)
                    if S is not None:
                        found.append((w, ys, S))
            if len(w) == lmax:
                continue
            for s in self.alph:
                be2 = (self.p * be - s - self.c) / self.q
                al2 = al * R
                lo2 = max(lo, -be2 / al2)
                hi2 = min(hi, (1 - be2) / al2)
                if lo2 >= hi2:
                    continue
                st2 = self.step_masks(st, s) if self.PM else ()
                if st2 is None:
                    continue
                stack.append((st2, al2, be2, lo2, hi2, w + (s,)))
        return found, nodes, False

    def horse_ok(self, W, K):
        lo, hi = K
        for s in reversed(W):
            lo = (self.q * lo + s + self.c) / self.p
            hi = (self.q * hi + s + self.c) / self.p
            if lo < 0 or hi >= 1:
                return False
        return K[0] <= lo and hi <= K[1]

    def crt(self, S1, S2):
        M, r0 = 1, 0
        for l, m1, m2 in zip(self.PM, S1, S2):
            m = m1 & m2
            r = next(r for r in range(1, l) if (m >> r) & 1)
            # combine r0 mod M with r mod l
            t = ((r - r0) * pow(M, -1, l)) % l
            r0, M = r0 + M * t, M * l
        return r0, M

    def search(self, lmax, node_cap, pair_cap=2_000_000):
        found, nodes, cut = self.words(lmax, node_cap)
        found.sort(key=lambda f: (len(f[0]), f[0]))
        tried = 0
        for i in range(len(found)):
            W1, y1, S1 = found[i]
            for j in range(i + 1, len(found)):
                W2, y2, S2 = found[j]
                if any(not (a & b) for a, b in zip(S1, S2)):
                    continue
                if W1 + W2 == W2 + W1:
                    continue
                tried += 1
                if tried > pair_cap:
                    return None, dict(words=len(found), nodes=nodes, cut=cut, pairs=tried,
                                      pair_cut=True)
                K = (min(y1, y2), max(y1, y2))
                if self.horse_ok(W1, K) and self.horse_ok(W2, K):
                    r0, M = self.crt(S1, S2)
                    return (dict(r0=r0, M=M, W1=list(W1), W2=list(W2),
                                 K=[str(K[0]), str(K[1])]),
                            dict(words=len(found), nodes=nodes, cut=cut, pairs=tried))
        return None, dict(words=len(found), nodes=nodes, cut=cut, pairs=tried, pair_cut=False)


# ------------------------------------------------------------------ G-4(b): independent recheck

def recheck(p, q, nu, P, wit, trials=20, blocks=30, seed=1):
    """Independent of Model: build y0 for a random block sequence by composing the inverse
    branches from scratch, then simulate forward exactly; residues by brute-force division."""
    nu = Fraction(nu)
    PM = [l for l in P if q % l]
    W = [wit["W1"], wit["W2"]]
    Ks = [Fraction(wit["K"][0]), Fraction(wit["K"][1])]
    rng = random.Random(seed)
    for i in range(trials):
        seq = [rng.randrange(2) for _ in range(blocks)]
        word = [s for b in seq for s in W[b]]
        y = Ks[i % 2]                                 # both ends of K
        for s in reversed(word):                      # y_{t} from y_{t+1}
            y = (q * y + s + (p - q) * nu) / p
        r = {l: wit["r0"] % l for l in PM}               # residues prime by prime (CRT)
        for t, s in enumerate(word):
            if not (0 <= y < 1):
                return False, f"y out of [0,1) at t={t}"
            if any(r[l] == 0 for l in PM):
                return False, f"residue not avoiding at t={t}"
            if any(s % l == 0 for l in P if q % l == 0):
                return False, f"letter {s} not avoiding at t={t}"
            y2 = (p * y - s - (p - q) * nu) / q
            r2 = {}
            for l in PM:
                sol = [x for x in range(l) if (q * x - p * r[l] - s) % l == 0]
                assert len(sol) == 1
                r2[l] = sol[0]
            y, r = y2, r2
        if not (0 <= y < 1) or any(r[l] != wit["r0"] % l for l in PM):
            return False, "block sequence does not close"
    return True, "ok"


def engine_check(p, q, nu, P, wit, Ds=(None,), blocks=12, seed=2):
    """G-4(c): the witness pseudo-orbits are paths of the exact GenCert graph
    (gencert.LeanModel.succMask = Params.succMask of DubC2/GenCert.lean) at the given D's."""
    sys.path.insert(0, HERE)
    from gencert import LeanModel
    nu = Fraction(nu)
    a, b = nu.numerator, nu.denominator
    W = [wit["W1"], wit["W2"]]
    rng = random.Random(seed)
    seq = [rng.randrange(2) for _ in range(blocks)]
    word = [s for blk in seq for s in W[blk]]
    y = Fraction(wit["K"][0])
    for s in reversed(word):
        y = (q * y + s + (p - q) * nu) / p
    out = []
    for D in Ds:
        D = D or p * b * 4
        m = LeanModel(p, q, a, b, list(P), D)
        if m.nV > 6_000_000:                   # succMask bitmasks have nV bits: skip
            out.append((D, "skipped: nV=%d" % m.nV))
            continue
        yy, r = y, wit["r0"] % m.M
        ok = True
        for s in word:
            k = r * D + int(D * yy)            # floor, y >= 0
            y2 = (p * yy - s - (p - q) * nu) / q
            r2 = (p * r + s) * m.qinv % m.M
            k2 = r2 * D + int(D * y2)
            if not (m.succMask(k, s) >> k2) & 1:
                ok = False
                break
            yy, r = y2, r2
        out.append((D, ok))
    # False iff some D rejected the path; None iff every D was skipped
    if any(ok is False for _, ok in out):
        return False, out
    return (True if any(ok is True for _, ok in out) else None), out


# ------------------------------------------------------------------ drivers

def run_cell(p, q, nu, P, lmax, node_cap):
    t0 = time.time()
    m = Model(p, q, nu, P)
    wit, stats = m.search(lmax, node_cap)
    rc = recheck(p, q, nu, P, wit) if wit else None
    ec = engine_check(p, q, nu, P, wit, Ds=(None, 7 * p)) if wit else None
    return dict(p=p, q=q, nu=str(Fraction(nu)), P=list(P), lmax=lmax, witness=wit,
                recheck=rc, engine=ec, secs=round(time.time() - t0, 2), **stats)


def controls(lmax, node_cap):
    reg = json.load(open(os.path.join(HERE, "Atlas", "registry.json")))
    rows = []
    for e in reg:
        p, q, P = e["p"], e["q"], e["P"]
        extra = [l for l in primes_upto(13) if l not in P][:2]
        for PP in [P] + [sorted(P + [l]) for l in extra]:
            r = run_cell(p, q, e["nu"], PP, lmax, node_cap)
            r["control"] = e["name"]
            rows.append(r)
            print(json.dumps({k: r[k] for k in ("control", "P", "witness", "words", "cut",
                                                 "secs")}), flush=True)
    return rows


def downward(p, q, nu, primes, lmax, node_cap):
    """horseshoe at the maximal set; else the antichain of maximal killed subsets."""
    rows, killed, alive = [], [], []
    for k in range(len(primes), 0, -1):
        for P in itertools.combinations(primes, k):
            if any(set(P) <= set(K) for K in killed):
                continue
            r = run_cell(p, q, nu, list(P), lmax, node_cap)
            rows.append(r)
            ok = r["witness"] is not None and r["recheck"][0]
            (killed if ok else alive).append(P)
            print(json.dumps({k2: r[k2] for k2 in ("p", "q", "P", "witness", "recheck",
                                                    "words", "cut", "secs")}), flush=True)
    return rows, killed


def empty_row_list():
    """the empty rows of the atlas scan (data/transform/db/rows.csv), minus the N-2 rows."""
    import csv
    rows = []
    for r in csv.DictReader(open(os.path.join(HERE, "data", "transform", "db", "rows.csv"))):
        key = (int(r["p"]), int(r["q"]), str(Fraction(r["nu"])))
        if r["hit"] != "False" or r["source"] != "atlas2" or key in rows:
            continue
        if key[2] == "1/2" and key[0] - key[1] == 1 and key[0] <= 7:
            continue                                # 5/4, 6/5, 7/6 at 1/2: done (note section 9)
        rows.append(key)
    return rows


def empty_rows(shard, pmax, lmax, node_cap, tag):
    i, n = map(int, shard.split("/"))
    rows = empty_row_list()[i::n]
    with open(os.path.join(OUT, f"xh_empty_{i}of{n}{tag}.jsonl"), "w") as f:
        for p, q, nu in rows:
            t0 = time.time()
            res, killed = downward(p, q, nu, primes_upto(pmax), lmax, node_cap)
            for r in res:
                f.write(json.dumps(r) + "\n")
            f.flush()
            print(f"ROW {p}/{q} nu={nu}: maximal killed {killed} ({time.time() - t0:.0f}s)",
                  flush=True)


def extend_empty(shard, node_cap, tag, Ls=(16, 20, 24), deep=False):
    """the sets left alive by --empty (and, if deep, by --extend-empty), largest first; a kill
    covers all subsets."""
    import glob
    i, n = map(int, shard.split("/"))
    rows = {}
    pats = ["xh_empty_*of3.jsonl"] + (["xh_extempty_*of3.jsonl"] if deep else [])
    for fn in sorted(f for pat in pats for f in glob.glob(os.path.join(OUT, pat))):
        for line in open(fn):
            r = json.loads(line)
            rows.setdefault((r["p"], r["q"], r["nu"]), []).append(r)
    def dead(r):
        return r["witness"] and r["recheck"][0]
    part = []
    for k, rs in sorted(rows.items()):
        old = [set(r["P"]) for r in rs if dead(r)]
        alive = sorted({tuple(r["P"]) for r in rs if not dead(r)
                        and not any(set(r["P"]) <= K for K in old)})
        if alive:
            part.append((k, alive))
    name = "xh_deepempty" if deep else "xh_extempty"
    with open(os.path.join(OUT, f"{name}_{i}of{n}{tag}.jsonl"), "w") as f:
        for (p, q, nu), alive in part[i::n]:
            killed = []
            for P in sorted(alive, key=lambda P: (-len(P), P)):
                if any(set(P) <= set(K) for K in killed):
                    continue
                for L in Ls:
                    r = run_cell(p, q, nu, list(P), L, node_cap)
                    f.write(json.dumps(r) + "\n")
                    f.flush()
                    print(json.dumps({k: r[k] for k in ("p", "q", "nu", "P", "lmax", "recheck",
                                                         "words", "nodes", "cut", "secs")}),
                          flush=True)
                    if r["witness"] and r["recheck"][0]:
                        killed.append(P)
                        break
            print(f"ROW {p}/{q} nu={nu}: newly killed {killed}", flush=True)


# ---------------------------------------------------------------------------------------------
# --emit: the witnesses as `DubC2.Gen.HorseWitness` data (DubC2/Horseshoe.lean)
#
# Lean's witness has two words of ONE length; from (W1, W2) we emit w1 = W1 W2, w2 = W2 W1 (equal
# length, distinct iff W1 W2 != W2 W1, and both carry K into K).  lean_horse_ok mirrors
# `DubC2.Gen.horseOK` exactly, so a witness that fails it is never emitted.

def lean_inv(q, l):
    return next((i for i in range(l) if q * i % l == 1), 0)


def lean_horse_ok(p, q, a, b, H):
    PM, Pq, R, w1, w2, lo, hi = H
    c = Fraction((p - q) * a, b)

    def hb(s, y):
        return (q * y + s + c) / p

    def back(w, y):
        for s in reversed(w):
            y = hb(s, y)
        return y

    def walk(l, r, w, i):
        inv = lean_inv(q, l)
        for s in w[:i]:
            r = ((p * r + s) * inv) % l
        return r

    def word_ok(w):
        L = len(w)
        for l in PM:
            r = R % l
            if walk(l, r, w, L) != r or any(walk(l, r, w, i) == 0 for i in range(L)):
                return False
        if any(s % l == 0 for l in Pq for s in w):
            return False
        if not (lo <= back(w, lo) and back(w, hi) <= hi):
            return False
        return all(0 <= back(w[i:], lo) and back(w[i:], hi) < 1 for i in range(L))

    return (len(w1) > 0 and len(w1) == len(w2) and w1 != w2
            and all(l >= 2 and q * lean_inv(q, l) % l == 1 for l in PM)
            and word_ok(w1) and word_ok(w2))


def lean_witness(p, q, P, wit):
    W1, W2 = wit["W1"], wit["W2"]
    PM = [l for l in P if q % l != 0]
    Pq = [l for l in P if q % l == 0]
    lo, hi = Fraction(wit["K"][0]), Fraction(wit["K"][1])
    return (PM, Pq, wit["r0"], W1 + W2, W2 + W1, lo, hi)


def lean_q(x):
    x = Fraction(x)
    return f"({x.numerator} / {x.denominator} : ℚ)" if x.denominator != 1 else f"({x.numerator} : ℚ)"


def lean_list(xs):
    return "[" + ", ".join(str(x) for x in xs) + "]"


def nu_tag(nu):
    nu = Fraction(nu)
    if nu < 0:
        return "num" + str(-nu).replace("/", "_")
    return "nu" + str(nu).replace("/", "_")


def engine_rejected(r):
    eng = r.get("engine")
    return bool(eng) and any(ok is False for _, ok in eng[1])


def emit(path):
    found = {}
    for name in sorted(os.listdir(OUT)):
        if not name.endswith(".jsonl") or "controls" in name:
            continue
        for line in open(os.path.join(OUT, name)):
            r = json.loads(line)
            if not r.get("witness") or not (r.get("recheck") or [False])[0]:
                continue
            if r.get("source") == "follower":       # long words: --emit-frontier, own module
                continue
            if engine_rejected(r):
                print(f"engine rejected: {r['p']}/{r['q']} {r['nu']} {r['P']}", file=sys.stderr)
                continue
            found.setdefault((r["p"], r["q"], Fraction(r["nu"])), {})[tuple(r["P"])] = r["witness"]
    out = ["/-",
           "(C) 2026 Ralf Stephan, in collaboration with Claude Code.",
           "Released under CC0 1.0 Universal (public-domain dedication).",
           "See https://creativecommons.org/publicdomain/zero/1.0/",
           "-/",
           "import DubC2.Horseshoe",
           "",
           "/-!",
           "# Horseshoe obstructions on the empty atlas rows (generated)",
           "",
           "Generated by `DubC2/xhorse.py --emit`, from the witnesses of experiment X-H",
           "(`DubC2/data/transform/xh/`).  Each witness `(W₁, W₂)` found by the search is emitted as the",
           "equal-length pair `w₁ = W₁W₂`, `w₂ = W₂W₁`; only the **maximal** witnessed prime sets of each",
           "row are listed.  Each row is one theorem: no certificate is checked for any parameter set of",
           "that base and shift whose prime lists lie inside a listed witness's — for every cell count",
           "`D` and every modulus `M` (`DubC2.Gen.not_checked_of_horseRow`).",
           "",
           "These are statements about the certificate method, not about the orbits: a horseshoe",
           "pseudo-orbit need not come from any real `ξ`.",
           "",
           "## References",
           "",
           "* [Oda26] Y. Odagiri, *Finite graph certificates for composite terms in rational floor "
           "sequences*,",
           "  Zenodo, doi:10.5281/zenodo.22997709 (2026).",
           "-/",
           "",
           "namespace DubC2.Gen.HorseAtlas",
           "",
           "open DubC2.Gen",
           ""]
    for (p, q, nu) in sorted(found, key=lambda k: (k[0] / k[1], k[0], k[2])):
        a, b = nu.numerator, nu.denominator
        sets = found[(p, q, nu)]
        maxi = sorted((P for P in sets if not any(set(P) < set(Q) for Q in sets)),
                      key=lambda P: (len(P), P))
        ws = []
        for P in maxi:
            H = lean_witness(p, q, list(P), sets[P])
            if not lean_horse_ok(p, q, a, b, H):
                print(f"REJECTED by lean_horse_ok: {p}/{q} {nu} {P}", file=sys.stderr)
                continue
            ws.append(H)
        if not ws:
            continue
        name = f"b{p}_{q}_{nu_tag(nu)}"
        out.append(f"/-- Maximal horseshoe-killed divisor sets at `{p}/{q}`, `ν = {nu}`. -/")
        out.append(f"def {name} : List HorseWitness :=")
        items = []
        for PM, Pq, R, w1, w2, lo, hi in ws:
            items.append("  ⟨" + lean_list(PM) + ", " + lean_list(Pq) + f", {R},\n    "
                         + lean_list(w1) + ",\n    " + lean_list(w2) + ",\n    "
                         + lean_q(lo) + ", " + lean_q(hi) + "⟩")
        out.append("  [" + ",\n".join(items)[2:] + "]")
        out.append("")
        out.append(f"/-- No certificate for `{p}/{q}`, `ν = {nu}`, with primes inside a listed set. -/")
        out.append('@[category research solved, AMS 11 37, ref "Oda26", group "dubc2_obstruction"]')
        out.append(f"theorem {name}_killed : ∀ w ∈ {name}, ∀ (P : Params) (C : Cert), P.p = {p} →")
        out.append(f"    P.q = {q} → P.a = {a} → P.b = {b} → (∀ l ∈ P.PM, l ∈ w.PM) →")
        out.append("    (∀ l ∈ P.Pq, l ∈ w.Pq) → ¬ Checked P C :=")
        out.append("  not_checked_of_horseRow (by decide +kernel)")
        out.append("")
        print(f"{p}/{q} nu={nu}: {len(ws)} maximal witnessed sets: {[list(P) for P in maxi]}")
    out.append("end DubC2.Gen.HorseAtlas")
    with open(path, "w") as f:
        f.write("\n".join(out) + "\n")


def emit_frontier(path):
    """the horseshoes of xfrontier.py (xh_frontier.jsonl) as DubC2/HorseshoeFrontier.lean, one
    theorem per witness: their words run to 190 letters and a whole row in one `decide` exceeds
    the 7 GB build cap."""
    recs = [json.loads(l) for l in open(os.path.join(OUT, "xh_frontier.jsonl"))]
    recs = [r for r in recs if not any((s["p"], s["q"], s["nu"]) == (r["p"], r["q"], r["nu"])
                                       and set(r["P"]) < set(s["P"]) for s in recs)]  # maximal
    out = ["/-",
           "(C) 2026 Ralf Stephan, in collaboration with Claude Code.",
           "Released under CC0 1.0 Universal (public-domain dedication).",
           "See https://creativecommons.org/publicdomain/zero/1.0/",
           "-/",
           "import DubC2.Horseshoe",
           "",
           "/-!",
           "# Horseshoe obstructions on the zero-entropy frontier (generated)",
           "",
           "Generated by `DubC2/xhorse.py --emit-frontier` from `DubC2/data/transform/xh/"
           "xh_frontier.jsonl`,",
           "the horseshoes that `DubC2/xfrontier.py` reads off the exact follower automaton of a "
           "cell",
           "(two closed walks at a branching state).  These are the cells left open by the "
           "length-bounded",
           "search of `DubC2/HorseshoeAtlas.lean`; one theorem per witness, since a single word has "
           "up to",
           "190 letters.  Statements about the certificate method, not about the orbits.",
           "",
           "## References",
           "",
           "* [Oda26] Y. Odagiri, *Finite graph certificates for composite terms in rational floor "
           "sequences*,",
           "  Zenodo, doi:10.5281/zenodo.22997709 (2026).",
           "-/",
           "",
           "namespace DubC2.Gen.HorseFrontier",
           "",
           "open DubC2.Gen",
           ""]
    for r in recs:
        p, q, nu, P, wit = r["p"], r["q"], Fraction(r["nu"]), r["P"], r["witness"]
        if not wit or not r["recheck"][0]:
            continue
        a, b = nu.numerator, nu.denominator
        H = lean_witness(p, q, P, wit)
        if not lean_horse_ok(p, q, a, b, H):
            print(f"REJECTED by lean_horse_ok: {p}/{q} {nu} {P}", file=sys.stderr)
            continue
        PM, Pq, R, w1, w2, lo, hi = H
        name = f"b{p}_{q}_{nu_tag(nu)}_P" + "_".join(map(str, P))
        out.append(f"/-- Horseshoe witness at `{p}/{q}`, `ν = {nu}`, `𝒫 = {{{', '.join(map(str, P))}}}` "
                   f"(words of length {len(w1)}). -/")
        out.append(f"def {name} : List HorseWitness :=")
        out.append("  [⟨" + lean_list(PM) + ", " + lean_list(Pq) + f", {R},\n    "
                   + lean_list(w1) + ",\n    " + lean_list(w2) + ",\n    "
                   + lean_q(lo) + ", " + lean_q(hi) + "⟩]")
        out.append("")
        out.append(f"/-- No certificate for `{p}/{q}`, `ν = {nu}`, with primes inside "
                   f"`{{{', '.join(map(str, P))}}}`. -/")
        out.append('@[category research solved, AMS 11 37, ref "Oda26", group "dubc2_obstruction"]')
        out.append(f"theorem {name}_killed : ∀ w ∈ {name}, ∀ (P : Params) (C : Cert), P.p = {p} →")
        out.append(f"    P.q = {q} → P.a = {a} → P.b = {b} → (∀ l ∈ P.PM, l ∈ w.PM) →")
        out.append("    (∀ l ∈ P.Pq, l ∈ w.Pq) → ¬ Checked P C :=")
        out.append("  not_checked_of_horseRow (by decide +kernel)")
        out.append("")
        print(f"{name}: words of length {len(w1)}")
    out.append("end DubC2.Gen.HorseFrontier")
    with open(path, "w") as f:
        f.write("\n".join(out) + "\n")


def main():
    ap = argparse.ArgumentParser()
    ap.add_argument("--controls", action="store_true")
    ap.add_argument("--rows", default="")
    ap.add_argument("--nu", default="1/2")
    ap.add_argument("--pmax", type=int, default=17)
    ap.add_argument("--lmax", type=int, default=12)
    ap.add_argument("--nodes", type=int, default=2_000_000)
    ap.add_argument("--tag", default="")
    ap.add_argument("--extend", action="store_true",
                    help="longer words: 6/5, 7/6 beyond primes <= 17, the 5/4 survivors")
    ap.add_argument("--deep", action="store_true",
                    help="the 5/4 sets still open after --extend, at lengths 28..40")
    ap.add_argument("--empty", default="",
                    help="SHARD/NSHARDS: X-H downward on the remaining empty rows of rows.csv")
    ap.add_argument("--extend-empty", default="",
                    help="SHARD/NSHARDS: the survivors of --empty, top-down, at L = 16, 20, 24")
    ap.add_argument("--deep-empty", default="",
                    help="SHARD/NSHARDS: what --extend-empty left open, at L = 28, 32, 36")
    ap.add_argument("--emit", default="",
                    help="write the maximal witnesses as Lean data (DubC2/HorseshoeAtlas.lean)")
    ap.add_argument("--emit-frontier", default="",
                    help="write xfrontier.py's horseshoes as Lean (DubC2/HorseshoeFrontier.lean)")
    args = ap.parse_args()
    os.makedirs(OUT, exist_ok=True)
    if args.emit_frontier:
        emit_frontier(args.emit_frontier)
        return
    if args.emit:
        emit(args.emit)
        return
    if args.deep_empty:
        extend_empty(args.deep_empty, args.nodes, args.tag, Ls=(28, 32, 36), deep=True)
        return
    if args.extend_empty:
        extend_empty(args.extend_empty, args.nodes, args.tag)
        return
    if args.empty:
        empty_rows(args.empty, args.pmax, args.lmax, args.nodes, args.tag)
        return
    if args.deep:
        sets = [[2, 3, 7, 11, 13], [2, 3, 7, 11, 17], [2, 3, 7, 13, 17],
                [2, 3, 5, 7, 11, 13], [2, 3, 5, 7, 11, 17], [2, 3, 5, 7, 13, 17],
                [2, 3, 7, 11, 13, 17], [2, 3, 5, 7, 11, 13, 17]]
        with open(os.path.join(OUT, f"xh_5_4_deep{args.tag}.jsonl"), "w") as f:
            for P in sets:
                for L in (28, 32, 36, 40):
                    r = run_cell(5, 4, args.nu, P, L, 8_000_000)
                    f.write(json.dumps(r) + "\n")
                    f.flush()
                    print(json.dumps({k: r[k] for k in ("P", "lmax", "recheck", "engine",
                                                         "words", "nodes", "cut", "secs")}),
                          flush=True)
                    if r["witness"]:
                        break
        return
    if args.extend:
        jobs = [(6, 5, primes_upto(pm), L) for pm in (19, 23, 29) for L in (20, 24, 28)]
        jobs += [(7, 6, primes_upto(pm), L) for pm in (19, 23) for L in (16, 18)]
        # the 19 sets of 5/4 with no witness at length 12 (xh_5_4_nu1_2.jsonl)
        surv = [json.loads(l)["P"] for l in open(os.path.join(OUT, "xh_5_4_nu1_2.jsonl"))]
        surv = [P for P, l in zip(surv, open(os.path.join(OUT, "xh_5_4_nu1_2.jsonl")))
                if json.loads(l)["witness"] is None]
        jobs += [(5, 4, P, L) for P in sorted(surv, key=len) for L in (16, 20, 24)]
        done = set()
        with open(os.path.join(OUT, f"xh_extend{args.tag}.jsonl"), "w") as f:
            for p, q, P, L in jobs:
                if (p, q, tuple(P)) in done:
                    continue
                r = run_cell(p, q, args.nu, P, L, args.nodes)
                f.write(json.dumps(r) + "\n")
                f.flush()
                if r["witness"] and r["recheck"][0]:
                    done.add((p, q, tuple(P)))
                print(json.dumps({k: r[k] for k in ("p", "q", "P", "lmax", "recheck", "words",
                                                     "nodes", "cut", "secs")}), flush=True)
        return
    if args.controls:
        rows = controls(args.lmax, args.nodes)
        with open(os.path.join(OUT, f"xh_controls{args.tag}.jsonl"), "w") as f:
            for r in rows:
                f.write(json.dumps(r) + "\n")
        bad = [r for r in rows if r["witness"]]
        print("CONTROL VIOLATIONS:", len(bad))
        return
    for base in args.rows.split(","):
        b = Fraction(base)
        p, q = b.numerator, b.denominator
        primes = primes_upto(args.pmax)
        rows, killed = downward(p, q, args.nu, primes, args.lmax, args.nodes)
        name = f"xh_{p}_{q}_nu{str(Fraction(args.nu)).replace('/', '_')}{args.tag}.jsonl"
        with open(os.path.join(OUT, name), "w") as f:
            for r in rows:
                f.write(json.dumps(r) + "\n")
        print(f"{p}/{q}: maximal killed sets {killed}")


if __name__ == "__main__":
    main()
