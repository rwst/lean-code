#!/usr/bin/env python3
# (C) 2026 Ralf Stephan, in collaboration with Claude Code.  CC0 1.0.
#
# xnu.py -- plan-dubC2-transform, experiment X-nu (M3 flagship, gate G-2).
#
# The exact nu-cell decomposition of the shift circle for x_n = floor(xi (p/q)^n + nu).
#
# At a fixed cell count D every comparison of the certificate graph (GenCert.lean, succList) is
#     q b c' < p b (c+1) - (p-q) a D - s b D,      p b c - (p-q) a D - s b D < q b (c'+1)
# with nu = a/b, i.e. an integer against (p-q) D nu.  So the graph is constant on every open
# nu-cell  (j, j+1) / ((p-q) D),  and on the CLOSED cell the hull graph (NuInterval.lean, hullOK)
# equals the open-cell graph.  Hence: a certificate at the midpoint nu* = (2j+1)/(2(p-q)D) plus
# hullOK proves the divisor-set theorem for every real nu in [j, j+1]/((p-q)D).
#
# The verdict is periodic in nu with period L = lcm(P) (nu -> nu + L shifts x_n by L), so the
# circle is [0, L).  Driver: start at D0, certify each cell at its midpoint (gencert.fast_verdict),
# refine every uncertified cell by doubling D, up to a cap on D.  Output: the certified cells
# (as exact closed intervals) and the uncertified remainder, per depth.
#
# Usage:
#   xnu.py --pq 3 2 --P 2,5 --D0 6 --Dmax 192         # the flagship (3/2, {2,5})
#   xnu.py ... --json out.jsonl
#
# Recheck (R-5): --recheck samples random rational nu inside each certified cell and runs
# fast_verdict pointwise there at the same D (must certify: the graph is the same).

import argparse
import json
import math
import os
import random
import sys
import time
from fractions import Fraction

HERE = os.path.dirname(os.path.abspath(__file__))
sys.path.insert(0, HERE)
import gencert as gc  # noqa: E402


def lcm_list(xs):
    L = 1
    for x in xs:
        L = L * x // math.gcd(L, x)
    return L


def verdict(p, q, P, D, nu, det_limit):
    """certify at the rational shift nu with cell count D (the exact Lean semantics)."""
    r = gc.fast_verdict(p, q, nu.numerator, nu.denominator, P, D, det_limit=det_limit)
    return bool(r and r.get("ok"))


def midpoint(p, q, D, j):
    return Fraction(2 * j + 1, 2 * (p - q) * D)


def branches(p, q, P, nu, cap=20000):
    """the exact follower automaton at the rational shift nu has a branching SCC (then nu is
    uncertifiable at every D, Follower.checked_iff_finite); None if it exceeds the cap."""
    import xhorse as xh
    import xfrontier as xf
    st, adj, cut = xf.follower(xh.Model(p, q, nu, P), cap)
    if cut:
        return None
    return not xf.classify(st, adj)[0]


def run(p, q, P, D0, Dmax, det_limit, recheck=0, log=print, prune=False):
    L = lcm_list(P)
    g = p - q
    todo = [(D0, j) for j in range(L * g * D0)]
    cert, left = [], []
    D = D0
    while todo:
        t0 = time.time()
        nxt = []
        nok = 0
        for (D, j) in todo:
            nu = midpoint(p, q, D, j)
            if verdict(p, q, P, D, nu, det_limit):
                cert.append((D, j))
                nok += 1
                for _ in range(recheck):
                    lo, hi = Fraction(j, g * D), Fraction(j + 1, g * D)
                    k = random.randint(1, 999)
                    nu2 = lo + (hi - lo) * Fraction(k, 1000)
                    assert verdict(p, q, P, D, nu2, det_limit), ("recheck failed", D, j, nu2)
            elif 2 * D <= Dmax and not (prune and branches(p, q, P, nu)):
                nxt += [(2 * D, 2 * j), (2 * D, 2 * j + 1)]
            else:
                left.append((D, j))
        meas = sum(Fraction(1, g * d) for d, _ in cert)
        log(f"D={D}: {len(todo)} cells, {nok} certified; certified measure {float(meas):.6f}"
            f" of {L} ({float(meas / L):.4%}); {time.time() - t0:.1f}s", flush=True)
        todo = nxt
    return L, cert, left


def merge(p, q, cells):
    """certified cells -> maximal closed intervals (exact)."""
    g = p - q
    iv = sorted((Fraction(j, g * D), Fraction(j + 1, g * D)) for D, j in cells)
    out = []
    for a, b in iv:
        if out and out[-1][1] >= a:
            out[-1][1] = max(out[-1][1], b)
        else:
            out.append([a, b])
    return out


# ------------------------------------------------------------------ Lean emission
#
# Layout (one linear import chain, built one target at a time):
#   DubC2.NuCircle -> NuAtlas/<tag>_Small<k>   small cells (D <= SMALL): Params, Cert, Checked
#                  -> NuAtlas/<cell>/{Data,Part*,Main}   big cells, via gencert.emit_instance
#                  -> NuAtlas/<tag>_Cells<k>   hullOK + the closed-cell theorem `<cell>_cell`
#                  -> NuAtlas/<tag>_Circle     merged intervals, the domain, the circle theorem
# Params/Cert/Checked live in namespace DubC2.Atlas (as gencert emits them); the shift
# theorems in DubC2.NuAtlas.

HEADER = gc.HEADER
SMALL = 48


def lit(x):
    return f"({x.numerator} : ℝ)" if x.denominator == 1 else f"({x.numerator} / {x.denominator} : ℝ)"


def plist(P):
    return "[" + ", ".join(str(l) for l in sorted(P)) + "]"


def cell_model(p, q, P, D, j):
    g = p - q
    m = gc.LeanModel(p, q, 2 * j + 1, 2 * g * D, sorted(P), D)
    cert = m.certificate()
    assert cert is not None and cert["ok"], ("no certificate", D, j)
    return m, cert


def lean_small(m, cert, nm, Z=256):
    nB = (m.nV + Z - 1) // Z
    opt = lambda x: "none" if x is None else f"some {x}"
    blocks = lambda A: "[" + ", ".join(str((A >> (i * Z)) & ((1 << Z) - 1)) for i in range(nB)) + "]"
    LB = lambda As: "[" + ", ".join(blocks(A) for A in As) + "]"
    trans = "[" + ",\n    ".join("[" + ", ".join(opt(x) for x in row) + "]" for row in cert["trans"]) + "]"
    return (f"/-- Parameters (cell midpoint). -/\n"
            f"def {nm}P : Params where\n  p := {m.p}\n  q := {m.q}\n  a := {m.a}\n  b := {m.b}\n"
            f"  D := {m.D}\n  M := {m.M}\n  qinv := {m.qinv}\n  PM := {m.PM}\n  Pq := {m.Pq}\n"
            f"  sLo := {m.sLo}\n  nA := {m.nA}\n\n"
            f"set_option maxRecDepth 100000 in\n/-- Certificate. -/\ndef {nm}C : Cert where\n"
            f"  J := {cert['J']}\n  Z := {Z}\n  nB := {nB}\n  peels := {LB(cert['peels'])}\n"
            f"  imgs := {LB(cert['imgs'])}\n  core := {cert['core']}\n  sets := {cert['sets']}\n"
            f"  trans := {trans}\n  rank := {cert['rank']}\n\n"
            f"set_option maxRecDepth 100000 in\n"
            f"theorem {nm}_checked : Checked {nm}P {nm}C :=\n"
            f"  ⟨by decide +kernel, by decide +kernel, by decide +kernel⟩\n\n")


def lean_tail(p, q, P, D, j, nm):
    g = p - q
    lo, hi = Fraction(j, g * D), Fraction(j + 1, g * D)
    A = f"DubC2.Atlas.{nm}"
    pl = plist(P)
    return (f"theorem {nm}_hull : hullOK {A}P {2 * j} {2 * j + 2} = true := by decide +kernel\n\n"
            f"/-- `{pl}` at `{p}/{q}` for every real `ν ∈ [{lo}, {hi}]` (`D = {D}`). -/\n"
            f"theorem {nm}_cell {{ξ ν : ℝ}} (hξ : ξ ≠ 0) (h₀ : {lit(lo)} ≤ ν) (h₁ : ν ≤ {lit(hi)}) :\n"
            f"    ∃ᶠ n in atTop, ∃ ℓ ∈ ({pl} : List ℤ), ℓ ∣ Z32.xInt {p} {q} ξ ν n := by\n"
            f"  refine (divisor_set_of_checked_hull {A}_checked {nm}_hull (ν := ν)\n"
            f"    (by norm_num [{A}P]; linarith) (by norm_num [{A}P]; linarith) hξ).mono\n"
            f"    fun n ⟨ℓ, hℓ, hd⟩ => ⟨ℓ, ?_, by simpa [{A}P] using hd⟩\n"
            f"  exact (by decide +kernel : ∀ l ∈ {A}P.PM ++ {A}P.Pq, (l : ℤ) ∈ ({pl} : List ℤ)) ℓ hℓ\n\n")


def lean_union(p, q, P, name, cells, doc):
    """a theorem for a closed interval covered by consecutive cells (nm, (lo, hi)), sorted."""
    pl = plist(P)
    lo, hi = cells[0][1][0], cells[-1][1][1]
    lines, ind = [], "  "
    for k, (nm, (a, b)) in enumerate(cells):
        if k == len(cells) - 1:
            lines.append(f"{ind}exact {nm}_cell hξ (by linarith) h₁")
        else:
            lines.append(f"{ind}rcases le_total ν {lit(b)} with h{k} | h{k}")
            lines.append(f"{ind}· exact {nm}_cell hξ (by linarith) h{k}")
            lines.append(f"{ind}· ")
            ind += "  "
    merged = []
    for ln in lines:
        if merged and merged[-1].strip() == "·":
            merged[-1] = merged[-1].rstrip() + " " + ln.strip()
        else:
            merged.append(ln)
    return (f"/-- {doc} -/\n@[category research solved, AMS 11 37, ref \"DN05\", group \"dubc2_shift\"]\n"
            f"theorem {name} {{ξ ν : ℝ}} (hξ : ξ ≠ 0) (h₀ : {lit(lo)} ≤ ν) (h₁ : ν ≤ {lit(hi)}) :\n"
            f"    ∃ᶠ n in atTop, ∃ ℓ ∈ ({pl} : List ℤ), ℓ ∣ Z32.xInt {p} {q} ξ ν n := by\n"
            + "\n".join(merged) + "\n\n")


def file_head(prev, doc):
    return (HEADER + f"import {prev}\n\n/-! {doc} — generated by `DubC2/xnu.py`; do not edit. -/\n\n")


def emit_atlas(p, q, P, cells, tag, root="DubC2/NuAtlas", first="DubC2.NuCircle", per_file=8,
               title=""):
    """cells: certified (D, j) on the fundamental domain.  Returns the last module name."""
    os.makedirs(root, exist_ok=True)
    g = p - q
    cells = sorted(cells, key=lambda c: Fraction(c[1], c[0]))
    names = [(f"{tag}_D{D}_j{j}", D, j) for D, j in cells]
    prev = first
    small = [x for x in names if x[1] <= SMALL]
    big = [x for x in names if x[1] > SMALL]
    # batch small cells by total cell count (memory: three D = 96 cells in one file exceed 7 GB)
    batches, cur = [], []
    for x in small:
        if cur and sum(y[1] for y in cur) + x[1] > 96:
            batches.append(cur)
            cur = []
        cur.append(x)
    if cur:
        batches.append(cur)
    k = 0
    for bi, part in enumerate(batches):
        mn = f"{tag}_Small{bi + 1}"
        body = file_head(prev, f"{title}: small cells {k + 1}–{k + len(part)}")
        k += len(part)
        body += "namespace DubC2.Atlas\n\nopen DubC2.Gen\n\n"
        for nm, D, j in part:
            m, cert = cell_model(p, q, P, D, j)
            body += lean_small(m, cert, nm)
        body += "end DubC2.Atlas\n"
        open(os.path.join(root, mn + ".lean"), "w").write(body)
        prev = f"DubC2.NuAtlas.{mn}"
        print("wrote", mn, flush=True)
    for nm, D, j in big:
        m, cert = cell_model(p, q, P, D, j)
        lo, hi = Fraction(j, g * D), Fraction(j + 1, g * D)
        gc.emit_instance(m, cert, nm, os.path.join(root, nm),
                         f"{title}: the certificate at the midpoint of `[{lo}, {hi}]`",
                         prev=prev, modroot="DubC2.NuAtlas", group="dubc2_shift",
                         member_budget=3000)  # 94-member pieces of D=384 cells exceed 7 GB
        prev = f"DubC2.NuAtlas.{nm}.Main"
        print("wrote", nm, flush=True)
    for k in range(0, len(names), 2 * per_file):
        part = names[k:k + 2 * per_file]
        mn = f"{tag}_Cells{k // (2 * per_file) + 1}"
        body = file_head(prev, f"{title}: hull checks and closed cells {k + 1}–{k + len(part)}")
        body += "namespace DubC2.NuAtlas\n\nopen Filter DubC2.Gen\n\n"
        for nm, D, j in part:
            body += lean_tail(p, q, P, D, j, nm)
        body += "end DubC2.NuAtlas\n"
        open(os.path.join(root, mn + ".lean"), "w").write(body)
        prev = f"DubC2.NuAtlas.{mn}"
        print("wrote", mn, flush=True)
    return prev, [(nm, (Fraction(j, g * D), Fraction(j + 1, g * D))) for nm, D, j in names]


def emit_circle(p, q, P, tag, cells, prev, L, root="DubC2/NuAtlas", title=""):
    """merged intervals of the domain, the domain predicate, the circle theorem."""
    pl = plist(P)
    runs = []
    for c in cells:
        if runs and runs[-1][-1][1][1] == c[1][0]:
            runs[-1].append(c)
        else:
            runs.append([c])
    body = file_head(prev, f"{title}: the shift circle")
    body += "namespace DubC2.NuAtlas\n\nopen Filter DubC2.Gen\n\n"
    ivs = []
    for i, r in enumerate(runs):
        lo, hi = r[0][1][0], r[-1][1][1]
        body += lean_union(p, q, P, f"{tag}_iv{i + 1}", r,
                           f"`{pl}` at `{p}/{q}` for every real `ν ∈ [{lo}, {hi}]`.")
        ivs.append((lo, hi))
    conds = " ∨\n    ".join(f"({lit(a)} ≤ ν ∧ ν ≤ {lit(b)})" for a, b in ivs)
    body += (f"/-- The certified shifts of the fundamental domain: {len(ivs)} closed intervals. -/\n"
             f"def {tag}_dom (ν : ℝ) : Prop :=\n    {conds}\n\n")
    cases = "\n".join(
        f"  {'· ' if True else ''}exact {tag}_iv{i + 1} hξ h.1 h.2" if i == len(ivs) - 1 else
        f"  rcases h with h | h\n  · exact {tag}_iv{i + 1} hξ h.1 h.2" for i in range(len(ivs)))
    # nested rcases: rewrite as a flat chain
    lines = []
    for i in range(len(ivs)):
        if i < len(ivs) - 1:
            lines.append(f"  rcases h with h | h")
            lines.append(f"  · exact {tag}_iv{i + 1} hξ h.1 h.2")
        else:
            lines.append(f"  exact {tag}_iv{i + 1} hξ h.1 h.2")
    body += (f"theorem {tag}_of_dom {{ξ ν : ℝ}} (hξ : ξ ≠ 0) (h : {tag}_dom ν) :\n"
             f"    ∃ᶠ n in atTop, ∃ ℓ ∈ ({pl} : List ℤ), ℓ ∣ Z32.xInt {p} {q} ξ ν n := by\n"
             f"  simp only [{tag}_dom] at h\n" + "\n".join(lines) + "\n\n")
    base = f"(({p} : ℝ) / {q})"
    body += (f"/-- **`{pl}` at `{p}/{q}` on the shift circle.**  For every real `ν` congruent mod `{L}`\n"
             f"to a certified shift or to its mirror image (`{tag}_dom`), and every real `ξ ≠ 0`,\n"
             f"infinitely many of `⌊ξ({p}/{q})ⁿ + ν⌋` are divisible by a member of `{pl}`. -/\n"
             f"@[category research solved, AMS 11 37, ref \"DN05\", group \"dubc2_shift\"]\n"
             f"theorem {tag}_circle {{ξ ν : ℝ}} (hξ : ξ ≠ 0)\n"
             f"    (h : ∃ k : ℤ, {tag}_dom (ν - {L} * k) ∨ {tag}_dom (1 - ν - {L} * k)) :\n"
             f"    ∃ᶠ n in atTop, ∃ ℓ ∈ ({pl} : List ℤ), ℓ ∣ ⌊ξ * {base} ^ n + ν⌋ := by\n"
             f"  have := frequently_of_circle (p := {p}) (q := {q}) (L := {L}) (by norm_num) (by norm_num)\n"
             f"    (by norm_num) (by decide) (fun ξ ν hξ h => {tag}_of_dom hξ h) hξ\n"
             f"    (by simpa using h)\n"
             f"  simpa [Z32.xInt, Z32.orb] using this\n\n"
             "end DubC2.NuAtlas\n")
    mn = f"{tag}_Circle"
    open(os.path.join(root, mn + ".lean"), "w").write(body)
    return f"DubC2.NuAtlas.{mn}", ivs


def main():
    ap = argparse.ArgumentParser()
    ap.add_argument("--pq", nargs=2, type=int, required=True)
    ap.add_argument("--P", required=True)
    ap.add_argument("--D0", type=int, default=6)
    ap.add_argument("--Dmax", type=int, default=96)
    ap.add_argument("--det", type=int, default=3000)
    ap.add_argument("--recheck", type=int, default=0)
    ap.add_argument("--json", default=None)
    ap.add_argument("--emit", default=None, help="tag: emit the fundamental-domain cells to DubC2/NuAtlas")
    ap.add_argument("--from-json", default=None, help="reuse a decomposition instead of recomputing")
    ap.add_argument("--prune", action="store_true",
                    help="refine only cells whose midpoint follower automaton does not branch")
    a = ap.parse_args()
    p, q = a.pq
    P = [int(x) for x in a.P.split(",")]
    if a.from_json:
        d = json.load(open(a.from_json))
        L, cert, left = d["L"], [tuple(c) for c in d["cert"]], [tuple(c) for c in d["left"]]
    else:
        L, cert, left = run(p, q, P, a.D0, a.Dmax, a.det, a.recheck, prune=a.prune)
    if a.emit:
        g = p - q
        lo_fd, hi_fd = Fraction(1, 2), Fraction(L, 2) + Fraction(1, 2)
        fd = [c for c in cert if lo_fd <= Fraction(c[1], g * c[0]) and Fraction(c[1] + 1, g * c[0]) <= hi_fd]
        title = f"`{plist(P)}` at `{p}/{q}`, shift-interval atlas"
        prev, cells = emit_atlas(p, q, P, fd, a.emit, title=title)
        last, ivs = emit_circle(p, q, P, a.emit, cells, prev, L, title=title)
        print("last module:", last)
        for x, y in ivs:
            print(f"  [{x}, {y}]")
        return
    iv = merge(p, q, cert)
    print(f"certified: {len(cert)} cells, {len(iv)} maximal closed intervals")
    for x, y in iv:
        print(f"  [{x}, {y}]")
    lv = merge(p, q, left)
    print(f"uncertified at Dmax: {len(left)} cells, {len(lv)} intervals")
    for x, y in lv[:60]:
        print(f"  ({x}, {y})")
    if a.json:
        with open(a.json, "w") as f:
            json.dump(dict(p=p, q=q, P=P, L=L, D0=a.D0, Dmax=a.Dmax,
                           cert=[[D, j] for D, j in cert], left=[[D, j] for D, j in left],
                           intervals=[[str(x), str(y)] for x, y in iv]), f)


if __name__ == "__main__":
    main()
