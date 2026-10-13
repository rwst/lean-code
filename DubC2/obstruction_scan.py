#!/usr/bin/env python3
# (C) 2026 Ralf Stephan, in collaboration with Claude Code.  CC0 1.0 Universal.
"""Which atlas cells does [Oda26] Theorem 42 (`DubC2.Gen.not_checked_of_two_letters`) kill?

For each (p/q, nu) row of atlas_out/atlas2.jsonl and every divisor set P of primes <= pmax with
|P| <= maxP (the atlas scan's search space), look for a two-letter witness of the Lean theorem:
letters s0 != c, and per prime l of PM (= primes of P not dividing q) a residue r != 0 mod l with
  [l | p and l does not divide s0, c]  or  [l | (p-q) r + s0 and l | c - s0],
every l of Pq (= primes of P dividing q) dividing neither letter, and with x* = s0/(p-q) + nu:
  0 <= x* <= 1,  0 < x* + (c - s0)/p < 1.
The residue conditions are per prime, so the CRT residue r0 = (combination) % M exists for every M
(every l of PM divides M); a witness therefore kills the cell for EVERY cell count D and modulus M.

Sanity: a killed P must not contain a certified (minimal) P of the same row.

Output: one JSON line per row: {"p","q","nu","killed":[[P, s0, c, {l: r}]...],"alive":[P...]}.
Usage: obstruction_scan.py [--pmax 13] [--maxP 4] [--atlas atlas_out/atlas2.jsonl]
                           [--emit DubC2/ObstructionAtlas.lean]
--emit writes the maximal killed sets of every row as `DubC2.Gen.Witness` data, each row checked by
one `decide +kernel` through `DubC2.Gen.not_checked_of_row` (DubC2/ObstructionKit.lean).
"""
import argparse, itertools, json, sys
from fractions import Fraction
from math import floor, ceil


def primes_upto(n):
    return [k for k in range(2, n + 1) if all(k % d for d in range(2, int(k ** 0.5) + 1))]


def witness(p, q, nu, P):
    Pq = [l for l in P if q % l == 0]
    PM = [l for l in P if q % l != 0]
    if any(p % l == 0 for l in Pq):
        return None
    lo = ceil(-nu * (p - q))
    hi = floor((1 - nu) * (p - q))
    for s0 in range(lo, hi + 1):
        xs = Fraction(s0, p - q) + nu
        if not (0 <= xs <= 1):
            continue
        # x* + (c - s0)/p in (0,1)  <=>  c - s0 in (-p x*, p (1 - x*))
        dlo = floor(-p * xs) + 1
        dhi = ceil(p * (1 - xs)) - 1
        for dd in range(dlo, dhi + 1):
            c = s0 + dd
            if c == s0:
                continue
            e = xs + Fraction(dd, p)
            if not (0 < e < 1):
                continue
            if any(s0 % l == 0 or c % l == 0 for l in Pq):
                continue
            res = {}
            for l in PM:
                found = None
                for r in range(1, l):
                    if (p % l == 0 and s0 % l and c % l) or \
                       (((p - q) * r + s0) % l == 0 and (c - s0) % l == 0):
                        found = r
                        break
                if found is None:
                    break
                res[l] = found
            else:
                return (s0, c, res)
    return None


def main():
    ap = argparse.ArgumentParser()
    ap.add_argument("--pmax", type=int, default=13)
    ap.add_argument("--maxP", type=int, default=4)
    ap.add_argument("--atlas", default="DubC2/atlas_out/atlas2.jsonl")
    ap.add_argument("--emit", default=None)
    args = ap.parse_args()
    rows_out = []
    primes = primes_upto(args.pmax)
    bad = 0
    for line in open(args.atlas):
        row = json.loads(line)
        p, q, nu = row["p"], row["q"], Fraction(row["nu"])
        certified = [set(m["P"]) for m in row["minimal"]]
        killed, alive = [], []
        for size in range(1, args.maxP + 1):
            for P in itertools.combinations(primes, size):
                w = witness(p, q, nu, P)
                if w is None:
                    alive.append(list(P))
                    continue
                if any(cs <= set(P) for cs in certified):
                    print(f"SANITY FAIL {p}/{q} nu={nu} P={P} contains a certified set",
                          file=sys.stderr)
                    bad += 1
                killed.append([list(P), w[0], w[1], w[2]])
        rows_out.append((p, q, nu, row["nu"], killed))
        print(json.dumps({"p": p, "q": q, "nu": row["nu"], "certified": row["minimal"] != [],
                          "nkilled": len(killed), "nalive": len(alive),
                          "killed": killed, "alive": alive}))
    if bad:
        sys.exit(1)
    if args.emit:
        emit(rows_out, args.emit, args.pmax, args.maxP)


def crt(res):
    R, m = 0, 1
    for l, r in res.items():
        while R % l != r:
            R += m
        m *= l
    return R


def tag(nu):
    return str(nu).replace("/", "_").replace("-", "m")


def emit(rows, path, pmax, maxP):
    out = ["/-",
           "(C) 2026 Ralf Stephan, in collaboration with Claude Code.",
           "Released under CC0 1.0 Universal (public-domain dedication).",
           "See https://creativecommons.org/publicdomain/zero/1.0/",
           "-/",
           "import DubC2.ObstructionKit",
           "",
           "/-!",
           "# Two-letter obstructions across the atlas (generated)",
           "",
           "Generated by `DubC2/obstruction_scan.py --emit`.  For every row `(p/q, ν)` of",
           f"`DubC2/atlas_out/atlas2.jsonl` and every divisor set of primes `≤ {pmax}` with at most "
           f"{maxP} members,",
           "the scan looks for a witness of [Oda26] Theorem 42 (`DubC2.Gen.not_checked_of_two_letters`).",
           "Listed here are the **maximal** killed sets of each row; each row is one theorem: no",
           "certificate is checked for any parameter set of that base and shift whose prime lists lie",
           "inside a listed witness's — for every cell count `D` and modulus `M`.",
           "",
           "## References",
           "",
           "* [Oda26] Y. Odagiri, *Finite graph certificates for composite terms in rational floor "
           "sequences*,",
           "  Zenodo, doi:10.5281/zenodo.22997709 (2026).",
           "-/",
           "",
           "namespace DubC2.Gen.ObsAtlas",
           "",
           "open DubC2.Gen",
           ""]
    for p, q, nu, nus, killed in rows:
        sets = [set(k[0]) for k in killed]
        maxi = [k for k, s in zip(killed, sets) if not any(s < t for t in sets)]
        if not maxi:
            continue
        a, b = nu.numerator, nu.denominator
        name = f"b{p}_{q}_nu{tag(nus)}"
        ws = []
        for P, s0, c, res in maxi:
            Pq = [l for l in P if q % l == 0]
            PM = [l for l in P if q % l != 0]
            R = crt({int(l): r for l, r in res.items()})
            ws.append(f"⟨{PM}, {Pq}, {s0}, {c}, {R}⟩")
        out.append(f"/-- Maximal two-letter-killed divisor sets at `{p}/{q}`, `ν = {nus}`. -/")
        out.append(f"def {name} : List Witness :=")
        out.append("  [" + ",\n   ".join(ws) + "]")
        out.append("")
        out.append(f"/-- No certificate for `{p}/{q}`, `ν = {nus}`, with primes inside a listed set. -/")
        out.append(f'@[category research solved, AMS 11 37, ref "Oda26", group "dubc2_obstruction"]')
        out.append(f"theorem {name}_killed : ∀ w ∈ {name}, ∀ (P : Params) (C : Cert), P.p = {p} →")
        out.append(f"    P.q = {q} → P.a = {a} → P.b = {b} → (∀ l ∈ P.PM, l ∈ w.PM) →")
        out.append(f"    (∀ l ∈ P.Pq, l ∈ w.Pq) → ¬ Checked P C :=")
        out.append(f"  not_checked_of_row (by decide +kernel)")
        out.append("")
    out.append("end DubC2.Gen.ObsAtlas")
    open(path, "w").write("\n".join(out) + "\n")


if __name__ == "__main__":
    main()
