#!/usr/bin/env python3
# (C) 2026 Ralf Stephan, in collaboration with Claude Code.  CC0 1.0.
#
# verify_pressure.py -- plan-B10 WP4': an INDEPENDENT re-check of the exponent
# brackets shipped as Lean theorems in `Z32/Pressure.lean`.
#
# The numbers under test are READ OUT OF THE LEAN SOURCE, not recomputed by the
# generator that produced them: the script parses each `bowen_*_mem_Icc` and
# `flatto_*_mem_Icc` instance, recovers the window, the claimed interval, and the
# six numbers `(u, v, n1, d1, n2, d2)` fed to the generic lemma, and then runs
# four checks by routes that do not share code with `Z32/pressure.py`.
#
#  (P1) THE INTERVAL IS THE ONE STATED.  The Icc endpoints in the theorem must be
#       exactly n1/d1 and n2/d2 -- i.e. the displayed bracket is the one the
#       power inequalities actually certify, with no transcription drift.
#
#  (P2) THE POWER INEQUALITIES HOLD.  r^n1 <= u^d1 and v^d2 <= r^n2, in exact
#       integer arithmetic, cross-multiplied.  These are the two facts `norm_num`
#       discharges in the kernel; re-doing them here catches a wrong literal that
#       happens to still typecheck (both inequalities can hold for a bracket that
#       is merely valid, so P3/P4 below are what pin it to the right window).
#
#  (P3) THE RATIONALS BRACKET THE CERTIFICATE.  u <= lambda_lo and
#       lambda_hi <= v, against a certificate rebuilt from the window alone.
#       This is the step that ties the exponent bracket to *this* window rather
#       than to some other one.
#
#  (P4) THE BRACKET IS HONEST.  The type graph is re-derived here from the
#       transition rule (a forward closure on right endpoints, in Fractions --
#       no scaling, no common denominator, none of the generator's integer
#       machinery), the growth rate is measured as a ratio of two exact
#       big-integer path counts at depth 400, and log(growth)/log(base) is
#       checked to lie inside the claimed interval.
#
#   ./verify_pressure.py            # every instance in Z32/Pressure.lean

import re
import sys
from decimal import Decimal, getcontext
from fractions import Fraction as F

sys.path.insert(0, __file__.rsplit("/", 1)[0])
import entcert                                    # only for lambda_lo/lambda_hi

getcontext().prec = 80

LEAN = __file__.rsplit("/", 1)[0] + "/Pressure.lean"

THM = re.compile(
    r"theorem\s+(bowen|flatto)_(\w+?)_mem_Icc\s*:\s*"
    r"(?:modelBowen|flattoExponent)\s*\(Set\.Ico\s*\(0\s*:\s*ℝ\)\s*\((\d+)\s*/\s*(\d+)\)\)\s*∈\s*"
    r"Set\.Icc\s*\(\((\d+)\s*:\s*ℝ\)\s*/\s*(\d+)\)\s*\(\((\d+)\s*:\s*ℝ\)\s*/\s*(\d+)\)\s*:=\s*by"
    r"(.*?)(?=\n/--|\n@\[|\Z)", re.S)

ARG = re.compile(r"\((\w+)\s*:=\s*([\d/\s]+?)\)")


def type_graph(ell):
    """(P4) the reachable type set and its transitions, from the rule alone."""
    seen, stack, edges = {ell}, [ell], []
    while stack:
        t = stack.pop()
        for s in (0, 1):
            c = min(ell, (3 * t - s) / 2)
            if c > 0:
                edges.append((t, s, c))
                if c not in seen:
                    seen.add(c)
                    stack.append(c)
        if len(seen) > 5000:
            raise SystemExit(f"type set of {ell} did not close")
    return sorted(seen), edges


def growth(ell, depth=400):
    """Exact ratio of consecutive path counts from the root -- no eigenvalues."""
    states, edges = type_graph(ell)
    idx = {t: i for i, t in enumerate(states)}
    rows = [[] for _ in states]
    for (t, _s, c) in edges:
        rows[idx[t]].append(idx[c])
    vec = [1] * len(states)
    for _ in range(depth - 1):
        vec = [sum(vec[j] for j in r) for r in rows]
    prev = vec[idx[ell]]
    vec = [sum(vec[j] for j in r) for r in rows]
    return F(vec[idx[ell]], prev), len(states)


def dlog(x: F) -> Decimal:
    return (Decimal(x.numerator) / Decimal(x.denominator)).ln()


def pow_le(u: F, i: int, v: F, j: int) -> bool:
    return u.numerator ** i * v.denominator ** j <= v.numerator ** j * u.denominator ** i


def check(kind, name, ell, claimed, args, verbose=True):
    fails = []

    def want(cond, msg):
        if not cond:
            fails.append(msg)

    r = F(3, 2) if kind == "bowen" else F(2, 1)
    u, v = F(args["u"]), F(args["v"])
    n1, d1 = int(args["n₁"]), int(args["d₁"])
    n2, d2 = int(args["n₂"]), int(args["d₂"])

    # ---- P1
    want(claimed == (F(n1, d1), F(n2, d2)),
         f"P1: displayed interval {claimed} != ({F(n1,d1)}, {F(n2,d2)})")

    # ---- P2
    want(pow_le(r, n1, u, d1), f"P2: r^{n1} <= u^{d1} is false")
    want(pow_le(v, d2, r, n2), f"P2: v^{d2} <= r^{n2} is false")

    # ---- P3
    c = entcert.build(ell.numerator, ell.denominator)
    want(u <= c["lam_lo"], f"P3: u = {u} exceeds lambda_lo = {c['lam_lo']}")
    want(c["lam_up"] <= v, f"P3: v = {v} below lambda_hi = {c['lam_up']}")

    # ---- P4
    g, nstates = growth(ell)
    e = dlog(g) / dlog(r)
    want(Decimal(n1) / Decimal(d1) <= e <= Decimal(n2) / Decimal(d2),
         f"P4: measured exponent {e} outside [{F(n1,d1)}, {F(n2,d2)}]")

    if verbose:
        tag = "OK  " if not fails else "FAIL"
        print(f"{tag} {kind:6s} ell={str(ell):8s} states={nstates:4d} base={r} "
              f"[{n1}/{d1}, {n2}/{d2}] = [{float(F(n1,d1)):.9f}, {float(F(n2,d2)):.9f}] "
              f"measured={float(e):.9f}")
        for f in fails:
            print(f"       !! {f}")
    return fails


def main():
    src = open(LEAN).read()
    total, seen = 0, 0
    for m in THM.finditer(src):
        kind, name = m.group(1), m.group(2)
        ell = F(int(m.group(3)), int(m.group(4)))
        claimed = (F(int(m.group(5)), int(m.group(6))),
                   F(int(m.group(7)), int(m.group(8))))
        args = {k: val.replace(" ", "") for k, val in ARG.findall(m.group(9))}
        for key in ("u", "v", "n₁", "d₁", "n₂", "d₂"):
            if key not in args:
                print(f"FAIL {kind}_{name}: could not read `{key}` from the proof")
                total += 1
        seen += 1
        total += len(check(kind, name, ell, claimed, args))
    if seen != 14:
        print(f"FAIL: parsed {seen} instances, expected 14")
        total += 1
    print(f"\n{'ALL EXPONENT BRACKETS VERIFIED' if not total else str(total)+' FAILURES'}")
    return 1 if total else 0


if __name__ == "__main__":
    sys.exit(main())
