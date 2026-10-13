#!/usr/bin/env python3
# (C) 2026 Ralf Stephan, in collaboration with Claude Code.  CC0 1.0.
#
# xblocks.py -- cycle certificates for DubC2/GenBlocks.lean (Gen.CycChecked), read from the
# atlas certificates' Data.lean, with exactly the Lean semantics of keep / kf / next / fstep:
#   keep i  = letter indices t with trans[i][t] = some j and rank[j] = rank[i]
#   kf i    = head of keep i (0 if empty);  next i t = trans[i][t] or 0;  fstep i = next i (kf i)
# Emits the word list W (primitive roots), the listed fstep-cycles (states, word index, rotation)
# and a potential that drops along fstep off the cycles.
import os, sys, json
HERE = os.path.dirname(os.path.abspath(__file__))
sys.path.insert(0, HERE)
from xcensus import parse_data, canon, prim_root

def cert(name):
    d = parse_data(os.path.join(HERE, "Atlas", name, "Data.lean"))
    trans, rank, sLo, nA = d["trans"], d["rank"], d["sLo"], d["nA"]
    n = len(trans)
    rk = lambda j: rank[j] if j < len(rank) else 0
    def nxt(i, t):
        row = trans[i] if i < len(trans) else []
        v = row[t] if t < len(row) else None
        return 0 if v is None else v
    keep = [[t for t in range(nA) if t < len(trans[i]) and trans[i][t] is not None
             and rk(trans[i][t]) == rk(i)] for i in range(n)]
    kf = [k[0] if k else 0 for k in keep]
    fs = [nxt(i, kf[i]) for i in range(n)]
    good = [bool(k) for k in keep]
    # fstep cycles among good states
    cycles, onc = [], set()
    for i in range(n):
        seen, j = [], i
        while good[j] and j not in seen and j not in onc:
            seen.append(j); j = fs[j]
        if good[j] and j in seen:
            c = seen[seen.index(j):]
            cycles.append(c); onc.update(c)
    W = []
    out = []
    for c in cycles:
        word = tuple(sLo + kf[i] for i in c)
        root = canon(prim_root(word))
        if root not in W:
            W.append(root)
        wi = W.index(root)
        L = len(root)
        r = next(r for r in range(L) if all(word[j] == root[(r + j) % L] for j in range(len(word))))
        out.append((c, wi, r))
    listed = lambda i: i in onc
    pot = [None] * n
    def P(i, depth=0):
        if pot[i] is not None:
            return pot[i]
        assert depth <= n, "potential: unlisted cycle"
        j = fs[i]
        if listed(i) or not good[i] or rk(j) != rk(i) or listed(j):
            pot[i] = 0
        else:
            pot[i] = P(j, depth + 1) + 1
        return pot[i]
    for i in range(n):
        P(i)
    return [list(w) for w in W], [(c, wi, r) for c, wi, r in out], pot

def lean_lists(name, W, cyc, pot):
    Ws = "[" + ", ".join("[" + ", ".join(str(a) for a in w) + "]" for w in W) + "]"
    cs = "[" + ",\n    ".join(f"([{', '.join(map(str, c))}], {wi}, {r})" for c, wi, r in cyc) + "]"
    ps = "[" + ", ".join(map(str, pot)) + "]"
    return Ws, cs, ps

if __name__ == "__main__" and (len(sys.argv) < 2 or not sys.argv[1].startswith("--")):
    for name in sys.argv[1:]:
        W, cyc, pot = cert(name)
        print(name, "W =", W, "cycles", [(len(c), wi, r) for c, wi, r in cyc], "maxpot", max(pot))
        print(json.dumps(dict(name=name, W=W, cyc=cyc, pot=pot)))


# ---------------------------------------------------------------- Lean emission (DubC2/Blocks.lean)

from fractions import Fraction
from xcensus import Census, frac

CELLS = [
    ("b7_5_nu1_2_P2_3_5_13", "seven_fifths_two_three_five_thirteen",
     "Base `7/5`, `ν = 1/2`, `𝒫 = {2,3,5,13}`"),
    ("b3_2_nu0_P2_7_11_13", "floor_three_halves_two_seven_eleven_thirteen",
     "Floor `3/2`, `𝒫 = {2,7,11,13}`"),
    ("b3_2_nu0_P3_5_7_11", "floor_three_halves_three_five_seven_eleven",
     "Floor `3/2`, `𝒫 = {3,5,7,11}`"),
]


def exact_orbit(e, w):
    p, q = e["p"], e["q"]
    a, b = frac(e["nu"])
    c = Fraction((p - q) * a, b)
    al, be = Fraction(1), Fraction(0)
    for s in w:
        al, be = al * Fraction(p, q), (p * be - s - c) / q
    y = be / (1 - al)
    ys = []
    for s in w:
        ys.append(y)
        y = (p * y - s - c) / q
    assert y == ys[0]
    return ys


def qlit(f):
    return f"({f.numerator} : ℚ)" if f.denominator == 1 else f"({f.numerator} / {f.denominator} : ℚ)"


def zlist(ws):
    return "[" + ", ".join(str(a) for a in ws) + "]"


def emit():
    reg = {e["name"]: e for e in json.load(open(os.path.join(HERE, "Atlas", "registry.json")))}
    out = []
    for name, thm, title in CELLS:
        e = reg[name]
        W, cyc, pot = cert(name)
        real, arts = [], []
        for w in W:
            ys = exact_orbit(e, w)
            (arts if any(v < 0 or v >= 1 for v in ys) else real).append((w, ys))
        order = [w for w, _ in real] + [w for w, _ in arts]
        remap = {tuple(w): order.index(w) for w in W}
        cyc2 = [(c, remap[tuple(W[wi])], r) for c, wi, r in cyc]
        Wr = "[" + ",\n      ".join(zlist(w) for w, _ in real) + "]"
        At = "[" + ",\n    ".join(f"({zlist(w)}, [{', '.join(qlit(v) for v in ys)}])"
                                   for w, ys in arts) + "]"
        Cy = "[" + ",\n    ".join(f"([{', '.join(map(str, c))}], {wi}, {r})" for c, wi, r in cyc2) + "]"
        Po = "[]" if not any(pot) else "[" + ", ".join(map(str, pot)) + "]"
        Pn, Cn = f"{name}P", f"{name}C"
        out.append(dict(name=name, thm=thm, title=title, Wr=Wr, At=At, Cy=Cy, Po=Po, Pn=Pn, Cn=Cn,
                        real=[w for w, _ in real], arts=[(w, ys) for w, ys in arts]))
    return out


if __name__ == "__main__" and len(sys.argv) > 1 and sys.argv[1] == "--emit":
    pass


HEADER = """/-
(C) 2026 Ralf Stephan, in collaboration with Claude Code.
Released under CC0 1.0 Universal (public-domain dedication).
See https://creativecommons.org/publicdomain/zero/1.0/
-/
"""

DOC = """/-!
# The surviving words at three atlas cells (generated by `DubC2/xblocks.py`; do not edit)

Claim C‑8 of `plans/plan-dubC2-transform.html` (balanced words) is refuted by the X‑C census
(`plans/note-dubC2T-M0.html` §6); what survives is a **block structure**.  At `7/5`
`{2,3,5,11}` and floor `3/2` `{2,5,7,11}` it was already proved by the hand chains
(`DubC2.AC.isEventuallyPeriodic`, `DubC2.FS.isEventuallyPeriodic`).  Here it is proved at the
three remaining cells, in its strongest form: **every avoiding pseudo-orbit (`DubC2.Gen.Pseudo`)
eventually reads one explicit word forever**, a rotation of one of the listed words.

| cell | surviving words (`A,C` resp. `−1 = A`, `1 = B`) |
|---|---|
| `7/5`, `ν = 1/2`, `{2,3,5,13}` | `(AC²)^∞`, `(AC·AC³·AC²)^∞` (`A = −4`, `C = 2`) and their mirrors (`−2,−2,4` …) |
| floor `3/2`, `{2,7,11,13}` | `(AB²·AB²·AB²·AB⁶)^∞` |
| floor `3/2`, `{3,5,7,11}` | `(AB²·AB⁴)^∞`, `(AB²·AB²·AB²·AB⁶)^∞`, `(AB²·A2·AB³·A2)^∞` (letter `2` too) |

Method (`DubC2/GenBlocks.lean`): the atlas certificate's det automaton, once its rank stops
dropping, follows the rank-keeping successor; the listed `fstep` cycles and a potential are
checked by `decide`, and the det cycles whose exact orbit leaves `[0,1)` — the constant word `1`
(fixed point `y = 1`) and, at `{3,5,7,11}`, one word of length 22 — are excluded by
`Gen.Pseudo.not_artefact`.  For real orbits these statements are vacuous (the atlas theorems say
no real orbit avoids `𝒫`); they are statements about the certificate's pseudo-orbit model,
which is not empty (the census lists its periodic members).
-/
"""


def lean_file():
    cells = emit()
    imports = "".join(f"import DubC2.Atlas.{c['name']}.Main\n" for c in cells)
    body = [HEADER + "import DubC2.GenBlocks\n" + imports + "\n" + DOC,
            "namespace DubC2.Blocks\n\nopen DubC2.Gen DubC2.Atlas\n"]
    for c in cells:
        n = c["name"]
        body.append(f"""/-! ## {c['title']} -/

/-- The listed `fstep` cycles of `{n}C`: (states, word index, rotation). -/
def {n}_cyc : List (List ℕ × ℕ × ℕ) :=
  {c['Cy']}

/-- The potential of `{n}C` (empty = zero: every rank-keeping state is on a listed
cycle). -/
def {n}_pot : List ℕ := {c['Po']}

/-- The grid artefacts of `{n}C`, each with its exact orbit. -/
def {n}_arts : List (List ℤ × List ℚ) :=
  {c['At']}

/-- **{c['title']}: every avoiding pseudo-orbit eventually reads one of
the listed words forever.** -/
@[category research solved, AMS 11 37 68, ref "DN05", group "dubc2_blocks"]
theorem {c['thm']} {{x : ℕ → ℤ}} {{y : ℕ → ℝ}} {{s : ℕ → ℤ}}
    (h : Pseudo {c['Pn']} x y s) :
    ∃ n₀, ∃ w ∈ ({c['Wr']} : List (List ℤ)), ∃ r,
      ∀ m, s (n₀ + m) = w.getD ((r + m) % w.length) 0 :=
  h.eventually_realized_word {n}_checked (arts := {n}_arts) (cyc := {n}_cyc)
    (pot := {n}_pot) ⟨by decide +kernel, by decide +kernel⟩ (by decide +kernel)
""")
    body.append("end DubC2.Blocks\n")
    return "\n".join(body)


if __name__ == "__main__" and len(sys.argv) > 1 and sys.argv[1] == "--lean":
    open(os.path.join(HERE, "Blocks.lean"), "w").write(lean_file())
    print("wrote DubC2/Blocks.lean")
