import sys; sys.path.insert(0, __import__('os').path.dirname(__import__('os').path.abspath(__file__)))
from entcert import *
from fractions import Fraction
def check(m, sets, trans, w, a, b):
    assert sets[0] == (1 << m.nV) - 1
    for i, S in enumerate(sets):
        assert w[i] >= 1
        for t in range(m.nA):
            for k in range(m.nV):
                if (S >> k) & 1:
                    for k2 in m.succList(k, m.letter(t)):
                        j = trans[i][t]; assert j is not None and (sets[j] >> k2) & 1
        s = sum(w[j] for j in trans[i] if j is not None)
        assert b * s <= a * w[i]
def emit(name, p, q, a_, b_, P, D, a, b, doc):
    m = LeanModel(p, q, a_, b_, P, D); sets, trans = dfa(m)
    w = vcert(trans, a, b); assert w is not None
    check(m, sets, trans, w, a, b)
    print(f"-- {name}: states {len(sets)}, lam {lam_np(trans):.6f}, a/b {a/b:.6f}, max w {max(w)}", file=sys.stderr)
    tr = "[" + ",\n    ".join("[" + ", ".join("none" if j is None else f"some {j}" for j in row) + "]" for row in trans) + "]"
    L = lambda xs: "[" + ", ".join(map(str, xs)) + "]"
    return (f"/-- {doc} -/\ndef {name}P : Params where\n  p := {m.p}\n  q := {m.q}\n  a := {m.a}\n  b := {m.b}\n  D := {m.D}\n  M := {m.M}\n"
            f"  qinv := {m.qinv}\n  PM := {L(m.PM)}\n  Pq := {L(m.Pq)}\n  sLo := {m.sLo}\n  nA := {m.nA}\n\n"
            f"/-- The subset automaton and its weights. -/\ndef {name}E : EntCert where\n  sets := {L(sets)}\n  trans := {tr}\n  w := {L(w)}\n  a := {a}\n  b := {b}\n\n"
            f"theorem {name}_check : {name}E.check {name}P = true := by decide +kernel\n")
out = []
out.append(emit("ent32_2_5", 3,2,0,1,[2,5],2, 53,40, "`(3/2, ν = 0, {2,5})`, `D = 2`."))
out.append(emit("ent32_2_5_7", 3,2,0,1,[2,5,7],2, 109,90, "`(3/2, ν = 0, {2,5,7})`, `D = 2`."))
out.append(emit("ent32_2_7", 3,2,0,1,[2,7],8, 9,7, "`(3/2, ν = 0, {2,7})`, `D = 8`."))
open(sys.argv[1] if len(sys.argv) > 1 else 'data.lean','w').write("\n".join(out))
