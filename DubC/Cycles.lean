/-
(C) 2026 Ralf Stephan, in collaboration with Claude Code.
Released under CC0 1.0 Universal (public-domain dedication).
See https://creativecommons.org/publicdomain/zero/1.0/
-/
import DubC.Rungs
import DubC.Y31

/-!
# From the core to the cycles, and the `a = 7` theorem

`DubC/Rungs.lean` ends at the **core** of the base-`7` coprimality subshift modulo
`∏_{p≤31} p`: the `371 702` residues with an admissible path in both directions
(`DubC.Rungs.cc4`).  `DubC/Y31.lean` needs something smaller — the `365 761` residues that
actually lie on a cycle, which is where `DubC.CoreDet` holds (`DubC.Y31.coreDet_seven`); on the
core it fails, because `147` core states have two core successors.

The gap is the `5 941` core states that are *transient*: they sit on a path from one cycle to
another.  Ruling out a cycle through them is one more rank certificate, and this time the
candidate set is small enough that the rank is genuinely a condensation height rather than a
peeling depth.

## The rank

On the core, weight an edge `r → t` by `0` when both ends are cycle states and by `1` otherwise,
and let `ρ r` be the longest weighted path out of `r`.  Then

* `ρ` never increases along a core edge (all weights are `≥ 0`), and
* out of a state that is **not** a cycle state every edge has weight `1`, so `ρ` strictly drops.

A cycle avoiding `K` would therefore give `ρ r < ρ r`.  The construction is well defined exactly
because there is no such cycle, so a divergent relaxation would be a *failure* of the check and
not a wrong answer — the certificate is verified against the array that comes out, whatever it
is.  It converges here, with `ρ ≤ 241`.

`DubC.Cycles.condRank` computes it by worklist relaxation over the reverse edges of the core.
Note that this needs the cycle set only to *weight* the edges: nothing is assumed about
`DubC.Y31.KA` here either.

## The result

`DubC.Cycles.infinite_composites_seven` — for every real `ξ > 0` the sequence `⌊ξ·7ⁿ⌋` contains
infinitely many composite terms.  Its inputs are `DubC.Rungs.cc4` (this ladder),
`DubC.Y31.coreDet_seven` (the determinism check) and the reduction of
`DubC/CoreCertificate.lean` resting on **[Dub09] Theorem 4**, itself proved in
`DubC/ReturnEngine.lean`.

## References

* **[Dub09]** A. Dubickas, *Prime and composite integers close to powers of a number*,
  Monatsh. Math. **158** (2009) 271–284.
* **[DubOst06]** A. Dubickas, *Truncatable primes and unavoidable sets of divisors*,
  Acta Math. Univ. Ostrav. **14** (2006) 21–25.
-/

namespace DubC
namespace Cycles

open Engine Rungs

/-! ### A rank check with explicit candidate and target sets -/

/-- The rank obligation at one state.  Unlike `DubC.rungChkF` the two sets are given directly,
because here the target set is the cycle set of `DubC/Y31Data.lean` and not something the
peeling produced. -/
def rankChk (M : ℕ) (Cn Kn : ℕ → Bool) (rho : ℕ → ℕ) (x : ℕ) : Bool :=
  if !Cn x then true else
  let rx := rho x
  let kx := Kn x
  allLt 7 fun d =>
    if d == 0 then true
    else if (x + d) % 2 != 1 then true
    else
      let y := (7 * x + d) % M
      if Cn y then decide (rho y ≤ rx) && (kx || decide (rho y < rx)) else true

@[category API, AMS 11 37, ref "Dub09", group "dubc_cycles"]
theorem rankChk_spec {M : ℕ} {Cn Kn : ℕ → Bool} {rho : ℕ → ℕ} {x : ℕ}
    (h : rankChk M Cn Kn rho x = true) (hx : Cn x = true) :
    ∀ d < 7, d ≠ 0 → (x + d) % 2 = 1 → Cn ((7 * x + d) % M) = true →
      rho ((7 * x + d) % M) ≤ rho x ∧ (Kn x = false → rho ((7 * x + d) % M) < rho x) := by
  intro d hd hd0 hpar hy
  rw [rankChk, hx] at h
  simp only [Bool.not_true, Bool.false_eq_true, ↓reduceIte] at h
  have hb := allLt_spec h d hd
  simp only [beq_iff_eq, hd0, ↓reduceIte, hpar, bne_self_eq_false, Bool.false_eq_true, hy,
    Bool.and_eq_true, Bool.or_eq_true, decide_eq_true_eq] at hb
  refine ⟨hb.1, fun hK => ?_⟩
  rcases hb.2 with hk | hlt
  · simp [hK] at hk
  · exact hlt

/-! ### The condensation rank on the core -/

/-- Cycle-set membership of the core states, indexed as `DubC.Engine.compact` indexes them
(`1`-based, slot `0` unused). -/
def isCyc : ByteArray := Id.run do
  let n := D4.L.S.size
  let mut a : ByteArray := ByteArray.mk (Array.replicate (n + 1) 0)
  for i in [0:n] do
    if Y31.bmem Y31.KA (D4.L.S[i]!) then a := a.set! (i + 1) 1
  return a

/-- The longest weighted path out of each core state, by worklist relaxation over the reverse
edges.  Edge weight `0` exactly between two cycle states.

`z` is always `0` (see `DubC.Cycles.condRank`).  It is here only to keep this a *function*.
Measured 2026-08-08: with this loop inlined into the body of a nullary constant the evaluator
does not finish it in `323 s`; the byte-identical body as a function takes `10 s`.  It is not
`Id` versus `IO`, and not the `isCyc` reference inside the loop — hoisting that changes nothing.
The rest of the development is safe by accident: `DubC/Engine.lean`'s heavy loops all take
arguments, and `DubC.Rungs.D0 … D4` are nullary but their bodies are applications of those. -/
def condRankAux (z : ℕ) : Array ℕ := Id.run do
  let n := D4.L.S.size + z
  let SU := D4.L.SU
  -- reverse edges, in compressed-row form
  let mut start : Array ℕ := Array.replicate (n + 1) 0
  for e in [0:3 * n] do
    let s := SU[e]!
    if s != 0 then start := start.modify (s - 1) (· + 1)
  let mut acc := 0
  for g in [0:n + 1] do
    let c := start[g]!
    start := start.set! g acc
    acc := acc + c
  let mut fill : Array ℕ := Array.replicate n 0
  for g in [0:n] do fill := fill.set! g (start[g]!)
  let mut lst : Array ℕ := Array.replicate acc 0
  for g in [0:n] do
    for e in [0:3] do
      let s := SU[3 * g + e]!
      if s != 0 then
        let t := s - 1
        lst := lst.set! (fill[t]!) g
        fill := fill.set! t (fill[t]! + 1)
  -- relaxation
  let mut rho : Array ℕ := Array.replicate (n + 1) 0
  let mut mark : ByteArray := ByteArray.mk (Array.replicate n 0)
  let mut cur : Array ℕ := Array.range n
  for _ in [0:4000000] do
    if cur.isEmpty then break
    for i in cur do mark := mark.set! i 0
    let mut nxt : Array ℕ := #[]
    for i in cur do
      let ki := isCyc.get! (i + 1)
      let mut best := 0
      for e in [0:3] do
        let s := SU[3 * i + e]!
        if s != 0 then
          let j := s - 1
          let w := if ki == 1 && isCyc.get! (j + 1) == 1 then 0 else 1
          let v := rho[j + 1]! + w
          if v > best then best := v
      if best > rho[i + 1]! then
        rho := rho.set! (i + 1) best
        for q in [start[i]!:start[i + 1]!] do
          let pn := lst[q]!
          if mark.get! pn == 0 then
            mark := mark.set! pn 1
            nxt := nxt.push pn
    cur := nxt
  return rho

/-- The condensation rank.  Nothing about it is assumed: `DubC.Cycles.chkCyc` verifies the array
that comes out, whatever it is, so the `z = 0` indirection is invisible to every proof. -/
def condRank : Array ℕ := condRankAux 0

/-- The rank as a function of a residue: `0` off the core, where it is never consulted. -/
def rhoC (y : ℕ) : ℕ := condRank.getD (D4.RK.getD (inf4 y).1 0) 0

/-- The target set: the `365 761` cycle states of `DubC/Y31Data.lean`. -/
def cycK (y : ℕ) : Bool := Y31.bmem Y31.KA y

/-! ### The check -/

def chkCyc : Bool := loop4 fun x => rankChk M4 cnK4 cycK rhoC x

@[category API, AMS 11 37, ref "Dub09", group "dubc_cycles"]
theorem chkCyc_true : chkCyc = true := by native_decide

/-! ### The certificate -/

/-- **Every residue lying on a cycle of the base-`7` coprimality subshift modulo `∏_{p≤31} p` is
one of the `365 761` states of `DubC/Y31Data.lean`.**

This is the hypothesis `DubC.Y31.infinite_composites_seven_of_coreClosed` was waiting for. -/
@[category research solved, AMS 11 37, ref "Dub09" "DubOst06", group "dubc_cycles"]
theorem coreClosed_seven : CoreClosed 7 primorial31 Y31.Kset := by
  refine coreClosed_of_rankNat (by norm_num [M4, primorial31]) (by norm_num [M4, primorial31])
    cnK4 cycK rhoC cc4 ?_
  intro x hx hcx d hd hd0 hpar hy
  exact rankChk_spec (loop4_spec chkCyc_true x hx (and_left (and_left hcx))) hcx d hd hd0 hpar hy

/-! ### The payoff -/

/-- **The `a = 7` case of the 1967 Forman–Shapiro problem.**  For every real `ξ > 0` the
sequence `⌊ξ·7ⁿ⌋` contains infinitely many composite terms.

Both halves of the compressed-core certificate at `𝒫 = {p ≤ 31}` are now theorems:
`DubC.Cycles.coreClosed_seven` (every cycle is caught, via the ladder of `DubC/Rungs.lean`) and
`DubC.Y31.coreDet_seven` (the caught set is deterministic).  The reduction from there is
`DubC/CoreCertificate.lean`, resting on [Dub09] Theorem 4 as proved in
`DubC/ReturnEngine.lean`. -/
@[category research solved, AMS 11 37, ref "Dub09" "DubOst06", group "dubc_cycles"]
theorem infinite_composites_seven {ξ : ℝ} (hξ : 0 < ξ) :
    {n | CompositeInt (floorPow ξ 7 n)}.Infinite :=
  Y31.infinite_composites_seven_of_coreClosed coreClosed_seven hξ

end Cycles
end DubC
