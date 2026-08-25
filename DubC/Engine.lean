/-
(C) 2026 Ralf Stephan, in collaboration with Claude Code.
Released under CC0 1.0 Universal (public-domain dedication).
See https://creativecommons.org/publicdomain/zero/1.0/
-/

/-!
# The ladder engine

Pure computation: no theorem in this file, and nothing here has to be correct.  It produces the
witnesses — a candidate set, a rank, a re-indexing — that `DubC/Rung.lean`'s certificates are
*checked against*.  A bug in this file can only make the check in `DubC/Rungs.lean` fail; it
cannot make a false statement provable.  That is the same discipline as `DubC/Y31.lean`, applied
to a much larger witness: at the last rung the rank has `2.3·10⁷` entries and values up to about
`700`, so it cannot be shipped and has to be recomputed on the spot.

## Representation

A state at level `M = M' · p` is a pair `(i, k)`: `i` indexes the surviving set at level `M'`
and `k < p` picks the lift, with residue `S'[i] + k·M'`.  The **grid index** is
`(i+1)·p + k`, leaving the slots `0, …, p-1` for "the predecessor died", so that a dead index
never collides with a live one.

The point of this indexing is that the successor is *arithmetic*:

    succ (i, k) d = (SU'[i][d], k')     with   k' = ((7·r + d) mod M) / M'

so no lookup structure is needed and no search ever happens — the successor table at level `M`
is built from the one at level `M'` in `O(1)` per entry.  Only the digits `2, 4, 6` are stored:
an admissible successor is coprime to `M`, hence odd and not a multiple of `7`, which leaves no
other digit.

## Peeling

Both stages are **layered worklists**, so every edge is examined a bounded number of times:
`O(E)` in total rather than `O(E · depth)`.  That matters — the depth reaches `667`, and a
round-by-round rescan costs `3.9·10⁹` state visits where the worklist costs about `10⁸`.

* forward (`peelFwd`): a state dies when its count of live successors hits `0`; propagation is
  along *predecessors*, so it needs the transpose (`transpose`).
* backward (`peelBwd`): a state dies when its count of live predecessors hits `0`; propagation
  is along successors, so it needs no extra structure.

The rank returned is the round at which the state died, capped at `cap` for the survivors —
exactly the potential the rank certificate wants.
-/

namespace DubC
namespace Engine

/-- The rank cap.  Only an efficiency knob: too small a cap merely certifies a larger set (the
survivors of `cap` rounds rather than of all of them), never a wrong one. -/
def CAP : Nat := 1024

/-- A compacted level: modulus, the residues of the surviving states, and their successor table
(three digit slots per state; `0` means "no successor", otherwise the successor's index `+1`). -/
structure Level where
  M : Nat
  S : Array Nat
  SU : Array Nat
  deriving Inhabited

/-- One level lifted by a prime, before peeling: same fields plus the alive flags. -/
structure Grid where
  M : Nat
  S : Array Nat
  SU : Array Nat
  alive : ByteArray
  deriving Inhabited

/-- The bottom of the ladder: every residue mod `M₀`, alive iff a unit.  Here the grid index of
a state *is* its residue. -/
def mkLevel0 (M0 : Nat) : Grid := Id.run do
  let mut S : Array Nat := Array.replicate M0 0
  let mut SU : Array Nat := Array.replicate (3 * M0) 0
  let mut al : ByteArray := ByteArray.mk (Array.replicate M0 0)
  for x in [0:M0] do
    S := S.set! x x
    if Nat.gcd x M0 == 1 then
      al := al.set! x 1
      for e in [0:3] do
        let y := (7 * x + 2 * e + 2) % M0
        if Nat.gcd y M0 == 1 then SU := SU.set! (3 * x + e) (y + 1)
  return { M := M0, S := S, SU := SU, alive := al }

/-- Lift a compacted level by one prime. -/
def mkGrid (L : Level) (p : Nat) : Grid := Id.run do
  let n := L.S.size
  let G := (n + 1) * p
  let Mn := L.M * p
  let mut S : Array Nat := Array.replicate G 0
  let mut SU : Array Nat := Array.replicate (3 * G) 0
  let mut al : ByteArray := ByteArray.mk (Array.replicate G 0)
  for i in [0:n] do
    let ri := L.S[i]!
    let base := (i + 1) * p
    for k in [0:p] do
      let g := base + k
      let r := ri + k * L.M
      S := S.set! g r
      if r % p != 0 then
        al := al.set! g 1
        for e in [0:3] do
          let s := L.SU[3 * i + e]!
          if s != 0 then
            let y := (7 * r + 2 * e + 2) % Mn
            if y % p != 0 then
              SU := SU.set! (3 * g + e) (s * p + y / L.M + 1)
  return { M := Mn, S := S, SU := SU, alive := al }

/-- Predecessor lists in compressed-row form. -/
def transpose (G : Nat) (SU : Array Nat) : Array Nat × Array Nat := Id.run do
  let mut start : Array Nat := Array.replicate (G + 1) 0
  for i in [0:3 * G] do
    let s := SU[i]!
    if s != 0 then start := start.modify (s - 1) (· + 1)
  let mut acc := 0
  for g in [0:G + 1] do
    let c := start[g]!
    start := start.set! g acc
    acc := acc + c
  let mut fill : Array Nat := Array.replicate G 0
  for g in [0:G] do
    fill := fill.set! g (start[g]!)
  let mut lst : Array Nat := Array.replicate acc 0
  for g in [0:G] do
    for e in [0:3] do
      let s := SU[3 * g + e]!
      if s != 0 then
        let t := s - 1
        let pos := fill[t]!
        lst := lst.set! pos g
        fill := fill.set! t (pos + 1)
  return (start, lst)

/-- Forward peeling: kill states with no live successor, layer by layer.  Returns the death
round of every state (`cap` for the survivors) and the surviving flags. -/
def peelFwd (G cap : Nat) (SU : Array Nat) (alive0 : ByteArray) (pStart pList : Array Nat) :
    Array Nat × ByteArray := Id.run do
  let mut al := alive0
  let mut rank : Array Nat := Array.replicate G 0
  let mut cnt : Array Nat := Array.replicate G 0
  let mut layer : Array Nat := #[]
  for g in [0:G] do
    if al.get! g == 1 then
      rank := rank.set! g cap
      let mut c := 0
      for e in [0:3] do
        let s := SU[3 * g + e]!
        if s != 0 && al.get! (s - 1) == 1 then c := c + 1
      cnt := cnt.set! g c
      if c == 0 then layer := layer.push g
  let mut round := 0
  for _ in [0:cap] do
    if layer.isEmpty then break
    let mut nxt : Array Nat := #[]
    for g in layer do
      if al.get! g == 1 then
        al := al.set! g 0
        rank := rank.set! g round
        for q in [pStart[g]!:pStart[g + 1]!] do
          let j := pList[q]!
          if al.get! j == 1 then
            let c := cnt[j]! - 1
            cnt := cnt.set! j c
            if c == 0 then nxt := nxt.push j
    layer := nxt
    round := round + 1
  return (rank, al)

/-- Backward peeling: kill states with no live predecessor, layer by layer. -/
def peelBwd (G cap : Nat) (SU : Array Nat) (alive0 : ByteArray) : Array Nat × ByteArray :=
    Id.run do
  let mut al := alive0
  let mut rank : Array Nat := Array.replicate G 0
  let mut indeg : Array Nat := Array.replicate G 0
  for g in [0:G] do
    if al.get! g == 1 then
      rank := rank.set! g cap
      for e in [0:3] do
        let s := SU[3 * g + e]!
        if s != 0 && al.get! (s - 1) == 1 then indeg := indeg.modify (s - 1) (· + 1)
  let mut layer : Array Nat := #[]
  for g in [0:G] do
    if al.get! g == 1 && indeg[g]! == 0 then layer := layer.push g
  let mut round := 0
  for _ in [0:cap] do
    if layer.isEmpty then break
    let mut nxt : Array Nat := #[]
    for g in layer do
      if al.get! g == 1 then
        al := al.set! g 0
        rank := rank.set! g round
        for e in [0:3] do
          let s := SU[3 * g + e]!
          if s != 0 then
            let j := s - 1
            if al.get! j == 1 then
              let c := indeg[j]! - 1
              indeg := indeg.set! j c
              if c == 0 then nxt := nxt.push j
    layer := nxt
    round := round + 1
  return (rank, al)

/-- Re-index the survivors consecutively.  Returns the map "grid index ↦ new index + 1"
(`0` = did not survive) and the compacted level. -/
def compact (g : Grid) (al : ByteArray) : Array Nat × Level := Id.run do
  let G := g.S.size
  let mut rk : Array Nat := Array.replicate G 0
  let mut m := 0
  for i in [0:G] do
    if al.get! i == 1 then
      m := m + 1
      rk := rk.set! i m
  let mut S : Array Nat := Array.replicate m 0
  let mut SU : Array Nat := Array.replicate (3 * m) 0
  for i in [0:G] do
    let c := rk[i]!
    if c != 0 then
      S := S.set! (c - 1) (g.S[i]!)
      for e in [0:3] do
        let s := g.SU[3 * i + e]!
        if s != 0 then
          let c2 := rk[s - 1]!
          if c2 != 0 then SU := SU.set! (3 * (c - 1) + e) c2
  return (rk, { M := g.M, S := S, SU := SU })

/-- Everything one rung produces: the two rank arrays that the two certificates are checked
against, the re-indexing the next rung needs, and the compacted level. -/
structure RungData where
  F : Array Nat
  B : Array Nat
  RK : Array Nat
  L : Level
  deriving Inhabited

/-- Peel a grid forward, then backward, then compact.  Two stages suffice: the backward
survivors of the forward survivors are exactly the states with an infinite path in both
directions. -/
def runRung (g : Grid) : RungData :=
  let G := g.S.size
  let (ps, pl) := transpose G g.SU
  let (F, alF) := peelFwd G CAP g.SU g.alive ps pl
  let (B, alB) := peelBwd G CAP g.SU alF
  let (rk, L) := compact g alB
  { F := F, B := B, RK := rk, L := L }

end Engine
end DubC
