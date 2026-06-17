/-
(C) 2026 Ralf Stephan, in collaboration with Claude Code.
Released under CC0 1.0 Universal (public-domain dedication).
See https://creativecommons.org/publicdomain/zero/1.0/
-/
import Mathlib.Data.Nat.Basic
import Mathlib.Logic.Function.Iterate
import Corpus.Util.Attributes.Database
import Corpus.Util.Attributes.Basic

/-!
# Antihydra macro model — `BusyLean`-free fragment (for `SRS.AntihydraSRS`)

`SRS.AntihydraMachine` formalises the **Antihydra** BB(6) candidate at the Turing-machine level using
the `BusyLean` framework, and distils its dynamics into a small "high-level" macro model on states
`(a, b) : ℕ × ℕ`. That whole development depends on `BusyLean`, which is not on this project's `lake`
dependency path, so importing `SRS.AntihydraMachine` would break the build of the pure
string-rewriting file `SRS.AntihydraSRS`.

This file re-states **only** the `BusyLean`-free pieces of that macro model that `SRS.AntihydraSRS`
refers to — the macro maps `A` / `nextMathState`, the state `MathState`, the iterate `Aiter`, and the
halting predicate `mathHalts` — together with the deep halting characterization
`mathHalts_iff_Aiter_8_2` as a **cited axiom**. (That equivalence *is* proved in
`SRS.AntihydraMachine` as `Antihydra.mathHalts_iff_Aiter_8_2`, ultimately via the `BusyLean`
TM-simulation `antihydra_halts_iff`; it is taken as an axiom here purely to keep this file independent
of the `BusyLean` module.) The definitions mirror `Antihydra.MathState`, `Antihydra.A`,
`Antihydra.nextMathState`, `Antihydra.Aiter`, `Antihydra.mathHalts` of `SRS.AntihydraMachine`.
-/

namespace StringRewriting.AntihydraSRS

/-- The high-level Antihydra macro state `(a, b)`: a "value" `a` and a "counter" `b`
(mirrors `Antihydra.MathState`). -/
@[category API, AMS 11 68, ref "bbchallenge", group "antihydra_srs"]
structure MathState where
  /-- The value. -/
  a : Nat
  /-- The counter. -/
  b : Nat
deriving Repr, Inhabited, DecidableEq

/-- The **total** Antihydra macro map on `(a, b)` (mirrors `Antihydra.A`): with `n = a / 2`,
even `a` goes to `(3n+2, b+2)` and odd `a` to `(3n+3, b−1)` (the halting condition `b = 0` on the odd
branch is handled by `nextMathState`). -/
@[category API, AMS 11, ref "bbchallenge", group "antihydra_srs"]
def A (ab : ℕ × ℕ) : ℕ × ℕ :=
  let (a, b) := ab
  let n := a / 2
  if a % 2 == 0 then (3 * n + 2, b + 2)
  else              (3 * n + 3, b - 1)

/-- The partial Antihydra macro step with the halting condition (mirrors `Antihydra.nextMathState`):
`none` (HALT) exactly when `a` is odd and the counter `b = 0`; otherwise one application of `A`. -/
@[category API, AMS 11, ref "bbchallenge", group "antihydra_srs"]
def nextMathState (m : MathState) : Option MathState :=
  let n := m.a / 2
  if n ≥ 1 then
    if m.a % 2 == 0 then some { a := 3 * n + 2, b := m.b + 2 }
    else if m.b == 0 then none else some { a := 3 * n + 3, b := m.b - 1 }
  else none

/-- The `i`-th iterate of the total macro map `A` (mirrors `Antihydra.Aiter`). -/
@[category API, AMS 11, ref "bbchallenge", group "antihydra_srs"]
def Aiter (i : ℕ) (ab : ℕ × ℕ) : ℕ × ℕ := A^[i] ab

/-- The Antihydra macro model **halts** from a state when iterating `nextMathState` eventually reaches
the undefined value `none` (mirrors `Antihydra.mathHalts`). -/
@[category API, AMS 11, ref "bbchallenge", group "antihydra_srs"]
inductive mathHalts : MathState → Prop where
  | haltStep (m : MathState) (h : nextMathState m = none) : mathHalts m
  | nextStep (m m' : MathState) (h : nextMathState m = some m') (h' : mathHalts m') : mathHalts m

/-- **Antihydra halting characterization** ([bbchallenge]; `Antihydra.mathHalts_iff_Aiter_8_2`). The
macro model started at the Antihydra initial state `(8, 2)` halts iff some iterate of the total map
`A` reaches an odd value (`> 1`) with an empty counter. **Cited axiom**: this is *proved* in
`SRS.AntihydraMachine` — via the `BusyLean` Turing-machine simulation `Antihydra.antihydra_halts_iff`
— but is recorded here as an axiom to keep this file free of the `BusyLean` dependency. -/
@[category research solved, AMS 11 68, ref "bbchallenge", group "antihydra_srs"]
axiom mathHalts_iff_Aiter_8_2 :
    mathHalts { a := 8, b := 2 } ↔
    ∃ i, (Aiter i (8, 2)).1 % 2 = 1 ∧ (Aiter i (8, 2)).1 / 2 ≥ 1 ∧ (Aiter i (8, 2)).2 = 0

end StringRewriting.AntihydraSRS
