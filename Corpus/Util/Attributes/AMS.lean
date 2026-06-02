/-
Adapted from the Formal Conjectures project (Apache License, Version 2.0):
https://github.com/google-deepmind/formal-conjectures
  FormalConjectures/Util/Attributes/AMS.lean
Changes: ported from the Lean module system (`module` / `public` / `meta`) to
plain Lean 4 for this repository; dropped the unused `numToAMSSubjects`.
-/
import Lean
import Qq

/-! # AMS Subject classification

Defines the `AMS` subject type used by the `AMS` attribute. `AMSDescription.«n»`
exists for each `n ∈ {0, …, 97}` that has a corresponding AMS subject (not all do).
Use the `#AMS` command to print the list of subjects and their indices.
-/

open Lean Elab Meta Qq Command

inductive AMS
  /-- General and overarching topics -/
  | «0»
  /-- History and biography -/
  | «1»
  /-- Mathematical logic and foundations -/
  | «3»
  /-- Combinatorics -/
  | «5»
  /-- Order, lattices, ordered algebraic structures -/
  | «6»
  /-- General algebraic systems -/
  | «8»
  /-- Number theory -/
  | «11»
  /-- Field theory and polynomials -/
  | «12»
  /-- Commutative algebra -/
  | «13»
  /-- Algebraic geometry -/
  | «14»
  /-- Linear and multilinear algebra; matrix theory -/
  | «15»
  /-- Associative rings and algebras -/
  | «16»
  /-- Nonassociative rings and algebras -/
  | «17»
  /-- Category theory; homological algebra -/
  | «18»
  /-- K-theory -/
  | «19»
  /-- Group theory and generalizations -/
  | «20»
  /-- Topological groups, Lie groups -/
  | «22»
  /-- Real functions -/
  | «26»
  /-- Measure and integration -/
  | «28»
  /-- Functions of a complex variable -/
  | «30»
  /-- Potential theory -/
  | «31»
  /-- Several complex variables and analytic spaces -/
  | «32»
  /-- Special functions -/
  | «33»
  /-- Ordinary differential equations -/
  | «34»
  /-- Partial differential equations -/
  | «35»
  /-- Dynamical systems and ergodic theory -/
  | «37»
  /-- Difference and functional equations -/
  | «39»
  /-- Sequences, series, summability -/
  | «40»
  /-- Approximations and expansions -/
  | «41»
  /-- Harmonic analysis on Euclidean spaces -/
  | «42»
  /-- Abstract harmonic analysis -/
  | «43»
  /-- Integral transforms, operational calculus -/
  | «44»
  /-- Integral equations -/
  | «45»
  /-- Functional analysis -/
  | «46»
  /-- Operator theory -/
  | «47»
  /-- Calculus of variations and optimal control; optimization -/
  | «49»
  /-- Geometry -/
  | «51»
  /-- Convex and discrete geometry -/
  | «52»
  /-- Differential geometry -/
  | «53»
  /-- General topology -/
  | «54»
  /-- Algebraic topology -/
  | «55»
  /-- Manifolds and cell complexes -/
  | «57»
  /-- Global analysis, analysis on manifolds -/
  | «58»
  /-- Probability theory and stochastic processes -/
  | «60»
  /-- Statistics -/
  | «62»
  /-- Numerical analysis -/
  | «65»
  /-- Computer science -/
  | «68»
  /-- Mechanics of particles and systems -/
  | «70»
  /-- Mechanics of deformable solids -/
  | «74»
  /-- Fluid mechanics -/
  | «76»
  /-- Optics, electromagnetic theory -/
  | «78»
  /-- Classical thermodynamics, heat transfer -/
  | «80»
  /-- Quantum theory -/
  | «81»
  /-- Statistical mechanics, structure of matter -/
  | «82»
  /-- Relativity and gravitational theory -/
  | «83»
  /-- Astronomy and astrophysics -/
  | «85»
  /-- Geophysics -/
  | «86»
  /-- Operations research, mathematical programming -/
  | «90»
  /-- Game theory, economics, social and behavioral sciences -/
  | «91»
  /-- Biology and other natural sciences -/
  | «92»
  /-- Systems theory; control -/
  | «93»
  /-- Information and communication, circuits -/
  | «94»
  /-- Mathematics education -/
  | «97»
  deriving Inhabited, BEq, Hashable, ToExpr

def numToAMSName (n : Nat) : MetaM Name := do
  let nm : Name := Name.str ``AMS (ToString.toString n)
  unless !(← Lean.hasConst nm) do return nm
  throwError "Out of bounds"

def AMS.getDesc (a : AMS) : CoreM String := do
  let .const n [] := Lean.toExpr a | throwError "this shouldn't happen"
  let .some doc := ← Lean.findDocString? (← getEnv) n | throwError m!"{.ofConstName n} is missing a docstring"
  return doc.trimAscii.toString

def AMS.toNat? (a : AMS) : Option Nat := do
  let .const (.str _ m) [] := Lean.toExpr a | none
  m.toNat?

/-- The `#AMS` command outputs the list of AMS subjects and their indices. -/
elab "#AMS" : command => do
  let env ← Lean.getEnv
  let lines ← (List.range 98).filterMapM fun n => do
    let nm : Name := Name.str ``AMS (ToString.toString n)
    if ← Lean.hasConst nm then
      if let some doc := ← Lean.findDocString? env nm then
        return s!"{n} {doc.trimAscii}"
    return none
  Lean.logInfo ("\n".intercalate lines)
