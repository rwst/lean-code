/-
(C) 2026 Ralf Stephan, in collaboration with Claude Code.
Released under CC0 1.0 Universal (public-domain dedication).
See https://creativecommons.org/publicdomain/zero/1.0/
-/
import DubC.Y31Data
import DubC.Verdict

/-!
# The `y = 31` certificate, checked by a certified checker under `native_decide`

This file discharges the *local* half of the compressed-core certificate for `a = 7` at the
modulus `DubC.primorial31 = ∏_{p≤31} p ≈ 2·10¹¹`: the set `K` of the 365 761 cycle states is
**deterministic** — each of its members has at most one successor inside `K`
(`DubC.Y31.coreDet_seven`).

## The trust cost, stated honestly

`native_decide` compiles a `Bool`-valued term and runs it, so the trusted base grows by the Lean
compiler and the axiom recording that run.  This is **not** a debt that can be paid off: it
would take a verified Lean compiler, which does not exist and is not a realistic project.  The
only real alternative is a *kernel-checked* evaluator, and Lean has one — `cbv`, which mimics
call-by-value evaluation while constructing a proof term ("the proofs produced by `cbv` only use
the three standard axioms; in particular, they do not require trust in the correctness of the
code generator").

`cbv` was measured on this problem and does not reach it, by two independent margins.

* **Proof-term size.** A `cbv` evaluation costs about 118 kB of memory per reduction step here
  (measured at 5 000 / 10 000 / 20 000 steps of the residue walk: 3.82 / 4.41 / 5.59 GB, linear).
  The 365 761-step cycle walk alone would need ≈ 43 GB — more than this machine has — *before*
  any membership work.  Time is ≈ 2.4 ms/step, so ≈ 15 min for the same walk; that part would be
  tolerable, the memory is not.
* **Random access.** `cbv` represents arrays as terms, so an index costs a traversal: ≈ 1.5 s per
  lookup into a 10 000-element array.  This check needs ≈ 2.5 M lookups into a 365 761-element
  array.

That is the same wall the kernel hits (`Array` reduces structurally), for the same reason, with
a proof-term wall stacked on top.  So the choice here is not "compiler trust versus no compiler
trust" but "compiler trust versus no theorem", and the response is to *quarantine* rather than
eliminate: this file is the only one in `DubC/` that leaves the three standard axioms, nothing
axiom-free imports it, and `#print axioms` names the dependency at every use site.

What the design does eliminate is everything else:

* **The witness data is untrusted.**  `K` is *defined* as "what `DubC.Y31.bmem` answers on what
  `DubC.cyclesData` decodes to".  It is not claimed to be the cycle set, or to be sorted, or to
  be anything at all.  A corrupted entry, a wrong residue, an unsorted array — each can only
  make the check *fail*.  None can make a false theorem provable.
* **The search needs no correctness proof.**  `bmem` is written so that soundness is immediate:
  it computes some index and then *asks the array what is there*, so `bmem a x = true` literally
  exhibits `x` as an element of `a` (`DubC.Y31.bmem_sound`).  Whether the index is the right one
  — whether the binary search is correct at all — is irrelevant.  Completeness is never used.
* **The decoder needs no correctness proof.**  Same reason: it produces the array that *defines*
  `K`.

So the reasoning that has to be believed is exactly `DubC.Y31.detOK_spec` (extracting the
per-state statement from the checker) and the two bridges `DubC.Y31.val_succ` /
`DubC.Y31.forall_of_mem_KA` between `ZMod primorial31` arithmetic and `Nat` arithmetic — all
small, and all checked by the ordinary kernel.

## What remains

`DubC.CoreClosed 7 primorial31 K` — "every residue lying on a cycle is in `K`" — is *not* proved
here.  It is the global half, and `DubC/Ladder.lean` reduces it to a chain of rung checks; that
chain is the next piece.  `DubC.Y31.infinite_composites_seven_of_coreClosed` states the `a = 7`
target with `CoreClosed` as its **only** remaining hypothesis.

Two measured facts shape what that chain has to look like.  First, `K` must be the *cycle set*
and not the pruned core: 147 of the 371 555 core states have two successors inside the core, so
`CoreDet` is false for the core.  Second, the pruning that produces the core is deep — 82, 159,
499 and 319 rounds at the rungs `p = 19, 23, 29, 31` — so the rank function that
`DubC.coreClosed_of_rankOn` wants takes values up to ~500 and is needed at every one of the
22 149 090 candidate states of the last rung.  It is therefore too large to ship as a literal
and has to be *computed* by the checker (which needs no correctness proof, exactly as here — it
is a witness), by a linear-time peeling with reverse adjacency.  That is a substantially larger
engine than this file, and it is not built yet.

## References

* **[Dub09]** A. Dubickas, *Prime and composite integers close to powers of a number*,
  Monatsh. Math. **158** (2009) 271–284.
* **[DubOst06]** A. Dubickas, *Truncatable primes and unavoidable sets of divisors*,
  Acta Math. Univ. Ostrav. **14** (2006) 21–25.
-/

namespace DubC
namespace Y31

/-! ### Decoding the witness (no correctness needed) -/

/-- The states of one cycle, obtained by walking `r ↦ (7r + d) mod M` along the digit word.
Digits are the characters `'2'`, `'4'`, `'6'`. -/
def cycleStates (s : String) : Array Nat :=
  match s.splitOn " " with
  | [a, w] => Id.run do
      let mut out : Array Nat := #[]
      let mut r : Nat := a.toNat!
      for c in w.toList do
        out := out.push r
        r := (7 * r + (c.toNat - 48)) % primorial31
      return out
  | _ => #[]

/-- The witness array: every state of every cycle of `DubC.cyclesData`, sorted. -/
def buildK : Array Nat :=
  (cyclesData.foldl (fun acc s => acc ++ cycleStates s) #[]).qsort (fun a b => decide (a < b))

/-- The set the certificate is about — *by definition* whatever `buildK` produced. -/
def KA : Array Nat := buildK

/-! ### Membership: a search whose soundness is free

`bidx` may return any index whatsoever; `bmem` then asks the array what is stored there.  So a
positive answer *is* a membership witness, and nothing about the search has to be proved. -/

/-- Binary search for an index, with a step budget.  Deliberately unverified. -/
def bidx (a : Array Nat) (x : Nat) : Nat → Nat → Nat → Nat
  | 0, lo, _ => lo
  | fuel + 1, lo, hi =>
    if lo < hi then
      let mid := (lo + hi) / 2
      let v := a[mid]!
      if v == x then mid
      else if v < x then bidx a x fuel (mid + 1) hi
      else bidx a x fuel lo mid
    else lo

/-- Membership test: look up a candidate index and compare what is actually there. -/
def bmem (a : Array Nat) (x : Nat) : Bool := a[bidx a x (a.size + 1) 0 a.size]? == some x

/-- **Soundness of the membership test, and the only thing needed about it.**  No sortedness, no
loop invariant, no completeness: a positive answer exhibits the element. -/
@[category API, AMS 11 37, ref "Dub09", group "dubc_y31"]
theorem bmem_sound {a : Array Nat} {x : Nat} (h : bmem a x = true) : x ∈ a := by
  rw [bmem, beq_iff_eq] at h
  obtain ⟨hlt, he⟩ := Array.getElem?_eq_some_iff.mp h
  exact he ▸ Array.getElem_mem hlt

/-! ### The set `K` and the arithmetic bridge -/

/-- The candidate core: membership in the decoded witness array. -/
def Kset (r : ZMod primorial31) : Prop := bmem KA r.val = true

instance : DecidablePred Kset := fun r => by unfold Kset; infer_instance

/-- The successor of a residue in `Nat` arithmetic. -/
def succN (x d : Nat) : Nat := (7 * x + d) % primorial31

@[category API, AMS 11 37, ref "Dub09", group "dubc_y31"]
theorem val_succ (r : ZMod primorial31) (d : ℕ) :
    (((7 : ℕ) : ZMod primorial31) * r + ((d : ℕ) : ZMod primorial31)).val = succN r.val d := by
  have h : ((7 : ℕ) : ZMod primorial31) * r + ((d : ℕ) : ZMod primorial31)
      = ((7 * r.val + d : ℕ) : ZMod primorial31) := by push_cast; simp
  rw [h, ZMod.val_natCast]
  rfl

@[category API, AMS 11 37, ref "Dub09", group "dubc_y31"]
theorem val_inj {u v : ZMod primorial31} (h : u.val = v.val) : u = v := by
  have : ((u.val : ℕ) : ZMod primorial31) = ((v.val : ℕ) : ZMod primorial31) := by rw [h]
  simpa using this

/-- A statement about every member of `K` reduces to a statement about every entry of the
witness array — this is where `bmem_sound` is used, and the only place. -/
@[category API, AMS 11 37, ref "Dub09", group "dubc_y31"]
theorem forall_of_mem_KA {P : ZMod primorial31 → Prop}
    (h : ∀ r : ZMod primorial31, r.val ∈ KA → P r) :
    ∀ r : ZMod primorial31, Kset r → P r :=
  fun _ hr => h _ (bmem_sound hr)

/-- `Array.all` in the form used below.  Stated for an abstract array: instantiating it at `KA`
before generalising would ask the elaborator to unfold the decoder. -/
@[category API, AMS 11 37, ref "Dub09", group "dubc_y31"]
theorem all_of_mem {a : Array Nat} {p : Nat → Bool} (h : a.all p = true) {x : Nat}
    (hx : x ∈ a) : p x = true := by
  obtain ⟨i, hi, rfl⟩ := Array.mem_iff_getElem.mp hx
  exact Array.all_eq_true.mp h i hi

/-! ### The checker -/

/-- The digits `d < 7` whose successor lands in `K`. -/
def Ksucc (x : Nat) : List Nat := (List.range 7).filter (fun d => bmem KA (succN x d))

/-- The local check at one state: all `K`-successors coincide. -/
def detOK (x : Nat) : Bool :=
  (Ksucc x).all fun d₁ => (Ksucc x).all fun d₂ => succN x d₁ == succN x d₂

/-- The whole check: `detOK` at every state of the witness array. -/
def checkDet : Bool := KA.all detOK

@[category API, AMS 11 37, ref "Dub09", group "dubc_y31"]
theorem detOK_spec {x d₁ d₂ : ℕ} (h : detOK x = true) (h1 : d₁ < 7) (h2 : d₂ < 7)
    (k1 : bmem KA (succN x d₁) = true) (k2 : bmem KA (succN x d₂) = true) :
    succN x d₁ = succN x d₂ := by
  have m1 : d₁ ∈ Ksucc x := List.mem_filter.mpr ⟨List.mem_range.mpr h1, k1⟩
  have m2 : d₂ ∈ Ksucc x := List.mem_filter.mpr ⟨List.mem_range.mpr h2, k2⟩
  have hd := (List.all_eq_true.mp h) d₁ m1
  exact eq_of_beq ((List.all_eq_true.mp hd) d₂ m2)

/-! ### Running it -/

/-- **The certified computation.**  365 761 states, each with seven successor tests against a
365 761-element array. -/
@[category API, AMS 11 37, ref "Dub09", group "dubc_y31"]
theorem checkDet_true : checkDet = true := by native_decide

/-- **`K` is deterministic at `𝒫 = {p ≤ 31}`.**  Every residue of the decoded core has at most
one successor inside it — the local half of the compressed-core certificate for `a = 7`. -/
@[category research solved, AMS 11 37, ref "Dub09" "DubOst06", group "dubc_y31"]
theorem coreDet_seven : CoreDet 7 primorial31 Kset := by
  refine forall_of_mem_KA (fun r hx => ?_)
  intro d₁ hd₁ d₂ hd₂ k1 k2
  have hdet : detOK r.val = true := all_of_mem checkDet_true hx
  refine val_inj ?_
  rw [val_succ, val_succ]
  exact detOK_spec hdet hd₁ hd₂ (by rw [← val_succ]; exact k1) (by rw [← val_succ]; exact k2)

/-! ### The `a = 7` target, with one hypothesis left -/

/-- **The `a = 7` case of the 1967 Forman–Shapiro problem, conditional on `CoreClosed` alone.**
The determinism half is now a theorem (`DubC.Y31.coreDet_seven`), so the only input still
outstanding is the global statement that every residue lying on a cycle of the subshift is in
the decoded core `K` — the half that `DubC/Ladder.lean` reduces to a chain of rung checks. -/
@[category research solved, AMS 11 37, ref "Dub09" "DubOst06", group "dubc_y31"]
theorem infinite_composites_seven_of_coreClosed (hclosed : CoreClosed 7 primorial31 Kset)
    {ξ : ℝ} (hξ : 0 < ξ) : {n | CompositeInt (floorPow ξ 7 n)}.Infinite :=
  infinite_composites_floorPow_of_coreCert (by norm_num) (by norm_num [primorial31])
    Kset hclosed coreDet_seven hξ

end Y31
end DubC
