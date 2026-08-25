/-
(C) 2026 Ralf Stephan, in collaboration with Claude Code.
Released under CC0 1.0 Universal (public-domain dedication).
See https://creativecommons.org/publicdomain/zero/1.0/
-/
import DubC.Certificate

/-!
# The compressed-core certificate

A second certificate form for the subshift of `DubC/Certificate.lean`, carrying **no rank data
at all**.  It asks for a set `K` of residues with two properties:

* **(a) `K` catches every cycle** — every residue lying on a cycle of the subshift is in `K`
  (`DubC.CoreClosed`);
* **(b) `K` is deterministic** — a residue of `K` has at most one successor in `K`
  (`DubC.CoreDet`).

Then every infinite admissible path is eventually periodic (`DubC.eventually_periodic_of_core`),
and the rest of the pipeline is shared with the rank form, giving
`DubC.infinite_composites_floorPow_of_coreCert`.

## Why this shape

The proof is shorter than the rank argument and needs less: in a finite state space every
sequence eventually consists of *recurrent* values (`DubC.exists_tail_recurrent`), a recurrent
value lies on a cycle, so by (a) the whole tail of the path lies in `K`; by (b) the path is
forced from there on, and a deterministic orbit of a finite set is eventually periodic.

## Relation to the rank form

The two forms are **not** equivalent, and neither implies the other.

* (b) is strictly stronger than `C(𝒫)` in general.  `C(𝒫)` allows an edge from one cycle to
  another — the rank drops across it — whereas (b) forbids it.  Base `4` at `𝒫 = {2,3}` is a
  worked counterexample: both units mod `6` are fixed points, and the edge `1 → 5` (digit `1`)
  runs between the two cycles, so `CertOK` holds with a two-valued rank while `CoreDet` fails
  (`DubC.not_coreDet_four_six` in `DubC/Verdict.lean`).
* (a) is a global statement about the subshift that no local check sees, and it is exactly what
  a *core computation* — prune the non-recurrent states, then split into strongly connected
  components — produces.

The point of this form is the `a = 7` target.  There the computation of `DubC/cycles.c`,
cross-checked by `DubC/compress.py`, reports that the pruned core at `𝒫 = {p ≤ 31}` has **no
edges between distinct cycles**: all `365 761` cycle states have exactly one successor inside
the cycle set.  On that data the rank function is constant, so carrying it is pure overhead,
and the certificate reduces to (a) + (b) with `K` = the `849` stored cycles.  The obligation
that remains is therefore as small as the data allows: one global fact about where the cycles
are, and one purely local check on `K`.

## References

* **[Dub09]** A. Dubickas, *Prime and composite integers close to powers of a number*,
  Monatsh. Math. **158** (2009) 271–284.
* **[DubOst06]** A. Dubickas, *Truncatable primes and unavoidable sets of divisors*,
  Acta Math. Univ. Ostrav. **14** (2006) 21–25.
-/

namespace DubC

open Filter

/-! ### Recurrence in a finite state space -/

/-- **Every sequence in a finite state space eventually consists of recurrent values.**  A value
is *recurrent* along `s` when it reappears arbitrarily late; the values that are not have a last
occurrence, and there are only finitely many of them, so their occurrences are bounded. -/
@[category API, AMS 11 37, ref "Dub09", group "dubc_core"]
theorem exists_tail_recurrent {S : Type*} [Finite S] (s : ℕ → S) :
    ∃ N, ∀ n, N ≤ n → ∀ k, ∃ m, k < m ∧ s m = s n := by
  classical
  -- occurrences of the non-recurrent values form a finite set of indices
  have hfin : (⋃ v ∈ {v : S | ¬ ∀ k, ∃ m, k < m ∧ s m = v}, {n | s n = v}).Finite := by
    refine Set.Finite.biUnion (Set.toFinite _) ?_
    intro v hv
    simp only [Set.mem_ofPred_eq, not_forall] at hv
    obtain ⟨k, hk⟩ := hv
    refine Set.Finite.subset (Set.finite_Iic k) ?_
    intro n hn
    simp only [Set.mem_ofPred_eq] at hn
    simp only [Set.mem_Iic]
    by_contra hcon
    exact hk ⟨n, by omega, hn⟩
  obtain ⟨N, hN⟩ := hfin.bddAbove
  refine ⟨N + 1, fun n hn k => ?_⟩
  by_cases hv : ¬ ∀ k, ∃ m, k < m ∧ s m = s n
  · exact absurd (hN (Set.mem_biUnion hv rfl)) (by omega)
  · exact not_not.mp hv k

/-! ### The abstract engine -/

/-- **Compressed-core certificate ⇒ every infinite path is eventually periodic.**

`K` contains every state lying on a cycle (`hclosed`), and inside `K` the transition relation is
deterministic (`hdet`).  Along an infinite admissible path every sufficiently late state is
recurrent, hence lies on a cycle, hence lies in `K`; from there the path is forced, so a
repetition — supplied by pigeonhole — propagates forever.

Compare `DubC.eventually_periodic_of_rank`, which trades the global hypothesis `hclosed` for a
rank function.  Neither hypothesis implies the other. -/
@[category research solved, AMS 11 37, ref "Dub09" "DubOst06", group "dubc_core"]
theorem eventually_periodic_of_core {S : Type*} [Finite S] {adm : S → S → Prop} (K : S → Prop)
    (hclosed : ∀ v, Relation.TransGen adm v v → K v)
    (hdet : ∀ v t u, K v → K t → K u → adm v t → adm v u → t = u)
    (s : ℕ → S) (hs : ∀ n, adm (s n) (s (n + 1))) :
    ∃ n₀ L, 0 < L ∧ ∀ m, n₀ ≤ m → s (m + L) = s m := by
  -- an initial segment of the path is a chain of transitions
  have hpath : ∀ p q : ℕ, p < q → Relation.TransGen adm (s p) (s q) := by
    intro p q hpq
    induction q, hpq using Nat.le_induction with
    | base => exact Relation.TransGen.single (hs p)
    | succ q _ ih => exact ih.tail (hs q)
  -- late states are recurrent, hence lie on a cycle, hence lie in `K`
  obtain ⟨N, hN⟩ := exists_tail_recurrent s
  have hKtail : ∀ n, N ≤ n → K (s n) := by
    intro n hn
    obtain ⟨m, hm, hsm⟩ := hN n hn n
    have h := hpath n m hm
    rw [hsm] at h
    exact hclosed _ h
  -- past `N` the path is deterministic, so a repetition propagates forever
  have main : ∀ p q : ℕ, N ≤ p → p < q → s p = s q →
      ∃ n₀ L, 0 < L ∧ ∀ m, n₀ ≤ m → s (m + L) = s m := by
    intro p q hnp hpq heq
    obtain ⟨L, hL, rfl⟩ : ∃ L, 0 < L ∧ q = p + L := ⟨q - p, by omega, by omega⟩
    refine ⟨p, L, hL, ?_⟩
    intro m hm
    induction m, hm using Nat.le_induction with
    | base => exact heq.symm
    | succ m hpm ih =>
      have hadm2 : adm (s m) (s (m + L + 1)) := by rw [← ih]; exact hs (m + L)
      have huq := hdet (s m) (s (m + 1)) (s (m + L + 1)) (hKtail m (by omega))
        (hKtail (m + 1) (by omega)) (hKtail (m + L + 1) (by omega)) (hs m) hadm2
      have hidx : m + 1 + L = m + L + 1 := by omega
      rw [hidx, ← huq]
  -- pigeonhole supplies the repetition
  obtain ⟨j₁, j₂, hjne, hjeq⟩ := Finite.exists_ne_map_eq_of_infinite fun j : ℕ => s (N + j)
  rcases lt_trichotomy j₁ j₂ with h | h | h
  · exact main (N + j₁) (N + j₂) (by omega) (by omega) hjeq
  · exact absurd h hjne
  · exact main (N + j₂) (N + j₁) (by omega) (by omega) hjeq.symm

/-! ### The two conditions on the core -/

/-- **(a) `K` catches every cycle.**  A global fact about the subshift: this is what a core
computation establishes (prune to the recurrent part, split into strongly connected components,
collect the states lying on cycles). -/
def CoreClosed (a M : ℕ) (K : ZMod M → Prop) : Prop :=
  ∀ r : ZMod M, Relation.TransGen (Step a M) r r → K r

/-- **(b) `K` is deterministic.**  A purely local check, quantified over digits rather than over
target states so that it costs `O(|K| · a²)` and never enumerates the residue ring. -/
def CoreDet (a M : ℕ) (K : ZMod M → Prop) : Prop :=
  ∀ r : ZMod M, K r → ∀ d₁ < a, ∀ d₂ < a,
    K ((a : ZMod M) * r + (d₁ : ZMod M)) → K ((a : ZMod M) * r + (d₂ : ZMod M)) →
      (a : ZMod M) * r + (d₁ : ZMod M) = (a : ZMod M) * r + (d₂ : ZMod M)

-- The unfolded `CoreDet` is a deep nest of bounded quantifiers; instance search needs room.
set_option synthInstance.maxSize 1000
set_option synthInstance.maxHeartbeats 1000000

/-- For a decidable `K` on a finite residue ring `CoreDet` is a finite check. -/
instance (a M : ℕ) [NeZero M] (K : ZMod M → Prop) [DecidablePred K] :
    Decidable (CoreDet a M K) := by
  unfold CoreDet
  infer_instance

/-- `CoreDet` in the shape the abstract engine wants. -/
@[category API, AMS 11 37, ref "Dub09", group "dubc_core"]
theorem det_of_coreDet {a M : ℕ} {K : ZMod M → Prop} (hdet : CoreDet a M K) :
    ∀ r t u : ZMod M, K r → K t → K u → Step a M r t → Step a M r u → t = u := by
  rintro r t u hr ht hu ⟨-, -, d₁, hd₁, rfl⟩ ⟨-, -, d₂, hd₂, rfl⟩
  exact hdet r hr d₁ hd₁ d₂ hd₂ ht hu

/-! ### The certificate forces an eventually periodic digit word -/

/-- If the residues of `⌊ξaⁿ⌋` modulo `M` are units from `N` on, the compressed-core certificate
makes the base-`a` digit word of `ξ` eventually periodic. -/
@[category research solved, AMS 11 37, ref "Dub09", group "dubc_core"]
theorem digits_eventually_periodic_of_coreCert {a M : ℕ} (ha : 2 ≤ a) (haM : a ≤ M) [NeZero M]
    (K : ZMod M → Prop) (hclosed : CoreClosed a M K) (hdet : CoreDet a M K)
    {ξ : ℝ} {N : ℕ} (hunit : ∀ n, N ≤ n → Cop M ((floorPow ξ a n : ZMod M))) :
    ∃ n₀ L, 0 < L ∧ ∀ m, n₀ ≤ m → floorDigit ξ a (m + L) = floorDigit ξ a m := by
  obtain ⟨j₀, L, hL, hjper⟩ := eventually_periodic_of_core K hclosed (det_of_coreDet hdet)
    (fun j => ((floorPow ξ a (N + j) : ZMod M))) (step_floorPow (by omega) hunit)
  refine ⟨N + j₀, L, hL, digits_periodic_of_residues_periodic ha haM ?_⟩
  intro p hp
  have h1 := hjper (p - N) (by omega)
  have e1 : N + (p - N + L) = p + L := by omega
  have e2 : N + (p - N) = p := by omega
  rw [e1, e2] at h1
  exact h1

/-! ### The payoff -/

/-- **One compressed core settles the base.**  If some set `K` of residues mod `M ≥ a` catches
every cycle of the base-`a` coprimality subshift and is deterministic, then for **every** real
`ξ > 0` the sequence `⌊ξ·aⁿ⌋` contains infinitely many composite terms — [DubOst06]
Conjecture 2 for the base `a`, which for `a ≥ 7` is the open case of the 1967 Forman–Shapiro
problem.

No rank data, no spectral estimate and no graph algorithm appears in the hypotheses: `hclosed`
is a single global statement about where the cycles are, and `hdet` is a local check on `K`. -/
@[category research solved, AMS 11 37, ref "Dub09" "DubOst06", group "dubc_core"]
theorem infinite_composites_floorPow_of_coreCert {a M : ℕ} (ha : 2 ≤ a) (haM : a ≤ M) [NeZero M]
    (K : ZMod M → Prop) (hclosed : CoreClosed a M K) (hdet : CoreDet a M K)
    {ξ : ℝ} (hξ : 0 < ξ) :
    {n | CompositeInt (floorPow ξ a n)}.Infinite :=
  infinite_composites_floorPow_of_digits ha hξ fun _ hunit =>
    digits_eventually_periodic_of_coreCert ha haM K hclosed hdet hunit

/-! ### The cheapest instance: take `K` to be all units

When every unit has at most one unit successor, condition (a) is free — every state of the
subshift is a unit by definition of `DubC.Step` — and the certificate collapses to a single
`decide`.  This is the `y`-minimal situation for the bases `3` and `5`; see
`DubC/Verdict.lean`. -/

/-- Condition (a) is automatic for `K` = the units, because `DubC.Step` only relates units. -/
@[category API, AMS 11 37, ref "Dub09", group "dubc_core"]
theorem coreClosed_cop (a M : ℕ) : CoreClosed a M (Cop M) := by
  intro r h
  cases h with
  | single hstep => exact hstep.1
  | tail _ hstep => exact hstep.2.1

/-- **Unit-determinism settles the base.**  If every unit mod `M` has at most one unit successor
in base `a`, then `⌊ξ·aⁿ⌋` has infinitely many composite terms for every real `ξ > 0`. -/
@[category research solved, AMS 11 37, ref "Dub09" "DubOst06", group "dubc_core"]
theorem infinite_composites_floorPow_of_unitDet {a M : ℕ} (ha : 2 ≤ a) (haM : a ≤ M) [NeZero M]
    (hdet : CoreDet a M (Cop M)) {ξ : ℝ} (hξ : 0 < ξ) :
    {n | CompositeInt (floorPow ξ a n)}.Infinite :=
  infinite_composites_floorPow_of_coreCert ha haM (Cop M) (coreClosed_cop a M) hdet hξ

end DubC
