/-
(C) 2026 Ralf Stephan, in collaboration with Claude Code.
Released under CC0 1.0 Universal (public-domain dedication).
See https://creativecommons.org/publicdomain/zero/1.0/
-/
import SRS.AntihydraSRSForward
import Mathlib.Data.Nat.Lattice
import Mathlib.Computability.DFA

/-!
# A pumping obstruction to regular invariants of Antihydra

A **FAR-style** (Finite Automata Reduction) non-halting proof of a Turing machine exhibits a *regular*
set `S` of configurations that (i) contains every reachable configuration, (ii) is closed under one
rewriting step, and (iii) contains no halting configuration. This file proves a hard limitation of
such proofs for **Antihydra**: when the counter is stored as a contiguous unary block and `S` is
recognized with `p` automaton states, the *future dips* of the counter are bounded by `p`.

Concretely, let `bₙ` be the counter after `n` macro steps of the (deterministic) orbit and define the
future-dip sequence `D(n) := bₙ − min_{m ≥ n} bₘ`. The **proposition** is:

> If a regular set `S` with `p` states satisfies (i)–(iii), then `D(n) < p` whenever `bₙ ≥ p`.

**Proof idea** (formalized here). Take the reachable configuration `◁ wₙ ▷ cᵇⁿ` at time `n`; its
counter block has length `bₙ ≥ p`, so the accepting run repeats a state inside the block and a factor
`cʲ` (`1 ≤ j ≤ p`) can be pumped out — yielding `◁ wₙ ▷ c^{b'}` with `b' < p`, still in `S`
(`hpump`). Because counter increments depend only on the value (the value orbit ignores the counter —
this is exactly what `antihydraSRS_realizes_orbit` encodes), the forward orbit of the pumped
configuration tracks the real one with the counter shifted *down* by `bₙ − b'`. If `D(n) ≥ p > b'`,
that shifted counter would go negative; since odd steps decrement by exactly `1`, it instead reaches
`0` at an odd step — a **halting** configuration — reachable from the pumped one and hence in `S` by
(ii), contradicting (iii).

The heart is `futureDip_bound`. Its contradiction is produced by re-running the forward simulation
`antihydraSRS_realizes_orbit` from the *pumped* configuration until it halts.

* `IsHalting` — a halting configuration: an all-binary value string of odd value with empty counter
  (`◁ w ▷` with `w` binary, `cval w` odd; no `c`, so the odd dynamic rule cannot fire).
* `futureDip_bound` — the proposition in the form `bₙ < bₘ + p` for all `m ≥ n` with `bₙ ≥ p`
  (equivalently `D(n) < p`).
* `futureDip` / `futureDip_lt_card` — the literal `D(n) < p`.
* `no_regular_invariant_of_unbounded_dips` — the **corollary**: if the dips are unbounded, no regular
  invariant of any size exists over unary-counter encodings.
* `dfa_pump` / `regularInvariant_of_dfa` / `no_dfa_invariant_of_unbounded_dips` — the pumping property
  is derived from an actual `DFA` (suffix pigeonhole on the counter block), making "recognized with
  `p` states" literal: unbounded dips rule out a finite automaton of *any* state count.

## References
* [bbchallenge] The Busy Beaver Challenge. *Finite Automata Reduction (FAR)* deciders;
  *Antihydra* (`bbchallenge.org`).
* [YAH] E. Yolcu, S. Aaronson, M. J. H. Heule. *An Automated Approach to the Collatz Conjecture.*
  Journal of Automated Reasoning (2023); arXiv:2105.14697.
-/

namespace StringRewriting.AntihydraSRS

open StringRewriting StringRewriting.MixedBase ASym Relation

/-! ### Orbit lemmas

The value orbit and the (integer) counter orbit are *additive* in the step index and the counter
start, and the partial iterate `macroIter` agrees with them while it has not halted. These are the
arithmetic facts the obstruction needs. -/

/-- The value orbit is additive in the step index: `valOrbit a₀ (n + j) = valOrbit (valOrbit a₀ n) j`
(restarting the orbit at step `n`). -/
@[category API, AMS 11, ref "YAH", group "antihydra_srs"]
theorem valOrbit_add (a₀ n j : ℕ) : valOrbit a₀ (n + j) = valOrbit (valOrbit a₀ n) j := by
  induction j with
  | zero => rfl
  | succ j ih => rw [Nat.add_succ, valOrbit_succ, valOrbit_succ, ih]

/-- Shifting the initial counter shifts the whole counter orbit by the same amount:
`counterZ b' a₀ j = counterZ b a₀ j + (b' − b)` (the increments depend only on the value orbit). -/
@[category API, AMS 11, ref "YAH", group "antihydra_srs", formal_uses counterZ_closed]
theorem counterZ_shift (b b' : ℤ) (a₀ j : ℕ) :
    counterZ b' a₀ j = counterZ b a₀ j + (b' - b) := by
  rw [counterZ_closed, counterZ_closed]; ring

/-- The counter orbit is additive in the step index, restarting at step `n` with counter
`counterZ b₀ a₀ n` and value `valOrbit a₀ n`. -/
@[category API, AMS 11, ref "YAH", group "antihydra_srs", formal_uses valOrbit_add]
theorem counterZ_add (b₀ : ℤ) (a₀ n j : ℕ) :
    counterZ b₀ a₀ (n + j) = counterZ (counterZ b₀ a₀ n) (valOrbit a₀ n) j := by
  induction j with
  | zero => rfl
  | succ j ih => rw [Nat.add_succ, counterZ_succ, counterZ_succ, ih, valOrbit_add]

/-- The value orbit stays `≥ 2` from a start value `≥ 2` (`⌊3a/2⌋ ≥ 2` for `a ≥ 2`); so the value
string is never empty and always carries a parity-bearing last symbol. -/
@[category API, AMS 11, ref "YAH", group "antihydra_srs"]
theorem valOrbit_ge_two {a₀ : ℕ} (h : 2 ≤ a₀) (n : ℕ) : 2 ≤ valOrbit a₀ n := by
  induction n with
  | zero => exact h
  | succ n ih => rw [valOrbit_succ]; unfold valStep; omega

/-- The macro step halts exactly at an odd value with empty counter. -/
@[category API, AMS 11 68, ref "YAH", group "antihydra_srs"]
theorem macroStep_eq_none_iff (a b : ℕ) : macroStep (a, b) = none ↔ a % 2 = 1 ∧ b = 0 := by
  simp only [macroStep]; split_ifs with h1 h2 <;> simp_all

/-- While `macroIter` has not halted, its value and counter agree with the deterministic orbit:
`aₙ = valOrbit a₀ n` and `bₙ = counterZ b₀ a₀ n` (in `ℤ`). -/
@[category research solved, AMS 11, ref "YAH", group "antihydra_srs",
  formal_uses macroStep_value counterZ_succ]
theorem macroIter_eq_orbit (a₀ b₀ : ℕ) :
    ∀ (n aₙ bₙ : ℕ), macroIter n (a₀, b₀) = some (aₙ, bₙ) →
      aₙ = valOrbit a₀ n ∧ (bₙ : ℤ) = counterZ (b₀ : ℤ) a₀ n := by
  intro n
  induction n with
  | zero =>
    intro aₙ bₙ h; simp only [macroIter] at h
    obtain ⟨rfl, rfl⟩ : a₀ = aₙ ∧ b₀ = bₙ := by simpa using h
    exact ⟨rfl, rfl⟩
  | succ n ih =>
    intro aₙ₁ bₙ₁ h
    rw [macroIter_succ] at h
    rcases hmn : macroIter n (a₀, b₀) with _ | ⟨aₙ, bₙ⟩
    · rw [hmn] at h; simp at h
    · rw [hmn] at h
      replace h : macroStep (aₙ, bₙ) = some (aₙ₁, bₙ₁) := h
      obtain ⟨hav, hcv⟩ := ih aₙ bₙ hmn
      refine ⟨by rw [valOrbit_succ, ← hav]; exact macroStep_value h, ?_⟩
      have hcounter : (bₙ₁ : ℤ) = (bₙ : ℤ) + (if aₙ % 2 = 0 then 2 else -1) := by
        by_cases hpar : aₙ % 2 = 0
        · rw [if_pos hpar]
          have hb1 : bₙ₁ = bₙ + 2 := by
            have h' := h
            simp only [macroStep, if_pos hpar, Option.some.injEq, Prod.mk.injEq] at h'; omega
          rw [hb1]; push_cast; ring
        · rw [if_neg hpar]
          have hb : bₙ ≠ 0 := by
            rintro rfl
            rw [(macroStep_eq_none_iff aₙ 0).mpr ⟨by omega, rfl⟩] at h; exact absurd h (by simp)
          have hb1 : bₙ₁ = bₙ - 1 := by
            have h' := h
            simp only [macroStep, if_neg hpar, if_neg hb, Option.some.injEq, Prod.mk.injEq] at h'; omega
          rw [hb1, Nat.cast_sub (show 1 ≤ bₙ by omega)]; push_cast; ring
      rw [counterZ_succ, ← hav, ← hcv]; exact hcounter

/-- If `macroIter` reaches `none` (the orbit halts) by step `N`, there is a first halting transition:
some step `j` that is still defined whose successor is `none`. -/
@[category API, AMS 11, ref "YAH", group "antihydra_srs"]
theorem exists_first_none {a₀ b₀ : ℕ} : ∀ N, macroIter N (a₀, b₀) = none →
    ∃ j aⱼ bⱼ, macroIter j (a₀, b₀) = some (aⱼ, bⱼ) ∧ macroIter (j + 1) (a₀, b₀) = none := by
  intro N
  induction N with
  | zero => intro h; simp [macroIter] at h
  | succ N ih =>
    intro h
    rcases hmN : macroIter N (a₀, b₀) with _ | ⟨aN, bN⟩
    · exact ih hmN
    · exact ⟨N, aN, bN, hmN, h⟩

/-- A set closed under one rewriting step is closed under derivations (`ReflTransGen`). -/
@[category API, AMS 68, ref "BO93", group "antihydra_srs"]
theorem mem_of_reflTransGen {S : Set (List ASym)}
    (hclosed : ∀ u v, u ∈ S → RewriteStep antihydraSRS u v → v ∈ S)
    {u v : List ASym} (hu : u ∈ S) (h : ReflTransGen (RewriteStep antihydraSRS) u v) : v ∈ S := by
  induction h with
  | refl => exact hu
  | tail _ hstep ih => exact hclosed _ _ ih hstep

/-! ### Halting configurations and the obstruction -/

/-- A **halting configuration**: an all-binary value string `w` of odd value with empty counter,
`◁ w ▷` (no `c`). The odd dynamic rule `t▷c → 1▷` needs a `c`, so such a configuration is
irreducible — this is the form in which the Antihydra macro model halts. -/
@[category API, AMS 68 11, ref "bbchallenge", group "antihydra_srs"]
def IsHalting (cfg : List ASym) : Prop := ∃ w, IsBinary w ∧ cval w % 2 = 1 ∧ cfg = config w 0

/-- **Pumping obstruction (core form).** Let `S` recognize a set of configurations closed under
rewriting, containing every configuration reachable from `config w₀ b₀` and no halting configuration,
and admit unary-counter pumping below `p` (`hpump`: any in-`S` configuration with counter `≥ p` has an
in-`S` sibling with the same value string and counter `< p`). Then along the orbit the counter never
dips by `p` or more once it is `≥ p`: for all `m ≥ n`, if `bₙ ≥ p` then `bₙ < bₘ + p`. Equivalently,
the future dip `D(n) = bₙ − min_{m ≥ n} bₘ` is `< p` whenever `bₙ ≥ p`.

The proof pumps the step-`n` configuration down to counter `b' < p` and re-runs the forward
simulation `antihydraSRS_realizes_orbit` from it: if the dip were `≥ p`, the pumped orbit's signed
counter would be negative by step `m − n` (`counterZ_shift`/`counterZ_add`), so it halts first
(`exists_first_none`, `macroStep_eq_none_iff`) at a halting configuration that lies in `S` by closure
— contradicting `hnohalt`. -/
@[category research solved, AMS 68 11, ref "bbchallenge", group "antihydra_srs",
  formal_uses antihydraSRS_realizes_orbit macroIter_eq_orbit counterZ_shift counterZ_add
    exists_first_none mem_of_reflTransGen]
theorem futureDip_bound
    (w₀ : List ASym) (hw₀ : IsBinary w₀) (b₀ : ℕ) (ha₀ : 2 ≤ cval w₀)
    {S : Set (List ASym)} {p : ℕ}
    (hreach : ∀ c, ReflTransGen (RewriteStep antihydraSRS) (config w₀ b₀) c → c ∈ S)
    (hclosed : ∀ u v, u ∈ S → RewriteStep antihydraSRS u v → v ∈ S)
    (hnohalt : ∀ c ∈ S, ¬ IsHalting c)
    (hpump : ∀ w b, config w b ∈ S → p ≤ b → ∃ b', b' < p ∧ config w b' ∈ S)
    {n m an bn am bm : ℕ} (hnm : n ≤ m)
    (hin : macroIter n (cval w₀, b₀) = some (an, bn))
    (him : macroIter m (cval w₀, b₀) = some (am, bm))
    (hp : p ≤ bn) :
    bn < bm + p := by
  obtain ⟨Wn, hWnbin, hWnval, hWnge, hWnderiv⟩ :=
    antihydraSRS_realizes_orbit w₀ hw₀ b₀ ha₀ n an bn hin
  have hWnS : config Wn bn ∈ S := hreach _ hWnderiv
  obtain ⟨b', hb'p, hb'S⟩ := hpump Wn bn hWnS hp
  obtain ⟨hanv, hbnv⟩ := macroIter_eq_orbit (cval w₀) b₀ n an bn hin
  obtain ⟨-, hbmv⟩ := macroIter_eq_orbit (cval w₀) b₀ m am bm him
  by_contra hcon
  rw [not_lt] at hcon
  have hnone : macroIter (m - n) (an, b') = none := by
    rcases hmm : macroIter (m - n) (an, b') with _ | ⟨a'', b''⟩
    · rfl
    · exfalso
      obtain ⟨-, hb''⟩ := macroIter_eq_orbit an b' (m - n) a'' b'' hmm
      have key : counterZ (b' : ℤ) an (m - n) = (bm : ℤ) + (b' : ℤ) - (bn : ℤ) := by
        rw [counterZ_shift (bn : ℤ) (b' : ℤ) an (m - n)]
        have hadd : counterZ (bn : ℤ) an (m - n) = (bm : ℤ) := by
          have hc := counterZ_add (b₀ : ℤ) (cval w₀) n (m - n)
          rw [Nat.add_sub_cancel' hnm, ← hbnv, ← hanv, ← hbmv] at hc
          exact hc.symm
        rw [hadd]; ring
      rw [key] at hb''
      omega
  obtain ⟨j, aⱼ, bⱼ, hjsome, hjnone⟩ := exists_first_none (m - n) hnone
  have hstepnone : macroStep (aⱼ, bⱼ) = none := by
    rw [macroIter_succ, hjsome] at hjnone; exact hjnone
  obtain ⟨hodd, hbj0⟩ := (macroStep_eq_none_iff aⱼ bⱼ).mp hstepnone
  subst hbj0
  rw [← hWnval] at hjsome
  obtain ⟨Wj, hWjbin, hWjval, -, hWjderiv⟩ :=
    antihydraSRS_realizes_orbit Wn hWnbin b' hWnge j aⱼ 0 hjsome
  have hWjS : config Wj 0 ∈ S := mem_of_reflTransGen hclosed hb'S hWjderiv
  exact hnohalt _ hWjS ⟨Wj, hWjbin, by rw [hWjval]; exact hodd, rfl⟩

/-! ### Packaging: regular invariants and the future-dip sequence -/

/-- A **regular invariant** of `p` automaton states recognizing a set `S` of configurations (unary
counter block): `S` contains every configuration reachable from `config w₀ b₀` (`reach`), is closed
under one rewriting step (`closed`), contains no halting configuration (`noHalt`), and admits
unary-counter pumping below `p` (`pump` — any in-`S` configuration with counter `≥ p` has an in-`S`
sibling with the same value string and counter `< p`, the consequence of recognizing the counter
block with `p` states). This bundles hypotheses (i)–(iii) of the proposition together with the
pumping property a `p`-state recognizer provides. -/
@[category API, AMS 68 11, ref "bbchallenge", group "antihydra_srs"]
structure RegularInvariant (w₀ : List ASym) (b₀ : ℕ) (S : Set (List ASym)) (p : ℕ) : Prop where
  /-- `S` contains every reachable configuration. -/
  reach : ∀ c, ReflTransGen (RewriteStep antihydraSRS) (config w₀ b₀) c → c ∈ S
  /-- `S` is closed under one rewriting step. -/
  closed : ∀ u v, u ∈ S → RewriteStep antihydraSRS u v → v ∈ S
  /-- `S` contains no halting configuration. -/
  noHalt : ∀ c ∈ S, ¬ IsHalting c
  /-- Unary-counter pumping: from counter `≥ p` one can pump down to `< p` within `S`. -/
  pump : ∀ w b, config w b ∈ S → p ≤ b → ∃ b', b' < p ∧ config w b' ∈ S

/-- The counter `bₙ` after `n` macro steps of the orbit from `config w₀ b₀` (`0` past a halt, which
does not occur under a `RegularInvariant`). -/
@[category API, AMS 11 68, ref "bbchallenge", group "antihydra_srs"]
def orbitCounter (w₀ : List ASym) (b₀ n : ℕ) : ℕ := ((macroIter n (cval w₀, b₀)).getD (0, 0)).2

/-- `orbitCounter` reads off the counter of a non-halting orbit step. -/
@[category API, AMS 11, ref "bbchallenge", group "antihydra_srs"]
theorem orbitCounter_eq {w₀ : List ASym} {b₀ n an bn : ℕ}
    (h : macroIter n (cval w₀, b₀) = some (an, bn)) : orbitCounter w₀ b₀ n = bn := by
  simp [orbitCounter, h]

/-- **The orbit never halts under a regular invariant.** If it did, a halting configuration would be
reachable, hence in `S`, contradicting `noHalt`. So `macroIter` is defined at every step. -/
@[category research solved, AMS 68 11, ref "bbchallenge", group "antihydra_srs",
  formal_uses antihydraSRS_realizes_orbit macroStep_eq_none_iff]
theorem macroIter_isSome
    (w₀ : List ASym) (hw₀ : IsBinary w₀) (b₀ : ℕ) (ha₀ : 2 ≤ cval w₀)
    {S : Set (List ASym)} {p : ℕ} (hreg : RegularInvariant w₀ b₀ S p) :
    ∀ n, ∃ an bn, macroIter n (cval w₀, b₀) = some (an, bn) := by
  intro n
  induction n with
  | zero => exact ⟨cval w₀, b₀, rfl⟩
  | succ n ih =>
    obtain ⟨an, bn, hn⟩ := ih
    rcases hstep : macroStep (an, bn) with _ | ⟨an1, bn1⟩
    · exfalso
      obtain ⟨hodd, hbn0⟩ := (macroStep_eq_none_iff an bn).mp hstep
      subst hbn0
      obtain ⟨Wn, hWnbin, hWnval, -, hWnderiv⟩ :=
        antihydraSRS_realizes_orbit w₀ hw₀ b₀ ha₀ n an 0 hn
      exact hreg.noHalt _ (hreg.reach _ hWnderiv) ⟨Wn, hWnbin, by rw [hWnval]; exact hodd, rfl⟩
    · exact ⟨an1, bn1, by rw [macroIter_succ, hn]; exact hstep⟩

/-- **Future dips are bounded by `p`** (`bₙ < bₘ + p` for `m ≥ n`, `bₙ ≥ p`): the proposition, stated
on `orbitCounter` and avoiding truncated subtraction. -/
@[category research solved, AMS 68 11, ref "bbchallenge", group "antihydra_srs",
  formal_uses futureDip_bound macroIter_isSome orbitCounter_eq]
theorem orbitDip_lt
    (w₀ : List ASym) (hw₀ : IsBinary w₀) (b₀ : ℕ) (ha₀ : 2 ≤ cval w₀)
    {S : Set (List ASym)} {p : ℕ} (hreg : RegularInvariant w₀ b₀ S p)
    (n m : ℕ) (hnm : n ≤ m) (hp : p ≤ orbitCounter w₀ b₀ n) :
    orbitCounter w₀ b₀ n < orbitCounter w₀ b₀ m + p := by
  obtain ⟨an, bn, hin⟩ := macroIter_isSome w₀ hw₀ b₀ ha₀ hreg n
  obtain ⟨am, bm, him⟩ := macroIter_isSome w₀ hw₀ b₀ ha₀ hreg m
  rw [orbitCounter_eq hin] at hp
  rw [orbitCounter_eq hin, orbitCounter_eq him]
  exact futureDip_bound w₀ hw₀ b₀ ha₀ hreg.reach hreg.closed hreg.noHalt hreg.pump hnm hin him hp

/-- The **future-dip sequence** `D(n) = bₙ − min_{m ≥ n} bₘ`, with the minimum realized as the
infimum of the future counter values. -/
@[category API, AMS 11 68, ref "bbchallenge", group "antihydra_srs"]
noncomputable def futureDip (b : ℕ → ℕ) (n : ℕ) : ℕ := b n - sInf (Set.range fun k => b (n + k))

/-- **The proposition, in the form `D(n) < p`.** Under a regular invariant with `p` states, the
future dip of the orbit counter is `< p` whenever `bₙ ≥ p`. (The minimizing future step `m` has
`bₘ ≤ bₙ`, so the dip is a genuine difference, and `orbitDip_lt` bounds it.) -/
@[category research solved, AMS 68 11, ref "bbchallenge", group "antihydra_srs",
  formal_uses orbitDip_lt]
theorem futureDip_lt_card
    (w₀ : List ASym) (hw₀ : IsBinary w₀) (b₀ : ℕ) (ha₀ : 2 ≤ cval w₀)
    {S : Set (List ASym)} {p : ℕ} (hreg : RegularInvariant w₀ b₀ S p)
    (n : ℕ) (hp : p ≤ orbitCounter w₀ b₀ n) :
    futureDip (orbitCounter w₀ b₀) n < p := by
  obtain ⟨k₀, hk₀raw⟩ := Nat.sInf_mem (Set.range_nonempty (fun k => orbitCounter w₀ b₀ (n + k)))
  have hk₀ : orbitCounter w₀ b₀ (n + k₀)
      = sInf (Set.range fun k => orbitCounter w₀ b₀ (n + k)) := hk₀raw
  have hle : sInf (Set.range fun k => orbitCounter w₀ b₀ (n + k)) ≤ orbitCounter w₀ b₀ n :=
    Nat.sInf_le ⟨0, by simp⟩
  have hb := orbitDip_lt w₀ hw₀ b₀ ha₀ hreg n (n + k₀) (Nat.le_add_right n k₀) hp
  unfold futureDip
  rw [← hk₀] at hle ⊢
  omega

/-- **Corollary.** If the future dips of the orbit counter are unbounded (for every `q` some step `n`
has both `bₙ ≥ q` and `D(n) ≥ q`), then **no regular invariant of any size `p` exists** over
unary-counter encodings: a `p`-state invariant forces `D(n) < p` whenever `bₙ ≥ p`
(`futureDip_lt_card`), contradicting unboundedness at `q = p`. (Conversely, a FAR proof with `p`
states is exactly a proof that all dips are `< p` from the moment `bₙ ≥ p`.) -/
@[category research solved, AMS 68 11, ref "bbchallenge", group "antihydra_srs",
  formal_uses futureDip_lt_card]
theorem no_regular_invariant_of_unbounded_dips
    (w₀ : List ASym) (hw₀ : IsBinary w₀) (b₀ : ℕ) (ha₀ : 2 ≤ cval w₀)
    (hunbounded : ∀ q : ℕ, ∃ n, q ≤ orbitCounter w₀ b₀ n ∧ q ≤ futureDip (orbitCounter w₀ b₀) n)
    (p : ℕ) {S : Set (List ASym)} (hreg : RegularInvariant w₀ b₀ S p) : False := by
  obtain ⟨n, hbn, hdip⟩ := hunbounded p
  have := futureDip_lt_card w₀ hw₀ b₀ ha₀ hreg n hbn
  omega

/-! ### The pumping property comes from a finite automaton

The abstract `RegularInvariant.pump` field is exactly what a finite-automaton recognizer with a
contiguous unary counter block provides. We make this literal: a `DFA` over `ASym` with `p` states
pumps any accepted configuration of counter `≥ p` down to counter `< p` (`dfa_pump`), via the
suffix-pumping pigeonhole on the counter block (`exists_iterate_lt_card`). So a DFA-recognized
closed, reachable-containing, halt-free language *is* a `RegularInvariant` with `p = card σ`
(`regularInvariant_of_dfa`), and the corollary applies to genuine finite automata
(`no_dfa_invariant_of_unbounded_dips`). -/

/-- **Iterate pigeonhole.** For `g : σ → σ` on a finite type and `n ≥ card σ`, some iterate index
`k < card σ` reaches the same state as `n`: `g^[k] q = g^[n] q`. (The orbit of `q` under `g` enters a
cycle within `card σ` steps; `n` is reduced modulo the period into the prefix.) -/
@[category API, AMS 68 5, ref "BO93", group "antihydra_srs"]
theorem exists_iterate_lt_card {σ : Type*} [Fintype σ] (g : σ → σ) (q : σ) (n : ℕ)
    (hn : Fintype.card σ ≤ n) : ∃ k, k < Fintype.card σ ∧ g^[k] q = g^[n] q := by
  obtain ⟨i, j, hij, hfij⟩ := Fintype.exists_ne_map_eq_of_card_lt
    (fun i : Fin (Fintype.card σ + 1) => g^[(i:ℕ)] q)
    (by rw [Fintype.card_fin]; exact Nat.lt_succ_self _)
  set a := min (i:ℕ) (j:ℕ) with ha
  set b := max (i:ℕ) (j:ℕ) with hb
  have hne : (i:ℕ) ≠ (j:ℕ) := fun h => hij (Fin.ext h)
  have hab : a < b := by rw [ha, hb]; omega
  have hbcard : b ≤ Fintype.card σ := by rw [hb]; have := i.isLt; have := j.isLt; omega
  have hperiod : g^[a] q = g^[b] q := by
    rcases le_total (i:ℕ) (j:ℕ) with h | h
    · rw [ha, hb, min_eq_left h, max_eq_right h]; exact hfij
    · rw [ha, hb, min_eq_right h, max_eq_left h]; exact hfij.symm
  set d := b - a with hd
  have hd1 : 1 ≤ d := by omega
  have hperiod' : g^[a] q = g^[a + d] q := by
    rw [hd, show a + (b - a) = b from by omega]; exact hperiod
  have iterper : ∀ m, g^[a + m] q = g^[a + d + m] q := by
    intro m
    induction m with
    | zero => simpa using hperiod'
    | succ m ih =>
      rw [show a + (m + 1) = (a + m) + 1 from by ring, show a + d + (m + 1) = (a + d + m) + 1 from by ring,
          Function.iterate_succ_apply', Function.iterate_succ_apply', ih]
  have hred : ∀ m, g^[a + m] q = g^[a + m % d] q := by
    intro m
    induction m using Nat.strong_induction_on with
    | _ m ih =>
      rcases Nat.lt_or_ge m d with hlt | hge
      · rw [Nat.mod_eq_of_lt hlt]
      · have hstep : g^[a + m] q = g^[a + (m - d)] q := by
          have hp := iterper (m - d)
          rw [show a + d + (m - d) = a + m from by omega] at hp
          exact hp.symm
        rw [hstep, ih (m - d) (by omega), Nat.mod_eq_sub_mod hge]
  refine ⟨a + (n - a) % d, ?_, ?_⟩
  · have : (n - a) % d < d := Nat.mod_lt _ hd1
    omega
  · rw [← hred (n - a), show a + (n - a) = n from by omega]

/-- Reading a unary block `xᵇ` iterates the one-symbol transition `b` times. -/
@[category API, AMS 68, ref "BO93", group "antihydra_srs"]
theorem foldl_step_replicate {α σ : Type*} (M : DFA α σ) (x : α) (b : ℕ) (q : σ) :
    (List.replicate b x).foldl M.step q = (fun s => M.step s x)^[b] q := by
  induction b generalizing q with
  | zero => rfl
  | succ b ih => rw [List.replicate_succ, List.foldl_cons, ih, Function.iterate_succ_apply]

/-- A DFA's run on a configuration factors through the counter block: after the value prefix
`◁ w ▷` it iterates the `c`-transition `b` times. -/
@[category API, AMS 68, ref "bbchallenge", group "antihydra_srs", formal_uses foldl_step_replicate]
theorem eval_config {σ : Type*} (M : DFA ASym σ) (w : List ASym) (b : ℕ) :
    M.eval (config w b)
      = (fun s => M.step s c)^[b] (M.evalFrom M.start (lhd :: w ++ [rhd])) := by
  have hlist : config w b = (lhd :: w ++ [rhd]) ++ List.replicate b c := by
    simp [config, List.append_assoc]
  rw [DFA.eval, hlist, DFA.evalFrom, List.foldl_append, foldl_step_replicate]

/-- **Suffix pumping for a DFA.** If a DFA with `p = card σ` states accepts `◁ w ▷ cᵇ` with `b ≥ p`,
the accepting run repeats a state inside the `c`-block, so a factor can be pumped out: the DFA also
accepts `◁ w ▷ c^{b'}` for some `b' < p` (same value string). This is the `RegularInvariant.pump`
property for a finite automaton. -/
@[category research solved, AMS 68, ref "BO93", group "antihydra_srs",
  formal_uses exists_iterate_lt_card eval_config]
theorem dfa_pump {σ : Type*} [Fintype σ] (M : DFA ASym σ) (w : List ASym) (b : ℕ)
    (hmem : config w b ∈ M.accepts) (hb : Fintype.card σ ≤ b) :
    ∃ b', b' < Fintype.card σ ∧ config w b' ∈ M.accepts := by
  obtain ⟨k, hk, hkeq⟩ :=
    exists_iterate_lt_card (fun s => M.step s c) (M.evalFrom M.start (lhd :: w ++ [rhd])) b hb
  refine ⟨k, hk, ?_⟩
  show M.eval (config w k) ∈ M.accept
  rw [eval_config, hkeq, ← eval_config]
  exact hmem

/-- A DFA recognizing a closed, reachable-containing, halt-free language **is** a `RegularInvariant`
with `p = card σ` states — the pumping property is automatic (`dfa_pump`). -/
@[category research solved, AMS 68 11, ref "bbchallenge", group "antihydra_srs",
  formal_uses dfa_pump]
theorem regularInvariant_of_dfa {σ : Type*} [Fintype σ] (M : DFA ASym σ) (w₀ : List ASym) (b₀ : ℕ)
    (reach : ∀ c, ReflTransGen (RewriteStep antihydraSRS) (config w₀ b₀) c → c ∈ M.accepts)
    (closed : ∀ u v, u ∈ M.accepts → RewriteStep antihydraSRS u v → v ∈ M.accepts)
    (noHalt : ∀ c ∈ M.accepts, ¬ IsHalting c) :
    RegularInvariant w₀ b₀ M.accepts (Fintype.card σ) :=
  ⟨reach, closed, noHalt, fun w b => dfa_pump M w b⟩

/-- **Corollary (finite-automaton form).** If the orbit's future dips are unbounded, then no finite
automaton recognizes a closed, reachable-containing, halt-free set of configurations — a FAR-style
non-halting proof of Antihydra over unary-counter encodings is impossible, *at any number of states*.
-/
@[category research solved, AMS 68 11, ref "bbchallenge", group "antihydra_srs",
  formal_uses no_regular_invariant_of_unbounded_dips regularInvariant_of_dfa]
theorem no_dfa_invariant_of_unbounded_dips
    (w₀ : List ASym) (hw₀ : IsBinary w₀) (b₀ : ℕ) (ha₀ : 2 ≤ cval w₀)
    (hunbounded : ∀ q : ℕ, ∃ n, q ≤ orbitCounter w₀ b₀ n ∧ q ≤ futureDip (orbitCounter w₀ b₀) n)
    {σ : Type} [Fintype σ] (M : DFA ASym σ)
    (reach : ∀ c, ReflTransGen (RewriteStep antihydraSRS) (config w₀ b₀) c → c ∈ M.accepts)
    (closed : ∀ u v, u ∈ M.accepts → RewriteStep antihydraSRS u v → v ∈ M.accepts)
    (noHalt : ∀ c ∈ M.accepts, ¬ IsHalting c) : False :=
  no_regular_invariant_of_unbounded_dips w₀ hw₀ b₀ ha₀ hunbounded (Fintype.card σ)
    (regularInvariant_of_dfa M w₀ b₀ reach closed noHalt)

end StringRewriting.AntihydraSRS
