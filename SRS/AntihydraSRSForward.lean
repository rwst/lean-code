/-
(C) 2026 Ralf Stephan, in collaboration with Claude Code.
Released under CC0 1.0 Universal (public-domain dedication).
See https://creativecommons.org/publicdomain/zero/1.0/
-/
import SRS.AntihydraSRSSimulation
import Mathlib.Data.List.Induction

/-!
# Forward (constructive) simulation: a strategy that *realises* the Antihydra orbit

`SRS.AntihydraSRSSimulation` proves the **backward / universal** half of the simulation (the analog of
[YAH] §3.2, Claim 1, made config-faithful): *every* configuration reachable from `config w₀ b₀` by
*any* `antihydraSRS`-derivation already lies on the deterministic orbit
(`antihydraSRS_simulates`). That is a soundness statement — no strategy can stray off the orbit — but
on its own it is compatible with "no progress is ever possible": it does not exhibit a single
derivation that actually *walks* the orbit.

This file supplies the missing **forward / constructive** half ([YAH] §3.2, Claim 3 — progress /
liveness), mirroring the corpus's own forward simulation `SRS.Zantema` (`evenSim` / `oddSim`, built
from `ReflTransGen` sweeps), but for the *mixed-base* alphabet. We give an explicit, essentially
deterministic strategy and prove it realises each non-halting macro step:

1. **Dynamic step at the boundary.** From an all-binary digit string `w` ending in `f` (value even)
   or `t` (value odd, counter `≥ 1`), fire the dynamic rule at the unique `▷`
   (`config_even_step` / `config_odd_step`). This produces one ternary digit `d0` / `d1` at the right
   end and updates the counter (`+2` / `−1`).
2. **Carry sweep.** Transport that single ternary digit leftward through the binary block by the
   value-preserving rules `𝒜`, one swap at a time (`auxA_swap`), until it reaches the boundary `◁`,
   then resolve it into binary by `ℬ` (`carry_sweep`). The string is all-binary again, so the next
   dynamic redex is exposed.

The net effect of one round is `config wₙ bₙ →* config wₙ₊₁ bₙ₊₁` with
`(cval wₙ₊₁, bₙ₊₁) = macroStep (cval wₙ, bₙ)`. Chaining gives `antihydraSRS_realizes_orbit`: for as
long as the macro model has not halted (`macroIter n (cval w₀, b₀) = some (aₙ, bₙ)`), the SRS *derives*
`config wₙ bₙ` with `cval wₙ = aₙ`. Re-expressed against the deterministic value orbit this is
`antihydraSRS_realizes_valOrbit` (`cval wₙ = valOrbit (cval w₀) n`), and combined with the backward
`antihydraSRS_simulates` it yields the **exact** orbit characterization `antihydraSRS_orbit_exact`:
the orbit is realised *and* nothing else is reachable.

Here `cval w = compFun w 1` is the value of `◁ w ▷ cᵇ`; on all-binary `w` it is the natural number
whose binary expansion (most-significant-bit first) is `1 :: w` (`f = 0`, `t = 1`), so `cval` is a
bijection from binary strings onto `{n ≥ 1}` and the value parity is read off the last symbol.

## References
* [YAH] E. Yolcu, S. Aaronson, M. J. H. Heule. *An Automated Approach to the Collatz Conjecture.*
  Journal of Automated Reasoning (2023); arXiv:2105.14697. §3.2, Theorem 3.17 (Claims 1–3).
* [BO93] R. V. Book, F. Otto. *String-Rewriting Systems.* Springer, 1993.
-/

namespace StringRewriting.AntihydraSRS

open StringRewriting StringRewriting.MixedBase ASym Relation

/-! ### Binary digit strings -/

/-- A **binary digit string**: a list of only the two binary symbols `f` (`= 0`) and `t` (`= 1`); the
"resolved" form of a configuration's middle part, with no ternary result digits `d0,d1,d2` and no
markers. On such a string the value `cval w` is the number with binary expansion `1 :: w`. -/
@[category API, AMS 68, ref "YAH", group "antihydra_srs"]
def IsBinary (w : List ASym) : Prop := ∀ s ∈ w, s = f ∨ s = t

/-- A binary string is in particular a digit string, so it inherits the structural lemmas of
`SRS.AntihydraSRSSimulation`. -/
@[category API, AMS 68, ref "YAH", group "antihydra_srs"]
theorem IsBinary.isDigits {w : List ASym} (h : IsBinary w) : IsDigits w := by
  intro s hs; rcases h s hs with h | h
  · exact Or.inl h
  · exact Or.inr (Or.inl h)

/-- Extending a binary string by a binary symbol keeps it binary. -/
@[category API, AMS 68, ref "YAH", group "antihydra_srs"]
theorem IsBinary.snoc {w : List ASym} {s : ASym} (hw : IsBinary w) (hs : s = f ∨ s = t) :
    IsBinary (w ++ [s]) := by
  intro u hu
  rcases List.mem_append.mp hu with hu | hu
  · exact hw u hu
  · rw [List.mem_singleton.mp hu]; exact hs

/-- A nonempty binary string splits off its last (least-significant) symbol: `w = p ++ [s]` with `s`
binary and `p` binary. This is what lets us read the value parity off the last symbol (`f` → even,
`t` → odd) and feed `p` to the carry sweep. -/
@[category API, AMS 68, ref "YAH", group "antihydra_srs"]
theorem IsBinary.exists_snoc {w : List ASym} (hw : IsBinary w) (hne : w ≠ []) :
    ∃ p s, w = p ++ [s] ∧ (s = f ∨ s = t) ∧ IsBinary p := by
  rcases w.eq_nil_or_concat with h | ⟨p, s, h⟩
  · exact absurd h hne
  · rw [List.concat_eq_append] at h; subst h
    exact ⟨p, s, rfl, hw s (by simp), fun u hu => hw u (by simp [hu])⟩

/-! ### Lifting auxiliary derivations to the full system -/

/-- A single value-preserving (`𝒳`) rewrite is a single `antihydraSRS` rewrite (`𝒳 ⊆ 𝒟 ∪ 𝒳`). -/
@[category API, AMS 68, ref "BO93", group "antihydra_srs"]
theorem auxStep_to_antihydra {u v : List ASym} (h : RewriteStep auxRules u v) :
    RewriteStep antihydraSRS u v := by
  obtain ⟨pre, post, ℓ, r, hrule, hu, hv⟩ := h
  exact ⟨pre, post, ℓ, r, Or.inr hrule, hu, hv⟩

/-- A value-preserving (`𝒳`) derivation is an `antihydraSRS`-derivation (`ReflTransGen` monotonicity).
This is how the carry sweep, built purely from `𝒳`, plugs into the full simulation. -/
@[category API, AMS 68, ref "BO93", group "antihydra_srs", formal_uses auxStep_to_antihydra]
theorem auxDeriv_to_antihydra {u v : List ASym}
    (h : ReflTransGen (RewriteStep auxRules) u v) :
    ReflTransGen (RewriteStep antihydraSRS) u v :=
  ReflTransGen.mono (fun _ _ hab => auxStep_to_antihydra hab) _ _ h

/-! ### The carry sweep

The transport rules `𝒜` swap a binary symbol with the ternary digit to its right, moving the ternary
digit one place left while preserving the composite value (`auxA_swap`). Iterating, a single ternary
digit produced by a dynamic step is carried all the way to the boundary `◁` and resolved into binary
by `ℬ` (`carry_sweep`). -/

/-- **One transport swap** (`𝒜`, value-preserving). For a binary symbol `s` and a ternary digit `dk`
there are a unique ternary digit `dj` and binary symbol `sj` with `s dk → dj sj` a rule of `𝒜`, and
the swap preserves the composite map: `β_dk ∘ β_s = β_sj ∘ β_dj`. (The six instances are
`f0→0f, f1→0t, f2→1f, t0→1t, t1→2f, t2→2t`.) -/
@[category API, AMS 68, ref "YAH", group "antihydra_srs"]
theorem auxA_swap {s : ASym} (hs : s = f ∨ s = t) {dk : ASym}
    (hk : dk = d0 ∨ dk = d1 ∨ dk = d2) :
    ∃ dj sj, (dj = d0 ∨ dj = d1 ∨ dj = d2) ∧ (sj = f ∨ sj = t) ∧ auxA [s, dk] [dj, sj] ∧
      ∀ y, symFun dk (symFun s y) = symFun sj (symFun dj y) := by
  rcases hs with rfl | rfl <;> rcases hk with rfl | rfl | rfl
  · exact ⟨d0, f, by tauto, by tauto, by unfold auxA; tauto, fun y => by simp only [symFun, beta]; ring⟩
  · exact ⟨d0, t, by tauto, by tauto, by unfold auxA; tauto, fun y => by simp only [symFun, beta]; ring⟩
  · exact ⟨d1, f, by tauto, by tauto, by unfold auxA; tauto, fun y => by simp only [symFun, beta]; ring⟩
  · exact ⟨d1, t, by tauto, by tauto, by unfold auxA; tauto, fun y => by simp only [symFun, beta]; ring⟩
  · exact ⟨d2, f, by tauto, by tauto, by unfold auxA; tauto, fun y => by simp only [symFun, beta]; ring⟩
  · exact ⟨d2, t, by tauto, by tauto, by unfold auxA; tauto, fun y => by simp only [symFun, beta]; ring⟩

/-- **The carry sweep** ([YAH] Claim 3, carry-propagation step). Given a binary prefix `p` and a single
ternary digit `dk` sitting just to its right (the digit a dynamic step produces), the value-preserving
rules `𝒳` derive `◁ p dk · rest →* ◁ q · rest` for a binary string `q` of the same value
`cval q = β_dk(cval p)`. So one dynamic step followed by one carry sweep returns the digit block to
all-binary form, re-exposing the next dynamic redex.

The proof is induction on `p` from the right: the rightmost binary symbol `s` of `p` swaps with `dk`
(`auxA_swap`, one `𝒜` step), moving the ternary digit one place left, and the induction hypothesis
sweeps it the rest of the way; the base case `p = []` resolves `◁ dk` by a single `ℬ` step. Value
preservation of each swap (`auxA_swap`) keeps `cval q = β_dk(cval p)` throughout. -/
@[category research solved, AMS 68 11, ref "YAH", group "antihydra_srs", formal_uses auxA_swap]
theorem carry_sweep : ∀ (p : List ASym), IsBinary p → ∀ (dk : ASym),
    (dk = d0 ∨ dk = d1 ∨ dk = d2) → ∀ (rest : List ASym),
    ∃ q, IsBinary q ∧ cval q = symFun dk (cval p) ∧
      ReflTransGen (RewriteStep auxRules) (lhd :: (p ++ dk :: rest)) (lhd :: (q ++ rest)) := by
  intro p
  induction p using List.reverseRecOn with
  | nil =>
    intro _hp dk hk rest
    rcases hk with rfl | rfl | rfl
    · exact ⟨[t], fun s hs => Or.inr (List.mem_singleton.mp hs), by decide,
        ReflTransGen.single ⟨[], rest, [lhd, d0], [lhd, t], Or.inr (Or.inl ⟨rfl, rfl⟩), by simp, by simp⟩⟩
    · exact ⟨[f, f], by intro s hs; fin_cases hs <;> tauto, by decide,
        ReflTransGen.single ⟨[], rest, [lhd, d1], [lhd, f, f], Or.inr (Or.inr (Or.inl ⟨rfl, rfl⟩)), by simp, by simp⟩⟩
    · exact ⟨[f, t], by intro s hs; fin_cases hs <;> tauto, by decide,
        ReflTransGen.single ⟨[], rest, [lhd, d2], [lhd, f, t], Or.inr (Or.inr (Or.inr ⟨rfl, rfl⟩)), by simp, by simp⟩⟩
  | append_singleton p' s ih =>
    intro hp dk hk rest
    have hsbin : s = f ∨ s = t := hp s (by simp)
    have hp' : IsBinary p' := fun u hu => hp u (by simp [hu])
    obtain ⟨dj, sj, hdj, hsj, hrule, hval⟩ := auxA_swap hsbin hk
    have step1 : RewriteStep auxRules (lhd :: (p' ++ s :: dk :: rest))
        (lhd :: (p' ++ dj :: sj :: rest)) := by
      refine ⟨lhd :: p', rest, [s, dk], [dj, sj], Or.inl hrule, ?_, ?_⟩ <;> simp
    obtain ⟨q', hq'bin, hq'val, hq'sweep⟩ := ih hp' dj hdj (sj :: rest)
    refine ⟨q' ++ [sj], hq'bin.snoc hsj, ?_, ?_⟩
    · rw [cval_snoc, hq'val, ← hval (cval p'), cval_snoc]
    · have hstart : lhd :: ((p' ++ [s]) ++ dk :: rest) = lhd :: (p' ++ s :: dk :: rest) := by simp
      have hend : lhd :: (q' ++ sj :: rest) = lhd :: ((q' ++ [sj]) ++ rest) := by simp
      rw [hstart, ← hend]
      exact ReflTransGen.head step1 hq'sweep

/-! ### The macro orbit as an `Option` iteration

`macroIter n` iterates the partial macro step `macroStep`; `macroIter n (a₀, b₀) = some (aₙ, bₙ)` is
exactly the statement that the macro model has not halted within `n` steps, and then `(aₙ, bₙ)` is the
state after `n` steps. This is the non-halting witness the forward simulation consumes. -/

/-- Iterate the partial macro step `macroStep` `n` times, threading the halt (`none`). -/
@[category API, AMS 11 68, ref "YAH", group "antihydra_srs"]
def macroIter : ℕ → (ℕ × ℕ) → Option (ℕ × ℕ)
  | 0, s => some s
  | n + 1, s => macroIter n s >>= macroStep

/-- One unfolding of `macroIter`. -/
@[category API, AMS 11, ref "YAH", group "antihydra_srs"]
theorem macroIter_succ (n : ℕ) (s : ℕ × ℕ) :
    macroIter (n + 1) s = macroIter n s >>= macroStep := rfl

/-! ### The forward simulation -/

/-- **The Antihydra SRS realises the macro orbit** ([YAH] Claim 3, progress / liveness). Starting from
an all-binary configuration `config w₀ b₀` of value `≥ 2`, for as long as the macro model has not
halted (`macroIter n (cval w₀, b₀) = some (aₙ, bₙ)`) the SRS *derives* a configuration `config wₙ bₙ`
whose value and counter are exactly the macro state `(aₙ, bₙ)` after `n` steps, with `wₙ` again
all-binary (ready for the next step).

This is the constructive converse of `antihydraSRS_simulates`: that result says every reachable
configuration lies on the orbit; this one says the orbit is actually walked, step by step, by the
"dynamic step then carry sweep" strategy. The induction is on `n`: a single round splits `wₙ` at its
last symbol (`exists_snoc`), fires the parity-appropriate dynamic step (`config_even_step` /
`config_odd_step`, the odd one needing `bₙ ≥ 1`, which non-halting supplies), then carries the
produced ternary digit to all-binary form (`carry_sweep`, lifted by `auxDeriv_to_antihydra`). -/
@[category research solved, AMS 68 11, ref "YAH", group "antihydra_srs",
  formal_uses carry_sweep auxDeriv_to_antihydra config_even_step config_odd_step]
theorem antihydraSRS_realizes_orbit (w₀ : List ASym) (hw₀ : IsBinary w₀) (b₀ : ℕ)
    (ha₀ : 2 ≤ cval w₀) :
    ∀ (n aₙ bₙ : ℕ), macroIter n (cval w₀, b₀) = some (aₙ, bₙ) →
      ∃ wₙ, IsBinary wₙ ∧ cval wₙ = aₙ ∧ 2 ≤ cval wₙ ∧
        ReflTransGen (RewriteStep antihydraSRS) (config w₀ b₀) (config wₙ bₙ) := by
  intro n
  induction n with
  | zero =>
    intro aₙ bₙ hiter
    simp only [macroIter] at hiter
    obtain ⟨rfl, rfl⟩ : cval w₀ = aₙ ∧ b₀ = bₙ := by simpa using hiter
    exact ⟨w₀, hw₀, rfl, ha₀, ReflTransGen.refl⟩
  | succ n ih =>
    intro aₙ₁ bₙ₁ hiter
    rw [macroIter_succ] at hiter
    rcases hmn : macroIter n (cval w₀, b₀) with _ | ⟨aₙ, bₙ⟩
    · rw [hmn] at hiter; simp at hiter
    · rw [hmn] at hiter
      replace hiter : macroStep (aₙ, bₙ) = some (aₙ₁, bₙ₁) := hiter
      obtain ⟨wₙ, hwₙbin, hwₙval, hwₙge, hwₙderiv⟩ := ih aₙ bₙ hmn
      have hne : wₙ ≠ [] := by rintro rfl; exact absurd hwₙge (by decide)
      obtain ⟨p, s, rfl, hsbin, hpbin⟩ := hwₙbin.exists_snoc hne
      have hcp : 1 ≤ cval p := by
        rcases hsbin with rfl | rfl <;>
          (have h2 := hwₙge; rw [cval_snoc] at h2; simp only [symFun, beta] at h2; omega)
      rcases hsbin with rfl | rfl
      · -- even value: last symbol `f`, `cval (p ++ [f]) = 2 · cval p`
        have haₙ : aₙ = 2 * cval p := by rw [← hwₙval, cval_snoc]; simp [symFun, beta]
        have hms : macroStep (aₙ, bₙ) = some (3 * cval p, bₙ + 2) := by
          rw [haₙ]; exact macroStep_even (cval p) bₙ
        have hcombine : some (3 * cval p, bₙ + 2) = some (aₙ₁, bₙ₁) := by rw [← hms]; exact hiter
        obtain ⟨rfl, rfl⟩ : 3 * cval p = aₙ₁ ∧ bₙ + 2 = bₙ₁ := by simpa using hcombine
        obtain ⟨q, hqbin, hqval, hqsweep⟩ :=
          carry_sweep p hpbin d0 (Or.inl rfl) (rhd :: List.replicate (bₙ + 2) c)
        have hsweep' : ReflTransGen (RewriteStep antihydraSRS)
            (config (p ++ [d0]) (bₙ + 2)) (config q (bₙ + 2)) := by
          have h := auxDeriv_to_antihydra hqsweep
          rwa [show config (p ++ [d0]) (bₙ + 2)
                = lhd :: (p ++ d0 :: (rhd :: List.replicate (bₙ + 2) c)) by
                simp [config, List.append_assoc],
              show config q (bₙ + 2) = lhd :: (q ++ (rhd :: List.replicate (bₙ + 2) c)) by
                simp [config]]
        refine ⟨q, hqbin, ?_, ?_, ?_⟩
        · rw [hqval]; simp [symFun, beta]
        · rw [hqval]; simp only [symFun, beta]; omega
        · exact hwₙderiv.trans (ReflTransGen.head (config_even_step p bₙ) hsweep')
      · -- odd value: last symbol `t`, `cval (p ++ [t]) = 2 · cval p + 1`; needs counter `≥ 1`
        have haₙ : aₙ = 2 * cval p + 1 := by rw [← hwₙval, cval_snoc]; simp [symFun, beta]
        have hbₙ : bₙ ≠ 0 := by
          intro h0; rw [haₙ, h0, macroStep_halt (cval p)] at hiter; simp at hiter
        obtain ⟨b', rfl⟩ : ∃ b', bₙ = b' + 1 := ⟨bₙ - 1, by omega⟩
        have hms : macroStep (aₙ, b' + 1) = some (3 * cval p + 1, b') := by
          rw [haₙ]; exact macroStep_odd (cval p) b'
        have hcombine : some (3 * cval p + 1, b') = some (aₙ₁, bₙ₁) := by rw [← hms]; exact hiter
        obtain ⟨rfl, rfl⟩ : 3 * cval p + 1 = aₙ₁ ∧ b' = bₙ₁ := by simpa using hcombine
        obtain ⟨q, hqbin, hqval, hqsweep⟩ :=
          carry_sweep p hpbin d1 (Or.inr (Or.inl rfl)) (rhd :: List.replicate b' c)
        have hsweep' : ReflTransGen (RewriteStep antihydraSRS)
            (config (p ++ [d1]) b') (config q b') := by
          have h := auxDeriv_to_antihydra hqsweep
          rwa [show config (p ++ [d1]) b'
                = lhd :: (p ++ d1 :: (rhd :: List.replicate b' c)) by
                simp [config, List.append_assoc],
              show config q b' = lhd :: (q ++ (rhd :: List.replicate b' c)) by simp [config]]
        refine ⟨q, hqbin, ?_, ?_, ?_⟩
        · rw [hqval]; simp [symFun, beta]
        · rw [hqval]; simp only [symFun, beta]; omega
        · exact hwₙderiv.trans (ReflTransGen.head (config_odd_step p b') hsweep')

/-- The macro value after `n` non-halting steps is the deterministic value orbit `valOrbit a₀ n`
(`macroStep`'s value component is `valStep` on either branch, `macroStep_value`). This bridges the
`Option`-iterate `macroIter` to the `valOrbit` used by the backward theorem. -/
@[category research solved, AMS 11, ref "YAH", group "antihydra_srs", formal_uses macroStep_value]
theorem macroIter_fst_eq_valOrbit (a₀ b₀ : ℕ) :
    ∀ (n aₙ bₙ : ℕ), macroIter n (a₀, b₀) = some (aₙ, bₙ) → aₙ = valOrbit a₀ n := by
  intro n
  induction n with
  | zero =>
    intro aₙ bₙ hiter; simp only [macroIter] at hiter
    obtain ⟨rfl, rfl⟩ : a₀ = aₙ ∧ b₀ = bₙ := by simpa using hiter
    rfl
  | succ n ih =>
    intro aₙ₁ bₙ₁ hiter
    rw [macroIter_succ] at hiter
    rcases hmn : macroIter n (a₀, b₀) with _ | ⟨aₙ, bₙ⟩
    · rw [hmn] at hiter; simp at hiter
    · rw [hmn] at hiter
      replace hiter : macroStep (aₙ, bₙ) = some (aₙ₁, bₙ₁) := hiter
      rw [valOrbit_succ, ← ih aₙ bₙ hmn]; exact macroStep_value hiter

/-- **The Antihydra SRS realises the value orbit.** Repackaging of `antihydraSRS_realizes_orbit`
against the deterministic value orbit: for as long as the macro model has not halted, the SRS derives
`config wₙ bₙ` with `cval wₙ = valOrbit (cval w₀) n`. -/
@[category research solved, AMS 68 11, ref "YAH", group "antihydra_srs",
  formal_uses antihydraSRS_realizes_orbit macroIter_fst_eq_valOrbit]
theorem antihydraSRS_realizes_valOrbit (w₀ : List ASym) (hw₀ : IsBinary w₀) (b₀ : ℕ)
    (ha₀ : 2 ≤ cval w₀) (n aₙ bₙ : ℕ) (hiter : macroIter n (cval w₀, b₀) = some (aₙ, bₙ)) :
    ∃ wₙ, IsBinary wₙ ∧ cval wₙ = valOrbit (cval w₀) n ∧
      ReflTransGen (RewriteStep antihydraSRS) (config w₀ b₀) (config wₙ bₙ) := by
  obtain ⟨wₙ, hbin, hval, _, hderiv⟩ := antihydraSRS_realizes_orbit w₀ hw₀ b₀ ha₀ n aₙ bₙ hiter
  exact ⟨wₙ, hbin, by rw [hval]; exact macroIter_fst_eq_valOrbit (cval w₀) b₀ n aₙ bₙ hiter, hderiv⟩

/-- **Exact orbit characterization.** Combining the forward simulation with the backward
`antihydraSRS_simulates`: along a non-halting orbit, (1) the orbit value `valOrbit (cval w₀) n` *is*
realised by a configuration the SRS derives, and (2) conversely *every* configuration reachable from
`config w₀ b₀` lies at some orbit value `valOrbit (cval w₀) k`. So the configurations reachable from
`config w₀ b₀` are exactly the orbit configurations — the SRS simulates the integer orbit exactly. -/
@[category research solved, AMS 68 11, ref "YAH", group "antihydra_srs",
  formal_uses antihydraSRS_realizes_valOrbit antihydraSRS_simulates]
theorem antihydraSRS_orbit_exact (w₀ : List ASym) (hw₀ : IsBinary w₀) (b₀ : ℕ)
    (ha₀ : 2 ≤ cval w₀) (n aₙ bₙ : ℕ) (hiter : macroIter n (cval w₀, b₀) = some (aₙ, bₙ)) :
    (∃ wₙ, IsBinary wₙ ∧ cval wₙ = valOrbit (cval w₀) n ∧
        ReflTransGen (RewriteStep antihydraSRS) (config w₀ b₀) (config wₙ bₙ)) ∧
    (∀ C, ReflTransGen (RewriteStep antihydraSRS) (config w₀ b₀) C →
        ∃ k w b, C = config w b ∧ cval w = valOrbit (cval w₀) k) := by
  refine ⟨antihydraSRS_realizes_valOrbit w₀ hw₀ b₀ ha₀ n aₙ bₙ hiter, ?_⟩
  intro C hC
  obtain ⟨k, w, b, hCeq, _, hcval, _⟩ := antihydraSRS_simulates w₀ b₀ hw₀.isDigits hC
  exact ⟨k, w, b, hCeq, hcval⟩

/-- **Concrete instance: the Antihydra value `8`.** The initial digit block `fff` has value `8`
(`cval [f,f,f] = 8`, the binary `1000`). So from `config [f,f,f] b₀` the SRS realises the value orbit
`valOrbit 8 n` for every non-halting prefix — the forward simulation applied at the Antihydra start
value. -/
@[category research solved, AMS 68 11, ref "YAH", group "antihydra_srs",
  formal_uses antihydraSRS_realizes_valOrbit]
theorem antihydraSRS_realizes_orbit_from_eight (b₀ n aₙ bₙ : ℕ)
    (hiter : macroIter n (8, b₀) = some (aₙ, bₙ)) :
    ∃ wₙ, IsBinary wₙ ∧ cval wₙ = valOrbit 8 n ∧
      ReflTransGen (RewriteStep antihydraSRS) (config [f, f, f] b₀) (config wₙ bₙ) := by
  have hbin : IsBinary [f, f, f] := by intro s hs; fin_cases hs <;> tauto
  have key := antihydraSRS_realizes_valOrbit [f, f, f] hbin b₀ (by decide) n aₙ bₙ hiter
  rwa [show cval [f, f, f] = 8 from by decide] at key

end StringRewriting.AntihydraSRS
