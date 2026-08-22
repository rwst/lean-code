/-
(C) 2026 Ralf Stephan, in collaboration with Claude Code.
Released under CC0 1.0 Universal (public-domain dedication).
See https://creativecommons.org/publicdomain/zero/1.0/
-/
import BB13.CensusSweep
import BB13.Subspace
import BB13.TwoAdicRigidity
import AB.SubspaceTheorem
import Mathlib.NumberTheory.Padics.PadicIntegers

/-!
# The 2-adic limit point: the rigidity half delivered, the Problem-2 half priced (B5)

Item **B5** of `plans/report3-BB13.html` (§4 "the Z-number-shaped limit", §6 B5, §7): the last
untouched entry of the attack order, rated `5%`.  Its brief has two halves.

* **The rigidity half** it *owns* after `CB1`: "no integer is a self-referential `3^α`" — i.e.
  per-`k` finiteness of `SelfRef` (`BB13/TwoAdicRigidity.lean`), which `CB1` declared "not
  elementary … precisely the 2-adic transcendence question of strategy B5".
* **The Problem-2 half**: convert the negation of Problem 2 into digit statistics of the single
  unit `λ = 3^α ∈ ℤ₂ˣ` and attack it with 2-adic Mahler's method / rigid-analytic transcendence on
  `3^{ℤ₂}`, or with subword-complexity obstructions.

## The rigidity half is a theorem, and the finishing move is archimedean

The whole of `CB1`'s residue collapses to **one inequality**, `selfRef_abs_resid_le`:

  `SelfRef k a → |kₐ| ≤ |k|`.

Reason: `SelfRef k a` says `3ᵃ − k = 2^{a+2}M`, so `k = 3ᵃ − (4M)·2ᵃ` is *one of the integers the
rounding competes with*, and `kₐ` is by definition the smallest of them (`round_le`).  Three
consequences, at three strengths:

* `selfRef_isFailure` — a self-referential `k` inside the corridor `|k| < (3/2)ᵃ` forces `a ∈ 𝓔`.
  So the self-referential indices of *any* `k` are exceptions from `log_{3/2}|k|` on.
* `exists_selfRef_height_bound`, `selfRef_finite`, `no_selfRef_limit` — with `failures_bounded`
  (the corpus's Subspace/Ridout lane) this gives **per-`k` finiteness**: for every `k` the set
  `{a : SelfRef k a}` is finite, of size bounded by `max(N₀, 2·⌈|k|⌉)`.  *No integer is a
  self-referential `3^α`.*  That is B5's own first deliverable, and it needed no 2-adic
  transcendence at all — so `CB1`'s "not established … precisely the 2-adic transcendence
  question of strategy B5" is itself the report's error (`CB28`).
* `selfRef_height_of_rate` / `selfRef_height_zudilin` — the *effective* form: any rate
  `cᵃ ≤ |kₐ|` transports verbatim to `cᵃ ≤ |k|`.  At [Zud07]'s `c = 2·0.5803` this reads
  `a ≤ log|k| / log 1.1606 = 4.653·log₂|k|`; on `CB1`'s own counterexample
  `k = 359212078195` the bound is `a ≤ 178` — and the chain there is `1, 5, 37`, three
  members, against `selfRef_gap`'s next-member floor `37 + 2³⁷`.
* `selfRef_census` — and inside the certified range the statement is unconditional: a corridor
  `k` self-referential at `1 ≤ a ≤ 10⁵` forces `a ∈ {1,2,3,4,7}` (`failures_up_to_100000`).

The contrast that pins the phenomenon: **finite chains of every length exist** — `selfChain`,
`selfChain_selfRef`, the tower `1, 3, 11, 2059, …` of B4's `exists_selfRef_pair` — but no infinite
one does, because along a chain `|k| ≥ (3/2)^{aⱼ}` grows while `k` is fixed.  The obstruction is
archimedean, not 2-adic; a purely 2-adic argument cannot exist, since `SelfApprox` (the same
condition read at a point of `ℤ₂`) *is* satisfiable at every length.

## The Problem-2 half: three separate walls

1. **The proposed tool has no hypothesis.**  `three_pow_reach_iff`: for every `m ≥ 3`, an integer
   is congruent to a power of `3` mod `2ᵐ` **iff** it is `≡ 1` or `3 (mod 8)`.  So the closure of
   `3^ℕ` in `ℤ₂` — the "curve" `3^{ℤ₂}` the strategy wants to do rigid-analytic transcendence on —
   is an **open subgroup of index 2**, and `λ ∈ 3^{ℤ₂}` is two bits of information.  It contains
   algebraic points densely: `eleven_mem_closure`, `11 = 3^α` for an `α ∈ ℤ₂ \ ℕ`
   (`eleven_reached`, `eleven_not_three_pow`).  No transcendence statement of the form "`3^α` is
   irrational/transcendental for `α ∉ ℕ`" is available, because it is false.

2. **The anchored runs do not survive the passage to the limit** (`CB29`).  `λ`'s digits below
   position `M` are those of `3^{aⱼ}` only when `2^M ∣ α − aⱼ` in `ℤ₂`; the exception's block
   starts at `≈0.585aⱼ`, so a *usable* transfer needs `2^R ∣ α − aⱼ` with `2^R > |k_{aⱼ}|`.  Two
   indices that both transfer are then tower-separated, `a' ≥ a + (3/2)ᵃ`
   (`block_transfer_gap`).  Compactness supplies a limit point but no lock: the limit condenses at
   most a tower-thin subchain of `𝓔`, and "run density `≥ 0.415` along a scale sequence" does not
   follow from the negation of Problem 2.

3. **The approximation exponent is `1.70951`, and Ridout's threshold is `2`.**  An exception
   supplies an integer of height `< (3/2)ᵃ` approximating `λ` to 2-adic precision `2^{-(a+w)}`,
   i.e. exponent `(a+w)/(a·log₂(3/2)) → 1/log₂(3/2) = 1.70951`.  `corridor_exponent_lt_two`: as
   soon as `6·v₂(mₐ) ≤ a` — which `vTwo_eventually_lt` makes eventual — the corridor bound
   *provably* fails to reach exponent `2`.  Conversely `ridout_forces_rate`: reaching it at `a`
   with `10·v₂(mₐ) ≤ a` forces `‖(3/2)ᵃ‖ < 0.733ᵃ`, strictly sharper than Problem 1's own `3/4`.
   The route would fire for the family at any threshold `c < 1/√2 = 0.70711`, a window
   (`ridout_window`) that is nonempty above [Zud07]'s floor `0.5803` but does **not** contain
   `3/4`.  Reaching exponent `2` needs `v₂(mₐ) ≥ 0.16993a`; the report's own §3 theorem
   `v₂(mₐ) = o(a)` forbids that, and in the data the last index meeting it is `a = 5`.

4. **What the AB machinery gives is transcendence, not a contradiction.**  The anchored block is a
   `ConditionStar` witness: `bitAt_const_of_isFailure` (the block, in digit form, from
   `filter_bits`) and `transcendental_of_anchored_blocks` (the bridge to
   `AB.transcendental_of_conditionStar`, [AB07] Theorem 6 via Schlickewei) give — for a digit
   sequence with blocks `[Rⱼ, Rⱼ+Lⱼ)`, `Rⱼ ≤ 3·⌊Lⱼ/2⌋`, not eventually periodic — that the
   `p`-adic value is transcendental.  The two halves are deliberately *not* joined here: joining
   them is exactly the lock of wall 2, which is unavailable.  And even joined, "λ is
   transcendental" contradicts nothing.

**Verdict.**  Rigidity half **delivered**; Problem-2 half **0% by this route**.  Re-rating
`5% → done (half) + closed (half)`.

## Footprint

`std3` for 24 of the 29 theorems.  Three (`exists_selfRef_height_bound`, `selfRef_finite`,
`no_selfRef_limit`) carry `Subspace.evertseSchlickewei` through `failures_bounded`
(`BB13/Subspace.lean`, the Corvaja–Zannier/Subspace lane); `shallow_eventually` carries
`BugeaudEvertse.ridout_line_cover` through Theorem D; `transcendental_of_anchored_blocks` carries
`AB.transcendental_of_conditionStar`.  All three are cited axioms already in the corpus; **no new
axiom is introduced here**.  In particular `selfRef_census` is `std3` — `census_scan_100000` is
axiom-free — so the unconditional statement inside the certified range costs nothing.

## References
* [AB07] B. Adamczewski, Y. Bugeaud, *On the complexity of algebraic numbers I*, Ann. of Math. 165
  (2007), 547–565 — §6, Theorem 6 (the `p`-adic stammering criterion).
* [Bug12] Y. Bugeaud, *Distribution modulo one and Diophantine approximation*, 2012 — Prob. 10.13.
* [CZ04] P. Corvaja, U. Zannier, *On the length of the continued fraction …*, 2004 — the Subspace
  lane behind `failures_bounded`.
* [Sch77] H. P. Schlickewei, *The `p`-adic Thue–Siegel–Roth–Schmidt theorem*, Arch. Math. 29 (1977).
* [Zud07] W. Zudilin, *A new lower bound for `‖(3/2)ᵏ‖`*, J. Théor. Nombres Bordeaux 19 (2007).
-/

namespace BB13

open scoped Real

/-! ## §1  The height inequality, and per-`k` finiteness

`CB1`'s residue, in one line: a self-referential `k` is one of the integers the rounding competes
with, and `kₐ` is the winner. -/

/-- **`|kₐ|` is minimal among `|3ᵃ − N·2ᵃ|`.**  Immediate from `round_le`: `mₐ` is the nearest
integer to `(3/2)ᵃ`. -/
@[category API, AMS 11, ref "Bug12", group "bugeaud_10_13"]
theorem abs_resid_le_abs_sub (a : ℕ) (N : ℤ) :
    |((resid 3 2 a : ℤ) : ℝ)| ≤ |(((3 : ℤ) ^ a - N * 2 ^ a : ℤ) : ℝ)| := by
  have h2 : (0 : ℝ) < 2 ^ a := by positivity
  have hM : (Mnum 3 2 a : ℤ) = round (((3 : ℝ) / 2) ^ a) := by
    rw [Mnum]; norm_num
  have key : |((3 : ℝ) / 2) ^ a - (Mnum 3 2 a : ℝ)| ≤ |((3 : ℝ) / 2) ^ a - (N : ℝ)| := by
    rw [show ((Mnum 3 2 a : ℤ) : ℝ) = ((round (((3 : ℝ) / 2) ^ a) : ℤ) : ℝ) by rw [hM]]
    exact round_le (((3 : ℝ) / 2) ^ a) N
  have e1 : ((resid 3 2 a : ℤ) : ℝ) = (2 : ℝ) ^ a * (((3 : ℝ) / 2) ^ a - (Mnum 3 2 a : ℝ)) := by
    rw [resid]; push_cast; rw [div_pow]; field_simp
  have e2 : (((3 : ℤ) ^ a - N * 2 ^ a : ℤ) : ℝ) = (2 : ℝ) ^ a * (((3 : ℝ) / 2) ^ a - (N : ℝ)) := by
    push_cast; rw [div_pow]; field_simp
  rw [e1, e2, abs_mul, abs_mul, abs_of_pos h2]
  exact mul_le_mul_of_nonneg_left key (le_of_lt h2)

/-- **The height inequality.**  If `a` is self-referential for `k` then `|kₐ| ≤ |k|`: the
self-referential `k` is `3ᵃ − (4M)·2ᵃ`, one of the competitors of the rounding. -/
@[category research solved, AMS 11, ref "Bug12", group "bugeaud_10_13"]
theorem selfRef_abs_resid_le {k : ℤ} {a : ℕ} (h : SelfRef k a) :
    |((resid 3 2 a : ℤ) : ℝ)| ≤ |(k : ℝ)| := by
  obtain ⟨M, hM⟩ := h
  have hp : (2 : ℤ) ^ (a + 2) = 4 * 2 ^ a := by rw [pow_add]; ring
  rw [hp] at hM
  have hk2 : (3 : ℤ) ^ a - (4 * M) * 2 ^ a = k := by linear_combination hM
  have := abs_resid_le_abs_sub a (4 * M)
  rwa [hk2] at this

/-- **A self-referential `k` inside the corridor forces an exception.**  With `|k| < (3/2)ᵃ` the
height inequality gives `|kₐ| < (3/2)ᵃ`, which *is* `‖(3/2)ᵃ‖ < (3/4)ᵃ`. -/
@[category research solved, AMS 11, ref "Bug12", group "bugeaud_10_13"]
theorem selfRef_isFailure {k : ℤ} {a : ℕ} (h : SelfRef k a) (hk : |(k : ℝ)| < ((3 : ℝ) / 2) ^ a) :
    IsFailure 3 2 (3 / 4) a := by
  have h1 := selfRef_abs_resid_le h
  have h2 : |((resid 3 2 a : ℤ) : ℝ)| < ((3 : ℝ) / 2) ^ a := lt_of_le_of_lt h1 hk
  rw [IsFailure]
  have hc : ((3 : ℝ) / 4 * ((2 : ℕ) : ℝ)) ^ a = ((3 : ℝ) / 2) ^ a := by norm_num
  rw [hc]
  exact h2

/-- **Per-`k` finiteness, boundedness form.**  Past the (ineffective) threshold `N₀` of
`failures_bounded`, every self-referential `k` at `a` satisfies `(3/2)ᵃ ≤ |k|`.  Contrapositive of
`selfRef_isFailure`. -/
@[category research solved, AMS 11, ref "CZ04" "Bug12", group "bugeaud_10_13"]
theorem exists_selfRef_height_bound :
    ∃ N₀ : ℕ, ∀ (k : ℤ) (a : ℕ), N₀ ≤ a → SelfRef k a → ((3 : ℝ) / 2) ^ a ≤ |(k : ℝ)| := by
  obtain ⟨N₀, hN₀⟩ := failures_bounded
  refine ⟨N₀, fun k a ha h => ?_⟩
  by_contra hlt
  exact hN₀ a ha (selfRef_isFailure h (not_le.mp hlt))

/-- **`CB1`'s residue, resolved: for every `k` only finitely many indices are self-referential.**
The set is contained in `[0, max(N₀, 2B+1))` for any natural `B > |k|`, by Bernoulli
`1 + a/2 ≤ (3/2)ᵃ`.  Equivalently: *no integer is a self-referential `3^α`* — B5's own first
deliverable, obtained from the archimedean side. -/
@[category research solved, AMS 11, ref "CZ04" "Bug12", group "bugeaud_10_13"]
theorem selfRef_finite (k : ℤ) : {a : ℕ | SelfRef k a}.Finite := by
  obtain ⟨N₀, hN₀⟩ := exists_selfRef_height_bound
  obtain ⟨B, hB⟩ := exists_nat_gt |(k : ℝ)|
  refine Set.Finite.subset (Set.finite_Iio (max N₀ (2 * B + 1))) ?_
  intro a ha
  simp only [Set.mem_setOf_eq] at ha
  by_contra hge
  simp only [Set.mem_Iio, not_lt] at hge
  have h1 : N₀ ≤ a := le_trans (le_max_left _ _) hge
  have h2 : 2 * B + 1 ≤ a := le_trans (le_max_right _ _) hge
  have hb := hN₀ k a h1 ha
  have hBer : (1 : ℝ) + (a : ℝ) * (1 / 2) ≤ ((3 : ℝ) / 2) ^ a := by
    have h := one_add_mul_le_pow (show (-2 : ℝ) ≤ 1 / 2 by norm_num) a
    rwa [show (1 : ℝ) + 1 / 2 = 3 / 2 by norm_num] at h
  have ha' : ((2 * B + 1 : ℕ) : ℝ) ≤ (a : ℝ) := by exact_mod_cast h2
  push_cast at ha'
  linarith

/-- **No integer is a self-referential `3^α`.**  The `Set.Infinite` phrasing of `selfRef_finite`:
an infinite self-referential chain for a fixed `k` — the object whose exclusion `CB1` called "the
2-adic transcendence question of strategy B5" — does not exist. -/
@[category research solved, AMS 11, ref "CZ04" "Bug12", group "bugeaud_10_13"]
theorem no_selfRef_limit (k : ℤ) : ¬ {a : ℕ | SelfRef k a}.Infinite :=
  fun h => h (selfRef_finite k)

/-- **The effective form.**  Any archimedean rate `cᵃ ≤ |kₐ|` transports verbatim to the height of
a self-referential `k`.  Reading it backwards bounds `a` by `log|k| / log c`. -/
@[category research solved, AMS 11, ref "Bug12", group "bugeaud_10_13"]
theorem selfRef_height_of_rate {c : ℝ} {k : ℤ} {a : ℕ}
    (hrate : c ^ a ≤ |((resid 3 2 a : ℤ) : ℝ)|) (h : SelfRef k a) : c ^ a ≤ |(k : ℝ)| :=
  le_trans hrate (selfRef_abs_resid_le h)

/-- **At [Zud07]'s constant.**  `c = 2·0.5803 = 5803/5000`: a self-referential `k` has
`|k| ≥ 1.1606ᵃ`, i.e. `a ≤ log|k| / log 1.1606 = 4.653·log₂|k|`.  On `CB1`'s counterexample
(`|k| ≈ 3.59·10¹¹`, bit length `39`) the bound is `a ≤ 182`; the witnesses are `a = 5, 37`. -/
@[category research solved, AMS 11, ref "Zud07" "Bug12", group "bugeaud_10_13"]
theorem selfRef_height_zudilin {k : ℤ} {a : ℕ}
    (hrate : ((5803 : ℝ) / 5000) ^ a ≤ |((resid 3 2 a : ℤ) : ℝ)|) (h : SelfRef k a) :
    ((5803 : ℝ) / 5000) ^ a ≤ |(k : ℝ)| :=
  selfRef_height_of_rate hrate h

/-- **Unconditional inside the certified range.**  A corridor `k` self-referential at
`1 ≤ a ≤ 10⁵` forces `a ∈ {1,2,3,4,7}` — `selfRef_isFailure` against the kernel census
`failures_up_to_100000`.  This strengthens B4's `no_selfRef_failure_le_256`, which only ruled out
`k = kₐ`. -/
@[category research solved, AMS 11, ref "Bug12" "DD90", group "bugeaud_10_13"]
theorem selfRef_census {k : ℤ} {a : ℕ} (h1 : 1 ≤ a) (h2 : a ≤ 100000) (h : SelfRef k a)
    (hk : |(k : ℝ)| < ((3 : ℝ) / 2) ^ a) : a = 1 ∨ a = 2 ∨ a = 3 ∨ a = 4 ∨ a = 7 :=
  (failures_up_to_100000 a h1 h2).mp (selfRef_isFailure h hk)

/-! ### Finite chains of every length do exist

So the failure of the infinite chain is *not* a 2-adic phenomenon: it is the growth of `|k|`. -/

/-- The tower chain `1, 3, 11, 2059, …`: `c 0 = 1`, `c (j+1) = c j + 2^{c j}`.  It meets B4's
`selfRef_gap` with equality at every step. -/
@[category API, AMS 11, ref "Bug12", group "bugeaud_10_13"]
def selfChain : ℕ → ℕ
  | 0 => 1
  | j + 1 => selfChain j + 2 ^ selfChain j

@[category API, AMS 11, ref "Bug12", group "bugeaud_10_13"]
theorem selfChain_pos (j : ℕ) : 1 ≤ selfChain j := by
  induction j with
  | zero => simp [selfChain]
  | succ j ih => exact le_trans ih (Nat.le_add_right _ _)

@[category API, AMS 11, ref "Bug12", group "bugeaud_10_13"]
theorem selfChain_mono : ∀ {i j : ℕ}, i ≤ j → selfChain i ≤ selfChain j := by
  intro i j
  induction j with
  | zero =>
    intro h
    have hi : i = 0 := Nat.le_zero.mp h
    subst hi; exact le_rfl
  | succ j ih =>
    intro h
    rcases Nat.lt_or_ge i (j + 1) with hlt | hge
    · have h1 : selfChain i ≤ selfChain j := ih (by omega)
      exact le_trans h1 (Nat.le_add_right _ _)
    · have hij : i = j + 1 := by omega
      subst hij; exact le_rfl

/-- The chain is locked at every step: `2^{c i} ∣ c j − c i` for `i ≤ j`. -/
@[category research solved, AMS 11, ref "Bug12", group "bugeaud_10_13"]
theorem selfChain_dvd : ∀ {i j : ℕ}, i ≤ j → 2 ^ selfChain i ∣ selfChain j - selfChain i := by
  intro i j
  induction j with
  | zero =>
    intro h
    have hi : i = 0 := Nat.le_zero.mp h
    subst hi; simp
  | succ j ih =>
    intro h
    rcases Nat.lt_or_ge i (j + 1) with hlt | hge
    · have hij : i ≤ j := by omega
      have h1 := ih hij
      have h2 : selfChain i ≤ selfChain j := selfChain_mono hij
      have h3 : (2 : ℕ) ^ selfChain i ∣ 2 ^ selfChain j := pow_dvd_pow 2 h2
      have hdef : selfChain (j + 1) = selfChain j + 2 ^ selfChain j := rfl
      have hsplit : selfChain (j + 1) - selfChain i
          = (selfChain j - selfChain i) + 2 ^ selfChain j := by
        rw [hdef]; exact Nat.sub_add_comm h2
      rw [hsplit]
      exact dvd_add h1 h3
    · have hij : i = j + 1 := by omega
      subst hij; simp

/-- **Self-referential chains of every finite length.**  For each `J`, the single integer
`k = 3^{c J}` is self-referential at all of `c 0, c 1, …, c J` (B4's `exists_selfRef_pair`).  The
2-adic condition alone is therefore satisfiable at every length; what `selfRef_finite` excludes is
the *infinite* chain, and it excludes it archimedeanly, because `|k| ≥ (3/2)^{c j}` for all `j`
cannot hold with `k` fixed. -/
@[category research solved, AMS 11, ref "Bug12", group "bugeaud_10_13"]
theorem selfChain_selfRef (J : ℕ) : ∀ i ≤ J, SelfRef ((3 : ℤ) ^ selfChain J) (selfChain i) :=
  fun i hi =>
    (exists_selfRef_pair (selfChain_pos i) (selfChain_mono hi) (selfChain_dvd hi)).1

/-! ## §2  The target curve is open: no rigid-analytic transcendence on `3^{ℤ₂}` -/

/-- `3ⁿ ≡ 1` or `3 (mod 8)`. -/
@[category API, AMS 11, ref "Bug12", group "bugeaud_10_13"]
theorem three_pow_emod_eight (n : ℕ) : (3 : ℤ) ^ n % 8 = 1 ∨ (3 : ℤ) ^ n % 8 = 3 := by
  induction n with
  | zero => left; norm_num
  | succ n ih =>
    rcases ih with h | h
    · right; rw [pow_succ, Int.mul_emod, h]; norm_num
    · left; rw [pow_succ, Int.mul_emod, h]; norm_num

/-- **The reach of `3^ℕ` modulo `2ᵐ` is decided at `m = 3`.**  For `m ≥ 3`, if `k ≡ 3^0` or `3^1`
mod `8` then some power of `3` is congruent to `k` mod `2ᵐ`.  Lifting the exponent: the step
`n ↦ n + 2^{m−2}` moves `3ⁿ` by exactly `2ᵐ·odd`. -/
@[category research solved, AMS 11, ref "Bug12", group "bugeaud_10_13"]
theorem exists_three_pow_congr {k : ℤ} :
    ∀ m : ℕ, 3 ≤ m → ((2 : ℤ) ^ 3 ∣ 3 ^ (0 : ℕ) - k ∨ (2 : ℤ) ^ 3 ∣ 3 ^ (1 : ℕ) - k) →
      ∃ n : ℕ, (2 : ℤ) ^ m ∣ 3 ^ n - k := by
  intro m
  induction m with
  | zero => intro h; omega
  | succ m ih =>
    intro hm hbase
    rcases Nat.lt_or_ge m 3 with hlt | hge
    · have hm2 : m = 2 := by omega
      subst hm2
      rcases hbase with h | h
      · exact ⟨0, h⟩
      · exact ⟨1, h⟩
    · obtain ⟨n, hn⟩ := ih hge hbase
      by_cases hnext : (2 : ℤ) ^ (m + 1) ∣ 3 ^ n - k
      · exact ⟨n, hnext⟩
      · refine ⟨n + 2 ^ (m - 2), ?_⟩
        have hd1 : (2 : ℤ) ^ m ∣ 3 ^ (2 ^ (m - 2)) - 1 :=
          (two_pow_dvd_three_pow_sub_one_iff hge).mpr dvd_rfl
        have hd2 : ¬ ((2 : ℤ) ^ (m + 1) ∣ 3 ^ (2 ^ (m - 2)) - 1) := by
          intro hc
          have hdd := (two_pow_dvd_three_pow_sub_one_iff (by omega : 3 ≤ m + 1)).mp hc
          have hle : (2 : ℕ) ^ (m + 1 - 2) ≤ 2 ^ (m - 2) :=
            Nat.le_of_dvd (pow_pos (by norm_num) _) hdd
          have : (2 : ℕ) ^ (m - 2) < 2 ^ (m + 1 - 2) :=
            Nat.pow_lt_pow_right (by norm_num) (by omega)
          omega
        obtain ⟨s, hs⟩ := hd1
        obtain ⟨t, ht⟩ := hn
        have hsodd : Odd s := by
          rcases Int.even_or_odd s with he | ho
          · exfalso
            obtain ⟨s', hs'⟩ := he
            exact hd2 ⟨s', by rw [hs, hs']; ring⟩
          · exact ho
        have htodd : Odd t := by
          rcases Int.even_or_odd t with he | ho
          · exfalso
            obtain ⟨t', ht'⟩ := he
            exact hnext ⟨t', by rw [ht, ht']; ring⟩
          · exact ho
        have h3odd : Odd ((3 : ℤ) ^ n) := Odd.pow (by decide)
        have heven : Even ((3 : ℤ) ^ n * s + t) := (h3odd.mul hsodd).add_odd htodd
        obtain ⟨u, hu⟩ := heven
        refine ⟨u, ?_⟩
        have hexp : (3 : ℤ) ^ (n + 2 ^ (m - 2)) = 3 ^ n * 3 ^ (2 ^ (m - 2)) := pow_add 3 _ _
        have hkey : (3 : ℤ) ^ (n + 2 ^ (m - 2)) - k
            = 2 ^ m * ((3 : ℤ) ^ n * s + t) := by
          rw [hexp]
          have h1 : (3 : ℤ) ^ (2 ^ (m - 2)) = 2 ^ m * s + 1 := by linarith [hs]
          rw [h1]
          linear_combination ht
        rw [hkey, hu, pow_succ]
        ring

/-- **The reach is an iff.**  For `m ≥ 3`: `k` is congruent to a power of `3` mod `2ᵐ` **iff** it
is congruent to one mod `8`.  Equivalently, the closure of `3^ℕ` in `ℤ₂` is the open index-`2`
subgroup `{u : u ≡ 1, 3 (mod 8)}`. -/
@[category research solved, AMS 11, ref "Bug12", group "bugeaud_10_13"]
theorem three_pow_reach_iff {m : ℕ} (hm : 3 ≤ m) (k : ℤ) :
    (∃ n : ℕ, (2 : ℤ) ^ m ∣ 3 ^ n - k) ↔
      ((2 : ℤ) ^ 3 ∣ 3 ^ (0 : ℕ) - k ∨ (2 : ℤ) ^ 3 ∣ 3 ^ (1 : ℕ) - k) := by
  constructor
  · rintro ⟨n, hn⟩
    have h8 : (8 : ℤ) ∣ 3 ^ n - k := by
      have := dvd_trans (pow_dvd_pow (2 : ℤ) hm) hn
      simpa using this
    rcases three_pow_emod_eight n with h | h
    · left
      have : (8 : ℤ) ∣ (3 : ℤ) ^ n - 1 := by omega
      have : (8 : ℤ) ∣ 1 - k := by omega
      simpa using this
    · right
      have : (8 : ℤ) ∣ (3 : ℤ) ^ n - 3 := by omega
      have : (8 : ℤ) ∣ 3 - k := by omega
      simpa using this
  · exact exists_three_pow_congr m hm

/-- `11` is reached mod every `2ᵐ` (`11 ≡ 3 (mod 8)`), yet is no power of `3`: the "curve"
`3^{ℤ₂}` contains rational integers off `3^ℕ`. -/
@[category research solved, AMS 11, ref "Bug12", group "bugeaud_10_13"]
theorem eleven_reached (m : ℕ) : ∃ n : ℕ, (2 : ℤ) ^ m ∣ 3 ^ n - 11 := by
  rcases Nat.lt_or_ge m 3 with h | h
  · refine ⟨1, ?_⟩
    have : (2 : ℤ) ^ m ∣ 2 ^ 3 := pow_dvd_pow 2 (by omega)
    have h8 : (2 : ℤ) ^ 3 ∣ (3 : ℤ) ^ (1 : ℕ) - 11 := by norm_num
    exact dvd_trans this h8
  · exact exists_three_pow_congr m h (Or.inr (by norm_num))

@[category API, AMS 11, ref "Bug12", group "bugeaud_10_13"]
theorem eleven_not_three_pow (n : ℕ) : (3 : ℤ) ^ n ≠ 11 := by
  rcases Nat.lt_or_ge n 3 with h | h
  · interval_cases n <;> norm_num
  · have h27 : (27 : ℤ) ≤ 3 ^ n := by
      calc (27 : ℤ) = 3 ^ (3 : ℕ) := by norm_num
        _ ≤ 3 ^ n := pow_le_pow_right₀ (by norm_num) h
    omega

/-- **The strategy's target set contains algebraic points.**  In `ℤ₂`, `11` is a limit of powers of
`3` but is not one of them: `11 = 3^α` for an `α ∈ ℤ₂ \ ℕ`.  So no statement of the form "`3^α` is
transcendental (or even irrational) for `α ∉ ℕ`" is available, and rigid-analytic transcendence on
`3^{ℤ₂}` has no hypothesis to bite on. -/
@[category research solved, AMS 11, ref "Bug12", group "bugeaud_10_13"]
theorem eleven_mem_closure :
    (11 : ℤ_[2]) ∈ closure (Set.range fun n : ℕ => (3 : ℤ_[2]) ^ n) ∧
      (11 : ℤ_[2]) ∉ Set.range fun n : ℕ => (3 : ℤ_[2]) ^ n := by
  constructor
  · rw [Metric.mem_closure_iff]
    intro ε hε
    obtain ⟨m, hm⟩ := exists_pow_lt_of_lt_one hε (show (1 : ℝ) / 2 < 1 by norm_num)
    obtain ⟨n, hn⟩ := eleven_reached m
    refine ⟨(3 : ℤ_[2]) ^ n, ⟨n, rfl⟩, ?_⟩
    have hcast : (((3 ^ n - 11 : ℤ)) : ℤ_[2]) = (3 : ℤ_[2]) ^ n - 11 := by push_cast; ring
    have hnorm : ‖(((3 ^ n - 11 : ℤ)) : ℤ_[2])‖ ≤ ((2 : ℕ) : ℝ) ^ (-(m : ℤ)) :=
      PadicInt.norm_int_le_pow_iff_dvd.mpr (by exact_mod_cast hn)
    rw [hcast] at hnorm
    have hzp : ((2 : ℕ) : ℝ) ^ (-(m : ℤ)) = ((1 : ℝ) / 2) ^ m := by
      rw [zpow_neg, zpow_natCast, div_pow, one_pow, inv_eq_one_div]
      norm_num
    rw [hzp] at hnorm
    rw [dist_comm, dist_eq_norm]
    exact lt_of_le_of_lt hnorm hm
  · rintro ⟨n, hn⟩
    have hn' : (3 : ℤ_[2]) ^ n = 11 := hn
    have : (((3 ^ n - 11 : ℤ)) : ℤ_[2]) = 0 := by push_cast; rw [hn']; ring
    have hz : ((3 : ℤ) ^ n - 11 : ℤ) = 0 := by exact_mod_cast this
    exact eleven_not_three_pow n (by omega)

/-! ## §3  The lock: what the passage to the limit costs (`CB29`) -/

/-- **`a` approximates `α ∈ ℤ₂` self-referentially**: `2ᵃ ∣ α − a`.  This is B4's `SelfRef k a`
read at the point `α = log₃ k`, and in this language tower separation is transparent. -/
@[category API, AMS 11, ref "Bug12", group "bugeaud_10_13"]
def SelfApprox (α : ℤ_[2]) (a : ℕ) : Prop := (2 : ℤ_[2]) ^ a ∣ (α - (a : ℤ_[2]))

/-- **The lock, at arbitrary precision.**  Two integers that both sit within `2^{-R}` of the same
`α ∈ ℤ₂` are congruent mod `2ᴿ`. -/
@[category research solved, AMS 11, ref "Bug12", group "bugeaud_10_13"]
theorem lock_dvd_sub {α : ℤ_[2]} {a a' R R' : ℕ} (hRR : R ≤ R') (hle : a ≤ a')
    (h : (2 : ℤ_[2]) ^ R ∣ α - (a : ℤ_[2])) (h' : (2 : ℤ_[2]) ^ R' ∣ α - (a' : ℤ_[2])) :
    2 ^ R ∣ a' - a := by
  have h'' : (2 : ℤ_[2]) ^ R ∣ α - (a' : ℤ_[2]) := dvd_trans (pow_dvd_pow 2 hRR) h'
  have hsub : (2 : ℤ_[2]) ^ R ∣ (((a' : ℤ) - (a : ℤ) : ℤ) : ℤ_[2]) := by
    have := dvd_sub h h''
    have heq : (α - (a : ℤ_[2])) - (α - (a' : ℤ_[2])) = (((a' : ℤ) - (a : ℤ) : ℤ) : ℤ_[2]) := by
      push_cast; ring
    rwa [heq] at this
  have hz : ((2 : ℕ) ^ R : ℤ) ∣ ((a' : ℤ) - (a : ℤ)) := by
    have := (PadicInt.pow_p_dvd_int_iff (p := 2) R ((a' : ℤ) - (a : ℤ))).mp (by exact_mod_cast hsub)
    exact_mod_cast this
  have : ((2 ^ R : ℕ) : ℤ) ∣ ((a' - a : ℕ) : ℤ) := by
    rw [Nat.cast_sub hle]; exact_mod_cast hz
  exact_mod_cast this

/-- **`CB29`, the quantitative form.**  The anchored block of the exception `a` transfers to the
limit only if `α` is locked to `a` at precision `2ᴿ > |kₐ|`, i.e. `R ≳ 0.585a`.  Any two indices
whose blocks transfer are then separated by at least `2ᴿ ≥ (3/2)ᵃ`: the limit condenses at most a
**tower-thin** subchain of `𝓔`, not `𝓔` itself. -/
@[category research solved, AMS 11, ref "Bug12", group "bugeaud_10_13"]
theorem block_transfer_gap {α : ℤ_[2]} {a a' R R' : ℕ} (hRR : R ≤ R') (hlt : a < a')
    (hR : ((3 : ℝ) / 2) ^ a ≤ 2 ^ R)
    (h : (2 : ℤ_[2]) ^ R ∣ α - (a : ℤ_[2])) (h' : (2 : ℤ_[2]) ^ R' ∣ α - (a' : ℤ_[2])) :
    (a : ℝ) + ((3 : ℝ) / 2) ^ a ≤ (a' : ℝ) := by
  have hdvd := lock_dvd_sub hRR (le_of_lt hlt) h h'
  have hge : 2 ^ R ≤ a' - a := Nat.le_of_dvd (by omega) hdvd
  have hnat : a + 2 ^ R ≤ a' := by omega
  have hcast : ((a : ℝ)) + ((2 : ℝ)) ^ R ≤ (a' : ℝ) := by exact_mod_cast hnat
  linarith

/-! ## §4  The approximation exponent, and Ridout's threshold -/

/-- **The corridor can never reach Ridout's exponent `2`.**  An exception supplies a height
`|kₐ| < (3/2)ᵃ` at 2-adic precision `2^{a+v₂(mₐ)}`; the resulting exponent is
`(a+w)/(a·log₂(3/2)) → 1.70951 < 2`.  As soon as `6·v₂(mₐ) ≤ a` — eventual, by
`vTwo_eventually_lt` — the inequality `2^{a+w} < ((3/2)ᵃ)²` is a theorem, with the single
certificate `2¹⁹ < 3¹²` (`524288 < 531441`). -/
@[category research solved, AMS 11, ref "Bug12", group "bugeaud_10_13"]
theorem corridor_exponent_lt_two {a : ℕ} (ha : 1 ≤ a) (hw : 6 * vTwo a ≤ a) :
    (2 : ℝ) ^ (a + vTwo a) < (((3 : ℝ) / 2) ^ a) ^ 2 := by
  have key : (2 : ℕ) ^ (3 * a + vTwo a) < 3 ^ (a * 2) := by
    refine lt_of_pow_lt_pow_left₀ 6 (Nat.zero_le _) ?_
    calc ((2 : ℕ) ^ (3 * a + vTwo a)) ^ 6 = 2 ^ ((3 * a + vTwo a) * 6) := by rw [← pow_mul]
      _ ≤ 2 ^ (19 * a) := Nat.pow_le_pow_right (by norm_num) (by omega)
      _ = (2 ^ 19) ^ a := by rw [← pow_mul]
      _ < (3 ^ 12) ^ a := Nat.pow_lt_pow_left (by norm_num) (by omega)
      _ = 3 ^ (12 * a) := by rw [← pow_mul]
      _ = 3 ^ (a * 2 * 6) := by congr 1; ring
      _ = ((3 : ℕ) ^ (a * 2)) ^ 6 := by rw [pow_mul]
  have keyR : (2 : ℝ) ^ (3 * a + vTwo a) < 3 ^ (a * 2) := by exact_mod_cast key
  have hgoal : (((3 : ℝ) / 2) ^ a) ^ 2 = 3 ^ (a * 2) / 2 ^ (a * 2) := by
    rw [← pow_mul, div_pow]
  rw [hgoal, lt_div_iff₀ (show (0 : ℝ) < 2 ^ (a * 2) by positivity), ← pow_add,
    show a + vTwo a + a * 2 = 3 * a + vTwo a from by ring]
  exact keyR

/-- **What reaching the exponent would cost.**  If the Ridout condition `|kₐ|² < 2^{a+v₂(mₐ)}`
*does* hold at `a`, with `10·v₂(mₐ) ≤ a`, then `‖(3/2)ᵃ‖ < 0.733ᵃ` — strictly sharper than the
`3/4` of Problem 1.  Certificate: `2¹¹·1000²⁰ ≤ 1466²⁰`. -/
@[category research solved, AMS 11, ref "Bug12", group "bugeaud_10_13"]
theorem ridout_forces_rate {a : ℕ} (hw : 10 * vTwo a ≤ a)
    (hR : |((resid 3 2 a : ℤ) : ℝ)| ^ 2 < 2 ^ (a + vTwo a)) :
    IsFailure 3 2 (733 / 1000) a := by
  have hbase : (2 : ℝ) ^ 11 ≤ ((1466 : ℝ) / 1000) ^ 20 := by norm_num
  have hkey : |((resid 3 2 a : ℤ) : ℝ)| ^ 20 < (((1466 : ℝ) / 1000) ^ a) ^ 20 := by
    calc |((resid 3 2 a : ℤ) : ℝ)| ^ 20 = (|((resid 3 2 a : ℤ) : ℝ)| ^ 2) ^ 10 := by
          rw [← pow_mul]
      _ < ((2 : ℝ) ^ (a + vTwo a)) ^ 10 := pow_lt_pow_left₀ hR (by positivity) (by norm_num)
      _ = (2 : ℝ) ^ ((a + vTwo a) * 10) := by rw [← pow_mul]
      _ ≤ (2 : ℝ) ^ (11 * a) := pow_le_pow_right₀ (by norm_num) (by omega)
      _ = ((2 : ℝ) ^ 11) ^ a := by rw [← pow_mul]
      _ ≤ (((1466 : ℝ) / 1000) ^ 20) ^ a := pow_le_pow_left₀ (by positivity) hbase a
      _ = ((1466 : ℝ) / 1000) ^ (20 * a) := by rw [← pow_mul]
      _ = ((1466 : ℝ) / 1000) ^ (a * 20) := by congr 1; ring
      _ = (((1466 : ℝ) / 1000) ^ a) ^ 20 := by rw [pow_mul]
  have hlt : |((resid 3 2 a : ℤ) : ℝ)| < ((1466 : ℝ) / 1000) ^ a :=
    lt_of_pow_lt_pow_left₀ 20 (by positivity) hkey
  rw [IsFailure,
    show ((733 : ℝ) / 1000 * ((2 : ℕ) : ℝ)) ^ a = ((1466 : ℝ) / 1000) ^ a by norm_num]
  exact hlt

/-- The hypothesis of `corridor_exponent_lt_two` is eventual: `v₂(mₐ) = o(a)` (the report's §3
Theorem D) gives `10·v₂(mₐ) ≤ a` for all large `a`.  So the report's own theorem is what forbids
closing the exponent gap with the fibre depth. -/
@[category research solved, AMS 11, ref "BE08" "Bug12", group "bugeaud_10_13"]
theorem shallow_eventually : ∀ᶠ a : ℕ in Filter.atTop, 10 * vTwo a ≤ a := by
  filter_upwards [vTwo_eventually_lt (1 / 10) (by norm_num)] with a ha
  have h10 : (10 : ℝ) * (vTwo a : ℝ) < (a : ℝ) := by linarith
  have : ((10 * vTwo a : ℕ) : ℝ) < ((a : ℕ) : ℝ) := by push_cast; linarith
  exact le_of_lt (by exact_mod_cast this)

/-- **The window in which the Ridout route would fire.**  The exponent passes `2` exactly at rate
`1/√2 = 0.70711`, i.e. `c² = 1/2`.  That window is nonempty above [Zud07]'s floor `0.5803`, but it
does not contain Problem 1's own `3/4`. -/
@[category research solved, AMS 11, ref "Zud07" "Bug12", group "bugeaud_10_13"]
theorem ridout_window : ((5803 : ℝ) / 10000) ^ 2 < 1 / 2 ∧ (1 : ℝ) / 2 < ((3 : ℝ) / 4) ^ 2 := by
  constructor <;> norm_num

/-! ## §5  The digit side: the anchored block, and what [AB07] concludes from it -/

/-- The `i`-th binary digit of `x`. -/
@[category API, AMS 11, ref "AB07", group "bugeaud_10_13"]
def bitAt (x i : ℕ) : ℕ := x / 2 ^ i % 2

@[category API, AMS 11, ref "AB07", group "bugeaud_10_13"]
theorem bitAt_lt_two (x i : ℕ) : bitAt x i < 2 := Nat.mod_lt _ (by norm_num)

@[category API, AMS 11, ref "AB07", group "bugeaud_10_13"]
theorem bitAt_mod {x M i : ℕ} (h : i < M) : bitAt (x % 2 ^ M) i = bitAt x i := by
  have hsplit : (2 : ℕ) ^ M = 2 ^ i * 2 ^ (M - i) := by rw [← pow_add]; congr 1; omega
  have hdvd : (2 : ℕ) ∣ 2 ^ (M - i) := dvd_pow_self 2 (by omega)
  rw [bitAt, bitAt, hsplit, Nat.mod_mul_right_div_self, Nat.mod_mod_of_dvd _ hdvd]

/-- **The anchored block, in digit form.**  For an exception `n`, the binary digits of `3ⁿ` in the
window `[n − t, n)` are all equal, for every `t` with `41t ≤ 17n` (i.e. `t ≲ 0.4146n`).  This is
`filter_bits` read digitwise; it is the run the report's §4 wants to transport to the limit. -/
@[category research solved, AMS 11, ref "DD90" "Bug12", group "bugeaud_10_13"]
theorem bitAt_const_of_isFailure {n t i i' : ℕ} (hf : IsFailure 3 2 (3 / 4) n)
    (ht : 41 * t ≤ 17 * n) (h1 : n - t ≤ i) (h2 : i < n) (h1' : n - t ≤ i') (h2' : i' < n) :
    bitAt (3 ^ n) i = bitAt (3 ^ n) i' := by
  have hti : i - (n - t) < t := by omega
  have hti' : i' - (n - t) < t := by omega
  have step : ∀ j : ℕ, n - t ≤ j → j < n →
      bitAt (3 ^ n) j
        = (3 ^ n % 2 ^ n / 2 ^ (n - t) / 2 ^ (j - (n - t))) % 2 := by
    intro j hj1 hj2
    rw [← bitAt_mod (x := 3 ^ n) (M := n) hj2, bitAt, Nat.div_div_eq_div_mul, ← pow_add,
      show (n - t) + (j - (n - t)) = j by omega]
  have hq := filter_bits hf ht
  rw [step i h1 h2, step i' h1' h2']
  rcases hq with h0 | h1p
  · rw [h0]; simp
  · rw [h1p]
    have gen : ∀ j : ℕ, j < t → ((2 : ℕ) ^ t - 1) / 2 ^ j % 2 = 1 := by
      intro j hj
      have hA : 0 < (2 : ℕ) ^ j := pow_pos (by norm_num) _
      have hB : 0 < (2 : ℕ) ^ (t - j) := pow_pos (by norm_num) _
      have hsplit : (2 : ℕ) ^ t = 2 ^ j * 2 ^ (t - j) := by
        rw [← pow_add]; congr 1; omega
      have hmulpos : 0 < (2 : ℕ) ^ j * 2 ^ (t - j) := Nat.mul_pos hA hB
      have hAle : (2 : ℕ) ^ j ≤ 2 ^ j * 2 ^ (t - j) := Nat.le_mul_of_pos_right _ hB
      have e1 : ((2 : ℕ) ^ (t - j) - 1) * 2 ^ j = 2 ^ j * 2 ^ (t - j) - 2 ^ j := by
        rw [Nat.sub_mul, one_mul, Nat.mul_comm]
      have e2 : ((2 : ℕ) ^ (t - j) - 1 + 1) * 2 ^ j = 2 ^ j * 2 ^ (t - j) := by
        rw [Nat.sub_add_cancel hB, Nat.mul_comm]
      have hdiv : ((2 : ℕ) ^ t - 1) / 2 ^ j = 2 ^ (t - j) - 1 := by
        rw [hsplit]
        refine Nat.div_eq_of_lt_le ?_ ?_
        · rw [e1]; omega
        · rw [e2]; omega
      rw [hdiv]
      have hev : (2 : ℕ) ∣ 2 ^ (t - j) := dvd_pow_self 2 (by omega)
      omega
    rw [gen _ hti, gen _ hti']

/-- **The bridge to [AB07].**  A binary digit sequence with constant blocks `[Rⱼ, Rⱼ+Lⱼ)` whose
starts are bounded by three halves of the blocks (`Rⱼ ≤ 3⌊Lⱼ/2⌋`) satisfies Condition (∗)₂, hence
— if it is not eventually periodic — defines a **transcendental** 2-adic number.  Take
`Uⱼ` = the first `Rⱼ` digits and `Vⱼ` = a half-block; `Uⱼ Vⱼ²` is a prefix because the block is
constant.  Cited input: `AB.transcendental_of_conditionStar` ([AB07] Thm 6, via [Sch77]).

This is the strongest conclusion the subword-complexity route can reach, and it is **not** a
contradiction: `λ = 3^α` transcendental is consistent with everything.  Joining it to
`bitAt_const_of_isFailure` would additionally require the lock of `block_transfer_gap`. -/
@[category research solved, AMS 11 68, ref "AB07" "Sch77", group "bugeaud_10_13"]
theorem transcendental_of_anchored_blocks (d : ℕ → ℕ) (hd : ∀ i, d i < 2) (R L : ℕ → ℕ)
    (hpos : ∀ j, 0 < L j / 2) (hmono : StrictMono fun j => L j / 2)
    (hconst : ∀ j i i', R j ≤ i → i < R j + L j → R j ≤ i' → i' < R j + L j → d i = d i')
    (hratio : ∀ j, R j ≤ 3 * (L j / 2)) (hnep : ¬ AB.IsEventuallyPeriodic d) :
    Transcendental ℚ (AB.henselValue 2 0 d) := by
  refine AB.transcendental_of_conditionStar 2 0 d hd 2 (by norm_num) ⟨hnep, R, fun j => L j / 2,
    hpos, ?_, ⟨3, ?_⟩, hmono⟩
  · intro j i hi1 hi2
    have hfl : ⌊(2 : ℝ) * ((L j / 2 : ℕ) : ℝ)⌋₊ = 2 * (L j / 2) := by
      rw [show (2 : ℝ) * ((L j / 2 : ℕ) : ℝ) = ((2 * (L j / 2) : ℕ) : ℝ) by push_cast; ring,
        Nat.floor_natCast]
    rw [hfl] at hi2
    have hi1' : R j + L j / 2 ≤ i := hi1
    have hi2' : i < R j + 2 * (L j / 2) := hi2
    have hhalf : 2 * (L j / 2) ≤ L j := by omega
    show d i = d (i - L j / 2)
    exact hconst j i (i - L j / 2) (by omega) (by omega) (by omega) (by omega)
  · intro j
    have h := hratio j
    have : ((R j : ℕ) : ℝ) ≤ ((3 * (L j / 2) : ℕ) : ℝ) := by exact_mod_cast h
    push_cast at this ⊢
    linarith

end BB13
