/-
(C) 2026 Ralf Stephan, in collaboration with Claude Code.
Released under CC0 1.0 Universal (public-domain dedication).
See https://creativecommons.org/publicdomain/zero/1.0/
-/
import BB13.LeastException
import BB13.QualityLedger

/-!
# Thin sets: Q2.5's challenge on a subsequence (B9)

Item **B9** of `plans/report3-BB13.html` (§6 B9, §9): A2's thin-set probe AK (lifting the
exponent on `a = 2ˡ`) and A4's P2.5 (arithmetic progressions, automatic index sets, the density-1
target).  Rated 12%.  The precise challenge of Q2.5:

> exhibit an infinite `A` and a proof of `min(v₂(mₐ), D(a)) ≤ C` on `A` that does not go through
> a rate `‖(3/2)ᵃ‖ > cᵃ` with `c > 2^{−0.8}`.

## The challenge has three readings, and only one is live

* `A ⊆ 𝓔`: **vacuous**.  The exception set is finite (Mahler, `BB13.failures_finite_of_lineCover`),
  so no infinite `A` of exceptions exists at all — `no_infinite_exception_set`.
* `A ⊆ ℕ` with the `min`: **trivial**.  Off `𝓔` the dyadic surplus is negative
  (`surplus_neg_of_not_failure`), so `min(v₂, D) ≤ 0` on the complement of `𝓔`, a set of density
  one, and Mahler already supplies that.
* `A ⊆ ℕ` with the `v` arm alone, `v₂(mₐ) ≤ C`: **the real challenge**, and it is what Q2.1 asked
  for ("*any nontrivial unconditional upper bound on `v₂(mₐ)`, even along subsequences*").

## The challenge is met, with `C = 1`

B8's descent law `vTwo_succ_lt` (`v₂(mₙ) ≥ 2 ⟹ v₂(m_{n+1}) < v₂(mₙ)`) is all it takes.  Write
`Shallow = {n : v₂(mₙ) ≤ 1}`.  Then:

> **`shallow_gap`**: for every `n` some `n + j` with `j ≤ v₂(mₙ)` is shallow.

The valuation cannot rise above height `1` without descending one unit per step, so a shallow
index is never further away than the current height.  With the elementary row for the `v` arm,
`vTwo_le_of_arm` (`41·v₂(mₐ) ≤ 24a + 41`, the `0.5854` bound, from `3⁴¹ ≤ 2⁶⁵`), the gap becomes
*effective*:

> **`shallow_dyadic`**: every dyadic block `[2ⁱ, 2^{i+1})` contains a shallow index;
> **`shallow_ncard_ge`**: `#(Shallow ∩ [1, 2ⁱ]) ≥ i`, i.e. `#(Shallow ∩ [1,N]) ≥ log₂ N`;
> **`shallow_infinite`**, hence **`thin_set_challenge`**.

No rate, no Diophantine input, no exception hypothesis: the footprint of everything in §2 below is
`std3`.  On a line whose least member is shallow the fibre has at most two elements
(`shallow_fibre_le_two`).  Measured (`BB13/b9_thinsets.py` [B]): `Shallow` has density `0.7446` on
`[1, 2·10⁴]` and the largest gap there is `9`, so the proved gap bound `v₂(mₙ)` is loose by orders
of magnitude — but it is the only unconditional one available.

## No a-priori set can replace it — the transport theorem

The delivered set is defined by the sequence.  What A2 and A4 asked for is a set described in
advance: a residue class, `{2ˡ}`, an automatic set.  All of them die at one inequality.  Transport
between two indices is exact,

> **`pin_depth_iff`**: for `a ≤ b` and `M ≥ 3`, `2ᴹ ∣ 3ᵇ − 3ᵃ ↔ 2^{M−2} ∣ b − a`,

so the deepest fact about `3ᵇ` that *any* smaller index can supply sits at depth
`log₂(b − a) + 2 ≤ log₂ b + 2` (`pin_depth_le_log`), while `v₂(m_b) ≥ H` is a condition on `3ᵇ`
modulo `2^{b+H}` (`BB13.two_pow_dvd_three_pow_sub_resid_iff`).  Hence

> **`no_pair_reaches_window`**: for `a < b` and `H ≥ 2`, `2^{b+H} ∤ 3ᵇ − 3ᵃ`.

*No pair of indices ever reaches the other's window.*  This is uniform over all sets, so it prices
the three named candidates at once: a class mod `2ʲ` pins exactly `j + 2` bits and no more
(`class_pins`, `class_pins_no_more`, quantitatively `orderOf_three_pow_two_pow`: the class is a
subgroup of index `2ʲ` in `⟨3⟩ ≤ (ℤ/2ᴹ)ˣ`); AK's probe `A = {2ˡ}` pins exactly `l + 2 = log₂ a + 2`
bits (`lte_probe`) — it is therefore the *optimal* instance of the residue-class idea, not a weak
one; and an infinite automatic index set contains a pumped family `α2^{si} + β`, whose pairs are
covered by the same bound.

## And the sign is wrong anyway

The one thing pinning *would* buy points the other way:

> **`pinned_forces_vTwo_ge`**: if `2^{b+H} ∣ 3ᵇ − c` for a `c` in the residue corridor, then
> `v₂(m_b) ≥ H`.

A set whose members' windows are pinned to a fixed value is a set of *deep* indices, not shallow
ones — the thin-set route and its target have opposite signs.  Together: the window at `b` is
reachable only from `b` itself, and a hypothetical reach would produce the enemy rather than
exclude it.

## Density 1

A4's density-1 target is not available through the `v` arm at any fixed `C`: the density of
`{n : v₂(mₙ) ≥ C+1}` is `2^{−(C+1)} > 0` (measured, `b9_thinsets.py` [D]).  Off `𝓔` the `min` is
trivially negative, so "density 1" is a statement about `𝓔`, i.e. about Mahler, not about
Problem 2.  §4 brackets what is actually open here: `Shallow` is proved infinite, its complement
`{n : v₂(mₙ) ≥ 2}` is *not known to be infinite*, and the `v` arm is bounded as soon as that
complement is finite (`vArm_bounded_of_deep_finite`).  The gap between the two is the whole of
Problem 2's `v` half.

## Footprint

`std3` throughout, except `no_infinite_exception_set`, which consumes the root's cited Ridout
axiom through `BB13.failures_finite_of_lineCover` (it is the reading-(i) triviality, not a
mechanism).

## References

* [Bug12] Y. Bugeaud, *Distribution modulo one and Diophantine approximation*, Cambridge Tracts
  **193**, 2012 — Problem 10.13.
* [DD90] F. Delmer, J.-M. Deshouillers, *The computation of `g(k)` in Waring's problem*, Math.
  Comp. **54** (1990), 885–893.
* `plans/report3-BB13.html` §5 Q2.5, §6 B9, §9; `plans/note-BB13-B9.html` (the note);
  `BB13/b9_thinsets.py` (the evidence).
-/

namespace BB13

open scoped Real

/-! ## 1. The three readings of Q2.5's challenge -/

/-- **Reading (i) is vacuous**: there is no infinite set of exceptions, because `𝓔` is finite
(Mahler's theorem along the quantitative Ridout route, `BB13.failures_finite_of_lineCover`).  A
challenge quantified over exceptions has no instances to be met on. -/
@[category research solved, AMS 11, ref "BE08" "Bug12", group "bugeaud_10_13"]
theorem no_infinite_exception_set {A : Set ℕ} (hA : A.Infinite)
    (hsub : A ⊆ {n : ℕ | 1 ≤ n ∧ IsFailure 3 2 (3 / 4) n}) : False :=
  hA (failures_finite_of_lineCover.subset hsub)

/-- **Reading (ii) is trivial**: off the exceptions there is no dyadic surplus at all — not even
`d = 0` clears the fibre inequality — so `min(v₂(mₐ), D(a))` is negative there, and the
complement of `𝓔` is everything but five indices. -/
@[category research solved, AMS 11, ref "Bug12", group "bugeaud_10_13"]
theorem surplus_neg_of_not_failure {a : ℕ} (h : ¬ IsFailure 3 2 (3 / 4) a) :
    ¬ (2 ^ 0 * |resid 3 2 a| * 2 ^ a < 3 ^ a) := by
  rw [isFailure_iff_int] at h
  simpa using h

/-! ## 2. The delivered set: `Shallow = {n : v₂(mₙ) ≤ 1}`

Everything in this section is `std3` and uses no Diophantine input: only B8's descent law and the
elementary row `41·v₂(mₐ) ≤ 24a + 41`. -/

/-- **The shallow indices** `{n : v₂(mₙ) ≤ 1}` — the set on which Q2.5's challenge is met, with
`C = 1`. -/
def Shallow : Set ℕ := {n : ℕ | vTwo n ≤ 1}

@[category API, AMS 11, ref "Bug12", group "bugeaud_10_13"]
theorem mem_shallow_iff (n : ℕ) : n ∈ Shallow ↔ vTwo n ≤ 1 := Iff.rfl

/-- **The gap bound**, by induction along B8's descent law: from any `n` a shallow index is
reached within `v₂(mₙ)` steps.  Above height `1` the valuation drops by at least one at every
step (`BB13.vTwo_succ_lt`), so the walk cannot avoid height `≤ 1` for longer than its current
height. -/
private theorem exists_shallow_of_eq : ∀ w n : ℕ, vTwo n = w → ∃ j ≤ w, vTwo (n + j) ≤ 1 := by
  intro w
  induction w using Nat.strong_induction_on with
  | _ w ih =>
    intro n hn
    rcases le_or_gt (vTwo n) 1 with h | h
    · exact ⟨0, Nat.zero_le _, by simpa using h⟩
    · have hlt : vTwo (n + 1) < vTwo n := vTwo_succ_lt (by omega)
      obtain ⟨j, hj, hjs⟩ := ih (vTwo (n + 1)) (by omega) (n + 1) rfl
      exact ⟨j + 1, by omega, by rwa [show n + (j + 1) = n + 1 + j by ring]⟩

/-- **`shallow_gap`**: for every `n` there is a shallow index in `[n, n + v₂(mₙ)]`. -/
@[category research solved, AMS 11, ref "DD90" "Bug12", group "bugeaud_10_13"]
theorem shallow_gap (n : ℕ) : ∃ j ≤ vTwo n, n + j ∈ Shallow :=
  exists_shallow_of_eq (vTwo n) n rfl

/-- `2^{v₂(mₐ)+a} ≤ 2·3ᵃ`: the `v` arm sits inside the numerator, which sits inside `2·3ᵃ`. -/
@[category API, AMS 11, ref "Bug12", group "bugeaud_10_13"]
theorem two_pow_vTwo_add_le (a : ℕ) : 2 ^ (vTwo a + a) ≤ 2 * 3 ^ a := by
  have hdvd : 2 ^ vTwo a ∣ mNat a := (two_pow_dvd_Mnum_iff a (vTwo a)).mp (two_pow_vTwo_dvd a)
  have h1 : 2 ^ vTwo a ≤ mNat a := Nat.le_of_dvd (mNat_pos a) hdvd
  calc 2 ^ (vTwo a + a) = 2 ^ vTwo a * 2 ^ a := by rw [pow_add]
    _ ≤ mNat a * 2 ^ a := Nat.mul_le_mul_right _ h1
    _ ≤ 2 * 3 ^ a := mNat_mul_two_pow_le a

/-- **The elementary row for the `v` arm**: `41·v₂(mₐ) ≤ 24a + 41`, i.e. `v₂(mₐ) ≤ 0.5854a + 1`.
The companion of `BB13.depth_le_of_arm` on the other arm, through the same certificate
`3⁴¹ ≤ 2⁶⁵`; it is what makes `shallow_gap` effective. -/
@[category research solved, AMS 11, ref "Bug12", group "bugeaud_10_13"]
theorem vTwo_le_of_arm (a : ℕ) : 41 * vTwo a ≤ 24 * a + 41 := by
  have h1 : 2 ^ (vTwo a + a) ≤ 2 * 3 ^ a := two_pow_vTwo_add_le a
  have h2 : 2 ^ (41 * (vTwo a + a)) ≤ 2 ^ (41 + 65 * a) := by
    calc 2 ^ (41 * (vTwo a + a)) = (2 ^ (vTwo a + a)) ^ 41 := by
          rw [← pow_mul, Nat.mul_comm]
      _ ≤ (2 * 3 ^ a) ^ 41 := Nat.pow_le_pow_left h1 41
      _ = 2 ^ 41 * 3 ^ (41 * a) := by rw [Nat.mul_pow, ← pow_mul, Nat.mul_comm a 41]
      _ ≤ 2 ^ 41 * 2 ^ (65 * a) := Nat.mul_le_mul_left _ (three_pow_le_two_pow a)
      _ = 2 ^ (41 + 65 * a) := by rw [← pow_add]
  have := (Nat.pow_le_pow_iff_right (by norm_num : 1 < 2)).mp h2
  omega

/-- **The effective gap**: after `n` a shallow index arrives by `(65n + 41)/41`, i.e. by
`1.5854n + 1`. -/
@[category research solved, AMS 11, ref "DD90" "Bug12", group "bugeaud_10_13"]
theorem shallow_within (n : ℕ) : ∃ j, n ≤ j ∧ 41 * j ≤ 65 * n + 41 ∧ j ∈ Shallow := by
  obtain ⟨i, hi, hs⟩ := shallow_gap n
  have := vTwo_le_of_arm n
  exact ⟨n + i, Nat.le_add_right _ _, by omega, hs⟩

/-- **Every dyadic block carries a shallow index**: `Shallow ∩ [2ⁱ, 2^{i+1}) ≠ ∅` for every `i`.
For `i ≥ 2` this is `shallow_within` (`65·2ⁱ + 41 < 82·2ⁱ`); the two small blocks are the census
values `v₂(m₁) = v₂(m₂) = 1`. -/
@[category research solved, AMS 11, ref "DD90" "Bug12", group "bugeaud_10_13"]
theorem shallow_dyadic (i : ℕ) : ∃ j, 2 ^ i ≤ j ∧ j < 2 ^ (i + 1) ∧ j ∈ Shallow := by
  match i with
  | 0 => exact ⟨1, by norm_num, by norm_num, by simp [Shallow, vTwo_census.1]⟩
  | 1 => exact ⟨2, by norm_num, by norm_num, by simp [Shallow, vTwo_census.2.1]⟩
  | (k + 2) =>
    obtain ⟨j, hj1, hj2, hj3⟩ := shallow_within (2 ^ (k + 2))
    refine ⟨j, hj1, ?_, hj3⟩
    have h4 : (4 : ℕ) ≤ 2 ^ (k + 2) := by
      calc (4 : ℕ) = 2 ^ 2 := by norm_num
        _ ≤ 2 ^ (k + 2) := Nat.pow_le_pow_right (by norm_num) (by omega)
    have hpow : 2 ^ (k + 2 + 1) = 2 * 2 ^ (k + 2) := by rw [pow_succ]; ring
    omega

/-- **`Shallow` is infinite** — Q2.5's challenge, met with `C = 1` and no rate. -/
@[category research solved, AMS 11, ref "DD90" "Bug12", group "bugeaud_10_13"]
theorem shallow_infinite : Shallow.Infinite := by
  apply Set.infinite_of_not_bddAbove
  rintro ⟨B, hB⟩
  obtain ⟨j, hj1, -, hj3⟩ := shallow_dyadic (B + 1)
  have hle : j ≤ B := hB hj3
  have : B + 1 < 2 ^ (B + 1) := Nat.lt_two_pow_self
  omega

/-- **Q2.5's challenge, in one line**: an infinite set of indices on which the `v` arm is at most
`1`, proved without any rate for `‖(3/2)ᵃ‖` — indeed without any Diophantine input whatever. -/
@[category research solved, AMS 11, ref "DD90" "Bug12", group "bugeaud_10_13"]
theorem thin_set_challenge : ∃ A : Set ℕ, A.Infinite ∧ ∀ a ∈ A, vTwo a ≤ 1 :=
  ⟨Shallow, shallow_infinite, fun _ h => h⟩

/-- **The count**: `#(Shallow ∩ [1, 2ⁱ]) ≥ i`, i.e. `#(Shallow ∩ [1,N]) ≥ ⌊log₂ N⌋`.  One witness
per dyadic block, and the blocks are disjoint. -/
@[category research solved, AMS 11, ref "DD90" "Bug12", group "bugeaud_10_13"]
theorem shallow_ncard_ge (i : ℕ) : i ≤ (Shallow ∩ Set.Icc 1 (2 ^ i)).ncard := by
  classical
  choose f hf1 hf2 hf3 using shallow_dyadic
  have hmono : StrictMono f := by
    intro s t hst
    calc f s < 2 ^ (s + 1) := hf2 s
      _ ≤ 2 ^ t := Nat.pow_le_pow_right (by norm_num) (by omega)
      _ ≤ f t := hf1 t
  have hfin : (Shallow ∩ Set.Icc 1 (2 ^ i)).Finite :=
    (Set.finite_Icc 1 (2 ^ i)).subset Set.inter_subset_right
  have hsub : ↑((Finset.range i).image f) ⊆ Shallow ∩ Set.Icc 1 (2 ^ i) := by
    intro x hx
    simp only [Finset.coe_image, Finset.coe_range, Set.mem_image, Set.mem_Iio] at hx
    obtain ⟨t, ht, rfl⟩ := hx
    refine ⟨hf3 t, le_trans Nat.one_le_two_pow (hf1 t), ?_⟩
    have h1 : f t < 2 ^ (t + 1) := hf2 t
    have h2 : (2 : ℕ) ^ (t + 1) ≤ 2 ^ i := Nat.pow_le_pow_right (by norm_num) (by omega)
    omega
  have := Set.ncard_le_ncard hsub hfin
  rwa [Set.ncard_coe_finset, Finset.card_image_of_injective _ hmono.injective,
    Finset.card_range] at this

/-- **What it buys on the fibre**: a line whose least member is shallow carries at most two
exceptions.  (`BB13.lineFibre_card_le_vTwo` at `v₂ ≤ 1`.) -/
@[category research solved, AMS 11, ref "Bug12", group "bugeaud_10_13"]
theorem shallow_fibre_le_two {r : ℚ} {a : ℕ} (ha : a ∈ lineFibre r)
    (hmin : ∀ b ∈ lineFibre r, a ≤ b) (hs : a ∈ Shallow) : (lineFibre r).ncard ≤ 2 := by
  have := lineFibre_card_le_vTwo ha hmin
  have hs' : vTwo a ≤ 1 := hs
  omega

/-! ## 3. Transport: what one index can tell another

The window that carries `v₂(m_b)` sits at depth `b + H` (`two_pow_dvd_three_pow_sub_resid_iff`).
This section computes exactly how deep a *comparison with another index* can reach, and finds
`log₂ b + 2`. -/

/-- **The transport identity**, in divisibility form: for `a ≤ b` and `M ≥ 3`,
`2ᴹ ∣ 3ᵇ − 3ᵃ ↔ 2^{M−2} ∣ b − a`.  (Equivalently `v₂(3ᵇ − 3ᵃ) = v₂(b − a) + 2` for `b − a` even,
`= 1` for `b − a` odd — verified on all pairs `0 ≤ a < b ≤ 200` in `b9_thinsets.py` [E].)  The `3ᵃ`
factor is invisible at `2`, so this is `BB13.two_pow_dvd_three_pow_sub_one_iff` transported. -/
@[category research solved, AMS 11, ref "Bug12", group "bugeaud_10_13"]
theorem pin_depth_iff {a b M : ℕ} (hab : a ≤ b) (hM : 3 ≤ M) :
    ((2 : ℤ) ^ M ∣ 3 ^ b - 3 ^ a) ↔ 2 ^ (M - 2) ∣ (b - a) := by
  have hsplit : (3 : ℤ) ^ b - 3 ^ a = 3 ^ a * (3 ^ (b - a) - 1) := by
    rw [mul_sub, mul_one, ← pow_add, Nat.add_sub_cancel' hab]
  have hcop : IsCoprime ((2 : ℤ) ^ M) ((3 : ℤ) ^ a) :=
    IsCoprime.pow (by rw [Int.isCoprime_iff_gcd_eq_one]; norm_num)
  rw [hsplit, ← two_pow_dvd_three_pow_sub_one_iff hM]
  exact ⟨fun h => hcop.dvd_of_dvd_mul_left h, fun h => Dvd.dvd.mul_left h _⟩

/-- **Transport is at most logarithmic**: if `2ᴹ ∣ 3ᵇ − 3ᵃ` with `a < b` then `2^{M−2} ≤ b − a`. -/
@[category research solved, AMS 11, ref "Bug12", group "bugeaud_10_13"]
theorem pin_depth_le {a b M : ℕ} (hab : a < b) (hM : 3 ≤ M)
    (h : (2 : ℤ) ^ M ∣ 3 ^ b - 3 ^ a) : 2 ^ (M - 2) ≤ b - a :=
  Nat.le_of_dvd (by omega) ((pin_depth_iff hab.le hM).mp h)

/-- **The information bound**: a comparison of `3ᵇ` with any earlier `3ᵃ` reaches depth at most
`log₂ b + 2`.  The window that decides `v₂(m_b)` sits at depth `b + H`. -/
@[category research solved, AMS 11, ref "Bug12", group "bugeaud_10_13"]
theorem pin_depth_le_log {a b M : ℕ} (hab : a < b) (hM : 3 ≤ M)
    (h : (2 : ℤ) ^ M ∣ 3 ^ b - 3 ^ a) : M ≤ Nat.log 2 b + 2 := by
  have h1 : 2 ^ (M - 2) ≤ b := le_trans (pin_depth_le hab hM h) (Nat.sub_le b a)
  have h2 : M - 2 ≤ Nat.log 2 b :=
    (Nat.le_log_iff_pow_le (by norm_num) (by omega)).mpr h1
  omega

/-- **No pair of indices ever reaches the other's window.**  For `a < b` and `H ≥ 2`,
`2^{b+H} ∤ 3ᵇ − 3ᵃ`: the transported depth would have to be `2^{b+H−2} ≤ b − a < b`, and
`b < 2ᵇ`.  This is the whole B9 no-go, and it is uniform over *all* index sets — residue classes,
`{2ˡ}`, automatic sets and everything else. -/
@[category research solved, AMS 11, ref "Bug12" "DD90", group "bugeaud_10_13"]
theorem no_pair_reaches_window {a b H : ℕ} (hab : a < b) (hH : 2 ≤ H) :
    ¬ ((2 : ℤ) ^ (b + H) ∣ 3 ^ b - 3 ^ a) := by
  intro h
  have hle := pin_depth_le hab (by omega) h
  have hb : b < 2 ^ b := Nat.lt_two_pow_self
  have hmono : (2 : ℕ) ^ b ≤ 2 ^ (b + H - 2) := Nat.pow_le_pow_right (by norm_num) (by omega)
  omega

/-- **No set pins a window**: for any `A` with an element below `b`, the members of `A` do not
determine `3ᵇ` to the depth `b + H` that `v₂(m_b) ≥ H` lives at. -/
@[category research solved, AMS 11, ref "Bug12" "DD90", group "bugeaud_10_13"]
theorem no_set_pins_window {A : Set ℕ} {b H : ℕ} (hH : 2 ≤ H) (ha : ∃ a ∈ A, a < b) :
    ¬ (∀ a ∈ A, (2 : ℤ) ^ (b + H) ∣ 3 ^ b - 3 ^ a) := by
  obtain ⟨a, haA, hab⟩ := ha
  exact fun h => no_pair_reaches_window hab hH (h a haA)

/-! ### The three named candidates -/

/-- **A residue class mod `2ʲ` pins `j + 2` bits**: `a ≡ b (mod 2ʲ)` gives
`3ᵃ ≡ 3ᵇ (mod 2^{j+2})`. -/
@[category research solved, AMS 11, ref "Bug12", group "bugeaud_10_13"]
theorem class_pins {j a b : ℕ} (hj : 1 ≤ j) (hab : a ≤ b) (h : 2 ^ j ∣ b - a) :
    (2 : ℤ) ^ (j + 2) ∣ 3 ^ b - 3 ^ a := by
  refine (pin_depth_iff hab (by omega)).mpr ?_
  simpa using h

/-- **…and not one bit more.**  The two class members `r` and `r + 2ʲ` are not congruent modulo
`2^{j+3}` — so the pinned depth of a class mod `2ʲ` is *exactly* `j + 2`, a constant, while the
window at `a` moves out to depth `a`. -/
@[category research solved, AMS 11, ref "Bug12", group "bugeaud_10_13"]
theorem class_pins_no_more (j r : ℕ) :
    ¬ ((2 : ℤ) ^ (j + 3) ∣ 3 ^ (r + 2 ^ j) - 3 ^ r) := by
  intro h
  have hpos : 0 < (2 : ℕ) ^ j := Nat.two_pow_pos j
  have hle := pin_depth_le (a := r) (b := r + 2 ^ j) (by omega) (by omega) h
  have : (2 : ℕ) ^ (j + 1) ≤ 2 ^ j := by
    simpa [Nat.add_sub_cancel_left, show j + 3 - 2 = j + 1 by omega] using hle
  have hlt : (2 : ℕ) ^ j < 2 ^ (j + 1) := Nat.pow_lt_pow_right (by norm_num) (by omega)
  omega

/-- **The index count behind the last two statements**: the powers `3^a` with `a` in a fixed class
mod `2ʲ` form a coset of a subgroup of index `2ʲ` in `⟨3⟩ ≤ (ℤ/2ᴹ)ˣ`, of order `2^{M−2−j}`.  A
class therefore gives away exactly `j` of the `M − 2` bits of the orbit, uniformly in `M`. -/
@[category research solved, AMS 11, ref "Bug12", group "bugeaud_10_13"]
theorem orderOf_three_pow_two_pow {M j : ℕ} (hM : 3 ≤ M) (hj : j ≤ M - 2) :
    orderOf ((3 : ZMod (2 ^ M)) ^ (2 ^ j)) = 2 ^ (M - 2 - j) := by
  have hord := orderOf_three_zmod hM
  rw [orderOf_pow_of_dvd (by positivity) (hord ▸ pow_dvd_pow 2 hj), hord,
    Nat.pow_div hj (by norm_num)]

/-- **A2's probe AK, exactly**: lifting the exponent gives `v₂(3^{2ˡ} − 1) = l + 2`, so the index
set `{2ˡ}` pins `log₂ a + 2` bits of `3ᵃ` and no more.  Since `class_pins`/`class_pins_no_more`
cap every class mod `2ʲ` at `j + 2`, the probe is the **optimal** instance of the residue-class
idea, not a weak one — and `log₂ a + 2` against a window at depth `a` is A2's own verdict. -/
@[category research solved, AMS 11, ref "Bug12", group "bugeaud_10_13"]
theorem lte_probe (l : ℕ) (hl : 1 ≤ l) :
    ((2 : ℤ) ^ (l + 2) ∣ 3 ^ (2 ^ l) - 1) ∧ ¬ ((2 : ℤ) ^ (l + 3) ∣ 3 ^ (2 ^ l) - 1) := by
  constructor
  · exact (two_pow_dvd_three_pow_sub_one_iff (by omega)).mpr (by simp)
  · intro h
    have h2 := (two_pow_dvd_three_pow_sub_one_iff (m := l + 3) (by omega)).mp h
    have hle : (2 : ℕ) ^ (l + 1) ≤ 2 ^ l := by
      simpa [show l + 3 - 2 = l + 1 by omega] using Nat.le_of_dvd (by positivity) h2
    have hlt : (2 : ℕ) ^ l < 2 ^ (l + 1) := Nat.pow_lt_pow_right (by norm_num) (by omega)
    omega

/-! ### The reversal: pinning produces the enemy

Not only is the window unreachable — reaching it would be the wrong thing to do.  A `b` whose
window is pinned to a fixed value in the residue corridor has a *deep* `v` arm. -/

/-- The residue is the unique corridor representative: if `2ᵇ ∣ 3ᵇ − c` and `2|c| < 2ᵇ`, then
`c = k_b`. -/
@[category API, AMS 11, ref "Bug12", group "bugeaud_10_13"]
theorem resid_eq_of_corridor {b : ℕ} {c : ℤ} (hc : 2 * |c| < 2 ^ b)
    (h : (2 : ℤ) ^ b ∣ 3 ^ b - c) : c = resid 3 2 b := by
  have hk : (2 : ℤ) ^ b ∣ 3 ^ b - resid 3 2 b := ⟨Mnum 3 2 b, by rw [three_pow_sub_resid]; ring⟩
  have hdvd : (2 : ℤ) ^ b ∣ resid 3 2 b - c := by
    have := dvd_sub h hk
    simpa using this
  have habs : |resid 3 2 b - c| < 2 ^ b := by
    have h1 := two_mul_abs_resid_le b
    have h2 : |resid 3 2 b - c| ≤ |resid 3 2 b| + |c| := abs_sub _ _
    linarith
  have := Int.eq_zero_of_abs_lt_dvd hdvd habs
  linarith [sub_eq_zero.mp this]

/-- **The reversal.**  If the window of `3ᵇ` is pinned to a corridor value `c` down to depth
`b + H`, then `v₂(m_b) ≥ H`: the pinned indices are exactly the *deep* ones.  So a thin set that
did control its members' windows would exhibit tall fibres, not exclude them — the route's method
and its target have opposite signs. -/
@[category research solved, AMS 11, ref "Bug12" "DD90", group "bugeaud_10_13"]
theorem pinned_forces_vTwo_ge {b H : ℕ} {c : ℤ} (hc : 2 * |c| < 2 ^ b)
    (h : (2 : ℤ) ^ (b + H) ∣ 3 ^ b - c) : H ≤ vTwo b := by
  have hb : (2 : ℤ) ^ b ∣ 3 ^ b - c :=
    dvd_trans (pow_dvd_pow 2 (Nat.le_add_right b H)) h
  rw [resid_eq_of_corridor hc hb] at h
  exact (two_pow_dvd_three_pow_sub_resid_iff b H).mp h

/-- **The transport would produce the enemy.**  If `3ᵃ` sits in the residue corridor at `b`
(`2·3ᵃ < 2ᵇ`, i.e. `a < 0.63(b−1)` — the generic case for a thin set, whose members are far
apart) and the comparison with `a` *did* reach depth `b + H`, then `v₂(m_b) ≥ H`.  With
`no_pair_reaches_window` the hypothesis is never satisfiable; the point of the statement is the
direction of the conclusion. -/
@[category research solved, AMS 11, ref "Bug12" "DD90", group "bugeaud_10_13"]
theorem transport_would_produce_depth {a b H : ℕ} (hcorr : 2 * 3 ^ a < 2 ^ b)
    (h : (2 : ℤ) ^ (b + H) ∣ 3 ^ b - 3 ^ a) : H ≤ vTwo b := by
  refine pinned_forces_vTwo_ge (c := (3 : ℤ) ^ a) ?_ h
  have hpos : (0 : ℤ) < 3 ^ a := by positivity
  rw [abs_of_pos hpos]
  exact_mod_cast hcorr

/-- **Automatic index sets, priced.**  An infinite `2`-automatic set contains, by the pumping
lemma for automata, a family `aᵢ = α·2^{si} + β` (`s ≥ 1`) — A2's probe `{2ˡ}` is the case
`α = 1, β = 0, s = 1`.  Every such family obeys the general bound: a comparison inside it reaches
depth at most `log₂ aⱼ + 2`.  So automata buy exactly what LTE buys, and neither reaches the
window. -/
@[category research solved, AMS 11, ref "Bug12" "DD90", group "bugeaud_10_13"]
theorem pumped_pin_depth {α β s i j M : ℕ} (hα : 1 ≤ α) (hs : 1 ≤ s) (hij : i < j) (hM : 3 ≤ M)
    (h : (2 : ℤ) ^ M ∣ 3 ^ (α * 2 ^ (s * j) + β) - 3 ^ (α * 2 ^ (s * i) + β)) :
    M ≤ Nat.log 2 (α * 2 ^ (s * j) + β) + 2 := by
  refine pin_depth_le_log ?_ hM h
  have hsij : s * i < s * j := mul_lt_mul_of_pos_left hij (by omega)
  have hlt : (2 : ℕ) ^ (s * i) < 2 ^ (s * j) := Nat.pow_lt_pow_right (by norm_num) hsij
  have hne : α * 2 ^ (s * i) < α * 2 ^ (s * j) := mul_lt_mul_of_pos_left hlt (by omega)
  omega

/-! ## 4. What the density-1 target actually asks

`Shallow` is infinite; its complement `{n : v₂(mₙ) ≥ 2}` is *not known to be infinite* — that
would say `4 ∣ mₙ` infinitely often, a statement about the binary window of `3ⁿ` at bit `n` with
no proof in sight.  The two theorems below bracket the question: the `v` arm is bounded as soon as
the deep set is finite, and the deep set is infinite as soon as the `v` arm is unbounded.  So
"density 1 for the `v` arm at some fixed `C`" sits strictly between `Shallow` being infinite
(proved here) and Problem 2 itself. -/

/-- If only finitely many indices are deep, the `v` arm is bounded outright — Problem 2's `v`
half, with no exception hypothesis. -/
@[category research solved, AMS 11, ref "Bug12", group "bugeaud_10_13"]
theorem vArm_bounded_of_deep_finite (h : {n : ℕ | 2 ≤ vTwo n}.Finite) : ∃ C, ∀ a, vTwo a ≤ C := by
  obtain ⟨B, hB⟩ := h.bddAbove
  refine ⟨24 * B + 41, fun a => ?_⟩
  rcases le_or_gt (vTwo a) 1 with hle | hgt
  · omega
  · have haB : a ≤ B := hB (show 2 ≤ vTwo a by omega)
    have := vTwo_le_of_arm a
    omega

/-- Conversely, an unbounded `v` arm forces infinitely many deep indices. -/
@[category research solved, AMS 11, ref "Bug12", group "bugeaud_10_13"]
theorem deep_infinite_of_vArm_unbounded (h : ∀ C, ∃ a, C < vTwo a) :
    {n : ℕ | 2 ≤ vTwo n}.Infinite := by
  refine Set.infinite_of_not_bddAbove ?_
  rintro ⟨B, hB⟩
  obtain ⟨a, ha⟩ := h (24 * B + 41)
  have hmem : 2 ≤ vTwo a := by omega
  have haB : a ≤ B := hB hmem
  have := vTwo_le_of_arm a
  omega

/-! ## 5. Kernel-checked witnesses -/

/-- The dyadic-block witnesses of `shallow_dyadic` for `i ≤ 7`, computed: the first shallow index
of `[2ⁱ, 2^{i+1})` is `1, 2, 4, 8, 16, 35, 64, 131` (`b9_thinsets.py` [C]).  The two nontrivial
ones are checked here. -/
@[category test, AMS 11, ref "Bug12", group "bugeaud_10_13"]
theorem shallow_block_witnesses : vTwo 35 = 1 ∧ vTwo 64 = 0 ∧ vTwo 131 = 1 :=
  ⟨vTwo_eq_of_mNat (by decide) (by decide), vTwo_eq_of_mNat (by decide) (by decide),
   vTwo_eq_of_mNat (by decide) (by decide)⟩

/-- The block `[32, 64)` really needs `35`, and the reason is the descent law itself:
`v₂(m₃₂), …, v₂(m₃₅) = 4, 3, 2, 1` is a full descent run of `BB13.vTwo_succ_lt`, so the delay is
exactly the height at the start of the block — `shallow_gap` is attained here.  The block
`[128, 256)` repeats it verbatim: `4, 3, 2, 1` at `128, …, 131`. -/
@[category test, AMS 11, ref "DD90" "Bug12", group "bugeaud_10_13"]
theorem shallow_block_descent_run :
    vTwo 32 = 4 ∧ vTwo 33 = 3 ∧ vTwo 34 = 2 ∧ vTwo 35 = 1 :=
  ⟨vTwo_eq_of_mNat (by decide) (by decide), vTwo_eq_of_mNat (by decide) (by decide),
   vTwo_eq_of_mNat (by decide) (by decide), vTwo_eq_of_mNat (by decide) (by decide)⟩

/-- **The `(5, 37)` pair of `BB13.selfRef_five`/`selfRef_thirtyseven`, read through the transport
theorem**: it transports `7 = v₂(32) + 2` bits, while the window at `37` sits at depth `39`.  The
extremal self-referential pair of B4 is not a counterexample to `no_pair_reaches_window` — it is
an instance of it. -/
@[category test, AMS 11, ref "Bug12", group "bugeaud_10_13"]
theorem five_thirtyseven_transport :
    ((2 : ℤ) ^ 7 ∣ 3 ^ 37 - 3 ^ 5) ∧ ¬ ((2 : ℤ) ^ 8 ∣ 3 ^ 37 - 3 ^ 5) := by
  constructor
  · decide
  · decide

/-- The LTE probe at `l = 3`: `v₂(3⁸ − 1) = 5 = 3 + 2`. -/
@[category test, AMS 11, ref "Bug12", group "bugeaud_10_13"]
theorem lte_probe_three : ((2 : ℤ) ^ 5 ∣ 3 ^ 8 - 1) ∧ ¬ ((2 : ℤ) ^ 6 ∣ 3 ^ 8 - 1) := by
  constructor
  · decide
  · decide

end BB13
