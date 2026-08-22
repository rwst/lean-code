/-
(C) 2026 Ralf Stephan, in collaboration with Claude Code.
Released under CC0 1.0 Universal (public-domain dedication).
See https://creativecommons.org/publicdomain/zero/1.0/
-/
import BB13.ValuationArm
import Mathlib.NumberTheory.Multiplicity

/-!
# The self-referential indices: 2-adic rigidity, and what a height-only measure can see (B4)

Item **B4** of `plans/report3-BB13.html` (§4, §6 B4, §9 item 2): the *2-adic reformulation* of the
per-line problem and the rigidity facts that survive the report's correction `CB1`.

## The reformulation

`3ᵃ − kₐ = mₐ2ᵃ` exactly (`three_pow_sub_resid`), so `v₂(3ᵃ − kₐ) = a + v₂(mₐ)` and a relation
tower over `a` reaching `b` is *exactly* the congruence `3ᵃ ≡ kₐ (mod 2ᵇ)`
(`two_pow_dvd_three_pow_sub_resid_iff`, `sameTower_dvd_three_pow_sub_resid`).  Call `a`
**self-referential for `k`** when `v₂(3ᵃ − k) ≥ a + 2` (`SelfRef`); by `selfRef_resid_iff` the
index `a` is self-referential for its *own* residue iff `4 ∣ mₐ`, i.e. iff its fibre can reach
`a + 2`.

## The rigidity facts (the 90% half of B4)

* `two_pow_dvd_three_pow_sub_one_iff` — `2ᵐ ∣ 3ᵈ − 1 ↔ 2^{m−2} ∣ d` for `m ≥ 3`, i.e.
  `ord(3 mod 2ᵐ) = 2^{m−2}` (`orderOf_three_zmod`).  Lifting the exponent at `2`.
* `selfRef_dvd_sub` / `selfRef_gap` — **tower separation**: if `a < a'` are both self-referential
  for the *same* `k` then `2ᵃ ∣ a' − a`, hence `a' ≥ a + 2ᵃ`.
* `selfRef_card_le` — hence a fixed `k` has at most `n` self-referential indices in `[1, X]`
  whenever `X < twoTower n`: the `log*` recurrence bound, effective.
* `selfRef_five` / `selfRef_thirtyseven` / `not_selfRef_unique` — the report's counterexample
  `(a, a', k) = (5, 37, 359212078195)`, machine-checked: A3's uniqueness claim is **false**.
  It is *extremal*: `37 = 5 + 2⁵` meets `selfRef_gap` with equality (`five_thirtyseven_extremal`).
* `exists_selfRef_pair` / `selfRef_pair_iff` — and the failure is **systematic, not accidental**:
  for every `a ≥ 1` and every `a' ≡ a (mod 2ᵃ)` there is a `k` self-referential at both.  Tower
  separation is not merely necessary, it is the whole obstruction.

## The corridor, and the 8% half of B4

The remaining question of `CB1` was whether cancellation can happen *inside the exception
corridor* `|k| < (3/2)ᵃ`, where the report's counterexample (`k ≈ 3.6·10¹¹` against
`(3/2)³⁷ ≈ 3.3·10⁶`) does not live.  Three theorems settle its shape:

* `corridor_candidate_unique` — for `a ≥ 3` the corridor contains **at most one** `k` with
  `2ᵃ ∣ 3ᵃ − k`, namely `kₐ` itself.  So corridor questions about arbitrary `k` are questions
  about `kₐ`, and nothing else.
* `no_selfRef_failure_le_256` — **no exception below `257` is self-referential**: the census
  `E ∩ [1,256] = {1,2,3,4,7}` carries `v₂(mₐ) ≤ 1` throughout, so `4 ∣ mₐ` never happens on it.
  (`BB13/m0_failures.py` extends the census to `10⁶`; `BB13/b4_twoadic.py` block [B].)  Hence
  `corridor_recurrence_large`: a corridor recurrence would need `a > 256` and
  `2^{a−2} ∣ a' − a`, i.e. `a' − a > 2²⁵⁴` — the phenomenon is out of computational reach, not
  merely unobserved.
* `resid_two`, `resid_four`, `resid_recurs` — but the *value* `kₐ` does recur among exceptions:
  `k₂ = k₄ = 1`, on two different lines.  A3's downstream reading "no value of `kₐ` recurs" is
  therefore false as stated; what its hypothesis buys is the depth-`(a+2)` condition, and that
  condition is what the census kills.

And the pricing of the Padé bet, which is the point of the file:

* `measure_iff_problem_two` — for `a ≥ 3` and any `C`, the *height-only* 2-adic measure
  "`v₂(3ᵃ − k) ≤ a + C` for every `k` with `|k| < (3/2)ᵃ`" is **equivalent** to
  "`a` is not an exception, or `v₂(mₐ) ≤ C`".  A measure at the self-referential points is not a
  route to Problem 2 — quantified over the corridor, it *is* Problem 2.
* `corridor_saturation` — and what such a measure can reach for free stops at `≈ 0.585a`: whenever
  `2^{M+1} ≤ (3/2)ᵃ` the corridor already contains a `k` with `2ᴹ ∣ 3ᵃ − k`.  The entire content
  of Problem 2 sits in the window `[0.585a, a]`, where the only available input is the integrality
  of `mₐ` — the circularity that `CB2` diagnosed on the Baker/Yu side, here in exact form.

## What is not proved here

Per-`k` **finiteness**: an infinite self-referential chain for a fixed `k` forces `k = 3^α` for a
2-adic limit `α`, and excluding that is the transcendence question of strategy B5 (`CB1`).  The
`log*` bound above is the effective substitute.  Nothing here bounds `v₂(mₐ)`; B4's second
deliverable — a Padé-based 2-adic measure at the `kₐ` — is priced, not delivered, and
`measure_iff_problem_two` says why no height-only version of it can exist.

Footprint: `std3` throughout — this file uses no cited axiom (in particular, none of the root's
Ridout input).  Everything is lifting-the-exponent, the exact identity `3ᵃ − kₐ = mₐ2ᵃ`, and the
kernel census of `BB13/M0Verify.lean`.

## References

* [Bug12] Y. Bugeaud, *Distribution modulo one and Diophantine approximation*, Cambridge Tracts
  **193**, 2012 — Problem 10.13.
* [DD90] F. Delmer, J.-M. Deshouillers, *The computation of `g(k)` in Waring's problem*, Math.
  Comp. **54** (1990), 885–893 — the exact-integer frame.
* [Yu07] K. Yu, *`p`-adic logarithmic forms and group varieties III*, Forum Math. **19** (2007),
  187–280 — the generic `p`-adic Baker bound that `CB2` shows to be vacuous here.
* `plans/report3-BB13.html` §4 (the reformulation and `CB1`), §6 B4, §7 (the grid);
  `plans/note-BB13-B4.html` (this work); `BB13/b4_twoadic.py` (the evidence).
-/

namespace BB13

open scoped Real

/-! ### The order of `3` in `(ℤ/2ᵐ)ˣ`

Lifting the exponent at `2`: `v₂(3ᵈ − 1) = v₂(d) + 2` for even `d`, and `= 1` for odd `d`.  The
divisibility form below is the workhorse; `orderOf_three_zmod` is the group-theoretic restatement.
-/

/-- For odd `d`, `3ᵈ ≡ 3 (mod 4)`: the parity obstruction that starts the order computation. -/
@[category API, AMS 11, ref "Bug12", group "bugeaud_10_13"]
theorem four_not_dvd_three_pow_sub_one {d : ℕ} (hd : Odd d) : ¬ ((4 : ℤ) ∣ 3 ^ d - 1) := by
  intro h
  have h0 : (((3 : ℤ) ^ d - 1 : ℤ) : ZMod 4) = 0 := (ZMod.intCast_zmod_eq_zero_iff_dvd _ 4).mpr h
  push_cast at h0
  rw [show (3 : ZMod 4) = -1 by decide, hd.neg_one_pow] at h0
  exact absurd h0 (by decide)

/-- **The order of `3` modulo `2ᵐ`**, in divisibility form: for `m ≥ 3`,
`2ᵐ ∣ 3ᵈ − 1 ↔ 2^{m−2} ∣ d`.  Lifting the exponent at `2` (`padicValNat.pow_two_sub_one`) plus the
parity obstruction. -/
@[category research solved, AMS 11, ref "Bug12", group "bugeaud_10_13"]
theorem two_pow_dvd_three_pow_sub_one_iff {m d : ℕ} (hm : 3 ≤ m) :
    ((2 : ℤ) ^ m ∣ 3 ^ d - 1) ↔ 2 ^ (m - 2) ∣ d := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  rcases Nat.eq_zero_or_pos d with rfl | hd0
  · simp
  rcases Nat.even_or_odd d with he | ho
  · -- the substantial case: lifting the exponent
    have hone : (1 : ℕ) ≤ 3 ^ d := Nat.one_le_pow _ _ (by norm_num)
    have hcast : (((3 ^ d - 1 : ℕ) : ℤ)) = (3 : ℤ) ^ d - 1 := by
      rw [Nat.cast_sub hone]; push_cast; ring
    have hiff : ((2 : ℤ) ^ m ∣ (3 : ℤ) ^ d - 1) ↔ (2 ^ m ∣ 3 ^ d - 1) := by
      rw [← Int.natCast_dvd_natCast, hcast]
      push_cast
      exact Iff.rfl
    have hne : 3 ^ d - 1 ≠ 0 := by
      have : 1 < 3 ^ d := Nat.one_lt_pow (by omega) (by norm_num)
      omega
    have hLTE : padicValNat 2 (3 ^ d - 1) = padicValNat 2 d + 2 := by
      have h := padicValNat.pow_two_sub_one (x := 3) (n := d) (by norm_num) (by norm_num)
        (by omega) he
      have h4 : padicValNat 2 4 = 2 := by
        simpa using padicValNat.prime_pow (p := 2) 2
      have h2 : padicValNat 2 2 = 1 := by simp
      norm_num [h4, h2] at h
      omega
    rw [hiff, padicValNat_dvd_iff_le hne, padicValNat_dvd_iff_le (by omega : d ≠ 0), hLTE]
    omega
  · -- both sides fail for odd `d`
    constructor
    · intro h
      refine absurd (dvd_trans ?_ h) (four_not_dvd_three_pow_sub_one ho)
      rw [show (4 : ℤ) = 2 ^ 2 by norm_num]
      exact pow_dvd_pow 2 (by omega)
    · intro h
      have h2 : (2 : ℕ) ∣ d := dvd_trans (dvd_pow_self 2 (by omega : m - 2 ≠ 0)) h
      exact absurd (even_iff_two_dvd.mpr h2) (Nat.not_even_iff_odd.mpr ho)

/-- **`ord(3 mod 2ᵐ) = 2^{m−2}`** for `m ≥ 3` — the group-theoretic form of
`two_pow_dvd_three_pow_sub_one_iff`, and the reason a congruence `3ˣ ≡ k (mod 2^ℓ)` pins `x` to a
single class mod `2^{ℓ−2}` (report §4). -/
@[category research solved, AMS 11, ref "Bug12", group "bugeaud_10_13"]
theorem orderOf_three_zmod {m : ℕ} (hm : 3 ≤ m) :
    orderOf (3 : ZMod (2 ^ m)) = 2 ^ (m - 2) := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have : NeZero ((2 : ℕ) ^ m) := ⟨by positivity⟩
  have key : ∀ d : ℕ, ((3 : ZMod (2 ^ m)) ^ d = 1 ↔ (2 : ℤ) ^ m ∣ 3 ^ d - 1) := by
    intro d
    rw [← sub_eq_zero]
    have hc : (((3 : ℤ) ^ d - 1 : ℤ) : ZMod (2 ^ m)) = (3 : ZMod (2 ^ m)) ^ d - 1 := by
      push_cast; ring
    rw [← hc, ZMod.intCast_zmod_eq_zero_iff_dvd]
    push_cast
    exact Iff.rfl
  have hm2 : m - 2 = (m - 3) + 1 := by omega
  rw [hm2]
  refine orderOf_eq_prime_pow (p := 2) ?_ ?_
  · rw [key, two_pow_dvd_three_pow_sub_one_iff hm]
    intro h
    have hle := Nat.le_of_dvd (pow_pos (by norm_num) _) h
    have hlt : (2 : ℕ) ^ (m - 3) < 2 ^ (m - 2) :=
      Nat.pow_lt_pow_right (by norm_num) (by omega)
    omega
  · rw [key, two_pow_dvd_three_pow_sub_one_iff hm, hm2]

/-! ### The exact identity, and the self-referential condition -/

/-- **`a` is self-referential for `k`**: `v₂(3ᵃ − k) ≥ a + 2`, the condition of the report's §4
(A3's strategy (C), corrected by `CB1`). -/
def SelfRef (k : ℤ) (a : ℕ) : Prop := (2 : ℤ) ^ (a + 2) ∣ 3 ^ a - k

/-- **The exact identity** `3ᵃ − kₐ = mₐ·2ᵃ`, from which `v₂(3ᵃ − kₐ) = a + v₂(mₐ)`. -/
@[category API, AMS 11, ref "Bug12" "DD90", group "bugeaud_10_13"]
theorem three_pow_sub_resid (a : ℕ) : (3 : ℤ) ^ a - resid 3 2 a = Mnum 3 2 a * 2 ^ a := by
  rw [resid]; push_cast; ring

/-- **The fibre congruence:** `2^{a+H} ∣ 3ᵃ − kₐ ↔ H ≤ v₂(mₐ)`.  With `sameTower_span_le_vTwo`
this is the report's "a fibre of size `H` at bottom `a` is exactly the congruence
`3ᵃ ≡ kₐ (mod 2^{a+H−1})`". -/
@[category research solved, AMS 11, ref "Bug12" "DD90", group "bugeaud_10_13"]
theorem two_pow_dvd_three_pow_sub_resid_iff (a H : ℕ) :
    ((2 : ℤ) ^ (a + H) ∣ 3 ^ a - resid 3 2 a) ↔ H ≤ vTwo a := by
  rw [three_pow_sub_resid, pow_add, mul_comm ((2 : ℤ) ^ a) ((2 : ℤ) ^ H)]
  constructor
  · intro h
    exact le_vTwo_of_dvd ((mul_dvd_mul_iff_right (by positivity : ((2 : ℤ) ^ a) ≠ 0)).mp h)
  · intro h
    exact mul_dvd_mul (dvd_trans (pow_dvd_pow 2 h) (two_pow_vTwo_dvd a)) dvd_rfl

/-- `a` is self-referential for its own residue iff `4 ∣ mₐ`. -/
@[category research solved, AMS 11, ref "Bug12", group "bugeaud_10_13"]
theorem selfRef_resid_iff (a : ℕ) : SelfRef (resid 3 2 a) a ↔ 2 ≤ vTwo a :=
  two_pow_dvd_three_pow_sub_resid_iff a 2

/-- A relation tower over `a` reaching `b` **is** the congruence `3ᵃ ≡ kₐ (mod 2ᵇ)`. -/
@[category research solved, AMS 11, ref "Bug12", group "bugeaud_10_13"]
theorem sameTower_dvd_three_pow_sub_resid {a b : ℕ} (hab : a ≤ b) (h : SameTower a b) :
    (2 : ℤ) ^ b ∣ 3 ^ a - resid 3 2 a := by
  have h2 := (two_pow_dvd_three_pow_sub_resid_iff a (b - a)).mpr (sameTower_span_le_vTwo hab h)
  rwa [show a + (b - a) = b by omega] at h2

/-! ### Tower separation: the corrected rigidity fact (`CB1`) -/

/-- **Tower separation.**  If `a ≤ a'` are both self-referential for the *same* `k`, then
`2ᵃ ∣ a' − a`.  (A3 claimed `a` is unique; `CB1` refutes that, and this is what is true.) -/
@[category research solved, AMS 11, ref "Bug12", group "bugeaud_10_13"]
theorem selfRef_dvd_sub {k : ℤ} {a a' : ℕ} (hle : a ≤ a') (h : SelfRef k a) (h' : SelfRef k a') :
    2 ^ a ∣ a' - a := by
  rcases Nat.eq_zero_or_pos a with rfl | ha1
  · simp
  have hd : (2 : ℤ) ^ (a + 2) ∣ 3 ^ a' - k :=
    dvd_trans (pow_dvd_pow (2 : ℤ) (show a + 2 ≤ a' + 2 by omega)) h'
  have hsub : (2 : ℤ) ^ (a + 2) ∣ (3 : ℤ) ^ a' - 3 ^ a := by
    have h3 := dvd_sub hd h
    simpa using h3
  have hfac : (3 : ℤ) ^ a' - 3 ^ a = ((3 : ℤ) ^ (a' - a) - 1) * 3 ^ a := by
    rw [sub_mul, one_mul, ← pow_add]
    congr 2
    omega
  rw [hfac] at hsub
  have hcop : IsCoprime ((2 : ℤ) ^ (a + 2)) ((3 : ℤ) ^ a) :=
    IsCoprime.pow (Int.isCoprime_iff_gcd_eq_one.mpr (by norm_num))
  have hkey : (2 : ℤ) ^ (a + 2) ∣ 3 ^ (a' - a) - 1 := hcop.dvd_of_dvd_mul_right hsub
  have hfin := (two_pow_dvd_three_pow_sub_one_iff (by omega : 3 ≤ a + 2)).mp hkey
  simpa using hfin

/-- **The gap:** two self-referential indices for one `k` are tower-separated, `a' ≥ a + 2ᵃ`. -/
@[category research solved, AMS 11, ref "Bug12", group "bugeaud_10_13"]
theorem selfRef_gap {k : ℤ} {a a' : ℕ} (hlt : a < a') (h : SelfRef k a) (h' : SelfRef k a') :
    a + 2 ^ a ≤ a' := by
  have hdvd := selfRef_dvd_sub (le_of_lt hlt) h h'
  have hle := Nat.le_of_dvd (by omega : 0 < a' - a) hdvd
  omega

/-- **The converse — the failure of uniqueness is systematic.**  For every `a ≤ a'` with
`2ᵃ ∣ a' − a` the integer `k = 3^{a'}` is self-referential at both.  So tower separation is not
just a necessary condition: it is the *whole* obstruction, and `CB1`'s counterexample is one
member of an infinite family. -/
@[category research solved, AMS 11, ref "Bug12", group "bugeaud_10_13"]
theorem exists_selfRef_pair {a a' : ℕ} (ha : 1 ≤ a) (hle : a ≤ a') (hdvd : 2 ^ a ∣ a' - a) :
    SelfRef ((3 : ℤ) ^ a') a ∧ SelfRef ((3 : ℤ) ^ a') a' := by
  refine ⟨?_, by simp [SelfRef]⟩
  have hkey : (2 : ℤ) ^ (a + 2) ∣ 3 ^ (a' - a) - 1 :=
    (two_pow_dvd_three_pow_sub_one_iff (by omega : 3 ≤ a + 2)).mpr (by simpa using hdvd)
  have hpow : (3 : ℤ) ^ (a' - a) * 3 ^ a = 3 ^ a' := by
    rw [← pow_add]; congr 1; omega
  have hfac : (3 : ℤ) ^ a - 3 ^ a' = -(((3 : ℤ) ^ (a' - a) - 1) * 3 ^ a) := by
    linear_combination hpow
  rw [SelfRef, hfac]
  exact dvd_neg.mpr (hkey.mul_right _)

/-- `2ᵃ ∣ a' − a` is **exactly** the condition for a common self-referential `k` to exist. -/
@[category research solved, AMS 11, ref "Bug12", group "bugeaud_10_13"]
theorem selfRef_pair_iff {a a' : ℕ} (ha : 1 ≤ a) (hle : a ≤ a') :
    (∃ k : ℤ, SelfRef k a ∧ SelfRef k a') ↔ 2 ^ a ∣ a' - a := by
  constructor
  · rintro ⟨k, h, h'⟩
    exact selfRef_dvd_sub hle h h'
  · intro h
    exact ⟨(3 : ℤ) ^ a', exists_selfRef_pair ha hle h⟩

/-! ### The `log*` recurrence bound -/

/-- The tower `1, 2, 4, 16, 65536, …`: `twoTower n` is `2` exponentiated `n` times over `1`. -/
def twoTower : ℕ → ℕ
  | 0 => 1
  | n + 1 => 2 ^ twoTower n

@[category API, AMS 11, ref "Bug12", group "bugeaud_10_13"]
theorem twoTower_succ (n : ℕ) : twoTower (n + 1) = 2 ^ twoTower n := rfl

@[category API, AMS 11, ref "Bug12", group "bugeaud_10_13"]
theorem twoTower_pos (n : ℕ) : 0 < twoTower n := by
  induction n with
  | zero => exact Nat.one_pos
  | succ n _ => exact pow_pos (by norm_num) _

/-- **The `log*` bound, effective.**  A fixed `k` has at most `n` self-referential indices below
any `X < twoTower n`: the salvage of A3's uniqueness claim (`CB1`).  Values of `kₐ` therefore
cannot recur at positive density — though they can recur (`resid_recurs`). -/
@[category research solved, AMS 11, ref "Bug12", group "bugeaud_10_13"]
theorem selfRef_card_le {k : ℤ} {T : Finset ℕ} (hT : ∀ a ∈ T, 1 ≤ a ∧ SelfRef k a) {n X : ℕ}
    (hTX : ∀ a ∈ T, a ≤ X) (hX : X < twoTower n) : T.card ≤ n := by
  induction n generalizing T X with
  | zero =>
    have hX1 : X < 1 := hX
    have hTe : T = ∅ := by
      by_contra hne
      obtain ⟨a, ha⟩ := Finset.nonempty_iff_ne_empty.mpr hne
      have h1 := (hT a ha).1
      have h2 := hTX a ha
      omega
    simp [hTe]
  | succ n ih =>
    rcases Finset.eq_empty_or_nonempty T with rfl | hne
    · simp
    · have hMmem : T.max' hne ∈ T := T.max'_mem hne
      have hcard : T.card = (T.erase (T.max' hne)).card + 1 := by
        rw [Finset.card_erase_of_mem hMmem]
        have : 0 < T.card := Finset.card_pos.mpr hne
        omega
      have hstep : ∀ a ∈ T.erase (T.max' hne), a ≤ twoTower n - 1 := by
        intro a ha
        have hne' : a ≠ T.max' hne := Finset.ne_of_mem_erase ha
        have haT : a ∈ T := Finset.mem_of_mem_erase ha
        have hlt : a < T.max' hne := lt_of_le_of_ne (T.le_max' a haT) hne'
        have hgap : a + 2 ^ a ≤ T.max' hne := selfRef_gap hlt (hT a haT).2 (hT _ hMmem).2
        have hMX : T.max' hne ≤ X := hTX _ hMmem
        have hXt : X < 2 ^ twoTower n := by rw [← twoTower_succ]; exact hX
        have h1 : (2 : ℕ) ^ a < 2 ^ twoTower n := by omega
        have h2 : a < twoTower n := (Nat.pow_lt_pow_iff_right (by norm_num)).mp h1
        omega
      have hXn : twoTower n - 1 < twoTower n := by have := twoTower_pos n; omega
      have hrec := ih (T := T.erase (T.max' hne))
        (fun a ha => hT a (Finset.mem_of_mem_erase ha)) hstep hXn
      omega

/-! ### `CB1`'s counterexample, machine-checked -/

/-- `v₂(3⁵ − k) ≥ 7` for `k = 3³⁷ mod 2³⁹ = 359212078195`. -/
@[category research solved, AMS 11, ref "Bug12", group "bugeaud_10_13"]
theorem selfRef_five : SelfRef 359212078195 5 := ⟨-2806344359, by norm_num⟩

/-- `v₂(3³⁷ − k) ≥ 39` for the same `k` — by construction. -/
@[category research solved, AMS 11, ref "Bug12", group "bugeaud_10_13"]
theorem selfRef_thirtyseven : SelfRef 359212078195 37 := ⟨819061, by norm_num⟩

/-- **`CB1`:** A3's claim that a fixed `k` has *at most one* self-referential index `a ≥ 5` is
false — `(a, a', k) = (5, 37, 359212078195)`. -/
@[category research solved, AMS 11, ref "Bug12", group "bugeaud_10_13"]
theorem not_selfRef_unique :
    ¬ ∀ (k : ℤ) (a a' : ℕ), 5 ≤ a → a < a' → SelfRef k a → SelfRef k a' → a = a' := by
  intro h
  have hcon := h 359212078195 5 37 (by norm_num) (by norm_num) selfRef_five selfRef_thirtyseven
  omega

/-- The counterexample is **extremal** for `selfRef_gap`: `37 = 5 + 2⁵`. -/
@[category research solved, AMS 11, ref "Bug12", group "bugeaud_10_13"]
theorem five_thirtyseven_extremal : 5 + 2 ^ 5 = 37 := by norm_num

/-! ### The corridor `|k| < (3/2)ᵃ` -/

/-- `2·(3/2)ᵃ < 2ᵃ` for `a ≥ 3` — the corridor is narrower than half the frame scale. -/
@[category API, AMS 11, ref "Bug12", group "bugeaud_10_13"]
theorem two_mul_three_half_pow_lt {a : ℕ} (ha : 3 ≤ a) : 2 * (3 / 2 : ℝ) ^ a < 2 ^ a := by
  have h2 : ((4 : ℝ) / 3) ^ 3 ≤ (4 / 3 : ℝ) ^ a := pow_le_pow_right₀ (by norm_num) ha
  have h1 : (2 : ℝ) < (4 / 3 : ℝ) ^ a := by nlinarith [h2]
  have h3 : (3 / 2 : ℝ) ^ a * (4 / 3 : ℝ) ^ a = 2 ^ a := by
    rw [← mul_pow]; norm_num
  nlinarith [pow_pos (show (0 : ℝ) < 3 / 2 by norm_num) a]

/-- **At most one corridor candidate.**  For `a ≥ 3`, the only `k` with `|k| < (3/2)ᵃ` and
`2ᵃ ∣ 3ᵃ − k` is `kₐ`.  Every corridor question about arbitrary `k` is a question about `kₐ`. -/
@[category research solved, AMS 11, ref "Bug12" "DD90", group "bugeaud_10_13"]
theorem corridor_candidate_unique {a : ℕ} (ha : 3 ≤ a) {k : ℤ}
    (hk : |((k : ℤ) : ℝ)| < (3 / 2 : ℝ) ^ a) (hdvd : (2 : ℤ) ^ a ∣ 3 ^ a - k) :
    k = resid 3 2 a := by
  obtain ⟨j, hj⟩ := hdvd
  have h1 := three_pow_sub_resid a
  have hid : resid 3 2 a - k = (j - Mnum 3 2 a) * 2 ^ a := by linear_combination hj - h1
  have h2a : (0 : ℝ) < 2 ^ a := by positivity
  have hr := abs_resid_le a
  have hgap := two_mul_three_half_pow_lt ha
  have hab : |((resid 3 2 a : ℤ) : ℝ) - ((k : ℤ) : ℝ)|
      ≤ |((resid 3 2 a : ℤ) : ℝ)| + |((k : ℤ) : ℝ)| := by
    rw [sub_eq_add_neg]
    exact le_trans (abs_add_le _ _) (le_of_eq (by rw [abs_neg]))
  have hcalc : |((j - Mnum 3 2 a : ℤ) : ℝ)| * 2 ^ a
      = |((resid 3 2 a : ℤ) : ℝ) - ((k : ℤ) : ℝ)| := by
    have hcast : ((resid 3 2 a - k : ℤ) : ℝ) = ((j - Mnum 3 2 a : ℤ) : ℝ) * 2 ^ a := by
      rw [hid]; push_cast; ring
    rw [← abs_of_pos h2a, ← abs_mul, ← hcast]
    push_cast
    ring_nf
  have hsize : |((j - Mnum 3 2 a : ℤ) : ℝ)| * 2 ^ a < 1 * 2 ^ a := by
    rw [hcalc, one_mul]
    linarith
  have hlt1 : |((j - Mnum 3 2 a : ℤ) : ℝ)| < 1 := lt_of_mul_lt_mul_right hsize h2a.le
  have hlt2 : |j - Mnum 3 2 a| < 1 := by exact_mod_cast hlt1
  have hzero : j - Mnum 3 2 a = 0 := Int.abs_lt_one_iff.mp hlt2
  have hfin : resid 3 2 a - k = 0 := by rw [hid, hzero, zero_mul]
  linarith

/-- Unfolding of the failure condition: `a ∈ E ↔ |kₐ| < (3/2)ᵃ`. -/
@[category API, AMS 11, ref "Bug12", group "bugeaud_10_13"]
theorem isFailure_iff_abs_resid_lt (a : ℕ) :
    IsFailure 3 2 (3 / 4) a ↔ |((resid 3 2 a : ℤ) : ℝ)| < (3 / 2 : ℝ) ^ a := by
  rw [IsFailure]
  norm_num

/-- **The corridor form of self-reference:** for `a ≥ 3`, a corridor `k` is self-referential at `a`
iff it is `kₐ` and `4 ∣ mₐ`. -/
@[category research solved, AMS 11, ref "Bug12", group "bugeaud_10_13"]
theorem corridor_selfRef_iff {a : ℕ} (ha : 3 ≤ a) {k : ℤ}
    (hk : |((k : ℤ) : ℝ)| < (3 / 2 : ℝ) ^ a) :
    SelfRef k a ↔ (k = resid 3 2 a ∧ 2 ≤ vTwo a) := by
  constructor
  · intro h
    have hk' : k = resid 3 2 a :=
      corridor_candidate_unique ha hk (dvd_trans (pow_dvd_pow 2 (by omega)) h)
    subst hk'
    exact ⟨rfl, (selfRef_resid_iff a).mp h⟩
  · rintro ⟨rfl, hv⟩
    exact (selfRef_resid_iff a).mpr hv

/-- **The pricing of B4's Padé branch.**  For `a ≥ 3` and any `C`, a *height-only* 2-adic measure
at the corridor points — "`v₂(3ᵃ − k) ≤ a + C` for every `k` with `|k| < (3/2)ᵃ`" — holds **iff**
`a` is not an exception or `v₂(mₐ) ≤ C`.  Quantified over the corridor, such a measure is not a
route to Problem 2: it *is* Problem 2. -/
@[category research solved, AMS 11, ref "Bug12" "Yu07", group "bugeaud_10_13"]
theorem measure_iff_problem_two {a : ℕ} (ha : 3 ≤ a) (C : ℕ) :
    (∀ k : ℤ, |((k : ℤ) : ℝ)| < (3 / 2 : ℝ) ^ a → ¬ ((2 : ℤ) ^ (a + C + 1) ∣ 3 ^ a - k))
      ↔ (¬ IsFailure 3 2 (3 / 4) a ∨ vTwo a ≤ C) := by
  constructor
  · intro h
    by_contra hcon
    push Not at hcon
    obtain ⟨hfail, hv⟩ := hcon
    refine h (resid 3 2 a) ((isFailure_iff_abs_resid_lt a).mp hfail) ?_
    rw [show a + C + 1 = a + (C + 1) by ring]
    exact (two_pow_dvd_three_pow_sub_resid_iff a (C + 1)).mpr (by omega)
  · intro h k hk hdvd
    have hk' : k = resid 3 2 a :=
      corridor_candidate_unique ha hk (dvd_trans (pow_dvd_pow 2 (by omega)) hdvd)
    subst hk'
    have hfail : IsFailure 3 2 (3 / 4) a := (isFailure_iff_abs_resid_lt a).mpr hk
    have hv : C + 1 ≤ vTwo a := by
      refine (two_pow_dvd_three_pow_sub_resid_iff a (C + 1)).mp ?_
      rwa [show a + (C + 1) = a + C + 1 by ring]
    rcases h with h | h
    · exact h hfail
    · omega

/-- **What a height-only measure gets for free, and no more.**  Whenever `2^{M+1} ≤ (3/2)ᵃ` the
corridor already contains a `k` with `2ᴹ ∣ 3ᵃ − k`.  So no argument that sees only the height of
`k` can push past `M ≈ a·log₂(3/2) = 0.585a`, while Problem 2 asks for `a + O(1)`: the whole
content sits in the window `[0.585a, a]`, where the only extra input is that `mₐ` is an integer. -/
@[category research solved, AMS 11, ref "Bug12" "Yu07", group "bugeaud_10_13"]
theorem corridor_saturation (a M : ℕ) (h : (2 : ℝ) ^ (M + 1) ≤ (3 / 2 : ℝ) ^ a) :
    ∃ k : ℤ, |((k : ℤ) : ℝ)| < (3 / 2 : ℝ) ^ a ∧ (2 : ℤ) ^ M ∣ 3 ^ a - k := by
  refine ⟨(3 : ℤ) ^ a % 2 ^ M, ?_, ⟨(3 : ℤ) ^ a / 2 ^ M, by rw [Int.emod_def]; ring⟩⟩
  have h0 : (0 : ℤ) ≤ (3 : ℤ) ^ a % 2 ^ M := Int.emod_nonneg _ (by positivity)
  have h1 : (3 : ℤ) ^ a % 2 ^ M < 2 ^ M := Int.emod_lt_of_pos _ (by positivity)
  have h2 : ((((3 : ℤ) ^ a % 2 ^ M : ℤ)) : ℝ) < ((2 : ℝ)) ^ M := by exact_mod_cast h1
  have h3 : (0 : ℝ) ≤ (((3 : ℤ) ^ a % 2 ^ M : ℤ) : ℝ) := by exact_mod_cast h0
  have h4 : ((2 : ℝ)) ^ M < 2 ^ (M + 1) := by
    have : (0 : ℝ) < 2 ^ M := by positivity
    rw [pow_succ]
    linarith
  rw [abs_of_nonneg h3]
  linarith

/-! ### The corridor is empty in the census range, but values do recur -/

/-- **No exception below `257` is self-referential**: the certified census
`E ∩ [1,256] = {1,2,3,4,7}` has `v₂(mₐ) ≤ 1` throughout, so `4 ∣ mₐ` never happens on it.  The
hypothesis of A3's rigidity claim is *vacuous* in the verified range. -/
@[category research solved, AMS 11, ref "Bug12" "DD90", group "bugeaud_10_13"]
theorem no_selfRef_failure_le_256 {a : ℕ} (h1 : 1 ≤ a) (h2 : a ≤ 256)
    (hf : IsFailure 3 2 (3 / 4) a) : ¬ SelfRef (resid 3 2 a) a := by
  rw [selfRef_resid_iff]
  obtain ⟨c1, c2, c3, c4, c7⟩ := vTwo_census
  rcases (failures_up_to_256 a h1 h2).mp hf with rfl | rfl | rfl | rfl | rfl <;> omega

/-- **The corridor recurrence, if it exists at all, is astronomically far out.**  If `a` is a
self-referential exception and its residue recurs at `a' > a`, then `a > 256` and
`2^{a−2} ∣ a' − a`, so `a' − a > 2²⁵⁴`.  (`BB13/m0_failures.py` pushes the census to `10⁶`,
raising the bound to `2^{10⁶}`.) -/
@[category research solved, AMS 11, ref "Bug12" "DD90", group "bugeaud_10_13"]
theorem corridor_recurrence_large {a a' : ℕ} (h1 : 1 ≤ a) (hlt : a < a')
    (hf : IsFailure 3 2 (3 / 4) a) (hv : 2 ≤ vTwo a) (heq : resid 3 2 a = resid 3 2 a') :
    256 < a ∧ 2 ^ (a - 2) ∣ a' - a := by
  have h256 : 256 < a := by
    by_contra hcon
    exact no_selfRef_failure_le_256 h1 (by omega) hf ((selfRef_resid_iff a).mpr hv)
  refine ⟨h256, ?_⟩
  have hda : (2 : ℤ) ^ a ∣ 3 ^ a - resid 3 2 a := by
    have h0 := (two_pow_dvd_three_pow_sub_resid_iff a 0).mpr (Nat.zero_le _)
    rwa [add_zero] at h0
  have hda' : (2 : ℤ) ^ a ∣ 3 ^ a' - resid 3 2 a := by
    rw [heq]
    refine dvd_trans (pow_dvd_pow (2 : ℤ) (show a ≤ a' from le_of_lt hlt)) ?_
    have h0 := (two_pow_dvd_three_pow_sub_resid_iff a' 0).mpr (Nat.zero_le _)
    rwa [add_zero] at h0
  have hsub : (2 : ℤ) ^ a ∣ (3 : ℤ) ^ a' - 3 ^ a := by
    have h3 := dvd_sub hda' hda
    simpa using h3
  have hfac : (3 : ℤ) ^ a' - 3 ^ a = ((3 : ℤ) ^ (a' - a) - 1) * 3 ^ a := by
    rw [sub_mul, one_mul, ← pow_add]
    congr 2
    omega
  rw [hfac] at hsub
  have hcop : IsCoprime ((2 : ℤ) ^ a) ((3 : ℤ) ^ a) :=
    IsCoprime.pow (Int.isCoprime_iff_gcd_eq_one.mpr (by norm_num))
  have hkey : (2 : ℤ) ^ a ∣ 3 ^ (a' - a) - 1 := hcop.dvd_of_dvd_mul_right hsub
  exact (two_pow_dvd_three_pow_sub_one_iff (by omega : 3 ≤ a)).mp hkey

/-- `k₂ = 1`. -/
@[category API, AMS 11, ref "Bug12" "DD90", group "bugeaud_10_13"]
theorem resid_two : resid 3 2 2 = 1 := by
  rw [resid, Mnum_eq_mNat]
  norm_num [mNat]

/-- `k₄ = 1`. -/
@[category API, AMS 11, ref "Bug12" "DD90", group "bugeaud_10_13"]
theorem resid_four : resid 3 2 4 = 1 := by
  rw [resid, Mnum_eq_mNat]
  norm_num [mNat]

/-- **Values of `kₐ` do recur among the exceptions:** `k₂ = k₄ = 1`, and `2`, `4` lie on different
lines (the census line partition is `{1}, {2,3}, {4}, {7}`).  A3's downstream reading of its
rigidity claim — "no value of `kₐ` recurs" — is therefore false as stated; what carries the claim
is the depth-`(a+2)` hypothesis, which `no_selfRef_failure_le_256` shows to be vacuous on the
certified range. -/
@[category research solved, AMS 11, ref "Bug12" "DD90", group "bugeaud_10_13"]
theorem resid_recurs : ∃ a b : ℕ, a < b ∧ IsFailure 3 2 (3 / 4) a ∧ IsFailure 3 2 (3 / 4) b ∧
    resid 3 2 a = resid 3 2 b :=
  ⟨2, 4, by norm_num,
    (failures_up_to_256 2 (by norm_num) (by norm_num)).mpr (by norm_num),
    (failures_up_to_256 4 (by norm_num) (by norm_num)).mpr (by norm_num),
    by rw [resid_two, resid_four]⟩

end BB13
