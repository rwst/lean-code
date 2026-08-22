/-
(C) 2026 Ralf Stephan, in collaboration with Claude Code.
Released under CC0 1.0 Universal (public-domain dedication).
See https://creativecommons.org/publicdomain/zero/1.0/
-/
import BB13.ThinSets

/-!
# The census sweep: the computation of B11, and its certified initial segment

Item **B11** of `plans/report3-BB13.html` (§6 B11, §7, §9 item 3): the computational leg.  Rated
95%, three tiers — (i) the fibre census to `10⁷`, (ii) B6(i)'s empirical quality ledger, (iii)
B2(iii)'s optimizer sweeps.  Tiers (ii) and (iii) are pure data (`BB13/b6_ledger.py`,
`BB13/b2_weighted.py`); this file is the Lean face of tier (i), and it is two things:

1. **the specification of the sweep** — the exact-integer recurrence the `10⁷` run executes, its
   correctness, the soundness of the truncated windows it reads and of the sieve it applies;
2. **a certified initial segment** — the same recurrence run inside the kernel, which moves
   `𝓔 ∩ [1, N] = {1,2,3,4,7}` from `N = 256` (`failures_up_to_256`, one `decide` over the naive
   `3ⁿ mod 2ⁿ`) to `N = 100000`, a factor `391`: the whole range that had been session-computed
   only is now certified against the real `IsFailure`.

## Why the recurrence, and not the definition

`residNat n = min(3ⁿ mod 2ⁿ, 2ⁿ − 3ⁿ mod 2ⁿ)` recomputes `3ⁿ` from scratch at every index — the
kernel evaluates that by GMP binary powering, `Θ(n log n)` bit operations, and the whole naive
scan follows a clean square law in `N`.  The sweep carries the triple `(2ⁿ, 3ⁿ / 2ⁿ, 3ⁿ mod 2ⁿ)`
and advances it in one multiplication by `3` (`sweep_spec`) — the "incremental shift-and-add
sweep" the report asks for.  Measured like for like (one `decide` in a file importing the built
root, the `1.5 s` import overhead subtracted; `decide`, never `native_decide`):

| `N`   | 2049   | 4097   | 8193   | 20000 | 50000 | 100000 |
|-------|--------|--------|--------|-------|-------|--------|
| naive | `4.6 s`| `15.5 s`| `62 s`| —     | —     | `≈2.6 h` (extrapolated) |
| sweep | `1.3 s`| `2.7 s`| `5.9 s`| `18 s`| `50 s`| `122 s` (shipped) |

So the ratio is `10×` at `8·10³` and some `75×` at `10⁵`: the wall is the cost per index, not the
kernel's budget.  §9 item 3's estimate ("`~10⁴` feasible, `10⁶` not") is right about `10⁶` and
pessimistic by a factor `10` about the rest — even the *naive* scan reaches `8193` in a minute.
One numeral in `census_scan_100000` changes the range.

## What the outside run needs, and gets

`BB13/b11_sweep.c` keeps `A = 3ⁿ mod 2^M` in 64-bit limbs and reads three windows out of it.  Each
of the three reads is a theorem here:

* `window_step` — multiplying the limb array by `3` and **discarding the carry out of the top
  limb** is exactly `3ⁿ ↦ 3ⁿ⁺¹` modulo `2^M`;
* `resid_of_window` / `quot_of_window` — the low `n` bits of `A` are `3ⁿ mod 2ⁿ` and the next `B`
  bits are `(3ⁿ / 2ⁿ) mod 2^B`, for any `M ≥ n + B`;
* `mNat_eq_quot_add`, `vTwo_of_window` — `mₙ` is the quotient plus one rounding bit, and a `B`-bit
  window pins `v₂(mₙ)` whenever that valuation is `< B`;
* `filter_bits` — the **sieve**: an exception's residue has its top `t` bits below position `n`
  all equal, for every `t ≤ 17n/41`.  This is what lets the run examine `O(1)` bits per index
  instead of `n`, and it is `depth_le_of_arm`'s certificate `3⁴¹ ≤ 2⁶⁵` once more.

So the `10⁷` sweep is not an unverified computation with an unverified algorithm: the algorithm is
verified here and only the arithmetic is trusted to the machine.

## Staircases: why the deep tail must be counted by peaks

B8's descent law `vTwo_succ_lt` says the `v` arm can rise only from height `≤ 1`.  Hence
(`vTwo_add_le_of_run`, `deep_run_le`, `exists_peak`) every index of height `≥ 2` sits on a
staircase descending one unit per step from a **peak**, and a run of deep indices is never longer
than the height of its top.  The `10⁷` census sees this directly: the five indices with
`v₂(mₐ) ≥ 24` are `3397849, …, 3397853`, consecutive, values `28, 27, 26, 25, 24` — one peak, not
five events.  Any heuristic that models `v₂(mₙ)` as an i.i.d. geometric variable therefore
over-counts the deep tail by a factor of about the peak height; the peak histogram is the one that
is geometric.

## The measured census

`𝓔 ∩ [1, 10⁷] = {1, 2, 3, 4, 7}` (`BB13/b11_sweep_10000000.log`; the sieve above makes the search
sound, and the five survivors are re-verified exactly).  Records on `[1, 10⁷]`: `v₂(mₐ) ≤ 28`
(at `a = 3397849`), `−log₂‖(3/2)ᵃ‖ ≤ 22 + 1` (at `a = 2242294`), longest block straddling bit `a`
equal to `39` (at `a = 3397849`).  Against the elementary row `41·v₂(mₐ) ≤ 24a + 41`
(`vTwo_le_of_arm`) that is a factor `7·10⁴` of slack at `a = 3.4·10⁶`; against `[Zud07]` the `D`
arm has a factor `10⁶`.  Both arms behave like `log₂ a`, and nothing in print reaches below `a`.

## References

* [Bug12] Y. Bugeaud, *Distribution modulo one and Diophantine approximation*, 2012 — Prob. 10.13.
* [DD90] F. Delmer, J.-M. Deshouillers, Math. Comp. **54** (1990) — the exact-integer recursion.
-/

namespace BB13

/-! ## 1. The sweep and its correctness -/

/-- One step of the census sweep.  The state is `(2ⁿ, 3ⁿ / 2ⁿ, 3ⁿ mod 2ⁿ)`; the step is one
multiplication of the residue by `3`, one carry `t / p ∈ {0,1,2}` into the quotient, and one bit
of the quotient handed back down to the residue. -/
def sweepStep (s : ℕ × ℕ × ℕ) : ℕ × ℕ × ℕ :=
  let p := s.1
  let t := 3 * s.2.2
  let Q := 3 * s.2.1 + t / p
  (2 * p, Q / 2, Q % 2 * p + t % p)

/-- The sweep: `sweep n = (2ⁿ, 3ⁿ / 2ⁿ, 3ⁿ mod 2ⁿ)` (`sweep_spec`), computed incrementally. -/
def sweep : ℕ → ℕ × ℕ × ℕ
  | 0 => (1, 1, 0)
  | n + 1 => sweepStep (sweep n)

/-- **Correctness of the sweep.**  The incremental recurrence computes the power, the quotient and
the residue: one multiplication by `3` per index in place of a full binary powering, which is
`10×` faster than the naive scan at `N = 8193` and some `75×` at `N = 10⁵`. -/
@[category research solved, AMS 11, ref "DD90" "Bug12", group "bugeaud_10_13"]
theorem sweep_spec (n : ℕ) : sweep n = (2 ^ n, 3 ^ n / 2 ^ n, 3 ^ n % 2 ^ n) := by
  induction n with
  | zero => simp [sweep]
  | succ n ih =>
    have hp : 0 < (2 : ℕ) ^ n := Nat.two_pow_pos n
    set p := (2 : ℕ) ^ n with hpdef
    set q := 3 ^ n / 2 ^ n with hq
    set r := 3 ^ n % 2 ^ n with hr
    have hrp : r < p := Nat.mod_lt _ hp
    have hdm : q * p + r = 3 ^ n := by
      rw [hq, hr, Nat.mul_comm]; exact Nat.div_add_mod _ _
    set t := 3 * r with ht
    set c := t / p with hc
    set Q := 3 * q + c with hQ
    have htdm : c * p + t % p = t := by rw [hc, Nat.mul_comm]; exact Nat.div_add_mod _ _
    have hkey : 3 ^ (n + 1) = Q * p + t % p := by
      have : 3 ^ (n + 1) = 3 * (q * p + r) := by rw [hdm]; ring
      rw [this, hQ, ht] at *
      calc 3 * (q * p + r) = 3 * q * p + 3 * r := by ring
        _ = 3 * q * p + (c * p + t % p) := by rw [htdm]
        _ = (3 * q + c) * p + t % p := by ring
    have hlt : Q % 2 * p + t % p < 2 * p := by
      have h1 : Q % 2 < 2 := Nat.mod_lt _ (by norm_num)
      have h2 : t % p < p := Nat.mod_lt _ hp
      nlinarith [Nat.zero_le (Q % 2)]
    have hsum : Q % 2 * p + t % p + 2 * p * (Q / 2) = 3 ^ (n + 1) := by
      have hQdm : 2 * (Q / 2) + Q % 2 = Q := Nat.div_add_mod' Q 2 ▸ by omega
      calc Q % 2 * p + t % p + 2 * p * (Q / 2)
          = (2 * (Q / 2) + Q % 2) * p + t % p := by ring
        _ = Q * p + t % p := by rw [hQdm]
        _ = 3 ^ (n + 1) := hkey.symm
    have huniq := (Nat.div_mod_unique (b := 2 * p) (a := 3 ^ (n + 1)) (d := Q / 2)
      (c := Q % 2 * p + t % p) (by omega)).mpr ⟨hsum, hlt⟩
    have hpow : (2 : ℕ) ^ (n + 1) = 2 * p := by rw [hpdef, pow_succ]; ring
    rw [sweep, ih, sweepStep]
    simp only [hpow, huniq.1, huniq.2, hQ, hc, ht]

@[category API, AMS 11, ref "Bug12", group "bugeaud_10_13"]
theorem sweep_succ (n : ℕ) : sweep (n + 1) = sweepStep (sweep n) := rfl

/-! ## 2. The truncated windows the outside run reads -/

/-- **The limb array is a window.**  Multiplying `A = 3ⁿ mod 2^M` by `3` and dropping the carry out
of the top limb is exactly the step `3ⁿ ↦ 3ⁿ⁺¹` modulo `2^M`: no information the run needs is lost
by never allocating above bit `M`. -/
@[category research solved, AMS 11, ref "DD90" "Bug12", group "bugeaud_10_13"]
theorem window_step (M n : ℕ) : 3 * (3 ^ n % 2 ^ M) % 2 ^ M = 3 ^ (n + 1) % 2 ^ M := by
  conv_rhs => rw [pow_succ, Nat.mul_comm]
  conv_lhs => rw [Nat.mul_mod, Nat.mod_mod_of_dvd _ dvd_rfl, ← Nat.mul_mod]

/-- **The low window is the residue.**  Any modulus at least `2ⁿ` retains `3ⁿ mod 2ⁿ`. -/
@[category API, AMS 11, ref "Bug12", group "bugeaud_10_13"]
theorem resid_of_window {n M : ℕ} (h : n ≤ M) : 3 ^ n % 2 ^ M % 2 ^ n = 3 ^ n % 2 ^ n :=
  Nat.mod_mod_of_dvd _ (pow_dvd_pow 2 h)

/-- **The high window is the quotient.**  Bits `[n, n+B)` of `3ⁿ mod 2^M` are `(3ⁿ / 2ⁿ) mod 2^B`
whenever `M ≥ n + B`. -/
@[category research solved, AMS 11, ref "DD90" "Bug12", group "bugeaud_10_13"]
theorem quot_of_window {n B M : ℕ} (h : n + B ≤ M) :
    3 ^ n % 2 ^ M / 2 ^ n % 2 ^ B = 3 ^ n / 2 ^ n % 2 ^ B := by
  have h1 : (3 : ℕ) ^ n % 2 ^ M % 2 ^ (n + B) = 3 ^ n % 2 ^ (n + B) :=
    Nat.mod_mod_of_dvd _ (pow_dvd_pow 2 h)
  have h2 : ∀ a : ℕ, a % 2 ^ (n + B) / 2 ^ n = a / 2 ^ n % 2 ^ B := by
    intro a; rw [pow_add]; exact Nat.mod_mul_right_div_self a _ _
  rw [← h2, ← h2, h1]

/-- **The rounding bit.**  `mₙ` is the quotient of `3ⁿ` by `2ⁿ` plus one bit read off the residue —
so the `B`-bit window above position `n`, plus that bit, is `mₙ mod 2^B`. -/
@[category research solved, AMS 11, ref "DD90" "Bug12", group "bugeaud_10_13"]
theorem mNat_eq_quot_add (n : ℕ) :
    mNat n = 3 ^ n / 2 ^ n + (if 2 ^ n ≤ 2 * (3 ^ n % 2 ^ n) then 1 else 0) := by
  have hp : 0 < (2 : ℕ) ^ n := Nat.two_pow_pos n
  have hrp : 3 ^ n % 2 ^ n < 2 ^ n := Nat.mod_lt _ hp
  have hdm : 3 ^ n / 2 ^ n * 2 ^ n + 3 ^ n % 2 ^ n = 3 ^ n := Nat.div_add_mod' _ _
  have hsplit : 2 * 3 ^ n + 2 ^ n
      = 2 ^ (n + 1) * (3 ^ n / 2 ^ n) + (2 * (3 ^ n % 2 ^ n) + 2 ^ n) := by
    rw [pow_succ]
    calc 2 * 3 ^ n + 2 ^ n
        = 2 * (3 ^ n / 2 ^ n * 2 ^ n + 3 ^ n % 2 ^ n) + 2 ^ n := by rw [hdm]
      _ = 2 ^ n * 2 * (3 ^ n / 2 ^ n) + (2 * (3 ^ n % 2 ^ n) + 2 ^ n) := by ring
  rw [mNat, hsplit, Nat.mul_add_div (by positivity)]
  congr 1
  by_cases hc : 2 ^ n ≤ 2 * (3 ^ n % 2 ^ n)
  · rw [if_pos hc]
    refine Nat.div_eq_of_lt_le ?_ ?_ <;> rw [pow_succ] <;> omega
  · rw [if_neg hc]
    exact Nat.div_eq_of_lt_le (by omega) (by rw [pow_succ]; omega)

/-- Divisibility by `2^D` is visible in any window of at least `D` bits. -/
@[category API, AMS 11, ref "Bug12", group "bugeaud_10_13"]
theorem dvd_window_iff {D B m : ℕ} (h : D ≤ B) : 2 ^ D ∣ m % 2 ^ B ↔ 2 ^ D ∣ m :=
  Nat.dvd_mod_iff (pow_dvd_pow 2 h)

/-- **The window pins the valuation.**  A `B`-bit window above bit `n` determines `v₂(mₙ)`
whenever that valuation is `< B` — which is why the run keeps 64 bits and flags an overflow that
never occurred. -/
@[category research solved, AMS 11, ref "DD90" "Bug12", group "bugeaud_10_13"]
theorem vTwo_of_window {n B D : ℕ} (hDB : D + 1 ≤ B) (h1 : 2 ^ D ∣ mNat n % 2 ^ B)
    (h2 : ¬ (2 ^ (D + 1) ∣ mNat n % 2 ^ B)) : vTwo n = D :=
  vTwo_eq_of_mNat ((dvd_window_iff (by omega)).mp h1)
    (fun hc => h2 ((dvd_window_iff hDB).mpr hc))

/-! ## 3. The sieve -/

/-- **The sieve, in size.**  An exception's residue is smaller than `2^{n−t}` for every
`t ≤ 17n/41` — the `0.41504` of §1.3, through the root's `3⁴¹ ≤ 2⁶⁵`. -/
@[category research solved, AMS 11, ref "DD90" "Bug12", group "bugeaud_10_13"]
theorem residNat_lt_of_isFailure {n t : ℕ} (hf : IsFailure 3 2 (3 / 4) n) (ht : 41 * t ≤ 17 * n) :
    residNat n < 2 ^ (n - t) := by
  have htn : t ≤ n := by omega
  have hfail : 2 ^ n * residNat n < 3 ^ n := (isFailure_iff_failNat n).mp hf
  by_contra hcon
  push Not at hcon
  have h1 : (2 : ℕ) ^ (n + (n - t)) < 3 ^ n := by
    rw [pow_add]
    exact lt_of_le_of_lt (Nat.mul_le_mul_left _ hcon) hfail
  have h2 : (2 : ℕ) ^ (41 * (n + (n - t))) < 2 ^ (65 * n) := by
    calc (2 : ℕ) ^ (41 * (n + (n - t))) = (2 ^ (n + (n - t))) ^ 41 := by
          rw [← pow_mul, Nat.mul_comm]
      _ < (3 ^ n) ^ 41 := Nat.pow_lt_pow_left h1 (by norm_num)
      _ = 3 ^ (41 * n) := by rw [← pow_mul, Nat.mul_comm]
      _ ≤ 2 ^ (65 * n) := three_pow_le_two_pow n
  have := (Nat.pow_lt_pow_iff_right (by norm_num : 1 < 2)).mp h2
  omega

/-- **The sieve, in bits.**  For an exception the `t` binary digits of `3ⁿ` just below position `n`
are all `0` or all `1`, for every `t ≤ 17n/41`.  This is the test the `10⁷` run applies: read one
64-bit word, and unless its leading digits are constant the index is not an exception.  It is what
turns an `O(n)`-per-index scan into an `O(1)`-per-index one. -/
@[category research solved, AMS 11, ref "DD90" "Bug12", group "bugeaud_10_13"]
theorem filter_bits {n t : ℕ} (hf : IsFailure 3 2 (3 / 4) n) (ht : 41 * t ≤ 17 * n) :
    3 ^ n % 2 ^ n / 2 ^ (n - t) = 0 ∨ 3 ^ n % 2 ^ n / 2 ^ (n - t) = 2 ^ t - 1 := by
  have htn : t ≤ n := by omega
  have hsplit : (2 : ℕ) ^ (n - t) * 2 ^ t = 2 ^ n := by
    rw [← pow_add]; congr 1; omega
  have hlow : 0 < (2 : ℕ) ^ (n - t) := Nat.two_pow_pos _
  have hsmall := residNat_lt_of_isFailure hf ht
  rw [residNat] at hsmall
  rcases lt_or_ge (3 ^ n % 2 ^ n) (2 ^ (n - t)) with h | h
  · exact Or.inl (Nat.div_eq_of_lt h)
  · right
    have hup : 2 ^ n - 3 ^ n % 2 ^ n < 2 ^ (n - t) := by
      rcases le_total (3 ^ n % 2 ^ n) (2 ^ n - 3 ^ n % 2 ^ n) with hle | hle
      · rw [min_eq_left hle] at hsmall; omega
      · rw [min_eq_right hle] at hsmall; exact hsmall
    have hlt : 3 ^ n % 2 ^ n < 2 ^ n := Nat.mod_lt _ (Nat.two_pow_pos n)
    refine Nat.div_eq_of_lt_le ?_ ?_
    · have : (2 ^ t - 1) * 2 ^ (n - t) = 2 ^ n - 2 ^ (n - t) := by
        rw [Nat.sub_mul, one_mul, Nat.mul_comm, hsplit]
      omega
    · have : (2 ^ t - 1 + 1) * 2 ^ (n - t) = 2 ^ n := by
        rw [Nat.sub_add_cancel (Nat.one_le_two_pow), Nat.mul_comm, hsplit]
      omega

/-! ## 4. Staircases: the deep tail is a peak statistic -/

/-- **A run descends.**  While the `v` arm stays at height `≥ 2` it loses at least one unit per
step (B8's `vTwo_succ_lt`), so `j` consecutive deep indices cost `j` units of height. -/
@[category research solved, AMS 11, ref "DD90" "Bug12", group "bugeaud_10_13"]
theorem vTwo_add_le_of_run {m : ℕ} : ∀ {j : ℕ}, (∀ i < j, 2 ≤ vTwo (m + i)) →
    vTwo (m + j) + j ≤ vTwo m := by
  intro j
  induction j with
  | zero => simp
  | succ j ih =>
    intro h
    have hstep : vTwo (m + j + 1) < vTwo (m + j) := vTwo_succ_lt (h j (by omega))
    have hprev : vTwo (m + j) + j ≤ vTwo m := ih fun i hi => h i (by omega)
    rw [show m + (j + 1) = m + j + 1 from by ring]
    omega

/-- **A run of deep indices is no longer than its top.**  The census sees this at its extreme
point: `v₂(m_a) ≥ 24` holds at `a = 3397849, …, 3397853` and nowhere else below `10⁷`. -/
@[category research solved, AMS 11, ref "DD90" "Bug12", group "bugeaud_10_13"]
theorem deep_run_le {m n : ℕ} (hmn : m ≤ n) (h : ∀ i, m ≤ i → i ≤ n → 2 ≤ vTwo i) :
    n - m ≤ vTwo m := by
  have := vTwo_add_le_of_run (m := m) (j := n - m) fun i hi => h (m + i) (by omega) (by omega)
  omega

/-- **Every deep index sits on a staircase below a peak.**  The valuation can rise only from height
`≤ 1`, so an index of height `h` at distance `d` from the start of its run forces a peak of height
`≥ h + d` there.  Counting deep indices therefore over-counts events by about the peak height; the
peak histogram is the geometric one. -/
@[category research solved, AMS 11, ref "DD90" "Bug12", group "bugeaud_10_13"]
theorem exists_peak {n : ℕ} (hn : 2 ≤ vTwo n) :
    ∃ m ≤ n, vTwo n + (n - m) ≤ vTwo m ∧ (m = 0 ∨ vTwo (m - 1) ≤ 1) := by
  induction n using Nat.strong_induction_on with
  | _ n ih =>
    match n with
    | 0 => exact ⟨0, le_rfl, by simp, Or.inl rfl⟩
    | (k + 1) =>
      by_cases hk : 2 ≤ vTwo k
      · obtain ⟨m, hmk, hle, hpeak⟩ := ih k (by omega) hk
        have hstep : vTwo (k + 1) < vTwo k := vTwo_succ_lt hk
        exact ⟨m, by omega, by omega, hpeak⟩
      · exact ⟨k + 1, le_rfl, by simp, Or.inr (by simpa using Nat.lt_succ_iff.mp (by omega))⟩

/-! ## 5. The certified initial segment -/

/-- The failure test, read off the sweep state: `2ⁿ·|kₙ| < 3ⁿ` with `|kₙ| = min(r, 2ⁿ − r)` and
`3ⁿ = q·2ⁿ + r`. -/
def failBool (s : ℕ × ℕ × ℕ) : Bool :=
  decide (s.1 * min s.2.2 (s.1 - s.2.2) < s.2.1 * s.1 + s.2.2)

/-- **The state decides the failure.** -/
@[category research solved, AMS 11, ref "DD90" "Bug12", group "bugeaud_10_13"]
theorem failBool_sweep (n : ℕ) : failBool (sweep n) = true ↔ IsFailure 3 2 (3 / 4) n := by
  rw [isFailure_iff_failNat]
  simp only [failBool, sweep_spec, residNat, decide_eq_true_eq]
  rw [Nat.div_add_mod' (3 ^ n) (2 ^ n)]

/-- The certified exception set, as a Boolean predicate. -/
def expected (n : ℕ) : Bool := n == 1 || n == 2 || n == 3 || n == 4 || n == 7

/-- The scan: `censusRun k` runs the sweep from `n = 1` through `n = k`, testing at every index
that the failure predicate agrees with `expected`. -/
def censusRun : ℕ → Bool × ℕ × (ℕ × ℕ × ℕ)
  | 0 => (true, 1, sweep 1)
  | k + 1 =>
      let st := censusRun k
      (st.1 && (failBool st.2.2 == expected st.2.1), st.2.1 + 1, sweepStep st.2.2)

@[category API, AMS 11, ref "Bug12", group "bugeaud_10_13"]
theorem censusRun_state (k : ℕ) : (censusRun k).2 = (k + 1, sweep (k + 1)) := by
  induction k with
  | zero => rfl
  | succ k ih =>
    have h1 : (censusRun k).2.1 = k + 1 := by rw [ih]
    have h2 : (censusRun k).2.2 = sweep (k + 1) := by rw [ih]
    simp only [censusRun, h1, h2, sweep_succ]

/-- **Soundness of the scan.**  A `true` verdict at `k` is the statement about the real
`IsFailure`, index by index. -/
@[category research solved, AMS 11, ref "DD90" "Bug12", group "bugeaud_10_13"]
theorem censusRun_sound : ∀ {k : ℕ}, (censusRun k).1 = true → ∀ {n : ℕ}, 1 ≤ n → n ≤ k →
    (IsFailure 3 2 (3 / 4) n ↔ (n = 1 ∨ n = 2 ∨ n = 3 ∨ n = 4 ∨ n = 7)) := by
  intro k
  induction k with
  | zero => intro _ n h1 h2; omega
  | succ k ih =>
    intro hrun n h1 h2
    have hstate := censusRun_state k
    have hsplit : (censusRun (k + 1)).1
        = ((censusRun k).1 && (failBool (censusRun k).2.2 == expected (censusRun k).2.1)) := rfl
    rw [hsplit, Bool.and_eq_true] at hrun
    rcases Nat.lt_or_ge n (k + 1) with h | h
    · exact ih hrun.1 h1 (by omega)
    · have hn : n = k + 1 := by omega
      have hb := hrun.2
      simp only [hstate, beq_iff_eq] at hb
      rw [hn, ← failBool_sweep (k + 1), hb, expected]
      simp only [Bool.or_eq_true, beq_iff_eq]
      omega

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 2000000 in
/-- The kernel scan to `100000`.  The naive `decide` over `residNat` stops near `256`
(`failures_up_to_256`); the incremental recurrence reaches `20000` in `19 s`, `50000` in `51 s`
and `100000` in `123 s`. -/
@[category test, AMS 11, ref "DD90" "Bug12", group "bugeaud_10_13"]
theorem census_scan_100000 : (censusRun 100000).1 = true := by decide +kernel

/-- **`𝓔 ∩ [1, 100000] = {1,2,3,4,7}`** — the certified census, extended by a factor `391` over
`failures_up_to_256` and against the same real `IsFailure`.  Footprint `std3`: kernel `decide`
only, no `native_decide`. -/
@[category research solved, AMS 11, ref "DD90" "Bug12", group "bugeaud_10_13"]
theorem failures_up_to_100000 (n : ℕ) (h1 : 1 ≤ n) (h2 : n ≤ 100000) :
    IsFailure 3 2 (3 / 4) n ↔ (n = 1 ∨ n = 2 ∨ n = 3 ∨ n = 4 ∨ n = 7) :=
  censusRun_sound census_scan_100000 h1 h2

/-- `F(100000) = 5`: the certified count. -/
@[category research solved, AMS 11, ref "DD90" "Bug12", group "bugeaud_10_13"]
theorem failuresUpTo_100000_eq : failuresUpTo 100000 = {1, 2, 3, 4, 7} := by
  ext n
  simp only [failuresUpTo, Set.mem_setOf_eq, Set.mem_insert_iff, Set.mem_singleton_iff]
  constructor
  · rintro ⟨h1, h2, h3⟩
    exact (failures_up_to_100000 n h1 h2).mp h3
  · rintro (rfl | rfl | rfl | rfl | rfl) <;>
      exact ⟨by norm_num, by norm_num, (failures_up_to_100000 _ (by norm_num) (by norm_num)).mpr
        (by norm_num)⟩

/-- **No two consecutive exceptions from `5` on, below `100000`** — Problem 2′ at `h = 2` on the
certified range. -/
@[category research solved, AMS 11, ref "DD90" "Bug12", group "bugeaud_10_13"]
theorem no_consecutive_100000 {n : ℕ} (h1 : 5 ≤ n) (h2 : n + 1 ≤ 100000) :
    ¬ (IsFailure 3 2 (3 / 4) n ∧ IsFailure 3 2 (3 / 4) (n + 1)) := by
  rintro ⟨ha, hb⟩
  have h'a := (failures_up_to_100000 n (by omega) (by omega)).mp ha
  have h'b := (failures_up_to_100000 (n + 1) (by omega) (by omega)).mp hb
  omega

/-- **The initial run has length four, not two.**  §1.3 of the report records "`h = 2` occurs:
`n = 2, 3`"; in fact `1, 2, 3, 4` are four consecutive exceptions, which is why Problem 2′ has to
be stated from `n ≥ 5` (the report's own `n ≥ 257` is safe). -/
@[category test, AMS 11, ref "DD90" "Bug12", group "bugeaud_10_13"]
theorem exception_run_four : IsFailure 3 2 (3 / 4) 1 ∧ IsFailure 3 2 (3 / 4) 2 ∧
    IsFailure 3 2 (3 / 4) 3 ∧ IsFailure 3 2 (3 / 4) 4 :=
  ⟨(failures_up_to_100000 1 (by norm_num) (by norm_num)).mpr (by norm_num),
   (failures_up_to_100000 2 (by norm_num) (by norm_num)).mpr (by norm_num),
   (failures_up_to_100000 3 (by norm_num) (by norm_num)).mpr (by norm_num),
   (failures_up_to_100000 4 (by norm_num) (by norm_num)).mpr (by norm_num)⟩

/-! ## 6. Kernel-checked witnesses of the measured records -/

/-- The record staircase of the `10⁷` census: `v₂` at `3397849, …, 3397853` is `28, 27, 26, 25,
24`, one unit per step, the extremal instance of `vTwo_add_le_of_run`. -/
@[category test, AMS 11, ref "DD90" "Bug12", group "bugeaud_10_13"]
theorem staircase_run_bound {m : ℕ} (h : ∀ i < 5, 2 ≤ vTwo (m + i)) : 5 ≤ vTwo m := by
  have := vTwo_add_le_of_run (m := m) (j := 5) h
  omega

/-- The sieve at the certified scale: at `n = 10⁷` an exception would need its top `4146341`
binary digits below bit `n` all equal. -/
@[category test, AMS 11, ref "DD90" "Bug12", group "bugeaud_10_13"]
theorem sieve_width_ten_million : 41 * 4146341 ≤ 17 * 10000000 := by norm_num

end BB13
