/-
(C) 2026 Ralf Stephan, in collaboration with Claude Code.
Released under CC0 1.0 Universal (public-domain dedication).
See https://creativecommons.org/publicdomain/zero/1.0/
-/
import BB6.Basic
import Mathlib.Analysis.Complex.ExponentialBounds
import Corpus.Util.Attributes.Basic
import Corpus.Util.Attributes.Database

/-!
# Proposition C — ordering the readings of "very rapidly increasing"

Problem 10.6 [Bug12, Ch. 10] does not say what *very rapidly increasing* means.  The note reads it
four ways; three of them are conditions on the size or the sparsity of the sequence (R1, R2) or on
its multiplicative structure (R4), and one is a floor under the consecutive ratios:

* **R1** (growth) `Bugeaud06.HasIntermediateGrowth α m` — eventually `exp (nᵅ) ≤ mₙ`;
* **R2** (sparsity) — an upper bound on the counting function `BB6.countingFn`;
* **R3** (ratio floor) `Bugeaud06.IsGenuinelySublacunary m` — eventually `1 + c/log n ≤ mₙ₊₁/mₙ`.

`BB6/Vacuity.lean` shows R1 and R2 are vacuous as readings: runs of consecutive integers satisfy
either at any prescribed strength and are still universally densifying.  This file proves the
converse half of the ordering, which is what leaves R3 as the only reading with content:

* `BB6.isGenuinelySublacunary_of_isLacunary` — R3 is *implied* by lacunarity, so it is a floor
  under the ratios and not a non-lacunarity hypothesis;
* `BB6.log_lower_of_r3` — **the master estimate**: R3 with constant `c` forces
  `log mₙ ≥ (c/4)·n/log n` eventually.  Everything else in the file is a corollary;
* `BB6.hasIntermediateGrowth_of_r3` — R3 ⟹ R1, for *every* `α < 1`;
* `BB6.countingFn_of_r3` — R3 ⟹ R2, at `π_A(N) = O(log N · log log N)`;
* `BB6.proposition_C` — the package.

The estimate is the discrete form of `∫ dt/log t`: R3 gives `log mₙ₊₁ - log mₙ ≥ log(1 + c/log n)`,
which is `≥ c/(2 log n)` once `c/log n ≤ 1`, and summing that from `N` to `n` against the *largest*
denominator `log n` gives `(n - N)·c/(2 log n)`.  Because the denominator is monotone the sum needs
no `Finset` bookkeeping: the induction carries `j · c/(2 log (N+j))` directly.

*References:*
  - [Bug12] Bugeaud, Y. *Distribution modulo one and Diophantine approximation*, CUP 2012, Ch. 10.
-/

namespace BB6

open Filter

/-! ## R3 is a floor, not a non-lacunarity hypothesis

Worth stating because the name invites the opposite reading: "genuinely sublacunary" sounds like a
denial of lacunarity, and it is not one.  A lacunary sequence has ratios bounded below by a
*constant* `> 1`, which is stronger than the `1 + c/log n` R3 demands. -/

/-- **Lacunary ⟹ R3.**  If `c · mₖ < mₖ₊₁` eventually with `c > 1`, then the ratio exceeds
`1 + (c-1)` , hence exceeds `1 + (c-1)/log n` for every `n ≥ 3`. -/
@[category research solved, AMS 11, ref "Bug12", group "bugeaud_10_6"]
theorem isGenuinelySublacunary_of_isLacunary {m : ℕ → ℕ} (hpos : ∀ n, 0 < m n)
    (h : IsLacunary m) : Bugeaud06.IsGenuinelySublacunary m := by
  obtain ⟨c, hc, hev⟩ := h
  refine ⟨c - 1, by linarith, ?_⟩
  filter_upwards [hev, eventually_ge_atTop 3] with n hn hn3
  have hn3R : (3 : ℝ) ≤ (n : ℝ) := by exact_mod_cast hn3
  have hpn : (0 : ℝ) < (m n : ℝ) := by exact_mod_cast hpos n
  have hlog : (1 : ℝ) ≤ Real.log n := by
    calc (1 : ℝ) = Real.log (Real.exp 1) := (Real.log_exp 1).symm
      _ ≤ Real.log n := Real.log_le_log (Real.exp_pos 1) (by linarith [Real.exp_one_lt_d9])
  have hdiv : (c - 1) / Real.log n ≤ c - 1 := by
    rw [div_le_iff₀ (by linarith)]
    nlinarith
  rw [le_div_iff₀ hpn]
  nlinarith

/-! ## The master estimate -/

/-- An R3-regular sequence is eventually positive: the ratio is `> 1` at large `n`, and a ratio
with a zero denominator is `0` in Lean's convention. -/
@[category API, AMS 11, group "bugeaud_10_6"]
theorem eventually_pos_of_r3 {m : ℕ → ℕ} (h : Bugeaud06.IsGenuinelySublacunary m) :
    ∀ᶠ n : ℕ in atTop, 0 < m n := by
  obtain ⟨c, hc, hev⟩ := h
  filter_upwards [hev, eventually_ge_atTop 3] with n hn hn3
  by_contra hcon
  have h0 : m n = 0 := by omega
  have hn3R : (3 : ℝ) ≤ (n : ℝ) := by exact_mod_cast hn3
  have hlog : (0 : ℝ) < Real.log n := Real.log_pos (by linarith)
  rw [h0, Nat.cast_zero, div_zero] at hn
  nlinarith [div_pos hc hlog]

/-- The per-step increment of `log mₙ`.  From `1 + c/log n ≤ mₙ₊₁/mₙ` and `log(1+x) ≥ x/(1+x)`,
with `x = c/log n ≤ 1` so that `1 + x ≤ 2`. -/
@[category API, AMS 11, group "bugeaud_10_6"]
theorem log_step_of_r3 {m : ℕ → ℕ} {c : ℝ} (hc : 0 < c)
    (hev : ∀ᶠ n : ℕ in atTop, (1 + c / Real.log n) ≤ (m (n + 1) : ℝ) / m n) :
    ∀ᶠ n : ℕ in atTop, c / (2 * Real.log n) ≤ Real.log (m (n + 1)) - Real.log (m n) := by
  filter_upwards [hev, tendsto_log_natCast.eventually_ge_atTop c,
    tendsto_log_natCast.eventually_ge_atTop 1] with n hn hcn h1n
  have hlogpos : (0 : ℝ) < Real.log n := by linarith
  set x : ℝ := c / Real.log n with hx
  have hx0 : 0 < x := div_pos hc hlogpos
  have hx1 : x ≤ 1 := by rw [hx, div_le_one hlogpos]; exact hcn
  -- both terms are positive: a zero denominator or numerator would make the ratio `0 < 1 + x`
  have hmn : 0 < m n := by
    by_contra hcon
    have h0 : m n = 0 := by omega
    rw [h0, Nat.cast_zero, div_zero] at hn
    linarith
  have hmnR : (0 : ℝ) < (m n : ℝ) := by exact_mod_cast hmn
  have hmn' : 0 < m (n + 1) := by
    by_contra hcon
    have h0 : m (n + 1) = 0 := by omega
    rw [h0, Nat.cast_zero, zero_div] at hn
    linarith
  have hmnR' : (0 : ℝ) < (m (n + 1) : ℝ) := by exact_mod_cast hmn'
  have hlogdiv : Real.log (1 + x) ≤ Real.log (m (n + 1)) - Real.log (m n) := by
    have h := Real.log_le_log (by linarith) hn
    rwa [Real.log_div (ne_of_gt hmnR') (ne_of_gt hmnR)] at h
  have hkey : x / 2 ≤ Real.log (1 + x) := by
    have h1 := Real.log_le_sub_one_of_pos (show (0 : ℝ) < 1 / (1 + x) by positivity)
    rw [Real.log_div one_ne_zero (by positivity), Real.log_one, zero_sub] at h1
    have h2 : 1 / (1 + x) ≤ 1 - x / 2 := by
      rw [div_le_iff₀ (by linarith)]
      nlinarith
    linarith
  have hrw : c / (2 * Real.log n) = x / 2 := by rw [hx]; ring
  rw [hrw]
  linarith

/-- The summed form, by induction and with **no `Finset`**: the denominator `log (N+j)` is
monotone in `j`, so the accumulated bound may be carried at the current denominator throughout. -/
@[category API, AMS 11, group "bugeaud_10_6"]
theorem log_lower_aux {m : ℕ → ℕ} {c : ℝ} {N : ℕ} (hc : 0 < c) (hN : 3 ≤ N)
    (hstep : ∀ n, N ≤ n → c / (2 * Real.log n) ≤ Real.log (m (n + 1)) - Real.log (m n))
    (hbase : 0 ≤ Real.log (m N)) :
    ∀ j : ℕ, (j : ℝ) * (c / (2 * Real.log ((N + j : ℕ) : ℝ))) ≤ Real.log (m (N + j)) := by
  intro j
  induction j with
  | zero => simpa using hbase
  | succ i ih =>
    have ha3 : 3 ≤ N + i := by omega
    have ha3R : (3 : ℝ) ≤ ((N + i : ℕ) : ℝ) := by exact_mod_cast ha3
    have hlogpos : (0 : ℝ) < Real.log ((N + i : ℕ) : ℝ) := Real.log_pos (by linarith)
    have hle : ((N + i : ℕ) : ℝ) ≤ ((N + i + 1 : ℕ) : ℝ) := by
      have : N + i ≤ N + i + 1 := by omega
      exact_mod_cast this
    have hlogle : Real.log ((N + i : ℕ) : ℝ) ≤ Real.log ((N + i + 1 : ℕ) : ℝ) :=
      Real.log_le_log (by linarith) hle
    have hlogpos' : (0 : ℝ) < Real.log ((N + i + 1 : ℕ) : ℝ) := by linarith
    have hmono : c / (2 * Real.log ((N + i + 1 : ℕ) : ℝ))
        ≤ c / (2 * Real.log ((N + i : ℕ) : ℝ)) := by
      rw [div_le_div_iff₀ (by linarith) (by linarith)]
      nlinarith
    have h1 := hstep (N + i) (by omega)
    have hnn : (0 : ℝ) ≤ ((i : ℝ) + 1) := by positivity
    have h2 := mul_le_mul_of_nonneg_left hmono hnn
    have hexp : ((i : ℝ) + 1) * (c / (2 * Real.log ((N + i : ℕ) : ℝ)))
        = (i : ℝ) * (c / (2 * Real.log ((N + i : ℕ) : ℝ)))
          + c / (2 * Real.log ((N + i : ℕ) : ℝ)) := by ring
    have hcast : ((i + 1 : ℕ) : ℝ) = (i : ℝ) + 1 := by push_cast; ring
    have hgoal : ((i + 1 : ℕ) : ℝ) * (c / (2 * Real.log ((N + i + 1 : ℕ) : ℝ)))
        ≤ Real.log (m (N + i + 1)) := by rw [hcast]; linarith
    have hidx : N + (i + 1) = N + i + 1 := by omega
    rw [hidx]
    exact hgoal

/-- **The master estimate (Proposition C, main clause).**  R3 with constant `c` forces
`log mₙ ≥ (c/4)·n/log n` eventually.  Both growth corollaries below are read off from this. -/
@[category research solved, AMS 11, ref "Bug12", group "bugeaud_10_6",
  formal_uses log_step_of_r3 log_lower_aux eventually_pos_of_r3]
theorem log_lower_of_r3 {m : ℕ → ℕ} (h : Bugeaud06.IsGenuinelySublacunary m) :
    ∃ c' > 0, ∀ᶠ n : ℕ in atTop, c' * n / Real.log n ≤ Real.log (m n) := by
  obtain ⟨c, hc, hev⟩ := h
  refine ⟨c / 4, by positivity, ?_⟩
  obtain ⟨N, hN⟩ := eventually_atTop.1
    (((log_step_of_r3 hc hev).and (eventually_pos_of_r3 ⟨c, hc, hev⟩)).and
      (eventually_ge_atTop 3))
  have hN3 : 3 ≤ N := (hN N le_rfl).2
  have hstep : ∀ n, N ≤ n → c / (2 * Real.log n) ≤ Real.log (m (n + 1)) - Real.log (m n) :=
    fun n hn => (hN n hn).1.1
  have hbase : 0 ≤ Real.log (m N) := by
    have h1 : 0 < m N := (hN N le_rfl).1.2
    have : (1 : ℝ) ≤ (m N : ℝ) := by exact_mod_cast h1
    exact Real.log_nonneg this
  have haux := log_lower_aux hc hN3 hstep hbase
  filter_upwards [eventually_ge_atTop (2 * N)] with n hn
  have hnN : N ≤ n := by omega
  have hj := haux (n - N)
  have hidx : N + (n - N) = n := by omega
  rw [hidx] at hj
  have hnR : (2 * N : ℝ) ≤ (n : ℝ) := by exact_mod_cast hn
  have hn3R : (3 : ℝ) ≤ (n : ℝ) := by
    have : (3 : ℕ) ≤ n := by omega
    exact_mod_cast this
  have hlogpos : (0 : ℝ) < Real.log n := Real.log_pos (by linarith)
  have hcast : ((n - N : ℕ) : ℝ) = (n : ℝ) - (N : ℝ) := by
    rw [Nat.cast_sub hnN]
  rw [hcast] at hj
  have hhalf : (n : ℝ) / 2 ≤ (n : ℝ) - (N : ℝ) := by linarith
  have hmul : ((n : ℝ) / 2) * (c / (2 * Real.log n)) ≤ ((n : ℝ) - N) * (c / (2 * Real.log n)) :=
    mul_le_mul_of_nonneg_right hhalf (by positivity)
  have hrw : ((n : ℝ) / 2) * (c / (2 * Real.log n)) = c / 4 * n / Real.log n := by
    field_simp
    ring
  linarith [hrw ▸ hmul]

/-! ## R3 ⟹ R1 -/

/-- **R3 ⟹ R1, at every exponent.**  An R3-regular sequence eventually dominates `exp (nᵅ)` for
every `α < 1` — so the growth reading is not merely implied, it is implied at full strength. -/
@[category research solved, AMS 11, ref "Bug12", group "bugeaud_10_6",
  formal_uses log_lower_of_r3 eventually_log_le eventually_pos_of_r3]
theorem hasIntermediateGrowth_of_r3 {m : ℕ → ℕ} (h : Bugeaud06.IsGenuinelySublacunary m)
    {α : ℝ} (hα0 : 0 < α) (hα1 : α < 1) : Bugeaud06.HasIntermediateGrowth α m := by
  obtain ⟨c', hc', hlow⟩ := log_lower_of_r3 h
  filter_upwards [hlow, eventually_log_le (c := c') (r := 1 - α) hc' (by linarith),
    eventually_pos_of_r3 h, eventually_ge_atTop 3] with n hn hlog hpos hn3
  have hn3R : (3 : ℝ) ≤ (n : ℝ) := by exact_mod_cast hn3
  have hnpos : (0 : ℝ) < (n : ℝ) := by linarith
  have hlogpos : (0 : ℝ) < Real.log n := Real.log_pos (by linarith)
  have hmpos : (0 : ℝ) < (m n : ℝ) := by exact_mod_cast hpos
  have hrp : (n : ℝ) ^ α * (n : ℝ) ^ (1 - α) = (n : ℝ) := by
    rw [← Real.rpow_add hnpos]; simp
  have hstep : (n : ℝ) ^ α ≤ c' * n / Real.log n := by
    rw [le_div_iff₀ hlogpos]
    calc (n : ℝ) ^ α * Real.log n ≤ (n : ℝ) ^ α * (c' * (n : ℝ) ^ (1 - α)) :=
          mul_le_mul_of_nonneg_left hlog (Real.rpow_nonneg hnpos.le α)
      _ = c' * ((n : ℝ) ^ α * (n : ℝ) ^ (1 - α)) := by ring
      _ = c' * n := by rw [hrp]
  calc Real.exp ((n : ℝ) ^ α) ≤ Real.exp (Real.log (m n)) :=
        Real.exp_le_exp.2 (le_trans hstep hn)
    _ = (m n : ℝ) := Real.exp_log hmpos

/-! ## R3 ⟹ R2

Sparsity is a growth statement in disguise (`BB6.countingFn_le`): for a strictly increasing `m`,
`π_A(N) ≤ M` as soon as `m_M > N`.  So the counting bound is just the master estimate read at the
index `M = ⌈4/c · log N · log log N⌉`, where it gives `log m_M ≥ 2 log N > log N`. -/

/-- **R3 ⟹ R2.**  An R3-regular strictly increasing sequence has
`π_A(N) = O(log N · log log N)` — sparser than any sublacunary sequence can be by more than a
`log log`, and in particular sparser than the `log N (log log log N)²` of [Kat16, Cor. 4.10] is
allowed to be. -/
@[category research solved, AMS 11, ref "Bug12" "Kat16", group "bugeaud_10_6",
  formal_uses log_lower_of_r3 countingFn_le tendsto_log_natCast]
theorem countingFn_of_r3 {m : ℕ → ℕ} (hm : StrictMono m)
    (h : Bugeaud06.IsGenuinelySublacunary m) :
    ∃ C > 0, ∀ᶠ N : ℕ in atTop,
      (countingFn m N : ℝ) ≤ C * Real.log N * Real.log (Real.log N) := by
  obtain ⟨c', hc', hlow⟩ := log_lower_of_r3 h
  obtain ⟨n₀, hn₀⟩ := eventually_atTop.1 hlow
  set K : ℝ := 4 / c' with hK
  have hK0 : 0 < K := by positivity
  have hT : Tendsto (fun n : ℕ => Real.log (Real.log n)) atTop atTop :=
    Real.tendsto_log_atTop.comp tendsto_log_natCast
  have hprod : Tendsto (fun n : ℕ => K * Real.log n * Real.log (Real.log n)) atTop atTop := by
    simpa [mul_assoc] using
      (Filter.Tendsto.const_mul_atTop hK0 (tendsto_log_natCast.atTop_mul_atTop₀ hT))
  refine ⟨K + 1, by positivity, ?_⟩
  filter_upwards [eventually_ge_atTop 3,
    tendsto_log_natCast.eventually_ge_atTop ((2 * K + 1) ^ 2 + 3),
    hprod.eventually_ge_atTop ((n₀ : ℝ) + 3)] with N hN3 hL hM
  have hN3R : (3 : ℝ) ≤ (N : ℝ) := by exact_mod_cast hN3
  have hNpos : (0 : ℝ) < (N : ℝ) := by linarith
  set L : ℝ := Real.log N with hLdef
  set T : ℝ := Real.log L with hTdef
  have hL3 : (3 : ℝ) ≤ L := by nlinarith [sq_nonneg (2 * K + 1)]
  have hLpos : (0 : ℝ) < L := by linarith
  have hT1 : (1 : ℝ) ≤ T := by
    rw [hTdef]
    calc (1 : ℝ) = Real.log (Real.exp 1) := (Real.log_exp 1).symm
      _ ≤ Real.log L := Real.log_le_log (Real.exp_pos 1) (by linarith [Real.exp_one_lt_d9])
  have hTpos : (0 : ℝ) < T := by linarith
  set M : ℕ := ⌈K * L * T⌉₊ with hMdef
  have hMge : K * L * T ≤ (M : ℝ) := Nat.le_ceil _
  have hMle : (M : ℝ) ≤ K * L * T + 1 := by
    rw [hMdef]; exact (Nat.ceil_lt_add_one (by positivity)).le
  have hn₀le : ((n₀ : ℕ) : ℝ) + 3 ≤ (M : ℝ) := le_trans hM hMge
  have hMn₀ : n₀ ≤ M := by
    have : ((n₀ : ℕ) : ℝ) ≤ (M : ℝ) := by linarith
    exact_mod_cast this
  have hM3 : (3 : ℝ) ≤ (M : ℝ) := by
    have : (0 : ℝ) ≤ ((n₀ : ℕ) : ℝ) := Nat.cast_nonneg _
    linarith
  have hMpos : (0 : ℝ) < (M : ℝ) := by linarith
  -- `M ≤ L²`, hence `log M ≤ 2 log log N`
  have hsqpos : (0 : ℝ) < Real.sqrt L := Real.sqrt_pos.2 hLpos
  have hsq : Real.sqrt L * Real.sqrt L = L := Real.mul_self_sqrt hLpos.le
  have hs1 : 2 * K + 1 ≤ Real.sqrt L := by
    have h1 : Real.sqrt ((2 * K + 1) ^ 2) ≤ Real.sqrt L := Real.sqrt_le_sqrt (by linarith)
    rwa [Real.sqrt_sq (by positivity)] at h1
  have hTle : T ≤ 2 * Real.sqrt L - 2 := by
    have h1 : Real.log (Real.sqrt L) ≤ Real.sqrt L - 1 := Real.log_le_sub_one_of_pos hsqpos
    have h2 : Real.log (Real.sqrt L) = Real.log L / 2 := Real.log_sqrt hLpos.le
    rw [hTdef]
    linarith
  have hMsq : (M : ℝ) ≤ L ^ 2 := by
    have hs0 : (1 : ℝ) ≤ Real.sqrt L := by linarith
    set s : ℝ := Real.sqrt L with hsdef
    have hL' : L = s * s := hsq.symm
    have h1 : K * L * T ≤ K * L * (2 * s - 2) :=
      mul_le_mul_of_nonneg_left hTle (mul_pos hK0 hLpos).le
    have h2 : K * L * (2 * s - 2) = 2 * K * s * s * s - 2 * K * (s * s) := by rw [hL']; ring
    have h3 : L ^ 2 = s * s * s * s := by rw [hL']; ring
    have hs3 : (1 : ℝ) ≤ s * s * s := by nlinarith
    have h4 : 2 * K * s * s * s + 1 ≤ s * s * s * s := by
      nlinarith [mul_le_mul_of_nonneg_right hs1 (show (0 : ℝ) ≤ s * s * s by positivity)]
    nlinarith [hMle, h1, h2, h3, h4, mul_pos hK0 (mul_pos hsqpos hsqpos)]
  have hlogM : Real.log (M : ℝ) ≤ 2 * T := by
    have h1 : Real.log (M : ℝ) ≤ Real.log (L ^ 2) := Real.log_le_log hMpos hMsq
    rw [Real.log_pow] at h1
    rw [hTdef]
    push_cast at h1
    linarith
  have hlogMpos : (0 : ℝ) < Real.log (M : ℝ) := Real.log_pos (by linarith)
  -- the master estimate at index `M`
  have hlogm : c' * M / Real.log M ≤ Real.log (m M) := hn₀ M hMn₀
  have hchain : 2 * L ≤ c' * M / Real.log M := by
    rw [le_div_iff₀ hlogMpos]
    calc 2 * L * Real.log (M : ℝ) ≤ 2 * L * (2 * T) := by nlinarith
      _ = 4 * (L * T) := by ring
      _ = c' * (K * L * T) := by rw [hK]; field_simp
      _ ≤ c' * M := by nlinarith
  have hlogN : L < Real.log (m M) := by linarith
  have hmMpos : (0 : ℝ) < (m M : ℝ) := by
    rcases eq_or_lt_of_le (Nat.cast_nonneg (α := ℝ) (m M)) with heq | hlt
    · rw [← heq, Real.log_zero] at hlogN; linarith
    · exact hlt
  have hNM : (N : ℝ) < (m M : ℝ) := by
    rw [← Real.exp_log hNpos, ← Real.exp_log hmMpos]
    exact Real.exp_lt_exp.2 hlogN
  have hNM' : N < m M := by exact_mod_cast hNM
  have hcount : (countingFn m N : ℝ) ≤ (M : ℝ) := by
    have := countingFn_le hm hNM'
    exact_mod_cast this
  calc (countingFn m N : ℝ) ≤ (M : ℝ) := hcount
    _ ≤ K * L * T + 1 := hMle
    _ ≤ (K + 1) * L * T := by nlinarith

/-! ## The package -/

/-- **Proposition C.**  R3 ⟹ R1 ∧ R2: an R3-regular sequence grows at least like
`exp((c/4)·n/log n)`, hence beats `exp(nᵅ)` for every `α < 1`, hence has counting function
`O(log N · log log N)`.  Together with Theorem A (`BB6/Vacuity.lean`), which makes R1 and R2
vacuous, this is the ordering that leaves R3 as the only reading of Problem 10.6 with content. -/
@[category research solved, AMS 11, ref "Bug12", group "bugeaud_10_6",
  formal_uses log_lower_of_r3 hasIntermediateGrowth_of_r3 countingFn_of_r3]
theorem proposition_C {m : ℕ → ℕ} (hm : StrictMono m)
    (h : Bugeaud06.IsGenuinelySublacunary m) :
    (∃ c' > 0, ∀ᶠ n : ℕ in atTop, c' * n / Real.log n ≤ Real.log (m n)) ∧
    (∀ α : ℝ, 0 < α → α < 1 → Bugeaud06.HasIntermediateGrowth α m) ∧
    (∃ C > 0, ∀ᶠ N : ℕ in atTop,
      (countingFn m N : ℝ) ≤ C * Real.log N * Real.log (Real.log N)) :=
  ⟨log_lower_of_r3 h, fun _ hα0 hα1 => hasIntermediateGrowth_of_r3 h hα0 hα1,
    countingFn_of_r3 hm h⟩

end BB6
