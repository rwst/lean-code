/-
(C) 2026 Ralf Stephan, in collaboration with Claude Code.
Released under CC0 1.0 Universal (public-domain dedication).
See https://creativecommons.org/publicdomain/zero/1.0/
-/
import TH.ComplexityLower

/-!
# Complexity as a packing count: where `p_T` sits between `k` and `3^k`

Placement companion to `TH.ComplexityLower` ([M4A3] §3.3).  T0.1 and the M4
capstone bound `p_T(k)` from **below** by `(41/24)·k − 3` and by `ω(k)`.  This
file records what those bounds are bounds *towards*, by turning the contraction
lemma of `TH.RepetitionIdentity` around.

The contraction `abs_eps_sub_le_of_repetition` says equal length-`k` factors force
`|ε_c − ε_a| ≤ (2/3)^k`.  Contrapositively, orbit points that are **pairwise more
than `(2/3)^k` apart carry pairwise distinct factors**, so

  `p_T(k) ≥ N((2/3)^k)`,  the packing number of `{ε_n}` at scale `(2/3)^k`

(`card_le_complexity_of_separated`).  Hence `p_T` is a proxy for the spread of the
orbit `((3/2)^n mod 1)`, and the long-standing density question sits directly
above the M4 theorem:

* **if `((3/2)^n)` is dense mod 1 then `p_T(k) ≥ ⌈(3/2)^k⌉ − 1`**
  (`complexity_ge_ceil_of_orbitDense`) — exponential, so the M4 theorem
  `p_T(k)/k → ∞` is the weakest nontrivial instance of what density predicts;
* contrapositively, **any subexponential upper bound `p_T(k) = o((3/2)^k)` would
  refute density** — which is why no upper bound of that strength is on offer
  here.

The implication runs one way only.  `p_T(k) ≥ N((2/3)^k)` lower-bounds the
complexity by the packing number, not conversely: the letter `t_n` is a function
of `(ε_n, m_n mod 2)` but `m_{n+1} mod 2` needs `m_n mod 4`, so a length-`k`
window is governed by `(ε_a, m_a mod 2^k)` and distinct factors need *not* come
from separated `ε`.  No converse to the contraction is claimed, and the M4
theorem therefore transfers nothing back to density.

For the ceiling, `complexity_le_five_pow` records the trivial alphabet bound
`p_T(k) ≤ 5^k`; the sharp known environment is Kopra's trace subshift
`P(k) = 4·3^k − 3·2^k` ([Kop21] Thm 3.15/Ex. 3.16), of base `3` rather than
`3/2` — consistent with the `m_a mod 2^k` obstruction above.

## Contents

* `complexity_le_five_pow` — the trivial ceiling `p_T(k) ≤ 5^k`.
* `card_le_complexity_of_separated` — **packing ≤ complexity**: a `(2/3)^k`-separated
  set of positions injects into the length-`k` factors.
* `TH.OrbitDense` — density of `((3/2)^n)` mod 1, in the centered coordinate `ε`.
* `complexity_ge_of_orbitDense`, `complexity_ge_ceil_of_orbitDense` — **the rung**:
  density forces `p_T(k) ≥ ⌈(3/2)^k⌉ − 1`.

## References

* [M4A3] `plan-M4A3.html` (this repository, 2026-07): §3.3 (T0.1), §2 (targets).
* [Kop21] Kopra. *On the trace subshifts of fractional multiplication automata.*
  Theoret. Comput. Sci. **851** (2021), 92–110. (Thm 3.15/Ex. 3.16: the
  enveloping trace subshift, `P(k) = 4·3^k − 3·2^k`.)
* [FLP95] Flatto, Lagarias, Pollington. *On the range of fractional parts
  `{ξ(p/q)ⁿ}`.* Acta Arith. **70** (1995), 125–147. (The complementary
  unconditional fact: the limit set has diameter `≥ 1/p`.)
-/

namespace TH

/-! ## The trivial ceiling -/

/-- The five-letter alphabet bounds the complexity: `p_T(k) ≤ 5^k`.  (The sharp
known environment is Kopra's `4·3^k − 3·2^k`, [Kop21] Thm 3.15.) -/
@[category research solved, AMS 11 68, ref "M4A3", group "three_halves_m4"]
theorem complexity_le_five_pow (k : ℕ) : complexity k ≤ 5 ^ k := by
  have hsub : (factorSet_finite k).toFinset ⊆
      Fintype.piFinset fun _ : Fin k => Finset.Icc (-2 : ℤ) 2 := by
    intro w hw
    rw [Set.Finite.mem_toFinset] at hw
    obtain ⟨a, rfl⟩ := hw
    simp only [Fintype.mem_piFinset, Finset.mem_Icc]
    exact fun i => abs_le.mp (t_abs_le _)
  have hcard := Finset.card_le_card hsub
  rw [Fintype.card_piFinset] at hcard
  have hIcc : (Finset.Icc (-2 : ℤ) 2).card = 5 := by decide
  simp only [hIcc, Finset.prod_const, Finset.card_univ, Fintype.card_fin] at hcard
  have hncard : complexity k = (factorSet_finite k).toFinset.card :=
    Set.ncard_eq_toFinset_card _ (factorSet_finite k)
  omega

/-! ## Packing ≤ complexity -/

/-- **Packing bound** (contrapositive of the contraction
`abs_eps_sub_le_of_repetition`): positions whose orbit points are pairwise more
than `(2/3)^k` apart carry pairwise distinct length-`k` factors, so the packing
number of `{ε_n}` at scale `(2/3)^k` is a lower bound for `p_T(k)`. -/
@[category research solved, AMS 11 68, ref "M4A3", group "three_halves_m4"]
theorem card_le_complexity_of_separated {k : ℕ} (S : Finset ℕ)
    (hsep : ∀ a ∈ S, ∀ c ∈ S, a ≠ c → (2 / 3 : ℚ) ^ k < |eps c - eps a|) :
    S.card ≤ complexity k := by
  have hinj : Set.InjOn (fun a => factor a k) ↑S := by
    intro x hx y hy hxy
    by_contra hne
    have h1 := abs_eps_sub_le_of_repetition (factor_eq_iff.mp hxy)
    have h2 := hsep x hx y hy hne
    linarith
  have himg : (S.image fun a => factor a k).card = S.card :=
    Finset.card_image_of_injOn hinj
  have hsub : (S.image fun a => factor a k) ⊆ (factorSet_finite k).toFinset := by
    intro w hw
    rw [Set.Finite.mem_toFinset]
    obtain ⟨x, _, rfl⟩ := Finset.mem_image.mp hw
    exact ⟨x, rfl⟩
  have hcard := Finset.card_le_card hsub
  have hncard : complexity k = (factorSet_finite k).toFinset.card :=
    Set.ncard_eq_toFinset_card _ (factorSet_finite k)
  omega

/-! ## The rung: density mod 1 forces exponential complexity -/

/-- Density of `((3/2)^n)` modulo one, in the centered coordinate: every point of
the window `[-1/2, 1/2)` is approximated by some `ε_n`.  Stated with rational
targets and rational tolerances, so it is *implied by* (hence weaker than) density
in the reals — which makes the theorems below correspondingly stronger. -/
@[category API, AMS 11 68, ref "M4A3", group "three_halves_m4"]
def OrbitDense : Prop :=
  ∀ x : ℚ, -(1 / 2 : ℚ) ≤ x → x < 1 / 2 → ∀ δ : ℚ, 0 < δ → ∃ n : ℕ, |eps n - x| < δ

/-- Distinct naturals are at rational distance at least `1`. -/
private lemma one_le_abs_sub_of_ne {i j : ℕ} (hij : i ≠ j) : (1 : ℚ) ≤ |(j : ℚ) - i| := by
  rcases Nat.lt_or_ge i j with hlt | hge
  · have h1 : (i : ℚ) + 1 ≤ (j : ℚ) := by exact_mod_cast Nat.succ_le_of_lt hlt
    rw [abs_of_nonneg (by linarith)]
    linarith
  · have hji : j < i := by omega
    have h1 : (j : ℚ) + 1 ≤ (i : ℚ) := by exact_mod_cast Nat.succ_le_of_lt hji
    rw [abs_of_nonpos (by linarith)]
    linarith

/-- **The rung** ([M4A3] placement): if `((3/2)^n)` is dense mod 1, then every
`M` strictly below `(3/2)^k` is a lower bound for `p_T(k)`.  Density spreads the
orbit over `≈ (3/2)^k` cells of width `(2/3)^k`, and the contraction turns each
cell into a distinct factor. -/
@[category research solved, AMS 11 68, ref "M4A3", group "three_halves_m4"]
theorem complexity_ge_of_orbitDense (h : OrbitDense) {k M : ℕ}
    (hM : (M : ℚ) < (3 / 2 : ℚ) ^ k) : M ≤ complexity k := by
  rcases Nat.eq_zero_or_pos M with rfl | hMpos
  · exact Nat.zero_le _
  have hMQ : (0 : ℚ) < M := by exact_mod_cast hMpos
  have h23 : (0 : ℚ) < (2 / 3 : ℚ) ^ k := by positivity
  have hmulone : ((3 : ℚ) / 2) ^ k * (2 / 3 : ℚ) ^ k = 1 := by
    rw [← mul_pow]; norm_num
  -- the cell width `(2/3)^k` is below the spacing `1/M`
  have hkey : (2 / 3 : ℚ) ^ k < 1 / M := by
    rw [lt_div_iff₀ hMQ]
    have := mul_lt_mul_of_pos_right hM h23
    rw [hmulone] at this
    linarith
  set δ : ℚ := (1 / M - (2 / 3 : ℚ) ^ k) / 3 with hδdef
  have hδpos : 0 < δ := by rw [hδdef]; linarith
  -- pick an orbit point near each of the `M` equally spaced targets
  have hpts : ∀ j : ℕ, ∃ n : ℕ,
      j < M → |eps n - (-(1 / 2 : ℚ) + (j : ℚ) / M)| < δ := by
    intro j
    by_cases hj : j < M
    · have hlo : -(1 / 2 : ℚ) ≤ -(1 / 2 : ℚ) + (j : ℚ) / M := by
        have : (0 : ℚ) ≤ (j : ℚ) / M := by positivity
        linarith
      have hhi : -(1 / 2 : ℚ) + (j : ℚ) / M < 1 / 2 := by
        have : (j : ℚ) / M < 1 := by
          rw [div_lt_one hMQ]; exact_mod_cast hj
        linarith
      obtain ⟨n, hn⟩ := h _ hlo hhi δ hδpos
      exact ⟨n, fun _ => hn⟩
    · exact ⟨0, fun hc => absurd hc hj⟩
  choose f hf using hpts
  -- the chosen points are `(2/3)^k`-separated
  have hsep : ∀ i, i < M → ∀ j, j < M → i ≠ j →
      (2 / 3 : ℚ) ^ k < |eps (f j) - eps (f i)| := by
    intro i hi j hj hij
    have hfi := hf i hi
    have hfj := hf j hj
    have hxx : |(-(1 / 2 : ℚ) + (j : ℚ) / M) - (-(1 / 2 : ℚ) + (i : ℚ) / M)|
        = |(j : ℚ) - i| / M := by
      rw [show (-(1 / 2 : ℚ) + (j : ℚ) / M) - (-(1 / 2 : ℚ) + (i : ℚ) / M)
            = ((j : ℚ) - i) / M by ring, abs_div, abs_of_pos hMQ]
    have hge : (1 : ℚ) / M ≤ |(j : ℚ) - i| / M := by
      gcongr
      exact one_le_abs_sub_of_ne hij
    set xi : ℚ := -(1 / 2 : ℚ) + (i : ℚ) / M with hxi
    set xj : ℚ := -(1 / 2 : ℚ) + (j : ℚ) / M with hxj
    have htri : |xj - xi| ≤ |xj - eps (f j)| + |eps (f j) - eps (f i)| + |eps (f i) - xi| :=
      le_trans (abs_sub_le xj (eps (f j)) xi)
        (by linarith [abs_sub_le (eps (f j)) (eps (f i)) xi])
    rw [abs_sub_comm xj (eps (f j))] at htri
    rw [hxx] at htri
    have hlow : (1 : ℚ) / M ≤ |eps (f j) - eps (f i)| + δ + δ := by
      linarith [hfi.le, hfj.le]
    rw [hδdef] at hlow
    linarith
  -- assemble the separated family
  have hfinj : Set.InjOn f ↑(Finset.range M) := by
    intro x hx y hy hxy
    simp only [Finset.coe_range, Set.mem_Iio] at hx hy
    by_contra hne
    have hthis := hsep x hx y hy hne
    rw [hxy, sub_self, abs_zero] at hthis
    exact absurd hthis (not_lt.mpr h23.le)
  refine le_trans (le_of_eq ?_)
    (card_le_complexity_of_separated ((Finset.range M).image f) ?_)
  · rw [Finset.card_image_of_injOn hfinj, Finset.card_range]
  · intro a ha c hc hac
    obtain ⟨i, hi, rfl⟩ := Finset.mem_image.mp ha
    obtain ⟨j, hj, rfl⟩ := Finset.mem_image.mp hc
    exact hsep i (Finset.mem_range.mp hi) j (Finset.mem_range.mp hj)
      (fun hij => hac (by rw [hij]))

/-- **The rung, headline form**: density of `((3/2)^n)` mod 1 forces exponential
complexity, `p_T(k) ≥ ⌈(3/2)^k⌉ − 1`.  Contrapositively, any proof of
`p_T(k) = o((3/2)^k)` would refute density. -/
@[category research solved, AMS 11 68, ref "M4A3", group "three_halves_m4"]
theorem complexity_ge_ceil_of_orbitDense (h : OrbitDense) (k : ℕ) :
    ⌈(3 / 2 : ℚ) ^ k⌉₊ - 1 ≤ complexity k := by
  have hpos : (0 : ℚ) < (3 / 2 : ℚ) ^ k := by positivity
  have hceil : 0 < ⌈(3 / 2 : ℚ) ^ k⌉₊ := Nat.ceil_pos.mpr hpos
  refine complexity_ge_of_orbitDense h ?_
  exact Nat.lt_ceil.mp (by omega)

end TH
