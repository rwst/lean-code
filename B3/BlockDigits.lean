import B3.StammeringWiring
import Corpus.Util.Attributes.Basic
import Corpus.Util.Attributes.Database

namespace B3

open BL AB Function Filter

@[category API, AMS 11 37, ref "BL96"]
theorem S_natCast_add_two_mul (b : ℕ) (hb : b < 2) (y : ℤ_[2]) :
    S ((b : ℤ_[2]) + 2 * y) = y := by
  have h2zero : PadicInt.toZMod (2 : ℤ_[2]) = 0 := by
    have hc2 : ((2 : ℕ) : ℤ_[2]) = (2 : ℤ_[2]) := by norm_cast
    rw [← hc2, map_natCast]
    exact ZMod.natCast_self 2
  have hpar : parity ((b : ℤ_[2]) + 2 * y) = b := by
    unfold parity
    rw [map_add, map_mul, h2zero, zero_mul, add_zero, map_natCast]
    exact ZMod.val_natCast_of_lt hb
  have h2S : 2 * S ((b : ℤ_[2]) + 2 * y) = 2 * y := by rw [two_mul_S, hpar]; ring
  exact mul_left_cancel₀ two_ne_zero h2S

@[category API, AMS 11 37, ref "BL96"]
theorem S_iterate_natCast_add : ∀ (p n : ℕ) (x : ℤ_[2]), n < 2 ^ p →
    S^[p] ((n : ℤ_[2]) + 2 ^ p * x) = x
  | 0, n, x, hn => by
    simp only [pow_zero] at hn ⊢
    obtain rfl : n = 0 := by omega
    simp
  | p + 1, n, x, hn => by
    have hn_split : ((n % 2 : ℕ) : ℤ_[2]) + 2 * ((n / 2 : ℕ) : ℤ_[2]) = (n : ℤ_[2]) := by
      have hmod : n % 2 + 2 * (n / 2) = n := by omega
      calc ((n % 2 : ℕ) : ℤ_[2]) + 2 * ((n / 2 : ℕ) : ℤ_[2])
          = ((n % 2 + 2 * (n / 2) : ℕ) : ℤ_[2]) := by push_cast; ring
        _ = (n : ℤ_[2]) := by rw [hmod]
    have hsplit : (n : ℤ_[2]) + 2 ^ (p + 1) * x
        = ((n % 2 : ℕ) : ℤ_[2]) + 2 * (((n / 2 : ℕ) : ℤ_[2]) + 2 ^ p * x) := by
      rw [← hn_split, pow_succ']; ring
    have hpeel : S ((n : ℤ_[2]) + 2 ^ (p + 1) * x) = ((n / 2 : ℕ) : ℤ_[2]) + 2 ^ p * x := by
      rw [hsplit, S_natCast_add_two_mul (n % 2) (by omega) _]
    have hlt : n / 2 < 2 ^ p := by
      have h2 : 2 ^ (p + 1) = 2 * 2 ^ p := by ring
      omega
    rw [Function.iterate_succ_apply, hpeel]
    exact S_iterate_natCast_add p (n / 2) x hlt

@[category API, AMS 11 37, ref "BL96"]
def blockFirst (c : ℕ) (e : ℕ → ℕ) : ℕ := ∑ r ∈ Finset.range c, 2 ^ e r

@[category API, AMS 11 37, ref "BL96"]
theorem sum_two_pow_range_lt : ∀ p : ℕ, ∑ j ∈ Finset.range p, 2 ^ j < 2 ^ p
  | 0 => by simp
  | p + 1 => by
    rw [Finset.sum_range_succ]
    have ih := sum_two_pow_range_lt p
    have h2 : 2 ^ (p + 1) = 2 ^ p + 2 ^ p := by ring
    omega

@[category API, AMS 11 37, ref "BL96"]
theorem blockFirst_lt_two_pow {c p : ℕ} {e : ℕ → ℕ}
    (he_lt : ∀ r, r < c → e r < p) (he_mono : ∀ r r', r < r' → r' < c → e r < e r') :
    blockFirst c e < 2 ^ p := by
  have hinj : Set.InjOn e (Finset.range c) := by
    intro a ha b hb hab
    rw [Finset.coe_range, Set.mem_Iio] at ha hb
    rcases lt_trichotomy a b with h | h | h
    · exact absurd hab (ne_of_lt (he_mono a b h hb))
    · exact h
    · exact absurd hab.symm (ne_of_lt (he_mono b a h ha))
  have hsub : Finset.image e (Finset.range c) ⊆ Finset.range p := by
    intro j hj
    rw [Finset.mem_image] at hj
    obtain ⟨i, hi, rfl⟩ := hj
    rw [Finset.mem_range] at hi ⊢
    exact he_lt i hi
  unfold blockFirst
  rw [← Finset.sum_image (f := fun j => 2 ^ j) hinj]
  calc ∑ j ∈ Finset.image e (Finset.range c), 2 ^ j
      ≤ ∑ j ∈ Finset.range p, 2 ^ j := Finset.sum_le_sum_of_subset hsub
    _ < 2 ^ p := sum_two_pow_range_lt p

@[category API, AMS 11 37, ref "BL96"]
theorem summable_two_pow_blockPos {c p : ℕ} {e : ℕ → ℕ} (hc : 0 < c)
    (he_lt : ∀ r, r < c → e r < p) (he_mono : ∀ r r', r < r' → r' < c → e r < e r') :
    Summable (fun i => (2 : ℤ_[2]) ^ blockPos c p e i) := by
  have hmono := blockPos_strictMono hc he_lt he_mono
  have h2lt1 : ‖(2 : ℤ_[2])‖ < 1 := by
    rw [PadicInt.norm_lt_one_iff_dvd]; exact_mod_cast dvd_refl (2 : ℤ_[2])
  apply Summable.of_norm_bounded (summable_geometric_of_lt_one (norm_nonneg _) h2lt1)
  intro i
  rw [norm_pow]
  exact pow_le_pow_of_le_one (norm_nonneg _) (le_of_lt h2lt1) hmono.le_apply

@[category research solved, AMS 11 37, ref "BL96", group "b3_missing_lemma"]
theorem blockVal_self_similar {c p : ℕ} {e : ℕ → ℕ} (_hp : 0 < p)
    (he_lt : ∀ r, r < c → e r < p) (he_mono : ∀ r r', r < r' → r' < c → e r < e r') :
    blockVal c p e = (blockFirst c e : ℤ_[2]) + 2 ^ p * blockVal c p e := by
  rcases Nat.eq_zero_or_pos c with rfl | hc
  · rw [blockVal_zero]; simp [blockFirst]
  have hsummable := summable_two_pow_blockPos hc he_lt he_mono
  have hreg : (∑ i ∈ Finset.range c, (2 : ℤ_[2]) ^ blockPos c p e i)
      + ∑' j, (2 : ℤ_[2]) ^ blockPos c p e (j + c) = ∑' i, (2 : ℤ_[2]) ^ blockPos c p e i :=
    hsummable.sum_add_tsum_nat_add c
  have htail : ∑' j, (2 : ℤ_[2]) ^ blockPos c p e (j + c) = 2 ^ p * blockVal c p e := by
    rw [blockVal_of_pos hc, ← Summable.tsum_mul_left _ hsummable]
    exact tsum_congr (fun j => by rw [blockPos_add_period hc]; ring)
  have hfirst : (∑ i ∈ Finset.range c, (2 : ℤ_[2]) ^ blockPos c p e i) = (blockFirst c e : ℤ_[2]) := by
    rw [blockFirst]
    push_cast
    apply Finset.sum_congr rfl
    intro i hi
    rw [Finset.mem_range] at hi
    rw [blockPos_eq_of_lt hi]
  conv_lhs => rw [blockVal_of_pos hc, ← hreg]
  rw [hfirst, htail]

@[category research solved, AMS 11 37, ref "BL96", group "b3_missing_lemma"]
theorem S_iterate_blockVal {c p : ℕ} {e : ℕ → ℕ} (hp : 0 < p)
    (he_lt : ∀ r, r < c → e r < p) (he_mono : ∀ r r', r < r' → r' < c → e r < e r') :
    S^[p] (blockVal c p e) = blockVal c p e := by
  conv_lhs => rw [blockVal_self_similar hp he_lt he_mono]
  exact S_iterate_natCast_add p (blockFirst c e) (blockVal c p e)
    (blockFirst_lt_two_pow he_lt he_mono)

@[category research solved, AMS 11 37, ref "BL96", group "b3_missing_lemma"]
theorem binaryDigit_blockVal_add_period {c p : ℕ} {e : ℕ → ℕ} (hp : 0 < p)
    (he_lt : ∀ r, r < c → e r < p) (he_mono : ∀ r r', r < r' → r' < c → e r < e r') (k : ℕ) :
    binaryDigit (blockVal c p e) (k + p) = binaryDigit (blockVal c p e) k := by
  unfold binaryDigit
  rw [Function.iterate_add_apply, S_iterate_blockVal hp he_lt he_mono]

@[category API, AMS 11 37, ref "BL96"]
theorem binaryDigit_agree_of_dvd_two_pow : ∀ (N : ℕ) (x y : ℤ_[2]),
    (2 : ℤ_[2]) ^ N ∣ x - y → ∀ k, k < N → binaryDigit x k = binaryDigit y k
  | 0, _, _, _ => fun k hk => absurd hk (Nat.not_lt_zero k)
  | N + 1, x, y, hdvd => by
    have h2 : (2 : ℤ_[2]) ∣ x - y := dvd_trans (dvd_pow_self 2 (Nat.succ_ne_zero N)) hdvd
    have hpar : parity x = parity y := by
      unfold parity
      have hz : PadicInt.toZMod (x - y) = 0 := (two_dvd_iff_toZMod_eq_zero _).mp h2
      rw [map_sub, sub_eq_zero] at hz
      rw [hz]
    have hxy : x - y = 2 * (S x - S y) := by
      have hx := parity_add_two_mul_S x
      have hy := parity_add_two_mul_S y
      have hpc : (parity x : ℤ_[2]) = (parity y : ℤ_[2]) := by rw [hpar]
      linear_combination hy - hx + hpc
    have hSdvd : (2 : ℤ_[2]) ^ N ∣ S x - S y := by
      have hd : (2 : ℤ_[2]) ^ (N + 1) ∣ 2 * (S x - S y) := hxy ▸ hdvd
      rw [pow_succ'] at hd
      exact (mul_dvd_mul_iff_left (two_ne_zero (α := ℤ_[2]))).mp hd
    intro k hk
    rcases Nat.eq_zero_or_pos k with rfl | hk0
    · rw [binaryDigit_zero, binaryDigit_zero, hpar]
    · obtain ⟨k', rfl⟩ := Nat.exists_eq_succ_of_ne_zero hk0.ne'
      rw [binaryDigit_succ, binaryDigit_succ]
      exact binaryDigit_agree_of_dvd_two_pow N (S x) (S y) hSdvd k' (by omega)

@[category research solved, AMS 11 37, ref "BL96", group "b3_missing_lemma"]
theorem binaryDigit_blockVal_lt {c p : ℕ} {e : ℕ → ℕ} (hp : 0 < p)
    (he_lt : ∀ r, r < c → e r < p) (he_mono : ∀ r r', r < r' → r' < c → e r < e r') {k : ℕ}
    (hk : k < p) :
    binaryDigit (blockVal c p e) k = binaryDigit ((blockFirst c e : ℕ) : ℤ_[2]) k := by
  have hdvd : (2 : ℤ_[2]) ^ p ∣ blockVal c p e - (blockFirst c e : ℤ_[2]) := by
    have hsub : blockVal c p e - (blockFirst c e : ℤ_[2]) = 2 ^ p * blockVal c p e := by
      linear_combination blockVal_self_similar hp he_lt he_mono
    rw [hsub]
    exact dvd_mul_right _ _
  exact binaryDigit_agree_of_dvd_two_pow p _ _ hdvd k hk

@[category API, AMS 11 37, ref "BL96"]
theorem binaryDigit_blockVal_add_mul_period {c p : ℕ} {e : ℕ → ℕ} (hp : 0 < p)
    (he_lt : ∀ r, r < c → e r < p) (he_mono : ∀ r r', r < r' → r' < c → e r < e r') (k j : ℕ) :
    binaryDigit (blockVal c p e) (k + p * j) = binaryDigit (blockVal c p e) k := by
  induction j with
  | zero => simp
  | succ j ih =>
    have hkj : k + p * (j + 1) = (k + p * j) + p := by ring
    rw [hkj, binaryDigit_blockVal_add_period hp he_lt he_mono, ih]

@[category research solved, AMS 11 37, ref "BL96", group "b3_missing_lemma"]
theorem binaryDigit_blockVal_eq_first {c p : ℕ} {e : ℕ → ℕ} (hp : 0 < p)
    (he_lt : ∀ r, r < c → e r < p) (he_mono : ∀ r r', r < r' → r' < c → e r < e r') (k : ℕ) :
    binaryDigit (blockVal c p e) k = binaryDigit ((blockFirst c e : ℕ) : ℤ_[2]) (k % p) := by
  conv_lhs => rw [← Nat.mod_add_div k p]
  rw [binaryDigit_blockVal_add_mul_period hp he_lt he_mono (k % p) (k / p)]
  exact binaryDigit_blockVal_lt hp he_lt he_mono (Nat.mod_lt k hp)

end B3
