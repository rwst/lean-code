import B3.PrefixApproximants
import Corpus.Util.Attributes.Basic
import Corpus.Util.Attributes.Database

namespace B3

open BL AB Function Filter

@[category research solved, AMS 11 37, ref "BL96", group "b3_missing_lemma"]
theorem binaryDigit_prefixBlockVal_lt_eq_of_dvd {v : ℤ_[2]} {A t c p : ℕ} {e : ℕ → ℕ}
    (hAv : (2 : ℤ_[2]) ^ t ∣ v - (A : ℤ_[2])) {k : ℕ} (hk : k < t) :
    binaryDigit v k = binaryDigit (prefixBlockVal A t c p e) k := by
  rw [binaryDigit_prefixBlockVal_lt hk]
  exact binaryDigit_agree_of_dvd_two_pow t v ((A : ℕ) : ℤ_[2]) hAv k hk

@[category research solved, AMS 11 37, ref "BL96" "AB07", group "b3_missing_lemma"]
theorem binaryDigit_prefixBlockVal_eq_of_periodic {v : ℤ_[2]} {A t c p : ℕ} {e : ℕ → ℕ}
    (hp : 0 < p) (he_lt : ∀ r, r < c → e r < p)
    (he_mono : ∀ r r', r < r' → r' < c → e r < e r') (hA : A < 2 ^ t) {N : ℕ}
    (hprefix : ∀ k, k < t + p → binaryDigit v k = binaryDigit (prefixBlockVal A t c p e) k)
    (hper : ∀ i, t + p ≤ i → i < N → binaryDigit v i = binaryDigit v (i - p)) :
    ∀ k, k < N → binaryDigit v k = binaryDigit (prefixBlockVal A t c p e) k := by
  intro k
  induction k using Nat.strong_induction_on with
  | _ k ih =>
    intro hkN
    rcases lt_or_ge k (t + p) with hk | hk
    · exact hprefix k hk
    · have hper_k : binaryDigit v k = binaryDigit v (k - p) := hper k hk hkN
      have hα : binaryDigit (prefixBlockVal A t c p e) k
          = binaryDigit (prefixBlockVal A t c p e) (k - p) := by
        rw [binaryDigit_prefixBlockVal_ge hA (by omega : t ≤ k),
            binaryDigit_prefixBlockVal_ge hA (by omega : t ≤ k - p),
            show k - t = ((k - p) - t) + p from by omega]
        exact binaryDigit_blockVal_add_period hp he_lt he_mono _
      have hih : binaryDigit v (k - p) = binaryDigit (prefixBlockVal A t c p e) (k - p) :=
        ih (k - p) (by omega) (by omega)
      rw [hper_k, hih, hα]

@[category API, AMS 11 37, ref "BL96"]
theorem binaryDigit_S_iterate (v : ℤ_[2]) (t j : ℕ) :
    binaryDigit (S^[t] v) j = binaryDigit v (t + j) := by
  unfold binaryDigit
  rw [← Function.iterate_add_apply S j t v, Nat.add_comm j t]

@[category research solved, AMS 11 37, ref "BL96", group "b3_missing_lemma"]
theorem binaryDigit_prefixBlockVal_block_eq_of_dvd {v : ℤ_[2]} {A t c p : ℕ} {e : ℕ → ℕ}
    (hp : 0 < p) (he_lt : ∀ r, r < c → e r < p)
    (he_mono : ∀ r r', r < r' → r' < c → e r < e r') (hA : A < 2 ^ t)
    (hBv : (2 : ℤ_[2]) ^ p ∣ S^[t] v - ((blockFirst c e : ℕ) : ℤ_[2])) {k : ℕ}
    (hk1 : t ≤ k) (hk2 : k < t + p) :
    binaryDigit v k = binaryDigit (prefixBlockVal A t c p e) k := by
  rw [binaryDigit_prefixBlockVal_ge hA hk1, binaryDigit_blockVal_eq_first hp he_lt he_mono,
      Nat.mod_eq_of_lt (by omega : k - t < p)]
  conv_lhs => rw [show k = t + (k - t) from by omega, ← binaryDigit_S_iterate v t (k - t)]
  exact binaryDigit_agree_of_dvd_two_pow p (S^[t] v) ((blockFirst c e : ℕ) : ℤ_[2]) hBv (k - t)
    (by omega)

@[category research solved, AMS 11 37, ref "BL96", group "b3_missing_lemma"]
theorem prefixAgreement_of_dvd {v : ℤ_[2]} {A t c p : ℕ} {e : ℕ → ℕ}
    (hp : 0 < p) (he_lt : ∀ r, r < c → e r < p)
    (he_mono : ∀ r r', r < r' → r' < c → e r < e r') (hA : A < 2 ^ t)
    (hAv : (2 : ℤ_[2]) ^ t ∣ v - ((A : ℕ) : ℤ_[2]))
    (hBv : (2 : ℤ_[2]) ^ p ∣ S^[t] v - ((blockFirst c e : ℕ) : ℤ_[2])) :
    ∀ k, k < t + p → binaryDigit v k = binaryDigit (prefixBlockVal A t c p e) k := by
  intro k hk
  rcases lt_or_ge k t with hkt | hkt
  · exact binaryDigit_prefixBlockVal_lt_eq_of_dvd hAv hkt
  · exact binaryDigit_prefixBlockVal_block_eq_of_dvd hp he_lt he_mono hA hBv hkt hk

@[category research solved, AMS 11 37, ref "BL96" "AB07", group "b3_missing_lemma"]
theorem binaryDigit_window_agreement {v : ℤ_[2]} {A t c p : ℕ} {e : ℕ → ℕ}
    (hp : 0 < p) (he_lt : ∀ r, r < c → e r < p)
    (he_mono : ∀ r r', r < r' → r' < c → e r < e r') (hA : A < 2 ^ t)
    (hAv : (2 : ℤ_[2]) ^ t ∣ v - ((A : ℕ) : ℤ_[2]))
    (hBv : (2 : ℤ_[2]) ^ p ∣ S^[t] v - ((blockFirst c e : ℕ) : ℤ_[2])) {N : ℕ}
    (hper : ∀ i, t + p ≤ i → i < N → binaryDigit v i = binaryDigit v (i - p)) :
    ∀ k, k < N → binaryDigit v k = binaryDigit (prefixBlockVal A t c p e) k :=
  binaryDigit_prefixBlockVal_eq_of_periodic hp he_lt he_mono hA
    (prefixAgreement_of_dvd hp he_lt he_mono hA hAv hBv) hper

end B3
