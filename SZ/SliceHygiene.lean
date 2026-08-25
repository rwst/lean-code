/-
(C) 2026 Ralf Stephan, in collaboration with Claude Code.
Released under CC0 1.0 Universal (public-domain dedication).
See https://creativecommons.org/publicdomain/zero/1.0/
-/
import SZ.Slice
import Mathlib.Tactic.Push

/-!
# Tail hygiene in the uniform case

Proposition 5.4 of `paper-dubD1O5.tex`: when the largest digit of the alphabet is
`e = m - 1` — that is, when `p ∣ m - 1` — and `√m ≥ p`, the digits produced by the greedy
of `SZ/Slice.lean` are not eventually stuck at an endpoint.  Concretely

`aᵢ ≤ e - p` infinitely often   and   `bᵢ ≥ p` infinitely often,

which is exactly the canonicity \eqref{eq:L1} the reduction needs.  When `e ≤ m - 2` the
condition is free (`Slice.dvd_floor_of_e_le`); this file is what the odd cells `m = 5` and
`m = 7` of Theorem B and the whole of branch (i) of Theorem C require.

## The argument

Here `M = 1` and `U = 1 + √m`, so the state lives in `ℤ[√m]` and its `√m`-coordinate can
be tracked exactly (`stt`).  Three ingredients:

* **growth** (`stt_snd_lower`) — `Q k ≥ p m^{k+1} + m`, by a one-line induction with the
  invariant chosen so that the geometric series never appears.  Hence `Q k > m`, so by
  freeness of `ℤ[√m]` the state is never `0` and never `mU = m + m√m`.  It is the
  *growth*, not mere irrationality, that excludes the second point.
* **expansion** (`eq_fixed_of_trapped`) — an `r`-expanding affine map, `r > 1`, cannot keep
  an orbit bounded unless the orbit sits at its fixed point.
* **the rule** — `b = 0` exactly on `L = [0, p√m)` (`Slice.bsel_eq_zero_iff`, the paper's
  (5.2)), and `a = e` forces `b = e` once `(p-1)(√m+1) ≤ e`.

The hypothesis `√m ≥ p` enters through exactly two consequences, the paper's (5.3):
`(p-1)(√m+1) ≤ e` (`form_a` below, in expanded form) and `m(U - p) ≥ p√m` (`form_b`).

The `a`-side then says: were `a` stuck at `e`, the offset would be the constant
`e(1+√m) = (m-1)U`, the orbit would sit at the fixed point `mU`, and growth forbids it.
The `b`-side says: were `b` stuck at `0`, the state would stay in `[0, p√m)`; one step from
above `U` lands beyond `m(U-p) ≥ p√m`, and from below `U` the state is merely multiplied
by `m` forever, which a positive state cannot survive.

## References

* [Dub06EO] A. Dubickas, *Even and odd integral parts of powers of a real number*,
  Glasgow Math. J. **48** (2006), 331–336.
-/

namespace SZ

namespace Slice

/-! ## An expanding map cannot confine an orbit -/

/-- If from step `K` on the orbit obeys one affine `r`-expanding map, `r > 1`, and stays
bounded, it sits at that map's fixed point `c/(r-1)`. -/
@[category research solved, AMS 11, ref "Dub06EO", group "dub06_slice"]
theorem eq_fixed_of_trapped {f : ℕ → ℝ} {r c D : ℝ} {K : ℕ} (hr : 1 < r)
    (hrec : ∀ k, K ≤ k → f (k + 1) = r * f k - c)
    (hbd : ∀ k, K ≤ k → |f k - c / (r - 1)| ≤ D) : f K = c / (r - 1) := by
  by_contra hne
  have hr1 : (0 : ℝ) < r - 1 := by linarith
  have hpos : 0 < |f K - c / (r - 1)| := abs_pos.mpr (sub_ne_zero.mpr hne)
  have hpow : ∀ n : ℕ, f (K + n) - c / (r - 1) = r ^ n * (f K - c / (r - 1)) := by
    intro n
    induction n with
    | zero => simp
    | succ n ih =>
      have hstep := hrec (K + n) (Nat.le_add_right _ _)
      have e : K + (n + 1) = (K + n) + 1 := by omega
      rw [e, hstep, pow_succ]
      have hc : r * (c / (r - 1)) - c = c / (r - 1) := by field_simp; ring
      nlinarith [ih]
  obtain ⟨n, hn⟩ := pow_unbounded_of_one_lt (D / |f K - c / (r - 1)|) hr
  have hb := hbd (K + n) (Nat.le_add_right _ _)
  rw [hpow n, abs_mul, abs_pow, abs_of_nonneg (by linarith : (0:ℝ) ≤ r)] at hb
  have hlt := (div_lt_iff₀ hpos).mp hn
  nlinarith [hpos]

/-! ## The uniform case `e = m - 1` -/

variable {S : Slice}

theorem M_eq_one (he : S.e = (S.m : ℤ) - 1) : S.M = 1 := by
  have h : ((S.m : ℝ) - 1) ≠ 0 := S.m_sub_one_ne
  have hcast : (S.e : ℝ) = (S.m : ℝ) - 1 := by rw [he]; push_cast; ring
  rw [M, hcast, div_self h]

theorem U_eq_one_add (he : S.e = (S.m : ℤ) - 1) : S.U = 1 + S.sq := by
  rw [S.U_eq, M_eq_one he, one_mul]

/-- The first form of `√m ≥ p`, the paper's (5.3): `(p-1)(√m+1) ≤ e`, expanded so that
`linarith` can use it. -/
theorem form_a (he : S.e = (S.m : ℤ) - 1) (hp : (S.p : ℝ) ≤ S.sq) :
    (S.p : ℝ) * S.sq + (S.p : ℝ) ≤ (S.e : ℝ) + S.sq + 1 := by
  have hecast : (S.e : ℝ) = (S.m : ℝ) - 1 := by rw [he]; push_cast; ring
  have hsq := S.sq_sq
  have hpos := S.sq_pos
  nlinarith [mul_nonneg (by linarith : (0:ℝ) ≤ S.sq - (S.p : ℝ))
    (by linarith : (0:ℝ) ≤ S.sq + 1)]

/-- The second form of `√m ≥ p`, the paper's (5.3): `m(U - p) ≥ p√m`. -/
theorem form_b (he : S.e = (S.m : ℤ) - 1) (hp : (S.p : ℝ) ≤ S.sq) :
    (S.p : ℝ) * S.sq ≤ (S.m : ℝ) * (S.U - (S.p : ℝ)) := by
  have hU := U_eq_one_add he
  have hsq := S.sq_sq
  have hpos := S.sq_pos
  rw [hU]
  nlinarith [mul_nonneg (mul_nonneg hpos.le (by linarith : (0:ℝ) ≤ S.sq + 1))
    (by linarith : (0:ℝ) ≤ S.sq - (S.p : ℝ))]

/-! ## The state in `ℤ[√m]` -/

/-- The greedy's state as a pair `(P, Q)` with value `P + Q√m`, in the uniform case. -/
noncomputable def stt (S : Slice) (j k₀ : ℤ) : ℕ → ℤ × ℤ
  | 0 => (-S.p * j * (S.m : ℤ), (S.p * k₀ + 1) * (S.m : ℤ))
  | k + 1 => ((S.m : ℤ) * ((stt S j k₀ k).1 - S.dA (S.w0 j k₀) k),
              (S.m : ℤ) * ((stt S j k₀ k).2 - S.dB (S.w0 j k₀) k))

theorem stt_zero (S : Slice) (j k₀ : ℤ) :
    stt S j k₀ 0 = (-S.p * j * (S.m : ℤ), (S.p * k₀ + 1) * (S.m : ℤ)) := rfl

theorem stt_succ (S : Slice) (j k₀ : ℤ) (k : ℕ) :
    stt S j k₀ (k + 1) = ((S.m : ℤ) * ((stt S j k₀ k).1 - S.dA (S.w0 j k₀) k),
      (S.m : ℤ) * ((stt S j k₀ k).2 - S.dB (S.w0 j k₀) k)) := rfl

/-- The state pair realises the state value. -/
@[category API, AMS 11, ref "Dub06EO", group "dub06_slice"]
theorem stt_val (he : S.e = (S.m : ℤ) - 1) (j k₀ : ℤ) (k : ℕ) :
    S.W (S.w0 j k₀) k = ((stt S j k₀ k).1 : ℝ) + ((stt S j k₀ k).2 : ℝ) * S.sq := by
  induction k with
  | zero =>
    rw [W_zero, stt_zero, w0_def, sigma, M_eq_one he]
    push_cast
    ring
  | succ k ih =>
    rw [W_succ, val_pick_W, ih, stt_succ]
    push_cast
    ring

/-- **Growth.**  The `√m`-coordinate of the state satisfies `Q k ≥ p m^{k+1} + m`; in
particular it always exceeds `m`. -/
@[category research solved, AMS 11, ref "Dub06EO", group "dub06_slice"]
theorem stt_snd_lower (he : S.e = (S.m : ℤ) - 1) {j k₀ : ℤ} (hk : 1 ≤ k₀)
    (h0 : 0 ≤ S.sigma j k₀) (h1 : S.sigma j k₀ ≤ S.U) (k : ℕ) :
    S.p * (S.m : ℤ) ^ (k + 1) + (S.m : ℤ) ≤ (stt S j k₀ k).2 := by
  have hmz : (3 : ℤ) ≤ (S.m : ℤ) := by exact_mod_cast S.three_le
  have hmr : (0 : ℝ) < (S.m : ℝ) := by have := S.three_le_cast; linarith
  have hw0 : 0 ≤ S.w0 j k₀ := mul_nonneg hmr.le h0
  have hw1 : S.w0 j k₀ ≤ (S.m : ℝ) * S.U := mul_le_mul_of_nonneg_left h1 hmr.le
  have hppos := S.p_pos
  induction k with
  | zero =>
    have hd : (0 : ℤ) ≤ (S.m : ℤ) * (S.p * (k₀ - 1)) :=
      mul_nonneg (by omega) (mul_nonneg hppos.le (by omega))
    rw [stt_zero]
    simp only [pow_succ, pow_zero, one_mul]
    nlinarith [hd]
  | succ k ih =>
    rw [stt_succ]
    show S.p * (S.m : ℤ) ^ (k + 1 + 1) + (S.m : ℤ)
      ≤ (S.m : ℤ) * ((stt S j k₀ k).2 - S.dB (S.w0 j k₀) k)
    have hb : S.dB (S.w0 j k₀) k ≤ S.e := (dB_mem hw0 hw1 k).2.2
    have hbe : S.dB (S.w0 j k₀) k ≤ (S.m : ℤ) - 1 := by rw [he] at hb; exact hb
    have hinner : S.p * (S.m : ℤ) ^ (k + 1) + 1
        ≤ (stt S j k₀ k).2 - S.dB (S.w0 j k₀) k := by linarith
    have hstep := mul_le_mul_of_nonneg_left hinner (by omega : (0 : ℤ) ≤ (S.m : ℤ))
    have hid : (S.m : ℤ) * (S.p * (S.m : ℤ) ^ (k + 1) + 1)
        = S.p * (S.m : ℤ) ^ (k + 1 + 1) + (S.m : ℤ) := by ring
    rw [hid] at hstep
    linarith

/-- The state is never a point of `ℤ[√m]` with small `√m`-coordinate — in particular never
`0` and never the trap fixed point `mU = m + m√m`. -/
@[category research solved, AMS 11, ref "Dub06EO", group "dub06_slice"]
theorem W_ne_val (he : S.e = (S.m : ℤ) - 1) {j k₀ : ℤ} (hk : 1 ≤ k₀)
    (h0 : 0 ≤ S.sigma j k₀) (h1 : S.sigma j k₀ ≤ S.U) (k : ℕ) {p q : ℤ}
    (hq : q ≤ (S.m : ℤ)) : S.W (S.w0 j k₀) k ≠ (p : ℝ) + (q : ℝ) * S.sq := by
  intro hcon
  rw [stt_val he] at hcon
  obtain ⟨-, h2⟩ := S.val_inj hcon
  have hlow := stt_snd_lower he hk h0 h1 k
  have hmz : (3 : ℤ) ≤ (S.m : ℤ) := by exact_mod_cast S.three_le
  have hpow : (S.m : ℤ) ≤ (S.m : ℤ) ^ (k + 1) := by
    calc (S.m : ℤ) = (S.m : ℤ) ^ 1 := (pow_one _).symm
      _ ≤ (S.m : ℤ) ^ (k + 1) := pow_le_pow_right₀ (by omega) (by omega)
  have hpm : (S.m : ℤ) ≤ S.p * (S.m : ℤ) ^ (k + 1) :=
    le_trans hpow (le_mul_of_one_le_left (by positivity) (by have := S.two_le_p; omega))
  rw [h2] at hlow
  linarith

/-! ## Lemma L1, the `a`-side -/

/-- **L1(a).**  The `a`-digits are not eventually stuck at the top digit `e`: were they,
the offset would be the constant `e(1+√m) = (m-1)U`, the orbit would sit at the fixed
point `mU = m + m√m`, and growth forbids that. -/
@[category research solved, AMS 11, ref "Dub06EO", group "dub06_slice"]
theorem exists_dA_ne (he : S.e = (S.m : ℤ) - 1) (hpsq : (S.p : ℝ) ≤ S.sq) {j k₀ : ℤ}
    (hk : 1 ≤ k₀) (h0 : 0 ≤ S.sigma j k₀) (h1 : S.sigma j k₀ ≤ S.U) (N : ℕ) :
    ∃ k, N ≤ k ∧ S.dA (S.w0 j k₀) k ≠ S.e := by
  by_contra hcon
  push Not at hcon
  have hmr : (0 : ℝ) < (S.m : ℝ) := by have := S.three_le_cast; linarith
  have hm1 : (1 : ℝ) < (S.m : ℝ) := by have := S.three_le_cast; linarith
  have hw0 : 0 ≤ S.w0 j k₀ := mul_nonneg hmr.le h0
  have hw1 : S.w0 j k₀ ≤ (S.m : ℝ) * S.U := mul_le_mul_of_nonneg_left h1 hmr.le
  have hU := U_eq_one_add he
  have hfa := form_a he hpsq
  have hecast : (S.e : ℝ) = (S.m : ℝ) - 1 := by rw [he]; push_cast; ring
  -- the `b`-digit is forced to `e` as well
  have hbe : ∀ k, N ≤ k → S.dB (S.w0 j k₀) k = S.e := by
    intro k hkN
    by_contra hb
    have hblt : S.bsel (S.W (S.w0 j k₀) k) < S.e :=
      lt_of_le_of_ne (S.bsel_le _) (by rw [dB_eq] at hb; exact hb)
    have hmax := S.lt_bsel_add hblt
    have hexp : ((S.bsel (S.W (S.w0 j k₀) k) : ℝ) + (S.p : ℝ)) * S.sq
        = (S.bsel (S.W (S.w0 j k₀) k) : ℝ) * S.sq + (S.p : ℝ) * S.sq := by ring
    rw [hexp] at hmax
    have hv : S.W (S.w0 j k₀) k - (S.bsel (S.W (S.w0 j k₀) k) : ℝ) * S.sq
        < (S.p : ℝ) * S.sq := by linarith
    have ha : (S.dA (S.w0 j k₀) k : ℝ) < (S.e : ℝ) := by
      rcases le_or_gt (S.W (S.w0 j k₀) k - (S.bsel (S.W (S.w0 j k₀) k) : ℝ) * S.sq) S.U with
        hle | hlt
      · rw [dA_eq, S.asel_eq_zero hle]
        have := S.e_pos
        exact_mod_cast this
      · have hal := S.asel_lt hlt
        rw [dA_eq]
        linarith
    rw [hcon k hkN] at ha
    exact lt_irrefl _ ha
  -- from `N` on the dynamics is one affine map
  have hrec : ∀ k, N ≤ k → S.W (S.w0 j k₀) (k + 1)
      = (S.m : ℝ) * S.W (S.w0 j k₀) k - (S.m : ℝ) * ((S.m : ℝ) - 1) * S.U := by
    intro k hkN
    rw [W_succ, val_pick_W, hcon k hkN, hbe k hkN, hecast, hU]
    ring
  have hfix : ((S.m : ℝ) * ((S.m : ℝ) - 1) * S.U) / ((S.m : ℝ) - 1) = (S.m : ℝ) * S.U := by
    have hne := S.m_sub_one_ne
    field_simp
  have hbd : ∀ k, N ≤ k →
      |S.W (S.w0 j k₀) k - ((S.m : ℝ) * ((S.m : ℝ) - 1) * S.U) / ((S.m : ℝ) - 1)|
        ≤ (S.m : ℝ) * S.U := by
    intro k _
    rw [hfix]
    obtain ⟨hlo, hhi⟩ := W_mem hw0 hw1 k
    rw [abs_le]
    constructor <;> linarith
  have hfixed := eq_fixed_of_trapped (f := S.W (S.w0 j k₀)) (r := (S.m : ℝ))
    (c := (S.m : ℝ) * ((S.m : ℝ) - 1) * S.U) (D := (S.m : ℝ) * S.U) hm1 hrec hbd
  rw [hfix] at hfixed
  have hval : (S.m : ℝ) * S.U = (((S.m : ℤ)) : ℝ) + (((S.m : ℤ)) : ℝ) * S.sq := by
    rw [hU]; push_cast; ring
  exact W_ne_val he hk h0 h1 N (le_refl _) (by rw [hfixed, hval])

/-! ## Lemma L1, the `b`-side -/

/-- **L1(b).**  The `b`-digits are not eventually stuck at `0`: that would confine the
state to `L = [0, p√m)`, but one step from above `U` overshoots `m(U-p) ≥ p√m`, and below
`U` the state is merely multiplied by `m` forever. -/
@[category research solved, AMS 11, ref "Dub06EO", group "dub06_slice"]
theorem exists_dB_ne (he : S.e = (S.m : ℤ) - 1) (hpsq : (S.p : ℝ) ≤ S.sq) {j k₀ : ℤ}
    (hk : 1 ≤ k₀) (h0 : 0 ≤ S.sigma j k₀) (h1 : S.sigma j k₀ ≤ S.U) (N : ℕ) :
    ∃ k, N ≤ k ∧ S.dB (S.w0 j k₀) k ≠ 0 := by
  by_contra hcon
  push Not at hcon
  have hmr : (0 : ℝ) < (S.m : ℝ) := by have := S.three_le_cast; linarith
  have hm1 : (1 : ℝ) < (S.m : ℝ) := by have := S.three_le_cast; linarith
  have hw0 : 0 ≤ S.w0 j k₀ := mul_nonneg hmr.le h0
  have hw1 : S.w0 j k₀ ≤ (S.m : ℝ) * S.U := mul_le_mul_of_nonneg_left h1 hmr.le
  have hU := U_eq_one_add he
  have hsqpos := S.sq_pos
  have hppos := S.p_cast_pos
  -- the state stays in `L = [0, p√m)`
  have hltL : ∀ k, N ≤ k → S.W (S.w0 j k₀) k < (S.p : ℝ) * S.sq := by
    intro k hkN
    refine (S.bsel_eq_zero_iff (W_mem hw0 hw1 k).1).mp ?_
    rw [← dB_eq]
    exact hcon k hkN
  -- one step from above the window overshoots
  have hover : (S.p : ℝ) * S.sq ≤ (S.m : ℝ) * (S.U - (S.p : ℝ)) := form_b he hpsq
  by_cases hcase : ∃ k, N ≤ k ∧ S.U < S.W (S.w0 j k₀) k
  · obtain ⟨k, hkN, hkU⟩ := hcase
    have hb0 : S.bsel (S.W (S.w0 j k₀) k) = 0 := by rw [← dB_eq]; exact hcon k hkN
    have hv : S.W (S.w0 j k₀) k - (S.bsel (S.W (S.w0 j k₀) k) : ℝ) * S.sq
        = S.W (S.w0 j k₀) k := by rw [hb0]; push_cast; ring
    have halt : (S.dA (S.w0 j k₀) k : ℝ) < S.W (S.w0 j k₀) k - S.U + (S.p : ℝ) := by
      have := S.asel_lt (w := S.W (S.w0 j k₀) k) (by rw [hv]; exact hkU)
      rw [hv] at this
      rw [dA_eq]
      exact this
    have hstep : S.W (S.w0 j k₀) (k + 1)
        = (S.m : ℝ) * (S.W (S.w0 j k₀) k - (S.dA (S.w0 j k₀) k : ℝ)) := by
      rw [W_succ, val_pick_W, hcon k hkN]
      push_cast
      ring
    have hnext := hltL (k + 1) (by omega)
    rw [hstep] at hnext
    nlinarith [mul_lt_mul_of_pos_left halt hmr]
  · push Not at hcase
    have hmul : ∀ k, N ≤ k → S.W (S.w0 j k₀) (k + 1) = (S.m : ℝ) * S.W (S.w0 j k₀) k := by
      intro k hkN
      have hb0 : S.bsel (S.W (S.w0 j k₀) k) = 0 := by rw [← dB_eq]; exact hcon k hkN
      have hv : S.W (S.w0 j k₀) k - (S.bsel (S.W (S.w0 j k₀) k) : ℝ) * S.sq
          = S.W (S.w0 j k₀) k := by rw [hb0]; push_cast; ring
      have ha0 : S.dA (S.w0 j k₀) k = 0 := by
        rw [dA_eq]
        exact S.asel_eq_zero (by rw [hv]; exact hcase k hkN)
      rw [W_succ, val_pick_W, ha0, hcon k hkN]
      push_cast
      ring
    have hpow : ∀ n : ℕ, S.W (S.w0 j k₀) (N + n) = (S.m : ℝ) ^ n * S.W (S.w0 j k₀) N := by
      intro n
      induction n with
      | zero => simp
      | succ n ih =>
        have e : N + (n + 1) = (N + n) + 1 := by omega
        rw [e, hmul (N + n) (Nat.le_add_right _ _), ih, pow_succ]
        ring
    have hne0 : S.W (S.w0 j k₀) N ≠ 0 := by
      have h := W_ne_val he hk h0 h1 N (p := 0) (q := 0) (by omega)
      simpa using h
    have hpos : 0 < S.W (S.w0 j k₀) N :=
      lt_of_le_of_ne (W_mem hw0 hw1 N).1 (Ne.symm hne0)
    obtain ⟨n, hn⟩ := pow_unbounded_of_one_lt ((S.p : ℝ) * S.sq / S.W (S.w0 j k₀) N) hm1
    have hlt := hltL (N + n) (Nat.le_add_right _ _)
    rw [hpow n] at hlt
    have := (div_lt_iff₀ hpos).mp hn
    nlinarith

/-! ## The uniform case of the reduction -/

/-- **Proposition 5.4.**  For `e = m - 1` and `√m ≥ p` the greedy's streams are canonical,
so the reduction applies and the translate produces a `ξ > 0` with `p ∣ ⌊ξ √mⁿ⌋` for every
`n ≥ 1`.  With `Slice.dvd_floor_of_e_le` this covers both branches of Theorem C. -/
@[category research solved, AMS 11, ref "Dub06EO", group "dub06_slice"]
theorem dvd_floor_of_uniform (S : Slice) (he : S.e = (S.m : ℤ) - 1)
    (hpsq : (S.p : ℝ) ≤ S.sq) {j k₀ : ℤ} (hj : 1 ≤ j) (hk : 1 ≤ k₀)
    (h0 : 0 ≤ S.sigma j k₀) (h1 : S.sigma j k₀ ≤ S.U) :
    ∃ ξ : ℝ, 0 < ξ ∧ ∀ n : ℕ, 1 ≤ n → S.p ∣ ⌊ξ * Real.sqrt S.m ^ n⌋ := by
  have hmr : (0 : ℝ) < (S.m : ℝ) := by have := S.three_le_cast; linarith
  have hw0 : 0 ≤ S.w0 j k₀ := mul_nonneg hmr.le h0
  have hw1 : S.w0 j k₀ ≤ (S.m : ℝ) * S.U := mul_le_mul_of_nonneg_left h1 hmr.le
  have hple : S.p ≤ (S.m : ℤ) - 1 := le_trans S.p_le_e (by omega)
  refine dvd_floor_of_hygiene S hj h0 h1 (fun N => ?_) (fun N => ?_)
  · obtain ⟨k, hkN, hne⟩ := exists_dA_ne he hpsq hk h0 h1 N
    have hle := (dA_mem hw0 hw1 k).2.2
    obtain ⟨r, hr⟩ := (dA_mem hw0 hw1 k).1
    obtain ⟨t, ht⟩ := S.p_dvd_e
    have hlt : S.dA (S.w0 j k₀) k < S.e := lt_of_le_of_ne hle hne
    have h4 : S.p * r < S.p * t := by rw [← hr, ← ht]; exact hlt
    have h5 : r < t := lt_of_mul_lt_mul_left h4 S.p_pos.le
    have h6 : S.dA (S.w0 j k₀) k ≤ S.e - S.p := by
      calc S.dA (S.w0 j k₀) k = S.p * r := hr
        _ ≤ S.p * (t - 1) := mul_le_mul_of_nonneg_left (by omega) S.p_pos.le
        _ = S.p * t - S.p := by ring
        _ = S.e - S.p := by rw [← ht]
    exact ⟨k, hkN, by omega⟩
  · obtain ⟨k, hkN, hne⟩ := exists_dB_ne he hpsq hk h0 h1 N
    have hge := (dB_mem hw0 hw1 k).2.1
    obtain ⟨r, hr⟩ := (dB_mem hw0 hw1 k).1
    have hr0 : 0 < r := by
      rcases lt_trichotomy r 0 with h | h | h
      · exfalso; nlinarith [S.p_pos]
      · exact absurd (by rw [hr, h, mul_zero]) hne
      · exact h
    have h6 : S.p ≤ S.dB (S.w0 j k₀) k := by
      calc S.p = S.p * 1 := (mul_one _).symm
        _ ≤ S.p * r := mul_le_mul_of_nonneg_left (by omega) S.p_pos.le
        _ = S.dB (S.w0 j k₀) k := hr.symm
    have hle := (dB_mem hw0 hw1 k).2.2
    exact ⟨k, hkN, by omega⟩

/-- **Proposition 5.4 at `p = 2`.**  For `e = m - 1` and `m ≥ 5` the greedy's streams are
canonical, so `√m ∈ 𝒵`.  With `Slice.mem_MahlerZ_of_e_le` this covers every non-square
base. -/
@[category research solved, AMS 11, ref "Dub06EO", group "dub06_slice"]
theorem mem_MahlerZ_of_uniform (S : Slice) (hp : S.p = 2) (he : S.e = (S.m : ℤ) - 1)
    (hpsq : (S.p : ℝ) ≤ S.sq) {j k₀ : ℤ} (hj : 1 ≤ j) (hk : 1 ≤ k₀)
    (h0 : 0 ≤ S.sigma j k₀) (h1 : S.sigma j k₀ ≤ S.U) :
    Real.sqrt S.m ∈ MahlerZ :=
  mem_MahlerZ_of_dvd S hp (dvd_floor_of_uniform S he hpsq hj hk h0 h1)

end Slice

end SZ
