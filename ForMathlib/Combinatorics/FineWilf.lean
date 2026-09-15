/-
(C) 2026 Ralf Stephan, in collaboration with Claude Code.
Released under CC0 1.0 Universal (public-domain dedication).
See https://creativecommons.org/publicdomain/zero/1.0/
-/
import Mathlib.Algebra.Ring.Periodic
import Mathlib.Data.Nat.GCD.Basic
import Mathlib.Data.Nat.ModEq
import Mathlib.Data.List.Basic
import Mathlib.Tactic.Common
import Mathlib.Tactic.Ring

/-!
# The theorem of Fine and Wilf

If a word has two periods `p` and `q` and is at least `p + q - gcd p q` letters long, then it has
the period `gcd p q`.  This is the **periodicity lemma** of Fine and Wilf [FW65], the basic
theorem of combinatorics on words, and Mathlib does not have it.

## Statement

A word is read, as everywhere in this cluster of files, as a function `u : ℕ → α` on a window
`[0, L)`, and

* `HasPeriodOn u L p` — `u i = u (i + p)` whenever *both* positions lie in `[0, L)`.

A period is not required to divide, or even to be at most, the length: `HasPeriodOn u L p` is
vacuously true for `L ≤ p`, which is why the length hypothesis carries the whole content.

## Main results

* `fine_wilf` — the theorem: two periods `p, q` on a window of length `L ≥ p + q - gcd p q` give
  the period `gcd p q` on that window.  The hypothesis is written `p + q ≤ L + gcd p q`, to keep
  truncated subtraction out of it.
* `List.fine_wilf` — the same for a `List`, phrased with `l[i]?`; a one-line specialisation.
* `exists_not_hasPeriodOn_gcd` — the length bound is **sharp**: for every `p ≥ 2` the word
  `a^(p-1) b a^(p-1)` of length `2p - 1 = p + (p + 1) - gcd p (p + 1) - 1` has periods `p` and
  `p + 1` and is not constant.
* `exists_periodic_not_shift` — the same sharpness one level up: the two periodic extensions of
  that word agree on those `2p - 1` letters and are still not shifts of one another.
* `periodic_gcd` — for a *globally* periodic word two periods always give their gcd, with no
  length hypothesis (a one-line corollary of `fine_wilf` on a large enough window).
* `eq_shift_of_periodic_of_factor_eq` — the form the applications use: two periodic words that
  agree on **one** window of length `p + q` agree forever, and both have period `gcd p q`.  So two
  periodic points of a subshift that share a long enough factor lie on the same orbit.

## Proof

Strong induction on `p + q` — the Euclidean algorithm run on the two periods — with the
degenerate cases (`p = 0`, `p ∣ q`, `q ∣ p`) handing back one of the hypotheses unchanged.  For
`0 < p < q` put `r = q - p`, so that `gcd p r = gcd p q =: d`.

* **The Euclidean step**, available when `r > d`.  The prefix of length `L - p` has period `r`:
  for `i + r < L - p` one has `u i = u (i + q) = u (i + r)`, the second equality by the period `p`
  at `i + r`.  It also has period `p`, so induction gives it the period `d`, and the period `p`
  carries that up to the full window: for `i + d < L` with `p ≤ i` read
  `u i = u (i - p) = u (i - p + d) = u (i + d)`.  What is left is `i < p` with `i + d ≥ L - p`,
  which forces `L < 2p + d`; against `L ≥ p + q - d = 2p + r - d` that gives `r < 2d`, and
  `d ∣ r`, so `r = d`.
* **The remaining case `r = d`**, i.e. `q = p + d` with `d ∣ p` and `L ≥ 2p`.  Here `u i = u (i+d)`
  holds as soon as `i + p + d < L` (go up by `q`, come back down by `p`) and, by the period `p`
  again, as soon as `p ≤ i`.  The `i` that are left satisfy `p - d ≤ i < p`; for those `u (i + d)`
  equals `u c` with `c = i + d - p < d`, and a chain of `p/d - 1` steps of the first kind — each
  one legal because `c + (p - d) + p < 2p ≤ L` — climbs from `c` back to `c + p - d = i`.

The extremal words for the bound are the *central words*; `exists_not_hasPeriodOn_gcd` exhibits
only the `q = p + 1` member of that family, which is already enough to show that `p + q - gcd p q`
cannot be lowered.

## References

* [FW65] N. J. Fine, H. S. Wilf, *Uniqueness theorems for periodic functions*, Proc. Amer. Math.
  Soc. **16** (1965), 109–114.
* [Lot02] M. Lothaire, *Algebraic Combinatorics on Words*, Cambridge, 2002: Prop. 1.3.5, and the
  discussion of sharpness following it.
* [BK26] Y. Bugeaud, D. H. Kim, *On the b-ary expansion of a real number whose irrationality
  exponent is close to 2*, arXiv:2510.02059: Lemma 2.3 is this statement, quoted there as the
  tool that separates two periodic orbits.
-/

namespace ForMathlib.SubwordComplexity

variable {α : Type*}

/-- The word `u`, read on the window `[0, L)`, **has period `p`**: `u i = u (i + p)` whenever both
positions lie in the window.  For `L ≤ p` this is vacuous. -/
def HasPeriodOn (u : ℕ → α) (L p : ℕ) : Prop := ∀ i, i + p < L → u i = u (i + p)

lemma hasPeriodOn_zero (u : ℕ → α) (L : ℕ) : HasPeriodOn u L 0 := fun _ _ => rfl

lemma hasPeriodOn_of_le {u : ℕ → α} {L p : ℕ} (h : L ≤ p) : HasPeriodOn u L p :=
  fun _ hi => absurd hi (by omega)

/-- A period of a window is a period of every shorter window. -/
lemma HasPeriodOn.mono {u : ℕ → α} {L L' p : ℕ} (h : HasPeriodOn u L p) (hL : L' ≤ L) :
    HasPeriodOn u L' p := fun i hi => h i (lt_of_lt_of_le hi hL)

/-- A global period is a period of every window. -/
lemma HasPeriodOn.of_periodic {u : ℕ → α} {p : ℕ} (h : Function.Periodic u p) (L : ℕ) :
    HasPeriodOn u L p := fun i _ => (h i).symm

/-- Inside the window, a period lets one reduce the position modulo it. -/
lemma hasPeriodOn_mod {u : ℕ → α} {L p : ℕ} (h : HasPeriodOn u L p) (hp : 0 < p) :
    ∀ i, i < L → u (i % p) = u i := by
  intro i
  induction i using Nat.strong_induction_on with
  | _ i IH =>
    intro hi
    by_cases hlt : i < p
    · rw [Nat.mod_eq_of_lt hlt]
    · have e1 : u (i - p) = u i := by
        have := h (i - p) (by omega)
        rwa [show i - p + p = i by omega] at this
      have e2 : (i - p) % p = i % p := by
        conv_rhs => rw [show i = i - p + p by omega]
        exact (Nat.add_mod_right (i - p) p).symm
      rw [← e2, IH (i - p) (by omega) (by omega), e1]

/-! ### The theorem -/

/-- The inductive step of `fine_wilf` for `p < q`, with the induction hypothesis supplied as a
statement about pairs of smaller total size. -/
private lemma fine_wilf_lt {u : ℕ → α} {N p q L : ℕ}
    (IH : ∀ p' q' L' : ℕ, p' + q' ≤ N → HasPeriodOn u L' p' → HasPeriodOn u L' q' →
      p' + q' ≤ L' + Nat.gcd p' q' → HasPeriodOn u L' (Nat.gcd p' q'))
    (hN : p + q ≤ N + 1) (hpq : p < q) (hp : HasPeriodOn u L p) (hq : HasPeriodOn u L q)
    (hL : p + q ≤ L + Nat.gcd p q) : HasPeriodOn u L (Nat.gcd p q) := by
  -- the degenerate cases hand back one of the two hypotheses
  rcases Nat.eq_zero_or_pos p with rfl | hp0
  · simpa using hq
  by_cases hdvd : p ∣ q
  · simpa [Nat.gcd_eq_left hdvd] using hp
  -- the generic case: write `q = p + r` and normalise every gcd to `gcd p r`
  obtain ⟨r, rfl⟩ : ∃ r, q = p + r := ⟨q - p, by omega⟩
  rw [Nat.gcd_self_add_right] at hL ⊢
  set d := Nat.gcd p r with hd
  have hdp : d ∣ p := hd ▸ Nat.gcd_dvd_left p r
  have hdr : d ∣ r := hd ▸ Nat.gcd_dvd_right p r
  have hd0 : 0 < d := hd ▸ Nat.gcd_pos_of_pos_left r hp0
  have hdlep : d ≤ p := Nat.le_of_dvd hp0 hdp
  have hr0 : 0 < r := by omega
  have hdler : d ≤ r := Nat.le_of_dvd hr0 hdr
  have hdltp : d < p := by
    rcases eq_or_lt_of_le hdlep with hdd | hdd
    · exact absurd (Dvd.dvd.add (dvd_refl p) (hdd ▸ hdr)) hdvd
    · exact hdd
  have hLp : p < L := by omega
  rcases eq_or_lt_of_le hdler with hrd | hrd
  · -- ### the case `q = p + d`, where the Euclidean step has nothing left to subtract
    have hL2 : 2 * p ≤ L := by omega
    -- one step up by `q`, one step back down by `p`
    have hA : ∀ i, i + p + d < L → u i = u (i + d) := by
      intro i hi
      have e1 : u i = u (i + (p + r)) := hq i (by omega)
      have e2 : u (i + d) = u (i + d + p) := hp (i + d) (by omega)
      rw [show i + (p + r) = i + d + p by omega] at e1
      exact e1.trans e2.symm
    -- iterate it along any multiple of `d`
    have hchain : ∀ t c : ℕ, d ∣ t → c + t + p < L → u c = u (c + t) := by
      intro t
      induction t using Nat.strong_induction_on with
      | _ t IHt =>
        intro c hdt hct
        rcases Nat.eq_zero_or_pos t with rfl | ht0
        · simp
        · have hdt' : d ≤ t := Nat.le_of_dvd ht0 hdt
          have h1 := IHt (t - d) (by omega) c (Nat.dvd_sub hdt dvd_rfl) (by omega)
          have h2 := hA (c + (t - d)) (by omega)
          rw [show c + (t - d) + d = c + t by omega] at h2
          exact h1.trans h2
    intro i hi
    by_cases h1 : i + p + d < L
    · exact hA i h1
    by_cases h2 : p ≤ i
    · have e1 := hp (i - p) (by omega)
      have e2 := hp (i + d - p) (by omega)
      have e3 := hA (i - p) (by omega)
      rw [show i - p + p = i by omega] at e1
      rw [show i + d - p + p = i + d by omega] at e2
      rw [show i - p + d = i + d - p by omega] at e3
      rw [← e1, e3, e2]
    · -- `p - d ≤ i < p`: climb from the residue `c = i + d - p < d` back up to `i`
      have e1 := hp (i + d - p) (by omega)
      rw [show i + d - p + p = i + d by omega] at e1
      have e2 := hchain (p - d) (i + d - p) (Nat.dvd_sub hdp dvd_rfl) (by omega)
      rw [show i + d - p + (p - d) = i by omega] at e2
      exact e2.symm.trans e1
  · -- ### the Euclidean step, `d < r`
    have h2d : 2 * d ≤ r := by
      obtain ⟨k, hk⟩ := hdr
      have hk2 : 2 ≤ k := by rcases k with _ | _ | k <;> omega
      calc 2 * d = d * 2 := Nat.mul_comm 2 d
        _ ≤ d * k := Nat.mul_le_mul_left d hk2
        _ = r := hk.symm
    have hp' : HasPeriodOn u (L - p) p := hp.mono (by omega)
    have hr' : HasPeriodOn u (L - p) r := by
      intro i hi
      have e1 : u i = u (i + (p + r)) := hq i (by omega)
      have e2 : u (i + r) = u (i + r + p) := hp (i + r) (by omega)
      rw [show i + (p + r) = i + r + p by omega] at e1
      exact e1.trans e2.symm
    have hd' : HasPeriodOn u (L - p) d := by
      rw [hd]
      exact IH p r (L - p) (by omega) hp' hr' (by rw [← hd]; omega)
    intro i hi
    by_cases h1 : i + d < L - p
    · exact hd' i h1
    by_cases h2 : p ≤ i
    · have e1 := hp (i - p) (by omega)
      have e2 := hp (i + d - p) (by omega)
      have e3 := hd' (i - p) (by omega)
      rw [show i - p + p = i by omega] at e1
      rw [show i + d - p + p = i + d by omega] at e2
      rw [show i - p + d = i + d - p by omega] at e3
      rw [← e1, e3, e2]
    · omega

/-- **The theorem of Fine and Wilf** [FW65].  A word that, read on a window of length `L`, has the
two periods `p` and `q`, and whose length satisfies `p + q ≤ L + gcd p q`, has the period
`gcd p q` on that window.  The length hypothesis is sharp: see `exists_not_hasPeriodOn_gcd`. -/
theorem fine_wilf {u : ℕ → α} {p q L : ℕ} (hp : HasPeriodOn u L p) (hq : HasPeriodOn u L q)
    (hL : p + q ≤ L + Nat.gcd p q) : HasPeriodOn u L (Nat.gcd p q) := by
  have H : ∀ N p' q' L' : ℕ, p' + q' ≤ N → HasPeriodOn u L' p' → HasPeriodOn u L' q' →
      p' + q' ≤ L' + Nat.gcd p' q' → HasPeriodOn u L' (Nat.gcd p' q') := by
    intro N
    induction N with
    | zero =>
      intro p' q' L' hN hp' _ _
      obtain ⟨rfl, rfl⟩ : p' = 0 ∧ q' = 0 := by omega
      simpa using hp'
    | succ N IH =>
      intro p' q' L' hN hp' hq' hL'
      rcases lt_trichotomy p' q' with h | rfl | h
      · exact fine_wilf_lt IH hN h hp' hq' hL'
      · simpa using hp'
      · rw [Nat.gcd_comm] at hL' ⊢
        exact fine_wilf_lt IH (by omega) h hq' hp' (by omega)
  exact H (p + q) p q L le_rfl hp hq hL

/-- **Fine–Wilf for lists**, phrased with `l[i]?` so that no `Inhabited` instance is needed: a
list with periods `p` and `q` whose length satisfies `p + q ≤ l.length + gcd p q` has the period
`gcd p q`. -/
theorem _root_.List.fine_wilf {l : List α} {p q : ℕ}
    (hp : ∀ i, i + p < l.length → l[i]? = l[i + p]?)
    (hq : ∀ i, i + q < l.length → l[i]? = l[i + q]?)
    (hL : p + q ≤ l.length + Nat.gcd p q) :
    ∀ i, i + Nat.gcd p q < l.length → l[i]? = l[i + Nat.gcd p q]? :=
  ForMathlib.SubwordComplexity.fine_wilf (u := fun i => l[i]?) hp hq hL

/-- **The length bound of `fine_wilf` is sharp.**  For `p ≥ 2` the word `a^(p-1) b a^(p-1)`, of
length `2p - 1 = p + (p + 1) - gcd p (p + 1) - 1`, has both the period `p` and the period `p + 1`
but is not constant, i.e. does not have the period `gcd p (p + 1) = 1`. -/
theorem exists_not_hasPeriodOn_gcd {p : ℕ} (hp : 2 ≤ p) :
    ∃ u : ℕ → Bool, HasPeriodOn u (2 * p - 1) p ∧ HasPeriodOn u (2 * p - 1) (p + 1) ∧
      ¬ HasPeriodOn u (2 * p - 1) (Nat.gcd p (p + 1)) := by
  have hg : Nat.gcd p (p + 1) = 1 := by rw [Nat.gcd_self_add_right]; exact Nat.gcd_one_right p
  refine ⟨fun i => decide (i ≠ p - 1), fun i hi => ?_, fun i hi => ?_, ?_⟩
  · simp only [decide_eq_decide]
    omega
  · simp only [decide_eq_decide]
    omega
  · intro hcon
    rw [hg] at hcon
    have := hcon (p - 2) (by omega)
    simp only [decide_eq_decide] at this
    omega

/-! ### Globally periodic words -/

/-- Iterating a global period. -/
lemma periodic_add_mul {u : ℕ → α} {p : ℕ} (h : Function.Periodic u p) (j k : ℕ) :
    u (j + k * p) = u j := by
  induction k with
  | zero => simp
  | succ k IH =>
    rw [show j + (k + 1) * p = j + k * p + p by ring, h (j + k * p)]
    exact IH

/-- A global period lets one reduce the argument modulo that period. -/
lemma periodic_eq_mod {u : ℕ → α} {p : ℕ} (h : Function.Periodic u p) (j : ℕ) :
    u (j % p) = u j := by
  conv_rhs => rw [← Nat.mod_add_div' j p]
  exact (periodic_add_mul h (j % p) (j / p)).symm

/-- Two arguments congruent modulo a global period carry the same letter. -/
lemma periodic_eq_of_mod_eq {u : ℕ → α} {p : ℕ} (h : Function.Periodic u p) {m m' : ℕ}
    (hmm : m % p = m' % p) : u m = u m' := by
  rw [← periodic_eq_mod h m, ← periodic_eq_mod h m', hmm]

/-- For a globally periodic word two periods give their gcd, with no length hypothesis: every
window is long enough for `fine_wilf`. -/
theorem periodic_gcd {u : ℕ → α} {p q : ℕ} (hp : Function.Periodic u p)
    (hq : Function.Periodic u q) : Function.Periodic u (Nat.gcd p q) := by
  intro i
  exact (fine_wilf (u := u) (p := p) (q := q) (L := i + p + q + Nat.gcd p q + 1)
    (HasPeriodOn.of_periodic hp _) (HasPeriodOn.of_periodic hq _) (by omega) i (by omega)).symm

/-- **Sharpness at the level of orbits.**  For every `p ≥ 2` there are a `p`-periodic word `x` and
a `(p+1)`-periodic word `y` that agree on a block of length `2p - 1`, one letter short of the
`p + (p + 1) - gcd p (p + 1) = 2p` demanded by `fine_wilf`, and that are nevertheless **not**
shifts of one another.  Both are periodic extensions of the word of
`exists_not_hasPeriodOn_gcd`. -/
theorem exists_periodic_not_shift {p : ℕ} (hp : 2 ≤ p) :
    ∃ x y : ℕ → Bool, Function.Periodic x p ∧ Function.Periodic y (p + 1) ∧
      (∀ i, i < 2 * p - 1 → x i = y i) ∧ ¬ ∃ c, ∀ i, x i = y (i + c) := by
  set w : ℕ → Bool := fun i => decide (i ≠ p - 1) with hw
  have hwp : HasPeriodOn w (2 * p - 1) p := by
    intro i hi; simp only [hw, decide_eq_decide]; omega
  have hwp1 : HasPeriodOn w (2 * p - 1) (p + 1) := by
    intro i hi; simp only [hw, decide_eq_decide]; omega
  refine ⟨fun i => w (i % p), fun i => w (i % (p + 1)), fun i => ?_, fun i => ?_, fun i hi => ?_,
    ?_⟩
  · simp [Nat.add_mod_right]
  · simp [Nat.add_mod_right]
  · show w (i % p) = w (i % (p + 1))
    rw [hasPeriodOn_mod hwp (by omega) i hi, hasPeriodOn_mod hwp1 (by omega) i hi]
  · rintro ⟨c, hc⟩
    -- a shift of a `(p+1)`-periodic word is `(p+1)`-periodic, so `x` would have both periods
    have hx : Function.Periodic (fun i => w (i % p)) p := fun i => by simp [Nat.add_mod_right]
    have hy : Function.Periodic (fun i => w (i % (p + 1))) (p + 1) := fun i => by
      simp [Nat.add_mod_right]
    have hx1 : Function.Periodic (fun i => w (i % p)) (p + 1) := by
      intro i
      rw [hc (i + (p + 1)), show i + (p + 1) + c = i + c + (p + 1) by omega, hy (i + c), ← hc i]
    have hone : Function.Periodic (fun i => w (i % p)) 1 := by
      have := periodic_gcd hx hx1
      rwa [Nat.gcd_self_add_right, Nat.gcd_one_right] at this
    have h1 := hone (p - 2)
    simp only [Nat.mod_eq_of_lt (show p - 2 + 1 < p by omega),
      Nat.mod_eq_of_lt (show p - 2 < p by omega), hw, decide_eq_decide] at h1
    omega

/-- Shifting the reading position preserves a global period. -/
lemma periodic_shift {u : ℕ → α} {p : ℕ} (h : Function.Periodic u p) (a : ℕ) :
    Function.Periodic (fun i => u (a + i)) p := by
  intro i
  show u (a + (i + p)) = u (a + i)
  rw [show a + (i + p) = a + i + p by omega]
  exact h (a + i)

/-- A word with a global period `p > 0` inherits from a shifted copy of itself any period of that
copy. -/
lemma periodic_of_shift_periodic {u : ℕ → α} {p d a : ℕ} (hp0 : 0 < p)
    (hu : Function.Periodic u p) (hs : Function.Periodic (fun i => u (a + i)) d) :
    Function.Periodic u d := by
  intro j
  have hap : a ≤ a * p := by
    calc a = a * 1 := (Nat.mul_one a).symm
      _ ≤ a * p := Nat.mul_le_mul_left a hp0
  have e1 : u (j + a * p) = u j := periodic_add_mul hu j a
  have e2 : u (j + d + a * p) = u (j + d) := periodic_add_mul hu (j + d) a
  have e3 := hs (j + a * p - a)
  simp only at e3
  rw [show a + (j + a * p - a + d) = j + d + a * p by omega,
    show a + (j + a * p - a) = j + a * p by omega] at e3
  rw [← e2, e3]
  exact e1

/-- The zero-shift case of `eq_shift_of_periodic_of_factor_eq`. -/
private lemma eq_of_periodic_of_eq_on {X Y : ℕ → α} {p q : ℕ} (hp0 : 0 < p) (hq0 : 0 < q)
    (hX : Function.Periodic X p) (hY : Function.Periodic Y q)
    (h : ∀ i, i < p + q → X i = Y i) :
    (∀ i, X i = Y i) ∧ Function.Periodic X (Nat.gcd p q) ∧ Function.Periodic Y (Nat.gcd p q) := by
  set d := Nat.gcd p q with hd
  have hd0 : 0 < d := hd ▸ Nat.gcd_pos_of_pos_left q hp0
  have hdlep : d ≤ p := Nat.le_of_dvd hp0 (hd ▸ Nat.gcd_dvd_left p q)
  have hdleq : d ≤ q := Nat.le_of_dvd hq0 (hd ▸ Nat.gcd_dvd_right p q)
  -- on the common window `X` inherits the period `q` of `Y`, so Fine–Wilf applies to `X`
  have hXq : HasPeriodOn X (p + q) q := by
    intro i hi
    rw [h i (by omega), h (i + q) (by omega)]
    exact (hY i).symm
  have hwin : HasPeriodOn X (p + q) d := by
    rw [hd]
    exact fine_wilf (HasPeriodOn.of_periodic hX _) hXq (by omega)
  have hwinY : HasPeriodOn Y (p + q) d := by
    intro i hi
    rw [← h i (by omega), ← h (i + d) (by omega)]
    exact hwin i hi
  -- a window of length `p + d` with the period `d`, plus the global period `p`, is enough
  have hXd : Function.Periodic X d := by
    intro j
    have h1 : X (j % p) = X (j % p + d) := hwin (j % p) (by have := Nat.mod_lt j hp0; omega)
    have h2 : X (j % p + d) = X (j + d) :=
      periodic_eq_of_mod_eq hX ((Nat.mod_modEq j p).add_right d)
    have h3 : X (j % p) = X j := periodic_eq_mod hX j
    rw [← h3, h1]
    exact h2.symm
  have hYd : Function.Periodic Y d := by
    intro j
    have h1 : Y (j % q) = Y (j % q + d) := hwinY (j % q) (by have := Nat.mod_lt j hq0; omega)
    have h2 : Y (j % q + d) = Y (j + d) :=
      periodic_eq_of_mod_eq hY ((Nat.mod_modEq j q).add_right d)
    have h3 : Y (j % q) = Y j := periodic_eq_mod hY j
    rw [← h3, h1]
    exact h2.symm
  refine ⟨fun i => ?_, hXd, hYd⟩
  -- both sides depend only on `i mod d`, and there they agree inside the window
  have h1 : X (i % d) = X i := periodic_eq_mod hXd i
  have h2 : Y (i % d) = Y i := periodic_eq_mod hYd i
  have h3 : X (i % d) = Y (i % d) := h (i % d) (by have := Nat.mod_lt i hd0; omega)
  rw [← h1, ← h2, h3]

/-- **Two periodic words that share one long enough factor agree forever.**  If `x` has period
`p > 0`, `y` has period `q > 0`, and the length-`(p + q)` factors of `x` at `a` and of `y` at `b`
coincide, then `x (a + i) = y (b + i)` for *every* `i`, and both words have the period `gcd p q`.

For a subshift this says that two periodic points with a common factor of length the sum of their
periods lie on the same orbit — the Fine–Wilf input to the structure theory of words of low
complexity. -/
theorem eq_shift_of_periodic_of_factor_eq {x y : ℕ → α} {p q a b : ℕ} (hp0 : 0 < p) (hq0 : 0 < q)
    (hx : Function.Periodic x p) (hy : Function.Periodic y q)
    (h : ∀ i, i < p + q → x (a + i) = y (b + i)) :
    (∀ i, x (a + i) = y (b + i)) ∧ Function.Periodic x (Nat.gcd p q) ∧
      Function.Periodic y (Nat.gcd p q) := by
  obtain ⟨h1, h2, h3⟩ :=
    eq_of_periodic_of_eq_on hp0 hq0 (periodic_shift hx a) (periodic_shift hy b) h
  exact ⟨h1, periodic_of_shift_periodic hp0 hx h2, periodic_of_shift_periodic hq0 hy h3⟩

end ForMathlib.SubwordComplexity
