/-
(C) 2026 Ralf Stephan, in collaboration with Claude Code.
Released under CC0 1.0 Universal (public-domain dedication).
See https://creativecommons.org/publicdomain/zero/1.0/
-/
import SRS.AntihydraSRS

/-!
# Faithful simulation layer for the Antihydra SRS

`SRS.AntihydraSRS` proves the *soundness* half of the simulation (the analog of [YAH] §3, Claim 1):
every value-preserving rule preserves the value `a` and the counter `b`, and a dynamic step shifts
them by the macro amounts. What it does **not** yet do is tie those per-step facts to the *structure*
of a configuration `◁ w ▷ cᵇ`, so that the dynamic step is *forced* to the boundary `▷` and its
parity is *forced* by the value. That structural link is what makes the simulation faithful, and is
the subject of this file.

The construction follows [YAH] §3.2 (Theorem 3.17, Claims 1–3) and mirrors the corpus's own forward
simulation `SRS.Zantema` (`evenSim` / `oddSim`, built from `ReflTransGen` sweeps). A subtlety the
counter introduces: in [YAH]'s Collatz system the end marker `▷` is the *rightmost* symbol, so a
dynamic rule fires only at the right end (empty right context); in the Antihydra system the counter
block `cᵇ` sits *after* `▷`, so the right context of a dynamic redex is the counter block, and the
value/parity is forced only once we know the redex sits at the unique `▷`.

* `IsDigits w` — `w` is a digit string (only `f,t,d0,d1,d2`; no markers `◁`,`▷` or counter `c`).
* `dynStep_config_dest` — **the redex-alignment crux**: a dynamic step from a configuration
  `config w b` (with `w` a digit string) is forced to the boundary, so it is the even rule
  `…f▷ → …d0▷cc` (when `w` ends in `f`) or the odd rule `…t▷c → …d1▷` (when `w` ends in `t`,
  `b ≥ 1`). This is [YAH] Claim 1's dynamic half made config-faithful — it is what lets us read the
  parity of the value off the rule that fired.

## References
* [YAH] E. Yolcu, S. Aaronson, M. J. H. Heule. *An Automated Approach to the Collatz Conjecture.*
  Journal of Automated Reasoning (2023); arXiv:2105.14697. §3.2, Theorem 3.17 (Claims 1–3).
* [BO93] R. V. Book, F. Otto. *String-Rewriting Systems.* Springer, 1993.
-/

namespace StringRewriting.AntihydraSRS

open StringRewriting StringRewriting.MixedBase ASym Relation

/-- A **digit string**: a list of only the binary/ternary digit symbols `f, t, d0, d1, d2`, with no
markers `◁`, `▷` or counter symbol `c`. The middle part `w` of a configuration `◁ w ▷ cᵇ`. -/
@[category API, AMS 68, ref "YAH", group "antihydra_srs"]
def IsDigits (w : List ASym) : Prop := ∀ s ∈ w, s = f ∨ s = t ∨ s = d0 ∨ s = d1 ∨ s = d2

/-- A digit string contains no end marker `▷`. -/
@[category API, AMS 68, ref "YAH", group "antihydra_srs"]
theorem IsDigits.rhd_not_mem {w : List ASym} (h : IsDigits w) : rhd ∉ w := by
  intro hmem; rcases h rhd hmem with h | h | h | h | h <;> exact absurd h (by decide)

/-- A digit string contains no begin marker `◁`. -/
@[category API, AMS 68, ref "YAH", group "antihydra_srs"]
theorem IsDigits.lhd_not_mem {w : List ASym} (h : IsDigits w) : lhd ∉ w := by
  intro hmem; rcases h lhd hmem with h | h | h | h | h <;> exact absurd h (by decide)

/-- `IsDigits` distributes over concatenation. -/
@[category API, AMS 68, ref "YAH", group "antihydra_srs"]
theorem isDigits_append {u v : List ASym} : IsDigits (u ++ v) ↔ IsDigits u ∧ IsDigits v := by
  constructor
  · exact fun h => ⟨fun s hs => h s (List.mem_append_left _ hs),
      fun s hs => h s (List.mem_append_right _ hs)⟩
  · rintro ⟨h1, h2⟩ s hs
    rcases List.mem_append.mp hs with h | h
    · exact h1 s h
    · exact h2 s h

/-- Replacing the middle of a digit string by another digit string keeps it a digit string. -/
@[category API, AMS 68, ref "YAH", group "antihydra_srs", formal_uses isDigits_append]
theorem isDigits_replace {wp mid mid' wq : List ASym} (hw : IsDigits (wp ++ mid ++ wq))
    (hmid' : IsDigits mid') : IsDigits (wp ++ mid' ++ wq) := by
  rw [isDigits_append, isDigits_append] at hw ⊢
  exact ⟨⟨hw.1.1, hmid'⟩, hw.2⟩

/-- **Uniqueness of a split at an absent-elsewhere symbol.** If `x` occurs in neither `A` nor `C`,
then a shared decomposition `A ++ x :: B = C ++ x :: D` forces `A = C` and `B = D`. (Used to align a
dynamic redex, which contains `▷`, with the *unique* `▷` of a configuration.) -/
@[category API, AMS 68, ref "YAH", group "antihydra_srs"]
theorem append_cons_inj {α} (x : α) : ∀ (A C B D : List α),
    x ∉ A → x ∉ C → A ++ x :: B = C ++ x :: D → A = C ∧ B = D
  | [], [], _, _ => by intro _ _ h; simpa using h
  | [], d :: cs, _, _ => by
      intro _ hC h
      simp only [List.nil_append, List.cons_append, List.cons.injEq] at h
      exact absurd h.1 (List.ne_of_not_mem_cons hC)
  | a :: as, [], _, _ => by
      intro hA _ h
      simp only [List.cons_append, List.nil_append, List.cons.injEq] at h
      exact absurd h.1.symm (List.ne_of_not_mem_cons hA)
  | a :: as, d :: cs, B, D => by
      intro hA hC h
      simp only [List.cons_append, List.cons.injEq] at h
      obtain ⟨rfl, h2⟩ := h
      obtain ⟨rfl, rfl⟩ := append_cons_inj x as cs B D
        (List.not_mem_of_not_mem_cons hA) (List.not_mem_of_not_mem_cons hC) h2
      exact ⟨rfl, rfl⟩

/-- A configuration `◁ w ▷ cᵇ` contains the end marker `▷` exactly once (when `w` is a digit
string). -/
@[category API, AMS 68, ref "YAH", group "antihydra_srs", formal_uses IsDigits.rhd_not_mem]
theorem count_rhd_config (w : List ASym) (b : ℕ) (hw : rhd ∉ w) :
    (config w b).count rhd = 1 := by
  simp only [config, List.count_cons, List.count_append, List.count_replicate,
    List.count_eq_zero.mpr hw]
  simp

/-- **Redex-alignment crux** ([YAH] Claim 1, dynamic half, made config-faithful). A dynamic rewrite
from a configuration `config w b` with `w` a digit string is *forced* to the boundary `▷`: either the
even rule `f▷ → d0▷cc` fires (so `w` ends in `f`, the result is `config (w' ++ [d0]) (b+2)`), or the
odd rule `t▷c → d1▷` fires (so `w` ends in `t`, `b ≥ 1`, the result is `config (w' ++ [d1]) b'`).
Crucially, *which* rule fired is determined by the last digit of `w` — hence by the parity of the
value — because `▷` occurs only once (`count_rhd_config`) and `append_cons_inj` pins the redex
there. -/
@[category research solved, AMS 68 11, ref "YAH", group "antihydra_srs",
  formal_uses append_cons_inj count_rhd_config IsDigits.rhd_not_mem]
theorem dynStep_config_dest (w : List ASym) (b : ℕ) (hw : IsDigits w) (v : List ASym)
    (h : RewriteStep dynRules (config w b) v) :
    (∃ w', w = w' ++ [f] ∧ v = config (w' ++ [d0]) (b + 2)) ∨
    (∃ w' b', w = w' ++ [t] ∧ b = b' + 1 ∧ v = config (w' ++ [d1]) b') := by
  obtain ⟨pre, post, ℓ, r, hrule, hu, hv⟩ := h
  have hrhd : rhd ∉ w := hw.rhd_not_mem
  have hcount : (config w b).count rhd = 1 := count_rhd_config w b hrhd
  rcases hrule with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
  · -- even rule: ℓ = [f, rhd], r = [d0, rhd, c, c]
    left
    rw [hu, List.count_append, List.count_append] at hcount
    have hfr : ([f, rhd] : List ASym).count rhd = 1 := by decide
    have hpre : rhd ∉ pre := by rw [← List.count_eq_zero]; omega
    have heq : (lhd :: w) ++ rhd :: List.replicate b c = (pre ++ [f]) ++ rhd :: post := by
      show config w b = (pre ++ [f]) ++ rhd :: post
      rw [hu]; simp [List.append_assoc]
    obtain ⟨h1, h2⟩ := append_cons_inj rhd (lhd :: w) (pre ++ [f]) (List.replicate b c) post
      (by simp [hrhd]) (by simp [hpre]) heq
    rcases pre with _ | ⟨p, ps⟩
    · rw [List.nil_append] at h1; simp at h1
    · rw [List.cons_append, List.cons.injEq] at h1
      obtain ⟨rfl, rfl⟩ := h1
      refine ⟨ps, rfl, ?_⟩
      rw [hv, ← h2]
      simp only [config, List.cons_append, List.append_assoc, List.replicate_succ,
        List.nil_append]
  · -- odd rule: ℓ = [t, rhd, c], r = [d1, rhd]
    right
    rw [hu, List.count_append, List.count_append] at hcount
    have htr : ([t, rhd, c] : List ASym).count rhd = 1 := by decide
    have hpre : rhd ∉ pre := by rw [← List.count_eq_zero]; omega
    have heq : (lhd :: w) ++ rhd :: List.replicate b c = (pre ++ [t]) ++ rhd :: (c :: post) := by
      show config w b = (pre ++ [t]) ++ rhd :: (c :: post)
      rw [hu]; simp [List.append_assoc]
    obtain ⟨h1, h2⟩ := append_cons_inj rhd (lhd :: w) (pre ++ [t]) (List.replicate b c) (c :: post)
      (by simp [hrhd]) (by simp [hpre]) heq
    -- h2 : replicate b c = c :: post  ⟹  b = b' + 1, post = replicate b' c
    rcases b with _ | b'
    · simp at h2
    · rw [List.replicate_succ, List.cons.injEq] at h2
      obtain ⟨_, rfl⟩ := h2
      rcases pre with _ | ⟨p, ps⟩
      · rw [List.nil_append] at h1; simp at h1
      · rw [List.cons_append, List.cons.injEq] at h1
        obtain ⟨rfl, rfl⟩ := h1
        refine ⟨ps, b', rfl, rfl, ?_⟩
        rw [hv]
        simp only [config, List.cons_append, List.append_assoc, List.nil_append]

/-! ### The value of a configuration, and the faithful single dynamic step -/

/-- The **value** `a = Val(◁ w ▷ cᵇ)` a configuration represents, read off the digit string `w`:
since `◁(x) = 1`, `▷` and `c` are the identity, the value is `Γ_w(1) = compFun w 1`, independent of
the counter `b` and the evaluation point (`config_val`). -/
@[category API, AMS 68 11, ref "YAH", group "antihydra_srs"]
def cval (w : List ASym) : ℕ := compFun w 1

/-- The value of a configuration is `cval w`, independent of the counter `b` and of `x`. -/
@[category research solved, AMS 68 11, ref "YAH", group "antihydra_srs", formal_uses cval]
theorem config_val (w : List ASym) (b x : ℕ) : compFun (config w b) x = cval w := by
  rw [cfgVal, compFun_cons, compFun_append]
  simp [symFun, beta, compFun, cval]

/-- Appending a digit `s` multiplies the value by `s`'s base and adds its digit: `cval (w ++ [s]) =
β_s(cval w) = symFun s (cval w)` (the new symbol is applied outermost). -/
@[category research solved, AMS 68 11, ref "YAH", group "antihydra_srs", formal_uses cval]
theorem cval_snoc (w : List ASym) (s : ASym) : cval (w ++ [s]) = symFun s (cval w) := by
  simp only [cval, compFun_append]; rfl

/-- A digit string `w ++ [s]` has digit prefix `w`. -/
@[category API, AMS 68, ref "YAH", group "antihydra_srs"]
theorem IsDigits.of_snoc {w : List ASym} {s : ASym} (h : IsDigits (w ++ [s])) : IsDigits w :=
  fun u hu => h u (List.mem_append_left _ hu)

/-- Extending a digit string by another digit symbol keeps it a digit string. -/
@[category API, AMS 68, ref "YAH", group "antihydra_srs"]
theorem IsDigits.snoc {w : List ASym} {s : ASym} (hw : IsDigits w)
    (hs : s = f ∨ s = t ∨ s = d0 ∨ s = d1 ∨ s = d2) : IsDigits (w ++ [s]) := by
  intro u hu
  rcases List.mem_append.mp hu with hu | hu
  · exact hw u hu
  · rw [List.mem_singleton.mp hu]; exact hs

/-- **The faithful single dynamic step** ([YAH] Claim 1, dynamic half, config-faithful). A dynamic
rewrite from a configuration `config w b` lands on a configuration `config w' b'` that:
* advances the value by the Antihydra map, `cval w' = valStep (cval w)`;
* changes the counter by an amount **forced by the parity of the value** — `+2` exactly when
  `cval w` is even (the even rule `f▷ → d0▷cc` fired), `−1` exactly when `cval w` is odd (the odd
  rule `t▷c → d1▷` fired, consuming one `c`).

This is the structural fact missing from the soundness layer: the *rule that fires* (hence the
counter increment) is determined by `cval w`'s parity, not by the rewriting strategy. -/
@[category research solved, AMS 68 11, ref "YAH", group "antihydra_srs",
  formal_uses dynStep_config_dest cval_snoc IsDigits.snoc IsDigits.of_snoc]
theorem dynStep_config (w : List ASym) (b : ℕ) (hw : IsDigits w) (v : List ASym)
    (h : RewriteStep dynRules (config w b) v) :
    ∃ w' b', v = config w' b' ∧ IsDigits w' ∧ cval w' = valStep (cval w) ∧
      (cval w % 2 = 0 ∧ b' = b + 2 ∨ cval w % 2 = 1 ∧ b = b' + 1) := by
  rcases dynStep_config_dest w b hw v h with ⟨w', rfl, rfl⟩ | ⟨w', b', rfl, rfl, rfl⟩
  · refine ⟨w' ++ [d0], b + 2, rfl, hw.of_snoc.snoc (by decide), ?_, Or.inl ⟨?_, rfl⟩⟩
    · rw [cval_snoc, cval_snoc]; simp only [symFun, beta]; unfold valStep; omega
    · rw [cval_snoc]; simp only [symFun, beta]; omega
  · refine ⟨w' ++ [d1], b', rfl, hw.of_snoc.snoc (by decide), ?_, Or.inr ⟨?_, rfl⟩⟩
    · rw [cval_snoc, cval_snoc]; simp only [symFun, beta]; unfold valStep; omega
    · rw [cval_snoc]; simp only [symFun, beta]; omega

/-! ### Config-structure invariant under the auxiliary rules

The auxiliary (transport/boundary) rules never disturb a configuration's shape `◁ w ▷ cᵇ`: a
transport redex (two digit symbols, no markers) sits inside the digit block `w` (`config_infix_locate`),
and a boundary redex `◁ d` sits at the head (`config_headB_locate`). So an aux step rewrites `w` to a
new digit string `w'` and leaves the counter `b` untouched (`auxStep_config_dest`). This is the
structural invariant that, together with `dynStep_config`, lets a whole derivation be read as the
macro orbit. -/

/-- **Marker-avoiding infix locator.** A factor `mid` that contains no marker (`◁`,`▷`) and no counter
`c`, and is nonempty, occurring in a configuration `config w b`, must sit entirely inside the digit
block `w`: `pre = ◁ wp`, `post = wq ▷ cᵇ`, and `w = wp ++ mid ++ wq`. -/
@[category research solved, AMS 68, ref "YAH", group "antihydra_srs",
  formal_uses append_cons_inj count_rhd_config]
theorem config_infix_locate (w : List ASym) (b : ℕ) (hw : rhd ∉ w) {pre mid post : List ASym}
    (hmidrhd : rhd ∉ mid) (hmidc : c ∉ mid) (hmidlhd : lhd ∉ mid) (hne : mid ≠ [])
    (heq : config w b = pre ++ mid ++ post) :
    ∃ wp wq, pre = lhd :: wp ∧ post = wq ++ rhd :: List.replicate b c ∧ w = wp ++ mid ++ wq := by
  obtain ⟨mh, mt, rfl⟩ : ∃ mh mt, mid = mh :: mt := by
    cases mid with
    | nil => exact absurd rfl hne
    | cons mh mt => exact ⟨mh, mt, rfl⟩
  have hcfg : config w b = lhd :: (w ++ rhd :: List.replicate b c) := rfl
  cases pre with
  | nil =>
    exfalso
    rw [List.nil_append, hcfg, List.cons_append, List.cons.injEq] at heq
    exact hmidlhd (by simp [heq.1])
  | cons ph pre' =>
    rw [hcfg] at heq
    simp only [List.cons_append, List.cons.injEq] at heq
    obtain ⟨rfl, heq2⟩ := heq
    -- heq2 : w ++ rhd :: replicate b c = pre' ++ (mh :: mt) ++ post
    have hcount : (pre' ++ (mh :: mt) ++ post).count rhd = 1 := by
      rw [← heq2, List.count_append, List.count_eq_zero.mpr hw, List.count_cons_self,
          List.count_replicate]; simp
    have hrhd_in : rhd ∈ post := by
      have hin : rhd ∈ pre' ++ (mh :: mt) ++ post := by rw [← heq2]; simp
      rcases List.mem_append.mp hin with hp | hpost
      · rcases List.mem_append.mp hp with hpre' | hmid
        · exfalso
          obtain ⟨qA, qB, rfl⟩ := List.append_of_mem hpre'
          have heq3 : w ++ rhd :: List.replicate b c
              = qA ++ rhd :: (qB ++ (mh :: mt) ++ post) := by rw [heq2]; simp [List.append_assoc]
          have hcountqA : qA.count rhd = 0 := by
            simp only [List.count_append, List.count_cons_self,
              List.count_eq_zero.mpr hmidrhd] at hcount ⊢; omega
          obtain ⟨_, hrep⟩ := append_cons_inj rhd w qA (List.replicate b c)
            (qB ++ (mh :: mt) ++ post) hw (List.count_eq_zero.mp hcountqA) heq3
          have hmem : mh ∈ List.replicate b c := by rw [hrep]; simp
          rw [List.eq_of_mem_replicate hmem] at hmidc
          exact hmidc (by simp)
        · exact absurd hmid hmidrhd
      · exact hpost
    obtain ⟨pA, pB, rfl⟩ := List.append_of_mem hrhd_in
    have heq3 : w ++ rhd :: List.replicate b c
        = (pre' ++ (mh :: mt) ++ pA) ++ rhd :: pB := by rw [heq2]; simp [List.append_assoc]
    have hcountL : (pre' ++ (mh :: mt) ++ pA).count rhd = 0 := by
      simp only [List.count_append, List.count_cons_self,
        List.count_eq_zero.mpr hmidrhd] at hcount ⊢; omega
    obtain ⟨hwL, hrep⟩ := append_cons_inj rhd w (pre' ++ (mh :: mt) ++ pA) (List.replicate b c) pB
      hw (List.count_eq_zero.mp hcountL) heq3
    exact ⟨pre', pA, rfl, by rw [hrep], hwL⟩

/-- **Boundary-redex locator.** A boundary redex `◁ d` (begin marker followed by a digit `d ≠ ▷`)
occurring in `config w b` sits at the head: `pre = []`, `w = d :: wrest`, `post = wrest ▷ cᵇ`. -/
@[category research solved, AMS 68, ref "YAH", group "antihydra_srs"]
theorem config_headB_locate (w : List ASym) (b : ℕ) (hw : IsDigits w) {dk : ASym}
    (hdk : dk ≠ rhd) {pre post : List ASym} (heq : config w b = pre ++ [lhd, dk] ++ post) :
    pre = [] ∧ ∃ wrest, w = dk :: wrest ∧ post = wrest ++ rhd :: List.replicate b c := by
  have hcfg : config w b = lhd :: (w ++ rhd :: List.replicate b c) := rfl
  have hlhd : lhd ∉ w ++ rhd :: List.replicate b c := by
    simp only [List.mem_append, List.mem_cons, List.mem_replicate]
    push Not
    exact ⟨hw.lhd_not_mem, by decide, fun _ => by decide⟩
  cases pre with
  | cons ph pre' =>
    exfalso
    rw [hcfg] at heq
    simp only [List.cons_append, List.cons.injEq] at heq
    obtain ⟨rfl, heq2⟩ := heq
    exact hlhd (by rw [heq2]; simp)
  | nil =>
    refine ⟨rfl, ?_⟩
    rw [List.nil_append, hcfg,
      show ([lhd, dk] : List ASym) ++ post = lhd :: dk :: post from rfl, List.cons.injEq] at heq
    obtain ⟨-, heq2⟩ := heq
    -- heq2 : w ++ rhd :: replicate b c = dk :: post
    cases w with
    | nil =>
      rw [List.nil_append, List.cons.injEq] at heq2
      exact absurd heq2.1.symm hdk
    | cons wh wrest =>
      rw [List.cons_append, List.cons.injEq] at heq2
      obtain ⟨rfl, rfl⟩ := heq2
      exact ⟨wrest, rfl, rfl⟩

/-- **Config-structure invariant for the auxiliary rules.** Every value-preserving rewrite from a
configuration `config w b` (with `w` a digit string) lands on a configuration `config w' b` with the
*same counter* `b` and a digit string `w'`. (Transport rules rewrite inside `w`; boundary rules
rewrite the leading digit.) -/
@[category research solved, AMS 68, ref "YAH", group "antihydra_srs",
  formal_uses config_infix_locate config_headB_locate isDigits_replace]
theorem auxStep_config_dest (w : List ASym) (b : ℕ) (hw : IsDigits w) (v : List ASym)
    (h : RewriteStep auxRules (config w b) v) :
    ∃ w', IsDigits w' ∧ v = config w' b := by
  obtain ⟨pre, post, ℓ, r, hrule, hu, hv⟩ := h
  rcases hrule with hA | hB
  · -- transport rules: the redex `ℓ` is a marker-free digit pair, located inside `w`
    obtain ⟨hℓrhd, hℓc, hℓlhd, hℓne, hr⟩ :
        rhd ∉ ℓ ∧ c ∉ ℓ ∧ lhd ∉ ℓ ∧ ℓ ≠ [] ∧ IsDigits r := by
      rcases hA with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ <;>
        exact ⟨by decide, by decide, by decide, by decide, by intro s hs; fin_cases hs <;> decide⟩
    obtain ⟨wp, wq, hpre, hpost, hweq⟩ :=
      config_infix_locate w b hw.rhd_not_mem hℓrhd hℓc hℓlhd hℓne hu
    exact ⟨wp ++ r ++ wq, isDigits_replace (hweq ▸ hw) hr,
      by rw [hv, hpre, hpost]; simp [config, List.append_assoc]⟩
  · -- boundary rules: the redex `◁ d` is at the head
    obtain ⟨dk, rtl, hℓeq, hreq, hdk, hrtl⟩ :
        ∃ dk rtl, ℓ = [lhd, dk] ∧ r = lhd :: rtl ∧ dk ≠ rhd ∧ IsDigits rtl := by
      rcases hB with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ <;>
        exact ⟨_, _, rfl, rfl, by decide, by intro s hs; fin_cases hs <;> decide⟩
    obtain ⟨rfl, wrest, hweq, hpost⟩ := config_headB_locate w b hw hdk (hℓeq ▸ hu)
    refine ⟨rtl ++ wrest, ?_, ?_⟩
    · rw [hweq] at hw
      exact isDigits_append.mpr ⟨hrtl, fun s hs => hw s (List.mem_cons_of_mem dk hs)⟩
    · rw [hv, hreq, hpost]; simp [config, List.append_assoc]

/-! ### The faithful simulation: every derivation tracks the orbit and `counterZ` -/

/-- A rewrite by a union of systems is a rewrite by one of them. -/
@[category API, AMS 68, ref "BO93", group "antihydra_srs"]
theorem rewriteStep_union {α} {R S : System α} {u v : List α}
    (h : RewriteStep (System.union R S) u v) : RewriteStep R u v ∨ RewriteStep S u v := by
  obtain ⟨pre, post, ℓ, r, hrule, hu, hv⟩ := h
  rcases hrule with hR | hS
  · exact Or.inl ⟨pre, post, ℓ, r, hR, hu, hv⟩
  · exact Or.inr ⟨pre, post, ℓ, r, hS, hu, hv⟩

/-- **The Antihydra SRS faithfully simulates the macro orbit.** Every configuration reachable from a
starting configuration `config w₀ b₀` (with `w₀` a digit string) by *any* `antihydraSRS`-derivation
— i.e. by *any rewriting strategy* — is itself a configuration `config w b`, and its state
`(value, counter) = (cval w, b)` is exactly the orbit state after some number `k` of dynamic steps:
`cval w = valOrbit (cval w₀) k` and `b = counterZ b₀ (cval w₀) k`. So the counter, value, and the
remaining digit string are determined by the dynamic-step count `k` alone, *not* by the strategy.

Proof: induction on the derivation. Value-preserving steps keep `(cval, b, k)` (`auxStep_config_dest`
+ `auxRules_rewriteStep_preserve_value`); each dynamic step advances `cval` by `valStep` and the
counter by the parity-forced amount (`dynStep_config`), which is exactly one step of `valOrbit` /
`counterZ`. -/
@[category research solved, AMS 68 11, ref "YAH", group "antihydra_srs",
  formal_uses rewriteStep_union dynStep_config auxStep_config_dest config_val]
theorem antihydraSRS_simulates (w₀ : List ASym) (b₀ : ℕ) (hw₀ : IsDigits w₀)
    {C : List ASym} (h : Relation.ReflTransGen (RewriteStep antihydraSRS) (config w₀ b₀) C) :
    ∃ k w b, C = config w b ∧ IsDigits w ∧ cval w = valOrbit (cval w₀) k ∧
      (b : ℤ) = counterZ (b₀ : ℤ) (cval w₀) k := by
  induction h with
  | refl => exact ⟨0, w₀, b₀, rfl, hw₀, rfl, rfl⟩
  | tail _ hlast ih =>
    obtain ⟨k, w, b, rfl, hw, hcval, hcount⟩ := ih
    rcases rewriteStep_union hlast with hdyn | haux
    · obtain ⟨w', b', rfl, hw', hval', hpar⟩ := dynStep_config w b hw _ hdyn
      refine ⟨k + 1, w', b', rfl, hw', by rw [hval', hcval, valOrbit_succ], ?_⟩
      rw [counterZ_succ, ← hcount, ← hcval]
      rcases hpar with ⟨hev, rfl⟩ | ⟨hodd, hb⟩
      · rw [if_pos hev]; push_cast; ring
      · rw [if_neg (by omega), hb]; push_cast; ring
    · obtain ⟨w', hw', rfl⟩ := auxStep_config_dest w b hw _ haux
      refine ⟨k, w', b, rfl, hw', ?_, hcount⟩
      have hval : compFun (config w b) 0 = compFun (config w' b) 0 :=
        auxRules_rewriteStep_preserve_value _ _ haux 0
      rw [config_val, config_val] at hval
      rw [← hval]; exact hcval

/-- **Strategy-independence of the counter after the `j`-th odd step (faithful form).** Along *any*
`antihydraSRS`-derivation from `config w₀ b₀`, a reachable configuration is `config w b` whose counter
satisfies `b = b₀ + 2k − 3j`, where `k` is the dynamic-step count and `j = oddSteps … k` the number of
odd steps so far — a value fixed by the deterministic orbit, hence the same for every strategy. This
is the lightweight `counterZ_after_jth_odd` upgraded to actual SRS derivations. -/
@[category research solved, AMS 68 11, ref "YAH", group "antihydra_srs",
  formal_uses antihydraSRS_simulates counterZ_after_jth_odd]
theorem counter_strategy_independent (w₀ : List ASym) (b₀ : ℕ) (hw₀ : IsDigits w₀)
    {C : List ASym} (h : Relation.ReflTransGen (RewriteStep antihydraSRS) (config w₀ b₀) C) :
    ∃ (k : ℕ) (w : List ASym) (b : ℕ), C = config w b ∧
      (b : ℤ) = (b₀ : ℤ) + 2 * (k : ℤ) - 3 * (oddSteps (cval w₀) k : ℤ) := by
  obtain ⟨k, w, b, hC, _, _, hb⟩ := antihydraSRS_simulates w₀ b₀ hw₀ h
  exact ⟨k, w, b, hC,
    by rw [hb]; exact counterZ_after_jth_odd (b₀ : ℤ) (cval w₀) k (oddSteps (cval w₀) k) rfl⟩

end StringRewriting.AntihydraSRS
