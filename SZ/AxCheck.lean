/-
(C) 2026 Ralf Stephan, in collaboration with Claude Code.
Released under CC0 1.0 Universal (public-domain dedication).
See https://creativecommons.org/publicdomain/zero/1.0/
-/
import SZ.Classification
import SZ.QuadraticDesign
import SZ.SqrtThree
import SZ.CoverTree
import SZ.SqrtTwo
import SZ.Cells
import SZ.ThmC

/-!
# Axiom hygiene for the `SZ` root

`plans/plan-dubD1.html` §6.2: every claimed declaration depends on the standard three
axioms `propext, Classical.choice, Quot.sound` and nothing else — no cited literature
axiom, no `native_decide`, no `sorry`.  Rebuild this module to check.

Nothing in `SZ/` is imported from the literature: the four `𝒵` cells and the one `𝒮` cell
of Theorem B are all proved here, so the classification carries no citation.  The same
holds for `plans/plan-dubD1O5.html`'s chain (`SZ/DigitParity.lean`, `SZ/CoverGame.lean`,
`SZ/SqrtThree.lean`): the Cover Lemma is reproved rather than cited to [Utz51], and
lemma L1 is proved outright, so `SZ.sqrtThree_mem_MahlerZ` is unconditional.
-/

-- Definitions and tail closure
#print axioms SZ.mem_MahlerZ_of_eventually
#print axioms SZ.mem_MahlerZ_of_floor_eq
#print axioms SZ.natCast_mem_MahlerZ

-- The trace engine
#print axioms SZ.rec2_real
#print axioms SZ.rec2_even
#print axioms SZ.rec2_dvd_sub

-- The design
#print axioms SZ.floorNeg
#print axioms SZ.dvd_floor_of_neg
#print axioms SZ.mem_MahlerZ_of_neg
#print axioms SZ.mem_MahlerZ_of_pos

-- Theorem A: the headline
#print axioms SZ.silver_pair
#print axioms SZ.floor_silver
#print axioms SZ.floor_silver_pell
#print axioms SZ.silver_mem_MahlerZ
#print axioms SZ.even_floor_silver
#print axioms SZ.fract_silver

-- The Tijdeman engine (report §D.6)
#print axioms SZ.floor_greedy
#print axioms SZ.mem_MahlerZ_of_three_le

-- The confinement cell
#print axioms SZ.strace_emod
#print axioms SZ.floor_oneAddSqrtThree
#print axioms SZ.oneAddSqrtThree_mem_MahlerZ

-- The `𝒮` side
#print axioms SZ.golden_mem_S

-- Theorem B: the classification
#print axioms SZ.quadPisot_mem_MahlerZ
#print axioms SZ.quadPisot_mem_S_iff
#print axioms SZ.quadPisot_notMem_S_of_two_lt
#print axioms SZ.isQuadPisot_silver
#print axioms SZ.isQuadPisot_golden

-- Theorem C: designed congruences (report §D.4)
#print axioms SZ.eventually_composite
#print axioms SZ.twoAddSqrtFive_mem_MahlerZ
#print axioms SZ.threeAddSqrtTen_mem_MahlerZ
#print axioms SZ.three_dvd_floor_sqrtTen
#print axioms SZ.six_dvd_floor_sqrtTen
#print axioms SZ.eventually_composite_sqrtTen

-- Lemma D and the digit-stream API (plan dubD1O5 §1.1)
#print axioms SZ.digitSum_le_of_le
#print axioms SZ.digitReal_lt_digitSum_add
#print axioms SZ.floor_add_digitReal_mul_pow
#print axioms SZ.even_floor_add_digitReal_mul_pow
#print axioms SZ.digitReal_compl
#print axioms SZ.digitReal_two_eq_zero

-- The cover game and lemma L1 (plan dubD1O5 §1.3, §1.6)
#print axioms SZ.pick_residual_mem
#print axioms SZ.W_mem
#print axioms SZ.coverState_snd_lower
#print axioms SZ.eq_fixed_of_trapped
#print axioms SZ.exists_digitA_eq_zero
#print axioms SZ.exists_digitB_eq_two
#print axioms SZ.digitReal_translate

-- Theorem A: [Dub06EO] Problem 3 (plan dubD1O5 §1.4)
#print axioms SZ.coupling
#print axioms SZ.even_floor_even_case
#print axioms SZ.even_floor_odd_case
#print axioms SZ.sqrtThree_mem_MahlerZ
#print axioms SZ.sqrtThree_notMem_S
#print axioms SZ.floor_witXi_sqrtThree
#print axioms SZ.floor_witXi_three

-- Theorem 9.1 of `paper-dubD1O5.tex`: the witness set has cardinality `2^ℵ₀`
-- (plan dubD1O5 M4 addendum; `SZ/CoverTree.lean`)
#print axioms SZ.runVal_mem
#print axioms SZ.runState_snd_lower
#print axioms SZ.gExists_fst_eq_zero
#print axioms SZ.gExists_snd_eq_two
#print axioms SZ.gExists_inO
#print axioms SZ.branchDigit_adm
#print axioms SZ.tree_isRun
#print axioms SZ.tree_exists_branching
#print axioms SZ.tree_exists_fst_eq_zero
#print axioms SZ.tree_exists_snd_eq_two
#print axioms SZ.run_translate
#print axioms SZ.run_even_floor
#print axioms SZ.digitReal_ne
#print axioms SZ.exists_branch_at_used
#print axioms SZ.node_congr
#print axioms SZ.runXi_treeDigit_injective
#print axioms SZ.treeXi_mem
#print axioms SZ.continuum_le_mk_witnessSet
#print axioms SZ.not_countable_witnessSet
#print axioms SZ.exists_transcendental_mem_witnessSet
#print axioms SZ.exists_transcendental_witness_sqrtThree

-- Proposition 2.3 of `paper-dubD1O5.tex`: `√2 ∈ 𝒮`, the base-2 degeneracy
-- (`SZ/SqrtTwo.lean`; with `digitReal_two_eq_zero` above it is the `𝒮` side of Theorem B)
#print axioms SZ.floor_two_mul
#print axioms SZ.fract_lt_half
#print axioms SZ.fract_two_mul
#print axioms SZ.fract_eq_zero_of_even_floors
#print axioms SZ.eq_intCast_of_even_floors
#print axioms SZ.sqrtTwo_notMem_MahlerZ
#print axioms SZ.sqrtTwo_mem_S

-- The cells `m ∈ {5,6,7,8}` of Theorem B: the generic cover game (`SZ/Slice.lean`), tail
-- hygiene in the uniform case (`SZ/SliceHygiene.lean`), the four slices (`SZ/Cells.lean`)
#print axioms SZ.Slice.pick_adm
#print axioms SZ.Slice.bsel_eq_zero_iff
#print axioms SZ.Slice.W_mem
#print axioms SZ.Slice.digitReal_translate
#print axioms SZ.Slice.digitReal_compl'
#print axioms SZ.Slice.exists_translate
#print axioms SZ.Slice.dvd_floor_of_hygiene
#print axioms SZ.Slice.dvd_floor_of_e_le
#print axioms SZ.Slice.mem_MahlerZ_of_dvd
#print axioms SZ.Slice.mem_MahlerZ_of_hygiene
#print axioms SZ.Slice.mem_MahlerZ_of_e_le
#print axioms SZ.Slice.eq_fixed_of_trapped
#print axioms SZ.Slice.stt_val
#print axioms SZ.Slice.stt_snd_lower
#print axioms SZ.Slice.W_ne_val
#print axioms SZ.Slice.exists_dA_ne
#print axioms SZ.Slice.exists_dB_ne
#print axioms SZ.Slice.form_a
#print axioms SZ.Slice.form_b
#print axioms SZ.Slice.dvd_floor_of_uniform
#print axioms SZ.Slice.mem_MahlerZ_of_uniform
#print axioms SZ.sqrtFive_mem_MahlerZ
#print axioms SZ.sqrtSix_mem_MahlerZ
#print axioms SZ.sqrtSeven_mem_MahlerZ
#print axioms SZ.sqrtEight_mem_MahlerZ
#print axioms SZ.exists_mem_MahlerZ_Ioo_two_three
#print axioms SZ.sqrt_natCast_mem_MahlerZ
#print axioms SZ.sqrt_natCast_mem_S_iff

-- Theorem C of `paper-dubD1O5.tex`: divisibility by a general `p` (`SZ/ThmC.lean`),
-- together with the paper's Lemma 3.3 (`Slice.exists_translate`) and Proposition 5.4 at
-- `p ≥ 3` (`Slice.dvd_floor_of_uniform`)
#print axioms SZ.p_le_sqrt
#print axioms SZ.p_lt_sqrt
#print axioms SZ.sq_lt_of_window
#print axioms SZ.exists_dvd_floor_sqrt
#print axioms SZ.exists_eventually_composite_sqrt
#print axioms SZ.sqrt_mem_MahlerZ_of_four_le
#print axioms SZ.not_isSquare_of_bounded
#print axioms SZ.exists_three_dvd_floor_sqrt_ten
#print axioms SZ.exists_three_dvd_floor_sqrt_twelve
#print axioms SZ.exists_four_dvd_floor_sqrt_seventeen
#print axioms SZ.exists_five_dvd_floor_sqrt_twentySix
