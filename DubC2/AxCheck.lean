/-
(C) 2026 Ralf Stephan, in collaboration with Claude Code.
Released under CC0 1.0 Universal (public-domain dedication).
See https://creativecommons.org/publicdomain/zero/1.0/
-/
import DubC2.Nearest
import DubC2.Calibration53
import DubC2.Calibration75
import DubC2.CalibrationFloor32
import DubC2.Obstruction
import DubC2.Budget
import DubC2.OdaBridge
import DubC2.ObstructionAtlas
import DubC2.Atlas
import DubC2.ShiftSchema
import DubC2.Blocks
import DubC2.ObstructionTwo
import DubC2.Mirror
import DubC2.HorseshoeAtlas
import DubC2.HorseshoeFrontier
import DubC2.BranchFrontier
import DubC2.Follower
import DubC2.FollowerAtlas
import DubC2.FollowerLiteral
import DubC2.FollowerOpen
import DubC2.NuAtlas
import DubC2.FirstHitAtlas
import DubC2.ResidueTargets
import DubC2.EntropyAtlas

/-!
# Axiom hygiene for the `DubC2` root

Milestone M3's exit condition (`plans/plan-dubC2.html` §7): every claimed declaration depends
on the standard three axioms `propext, Classical.choice, Quot.sound` and nothing else — no
cited literature axiom, no `native_decide`, no `sorry`.  Rebuild this module to check.

The one imported result that could have been an axiom is not: [DN05] Lemma 2 is *proved* in
`Z32/DubickasWord.lean` (`Z32.not_isEventuallyPeriodic_carry`), so the whole chain is
axiom-free in the corpus sense.
-/

-- The capstone at `3/2`, `ν = 1/2`, `𝒫 = {2,5}`
#print axioms DubC2.round_divisor_set
#print axioms DubC2.round_divisor_set_mem
#print axioms DubC2.infinite_dvd_two_or_five
#print axioms DubC2.round_composite

-- The certificate chain
#print axioms DubC2.exists_not_avoids
#print axioms DubC2.isEventuallyPeriodic_sN
#print axioms DubC2.funnel
#print axioms DubC2.cycle
#print axioms DubC2.seed

-- The model layer
#print axioms DubC2.xN_eq_round
#print axioms DubC2.stepA
#print axioms DubC2.stepB

-- The T3 calibration at `5/3`, `ν = 1/2`, `𝒫 = {2,3}` ([DN05] Thm 4(ii))
#print axioms DubC2.round_divisor_set_five_thirds
#print axioms DubC2.round_composite_five_thirds
#print axioms DubC2.isEventuallyPeriodic_s53
#print axioms DubC2.cycle53_four
#print axioms DubC2.cycle53_two
#print axioms DubC2.y53_lt_or_ge

-- The T3 calibration at `7/5`, `ν = 1/2`, `𝒫 = {2,3,5,11}` ([DN05] Thm 4(iii))
#print axioms DubC2.round_divisor_set_seven_fifths
#print axioms DubC2.round_divisor_set_mem_seven_fifths
#print axioms DubC2.round_composite_seven_fifths
#print axioms DubC2.isEventuallyPeriodic_s75
#print axioms DubC2.s75_mem
#print axioms DubC2.res3_succ
#print axioms DubC2.s75_AC
#print axioms DubC2.s75_BD
#print axioms DubC2.data_AC
#print axioms DubC2.data_BD

-- ... and the abstract `A,C` core it rests on
#print axioms DubC2.AC.isEventuallyPeriodic
#print axioms DubC2.AC.threeStep
#print axioms DubC2.AC.three_of_ge
#print axioms DubC2.AC.peel
#print axioms DubC2.AC.cycleV
#print axioms DubC2.AC.cycleU
#print axioms DubC2.AC.cycleACC

-- The T3 calibration at floor-`3/2`, `𝒫 = {2,5,7,11}` ([FS67] = [DN05] Thm 1 at `3/2`)
#print axioms DubC2.floor_divisor_set_three_halves
#print axioms DubC2.floor_composite_three_halves
#print axioms DubC2.data_floor
#print axioms DubC2.noAA_floor
#print axioms DubC2.FS.isEventuallyPeriodic
#print axioms DubC2.FS.periodic8
#print axioms DubC2.FS.periodic16

-- [Oda26] Lemma 38 / Theorem 42 / Corollary 43 for `Gen.Checked` (`DubC2/Obstruction.lean`)
#print axioms DubC2.Gen.PseudoOrbit.eventuallyPeriodic
#print axioms DubC2.Gen.not_checked_of_two_letters
#print axioms DubC2.Gen.not_checked_floor_internal

-- [Oda26] Theorem 42 (28) / Theorem 44 / Corollary 45 for floor certificates (`DubC2/Budget.lean`)
#print axioms DubC2.Gen.not_checked_floor_of_letter
#print axioms DubC2.Gen.p_le_jacobsthal
#print axioms DubC2.Gen.p_le_three_pow
#print axioms DubC2.Gen.p_le_four_mul_R
#print axioms DubC2.Gen.p_le_six_mul_R
#print axioms DubC2.Gen.exists_bound_of_R
#print axioms Oda.jacobsthal_prod_le
#print axioms Oda.jacobsthal_mul_primes
#print axioms DubC2.Gen.allPer_of_checked
#print axioms DubC2.Gen.allCert_of_checked
#print axioms DubC2.Gen.first_hit_of_checked
#print axioms DubC2.Gen.not_checked_of_witnessOK
#print axioms DubC2.Gen.not_checked_two_of_int
#print axioms DubC2.Gen.not_checked_three_of_int
#print axioms DubC2.Mirror.xInt_mirror
#print axioms DubC2.Mirror.eventually_fract_ne
#print axioms DubC2.Mirror.frequently_mirror_iff
#print axioms DubC2.Mirror.divisor_set_mirror_of_checked
#print axioms DubC2.Mirror.six_fifths_two_three_five_mirror
#print axioms DubC2.Mirror.Pseudo.mirror
#print axioms DubC2.Gen.not_checked_of_horseOK
#print axioms DubC2.Gen.not_checked_of_horseRow
#print axioms DubC2.Gen.HorseAtlas.b7_6_num1_killed
#print axioms DubC2.Gen.HorseAtlas.b7_6_nu0_killed
#print axioms DubC2.Gen.HorseAtlas.b7_6_nu1_2_killed
#print axioms DubC2.Gen.HorseAtlas.b6_5_nu0_killed
#print axioms DubC2.Gen.HorseAtlas.b6_5_nu1_2_killed
#print axioms DubC2.Gen.HorseFrontier.b5_4_nu0_P2_3_5_7_13_17_killed
#print axioms DubC2.Gen.HorseFrontier.b5_4_num1_P2_3_5_7_11_17_killed
#print axioms DubC2.Gen.HorseFrontier.b5_4_num1_P2_3_5_7_13_17_killed
#print axioms DubC2.Gen.HorseFrontier.b5_4_num1_P2_3_7_11_13_17_killed
#print axioms DubC2.Gen.HorseFrontier.b5_4_nu1_2_P2_3_5_7_11_13_17_killed
#print axioms DubC2.Gen.PseudoOrbit.step_of
#print axioms DubC2.Gen.rs_av_of_blocks
#print axioms DubC2.Gen.Branch.realize
#print axioms DubC2.Gen.Branch.exists_path_of_forall
#print axioms DubC2.Gen.not_checked_of_branchOK
#print axioms DubC2.Gen.not_checked_of_branchRow
#print axioms DubC2.Gen.BranchFrontier.b5_4_nu0_P2_3_5_7_13_17_branch
#print axioms DubC2.Gen.BranchFrontier.b5_4_num1_P2_3_5_7_11_17_branch
#print axioms DubC2.Gen.BranchFrontier.b5_4_num1_P2_3_5_7_13_17_branch
#print axioms DubC2.Gen.BranchFrontier.b5_4_num1_P2_3_7_11_13_17_branch
-- T5(iv) sufficiency: a finite non-branching follower automaton is certified
#print axioms DubC2.Gen.Follower.checked_of_family
#print axioms DubC2.Gen.Follower.succ_live
#print axioms DubC2.Gen.Follower.succ_dead
#print axioms DubC2.Gen.Follower.exists_checked
#print axioms DubC2.Gen.Follower.exists_checked_DF
#print axioms DubC2.Gen.Follower.exists_rep_fix
#print axioms DubC2.Gen.Follower.exists_branchOK
#print axioms DubC2.Gen.Follower.not_checked_of_branching
#print axioms DubC2.Gen.Follower.checked_iff
#print axioms DubC2.Gen.Follower.letter_mem
#print axioms DubC2.Gen.Follower.not_polyGrowth_of_branching
#print axioms DubC2.Gen.Follower.card_words_le
#print axioms DubC2.Gen.Follower.polyGrowth_iff
#print axioms DubC2.Gen.Follower.T5iv
#print axioms DubC2.Gen.HorseAtlas.b5_4_num1_killed
#print axioms DubC2.Gen.HorseAtlas.b5_4_nu0_killed
#print axioms DubC2.Gen.HorseAtlas.b5_4_nu1_2_killed
#print axioms DubC2.Gen.HorseAtlas.b9_7_num1_killed
#print axioms DubC2.Gen.HorseAtlas.b9_7_nu0_killed
#print axioms DubC2.Gen.HorseAtlas.b9_7_nu1_2_killed
#print axioms DubC2.Gen.HorseAtlas.b7_5_num1_killed
#print axioms DubC2.Gen.HorseAtlas.b7_5_nu0_killed
#print axioms DubC2.Gen.HorseAtlas.b10_7_num1_killed
#print axioms DubC2.Gen.HorseAtlas.b10_7_nu0_killed
#print axioms DubC2.Gen.HorseAtlas.b10_7_nu1_2_killed
#print axioms DubC2.Gen.HorseAtlas.b11_7_num1_killed
#print axioms DubC2.Gen.HorseAtlas.b11_7_nu0_killed
#print axioms DubC2.Gen.HorseAtlas.b11_7_nu1_2_killed
#print axioms DubC2.Gen.HorseAtlas.b8_5_num1_killed
#print axioms DubC2.Gen.HorseAtlas.b8_5_nu0_killed
#print axioms DubC2.Gen.HorseAtlas.b8_5_nu1_2_killed
#print axioms DubC2.Gen.HorseAtlas.b5_3_num1_killed
#print axioms DubC2.Gen.HorseAtlas.b5_3_nu0_killed
#print axioms DubC2.Gen.HorseAtlas.b12_7_num1_killed
#print axioms DubC2.Gen.HorseAtlas.b12_7_nu0_killed
#print axioms DubC2.Gen.HorseAtlas.b12_7_nu1_2_killed
#print axioms DubC2.Gen.HorseAtlas.b7_4_num1_killed
#print axioms DubC2.Gen.HorseAtlas.b7_4_nu0_killed
#print axioms DubC2.Gen.HorseAtlas.b7_4_nu1_2_killed
#print axioms DubC2.Gen.HorseAtlas.b9_5_num1_killed
#print axioms DubC2.Gen.HorseAtlas.b9_5_nu0_killed
#print axioms DubC2.Gen.HorseAtlas.b9_5_nu1_2_killed
#print axioms DubC2.Gen.HorseAtlas.b11_6_num1_killed
#print axioms DubC2.Gen.HorseAtlas.b11_6_nu0_killed
#print axioms DubC2.Gen.HorseAtlas.b11_6_nu1_2_killed
#print axioms DubC2.Gen.HorseAtlas.b13_7_num1_killed
#print axioms DubC2.Gen.HorseAtlas.b13_7_nu0_killed
#print axioms DubC2.Gen.HorseAtlas.b13_7_nu1_2_killed
#print axioms DubC2.Gen.HorseAtlas.b9_4_num1_killed
#print axioms DubC2.Gen.HorseAtlas.b9_4_nu0_killed
#print axioms DubC2.Gen.HorseAtlas.b9_4_nu1_2_killed
#print axioms DubC2.Gen.HorseAtlas.b7_3_num1_killed
#print axioms DubC2.Gen.HorseAtlas.b7_3_nu0_killed
#print axioms DubC2.Gen.HorseAtlas.b7_3_nu1_2_killed
#print axioms DubC2.Gen.HorseAtlas.b5_2_nu0_killed
#print axioms DubC2.Gen.HorseAtlas.b8_3_num1_killed
#print axioms DubC2.Gen.HorseAtlas.b8_3_nu0_killed
#print axioms DubC2.Gen.HorseAtlas.b8_3_nu1_2_killed
#print axioms DubC2.Gen.HorseAtlas.b11_4_num1_killed
#print axioms DubC2.Gen.HorseAtlas.b11_4_nu0_killed
#print axioms DubC2.Gen.HorseAtlas.b11_4_nu1_2_killed
#print axioms DubC2.Gen.not_checked_of_row
#print axioms DubC2.Gen.ObsAtlas.b3_2_nu0_killed
#print axioms DubC2.Gen.ObsAtlas.b13_7_nu0_killed

-- The (p/q, ν, 𝒫) divisor-set atlas (M2): every minimal hit of the scan, primes ≤ 13, |𝒫| ≤ 4
#print axioms DubC2.Atlas.b3_2_nu1_2_P2_5
#print axioms DubC2.Atlas.b7_5_nu1_2_P2_3_5_11
#print axioms DubC2.Atlas.b3_2_num1_P2_3
#print axioms DubC2.Atlas.b4_3_num1_P2_3
#print axioms DubC2.Atlas.b3_2_num1_P2_7
#print axioms DubC2.Atlas.b6_5_num1_P2_3_5
#print axioms DubC2.Atlas.b4_3_nu0_P2_3_5
#print axioms DubC2.Atlas.b5_2_num1_P2_3_5
#print axioms DubC2.Atlas.b4_3_nu1_2_P2_5
#print axioms DubC2.Atlas.b5_3_nu1_2_P2_3
#print axioms DubC2.Atlas.b5_3_nu1_2_P2_5
#print axioms DubC2.Atlas.b3_2_nu0_P2_5_7_11
#print axioms DubC2.Atlas.b5_2_nu1_2_P2_3_7_11
#print axioms DubC2.Atlas.b3_2_nu0_P2_7_11_13
#print axioms DubC2.Atlas.b3_2_nu0_P3_5_7_11
#print axioms DubC2.Atlas.b7_5_nu1_2_P2_3_5_13
-- plan-dubC2-transform M1: the shift-interval schema at 3/2, {2,3}
#print axioms DubC2.Schema.carry_eventually_periodic
#print axioms DubC2.Schema.three_halves_two_three
#print axioms DubC2.Schema.three_halves_two_three_circle
#print axioms DubC2.Schema.three_halves_minus_one
#print axioms DubC2.Schema.carry_eventually_periodic4
#print axioms DubC2.Schema.four_thirds_two_three
#print axioms DubC2.Schema.four_thirds_minus_one
#print axioms DubC2.Schema.carry_eventually_periodic52
#print axioms DubC2.Schema.five_halves_two_five
#print axioms DubC2.Schema.carry_eventually_periodic65
#print axioms DubC2.Schema.six_fifths_two_three_five
#print axioms DubC2.Schema.six_fifths_minus_one
#print axioms DubC2.Schema.eventually_avoids_iff
#print axioms DubC2.Schema.isCoprime_prod_iff
#print axioms DubC2.Schema.carry_window
#print axioms DubC2.Schema.frequently_dvd_of_letters
#print axioms DubC2.Gen.Pseudo.eventually_word
#print axioms DubC2.Gen.Pseudo.not_artefact
#print axioms DubC2.Blocks.seven_fifths_two_three_five_thirteen
#print axioms DubC2.Blocks.floor_three_halves_two_seven_eleven_thirteen
#print axioms DubC2.Blocks.floor_three_halves_three_five_seven_eleven
#print axioms DubC2.Gen.Follower.rstep_prodR
#print axioms DubC2.Gen.Follower.checkF_sound
#print axioms DubC2.Gen.Follower.exists_checked_of_checkF
#print axioms DubC2.Gen.Follower.T5iv_of_checkF
#print axioms DubC2.Gen.Follower.eventuallyPeriodic_of_checked
#print axioms DubC2.Gen.Follower.not_injective_of_periodic
#print axioms DubC2.Gen.Follower.exists_injective_path
#print axioms DubC2.Gen.Follower.finite_of_checked
#print axioms DubC2.Gen.Follower.checked_iff_finite
#print axioms DubC2.Gen.Follower.exists_aperiodic_adm
#print axioms DubC2.Gen.Follower.int_of_hits
#print axioms DubC2.Gen.Follower.hits_finite
#print axioms DubC2.Gen.Follower.exists_aperiodic_pseudoOrbit
#print axioms DubC2.Gen.Follower.T5iv_literal
#print axioms DubC2.Gen.Follower.hits_finite_cop
#print axioms DubC2.Gen.Follower.gcd_dvd_of_two_hits
#print axioms DubC2.Gen.Follower.coprime_red
#print axioms DubC2.Gen.Follower.paramFacts_red
#print axioms DubC2.Gen.Follower.adm_red
#print axioms DubC2.Gen.Follower.pseudoOrbit_of_red
#print axioms DubC2.Gen.Follower.triv32_infinite
#print axioms DubC2.Gen.Follower.no_zero_entropy_obstruction_iff
#print axioms DubC2.FollowerAtlas.b7_5_nu0_P2_3_7_11_13
#print axioms DubC2.FollowerAtlas.b7_5_nu0_P2_3_7_11_13_T5iv
#print axioms DubC2.FollowerAtlas.b7_5_nu0_P2_3_5_11_13
#print axioms DubC2.FollowerAtlas.b7_5_nu0_P2_3_5_11_13_T5iv
#print axioms DubC2.FollowerAtlas.b5_4_num1_P2_3_5_7_11_13
#print axioms DubC2.FollowerAtlas.b5_4_num1_P2_3_5_7_11_13_T5iv
#print axioms DubC2.FollowerAtlas.b5_4_nu0_P2_3_7_11_13
#print axioms DubC2.FollowerAtlas.b5_4_nu0_P2_3_7_11_13_T5iv
#print axioms DubC2.FollowerAtlas.b7_5_nu0_P2_3_5_11_17
#print axioms DubC2.FollowerAtlas.b7_5_nu0_P2_3_5_11_17_T5iv
#print axioms DubC2.FollowerAtlas.b7_5_nu0_P2_3_7_11_17
#print axioms DubC2.FollowerAtlas.b7_5_nu0_P2_3_7_11_17_T5iv
#print axioms DubC2.FollowerAtlas.b5_4_nu0_P2_3_7_11_17
#print axioms DubC2.FollowerAtlas.b5_4_nu0_P2_3_7_11_17_T5iv
#print axioms DubC2.Gen.hullOK_spec
#print axioms DubC2.Gen.Nu.sound
#print axioms DubC2.Gen.divisor_set_of_checked_hull
#print axioms DubC2.Gen.xInt_add_int
#print axioms DubC2.Gen.frequently_of_circle
#print axioms DubC2.NuAtlas.b3_2_P2_5_iv1
#print axioms DubC2.NuAtlas.b3_2_P2_5_of_dom
#print axioms DubC2.NuAtlas.b3_2_P2_5_circle
#print axioms DubC2.Gen.rank_bound
#print axioms DubC2.Gen.le_of_escape
#print axioms DubC2.Gen.win_mem_core
#print axioms DubC2.Gen.window_bound
#print axioms DubC2.Gen.first_hit_rank
#print axioms DubC2.Atlas.b3_2_nu1_2_P2_5_first_hit
#print axioms DubC2.Atlas.b7_5_nu1_2_P2_3_5_11_first_hit
#print axioms DubC2.Atlas.b3_2_num1_P2_3_first_hit
#print axioms DubC2.Atlas.b4_3_num1_P2_3_first_hit
#print axioms DubC2.Atlas.b3_2_num1_P2_7_first_hit
#print axioms DubC2.Atlas.b6_5_num1_P2_3_5_first_hit
#print axioms DubC2.Atlas.b4_3_nu0_P2_3_5_first_hit
#print axioms DubC2.Atlas.b5_2_num1_P2_3_5_first_hit
#print axioms DubC2.Atlas.b4_3_nu1_2_P2_5_first_hit
#print axioms DubC2.Atlas.b5_3_nu1_2_P2_3_first_hit
#print axioms DubC2.Atlas.b5_3_nu1_2_P2_5_first_hit
#print axioms DubC2.Atlas.b3_2_nu0_P2_5_7_11_first_hit
#print axioms DubC2.Atlas.b5_2_nu1_2_P2_3_7_11_first_hit
#print axioms DubC2.Atlas.b3_2_nu0_P2_7_11_13_first_hit
#print axioms DubC2.Atlas.b3_2_nu0_P3_5_7_11_first_hit
#print axioms DubC2.Atlas.b7_5_nu1_2_P2_3_5_13_first_hit
#print axioms DubC2.Gen.hitsTargets_iff_shift
#print axioms DubC2.Gen.exists_crt_shift
#print axioms DubC2.Gen.hitsTargets_iff_exists_shift
#print axioms DubC2.Gen.hitsTargets_of_checked
#print axioms DubC2.Gen.not_eventually_modEq
#print axioms DubC2.Gen.frequently_modEq_one_of_neg_one
#print axioms DubC2.Atlas.floor_three_halves_one_mod_two_three
#print axioms DubC2.Atlas.floor_four_thirds_one_mod_two_three
#print axioms DubC2.Atlas.floor_one_mod_two_three_five
#print axioms DubC2.Atlas.floor_three_halves_not_eventually_unit
#print axioms DubC2.Atlas.floor_three_halves_not_eventually_mod_six
#print axioms DubC2.Gen.EntCert.card_dwords_le
#print axioms DubC2.Gen.EntCert.facts
#print axioms DubC2.Gen.EntCert.dcount_le
#print axioms DubC2.Gen.EntCert.card_dwords_zero_le
#print axioms DubC2.Gen.cword_succ
#print axioms DubC2.Gen.xs_add_eq_runX
#print axioms DubC2.Gen.cword_mem
#print axioms DubC2.Gen.abs_sub_ctr_le
#print axioms DubC2.Gen.upperBoxDim_avoiders_le
#print axioms DubC2.Gen.dimH_eventually_avoids_le
#print axioms DubC2.Atlas.log_div_log_le
#print axioms DubC2.Atlas.ent32_2_5_check
#print axioms DubC2.Atlas.ent32_2_5_7_check
#print axioms DubC2.Atlas.ent32_2_7_check
#print axioms DubC2.Atlas.floor_three_halves_avoid_two_five_dimH
#print axioms DubC2.Atlas.floor_three_halves_avoid_two_five_seven_dimH
#print axioms DubC2.Atlas.floor_three_halves_avoid_two_seven_dimH
