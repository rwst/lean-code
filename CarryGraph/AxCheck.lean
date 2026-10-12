/-
(C) 2026 Ralf Stephan, in collaboration with Claude Code.
Released under CC0 1.0 Universal (public-domain dedication).
See https://creativecommons.org/publicdomain/zero/1.0/
-/
import CarryGraph.Affine
import CarryGraph.Basic
import CarryGraph.Core
import CarryGraph.Cover
import CarryGraph.Dimension
import CarryGraph.Flow
import CarryGraph.Follower
import CarryGraph.Growth
import CarryGraph.Horseshoe
import CarryGraph.Interval
import CarryGraph.Labelled
import CarryGraph.Language
import CarryGraph.Mirror
import CarryGraph.Path
import CarryGraph.Product
import CarryGraph.Quotient
import CarryGraph.Rank
import CarryGraph.Reach
import CarryGraph.Shift
import CarryGraph.Splitting
import CarryGraph.ZeroEntropy

/-! # Axiom audit of `CarryGraph/` — every theorem must be std3
(`propext`, `Classical.choice`, `Quot.sound`); no `sorryAx`, no `native_decide`.
Regenerate the list when a file is added. -/

-- Affine.lean
#print axioms CarryGraph.affStep_orbit
#print axioms CarryGraph.q_mul_floor_affStep
#print axioms CarryGraph.q_mul_affStep
#print axioms CarryGraph.fract_affStep
#print axioms CarryGraph.carry_window
#print axioms CarryGraph.carry_bounds
#print axioms CarryGraph.adj_residueGraph
#print axioms CarryGraph.resOK_intCast
#print axioms CarryGraph.cover_residueGraph
#print axioms CarryGraph.adj_blockGraph
#print axioms CarryGraph.cover_frac_of_blockArc
#print axioms CarryGraph.fract_semiconj
#print axioms CarryGraph.cover_blockGraph
#print axioms CarryGraph.exists_cell
#print axioms CarryGraph.cover_cellGraph
#print axioms CarryGraph.cover_affine
#print axioms CarryGraph.affine_rho_cover
#print axioms CarryGraph.realizes_blockGraph
#print axioms CarryGraph.continuous_orbit_fracStep
#print axioms CarryGraph.realizesInf_blockGraph
#print axioms CarryGraph.not_realizesInf_doubling
#print axioms CarryGraph.floor_run_eq
#print axioms CarryGraph.dimH_survivors_le
#print axioms CarryGraph.dimH_avoiders_le
-- Basic.lean
#print axioms CarryGraph.mem_out
#print axioms CarryGraph.ext'
#print axioms CarryGraph.adj_ofRel
#print axioms CarryGraph.adj_ofFinset
#print axioms CarryGraph.mem_arcs
#print axioms CarryGraph.ofFinset_arcs
#print axioms CarryGraph.arcs_ofFinset
#print axioms CarryGraph.adj_reverse
#print axioms CarryGraph.adj_restrict
#print axioms CarryGraph.adj_relabel
#print axioms CarryGraph.adj_forget
#print axioms CarryGraph.Hom.map_under
-- Core.lean
#print axioms CarryGraph.exists_ray
#print axioms CarryGraph.fwd_of_under
#print axioms CarryGraph.bwdIn_of_under
#print axioms CarryGraph.fwd_tail
#print axioms CarryGraph.bwdIn_tail
#print axioms CarryGraph.bwdIn_subset
#print axioms CarryGraph.fwd_greatest
#print axioms CarryGraph.bwdIn_greatest
#print axioms CarryGraph.two_stage
#print axioms CarryGraph.core_essential
#print axioms CarryGraph.subset_core_of_essential
#print axioms CarryGraph.mem_core_of_cyc
#print axioms CarryGraph.transGen_of_walk
#print axioms CarryGraph.exists_cyc_of_walk
#print axioms CarryGraph.npaths_pos_iff
#print axioms CarryGraph.hasWalk_of_fwd
#print axioms CarryGraph.core_eq_empty_iff
#print axioms CarryGraph.mem_peel
#print axioms CarryGraph.peel_antitone
#print axioms CarryGraph.peel_stable_of
#print axioms CarryGraph.exists_peel_stable
#print axioms CarryGraph.peel_eq_peel_card
#print axioms CarryGraph.hasWalk_card_iff
#print axioms CarryGraph.not_hasWalk_of_not_mem_peel
#print axioms CarryGraph.mem_fwdSet
#print axioms CarryGraph.bwdIn_univ_eq
#print axioms CarryGraph.mem_coreSet
#print axioms CarryGraph.core_eq_empty_iff_coreSet
#print axioms CarryGraph.IsPeelChain.walk_mem
#print axioms CarryGraph.IsPeelChain.core_subset
#print axioms CarryGraph.Functional.exists_period_of_walk
#print axioms CarryGraph.lnoBranch_of_functional
-- Cover.lean
#print axioms CarryGraph.orbit_succ'
#print axioms CarryGraph.AdmForever.tail
#print axioms CarryGraph.length_pre
#print axioms CarryGraph.pre_succ
#print axioms CarryGraph.AdmForever.follows
#print axioms CarryGraph.Cover.follows
#print axioms CarryGraph.Cover.isWord
#print axioms CarryGraph.Cover.exists_iPath
#print axioms CarryGraph.Cover.mono
#print axioms CarryGraph.Cover.mono_adm
#print axioms CarryGraph.Cover.comap
#print axioms CarryGraph.Cover.map
#print axioms CarryGraph.Cover.ofSimulation
#print axioms CarryGraph.Cover.lineGraph
#print axioms CarryGraph.Cover.labelProduct
#print axioms CarryGraph.Cover.piProduct
#print axioms CarryGraph.Cover.det
#print axioms CarryGraph.Cover.evPer_of_allPer
#print axioms CarryGraph.Cover.evPer_of_lnoBranch
#print axioms CarryGraph.Cover.evPer_of_det
#print axioms CarryGraph.Cover.not_allPer
#print axioms CarryGraph.Cover.not_allPer_of_horseshoe
#print axioms CarryGraph.Cover.not_lnoBranch_of_horseshoe
#print axioms CarryGraph.Cover.not_follows_of_not_hasWalk
#print axioms CarryGraph.Cover.escape_of_peel
#print axioms CarryGraph.Cover.escape_of_core_empty
#print axioms CarryGraph.Cover.not_admForever_of_core_empty
#print axioms CarryGraph.Cover.orbitWords_subset
#print axioms CarryGraph.Cover.ncard_orbitWords_le
#print axioms CarryGraph.Realizes.words_subset
#print axioms CarryGraph.Cover.orbitWords_eq
#print axioms CarryGraph.Cover.orbitLang_subset
#print axioms CarryGraph.Cover.ncard_orbitLang_le
#print axioms CarryGraph.Cover.orbitEntropy_le
#print axioms CarryGraph.Cover.orbitEntropy_eq
-- Dimension.lean
#print axioms CarryGraph.edist_le_of_follows
#print axioms CarryGraph.Cover.externalCoveringNumber_le
#print axioms CarryGraph.Cover.upperBoxDim_le
#print axioms CarryGraph.Cover.upperBoxDim_le_of_expanding
#print axioms CarryGraph.Cover.dimH_le
-- Flow.lean
#print axioms CarryGraph.IsCirculation.outflow_nonneg
#print axioms CarryGraph.IsCirculation.le_outflow
#print axioms CarryGraph.IsCirculation.le_inflow
#print axioms CarryGraph.IsCirculation.mem_flowSupp_of_pos
#print axioms CarryGraph.IsCirculation.essential
#print axioms CarryGraph.IsCirculation.supp_subset_core
#print axioms CarryGraph.IsCirculation.reach_of_pos
#print axioms CarryGraph.IsCirculation.cyc_of_pos
#print axioms CarryGraph.IsCirculation.sameSCC_of_pos
#print axioms CarryGraph.IsCirculation.eq_zero_of_not_cyc
#print axioms CarryGraph.IsCirculation.eq_of_pos_of_noBranch
#print axioms CarryGraph.IsCirculation.outflow_eq_of_noBranch
#print axioms CarryGraph.IsCirculation.noBranch_perm
#print axioms CarryGraph.sum_transits_out
#print axioms CarryGraph.sum_transits_in
#print axioms CarryGraph.abs_sum_transits_in_sub
#print axioms CarryGraph.sum_visits
#print axioms CarryGraph.empFlow_nonneg
#print axioms CarryGraph.empFlow_le_one
#print axioms CarryGraph.exists_circulation_of_walk
#print axioms CarryGraph.exists_circulation_avoiding
-- Follower.lean
#print axioms CarryGraph.reach_iff_exists_reads
#print axioms CarryGraph.adj_followerGraph
#print axioms CarryGraph.followerGraph_rightResolving
#print axioms CarryGraph.reads_followerGraph
#print axioms CarryGraph.langFrom_followerGraph
#print axioms CarryGraph.reach_followerGraph
#print axioms CarryGraph.leftQuotient_eq_empty
#print axioms CarryGraph.sofic_iff_finite_reach
#print axioms CarryGraph.exists_injective_of_not_sofic
#print axioms CarryGraph.RightResolving.reads_eq
#print axioms CarryGraph.langFrom_eq_leftQuotient
#print axioms CarryGraph.ncard_reach_le_of_rr
#print axioms CarryGraph.ncard_reach_le
#print axioms CarryGraph.allPer_of_followerGraph
-- Growth.lean
#print axioms CarryGraph.mem_arcsFrom
#print axioms CarryGraph.npaths_succ'
#print axioms CarryGraph.npaths_le_succ
#print axioms CarryGraph.npaths_add_le_succ
#print axioms CarryGraph.npaths_mono_of_reach
#print axioms CarryGraph.card_arcsFrom_le
#print axioms CarryGraph.npaths_le_of_isLRank
#print axioms CarryGraph.isLRank_polyGrowth
#print axioms CarryGraph.polyGrowth_of_lnoBranch
#print axioms CarryGraph.pow_le_npaths_of_branch
#print axioms CarryGraph.exists_pow_lt
#print axioms CarryGraph.polyGrowth_lnoBranch
#print axioms CarryGraph.polyGrowth_or_exp
#print axioms CarryGraph.npaths_le_ntot
#print axioms CarryGraph.expGrowthSup_poly_le
#print axioms CarryGraph.entropy_le_zero_of_polyGrowth
#print axioms CarryGraph.log_div_le_entropy
#print axioms CarryGraph.log_two_div_le_entropy
#print axioms CarryGraph.entropy_le_zero_iff
#print axioms CarryGraph.entropy_pos_iff
#print axioms CarryGraph.pow_mul_npaths_le
#print axioms CarryGraph.pow_mul_le_npaths
#print axioms CarryGraph.entropy_le_of_superEigen
#print axioms CarryGraph.log_le_entropy_of_subEigen
-- Horseshoe.lean
#print axioms CarryGraph.IsLWalk.cons
#print axioms CarryGraph.IsLWalk.append
#print axioms CarryGraph.exists_lWalk_of_reach
#print axioms CarryGraph.card_le_npaths
#print axioms CarryGraph.Horseshoe.div_mod_block
#print axioms CarryGraph.Horseshoe.blockS_block
#print axioms CarryGraph.Horseshoe.blockL_block
#print axioms CarryGraph.Horseshoe.blockS_block_succ
#print axioms CarryGraph.Horseshoe.isIPath
#print axioms CarryGraph.Horseshoe.blockS_zero
#print axioms CarryGraph.Horseshoe.eq_of_agree
#print axioms CarryGraph.Horseshoe.block_injective
#print axioms CarryGraph.Horseshoe.pow_le_npaths
#print axioms CarryGraph.Horseshoe.log_card_div_le_entropy
#print axioms CarryGraph.Horseshoe.isPow2_pow
#print axioms CarryGraph.Horseshoe.isPow2_of_lt
#print axioms CarryGraph.Horseshoe.isPow2_not_evPer
#print axioms CarryGraph.Horseshoe.periodic_iter
#print axioms CarryGraph.Horseshoe.exists_not_evPer
#print axioms CarryGraph.exists_horseshoe_of_branch
-- Interval.lean
#print axioms CarryGraph.adj_blockHull
#print axioms CarryGraph.blockArc_hull
#print axioms CarryGraph.adj_blockHull_iff
#print axioms CarryGraph.cover_blockHull
#print axioms CarryGraph.blockHull_mono
#print axioms CarryGraph.cover_affineHull
#print axioms CarryGraph.allPer_affine_mono
#print axioms CarryGraph.carry_window_of_interval
#print axioms CarryGraph.dimH_avoiders_le_hull
-- Labelled.lean
#print axioms CarryGraph.AllEvPer.allPer
#print axioms CarryGraph.allPer_of_hom
#print axioms CarryGraph.reach_of_ncard_eq
#print axioms CarryGraph.lnoBranch_isLRank_ncard
#print axioms CarryGraph.lnoBranch_iff_allEvPer
#print axioms CarryGraph.allPer_of_lnoBranch
#print axioms CarryGraph.RightResolving.eq
#print axioms CarryGraph.evPer_path_of_rr
#print axioms CarryGraph.lnoBranch_iff_allPer_of_rr
#print axioms CarryGraph.mem_detStep
#print axioms CarryGraph.detStep_empty
#print axioms CarryGraph.adj_det
#print axioms CarryGraph.det_rightResolving
#print axioms CarryGraph.ends_empty
#print axioms CarryGraph.isWord_det
#print axioms CarryGraph.isWord_det_singleton
#print axioms CarryGraph.words_det_singleton
#print axioms CarryGraph.isWord_det_empty
#print axioms CarryGraph.det_iPath_of_iPath
#print axioms CarryGraph.exists_forall_of_finset
#print axioms CarryGraph.exists_iPath_of_det
#print axioms CarryGraph.exists_iPath_of_forall_reads
#print axioms CarryGraph.allPer_det_iff
#print axioms CarryGraph.determinization
#print axioms CarryGraph.allPer_iff_polyGrowth_det
#print axioms CarryGraph.allPer_iff_entropy_det
#print axioms CarryGraph.allPer_iff_wordGrowth
#print axioms CarryGraph.allPer_of_graded
#print axioms CarryGraph.tube53_separates
#print axioms CarryGraph.diamond_separates
-- Language.lean
#print axioms CarryGraph.mem_langFrom
#print axioms CarryGraph.langFrom_prefixClosed
#print axioms CarryGraph.PrefixClosed.leftQuotient
#print axioms CarryGraph.mem_leftQuotient_langFrom
#print axioms CarryGraph.Hom.reads
#print axioms CarryGraph.langFrom_subset_of_hom
#print axioms CarryGraph.adj_transport
#print axioms CarryGraph.langFrom_transport
#print axioms CarryGraph.sofic_of_finite
#print axioms CarryGraph.sofic_of_finite_reach
#print axioms CarryGraph.Sofic.prefixClosed
#print axioms CarryGraph.langFrom_det_singleton
#print axioms CarryGraph.mem_evalFrom_toNFA
#print axioms CarryGraph.toNFA_accepts
#print axioms CarryGraph.toDFA_evalFrom_toNFA
#print axioms CarryGraph.Sofic.isRegular
#print axioms CarryGraph.sofic_of_isRegular
#print axioms CarryGraph.sofic_iff_isRegular_and_prefixClosed
#print axioms CarryGraph.sofic_iff
-- Mirror.lean
#print axioms CarryGraph.allPer_iff_of_adj_equiv
#print axioms CarryGraph.blockArc_mirror
#print axioms CarryGraph.cells_rev
#print axioms CarryGraph.letter_rev
#print axioms CarryGraph.adj_cellGraph_mirror
#print axioms CarryGraph.resOK_neg
#print axioms CarryGraph.adj_residueGraph_mirror
#print axioms CarryGraph.adj_affine_mirror
#print axioms CarryGraph.allPer_affine_mirror_iff
-- Path.lean
#print axioms CarryGraph.reads_nil
#print axioms CarryGraph.reads_cons
#print axioms CarryGraph.reads_append
#print axioms CarryGraph.isWord_nil
#print axioms CarryGraph.isWord_cons
#print axioms CarryGraph.IsWord.of_append
#print axioms CarryGraph.mem_ends
#print axioms CarryGraph.isWord_iff_ends_nonempty
#print axioms CarryGraph.npaths_zero
#print axioms CarryGraph.npaths_succ
#print axioms CarryGraph.mem_words
#print axioms CarryGraph.card_words_le_npaths
#print axioms CarryGraph.card_words_eq_npaths
#print axioms CarryGraph.Functional.rightResolving
#print axioms CarryGraph.Functional.npaths_le_one
#print axioms CarryGraph.Functional.iPath_eq
#print axioms CarryGraph.HasWalk.mono
#print axioms CarryGraph.hasWalk_iff
#print axioms CarryGraph.hasWalk_iff_exists_word
#print axioms CarryGraph.exists_succ_forall_hasWalk
#print axioms CarryGraph.exists_walk_of_forall_hasWalk
#print axioms CarryGraph.exists_iPath_of_forall_isWord
#print axioms CarryGraph.IsIPath.reads
#print axioms CarryGraph.IsIPath.isWalk
-- Product.lean
#print axioms CarryGraph.adj_labelProduct
#print axioms CarryGraph.reads_labelProduct
#print axioms CarryGraph.mem_langFrom_labelProduct
#print axioms CarryGraph.langFrom_labelProduct
#print axioms CarryGraph.Sofic.inter
#print axioms CarryGraph.rightResolving_labelProduct
#print axioms CarryGraph.allPer_labelProduct_left
#print axioms CarryGraph.allPer_labelProduct_right
#print axioms CarryGraph.core_labelProduct_left
#print axioms CarryGraph.core_labelProduct_right
#print axioms CarryGraph.detStep_labelProduct
#print axioms CarryGraph.npaths_labelProduct_le
#print axioms CarryGraph.fstHom_locInj
#print axioms CarryGraph.ntot_labelProduct_le
#print axioms CarryGraph.entropy_ne_top
#print axioms CarryGraph.entropy_labelProduct_le
#print axioms CarryGraph.entropy_labelProduct_le_left
#print axioms CarryGraph.lnoBranch_labelProduct
#print axioms CarryGraph.card_words_labelProduct_le
#print axioms CarryGraph.adj_piProduct
#print axioms CarryGraph.reads_piProduct
#print axioms CarryGraph.mem_langFrom_piProduct
#print axioms CarryGraph.rightResolving_piProduct
#print axioms CarryGraph.allPer_piProduct
#print axioms CarryGraph.detStep_piProduct
#print axioms CarryGraph.allPer_piProduct_mono
#print axioms CarryGraph.langFrom_piProduct_antitone
#print axioms CarryGraph.allPer_labelProduct_piProduct_mono
-- Quotient.lean
#print axioms CarryGraph.Hom.mem_fwd
#print axioms CarryGraph.Hom.mem_bwdIn_univ
#print axioms CarryGraph.Hom.mem_core
#print axioms CarryGraph.core_subset_preimage_core
#print axioms CarryGraph.Hom.core_eq_empty
#print axioms CarryGraph.cyc_mem_of_peelRank_of_hom
#print axioms CarryGraph.Hom.npaths_le
#print axioms CarryGraph.Hom.polyGrowth_of_locInj
#print axioms CarryGraph.Hom.entropy_le_of_locInj
#print axioms CarryGraph.Hom.lnoBranch_of_locInj
#print axioms CarryGraph.Hom.isSimulation
#print axioms CarryGraph.IsSimulation.reads
#print axioms CarryGraph.IsSimulation.langFrom_subset
#print axioms CarryGraph.IsSimulation.exists_iPath
#print axioms CarryGraph.allPer_of_simulation
#print axioms CarryGraph.allPer_of_peelChain
#print axioms CarryGraph.length_le_sdLen
#print axioms CarryGraph.sdPos_zero
#print axioms CarryGraph.sdPos_of_lt
#print axioms CarryGraph.sdPos_length
#print axioms CarryGraph.eq_zero_of_sdPos_eq_inl
#print axioms CarryGraph.sdPos_inj
#print axioms CarryGraph.adj_subdivide
#print axioms CarryGraph.sd_step_inr
#print axioms CarryGraph.sd_step_inl
#print axioms CarryGraph.reads_sdPos
#print axioms CarryGraph.reads_of_wReads
#print axioms CarryGraph.sdRest_sdPos
#print axioms CarryGraph.wReads_of_reads
#print axioms CarryGraph.reads_subdivide_iff
#print axioms CarryGraph.reads_eq_or_adj
#print axioms CarryGraph.reads_sdRest
#print axioms CarryGraph.mem_langFrom_subdivide
#print axioms CarryGraph.sofic_wordLang
#print axioms CarryGraph.eq_of_sdPos_one
#print axioms CarryGraph.lnoBranch_subdivide_iff
#print axioms CarryGraph.sd_follow
#print axioms CarryGraph.sd_arc
#print axioms CarryGraph.allPer_subdivide_iff
#print axioms CarryGraph.wAllPer_iff_det
-- Rank.lean
#print axioms CarryGraph.IsLRank.isRank
#print axioms CarryGraph.LNoBranch.noBranch
#print axioms CarryGraph.IsRank.eq_of_reach
#print axioms CarryGraph.IsRank.noBranch
#print axioms CarryGraph.IsLRank.lnoBranch
#print axioms CarryGraph.noBranch_isRank_desc
#print axioms CarryGraph.lnoBranch_isLRank_desc
#print axioms CarryGraph.exists_isRank_iff_noBranch
#print axioms CarryGraph.exists_isLRank_iff_lnoBranch
#print axioms CarryGraph.noBranch_isRank_ncard
#print axioms CarryGraph.IsRank.evPer'
#print axioms CarryGraph.IsRank.evPer
#print axioms CarryGraph.IsLRank.evPer
#print axioms CarryGraph.cyc_mem_of_peelRank_rel
#print axioms CarryGraph.cyc_mem_of_peelRank
#print axioms CarryGraph.transGen_swap
#print axioms CarryGraph.cyc_mem_of_peelRank_rev
#print axioms CarryGraph.noBranch_of_cyc_det
#print axioms CarryGraph.drops_add_le
-- Reach.lean
#print axioms CarryGraph.Reach.refl
#print axioms CarryGraph.Reach.single
#print axioms CarryGraph.Reach.trans
#print axioms CarryGraph.Reach.head
#print axioms CarryGraph.Reach.tail
#print axioms CarryGraph.SameSCC.refl
#print axioms CarryGraph.SameSCC.symm
#print axioms CarryGraph.SameSCC.trans
#print axioms CarryGraph.sameSCC_equivalence
#print axioms CarryGraph.cyc_iff
#print axioms CarryGraph.Cyc.of_sameSCC
#print axioms CarryGraph.Reach.restrict
#print axioms CarryGraph.Hom.reach_map
#print axioms CarryGraph.Hom.cyc_map
#print axioms CarryGraph.reachIn_succ'
#print axioms CarryGraph.reach_iff_exists_reachIn
#print axioms CarryGraph.ReachIn.isWalk
#print axioms CarryGraph.mem_ball
#print axioms CarryGraph.ball_mono
#print axioms CarryGraph.reach_of_mem_ball
#print axioms CarryGraph.mem_ball_of_stable
#print axioms CarryGraph.exists_ball_stable
#print axioms CarryGraph.mem_reachSet
#print axioms CarryGraph.reach_rank_le
#print axioms CarryGraph.mem_descSet
#print axioms CarryGraph.mem_predsSet
#print axioms CarryGraph.descSet_subset_of_reach
#print axioms CarryGraph.predsSet_subset_of_reach
#print axioms CarryGraph.desc_le_of_under
#print axioms CarryGraph.desc_eq_iff
#print axioms CarryGraph.desc_lt_of_not_reach
#print axioms CarryGraph.desc_le_card
#print axioms CarryGraph.preds_le_of_under
#print axioms CarryGraph.preds_ssubset
#print axioms CarryGraph.under_reverse
#print axioms CarryGraph.reach_reverse
#print axioms CarryGraph.desc_reverse
#print axioms CarryGraph.reachIn_dist
#print axioms CarryGraph.dist_le
#print axioms CarryGraph.dist_succ_le
#print axioms CarryGraph.under_geo
#print axioms CarryGraph.geo_reachIn
#print axioms CarryGraph.exists_injective_walk_of_infinite_reach
-- Shift.lean
#print axioms CarryGraph.reads_restrict_mem
#print axioms CarryGraph.isLanguage_blockWords
#print axioms CarryGraph.reads_of_biPath
#print axioms CarryGraph.language_labelShift
#print axioms CarryGraph.mem_labelShift_of_path
#print axioms CarryGraph.mem_core_of_biPath
#print axioms CarryGraph.mem_labelShift_core_of_path
#print axioms CarryGraph.adj_rauzy
#print axioms CarryGraph.under_rauzy
#print axioms CarryGraph.reach_rauzy
-- Splitting.lean
#print axioms CarryGraph.ereal_div_succ_le
#print axioms CarryGraph.expGrowthSup_shift
#print axioms CarryGraph.npaths_sink
#print axioms CarryGraph.npaths_succ_le_ntot
#print axioms CarryGraph.ntot_succ_le
#print axioms CarryGraph.ntot_eq_zero_of_le
#print axioms CarryGraph.core_eq_empty_iff_ntot
#print axioms CarryGraph.entropy_eq_of_ntot
#print axioms CarryGraph.core_eq_empty_iff_of_ntot
#print axioms CarryGraph.npaths_eq_of_rightCover
#print axioms CarryGraph.ntot_le_of_rightCover
#print axioms CarryGraph.ntot_rightCover_le
#print axioms CarryGraph.entropy_eq_of_rightCover
#print axioms CarryGraph.lnoBranch_iff_of_rightCover
#print axioms CarryGraph.polyGrowth_iff_of_rightCover
#print axioms CarryGraph.core_eq_empty_iff_of_rightCover
#print axioms CarryGraph.adj_inSplit
#print axioms CarryGraph.inSplit_rightCover
#print axioms CarryGraph.npaths_inSplit
#print axioms CarryGraph.entropy_inSplit
#print axioms CarryGraph.lnoBranch_inSplit_iff
#print axioms CarryGraph.core_inSplit
#print axioms CarryGraph.adj_outSplit
#print axioms CarryGraph.sum_npaths_outSplit
#print axioms CarryGraph.ntot_outSplit
#print axioms CarryGraph.entropy_outSplit
#print axioms CarryGraph.lnoBranch_outSplit_iff
#print axioms CarryGraph.core_outSplit
#print axioms CarryGraph.adj_lineGraph
#print axioms CarryGraph.lineGraph_rightCover
#print axioms CarryGraph.npaths_lineGraph
#print axioms CarryGraph.isSink_lineGraph
#print axioms CarryGraph.ntot_lineGraph
#print axioms CarryGraph.entropy_lineGraph
#print axioms CarryGraph.lnoBranch_lineGraph_iff
#print axioms CarryGraph.core_lineGraph
-- ZeroEntropy.lean
#print axioms CarryGraph.lnoBranch_iff_simpleCycles
#print axioms CarryGraph.allEvPer_of_isLRank
#print axioms CarryGraph.lnoBranch_of_allEvPer
#print axioms CarryGraph.zeroEntropy_tfae
#print axioms CarryGraph.under_forget
#print axioms CarryGraph.under_forget_eq
#print axioms CarryGraph.reach_forget
#print axioms CarryGraph.isLRank_forget_iff
#print axioms CarryGraph.lnoBranch_forget_iff
#print axioms CarryGraph.noBranch_tfae
