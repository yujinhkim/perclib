/- Integrated from independently rebuilt Ultramath work, base revision 4140ac56119d2cd80995f91886669efe004839d5.
Scratch source: ../../.ultramath/smwqozn0q/m2/Check.lean ; imports migrated;
auxiliary definitions and probability instances are collected in `Defs.lean`.
-/

/-
Axiom audit for the cutoff-fidelity module of direction B (m2, swarm smwqozn0q).
Every export must depend only on `propext`, `Classical.choice`, `Quot.sound`.
-/
module

public import PercLib.CriticalLRP.Analysis.Cutoff.KpowSum

open PercLib.CriticalLRP.Orchestration

#print axioms SourceModelData.cutTwoPointE_eq_ofReal
#print axioms SourceModelData.cutTwoPointE_le_one
#print axioms SourceModelData.cutTwoPoint_nonneg
#print axioms SourceModelData.cutTwoPoint_le_one
#print axioms SourceModelData.cutTwoPointE_self_eq_one
#print axioms SourceModelData.cutTwoPoint_self_eq_one
#print axioms SourceModelData.cutTwoPointE_comm
#print axioms SourceModelData.cutTwoPoint_comm
#print axioms SourceModelData.twoPoint_self_eq_one
#print axioms SourceModelData.twoPoint_comm
#print axioms SourceModelData.tsum_cutTwoPointE_eq_cutMassAt
#print axioms SourceModelData.cutMassAt_zero_eq_cutMoment
#print axioms SourceModelData.tsum_cutTwoPointE_eq_cutMoment
#print axioms SourceModelData.one_le_cutMoment_one
#print axioms SourceModelData.tsum_ofReal_cutTwoPoint_eq_cutMoment
#print axioms one_le_threefold_tsum
#print axioms not_forall_le_tail_add_rpow
#print axioms SourceModelData.one_le_cutThreefold
#print axioms SourceModelData.not_source_ell_three_bound
#print axioms SourceModelData.cutKernel_shift
#print axioms SourceModelData.cutEdgeProb_shift
#print axioms SourceModelData.cutLaw_map_shiftConfig
#print axioms SourceModelData.cutTwoPoint_translate
#print axioms SourceModelData.cutTwoPoint_eq_sub
#print axioms SourceModelData.clusterVol_shiftConfig
#print axioms SourceModelData.cutMassAt_translate
#print axioms SourceModelData.cutMassAt_eq_zero
#print axioms SourceModelData.tau_cutProb
#print axioms SourceModelData.chi_cutProb
#print axioms SourceModelData.cutTwoPoint_posSemidef
#print axioms SourceModelData.bernoulliEdgeProb_mono_kernel
#print axioms SourceModelData.cutKernel_le_uncut
#print axioms SourceModelData.cutKernel_mono_r
#print axioms SourceModelData.cutTwoPointE_le_twoPointE
#print axioms SourceModelData.cutTwoPoint_le_twoPoint
#print axioms SourceModelData.cutTwoPointE_mono_r
#print axioms SourceModelData.cutTwoPoint_mono_r
#print axioms SourceModelData.cutThreefold_le_uncutThreefold
#print axioms PercLib.CriticalLRP.KernelPower.Kpow_add
#print axioms PercLib.CriticalLRP.KernelPower.Kpow_rowSum
#print axioms PercLib.CriticalLRP.KernelPower.Kpow_colSum
#print axioms PercLib.CriticalLRP.KernelPower.Kpow_succ_le_pow
#print axioms PercLib.CriticalLRP.KernelPower.Kpow_colSum_of_symm
#print axioms SourceModelData.cutKpow_row
#print axioms SourceModelData.cutKpow_rowSum
#print axioms SourceModelData.cutKpow_colSum
#print axioms SourceModelData.cutKpow_entry
#print axioms SourceModelData.cutKpow_comp
#print axioms SourceModelData.cutKpow_rowSum_toReal
#print axioms SourceModelData.cutKpow_colSum_toReal

-- statements of the two source-facing corollaries
#check @SourceModelData.cutTwoPoint_eq_sub
#check @SourceModelData.cutMassAt_eq_zero
#check @SourceModelData.cutMassAt_zero_eq_cutMoment
#check @SourceModelData.cutThreefold_le_uncutThreefold
#check @SourceModelData.cutKpow_comp
#check @SourceModelData.cutKpow_colSum
#check @SourceModelData.cutKpow_entry
#check @SourceModelData.cutKpow_colSum_toReal
