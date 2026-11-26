/-
Axiom audit for direction `HISTORY-FIBRE-PACKAGING` (swarm `smwxfstjy`, member `m1`).
-/
module

public import PercLib.CriticalLRP.Correlation.I417.Fresh.HistFibre.Final

/-!
# Axiom audit

Every theorem of this package must rest only on the three standard axioms
`propext`, `Classical.choice` and `Quot.sound`.
-/

set_option linter.hashCommand false

open PercLib.CriticalLRP.I417HistFibre

/-! ## The fibre reindexing and its iteration -/

#print axioms splitChoices_snoc_apply_last
#print axioms splitChoices_snoc_apply_castSucc
#print axioms histFibre_snoc
#print axioms histFibre_snoc_splitWt
#print axioms histFibre_zero
#print axioms restr_succ
#print axioms restr_self
#print axioms histFibre_slotW_iter
#print axioms slotW_top_fun
#print axioms histFibre_eq_histW_slotW

/-! ## The stage-`0` evaluation and the branch value -/

#print axioms histW_nil_eq
#print axioms histW_slotW_zero
#print axioms tsum_histFibre_chainM
#print axioms histFibre_eq_twoChains
#print axioms tsum_histFibre_markDepth

/-! ## The pin--mark depth identification -/

#print axioms chainF_eq_succ
#print axioms chainF_eq_top
#print axioms stepSet_union
#print axioms stepSet_eq_erase_image
#print axioms chainF_empty
#print axioms chainF_union
#print axioms chainF_singleton_disjoint
#print axioms chainM_eq_card_chainF
#print axioms pathLegsK_eq_stepSet
#print axioms chainF_succ_last
#print axioms chainF_zero_eq_pathLegsK
#print axioms markDepthK_eq_card_pathLegsK
#print axioms markDepthK_eq_chainM
