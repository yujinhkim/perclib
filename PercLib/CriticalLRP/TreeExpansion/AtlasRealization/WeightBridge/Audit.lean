/- Integrated from independently rebuilt Ultramath work.
Production base 50c2eed0682a7e1b078ae771dbef463ebe00701d.
Scratch source: repository-root .ultramath/.
-/

/-
Axiom audit of the weight/positions bridge and its consumer.
-/
module

public import PercLib.CriticalLRP.TreeExpansion.AtlasRealization.WeightBridge.Orbit

/-! Standard-axiom audit: every result below must use only
`propext`, `Classical.choice`, `Quot.sound`. -/

set_option linter.hashCommand false

open PercLib.CriticalLRP.TreeExpansion.Real

#print axioms PercLib.CriticalLRP.TreeExpansion.Real.prod_aedge_leaf
#print axioms PercLib.CriticalLRP.TreeExpansion.Real.prod_aedge_node
#print axioms PercLib.CriticalLRP.TreeExpansion.Real.sum_ipos_node
#print axioms PercLib.CriticalLRP.TreeExpansion.Real.sum_triple_factor
#print axioms PercLib.CriticalLRP.TreeExpansion.Real.posSumWt_leaf
#print axioms PercLib.CriticalLRP.TreeExpansion.Real.posSumWt_node
#print axioms PercLib.CriticalLRP.TreeExpansion.Real.posSumWt_eq_wtL
#print axioms PercLib.CriticalLRP.TreeExpansion.Real.posSumWt_eq_wt
#print axioms PercLib.CriticalLRP.TreeExpansion.Real.ltonUnivEquivLT
#print axioms PercLib.CriticalLRP.TreeExpansion.Real.tsum_ipos_node
#print axioms PercLib.CriticalLRP.TreeExpansion.Real.tsum_three_comm
#print axioms PercLib.CriticalLRP.TreeExpansion.Real.posSumWtE_node
#print axioms PercLib.CriticalLRP.TreeExpansion.Real.posSumWtE_eq_wtE
#print axioms PercLib.CriticalLRP.TreeExpansion.Real.prob_conn_le_sum_wtL
#print axioms PercLib.CriticalLRP.TreeExpansion.Real.sum_LTon_univ_eq_sum_LT
#print axioms PercLib.CriticalLRP.TreeExpansion.Real.prob_conn_le_sum_wtL_fin
#print axioms PercLib.CriticalLRP.TreeExpansion.Real.sum_wtL_labelled
#print axioms PercLib.CriticalLRP.TreeExpansion.Real.sum_prob_le_card_mul
#print axioms PercLib.CriticalLRP.TreeExpansion.Real.wtL_swap
#print axioms PercLib.CriticalLRP.TreeExpansion.Real.sum_wtL_eq_two_pow_mul_treeSum
#print axioms PercLib.CriticalLRP.TreeExpansion.Real.prob_conn_le_two_pow_mul_treeSum
#print axioms PercLib.CriticalLRP.TreeExpansion.Real.sum_prob_le_two_pow_mul_dfactorial
#print axioms PercLib.CriticalLRP.TreeExpansion.RTree.swapFiber_self
#print axioms PercLib.CriticalLRP.TreeExpansion.RTree.swapFiber_symm
#print axioms PercLib.CriticalLRP.TreeExpansion.RTree.swapFiber_congr
#print axioms PercLib.CriticalLRP.TreeExpansion.RTree.image_node_prod_comm
#print axioms PercLib.CriticalLRP.TreeExpansion.wtL_eq_of_mem_swapFiber
