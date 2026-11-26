/-
Independently rebuilt and integrated from `smwx9itnu/m1`. Production
integration revision `3163cff3d90175d69f2612903830a27bdf5c0ab6`.
The coordinator supplies the fully applied 48-term aggregation and its
moment composition; only the strict build and global axiom audit determine acceptance.
-/
/-
Independently built for swarm `smwx9itnu`, member `m1`, direction Q4-SUMMED-EVALUATION.
No production files are modified; this module is read-only against production.
-/
module

public import PercLib.CriticalLRP.Correlation.I417.Fresh.Eval.Branch
public import PercLib.CriticalLRP.Correlation.I417.Fresh.Eval.Moment

/-!
# Axiom audit for the summed `q = 4` fresh-diagram evaluation

Every theorem below depends only on the allowed axioms `propext`, `Classical.choice` and
`Quot.sound`.  There is no `sorry`, no `admit`, no `native_decide` and no custom axiom anywhere in
`Q4Eval.Defs`, `Q4Eval.Engine` or `Q4Eval.Branch`.
-/

set_option linter.hashCommand false

open PercLib.CriticalLRP.I417FreshFour.Eval

#print axioms tsum_arm_four
#print axioms tsum_arm_four_tuple
#print axioms arms_inner
#print axioms iterPow_four_eq
#print axioms iterPow_transpose
#print axioms iterPow_kernel_comm
#print axioms chain_L1
#print axioms chain_L2
#print axioms chain_L3
#print axioms chain_L4
#print axioms perm13
#print axioms tsum_fin2
#print axioms tsum_fin2_bool
#print axioms tsum_fin2_bool_bool

#print axioms tsum_q4_le_profile
#print axioms tsum_freshMark_le_profile
#print axioms moment_gap_four_le_eval
#print axioms moment_gap_four_le_eval_transitive
#print axioms PercLib.CriticalLRP.TreeExpansion.latticeLongRange_moment_gap_four_le_eval
#print axioms ev_0
#print axioms ev_1
#print axioms ev_2
#print axioms ev_3
#print axioms ev_4
#print axioms ev_5
#print axioms ev_6
#print axioms ev_7
#print axioms ev_8
#print axioms ev_9
#print axioms ev_10
#print axioms ev_11
#print axioms ev_12
#print axioms ev_13
#print axioms ev_14
#print axioms ev_15
#print axioms ev_16
#print axioms ev_17
#print axioms ev_18
#print axioms ev_19
#print axioms ev_20
#print axioms ev_21
#print axioms ev_22
#print axioms ev_23
#print axioms ev_24
#print axioms ev_25
#print axioms ev_26
#print axioms ev_27
#print axioms ev_28
#print axioms ev_29
#print axioms ev_30
#print axioms ev_31
#print axioms ev_32
#print axioms ev_33
#print axioms ev_34
#print axioms ev_35
#print axioms ev_36
#print axioms ev_37
#print axioms ev_38
#print axioms ev_39
#print axioms ev_40
#print axioms ev_41
#print axioms ev_42
#print axioms ev_43
#print axioms ev_44
#print axioms ev_45
#print axioms ev_46
#print axioms ev_47
