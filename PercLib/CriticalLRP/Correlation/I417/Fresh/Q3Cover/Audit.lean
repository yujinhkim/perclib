/-
Independently rebuilt and integrated from the accepted `smwx5p94b/m3` artifact.
Production integration revision `9be3dd2832bf4fe01e33a70c2c3192ab4c837d88`.
Axiom audit for the spine–hub family and the fan obstruction.
-/

module

public import PercLib.CriticalLRP.Correlation.I417.Fresh.Q3Cover.Main

/-!
Axiom audit for `Q3Cover.{Defs,Main}`.  Every exported declaration must depend only
on `propext`, `Classical.choice` and `Quot.sound`.
-/

set_option linter.hashCommand false

open PercLib.CriticalLRP.I417Fresh
open PercLib.CriticalLRP.I417Fresh.Q3

#print axioms spineHubBound_eq
#print axioms isUpperSet_spineHubReq
#print axioms finiteWitness_spineHubReq
#print axioms spineHubEvent_measure_le
#print axioms fresh_spineHub_le
#print axioms fresh_spineHub_le_bound
#print axioms fanCutEdge_mem
#print axioms fan_cut_unique
#print axioms fan_walk_has_sep_edge
#print axioms fan_cut_mem_of_connects
#print axioms fan_mem_connSet_of_single
#print axioms fan_conn
#print axioms fan_conn_arm
#print axioms fanSep_ge_six
#print axioms fanSep_le_five
#print axioms fan_not_forkEvent
#print axioms fanSpineHubW_sub
#print axioms fanSpineHubW_mem
#print axioms fanSpineHubW_disj
#print axioms fan_spineHubEvent
#print axioms fan_hubEvent
#print axioms fan_spineHub_vs_fork
