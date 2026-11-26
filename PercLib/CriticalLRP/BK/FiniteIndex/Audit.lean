/-
Axiom audit for the finite-index canonical BK bridge.  Swarm smwwtd5t5, member m2.
Production read only, at HEAD 4c53bb5a8e76a4358a426adf71169b916b90f51f.
-/

/-
# Axiom audit

Every statement below is printed with `#print axioms`.  Only the three standard axioms
`propext`, `Classical.choice` and `Quot.sound` may appear; `sorry`/`admit`,
`native_decide` and custom axioms are not used anywhere in this development.
-/

module

public import PercLib.CriticalLRP.BK.FiniteIndex.Canonical

/-!
# Axiom audit of the headline results
-/

@[expose] public section

set_option linter.hashCommand false

-- Definitions layer (`Defs.lean`)
#print axioms PercLib.CriticalLRP.Percolation.disjFam_finiteWitness
#print axioms PercLib.CriticalLRP.Percolation.disjFam_congr
#print axioms PercLib.CriticalLRP.Percolation.disjFam_isEmpty
#print axioms PercLib.CriticalLRP.Percolation.disjFam_option_univ

-- The `List` form is the family form (`FiniteBK.lean`)
#print axioms PercLib.CriticalLRP.Percolation.disjFam_eq_disjointOccurrenceList_ofFn
#print axioms PercLib.CriticalLRP.Percolation.disjFam_eq_disjointOccurrenceList_equiv
#print axioms PercLib.CriticalLRP.Percolation.disjFam_eq_disjointOccurrenceList

-- Finite-index BK (`FiniteBK.lean`)
#print axioms PercLib.CriticalLRP.Percolation.bk_disjFam_real_fin
#print axioms PercLib.CriticalLRP.Percolation.bk_disjFam_real
#print axioms PercLib.CriticalLRP.Percolation.bk_disjFam
#print axioms PercLib.CriticalLRP.Percolation.ofReal_prod_map_real
#print axioms PercLib.CriticalLRP.Percolation.edgeMeasure_bk_list_ennreal

-- Canonical connection events and the atlas index (`Canonical.lean`)
#print axioms PercLib.CriticalLRP.edgeMeasure_bk_connSet_fam
#print axioms PercLib.CriticalLRP.edgeMeasure_bk_connSet_fam_real
#print axioms PercLib.CriticalLRP.edgeMeasure_bk_atlas
#print axioms PercLib.CriticalLRP.conn_iff_connects
#print axioms PercLib.CriticalLRP.diagEvent_subset_disjFam

-- The diagonal `u = v` contributes the factor `1` and no edge
#print axioms PercLib.CriticalLRP.connSet_self
#print axioms PercLib.CriticalLRP.edgeMeasure_connSet_self
#print axioms PercLib.CriticalLRP.disjFam_connSet_self_option
#print axioms PercLib.CriticalLRP.edgeMeasure_bk_connSet_fam_diag

-- Union bounds over countable families
#print axioms PercLib.CriticalLRP.edgeMeasure_iUnion_le_tsum
#print axioms PercLib.CriticalLRP.edgeMeasure_iUnion_bk_le_tsum
#print axioms PercLib.CriticalLRP.edgeMeasure_iUnion_atlas_le_tsum
#print axioms PercLib.CriticalLRP.measurableSet_disjFam
