/-
Independently built axiom audit for swarm `smwwtd5t5`, member `m1` (direction A).

Every public result of the directory is printed with `#print axioms`.  The expected answer for
every line is `[propext, Classical.choice, Quot.sound]` (or a subset), i.e. Lean's three standard
axioms and nothing else: no `sorry`, no `admit`, no `native_decide`, no custom axiom, no
`Lean.ofReduceBool`.
-/
module

public import PercLib.CriticalLRP.TreeExpansion.AtlasRealization.Canonical.Example

/-!
# Axiom audit

The audit covers, in order:

* the transport between the finite graph on `↥W` and the canonical countable graph
  (`treeConn_iff_connects`, `witLift_univ`, `isCanonRealization_of_isRealization`);
* the selection of a finite edge witness inside a configuration (`exists_finset_conn_witness`);
* the all-configurations realization in the canonical model (`exists_canonical_realization`);
* the covering statements (`conn_subset_canonAtlas_iUnion`, `conn_subset_canonCover`,
  `labelEvent_subset_canonAtlas_iUnion`, `labelEvent_subset_canonCover`) and the countability of
  the index type (`countable_atlasIndex`);
* the `q = 1` exact case (`canonRealization_leaf_one`, `labelEvent_one_eq`);
* the degenerate `q = 0` statements (`isEmpty_atlasIndex_zero`, `canonCover_zero_eq_empty`,
  `labelEvent_zero`, `not_conn_subset_canonCover_zero`);
* the honesty of empty witnesses (`openGraph_empty`, `connects_empty_eq`,
  `srcPos_eq_dstPos_of_wit_eq_empty`);
* the hypotheses of the canonical BK law (`isUpperSet_canonAtlasEvent`,
  `finiteWitness_canonAtlasEvent`, `mem_connSet_wit`);
* the shape count (`numLeaves_of_isLabelledShape`, `card_aedge_of_labelled`).
-/

@[expose] public section

set_option linter.hashCommand false

#print axioms CanonAtlas.openGraph_lift_le
#print axioms CanonAtlas.openGraph_lift_ge
#print axioms CanonAtlas.treeConn_iff_connects
#print axioms CanonAtlas.treeConn_univ_iff_connects
#print axioms CanonAtlas.witLift_univ
#print axioms CanonAtlas.isCanonRealization_of_isRealization
#print axioms CanonAtlas.exists_finset_conn_witness
#print axioms CanonAtlas.exists_canonical_realization
#print axioms CanonAtlas.conn_subset_canonAtlas_iUnion
#print axioms CanonAtlas.conn_subset_canonCover
#print axioms CanonAtlas.countable_atlasIndex
#print axioms CanonAtlas.numLeaves_of_isLabelledShape
#print axioms CanonAtlas.card_aedge_of_labelled
#print axioms CanonAtlas.isUpperSet_canonAtlasEvent
#print axioms CanonAtlas.finiteWitness_canonAtlasEvent
#print axioms CanonAtlas.labelEvent_eq_conn
#print axioms CanonAtlas.labelEvent_subset_canonAtlas_iUnion
#print axioms CanonAtlas.labelEvent_subset_canonCover
#print axioms CanonAtlas.mem_connSet_wit
#print axioms CanonAtlas.openGraph_empty
#print axioms CanonAtlas.connects_empty_eq
#print axioms CanonAtlas.srcPos_eq_dstPos_of_wit_eq_empty
#print axioms CanonAtlas.subsingleton_aedge_leaf
#print axioms CanonAtlas.canonRealization_leaf_one
#print axioms CanonAtlas.labelEvent_one_eq
#print axioms CanonAtlas.isEmpty_atlasIndex_zero
#print axioms CanonAtlas.canonCover_zero_eq_empty
#print axioms CanonAtlas.labelEvent_zero
#print axioms CanonAtlas.not_conn_subset_canonCover_zero
#print axioms CanonAtlas.Measure.measure_labelEvent_le_tsum
#print axioms CanonAtlas.Measure.measure_labelEvent_le_tsum_shapes
#print axioms CanonAtlas.Measure.atlasProduct
#print axioms CanonAtlas.Example.isRealization
#print axioms CanonAtlas.Example.mem_atlasEvent
#print axioms CanonAtlas.Example.mem_canonCover_example
#print axioms CanonAtlas.Example.degenerate_edge
#print axioms CanonAtlas.Example.card_aedge_twoLeaf
