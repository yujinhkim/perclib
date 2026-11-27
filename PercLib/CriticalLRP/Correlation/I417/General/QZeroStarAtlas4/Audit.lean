/-
Ultramath swarm `smwziumdb`, member `m7`, direction `d4`.

Copyright (c) 2026 PercLib contributors. Released under Apache 2.0.

Accepted and independently rebuilt from Ultramath `smwziumdb`.
Supporting integration based on production commit `5d2d681b941eb1c687f1ba17e6a798b8f0175aa0`.

# Axiom audit for the four-label star atlas realization

Every exported theorem of `Defs.lean` and `Main.lean` is checked here: the permitted axioms are
exactly `propext`, `Classical.choice` and `Quot.sound`.  No `sorry`, `admit`, `native_decide`,
`sorryAx`, custom axioms or `False.elim` appear anywhere in the two files.
-/
module

public import PercLib.CriticalLRP.Correlation.I417.General.QZeroStarAtlas4.Eval

/-! # Axiom audit for the canonical star realization and evaluation -/

set_option linter.hashCommand false

open MeasureTheory Measure ProbabilityTheory unitInterval
open scoped ENNReal NNReal

@[expose] public section

namespace PercLib.CriticalLRP.QZeroStarAtlas4

variable {V : Type*} [Countable V] [DecidableEq V]

-- the definitions
#print axioms starLabels
#print axioms starAtlasSum
#print axioms fin4Split
#print axioms fin4Join
#print axioms fin4Equiv
#print axioms tauK
#print axioms starDepth

-- the label bookkeeping
#print axioms starLabels_castSucc
#print axioms starLabels_three
#print axioms starLabels_last
#print axioms fin4Join_fin4Split
#print axioms fin4Split_fin4Join

-- the realization
#print axioms labelEvent_starLabels
#print axioms starMoment_le_starAtlasSum
#print axioms starMoment_le_tsum_shapes

-- the evaluation
#print axioms tsum_pinned_eq_tsum_arms
#print axioms tsum_arms_wtE
#print axioms starMoment_le_shape_eval
#print axioms starDepth_pos
#print axioms starDepth_le

-- the bridge to production
#print axioms starMoment_eq_jointPow
#print axioms starMoment_le_nonplane_markedDepth

end PercLib.CriticalLRP.QZeroStarAtlas4
