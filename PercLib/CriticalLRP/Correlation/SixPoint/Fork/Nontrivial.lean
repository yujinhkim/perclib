/-
Swarm `smwprafq1`, member `m2`: non-vacuity of the nine-arm six-terminal fork slot.
-/
module

public import PercLib.CriticalLRP.Correlation.SixPoint.Fork.Assembly

set_option autoImplicit false

open Set MeasureTheory
open scoped ENNReal BigOperators
open PercLib.Percolation.Bond
open PercLib.Probability

@[expose] public section

namespace PercLib.CriticalLRP.TreeExpansion.FivePoint

/-- The fork slot is realized by the full configuration on a single vertex (all arms empty),
so none of the bounds above is vacuous. -/
example : ForkSlots (V := PUnit) Set.univ () () () () () () () () () () := by
  refine ⟨.nil, .nil, .nil, .nil, .nil, .nil, .nil, .nil, .nil, ?_⟩
  simp

/-- Consequently the fork event is nonempty on a single vertex. -/
example : (ForkEvent (V := PUnit) () () () () () () : Set (Config PUnit)) = Set.univ := by
  ext ω
  refine iff_of_true ?_ (Set.mem_univ _)
  refine Set.mem_iUnion.mpr ⟨(), Set.mem_iUnion.mpr ⟨(), Set.mem_iUnion.mpr
    ⟨(), Set.mem_iUnion.mpr ⟨(), ?_⟩⟩⟩⟩
  refine ⟨SimpleGraph.Walk.nil, SimpleGraph.Walk.nil, SimpleGraph.Walk.nil,
    SimpleGraph.Walk.nil, SimpleGraph.Walk.nil, SimpleGraph.Walk.nil,
    SimpleGraph.Walk.nil, SimpleGraph.Walk.nil, SimpleGraph.Walk.nil, ?_⟩
  simp

#print axioms fork_shape_bound

end PercLib.CriticalLRP.TreeExpansion.FivePoint
