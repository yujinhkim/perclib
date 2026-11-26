/-
Independently rebuilt and integrated from the accepted `smwx5p94b/m1` artifact
`.ultramath/smwx5p94b/m1/M1Fresh`. Production integration revision:
`9c345df8dcb6d4027a2e61d7a7785abf4df111cf`. The coordinator assigns the production
namespace and fully qualified imports; the mathematical statements are unchanged.
-/
module

public import PercLib.CriticalLRP.Correlation.I417.Fresh.Two.Refined.Lattice

/-!
# Axiom audit for the `q = 2` refined fresh development

The three declarations below are the whole mathematical content:

* `exists_refined_branch` — the deterministic four-edge cover of the fresh event;
* `tsum_freshMark_le_refined` — the fresh-copy factor at `q = 2` bounded by four
  two-point factors, unconditionally (BK + constant row sum);
* `moment_gap_two_le_refined` — the assembled moment gap with the printed exponent `2p+5`.

Each must depend only on `propext`, `Classical.choice`, `Quot.sound`.
-/

open MeasureTheory Measure ProbabilityTheory unitInterval
open scoped ENNReal NNReal

set_option linter.hashCommand false
set_option autoImplicit false
set_option linter.unusedSectionVars false

@[expose] public section

namespace PercLib.CriticalLRP.I417FreshTwo.Refined

variable {V : Type*} [Countable V] [DecidableEq V]

#print axioms tree4_mem_of_walks
#print axioms edgeFinset_takeUntil_disjoint_dropUntil
#print axioms exists_refined_branch
#print axioms tree4_le
#print axioms shape_union_le_zero
#print axioms freshMark_measure_le_refined_zero
#print axioms freshMark_measure_le_refined_one
#print axioms tsum_freshMark_le_refined
#print axioms tsum_freshMark_le_refined_iterPow
#print axioms moment_gap_two_le_refined
#print axioms moment_gap_two_le_refined_transitive
#print axioms PercLib.CriticalLRP.TreeExpansion.latticeLongRange_moment_gap_two_le_refined

end PercLib.CriticalLRP.I417FreshTwo.Refined
