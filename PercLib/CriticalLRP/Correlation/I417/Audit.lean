/- Integrated from independently rebuilt Ultramath work, base revision 75f8858d8e30ea17b20f9ff1d216bc1508c01ce2.
Scratch source: ../../.ultramath/smwpwq50m/m2/I417B/Audit.lean ; module path rewritten only.
-/

/-
# Axiom audit and the form for the paper's law `P_β`

The main results are stated for the canonical law `edgeMeasure π` (as everywhere in this
repository); `longRangeMeasure J hJ β` is *definitionally* `edgeMeasure (bernoulliEdgeProb J hJ β)`,
so the paper's law is an immediate instance.

No `sorry`, no custom axioms; see the `#print axioms` block at the end.
-/
module

public import PercLib.CriticalLRP.Correlation.I417.Final
public import PercLib.CriticalLRP.Correlation.I417.CardFun
public import PercLib.CriticalLRP.Correlation.I417.Fails
public import PercLib.CriticalLRP.Correlation.I417.Lattice

open MeasureTheory Measure ProbabilityTheory unitInterval
open scoped ENNReal NNReal

set_option linter.unusedSectionVars false

@[expose] public section

namespace PercLib.CriticalLRP.I417

attribute [local instance] Classical.propDecidable

variable {V : Type*} [Countable V]

end PercLib.CriticalLRP.I417

/-! ## Axiom audit -/

#print axioms PercLib.CriticalLRP.I417.measurableSet_diagSet
#print axioms PercLib.CriticalLRP.I417.measurableSet_markSet
#print axioms PercLib.CriticalLRP.I417.prodSet_subset
#print axioms PercLib.CriticalLRP.I417.measure_prodSet_le
#print axioms PercLib.CriticalLRP.I417.tsum_connSet_eq_lintegral
#print axioms PercLib.CriticalLRP.I417.tsum_tsum_inter_connSet_eq_lintegral
#print axioms PercLib.CriticalLRP.I417.tsum_prodSet_eq
#print axioms PercLib.CriticalLRP.I417.twoCopy_moment_le
#print axioms PercLib.CriticalLRP.I417.diagSet_indicator_tsum
#print axioms PercLib.CriticalLRP.I417.tsum_diagSet
#print axioms PercLib.CriticalLRP.I417.I417_p21_le
#print axioms PercLib.CriticalLRP.I417.tsum_tsum_inter_mark_eq
#print axioms PercLib.CriticalLRP.I417.tsum_yInSet
#print axioms PercLib.CriticalLRP.I417.tsum_markSet_le
#print axioms PercLib.CriticalLRP.I417.I417_p21_source_le
#print axioms PercLib.CriticalLRP.I417.I417_p21_source_tsub_le
#print axioms PercLib.CriticalLRP.I417.I417_p21_source_le_unreduced
#print axioms PercLib.CriticalLRP.I417.I417_p21_source_tsub_le_excess
#print axioms PercLib.CriticalLRP.I417.excess_eq
#print axioms PercLib.CriticalLRP.I417.I417_p21_of_diagram
#print axioms PercLib.CriticalLRP.I417.I417_p21_printed_of_diagram
#print axioms PercLib.CriticalLRP.I417.tau_mul_tau_le_inter
#print axioms PercLib.CriticalLRP.I417.mean_sq_le_volSq
#print axioms PercLib.CriticalLRP.I417.clusterVol_eq_cardFun
#print axioms PercLib.CriticalLRP.I417.exclMomentSq_eq_cardFun
#print axioms PercLib.CriticalLRP.I417.volSq_eq_cardFun
#print axioms PercLib.CriticalLRP.I417.jointSq_eq_cardFun
#print axioms PercLib.CriticalLRP.I417.diagSet_not_base
#print axioms PercLib.CriticalLRP.I417.I417_p21_lattice_source_le
#print axioms PercLib.CriticalLRP.I417.I417_p21_lattice_source_le_lintegral
#print axioms PercLib.CriticalLRP.I417.I417_p21_lattice_source_tsub_le
