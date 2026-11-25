/- Integrated from independently rebuilt Ultramath work, base revision 75f8858d8e30ea17b20f9ff1d216bc1508c01ce2.
Scratch source: ../../.ultramath/smwpwq50m/m2/I417B/CardFun.lean ; module path rewritten only.
-/

/-
# The `cardFun(cluster)` convention

The repository writes the paper's `|K|` as `PercLib.CriticalLRP.Percolation.cardFun (cluster ω v)` in the
tree-moment files (`PowerLawTreeMoments.lean`, `MonotoneMoments.lean`), and as the (definitionally
equal) `clusterVol ω v` in the moment computations.  This file records the identification, so that
the marked two-copy quantities of `I417B/Defs.lean` are visibly the paper's `|Kx|²`, `|Ky|`,
`E[|Kx|² 1(w ∈ Kx)]` and `E[|Kx|² |Ky| 1(x ↮ y)]` and not surrogate variables.

No `sorry`, no custom axioms; no definitions.
-/
module

public import PercLib.CriticalLRP.Correlation.I417.Final
public import PercLib.CriticalLRP.BK.ClusterCardinal

open MeasureTheory Measure ProbabilityTheory unitInterval
open scoped ENNReal NNReal

set_option linter.unusedSectionVars false

@[expose] public section

namespace PercLib.CriticalLRP.I417

attribute [local instance] Classical.propDecidable

variable {V : Type*} [Countable V]

/-- `clusterVol` is `cardFun` of the cluster: the paper's `|K_v|`. -/
theorem clusterVol_eq_cardFun (ω : Config V) (v : V) :
    clusterVol ω v = PercLib.CriticalLRP.Percolation.cardFun (cluster ω v) := by
  rw [PercLib.CriticalLRP.Percolation.cardFun_eq_encard]

/-- The excluded moment `E[|Kx|² |Ky| 1(x ↮ y)]` in the `cardFun` convention. -/
theorem exclMomentSq_eq_cardFun (π : Sym2 V → unitInterval) (x y : V) :
    exclMomentSq π x y =
      ∫⁻ ω, PercLib.CriticalLRP.Percolation.cardFun (cluster ω x) ^ 2 *
        (cluster ω x)ᶜ.indicator (fun _ => (1 : ℝ≥0∞)) y *
        PercLib.CriticalLRP.Percolation.cardFun (cluster ω y) ∂(edgeMeasure π) := by
  rw [exclMomentSq]
  simp only [clusterVol_eq_cardFun]

/-- The second moment `E|Kx|²` in the `cardFun` convention. -/
theorem volSq_eq_cardFun (π : Sym2 V → unitInterval) (x : V) :
    volSq π x = ∫⁻ ω, PercLib.CriticalLRP.Percolation.cardFun (cluster ω x) ^ 2 ∂(edgeMeasure π) := by
  rw [volSq]
  simp only [clusterVol_eq_cardFun]

/-- The marked second moment `E[|Kx|² 1(w ∈ Kx)]` in the `cardFun` convention. -/
theorem jointSq_eq_cardFun (π : Sym2 V → unitInterval) (x w : V) :
    jointSq π x w =
      ∫⁻ ω, PercLib.CriticalLRP.Percolation.cardFun (cluster ω x) ^ 2 *
        (cluster ω x).indicator (fun _ => (1 : ℝ≥0∞)) w ∂(edgeMeasure π) := by
  rw [jointSq]
  simp only [clusterVol_eq_cardFun]

end PercLib.CriticalLRP.I417
