/-
Migration source: https://github.com/yujinhkim/Critical-Long-range-percolation
Integration revision: 3b3d1d0e43ef940bfaa2292ee5c2ee094ac4edbf
Licence: Apache-2.0 for the PercLib Lean sources and tooling; see third_party/critical-lrp/.
External provenance and modifications are recorded in the file-specific notices below.
-/

/-
# Two-cluster correlation of extended cluster cardinalities on the canonical model

The finite-exhaustion layer proves this for `Percolation.edgeLaw`. Here its
product-law and cluster equivalences are used to state the result on the
canonical countable percolation model and, in particular, on `longRangeMeasure`.
-/
module

public import PercLib.CriticalLRP.BK.FunctionalInterface
public import PercLib.CriticalLRP.BK.CanonicalBridge

set_option linter.unusedSectionVars false
set_option linter.unusedSimpArgs false
set_option linter.unnecessarySimpa false
set_option linter.unusedTactic false
set_option linter.unusedVariables false

set_option autoImplicit true

@[expose] public section

open MeasureTheory ProbabilityTheory unitInterval
open scoped ENNReal

namespace PercLib.CriticalLRP

attribute [local instance] Classical.propDecidable

variable {V : Type*} [Countable V]

/-- For every legitimate Bernoulli edge law on the canonical complete unordered-edge graph,
$$E(|K_x||K_y|1(x\nleftrightarrow y))\le E|K_x|\,E|K_y|,$$
where cluster cardinality is extended to infinite clusters by `Percolation.cardFun`. -/
theorem edgeMeasure_twoCluster_cardFun (π : Sym2 V → unitInterval) (hπ : ∀ e, π e < 1)
    (x y : V) :
    ∫⁻ ω, ({ω : Config V | ¬ Connects ω x y}).indicator (fun _ => (1 : ℝ≥0∞)) ω *
        (Percolation.cardFun (cluster ω x) * Percolation.cardFun (cluster ω y))
        ∂(edgeMeasure π) ≤
      (∫⁻ ω, Percolation.cardFun (cluster ω x) ∂(edgeMeasure π)) *
        (∫⁻ ω, Percolation.cardFun (cluster ω y) ∂(edgeMeasure π)) := by
  let := Encodable.ofCountable (Sym2 V)
  rw [edgeMeasure_eq_edgeLaw]
  have h := Percolation.twoCluster_cardFun_lintegral' (idBondGraph V) π hπ x y
  simpa only [← cluster_idBondGraph, ← conn_idBondGraph_iff] using h

/-- The extended-cardinality two-cluster bound for the paper's long-range parameter law. -/
theorem longRangeMeasure_twoCluster_cardFun {J : Sym2 V → ℝ} (hJ : ∀ e, 0 ≤ J e) (β : NNReal)
    (x y : V) :
    ∫⁻ ω, ({ω : Config V | ¬ Connects ω x y}).indicator (fun _ => (1 : ℝ≥0∞)) ω *
        (Percolation.cardFun (cluster ω x) * Percolation.cardFun (cluster ω y))
        ∂(longRangeMeasure J hJ β) ≤
      (∫⁻ ω, Percolation.cardFun (cluster ω x) ∂(longRangeMeasure J hJ β)) *
        (∫⁻ ω, Percolation.cardFun (cluster ω y) ∂(longRangeMeasure J hJ β)) :=
  edgeMeasure_twoCluster_cardFun _ (fun e => bernoulliEdgeProb_lt_one hJ β e) x y

end PercLib.CriticalLRP
