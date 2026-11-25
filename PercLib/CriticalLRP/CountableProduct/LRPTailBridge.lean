/-
Migration source: https://github.com/yujinhkim/Critical-Long-range-percolation
Integration revision: 3b3d1d0e43ef940bfaa2292ee5c2ee094ac4edbf
Licence: Apache-2.0 for the PercLib Lean sources and tooling; see third_party/critical-lrp/.
External provenance and modifications are recorded in the file-specific notices below.
-/

/-
# Bridge from native PercLib to the canonical product law

`tomhutchcroft/lrp` supplies the finite-witness tail theorem and its monotone
measure-continuity argument. The present module identifies its configuration,
cluster and independent product law with those of this project, so the tail
result can be used on the canonical `edgeMeasure` without restating its proof.
-/
module

public import PercLib.CriticalLRP.CountableProduct.Base
public import PercLib.Percolation.Bond.ClusterTails

set_option linter.unusedSectionVars false
set_option linter.unusedSimpArgs false
set_option linter.unnecessarySimpa false
set_option linter.unusedTactic false
set_option linter.unusedVariables false

set_option autoImplicit true

@[expose] public section

open MeasureTheory Set ProbabilityTheory unitInterval
open scoped ENNReal BigOperators

namespace PercLib.CriticalLRP

variable {V : Type*} [Countable V]

/-- Native PercLib connectivity is precisely canonical connectivity. -/
theorem lrp_conn_iff (ω : Config V) (v w : V) :
    ω ∈ PercLib.Percolation.Bond.conn v w ↔ Connects ω v w := Iff.rfl

/-- The LRP cluster is literally the canonical cluster. -/
theorem lrp_cluster_eq (ω : Config V) (v : V) :
    PercLib.CriticalLRP.cluster ω v = PercLib.Percolation.Bond.cluster ω v := rfl

/-- LRP's product law is the canonical independent-edge measure. -/
theorem lrp_law_eq_edgeMeasure (π : Sym2 V → unitInterval) :
    PercLib.Percolation.Bond.law π = edgeMeasure π := rfl

/-- The LRP cluster-tail exhaustion theorem on the canonical law: an increasing
exhaustive sequence of finite vertex sets works with arbitrary finite edge
restrictions. -/
theorem tendsto_cluster_tail_probability_lrp (π : Sym2 V → unitInterval)
    (v : V) (Λ : Finset V) (k : ℕ) {E : ℕ → Finset (Sym2 V)}
    (hE : Monotone E) (hcover : ∀ e, ∃ n, e ∈ E n) :
    Filter.Tendsto
      (fun n => edgeMeasure π {ω : Config V |
        k ≤ (cluster (ω ∩ (E n : Set (Sym2 V))) v ∩ (Λ : Set V)).ncard})
      Filter.atTop
      (nhds (edgeMeasure π {ω : Config V |
        k ≤ (cluster ω v ∩ (Λ : Set V)).ncard})) := by
  simpa only [lrp_law_eq_edgeMeasure, lrp_cluster_eq] using
    PercLib.Percolation.Bond.tendsto_cluster_tail_probability π v Λ k hE hcover

#print axioms PercLib.CriticalLRP.lrp_conn_iff
#print axioms PercLib.CriticalLRP.lrp_cluster_eq
#print axioms PercLib.CriticalLRP.lrp_law_eq_edgeMeasure
#print axioms PercLib.CriticalLRP.tendsto_cluster_tail_probability_lrp

end PercLib.CriticalLRP
