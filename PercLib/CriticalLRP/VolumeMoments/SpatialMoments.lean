/-
Migration source: https://github.com/yujinhkim/Critical-Long-range-percolation
Integration revision: 3b3d1d0e43ef940bfaa2292ee5c2ee094ac4edbf
Licence: Apache-2.0 for the PercLib Lean sources and tooling; see third_party/critical-lrp/.
External provenance and modifications are recorded in the file-specific notices below.
-/

module

public import PercLib.CriticalLRP.CutoffRusso
public import PercLib.CriticalLRP.FiniteGraphCluster

set_option autoImplicit true

@[expose] public section

open Finset

namespace PercLib.CriticalLRP.FiniteVolume

variable {V : Type*} [Fintype V] [DecidableEq V]
variable {E : Type*} [Fintype E] [DecidableEq E]

/-- A spatially weighted additive observable on the cluster of `o`.  In the
paper's application `q x = ⟪x, u⟫ ^ 2` for a direction `u`. -/
noncomputable def spatialMoment (s t : E → V) (q : V → ℝ) (o : V) (ω : Finset E) : ℝ :=
  ∑ x ∈ cluster s t ω o, q x

/-- Opening an edge joining two components produces exactly their union. -/
theorem cluster_insert_union_of_not_conn {s t : E → V} {e : E} {ω : Finset E}
    (hxy : ¬ Conn s t ω (s e) (t e)) :
    cluster s t (insert e ω) (s e) = cluster s t ω (s e) ∪ cluster s t ω (t e) := by
  ext w
  rw [mem_cluster_insert_of_not_conn hxy, mem_union]

theorem spatialMoment_insert_of_not_conn {s t : E → V} (q : V → ℝ) {e : E}
    {ω : Finset E} (hxy : ¬ Conn s t ω (s e) (t e)) :
    spatialMoment s t q (s e) (insert e ω) =
      spatialMoment s t q (s e) ω + spatialMoment s t q (t e) ω := by
  classical
  rw [spatialMoment, spatialMoment, spatialMoment,
    cluster_insert_union_of_not_conn hxy,
    sum_union (disjoint_cluster_of_not_conn hxy)]

theorem spatialMoment_base_of_conn {s t : E → V} (q : V → ℝ) {ω : Finset E}
    {o x : V} (h : Conn s t ω o x) :
    spatialMoment s t q o ω = spatialMoment s t q x ω := by
  rw [spatialMoment, spatialMoment, cluster_eq_of_conn h]

/-- The observable `|K| S(K)`, which occurs in the error decomposition of Lemma
I.5.8 as well as in mass-transport substitutions. -/
noncomputable def volWeightedSpatialMoment (s t : E → V) (q : V → ℝ) (o : V)
    (ω : Finset E) : ℝ :=
  ((cluster s t ω o).card : ℝ) * spatialMoment s t q o ω

/-- Merge formula for `|K| S(K)`. The three terms separate the spatial moment
of the new cluster from both old-cluster factors. -/
theorem volWeightedSpatialMoment_flip_of_not_conn {s t : E → V} (q : V → ℝ) {e : E}
    {ω : Finset E} (hxy : ¬ Conn s t ω (s e) (t e)) :
    volWeightedSpatialMoment s t q (s e) (insert e ω) - volWeightedSpatialMoment s t q (s e) ω =
      ((cluster s t ω (t e)).card : ℝ) * spatialMoment s t q (s e) ω +
        (((cluster s t ω (s e)).card : ℝ) + ((cluster s t ω (t e)).card : ℝ)) *
          spatialMoment s t q (t e) ω := by
  rw [volWeightedSpatialMoment, volWeightedSpatialMoment,
    card_cluster_insert_of_not_conn hxy, spatialMoment_insert_of_not_conn q hxy]
  push_cast
  ring

/-- The unweighted spatial moment of a merged cluster has no mixed sum. -/
theorem spatialMoment_flip_sub_of_not_conn {s t : E → V} (q : V → ℝ) {e : E}
    {ω : Finset E} (hxy : ¬ Conn s t ω (s e) (t e)) :
    spatialMoment s t q (s e) (insert e ω) - spatialMoment s t q (s e) ω =
      spatialMoment s t q (t e) ω := by
  rw [spatialMoment_insert_of_not_conn q hxy]
  ring

set_option linter.unusedSectionVars false in
/-- Finite-volume Russo differentiation of an additive observable with spatial
weights. The observable may be unbounded on finite configurations, matching the
quadratic moment used in Lemma I.5.8 without any additional growth premise. -/
theorem hasDerivAt_expectation_spatialMoment
    (s t : E → V) (q : V → ℝ) (o : V) (len : E → ℝ) (K : ℝ → ℝ) (K' : ℝ)
    {r β : ℝ} (hne : ∀ e, len e ≠ r) (hK : HasDerivAt K (-K') r) :
    HasDerivAt
      (fun r' => expectation (fun e => longRangeEdgeProbability β (cutoffProfile K r' (len e)))
        (spatialMoment s t q o))
      (β * K' * ∑ e ∈ (univ : Finset E).filter (fun e => len e ≤ r),
        ∑ τ ∈ (univ : Finset (Configuration E)).filter (fun τ => e ∉ τ),
          configurationLaw (fun e => longRangeEdgeProbability β (cutoffProfile K r (len e))) τ
            * (spatialMoment s t q o (insert e τ) - spatialMoment s t q o τ)) r :=
  hasDerivAt_expectation_cutoff len K K' hne hK (spatialMoment s t q o)

end PercLib.CriticalLRP.FiniteVolume

#print axioms PercLib.CriticalLRP.FiniteVolume.cluster_insert_union_of_not_conn
#print axioms PercLib.CriticalLRP.FiniteVolume.spatialMoment_insert_of_not_conn
#print axioms PercLib.CriticalLRP.FiniteVolume.spatialMoment_base_of_conn
#print axioms PercLib.CriticalLRP.FiniteVolume.volWeightedSpatialMoment_flip_of_not_conn
#print axioms PercLib.CriticalLRP.FiniteVolume.spatialMoment_flip_sub_of_not_conn
#print axioms PercLib.CriticalLRP.FiniteVolume.hasDerivAt_expectation_spatialMoment
