/-
Migration source: https://github.com/yujinhkim/Critical-Long-range-percolation
Integration revision: 3b3d1d0e43ef940bfaa2292ee5c2ee094ac4edbf
Licence: Apache-2.0 for the PercLib Lean sources and tooling; see third_party/critical-lrp/.
External provenance and modifications are recorded in the file-specific notices below.
-/

/-
The `r`-derivative of the spatial moment of the cluster, in restored-cluster form.

This is the finite-volume, exact counterpart of the first displayed identity in the
proof of Lemma I.5.8 of Hutchcroft, "Critical long-range percolation I"
(arXiv:2508.18807v1), namely

  d/dr E_r [ sum_{x in K} <x,u>^2 ]
    = beta |J'(r)| * E_r [ sum_{x in K} sum_{y in B_r(x)} 1(y notin K) sum_{z in K_y} <z,u>^2 ],

where `K_y` is the cluster of `y` in the configuration in which the edge `{x,y}`
is closed. This is exactly the paper's `K_y` in that display, because the
derivative is taken at a configuration in which the edge is absent; in the
literature on the cutoff model the same object is called the restored cluster.

The finite model used here is the one of `FiniteGraphCluster` and
`VolumeMoments/SpatialMoments`: a finite vertex type `V`, a finite edge type `E`
with endpoint maps `s t : E → V`, a configuration `ω : Finset E` of open edges,
and the spatial moment `spatialMoment s t q o ω = sum_{x in K_o(ω)} q x` for an
arbitrary weight `q : V → ℝ` (in the paper `q x = <x,u>^2`; `q` is kept abstract
here so that the quadratic expansion of `q (z - x)` is not duplicated).

Content:
* the one-edge pivot `spatialMoment s t q o (insert e ω) - spatialMoment s t q o ω`
  is `0` when the endpoints of `e` are already connected, is the spatial moment of
  the *restored* cluster of the far endpoint when exactly one endpoint lies in
  `K_o(ω)`, and vanishes when neither endpoint lies in `K_o(ω)`;
* consequently the derivative of `r ↦ E_r [spatialMoment ...]` of the cutoff model
  is a sum over edges of length `≤ r` that meet the cluster of the origin, each
  carrying the spatial moment of the restored cluster at the other endpoint;
* for `q ≥ 0` the pivotal masses and hence this double sum are nonnegative, and
  `|spatialMoment|` is bounded by `sum_x |q x|`.

Nothing here assumes positivity, monotonicity or integrability of `q`; all
identities are exact finite sums.
-/
module

public import PercLib.CriticalLRP.VolumeMoments.SpatialMoments
public import PercLib.CriticalLRP.CutoffRusso

set_option linter.unusedSectionVars false
set_option linter.unusedSimpArgs false
set_option linter.unnecessarySimpa false
set_option linter.unusedTactic false
set_option linter.unusedVariables false

set_option autoImplicit true

@[expose] public section

open Finset

-- Connectivity is a decidable relation on a finite graph, but not by type
-- class inference; we use classical decidability for the `if`-expressions below.
attribute [local instance] Classical.propDecidable

namespace PercLib.CriticalLRP.FiniteVolume

variable {V : Type*} [Fintype V] [DecidableEq V]
variable {E : Type*} [Fintype E] [DecidableEq E]

/-! ### The one-edge pivot of the spatial moment -/

/-- Opening an edge whose endpoints are already connected changes no cluster, so
it does not change the spatial moment. -/
theorem spatialMoment_insert_of_conn {s t : E → V} (q : V → ℝ) (o : V) {e : E} {ω : Finset E}
    (hxy : Conn s t ω (s e) (t e)) :
    spatialMoment s t q o (insert e ω) = spatialMoment s t q o ω := by
  simp only [spatialMoment, cluster_insert_of_conn hxy o]

/-- Opening an edge none of whose endpoints is connected to the base point
changes nothing. (No hypothesis on the two endpoints is needed.) -/
theorem spatialMoment_insert_of_not_conn_both {s t : E → V} (q : V → ℝ) (o : V) {e : E}
    {ω : Finset E} (h1 : ¬ Conn s t ω o (s e)) (h2 : ¬ Conn s t ω o (t e)) :
    spatialMoment s t q o (insert e ω) = spatialMoment s t q o ω := by
  simp only [spatialMoment, cluster_insert_of_not_conn_both h1 h2]

/-- Opening an edge that attaches a new component at the endpoint `s e` of the
cluster of the base point adds the spatial moment of the other component. -/
theorem spatialMoment_insert_of_not_conn_of_conn_left {s t : E → V} (q : V → ℝ) (o : V)
    {e : E} {ω : Finset E} (hxy : ¬ Conn s t ω (s e) (t e)) (ho : Conn s t ω o (s e)) :
    spatialMoment s t q o (insert e ω) =
      spatialMoment s t q o ω + spatialMoment s t q (t e) ω := by
  have h1 : spatialMoment s t q o (insert e ω) = spatialMoment s t q (s e) (insert e ω) :=
    spatialMoment_base_of_conn q (conn_mono (subset_insert e ω) ho)
  have h2 : spatialMoment s t q o ω = spatialMoment s t q (s e) ω :=
    spatialMoment_base_of_conn q ho
  rw [h1, h2, spatialMoment_insert_of_not_conn q hxy]

/-- The symmetric form of the merge identity, based at `t e`: after opening `e`
the two components coincide, so the spatial moment of the component of `t e` is
the sum of the two old spatial moments. -/
theorem spatialMoment_insert_of_not_conn_right {s t : E → V} (q : V → ℝ) {e : E} {ω : Finset E}
    (hxy : ¬ Conn s t ω (s e) (t e)) :
    spatialMoment s t q (t e) (insert e ω) =
      spatialMoment s t q (t e) ω + spatialMoment s t q (s e) ω := by
  have hconn : Conn s t (insert e ω) (t e) (s e) := by
    rw [conn_insert_iff]
    exact Or.inr (Or.inr ⟨conn_refl s t ω (t e), conn_refl s t ω (s e)⟩)
  have h1 : spatialMoment s t q (t e) (insert e ω) =
      spatialMoment s t q (s e) (insert e ω) :=
    spatialMoment_base_of_conn q hconn
  rw [h1, spatialMoment_insert_of_not_conn q hxy]
  ring

/-- Opening an edge that attaches a new component at the endpoint `t e` of the
cluster of the base point adds the spatial moment of the other component. -/
theorem spatialMoment_insert_of_not_conn_of_conn_right {s t : E → V} (q : V → ℝ) (o : V)
    {e : E} {ω : Finset E} (hxy : ¬ Conn s t ω (s e) (t e)) (ho : Conn s t ω o (t e)) :
    spatialMoment s t q o (insert e ω) =
      spatialMoment s t q o ω + spatialMoment s t q (s e) ω := by
  have h1 : spatialMoment s t q o (insert e ω) = spatialMoment s t q (t e) (insert e ω) :=
    spatialMoment_base_of_conn q (conn_mono (subset_insert e ω) ho)
  have h2 : spatialMoment s t q o ω = spatialMoment s t q (t e) ω :=
    spatialMoment_base_of_conn q ho
  rw [h1, h2, spatialMoment_insert_of_not_conn_right q hxy]

/-- **One-edge pivot, closed form.** The increment of the spatial moment under
opening the single edge `e` is zero if the endpoints of `e` are already
connected; otherwise it is the spatial moment of the component that the edge
attaches, provided that this component is attached at an endpoint lying in the
cluster of the base point; and it is zero when neither endpoint lies in the
cluster. -/
theorem spatialMoment_flip_sub_eq_ite {s t : E → V} (q : V → ℝ) (e : E) (ω : Finset E)
    (o : V) :
    spatialMoment s t q o (insert e ω) - spatialMoment s t q o ω =
      if Conn s t ω (s e) (t e) then 0
      else if s e ∈ cluster s t ω o then spatialMoment s t q (t e) ω
      else if t e ∈ cluster s t ω o then spatialMoment s t q (s e) ω else 0 := by
  by_cases hxy : Conn s t ω (s e) (t e)
  · rw [ite_eq_left hxy, spatialMoment_insert_of_conn q o hxy]
    ring
  · rw [ite_eq_right hxy]
    by_cases h1 : s e ∈ cluster s t ω o
    · rw [ite_eq_left h1, spatialMoment_insert_of_not_conn_of_conn_left q o hxy (mem_cluster.mp h1)]
      ring
    · rw [ite_eq_right h1]
      by_cases h2 : t e ∈ cluster s t ω o
      · rw [ite_eq_left h2, spatialMoment_insert_of_not_conn_of_conn_right q o hxy (mem_cluster.mp h2)]
        ring
      · rw [ite_eq_right h2,
          spatialMoment_insert_of_not_conn_both q o (by simpa only [mem_cluster] using h1)
            (by simpa only [mem_cluster] using h2)]
        ring

/-- **One-edge pivot, restored-cluster form.** When the endpoints of `e` are not
connected, exactly one of them can lie in the cluster of the base point, and the
increment is the spatial moment of the *other* component, i.e. of the cluster of
the far endpoint in the configuration with `e` deleted. -/
theorem spatialMoment_flip_sub_eq_restored {s t : E → V} (q : V → ℝ) (e : E) (ω : Finset E)
    (o : V) (hxy : ¬ Conn s t ω (s e) (t e)) :
    spatialMoment s t q o (insert e ω) - spatialMoment s t q o ω =
      (if s e ∈ cluster s t ω o then spatialMoment s t q (t e) ω else 0) +
        (if t e ∈ cluster s t ω o then spatialMoment s t q (s e) ω else 0) := by
  rw [spatialMoment_flip_sub_eq_ite, ite_eq_right hxy]
  by_cases h1 : s e ∈ cluster s t ω o <;> by_cases h2 : t e ∈ cluster s t ω o
  · exact absurd ((conn_symm (mem_cluster.mp h1)).trans (mem_cluster.mp h2)) hxy
  · simp [h1, h2]
  · simp [h1, h2]
  · simp [h1, h2]

/-- If neither endpoint of `e` lies in the cluster of the base point, then
opening `e` does not change the spatial moment: this is the "no contribution"
half of the paper's restriction of the sum to `x ∈ K`, `y ∉ K`. -/
theorem spatialMoment_flip_sub_eq_zero_of_not_mem {s t : E → V} (q : V → ℝ) (e : E)
    (ω : Finset E) (o : V) (h1 : s e ∉ cluster s t ω o) (h2 : t e ∉ cluster s t ω o) :
    spatialMoment s t q o (insert e ω) - spatialMoment s t q o ω = 0 := by
  by_cases hxy : Conn s t ω (s e) (t e)
  · rw [spatialMoment_insert_of_conn q o hxy]; ring
  · rw [spatialMoment_insert_of_not_conn_both q o (by simpa only [mem_cluster] using h1)
      (by simpa only [mem_cluster] using h2)]
    ring

omit [DecidableEq V] [Fintype E] [DecidableEq E] in
/-- Consistency with Lemma I.4.1: the spatial moment of the constant weight `1`
is the cluster volume. -/
theorem spatialMoment_one_eq_card {s t : E → V} (o : V) (ω : Finset E) :
    spatialMoment s t (fun _ => (1 : ℝ)) o ω = ((cluster s t ω o).card : ℝ) := by
  simp [spatialMoment]

/-! ### The derivative in restored-cluster form -/

/-- Pointwise: the raw edgewise increment of the derivative is the pivot value. -/
theorem sum_pivotal_spatialMoment_eq (s t : E → V) (q : V → ℝ) (o : V) (len : E → ℝ)
    (p : E → ℝ) (r : ℝ) :
    (∑ e with len e ≤ r,
        ∑ τ with e ∉ τ,
          configurationLaw p τ *
            (spatialMoment s t q o (insert e τ) - spatialMoment s t q o τ)) =
      ∑ e with len e ≤ r,
        ∑ τ with e ∉ τ,
          configurationLaw p τ *
            (if Conn s t τ (s e) (t e) then 0
             else if s e ∈ cluster s t τ o then spatialMoment s t q (t e) τ
             else if t e ∈ cluster s t τ o then spatialMoment s t q (s e) τ else 0) := by
  refine Finset.sum_congr rfl ?_
  intro e _
  refine Finset.sum_congr rfl ?_
  intro τ _
  rw [spatialMoment_flip_sub_eq_ite]

/-- Pointwise: on configurations in which the edge is not a self-loop of the
cluster (its endpoints are unconnected), the pivot value is the sum of the two
restored-cluster contributions. -/
theorem sum_pivotal_spatialMoment_eq_restored (s t : E → V) (q : V → ℝ) (o : V)
    (len : E → ℝ) (p : E → ℝ) (r : ℝ) :
    (∑ e with len e ≤ r,
        ∑ τ with e ∉ τ,
          configurationLaw p τ *
            (if Conn s t τ (s e) (t e) then 0
             else if s e ∈ cluster s t τ o then spatialMoment s t q (t e) τ
             else if t e ∈ cluster s t τ o then spatialMoment s t q (s e) τ else 0)) =
      ∑ e with len e ≤ r,
        ∑ τ with e ∉ τ,
          configurationLaw p τ *
            (if Conn s t τ (s e) (t e) then 0
             else (if s e ∈ cluster s t τ o then spatialMoment s t q (t e) τ else 0) +
                  (if t e ∈ cluster s t τ o then spatialMoment s t q (s e) τ else 0)) := by
  refine Finset.sum_congr rfl ?_
  intro e _
  refine Finset.sum_congr rfl ?_
  intro τ _
  by_cases hτ : Conn s t τ (s e) (t e)
  · rw [ite_eq_left hτ, ite_eq_left hτ]
  · rw [ite_eq_right hτ, ite_eq_right hτ]
    have h2 : spatialMoment s t q o (insert e τ) - spatialMoment s t q o τ =
        (if s e ∈ cluster s t τ o then spatialMoment s t q (t e) τ
         else if t e ∈ cluster s t τ o then spatialMoment s t q (s e) τ else 0) := by
      rw [spatialMoment_flip_sub_eq_ite, ite_eq_right hτ]
    rw [← spatialMoment_flip_sub_eq_restored q e τ o hτ, h2]

/-- **The `r`-derivative of the cutoff-model expectation of the spatial moment**,
with each edgewise increment replaced by its one-edge pivot value: the edge
contributes only if it leaves the cluster of the origin, and then it contributes
the spatial moment of the restored cluster at the other endpoint. -/
theorem hasDerivAt_expectation_spatialMoment_pivot
    (s t : E → V) (q : V → ℝ) (o : V) (len : E → ℝ) (K : ℝ → ℝ) (K' : ℝ)
    {r β : ℝ} (hne : ∀ e, len e ≠ r) (hK : HasDerivAt K (-K') r) :
    HasDerivAt
      (fun r' => expectation (fun e => longRangeEdgeProbability β (cutoffProfile K r' (len e)))
        (spatialMoment s t q o))
      (β * K' * ∑ e with len e ≤ r,
        ∑ τ with e ∉ τ,
          configurationLaw (fun e => longRangeEdgeProbability β (cutoffProfile K r (len e))) τ *
            (if Conn s t τ (s e) (t e) then 0
             else if s e ∈ cluster s t τ o then spatialMoment s t q (t e) τ
             else if t e ∈ cluster s t τ o then spatialMoment s t q (s e) τ else 0)) r := by
  have h := hasDerivAt_expectation_spatialMoment s t q o len K K' hne hK (β := β)
  rw [sum_pivotal_spatialMoment_eq s t q o len
    (fun e => longRangeEdgeProbability β (cutoffProfile K r (len e))) r] at h
  exact h

/-- The same derivative with the summand split into its two restored-cluster
contributions. Since the two endpoints of a non-merging edge cannot both lie in
the cluster of the origin, at most one of the two terms is nonzero. -/
theorem hasDerivAt_expectation_spatialMoment_restored
    (s t : E → V) (q : V → ℝ) (o : V) (len : E → ℝ) (K : ℝ → ℝ) (K' : ℝ)
    {r β : ℝ} (hne : ∀ e, len e ≠ r) (hK : HasDerivAt K (-K') r) :
    HasDerivAt
      (fun r' => expectation (fun e => longRangeEdgeProbability β (cutoffProfile K r' (len e)))
        (spatialMoment s t q o))
      (β * K' * ∑ e with len e ≤ r,
        ∑ τ with e ∉ τ,
          configurationLaw (fun e => longRangeEdgeProbability β (cutoffProfile K r (len e))) τ *
            (if Conn s t τ (s e) (t e) then 0
             else (if s e ∈ cluster s t τ o then spatialMoment s t q (t e) τ else 0) +
                  (if t e ∈ cluster s t τ o then spatialMoment s t q (s e) τ else 0))) r := by
  have h := hasDerivAt_expectation_spatialMoment_pivot s t q o len K K' hne hK (β := β)
  rw [sum_pivotal_spatialMoment_eq_restored s t q o len
    (fun e => longRangeEdgeProbability β (cutoffProfile K r (len e))) r] at h
  exact h

/-! ### The volume-weighted moment `|K| S(K)`

The error terms of Lemma I.5.8 involve `|K| S(K)`, so the same pivot analysis is
needed for `volWeightedSpatialMoment`. The one-edge merge identity for that
observable is already proved in `VolumeMoments/SpatialMoments.lean`; here we give
its pivot form. -/

/-- Opening an edge whose endpoints are already connected does not change
`|K| S(K)`. -/
theorem volWeightedSpatialMoment_insert_of_conn {s t : E → V} (q : V → ℝ) (o : V) {e : E}
    {ω : Finset E} (hxy : Conn s t ω (s e) (t e)) :
    volWeightedSpatialMoment s t q o (insert e ω) = volWeightedSpatialMoment s t q o ω := by
  simp only [volWeightedSpatialMoment, spatialMoment, cluster_insert_of_conn hxy o]

/-- Opening an edge none of whose endpoints is connected to the base point does
not change `|K| S(K)`. -/
theorem volWeightedSpatialMoment_insert_of_not_conn_both {s t : E → V} (q : V → ℝ) (o : V)
    {e : E} {ω : Finset E} (h1 : ¬ Conn s t ω o (s e)) (h2 : ¬ Conn s t ω o (t e)) :
    volWeightedSpatialMoment s t q o (insert e ω) = volWeightedSpatialMoment s t q o ω := by
  simp only [volWeightedSpatialMoment, spatialMoment, cluster_insert_of_not_conn_both h1 h2]

/-- The pivot of `|K| S(K)` when the new component is attached at `s e`: the
increment is `|K_{t e}| S(K) + (|K_{s e}| + |K_{t e}|) S(K_{t e})`. -/
theorem volWeightedSpatialMoment_insert_of_not_conn_of_conn_left {s t : E → V} (q : V → ℝ)
    (o : V) {e : E} {ω : Finset E} (hxy : ¬ Conn s t ω (s e) (t e))
    (ho : Conn s t ω o (s e)) :
    volWeightedSpatialMoment s t q o (insert e ω) - volWeightedSpatialMoment s t q o ω =
      ((cluster s t ω (t e)).card : ℝ) * spatialMoment s t q o ω +
        (((cluster s t ω (s e)).card : ℝ) + ((cluster s t ω (t e)).card : ℝ)) *
          spatialMoment s t q (t e) ω := by
  have hconn' : Conn s t (insert e ω) o (s e) := conn_mono (subset_insert e ω) ho
  have h1 : volWeightedSpatialMoment s t q o (insert e ω) =
      volWeightedSpatialMoment s t q (s e) (insert e ω) := by
    simp only [volWeightedSpatialMoment, spatialMoment, cluster_eq_of_conn hconn']
  have h2 : volWeightedSpatialMoment s t q o ω = volWeightedSpatialMoment s t q (s e) ω := by
    simp only [volWeightedSpatialMoment, spatialMoment, cluster_eq_of_conn ho]
  rw [h1, h2, volWeightedSpatialMoment_flip_of_not_conn q hxy, spatialMoment_base_of_conn q ho]

/-- The pivot of `|K| S(K)` when the new component is attached at `t e`. -/
theorem volWeightedSpatialMoment_insert_of_not_conn_of_conn_right {s t : E → V} (q : V → ℝ)
    (o : V) {e : E} {ω : Finset E} (hxy : ¬ Conn s t ω (s e) (t e))
    (ho : Conn s t ω o (t e)) :
    volWeightedSpatialMoment s t q o (insert e ω) - volWeightedSpatialMoment s t q o ω =
      ((cluster s t ω (s e)).card : ℝ) * spatialMoment s t q o ω +
        (((cluster s t ω (s e)).card : ℝ) + ((cluster s t ω (t e)).card : ℝ)) *
          spatialMoment s t q (s e) ω := by
  have hconn' : Conn s t (insert e ω) o (t e) := conn_mono (subset_insert e ω) ho
  have h1 : volWeightedSpatialMoment s t q o (insert e ω) =
      volWeightedSpatialMoment s t q (t e) (insert e ω) := by
    simp only [volWeightedSpatialMoment, spatialMoment, cluster_eq_of_conn hconn']
  have h2 : volWeightedSpatialMoment s t q o ω = volWeightedSpatialMoment s t q (t e) ω := by
    simp only [volWeightedSpatialMoment, spatialMoment, cluster_eq_of_conn ho]
  have hflip : volWeightedSpatialMoment s t q (t e) (insert e ω) -
      volWeightedSpatialMoment s t q (t e) ω =
      ((cluster s t ω (s e)).card : ℝ) * spatialMoment s t q (t e) ω +
        (((cluster s t ω (t e)).card : ℝ) + ((cluster s t ω (s e)).card : ℝ)) *
          spatialMoment s t q (s e) ω := by
    simp only [volWeightedSpatialMoment]
    rw [card_cluster_insert_right hxy, spatialMoment_insert_of_not_conn_right q hxy]
    push_cast
    ring
  rw [h1, h2, hflip, spatialMoment_base_of_conn q ho]
  ring

/-- **Pivot of `|K| S(K)`, closed form.** -/
theorem volWeightedSpatialMoment_flip_sub_eq_ite (s t : E → V) (q : V → ℝ) (e : E)
    (ω : Finset E) (o : V) :
    volWeightedSpatialMoment s t q o (insert e ω) - volWeightedSpatialMoment s t q o ω =
      if Conn s t ω (s e) (t e) then 0
      else if s e ∈ cluster s t ω o then
        ((cluster s t ω (t e)).card : ℝ) * spatialMoment s t q o ω +
          (((cluster s t ω (s e)).card : ℝ) + ((cluster s t ω (t e)).card : ℝ)) *
            spatialMoment s t q (t e) ω
      else if t e ∈ cluster s t ω o then
        ((cluster s t ω (s e)).card : ℝ) * spatialMoment s t q o ω +
          (((cluster s t ω (s e)).card : ℝ) + ((cluster s t ω (t e)).card : ℝ)) *
            spatialMoment s t q (s e) ω
      else 0 := by
  by_cases hxy : Conn s t ω (s e) (t e)
  · rw [ite_eq_left hxy, volWeightedSpatialMoment_insert_of_conn q o hxy]
    ring
  · rw [ite_eq_right hxy]
    by_cases h1 : s e ∈ cluster s t ω o
    · rw [ite_eq_left h1,
        volWeightedSpatialMoment_insert_of_not_conn_of_conn_left q o hxy (mem_cluster.mp h1)]
    · rw [ite_eq_right h1]
      by_cases h2 : t e ∈ cluster s t ω o
      · rw [ite_eq_left h2,
          volWeightedSpatialMoment_insert_of_not_conn_of_conn_right q o hxy (mem_cluster.mp h2)]
      · rw [ite_eq_right h2,
          volWeightedSpatialMoment_insert_of_not_conn_both q o (by simpa only [mem_cluster] using h1)
            (by simpa only [mem_cluster] using h2)]
        ring

/-- Sum-level form of the preceding pointwise identity. -/
theorem sum_pivotal_volWeighted_eq (s t : E → V) (q : V → ℝ) (o : V) (len : E → ℝ)
    (p : E → ℝ) (r : ℝ) :
    (∑ e with len e ≤ r,
        ∑ τ with e ∉ τ,
          configurationLaw p τ *
            (volWeightedSpatialMoment s t q o (insert e τ) -
              volWeightedSpatialMoment s t q o τ)) =
      ∑ e with len e ≤ r,
        ∑ τ with e ∉ τ,
          configurationLaw p τ *
            (if Conn s t τ (s e) (t e) then 0
             else if s e ∈ cluster s t τ o then
               ((cluster s t τ (t e)).card : ℝ) * spatialMoment s t q o τ +
                 (((cluster s t τ (s e)).card : ℝ) + ((cluster s t τ (t e)).card : ℝ)) *
                   spatialMoment s t q (t e) τ
             else if t e ∈ cluster s t τ o then
               ((cluster s t τ (s e)).card : ℝ) * spatialMoment s t q o τ +
                 (((cluster s t τ (s e)).card : ℝ) + ((cluster s t τ (t e)).card : ℝ)) *
                   spatialMoment s t q (s e) τ
             else 0) := by
  refine Finset.sum_congr rfl ?_
  intro e _
  refine Finset.sum_congr rfl ?_
  intro τ _
  rw [volWeightedSpatialMoment_flip_sub_eq_ite]

/-- **The `r`-derivative of the cutoff-model expectation of `|K| S(K)`**, in
pivot form: the observable whose absolute value produces the two error terms of
Lemma I.5.8. -/
theorem hasDerivAt_expectation_volWeightedSpatialMoment_pivot
    (s t : E → V) (q : V → ℝ) (o : V) (len : E → ℝ) (K : ℝ → ℝ) (K' : ℝ)
    {r β : ℝ} (hne : ∀ e, len e ≠ r) (hK : HasDerivAt K (-K') r) :
    HasDerivAt
      (fun r' => expectation (fun e => longRangeEdgeProbability β (cutoffProfile K r' (len e)))
        (volWeightedSpatialMoment s t q o))
      (β * K' * ∑ e with len e ≤ r,
        ∑ τ with e ∉ τ,
          configurationLaw (fun e => longRangeEdgeProbability β (cutoffProfile K r (len e))) τ *
            (if Conn s t τ (s e) (t e) then 0
             else if s e ∈ cluster s t τ o then
               ((cluster s t τ (t e)).card : ℝ) * spatialMoment s t q o τ +
                 (((cluster s t τ (s e)).card : ℝ) + ((cluster s t τ (t e)).card : ℝ)) *
                   spatialMoment s t q (t e) τ
             else if t e ∈ cluster s t τ o then
               ((cluster s t τ (s e)).card : ℝ) * spatialMoment s t q o τ +
                 (((cluster s t τ (s e)).card : ℝ) + ((cluster s t τ (t e)).card : ℝ)) *
                   spatialMoment s t q (s e) τ
             else 0)) r := by
  have h := hasDerivAt_expectation_cutoff len K K' hne hK
    (volWeightedSpatialMoment s t q o) (β := β)
  rw [sum_pivotal_volWeighted_eq s t q o len
    (fun e => longRangeEdgeProbability β (cutoffProfile K r (len e))) r] at h
  exact h

/-- The spatial moment is nonnegative for nonnegative weights. -/
theorem spatialMoment_nonneg {s t : E → V} {q : V → ℝ} (hq : ∀ x, 0 ≤ q x) (o : V)
    (ω : Finset E) : 0 ≤ spatialMoment s t q o ω := by
  unfold spatialMoment
  exact Finset.sum_nonneg fun x _ => hq x

/-- The pivot of the constant weight `1`, i.e. of the cluster volume: this is the
finite form of the `|K_y|` summand of Lemma I.4.1. -/
theorem spatialMoment_one_flip_sub_eq_card {s t : E → V} (e : E) (ω : Finset E) (o : V)
    (hxy : ¬ Conn s t ω (s e) (t e)) :
    spatialMoment s t (fun _ => (1 : ℝ)) o (insert e ω) - spatialMoment s t (fun _ => (1 : ℝ)) o ω =
      (if s e ∈ cluster s t ω o then ((cluster s t ω (t e)).card : ℝ) else 0) +
        (if t e ∈ cluster s t ω o then ((cluster s t ω (s e)).card : ℝ) else 0) := by
  rw [spatialMoment_flip_sub_eq_restored (fun _ => (1 : ℝ)) e ω o hxy,
    spatialMoment_one_eq_card, spatialMoment_one_eq_card]

/-! ### The sum runs only over edges leaving the cluster -/

/-- Under a non-merging edge, the two endpoints cannot both lie in the cluster
of the origin: this is the `y ∉ K` of the paper's double sum. -/
theorem not_both_mem_cluster_of_not_conn {s t : E → V} {e : E} {τ : Finset E} {o : V}
    (hxy : ¬ Conn s t τ (s e) (t e)) :
    ¬ (s e ∈ cluster s t τ o ∧ t e ∈ cluster s t τ o) := by
  rintro ⟨h1, h2⟩
  exact hxy ((conn_symm (mem_cluster.mp h1)).trans (mem_cluster.mp h2))

/-- **Restriction of the derivative sum to edges leaving the cluster.** The
τ-summand can only be nonzero when at least one endpoint of the edge lies in the
cluster of the origin, so the double sum may be restricted accordingly. This is
the finite form of the paper's restriction of `Σ_{y ∈ B_r(x)}` to `y ∉ K`. -/
theorem sum_pivotal_spatialMoment_eq_sum_leaving (s t : E → V) (q : V → ℝ) (o : V)
    (len : E → ℝ) (p : E → ℝ) (r : ℝ) :
    (∑ e with len e ≤ r,
        ∑ τ with e ∉ τ,
          configurationLaw p τ *
            (spatialMoment s t q o (insert e τ) - spatialMoment s t q o τ)) =
      ∑ e with len e ≤ r,
        ∑ τ ∈ (univ.filter (fun τ => e ∉ τ)).filter
            (fun τ => s e ∈ cluster s t τ o ∨ t e ∈ cluster s t τ o),
          configurationLaw p τ *
            (spatialMoment s t q o (insert e τ) - spatialMoment s t q o τ) := by
  refine Finset.sum_congr rfl ?_
  intro e _
  refine (Finset.sum_subset ?_ ?_).symm
  · intro τ hτ
    simp only [mem_filter, mem_univ, true_and] at hτ ⊢
    exact hτ.1
  · intro τ hτ hτ'
    simp only [mem_filter, mem_univ, true_and] at hτ
    have hnot : ¬ (s e ∈ cluster s t τ o ∨ t e ∈ cluster s t τ o) := by
      intro h
      exact hτ' (by simp only [mem_filter, mem_univ, true_and]; exact ⟨hτ, h⟩)
    rw [spatialMoment_flip_sub_eq_zero_of_not_mem q e τ o (by tauto) (by tauto)]
    ring

/-! ### Sign and size -/

/-- The spatial moment is monotone in the configuration for nonnegative weights:
opening edges only adds vertices to the cluster. -/
theorem spatialMoment_mono {s t : E → V} {q : V → ℝ} (hq : ∀ x, 0 ≤ q x) (o : V)
    {ω ω' : Finset E} (h : ω ⊆ ω') :
    spatialMoment s t q o ω ≤ spatialMoment s t q o ω' := by
  unfold spatialMoment
  refine Finset.sum_le_sum_of_subset_of_nonneg ?_ ?_
  · intro x hx
    rw [mem_cluster] at hx ⊢
    exact conn_mono h hx
  · intro x _ _
    exact hq x

/-- For nonnegative weights the spatial moment is an increasing observable, so
every edgewise pivotal mass is nonnegative. -/
theorem pivotalMass_spatialMoment_nonneg {s t : E → V} {q : V → ℝ} (hq : ∀ x, 0 ≤ q x)
    (o : V) {p : E → ℝ} (hp : ∀ e, 0 ≤ p e) (hp1 : ∀ e, p e ≤ 1) (e : E) :
    0 ≤ pivotalMass p e (spatialMoment s t q o) :=
  pivotalMass_nonneg hp hp1 (fun _ _ h => spatialMoment_mono hq o h) e

/-- The pivotal double sum of the cutoff derivative is nonnegative for
nonnegative weights and edge probabilities in `[0,1]`: this is the sign content
behind the bare factor `β |J'(r)|` of Lemma I.4.1 / Lemma I.5.8. -/
theorem pivotalSum_spatialMoment_nonneg {s t : E → V} {q : V → ℝ} (hq : ∀ x, 0 ≤ q x)
    (o : V) {p : E → ℝ} (hp : ∀ e, 0 ≤ p e) (hp1 : ∀ e, p e ≤ 1) (len : E → ℝ) (r : ℝ) :
    0 ≤ ∑ e with len e ≤ r,
        ∑ τ with e ∉ τ,
          configurationLaw p τ *
            (spatialMoment s t q o (insert e τ) - spatialMoment s t q o τ) := by
  refine sum_nonneg fun e _ => ?_
  have h := one_sub_mul_pivotalMass p e (spatialMoment s t q o)
  have hpne : 0 ≤ 1 - p e := by linarith [hp1 e]
  have hnn := pivotalMass_spatialMoment_nonneg (s := s) (t := t) hq o hp hp1 e
  calc 0 ≤ (1 - p e) * pivotalMass p e (spatialMoment s t q o) := mul_nonneg hpne hnn
    _ = ∑ τ with e ∉ τ,
          configurationLaw p τ *
            (spatialMoment s t q o (insert e τ) - spatialMoment s t q o τ) := h

/-- Uniform size bound: the spatial moment is bounded by the total mass of the
weight. This is the integrability input used when passing to the countable
model. -/
theorem abs_spatialMoment_le {s t : E → V} (q : V → ℝ) (o : V) (ω : Finset E) :
    |spatialMoment s t q o ω| ≤ ∑ x, |q x| := by
  have h1 : |spatialMoment s t q o ω| ≤ ∑ x ∈ cluster s t ω o, |q x| := by
    rw [spatialMoment]
    exact Finset.abs_sum_le_sum_abs _ _
  refine h1.trans ?_
  refine Finset.sum_le_sum_of_subset_of_nonneg (fun x _ => mem_univ x) ?_
  intro x _ _
  exact abs_nonneg (q x)

end PercLib.CriticalLRP.FiniteVolume

#print axioms PercLib.CriticalLRP.FiniteVolume.spatialMoment_insert_of_conn
#print axioms PercLib.CriticalLRP.FiniteVolume.spatialMoment_insert_of_not_conn_both
#print axioms PercLib.CriticalLRP.FiniteVolume.spatialMoment_insert_of_not_conn_of_conn_left
#print axioms PercLib.CriticalLRP.FiniteVolume.spatialMoment_insert_of_not_conn_right
#print axioms PercLib.CriticalLRP.FiniteVolume.spatialMoment_insert_of_not_conn_of_conn_right
#print axioms PercLib.CriticalLRP.FiniteVolume.spatialMoment_flip_sub_eq_ite
#print axioms PercLib.CriticalLRP.FiniteVolume.spatialMoment_flip_sub_eq_restored
#print axioms PercLib.CriticalLRP.FiniteVolume.spatialMoment_flip_sub_eq_zero_of_not_mem
#print axioms PercLib.CriticalLRP.FiniteVolume.spatialMoment_one_eq_card
#print axioms PercLib.CriticalLRP.FiniteVolume.sum_pivotal_spatialMoment_eq
#print axioms PercLib.CriticalLRP.FiniteVolume.sum_pivotal_spatialMoment_eq_restored
#print axioms PercLib.CriticalLRP.FiniteVolume.hasDerivAt_expectation_spatialMoment_pivot
#print axioms PercLib.CriticalLRP.FiniteVolume.hasDerivAt_expectation_spatialMoment_restored
#print axioms PercLib.CriticalLRP.FiniteVolume.spatialMoment_mono
#print axioms PercLib.CriticalLRP.FiniteVolume.pivotalMass_spatialMoment_nonneg
#print axioms PercLib.CriticalLRP.FiniteVolume.pivotalSum_spatialMoment_nonneg
#print axioms PercLib.CriticalLRP.FiniteVolume.abs_spatialMoment_le
#print axioms PercLib.CriticalLRP.FiniteVolume.not_both_mem_cluster_of_not_conn
#print axioms PercLib.CriticalLRP.FiniteVolume.sum_pivotal_spatialMoment_eq_sum_leaving
#print axioms PercLib.CriticalLRP.FiniteVolume.volWeightedSpatialMoment_insert_of_conn
#print axioms PercLib.CriticalLRP.FiniteVolume.volWeightedSpatialMoment_insert_of_not_conn_both
#print axioms PercLib.CriticalLRP.FiniteVolume.volWeightedSpatialMoment_insert_of_not_conn_of_conn_left
#print axioms PercLib.CriticalLRP.FiniteVolume.volWeightedSpatialMoment_insert_of_not_conn_of_conn_right
#print axioms PercLib.CriticalLRP.FiniteVolume.volWeightedSpatialMoment_flip_sub_eq_ite
#print axioms PercLib.CriticalLRP.FiniteVolume.sum_pivotal_volWeighted_eq
#print axioms PercLib.CriticalLRP.FiniteVolume.hasDerivAt_expectation_volWeightedSpatialMoment_pivot
#print axioms PercLib.CriticalLRP.FiniteVolume.spatialMoment_nonneg
#print axioms PercLib.CriticalLRP.FiniteVolume.spatialMoment_one_flip_sub_eq_card
