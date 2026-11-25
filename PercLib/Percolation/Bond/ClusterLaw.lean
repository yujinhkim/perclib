/-
Copyright (c) 2026 PercLib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

New proofs for issue 190 (Q-30), written on 2026-11-15 by PROVER-E. No upstream proof is
copied.
-/
module

public import PercLib.Percolation.Bond.LocalConnectivity
public import PercLib.Probability.ProdBernoulliIndependence

/-!
# The law of a finite cluster and the domain Markov property

For a finite set `C ∋ x`, the cluster of `x` is `C` exactly when `C` is internally
connected to `x` and every boundary pair `s(y, z)`, `y ∈ C`, `z ∉ C`, is closed
(`cluster_eq_finset_iff`). These two events depend on the disjoint sets of internal and
boundary pairs, so `P(K_x = C)` factors (`law_cluster_eq_finset`). The event `{K_x = C}`
depends only on pairs meeting `C`, so it is independent of every event determined by the
outer pairs (`law_cluster_eq_inter`, the domain Markov property).

This file adds no definition. The independence of events determined by disjoint
coordinate sets is used through a private lemma; PROVER-F's Q-15 (#136) proves a public
version.
-/

@[expose] public section

open MeasureTheory Set PercLib.Probability

namespace PercLib.Percolation.Bond

variable {V : Type*}

/-- The image of a configuration of a coordinate block is measurable in the block. -/
private theorem measurable_image_val {ι : Type*} (S : Set ι) :
    Measurable fun u : Set S => (Subtype.val '' u : Set ι) := by
  classical
  refine Measurable.of_mem fun i => ?_
  by_cases hi : i ∈ S
  · have : (fun u : Set S => i ∈ Subtype.val '' u) = fun u => (⟨i, hi⟩ : S) ∈ u := by
      funext u; simp [hi]
    rw [this]
    exact measurable_set_mem _
  · have : (fun u : Set S => i ∈ Subtype.val '' u) = fun _ => False := by
      funext u; simp [hi]
    rw [this]
    exact measurable_const

/-- Events determined by disjoint coordinate sets are independent. -/
private theorem prodBernoulli_inter_of_determined {ι : Type*} (p : ι → unitInterval)
    (S T : Set ι) (hST : Disjoint S T) {E F : Set (Set ι)} (hE : MeasurableSet E)
    (hF : MeasurableSet F) (hEd : ∀ ω, ω ∈ E ↔ ω ∩ S ∈ E) (hFd : ∀ ω, ω ∈ F ↔ ω ∩ T ∈ F) :
    prodBernoulli p (E ∩ F) = prodBernoulli p E * prodBernoulli p F := by
  have himg : ∀ (R : Set ι) (ω : Set ι), Subtype.val '' {i : R | (i : ι) ∈ ω} = ω ∩ R := by
    intro R ω
    ext i
    simp [and_comm]
  have hE' : E = {ω | {i : S | (i : ι) ∈ ω} ∈ (fun u : Set S => Subtype.val '' u) ⁻¹' E} := by
    ext ω
    simp only [mem_ofPred_eq, mem_preimage, himg]
    exact hEd ω
  have hF' : F = {ω | {i : T | (i : ι) ∈ ω} ∈ (fun u : Set T => Subtype.val '' u) ⁻¹' F} := by
    ext ω
    simp only [mem_ofPred_eq, mem_preimage, himg]
    exact hFd ω
  have h := prodBernoulli_block_inter p S T hST _ _ (measurable_image_val S hE)
    (measurable_image_val T hF)
  rw [← hE', ← hF'] at h
  have hEF : E ∩ F = {ω | {i : S | (i : ι) ∈ ω} ∈ (fun u : Set S => Subtype.val '' u) ⁻¹' E ∧
      {i : T | (i : ι) ∈ ω} ∈ (fun u : Set T => Subtype.val '' u) ⁻¹' F} := by
    ext ω
    simp only [mem_inter_iff, mem_ofPred_eq, mem_preimage, himg]
    exact and_congr (hEd ω) (hFd ω)
  rw [hEF]
  exact h

/-- **The cluster of `x` is a finite set `C`** exactly when every vertex of `C` is joined to
`x` inside `C` and no pair leaving `C` is open. -/
theorem cluster_eq_finset_iff (ω : Config V) (x : V) (C : Finset V) (hx : x ∈ C) :
    cluster ω x = C ↔
      (∀ y : (C : Set V), ((openGraph ω).induce (C : Set V)).Reachable ⟨x, hx⟩ y) ∧
      ∀ y ∈ C, ∀ z ∉ C, s(y, z) ∉ ω := by
  classical
  constructor
  · intro h
    refine ⟨fun y => ?_, fun y hy z hz hyz => ?_⟩
    · have hxy : (openGraph ω).Reachable x y := by
        have : (y : V) ∈ cluster ω x := by rw [h]; exact y.2
        exact this
      obtain ⟨w⟩ := hxy
      have hw : ∀ v ∈ w.support, v ∈ (C : Set V) := fun v hv => by
        rw [← h]
        exact ⟨w.takeUntil v hv⟩
      exact ⟨w.induce (C : Set V) hw⟩
    · have hne : y ≠ z := fun e => hz (e ▸ hy)
      have hz' : z ∈ cluster ω x := by
        have hxy : (openGraph ω).Reachable x y := by
          have : y ∈ cluster ω x := by rw [h]; exact hy
          exact this
        exact hxy.trans (SimpleGraph.Adj.reachable ((openGraph_adj_iff ω y z).2 ⟨hyz, hne⟩))
      rw [h] at hz'
      exact hz hz'
  · rintro ⟨hin, hbd⟩
    ext v
    constructor
    · intro hv
      change (openGraph ω).Reachable x v at hv
      rw [SimpleGraph.reachable_iff_reflTransGen] at hv
      induction hv with
      | refl => exact hx
      | @tail w z _ hadj ih =>
        by_contra hz
        rw [openGraph_adj_iff] at hadj
        exact hbd w ih z hz hadj.1
    · intro hv
      exact conn_of_localConn ω (C : Set V) ⟨x, hx⟩ ⟨v, hv⟩ (hin ⟨v, hv⟩)

/-- The internal connection event of a finite set is measurable. -/
theorem measurableSet_internally_connected [Countable V] (x : V) (C : Finset V) (hx : x ∈ C) :
    MeasurableSet {ω : Config V |
      ∀ y : (C : Set V), ((openGraph ω).induce (C : Set V)).Reachable ⟨x, hx⟩ y} := by
  rw [ofPred_forall]
  exact MeasurableSet.iInter fun y => measurableSet_localConn (C : Set V) ⟨x, hx⟩ y

/-- The event that no pair leaving `C` is open is measurable. -/
theorem measurableSet_boundary_closed [Countable V] (C : Finset V) :
    MeasurableSet {ω : Config V | ∀ y ∈ C, ∀ z ∉ C, s(y, z) ∉ ω} := by
  simp only [ofPred_forall]
  exact MeasurableSet.iInter fun y => MeasurableSet.iInter fun _ =>
    MeasurableSet.iInter fun z => MeasurableSet.iInter fun _ => (measurableSet_mem _).compl

/-- The event `{K_x = C}` is measurable. -/
theorem measurableSet_cluster_eq_finset [Countable V] (x : V) (C : Finset V) (hx : x ∈ C) :
    MeasurableSet {ω : Config V | cluster ω x = C} := by
  have : {ω : Config V | cluster ω x = C} =
      {ω : Config V | ∀ y : (C : Set V), ((openGraph ω).induce (C : Set V)).Reachable ⟨x, hx⟩ y} ∩
        {ω : Config V | ∀ y ∈ C, ∀ z ∉ C, s(y, z) ∉ ω} := by
    ext ω
    exact cluster_eq_finset_iff ω x C hx
  rw [this]
  exact (measurableSet_internally_connected x C hx).inter (measurableSet_boundary_closed C)

/-- **The law of a finite cluster.** `P(K_x = C)` is the probability that `C` is internally
connected to `x`, times the probability that every pair leaving `C` is closed. -/
theorem law_cluster_eq_finset [Countable V] (q : Sym2 V → unitInterval) (x : V) (C : Finset V)
    (hx : x ∈ C) :
    law q {ω | cluster ω x = C} =
      law q {ω : Config V |
        ∀ y : (C : Set V), ((openGraph ω).induce (C : Set V)).Reachable ⟨x, hx⟩ y} *
      law q {ω : Config V | ∀ y ∈ C, ∀ z ∉ C, s(y, z) ∉ ω} := by
  have hset : {ω : Config V | cluster ω x = C} =
      {ω : Config V | ∀ y : (C : Set V), ((openGraph ω).induce (C : Set V)).Reachable ⟨x, hx⟩ y} ∩
        {ω : Config V | ∀ y ∈ C, ∀ z ∉ C, s(y, z) ∉ ω} := by
    ext ω
    exact cluster_eq_finset_iff ω x C hx
  rw [hset]
  refine prodBernoulli_inter_of_determined q {e | ∀ v ∈ e, v ∈ C}
    {e | ∃ y ∈ C, ∃ z ∉ C, e = s(y, z)} ?_ (measurableSet_internally_connected x C hx)
    (measurableSet_boundary_closed C) ?_ ?_
  · refine Set.disjoint_left.2 fun e he ⟨y, _, z, hz, hez⟩ => hz (he z ?_)
    rw [hez]; exact Sym2.mem_mk_right y z
  · intro ω
    simp only [mem_ofPred_eq]
    refine forall_congr' fun y => localConn_iff_of_agree (C : Set V) ⟨x, hx⟩ y
      fun a ha b hb => ?_
    have : s(a, b) ∈ {e : Sym2 V | ∀ v ∈ e, v ∈ C} := by
      intro v hv
      rcases Sym2.mem_iff.1 hv with rfl | rfl
      · exact ha
      · exact hb
    simp [this]
  · intro ω
    simp only [mem_ofPred_eq, mem_inter_iff]
    refine forall_congr' fun y => forall_congr' fun hy => forall_congr' fun z =>
      forall_congr' fun hz => ?_
    simp only [not_and]
    exact ⟨fun h hm => absurd hm h, fun h hm => h hm ⟨y, hy, z, hz, rfl⟩⟩

/-- `{K_x = C}` depends only on the pairs meeting `C`. -/
theorem cluster_eq_finset_determined (x : V) (C : Finset V) (hx : x ∈ C) (ω : Config V) :
    ω ∈ {ω : Config V | cluster ω x = C} ↔
      ω ∩ {e | ∃ v ∈ e, v ∈ C} ∈ {ω : Config V | cluster ω x = C} := by
  simp only [mem_ofPred_eq]
  rw [cluster_eq_finset_iff ω x C hx, cluster_eq_finset_iff _ x C hx]
  refine and_congr (forall_congr' fun y => localConn_iff_of_agree (C : Set V) ⟨x, hx⟩ y
    fun a ha b _ => ?_) (forall_congr' fun y => forall_congr' fun hy => forall_congr' fun z =>
      forall_congr' fun _ => ?_)
  · have : s(a, b) ∈ {e : Sym2 V | ∃ v ∈ e, v ∈ C} := ⟨a, Sym2.mem_mk_left a b, ha⟩
    simp [this]
  · have : s(y, z) ∈ {e : Sym2 V | ∃ v ∈ e, v ∈ C} := ⟨y, Sym2.mem_mk_left y z, hy⟩
    simp [this]

/-- **Domain Markov property.** `{K_x = C}` is independent of every measurable event
determined by the pairs with both endpoints outside `C`. -/
theorem law_cluster_eq_inter [Countable V] (q : Sym2 V → unitInterval) (x : V) (C : Finset V)
    (hx : x ∈ C) {B : Set (Config V)} (hB : MeasurableSet B)
    (hdet : ∀ ω ω', (∀ a ∉ C, ∀ b ∉ C, (s(a, b) ∈ ω ↔ s(a, b) ∈ ω')) → (ω ∈ B ↔ ω' ∈ B)) :
    law q ({ω | cluster ω x = C} ∩ B) = law q {ω | cluster ω x = C} * law q B := by
  refine prodBernoulli_inter_of_determined q {e | ∃ v ∈ e, v ∈ C} {e | ∀ v ∈ e, v ∉ C} ?_
    (measurableSet_cluster_eq_finset x C hx) hB (cluster_eq_finset_determined x C hx) ?_
  · exact Set.disjoint_left.2 fun e ⟨v, hv, hvC⟩ he => he v hv hvC
  · intro ω
    refine hdet _ _ fun a ha b hb => ?_
    have : s(a, b) ∈ {e : Sym2 V | ∀ v ∈ e, v ∉ C} := by
      intro v hv
      rcases Sym2.mem_iff.1 hv with rfl | rfl
      · exact ha
      · exact hb
    simp [this]

/-- **Corollary.** Off `C`, connections are independent of `{K_x = C}`. -/
theorem law_cluster_eq_inter_localConn_compl [Countable V] (q : Sym2 V → unitInterval) (x : V)
    (C : Finset V) (hx : x ∈ C) (y z : ((C : Set V)ᶜ : Set V)) :
    law q ({ω | cluster ω x = C} ∩
        {ω | ((openGraph ω).induce ((C : Set V)ᶜ)).Reachable y z}) =
      law q {ω | cluster ω x = C} *
        law q {ω | ((openGraph ω).induce ((C : Set V)ᶜ)).Reachable y z} :=
  law_cluster_eq_inter q x C hx (measurableSet_localConn _ y z) fun _ _ h =>
    localConn_iff_of_agree _ y z fun a ha b hb => h a ha b hb

/-! ### Non-vacuity -/

/-- `C = {x}`: the cluster of `x` is `{x}` with the probability that every pair at `x` is
closed. -/
example [Countable V] (q : Sym2 V → unitInterval) (x : V) :
    law q {ω | cluster ω x = (({x} : Finset V) : Set V)} =
      law q {ω : Config V | ∀ y ∈ ({x} : Finset V), ∀ z ∉ ({x} : Finset V), s(y, z) ∉ ω} := by
  rw [law_cluster_eq_finset q x {x} (Finset.mem_singleton_self x)]
  have : {ω : Config V | ∀ y : (({x} : Finset V) : Set V),
      ((openGraph ω).induce (({x} : Finset V) : Set V)).Reachable
        ⟨x, Finset.mem_singleton_self x⟩ y} = univ := by
    ext ω
    simp only [mem_ofPred_eq, mem_univ, iff_true]
    rintro ⟨y, hy⟩
    have : y = x := by simpa using hy
    subst this
    exact SimpleGraph.Reachable.refl _
  rw [this, measure_univ, one_mul]

end PercLib.Percolation.Bond
