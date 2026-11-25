/-
Copyright (c) 2026 PercLib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

New proofs for issue 165 (Q-24), written on 2026-11-14 by PROVER-E. No upstream proof is
copied.
-/
module

public import Mathlib.MeasureTheory.MeasurableSpace.NCard
public import PercLib.Percolation.Bond.Susceptibility
public import PercLib.Probability.Cylinder
public import PercLib.Probability.OpenEventHarris
public import PercLib.Probability.ProdBernoulliIndependence

/-!
# Global connectivity events

Events about the whole open graph: it is preconnected, it is connected, every cluster is
finite, every cluster has at most `n` vertices. This file proves that they are measurable
for countably many vertices, that connectivity is increasing, and three bounds:

* a spanning set of pairs gives `P(preconnected) ≥ ∏_{e ∈ T} q(e)`;
* on a finite vertex type, Harris gives `P(preconnected) ≥ ∏_{y ≠ x} τ(x, y)`;
* on a finite vertex type with two vertices, `P(preconnected) ≤ 1 - P(x isolated)` and
  `P(x isolated) = ∏_{y ≠ x} (1 - q(s(x, y)))`.

This file adds no definition.
-/

@[expose] public section

open MeasureTheory ProbabilityTheory Set PercLib.Probability
open scoped ENNReal
open Classical

namespace PercLib.Percolation.Bond

variable {V : Type*}

/-- Preconnectedness of the open graph is the intersection of all connection events. -/
theorem setOf_preconnected_eq :
    {ω : Config V | (openGraph ω).Preconnected} = ⋂ x, ⋂ y, conn x y := by
  ext ω
  simp only [mem_ofPred_eq, mem_iInter]
  rfl

/-- **Preconnectedness of the open graph is measurable.** -/
theorem measurableSet_preconnected [Countable V] :
    MeasurableSet {ω : Config V | (openGraph ω).Preconnected} := by
  rw [setOf_preconnected_eq]
  exact MeasurableSet.iInter fun x => MeasurableSet.iInter fun y => measurableSet_conn x y

/-- **Connectedness of the open graph is measurable.** -/
theorem measurableSet_connected [Countable V] :
    MeasurableSet {ω : Config V | (openGraph ω).Connected} := by
  have : {ω : Config V | (openGraph ω).Connected} =
      {ω : Config V | (openGraph ω).Preconnected} ∩ {_ω | Nonempty V} := by
    ext ω
    simp only [mem_ofPred_eq, mem_inter_iff, SimpleGraph.connected_iff]
  rw [this]
  exact measurableSet_preconnected.inter (MeasurableSet.const _)

/-- **The event that every cluster is finite is measurable.** -/
theorem measurableSet_forall_cluster_finite [Countable V] :
    MeasurableSet {ω : Config V | ∀ x, (cluster ω x).Finite} := by
  have : {ω : Config V | ∀ x, (cluster ω x).Finite} =
      ⋂ x, {ω : Config V | (cluster ω x).Infinite}ᶜ := by
    ext ω
    simp only [mem_iInter, mem_compl_iff, mem_ofPred_eq, Set.not_infinite]
  rw [this]
  exact MeasurableSet.iInter fun x => (measurableSet_cluster_infinite x).compl

/-- **The event that every cluster has at most `n` vertices is measurable.** -/
theorem measurableSet_forall_encard_cluster_le [Countable V] (n : ℕ∞) :
    MeasurableSet {ω : Config V | ∀ x, (cluster ω x).encard ≤ n} := by
  rw [ofPred_forall]
  exact MeasurableSet.iInter fun x =>
    measurable_encard_cluster x (Set.to_countable {k : ℕ∞ | k ≤ n}).measurableSet

/-- Preconnectedness of the open graph is an increasing event. -/
theorem isUpperSet_preconnected : IsUpperSet {ω : Config V | (openGraph ω).Preconnected} :=
  fun _ _ h hω => hω.mono (openGraph_mono h)

/-- Connectedness of the open graph is an increasing event. -/
theorem isUpperSet_connected : IsUpperSet {ω : Config V | (openGraph ω).Connected} :=
  fun _ _ h hω => hω.mono (openGraph_mono h)

/-- **Spanning-set lower bound.** If the pairs of `T` span a preconnected graph, the open
graph is preconnected with probability at least `∏_{e ∈ T} q(e)`. No countability is
needed, and diagonal pairs in `T` are allowed (they only lower the bound). -/
theorem prod_le_law_preconnected (q : Sym2 V → unitInterval) (T : Finset (Sym2 V))
    (hconn : (SimpleGraph.fromEdgeSet (T : Set (Sym2 V))).Preconnected) :
    (∏ e ∈ T, (unitInterval.toNNReal (q e) : ℝ≥0∞)) ≤ law q {ω | (openGraph ω).Preconnected} := by
  rw [← prodBernoulli_subset]
  exact measure_mono fun ω hω => hconn.mono (SimpleGraph.fromEdgeSet_mono hω)

/-- On a finite vertex type, the open graph is preconnected exactly when one vertex is
joined to all others. -/
theorem setOf_preconnected_eq_biInter [Fintype V] (x : V) :
    {ω : Config V | (openGraph ω).Preconnected} = ⋂ y ∈ Finset.univ.erase x, conn x y := by
  ext ω
  simp only [mem_ofPred_eq, mem_iInter, Finset.mem_erase, Finset.mem_univ, and_true]
  constructor
  · intro h y _
    exact h x y
  · intro h a b
    have hx : ∀ z, (openGraph ω).Reachable x z := fun z => by
      by_cases hz : z = x
      · rw [hz]
      · exact h z hz
    exact (hx a).symm.trans (hx b)

/-- **Harris lower bound.** On a finite vertex type, `P(preconnected) ≥ ∏_{y ≠ x} τ(x, y)`. -/
theorem prod_tau_le_law_preconnected [Fintype V] (q : Sym2 V → unitInterval) (x : V) :
    (∏ y ∈ Finset.univ.erase x, tau q x y) ≤ law q {ω | (openGraph ω).Preconnected} := by
  rw [setOf_preconnected_eq_biInter x]
  exact prodBernoulli_prod_le_biInter q _ (fun y => conn x y)
    (fun y _ => isUpperSet_conn x y) (fun y _ => measurableSet_conn x y)

/-- A vertex is isolated in the open graph exactly when every pair joining it to another
vertex is closed. -/
theorem setOf_isolated_eq (x : V) :
    {ω : Config V | ∀ y, ¬ (openGraph ω).Adj x y} = ⋂ y ∈ {y | y ≠ x}, {ω | s(x, y) ∉ ω} := by
  ext ω
  simp only [mem_ofPred_eq, mem_iInter, openGraph_adj_iff, not_and]
  exact ⟨fun h y hy hxy => h y hxy (Ne.symm hy), fun h y hxy hne => h y (Ne.symm hne) hxy⟩

/-- **Probability of an isolated vertex.** On a finite vertex type,
`P(x isolated) = ∏_{y ≠ x} (1 - q(s(x, y)))`. -/
theorem law_isolated [Fintype V] (q : Sym2 V → unitInterval) (x : V) :
    law q {ω : Config V | ∀ y, ¬ (openGraph ω).Adj x y} =
      ∏ y ∈ Finset.univ.erase x, (1 - (unitInterval.toNNReal (q s(x, y)) : ℝ≥0∞)) := by
  have hind : iIndep (fun e : Sym2 V => MeasurableSpace.comap (fun ω : Config V => e ∈ ω) ⊤)
      (law q) := (iIndepFun_iff_iIndep _ _ _).1 (prodBernoulli_iIndepFun_mem q)
  have hinj : Set.InjOn (fun y => s(x, y)) ↑(Finset.univ.erase x) :=
    fun a _ b _ h => Sym2.congr_right.1 h
  have hset : {ω : Config V | ∀ y, ¬ (openGraph ω).Adj x y} =
      ⋂ e ∈ (Finset.univ.erase x).image (fun y => s(x, y)), {ω : Config V | e ∉ ω} := by
    rw [setOf_isolated_eq]
    ext ω
    simp only [mem_iInter, Finset.mem_image, Finset.mem_erase, Finset.mem_univ, and_true,
      mem_ofPred_eq, forall_exists_index, and_imp]
    constructor
    · rintro h e y hy rfl
      exact h y hy
    · intro h y hy
      exact h _ y hy rfl
  rw [hset, hind.meas_biInter (fun e _ => ⟨{False}, trivial, by ext ω; simp⟩),
    Finset.prod_image hinj]
  refine Finset.prod_congr rfl fun y _ => ?_
  have hc : {ω : Config V | s(x, y) ∉ ω} = {ω : Config V | s(x, y) ∈ ω}ᶜ := rfl
  rw [hc, prob_compl_eq_one_sub (measurableSet_mem _)]
  change 1 - prodBernoulli q _ = _
  rw [prodBernoulli_setOf_mem]

/-- **Isolated-vertex upper bound.** If some vertex other than `x` exists, then
`P(preconnected) ≤ 1 - P(x isolated)`. -/
theorem law_preconnected_le_one_sub_isolated [Countable V] (q : Sym2 V → unitInterval) (x : V)
    (hV : ∃ y, y ≠ x) :
    law q {ω : Config V | (openGraph ω).Preconnected} ≤
      1 - law q {ω : Config V | ∀ y, ¬ (openGraph ω).Adj x y} := by
  have hiso : MeasurableSet {ω : Config V | ∀ y, ¬ (openGraph ω).Adj x y} := by
    rw [setOf_isolated_eq]
    exact MeasurableSet.biInter (Set.to_countable _) fun y _ => (measurableSet_mem _).compl
  rw [← prob_compl_eq_one_sub hiso]
  refine measure_mono fun ω hω hisol => ?_
  obtain ⟨y, hy⟩ := hV
  obtain ⟨z, hz⟩ := (SimpleGraph.mem_support _).1
    (SimpleGraph.mem_support_of_reachable (Ne.symm hy) (hω x y))
  exact hisol z hz

/-! ### Non-vacuity -/

/-- With no vertices the open graph is preconnected but not connected. -/
example (ω : Config Empty) : (openGraph ω).Preconnected ∧ ¬ (openGraph ω).Connected :=
  ⟨fun a => a.elim, fun h => (h.nonempty).elim fun a => a.elim⟩

/-- On `Fin 3` with `q ≡ 1/2`, the path `0 - 1 - 2` gives `P(preconnected) ≥ 1/4`. -/
example : (unitInterval.toNNReal (⟨1 / 2, by norm_num, by norm_num⟩ : unitInterval) : ℝ≥0∞) *
      (unitInterval.toNNReal (⟨1 / 2, by norm_num, by norm_num⟩ : unitInterval) : ℝ≥0∞) ≤
    law (fun _ : Sym2 (Fin 3) => (⟨1 / 2, by norm_num, by norm_num⟩ : unitInterval))
      {ω | (openGraph ω).Preconnected} := by
  have h := prod_le_law_preconnected
    (fun _ : Sym2 (Fin 3) => (⟨1 / 2, by norm_num, by norm_num⟩ : unitInterval))
    {s(0, 1), s(1, 2)} (by
      have h01 : (SimpleGraph.fromEdgeSet ((({s(0, 1), s(1, 2)} : Finset (Sym2 (Fin 3))) :
          Set (Sym2 (Fin 3))))).Adj 0 1 := by
        rw [SimpleGraph.fromEdgeSet_adj]; simp
      have h12 : (SimpleGraph.fromEdgeSet ((({s(0, 1), s(1, 2)} : Finset (Sym2 (Fin 3))) :
          Set (Sym2 (Fin 3))))).Adj 1 2 := by
        rw [SimpleGraph.fromEdgeSet_adj]; simp
      have hr : ∀ z : Fin 3, (SimpleGraph.fromEdgeSet ((({s(0, 1), s(1, 2)} :
          Finset (Sym2 (Fin 3))) : Set (Sym2 (Fin 3))))).Reachable 0 z := by
        intro z
        fin_cases z
        · exact SimpleGraph.Reachable.refl _
        · exact h01.reachable
        · exact h01.reachable.trans h12.reachable
      exact fun a b => (hr a).symm.trans (hr b))
  rwa [Finset.prod_pair (by decide)] at h

/-- On `Bool`, the vertex `false` is isolated with probability `1 - q(s(false, true))`, and
this bounds the probability that the open graph is preconnected. -/
example (q : Sym2 Bool → unitInterval) :
    law q {ω : Config Bool | ∀ y, ¬ (openGraph ω).Adj false y} =
        1 - (unitInterval.toNNReal (q s(false, true)) : ℝ≥0∞) ∧
      law q {ω : Config Bool | (openGraph ω).Preconnected} ≤
        1 - law q {ω : Config Bool | ∀ y, ¬ (openGraph ω).Adj false y} := by
  refine ⟨?_, law_preconnected_le_one_sub_isolated q false ⟨true, by decide⟩⟩
  rw [law_isolated]
  refine Finset.prod_eq_single_of_mem true (by simp) fun b hb hbt => ?_
  cases b
  · simp at hb
  · exact absurd rfl hbt

end PercLib.Percolation.Bond
