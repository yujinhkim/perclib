/-
Copyright (c) 2026 PercLib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

New proofs for issue 119 (Q-3), written on 2026-11-14 by PROVER-E. No upstream proof is
copied.
-/
module

public import PercLib.Percolation.Bond.Intensity.Defs
public import PercLib.Probability.Cylinder
public import PercLib.Probability.OpenEventHarris

/-!
# Root independence of percolation and of the critical intensity

Write `θ(x) = law q {ω | (cluster ω x).Infinite}`. This file proves:

* `tau_mul_law_cluster_infinite_le`: `τ(x, y) θ(x) ≤ θ(y)` (Harris);
* `tau_pos_of_reachable`: two vertices joined in the support graph of `q` are connected
  with positive probability;
* `law_cluster_infinite_pos_iff_of_preconnected`: if the support graph is preconnected,
  whether `θ` is positive does not depend on the root;
* `law_exists_cluster_infinite_pos_iff`: an infinite cluster exists with positive
  probability exactly when some `θ(x)` is positive;
* `globalCriticalIntensity_le_rootCriticalIntensity` and, for a preconnected support,
  `rootCriticalIntensity_eq_globalCriticalIntensity`.

This file adds no definition.
-/

@[expose] public section

open MeasureTheory Set PercLib.Probability
open scoped ENNReal NNReal

namespace PercLib.Percolation.Bond

variable {V : Type*}

/-- Connected vertices have the same cluster. -/
theorem cluster_eq_of_mem_conn {ω : Config V} {x y : V} (h : ω ∈ conn x y) :
    cluster ω x = cluster ω y := by
  ext z
  exact ⟨fun hz => SimpleGraph.Reachable.trans (SimpleGraph.Reachable.symm h) hz,
    fun hz => SimpleGraph.Reachable.trans h hz⟩

/-- **Percolation at one root forces percolation at another.** -/
theorem tau_mul_law_cluster_infinite_le [Countable V] (q : Sym2 V → unitInterval) (x y : V) :
    tau q x y * law q {ω | (cluster ω x).Infinite} ≤ law q {ω | (cluster ω y).Infinite} := by
  refine (law_harris_conn_cluster_infinite q x y x).trans (measure_mono ?_)
  rintro ω ⟨hxy, hx⟩
  change (cluster ω y).Infinite
  rwa [← cluster_eq_of_mem_conn hxy]

/-- A walk in the support graph is open as soon as its pairs are open. -/
theorem setOf_forall_mem_edges_subset_conn (q : Sym2 V → unitInterval) {x y : V}
    (w : (SimpleGraph.fromEdgeSet {e | 0 < q e}).Walk x y) :
    {ω : Config V | ∀ e ∈ w.edges, e ∈ ω} ⊆ conn x y := by
  intro ω hω
  refine ⟨w.transfer (openGraph ω) fun e he => ?_⟩
  have hG := w.edges_subset_edgeSet he
  rw [SimpleGraph.edgeSet_fromEdgeSet] at hG
  rw [openGraph, SimpleGraph.edgeSet_fromEdgeSet]
  exact ⟨hω e he, hG.2⟩

/-- **Vertices joined in the support graph are connected with positive probability.**
No countability is needed. -/
theorem tau_pos_of_reachable (q : Sym2 V → unitInterval) {x y : V}
    (h : (SimpleGraph.fromEdgeSet {e | 0 < q e}).Reachable x y) : 0 < tau q x y := by
  classical
  obtain ⟨w⟩ := h
  have hsub : {ω : Config V | ((w.edges.toFinset : Finset (Sym2 V)) : Set (Sym2 V)) ⊆ ω} ⊆
      {ω : Config V | ∀ e ∈ w.edges, e ∈ ω} := fun ω hω e he =>
    hω (by simpa using he)
  refine lt_of_lt_of_le ?_ (measure_mono (hsub.trans (setOf_forall_mem_edges_subset_conn q w)))
  change 0 < prodBernoulli q _
  rw [prodBernoulli_subset]
  refine CanonicallyOrderedAdd.prod_pos.2 fun e he => ?_
  have hG := w.edges_subset_edgeSet (List.mem_toFinset.1 he)
  rw [SimpleGraph.edgeSet_fromEdgeSet] at hG
  have hq : 0 < q e := hG.1
  exact ENNReal.coe_pos.2 hq

/-- **If the support graph is preconnected, positivity of `θ` does not depend on the
root.** -/
theorem law_cluster_infinite_pos_iff_of_preconnected [Countable V] (q : Sym2 V → unitInterval)
    (hq : (SimpleGraph.fromEdgeSet {e | 0 < q e}).Preconnected) (x y : V) :
    0 < law q {ω | (cluster ω x).Infinite} ↔ 0 < law q {ω | (cluster ω y).Infinite} := by
  have key : ∀ a b : V, 0 < law q {ω | (cluster ω a).Infinite} →
      0 < law q {ω | (cluster ω b).Infinite} := fun a b ha =>
    lt_of_lt_of_le (ENNReal.mul_pos (tau_pos_of_reachable q (hq a b)).ne' ha.ne')
      (tau_mul_law_cluster_infinite_le q a b)
  exact ⟨key x y, key y x⟩

/-- **An infinite cluster exists with positive probability exactly when some root
percolates with positive probability.** -/
theorem law_exists_cluster_infinite_pos_iff [Countable V] (q : Sym2 V → unitInterval) :
    0 < law q {ω | ∃ x, (cluster ω x).Infinite} ↔ ∃ x, 0 < law q {ω | (cluster ω x).Infinite} := by
  simp only [pos_iff_ne_zero, ofPred_exists, ne_eq, measure_iUnion_null_iff, not_forall]

/-- At intensity zero every pair is closed. -/
theorem intensityProfile_zero_apply (J : Sym2 V → ℝ≥0) (e : Sym2 V) :
    intensityProfile J 0 e = 0 := by
  apply Subtype.ext
  simp [intensityProfile]

/-- At a positive intensity a pair is open with positive probability exactly when its
intensity is positive. -/
theorem intensityProfile_pos_iff (J : Sym2 V → ℝ≥0) {β : ℝ≥0} (hβ : 0 < β) (e : Sym2 V) :
    0 < intensityProfile J β e ↔ 0 < J e := by
  change (0 : ℝ) < 1 - Real.exp (-(β : ℝ) * (J e : ℝ)) ↔ 0 < J e
  rw [sub_pos, Real.exp_lt_one_iff, neg_mul, neg_lt_zero]
  constructor
  · intro h
    exact pos_of_mul_pos_right h (le_of_lt (by exact_mod_cast hβ))
  · intro h
    exact mul_pos (by exact_mod_cast hβ) (by exact_mod_cast h)

/-- With every pair closed almost surely, almost surely no cluster is infinite. -/
theorem law_exists_cluster_infinite_eq_zero_of_forall_eq_zero [Countable V]
    {q : Sym2 V → unitInterval} (hq : ∀ e, q e = 0) :
    law q {ω | ∃ x, (cluster ω x).Infinite} = 0 := by
  refine measure_mono_null (t := ⋃ e : Sym2 V, {ω : Config V | e ∈ ω}) ?_ ?_
  · rintro ω ⟨x, hx⟩
    by_contra h
    simp only [mem_iUnion, mem_ofPred_eq, not_exists] at h
    have : ω = ∅ := eq_empty_of_forall_notMem h
    subst this
    rw [cluster_empty] at hx
    exact hx (finite_singleton x)
  · refine measure_iUnion_null fun e => ?_
    change prodBernoulli q {ω | e ∈ ω} = 0
    rw [prodBernoulli_setOf_mem, hq]
    simp

/-- The threshold for some infinite cluster is at most the threshold at any root. -/
theorem globalCriticalIntensity_le_rootCriticalIntensity (J : Sym2 V → ℝ≥0) (x : V) :
    globalCriticalIntensity J ≤ rootCriticalIntensity J x := by
  refine sInf_le_sInf ?_
  rintro b ⟨β, rfl, hβ⟩
  refine ⟨β, rfl, lt_of_lt_of_le hβ (measure_mono ?_)⟩
  intro ω hω
  exact ⟨x, hω⟩

/-- For a preconnected support, at each intensity percolation at a root and existence of
an infinite cluster have positive probability together. -/
theorem law_cluster_infinite_pos_iff_law_exists_of_preconnected [Countable V]
    (J : Sym2 V → ℝ≥0) (hJ : (SimpleGraph.fromEdgeSet {e | 0 < J e}).Preconnected)
    (x : V) (β : ℝ≥0) :
    0 < law (intensityProfile J β) {ω | (cluster ω x).Infinite} ↔
      0 < law (intensityProfile J β) {ω | ∃ y, (cluster ω y).Infinite} := by
  rcases eq_zero_or_pos β with rfl | hβ
  · have h0 := law_exists_cluster_infinite_eq_zero_of_forall_eq_zero
      (intensityProfile_zero_apply J)
    have h1 : law (intensityProfile J 0) {ω | (cluster ω x).Infinite} = 0 :=
      measure_mono_null (fun ω (hω : (cluster ω x).Infinite) => (⟨x, hω⟩ :
        ∃ y, (cluster ω y).Infinite)) h0
    rw [h0, h1]
  · have hsupp : {e | 0 < intensityProfile J β e} = {e | 0 < J e} := by
      ext e
      exact intensityProfile_pos_iff J hβ e
    have hpre : (SimpleGraph.fromEdgeSet {e | 0 < intensityProfile J β e}).Preconnected := by
      rw [hsupp]; exact hJ
    rw [law_exists_cluster_infinite_pos_iff]
    exact ⟨fun h => ⟨x, h⟩, fun ⟨y, hy⟩ =>
      (law_cluster_infinite_pos_iff_of_preconnected _ hpre y x).1 hy⟩

/-- **For a preconnected support the critical intensity does not depend on the root, and
equals the threshold for the existence of an infinite cluster.** -/
theorem rootCriticalIntensity_eq_globalCriticalIntensity [Countable V] (J : Sym2 V → ℝ≥0)
    (hJ : (SimpleGraph.fromEdgeSet {e | 0 < J e}).Preconnected) (x : V) :
    rootCriticalIntensity J x = globalCriticalIntensity J := by
  unfold rootCriticalIntensity globalCriticalIntensity
  congr 1
  ext b
  constructor
  · rintro ⟨β, rfl, h⟩
    exact ⟨β, rfl, (law_cluster_infinite_pos_iff_law_exists_of_preconnected J hJ x β).1 h⟩
  · rintro ⟨β, rfl, h⟩
    exact ⟨β, rfl, (law_cluster_infinite_pos_iff_law_exists_of_preconnected J hJ x β).2 h⟩

/-- For a preconnected support the root critical intensities agree. -/
theorem rootCriticalIntensity_eq_of_preconnected [Countable V] (J : Sym2 V → ℝ≥0)
    (hJ : (SimpleGraph.fromEdgeSet {e | 0 < J e}).Preconnected) (x y : V) :
    rootCriticalIntensity J x = rootCriticalIntensity J y := by
  rw [rootCriticalIntensity_eq_globalCriticalIntensity J hJ,
    rootCriticalIntensity_eq_globalCriticalIntensity J hJ]

/-! ### Non-vacuity -/

/-- On `Bool` with the one pair open with probability `1/2`, the support graph joins the
two vertices, so they are connected with positive probability. -/
example : 0 < tau (fun _ : Sym2 Bool => (⟨1 / 2, by norm_num, by norm_num⟩ : unitInterval))
    false true := by
  refine tau_pos_of_reachable _ (SimpleGraph.Adj.reachable ?_)
  rw [SimpleGraph.fromEdgeSet_adj]
  refine ⟨?_, by decide⟩
  change (0 : ℝ) < 1 / 2
  norm_num

/-- On `Unit` every support graph is preconnected, and the critical intensities agree. -/
example (J : Sym2 Unit → ℝ≥0) : rootCriticalIntensity J () = globalCriticalIntensity J :=
  rootCriticalIntensity_eq_globalCriticalIntensity J (fun a b => by
    cases a; cases b; exact SimpleGraph.Reachable.refl _) ()

/-- The preconnectedness hypothesis is not automatic: `J = 0` on `Bool`. -/
example : ¬ (SimpleGraph.fromEdgeSet {e : Sym2 Bool | 0 < (0 : Sym2 Bool → ℝ≥0) e}).Preconnected := by
  intro h
  obtain ⟨w⟩ := h false true
  cases w with
  | cons hadj _ =>
    rw [SimpleGraph.fromEdgeSet_adj] at hadj
    simp at hadj

end PercLib.Percolation.Bond
