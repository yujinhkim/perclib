/-
Copyright (c) 2026 PercLib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

New for this project (issue 178, Q-28). No upstream proof is copied.
-/
module

public import PercLib.Percolation.Bond.Diagonal.Probability
public import PercLib.Probability.Coupling.Monotone
public import PercLib.Probability.OpenEventHarris
public import PercLib.Probability.Superposition

/-!
# Monotonicity of `τ`, `χ` and `θ` under embeddings of vertex sets

Let `f : V ↪ W` and let `q`, `q'` be profiles with `q e ≤ q' (Sym2.map f e)` for every
non-diagonal pair `e`. Then `τ`, `χ` and `θ` at `q` are at most those at `q'` at the image
points.

Route: pulling a configuration on `W` back along `Sym2.map f` turns `law q'` into
`law (q' ∘ Sym2.map f)` (identified on the all-open events of finite sets); connections in
the pulled-back configuration push forward along `f`; and `q`, with its diagonal set to `0`,
is dominated by `q' ∘ Sym2.map f`, so the monotone coupling S-2 and diagonal insensitivity
S-4 finish the comparison.
-/

@[expose] public section

noncomputable section

open MeasureTheory Set PercLib.Probability
open scoped ENNReal

namespace PercLib.Percolation.Bond

variable {V W : Type*}

/-! ### Pulling configurations back -/

theorem measurable_preimage_sym2Map (f : V → W) :
    Measurable fun ω : Config W => (Sym2.map f ⁻¹' ω : Config V) :=
  Measurable.of_mem fun e => measurable_set_mem (Sym2.map f e)

/-- Pulling a configuration back along an injection of vertex sets gives the law of the
pulled-back profile. No countability is needed. -/
theorem law_map_preimage_sym2Map (f : V ↪ W) (q' : Sym2 W → unitInterval) :
    (law q').map (fun ω : Config W => (Sym2.map f ⁻¹' ω : Config V)) =
      law (fun e => q' (Sym2.map f e)) := by
  have hm := measurable_preimage_sym2Map (f : V → W)
  have : IsProbabilityMeasure ((law q').map
      (fun ω : Config W => (Sym2.map f ⁻¹' ω : Config V))) :=
    (Measure.isProbabilityMeasure_map_iff hm.aemeasurable).2 inferInstance
  refine measure_ext_of_finset_subset _ _ fun F => ?_
  have hF : MeasurableSet {ω : Config V | (F : Set (Sym2 V)) ⊆ ω} :=
    generateFrom_finset_subset (ι := Sym2 V) ▸
      MeasurableSpace.measurableSet_generateFrom ⟨F, rfl⟩
  rw [Measure.map_apply hm hF]
  have hpre : (fun ω : Config W => (Sym2.map f ⁻¹' ω : Config V)) ⁻¹'
      {ω | (F : Set (Sym2 V)) ⊆ ω} =
        {ω : Config W | ((F.map f.sym2Map : Finset (Sym2 W)) : Set (Sym2 W)) ⊆ ω} := by
    ext ω
    simp [Set.subset_def]
  rw [hpre]
  simp only [law]
  rw [prodBernoulli_subset, prodBernoulli_subset, Finset.prod_map]
  rfl

/-- Connections in the pulled-back configuration push forward along `f`. -/
theorem mem_conn_of_preimage_sym2Map (f : V ↪ W) {ω : Config W} {x y : V}
    (h : (Sym2.map f ⁻¹' ω : Config V) ∈ conn x y) : ω ∈ conn (f x) (f y) := by
  let φ : openGraph (Sym2.map f ⁻¹' ω : Config V) →g openGraph ω :=
    ⟨f, fun {a b} hab => by
      rw [openGraph_adj_iff] at hab ⊢
      exact ⟨hab.1, f.injective.ne hab.2⟩⟩
  exact (h.map φ : (openGraph ω).Reachable (f x) (f y))

/-- Clusters of the pulled-back configuration push forward into clusters. -/
theorem image_cluster_preimage_sym2Map_subset (f : V ↪ W) (ω : Config W) (x : V) :
    f '' cluster (Sym2.map f ⁻¹' ω : Config V) x ⊆ cluster ω (f x) := by
  rintro _ ⟨y, hy, rfl⟩
  exact mem_conn_of_preimage_sym2Map f hy

/-! ### Comparison -/

open Classical in
theorem le_comp_sym2Map_of_dom (f : V ↪ W) {q : Sym2 V → unitInterval}
    {q' : Sym2 W → unitInterval}
    (hdom : ∀ e : Sym2 V, ¬ e.IsDiag → q e ≤ q' (Sym2.map f e)) :
    (fun e => if e.IsDiag then 0 else q e) ≤ fun e => q' (Sym2.map f e) := by
  intro e
  by_cases hd : e.IsDiag
  · simp only [hd, ite_true]
    exact bot_le
  · simp only [hd, ite_false]
    exact hdom e hd

section Comparison

variable [Countable V] (f : V ↪ W) {q : Sym2 V → unitInterval}
  {q' : Sym2 W → unitInterval}


/-- **Two-point function.** -/
theorem tau_le_of_embedding (hdom : ∀ e : Sym2 V, ¬ e.IsDiag → q e ≤ q' (Sym2.map f e))
    (x y : V) : tau q x y ≤ tau q' (f x) (f y) := by
  classical
  rw [tau_eq_of_offDiagonal q (fun e => if e.IsDiag then 0 else q e)
    (fun e hd => by simp [hd]) x y]
  refine (prodBernoulli_mono_event _ _ (le_comp_sym2Map_of_dom f hdom)
    (measurableSet_conn x y) (isUpperSet_conn x y)).trans ?_
  change law (fun e => q' (Sym2.map f e)) (conn x y) ≤ _
  rw [← law_map_preimage_sym2Map, Measure.map_apply (measurable_preimage_sym2Map _)
    (measurableSet_conn x y), tau]
  exact measure_mono fun ω h => mem_conn_of_preimage_sym2Map f h

/-- **Susceptibility.** -/
theorem chi_le_of_embedding (hdom : ∀ e : Sym2 V, ¬ e.IsDiag → q e ≤ q' (Sym2.map f e))
    (x : V) : chi q x ≤ chi q' (f x) := by
  classical
  have hmeas : Measurable fun ω : Config V => ((cluster ω x).encard : ℝ≥0∞) :=
    (Measurable.of_discrete (f := ((↑) : ℕ∞ → ℝ≥0∞))).comp (measurable_encard_cluster x)
  rw [chi_eq_of_offDiagonal q (fun e => if e.IsDiag then 0 else q e)
    (fun e hd => by simp [hd]) x]
  refine (lintegral_prodBernoulli_mono _ _ (le_comp_sym2Map_of_dom f hdom) hmeas
    fun _ _ hle => ENat.toENNReal_le.2
      (Set.encard_le_encard fun _ hy => conn_mono hle hy)).trans ?_
  change ∫⁻ ω, ((cluster ω x).encard : ℝ≥0∞) ∂law (fun e => q' (Sym2.map f e)) ≤ _
  rw [← law_map_preimage_sym2Map, lintegral_map hmeas (measurable_preimage_sym2Map _), chi]
  refine lintegral_mono fun ω => ENat.toENNReal_le.2 ?_
  rw [← f.injective.encard_image]
  exact Set.encard_le_encard (image_cluster_preimage_sym2Map_subset f ω x)

/-- **Infinite cluster.** -/
theorem law_cluster_infinite_le_of_embedding
    (hdom : ∀ e : Sym2 V, ¬ e.IsDiag → q e ≤ q' (Sym2.map f e)) (x : V) :
    law q {ω | (cluster ω x).Infinite} ≤ law q' {ω | (cluster ω (f x)).Infinite} := by
  classical
  rw [law_event_eq_of_offDiagonal q (fun e => if e.IsDiag then 0 else q e)
    (fun e hd => by simp [hd]) (measurableSet_cluster_infinite x) fun ω ω' h => by
      simp only [mem_ofPred_eq, cluster, ← openGraph_sdiff_diagSet ω, h,
        openGraph_sdiff_diagSet]]
  refine (prodBernoulli_mono_event _ _ (le_comp_sym2Map_of_dom f hdom)
    (measurableSet_cluster_infinite x)
    fun _ _ hle hinf => hinf.mono fun _ hy => conn_mono hle hy).trans ?_
  change law (fun e => q' (Sym2.map f e)) {ω | (cluster ω x).Infinite} ≤ _
  rw [← law_map_preimage_sym2Map, Measure.map_apply (measurable_preimage_sym2Map _)
    (measurableSet_cluster_infinite x)]
  refine measure_mono fun ω (h : (cluster _ x).Infinite) => ?_
  exact ((h.image f.injective.injOn).mono (image_cluster_preimage_sym2Map_subset f ω x))

end Comparison

/-! ### Non-vacuity -/

/-- Any embedding `ℕ ↪ ℤ` with the same constant profile on both sides. -/
example (f : ℕ ↪ ℤ) (t : unitInterval) (x y : ℕ) :
    tau (fun _ : Sym2 ℕ => t) x y ≤ tau (fun _ : Sym2 ℤ => t) (f x) (f y) :=
  tau_le_of_embedding f (q := fun _ => t) (q' := fun _ => t) (fun _ _ => le_rfl) x y

/-- The domination hypothesis may fail on the diagonal: there `q` is irrelevant. -/
example (f : ℕ ↪ ℤ) (x : ℕ) :
    chi (fun e : Sym2 ℕ => if e.IsDiag then 1 else 0) x ≤ chi (fun _ : Sym2 ℤ => 0) (f x) :=
  chi_le_of_embedding f (q := fun e => if e.IsDiag then 1 else 0) (q' := fun _ => 0)
    (fun e hd => by simp [hd]) x

end PercLib.Percolation.Bond

end
