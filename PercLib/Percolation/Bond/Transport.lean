/-
Copyright (c) 2026 PercLib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

New for this project (issue 125, Q-9). No upstream proof is copied.
-/
module

public import PercLib.Percolation.Bond.Basic
public import Mathlib.MeasureTheory.Integral.Lebesgue.Map
public import Mathlib.Data.Set.Card

/-!
# Transport of bond percolation along vertex bijections

For a bijection `σ : V ≃ W`, a configuration `ω : Config V` is pushed forward to
`Sym2.map σ '' ω : Config W`. This file shows that the open graph, connections and
clusters are carried along, that the push-forward is a measurable equivalence, and that
whenever it carries one law to another, the two-point function, the probability of an
infinite cluster and the susceptibility are carried along too. No countability is needed.

The hypothesis `(law q).map (fun ω => Sym2.map σ '' ω) = law q'` is supplied elsewhere
(S-1) when `q = q' ∘ Sym2.map σ`; it is not proved here.
-/

@[expose] public section

noncomputable section

open MeasureTheory Set
open scoped ENNReal

namespace PercLib.Percolation.Bond

variable {V W : Type*}

/-! ### Configurations -/

/-- A pair is open in the pushed-forward configuration exactly when its preimage is open. -/
theorem mem_image_sym2Map_iff (σ : V ≃ W) (ω : Config V) (e : Sym2 W) :
    e ∈ Sym2.map σ '' ω ↔ Sym2.map σ.symm e ∈ ω := by
  constructor
  · rintro ⟨e', he', rfl⟩
    rwa [Sym2.map_map, show (σ.symm ∘ σ) = id from funext σ.symm_apply_apply, Sym2.map_id,
      id]
  · intro h
    refine ⟨_, h, ?_⟩
    rw [Sym2.map_map, show (σ ∘ σ.symm) = id from funext σ.apply_symm_apply, Sym2.map_id, id]

/-- The pair of images is open in the pushed-forward configuration exactly when the pair
is open. -/
theorem mk_mem_image_sym2Map_iff (σ : V ≃ W) (ω : Config V) (a b : V) :
    s(σ a, σ b) ∈ Sym2.map σ '' ω ↔ s(a, b) ∈ ω := by
  rw [mem_image_sym2Map_iff, Sym2.map_mk, σ.symm_apply_apply, σ.symm_apply_apply]

/-- Pushing forward along `σ` and then along `σ.symm` gives back the configuration. -/
theorem image_sym2Map_symm_image (σ : V ≃ W) (ω : Config V) :
    Sym2.map σ.symm '' (Sym2.map σ '' ω) = ω := by
  ext e
  rw [mem_image_sym2Map_iff, Equiv.symm_symm, mem_image_sym2Map_iff, Sym2.map_map,
    σ.symm_comp_self, Sym2.map_id, id]

/-- Pushing forward along the identity does nothing. -/
theorem image_sym2Map_refl (ω : Config V) : Sym2.map (Equiv.refl V) '' ω = ω := by
  ext e
  rw [mem_image_sym2Map_iff, Equiv.refl_symm, Equiv.coe_refl, Sym2.map_id, id]

/-! ### Open graphs, connections and clusters -/

/-- Adjacency in the open graph is carried along `σ`. -/
theorem openGraph_image_adj_iff (σ : V ≃ W) (ω : Config V) (a b : V) :
    (openGraph (Sym2.map σ '' ω)).Adj (σ a) (σ b) ↔ (openGraph ω).Adj a b := by
  rw [openGraph_adj_iff, openGraph_adj_iff, mk_mem_image_sym2Map_iff, σ.injective.ne_iff]

/-- The open graph of the pushed-forward configuration is isomorphic to the open graph, by
an isomorphism whose underlying map is `σ`. -/
theorem nonempty_iso_openGraph_image (σ : V ≃ W) (ω : Config V) :
    ∃ φ : openGraph ω ≃g openGraph (Sym2.map σ '' ω), ⇑φ = σ :=
  ⟨⟨σ, fun {a b} => openGraph_image_adj_iff σ ω a b⟩, rfl⟩

/-- Connections are carried along `σ`. -/
theorem image_mem_conn_iff (σ : V ≃ W) (ω : Config V) (x y : V) :
    Sym2.map σ '' ω ∈ conn (σ x) (σ y) ↔ ω ∈ conn x y := by
  obtain ⟨φ, hφ⟩ := nonempty_iso_openGraph_image σ ω
  rw [mem_conn_iff, mem_conn_iff]
  simpa only [hφ] using SimpleGraph.Iso.reachable_iff (φ := φ) (u := x) (v := y)

/-- The connection event is the preimage of the transported connection event. -/
theorem preimage_conn_image (σ : V ≃ W) (x y : V) :
    (fun ω : Config V => Sym2.map σ '' ω) ⁻¹' conn (σ x) (σ y) = conn x y := by
  ext ω
  exact image_mem_conn_iff σ ω x y

/-- The cluster of `σ x` in the pushed-forward configuration is the image of the cluster
of `x`. -/
theorem cluster_image (σ : V ≃ W) (ω : Config V) (x : V) :
    cluster (Sym2.map σ '' ω) (σ x) = σ '' cluster ω x := by
  ext z
  rw [← σ.apply_symm_apply z, σ.injective.mem_set_image, mem_cluster_iff, mem_cluster_iff,
    image_mem_conn_iff]

/-- Cluster volumes are carried along `σ`. -/
theorem encard_cluster_image (σ : V ≃ W) (ω : Config V) (x : V) :
    (cluster (Sym2.map σ '' ω) (σ x)).encard = (cluster ω x).encard := by
  rw [cluster_image, σ.injective.encard_image]

/-- A cluster is infinite exactly when its transport is. -/
theorem cluster_image_infinite_iff (σ : V ≃ W) (ω : Config V) (x : V) :
    (cluster (Sym2.map σ '' ω) (σ x)).Infinite ↔ (cluster ω x).Infinite := by
  rw [cluster_image]
  exact Set.infinite_image_iff σ.injective.injOn

/-- The event of an infinite cluster is the preimage of the transported event. -/
theorem preimage_cluster_infinite_image (σ : V ≃ W) (x : V) :
    (fun ω : Config V => Sym2.map σ '' ω) ⁻¹' {ω' | (cluster ω' (σ x)).Infinite} =
      {ω | (cluster ω x).Infinite} := by
  ext ω
  exact cluster_image_infinite_iff σ ω x

/-- Escape events are carried along `σ`: leaving `σ '' F` from `σ x` in the transported
configuration is leaving `F` from `x`. -/
theorem preimage_escape_image (σ : V ≃ W) (x : V) (F : Set V) :
    (fun ω : Config V => Sym2.map σ '' ω) ⁻¹' (⋃ y ∈ (σ '' F)ᶜ, conn (σ x) y) =
      ⋃ y ∈ Fᶜ, conn x y := by
  ext ω
  simp only [mem_preimage, mem_iUnion, mem_compl_iff, exists_prop]
  constructor
  · rintro ⟨y, hy, hω⟩
    refine ⟨σ.symm y, fun h => hy ⟨_, h, σ.apply_symm_apply y⟩, ?_⟩
    rw [← image_mem_conn_iff σ, σ.apply_symm_apply]
    exact hω
  · rintro ⟨y, hy, hω⟩
    exact ⟨σ y, fun h => hy (σ.injective.mem_set_image.1 h), (image_mem_conn_iff σ ω x y).2 hω⟩

/-! ### Measurability -/

/-- Pushing configurations forward along `σ` is measurable. No countability is needed. -/
theorem measurable_image_sym2Map (σ : V ≃ W) :
    Measurable (fun ω : Config V => Sym2.map σ '' ω) := by
  refine Measurable.of_mem fun e => ?_
  simp_rw [mem_image_sym2Map_iff]
  exact measurable_set_mem _

/-- Pushing configurations forward along `σ` is a measurable equivalence. -/
theorem exists_measurableEquiv_image_sym2Map (σ : V ≃ W) :
    ∃ E : Config V ≃ᵐ Config W, ⇑E = fun ω => Sym2.map σ '' ω :=
  ⟨{ toFun := fun ω => Sym2.map σ '' ω
     invFun := fun ω => Sym2.map σ.symm '' ω
     left_inv := image_sym2Map_symm_image σ
     right_inv := fun ω => by
       simpa only [Equiv.symm_symm] using image_sym2Map_symm_image σ.symm ω
     measurable_toFun := measurable_image_sym2Map σ
     measurable_invFun := measurable_image_sym2Map σ.symm }, rfl⟩

/-- The measure of any set, measurable or not, under the push-forward law is the measure of
its preimage. -/
theorem map_image_sym2Map_apply (σ : V ≃ W) (μ : Measure (Config V)) (s : Set (Config W)) :
    μ.map (fun ω => Sym2.map σ '' ω) s = μ ((fun ω => Sym2.map σ '' ω) ⁻¹' s) := by
  obtain ⟨E, hE⟩ := exists_measurableEquiv_image_sym2Map σ
  rw [← hE]
  exact E.map_apply s

/-- Lower integrals against the push-forward law, for any integrand. -/
theorem lintegral_map_image_sym2Map (σ : V ≃ W) (μ : Measure (Config V))
    (f : Config W → ℝ≥0∞) :
    ∫⁻ ω, f ω ∂(μ.map (fun ω => Sym2.map σ '' ω)) = ∫⁻ ω, f (Sym2.map σ '' ω) ∂μ := by
  obtain ⟨E, hE⟩ := exists_measurableEquiv_image_sym2Map σ
  calc ∫⁻ ω, f ω ∂(μ.map (fun ω => Sym2.map σ '' ω)) = ∫⁻ ω, f ω ∂(μ.map E) := by rw [hE]
    _ = ∫⁻ ω, f (E ω) ∂μ := lintegral_map_equiv f E
    _ = _ := by rw [hE]

/-! ### Laws -/

variable {q : Sym2 V → unitInterval} {q' : Sym2 W → unitInterval}

/-- The two-point function is carried along `σ` when the laws are. -/
theorem tau_eq_of_map_law (σ : V ≃ W)
    (h : (law q).map (fun ω => Sym2.map σ '' ω) = law q') (x y : V) :
    tau q' (σ x) (σ y) = tau q x y := by
  rw [tau, ← h, map_image_sym2Map_apply, preimage_conn_image, tau]

/-- The probability that the cluster is infinite is carried along `σ` when the laws are. -/
theorem law_cluster_infinite_eq_of_map_law (σ : V ≃ W)
    (h : (law q).map (fun ω => Sym2.map σ '' ω) = law q') (x : V) :
    law q' {ω | (cluster ω (σ x)).Infinite} = law q {ω | (cluster ω x).Infinite} := by
  rw [← h, map_image_sym2Map_apply, preimage_cluster_infinite_image]

/-- The susceptibility is carried along `σ` when the laws are. No countability is needed. -/
theorem chi_eq_of_map_law (σ : V ≃ W)
    (h : (law q).map (fun ω => Sym2.map σ '' ω) = law q') (x : V) :
    chi q' (σ x) = chi q x := by
  rw [chi, ← h, lintegral_map_image_sym2Map]
  simp_rw [encard_cluster_image]
  rfl

/-! ### Automorphisms -/

section Automorphism

variable {p : Sym2 V → unitInterval}

/-- The two-point function is invariant under a vertex bijection that preserves the law. -/
theorem tau_apply_eq_of_map_law_eq (σ : V ≃ V)
    (h : (law p).map (fun ω => Sym2.map σ '' ω) = law p) (x y : V) :
    tau p (σ x) (σ y) = tau p x y :=
  tau_eq_of_map_law σ h x y

/-- The susceptibility is invariant under a vertex bijection that preserves the law. -/
theorem chi_apply_eq_of_map_law_eq (σ : V ≃ V)
    (h : (law p).map (fun ω => Sym2.map σ '' ω) = law p) (x : V) :
    chi p (σ x) = chi p x :=
  chi_eq_of_map_law σ h x

/-- The probability of an infinite cluster is invariant under a vertex bijection that
preserves the law. -/
theorem law_cluster_infinite_apply_eq_of_map_law_eq (σ : V ≃ V)
    (h : (law p).map (fun ω => Sym2.map σ '' ω) = law p) (x : V) :
    law p {ω | (cluster ω (σ x)).Infinite} = law p {ω | (cluster ω x).Infinite} :=
  law_cluster_infinite_eq_of_map_law σ h x

end Automorphism

/-! ### Non-vacuity -/

/-- The identity carries every law to itself, so the hypothesis of the transport theorems
holds for `σ = Equiv.refl`. -/
example (q : Sym2 V → unitInterval) :
    (law q).map (fun ω => Sym2.map (Equiv.refl V) '' ω) = law q := by
  simp_rw [image_sym2Map_refl]
  exact Measure.map_id

example (q : Sym2 V → unitInterval) (x y : V) :
    tau q ((Equiv.refl V) x) ((Equiv.refl V) y) = tau q x y :=
  tau_eq_of_map_law (Equiv.refl V) (by simp_rw [image_sym2Map_refl]; exact Measure.map_id) x y

/-- The swap of `Bool` carries the one-edge configuration to itself, and the loop at
`false` to the loop at `true`. -/
example : Sym2.map (Equiv.swap false true) '' ({s(false, true)} : Config Bool) =
    {s(false, true)} := by
  rw [Set.image_singleton, Sym2.map_mk, Equiv.swap_apply_left, Equiv.swap_apply_right,
    Sym2.eq_swap]

example : Sym2.map (Equiv.swap false true) '' ({s(false, false)} : Config Bool) =
    {s(true, true)} := by
  rw [Set.image_singleton, Sym2.map_mk, Equiv.swap_apply_left]

/-- In the one-edge configuration on `Bool`, the transported cluster of `true` is
the whole vertex set, as is the cluster of `false`. -/
example : cluster (Sym2.map (Equiv.swap false true) '' ({s(false, true)} : Config Bool))
    ((Equiv.swap false true) false) = (Equiv.swap false true) '' cluster {s(false, true)} false :=
  cluster_image _ _ _

end PercLib.Percolation.Bond

end
