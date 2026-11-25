/-
Copyright (c) 2026 PercLib contributors. Released under Apache 2.0.
New proofs, written for package Q-82 (issue 389, supports T-6), on the D-2 interface,
using mathlib's `Finset.sum_comp`. No source text or code is copied.
-/
module

public import PercLib.Percolation.Bond.Tightness.Defs
public import PercLib.Percolation.Bond.ClusterPartition
public import PercLib.Percolation.Bond.ClusterTails

/-! # The window partition of a finite set by open clusters

For a finite set `Λ` and a configuration `ω`, the traces of the open clusters on `Λ`,
`𝒞_Λ(ω) = {K(x) ∩ Λ : x ∈ Λ}`, are written as the image `Finset`
`Λ.image fun x => Λ.filter (· ∈ cluster ω x)` (no new definition).

* `sum_clusterIntersection_eq_sum_sq`: `∑_{x ∈ Λ} |K(x) ∩ Λ| = ∑_{D ∈ 𝒞_Λ} |D|²`.
* `sq_maxClusterIntersection_le_sum` and `sum_clusterIntersection_le`:
  `M_Λ² ≤ ∑_{x ∈ Λ} |K(x) ∩ Λ| ≤ M_Λ · |Λ|`.
* `sum_lintegral_clusterIntersection_eq`: `∑_{x ∈ Λ} E|K(x) ∩ Λ| = E ∑_{D ∈ 𝒞_Λ} |D|²`
  on a countable vertex type.

Items 1 and 2 hold for every `Λ`, including the empty set, and every configuration.
-/

@[expose] public section
noncomputable section

open MeasureTheory Set
open scoped ENNReal Classical

namespace PercLib.Percolation.Bond

variable {V : Type*}

/-- `|K(x) ∩ Λ|` as the cardinality of a filter of `Λ`. -/
theorem clusterIntersection_eq_card_filter (Λ : Finset V) (ω : Config V) (x : V) :
    clusterIntersection Λ ω x = (Λ.filter (· ∈ cluster ω x)).card := by
  rw [clusterIntersection, ← Set.ncard_coe_finset, Finset.coe_filter]
  congr 1
  ext y
  simp [and_comm]

/-- Two points of `Λ` have the same trace exactly when they are in the same cluster. -/
theorem filter_cluster_eq_iff (Λ : Finset V) (ω : Config V) {x a : V} (ha : a ∈ Λ) :
    Λ.filter (· ∈ cluster ω a) = Λ.filter (· ∈ cluster ω x) ↔ a ∈ cluster ω x := by
  constructor
  · intro h
    have : a ∈ Λ.filter (· ∈ cluster ω a) := Finset.mem_filter.2 ⟨ha, mem_cluster_self ω a⟩
    rw [h] at this
    exact (Finset.mem_filter.1 this).2
  · intro h
    have hc : cluster ω a = cluster ω x :=
      (cluster_eq_iff_conn ω a x).2 ((mem_cluster_iff ω x a).1 h).symm
    rw [hc]

/-- **Window partition** (wiki tag RU6O), item 1:
`∑_{x ∈ Λ} |K(x) ∩ Λ| = ∑_{D ∈ 𝒞_Λ} |D|²`. -/
theorem sum_clusterIntersection_eq_sum_sq (Λ : Finset V) (ω : Config V) :
    ∑ x ∈ Λ, clusterIntersection Λ ω x =
      ∑ D ∈ Λ.image (fun x => Λ.filter (· ∈ cluster ω x)), D.card ^ 2 := by
  simp_rw [clusterIntersection_eq_card_filter]
  rw [Finset.sum_comp (fun D : Finset V => D.card) (fun x => Λ.filter (· ∈ cluster ω x))]
  refine Finset.sum_congr rfl fun D hD => ?_
  obtain ⟨x, hx, rfl⟩ := Finset.mem_image.1 hD
  have hfib : Λ.filter (fun a => Λ.filter (· ∈ cluster ω a) = Λ.filter (· ∈ cluster ω x)) =
      Λ.filter (· ∈ cluster ω x) :=
    Finset.filter_congr fun a ha => filter_cluster_eq_iff Λ ω ha
  rw [hfib, smul_eq_mul, sq]

/-- Item 2, upper bound: `∑_{x ∈ Λ} |K(x) ∩ Λ| ≤ M_Λ · |Λ|`. -/
theorem sum_clusterIntersection_le (Λ : Finset V) (ω : Config V) :
    ∑ x ∈ Λ, clusterIntersection Λ ω x ≤ maxClusterIntersection Λ ω * Λ.card := by
  calc ∑ x ∈ Λ, clusterIntersection Λ ω x ≤ ∑ _x ∈ Λ, maxClusterIntersection Λ ω :=
        Finset.sum_le_sum fun x hx =>
          Finset.le_sup (f := fun v => (cluster ω v ∩ (Λ : Set V)).ncard) hx
    _ = maxClusterIntersection Λ ω * Λ.card := by rw [Finset.sum_const, smul_eq_mul, mul_comm]

/-- Item 2, lower bound: `M_Λ² ≤ ∑_{x ∈ Λ} |K(x) ∩ Λ|`. -/
theorem sq_maxClusterIntersection_le_sum (Λ : Finset V) (ω : Config V) :
    maxClusterIntersection Λ ω ^ 2 ≤ ∑ x ∈ Λ, clusterIntersection Λ ω x := by
  rcases Finset.eq_empty_or_nonempty Λ with rfl | hΛ
  · simp [maxClusterIntersection]
  obtain ⟨x, hx, hmax⟩ := Finset.exists_mem_eq_sup Λ hΛ
    (fun v => (cluster ω v ∩ (Λ : Set V)).ncard)
  rw [sum_clusterIntersection_eq_sum_sq]
  have hmem : Λ.filter (· ∈ cluster ω x) ∈ Λ.image (fun x => Λ.filter (· ∈ cluster ω x)) :=
    Finset.mem_image_of_mem _ hx
  have hM : maxClusterIntersection Λ ω = (Λ.filter (· ∈ cluster ω x)).card := by
    rw [maxClusterIntersection, hmax, ← clusterIntersection_eq_card_filter]; rfl
  rw [hM]
  exact Finset.single_le_sum (f := fun D : Finset V => D.card ^ 2)
    (fun _ _ => Nat.zero_le _) hmem

/-- `|K(x) ∩ Λ|` is measurable on a countable vertex type. -/
theorem measurable_clusterIntersection [Countable V] (Λ : Finset V) (x : V) :
    Measurable (fun ω : Config V => clusterIntersection Λ ω x) := by
  refine measurable_to_countable' fun n => ?_
  have h : (fun ω : Config V => clusterIntersection Λ ω x) ⁻¹' {n} =
      {ω | n ≤ (cluster ω x ∩ (Λ : Set V)).ncard} \
        {ω | n + 1 ≤ (cluster ω x ∩ (Λ : Set V)).ncard} := by
    ext ω
    simp only [Set.mem_preimage, Set.mem_singleton_iff, Set.mem_sdiff, Set.mem_ofPred_eq,
      clusterIntersection]
    omega
  rw [h]
  exact (measurableSet_cluster_tail x Λ n).diff (measurableSet_cluster_tail x Λ (n + 1))

/-- **Window partition** (wiki tag RU6O), item 3: on a countable vertex type, for every
profile, `∑_{x ∈ Λ} E|K(x) ∩ Λ| = E ∑_{D ∈ 𝒞_Λ} |D|²`. -/
theorem sum_lintegral_clusterIntersection_eq [Countable V] (q : Sym2 V → unitInterval)
    (Λ : Finset V) :
    ∑ x ∈ Λ, ∫⁻ ω, (clusterIntersection Λ ω x : ℝ≥0∞) ∂(law q) =
      ∫⁻ ω, ((∑ D ∈ Λ.image (fun x => Λ.filter (· ∈ cluster ω x)), D.card ^ 2 : ℕ) :
        ℝ≥0∞) ∂(law q) := by
  rw [← lintegral_finsetSum (f := fun x ω => (clusterIntersection Λ ω x : ℝ≥0∞)) _
    fun x _ => measurable_from_nat.comp (measurable_clusterIntersection Λ x)]
  refine lintegral_congr fun ω => ?_
  rw [← sum_clusterIntersection_eq_sum_sq, Nat.cast_sum]

/-! ### Non-vacuity (D-5) -/

/-- A singleton window: the sum is one. -/
example (ω : Config Unit) :
    ∑ x ∈ ({()} : Finset Unit), clusterIntersection {()} ω x = 1 ∧
      maxClusterIntersection {()} ω = 1 := by
  refine ⟨?_, maxClusterIntersection_singleton () ω⟩
  rw [Finset.sum_singleton, clusterIntersection_eq_card_filter]
  simp [mem_cluster_self]

/-- The empty configuration on a two-vertex window: two singleton traces, each of size one,
so both sides of item 1 equal two and `M_Λ = 1`. -/
example : ∑ x ∈ (Finset.univ : Finset Bool), clusterIntersection Finset.univ ∅ x = 2 ∧
    (Finset.univ.image (fun x : Bool =>
      (Finset.univ : Finset Bool).filter (· ∈ cluster (∅ : Config Bool) x))).card = 2 := by
  have h : ∀ x : Bool, (Finset.univ : Finset Bool).filter (· ∈ cluster (∅ : Config Bool) x) =
      {x} := by
    intro x; ext y; simp [cluster_empty]
  refine ⟨?_, ?_⟩
  · simp_rw [clusterIntersection_eq_card_filter, h]; rfl
  · simp_rw [h]; rfl

end PercLib.Percolation.Bond
