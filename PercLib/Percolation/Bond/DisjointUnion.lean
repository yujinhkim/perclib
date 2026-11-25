/-
Copyright (c) 2026 PercLib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

New proofs for issue 234 (Q-51), written on 2026-11-15 by PROVER-E. No upstream proof is
copied.
-/
module

public import PercLib.Percolation.Bond.Susceptibility
public import PercLib.Probability.Cylinder
public import PercLib.Probability.ProdBernoulliIndependence
public import PercLib.Probability.Transport.Pullback

/-!
# Percolation on a disjoint union of vertex sets

On `V₁ ⊕ V₂` with no open pair between the two sides, the cluster of `Sum.inl a` is the image
of the cluster of `a` for the restricted configuration `Sym2.map Sum.inl ⁻¹' ω`, and
similarly for `Sum.inr`. If every cross pair has probability `0`, this holds almost surely,
the two restrictions are independent with the restricted profiles, and `τ`, `χ` and `θ`
factor through the two sides; the probability that some cluster is infinite is
`1 - (1 - P₁)(1 - P₂)`. This file adds no definition.
-/

@[expose] public section

open MeasureTheory Set PercLib.Probability
open scoped ENNReal

namespace PercLib.Percolation.Bond

/-! ### Clusters through an injective map whose range no open pair leaves -/

section Embedding

variable {V W : Type*}

/-- **Clusters inside a closed part.** If `f` is injective and no open pair joins its range to
the outside, the cluster of `f a` is the image of the cluster of `a` for the pulled-back
configuration. -/
theorem cluster_image_of_closed (ω : Config V) {f : W → V} (hf : Function.Injective f)
    (hclosed : ∀ a z, z ∉ range f → s(f a, z) ∉ ω) (a : W) :
    cluster ω (f a) = f '' cluster (Sym2.map f ⁻¹' ω) a := by
  ext y
  constructor
  · intro hy
    change (openGraph ω).Reachable (f a) y at hy
    rw [SimpleGraph.reachable_iff_reflTransGen] at hy
    induction hy with
    | refl => exact ⟨a, mem_cluster_self _ a, rfl⟩
    | @tail u z _ huz ih =>
      obtain ⟨b, hb, rfl⟩ := ih
      rw [openGraph_adj_iff] at huz
      by_cases hz : z ∈ range f
      · obtain ⟨c, rfl⟩ := hz
        refine ⟨c, ?_, rfl⟩
        have hbc : b ≠ c := fun h => huz.2 (h ▸ rfl)
        exact SimpleGraph.Reachable.trans hb (SimpleGraph.Adj.reachable
          ((openGraph_adj_iff _ b c).2 ⟨by simpa using huz.1, hbc⟩))
      · exact absurd huz.1 (hclosed b z hz)
  · rintro ⟨b, hb, rfl⟩
    change (openGraph (Sym2.map f ⁻¹' ω)).Reachable a b at hb
    refine hb.map ⟨f, fun {u v} huv => ?_⟩
    rw [openGraph_adj_iff] at huv ⊢
    exact ⟨by simpa using huv.1, hf.ne huv.2⟩

/-- The pulled-back configuration is measurable in the configuration. -/
theorem measurable_preimage_map (f : W → V) :
    Measurable fun ω : Config V => Sym2.map f ⁻¹' ω :=
  Measurable.of_mem fun e => (measurableSet_mem (Sym2.map f e)).mem

/-- The law of the pulled-back configuration is the pulled-back profile. -/
theorem law_map_preimage_map (q : Sym2 V → unitInterval) {f : W → V}
    (hf : Function.Injective f) :
    (law q).map (fun ω : Config V => Sym2.map f ⁻¹' ω) = law (q ∘ Sym2.map f) :=
  prodBernoulli_map_preimage q (Sym2.map.injective hf)

end Embedding

/-! ### Disjoint unions -/

variable {V₁ V₂ : Type*}

/-- The `inl` side: no open pair leaves it when no cross pair is open. -/
theorem closed_inl {ω : Config (V₁ ⊕ V₂)} (h : ∀ a b, s(Sum.inl a, Sum.inr b) ∉ ω) :
    ∀ a z, z ∉ range (Sum.inl : V₁ → V₁ ⊕ V₂) → s(Sum.inl a, z) ∉ ω := by
  intro a z hz
  cases z with
  | inl c => exact absurd ⟨c, rfl⟩ hz
  | inr c => exact h a c

/-- The `inr` side: no open pair leaves it when no cross pair is open. -/
theorem closed_inr {ω : Config (V₁ ⊕ V₂)} (h : ∀ a b, s(Sum.inl a, Sum.inr b) ∉ ω) :
    ∀ b z, z ∉ range (Sum.inr : V₂ → V₁ ⊕ V₂) → s(Sum.inr b, z) ∉ ω := by
  intro b z hz
  cases z with
  | inl c => rw [Sym2.eq_swap]; exact h c b
  | inr c => exact absurd ⟨c, rfl⟩ hz

/-- **Deterministic factorisation of clusters.** -/
theorem cluster_inl_eq {ω : Config (V₁ ⊕ V₂)} (h : ∀ a b, s(Sum.inl a, Sum.inr b) ∉ ω)
    (a : V₁) :
    cluster ω (Sum.inl a) = Sum.inl '' cluster (Sym2.map Sum.inl ⁻¹' ω) a :=
  cluster_image_of_closed ω Sum.inl_injective (closed_inl h) a

/-- **Deterministic factorisation of clusters** (`inr` side). -/
theorem cluster_inr_eq {ω : Config (V₁ ⊕ V₂)} (h : ∀ a b, s(Sum.inl a, Sum.inr b) ∉ ω)
    (b : V₂) :
    cluster ω (Sum.inr b) = Sum.inr '' cluster (Sym2.map Sum.inr ⁻¹' ω) b :=
  cluster_image_of_closed ω Sum.inr_injective (closed_inr h) b

/-- **Almost surely no cross pair is open.** -/
theorem ae_no_cross [Countable V₁] [Countable V₂] (q : Sym2 (V₁ ⊕ V₂) → unitInterval)
    (hq : ∀ a b, q s(Sum.inl a, Sum.inr b) = 0) :
    ∀ᵐ ω ∂law q, ∀ a b, s(Sum.inl a, Sum.inr b) ∉ ω := by
  rw [ae_all_iff]
  intro a
  rw [ae_all_iff]
  intro b
  rw [ae_iff]
  change prodBernoulli q {ω | ¬ s(Sum.inl a, Sum.inr b) ∉ ω} = 0
  simp only [not_not]
  rw [prodBernoulli_setOf_mem, hq]
  simp

private theorem measurable_image_val'' {ι : Type*} (S : Set ι) :
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

private theorem inter_of_determined' {ι : Type*} (p : ι → unitInterval)
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
  have h := prodBernoulli_block_inter p S T hST _ _ (measurable_image_val'' S hE)
    (measurable_image_val'' T hF)
  rw [← hE', ← hF'] at h
  have hEF : E ∩ F = {ω | {i : S | (i : ι) ∈ ω} ∈ (fun u : Set S => Subtype.val '' u) ⁻¹' E ∧
      {i : T | (i : ι) ∈ ω} ∈ (fun u : Set T => Subtype.val '' u) ⁻¹' F} := by
    ext ω
    simp only [mem_inter_iff, mem_ofPred_eq, mem_preimage, himg]
    exact and_congr (hEd ω) (hFd ω)
  rw [hEF]
  exact h

/-- **The two sides are independent.** -/
theorem law_preimage_inl_inter_inr (q : Sym2 (V₁ ⊕ V₂) → unitInterval)
    {A : Set (Config V₁)} {B : Set (Config V₂)} (hA : MeasurableSet A) (hB : MeasurableSet B) :
    law q ({ω | Sym2.map Sum.inl ⁻¹' ω ∈ A} ∩ {ω | Sym2.map Sum.inr ⁻¹' ω ∈ B}) =
      law (fun e => q (Sym2.map Sum.inl e)) A * law (fun e => q (Sym2.map Sum.inr e)) B := by
  have h1 : law q {ω | Sym2.map Sum.inl ⁻¹' ω ∈ A} = law (fun e => q (Sym2.map Sum.inl e)) A :=
    prodBernoulli_preimage_preimage q (Sym2.map.injective Sum.inl_injective) hA
  have h2 : law q {ω | Sym2.map Sum.inr ⁻¹' ω ∈ B} = law (fun e => q (Sym2.map Sum.inr e)) B :=
    prodBernoulli_preimage_preimage q (Sym2.map.injective Sum.inr_injective) hB
  rw [← h1, ← h2]
  refine inter_of_determined' q (range (Sym2.map Sum.inl)) (range (Sym2.map Sum.inr)) ?_
    (measurable_preimage_map Sum.inl hA) (measurable_preimage_map Sum.inr hB) ?_ ?_
  · refine Set.disjoint_left.2 ?_
    rintro _ ⟨e, rfl⟩ ⟨e', he'⟩
    induction e using Sym2.ind with
    | _ x y =>
    induction e' using Sym2.ind with
    | _ x' y' =>
    simp only [Sym2.map_mk, Sym2.eq_iff] at he'
    rcases he' with ⟨h, -⟩ | ⟨h, -⟩ <;> exact Sum.inr_ne_inl h
  · intro ω
    simp only [mem_ofPred_eq]
    rw [show Sym2.map Sum.inl ⁻¹' (ω ∩ range (Sym2.map Sum.inl)) = Sym2.map Sum.inl ⁻¹' ω by
      ext e; simp]
  · intro ω
    simp only [mem_ofPred_eq]
    rw [show Sym2.map Sum.inr ⁻¹' (ω ∩ range (Sym2.map Sum.inr)) = Sym2.map Sum.inr ⁻¹' ω by
      ext e; simp]

/-- **Two-point function within one side.** -/
theorem tau_inl_inl [Countable V₁] [Countable V₂] (q : Sym2 (V₁ ⊕ V₂) → unitInterval)
    (hq : ∀ a b, q s(Sum.inl a, Sum.inr b) = 0) (a b : V₁) :
    tau q (Sum.inl a) (Sum.inl b) = tau (fun e => q (Sym2.map Sum.inl e)) a b := by
  have hae : conn (Sum.inl a) (Sum.inl b) =ᵐ[law q]
      {ω : Config (V₁ ⊕ V₂) | Sym2.map Sum.inl ⁻¹' ω ∈ conn a b} := by
    filter_upwards [ae_no_cross q hq] with ω hω
    refine propext ?_
    change Sum.inl b ∈ cluster ω (Sum.inl a) ↔ b ∈ cluster _ a
    rw [cluster_inl_eq hω, Sum.inl_injective.mem_set_image]
  rw [tau, measure_congr hae]
  exact prodBernoulli_preimage_preimage q (Sym2.map.injective Sum.inl_injective)
    (measurableSet_conn a b)

/-- **No connection between the two sides.** -/
theorem tau_inl_inr [Countable V₁] [Countable V₂] (q : Sym2 (V₁ ⊕ V₂) → unitInterval)
    (hq : ∀ a b, q s(Sum.inl a, Sum.inr b) = 0) (a : V₁) (b : V₂) :
    tau q (Sum.inl a) (Sum.inr b) = 0 := by
  refine measure_mono_null (t := {ω | ¬ ∀ a b, s(Sum.inl a, Sum.inr b) ∉ ω}) ?_
    (ae_iff.1 (ae_no_cross q hq))
  intro ω hω hcross
  change Sum.inr b ∈ cluster ω (Sum.inl a) at hω
  rw [cluster_inl_eq hcross] at hω
  obtain ⟨c, -, hc⟩ := hω
  exact Sum.inl_ne_inr hc

/-- **Percolation within one side.** -/
theorem law_cluster_inl_infinite [Countable V₁] [Countable V₂]
    (q : Sym2 (V₁ ⊕ V₂) → unitInterval) (hq : ∀ a b, q s(Sum.inl a, Sum.inr b) = 0) (a : V₁) :
    law q {ω | (cluster ω (Sum.inl a)).Infinite} =
      law (fun e => q (Sym2.map Sum.inl e)) {ω | (cluster ω a).Infinite} := by
  have hae : {ω : Config (V₁ ⊕ V₂) | (cluster ω (Sum.inl a)).Infinite} =ᵐ[law q]
      {ω : Config (V₁ ⊕ V₂) | Sym2.map Sum.inl ⁻¹' ω ∈ {ω' | (cluster ω' a).Infinite}} := by
    filter_upwards [ae_no_cross q hq] with ω hω
    refine propext ?_
    rw [cluster_inl_eq hω, Set.infinite_image_iff Sum.inl_injective.injOn]
  rw [measure_congr hae]
  exact prodBernoulli_preimage_preimage q (Sym2.map.injective Sum.inl_injective)
    (measurableSet_cluster_infinite a)

/-- **Percolation within one side** (`inr`). -/
theorem law_cluster_inr_infinite [Countable V₁] [Countable V₂]
    (q : Sym2 (V₁ ⊕ V₂) → unitInterval) (hq : ∀ a b, q s(Sum.inl a, Sum.inr b) = 0) (b : V₂) :
    law q {ω | (cluster ω (Sum.inr b)).Infinite} =
      law (fun e => q (Sym2.map Sum.inr e)) {ω | (cluster ω b).Infinite} := by
  have hae : {ω : Config (V₁ ⊕ V₂) | (cluster ω (Sum.inr b)).Infinite} =ᵐ[law q]
      {ω : Config (V₁ ⊕ V₂) | Sym2.map Sum.inr ⁻¹' ω ∈ {ω' | (cluster ω' b).Infinite}} := by
    filter_upwards [ae_no_cross q hq] with ω hω
    refine propext ?_
    rw [cluster_inr_eq hω, Set.infinite_image_iff Sum.inr_injective.injOn]
  rw [measure_congr hae]
  exact prodBernoulli_preimage_preimage q (Sym2.map.injective Sum.inr_injective)
    (measurableSet_cluster_infinite b)

/-- **Susceptibility within one side.** -/
theorem chi_inl [Countable V₁] [Countable V₂] (q : Sym2 (V₁ ⊕ V₂) → unitInterval)
    (hq : ∀ a b, q s(Sum.inl a, Sum.inr b) = 0) (a : V₁) :
    chi q (Sum.inl a) = chi (fun e => q (Sym2.map Sum.inl e)) a := by
  have hae : (fun ω : Config (V₁ ⊕ V₂) => ((cluster ω (Sum.inl a)).encard : ℝ≥0∞)) =ᵐ[law q]
      fun ω => ((cluster (Sym2.map Sum.inl ⁻¹' ω) a).encard : ℝ≥0∞) := by
    filter_upwards [ae_no_cross q hq] with ω hω
    rw [cluster_inl_eq hω, Sum.inl_injective.encard_image]
  rw [chi, lintegral_congr_ae hae, chi]
  show _ = ∫⁻ ω, ((cluster ω a).encard : ℝ≥0∞) ∂law (q ∘ Sym2.map Sum.inl)
  rw [← law_map_preimage_map q Sum.inl_injective]
  exact (lintegral_map
    ((measurable_of_countable (fun n : ℕ∞ => (n : ℝ≥0∞))).comp (measurable_encard_cluster a))
    (measurable_preimage_map (Sum.inl : V₁ → V₁ ⊕ V₂))).symm

/-- **Some cluster is infinite:** `P = 1 - (1 - P₁)(1 - P₂)`. -/
theorem law_exists_cluster_infinite_sum [Countable V₁] [Countable V₂]
    (q : Sym2 (V₁ ⊕ V₂) → unitInterval) (hq : ∀ a b, q s(Sum.inl a, Sum.inr b) = 0) :
    law q {ω | ∃ x, (cluster ω x).Infinite} =
      1 - (1 - law (fun e => q (Sym2.map Sum.inl e)) {ω | ∃ x, (cluster ω x).Infinite}) *
        (1 - law (fun e => q (Sym2.map Sum.inr e)) {ω | ∃ x, (cluster ω x).Infinite}) := by
  have hE₁ : MeasurableSet {ω : Config V₁ | ∃ x, (cluster ω x).Infinite} := by
    rw [ofPred_exists]; exact MeasurableSet.iUnion fun x => measurableSet_cluster_infinite x
  have hE₂ : MeasurableSet {ω : Config V₂ | ∃ x, (cluster ω x).Infinite} := by
    rw [ofPred_exists]; exact MeasurableSet.iUnion fun x => measurableSet_cluster_infinite x
  have hE : MeasurableSet {ω : Config (V₁ ⊕ V₂) | ∃ x, (cluster ω x).Infinite} := by
    rw [ofPred_exists]; exact MeasurableSet.iUnion fun x => measurableSet_cluster_infinite x
  have hae : {ω : Config (V₁ ⊕ V₂) | ∃ x, (cluster ω x).Infinite}ᶜ =ᵐ[law q]
      {ω | Sym2.map Sum.inl ⁻¹' ω ∈ {ω' : Config V₁ | ∃ x, (cluster ω' x).Infinite}ᶜ} ∩
        {ω | Sym2.map Sum.inr ⁻¹' ω ∈ {ω' : Config V₂ | ∃ x, (cluster ω' x).Infinite}ᶜ} := by
    filter_upwards [ae_no_cross q hq] with ω hω
    refine propext ?_
    simp only [mem_compl_iff, mem_ofPred_eq, mem_inter_iff, not_exists]
    constructor
    · intro h
      exact ⟨fun x hx => h (Sum.inl x) (by rw [cluster_inl_eq hω,
        Set.infinite_image_iff Sum.inl_injective.injOn]; exact hx),
        fun x hx => h (Sum.inr x) (by rw [cluster_inr_eq hω,
        Set.infinite_image_iff Sum.inr_injective.injOn]; exact hx)⟩
    · rintro ⟨h1, h2⟩ x
      cases x with
      | inl x =>
        rw [cluster_inl_eq hω, Set.infinite_image_iff Sum.inl_injective.injOn]
        exact h1 x
      | inr x =>
        rw [cluster_inr_eq hω, Set.infinite_image_iff Sum.inr_injective.injOn]
        exact h2 x
  have hc := prob_compl_eq_one_sub (μ := law q) hE
  rw [measure_congr hae, law_preimage_inl_inter_inr q hE₁.compl hE₂.compl,
    prob_compl_eq_one_sub hE₁, prob_compl_eq_one_sub hE₂] at hc
  rw [hc, ENNReal.sub_sub_cancel ENNReal.one_ne_top prob_le_one]

/-! ### Non-vacuity: percolation depends on the root without irreducibility -/

/-- On two copies of `ℕ`, with every pair of the first copy open and nothing else,
the first copy percolates and the second does not. -/
example :
    let q : Sym2 (ℕ ⊕ ℕ) → unitInterval := fun e =>
      by classical exact if ∃ a b : ℕ, e = s(Sum.inl a, Sum.inl b) then 1 else 0
    law q {ω | (cluster ω (Sum.inl 0)).Infinite} = 1 ∧
      law q {ω | (cluster ω (Sum.inr 0)).Infinite} = 0 := by
  classical
  intro q
  have hq : ∀ a b, q s(Sum.inl a, Sum.inr b) = 0 := by
    intro a b
    simp only [q]
    rw [ite_eq_right_iff]
    rintro ⟨c, d, h⟩
    exfalso
    rcases Sym2.eq_iff.1 h with ⟨-, h2⟩ | ⟨-, h2⟩ <;> exact Sum.inr_ne_inl h2
  have hq₁ : (fun e => q (Sym2.map Sum.inl e)) = fun _ => 1 := by
    funext e
    induction e using Sym2.ind with
    | _ a b =>
    simp only [q, Sym2.map_mk]
    rw [ite_eq_left_iff]
    intro h
    exact absurd ⟨a, b, rfl⟩ h
  have hq₂ : (fun e => q (Sym2.map Sum.inr e)) = fun _ => 0 := by
    funext e
    induction e using Sym2.ind with
    | _ a b =>
    simp only [q, Sym2.map_mk]
    rw [ite_eq_right_iff]
    rintro ⟨c, d, h⟩
    exfalso
    rcases Sym2.eq_iff.1 h with ⟨h1, -⟩ | ⟨h1, -⟩ <;> exact Sum.inr_ne_inl h1
  rw [law_cluster_inl_infinite q hq, law_cluster_inr_infinite q hq, hq₁, hq₂]
  constructor
  · refine (prob_compl_eq_zero_iff (measurableSet_cluster_infinite 0)).1 ?_
    refine measure_mono_null (t := ⋃ e : Sym2 ℕ, {ω : Config ℕ | e ∈ ω}ᶜ) ?_ ?_
    · intro ω hω
      by_contra h
      simp only [mem_iUnion, mem_compl_iff, mem_ofPred_eq, not_exists, not_not] at h
      refine hω ?_
      have : cluster ω 0 = univ := eq_univ_of_forall fun y => by
        by_cases hy : (0 : ℕ) = y
        · rw [← hy]; exact mem_cluster_self ω 0
        · exact mem_conn_of_mem hy (h _)
      show (cluster ω 0).Infinite
      rw [this]
      exact infinite_univ
    · refine measure_iUnion_null fun e => (prob_compl_eq_zero_iff (measurableSet_mem e)).2 ?_
      simpa [law] using prodBernoulli_setOf_mem (fun _ : Sym2 ℕ => (1 : unitInterval)) e
  · refine measure_mono_null (t := ⋃ e : Sym2 ℕ, {ω : Config ℕ | e ∈ ω}) ?_ ?_
    · intro ω hω
      by_contra h
      simp only [mem_iUnion, mem_ofPred_eq, not_exists] at h
      have : ω = ∅ := eq_empty_of_forall_notMem h
      subst this
      rw [mem_ofPred_eq, cluster_empty] at hω
      exact hω (finite_singleton _)
    · exact measure_iUnion_null fun e => by
        simpa [law] using prodBernoulli_setOf_mem (fun _ : Sym2 ℕ => (0 : unitInterval)) e

end PercLib.Percolation.Bond
