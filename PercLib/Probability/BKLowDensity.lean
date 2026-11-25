/-
Copyright (c) 2026 PercLib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

Adapted from NearCritical/BK.lean at tomhutchcroft/near-critical-diffusivity,
revision c820fea91a7482c1755de0ec94ecb9f59ccfcacc, under Tom Hutchcroft's reuse
permission (DECISIONS R-3). The native source has no licence header; this is not
an assertion of an upstream Apache licence. No vendored network code is copied.
The adaptation uses Set configurations, IsUpperSet, and the single finite-certificate
convention. Standard image/preimage/insert replace auxiliary Boolean definitions.
-/
module

public import PercLib.Probability.DisjointOccurrence
public import PercLib.Probability.FiniteExpectation
public import Mathlib.Data.Fintype.Option
public import Mathlib.Logic.Equiv.Basic
public import Mathlib.Logic.Equiv.Set
public import Mathlib.Algebra.BigOperators.Option
public import Mathlib.Tactic.Linarith
public import Mathlib.Tactic.Ring

/-! # Low-density BK induction
The coordinate decomposition distinguishes a closed extra coordinate from an open
one. Disjointness is always the existing finite-coordinate certificate convention.
-/
@[expose] public section
noncomputable section
open Set MeasureTheory
open scoped Classical
namespace PercLib.Probability
variable {E : Type*}

/-- Closed-coordinate sections of increasing events are increasing. -/
theorem isUpperSet_preimage_some {A : Set (Set (Option E))} (hA : IsUpperSet A) :
    IsUpperSet ((fun η : Set E => Option.some '' η) ⁻¹' A) := by
  intro η θ h hη
  exact hA (image_mono h) hη

/-- Open-coordinate sections of increasing events are increasing. -/
theorem isUpperSet_preimage_insert_none {A : Set (Set (Option E))} (hA : IsUpperSet A) :
    IsUpperSet ((fun η : Set E => insert none (Option.some '' η)) ⁻¹' A) := by
  intro η θ h hη
  exact hA (insert_subset_insert (image_mono h)) hη

/-- Opening the extra coordinate enlarges an increasing event's section. -/
theorem section_closed_subset_open {A : Set (Set (Option E))} (hA : IsUpperSet A) :
    ((fun η : Set E => Option.some '' η) ⁻¹' A) ⊆
      ((fun η : Set E => insert none (Option.some '' η)) ⁻¹' A) :=
  fun _ h => hA (subset_insert _ _) h

/-- Closing the extra coordinate leaves disjoint occurrence exactly on the tail. -/
theorem disjointOccurrence_image_some_iff {A B : Set (Set (Option E))}
    (hA : IsUpperSet A) (hB : IsUpperSet B) (η : Set E) :
    Option.some '' η ∈ disjointOccurrence A B ↔
      η ∈ disjointOccurrence ((fun θ : Set E => Option.some '' θ) ⁻¹' A)
        ((fun θ : Set E => Option.some '' θ) ⁻¹' B) := by
  rw [mem_disjointOccurrence_iff_open hA hB,
    mem_disjointOccurrence_iff_open (isUpperSet_preimage_some hA) (isUpperSet_preimage_some hB)]
  constructor
  · rintro ⟨F, H, hF, hH, hd, hFη, hHη, hFA, hHB⟩
    refine ⟨Option.some ⁻¹' F, Option.some ⁻¹' H,
      hF.preimage (Option.some_injective E).injOn,
      hH.preimage (Option.some_injective E).injOn, hd.preimage _, ?_, ?_, ?_, ?_⟩
    · intro e he
      simpa using hFη he
    · intro e he
      simpa using hHη he
    · change Option.some '' (Option.some ⁻¹' F) ∈ A
      rw [image_preimage_eq_of_subset (hFη.trans (image_subset_range _ _))]
      exact hFA
    · change Option.some '' (Option.some ⁻¹' H) ∈ B
      rw [image_preimage_eq_of_subset (hHη.trans (image_subset_range _ _))]
      exact hHB
  · rintro ⟨F, H, hF, hH, hd, hFη, hHη, hFA, hHB⟩
    exact ⟨Option.some '' F, Option.some '' H, hF.image _, hH.image _,
      hd.image (Option.some_injective E).injOn (subset_univ _) (subset_univ _),
      image_mono hFη, image_mono hHη, hFA, hHB⟩

/-- In a disjoint occurrence at most one certificate uses the extra coordinate. -/
theorem disjointOccurrence_insert_none_subset {A B : Set (Set (Option E))}
    (hA : IsUpperSet A) (hB : IsUpperSet B) {η : Set E}
    (h : insert none (Option.some '' η) ∈ disjointOccurrence A B) :
    η ∈ disjointOccurrence ((fun θ : Set E => insert none (Option.some '' θ)) ⁻¹' A)
      ((fun θ : Set E => Option.some '' θ) ⁻¹' B) ∪
      disjointOccurrence ((fun θ : Set E => Option.some '' θ) ⁻¹' A)
        ((fun θ : Set E => insert none (Option.some '' θ)) ⁻¹' B) := by
  obtain ⟨F, H, hF, hH, hd, hFη, hHη, hFA, hHB⟩ :=
    (mem_disjointOccurrence_iff_open hA hB _).mp h
  have htail (K : Set (Option E)) (hK : K ⊆ insert none (Option.some '' η)) :
      Option.some ⁻¹' K ⊆ η := by
    intro e he
    simpa using hK he
  have hdecomp (K : Set (Option E)) :
      K ⊆ insert none (Option.some '' (Option.some ⁻¹' K)) := by
    intro e he
    cases e with
    | none => exact mem_insert _ _
    | some e => exact mem_insert_of_mem _ ⟨e, he, rfl⟩
  have hclosed (K : Set (Option E)) (hn : none ∉ K) :
      Option.some '' (Option.some ⁻¹' K) = K := by
    apply image_preimage_eq_of_subset
    intro e he
    cases e with
    | none => exact (hn he).elim
    | some e => exact ⟨e, rfl⟩
  by_cases hnH : none ∈ H
  · have hnF : none ∉ F := fun hnF => disjoint_left.mp hd hnF hnH
    apply Or.inr
    apply (mem_disjointOccurrence_iff_open (isUpperSet_preimage_some hA)
      (isUpperSet_preimage_insert_none hB) η).mpr
    refine ⟨Option.some ⁻¹' F, Option.some ⁻¹' H,
      hF.preimage (Option.some_injective E).injOn,
      hH.preimage (Option.some_injective E).injOn, hd.preimage _,
      htail F hFη, htail H hHη, ?_, ?_⟩
    · change Option.some '' (Option.some ⁻¹' F) ∈ A
      rwa [hclosed F hnF]
    · exact hB (hdecomp H) hHB
  · apply Or.inl
    apply (mem_disjointOccurrence_iff_open (isUpperSet_preimage_insert_none hA)
      (isUpperSet_preimage_some hB) η).mpr
    refine ⟨Option.some ⁻¹' F, Option.some ⁻¹' H,
      hF.preimage (Option.some_injective E).injOn,
      hH.preimage (Option.some_injective E).injOn, hd.preimage _,
      htail F hFη, htail H hHη, ?_, ?_⟩
    · exact hA (hdecomp F) hFA
    · change Option.some '' (Option.some ⁻¹' H) ∈ B
      rwa [hclosed H hnH]

/-- The algebraic closing step of the low-density induction. -/
theorem bk_step_arithmetic {p a0 a1 b0 b1 : ℝ} (ha : a0 ≤ a1) (hb : b0 ≤ b1) :
    (1 - 2 * p) * (a0 * b0) + p * (a1 * b0 + a0 * b1) ≤
      ((1 - p) * a0 + p * a1) * ((1 - p) * b0 + p * b1) := by
  have h := mul_nonneg (sq_nonneg p) (mul_nonneg (sub_nonneg.mpr ha) (sub_nonneg.mpr hb))
  nlinarith

/-- Split the finite sum over configurations according to the extra coordinate. -/
theorem sum_sets_option [Fintype E] (f : Set (Option E) → ℝ) :
    (∑ ω : Set (Option E), f ω) =
      (∑ η : Set E, f (Option.some '' η)) +
      ∑ η : Set E, f (insert none (Option.some '' η)) := by
  classical
  let e : Set (Option E) ≃ Bool × Set E :=
    { toFun := fun ω => (decide (none ∈ ω), Option.some ⁻¹' ω)
      invFun := fun p => if p.1 then insert none (Option.some '' p.2) else Option.some '' p.2
      left_inv := by
        intro ω
        ext a
        cases a <;> by_cases h : none ∈ ω <;> simp [h]
      right_inv := by
        rintro ⟨b, η⟩
        cases b <;> simp <;> ext e <;> simp }
  have h := (e.symm.sum_comp f).symm
  simpa [e, Fintype.sum_prod_type, Fintype.univ_bool, add_comm] using h

/-- The homogeneous finite expectation splits into closed and open sections. -/
theorem finiteExpectation_option [Fintype E] (p : ℝ) (f : Set (Option E) → ℝ) :
    finiteExpectation p f =
      (1-p) * finiteExpectation p (fun η => f (Option.some '' η)) +
      p * finiteExpectation p (fun η => f (insert none (Option.some '' η))) := by
  classical
  unfold finiteExpectation
  rw [sum_sets_option]
  simp [univ_option, Finset.mul_sum, mul_left_comm]

/-- The finite expectation is monotone for probability parameters. -/
theorem finiteExpectation_mono [Fintype E] {p : ℝ} (hp : 0 ≤ p) (hp1 : p ≤ 1)
    {f g : Set E → ℝ} (hfg : ∀ η, f η ≤ g η) : finiteExpectation p f ≤ finiteExpectation p g := by
  classical
  apply Finset.sum_le_sum
  intro η _
  apply mul_le_mul_of_nonneg_right (hfg η)
  apply Finset.prod_nonneg
  intro e _
  split <;> linarith

/-- Inclusion-exclusion bound for the open-coordinate section of disjoint occurrence. -/
theorem indicator_disjointOccurrence_insert_none_le {A B : Set (Set (Option E))}
    (hA : IsUpperSet A) (hB : IsUpperSet B) (η : Set E) :
    let A0 := (fun θ : Set E => Option.some '' θ) ⁻¹' A
    let A1 := (fun θ : Set E => insert none (Option.some '' θ)) ⁻¹' A
    let B0 := (fun θ : Set E => Option.some '' θ) ⁻¹' B
    let B1 := (fun θ : Set E => insert none (Option.some '' θ)) ⁻¹' B
    (disjointOccurrence A B).indicator (fun _ => (1 : ℝ)) (insert none (Option.some '' η)) ≤
      (disjointOccurrence A1 B0).indicator (fun _ => (1 : ℝ)) η +
      (disjointOccurrence A0 B1).indicator (fun _ => (1 : ℝ)) η -
      (disjointOccurrence A0 B0).indicator (fun _ => (1 : ℝ)) η := by
  dsimp only
  let A0 := (fun θ : Set E => Option.some '' θ) ⁻¹' A
  let A1 := (fun θ : Set E => insert none (Option.some '' θ)) ⁻¹' A
  let B0 := (fun θ : Set E => Option.some '' θ) ⁻¹' B
  let B1 := (fun θ : Set E => insert none (Option.some '' θ)) ⁻¹' B
  change _ ≤ (disjointOccurrence A1 B0).indicator _ η +
    (disjointOccurrence A0 B1).indicator _ η - (disjointOccurrence A0 B0).indicator _ η
  by_cases h0 : η ∈ disjointOccurrence A0 B0
  · have h10 : η ∈ disjointOccurrence A1 B0 := disjointOccurrence_mono (section_closed_subset_open hA) (Subset.refl B0) h0
    have h01 : η ∈ disjointOccurrence A0 B1 := disjointOccurrence_mono (Subset.refl A0) (section_closed_subset_open hB) h0
    simp only [indicator_of_mem h0, indicator_of_mem h10, indicator_of_mem h01]
    by_cases h : insert none (Option.some '' η) ∈ disjointOccurrence A B <;> simp [h]
  · simp only [indicator_of_notMem h0, sub_zero]
    by_cases h1 : insert none (Option.some '' η) ∈ disjointOccurrence A B
    · rcases disjointOccurrence_insert_none_subset hA hB h1 with h10 | h01
      · change η ∈ disjointOccurrence A1 B0 at h10
        simp only [indicator_of_mem h1, indicator_of_mem h10]
        by_cases h : η ∈ disjointOccurrence A0 B1 <;> simp [h]
      · change η ∈ disjointOccurrence A0 B1 at h01
        simp only [indicator_of_mem h1, indicator_of_mem h01]
        by_cases h : η ∈ disjointOccurrence A1 B0 <;> simp [h]
    · simp only [indicator_of_notMem h1]
      exact add_nonneg (indicator_nonneg (fun _ _ => by norm_num) _)
        (indicator_nonneg (fun _ _ => by norm_num) _)

/-- The weighted disjoint-occurrence recursion; the coefficient 1-2p is explicit. -/
theorem finiteExpectation_disjointOccurrence_option [Fintype E] {p : ℝ}
    (hp : 0 ≤ p) (hp1 : p ≤ 1) {A B : Set (Set (Option E))}
    (hA : IsUpperSet A) (hB : IsUpperSet B) :
    let A0 := (fun θ : Set E => Option.some '' θ) ⁻¹' A
    let A1 := (fun θ : Set E => insert none (Option.some '' θ)) ⁻¹' A
    let B0 := (fun θ : Set E => Option.some '' θ) ⁻¹' B
    let B1 := (fun θ : Set E => insert none (Option.some '' θ)) ⁻¹' B
    let ep := fun C : Set (Set E) => finiteExpectation p (C.indicator (fun _ => (1 : ℝ)))
    finiteExpectation p ((disjointOccurrence A B).indicator (fun _ => (1 : ℝ))) ≤
      (1-2*p) * ep (disjointOccurrence A0 B0) +
        p * (ep (disjointOccurrence A1 B0) + ep (disjointOccurrence A0 B1)) := by
  classical
  dsimp only
  let A0 := (fun θ : Set E => Option.some '' θ) ⁻¹' A
  let A1 := (fun θ : Set E => insert none (Option.some '' θ)) ⁻¹' A
  let B0 := (fun θ : Set E => Option.some '' θ) ⁻¹' B
  let B1 := (fun θ : Set E => insert none (Option.some '' θ)) ⁻¹' B
  let ep := fun C : Set (Set E) => finiteExpectation p (C.indicator (fun _ => (1 : ℝ)))
  have hfalse : (fun η : Set E => (disjointOccurrence A B).indicator (fun _ => (1 : ℝ))
      (Option.some '' η)) = (disjointOccurrence A0 B0).indicator (fun _ => (1 : ℝ)) := by
    funext η
    simp only [indicator, disjointOccurrence_image_some_iff hA hB]
    rfl
  have htrue := finiteExpectation_mono hp hp1
    (fun η => indicator_disjointOccurrence_insert_none_le hA hB η)
  have hlin : finiteExpectation p (fun η : Set E =>
      (disjointOccurrence A1 B0).indicator (fun _ => (1 : ℝ)) η +
      (disjointOccurrence A0 B1).indicator (fun _ => (1 : ℝ)) η -
      (disjointOccurrence A0 B0).indicator (fun _ => (1 : ℝ)) η) =
      ep (disjointOccurrence A1 B0) + ep (disjointOccurrence A0 B1) -
        ep (disjointOccurrence A0 B0) := by
    simp only [ep, finiteExpectation, add_mul, sub_mul, Finset.sum_add_distrib,
      Finset.sum_sub_distrib]
  change _ ≤ finiteExpectation p (fun η : Set E =>
      (disjointOccurrence A1 B0).indicator (fun _ => (1 : ℝ)) η +
      (disjointOccurrence A0 B1).indicator (fun _ => (1 : ℝ)) η -
      (disjointOccurrence A0 B0).indicator (fun _ => (1 : ℝ)) η) at htrue
  rw [hlin] at htrue
  rw [finiteExpectation_option, hfalse]
  change (1-p) * ep (disjointOccurrence A0 B0) + _ ≤
    (1-2*p) * ep (disjointOccurrence A0 B0) +
      p * (ep (disjointOccurrence A1 B0) + ep (disjointOccurrence A0 B1))
  nlinarith [mul_le_mul_of_nonneg_left htrue hp]

/-- Low-density BK propagates across one additional coordinate. -/
theorem lowDensityBK_option [Fintype E] {p : ℝ} (hp : 0 ≤ p) (hpHalf : p ≤ 1/2)
    (hBK : ∀ A B : Set (Set E), IsUpperSet A → IsUpperSet B →
      finiteExpectation p ((disjointOccurrence A B).indicator (fun _ => (1 : ℝ))) ≤
        finiteExpectation p (A.indicator (fun _ => (1 : ℝ))) *
        finiteExpectation p (B.indicator (fun _ => (1 : ℝ))))
    (A B : Set (Set (Option E))) (hA : IsUpperSet A) (hB : IsUpperSet B) :
    finiteExpectation p ((disjointOccurrence A B).indicator (fun _ => (1 : ℝ))) ≤
      finiteExpectation p (A.indicator (fun _ => (1 : ℝ))) *
      finiteExpectation p (B.indicator (fun _ => (1 : ℝ))) := by
  let A0 := (fun θ : Set E => Option.some '' θ) ⁻¹' A
  let A1 := (fun θ : Set E => insert none (Option.some '' θ)) ⁻¹' A
  let B0 := (fun θ : Set E => Option.some '' θ) ⁻¹' B
  let B1 := (fun θ : Set E => insert none (Option.some '' θ)) ⁻¹' B
  let ep := fun C : Set (Set E) => finiteExpectation p (C.indicator (fun _ => (1 : ℝ)))
  have h00 := hBK A0 B0 (isUpperSet_preimage_some hA) (isUpperSet_preimage_some hB)
  have h10 := hBK A1 B0 (isUpperSet_preimage_insert_none hA) (isUpperSet_preimage_some hB)
  have h01 := hBK A0 B1 (isUpperSet_preimage_some hA) (isUpperSet_preimage_insert_none hB)
  have hp1 : p ≤ 1 := by linarith
  have hc : 0 ≤ 1-2*p := by linarith
  have hrec := finiteExpectation_disjointOccurrence_option hp hp1 hA hB
  have hfirst : finiteExpectation p ((disjointOccurrence A B).indicator (fun _ => (1 : ℝ))) ≤
      (1-2*p) * (ep A0 * ep B0) + p * (ep A1 * ep B0 + ep A0 * ep B1) := by
    apply hrec.trans
    change (1-2*p) * ep (disjointOccurrence A0 B0) +
      p * (ep (disjointOccurrence A1 B0) + ep (disjointOccurrence A0 B1)) ≤ _
    have hm00 := mul_le_mul_of_nonneg_left h00 hc
    have hm10 := mul_le_mul_of_nonneg_left h10 hp
    have hm01 := mul_le_mul_of_nonneg_left h01 hp
    change (1-2*p) * ep (disjointOccurrence A0 B0) ≤ _ at hm00
    change p * ep (disjointOccurrence A1 B0) ≤ _ at hm10
    change p * ep (disjointOccurrence A0 B1) ≤ _ at hm01
    nlinarith
  have hm (C D : Set (Set E)) (hCD : C ⊆ D) : ep C ≤ ep D := by
    apply finiteExpectation_mono hp hp1
    intro η
    by_cases h : η ∈ C
    · simp [h, hCD h]
    · simp only [indicator_of_notMem h]
      exact indicator_nonneg (fun _ _ => by norm_num) _
  have ha := hm A0 A1 (section_closed_subset_open hA)
  have hb := hm B0 B1 (section_closed_subset_open hB)
  rw [finiteExpectation_option p (A.indicator _), finiteExpectation_option p (B.indicator _)]
  convert hfirst.trans (bk_step_arithmetic ha hb) using 1
  rfl

/-- Increasing events remain increasing after a bijective coordinate reindexing. -/
theorem isUpperSet_preimage_image {F : Type*} (e : E ≃ F) {A : Set (Set F)}
    (hA : IsUpperSet A) : IsUpperSet ((fun η : Set E => e '' η) ⁻¹' A) :=
  fun _ _ h hη => hA (image_mono h) hη

/-- Increasing-event disjoint occurrence is invariant under coordinate bijections. -/
theorem disjointOccurrence_image_equiv_iff {F : Type*} (e : E ≃ F)
    {A B : Set (Set F)} (hA : IsUpperSet A) (hB : IsUpperSet B) (η : Set E) :
    e '' η ∈ disjointOccurrence A B ↔
      η ∈ disjointOccurrence ((fun θ : Set E => e '' θ) ⁻¹' A)
        ((fun θ : Set E => e '' θ) ⁻¹' B) := by
  rw [mem_disjointOccurrence_iff_open hA hB,
    mem_disjointOccurrence_iff_open (isUpperSet_preimage_image e hA)
      (isUpperSet_preimage_image e hB)]
  constructor
  · rintro ⟨K, L, hK, hL, hd, hKη, hLη, hKA, hLB⟩
    refine ⟨e ⁻¹' K, e ⁻¹' L, hK.preimage e.injective.injOn,
      hL.preimage e.injective.injOn, hd.preimage _, ?_, ?_, ?_, ?_⟩
    · simpa using (preimage_mono (f := e) hKη)
    · simpa using (preimage_mono (f := e) hLη)
    · simpa using hKA
    · simpa using hLB
  · rintro ⟨K, L, hK, hL, hd, hKη, hLη, hKA, hLB⟩
    exact ⟨e '' K, e '' L, hK.image _, hL.image _,
      hd.image e.injective.injOn (subset_univ _) (subset_univ _),
      image_mono hKη, image_mono hLη, hKA, hLB⟩

/-- Homogeneous finite expectations are invariant under coordinate bijections. -/
theorem finiteExpectation_image_equiv {F : Type*} [Fintype E] [Fintype F]
    (e : E ≃ F) (p : ℝ) (f : Set F → ℝ) :
    finiteExpectation p (fun η : Set E => f (e '' η)) = finiteExpectation p f := by
  classical
  unfold finiteExpectation
  rw [← e.setCongr.sum_comp (fun ω : Set F => f ω * ∏ i : F, if i ∈ ω then p else 1-p)]
  apply Finset.sum_congr rfl
  intro η _
  simp only [Equiv.setCongr_apply]
  congr 1
  rw [← e.prod_comp (fun i : F => if i ∈ e '' η then p else 1-p)]
  simp

/-- The low-density assertion transports across a coordinate equivalence. -/
theorem lowDensityBK_equiv {F : Type*} [Fintype E] [Fintype F] (e : E ≃ F) (p : ℝ)
    (hBK : ∀ A B : Set (Set E), IsUpperSet A → IsUpperSet B →
      finiteExpectation p ((disjointOccurrence A B).indicator (fun _ => (1 : ℝ))) ≤
        finiteExpectation p (A.indicator (fun _ => (1 : ℝ))) *
        finiteExpectation p (B.indicator (fun _ => (1 : ℝ))))
    (A B : Set (Set F)) (hA : IsUpperSet A) (hB : IsUpperSet B) :
    finiteExpectation p ((disjointOccurrence A B).indicator (fun _ => (1 : ℝ))) ≤
      finiteExpectation p (A.indicator (fun _ => (1 : ℝ))) *
      finiteExpectation p (B.indicator (fun _ => (1 : ℝ))) := by
  have h := hBK ((fun θ : Set E => e '' θ) ⁻¹' A) ((fun θ : Set E => e '' θ) ⁻¹' B)
    (isUpperSet_preimage_image e hA) (isUpperSet_preimage_image e hB)
  have hind : (disjointOccurrence ((fun θ : Set E => e '' θ) ⁻¹' A)
      ((fun θ : Set E => e '' θ) ⁻¹' B)).indicator (fun _ => (1 : ℝ)) =
      fun η : Set E => (disjointOccurrence A B).indicator (fun _ => (1 : ℝ)) (e '' η) := by
    funext η
    simp only [indicator, disjointOccurrence_image_equiv_iff e hA hB]
  rw [hind, finiteExpectation_image_equiv] at h
  have hAeq : finiteExpectation p (((fun θ : Set E => e '' θ) ⁻¹' A).indicator (fun _ => (1 : ℝ))) =
      finiteExpectation p (A.indicator (fun _ => (1 : ℝ))) := by
    convert finiteExpectation_image_equiv e p (A.indicator (fun _ => (1 : ℝ))) using 1
    rfl
  have hBeq : finiteExpectation p (((fun θ : Set E => e '' θ) ⁻¹' B).indicator (fun _ => (1 : ℝ))) =
      finiteExpectation p (B.indicator (fun _ => (1 : ℝ))) := by
    convert finiteExpectation_image_equiv e p (B.indicator (fun _ => (1 : ℝ))) using 1
    rfl
  rwa [hAeq, hBeq] at h

/-- The empty-coordinate case of the finite BK induction. -/
theorem lowDensityBK_empty (p : ℝ) (A B : Set (Set PEmpty)) :
    finiteExpectation p ((disjointOccurrence A B).indicator (fun _ => (1 : ℝ))) ≤
      finiteExpectation p (A.indicator (fun _ => (1 : ℝ))) *
      finiteExpectation p (B.indicator (fun _ => (1 : ℝ))) := by
  classical
  have he (C : Set (Set PEmpty)) :
      finiteExpectation p (C.indicator (fun _ => (1 : ℝ))) = if ∅ ∈ C then 1 else 0 := by
    unfold finiteExpectation
    rw [Finset.sum_eq_single (∅ : Set PEmpty)]
    · simp [indicator]
    · intro ω _ hω
      exact (hω (Subsingleton.elim _ _)).elim
    · intro h
      exact (h (Finset.mem_univ _)).elim
  rw [he, he, he]
  by_cases hD : ∅ ∈ disjointOccurrence A B
  · have h := disjointOccurrence_subset_inter A B hD
    simp [hD, h.1, h.2]
  · by_cases hA : ∅ ∈ A <;> by_cases hB : ∅ ∈ B <;> simp [hD, hA, hB]

/-- BK for increasing events under homogeneous finite weights in the range 0≤p≤1/2. -/
theorem lowDensity_bk [Fintype E] (p : ℝ) (hp : 0 ≤ p) (hpHalf : p ≤ 1/2)
    (A B : Set (Set E)) (hA : IsUpperSet A) (hB : IsUpperSet B) :
    finiteExpectation p ((disjointOccurrence A B).indicator (fun _ => (1 : ℝ))) ≤
      finiteExpectation p (A.indicator (fun _ => (1 : ℝ))) *
      finiteExpectation p (B.indicator (fun _ => (1 : ℝ))) := by
  refine Fintype.induction_empty_option
    (P := fun α [Fintype α] => ∀ A B : Set (Set α), IsUpperSet A → IsUpperSet B →
      finiteExpectation p ((disjointOccurrence A B).indicator (fun _ => (1 : ℝ))) ≤
        finiteExpectation p (A.indicator (fun _ => (1 : ℝ))) *
        finiteExpectation p (B.indicator (fun _ => (1 : ℝ)))) ?_ ?_ ?_ E A B hA hB
  · intro α β hβ e hBK
    let : Fintype α := Fintype.ofEquiv β e.symm
    exact lowDensityBK_equiv e p hBK
  · intro A B _ _
    exact lowDensityBK_empty p A B
  · intro α hα hBK
    exact lowDensityBK_option hp hpHalf hBK

/-- For probability parameters the event indicator expectation is the canonical real measure. -/
theorem finiteExpectation_indicator_eq_measureReal [Fintype E] (p : unitInterval)
    (A : Set (Set E)) :
    finiteExpectation (p : ℝ) (A.indicator (fun _ => (1 : ℝ))) =
      (prodBernoulli (fun _ : E => p)).real A := by
  rw [finiteExpectation_eq_integral]
  exact integral_indicator_one (Set.toFinite A).measurableSet

/-- Low-density BK for the canonical finite Bernoulli product law. -/
theorem finite_bernoulli_bk_le_half [Fintype E] (p : unitInterval)
    (hpHalf : (p : ℝ) ≤ 1/2) (A B : Set (Set E)) (hA : IsUpperSet A) (hB : IsUpperSet B) :
    (prodBernoulli (fun _ : E => p)).real (disjointOccurrence A B) ≤
      (prodBernoulli (fun _ : E => p)).real A * (prodBernoulli (fun _ : E => p)).real B := by
  have h := lowDensity_bk (p : ℝ) p.property.1 hpHalf A B hA hB
  simpa only [finiteExpectation_indicator_eq_measureReal] using h

-- The hypothesis includes both endpoints of the low-density interval.
example [Fintype E] (A B : Set (Set E)) (hA : IsUpperSet A) (hB : IsUpperSet B) :
    (prodBernoulli (fun _ : E => 0)).real (disjointOccurrence A B) ≤
      (prodBernoulli (fun _ : E => 0)).real A * (prodBernoulli (fun _ : E => 0)).real B :=
  finite_bernoulli_bk_le_half 0 (by norm_num) A B hA hB

example : (prodBernoulli (fun _ : Bool => (⟨1/2, by norm_num⟩ : unitInterval))).real
    (disjointOccurrence {ω | false ∈ ω} {ω | true ∈ ω}) ≤
    (prodBernoulli (fun _ : Bool => (⟨1/2, by norm_num⟩ : unitInterval))).real {ω | false ∈ ω} *
    (prodBernoulli (fun _ : Bool => (⟨1/2, by norm_num⟩ : unitInterval))).real {ω | true ∈ ω} := by
  apply finite_bernoulli_bk_le_half
  · norm_num
  · exact fun _ _ h hi => h hi
  · exact fun _ _ h hi => h hi

example (p : unitInterval) :
    (prodBernoulli (fun _ : Empty => p)).real
      (disjointOccurrence Set.univ Set.univ) = 1 := by
  rw [disjointOccurrence_univ, measureReal_def, measure_univ]
  rfl

end PercLib.Probability
