/-
Copyright (c) 2026 PercLib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

Adapted from NearCritical/CylinderDisjointOccurrence.lean at
https://github.com/tomhutchcroft/near-critical-diffusivity/tree/c820fea91a7482c1755de0ec94ecb9f59ccfcacc
under Tom Hutchcroft's reuse permission (DECISIONS R-3). The native upstream
file has no licence header; this records permission, not an upstream Apache claim.
Changed for PercLib: canonical Set configurations, standard preimage/image/set
difference for restriction/extension, and arbitrary coordinate subsets. Finite
certificates remain finite under injective preimages; no finite ambient set is needed.
-/
module

public import PercLib.Probability.DisjointOccurrence

/-! # Restriction of disjoint occurrence
Restriction to a coordinate subtype preserves and reflects disjoint occurrence
of cylinder events. Neither increasingness nor a probability law is needed.
-/
@[expose] public section
open Set
namespace PercLib.Probability
variable {ι : Type*}

/-- Extend a configuration on a subtype, keeping the background off that subtype.
Restriction recovers the original configuration. -/
theorem restrict_extendConfiguration (s : Set ι) (ω : Set ι) (η : Set s) :
    Subtype.val ⁻¹' ((Subtype.val '' η) ∪ (ω \ s)) = η := by
  ext e
  simp

/-- A certificate for a cylinder event restricts to a certificate on its coordinates. -/
theorem ForcesOn.restrict_preimage (s : Set ι) {A : Set (Set s)} {ω F : Set ι}
    (h : ForcesOn ((fun ξ : Set ι => Subtype.val ⁻¹' ξ) ⁻¹' A) ω F) :
    ForcesOn A (Subtype.val ⁻¹' ω) (Subtype.val ⁻¹' F) := by
  intro η hη
  have hext := h ((Subtype.val '' η) ∪ (ω \ s)) (by
    intro e he
    by_cases hs : e ∈ s
    · have hagree := hη ⟨e, hs⟩ he
      simpa [hs] using hagree
    · simp [hs])
  change Subtype.val ⁻¹' ((Subtype.val '' η) ∪ (ω \ s)) ∈ A at hext
  rwa [restrict_extendConfiguration] at hext

/-- Disjoint occurrence of cylinder events agrees with disjoint occurrence on
the coordinate subtype. This holds for arbitrary ambient and coordinate sets. -/
theorem disjointOccurrence_restrict_iff (s : Set ι) (A B : Set (Set s)) (ω : Set ι) :
    Subtype.val ⁻¹' ω ∈ disjointOccurrence A B ↔
      ω ∈ disjointOccurrence
        ((fun ξ : Set ι => Subtype.val ⁻¹' ξ) ⁻¹' A)
        ((fun ξ : Set ι => Subtype.val ⁻¹' ξ) ⁻¹' B) := by
  constructor
  · rintro ⟨F, H, hF, hH, hd, hf, hh⟩
    refine ⟨Subtype.val '' F, Subtype.val '' H, hF.image _, hH.image _, ?_, ?_, ?_⟩
    · exact hd.image Subtype.val_injective.injOn (subset_univ _) (subset_univ _)
    · intro η hη
      exact hf (Subtype.val ⁻¹' η) (fun e he => hη e.val ⟨e, he, rfl⟩)
    · intro η hη
      exact hh (Subtype.val ⁻¹' η) (fun e he => hη e.val ⟨e, he, rfl⟩)
  · rintro ⟨F, H, hF, hH, hd, hf, hh⟩
    exact ⟨Subtype.val ⁻¹' F, Subtype.val ⁻¹' H,
      hF.preimage Subtype.val_injective.injOn, hH.preimage Subtype.val_injective.injOn,
      hd.preimage _, hf.restrict_preimage s, hh.restrict_preimage s⟩

/-- The event-level identity used to push finite-cylinder BK bounds to the ambient space. -/
theorem disjointOccurrence_preimage_restrict (s : Set ι) (A B : Set (Set s)) :
    disjointOccurrence ((fun ξ : Set ι => Subtype.val ⁻¹' ξ) ⁻¹' A)
      ((fun ξ : Set ι => Subtype.val ⁻¹' ξ) ⁻¹' B) =
      (fun ξ : Set ι => Subtype.val ⁻¹' ξ) ⁻¹' disjointOccurrence A B := by
  ext ω
  exact (disjointOccurrence_restrict_iff s A B ω).symm

-- Finite-coordinate use, without an ambient countability assumption.
example (s : Finset ι) (A B : Set (Set s)) (ω : Set ι) :
    Subtype.val ⁻¹' ω ∈ disjointOccurrence A B ↔
      ω ∈ disjointOccurrence ((fun ξ : Set ι => Subtype.val ⁻¹' ξ) ⁻¹' A)
        ((fun ξ : Set ι => Subtype.val ⁻¹' ξ) ⁻¹' B) :=
  disjointOccurrence_restrict_iff (s : Set ι) A B ω

-- Empty-coordinate extensions preserve the background.
example (ω : Set ι) :
    (Subtype.val '' (∅ : Set (∅ : Set ι))) ∪ (ω \ ∅) = ω := by simp

-- An overlapping indispensable coordinate is not turned into disjoint witnesses.
example (s : Set ι) (e : s) :
    disjointOccurrence
      ((fun ξ : Set ι => Subtype.val ⁻¹' ξ) ⁻¹' {η | e ∈ η})
      ((fun ξ : Set ι => Subtype.val ⁻¹' ξ) ⁻¹' {η | e ∈ η}) = ∅ := by
  rw [disjointOccurrence_preimage_restrict, disjointOccurrence_mem_self, preimage_empty]

end PercLib.Probability
