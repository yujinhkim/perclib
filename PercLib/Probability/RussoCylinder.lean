/-
Copyright (c) 2026 PercLib contributors. Released under Apache 2.0.
New finite-cylinder transport of PercLib's finite-profile Russo formula. The latter
carries its near-critical-diffusivity attribution in Russo.lean; no upstream proof
is copied here. Ambient coordinate types are arbitrary, with no countability assumption.
-/
module

public import PercLib.Probability.Russo
public import PercLib.Probability.FiniteContinuity

@[expose] public section
noncomputable section
open MeasureTheory Set
open scoped Classical
namespace PercLib.Probability
variable {ι : Type*}

/-- Finite-event Russo for an arbitrary event: the forced difference may be negative. -/
theorem finite_event_difference_hasDerivWithinAt [Fintype ι]
    (q : ι → ℝ → ℝ) (dq : ι → ℝ) (t : ℝ) (hq : ∀ e, HasDerivAt (q e) (dq e) t)
    (p : ℝ → ι → unitInterval) (s : Set ℝ)
    (ht : ∀ e, (p t e : ℝ) = q e t) (hs : ∀ u ∈ s, ∀ e, (p u e : ℝ) = q e u)
    (A : Set (Set ι)) :
    HasDerivWithinAt (fun u => (prodBernoulli (p u)).real A)
      (∑ e, dq e * ((prodBernoulli (p t)).real {ω | insert e ω ∈ A} -
        (prodBernoulli (p t)).real {ω | ω \ {e} ∈ A})) s t := by
  have h := FiniteProfile.integral_hasDerivWithinAt q dq t hq p s ht hs
    (A.indicator (fun _ => 1))
  have hd (e : ι) : (∫ ω, (A.indicator (fun _ => (1:ℝ)) (insert e ω) -
      A.indicator (fun _ => 1) (ω \ {e})) ∂prodBernoulli (p t)) =
      (prodBernoulli (p t)).real {ω | insert e ω ∈ A} -
        (prodBernoulli (p t)).real {ω | ω \ {e} ∈ A} := by
    rw [integral_sub Integrable.of_finite Integrable.of_finite]
    congr 1 <;> exact integral_indicator_one (Set.toFinite _).measurableSet
  have hi (r : ι → unitInterval) :
      (∫ ω, A.indicator (fun _ => (1:ℝ)) ω ∂prodBernoulli r) = (prodBernoulli r).real A :=
    integral_indicator_one (Set.toFinite A).measurableSet
  simpa only [hd, hi] using h

/-- Restriction commutes with forcing a coordinate inside the finite block. -/
theorem restrict_insert (F : Finset ι) (e : F) (ω : Set ι) :
    (Subtype.val ⁻¹' insert (e:ι) ω : Set F) = insert e (Subtype.val ⁻¹' ω) := by
  ext j
  simp only [mem_preimage, mem_insert_iff, Subtype.val_inj]

/-- Restriction commutes with closing a coordinate inside the finite block. -/
theorem restrict_sdiff_singleton (F : Finset ι) (e : F) (ω : Set ι) :
    (Subtype.val ⁻¹' (ω \ {(e:ι)}) : Set F) = (Subtype.val ⁻¹' ω) \ {e} := by
  ext j
  simp only [mem_preimage, mem_sdiff, mem_singleton_iff, Subtype.val_inj]

/-- Russo for a finite cylinder on an arbitrary ambient coordinate type. Real extensions
need agree with the probability profiles only on the parameter domain and at its base point. -/
theorem cylinder_difference_hasDerivWithinAt
    (F : Finset ι) (B : Set (Set F)) (q : ι → ℝ → ℝ) (dq : ι → ℝ) (t : ℝ)
    (hq : ∀ e ∈ F, HasDerivAt (q e) (dq e) t)
    (p : ℝ → ι → unitInterval) (s : Set ℝ)
    (ht : ∀ e ∈ F, (p t e : ℝ) = q e t)
    (hs : ∀ u ∈ s, ∀ e ∈ F, (p u e : ℝ) = q e u) :
    HasDerivWithinAt
      (fun u => (prodBernoulli (p u)).real {ω | (Subtype.val ⁻¹' ω : Set F) ∈ B})
      (∑ e : F, dq e *
        ((prodBernoulli (p t)).real {ω | (Subtype.val ⁻¹' insert (e:ι) ω : Set F) ∈ B} -
         (prodBernoulli (p t)).real {ω | (Subtype.val ⁻¹' (ω \ {(e:ι)}) : Set F) ∈ B})) s t := by
  have h := finite_event_difference_hasDerivWithinAt (fun e : F => q e)
    (fun e : F => dq e) t (fun e => hq e e.property) (fun u (e : F) => p u e) s
    (fun e => ht e e.property) (fun u hu e => hs u hu e e.property) B
  have ho (e : F) : prodBernoulli (p t)
      {ω | (Subtype.val ⁻¹' insert (e:ι) ω : Set F) ∈ B} =
      prodBernoulli (fun j : F => p t j) {η | insert e η ∈ B} := by
    simp only [restrict_insert]
    exact prodBernoulli_cylinder_apply (p t) F {η | insert e η ∈ B}
  have hc (e : F) : prodBernoulli (p t)
      {ω | (Subtype.val ⁻¹' (ω \ {(e:ι)}) : Set F) ∈ B} =
      prodBernoulli (fun j : F => p t j) {η | η \ {e} ∈ B} := by
    simp only [restrict_sdiff_singleton]
    exact prodBernoulli_cylinder_apply (p t) F {η | η \ {e} ∈ B}
  simpa only [measureReal_def, ho, hc, prodBernoulli_cylinder_apply] using h

/-- Coordinates outside the block leave the cylinder unchanged under either forcing. -/
theorem cylinder_force_outside (F : Finset ι) (B : Set (Set F)) {e : ι} (he : e ∉ F)
    (ω : Set ι) :
    ((Subtype.val ⁻¹' insert e ω : Set F) ∈ B ↔ (Subtype.val ⁻¹' ω : Set F) ∈ B) ∧
    ((Subtype.val ⁻¹' (ω \ {e}) : Set F) ∈ B ↔ (Subtype.val ⁻¹' ω : Set F) ∈ B) := by
  have hne (j : F) : (j:ι) ≠ e := by rintro h; exact he (h ▸ j.property)
  have ho : (Subtype.val ⁻¹' insert e ω : Set F) = Subtype.val ⁻¹' ω := by ext j; simp [hne j]
  have hc : (Subtype.val ⁻¹' (ω \ {e}) : Set F) = Subtype.val ⁻¹' ω := by ext j; simp [hne j]
  simp [ho,hc]

/-- The forced probability difference vanishes outside the cylinder support. -/
theorem cylinder_difference_outside (p : ι → unitInterval) (F : Finset ι)
    (B : Set (Set F)) {e : ι} (he : e ∉ F) :
    (prodBernoulli p).real {ω | (Subtype.val ⁻¹' insert e ω : Set F) ∈ B} -
      (prodBernoulli p).real {ω | (Subtype.val ⁻¹' (ω \ {e}) : Set F) ∈ B} = 0 := by
  simp_rw [(cylinder_force_outside F B he _).1, (cylinder_force_outside F B he _).2]
  exact sub_self _

/-- For an increasing measurable event, the forced difference is the state-independent
pivotal probability. This includes endpoints, with no division by a coordinate probability. -/
theorem forced_difference_eq_pivotal (p : ι → unitInterval) {A : Set (Set ι)}
    (hA : IsUpperSet A) (hm : MeasurableSet A) (e : ι) :
    (prodBernoulli p).real {ω | insert e ω ∈ A} -
      (prodBernoulli p).real {ω | ω \ {e} ∈ A} =
      (prodBernoulli p).real {ω | insert e ω ∈ A ∧ ω \ {e} ∉ A} := by
  have hc : MeasurableSet {ω : Set ι | ω \ {e} ∈ A} := hm.preimage (by fun_prop)
  have hsub : {ω : Set ι | ω \ {e} ∈ A} ⊆ {ω | insert e ω ∈ A} :=
    fun ω hω => hA (Set.sdiff_subset.trans (Set.subset_insert e ω)) hω
  exact (measureReal_sdiff hsub hc).symm

/-- Increasing-cylinder Russo, with an ambient pivotal event and a finite sum. -/
theorem cylinder_pivotal_hasDerivWithinAt
    (F : Finset ι) (B : Set (Set F))
    (hA : IsUpperSet {ω : Set ι | (Subtype.val ⁻¹' ω : Set F) ∈ B})
    (q : ι → ℝ → ℝ) (dq : ι → ℝ) (t : ℝ)
    (hq : ∀ e ∈ F, HasDerivAt (q e) (dq e) t)
    (p : ℝ → ι → unitInterval) (s : Set ℝ)
    (ht : ∀ e ∈ F, (p t e : ℝ) = q e t)
    (hs : ∀ u ∈ s, ∀ e ∈ F, (p u e : ℝ) = q e u) :
    HasDerivWithinAt
      (fun u => (prodBernoulli (p u)).real {ω | (Subtype.val ⁻¹' ω : Set F) ∈ B})
      (∑ e : F, dq e * (prodBernoulli (p t)).real
        {ω | (Subtype.val ⁻¹' insert (e:ι) ω : Set F) ∈ B ∧
          (Subtype.val ⁻¹' (ω \ {(e:ι)}) : Set F) ∉ B}) s t := by
  have hm : MeasurableSet {ω : Set ι | (Subtype.val ⁻¹' ω : Set F) ∈ B} :=
    (Set.toFinite B).measurableSet.preimage (Measurable.of_mem fun e => measurable_set_mem e.val)
  have hd (e : ι) :
      (prodBernoulli (p t)).real {ω | (Subtype.val ⁻¹' insert e ω : Set F) ∈ B} -
      (prodBernoulli (p t)).real {ω | (Subtype.val ⁻¹' (ω \ {e}) : Set F) ∈ B} =
      (prodBernoulli (p t)).real {ω | (Subtype.val ⁻¹' insert e ω : Set F) ∈ B ∧
        (Subtype.val ⁻¹' (ω \ {e}) : Set F) ∉ B} :=
    forced_difference_eq_pivotal (p t) hA hm e
  simpa only [hd] using cylinder_difference_hasDerivWithinAt F B q dq t hq p s ht hs

/-- Intensity specialization on the nonnegative half-line, including beta=0. -/
theorem cylinder_intensity_hasDerivWithinAt
    (F : Finset ι) (B : Set (Set F)) (J : ι → ℝ) (β : ℝ)
    (p : ℝ → ι → unitInterval)
    (ht : ∀ e ∈ F, (p β e : ℝ) = 1 - Real.exp (-β * J e))
    (hs : ∀ b ∈ Ici (0:ℝ), ∀ e ∈ F, (p b e : ℝ) = 1 - Real.exp (-b * J e)) :
    HasDerivWithinAt
      (fun b => (prodBernoulli (p b)).real {ω | (Subtype.val ⁻¹' ω : Set F) ∈ B})
      (∑ e : F, (J e * Real.exp (-β * J e)) *
        ((prodBernoulli (p β)).real {ω | (Subtype.val ⁻¹' insert (e:ι) ω : Set F) ∈ B} -
         (prodBernoulli (p β)).real {ω | (Subtype.val ⁻¹' (ω \ {(e:ι)}) : Set F) ∈ B}))
      (Ici 0) β := by
  apply cylinder_difference_hasDerivWithinAt F B (fun e b => 1 - Real.exp (-b * J e))
    (fun e => J e * Real.exp (-β * J e)) β _ p (Ici 0) ht hs
  intro e _
  simpa [Pi.neg_apply, mul_comm] using
    ((hasDerivAt_id β).neg.mul_const (J e)).exp.const_sub 1

-- No ambient coordinates are restricted when the finite block is empty.
example (B : Set (Set (∅ : Finset ι))) (p : ℝ → ι → unitInterval) (s : Set ℝ) (t : ℝ) :
    HasDerivWithinAt
      (fun u => (prodBernoulli (p u)).real {ω | (Subtype.val ⁻¹' ω : Set (∅ : Finset ι)) ∈ B})
      0 s t := by
  simpa using cylinder_difference_hasDerivWithinAt ∅ B (fun _ _ => 0) (fun _ => 0) t
    (by simp) p s (by simp) (by simp)

-- A genuine cylinder in an infinite product, including the endpoint parameters.
example (t : ℝ) (ht : t ∈ Icc (0:ℝ) 1) :
    HasDerivWithinAt
      (fun u => (prodBernoulli (fun _ : ℕ => projIcc 0 1 zero_le_one u)).real {ω | 0 ∈ ω})
      1 (Icc 0 1) t := by
  let F : Finset ℕ := {0}
  let B : Set (Set F) := {η | (⟨0,by simp [F]⟩ : F) ∈ η}
  have hp (u : ℝ) (hu : u ∈ Icc (0:ℝ) 1) :
      ((projIcc 0 1 zero_le_one u : unitInterval) : ℝ) = u := by
    rw [projIcc_of_mem zero_le_one hu]
  have h := cylinder_difference_hasDerivWithinAt F B (fun _ u => u) (fun _ => 1) t
    (fun _ _ => hasDerivAt_id t) (fun u _ => projIcc 0 1 zero_le_one u) (Icc 0 1)
    (fun _ _ => hp t ht) (fun u hu _ _ => hp u hu)
  have he (e : F) : (e:ℕ) = 0 := Finset.mem_singleton.mp e.property
  simp only [B, Set.mem_ofPred_eq, Set.mem_preimage, Set.mem_insert_iff,
    Set.mem_sdiff, Set.mem_singleton_iff, he] at h
  simpa [F] using h

-- Closing that coordinate is a decreasing cylinder with derivative minus one.
example (t : ℝ) (ht : t ∈ Icc (0:ℝ) 1) :
    HasDerivWithinAt
      (fun u => (prodBernoulli (fun _ : ℕ => projIcc 0 1 zero_le_one u)).real {ω | 0 ∉ ω})
      (-1) (Icc 0 1) t := by
  let F : Finset ℕ := {0}
  let B : Set (Set F) := {η | (⟨0,by simp [F]⟩ : F) ∉ η}
  have hp (u : ℝ) (hu : u ∈ Icc (0:ℝ) 1) :
      ((projIcc 0 1 zero_le_one u : unitInterval) : ℝ) = u := by
    rw [projIcc_of_mem zero_le_one hu]
  have h := cylinder_difference_hasDerivWithinAt F B (fun _ u => u) (fun _ => 1) t
    (fun _ _ => hasDerivAt_id t) (fun u _ => projIcc 0 1 zero_le_one u) (Icc 0 1)
    (fun _ _ => hp t ht) (fun u hu _ _ => hp u hu)
  have he (e : F) : (e:ℕ) = 0 := Finset.mem_singleton.mp e.property
  simp only [B, Set.mem_ofPred_eq, Set.mem_preimage, Set.mem_insert_iff,
    Set.mem_sdiff, Set.mem_singleton_iff, he] at h
  simpa [F] using h

end PercLib.Probability
