/-
Copyright (c) 2026 PercLib contributors. Released under Apache 2.0.
Q-58: correspondence wrappers for the complete grouped Russo assertions.
Uses the existing finite-profile definitions and division-free pairing proof
from Russo.lean; no new configuration or pivotal convention is introduced.
-/
module

public import PercLib.Meta.Tag
public import PercLib.Probability.Russo

@[expose] public section
noncomputable section
open MeasureTheory Set
open scoped Classical

namespace PercLib.Probability.FiniteProfile
variable {E : Type*} [Fintype E]

omit [Fintype E] in
/-- The grouped vocabulary contract, including state independence and the signed
increment's reduction to pivotality for increasing events. -/
@[tag "71GK"]
theorem forced_increment_pivotal_identities (e : E) (ω : E → Bool)
    (f : (E → Bool) → ℝ) {A : Set (Set E)} (hA : IsUpperSet A) :
    toSet (force e true ω) = insert e (toSet ω) ∧
    toSet (force e false ω) = toSet ω \ {e} ∧
    difference e f ω = f (force e true ω) - f (force e false ω) ∧
    (∀ b, difference e f (force e b ω) = difference e f ω) ∧
    (pivotal A e ω ↔ insert e (toSet ω) ∈ A ∧ toSet ω \ {e} ∉ A) ∧
    difference e (eventValue A) ω = (if pivotal A e ω then 1 else 0) ∧
    ((pivotal A e ω ∧ ω e = false) ↔
      (insert e (toSet ω) ∈ A ∧ toSet ω \ {e} ∉ A) ∧ e ∉ toSet ω) := by
  refine ⟨toSet_force_true e ω, toSet_force_false e ω, rfl,
    fun b => difference_force e b f ω, ?_, difference_eventValue hA e ω, ?_⟩
  · simp only [pivotal, toSet_force_true, toSet_force_false]
  · simp only [pivotal, toSet_force_true, toSet_force_false]
    simp only [toSet, Set.mem_ofPred_eq]
    cases ω e <;> simp

/-- Polynomial Russo and its probability-domain transport, including the expectation
identity that identifies the polynomial with the canonical law on the cube. -/
@[tag "7WIO"]
theorem russo_observable_polynomial_and_probability
    (q : E → ℝ → ℝ) (dq : E → ℝ) (t : ℝ)
    (hq : ∀ e, HasDerivAt (q e) (dq e) t) :
    (∀ f : (E → Bool) → ℝ,
      HasDerivAt (fun u => expectation (fun e => q e u) f)
        (∑ e, dq e * expectation (fun j => q j t) (difference e f)) t) ∧
    (∀ (p : ℝ → E → unitInterval) (s : Set ℝ),
      (∀ e, (p t e : ℝ) = q e t) →
      (∀ u ∈ s, ∀ e, (p u e : ℝ) = q e u) → ∀ f : Set E → ℝ,
      ((∫ ω, f ω ∂prodBernoulli (p t)) =
        expectation (fun e => q e t) (fun ω => f (toSet ω))) ∧
      HasDerivWithinAt (fun u => ∫ ω, f ω ∂prodBernoulli (p u))
        (∑ e, dq e * ∫ ω, (f (insert e ω) - f (ω \ {e})) ∂prodBernoulli (p t)) s t) := by
  refine ⟨expectation_hasDerivAt q dq t hq, ?_⟩
  intro p s ht hs f
  refine ⟨?_, integral_hasDerivWithinAt q dq t hq p s ht hs f⟩
  rw [integral_prodBernoulli_eq_expectation]
  simp_rw [ht]

private theorem event_expectation_eq_real (p : E → unitInterval) (A : Set (Set E)) :
    expectation (fun e => (p e : ℝ)) (eventValue A) = (prodBernoulli p).real A := by
  rw [← integral_indicator_one (Set.toFinite A).measurableSet,
    integral_prodBernoulli_eq_expectation]
  rfl

private theorem pivotal_expectation_eq_real (p : E → unitInterval) (A : Set (Set E)) (e : E) :
    expectation (fun j => (p j : ℝ)) (fun ω => if pivotal A e ω then 1 else 0) =
      (prodBernoulli p).real {ω | insert e ω ∈ A ∧ ω \ {e} ∉ A} := by
  rw [← event_expectation_eq_real]
  congr 1
  funext ω
  simp only [eventValue, pivotal, toSet_force_true, toSet_force_false, Set.mem_ofPred_eq]
  split_ifs <;> simp_all

/-- Both the polynomial derivative and the event-probability derivative; coordinate
velocities are arbitrary real numbers and may have either sign. -/
@[tag "WU9R"]
theorem russo_event_polynomial_and_probability
    (q : E → ℝ → ℝ) (dq : E → ℝ) (t : ℝ)
    (hq : ∀ e, HasDerivAt (q e) (dq e) t)
    (p : ℝ → E → unitInterval) (s : Set ℝ)
    (ht : ∀ e, (p t e : ℝ) = q e t)
    (hs : ∀ u ∈ s, ∀ e, (p u e : ℝ) = q e u)
    {A : Set (Set E)} (hA : IsUpperSet A) :
    HasDerivAt (fun u => expectation (fun e => q e u) (eventValue A))
      (∑ e, dq e * (prodBernoulli (p t)).real
        {ω | insert e ω ∈ A ∧ ω \ {e} ∉ A}) t ∧
    HasDerivWithinAt (fun u => (prodBernoulli (p u)).real A)
      (∑ e, dq e * (prodBernoulli (p t)).real
        {ω | insert e ω ∈ A ∧ ω \ {e} ∉ A}) s t := by
  refine ⟨?_, event_real_hasDerivWithinAt q dq t hq p s ht hs hA⟩
  have h := event_hasDerivAt q dq t hq hA
  have he : (fun e => q e t) = fun e => (p t e : ℝ) := funext fun e => (ht e).symm
  simpa only [he, pivotal_expectation_eq_real] using h

/-- The homogeneous formula has both an ordinary polynomial derivative and a
within-domain probability derivative, valid at either endpoint of [0,1]. -/
@[tag "4IHK"]
theorem russo_homogeneous_polynomial_and_endpoints
    (t : ℝ) (p : ℝ → E → unitInterval) (s : Set ℝ)
    (ht : ∀ e, (p t e : ℝ) = t) (hs : ∀ u ∈ s, ∀ e, (p u e : ℝ) = u)
    {A : Set (Set E)} (hA : IsUpperSet A) :
    HasDerivAt (fun u => expectation (fun _ => u) (eventValue A))
      (∑ e, (prodBernoulli (p t)).real {ω | insert e ω ∈ A ∧ ω \ {e} ∉ A}) t ∧
    HasDerivWithinAt (fun u => (prodBernoulli (p u)).real A)
      (∑ e, (prodBernoulli (p t)).real {ω | insert e ω ∈ A ∧ ω \ {e} ∉ A}) s t := by
  simpa only [one_mul] using russo_event_polynomial_and_probability
    (fun _ u => u) (fun _ => 1) t (fun _ => hasDerivAt_id t) p s ht hs hA

private theorem expectation_closed_coordinate (q : E → ℝ) (e : E) (g : (E → Bool) → ℝ)
    (hg : ∀ ω, g (flip e ω) = g ω) :
    expectation q (fun ω => if ω e then 0 else g ω) = (1-q e) * expectation q g := by
  have hpoint (ω : E → Bool) :
      (if ω e then 0 else g ω) * weight q ω +
        (if flip e ω e then 0 else g (flip e ω)) * weight q (flip e ω) =
      (1-q e) * (g ω * weight q ω + g (flip e ω) * weight q (flip e ω)) := by
    rw [weight_split q e ω, weight_split q e (flip e ω)]
    simp only [deletedWeight_flip, flip_apply_self, hg]
    cases ω e <;> simp <;> ring
  have h := Finset.sum_congr (s₁ := Finset.univ) rfl (fun ω _ => hpoint ω)
  simp only [Finset.sum_add_distrib, ← Finset.mul_sum] at h
  rw [sum_flip e (fun ω => (if ω e then 0 else g ω) * weight q ω),
    sum_flip e (fun ω => g ω * weight q ω)] at h
  unfold expectation
  linarith

set_option backward.isDefEq.respectTransparency false in
private theorem closed_pivotal_probability (p : E → unitInterval) (A : Set (Set E)) (e : E) :
    (prodBernoulli p).real {ω | (insert e ω ∈ A ∧ ω \ {e} ∉ A) ∧ e ∉ ω} =
      (1-(p e : ℝ)) * (prodBernoulli p).real {ω | insert e ω ∈ A ∧ ω \ {e} ∉ A} := by
  rw [← event_expectation_eq_real, ← pivotal_expectation_eq_real]
  have hg (ω : E → Bool) : (if pivotal A e (flip e ω) then (1 : ℝ) else 0) =
      if pivotal A e ω then 1 else 0 := by
    simp only [pivotal, force_flip]
    split_ifs <;> simp_all
  convert expectation_closed_coordinate (fun j => (p j : ℝ)) e
    (fun ω => if pivotal A e ω then (1 : ℝ) else 0) hg using 1
  congr 1
  funext ω
  simp only [eventValue, Set.mem_ofPred_eq, pivotal, toSet_force_true, toSet_force_false]
  by_cases h : ω e = true <;> simp [toSet, h]

private theorem integral_insertion_increment (p : E → unitInterval) (f : Set E → ℝ) (e : E) :
    (∫ ω, (f (insert e ω) - f ω) ∂prodBernoulli p) =
      (1-(p e : ℝ)) * ∫ ω, (f (insert e ω) - f (ω \ {e})) ∂prodBernoulli p := by
  simp_rw [integral_prodBernoulli_eq_expectation]
  have hg (ω : E → Bool) :
      difference e (fun ω => f (toSet ω)) (flip e ω) =
        difference e (fun ω => f (toSet ω)) ω := by simp only [difference, force_flip]
  convert expectation_closed_coordinate (fun j => (p j : ℝ)) e
    (difference e (fun ω => f (toSet ω))) hg using 1
  · congr 1
    funext ω
    by_cases h : ω e = true
    · have he : e ∈ toSet ω := h
      simp [h, Set.insert_eq_of_mem he]
    · have he : e ∉ toSet ω := h
      simp [h, difference, toSet_force_true, toSet_force_false, Set.sdiff_singleton_eq_self he]
  · congr 1
    congr 1
    funext ω
    simp only [difference, toSet_force_true, toSet_force_false]

/-- Intensity Russo with both event coefficients, their coordinatewise factorization,
and the insertion-increment formula for arbitrary real observables. -/
@[tag "IENL"]
theorem russo_intensity_and_closed_pivotal (J : E → ℝ) (_hJ : ∀ e, 0 ≤ J e)
    (β : ℝ) (_hβ : 0 ≤ β) (p : ℝ → E → unitInterval) (s : Set ℝ)
    (ht : ∀ e, (p β e : ℝ) = 1-Real.exp (-β*J e))
    (hs : ∀ b ∈ s, ∀ e, (p b e : ℝ) = 1-Real.exp (-b*J e))
    {A : Set (Set E)} (hA : IsUpperSet A) :
    HasDerivWithinAt (fun b => (prodBernoulli (p b)).real A)
      (∑ e, (J e * Real.exp (-β*J e)) *
        (prodBernoulli (p β)).real {ω | insert e ω ∈ A ∧ ω \ {e} ∉ A}) s β ∧
    (∑ e, (J e * Real.exp (-β*J e)) *
        (prodBernoulli (p β)).real {ω | insert e ω ∈ A ∧ ω \ {e} ∉ A}) =
      ∑ e, J e * (prodBernoulli (p β)).real
        {ω | (insert e ω ∈ A ∧ ω \ {e} ∉ A) ∧ e ∉ ω} ∧
    (∀ e, (prodBernoulli (p β)).real
      {ω | (insert e ω ∈ A ∧ ω \ {e} ∉ A) ∧ e ∉ ω} =
      Real.exp (-β*J e) * (prodBernoulli (p β)).real
        {ω | insert e ω ∈ A ∧ ω \ {e} ∉ A}) ∧
    (∀ f : Set E → ℝ, HasDerivWithinAt (fun b => ∫ ω, f ω ∂prodBernoulli (p b))
      (∑ e, J e * ∫ ω, (f (insert e ω) - f ω) ∂prodBernoulli (p β)) s β) := by
  have hc (e : E) := closed_pivotal_probability (p β) A e
  simp only [ht, sub_sub_cancel] at hc
  refine ⟨event_intensity_real_hasDerivWithinAt J β p s ht hs hA, ?_, hc, ?_⟩
  · simp_rw [hc, mul_assoc]
  · intro f
    have h := integral_hasDerivWithinAt (fun e b => 1-Real.exp (-b*J e))
      (fun e => J e * Real.exp (-β*J e)) β (fun e => by
        simpa [Pi.neg_apply, mul_comm] using
          ((hasDerivAt_id β).neg.mul_const (J e)).exp.const_sub 1) p s ht hs f
    have hi (e : E) := integral_insertion_increment (p β) f e
    simp only [ht, sub_sub_cancel] at hi
    simpa only [hi, mul_assoc] using h

-- The nonzero one-coordinate derivative includes both endpoints.
example (t : ℝ) (ht : t ∈ Icc (0 : ℝ) 1) :
    HasDerivWithinAt (fun u => (prodBernoulli
      (fun _ : Unit => projIcc 0 1 zero_le_one u)).real {ω | () ∈ ω})
      1 (Icc 0 1) t := by
  have hp (u : ℝ) (hu : u ∈ Icc (0 : ℝ) 1) :
      ((projIcc 0 1 zero_le_one u : unitInterval) : ℝ) = u := by
    rw [projIcc_of_mem zero_le_one hu]
  have h := russo_homogeneous_polynomial_and_endpoints (E := Unit) t
    (fun u _ => projIcc 0 1 zero_le_one u) (Icc 0 1)
    (fun _ => hp t ht) (fun u hu _ => hp u hu)
    (A := {ω | () ∈ ω}) (fun _ _ hab ha => hab ha)
  simpa using h.2

-- The polynomial clause imposes no cube hypothesis at all, including at t=2.
example (f : (Bool → Bool) → ℝ) :
    HasDerivAt (fun u => expectation (fun _ : Bool => u) f)
      (∑ e, expectation (fun _ : Bool => 2) (difference e f)) 2 := by
  simpa using (russo_observable_polynomial_and_probability
    (fun _ : Bool => id) (fun _ => 1) 2 (fun _ => hasDerivAt_id 2)).1 f

-- The intensity formula is valid at beta=0 for a genuine right-sided domain.
example {A : Set (Set Unit)} (hA : IsUpperSet A) :
    HasDerivWithinAt (fun _b : ℝ => (prodBernoulli (fun _ : Unit => (0 : unitInterval))).real A)
      0 (Ici 0) 0 := by
  have h := russo_intensity_and_closed_pivotal (fun _ : Unit => 0) (by simp)
    0 (by norm_num) (fun _ _ => 0) (Ici 0) (by simp) (by simp) hA
  simpa using h.1

end PercLib.Probability.FiniteProfile
