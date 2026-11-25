/-
Adapted from NearCritical/Russo.lean by Tom Hutchcroft and collaborators.
Source: https://github.com/tomhutchcroft/near-critical-diffusivity/blob/c820fea91a7482c1755de0ec94ecb9f59ccfcacc/NearCritical/Russo.lean
Reuse authorized by Tom Hutchcroft under DECISIONS R-3. The native source has no
repository-wide licence inferred from its vendored dependencies.

Modified for PercLib on 2026-11-14: individual real coordinate profiles and derivatives;
division-free pairing of forced-open/forced-closed differences; p and beta specializations.
This is finite polynomial calculus, not a new probability law. The probability integral
bridge is the separate ProductExpectation package. Endpoint derivatives are derivatives
of the real polynomial extension, not a globally interval-valued family.
-/
module

public import PercLib.Probability.ProductExpectation
public import Mathlib.Analysis.Calculus.Deriv.Mul
public import Mathlib.Analysis.Calculus.Deriv.Add
public import Mathlib.Analysis.SpecialFunctions.ExpDeriv
public import Mathlib.Tactic.Ring
public import Mathlib.Tactic.Linarith

@[expose] public section
noncomputable section
namespace PercLib.Probability.FiniteProfile
open Finset
open scoped Classical
variable {E : Type*} [Fintype E]

/-- Coordinate weight polynomial, valid for all real profiles. -/
def weight (q : E → ℝ) (ω : E → Bool) : ℝ :=
  ∏ e, if ω e then q e else 1 - q e

/-- Finite profile expectation polynomial. On unit-interval profiles its canonical
probability interpretation is supplied by the ProductExpectation bridge. -/
def expectation (q : E → ℝ) (f : (E → Bool) → ℝ) : ℝ :=
  ∑ ω, f ω * weight q ω

def deletedWeight (q : E → ℝ) (e : E) (ω : E → Bool) : ℝ :=
  ∏ j ∈ univ.erase e, if ω j then q j else 1 - q j

def score (q : E → ℝ) (e : E) (ω : E → Bool) : ℝ :=
  deletedWeight q e ω * if ω e then 1 else -1

/-- Force a coordinate, using one classical choice of decidable equality. -/
def force (e : E) (b : Bool) (ω : E → Bool) : E → Bool :=
  Function.update ω e b

/-- State-independent increment at a tested coordinate. -/
def difference (e : E) (f : (E → Bool) → ℝ) (ω : E → Bool) : ℝ :=
  f (force e true ω) - f (force e false ω)

def flip (e : E) (ω : E → Bool) : E → Bool :=
  Function.update ω e (!(ω e))

omit [Fintype E] in
lemma flip_involutive (e : E) : Function.Involutive (flip e) := by
  intro ω
  ext j
  by_cases hj : j = e <;> simp [flip, Function.update_apply, hj]

def flipEquiv (e : E) : (E → Bool) ≃ (E → Bool) :=
  Function.Involutive.toPerm (flip e) (flip_involutive e)

lemma sum_flip (e : E) (g : (E → Bool) → ℝ) :
    ∑ ω, g (flip e ω) = ∑ ω, g ω := (flipEquiv e).sum_comp g

lemma deletedWeight_flip (q : E → ℝ) (e : E) (ω : E → Bool) :
    deletedWeight q e (flip e ω) = deletedWeight q e ω := by
  apply prod_congr rfl
  intro j hj
  simp [flip, Function.update_of_ne (mem_erase.mp hj).1]

lemma weight_split (q : E → ℝ) (e : E) (ω : E → Bool) :
    weight q ω = (if ω e then q e else 1 - q e) * deletedWeight q e ω :=
  (mul_prod_erase univ (fun j ↦ if ω j then q j else 1 - q j) (mem_univ e)).symm

omit [Fintype E] in
lemma force_flip (e : E) (b : Bool) (ω : E → Bool) :
    force e b (flip e ω) = force e b ω := by
  simp [force, flip, Function.update_idem]

omit [Fintype E] in
lemma difference_force (e : E) (b : Bool) (f : (E → Bool) → ℝ) (ω : E → Bool) :
    difference e f (force e b ω) = difference e f ω := by
  simp [difference, force, Function.update_idem]

omit [Fintype E] in
lemma flip_apply_self (e : E) (ω : E → Bool) : flip e ω e = !(ω e) :=
  Function.update_self _ _ _

lemma paired_difference (q : E → ℝ) (e : E) (f : (E → Bool) → ℝ) (ω : E → Bool) :
    f ω * score q e ω + f (flip e ω) * score q e (flip e ω) =
      difference e f ω * weight q ω +
      difference e f (flip e ω) * weight q (flip e ω) := by
  rw [weight_split q e ω, weight_split q e (flip e ω)]
  simp only [score, deletedWeight_flip, difference, force_flip, flip_apply_self]
  cases h : ω e
  · have hf : flip e ω = force e true ω := by simp [force, flip, h]
    have hc : force e false ω = ω := by
      simpa only [force] using
        (Function.update_eq_self_iff.mpr h.symm : Function.update ω e false = ω)
    simp only [Bool.not_false, Bool.false_eq_true, ite_false, ite_true]
    rw [hf, hc]
    ring
  · have hf : flip e ω = force e false ω := by simp [force, flip, h]
    have ho : force e true ω = ω := by
      simpa only [force] using
        (Function.update_eq_self_iff.mpr h.symm : Function.update ω e true = ω)
    simp only [Bool.not_true, Bool.false_eq_true, ite_false, ite_true]
    rw [hf, ho]
    ring

/-- Pairing each configuration with its flip removes the tested coordinate's weight.
Unlike an opening-only formula, this identity has no endpoint division. -/
lemma score_difference_identity (q : E → ℝ) (e : E) (f : (E → Bool) → ℝ) :
    (∑ ω, f ω * score q e ω) = expectation q (difference e f) := by
  have h := sum_congr (s₁ := (univ : Finset (E → Bool))) rfl
    (fun ω _ => paired_difference q e f ω)
  rw [sum_add_distrib, sum_add_distrib,
    sum_flip e (fun ω => f ω * score q e ω),
    sum_flip e (fun ω => difference e f ω * weight q ω)] at h
  unfold expectation
  linarith

lemma weight_hasDerivAt (q : E → ℝ → ℝ) (dq : E → ℝ) (t : ℝ)
    (hq : ∀ e, HasDerivAt (q e) (dq e) t) (ω : E → Bool) :
    HasDerivAt (fun u => weight (fun e => q e u) ω)
      (∑ e, dq e * score (fun j => q j t) e ω) t := by
  have hf (e : E) : HasDerivAt (fun u : ℝ => if ω e then q e u else 1 - q e u)
      (dq e * if ω e then 1 else -1) t := by
    cases ω e
    · simpa using (hq e).const_sub 1
    · simpa using hq e
  simpa only [weight, score, deletedWeight, smul_eq_mul, mul_left_comm, mul_assoc] using
    HasDerivAt.fun_finsetProd (fun e (_ : e ∈ (univ : Finset E)) => hf e)

/-- Finite inhomogeneous Russo identity, for the real polynomial extension. Valid at
mixed endpoint profiles as well as in the interior; no coordinate is divided out. -/
theorem expectation_hasDerivAt (q : E → ℝ → ℝ) (dq : E → ℝ) (t : ℝ)
    (hq : ∀ e, HasDerivAt (q e) (dq e) t) (f : (E → Bool) → ℝ) :
    HasDerivAt (fun u => expectation (fun e => q e u) f)
      (∑ e, dq e * expectation (fun j => q j t) (difference e f)) t := by
  have h := HasDerivAt.fun_sum (u := (univ : Finset (E → Bool)))
    (fun ω _ => (weight_hasDerivAt q dq t hq ω).const_mul (f ω))
  have hsum : (∑ ω, f ω * ∑ e, dq e * score (fun j => q j t) e ω) =
      ∑ e, dq e * expectation (fun j => q j t) (difference e f) := by
    simp_rw [mul_sum]
    rw [sum_comm]
    apply sum_congr rfl
    intro e _
    rw [← score_difference_identity, mul_sum]
    apply sum_congr rfl
    intro ω _
    ring
  rw [hsum] at h
  exact h

/-- Homogeneous parameter, including p=0 and p=1 as real-extension derivatives. -/
theorem expectation_homogeneous_hasDerivAt (p : ℝ) (f : (E → Bool) → ℝ) :
    HasDerivAt (fun u => expectation (fun _ => u) f)
      (∑ e, expectation (fun _ => p) (difference e f)) p := by
  simpa using expectation_hasDerivAt (fun _ u => u) (fun _ => 1) p
    (fun _ => hasDerivAt_id p) f

/-- Intensity parameter. In the probability interpretation J and beta are nonnegative;
the polynomial/exp identity itself holds for every real J and beta, including beta=0. -/
theorem expectation_intensity_hasDerivAt (J : E → ℝ) (β : ℝ) (f : (E → Bool) → ℝ) :
    HasDerivAt (fun b => expectation (fun e => 1 - Real.exp (-b * J e)) f)
      (∑ e, (J e * Real.exp (-β * J e)) *
        expectation (fun j => 1 - Real.exp (-β * J j)) (difference e f)) β := by
  apply expectation_hasDerivAt
  intro e
  simpa [Pi.neg_apply, mul_comm] using
    ((hasDerivAt_id β).neg.mul_const (J e)).exp.const_sub 1

end PercLib.Probability.FiniteProfile

namespace PercLib.Probability.FiniteProfile
open Finset Set
open scoped Classical
variable {E : Type*} [Fintype E]

/-- A Boolean configuration viewed in the canonical Set representation. -/
def toSet (ω : E → Bool) : Set E := {e | ω e = true}

/-- Indicator of an event on canonical configurations. -/
def eventValue (A : Set (Set E)) (ω : E → Bool) : ℝ := if toSet ω ∈ A then 1 else 0

/-- Pivotality depends only on the other coordinates; the tested coordinate is forced
both ways. This is the state-independent pivotal convention. -/
def pivotal (A : Set (Set E)) (e : E) (ω : E → Bool) : Prop :=
  toSet (force e true ω) ∈ A ∧ toSet (force e false ω) ∉ A

omit [Fintype E] in
lemma pivotal_force (A : Set (Set E)) (e : E) (b : Bool) (ω : E → Bool) :
    pivotal A e (force e b ω) ↔ pivotal A e ω := by
  simp [pivotal, force, Function.update_idem]

omit [Fintype E] in
lemma force_false_subset_true (e : E) (ω : E → Bool) :
    toSet (force e false ω) ⊆ toSet (force e true ω) := by
  intro j hj
  by_cases h : j = e
  · subst j; simp [toSet, force] at hj
  · simpa [toSet, force, Function.update_of_ne h] using hj

omit [Fintype E] in
/-- For increasing events the coordinate increment is exactly the pivotal indicator. -/
lemma difference_eventValue {A : Set (Set E)} (hA : IsUpperSet A) (e : E) (ω : E → Bool) :
    difference e (eventValue A) ω = if pivotal A e ω then 1 else 0 := by
  have hm := hA (force_false_subset_true e ω)
  by_cases ho : toSet (force e true ω) ∈ A <;>
    by_cases hc : toSet (force e false ω) ∈ A <;>
    simp_all [difference, eventValue, pivotal]

/-- Russo for an increasing event, with no q/(1-q) division. The right-hand side is the
profile polynomial of the state-independent pivotal indicator. -/
theorem event_hasDerivAt (q : E → ℝ → ℝ) (dq : E → ℝ) (t : ℝ)
    (hq : ∀ e, HasDerivAt (q e) (dq e) t) {A : Set (Set E)} (hA : IsUpperSet A) :
    HasDerivAt (fun u => expectation (fun e => q e u) (eventValue A))
      (∑ e, dq e * expectation (fun j => q j t) (fun ω => if pivotal A e ω then 1 else 0)) t := by
  simpa only [expectation, difference_eventValue hA] using
    expectation_hasDerivAt q dq t hq (eventValue A)

/-- In intensity coordinates the pivotal term includes the exponential factor. -/
theorem event_intensity_hasDerivAt (J : E → ℝ) (β : ℝ)
    {A : Set (Set E)} (hA : IsUpperSet A) :
    HasDerivAt (fun b => expectation (fun e => 1 - Real.exp (-b * J e)) (eventValue A))
      (∑ e, (J e * Real.exp (-β * J e)) * expectation
        (fun j => 1 - Real.exp (-β * J j)) (fun ω => if pivotal A e ω then 1 else 0)) β := by
  simpa only [expectation, difference_eventValue hA] using
    expectation_intensity_hasDerivAt J β (eventValue A)

/-! Boundary witnesses are algebraic real-extension derivatives. -/

example (t : ℝ) (f : (Empty → Bool) → ℝ) :
    HasDerivAt (fun u => expectation (fun _ : Empty => u) f) 0 t := by
  simpa using expectation_homogeneous_hasDerivAt (E := Empty) t f

example (q : Bool → ℝ → ℝ) (dq : Bool → ℝ) (t : ℝ)
    (hq : ∀ e, HasDerivAt (q e) (dq e) t) :
    HasDerivAt (fun u => expectation (fun e => q e u) (fun _ => 0)) 0 t := by
  simpa [difference, expectation] using expectation_hasDerivAt q dq t hq (fun _ => 0)

set_option backward.isDefEq.respectTransparency false in
/-- One coordinate really has expectation q, including both endpoints. -/
lemma expectation_singleton (p : ℝ) :
    expectation (fun _ : Unit => p) (fun ω => if ω () then 1 else 0) = p := by
  let : DecidableEq Unit := Classical.decEq _
  unfold expectation
  rw [← (Equiv.funUnique Unit Bool).symm.sum_comp
    (fun ω : Unit → Bool => (if ω () then (1 : ℝ) else 0) * weight (fun _ => p) ω)]
  simp [weight, Equiv.funUnique, Equiv.piUnique]

example (p : ℝ) :
    HasDerivAt (fun u => expectation (fun _ : Unit => u)
      (fun ω => if ω () then 1 else 0)) 1 p := by
  convert! hasDerivAt_id p using 1
  ext u
  exact expectation_singleton u

example (J : ℝ) :
    HasDerivAt (fun b => expectation (fun _ : Unit => 1 - Real.exp (-b * J))
      (fun ω => if ω () then 1 else 0)) J 0 := by
  simp only [expectation_singleton]
  simpa [Pi.neg_apply, mul_comm] using ((hasDerivAt_id (0 : ℝ)).neg.mul_const J).exp.const_sub 1

example (f : (Bool → Bool) → ℝ) :
    HasDerivAt (fun u => expectation (fun e : Bool => if e then u else 1-u) f)
      (∑ e : Bool, (if e then 1 else -1) * expectation
        (fun e : Bool => if e then 0 else 1) (difference e f)) 0 := by
  have hq (e : Bool) : HasDerivAt (fun u : ℝ => if e then u else 1-u)
      (if e then 1 else -1) 0 := by
    cases e
    · simpa using (hasDerivAt_id (0 : ℝ)).const_sub 1
    · convert! hasDerivAt_id (0 : ℝ) using 1
  simpa using expectation_hasDerivAt (fun e u => if e then u else 1-u)
    (fun e => if e then 1 else -1) 0 hq f

end PercLib.Probability.FiniteProfile

namespace PercLib.Probability.FiniteProfile
open MeasureTheory Finset Set
open scoped Classical
variable {E : Type*} [Fintype E]

omit [Fintype E] in
lemma toSet_bijective : Function.Bijective (toSet : (E → Bool) → Set E) := by
  constructor
  · intro a b hab
    funext e
    have h := Set.ext_iff.mp hab e
    change (a e = true ↔ b e = true) at h
    cases ha : a e <;> cases hb : b e <;> simp_all
  · intro s
    exact ⟨fun e => decide (e ∈ s), by ext e; simp [toSet]⟩

/-- Reindex the canonical finite-profile integral as the Boolean polynomial, without
introducing a second law. ProductExpectation supplies the measure calculation. -/
theorem integral_prodBernoulli_eq_expectation (p : E → unitInterval) (f : Set E → ℝ) :
    ∫ ω, f ω ∂prodBernoulli p = expectation (fun e => (p e : ℝ)) (fun ω => f (toSet ω)) := by
  rw [integral_prodBernoulli]
  unfold expectation weight
  symm
  apply Fintype.sum_bijective toSet toSet_bijective
  intro ω
  congr 1
  apply Finset.prod_congr rfl
  intro e _
  by_cases h : ω e = true <;> simp [toSet, h]

omit [Fintype E] in
lemma toSet_force_true (e : E) (ω : E → Bool) :
    toSet (force e true ω) = insert e (toSet ω) := by
  ext j
  by_cases h : j = e <;> simp [toSet, force, Function.update_apply, h]

omit [Fintype E] in
lemma toSet_force_false (e : E) (ω : E → Bool) :
    toSet (force e false ω) = toSet ω \ {e} := by
  ext j
  by_cases h : j = e <;> simp [toSet, force, Function.update_apply, h]

/-- Probability-law Russo on a parameter domain. The coordinate functions q are real
extensions; p takes values in the unit interval and agrees with q only on s and at t.
Thus this transport applies at boundary parameters without a fictitious global extension
of an interval-valued differentiable family. -/
theorem integral_hasDerivWithinAt (q : E → ℝ → ℝ) (dq : E → ℝ) (t : ℝ)
    (hq : ∀ e, HasDerivAt (q e) (dq e) t)
    (p : ℝ → E → unitInterval) (s : Set ℝ)
    (ht : ∀ e, (p t e : ℝ) = q e t)
    (hs : ∀ u ∈ s, ∀ e, (p u e : ℝ) = q e u) (f : Set E → ℝ) :
    HasDerivWithinAt (fun u => ∫ ω, f ω ∂prodBernoulli (p u))
      (∑ e, dq e * ∫ ω, (f (insert e ω) - f (ω \ {e})) ∂prodBernoulli (p t)) s t := by
  have h := (expectation_hasDerivAt q dq t hq (fun ω => f (toSet ω))).hasDerivWithinAt (s := s)
  have hpoint (u : ℝ) (hu : ∀ e, (p u e : ℝ) = q e u) :
      (∫ ω, f ω ∂prodBernoulli (p u)) = expectation (fun e => q e u) (fun ω => f (toSet ω)) := by
    rw [integral_prodBernoulli_eq_expectation]
    simp_rw [hu]
  have hd : (∑ e, dq e * ∫ ω, (f (insert e ω) - f (ω \ {e})) ∂prodBernoulli (p t)) =
      ∑ e, dq e * expectation (fun j => q j t) (difference e (fun ω => f (toSet ω))) := by
    simp_rw [integral_prodBernoulli_eq_expectation, ht]
    apply Finset.sum_congr rfl
    intro e _
    apply congrArg (fun g : (E → Bool) → ℝ => dq e * expectation (fun j => q j t) g)
    funext ω
    simp [difference, toSet_force_true, toSet_force_false]
  rw [hd]
  exact h.congr (fun u hu => hpoint u (hs u hu)) (hpoint t ht)

end PercLib.Probability.FiniteProfile

namespace PercLib.Probability.FiniteProfile
open MeasureTheory Finset Set
open scoped Classical
variable {E : Type*} [Fintype E]

/-- The canonical finite-event Russo formula. Pivotality is tested with the coordinate
forced both ways and therefore includes the closed-coordinate exponential factor in
intensity parametrisations via dq. -/
theorem event_real_hasDerivWithinAt (q : E → ℝ → ℝ) (dq : E → ℝ) (t : ℝ)
    (hq : ∀ e, HasDerivAt (q e) (dq e) t)
    (p : ℝ → E → unitInterval) (s : Set ℝ)
    (ht : ∀ e, (p t e : ℝ) = q e t)
    (hs : ∀ u ∈ s, ∀ e, (p u e : ℝ) = q e u)
    {A : Set (Set E)} (hA : IsUpperSet A) :
    HasDerivWithinAt (fun u => (prodBernoulli (p u)).real A)
      (∑ e, dq e * (prodBernoulli (p t)).real
        {ω | insert e ω ∈ A ∧ ω \ {e} ∉ A}) s t := by
  have h := integral_hasDerivWithinAt q dq t hq p s ht hs (A.indicator (fun _ => 1))
  have hd (e : E) : (fun ω : Set E =>
      A.indicator (fun _ => (1 : ℝ)) (insert e ω) - A.indicator (fun _ => 1) (ω \ {e})) =
      ({ω : Set E | insert e ω ∈ A ∧ ω \ {e} ∉ A}).indicator (fun _ => 1) := by
    funext ω
    have hm : ω \ {e} ∈ A → insert e ω ∈ A :=
      hA (Set.sdiff_subset.trans (Set.subset_insert e ω))
    by_cases ho : insert e ω ∈ A <;> by_cases hc : ω \ {e} ∈ A <;>
      simp_all
  have hi (r : E → unitInterval) (C : Set (Set E)) :
      (∫ ω, C.indicator (fun _ => (1 : ℝ)) ω ∂prodBernoulli r) = (prodBernoulli r).real C :=
    integral_indicator_one (Set.toFinite C).measurableSet
  simpa only [hd, hi] using h

end PercLib.Probability.FiniteProfile

namespace PercLib.Probability.FiniteProfile
open MeasureTheory Finset Set
open scoped Classical
variable {E : Type*} [Fintype E]

/-- Homogeneous canonical event formula on any domain where p is the identity profile. -/
theorem event_homogeneous_real_hasDerivWithinAt (t : ℝ) (p : ℝ → E → unitInterval) (s : Set ℝ)
    (ht : ∀ e, (p t e : ℝ) = t) (hs : ∀ u ∈ s, ∀ e, (p u e : ℝ) = u)
    {A : Set (Set E)} (hA : IsUpperSet A) :
    HasDerivWithinAt (fun u => (prodBernoulli (p u)).real A)
      (∑ e, (prodBernoulli (p t)).real {ω | insert e ω ∈ A ∧ ω \ {e} ∉ A}) s t := by
  simpa using event_real_hasDerivWithinAt (fun _ u => u) (fun _ => 1) t
    (fun _ => hasDerivAt_id t) p s ht hs hA

/-- Intensity canonical event formula, including beta=0 via within-domain derivatives.
The state-independent pivotal probability is multiplied by J_e exp(-beta J_e). -/
theorem event_intensity_real_hasDerivWithinAt (J : E → ℝ) (β : ℝ)
    (p : ℝ → E → unitInterval) (s : Set ℝ)
    (ht : ∀ e, (p β e : ℝ) = 1 - Real.exp (-β * J e))
    (hs : ∀ b ∈ s, ∀ e, (p b e : ℝ) = 1 - Real.exp (-b * J e))
    {A : Set (Set E)} (hA : IsUpperSet A) :
    HasDerivWithinAt (fun b => (prodBernoulli (p b)).real A)
      (∑ e, (J e * Real.exp (-β * J e)) *
        (prodBernoulli (p β)).real {ω | insert e ω ∈ A ∧ ω \ {e} ∉ A}) s β := by
  apply event_real_hasDerivWithinAt (fun e b => 1 - Real.exp (-b * J e)) _ β _ p s ht hs hA
  intro e
  simpa [Pi.neg_apply, mul_comm] using
    ((hasDerivAt_id β).neg.mul_const (J e)).exp.const_sub 1

end PercLib.Probability.FiniteProfile

namespace PercLib.Probability.FiniteProfile
open MeasureTheory Set
open scoped Classical

/-- A one-coordinate canonical event has derivative one throughout the closed parameter
interval, including both endpoints as within derivatives. -/
example (t : ℝ) (ht : t ∈ Icc (0 : ℝ) 1) :
    HasDerivWithinAt (fun u => (prodBernoulli
      (fun _ : Unit => projIcc 0 1 zero_le_one u)).real {ω | () ∈ ω})
      1 (Icc 0 1) t := by
  have hp (u : ℝ) (hu : u ∈ Icc (0 : ℝ) 1) :
      ((projIcc 0 1 zero_le_one u : unitInterval) : ℝ) = u := by
    rw [projIcc_of_mem zero_le_one hu]
  have h := event_homogeneous_real_hasDerivWithinAt (E := Unit) t
    (fun u _ => projIcc 0 1 zero_le_one u) (Icc 0 1)
    (fun _ => hp t ht) (fun u hu _ => hp u hu)
    (A := {ω | () ∈ ω}) (fun _ _ hab ha => hab ha)
  simpa using h

end PercLib.Probability.FiniteProfile
