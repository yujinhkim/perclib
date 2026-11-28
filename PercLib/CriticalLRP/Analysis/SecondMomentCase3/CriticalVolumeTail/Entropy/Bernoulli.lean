/-
Copyright (c) 2026 PercLib contributors. Released under Apache 2.0.

# Finite weighted Bernoulli (long-range) percolation: the configuration weight

Source: T. Hutchcroft, *Critical long-range percolation I* (arXiv:2508.18807v1), and
T. Hutchcroft, *On the derivation of mean-field percolation critical exponents from the
triangle condition* (arXiv:2106.06400), Section 3 (`thm:DM_Chi`, Theorem 3.1 and its
Lemma 3.3).

This file fixes the finite weighted Bernoulli model used by the two-intensity comparison:
a finite edge type `E`, positive edge weights `J`, and the open probability
`1 - exp(-β J e)` of a weighted graph `G = (V, E, J)` at intensity `β`.  The configuration
space is `E → Bool` and the law is the product of the one-edge Bernoulli weights.

The main results here are the normalisation of the product weight and the exact cylinder
probability (the mass of the configurations agreeing with a given partial configuration on a
finite edge set), which is what every entropy computation in the sequel uses.
-/
module

public import Mathlib.Algebra.BigOperators.Ring.Finset
public import Mathlib.Analysis.SpecialFunctions.Log.Basic
public import Mathlib.Data.Fintype.Pi
public import Mathlib.Basic.Real.Basic

/-!
# The finite weighted Bernoulli model
-/

set_option autoImplicit false
set_option linter.hashCommand false

@[expose] public section

open Finset

namespace LRP

variable {E : Type*} [Fintype E] [DecidableEq E]

/-- The one-edge open probability `1 - exp(-β J e)` of the weighted model. -/
noncomputable def openProb (J : E → ℝ) (β : ℝ) (e : E) : ℝ := 1 - Real.exp (-(β * J e))

/-- The Bernoulli weight of the bit `b` at edge `e`. -/
noncomputable def bem (J : E → ℝ) (β : ℝ) (e : E) (b : Bool) : ℝ :=
  if b then openProb J β e else 1 - openProb J β e

/-- The weight of a configuration: the product of the one-edge Bernoulli weights. -/
noncomputable def confWeight (J : E → ℝ) (β : ℝ) (ω : E → Bool) : ℝ :=
  ∏ e, bem J β e (ω e)

/-- The probability of a set of configurations, as a finite sum of weights. -/
noncomputable def evProb (J : E → ℝ) (β : ℝ) (A : Set (E → Bool)) : ℝ := by
  classical
  exact ∑ ω ∈ Finset.univ.filter (fun ω => ω ∈ A), confWeight J β ω

omit [Fintype E] [DecidableEq E] in
/-- At every edge the two weights sum to one. -/
theorem bem_true_add_false (J : E → ℝ) (β : ℝ) (e : E) :
    bem J β e true + bem J β e false = 1 := by
  simp [bem]

omit [Fintype E] [DecidableEq E] in
/-- For positive weights and positive intensity both Bernoulli weights are strictly positive. -/
theorem bem_pos {J : E → ℝ} {β : ℝ} (hJ : ∀ e, 0 < J e) (hβ : 0 < β) (e : E) (b : Bool) :
    0 < bem J β e b := by
  have hlt : Real.exp (-(β * J e)) < 1 := by
    rw [Real.exp_lt_one_iff]; nlinarith [hJ e, hβ]
  have hpos : 0 < Real.exp (-(β * J e)) := Real.exp_pos _
  cases b with
  | false =>
    simp only [bem, Bool.false_eq_true, ite_false, openProb]
    linarith
  | true =>
    simp only [bem, ite_true, openProb]
    linarith

/-- **Factorisation of the total mass.** -/
theorem sum_prod_bem (J : E → ℝ) (β : ℝ) :
    (∑ ω : E → Bool, ∏ e, bem J β e (ω e)) = ∏ e, (∑ b : Bool, bem J β e b) := by
  rw [Finset.prod_univ_sum]
  rw [Fintype.piFinset_univ]

/-- **Normalisation**: the product Bernoulli weights sum to one. -/
theorem sum_confWeight (J : E → ℝ) (β : ℝ) :
    ∑ ω : E → Bool, confWeight J β ω = 1 := by
  have h1 : ∀ e : E, (∑ b : Bool, bem J β e b) = 1 := by
    intro e
    rw [Fintype.sum_bool, bem_true_add_false]
  simp only [confWeight]
  rw [sum_prod_bem J β]
  simp only [h1]
  exact Finset.prod_const_one

/-- **Cylinder probability.**  The configurations agreeing with `b` on the finite set `S`
have total mass `∏_{e ∈ S} bem e (b e)`. -/
theorem sum_confWeight_cylinder (J : E → ℝ) (β : ℝ) (S : Finset E) (b : E → Bool) :
    ∑ ω ∈ Finset.univ.filter (fun ω : E → Bool => ∀ e ∈ S, ω e = b e), confWeight J β ω
      = ∏ e ∈ S, bem J β e (b e) := by
  have hsum : ∀ e : E, (∑ c : Bool, bem J β e c) = 1 := by
    intro e
    rw [Fintype.sum_bool, bem_true_add_false]
  have hpt : ∀ ω : E → Bool, (if ∀ e ∈ S, ω e = b e then confWeight J β ω else 0)
      = ∏ e, bem J β e (ω e) * (if e ∈ S then (if ω e = b e then 1 else 0) else 1) := by
    intro ω
    by_cases h : ∀ e ∈ S, ω e = b e
    · rw [ite_eq_left h]
      simp only [confWeight]
      refine Finset.prod_congr rfl ?_
      intro e _
      by_cases he : e ∈ S
      · rw [ite_eq_left he, ite_eq_left (h e he), mul_one]
      · rw [ite_eq_right he, mul_one]
    · rw [ite_eq_right h]
      have hex : ∃ e ∈ S, ω e ≠ b e := by
        by_contra hc
        exact h (fun e he => by by_contra hne; exact hc ⟨e, he, hne⟩)
      obtain ⟨e₀, he₀S, he₀⟩ := hex
      exact (Finset.prod_eq_zero (Finset.mem_univ e₀) (by rw [ite_eq_left he₀S, ite_eq_right he₀,
        mul_zero])).symm
  have hsplit : ∀ e : E,
      (∑ c : Bool, bem J β e c * (if e ∈ S then (if c = b e then 1 else 0) else 1))
        = if e ∈ S then bem J β e (b e) else 1 := by
    intro e
    by_cases he : e ∈ S
    · simp only [he, ite_true, Fintype.sum_bool]
      cases hbe : b e <;> simp
    · simp only [he, ite_false, mul_one]
      exact hsum e
  have hprod : (∑ ω : E → Bool,
        ∏ e, bem J β e (ω e) * (if e ∈ S then (if ω e = b e then 1 else 0) else 1))
      = ∏ e, ∑ c : Bool, bem J β e c * (if e ∈ S then (if c = b e then 1 else 0) else 1) := by
    rw [Finset.prod_univ_sum]
    rw [Fintype.piFinset_univ]
  calc ∑ ω ∈ Finset.univ.filter (fun ω : E → Bool => ∀ e ∈ S, ω e = b e), confWeight J β ω
      = ∑ ω : E → Bool, (if ∀ e ∈ S, ω e = b e then confWeight J β ω else 0) := by
        rw [Finset.sum_filter]
    _ = ∑ ω : E → Bool,
          ∏ e, bem J β e (ω e) * (if e ∈ S then (if ω e = b e then 1 else 0) else 1) :=
        Finset.sum_congr rfl fun ω _ => hpt ω
    _ = ∏ e, ∑ c : Bool, bem J β e c * (if e ∈ S then (if c = b e then 1 else 0) else 1) := hprod
    _ = ∏ e, if e ∈ S then bem J β e (b e) else 1 :=
        Finset.prod_congr rfl fun e _ => hsplit e
    _ = ∏ e ∈ S, bem J β e (b e) := by
        rw [← Finset.prod_filter]
        simp

end LRP

namespace LRP

set_option linter.hashCommand false in
#print axioms LRP.sum_confWeight

set_option linter.hashCommand false in
#print axioms LRP.sum_confWeight_cylinder

end LRP
