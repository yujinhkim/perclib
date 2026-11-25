/-
Migration source: https://github.com/yujinhkim/Critical-Long-range-percolation
Integration revision: 3b3d1d0e43ef940bfaa2292ee5c2ee094ac4edbf
Licence: Apache-2.0 for the PercLib Lean sources and tooling; see third_party/critical-lrp/.
External provenance and modifications are recorded in the file-specific notices below.
-/

/-
Finite Bernoulli percolation: product law and Harris--FKG.

This module provides the finite-volume component of the model introduced on
page 6 of Tom Hutchcroft, "Critical long-range percolation I", arXiv:2508.18807v1,
and the nonnegative-observable version of the Harris--FKG inequality displayed
on page 20.
-/
module

public import Mathlib.Combinatorics.SetFamily.FourFunctions
public import Mathlib.Algebra.BigOperators.Ring.Finset
public import Mathlib.Analysis.SpecialFunctions.Exp
public import Mathlib.Tactic

set_option linter.unusedSectionVars false
set_option linter.unusedSimpArgs false
set_option linter.unnecessarySimpa false
set_option linter.unusedTactic false
set_option linter.unusedVariables false

set_option autoImplicit true

@[expose] public section

open Finset

namespace PercLib.CriticalLRP

variable {E : Type*} [Fintype E] [DecidableEq E]

/-- An edge with nonnegative parameters `β` and `J` is open with probability
`1 - exp (-(β * J))`. -/
noncomputable def longRangeEdgeProbability (β J : ℝ) : ℝ := 1 - Real.exp (-(β * J))

theorem longRangeEdgeProbability_nonneg {β J : ℝ} (hβ : 0 ≤ β) (hJ : 0 ≤ J) :
    0 ≤ longRangeEdgeProbability β J := by
  have h : 0 ≤ β * J := mul_nonneg hβ hJ
  rw [longRangeEdgeProbability, sub_nonneg, Real.exp_le_one_iff]
  linarith

theorem longRangeEdgeProbability_le_one {β J : ℝ} (hβ : 0 ≤ β) (hJ : 0 ≤ J) :
    longRangeEdgeProbability β J ≤ 1 := by
  have h : 0 ≤ β * J := mul_nonneg hβ hJ
  have hpos := Real.exp_pos (-(β * J))
  dsimp [longRangeEdgeProbability]
  linarith

theorem longRangeEdgeProbability_mem_Icc {β J : ℝ} (hβ : 0 ≤ β) (hJ : 0 ≤ J) :
    longRangeEdgeProbability β J ∈ Set.Icc (0 : ℝ) 1 :=
  ⟨longRangeEdgeProbability_nonneg hβ hJ, longRangeEdgeProbability_le_one hβ hJ⟩

/-- The finite configuration is its set of open edges, ordered by inclusion.
This type is order-isomorphic to the independent `Bool`-valued edge variables. -/
abbrev Configuration (E : Type*) := Finset E

/-- The exact probability of a finite open-edge configuration under independent
Bernoulli edge variables with open probabilities `p`. -/
noncomputable def configurationLaw (p : E → ℝ) (s : Configuration E) : ℝ :=
  ∏ e, if e ∈ s then p e else 1 - p e

theorem configurationLaw_nonneg (p : E → ℝ) (hp : ∀ e, 0 ≤ p e)
    (hp1 : ∀ e, p e ≤ 1) (s : Configuration E) :
    0 ≤ configurationLaw p s := by
  apply prod_nonneg
  intro e _
  by_cases h : e ∈ s
  · simpa [h] using hp e
  · simpa [h] using sub_nonneg.mpr (hp1 e)

/-- The independent product law is multiplicatively modular over the
configuration lattice. -/
theorem configurationLaw_modular (p : E → ℝ) (a b : Configuration E) :
    configurationLaw p a * configurationLaw p b =
      configurationLaw p (a ⊓ b) * configurationLaw p (a ⊔ b) := by
  simp only [configurationLaw, ← prod_mul_distrib]
  refine prod_congr rfl fun e _ => ?_
  by_cases ha : e ∈ a <;> by_cases hb : e ∈ b <;> simp [ha, hb, mul_comm]

/-- The configuration law is normalized. -/
theorem configurationLaw_sum (p : E → ℝ) :
    ∑ s, configurationLaw p s = 1 := by
  classical
  have hsplit : ∀ t : Finset E, configurationLaw p t =
      (∏ e ∈ t, p e) * ∏ e ∈ univ \ t, (1 - p e) := by
    intro t
    rw [configurationLaw, ← Finset.prod_filter_mul_prod_filter_not (univ : Finset E)
      (fun e => e ∈ t) (fun e => if e ∈ t then p e else 1 - p e)]
    rw [show univ.filter (fun e => e ∈ t) = t from by simp,
      show univ.filter (fun e => ¬ e ∈ t) = univ \ t from by ext e; simp]
    congr 1
    · exact Finset.prod_congr rfl fun e he => by simp [he]
    · exact Finset.prod_congr rfl fun e he => by simp at he; simp [he]
  rw [Finset.sum_congr rfl fun t (_ : t ∈ univ) => hsplit t, ← powerset_univ,
    ← Finset.prod_add (fun e => p e) (fun e => (1 - p e)) univ]
  simp

/-- Expectation under the finite independent-edge law. -/
noncomputable def expectation (p : E → ℝ) (X : Configuration E → ℝ) : ℝ :=
  ∑ s, configurationLaw p s * X s

/-- Probability of a set of finite configurations. -/
noncomputable def probability (p : E → ℝ) (A : Set (Configuration E)) : ℝ := by
  classical
  exact expectation p fun s => if s ∈ A then 1 else 0

/-- Harris--FKG for nonnegative increasing observables in finite independent
bond percolation, obtained from Mathlib's Ahlswede--Daykin `fkg` theorem. -/
theorem expectation_mul_expectation_le (p : E → ℝ) (hp : ∀ e, 0 ≤ p e)
    (hp1 : ∀ e, p e ≤ 1) (F G : Configuration E → ℝ)
    (hF0 : ∀ s, 0 ≤ F s) (hG0 : ∀ s, 0 ≤ G s)
    (hF : Monotone F) (hG : Monotone G) :
    expectation p F * expectation p G ≤ expectation p (fun s => F s * G s) := by
  have h := fkg (f := F) (g := G) (μ := configurationLaw p)
    (configurationLaw_nonneg p hp hp1) hF0 hG0 hF hG
    fun a b => (configurationLaw_modular p a b).le
  simpa only [expectation, configurationLaw_sum, one_mul] using h

/-- Harris--FKG in event form: increasing events are nonnegatively correlated. -/
theorem probability_mul_le_probability_inter (p : E → ℝ) (hp : ∀ e, 0 ≤ p e)
    (hp1 : ∀ e, p e ≤ 1) (A B : Set (Configuration E))
    (hA : ∀ ⦃s⦄, s ∈ A → ∀ ⦃t⦄, s ⊆ t → t ∈ A)
    (hB : ∀ ⦃s⦄, s ∈ B → ∀ ⦃t⦄, s ⊆ t → t ∈ B) :
    probability p A * probability p B ≤ probability p (A ∩ B) := by
  classical
  have hF0 : ∀ s : Configuration E, 0 ≤ (if s ∈ A then (1 : ℝ) else 0) := by
    intro s; split <;> norm_num
  have hG0 : ∀ s : Configuration E, 0 ≤ (if s ∈ B then (1 : ℝ) else 0) := by
    intro s; split <;> norm_num
  have hF : Monotone (fun s : Configuration E => if s ∈ A then (1 : ℝ) else 0) := by
    intro s t hst
    by_cases hs : s ∈ A
    · simp [hs, hA hs hst]
    · simpa [hs] using hF0 t
  have hG : Monotone (fun s : Configuration E => if s ∈ B then (1 : ℝ) else 0) := by
    intro s t hst
    by_cases hs : s ∈ B
    · simp [hs, hB hs hst]
    · simpa [hs] using hG0 t
  calc
    probability p A * probability p B ≤
        expectation p (fun s => (if s ∈ A then (1 : ℝ) else 0) *
          if s ∈ B then (1 : ℝ) else 0) :=
      expectation_mul_expectation_le p hp hp1 _ _ hF0 hG0 hF hG
    _ = probability p (A ∩ B) := by
      unfold expectation probability
      apply Finset.sum_congr rfl
      intro s _
      by_cases hsA : s ∈ A <;> by_cases hsB : s ∈ B <;> simp [hsA, hsB]

end PercLib.CriticalLRP
