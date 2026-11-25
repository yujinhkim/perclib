/-
Copyright (c) 2026 PercLib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

New for this project (issue 211, Q-41): the measure form of mathlib's `fkg` and `holley`
(`Mathlib/Combinatorics/SetFamily/FourFunctions.lean`). No upstream proof is copied.
-/
module

public import PercLib.Probability.ProductExpectation
public import Mathlib.Combinatorics.SetFamily.FourFunctions
public import Mathlib.MeasureTheory.Integral.Bochner.SumMeasure

/-!
# FKG and Holley inequalities for measures on `Set E`, `E` finite

Write `w(ω) = μ {ω}`. If `w(ω) w(η) ≤ w(ω ∩ η) w(ω ∪ η)` (the lattice condition), increasing
events are positively correlated (FKG). If `w_μ(ω) w_ν(η) ≤ w_μ(ω ∩ η) w_ν(ω ∪ η)`, then `ν`
dominates `μ` on increasing events (Holley). `prodBernoulli p` satisfies the lattice condition
with equality, and `prodBernoulli p`, `prodBernoulli q` with `p ≤ q` satisfy Holley's condition.
-/

@[expose] public section

noncomputable section

open MeasureTheory Set
open scoped ENNReal

namespace PercLib.Probability

variable {E : Type*} [Fintype E]

/-! ### Measures on a finite configuration space as sums -/

theorem measureReal_eq_sum_indicator (μ : Measure (Set E)) [IsFiniteMeasure μ]
    (A : Set (Set E)) [DecidablePred (· ∈ A)] :
    μ.real A = ∑ ω, μ.real {ω} * (if ω ∈ A then (1 : ℝ) else 0) := by
  classical
  simp only [mul_ite, mul_one, mul_zero]
  rw [← Finset.sum_filter, sum_measureReal_singleton]
  congr 1
  ext ω
  simp

omit [Fintype E] in
theorem real_latticeCondition (μ : Measure (Set E)) [IsFiniteMeasure μ]
    (hμ : ∀ ω η : Set E, μ {ω} * μ {η} ≤ μ {ω ∩ η} * μ {ω ∪ η}) (ω η : Set E) :
    μ.real {ω} * μ.real {η} ≤ μ.real {ω ⊓ η} * μ.real {ω ⊔ η} := by
  simp only [measureReal_def, ← ENNReal.toReal_mul]
  exact ENNReal.toReal_mono (ENNReal.mul_ne_top (measure_ne_top _ _) (measure_ne_top _ _))
    (hμ ω η)

/-! ### FKG -/

/-- **FKG, function form.** -/
theorem integral_mul_integral_le_of_latticeCondition (μ : Measure (Set E))
    [IsProbabilityMeasure μ]
    (hμ : ∀ ω η : Set E, μ {ω} * μ {η} ≤ μ {ω ∩ η} * μ {ω ∪ η})
    {f g : Set E → ℝ} (hf₀ : 0 ≤ f) (hg₀ : 0 ≤ g) (hf : Monotone f) (hg : Monotone g) :
    (∫ ω, f ω ∂μ) * (∫ ω, g ω ∂μ) ≤ ∫ ω, f ω * g ω ∂μ := by
  classical
  rw [integral_fintype Integrable.of_finite, integral_fintype Integrable.of_finite,
    integral_fintype Integrable.of_finite]
  simp only [smul_eq_mul]
  have h := fkg (f := f) (g := g) (μ := fun ω : Set E => μ.real {ω}) (fun _ => measureReal_nonneg) hf₀ hg₀ hf hg
    (real_latticeCondition μ hμ)
  have hsum : ∑ ω : Set E, μ.real {ω} = 1 := by
    rw [sum_measureReal_singleton, Finset.coe_univ]
    simp
  rwa [hsum, one_mul] at h

/-- **FKG for events.** Under the lattice condition, increasing events are positively
correlated. -/
theorem measure_inter_ge_of_latticeCondition (μ : Measure (Set E)) [IsProbabilityMeasure μ]
    (hμ : ∀ ω η : Set E, μ {ω} * μ {η} ≤ μ {ω ∩ η} * μ {ω ∪ η})
    {A B : Set (Set E)} (hA : IsUpperSet A) (hB : IsUpperSet B) :
    μ A * μ B ≤ μ (A ∩ B) := by
  classical
  have h := integral_mul_integral_le_of_latticeCondition μ hμ
    (f := fun ω => if ω ∈ A then (1 : ℝ) else 0) (g := fun ω => if ω ∈ B then (1 : ℝ) else 0)
    (fun ω => by dsimp; split_ifs <;> norm_num) (fun ω => by dsimp; split_ifs <;> norm_num)
    (fun ω η hle => by dsimp; split_ifs with h1 h2 <;> first | exact absurd (hA hle h1) h2 | norm_num)
    (fun ω η hle => by dsimp; split_ifs with h1 h2 <;> first | exact absurd (hB hle h1) h2 | norm_num)
  rw [integral_fintype Integrable.of_finite, integral_fintype Integrable.of_finite,
    integral_fintype Integrable.of_finite] at h
  simp only [smul_eq_mul] at h
  rw [← measureReal_eq_sum_indicator, ← measureReal_eq_sum_indicator] at h
  have hAB : ∑ ω : Set E, μ.real {ω} * ((if ω ∈ A then (1 : ℝ) else 0) *
      (if ω ∈ B then (1 : ℝ) else 0)) = μ.real (A ∩ B) := by
    rw [measureReal_eq_sum_indicator μ (A ∩ B)]
    refine Finset.sum_congr rfl fun ω _ => ?_
    by_cases h1 : ω ∈ A <;> by_cases h2 : ω ∈ B <;> simp [h1, h2]
  rw [hAB] at h
  rw [← ofReal_measureReal (measure_ne_top μ A), ← ofReal_measureReal (measure_ne_top μ B),
    ← ofReal_measureReal (measure_ne_top μ (A ∩ B)), ← ENNReal.ofReal_mul measureReal_nonneg]
  exact ENNReal.ofReal_le_ofReal h

/-! ### Holley -/

/-- **Holley.** Under Holley's condition, `ν` dominates `μ` on increasing events. -/
theorem measure_le_of_holley (μ ν : Measure (Set E)) [IsProbabilityMeasure μ]
    [IsProbabilityMeasure ν]
    (h : ∀ ω η : Set E, μ {ω} * ν {η} ≤ μ {ω ∩ η} * ν {ω ∪ η})
    {A : Set (Set E)} (hA : IsUpperSet A) : μ A ≤ ν A := by
  classical
  have hr : ∀ ω η : Set E, μ.real {ω} * ν.real {η} ≤ μ.real {ω ⊓ η} * ν.real {ω ⊔ η} := by
    intro ω η
    simp only [measureReal_def, ← ENNReal.toReal_mul]
    exact ENNReal.toReal_mono (ENNReal.mul_ne_top (measure_ne_top _ _) (measure_ne_top _ _))
      (h ω η)
  have hsum : ∑ ω : Set E, μ.real {ω} = ∑ ω : Set E, ν.real {ω} := by
    rw [sum_measureReal_singleton, sum_measureReal_singleton, Finset.coe_univ]
    simp
  have hh := holley (μ := fun ω : Set E => if ω ∈ A then (1 : ℝ) else 0)
    (f := fun ω => μ.real {ω}) (g := fun ω => ν.real {ω})
    (fun ω => by dsimp; split_ifs <;> norm_num) (fun _ => measureReal_nonneg)
    (fun _ => measureReal_nonneg)
    (fun ω η hle => by dsimp; split_ifs with h1 h2 <;> first | exact absurd (hA hle h1) h2 | norm_num)
    hsum hr
  have e1 : ∑ ω : Set E, (if ω ∈ A then (1 : ℝ) else 0) * μ.real {ω} = μ.real A := by
    rw [measureReal_eq_sum_indicator μ A]
    exact Finset.sum_congr rfl fun ω _ => mul_comm _ _
  have e2 : ∑ ω : Set E, (if ω ∈ A then (1 : ℝ) else 0) * ν.real {ω} = ν.real A := by
    rw [measureReal_eq_sum_indicator ν A]
    exact Finset.sum_congr rfl fun ω _ => mul_comm _ _
  rw [e1, e2] at hh
  rw [← ofReal_measureReal (measure_ne_top μ A), ← ofReal_measureReal (measure_ne_top ν A)]
  exact ENNReal.ofReal_le_ofReal hh

/-! ### Product measures -/

theorem toNNReal_add_toNNReal_symm (t : unitInterval) :
    (unitInterval.toNNReal t : ℝ≥0∞) + unitInterval.toNNReal (unitInterval.symm t) = 1 := by
  rw [← ENNReal.coe_add, ← ENNReal.coe_one, ENNReal.coe_inj]
  apply NNReal.eq
  rw [NNReal.coe_add]
  change (t : ℝ) + (1 - t) = 1
  ring

/-- `prodBernoulli p` satisfies the lattice condition, with equality. -/
theorem prodBernoulli_latticeCondition (p : E → unitInterval) (ω η : Set E) :
    prodBernoulli p {ω} * prodBernoulli p {η} =
      prodBernoulli p {ω ∩ η} * prodBernoulli p {ω ∪ η} := by
  classical
  simp only [prodBernoulli_singleton, ← Finset.prod_mul_distrib]
  refine Finset.prod_congr rfl fun i _ => ?_
  by_cases h1 : i ∈ ω <;> by_cases h2 : i ∈ η <;> simp [h1, h2, mul_comm]

/-- `prodBernoulli p` and `prodBernoulli q` with `p ≤ q` satisfy Holley's condition. -/
theorem prodBernoulli_holley (p q : E → unitInterval) (hpq : p ≤ q) (ω η : Set E) :
    prodBernoulli p {ω} * prodBernoulli q {η} ≤
      prodBernoulli p {ω ∩ η} * prodBernoulli q {ω ∪ η} := by
  classical
  simp only [prodBernoulli_singleton, ← Finset.prod_mul_distrib]
  refine Finset.prod_le_prod fun i _ => ?_
  have hpq' : (unitInterval.toNNReal (p i) : ℝ≥0∞) ≤ unitInterval.toNNReal (q i) := by
    exact_mod_cast (show unitInterval.toNNReal (p i) ≤ unitInterval.toNNReal (q i) from hpq i)
  by_cases h1 : i ∈ ω <;> by_cases h2 : i ∈ η <;> simp only [h1, h2, mem_inter_iff,
    mem_union, and_self, and_true, and_false, or_true, or_false, ite_true, ite_false,
    le_refl]
  -- the only nontrivial case: `i ∈ ω`, `i ∉ η`: `p (1 - q) ≤ (1 - p) q`.
  have hp := toNNReal_add_toNNReal_symm (p i)
  have hq := toNNReal_add_toNNReal_symm (q i)
  set a := (unitInterval.toNNReal (p i) : ℝ≥0∞)
  set b := (unitInterval.toNNReal (q i) : ℝ≥0∞)
  set a' := (unitInterval.toNNReal (unitInterval.symm (p i)) : ℝ≥0∞)
  set b' := (unitInterval.toNNReal (unitInterval.symm (q i)) : ℝ≥0∞)
  -- `a b' = a (1 - b) ≤ a - a b ≤ b - a b = (1 - a) b = a' b`
  have ha : a ≠ ⊤ := ENNReal.coe_ne_top
  have hb : b ≠ ⊤ := ENNReal.coe_ne_top
  have hb' : b' = 1 - b := by rw [← hq, ENNReal.add_sub_cancel_left hb]
  have ha' : a' = 1 - a := by rw [← hp, ENNReal.add_sub_cancel_left ha]
  rw [hb', ha', ENNReal.mul_sub (fun _ _ => ha), ENNReal.sub_mul (fun _ _ => hb), mul_one,
    one_mul]
  exact tsub_le_tsub_right hpq' _

/-! ### Tests: Harris and monotone comparison on a finite index set -/

/-- Harris on a finite index set, re-derived from FKG. -/
example (p : E → unitInterval) {A B : Set (Set E)} (hA : IsUpperSet A) (hB : IsUpperSet B) :
    prodBernoulli p A * prodBernoulli p B ≤ prodBernoulli p (A ∩ B) :=
  measure_inter_ge_of_latticeCondition _ (fun ω η => (prodBernoulli_latticeCondition p ω η).le)
    hA hB

/-- The monotone comparison of S-2 on a finite index set, re-derived from Holley. -/
example (p q : E → unitInterval) (hpq : p ≤ q) {A : Set (Set E)} (hA : IsUpperSet A) :
    prodBernoulli p A ≤ prodBernoulli q A :=
  measure_le_of_holley _ _ (prodBernoulli_holley p q hpq) hA

end PercLib.Probability

end
