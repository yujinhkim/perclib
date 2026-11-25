/-
Copyright (c) 2026 PercLib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

New proofs for issue 135 (Q-14), written on 2026-11-14 by PROVER-E. No upstream proof is
copied.
-/
module

public import Mathlib.MeasureTheory.Integral.Lebesgue.Markov
public import Mathlib.MeasureTheory.MeasurableSpace.NCard
public import PercLib.Percolation.Bond.Basic
public import PercLib.Probability.FirstMoment

/-!
# Expected degree and expected numbers of open pairs

The degree of `v` is `{w | (openGraph ω).Adj v w}.encard : ℕ∞`. Its expectation is the
off-diagonal row sum of `q` at `v`, including the value `∞` (`lintegral_degree`); Markov's
inequality follows. The expected number of open pairs in a finite set of pairs is the sum
of `q` over it, and the expected number of open ordered pairs leaving a finite set `Λ` is
`∑ x ∈ Λ, ∑' y ∉ Λ, q s(x, y)`. Positive values of `q` on the diagonal never count. This
file adds no definition.
-/

@[expose] public section

open MeasureTheory Set PercLib.Probability
open scoped ENNReal
open Classical

namespace PercLib.Percolation.Bond

variable {V : Type*}

/-- The event that two vertices are adjacent in the open graph. -/
theorem setOf_adj_eq (v w : V) :
    {ω : Config V | (openGraph ω).Adj v w} = if v = w then ∅ else {ω | s(v, w) ∈ ω} := by
  ext ω
  split_ifs with h
  · subst h; simp
  · simp [openGraph_adj_iff, h]

/-- Adjacency events are measurable, for any vertex type. -/
theorem measurableSet_adj (v w : V) :
    MeasurableSet {ω : Config V | (openGraph ω).Adj v w} := by
  rw [setOf_adj_eq]
  split_ifs
  · exact MeasurableSet.empty
  · exact measurableSet_mem _

/-- The probability that two vertices are adjacent, with the diagonal excluded. -/
theorem law_adj (q : Sym2 V → unitInterval) (v w : V) :
    law q {ω : Config V | (openGraph ω).Adj v w} =
      if w = v then 0 else (unitInterval.toNNReal (q s(v, w)) : ℝ≥0∞) := by
  rw [setOf_adj_eq]
  by_cases h : v = w
  · simp [h]
  · simp only [h, Ne.symm h, ↓reduceIte]
    exact prodBernoulli_setOf_mem q _

/-- **The degree is measurable.** -/
theorem measurable_degree [Countable V] (v : V) :
    Measurable fun ω : Config V => {w | (openGraph ω).Adj v w}.encard :=
  measurable_encard.comp (Measurable.of_mem fun w => (measurableSet_adj v w).mem)

/-- The degree is the sum of the adjacency indicators. -/
theorem degree_eq_tsum (ω : Config V) (v : V) :
    ({w | (openGraph ω).Adj v w}.encard : ℝ≥0∞) =
      ∑' w, {ω' : Config V | (openGraph ω').Adj v w}.indicator (fun _ => (1 : ℝ≥0∞)) ω := by
  rw [encard_eq_tsum_indicator]
  rfl

/-- **The expected degree is the off-diagonal row sum**, including the value `∞`. -/
theorem lintegral_degree [Countable V] (q : Sym2 V → unitInterval) (v : V) :
    ∫⁻ ω, ({w | (openGraph ω).Adj v w}.encard : ℝ≥0∞) ∂law q =
      ∑' w, if w = v then 0 else (unitInterval.toNNReal (q s(v, w)) : ℝ≥0∞) := by
  simp_rw [degree_eq_tsum _ v]
  rw [lintegral_tsum fun w => (measurable_const.indicator (measurableSet_adj v w)).aemeasurable]
  refine tsum_congr fun w => ?_
  rw [lintegral_indicator_const (measurableSet_adj v w), one_mul, law_adj]

/-- **Markov's inequality for the degree.** -/
theorem mul_law_le_degree_le [Countable V] (q : Sym2 V → unitInterval) (v : V) (k : ℕ) :
    (k : ℝ≥0∞) * law q {ω | (k : ℕ∞) ≤ {w | (openGraph ω).Adj v w}.encard} ≤
      ∑' w, if w = v then 0 else (unitInterval.toNNReal (q s(v, w)) : ℝ≥0∞) := by
  rw [← lintegral_degree]
  have hm : Measurable fun ω : Config V => ({w | (openGraph ω).Adj v w}.encard : ℝ≥0∞) :=
    (measurable_of_countable _).comp (measurable_degree v)
  refine le_trans (le_of_eq ?_) (mul_meas_ge_le_lintegral₀ hm.aemeasurable (k : ℝ≥0∞))
  congr 2
  ext ω
  simp only [mem_ofPred_eq]
  rw [← ENat.toENNReal_coe, ENat.toENNReal_le]

/-- **Expected number of open pairs in a finite set of pairs.** No countability needed. -/
theorem lintegral_ncard_inter_finset_pairs (q : Sym2 V → unitInterval) (F : Finset (Sym2 V)) :
    ∫⁻ ω, ((ω ∩ F).ncard : ℝ≥0∞) ∂law q = ∑ e ∈ F, (unitInterval.toNNReal (q e) : ℝ≥0∞) :=
  lintegral_ncard_inter_finset q F

/-- **Expected number of open ordered pairs leaving a finite set.** -/
theorem lintegral_encard_boundary_pairs [Countable V] (q : Sym2 V → unitInterval)
    (Λ : Finset V) :
    ∫⁻ ω, ({z : V × V | z.1 ∈ Λ ∧ z.2 ∉ Λ ∧ (openGraph ω).Adj z.1 z.2}.encard : ℝ≥0∞) ∂law q =
      ∑ x ∈ Λ, ∑' y, if y ∈ Λ then 0 else (unitInterval.toNNReal (q s(x, y)) : ℝ≥0∞) := by
  set E : V × V → Set (Config V) := fun z =>
    {ω | z.1 ∈ Λ ∧ z.2 ∉ Λ ∧ (openGraph ω).Adj z.1 z.2}
  have hE : ∀ z, MeasurableSet (E z) := fun z => by
    have : E z = {_ω : Config V | z.1 ∈ Λ ∧ z.2 ∉ Λ} ∩ {ω | (openGraph ω).Adj z.1 z.2} := by
      ext ω; simp [E, and_assoc]
    rw [this]
    exact (MeasurableSet.const _).inter (measurableSet_adj _ _)
  have hpt : ∀ ω : Config V,
      ({z : V × V | z.1 ∈ Λ ∧ z.2 ∉ Λ ∧ (openGraph ω).Adj z.1 z.2}.encard : ℝ≥0∞) =
        ∑' z, (E z).indicator (fun _ => (1 : ℝ≥0∞)) ω := by
    intro ω
    rw [encard_eq_tsum_indicator]
    rfl
  simp_rw [hpt]
  rw [lintegral_tsum fun z => (measurable_const.indicator (hE z)).aemeasurable]
  simp_rw [lintegral_indicator_const (hE _), one_mul]
  rw [ENNReal.tsum_prod', tsum_eq_sum (s := Λ)]
  · refine Finset.sum_congr rfl fun x hx => tsum_congr fun y => ?_
    by_cases hy : y ∈ Λ
    · simp [E, hy]
    · have hxy : y ≠ x := fun h => hy (h ▸ hx)
      have : E (x, y) = {ω : Config V | (openGraph ω).Adj x y} := by
        ext ω; simp [E, hx, hy]
      simp only [hy, ↓reduceIte]
      rw [this, law_adj]
      simp only [hxy, ↓reduceIte]
  · intro x hx
    refine ENNReal.tsum_eq_zero.2 fun y => ?_
    have : E (x, y) = ∅ := by ext ω; simp [E, hx]
    rw [this, measure_empty]

/-! ### Non-vacuity -/

/-- On `Bool` with every pair open with probability `1/3`, the expected degree is `1/3`,
whatever the (irrelevant) value on the diagonal. -/
example : ∫⁻ ω, ({w | (openGraph ω).Adj false w}.encard : ℝ≥0∞)
    ∂law (fun _ : Sym2 Bool => (⟨1 / 3, by norm_num, by norm_num⟩ : unitInterval)) =
      (unitInterval.toNNReal ⟨1 / 3, by norm_num, by norm_num⟩ : ℝ≥0∞) := by
  rw [lintegral_degree, tsum_fintype, Fintype.sum_bool]
  simp

/-- On `ℕ` with every pair open with probability `1/2`, the expected degree is infinite. -/
example : ∫⁻ ω, ({w | (openGraph ω).Adj 0 w}.encard : ℝ≥0∞)
    ∂law (fun _ : Sym2 ℕ => (⟨1 / 2, by norm_num, by norm_num⟩ : unitInterval)) = ∞ := by
  rw [lintegral_degree]
  set c : ℝ≥0∞ := (unitInterval.toNNReal ⟨1 / 2, by norm_num, by norm_num⟩ : ℝ≥0∞)
  have hc : c ≠ 0 := by
    rw [Ne, ENNReal.coe_eq_zero]
    intro h
    have := congrArg NNReal.toReal h
    change (1 / 2 : ℝ) = 0 at this
    norm_num at this
  have : Infinite ({w : ℕ | w ≠ 0} : Set ℕ) := (finite_singleton 0).infinite_compl.to_subtype
  refine Eq.trans ?_ (ENNReal.tsum_const_eq_top_of_ne_zero (α := ({w : ℕ | w ≠ 0} : Set ℕ)) hc)
  rw [tsum_subtype ({w : ℕ | w ≠ 0} : Set ℕ) (fun _ => c)]
  congr 1
  funext w
  by_cases h : w = 0 <;> simp [h]

end PercLib.Percolation.Bond
