/-
Copyright (c) 2026 PercLib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

New for this project (issue 121, Q-5). No upstream proof is copied.
-/
module

public import PercLib.Percolation.Bond.Susceptibility
public import PercLib.Probability.Cylinder
public import Mathlib.MeasureTheory.Integral.Lebesgue.Markov
public import Mathlib.MeasureTheory.Measure.Continuity

/-!
# Tails of the cluster volume

The cluster volume `N_x = (cluster ω x).encard` is `ℕ∞`-valued. This file relates its tails
to the probability `θ(x)` that the cluster is infinite and to the susceptibility `χ(x)`:

* the tail events `{n ≤ N_x}` are measurable;
* `θ(x) = ⨅ n, P(n ≤ N_x)`;
* the tail-sum formula `χ(x) = ∑' n, P(n + 1 ≤ N_x)`, with infinite values allowed;
* Markov's inequality `n P(n ≤ N_x) ≤ χ(x)`, and `χ(x) < ∞ → θ(x) = 0`;
* the elementary lower bounds `q(s(x, y)) ≤ τ(x, y)` for `x ≠ y`, and
  `1 + ∑'_{y ≠ x} q(s(x, y)) ≤ χ(x)`.
-/

@[expose] public section

noncomputable section

open MeasureTheory Set
open scoped ENNReal

namespace PercLib.Percolation.Bond

variable {V : Type*}

/-! ### A tail-sum identity for `ℕ∞` -/

/-- An extended natural number, coerced to `ℝ≥0∞`, is the number of `n : ℕ` with
`n + 1 ≤ N`. Both sides are `∞` when `N = ⊤`. -/
theorem toENNReal_eq_tsum_ite_le (N : ℕ∞) :
    (N : ℝ≥0∞) = ∑' n : ℕ, if ((n + 1 : ℕ) : ℕ∞) ≤ N then (1 : ℝ≥0∞) else 0 := by
  classical
  have hS : {n : ℕ | ((n + 1 : ℕ) : ℕ∞) ≤ N}.encard = N := by
    induction N using ENat.recTopCoe with
    | top =>
      simp only [le_top, Set.ofPred_true]
      exact Set.encard_eq_top_iff.2 Set.infinite_univ
    | coe m =>
      simp only [Nat.cast_le, Nat.succ_le_iff]
      exact Set.Nat.encard_range m
  calc (N : ℝ≥0∞) = ({n : ℕ | ((n + 1 : ℕ) : ℕ∞) ≤ N}.encard : ℝ≥0∞) := by rw [hS]
    _ = ∑' _ : {n : ℕ | ((n + 1 : ℕ) : ℕ∞) ≤ N}, (1 : ℝ≥0∞) := (ENNReal.tsum_set_one _).symm
    _ = ∑' n : ℕ, {n : ℕ | ((n + 1 : ℕ) : ℕ∞) ≤ N}.indicator (fun _ => (1 : ℝ≥0∞)) n :=
      tsum_subtype {n : ℕ | ((n + 1 : ℕ) : ℕ∞) ≤ N} (fun _ => (1 : ℝ≥0∞))
    _ = _ := by
      congr 1
      funext n
      rw [Set.indicator_apply]
      rfl

/-! ### Measurability of tail events -/

/-- The tail events of the cluster volume are measurable. -/
theorem measurableSet_le_encard_cluster [Countable V] (x : V) (n : ℕ∞) :
    MeasurableSet {ω : Config V | n ≤ (cluster ω x).encard} :=
  measurable_encard_cluster x MeasurableSet.of_discrete

/-- The cluster is infinite exactly when every tail event occurs. -/
theorem cluster_infinite_eq_iInter_le_encard (x : V) :
    {ω : Config V | (cluster ω x).Infinite} =
      ⋂ n : ℕ, {ω : Config V | (n : ℕ∞) ≤ (cluster ω x).encard} := by
  ext ω
  simp only [mem_ofPred_eq, mem_iInter, ← Set.encard_eq_top_iff, ENat.eq_top_iff_forall_ge]

/-! ### The probability of an infinite cluster -/

/-- `θ(x)` is the limit of the tail probabilities of the cluster volume. -/
theorem law_cluster_infinite_eq_iInf [Countable V] (q : Sym2 V → unitInterval) (x : V) :
    law q {ω | (cluster ω x).Infinite} =
      ⨅ n : ℕ, law q {ω | (n : ℕ∞) ≤ (cluster ω x).encard} := by
  rw [cluster_infinite_eq_iInter_le_encard]
  refine Antitone.measure_iInter
    (fun m n hmn ω (hω : (n : ℕ∞) ≤ _) => show (m : ℕ∞) ≤ _ from
      le_trans (by exact_mod_cast hmn) hω)
    (fun n => (measurableSet_le_encard_cluster x n).nullMeasurableSet)
    ⟨0, measure_ne_top _ _⟩

/-! ### The tail-sum formula and Markov's inequality -/

/-- The tail-sum formula for the susceptibility. Infinite values are allowed on both
sides. -/
theorem chi_eq_tsum_law_le_encard [Countable V] (q : Sym2 V → unitInterval) (x : V) :
    chi q x = ∑' n : ℕ, law q {ω | ((n + 1 : ℕ) : ℕ∞) ≤ (cluster ω x).encard} := by
  have hpt : ∀ ω : Config V, ((cluster ω x).encard : ℝ≥0∞) =
      ∑' n : ℕ, {ω : Config V | ((n + 1 : ℕ) : ℕ∞) ≤ (cluster ω x).encard}.indicator
        (fun _ => (1 : ℝ≥0∞)) ω := by
    intro ω
    rw [toENNReal_eq_tsum_ite_le]
    congr 1
    funext n
    rw [Set.indicator_apply]
    rfl
  simp_rw [chi, hpt]
  rw [lintegral_tsum fun n =>
    (measurable_const.indicator (measurableSet_le_encard_cluster x _)).aemeasurable]
  congr 1
  funext n
  exact lintegral_indicator_one (measurableSet_le_encard_cluster x _)

/-- Markov's inequality for the cluster volume. -/
theorem mul_law_le_encard_le_chi [Countable V] (q : Sym2 V → unitInterval) (x : V) (n : ℕ) :
    (n : ℝ≥0∞) * law q {ω | (n : ℕ∞) ≤ (cluster ω x).encard} ≤ chi q x := by
  have h := mul_meas_ge_le_lintegral₀ (μ := law q)
    ((Measurable.of_discrete (f := ((↑) : ℕ∞ → ℝ≥0∞))).comp (measurable_encard_cluster x)).aemeasurable (n : ℝ≥0∞)
  have hset : {ω : Config V | (n : ℝ≥0∞) ≤ (((cluster ω x).encard : ℕ∞) : ℝ≥0∞)} =
      {ω | (n : ℕ∞) ≤ (cluster ω x).encard} := by
    ext ω
    simp only [mem_ofPred_eq]
    rw [← ENat.toENNReal_coe, ENat.toENNReal_le]
  rw [Function.comp_def, hset] at h
  exact h

/-- If the susceptibility is finite, the cluster is almost surely finite. -/
theorem law_cluster_infinite_eq_zero_of_chi_ne_top [Countable V] (q : Sym2 V → unitInterval)
    (x : V) (h : chi q x ≠ ∞) : law q {ω | (cluster ω x).Infinite} = 0 := by
  have hae := ae_lt_top (μ := law q)
    ((Measurable.of_discrete (f := ((↑) : ℕ∞ → ℝ≥0∞))).comp (measurable_encard_cluster x)) h
  rw [ae_iff] at hae
  refine measure_mono_null (fun ω hω => ?_) hae
  simp only [mem_ofPred_eq, not_lt, top_le_iff] at hω ⊢
  show ((cluster ω x).encard : ℝ≥0∞) = ∞
  rw [Set.encard_eq_top_iff.2 hω]
  rfl

/-- If the cluster is infinite with positive probability, the susceptibility is
infinite. -/
theorem chi_eq_top_of_law_cluster_infinite_ne_zero [Countable V]
    (q : Sym2 V → unitInterval) (x : V) (h : law q {ω | (cluster ω x).Infinite} ≠ 0) :
    chi q x = ∞ := by
  by_contra hne
  exact h (law_cluster_infinite_eq_zero_of_chi_ne_top q x hne)

/-! ### Elementary lower bounds -/

/-- An open pair connects its endpoints, so the probability that a pair of distinct vertices
is open is at most their two-point function. No countability is needed. -/
theorem toNNReal_le_tau (q : Sym2 V → unitInterval) {x y : V} (hxy : x ≠ y) :
    (unitInterval.toNNReal (q s(x, y)) : ℝ≥0∞) ≤ tau q x y := by
  rw [← PercLib.Probability.prodBernoulli_setOf_mem q s(x, y), tau]
  exact measure_mono fun ω hω => mem_conn_of_mem hxy hω

open Classical in
/-- The susceptibility is at least one plus the row sum of the edge probabilities. -/
theorem one_add_rowSum_le_chi [Countable V] (q : Sym2 V → unitInterval) (x : V) :
    1 + (∑' y, if y = x then 0 else (unitInterval.toNNReal (q s(x, y)) : ℝ≥0∞)) ≤
      chi q x := by
  rw [chi_eq_tsum_tau, ENNReal.tsum_eq_add_tsum_ite (f := fun y => tau q x y) x, tau_self]
  gcongr with y
  split_ifs with hy
  · exact le_rfl
  · exact toNNReal_le_tau q (Ne.symm hy)

/-! ### Non-vacuity -/

/-- Smallest case: on one vertex the susceptibility is one, so the hypothesis of
`law_cluster_infinite_eq_zero_of_chi_ne_top` holds. -/
example (q : Sym2 Unit → unitInterval) : law q {ω | (cluster ω ()).Infinite} = 0 :=
  law_cluster_infinite_eq_zero_of_chi_ne_top q ()
    (by rw [chi_eq_tsum_tau]; simp [tau_self])

/-- Two distinct vertices with their pair always open: the lower bound forces `τ = 1`. -/
example : tau (fun _ : Sym2 Bool => (1 : unitInterval)) false true = 1 :=
  le_antisymm (tau_le_one _ _ _) (by
    simpa using toNNReal_le_tau (fun _ : Sym2 Bool => (1 : unitInterval))
      (x := false) (y := true) (by decide))

/-- Largest parameter: on `ℕ` with every pair open, the row-sum bound already gives
`χ = ∞`. -/
example (x : ℕ) : chi (fun _ : Sym2 ℕ => (1 : unitInterval)) x = ∞ := by
  refine top_le_iff.1 (le_trans ?_ (one_add_rowSum_le_chi _ x))
  refine le_trans ?_ le_add_self
  have h := ENNReal.tsum_eq_add_tsum_ite (f := fun _ : ℕ => (1 : ℝ≥0∞)) x
  rw [ENNReal.tsum_const_eq_top_of_ne_zero one_ne_zero, eq_comm, ENNReal.add_eq_top] at h
  rcases h with h | h
  · exact absurd h ENNReal.one_ne_top
  · refine le_of_eq (h.symm.trans ?_)
    congr 1

end PercLib.Percolation.Bond

end
