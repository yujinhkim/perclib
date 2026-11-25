/-
Copyright (c) 2026 PercLib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

New proofs for issue 235 (Q-52), written on 2026-11-15 by PROVER-E. No upstream proof is
copied.
-/
module

public import Mathlib.Probability.Independence.Integration
public import PercLib.Percolation.Bond.Basic
public import PercLib.Probability.Cylinder
public import PercLib.Probability.ProdBernoulliIndependence

/-!
# The generating function of the degree

For `s ∈ [0, 1]` and a finite set `F` of vertices, the number `N_F(ω)` of open pairs
`s(v, w)`, `w ∈ F`, has generating function

`E s^{N_F} = ∏_{w ∈ F} (s q(s(v,w)) + (1 - q(s(v,w))))`,

that is `∏ (1 - (1 - s) q)`, by independence of distinct pairs (`lintegral_pow_card_open`).
Along an increasing sequence of finite sets the generating functions decrease to the
generating function of the number of open pairs to their union
(`lintegral_iInf_pow_card_open`). At `s = 0` this is the probability that no such pair is
open, and along an exhaustion of the other vertices it is the probability that `v` is
isolated (`law_isolated_eq_iInf`). This file adds no definition.
-/

@[expose] public section

open MeasureTheory ProbabilityTheory Set PercLib.Probability
open scoped ENNReal
open Classical

namespace PercLib.Percolation.Bond

variable {V : Type*}

/-- The factor of one pair: `s` if it is open, `1` if it is closed. -/
theorem lintegral_ite_mem (q : Sym2 V → unitInterval) (e : Sym2 V) (s : ℝ≥0∞) :
    ∫⁻ ω, (if e ∈ ω then s else 1) ∂law q =
      s * (unitInterval.toNNReal (q e) : ℝ≥0∞) + (1 - (unitInterval.toNNReal (q e) : ℝ≥0∞)) := by
  classical
  have hA : MeasurableSet {ω : Config V | e ∈ ω} := measurableSet_mem e
  have hsplit : (fun ω : Config V => if e ∈ ω then s else 1) =
      fun ω => {ω : Config V | e ∈ ω}.indicator (fun _ => s) ω +
        {ω : Config V | e ∈ ω}ᶜ.indicator (fun _ => 1) ω := by
    funext ω
    by_cases h : e ∈ ω <;> simp [h]
  rw [hsplit, lintegral_add_left (measurable_const.indicator hA),
    lintegral_indicator_const hA, lintegral_indicator_const hA.compl, one_mul,
    prob_compl_eq_one_sub hA]
  change s * prodBernoulli q _ + (1 - prodBernoulli q _) = _
  rw [prodBernoulli_setOf_mem]

/-- The factors of distinct pairs at `v` are independent. -/
theorem iIndepFun_ite_mem (q : Sym2 V → unitInterval) (v : V) (s : ℝ≥0∞) :
    iIndepFun (fun (w : V) (ω : Config V) => if s(v, w) ∈ ω then s else (1 : ℝ≥0∞)) (law q) := by
  classical
  have h := ((prodBernoulli_iIndepFun_mem q).precomp
    (g := fun w : V => s(v, w)) fun a b hab => Sym2.congr_right.1 hab)
  exact h.comp (fun _ (P : Prop) => if P then s else (1 : ℝ≥0∞))
    (fun _ => measurable_from_top)

/-- **The generating function of the number of open pairs to a finite set.** -/
theorem lintegral_pow_card_open (q : Sym2 V → unitInterval) (v : V) (F : Finset V)
    (s : ℝ≥0∞) :
    ∫⁻ ω, s ^ (F.filter fun w => s(v, w) ∈ ω).card ∂law q =
      ∏ w ∈ F, (s * (unitInterval.toNNReal (q s(v, w)) : ℝ≥0∞) +
        (1 - (unitInterval.toNNReal (q s(v, w)) : ℝ≥0∞))) := by
  classical
  have hpt : ∀ ω : Config V, s ^ (F.filter fun w => s(v, w) ∈ ω).card =
      ∏ w ∈ F, (if s(v, w) ∈ ω then s else 1) := by
    intro ω
    rw [Finset.prod_ite, Finset.prod_const, Finset.prod_const_one, mul_one]
  simp_rw [hpt]
  rw [lintegral_prod_eq_prod_lintegral_of_indepFun F _ (iIndepFun_ite_mem q v s)
    (fun w => Measurable.ite (measurableSet_mem _) measurable_const measurable_const)]
  exact Finset.prod_congr rfl fun w _ => lintegral_ite_mem q _ s

/-- **The probability that no pair to a finite set is open** (the case `s = 0`). -/
theorem law_forall_not_mem (q : Sym2 V → unitInterval) (v : V) (F : Finset V) :
    law q {ω : Config V | ∀ w ∈ F, s(v, w) ∉ ω} =
      ∏ w ∈ F, (1 - (unitInterval.toNNReal (q s(v, w)) : ℝ≥0∞)) := by
  classical
  have h := lintegral_pow_card_open q v F 0
  simp only [zero_mul, zero_add] at h
  rw [← h]
  have hpt : ∀ ω : Config V, (0 : ℝ≥0∞) ^ (F.filter fun w => s(v, w) ∈ ω).card =
      {ω : Config V | ∀ w ∈ F, s(v, w) ∉ ω}.indicator (fun _ => 1) ω := by
    intro ω
    by_cases hω : ∀ w ∈ F, s(v, w) ∉ ω
    · have : (F.filter fun w => s(v, w) ∈ ω) = ∅ := Finset.filter_eq_empty_iff.2 hω
      rw [this, Finset.card_empty, pow_zero, indicator_of_mem (by exact hω)]
    · have hne : (F.filter fun w => s(v, w) ∈ ω).card ≠ 0 := by
        push Not at hω
        obtain ⟨w, hw, hwω⟩ := hω
        exact Finset.card_ne_zero.2 ⟨w, Finset.mem_filter.2 ⟨hw, hwω⟩⟩
      rw [zero_pow hne, indicator_of_notMem (by exact hω)]
  simp_rw [hpt]
  have hm : MeasurableSet {ω : Config V | ∀ w ∈ F, s(v, w) ∉ ω} := by
    have : {ω : Config V | ∀ w ∈ F, s(v, w) ∉ ω} = ⋂ w ∈ F, {ω : Config V | s(v, w) ∈ ω}ᶜ := by
      ext ω
      simp
    rw [this]
    exact Finset.measurableSet_biInter F fun w _ => (measurableSet_mem _).compl
  rw [lintegral_indicator_const hm, one_mul]

/-- **Monotone limit along increasing finite sets.** For `s ≤ 1` the generating functions
decrease to that of the number of open pairs to the union. -/
theorem lintegral_iInf_pow_card_open (q : Sym2 V → unitInterval) (v : V) {F : ℕ → Finset V}
    (hF : Monotone F) {s : ℝ≥0∞} (hs : s ≤ 1) :
    ∫⁻ ω, ⨅ n, s ^ ((F n).filter fun w => s(v, w) ∈ ω).card ∂law q =
      ⨅ n, ∏ w ∈ F n, (s * (unitInterval.toNNReal (q s(v, w)) : ℝ≥0∞) +
        (1 - (unitInterval.toNNReal (q s(v, w)) : ℝ≥0∞))) := by
  classical
  rw [lintegral_iInf]
  · simp_rw [lintegral_pow_card_open]
  · intro n
    have : (fun ω : Config V => s ^ ((F n).filter fun w => s(v, w) ∈ ω).card) =
        fun ω => ∏ w ∈ F n, (if s(v, w) ∈ ω then s else 1) := by
      funext ω
      rw [Finset.prod_ite, Finset.prod_const, Finset.prod_const_one, mul_one]
    rw [this]
    exact Finset.measurable_prod _ fun w _ =>
      Measurable.ite (measurableSet_mem _) measurable_const measurable_const
  · intro m n hmn ω
    exact pow_le_pow_right_of_le_one' hs (Finset.card_le_card (Finset.filter_subset_filter _
      (hF hmn)))
  · refine ne_top_of_le_ne_top ENNReal.one_ne_top ?_
    calc ∫⁻ ω, s ^ ((F 0).filter fun w => s(v, w) ∈ ω).card ∂law q ≤ ∫⁻ _ω, 1 ∂law q :=
          lintegral_mono fun ω => pow_le_one₀ zero_le hs
      _ = 1 := by simp

/-- **The probability that `v` is isolated**, along an increasing exhaustion of the other
vertices by finite sets. -/
theorem law_isolated_eq_iInf [Countable V] (q : Sym2 V → unitInterval) (v : V)
    {F : ℕ → Finset V} (hF : Monotone F) (hcov : ∀ w, w ≠ v → ∃ n, w ∈ F n) :
    law q {ω : Config V | ∀ w, ¬ (openGraph ω).Adj v w} =
      ⨅ n, ∏ w ∈ (F n).erase v, (1 - (unitInterval.toNNReal (q s(v, w)) : ℝ≥0∞)) := by
  classical
  have hset : {ω : Config V | ∀ w, ¬ (openGraph ω).Adj v w} =
      ⋂ n, {ω : Config V | ∀ w ∈ (F n).erase v, s(v, w) ∉ ω} := by
    ext ω
    simp only [mem_ofPred_eq, mem_iInter, openGraph_adj_iff, not_and, Finset.mem_erase]
    constructor
    · intro h n w ⟨hwv, _⟩ hω
      exact h w hω (Ne.symm hwv)
    · intro h w hω hvw
      obtain ⟨n, hn⟩ := hcov w (Ne.symm hvw)
      exact h n w ⟨Ne.symm hvw, hn⟩ hω
  have hanti : Antitone fun n => {ω : Config V | ∀ w ∈ (F n).erase v, s(v, w) ∉ ω} :=
    fun m n hmn ω hω w hw => hω w (Finset.erase_subset_erase v (hF hmn) hw)
  have hm : ∀ n, MeasurableSet {ω : Config V | ∀ w ∈ (F n).erase v, s(v, w) ∉ ω} := by
    intro n
    simp only [ofPred_forall]
    exact MeasurableSet.iInter fun w => MeasurableSet.iInter fun _ =>
      (measurableSet_mem _).compl
  rw [hset, hanti.measure_iInter (fun n => (hm n).nullMeasurableSet) ⟨0, measure_ne_top _ _⟩]
  refine iInf_congr fun n => ?_
  rw [law_forall_not_mem]

/-! ### Non-vacuity -/

/-- On `Bool`, the generating function of the degree of `false` is `s t + (1 - t)`. -/
example (q : Sym2 Bool → unitInterval) (s : ℝ≥0∞) :
    ∫⁻ ω, s ^ (({true} : Finset Bool).filter fun w => s(false, w) ∈ ω).card ∂law q =
      s * (unitInterval.toNNReal (q s(false, true)) : ℝ≥0∞) +
        (1 - (unitInterval.toNNReal (q s(false, true)) : ℝ≥0∞)) := by
  rw [lintegral_pow_card_open, Finset.prod_singleton]

/-- On `ℕ`, the probability that `0` is isolated, along the exhaustion `{0, …, n}`. -/
example (q : Sym2 ℕ → unitInterval) :
    law q {ω : Config ℕ | ∀ w, ¬ (openGraph ω).Adj 0 w} =
      ⨅ n, ∏ w ∈ (Finset.range (n + 1)).erase 0,
        (1 - (unitInterval.toNNReal (q s(0, w)) : ℝ≥0∞)) := by
  convert law_isolated_eq_iInf q 0 (fun _ _ h => Finset.range_subset_range.2 (by omega))
    fun w _ => ⟨w, Finset.mem_range.2 (Nat.lt_succ_self w)⟩

end PercLib.Percolation.Bond
