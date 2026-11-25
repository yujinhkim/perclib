/-
Copyright (c) 2026 PercLib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

New proofs for issue 120 (Q-4), written on 2026-11-14 by PROVER-E. No upstream proof is
copied: the probabilistic input is mathlib's second Borel–Cantelli lemma
`ProbabilityTheory.measure_limsup_eq_one`.
-/
module

public import Mathlib.Analysis.Convex.SpecificFunctions.Basic
public import Mathlib.Probability.BorelCantelli
public import PercLib.Percolation.Bond.Intensity.Defs
public import PercLib.Probability.Cylinder
public import PercLib.Probability.ProdBernoulliIndependence

/-!
# Infinite row sums give infinite degree and zero critical intensity

If the row sum of `q` at `v` is infinite, the second Borel–Cantelli lemma gives `v`
infinitely many open neighbours almost surely, so the cluster of `v` is infinite almost
surely. For an intensity kernel `J` with an infinite row sum at `v`, the row sum of
`intensityProfile J β` at `v` is infinite for every `β > 0`, because
`1 - e^{-t} ≥ (1 - e^{-1}) min(t, 1)`; hence both critical intensities vanish.

Row sums exclude the diagonal (D-2). The hypothesis is about the one vertex `v`. This
file adds no definition.
-/

@[expose] public section

open MeasureTheory ProbabilityTheory Set Filter PercLib.Probability
open Classical
open scoped ENNReal NNReal

namespace PercLib.Percolation.Bond

variable {V : Type*}

/-- A row sum with the diagonal excluded is a sum over the other vertices. -/
theorem tsum_ite_eq_tsum_ne (v : V) (f : V → ℝ≥0∞) :
    (∑' w, if w = v then 0 else f w) = ∑' w : {w : V | w ≠ v}, f w := by
  rw [tsum_subtype]
  congr 1
  funext w
  by_cases h : w = v <;> simp [h]

/-- If the sum of `f` is infinite and `f` is finite, so is the sum of `min f 1`. -/
theorem tsum_min_one_eq_top {α : Type*} {f : α → ℝ≥0∞} (hf : ∀ a, f a ≠ ∞)
    (h : ∑' a, f a = ∞) : ∑' a, min (f a) 1 = ∞ := by
  by_contra hne
  have hev : ∀ᶠ a in cofinite, min (f a) 1 < 1 :=
    (tendsto_order.1 (ENNReal.tendsto_cofinite_zero_of_tsum_ne_top hne)).2 1 one_pos
  set T := {a | ¬ min (f a) 1 < 1}
  have hT : T.Finite := Filter.eventually_cofinite.1 hev
  have hle : ∀ a, f a ≤ min (f a) 1 + T.indicator f a := by
    intro a
    by_cases ha : a ∈ T
    · rw [indicator_of_mem ha]; exact le_add_self
    · rw [indicator_of_notMem ha, add_zero]
      have : min (f a) 1 < 1 := not_not.1 ha
      rcases min_lt_iff.1 this with h1 | h1
      · exact le_of_eq (min_eq_left h1.le).symm
      · exact absurd h1 (lt_irrefl _)
  have hfin : ∑' a, T.indicator f a ≠ ∞ := by
    rw [tsum_eq_sum (s := hT.toFinset) fun a ha => indicator_of_notMem (by simpa using ha) _]
    exact ENNReal.sum_ne_top.2 fun a _ => (indicator_le_self T f a).trans_lt (hf a).lt_top |>.ne
  have := (ENNReal.tsum_le_tsum hle).trans_eq (ENNReal.tsum_add)
  rw [h, top_le_iff] at this
  exact (ENNReal.add_ne_top.2 ⟨hne, hfin⟩) this

/-- **Second Borel–Cantelli for the neighbours of a vertex.** If the row sum of `q` at `v`
is infinite, then almost surely `v` has infinitely many open neighbours. -/
theorem ae_infinite_neighbors_of_rowSum_eq_top [Countable V] (q : Sym2 V → unitInterval)
    (v : V) (h : (∑' w, if w = v then 0 else (unitInterval.toNNReal (q s(v, w)) : ℝ≥0∞)) = ∞) :
    ∀ᵐ ω ∂law q, {w | (openGraph ω).Adj v w}.Infinite := by
  set N : Set V := {w | w ≠ v}
  have hsum : ∑' w : N, (unitInterval.toNNReal (q s(v, w)) : ℝ≥0∞) = ∞ := by
    rw [tsum_ite_eq_tsum_ne v] at h
    exact h
  have : Infinite N := by
    by_contra hfin
    rw [not_infinite_iff_finite] at hfin
    have hle : ∑' w : N, (unitInterval.toNNReal (q s(v, w)) : ℝ≥0∞) ≤ (N.encard : ℝ≥0∞) := by
      rw [← ENNReal.tsum_set_one]
      refine ENNReal.tsum_le_tsum fun w => ?_
      exact ENNReal.coe_le_one_iff.2 (by
        change ((q s(v, (w : V)) : ℝ)) ≤ 1
        exact (q _).2.2)
    rw [hsum, top_le_iff] at hle
    have : N.encard ≠ ⊤ := (toFinite N).encard_lt_top.ne
    exact this (by exact_mod_cast hle)
  obtain ⟨e⟩ : Nonempty (N ≃ ℕ) := ⟨(nonempty_denumerable N).some.eqv⟩
  set g : ℕ → V := fun n => (e.symm n : V)
  have hg : Function.Injective g := Subtype.val_injective.comp e.symm.injective
  set A : ℕ → Set (Config V) := fun n => {ω | s(v, g n) ∈ ω}
  have hind : iIndepSet A (law q) :=
    (prodBernoulli_iIndepSet_mem q).precomp (g := fun n => s(v, g n))
      fun a b hab => hg (Sym2.congr_right.1 hab)
  have hsumA : ∑' n, law q (A n) = ∞ := by
    have : ∀ n, law q (A n) = (unitInterval.toNNReal (q s(v, ((e.symm n : N) : V))) : ℝ≥0∞) :=
      fun n => prodBernoulli_setOf_mem q _
    simp_rw [this]
    rw [e.symm.tsum_eq (fun w : N => (unitInterval.toNNReal (q s(v, (w : V))) : ℝ≥0∞)), hsum]
  have hlim := measure_limsup_eq_one (fun n => measurableSet_mem _) hind hsumA
  have hmeas : MeasurableSet (limsup A atTop) := by
    rw [limsup_eq_iInf_iSup_of_nat]
    exact MeasurableSet.iInter fun n => MeasurableSet.iUnion fun i =>
      MeasurableSet.iUnion fun _ => measurableSet_mem _
  have hae : ∀ᵐ ω ∂law q, ω ∈ limsup A atTop :=
    (ae_mem_iff_measure_eq hmeas.nullMeasurableSet).2 (by rw [hlim, measure_univ])
  filter_upwards [hae] with ω hω
  rw [mem_limsup_iff_frequently_mem, Nat.frequently_atTop_iff_infinite] at hω
  refine Infinite.mono ?_ (hω.image hg.injOn)
  rintro _ ⟨n, hn, rfl⟩
  exact (openGraph_adj_iff ω v (g n)).2 ⟨hn, fun hv => (e.symm n).2 hv.symm⟩

/-- **An infinite row sum at `v` makes the cluster of `v` infinite almost surely.** -/
theorem law_cluster_infinite_eq_one_of_rowSum_eq_top [Countable V] (q : Sym2 V → unitInterval)
    (v : V) (h : (∑' w, if w = v then 0 else (unitInterval.toNNReal (q s(v, w)) : ℝ≥0∞)) = ∞) :
    law q {ω | (cluster ω v).Infinite} = 1 := by
  have hae : ∀ᵐ ω ∂law q, (cluster ω v).Infinite :=
    (ae_infinite_neighbors_of_rowSum_eq_top q v h).mono fun ω hω =>
      hω.mono fun w hw => SimpleGraph.Adj.reachable hw
  exact (prob_compl_eq_zero_iff (measurableSet_cluster_infinite v)).1 (ae_iff.1 hae)

/-- `1 - e^{-t} ≥ (1 - e^{-1}) min(t, 1)` for `t ≥ 0`. -/
theorem one_sub_exp_neg_one_mul_min_le (t : ℝ) (ht : 0 ≤ t) :
    (1 - Real.exp (-1)) * min t 1 ≤ 1 - Real.exp (-t) := by
  rcases le_total t 1 with h | h
  · rw [min_eq_left h]
    have hc := convexOn_exp.2 (mem_univ (0 : ℝ)) (mem_univ (-1 : ℝ)) (sub_nonneg.2 h) ht
      (by ring)
    simp only [smul_eq_mul, mul_zero, zero_add, Real.exp_zero, mul_one, mul_neg] at hc
    linarith
  · rw [min_eq_right h, mul_one]
    have := Real.exp_le_exp.2 (neg_le_neg h)
    linarith

/-- **An infinite row sum of `J` gives an infinite row sum of the profile at every
positive intensity.** -/
theorem rowSum_intensityProfile_eq_top (J : Sym2 V → ℝ≥0) (v : V) {β : ℝ≥0} (hβ : 0 < β)
    (hJ : (∑' w, if w = v then 0 else (J s(v, w) : ℝ≥0∞)) = ∞) :
    (∑' w, if w = v then 0 else
      (unitInterval.toNNReal (intensityProfile J β s(v, w)) : ℝ≥0∞)) = ∞ := by
  set c : ℝ≥0 := ⟨1 - Real.exp (-1), sub_nonneg.2 (Real.exp_le_one_iff.2 (by norm_num))⟩
  have hc : c ≠ 0 := by
    intro h0
    have : (1 : ℝ) - Real.exp (-1) = 0 := congrArg NNReal.toReal h0
    have := Real.exp_lt_one_iff.2 (show (-1 : ℝ) < 0 by norm_num)
    linarith
  have hpoint : ∀ w, (c : ℝ≥0∞) * (if w = v then 0 else min ((β * J s(v, w) : ℝ≥0) : ℝ≥0∞) 1) ≤
      if w = v then 0 else
        (unitInterval.toNNReal (intensityProfile J β s(v, w)) : ℝ≥0∞) := by
    intro w
    split_ifs
    · simp
    · rw [← ENNReal.coe_one, ← ENNReal.coe_min, ← ENNReal.coe_mul, ENNReal.coe_le_coe,
        ← NNReal.coe_le_coe]
      have := one_sub_exp_neg_one_mul_min_le ((β : ℝ) * (J s(v, w) : ℝ))
        (mul_nonneg β.coe_nonneg (J _).coe_nonneg)
      change (1 - Real.exp (-1)) * min ((β : ℝ) * (J s(v, w) : ℝ)) 1 ≤
        1 - Real.exp (-(β : ℝ) * (J s(v, w) : ℝ))
      rwa [neg_mul]
  have hmin : (∑' w, if w = v then 0 else min ((β * J s(v, w) : ℝ≥0) : ℝ≥0∞) 1) = ∞ := by
    have heq : ∀ w, (if w = v then 0 else min ((β * J s(v, w) : ℝ≥0) : ℝ≥0∞) 1) =
        min (if w = v then 0 else ((β * J s(v, w) : ℝ≥0) : ℝ≥0∞)) 1 := by
      intro w; split_ifs <;> simp
    simp_rw [heq]
    refine tsum_min_one_eq_top (fun w => by
      split_ifs
      · simp
      · exact ENNReal.coe_ne_top) ?_
    have : ∀ w, (if w = v then 0 else ((β * J s(v, w) : ℝ≥0) : ℝ≥0∞)) =
        (β : ℝ≥0∞) * (if w = v then 0 else (J s(v, w) : ℝ≥0∞)) := by
      intro w; split_ifs <;> simp
    simp_rw [this]
    rw [ENNReal.tsum_mul_left, hJ, ENNReal.mul_top (by exact_mod_cast hβ.ne')]
  refine top_le_iff.1 ?_
  calc (∞ : ℝ≥0∞) = (c : ℝ≥0∞) * ∑' w, (if w = v then 0 else
        min ((β * J s(v, w) : ℝ≥0) : ℝ≥0∞) 1) := by
        rw [hmin, ENNReal.mul_top (by exact_mod_cast hc)]
    _ = ∑' w, (c : ℝ≥0∞) * (if w = v then 0 else
        min ((β * J s(v, w) : ℝ≥0) : ℝ≥0∞) 1) := (ENNReal.tsum_mul_left).symm
    _ ≤ _ := ENNReal.tsum_le_tsum hpoint

/-- **A kernel with an infinite row sum at `v` has root critical intensity zero at `v`.** -/
theorem rootCriticalIntensity_eq_zero_of_rowSum_eq_top [Countable V] (J : Sym2 V → ℝ≥0)
    (v : V) (hJ : (∑' w, if w = v then 0 else (J s(v, w) : ℝ≥0∞)) = ∞) :
    rootCriticalIntensity J v = 0 := by
  refine le_antisymm (ENNReal.le_of_forall_pos_le_add fun ε hε _ => ?_) (by simp)
  rw [zero_add]
  refine sInf_le ⟨ε, rfl, ?_⟩
  show 0 < law (intensityProfile J ε) {ω | (cluster ω v).Infinite}
  rw [law_cluster_infinite_eq_one_of_rowSum_eq_top _ v
    (rowSum_intensityProfile_eq_top J v hε hJ)]
  exact one_pos

/-- **A kernel with an infinite row sum at one vertex has global critical intensity
zero.** -/
theorem globalCriticalIntensity_eq_zero_of_rowSum_eq_top [Countable V] (J : Sym2 V → ℝ≥0)
    (v : V) (hJ : (∑' w, if w = v then 0 else (J s(v, w) : ℝ≥0∞)) = ∞) :
    globalCriticalIntensity J = 0 := by
  refine le_antisymm (ENNReal.le_of_forall_pos_le_add fun ε hε _ => ?_) (by simp)
  rw [zero_add]
  refine sInf_le ⟨ε, rfl, ?_⟩
  show 0 < law (intensityProfile J ε) {ω | ∃ x, (cluster ω x).Infinite}
  have h2 : law (intensityProfile J ε) {ω | (cluster ω v).Infinite} ≤
      law (intensityProfile J ε) {ω | ∃ x, (cluster ω x).Infinite} :=
    measure_mono fun ω hω => ⟨v, hω⟩
  rw [law_cluster_infinite_eq_one_of_rowSum_eq_top _ v
    (rowSum_intensityProfile_eq_top J v hε hJ)] at h2
  exact lt_of_lt_of_le one_pos h2

/-! ### Non-vacuity -/

/-- A constant nonzero row on an infinite vertex type has infinite sum. -/
theorem tsum_ite_const_eq_top [Infinite V] (v : V) {c : ℝ≥0∞} (hc : c ≠ 0) :
    (∑' w, if w = v then 0 else c) = ∞ := by
  rw [tsum_ite_eq_tsum_ne v (fun _ => c)]
  have : Infinite {w : V | w ≠ v} := (finite_singleton v).infinite_compl.to_subtype
  exact ENNReal.tsum_const_eq_top_of_ne_zero hc

/-- `V = ℕ`, `q ≡ 1/2`: the cluster of `0` is infinite almost surely. -/
example : law (fun _ : Sym2 ℕ => (⟨1 / 2, by norm_num, by norm_num⟩ : unitInterval))
    {ω | (cluster ω 0).Infinite} = 1 :=
  law_cluster_infinite_eq_one_of_rowSum_eq_top _ 0 (tsum_ite_const_eq_top 0 (by
    rw [Ne, ENNReal.coe_eq_zero]
    intro h
    have := congrArg NNReal.toReal h
    change (1 / 2 : ℝ) = 0 at this
    norm_num at this))

/-- `J ≡ 1` on `ℕ`: both critical intensities are zero. -/
example : rootCriticalIntensity (fun _ : Sym2 ℕ => 1) 0 = 0 ∧
    globalCriticalIntensity (fun _ : Sym2 ℕ => 1) = 0 := by
  have h := tsum_ite_const_eq_top (V := ℕ) 0 (c := ((1 : ℝ≥0) : ℝ≥0∞)) (by simp)
  exact ⟨rootCriticalIntensity_eq_zero_of_rowSum_eq_top _ 0 h,
    globalCriticalIntensity_eq_zero_of_rowSum_eq_top _ 0 h⟩

end PercLib.Percolation.Bond
