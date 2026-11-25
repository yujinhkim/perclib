/-
Cut estimates for one-dimensional long-range bond percolation. New proofs using
mathlib 56a005855ea17e0b0958f73ec801ae140b0a1679 (product measures, infinite products,
and summability). The model is the canonical set of unordered open pairs.
-/
module

public import PercLib.Percolation.Bond.Basic
public import PercLib.Probability.ProdBernoulliIndependence
public import Mathlib.Analysis.SpecialFunctions.Log.Summable
public import Mathlib.Topology.Algebra.InfiniteSum.Real

@[expose] public section

open MeasureTheory ProbabilityTheory PercLib.Probability PercLib.Percolation.Bond
open scoped ENNReal NNReal

namespace PercLib.Models.LongRange

/-- A closed gap prevents a connection from crossing it. -/
theorem le_cut_iff_of_reachable (ω : Config ℤ) (k : ℤ)
    (hc : ∀ a b, a ≤ k → k < b → s(a, b) ∉ ω) {x y : ℤ}
    (h : (openGraph ω).Reachable x y) : x ≤ k ↔ y ≤ k := by
  have hstep : ∀ a b, (openGraph ω).Adj a b → (a ≤ k ↔ b ≤ k) := by
    intro a b hab
    have he := (openGraph_adj_iff ω a b).mp hab |>.1
    constructor
    · intro ha
      by_contra hb
      exact hc a b ha (lt_of_not_ge hb) he
    · intro hb
      by_contra ha
      exact hc b a hb (lt_of_not_ge ha) (by simpa only [Sym2.eq_swap] using he)
  have hr := (SimpleGraph.reachable_iff_reflTransGen x y).mp h
  clear h
  induction hr with
  | refl => rfl
  | @tail b c _ hab ih => exact ih.trans (hstep b c hab)

/-- Two cuts around the origin trap its cluster in the finite interval between them. -/
theorem cluster_subset_of_cuts (ω : Config ℤ) {k₁ k₂ : ℤ} (h₁ : k₁ < 0) (h₂ : 0 ≤ k₂)
    (hc₁ : ∀ a b, a ≤ k₁ → k₁ < b → s(a, b) ∉ ω)
    (hc₂ : ∀ a b, a ≤ k₂ → k₂ < b → s(a, b) ∉ ω) :
    cluster ω 0 ⊆ Set.Ioc k₁ k₂ := by
  intro y hy
  have hleft := le_cut_iff_of_reachable ω k₁ hc₁ hy
  have hright := le_cut_iff_of_reachable ω k₂ hc₂ hy
  exact ⟨lt_of_not_ge (fun h => (not_le.mpr h₁) (hleft.mpr h)), hright.mp h₂⟩

/-- In particular, a cluster bracketed by cuts is finite. -/
theorem finite_cluster_of_cuts (ω : Config ℤ) {k₁ k₂ : ℤ} (h₁ : k₁ < 0) (h₂ : 0 ≤ k₂)
    (hc₁ : ∀ a b, a ≤ k₁ → k₁ < b → s(a, b) ∉ ω)
    (hc₂ : ∀ a b, a ≤ k₂ → k₂ < b → s(a, b) ∉ ω) :
    (cluster ω 0).Finite :=
  (Set.finite_Ioc k₁ k₂).subset (cluster_subset_of_cuts ω h₁ h₂ hc₁ hc₂)

/-- A gap-cut event is measurable. -/
theorem measurableSet_cut (k : ℤ) :
    MeasurableSet {ω : Config ℤ | ∀ a b, a ≤ k → k < b → s(a, b) ∉ ω} := by
  simp only [Set.ofPred_forall]
  exact MeasurableSet.iInter fun a => MeasurableSet.iInter fun b =>
    MeasurableSet.iInter fun _ => MeasurableSet.iInter fun _ =>
      (measurableSet_mem s(a, b)).compl

/-- Closed coordinates in a countable, injectively indexed family have the product law. -/
theorem prodBernoulli_forall_notMem {ι α : Type*} [Countable α]
    (p : ι → unitInterval) (f : α → ι) (hf : Function.Injective f) :
    prodBernoulli p {ω | ∀ a, f a ∉ ω} =
      ∏' a, (unitInterval.toNNReal (unitInterval.symm (p (f a))) : ℝ≥0∞) := by
  classical
  rw [prodBernoulli_eq_map, Measure.map_apply (show Measurable (fun q : ι → Prop => {i | q i}) from by fun_prop)
    (by simpa only [Set.ofPred_forall, Set.compl_ofPred] using
      MeasurableSet.iInter (fun a => (measurableSet_mem (f a)).compl))]
  have hset : (fun q : ι → Prop => {i | q i}) ⁻¹' {ω | ∀ a, f a ∉ ω} =
      Set.pi (Set.range f) (fun _ => {False}) := by
    ext q
    simp only [Set.mem_preimage, Set.mem_ofPred_eq, Set.mem_pi, Set.mem_range,
      Set.mem_singleton_iff, forall_exists_index, forall_apply_eq_imp_iff]
    simp
  rw [hset]
  refine (Measure.infinitePi_pi_of_countable
    (μ := fun i => bernoulliMeasure True False (p i))
    (Set.countable_range f) (t := fun _ => {False}) (by measurability)).trans ?_
  rw [← (Equiv.ofInjective f hf).tprod_eq]
  apply tprod_congr
  intro a
  simp

/-- The parametrization by length and left-endpoint offset never repeats an unordered pair. -/
theorem cut_pair_injective (k : ℤ) :
    Function.Injective (fun z : Σ n : ℕ, Fin n =>
      s(k - (z.2.val : ℤ), k + (z.1 : ℤ) - (z.2.val : ℤ))) := by
  rintro ⟨n, i⟩ ⟨m, j⟩ h
  have hi := i.isLt
  have hj := j.isLt
  rcases Sym2.eq_iff.mp h with ⟨h₁, h₂⟩ | ⟨h₁, h₂⟩
  · have hn : n = m := by dsimp at h₁ h₂; omega
    subst m
    have hij : i = j := Fin.ext (by dsimp at h₁; omega)
    subst j
    rfl
  · dsimp at h₁ h₂
    omega

/-- There are exactly `n` crossing pairs of positive length `n`, indexed by `Fin n`. -/
theorem cut_iff_forall_length (ω : Config ℤ) (k : ℤ) :
    (∀ a b, a ≤ k → k < b → s(a, b) ∉ ω) ↔
      ∀ z : Σ n : ℕ, Fin n, s(k - (z.2.val : ℤ), k + (z.1 : ℤ) - (z.2.val : ℤ)) ∉ ω := by
  constructor
  · intro h ⟨n, i⟩
    exact h _ _ (by omega) (by have := i.isLt; dsimp; omega)
  · intro h a b ha hb
    let n := (b - a).toNat
    let i : Fin n := ⟨(k - a).toNat, by dsimp [n]; omega⟩
    have hn : (n : ℤ) = b - a := by dsimp [n]; omega
    have hi : (i.val : ℤ) = k - a := by dsimp [i]; omega
    simpa only [hi, hn, sub_sub_cancel, add_sub_sub_cancel, sub_add_cancel] using h ⟨n, i⟩

/-- The cut probability is the product of the closed probabilities of its crossing pairs. -/
theorem law_cut_eq_tprod_pairs (q : Sym2 ℤ → unitInterval) (k : ℤ) :
    law q {ω | ∀ a b, a ≤ k → k < b → s(a, b) ∉ ω} =
      ∏' z : Σ n : ℕ, Fin n, (unitInterval.toNNReal (unitInterval.symm
        (q s(k - (z.2.val : ℤ), k + (z.1 : ℤ) - (z.2.val : ℤ)))) : ℝ≥0∞) := by
  simp_rw [cut_iff_forall_length]
  exact prodBernoulli_forall_notMem q _ (cut_pair_injective k)

private theorem nnreal_multipliable_of_le_one {α : Type*} (f : α → ℝ≥0)
    (h : ∀ a, f a ≤ 1) : Multipliable f := by
  classical
  exact ⟨_, hasProd_of_isGLB_of_le_one _ h
    (isGLB_csInf (Set.range_nonempty (fun s : Finset α => ∏ a ∈ s, f a)))⟩

/-- For a distance profile the cut probability is independent of its location. -/
theorem law_cut_eq_tprod (p : ℕ → unitInterval) (q : Sym2 ℤ → unitInterval)
    (hq : ∀ a b, q s(a, b) = p (Int.natAbs (b - a))) (k : ℤ) :
    law q {ω | ∀ a b, a ≤ k → k < b → s(a, b) ∉ ω} =
      ∏' n : ℕ, (unitInterval.toNNReal (unitInterval.symm (p n)) : ℝ≥0∞) ^ n := by
  rw [law_cut_eq_tprod_pairs]
  have hdist (z : Σ n : ℕ, Fin n) :
      k + (z.1 : ℤ) - (z.2.val : ℤ) - (k - (z.2.val : ℤ)) = z.1 := by omega
  simp_rw [hq, hdist, Int.natAbs_natCast]
  let f : (Σ n : ℕ, Fin n) → ℝ≥0 := fun z => unitInterval.toNNReal (unitInterval.symm (p z.1))
  have hf : Multipliable f := nnreal_multipliable_of_le_one f (fun z => by
    exact_mod_cast (unitInterval.symm (p z.1)).property.2)
  have hn : Multipliable (fun n : ℕ => unitInterval.toNNReal (unitInterval.symm (p n)) ^ n) :=
    nnreal_multipliable_of_le_one _ (fun n => pow_le_one₀ (by positivity) (by
      exact_mod_cast (unitInterval.symm (p n)).property.2))
  calc
    _ = ((∏' z, f z : ℝ≥0) : ℝ≥0∞) := (hf.map_tprod ENNReal.ofNNRealHom ENNReal.continuous_coe).symm
    _ = ((∏' n : ℕ, unitInterval.toNNReal (unitInterval.symm (p n)) ^ n : ℝ≥0) : ℝ≥0∞) := by
      congr 1
      rw [Multipliable.tprod_sigma' (fun n => (hasProd_fintype _).multipliable) hf]
      simp [f, tprod_fintype]
    _ = _ := (hn.map_tprod ENNReal.ofNNRealHom ENNReal.continuous_coe).trans
      (tprod_congr (fun n => ENNReal.coe_pow _ _))

private theorem closed_product_pos {α : Type*} (p : α → unitInterval)
    (hs : Summable (fun a => (p a : ℝ))) (hlt : ∀ a, p a < 1) :
    0 < ∏' a, (unitInterval.toNNReal (unitInterval.symm (p a)) : ℝ≥0∞) := by
  classical
  have hnonneg (a) : 0 ≤ 1 - (p a : ℝ) := sub_nonneg.mpr (p a).property.2
  have hpos (a) : 0 < 1 - (p a : ℝ) := sub_pos.mpr (by exact_mod_cast hlt a)
  have hlog : Summable (fun a => Real.log (1 - (p a : ℝ))) := by
    simpa only [sub_eq_add_neg] using Real.summable_log_one_add_of_summable hs.neg
  have hp := Real.hasProd_of_hasSum_log hpos hlog.hasSum
  have hp' : HasProd (fun a => ENNReal.ofReal (1 - (p a : ℝ)))
      (ENNReal.ofReal (Real.exp (∑' a, Real.log (1 - (p a : ℝ))))) := by
    unfold HasProd at *
    convert (ENNReal.continuous_ofReal.tendsto _).comp hp using 1
    ext F
    simp [ENNReal.ofReal_prod_of_nonneg (fun a _ => hnonneg a)]
  have heq (a) : (unitInterval.toNNReal (unitInterval.symm (p a)) : ℝ≥0∞) =
      ENNReal.ofReal (1 - (p a : ℝ)) := by
    exact ENNReal.ofReal_coe_nnreal.symm
  simp_rw [heq]
  rw [hp'.tprod_eq]
  exact ENNReal.ofReal_pos.mpr (Real.exp_pos _)

/-- A summable weighted distance profile with no certain positive-length bond has a positive cut probability. -/
theorem law_cut_pos (p : ℕ → unitInterval) (q : Sym2 ℤ → unitInterval)
    (hq : ∀ a b, q s(a, b) = p (Int.natAbs (b - a)))
    (hsum : Summable fun n : ℕ => (n : ℝ) * (p n : ℝ))
    (hlt : ∀ n, 1 ≤ n → p n < 1) (k : ℤ) :
    0 < law q {ω | ∀ a b, a ≤ k → k < b → s(a, b) ∉ ω} := by
  rw [law_cut_eq_tprod_pairs]
  have hdist (z : Σ n : ℕ, Fin n) :
      k + (z.1 : ℤ) - (z.2.val : ℤ) - (k - (z.2.val : ℤ)) = z.1 := by omega
  simp_rw [hq, hdist, Int.natAbs_natCast]
  apply closed_product_pos
  · rw [summable_sigma_of_nonneg (fun z => (p z.1).property.1)]
    constructor
    · intro n; exact (hasSum_fintype _).summable
    · simpa [tsum_fintype] using hsum
  · intro ⟨n, i⟩
    exact hlt n (by have := i.isLt; omega)

private theorem summable_of_closed_product_pos {α : Type*} (p : α → unitInterval)
    (hpos : 0 < ∏' a, (unitInterval.toNNReal (unitInterval.symm (p a)) : ℝ≥0∞)) :
    Summable (fun a => (p a : ℝ)) := by
  classical
  let P := ∏' a, (unitInterval.toNNReal (unitInterval.symm (p a)) : ℝ≥0∞)
  have hle (a) : (unitInterval.toNNReal (unitInterval.symm (p a)) : ℝ≥0∞) ≤ 1 := by
    exact_mod_cast (unitInterval.symm (p a)).property.2
  have hP : P ≤ 1 := tprod_le_one hle
  have hPr : 0 < P.toReal := ENNReal.toReal_pos (ne_of_gt hpos) (ne_top_of_le_ne_top (by simp) hP)
  apply summable_of_sum_le (fun a => (p a).property.1) (c := -Real.log P.toReal)
  intro F
  have hF : P ≤ ∏ a ∈ F, (unitInterval.toNNReal (unitInterval.symm (p a)) : ℝ≥0∞) := by
    dsimp [P]
    rw [ENNReal.tprod_eq_iInf_prod hle]
    exact iInf_le _ F
  have hFr : P.toReal ≤ ∏ a ∈ F, (1 - (p a : ℝ)) := by
    have h := ENNReal.toReal_mono (ENNReal.prod_ne_top (fun _ _ => ENNReal.coe_ne_top)) hF
    simpa only [ENNReal.toReal_prod, ENNReal.coe_toReal, unitInterval.coe_toNNReal,
      unitInterval.coe_symm_eq] using h
  have hexp : (∏ a ∈ F, (1 - (p a : ℝ))) ≤ Real.exp (-∑ a ∈ F, (p a : ℝ)) := by
    rw [← Finset.sum_neg_distrib, Real.exp_sum]
    exact Finset.prod_le_prod₀ (fun a _ => sub_nonneg.mpr (p a).property.2)
      (fun a _ => Real.one_sub_le_exp_neg _)
  have hlog := Real.log_le_log hPr (hFr.trans hexp)
  rw [Real.log_exp] at hlog
  linarith

/-- Divergence of the weighted sum forces every gap-cut probability to vanish. -/
theorem law_cut_eq_zero_of_not_summable (p : ℕ → unitInterval) (q : Sym2 ℤ → unitInterval)
    (hq : ∀ a b, q s(a, b) = p (Int.natAbs (b - a)))
    (hsum : ¬ Summable fun n : ℕ => (n : ℝ) * (p n : ℝ)) (k : ℤ) :
    law q {ω | ∀ a b, a ≤ k → k < b → s(a, b) ∉ ω} = 0 := by
  rw [law_cut_eq_tprod_pairs]
  have hdist (z : Σ n : ℕ, Fin n) :
      k + (z.1 : ℤ) - (z.2.val : ℤ) - (k - (z.2.val : ℤ)) = z.1 := by omega
  simp_rw [hq, hdist, Int.natAbs_natCast]
  by_contra h
  have hs := summable_of_closed_product_pos (fun z : Σ n : ℕ, Fin n => p z.1) (lt_of_le_of_ne bot_le (Ne.symm h))
  rw [summable_sigma_of_nonneg (fun z => (p z.1).property.1)] at hs
  exact hsum (by simpa [tsum_fintype] using hs.2)

/-- A certain bond of positive length rules out a cut. The diagonal case is excluded. -/
theorem law_cut_eq_zero_of_certain_length (p : ℕ → unitInterval) (q : Sym2 ℤ → unitInterval)
    (hq : ∀ a b, q s(a, b) = p (Int.natAbs (b - a)))
    {n : ℕ} (hn : 0 < n) (hp : p n = 1) (k : ℤ) :
    law q {ω | ∀ a b, a ≤ k → k < b → s(a, b) ∉ ω} = 0 := by
  rw [law_cut_eq_tprod p q hq]
  apply tprod_of_exists_eq_zero
  exact ⟨n, by simp [hp, ne_of_gt hn]⟩

-- At zero profile every gap is a cut, including the endpoint p(0) = 0.
example (k : ℤ) :
    law (fun _ : Sym2 ℤ => 0) {ω | ∀ a b, a ≤ k → k < b → s(a, b) ∉ ω} = 1 := by
  rw [law_cut_eq_tprod (fun _ => 0) _ (by simp)]
  simp

-- A certain nearest-neighbour bond forces cut probability zero.
example (p : ℕ → unitInterval) (q : Sym2 ℤ → unitInterval)
    (hq : ∀ a b, q s(a, b) = p (Int.natAbs (b - a))) (h : p 1 = 1) (k : ℤ) :
    law q {ω | ∀ a b, a ≤ k → k < b → s(a, b) ∉ ω} = 0 :=
  law_cut_eq_zero_of_certain_length p q hq (by decide : 0 < 1) h k

-- A genuine infinite-range profile: p(n) = 2⁻ⁿ, with an always-open diagonal.
example (k : ℤ) :
    ∃ q : Sym2 ℤ → unitInterval,
      (∀ a b, (q s(a, b) : ℝ) = (1 / 2 : ℝ) ^ (b - a).natAbs) ∧
      0 < law q {ω | ∀ a b, a ≤ k → k < b → s(a, b) ∉ ω} := by
  let p : ℕ → unitInterval := fun n =>
    ⟨(1 / 2 : ℝ) ^ n, pow_nonneg (by norm_num) _, pow_le_one₀ (by norm_num) (by norm_num)⟩
  let q : Sym2 ℤ → unitInterval := Sym2.lift ⟨fun a b => p (b - a).natAbs,
    fun a b => by dsimp; rw [← Int.natAbs_neg (b - a), neg_sub]⟩
  have hq (a b : ℤ) : q s(a, b) = p (b - a).natAbs := rfl
  refine ⟨q, fun a b => rfl, law_cut_pos p q hq ?_ ?_ k⟩
  · simpa only [p, pow_one] using
      summable_pow_mul_geometric_of_norm_lt_one 1 (by norm_num : ‖(1 / 2 : ℝ)‖ < 1)
  · intro n hn
    change (1 / 2 : ℝ) ^ n < 1
    exact pow_lt_one₀ (by norm_num) (by norm_num) (by omega)

-- Empty configurations exhibit two bounding cuts without any probabilistic assumption.
example : (cluster (∅ : Config ℤ) 0).Finite :=
  finite_cluster_of_cuts ∅ (by norm_num : (-1 : ℤ) < 0) (by norm_num : (0 : ℤ) ≤ 0)
    (by simp) (by simp)

end PercLib.Models.LongRange
