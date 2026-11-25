/-
Copyright (c) 2026 PercLib contributors. Released under Apache 2.0.
New proofs, written for package Q-67 (issue 374, roadmap T-6), on the D-2 interface.
Source motivation: T. Hutchcroft, arXiv:2008.11197v2, §2.1, the moment bounds that follow
Theorem 2.2. No source text or code is copied.
-/
module

public import PercLib.Percolation.Bond.Tightness.FiniteQuantile
public import PercLib.Percolation.Bond.ClusterTails
public import Mathlib.Analysis.SpecificLimits.Basic
public import Mathlib.Analysis.Complex.Exponential

/-! # Moments of the largest cluster intersection at the quantile scale

With `Z = maxClusterIntersection Λ`, `M = tightnessScale q Λ`, `Λ` finite nonempty and
`V` countable:

* `lintegral_maxClusterIntersection_ge` (unconditional):
  `(M - 1) e⁻¹ ≤ E Z` and `M / (2e) ≤ E Z`.
* `lintegral_maxClusterIntersection_pow_le` (assuming `UniversalTightness V`): for every
  `k`, `E Z^k ≤ C_k M^k` with the explicit constant `C_k = 20 · 18^k · k!`.

The second bound is proved for every `k : ℕ`, which includes the requested `k ≥ 1`.
Expectations are lower Lebesgue integrals in `ℝ≥0∞` (D-2).
-/

@[expose] public section
noncomputable section

open MeasureTheory Set
open scoped ENNReal Nat

namespace PercLib.Percolation.Bond

variable {V : Type*}

private theorem one_le_max {Λ : Finset V} (hΛ : Λ.Nonempty) (ω : Config V) :
    1 ≤ maxClusterIntersection Λ ω := by
  obtain ⟨v, hv⟩ := hΛ
  have h1 : 1 ≤ (cluster ω v ∩ (Λ : Set V)).ncard := by
    rw [Nat.one_le_iff_ne_zero, Ne, Set.ncard_eq_zero (Λ.finite_toSet.subset
      Set.inter_subset_right)]
    exact Set.nonempty_iff_ne_empty.1 ⟨v, mem_cluster_self ω v, hv⟩
  exact h1.trans (Finset.le_sup (f := fun v => (cluster ω v ∩ (Λ : Set V)).ncard) hv)

private theorem two_le_scale (q : Sym2 V → unitInterval) {Λ : Finset V}
    (hΛ : Λ.Nonempty) : 2 ≤ tightnessScale q Λ := by
  by_contra h
  have ht := law_max_tail_le_of_tightnessScale_le q Λ (show tightnessScale q Λ ≤ 1 by omega)
  have huniv : {ω : Config V | 1 ≤ maxClusterIntersection Λ ω} = Set.univ :=
    Set.eq_univ_of_forall fun ω => one_le_max hΛ ω
  rw [huniv, measure_univ] at ht
  exact absurd ht (not_le.2 (ENNReal.ofReal_lt_one.2 (by simp)))

private theorem measurableSet_le_max [Countable V] (Λ : Finset V) (k : ℕ) :
    MeasurableSet {ω : Config V | k ≤ maxClusterIntersection Λ ω} := by
  classical
  rcases Nat.eq_zero_or_pos k with rfl | hk
  · simp
  have h : {ω : Config V | k ≤ maxClusterIntersection Λ ω} =
      ⋃ v ∈ Λ, {ω : Config V | k ≤ (cluster ω v ∩ (Λ : Set V)).ncard} := by
    ext ω
    simp only [Set.mem_ofPred_eq, Set.mem_iUnion, exists_prop, maxClusterIntersection]
    exact Finset.le_sup_iff (by simpa [Nat.bot_eq_zero] using hk)
  rw [h]
  exact Finset.measurableSet_biUnion _ fun v _ => measurableSet_cluster_tail v Λ k

private theorem measurable_max [Countable V] (Λ : Finset V) :
    Measurable (fun ω : Config V => maxClusterIntersection Λ ω) := by
  refine measurable_to_countable' fun n => ?_
  have h : (fun ω : Config V => maxClusterIntersection Λ ω) ⁻¹' {n} =
      {ω | n ≤ maxClusterIntersection Λ ω} \ {ω | n + 1 ≤ maxClusterIntersection Λ ω} := by
    ext ω
    simp only [Set.mem_preimage, Set.mem_singleton_iff, Set.mem_sdiff, Set.mem_ofPred_eq]
    omega
  rw [h]
  exact (measurableSet_le_max Λ n).diff (measurableSet_le_max Λ (n + 1))

/-! ### The first moment from below (unconditional) -/

/-- **First moment from below** (wiki tag AWWZ): `(M - 1) e⁻¹ ≤ E Z`, for every profile on
a countable vertex type and every finite nonempty `Λ`. -/
theorem lintegral_maxClusterIntersection_ge_sub_one [Countable V]
    (q : Sym2 V → unitInterval) {Λ : Finset V} (hΛ : Λ.Nonempty) :
    ENNReal.ofReal (((tightnessScale q Λ : ℝ) - 1) * Real.exp (-1)) ≤
      ∫⁻ ω, (maxClusterIntersection Λ ω : ℝ≥0∞) ∂(law q) := by
  set M := tightnessScale q Λ with hM
  have hM2 := two_le_scale q hΛ
  have hmeas : Measurable (fun ω : Config V => (maxClusterIntersection Λ ω : ℝ≥0∞)) :=
    measurable_from_nat.comp (measurable_max Λ)
  have hmarkov := mul_meas_ge_le_lintegral₀ (μ := law q) hmeas.aemeasurable
    ((M - 1 : ℕ) : ℝ≥0∞)
  have hev : {ω : Config V | ((M - 1 : ℕ) : ℝ≥0∞) ≤ (maxClusterIntersection Λ ω : ℝ≥0∞)} =
      {ω | M - 1 ≤ maxClusterIntersection Λ ω} := by
    ext ω; simp only [Set.mem_ofPred_eq, Nat.cast_le]
  rw [hev] at hmarkov
  have hstrict := lt_law_max_tail_of_lt_tightnessScale q Λ (show M - 1 < M by omega)
  refine le_trans ?_ hmarkov
  have hcast : ((M : ℝ) - 1) = ((M - 1 : ℕ) : ℝ) := by
    rw [Nat.cast_sub (by omega)]; simp
  rw [hcast, ENNReal.ofReal_mul (Nat.cast_nonneg _), ENNReal.ofReal_natCast]
  gcongr

/-- **First moment from below** (wiki tag AWWZ): `M / (2e) ≤ E Z`. -/
theorem lintegral_maxClusterIntersection_ge [Countable V]
    (q : Sym2 V → unitInterval) {Λ : Finset V} (hΛ : Λ.Nonempty) :
    ENNReal.ofReal ((tightnessScale q Λ : ℝ) / (2 * Real.exp 1)) ≤
      ∫⁻ ω, (maxClusterIntersection Λ ω : ℝ≥0∞) ∂(law q) := by
  refine le_trans (ENNReal.ofReal_le_ofReal ?_) (lintegral_maxClusterIntersection_ge_sub_one q hΛ)
  have hM2 : (2 : ℝ) ≤ tightnessScale q Λ := by exact_mod_cast two_le_scale q hΛ
  have he : 0 < Real.exp 1 := Real.exp_pos 1
  rw [Real.exp_neg, div_le_iff₀ (by positivity)]
  have : ((tightnessScale q Λ : ℝ) - 1) * (Real.exp 1)⁻¹ * (2 * Real.exp 1) =
      2 * ((tightnessScale q Λ : ℝ) - 1) := by
    field_simp
  rw [this]
  linarith

/-! ### Higher moments from above (assuming universal tightness) -/

/-- `(j + 2)^k e^{-(j+1)/9} ≤ k! 18^k (e^{-1/18})^j`. -/
private theorem term_le (k j : ℕ) :
    ((j : ℝ) + 2) ^ k * Real.exp (-((j : ℝ) + 1) / 9) ≤
      (k ! : ℝ) * 18 ^ k * Real.exp (-1 / 18) ^ j := by
  have hx : (0 : ℝ) ≤ ((j : ℝ) + 2) / 18 := by positivity
  have h1 := Real.pow_div_factorial_le_exp _ hx k
  have hfac : (0 : ℝ) < k ! := by exact_mod_cast Nat.factorial_pos k
  rw [div_le_iff₀ hfac] at h1
  have h2 : ((j : ℝ) + 2) ^ k = 18 ^ k * (((j : ℝ) + 2) / 18) ^ k := by
    rw [div_pow, mul_div_cancel₀ _ (by positivity)]
  have h3 : Real.exp (((j : ℝ) + 2) / 18) * Real.exp (-((j : ℝ) + 1) / 9) =
      Real.exp (-1 / 18) ^ j := by
    rw [← Real.exp_add, ← Real.exp_nat_mul]; ring_nf
  calc ((j : ℝ) + 2) ^ k * Real.exp (-((j : ℝ) + 1) / 9)
      = 18 ^ k * (((j : ℝ) + 2) / 18) ^ k * Real.exp (-((j : ℝ) + 1) / 9) := by rw [h2]
    _ ≤ 18 ^ k * (Real.exp (((j : ℝ) + 2) / 18) * k !) *
          Real.exp (-((j : ℝ) + 1) / 9) := by gcongr
    _ = (k ! : ℝ) * 18 ^ k * (Real.exp (((j : ℝ) + 2) / 18) *
          Real.exp (-((j : ℝ) + 1) / 9)) := by ring
    _ = (k ! : ℝ) * 18 ^ k * Real.exp (-1 / 18) ^ j := by rw [h3]

/-- `∑ (e^{-1/18})^j ≤ 19`. -/
private theorem tsum_geometric_le :
    ∑' j : ℕ, ENNReal.ofReal (Real.exp (-1 / 18)) ^ j ≤ 19 := by
  rw [ENNReal.tsum_geometric, ENNReal.inv_le_iff_inv_le]
  have he : Real.exp (-1 / 18) ≤ 18 / 19 := by
    have h := Real.add_one_le_exp (1 / 18 : ℝ)
    have hpos := Real.exp_pos (1 / 18 : ℝ)
    rw [show (-1 / 18 : ℝ) = -(1 / 18) by ring, Real.exp_neg, inv_le_iff_one_le_mul₀ hpos]
    linarith
  rw [← ENNReal.ofReal_one, ← ENNReal.ofReal_sub _ (Real.exp_pos _).le]
  have : (19 : ℝ≥0∞)⁻¹ = ENNReal.ofReal (1 / 19) := by
    rw [one_div, ENNReal.ofReal_inv_of_pos (by norm_num)]; simp
  rw [this]
  exact ENNReal.ofReal_le_ofReal (by linarith)

/-- **Higher moments** (wiki tag 2FN1): assuming universal tightness on `V`, for every
profile, every finite nonempty `Λ` and every `k`,
`E Z^k ≤ C_k M^k` with `C_k = 20 · 18^k · k!`, independent of `V`, `q` and `Λ`. -/
theorem lintegral_maxClusterIntersection_pow_le [Countable V] (hUT : UniversalTightness V)
    (q : Sym2 V → unitInterval) {Λ : Finset V} (hΛ : Λ.Nonempty) (k : ℕ) :
    ∫⁻ ω, (maxClusterIntersection Λ ω : ℝ≥0∞) ^ k ∂(law q) ≤
      (20 * 18 ^ k * k ! : ℝ≥0∞) * (tightnessScale q Λ : ℝ≥0∞) ^ k := by
  set M := tightnessScale q Λ with hM
  have hM2 := two_le_scale q hΛ
  have hupper := (hUT q Λ hΛ).1
  -- the layers `S j = {(j + 1) M ≤ Z}`
  have hS : ∀ j : ℕ, MeasurableSet {ω : Config V | (j + 1) * M ≤ maxClusterIntersection Λ ω} :=
    fun j => measurableSet_le_max Λ _
  -- pointwise layer-cake bound
  have hpt : ∀ ω : Config V, (maxClusterIntersection Λ ω : ℝ≥0∞) ^ k ≤
      (M : ℝ≥0∞) ^ k + ∑' j : ℕ,
        {ω : Config V | (j + 1) * M ≤ maxClusterIntersection Λ ω}.indicator
          (fun _ => (((j + 2) * M : ℕ) : ℝ≥0∞) ^ k) ω := by
    intro ω
    set z := maxClusterIntersection Λ ω with hz
    by_cases hzM : z < M
    · refine le_trans ?_ le_self_add
      gcongr
    · push Not at hzM
      refine le_trans ?_ le_add_self
      have hMpos : 0 < M := by omega
      set j := z / M - 1 with hj
      have hq : 1 ≤ z / M := (Nat.le_div_iff_mul_le hMpos).2 (by omega)
      have hlow : (j + 1) * M ≤ z := by
        rw [hj, Nat.sub_add_cancel hq]; exact Nat.div_mul_le_self z M
      have hhigh : z ≤ (j + 2) * M := by
        have := Nat.div_add_mod z M
        have := Nat.mod_lt z hMpos
        rw [hj, show z / M - 1 + 2 = z / M + 1 by omega, add_mul, one_mul]
        nlinarith [Nat.mul_comm M (z / M)]
      refine le_trans ?_ (ENNReal.le_tsum j)
      rw [Set.indicator_of_mem (show ω ∈ {ω : Config V |
        (j + 1) * M ≤ maxClusterIntersection Λ ω} from hlow)]
      gcongr
  -- each layer has probability at most `exp (-(j + 1) / 9)`
  have hlayer : ∀ j : ℕ, law q {ω : Config V | (j + 1) * M ≤ maxClusterIntersection Λ ω} ≤
      ENNReal.ofReal (Real.exp (-((j : ℝ) + 1) / 9)) := by
    intro j
    have h := hupper ((j : ℝ) + 1) (by linarith [(Nat.cast_nonneg j : (0 : ℝ) ≤ j)])
    have hev : {ω : Config V | ((j : ℝ) + 1) * (M : ℝ) ≤ (maxClusterIntersection Λ ω : ℝ)} =
        {ω | (j + 1) * M ≤ maxClusterIntersection Λ ω} := by
      ext ω
      simp only [Set.mem_ofPred_eq]
      exact_mod_cast Iff.rfl
    rw [hev] at h
    exact h
  calc ∫⁻ ω, (maxClusterIntersection Λ ω : ℝ≥0∞) ^ k ∂(law q)
      ≤ ∫⁻ ω, ((M : ℝ≥0∞) ^ k + ∑' j : ℕ,
          {ω : Config V | (j + 1) * M ≤ maxClusterIntersection Λ ω}.indicator
            (fun _ => (((j + 2) * M : ℕ) : ℝ≥0∞) ^ k) ω) ∂(law q) := lintegral_mono hpt
    _ = (M : ℝ≥0∞) ^ k + ∑' j : ℕ, (((j + 2) * M : ℕ) : ℝ≥0∞) ^ k *
          law q {ω : Config V | (j + 1) * M ≤ maxClusterIntersection Λ ω} := by
        rw [lintegral_add_left measurable_const, lintegral_const, measure_univ, mul_one,
          lintegral_tsum fun j => (measurable_const.indicator (hS j)).aemeasurable]
        simp_rw [lintegral_indicator_const (hS _)]
    _ ≤ (M : ℝ≥0∞) ^ k + ∑' j : ℕ, (M : ℝ≥0∞) ^ k * ((k ! * 18 ^ k : ℝ≥0∞) *
          ENNReal.ofReal (Real.exp (-1 / 18)) ^ j) := by
        refine add_le_add_right (ENNReal.tsum_le_tsum fun j => ?_) _
        calc (((j + 2) * M : ℕ) : ℝ≥0∞) ^ k *
              law q {ω : Config V | (j + 1) * M ≤ maxClusterIntersection Λ ω}
            ≤ (((j + 2) * M : ℕ) : ℝ≥0∞) ^ k *
                ENNReal.ofReal (Real.exp (-((j : ℝ) + 1) / 9)) := by gcongr; exact hlayer j
          _ = (M : ℝ≥0∞) ^ k * ENNReal.ofReal (((j : ℝ) + 2) ^ k *
                Real.exp (-((j : ℝ) + 1) / 9)) := by
              rw [ENNReal.ofReal_mul (by positivity), Nat.cast_mul, mul_pow,
                ENNReal.ofReal_pow (by positivity)]
              rw [show ((j : ℝ) + 2) = ((j + 2 : ℕ) : ℝ) by push_cast; ring,
                ENNReal.ofReal_natCast]
              ring
          _ ≤ (M : ℝ≥0∞) ^ k * ENNReal.ofReal ((k ! : ℝ) * 18 ^ k *
                Real.exp (-1 / 18) ^ j) := by
                exact mul_le_mul_right (ENNReal.ofReal_le_ofReal (term_le k j)) _
          _ = (M : ℝ≥0∞) ^ k * ((k ! * 18 ^ k : ℝ≥0∞) *
                ENNReal.ofReal (Real.exp (-1 / 18)) ^ j) := by
              rw [ENNReal.ofReal_mul (by positivity), ENNReal.ofReal_pow (Real.exp_pos _).le,
                ENNReal.ofReal_mul (by positivity), ENNReal.ofReal_pow (by norm_num),
                ENNReal.ofReal_natCast]
              norm_num
    _ = (M : ℝ≥0∞) ^ k + (M : ℝ≥0∞) ^ k * (k ! * 18 ^ k : ℝ≥0∞) *
          ∑' j : ℕ, ENNReal.ofReal (Real.exp (-1 / 18)) ^ j := by
        rw [ENNReal.tsum_mul_left, ENNReal.tsum_mul_left]; ring
    _ ≤ (M : ℝ≥0∞) ^ k + (M : ℝ≥0∞) ^ k * (k ! * 18 ^ k : ℝ≥0∞) * 19 := by
        gcongr; exact tsum_geometric_le
    _ ≤ (20 * 18 ^ k * k ! : ℝ≥0∞) * (M : ℝ≥0∞) ^ k := by
        have h1 : (1 : ℝ≥0∞) ≤ k ! * 18 ^ k := by
          have : 1 ≤ k ! * 18 ^ k := Nat.one_le_iff_ne_zero.2 (by positivity)
          exact_mod_cast this
        calc (M : ℝ≥0∞) ^ k + (M : ℝ≥0∞) ^ k * (k ! * 18 ^ k : ℝ≥0∞) * 19
            = (M : ℝ≥0∞) ^ k * 1 + (M : ℝ≥0∞) ^ k * (k ! * 18 ^ k : ℝ≥0∞) * 19 := by
              rw [mul_one]
          _ ≤ (M : ℝ≥0∞) ^ k * (k ! * 18 ^ k : ℝ≥0∞) +
                (M : ℝ≥0∞) ^ k * (k ! * 18 ^ k : ℝ≥0∞) * 19 := by gcongr
          _ = (20 * 18 ^ k * k ! : ℝ≥0∞) * (M : ℝ≥0∞) ^ k := by ring

/-! ### Non-vacuity (D-5) -/

/-- Item 1 at a singleton: `M = 2` and `Z = 1`. -/
example (q : Sym2 Unit → unitInterval) :
    ENNReal.ofReal (((tightnessScale q {()} : ℝ) - 1) * Real.exp (-1)) ≤
      ∫⁻ ω, (maxClusterIntersection {()} ω : ℝ≥0∞) ∂(law q) :=
  lintegral_maxClusterIntersection_ge_sub_one q (Finset.singleton_nonempty _)

example (q : Sym2 Unit → unitInterval) :
    ∫⁻ ω, (maxClusterIntersection {()} ω : ℝ≥0∞) ∂(law q) = 1 ∧ tightnessScale q {()} = 2 := by
  refine ⟨?_, tightnessScale_singleton q ()⟩
  simp [maxClusterIntersection_singleton]

private theorem clusterIntersection_unit_le (Λ : Finset Unit) (ω : Config Unit) (u : Unit) :
    clusterIntersection Λ ω u ≤ 1 := by
  unfold clusterIntersection
  calc (cluster ω u ∩ (Λ : Set Unit)).ncard ≤ (Set.univ : Set Unit).ncard :=
        Set.ncard_le_ncard (Set.subset_univ _) Set.finite_univ
    _ = 1 := by simp

private theorem max_unit_le (Λ : Finset Unit) (ω : Config Unit) :
    maxClusterIntersection Λ ω ≤ 1 :=
  Finset.sup_le fun v _ => clusterIntersection_unit_le Λ ω v

/-- Universal tightness holds on one vertex, so item 2 has a model. -/
private theorem universalTightness_one_vertex : UniversalTightness Unit := by
  intro q Λ hΛ
  have hΛ' : Λ = {()} := by
    obtain ⟨u, hu⟩ := hΛ
    ext v; simp [show v = u from rfl, hu]
  subst hΛ'
  have hM : (tightnessScale q {()} : ℝ) = 2 := by
    exact_mod_cast tightnessScale_singleton q ()
  refine ⟨fun a ha => ?_, fun ε hε _ => ?_, fun u a ha => ?_⟩
  · have : {ω : Config Unit | a * (tightnessScale q {()} : ℝ) ≤
        (maxClusterIntersection {()} ω : ℝ)} = ∅ := by
      apply Set.eq_empty_of_forall_notMem
      intro ω (hω : a * (tightnessScale q {()} : ℝ) ≤ _)
      have : (maxClusterIntersection {()} ω : ℝ) ≤ 1 := by exact_mod_cast max_unit_le _ ω
      rw [hM] at hω; linarith
    rw [this, measure_empty]; exact zero_le
  · by_cases hε2 : ε * 2 ≤ 1
    · have : {ω : Config Unit | (maxClusterIntersection {()} ω : ℝ) <
          ε * (tightnessScale q {()} : ℝ)} = ∅ := by
        apply Set.eq_empty_of_forall_notMem
        intro ω (hω : (maxClusterIntersection {()} ω : ℝ) < _)
        rw [maxClusterIntersection_singleton, hM] at hω
        norm_num at hω; linarith
      rw [this, measure_empty]; exact zero_le
    · refine prob_le_one.trans ?_
      rw [← ENNReal.ofReal_one]
      exact ENNReal.ofReal_le_ofReal (by linarith)
  · have : {ω : Config Unit | a * (tightnessScale q {()} : ℝ) ≤
        (clusterIntersection {()} ω u : ℝ)} = ∅ := by
      apply Set.eq_empty_of_forall_notMem
      intro ω (hω : a * (tightnessScale q {()} : ℝ) ≤ _)
      have : (clusterIntersection {()} ω u : ℝ) ≤ 1 := by
        exact_mod_cast clusterIntersection_unit_le _ ω u
      rw [hM] at hω; linarith
    rw [this, measure_empty]; exact zero_le

/-- Item 2 on one vertex. -/
example (q : Sym2 Unit → unitInterval) (k : ℕ) :
    ∫⁻ ω, (maxClusterIntersection {()} ω : ℝ≥0∞) ^ k ∂(law q) ≤
      (20 * 18 ^ k * k ! : ℝ≥0∞) * (tightnessScale q {()} : ℝ≥0∞) ^ k :=
  lintegral_maxClusterIntersection_pow_le universalTightness_one_vertex q
    (Finset.singleton_nonempty _) k

end PercLib.Percolation.Bond
