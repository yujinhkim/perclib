/-
Copyright (c) 2026 PercLib contributors. Released under Apache 2.0.
New proofs, written for package Q-65 (issue 372, roadmap T-6), on the D-2 interface.
Source motivation: T. Hutchcroft, arXiv:2008.11197v2, §2.1, deduction of Theorem 2.2
from Theorem 2.3. No source text or code is copied.
-/
module

public import PercLib.Percolation.Bond.Tightness.FiniteQuantile
public import PercLib.Percolation.Bond.ClusterTails

/-! # Universal tightness from the BK step

`TightnessBK V → UniversalTightness V` for every countable `V`. With `M` the quantile
scale, the BK step at `λ = M` gives the upper and rooted tails, and the BK step at
`λ = ε M` together with `P(max ≥ M - 1) > e⁻¹` gives the lower tail. The definitions
in `Tightness/Defs.lean` are used unchanged (reading `k ≥ 1` of issue 52).
-/

@[expose] public section
noncomputable section

open MeasureTheory Set
open scoped ENNReal

namespace PercLib.Percolation.Bond

variable {V : Type*}

/-- For nonempty `Λ` the largest intersection is at least one. -/
theorem one_le_maxClusterIntersection {Λ : Finset V} (hΛ : Λ.Nonempty) (ω : Config V) :
    1 ≤ maxClusterIntersection Λ ω := by
  obtain ⟨v, hv⟩ := hΛ
  have h1 : 1 ≤ (cluster ω v ∩ (Λ : Set V)).ncard := by
    rw [Nat.one_le_iff_ne_zero, Ne, Set.ncard_eq_zero (Λ.finite_toSet.subset
      Set.inter_subset_right)]
    exact Set.nonempty_iff_ne_empty.1 ⟨v, mem_cluster_self ω v, hv⟩
  exact h1.trans (Finset.le_sup (f := fun v => (cluster ω v ∩ (Λ : Set V)).ncard) hv)

/-- For nonempty `Λ` the quantile scale is at least two. -/
theorem two_le_tightnessScale (q : Sym2 V → unitInterval) {Λ : Finset V}
    (hΛ : Λ.Nonempty) : 2 ≤ tightnessScale q Λ := by
  by_contra h
  have hle : tightnessScale q Λ ≤ 1 := by omega
  have ht := law_max_tail_le_of_tightnessScale_le q Λ hle
  have huniv : {ω : Config V | 1 ≤ maxClusterIntersection Λ ω} = Set.univ :=
    Set.eq_univ_of_forall fun ω => one_le_maxClusterIntersection hΛ ω
  rw [huniv, measure_univ] at ht
  exact absurd ht (not_le.2 (ENNReal.ofReal_lt_one.2 (by simp)))

/-- The largest intersection is measurable on a countable vertex type. -/
theorem measurableSet_le_maxClusterIntersection [Countable V] (Λ : Finset V) (k : ℕ) :
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

/-- Real-threshold tails of the largest intersection are measurable. -/
theorem measurableSet_real_le_maxClusterIntersection [Countable V] (Λ : Finset V) (l : ℝ) :
    MeasurableSet {ω : Config V | l ≤ (maxClusterIntersection Λ ω : ℝ)} := by
  have h : {ω : Config V | l ≤ (maxClusterIntersection Λ ω : ℝ)} =
      {ω : Config V | ⌈l⌉₊ ≤ maxClusterIntersection Λ ω} := by
    ext ω
    simp only [Set.mem_ofPred_eq]
    exact Nat.ceil_le.symm
  rw [h]
  exact measurableSet_le_maxClusterIntersection Λ _

/-- `p ^ n ≤ exp (-(n (1 - p)))` for `0 ≤ p`. -/
private theorem pow_le_exp_neg {p : ℝ} (hp : 0 ≤ p) (n : ℕ) :
    p ^ n ≤ Real.exp (-((n : ℝ) * (1 - p))) := by
  have h1 : p ≤ Real.exp (-(1 - p)) := by
    have := Real.add_one_le_exp (-(1 - p))
    linarith
  calc p ^ n ≤ Real.exp (-(1 - p)) ^ n := pow_le_pow_left₀ hp h1 n
    _ = Real.exp (-((n : ℝ) * (1 - p))) := by
      rw [← Real.exp_nat_mul]; ring_nf

/-- The smallest `k` with `a < 3 ^ (k + 1)` brackets `a` between powers of three. -/
private theorem exists_pow_three_bracket (a : ℝ) :
    ∃ k : ℕ, a < (3 : ℝ) ^ (k + 1) ∧ (k = 0 ∨ (1 ≤ k ∧ (3 : ℝ) ^ k ≤ a)) := by
  classical
  have hex : ∃ k : ℕ, a < (3 : ℝ) ^ (k + 1) := by
    obtain ⟨n, hn⟩ := pow_unbounded_of_one_lt a (by norm_num : (1 : ℝ) < 3)
    exact ⟨n, hn.trans_le (pow_le_pow_right₀ (by norm_num) (Nat.le_succ n))⟩
  refine ⟨Nat.find hex, Nat.find_spec hex, ?_⟩
  rcases Nat.eq_zero_or_pos (Nat.find hex) with h | h
  · exact Or.inl h
  · right
    refine ⟨h, ?_⟩
    have hmin := Nat.find_min hex (show Nat.find hex - 1 < Nat.find hex by omega)
    rw [Nat.sub_add_cancel h] at hmin
    exact not_lt.1 hmin

/-- The upper tail. -/
private theorem upper_tail_of_bk [Countable V] (hBK : TightnessBK V)
    (q : Sym2 V → unitInterval) {Λ : Finset V} (hΛ : Λ.Nonempty) {a : ℝ} (ha : 1 ≤ a) :
    law q {ω | a * (tightnessScale q Λ : ℝ) ≤ (maxClusterIntersection Λ ω : ℝ)} ≤
      ENNReal.ofReal (Real.exp (-a / 9)) := by
  set M := tightnessScale q Λ with hM
  have hM2 : (2 : ℝ) ≤ M := by exact_mod_cast two_le_tightnessScale q hΛ
  have hMnn : (0 : ℝ) ≤ M := by linarith
  have hMev : {ω : Config V | (M : ℝ) ≤ (maxClusterIntersection Λ ω : ℝ)} =
      {ω | M ≤ maxClusterIntersection Λ ω} := by
    ext ω; simp only [Set.mem_ofPred_eq, Nat.cast_le]
  have hMtail : law q {ω : Config V | (M : ℝ) ≤ (maxClusterIntersection Λ ω : ℝ)} ≤
      ENNReal.ofReal (Real.exp (-1)) := by
    rw [hMev]; exact law_max_tail_at_tightnessScale q Λ
  obtain ⟨k, hk1, hk2⟩ := exists_pow_three_bracket a
  rcases hk2 with rfl | hk2
  · have ha3 : a < 3 := by simpa using hk1
    have hsub : {ω : Config V | a * (M : ℝ) ≤ (maxClusterIntersection Λ ω : ℝ)} ⊆
        {ω | (M : ℝ) ≤ (maxClusterIntersection Λ ω : ℝ)} := by
      intro ω (hω : a * (M : ℝ) ≤ _)
      show (M : ℝ) ≤ _
      nlinarith
    have hexp : Real.exp (-1) ≤ Real.exp (-a / 9) := Real.exp_le_exp.2 (by linarith)
    exact (measure_mono hsub).trans (hMtail.trans (ENNReal.ofReal_le_ofReal hexp))
  · obtain ⟨hk, hk2⟩ := hk2
    have hbk := (hBK q Λ hΛ (M : ℝ) (by linarith) k hk).1
    have hsub : {ω : Config V | a * (M : ℝ) ≤ (maxClusterIntersection Λ ω : ℝ)} ⊆
        {ω | (3 : ℝ) ^ k * (M : ℝ) ≤ (maxClusterIntersection Λ ω : ℝ)} :=
      fun ω (hω : a * (M : ℝ) ≤ _) =>
        (mul_le_mul_of_nonneg_right hk2 hMnn).trans hω
    refine (measure_mono hsub).trans (hbk.trans ?_)
    refine (pow_le_pow_left₀ zero_le hMtail _).trans ?_
    rw [← ENNReal.ofReal_pow (Real.exp_pos _).le, ← Real.exp_nat_mul]
    apply ENNReal.ofReal_le_ofReal
    apply Real.exp_le_exp.2
    have h3 : (3 : ℝ) ^ (k + 1) = 9 * (3 : ℝ) ^ (k - 1) := by
      rw [show k + 1 = (k - 1) + 2 by omega, pow_add]; ring
    push_cast
    rw [h3] at hk1
    linarith

/-- The rooted tail. -/
private theorem rooted_tail_of_bk [Countable V] (hBK : TightnessBK V)
    (q : Sym2 V → unitInterval) {Λ : Finset V} (hΛ : Λ.Nonempty) (u : V) {a : ℝ}
    (ha : 1 ≤ a) :
    law q {ω | a * (tightnessScale q Λ : ℝ) ≤ (clusterIntersection Λ ω u : ℝ)} ≤
      ENNReal.ofReal (Real.exp 1) *
        law q {ω | tightnessScale q Λ ≤ clusterIntersection Λ ω u} *
        ENNReal.ofReal (Real.exp (-a / 9)) := by
  set M := tightnessScale q Λ with hM
  set L := law q {ω | M ≤ clusterIntersection Λ ω u} with hL
  have hM2 : (2 : ℝ) ≤ M := by exact_mod_cast two_le_tightnessScale q hΛ
  have hMnn : (0 : ℝ) ≤ M := by linarith
  have hMtail : law q {ω : Config V | (M : ℝ) ≤ (maxClusterIntersection Λ ω : ℝ)} ≤
      ENNReal.ofReal (Real.exp (-1)) := by
    have : {ω : Config V | (M : ℝ) ≤ (maxClusterIntersection Λ ω : ℝ)} =
        {ω | M ≤ maxClusterIntersection Λ ω} := by
      ext ω; simp only [Set.mem_ofPred_eq, Nat.cast_le]
    rw [this]; exact law_max_tail_at_tightnessScale q Λ
  have hLev : {ω : Config V | (M : ℝ) ≤ (clusterIntersection Λ ω u : ℝ)} =
      {ω | M ≤ clusterIntersection Λ ω u} := by
    ext ω; simp only [Set.mem_ofPred_eq, Nat.cast_le]
  -- the right side is `ofReal (exp (1 - a/9)) * L`
  have hrhs : ENNReal.ofReal (Real.exp 1) * L * ENNReal.ofReal (Real.exp (-a / 9)) =
      ENNReal.ofReal (Real.exp (1 - a / 9)) * L := by
    rw [mul_comm _ L, mul_assoc, ← ENNReal.ofReal_mul (Real.exp_pos _).le,
      ← Real.exp_add, mul_comm]
    ring_nf
  rw [hrhs]
  obtain ⟨k, hk1, hk2⟩ := exists_pow_three_bracket a
  rcases hk2 with rfl | hk2
  · have hsub : {ω : Config V | a * (M : ℝ) ≤ (clusterIntersection Λ ω u : ℝ)} ⊆
        {ω | M ≤ clusterIntersection Λ ω u} := by
      intro ω (hω : a * (M : ℝ) ≤ _)
      show M ≤ clusterIntersection Λ ω u
      exact_mod_cast (show (M : ℝ) ≤ (clusterIntersection Λ ω u : ℝ) by nlinarith)
    refine (measure_mono hsub).trans ?_
    calc L = 1 * L := (one_mul L).symm
      _ ≤ _ := by
        gcongr
        rw [← ENNReal.ofReal_one]
        apply ENNReal.ofReal_le_ofReal
        apply Real.one_le_exp
        have ha3 : a < 3 := by simpa using hk1
        linarith
  · obtain ⟨hk, hk2⟩ := hk2
    have hbk := (hBK q Λ hΛ (M : ℝ) (by linarith) k hk).2 u
    rw [hLev] at hbk
    have hsub : {ω : Config V | a * (M : ℝ) ≤ (clusterIntersection Λ ω u : ℝ)} ⊆
        {ω | (3 : ℝ) ^ k * (M : ℝ) ≤ (clusterIntersection Λ ω u : ℝ)} :=
      fun ω (hω : a * (M : ℝ) ≤ _) =>
        (mul_le_mul_of_nonneg_right hk2 hMnn).trans hω
    refine (measure_mono hsub).trans (hbk.trans ?_)
    gcongr
    refine (pow_le_pow_left₀ zero_le hMtail _).trans ?_
    rw [← ENNReal.ofReal_pow (Real.exp_pos _).le, ← Real.exp_nat_mul]
    apply ENNReal.ofReal_le_ofReal
    apply Real.exp_le_exp.2
    have h3 : (3 : ℝ) ^ (k + 1) = 9 * (3 : ℝ) ^ (k - 1) := by
      rw [show k + 1 = (k - 1) + 2 by omega, pow_add]; ring
    push_cast
    rw [h3] at hk1
    linarith

/-- The lower tail. -/
private theorem lower_tail_of_bk [Countable V] (hBK : TightnessBK V)
    (q : Sym2 V → unitInterval) {Λ : Finset V} (hΛ : Λ.Nonempty) {ε : ℝ} (hε : 0 < ε)
    (_hε1 : ε ≤ 1) :
    law q {ω | (maxClusterIntersection Λ ω : ℝ) < ε * (tightnessScale q Λ : ℝ)} ≤
      ENNReal.ofReal (27 * ε) := by
  set M := tightnessScale q Λ with hM
  have hM2' : 2 ≤ M := two_le_tightnessScale q hΛ
  have hM2 : (2 : ℝ) ≤ M := by exact_mod_cast hM2'
  -- Small threshold: the event is empty.
  by_cases hsmall : ε * (M : ℝ) < 1
  · have hempty : {ω : Config V | (maxClusterIntersection Λ ω : ℝ) < ε * (M : ℝ)} = ∅ := by
      apply Set.eq_empty_of_forall_notMem
      intro ω (hω : (maxClusterIntersection Λ ω : ℝ) < ε * (M : ℝ))
      have h1 : (1 : ℝ) ≤ maxClusterIntersection Λ ω := by
        exact_mod_cast one_le_maxClusterIntersection hΛ ω
      linarith
    rw [hempty, measure_empty]; exact zero_le
  push Not at hsmall
  obtain ⟨k, hk1, hk2⟩ := exists_pow_three_bracket (1 / (2 * ε))
  have hk1' : 1 < 2 * (3 : ℝ) ^ (k + 1) * ε := by
    rw [div_lt_iff₀ (by positivity)] at hk1; linarith
  rcases hk2 with rfl | hk2
  · -- `ε > 1/6`: the bound exceeds one.
    have h6 : 1 < 6 * ε := by norm_num at hk1'; linarith
    refine prob_le_one.trans ?_
    rw [← ENNReal.ofReal_one]
    apply ENNReal.ofReal_le_ofReal
    linarith
  obtain ⟨hk, hk2⟩ := hk2
  have hk2' : 2 * (3 : ℝ) ^ k * ε ≤ 1 := by
    rw [le_div_iff₀ (by positivity)] at hk2; linarith
  set l : ℝ := ε * M with hl
  set A := {ω : Config V | l ≤ (maxClusterIntersection Λ ω : ℝ)} with hA
  have hAm : MeasurableSet A := measurableSet_real_le_maxClusterIntersection Λ l
  set p := (law q A).toReal with hp
  have hlawA : law q A = ENNReal.ofReal p := (ENNReal.ofReal_toReal (measure_ne_top _ _)).symm
  have hp0 : 0 ≤ p := ENNReal.toReal_nonneg
  have hp1 : p ≤ 1 := by
    have := prob_le_one (μ := law q) (s := A)
    rw [hlawA] at this
    exact (ENNReal.ofReal_le_one).1 this
  -- `P(max ≥ M - 1) > e⁻¹`.
  have hstrict := lt_law_max_tail_of_lt_tightnessScale q Λ
    (show M - 1 < M by omega)
  have hsub : {ω : Config V | M - 1 ≤ maxClusterIntersection Λ ω} ⊆
      {ω | (3 : ℝ) ^ k * l ≤ (maxClusterIntersection Λ ω : ℝ)} := by
    intro ω (hω : M - 1 ≤ maxClusterIntersection Λ ω)
    show (3 : ℝ) ^ k * l ≤ _
    have hcast : ((M - 1 : ℕ) : ℝ) = (M : ℝ) - 1 := by
      rw [Nat.cast_sub (by omega)]; simp
    have h' : (M : ℝ) - 1 ≤ maxClusterIntersection Λ ω := by
      rw [← hcast]; exact_mod_cast hω
    have : (3 : ℝ) ^ k * l ≤ (M : ℝ) / 2 := by
      rw [hl]
      have hM0 : (0 : ℝ) ≤ M := by linarith
      nlinarith
    linarith
  have hbk := (hBK q Λ hΛ l hsmall k hk).1
  set n := 3 ^ (k - 1) + 1 with hn
  have hlt : ENNReal.ofReal (Real.exp (-1)) < ENNReal.ofReal (p ^ n) := by
    rw [ENNReal.ofReal_pow hp0, ← hlawA]
    exact hstrict.trans_le ((measure_mono hsub).trans hbk)
  have hlt' : Real.exp (-1) < p ^ n :=
    (ENNReal.ofReal_lt_ofReal_iff_of_nonneg (Real.exp_pos _).le).1 hlt
  have hexp := (hlt'.trans_le (pow_le_exp_neg hp0 n))
  rw [Real.exp_lt_exp] at hexp
  -- `n (1 - p) < 1` and `n ≥ 3^(k-1)`, `1 < 18 · 3^(k-1) ε`.
  have h3 : (3 : ℝ) ^ (k + 1) = 9 * (3 : ℝ) ^ (k - 1) := by
    rw [show k + 1 = (k - 1) + 2 by omega, pow_add]; ring
  have hn' : (3 : ℝ) ^ (k - 1) ≤ (n : ℝ) := by rw [hn]; push_cast; linarith
  have h1p : 0 ≤ 1 - p := by linarith
  have hfinal : 1 - p ≤ 27 * ε := by
    rw [h3] at hk1'
    have hpos : (0 : ℝ) < (3 : ℝ) ^ (k - 1) := by positivity
    nlinarith [mul_le_mul_of_nonneg_right hn' h1p]
  have hcompl : {ω : Config V | (maxClusterIntersection Λ ω : ℝ) < ε * (M : ℝ)} = Aᶜ := by
    ext ω; simp [hA, hl, not_le]
  rw [hcompl, prob_compl_eq_one_sub hAm, hlawA, ← ENNReal.ofReal_one,
    ← ENNReal.ofReal_sub _ hp0]
  exact ENNReal.ofReal_le_ofReal hfinal

/-- **Universal tightness from the BK step** (T-6, deduction of Theorem 2.2 from
Theorem 2.3 of arXiv:2008.11197v2, on the reading `k ≥ 1` of issue 52). -/
theorem universalTightness_of_tightnessBK [Countable V] (hBK : TightnessBK V) :
    UniversalTightness V := fun q _Λ hΛ =>
  ⟨fun _a ha => upper_tail_of_bk hBK q hΛ ha,
    fun _ε hε hε1 => lower_tail_of_bk hBK q hΛ hε hε1,
    fun u _a ha => rooted_tail_of_bk hBK q hΛ u ha⟩

/-! ### Non-vacuity (D-5): one vertex -/

private theorem clusterIntersection_unit_le (Λ : Finset Unit) (ω : Config Unit) (u : Unit) :
    clusterIntersection Λ ω u ≤ 1 := by
  unfold clusterIntersection
  calc (cluster ω u ∩ (Λ : Set Unit)).ncard ≤ (Set.univ : Set Unit).ncard :=
        Set.ncard_le_ncard (Set.subset_univ _) Set.finite_univ
    _ = 1 := by simp

private theorem maxClusterIntersection_unit_le (Λ : Finset Unit) (ω : Config Unit) :
    maxClusterIntersection Λ ω ≤ 1 :=
  Finset.sup_le fun v _ => clusterIntersection_unit_le Λ ω v

/-- The BK step holds on one vertex: every tail above one is empty. -/
theorem tightnessBK_unit : TightnessBK Unit := by
  intro q Λ _ l hl k hk
  have h3 : (3 : ℝ) ≤ (3 : ℝ) ^ k := by
    calc (3 : ℝ) = 3 ^ 1 := (pow_one 3).symm
      _ ≤ 3 ^ k := pow_le_pow_right₀ (by norm_num) hk
  have hbig : (1 : ℝ) < (3 : ℝ) ^ k * l := by nlinarith
  constructor
  · have : {ω : Config Unit | (3 : ℝ) ^ k * l ≤ (maxClusterIntersection Λ ω : ℝ)} = ∅ := by
      apply Set.eq_empty_of_forall_notMem
      intro ω (hω : (3 : ℝ) ^ k * l ≤ _)
      have : (maxClusterIntersection Λ ω : ℝ) ≤ 1 := by
        exact_mod_cast maxClusterIntersection_unit_le Λ ω
      linarith
    rw [this, measure_empty]; exact zero_le
  · intro u
    have : {ω : Config Unit | (3 : ℝ) ^ k * l ≤ (clusterIntersection Λ ω u : ℝ)} = ∅ := by
      apply Set.eq_empty_of_forall_notMem
      intro ω (hω : (3 : ℝ) ^ k * l ≤ _)
      have : (clusterIntersection Λ ω u : ℝ) ≤ 1 := by
        exact_mod_cast clusterIntersection_unit_le Λ ω u
      linarith
    rw [this, measure_empty]; exact zero_le

/-- Hence universal tightness holds on one vertex. -/
theorem universalTightness_unit : UniversalTightness Unit :=
  universalTightness_of_tightnessBK tightnessBK_unit

end PercLib.Percolation.Bond
