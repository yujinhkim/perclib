/-
Copyright (c) 2026 PercLib contributors. Released under Apache 2.0.

# Extended-power moments of the true cluster as finite-horizon limits.

Accepted from independent submission `smwpalb9h` direction D2.
No generation-moment induction or cluster-moment finiteness is asserted here.
-/
module

/-
Private swarm module (member m2, swarm smwpalb9h), direction 2.

The final infinite-volume limit step (item (III) of `PROOF.md` §8 of the accepted
run): monotone convergence of the finite-horizon cluster moment to the true
cluster moment, on the actual `Config (Sym2 V)` / `cluster`.

`epow lam n` is the extended power `lam ^ n`, defined for `n : ℕ∞` as the
supremum of the finite powers `lam ^ k`, `k ≤ n`.  For finite `n` it is the
usual `ENNReal.rpow`; it is exactly the monotone limit that occurs in the
frontier-exploration moment induction.
-/
public import PercLib.CriticalLRP.Exploration.BFS.Counting
public import Mathlib.MeasureTheory.MeasurableSpace.NCard
public import Mathlib.MeasureTheory.Integral.Lebesgue.Basic

set_option autoImplicit false


@[expose] public section

noncomputable section

open MeasureTheory Set Filter PercLib.Percolation.Bond
open scoped ENNReal BigOperators Topology

namespace PercLib.CriticalLRP.Exploration.BFS

variable {V : Type*}

theorem epow_natCast (lam : ℝ≥0∞) (hlam : 1 ≤ lam) (m : ℕ) :
    epow lam (m : ℕ∞) = lam ^ (m : ℝ) := by
  rw [epow]
  apply le_antisymm
  · apply iSup_le
    intro k
    apply ENNReal.rpow_le_rpow_of_exponent_le hlam
    exact_mod_cast ENat.toNat_le_toNat inf_le_left (by simp)
  · simpa using le_iSup (fun k : ℕ => lam ^ ((((m : ℕ∞) ⊓ (k : ℕ∞))).toNat : ℝ)) m

theorem epow_mono (lam : ℝ≥0∞) (hlam : 1 ≤ lam) : Monotone (epow lam) := by
  intro m n hmn
  rw [epow, epow]
  apply iSup_le
  intro k
  apply le_iSup_of_le k
  apply ENNReal.rpow_le_rpow_of_exponent_le hlam
  exact_mod_cast ENat.toNat_le_toNat (inf_le_inf_right _ hmn) (by simp)

/-- The extended power commutes with countable suprema: this is the pointwise
identity behind monotone convergence of the cluster moment. -/
theorem epow_iSup (lam : ℝ≥0∞) (hlam : 1 ≤ lam) (a : ℕ → ℕ∞) :
    epow lam (⨆ i, a i) = ⨆ i, epow lam (a i) := by
  rw [epow]
  rw [show (⨆ i, epow lam (a i)) =
      ⨆ k : ℕ, ⨆ i, lam ^ (((a i ⊓ (k : ℕ∞))).toNat : ℝ) from by
    simp only [epow]
    exact iSup_comm]
  apply iSup_congr
  intro k
  rw [iSup_inf_eq]
  have hk : (⨆ i, a i ⊓ (k : ℕ∞)) ≤ (k : ℕ∞) := iSup_le fun i => inf_le_right
  have hkne : (⨆ i, a i ⊓ (k : ℕ∞)) ≠ ⊤ := ne_top_of_le_ne_top (by simp) hk
  obtain ⟨i0, hi0⟩ := ENat.exists_eq_iSup_of_lt_top (lt_top_iff_ne_top.mpr hkne)
  apply le_antisymm
  · rw [← hi0]
    exact le_iSup (fun i => lam ^ (((a i ⊓ (k : ℕ∞))).toNat : ℝ)) i0
  · apply iSup_le
    intro i
    apply ENNReal.rpow_le_rpow_of_exponent_le hlam
    exact_mod_cast ENat.toNat_le_toNat (le_iSup (fun i => a i ⊓ (k : ℕ∞)) i) hkne

theorem measurable_epow (lam : ℝ≥0∞) : Measurable (epow lam) := by
  apply Measurable.iSup
  intro k
  exact measurable_of_countable _

/-- For `lam > 1` the extended power at `⊤` is `⊤`, the usual convention. -/
theorem epow_top_of_one_lt (lam : ℝ≥0∞) (hlam : 1 < lam) : epow lam ⊤ = ⊤ := by
  rw [epow]
  have hmin : ∀ k : ℕ, (⊤ : ℕ∞) ⊓ (k : ℕ∞) = (k : ℕ∞) := fun k => top_inf_eq _
  simp only [hmin, ENat.toNat_natCast]
  rw [iSup_eq_top]
  intro b hb
  obtain ⟨N, hN⟩ := ENNReal.exists_nat_gt hb.ne
  rcases eq_or_ne lam ⊤ with hl | hl
  · refine ⟨1, ?_⟩
    rw [hl]
    simpa using hb
  · have hpos : 0 < lam.toReal := ENNReal.toReal_pos (by positivity) hl
    have h1 : 1 < lam.toReal := by
      rw [← ENNReal.ofReal_lt_ofReal_iff hpos, ENNReal.ofReal_one, ENNReal.ofReal_toReal hl]
      exact hlam
    have htend : Tendsto (fun k : ℕ => lam.toReal ^ ((k : ℕ) : ℝ)) atTop atTop :=
      (tendsto_rpow_atTop_of_base_gt_one lam.toReal h1).comp tendsto_natCast_atTop_atTop
    obtain ⟨k, hk⟩ := (htend.eventually (eventually_gt_atTop (N : ℝ))).exists
    refine ⟨k, lt_trans hN ?_⟩
    have h_eq : lam ^ ((k : ℕ) : ℝ) = ENNReal.ofReal (lam.toReal ^ ((k : ℕ) : ℝ)) := by
      conv_lhs => rw [← ENNReal.ofReal_toReal hl]
      rw [ENNReal.ofReal_rpow_of_nonneg (by positivity) (by positivity)]
    rw [h_eq]
    exact ENNReal.natCast_lt_ofReal.mpr hk

/-- At `lam = 1` the extended power is `1` even at `⊤`. -/
theorem epow_one_top : epow 1 ⊤ = 1 := by
  rw [epow]
  have hmin : ∀ k : ℕ, (⊤ : ℕ∞) ⊓ (k : ℕ∞) = (k : ℕ∞) := fun k => top_inf_eq _
  simp only [hmin, ENat.toNat_natCast, ENNReal.one_rpow, iSup_const]

/-- For a finite set the extended power is the usual real power of its
cardinality. -/
theorem epow_encard_eq_rpow_toNat (lam : ℝ≥0∞) (hlam : 1 ≤ lam) {s : Set V}
    (h : s.encard ≠ ⊤) : epow lam s.encard = lam ^ (s.encard.toNat : ℝ) := by
  conv_lhs => rw [← ENat.natCast_toNat h]
  exact epow_natCast lam hlam s.encard.toNat

section Countable

variable [Countable V]

theorem measurable_encard_horizon_ENat (o : V) (k : ℕ) :
    Measurable fun ω : Config V => (horizon ω o k).encard := by
  refine measurable_encard.comp ?_
  rw [measurable_set_iff]
  intro y
  exact measurableSet_setOfPred.mp
    ((measurableSet_mem_state o k y).2.1.union (measurableSet_mem_state o k y).1)

theorem measurable_encard_horizon (o : V) (k : ℕ) :
    Measurable fun ω : Config V => ((horizon ω o k).encard : ℝ≥0∞) :=
  (measurable_of_countable (fun n : ℕ∞ => (n : ℝ≥0∞))).comp
    (measurable_encard_horizon_ENat o k)

theorem measurableSet_mem_cluster (o y : V) :
    MeasurableSet {ω : Config V | y ∈ cluster ω o} := by
  have h : {ω : Config V | y ∈ cluster ω o} = conn o y := by
    ext ω
    exact mem_cluster_iff ω o y
  rw [h]
  exact measurableSet_conn o y

theorem measurable_encard_cluster_ENat (o : V) :
    Measurable fun ω : Config V => (cluster ω o).encard := by
  refine measurable_encard.comp ?_
  rw [measurable_set_iff]
  intro y
  exact measurableSet_setOfPred.mp (measurableSet_mem_cluster o y)

theorem measurable_encard_cluster (o : V) :
    Measurable fun ω : Config V => ((cluster ω o).encard : ℝ≥0∞) :=
  (measurable_of_countable (fun n : ℕ∞ => (n : ℝ≥0∞))).comp
    (measurable_encard_cluster_ENat o)

/-- **Monotone convergence of the cluster moment.**  The extended moment of the
true cluster is the supremum of the finite-horizon extended moments. -/
theorem lintegral_epow_encard_cluster_eq_iSup (μ : Measure (Config V)) (o : V)
    (lam : ℝ≥0∞) (hlam : 1 ≤ lam) :
    ∫⁻ ω, epow lam ((cluster ω o).encard) ∂μ =
      ⨆ n, ∫⁻ ω, epow lam ((horizon ω o n).encard) ∂μ := by
  have hfun : (fun ω => epow lam ((cluster ω o).encard)) =
      fun ω => ⨆ n, epow lam ((horizon ω o n).encard) := by
    funext ω
    rw [← epow_iSup lam hlam, encard_cluster_eq_iSup_horizon]
  rw [hfun]
  refine lintegral_iSup (fun n => ?_) (fun i j hij ω => ?_)
  · exact (measurable_epow lam).comp (measurable_encard_horizon_ENat o n)
  · exact epow_mono lam hlam (Set.encard_mono (horizon_mono ω o hij))

/-- If every finite-horizon extended moment is bounded by `C`, then so is the
extended moment of the true (possibly infinite) cluster. -/
theorem lintegral_epow_encard_cluster_le (μ : Measure (Config V)) (o : V)
    (lam : ℝ≥0∞) (hlam : 1 ≤ lam) (C : ℝ≥0∞)
    (h : ∀ n, ∫⁻ ω, epow lam ((horizon ω o n).encard) ∂μ ≤ C) :
    ∫⁻ ω, epow lam ((cluster ω o).encard) ∂μ ≤ C := by
  rw [lintegral_epow_encard_cluster_eq_iSup μ o lam hlam]
  exact iSup_le h

end Countable

/-- If the cluster is almost surely finite, the extended moment is the usual
`∫ lam ^ |K|` with `|K| = (cluster).encard.toNat`. -/
theorem lintegral_epow_eq_of_ae_finite (μ : Measure (Config V)) (o : V)
    (lam : ℝ≥0∞) (hlam : 1 ≤ lam)
    (hfin : ∀ᵐ ω ∂μ, (cluster ω o).encard ≠ ⊤) :
    ∫⁻ ω, epow lam ((cluster ω o).encard) ∂μ =
      ∫⁻ ω, lam ^ (((cluster ω o).encard.toNat : ℕ) : ℝ) ∂μ := by
  apply lintegral_congr_ae
  filter_upwards [hfin] with ω h
  exact epow_encard_eq_rpow_toNat lam hlam h

end PercLib.CriticalLRP.Exploration.BFS
