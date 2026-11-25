/-
Copyright (c) 2026 PercLib contributors. Released under Apache 2.0.

# Logarithmic errors from ball-count and kernel normalizations

The proof of Proposition I.4.2 writes the normalized derivative of the flux as
`(1 + δ r) (1 + O(1/r))`.  This file proves the corresponding product closure,
and applies it to the genuine normalized `SourceModelData` ball count.  The
ball estimate is the already-proved Lemma I.4.6; finite balls and measurable
representatives are handled explicitly.
-/
module

public import PercLib.CriticalLRP.Analysis.ErrorFunctions
public import PercLib.CriticalLRP.Orchestration.Defs
public import PercLib.CriticalLRP.Orchestration.ModelWitness.Defs

set_option autoImplicit false

@[expose] public section

open MeasureTheory Set Filter
open scoped ENNReal Topology

namespace PercLib.CriticalLRP.Analysis

/-- Multiplying a logarithmic error by an eventual `O(1/r)` term still gives a
logarithmically integrable error. -/
theorem isLogErrorFunction_mul_of_denominator_bound {δ : ℝ → ℝ}
    (hδ : IsLogErrorFunction δ) {η : ℝ → ℝ} (hη : Measurable η)
    {c r₀ : ℝ} (hc : 0 ≤ c) (hr₀ : 0 < r₀)
    (hbound : ∀ r, r₀ ≤ r → |η r| ≤ c * r⁻¹) :
    IsLogErrorFunction (fun r => δ r * η r) := by
  obtain ⟨N, hN⟩ := Metric.tendsto_atTop.1 hδ.2 1 zero_lt_one
  refine isLogErrorFunction_of_denominator_bound (hδ.1.1.mul hη) hc
    (r₀ := max N r₀) (hr₀.trans_le (le_max_right N r₀)) ?_
  intro r hr
  have hrN : N ≤ r := (le_max_left N r₀).trans hr
  have hrR : r₀ ≤ r := (le_max_right N r₀).trans hr
  have hsmall : |δ r| ≤ 1 := by
    have h := hN r hrN
    rw [Real.dist_eq, sub_zero] at h
    exact h.le
  rw [abs_mul]
  calc
    |δ r| * |η r| ≤ 1 * |η r| :=
      mul_le_mul_of_nonneg_right hsmall (abs_nonneg _)
    _ ≤ 1 * (c * r⁻¹) := by
      gcongr
      exact hbound r hrR
    _ = c * r⁻¹ := one_mul _

/-- The complementary error `1 - (1 + δ)(1 + η)` is logarithmically
integrable when `δ` is a logarithmic error and `η` is eventual `O(1/r)`.
The signs of both terms are unrestricted. -/
theorem isLogErrorFunction_one_sub_mul_of_denominator_bound {δ : ℝ → ℝ}
    (hδ : IsLogErrorFunction δ) {η : ℝ → ℝ} (hη : Measurable η)
    {c r₀ : ℝ} (hc : 0 ≤ c) (hr₀ : 0 < r₀)
    (hbound : ∀ r, r₀ ≤ r → |η r| ≤ c * r⁻¹) :
    IsLogErrorFunction (fun r => 1 - (1 + δ r) * (1 + η r)) := by
  have hηlog := isLogErrorFunction_of_denominator_bound hη hc hr₀ hbound
  have hprod := isLogErrorFunction_mul_of_denominator_bound hδ hη hc hr₀ hbound
  have hsum := isLogErrorFunction_add hδ (isLogErrorFunction_add hηlog hprod)
  have heq : (fun r => 1 - (1 + δ r) * (1 + η r)) =
      (fun r => -(δ r + (η r + δ r * η r))) := by
    funext r
    ring
  rw [heq]
  exact isLogErrorFunction_neg hsum

#print axioms PercLib.CriticalLRP.Analysis.isLogErrorFunction_mul_of_denominator_bound
#print axioms PercLib.CriticalLRP.Analysis.isLogErrorFunction_one_sub_mul_of_denominator_bound

end PercLib.CriticalLRP.Analysis

namespace PercLib.CriticalLRP.Orchestration

open Analysis LatticeGeometry

/-- Every admissible source norm has finite lattice balls.  The proof uses the
same finite-cell packing argument as Lemma I.4.6; nonpositive outer radii are
handled separately. -/
theorem SourceNormData.finite_ball {d : ℕ} (S : SourceNormData d)
    {C : ℝ} (hC : ∀ y : Fin d → ℝ, (∀ j, 0 ≤ y j ∧ y j < 1) → S.ρ y ≤ C)
    (hC0 : 0 ≤ C) (r : ℝ) :
    {z : Fin d → ℤ | S.ρ (fun j => (z j : ℝ)) ≤ r}.Finite := by
  have hρnonneg (v : Fin d → ℝ) : 0 ≤ S.ρ v := by
    have h := S.ρ_add_le v (-v)
    rw [S.ρ_neg, add_neg_cancel, S.ρ_zero] at h
    linarith
  by_cases hrc : 0 < r + C
  · have hvol : volume {x : Fin d → ℝ | S.ρ x ≤ r + C} ≠ ∞ := by
      change volume (rhoBall S.ρ (r + C)) ≠ ∞
      rw [volume_rhoBall S.ρ_smul S.unitBall_volume hrc]
      exact ENNReal.ofReal_ne_top
    exact integer_centers_finite_of_volume_ne_top S.ρ_add_le S.ρ_neg hC hvol
  · have hsingle : {z : Fin d → ℤ | S.ρ (fun j => (z j : ℝ)) ≤ r} ⊆
        ({0} : Set (Fin d → ℤ)) := by
      intro z hz
      have hrc' : r + C ≤ 0 := le_of_not_gt hrc
      simp only [Set.mem_ofPred_eq] at hz
      have hzv : (fun j => (z j : ℝ)) = (0 : Fin d → ℝ) := by
        by_contra hv
        have hpos := S.ρ_pos _ hv
        linarith
      have hz0 : z = 0 := by
        funext j
        have hzero : (z j : ℝ) = 0 := by
          simpa using congrFun hzv j
        exact_mod_cast hzero
      simp [hz0]
    exact (Set.finite_singleton 0).subset hsingle

/-- Finiteness of the source model's normalized lattice balls. -/
theorem SourceModelData.finite_ball (M : SourceModelData) (r : ℝ) : (M.ball r).Finite := by
  change {z : M.V | M.S.ρ (fun j => (z j : ℝ)) ≤ r}.Finite
  obtain ⟨C, hC⟩ := exists_unitCube_upper_bound M.S.ρ M.S.ρ_continuous
  have hC0 : 0 ≤ C := by
    have h := hC 0 (fun j => by simp)
    rw [M.S.ρ_zero] at h
    exact h
  exact M.S.finite_ball hC hC0 r

/-- The normalized ball-count error has an explicit measurable representative. -/
theorem SourceModelData.measurable_ball_ratio_error (M : SourceModelData) :
    Measurable (fun r : ℝ => ((M.ball r).ncard : ℝ) / r ^ M.d - 1) := by
  have hmono : Monotone (fun r : ℝ => ((M.ball r).ncard : ℝ)) := by
    intro r s hrs
    have hsub : M.ball r ⊆ M.ball s := by
      intro z hz
      change M.S.ρ (toVec z) ≤ r at hz
      change M.S.ρ (toVec z) ≤ s
      exact hz.trans hrs
    exact Nat.cast_le.mpr (Set.ncard_le_ncard hsub (M.finite_ball s))
  exact (hmono.measurable.div (measurable_id.pow_const M.d)).sub measurable_const

/-- Lemma I.4.6 in ratio form: the relative ball-count error is eventually
bounded by a constant times `r⁻¹`. -/
theorem SourceModelData.ball_ratio_error_bound (M : SourceModelData) :
    ∃ c R : ℝ, 0 ≤ c ∧ 0 < R ∧
      ∀ r : ℝ, R ≤ r → |((M.ball r).ncard : ℝ) / r ^ M.d - 1| ≤ c * r⁻¹ := by
  have hO : (fun r : ℝ => (Set.ncard {z : Fin M.d → ℤ |
      M.S.ρ (fun j => (z j : ℝ)) ≤ r} : ℝ) - r ^ M.d) =O[atTop]
      (fun r => r ^ (M.d - 1)) :=
    lemma_I_4_6 M.S.ρ_add_le M.S.ρ_neg M.S.ρ_continuous M.S.ρ_smul M.S.unitBall_volume
  obtain ⟨C, hC⟩ := hO.bound
  obtain ⟨R, hR⟩ := eventually_atTop.1 hC
  refine ⟨max C 1, max R 1, (zero_le_one).trans (le_max_right C 1),
    lt_of_lt_of_le zero_lt_one (le_max_right R 1), ?_⟩
  intro r hr
  have hrR : R ≤ r := (le_max_left R 1).trans hr
  have hr1 : 1 ≤ r := (le_max_right R 1).trans hr
  have hrpos : 0 < r := zero_lt_one.trans_le hr1
  have hpowpos : 0 < r ^ M.d := pow_pos hrpos M.d
  have hdiff : |(M.ball r).ncard - r ^ M.d| ≤ max C 1 * r ^ (M.d - 1) := by
    have hnr := hR r hrR
    calc
      |(M.ball r).ncard - r ^ M.d| = ‖(M.ball r).ncard - r ^ M.d‖ :=
        (Real.norm_eq_abs _).symm
      _ ≤ C * ‖r ^ (M.d - 1)‖ := hnr
      _ ≤ max C 1 * r ^ (M.d - 1) := by
        rw [Real.norm_eq_abs, abs_of_nonneg (pow_nonneg hrpos.le _)]
        exact mul_le_mul_of_nonneg_right (le_max_left C 1) (pow_nonneg hrpos.le _)
  rw [div_sub_one (pow_ne_zero M.d hrpos.ne'), abs_div, abs_of_pos hpowpos]
  calc
    |(M.ball r).ncard - r ^ M.d| / r ^ M.d
        ≤ (max C 1 * r ^ (M.d - 1)) / r ^ M.d :=
      div_le_div_of_nonneg_right hdiff hpowpos.le
    _ = max C 1 * r⁻¹ := by
      rw [mul_div_assoc]
      congr 1
      have hsplit : r ^ (M.d - 1) / r ^ M.d = 1 / r := by
        rw [div_eq_div_iff (by positivity) (ne_of_gt hrpos), ← pow_succ,
          Nat.sub_add_cancel M.hd]
        ring
      simpa only [one_div] using hsplit

/-- **I.4.g9 at the actual source model.**  If `δ` is the kernel's
logarithmically integrable normalization error, then the complementary error
in the exact product of `1 + δ` with the normalized lattice-ball ratio is also
logarithmically integrable.  The product supplies its own measurable
representative; no sign condition is imposed on `δ`. -/
theorem SourceModelData.isLogErrorFunction_one_sub_mul_ball_ratio
    (M : SourceModelData) {δ : ℝ → ℝ} (hδ : Analysis.IsLogErrorFunction δ) :
    Analysis.IsLogErrorFunction (fun r : ℝ =>
      1 - (1 + δ r) * (((M.ball r).ncard : ℝ) / r ^ M.d)) := by
  obtain ⟨C, R, hC, hR, hbound⟩ := M.ball_ratio_error_bound
  have h := Analysis.isLogErrorFunction_one_sub_mul_of_denominator_bound hδ
    M.measurable_ball_ratio_error hC hR hbound
  have heq : (fun r : ℝ => 1 - (1 + δ r) * (((M.ball r).ncard : ℝ) / r ^ M.d)) =
      (fun r : ℝ => 1 - (1 + δ r) *
        (1 + (((M.ball r).ncard : ℝ) / r ^ M.d - 1))) := by
    funext r
    ring
  rw [heq]
  exact h

example : Analysis.IsLogErrorFunction (fun r : ℝ =>
    1 - (1 + (fun _ => 0) r) *
      (((Witness.sourceModelWitness 1 le_rfl 1 zero_lt_one).ball r).ncard : ℝ) /
        r ^ (Witness.sourceModelWitness 1 le_rfl 1 zero_lt_one).d) := by
  have hzero : Analysis.IsLogErrorFunction (fun _ : ℝ => 0) := by
    apply Analysis.isLogErrorFunction_of_denominator_bound measurable_const
      (c := 0) (r₀ := 1) le_rfl one_pos
    intro r _hr
    simp
  simpa using
    (Witness.sourceModelWitness 1 le_rfl 1 zero_lt_one).isLogErrorFunction_one_sub_mul_ball_ratio
      hzero

#print axioms PercLib.CriticalLRP.Orchestration.SourceNormData.finite_ball
#print axioms PercLib.CriticalLRP.Orchestration.SourceModelData.finite_ball
#print axioms PercLib.CriticalLRP.Orchestration.SourceModelData.measurable_ball_ratio_error
#print axioms PercLib.CriticalLRP.Orchestration.SourceModelData.ball_ratio_error_bound
#print axioms PercLib.CriticalLRP.Orchestration.SourceModelData.isLogErrorFunction_one_sub_mul_ball_ratio

end PercLib.CriticalLRP.Orchestration
