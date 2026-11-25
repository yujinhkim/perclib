/- Integrated from independently rebuilt Ultramath work.
Production base e6fb888fa60f4bb3d7fa5ab717b2d149345e3a7f.
Scratch source: repository-root .ultramath/smwwp7q3k/m1/.
-/

/-
Copyright (c) 2026 PercLib contributors. Released under Apache 2.0.

The Cauchy–Schwarz / tightness / (I.4.19) chain of Proposition I.4.20, Case 2
(`d = 3α + (Hydro)`),
together with the scalar asymptotic comparison against the normalized target
`|B_r| (M₂/M₁)^{p-1} M₁²`.  Statements only; every hypothesis is explicit.
-/
module

public import PercLib.CriticalLRP.VolumeMoments.HigherMoments.I420Case2.Defs
public import Mathlib.MeasureTheory.Integral.MeanInequalities

@[expose] public section

noncomputable section

open MeasureTheory Filter Topology Set
open scoped ENNReal NNReal Topology Asymptotics

namespace PercLib.CriticalLRP.Analysis.I420Case2

/-- Cauchy–Schwarz for `∫⁻` in the form used in Case 2 of Proposition I.4.20. -/
theorem lintegral_mul_le_rpow_half {α : Type*} [MeasurableSpace α] (μ : Measure α)
    {f g : α → ℝ≥0∞} (hf : AEMeasurable f μ) (hg : AEMeasurable g μ) :
    ∫⁻ a, f a * g a ∂μ ≤ (∫⁻ a, f a ^ (2 : ℝ) ∂μ) ^ (1 / 2 : ℝ)
      * (∫⁻ a, g a ^ (2 : ℝ) ∂μ) ^ (1 / 2 : ℝ) :=
  ENNReal.lintegral_mul_le_Lp_mul_Lq μ (p := 2) (q := 2)
    (show Real.HolderConjugate 2 2 from ⟨by norm_num, by norm_num, by norm_num⟩) hf hg

/-- **Cauchy–Schwarz step of Case 2.**
`E_r[|K|^{p+1}|K ∩ B_r|] ≤ √(E_r|K|^{2p+2}) √(E_r[|K ∩ B_r|²])`. -/
theorem jointMoment_le_cs (M : Orchestration.SourceModelData) (p : ℕ) (r : ℝ) :
    jointMoment M p r
      ≤ (M.cutMoment (2 * p + 2) r) ^ (1 / 2 : ℝ) * (interSecond M r) ^ (1 / 2 : ℝ) := by
  have hf : AEMeasurable (fun ω : Config M.V => clusterVol ω (0 : M.V) ^ (p + 1)) (M.cutLaw r) :=
    ((measurable_clusterVol (0 : M.V)).pow_const (p + 1)).aemeasurable
  have hg : AEMeasurable (fun ω : Config M.V => interVol M r ω) (M.cutLaw r) :=
    (measurable_clusterVolIn (0 : M.V) (M.ball r)).aemeasurable
  have hHolder := lintegral_mul_le_rpow_half (M.cutLaw r) hf hg
  have h1 : (∫⁻ ω : Config M.V, (fun ω => clusterVol ω (0 : M.V) ^ (p + 1)) ω ^ (2 : ℝ)
        ∂(M.cutLaw r)) = M.cutMoment (2 * p + 2) r := by
    rw [Orchestration.SourceModelData.cutMoment]
    refine lintegral_congr fun ω => ?_
    change (clusterVol ω (0 : M.V) ^ (p + 1)) ^ (2 : ℝ) = clusterVol ω (0 : M.V) ^ (2 * p + 2)
    rw [← ENNReal.rpow_natCast (clusterVol ω (0 : M.V)) (p + 1), ← ENNReal.rpow_mul,
      ← ENNReal.rpow_natCast (clusterVol ω (0 : M.V)) (2 * p + 2)]
    congr 1
    push_cast
    ring
  have h2 : (∫⁻ ω : Config M.V, (fun ω => interVol M r ω) ω ^ (2 : ℝ) ∂(M.cutLaw r))
      = interSecond M r := by
    rw [interSecond]
    refine lintegral_congr fun ω => ?_
    change interVol M r ω ^ (2 : ℝ) = interVol M r ω ^ 2
    rw [ENNReal.rpow_two]
  calc jointMoment M p r
      = ∫⁻ ω : Config M.V, (fun ω => clusterVol ω (0 : M.V) ^ (p + 1)) ω
          * (fun ω => interVol M r ω) ω ∂(M.cutLaw r) := rfl
    _ ≤ (∫⁻ ω : Config M.V, (fun ω => clusterVol ω (0 : M.V) ^ (p + 1)) ω ^ (2 : ℝ)
            ∂(M.cutLaw r)) ^ (1 / 2 : ℝ)
          * (∫⁻ ω : Config M.V, (fun ω => interVol M r ω) ω ^ (2 : ℝ) ∂(M.cutLaw r))
              ^ (1 / 2 : ℝ) := hHolder
    _ = (M.cutMoment (2 * p + 2) r) ^ (1 / 2 : ℝ) * (interSecond M r) ^ (1 / 2 : ℝ) := by
        rw [h1, h2]

/-- **Assembly of the Case 2 bounds.**  If the upper bound (I.4.19) at index `2p+2` holds with
constant `C (M₂/M₁)^{2p+1} M₁` and universal tightness gives `E_r[|K ∩ B_r|²] ≤ M_r M₁`,
then the joint moment is bounded by `√(C (M₂/M₁)^{2p+1} M₁) · √(M_r M₁)`. -/
theorem jointMoment_le_of_bounds (M : Orchestration.SourceModelData) (p : ℕ) (r : ℝ)
    (C : ℝ) (m₁ m₂ : ℝ → ℝ)
    (hC : 0 ≤ C * (m₂ r / m₁ r) ^ (2 * p + 1) * m₁ r)
    (hMr : 0 ≤ (M.Mr r : ℝ) * m₁ r)
    (hI419 : M.cutMoment (2 * p + 2) r
      ≤ ENNReal.ofReal (C * (m₂ r / m₁ r) ^ (2 * p + 1) * m₁ r))
    (hTight : interSecond M r ≤ ENNReal.ofReal ((M.Mr r : ℝ) * m₁ r)) :
    jointMoment M p r ≤ ENNReal.ofReal (jointUpper M p C m₁ m₂ r) := by
  have h1 : (M.cutMoment (2 * p + 2) r) ^ (1 / 2 : ℝ)
      ≤ (ENNReal.ofReal (C * (m₂ r / m₁ r) ^ (2 * p + 1) * m₁ r)) ^ (1 / 2 : ℝ) :=
    ENNReal.rpow_le_rpow hI419 (by norm_num)
  have h2 : (interSecond M r) ^ (1 / 2 : ℝ)
      ≤ (ENNReal.ofReal ((M.Mr r : ℝ) * m₁ r)) ^ (1 / 2 : ℝ) :=
    ENNReal.rpow_le_rpow hTight (by norm_num)
  refine le_trans (le_trans (jointMoment_le_cs M p r)
    (mul_le_mul h1 h2 (by positivity) (by positivity))) ?_
  have heq : (ENNReal.ofReal (C * (m₂ r / m₁ r) ^ (2 * p + 1) * m₁ r)) ^ (1 / 2 : ℝ)
        * (ENNReal.ofReal ((M.Mr r : ℝ) * m₁ r)) ^ (1 / 2 : ℝ)
      = ENNReal.ofReal (jointUpper M p C m₁ m₂ r) := by
    rw [ENNReal.ofReal_rpow_of_nonneg hC (by norm_num : (0 : ℝ) ≤ 1 / 2),
      ENNReal.ofReal_rpow_of_nonneg hMr (by norm_num : (0 : ℝ) ≤ 1 / 2),
      ← ENNReal.ofReal_mul (Real.rpow_nonneg hC _), jointUpper, i419Factor, tightFactor,
      Real.sqrt_eq_rpow, Real.sqrt_eq_rpow]
  rw [heq]

end PercLib.CriticalLRP.Analysis.I420Case2
