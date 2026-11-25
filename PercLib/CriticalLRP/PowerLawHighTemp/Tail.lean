/-
Copyright (c) 2026 PercLib contributors. Released under Apache 2.0.

# Exponential tail bounds for the paper's power-law model

Specialize the generic high-temperature tail estimate to the power-law
intensity on `Fin d → ℤ`, and then to the paper-literal `lrKernel`.
The critical parameter and the full sharpness interval are not inferred.
-/
module

public import PercLib.CriticalLRP.HighTemperatureTail
public import PercLib.CriticalLRP.PowerLawHighTemp.Moments

set_option autoImplicit false
set_option linter.unusedVariables false

attribute [local instance] Classical.propDecidable

@[expose] public section

noncomputable section

open Classical MeasureTheory Set
open PercLib.Percolation.Bond PercLib.Probability PercLib.CriticalLRP
open PercLib.CriticalLRP.FiniteVolume
open scoped ENNReal NNReal BigOperators

namespace PercLib.CriticalLRP.PowerLawHighTemp

open PercLib.CriticalLRP.Exploration.BFS

variable {V : Type*} [Countable V]

/-- A positive nonzero high-temperature interval always admits an exponential
cluster-tail bound. -/
theorem exists_lam_measure_cluster_encard_ge_le_intensityProfile (J : Sym2 V → ℝ≥0)
    (M : ℝ≥0)
    (hJ : ∀ v, (∑' w, if w = v then 0 else (J s(v,w) : ℝ≥0∞)) ≤ M) (β : ℝ≥0)
    (hβ : (β : ℝ≥0∞) * M < 1) (hm : 0 < ((β : ℝ≥0∞) * M).toReal) (o : V) :
    ∃ lam : ℝ, 1 < lam ∧ ∀ n : ℕ,
      (law (intensityProfile J β)) {ω | (n : ℕ∞) ≤ (cluster ω o).encard} ≤
        ENNReal.ofReal (1 / (((β : ℝ≥0∞) * M).toReal)) *
          ((ENNReal.ofReal lam) ^ (n : ℝ))⁻¹ := by
  let m := ((β : ℝ≥0∞) * M).toReal
  have hrow : UniformRowBound (intensityProfile J β) m :=
    uniformRowBound_intensityProfile J M hJ β hβ
  have hm1 : m < 1 := intensity_toReal_mul_lt_one M hβ
  obtain ⟨lam, hlam, hcond⟩ := ExplorationEnvelope.exists_admissible_lambda hm hm1
  refine ⟨lam, hlam, fun n => ?_⟩
  exact measure_cluster_encard_ge_le_inv_mul_rpow hrow o hlam hm hm1.le hcond n

/-- For the paper's power-law intensity, a positive high-temperature budget gives
an explicit exponential cluster-volume tail bound at `lrKernel d α`. -/
theorem exists_lam_measure_cluster_encard_ge_le_lrKernel {d : ℕ} (hd : 1 ≤ d)
    {α : ℝ} (hα : 0 < α) {β : ℝ≥0}
    (hβ : (β : ℝ≥0∞) * ((Real.toNNReal
      (∑' z : Fin d → ℤ, (linfNorm z : ℝ) ^ (-((d : ℝ) + α))) : ℝ≥0) : ℝ≥0∞) < 1)
    (hm : 0 < ((β : ℝ≥0∞) * Real.toNNReal
      (∑' z : Fin d → ℤ, (linfNorm z : ℝ) ^ (-((d : ℝ) + α)))).toReal)
    (x : Fin d → ℤ) :
let M : ℝ≥0 := Real.toNNReal
      (∑' z : Fin d → ℤ, (linfNorm z : ℝ) ^ (-((d : ℝ) + α)))
    ∃ lam : ℝ, 1 < lam ∧ ∀ n : ℕ,
      (PercLib.CriticalLRP.longRangeMeasure
        (PercLib.CriticalLRP.lrKernel d α) (PercLib.CriticalLRP.lrKernel_nonneg d α) β)
        {ω | (n : ℕ∞) ≤ (cluster ω x).encard} ≤
        ENNReal.ofReal (1 / ((β : ℝ≥0∞) * M).toReal) *
          ((ENNReal.ofReal lam) ^ (n : ℝ))⁻¹ := by
  obtain ⟨J, hJ⟩ := PercLib.Models.exists_sym2_kernel
    (fun z : Fin d → ℤ => Real.toNNReal ((linfNorm z : ℝ) ^ (-((d : ℝ) + α))))
    (fun z => by
      show Real.toNNReal ((linfNorm (-z) : ℝ) ^ (-((d : ℝ) + α)))
        = Real.toNNReal ((linfNorm z : ℝ) ^ (-((d : ℝ) + α)))
      rw [linfNorm_neg])
  let M : ℝ≥0 := Real.toNNReal (∑' z : Fin d → ℤ, (linfNorm z : ℝ) ^ (-((d : ℝ) + α)))
  have hrows : ∀ v : Fin d → ℤ,
      (∑' w : Fin d → ℤ, @ite ℝ≥0∞ (w = v) (Classical.propDecidable _) 0
        (J s(v,w) : ℝ≥0∞)) ≤ M := by
    intro v
    exact (ENNReal.tsum_le_tsum fun w => by split_ifs <;> simp).trans
      (power_rowSum_le hd (by linarith) hJ v)
  have htail := exists_lam_measure_cluster_encard_ge_le_intensityProfile J M hrows β hβ hm x
  simpa only [M, law_intensityProfile_eq_longRangeMeasure hJ β] using htail

end PercLib.CriticalLRP.PowerLawHighTemp
