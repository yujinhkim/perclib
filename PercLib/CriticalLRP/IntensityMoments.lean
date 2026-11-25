/-
Copyright (c) 2026 PercLib contributors. Released under Apache 2.0.

# Natural cluster moments for high-temperature intensity profiles

Apply the BFS exponential and polynomial cluster-moment bounds to the
intensity-parameter interface.  This is a high-temperature result at
`β M < 1`, not a statement about the critical parameter or a cutoff law.
-/
module

public import PercLib.Percolation.Bond.Intensity
public import PercLib.CriticalLRP.PowerLawHighTemp
public import PercLib.CriticalLRP.Exploration.BFS.HighTemperature.Moment.Natural

set_option autoImplicit false

attribute [local instance] Classical.propDecidable

@[expose] public section

noncomputable section

open Classical MeasureTheory Set
open PercLib.Percolation.Bond PercLib.Probability PercLib.CriticalLRP
open PercLib.CriticalLRP.FiniteVolume
open scoped ENNReal NNReal BigOperators

namespace PercLib.CriticalLRP.Exploration.BFS

variable {V : Type*}

/-- On a finite cluster, the real power of `encard.toNat` is the natural power in the
usual `ℝ≥0∞` cluster-volume normalization. -/
theorem ofReal_encard_toNat_pow (s : Set V) (hfin : s.encard ≠ ⊤) (k : ℕ) :
    ENNReal.ofReal ((s.encard.toNat : ℝ) ^ k) = ((s.encard : ℝ≥0∞) ^ k) := by
  have hbase : ENNReal.ofReal (s.encard.toNat : ℝ) = (s.encard : ℝ≥0∞) := by
    calc ENNReal.ofReal (s.encard.toNat : ℝ) = (s.encard.toNat : ℝ≥0∞) :=
          ENNReal.ofReal_natCast _
      _ = (s.encard : ℝ≥0∞) := congrArg (fun n : ℕ∞ => (n : ℝ≥0∞)) (ENat.natCast_toNat hfin)
  calc ENNReal.ofReal ((s.encard.toNat : ℝ) ^ k)
      = (ENNReal.ofReal (s.encard.toNat : ℝ)) ^ k :=
        ENNReal.ofReal_pow (by positivity : 0 ≤ (s.encard.toNat : ℝ)) k
    _ = (s.encard : ℝ≥0∞) ^ k := by rw [hbase]

/-- The usual intensity-row bound supplies the finite-partial real row bound used by the
BFS high-temperature theorem, on the actual `law`/`prodBernoulli` measure. -/
theorem uniformRowBound_intensityProfile [Countable V] (J : Sym2 V → ℝ≥0) (M : ℝ≥0)
    (hJ : ∀ v, (∑' w, if w = v then 0 else (J s(v,w) : ℝ≥0∞)) ≤ M) (β : ℝ≥0)
    (hβ : (β : ℝ≥0∞) * M < 1) :
    UniformRowBound (intensityProfile J β) ((β : ℝ≥0∞) * M).toReal := by
  have hprod : ((β : ℝ≥0∞) * M) ≠ ⊤ :=
    ne_top_of_lt ((hβ.trans_le le_top))
  have hM0 : 0 ≤ (((β : ℝ≥0∞) * M).toReal) := ENNReal.toReal_nonneg
  intro x t hx
  rw [← ENNReal.ofReal_le_ofReal_iff hM0]
  calc ENNReal.ofReal (∑ y ∈ t, ((intensityProfile J β s(x,y)) : ℝ))
      = ∑ y ∈ t, ENNReal.ofReal ((intensityProfile J β s(x,y)) : ℝ) :=
        ENNReal.ofReal_sum_of_nonneg (fun y _ => (intensityProfile J β s(x,y)).2.1)
    _ = ∑ y ∈ t, (if y = x then 0 else
          (unitInterval.toNNReal (intensityProfile J β s(x,y)) : ℝ≥0∞)) := by
      apply Finset.sum_congr rfl
      intro y hy
      have hyx : y ≠ x := by
        intro h
        exact hx (h ▸ hy)
      simp only [hyx, ↓reduceIte]
      exact (unitInterval_toNNReal_coe (intensityProfile J β) (s(x,y))).symm
    _ ≤ ∑' y : V, (if y = x then 0 else
          (unitInterval.toNNReal (intensityProfile J β s(x,y)) : ℝ≥0∞)) := by
      exact ENNReal.sum_le_tsum t
    _ ≤ (β : ℝ≥0∞) * M := intensity_rowSum_le J M hJ β x
    _ = ENNReal.ofReal (((β : ℝ≥0∞) * M).toReal) :=
        (ENNReal.ofReal_toReal hprod).symm

/-- The intensity budget is strictly below one in the real form used by the envelope. -/
theorem intensity_toReal_mul_lt_one (M : ℝ≥0) {β : ℝ≥0}
    (hβ : (β : ℝ≥0∞) * M < 1) : (((β : ℝ≥0∞) * M).toReal) < 1 := by
  refine (ENNReal.toReal_lt_toReal ?_ ENNReal.one_ne_top).2 hβ
  exact ne_top_of_lt (hβ.trans_le le_top)


open PercLib.Probability.ExplorationEnvelope

variable [Countable V]

/-- A unified admissible scalar envelope for a high-temperature intensity profile,
including the zero-row-budget case. -/
theorem exists_lam_envelope_intensityProfile (J : Sym2 V → ℝ≥0) (M : ℝ≥0)
    (hJ : ∀ v, (∑' w, if w = v then 0 else (J s(v,w) : ℝ≥0∞)) ≤ M) (β : ℝ≥0)
    (hβ : (β : ℝ≥0∞) * M < 1) :
    ∃ lam C : ℝ, 1 < lam ∧
      ∀ n : ℕ, lam * envelope (((β : ℝ≥0∞) * M).toReal) lam n ≤ C := by
  let m := ((β : ℝ≥0∞) * M).toReal
  have hrow : UniformRowBound (intensityProfile J β) m :=
    uniformRowBound_intensityProfile J M hJ β hβ
  have hm1 : m < 1 := intensity_toReal_mul_lt_one M hβ
  by_cases hm : m = 0
  · refine ⟨2, 2, by norm_num, ?_⟩
    intro n
    have hu : ∀ n : ℕ, envelope m (2 : ℝ) n = 1 := by
      intro k
      induction k with
      | zero => rw [envelope_zero]
      | succ k ih =>
          rw [envelope_succ, envelopeStep, ih, hm]
          norm_num
    rw [hu n]
    norm_num
  · have hmpos : 0 < m := lt_of_le_of_ne ENNReal.toReal_nonneg (Ne.symm hm)
    obtain ⟨lam, hlam, hcond⟩ := exists_admissible_lambda hmpos hm1
    refine ⟨lam, 1 / m, hlam, fun n => ?_⟩
    have hu := envelope_le_inv_mul hmpos hm1.le hlam.le hcond n
    have hpos : 0 < m * lam := by positivity
    calc lam * envelope m lam n ≤ lam * (1 / (m * lam)) :=
          mul_le_mul_of_nonneg_left hu (by linarith)
      _ = 1 / m := by field_simp

/-- Every natural cluster-volume moment is finite under an explicit high-temperature
intensity-row bound.  The actual law is `law (intensityProfile J β)`, i.e.
`prodBernoulli (intensityProfile J β)` definitionally. -/
theorem lintegral_clusterVol_intensity_pow_ne_top (J : Sym2 V → ℝ≥0) (M : ℝ≥0)
    (hJ : ∀ v, (∑' w, if w = v then 0 else (J s(v,w) : ℝ≥0∞)) ≤ M) (β : ℝ≥0)
    (hβ : (β : ℝ≥0∞) * M < 1) (o : V) (k : ℕ) :
    ∫⁻ ω, (clusterVol ω o) ^ k ∂(law (intensityProfile J β)) ≠ ⊤ := by
  let m := ((β : ℝ≥0∞) * M).toReal
  have hrow : UniformRowBound (intensityProfile J β) m :=
    uniformRowBound_intensityProfile J M hJ β hβ
  obtain ⟨lam, C, hlam, hC⟩ := exists_lam_envelope_intensityProfile J M hJ β hβ
  have hexp := lintegral_epow_cluster_le_of_envelope_bound hrow (lam := lam) o hlam.le hC
  have hfin : ∀ᵐ ω ∂(law (intensityProfile J β)), (cluster ω o).encard ≠ ⊤ :=
    ae_encard_cluster_ne_top_of_epow_le hlam hexp
  have hmom := lintegral_pow_encard_cluster_le hrow (lam := lam) o hlam hC k
  apply ne_of_lt
  calc ∫⁻ ω, (clusterVol ω o) ^ k ∂(law (intensityProfile J β))
      = ∫⁻ ω, ENNReal.ofReal (((cluster ω o).encard.toNat : ℝ) ^ k)
          ∂(law (intensityProfile J β)) := by
        apply lintegral_congr_ae
        filter_upwards [hfin] with ω hω
        rw [clusterVol_eq_encard]
        exact (ofReal_encard_toNat_pow (cluster ω o) hω k).symm
    _ ≤ ENNReal.ofReal (C * ((k.factorial : ℝ) / (Real.log lam) ^ k)) := hmom
    _ < ⊤ := ENNReal.ofReal_lt_top

/-- The first cluster-volume moment is finite under the same high-temperature
intensity-row bound. This exposes the `k = 1` case without specializing the
all-order consumer. No critical-range statement is implied. -/
theorem lintegral_clusterVol_intensity_ne_top (J : Sym2 V → ℝ≥0) (M : ℝ≥0)
    (hJ : ∀ v, (∑' w, if w = v then 0 else (J s(v,w) : ℝ≥0∞)) ≤ M) (β : ℝ≥0)
    (hβ : (β : ℝ≥0∞) * M < 1) (o : V) :
    ∫⁻ ω, clusterVol ω o ∂(law (intensityProfile J β)) ≠ ⊤ := by
  simpa using lintegral_clusterVol_intensity_pow_ne_top J M hJ β hβ o 1

/-- The natural moments under a compact nonzero interval of high-temperature
power-law intensities.  No statement at criticality is made. -/
theorem power_lintegral_clusterVol_pow_ne_top {d : ℕ} (hd : 1 ≤ d) {s : ℝ} (hs : (d : ℝ) < s)
    {J : Sym2 (Fin d → ℤ) → ℝ≥0}
    (hJ : ∀ x y : Fin d → ℤ, J s(x, y) = Real.toNNReal ((linfNorm (y - x) : ℝ) ^ (-s)))
    {β : ℝ≥0}
    (hβ : (β : ℝ≥0∞) *
      ((Real.toNNReal (∑' z : Fin d → ℤ, (linfNorm z : ℝ) ^ (-s)) : ℝ≥0) : ℝ≥0∞) < 1)
    (x : Fin d → ℤ) (k : ℕ) :
    ∫⁻ ω, (clusterVol ω x) ^ k ∂(law (intensityProfile J β)) ≠ ⊤ := by
  classical
  let M : ℝ≥0 := Real.toNNReal (∑' z : Fin d → ℤ, (linfNorm z : ℝ) ^ (-s))
  have hrows : ∀ v : Fin d → ℤ,
      (∑' w : Fin d → ℤ, @ite ℝ≥0∞ (w = v) (Classical.propDecidable _) 0
        (J s(v,w) : ℝ≥0∞)) ≤ M := by
    intro v
    exact (ENNReal.tsum_le_tsum fun w => by split_ifs <;> simp).trans
      (PercLib.CriticalLRP.PowerLawHighTemp.power_rowSum_le hd hs hJ v)
  exact lintegral_clusterVol_intensity_pow_ne_top J M hrows β hβ x k

end PercLib.CriticalLRP.Exploration.BFS
