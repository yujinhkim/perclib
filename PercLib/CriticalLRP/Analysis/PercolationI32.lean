/-
Migration source: https://github.com/yujinhkim/Critical-Long-range-percolation
Integration revision: 3b3d1d0e43ef940bfaa2292ee5c2ee094ac4edbf
Licence: Apache-2.0 for the PercLib Lean sources and tooling; see third_party/critical-lrp/.
External provenance and modifications are recorded in the file-specific notices below.
-/

/-
# The real restoration estimate on canonical cluster-volume laws
-/
module

public import PercLib.CriticalLRP.Analysis.PropositionI32
public import PercLib.CriticalLRP.Analysis.VolumeLaw

set_option linter.unusedSectionVars false
set_option linter.unusedSimpArgs false
set_option linter.unnecessarySimpa false
set_option linter.unusedTactic false
set_option linter.unusedVariables false

set_option autoImplicit true

@[expose] public section

open Filter Set MeasureTheory
open scoped Topology ENNReal

namespace PercLib.CriticalLRP
open PercLib.CriticalLRP.Analysis.I32

universe u
variable {V : Type*} [Countable V]

/-- A finite second moment makes the exponentially damped first moment integrable,
uniformly at any fixed positive damping rate. -/
theorem integrable_mul_exp_neg_of_secondMoment {μ : Measure ℝ} [IsProbabilityMeasure μ]
    {h : ℝ} (hh : 0 < h) (hμ : μ (Iio 0) = 0)
    (hsec : Integrable (fun x : ℝ => x ^ 2) μ) :
    Integrable (fun x : ℝ => x * Real.exp (-(h * x))) μ := by
  have hpoint : ∀ᵐ x ∂μ, 0 ≤ x := by
    filter_upwards [MeasureTheory.compl_mem_ae_iff.mpr hμ] with x hx
    simpa using hx
  have hf : AEStronglyMeasurable (fun x : ℝ => x * Real.exp (-(h * x))) μ := by fun_prop
  have hmajor : Integrable (fun x : ℝ => 1 + 1 / h + x ^ 2) μ :=
    (integrable_const (1 + 1 / h)).add hsec
  refine hmajor.mono' hf ?_
  filter_upwards [hpoint] with x hx
  have hprodnonneg : 0 ≤ h * x * Real.exp (-(h * x)) :=
    mul_nonneg (mul_nonneg hh.le hx) (Real.exp_pos _).le
  have hexpprod : h * x * Real.exp (-(h * x)) ≤ 1 := by
    have hlow := Real.add_one_le_exp (h * x)
    have hmul := mul_le_mul_of_nonneg_left hlow (Real.exp_pos (-(h * x))).le
    calc h * x * Real.exp (-(h * x))
        ≤ (h * x + 1) * Real.exp (-(h * x)) := by
          have he : 0 < Real.exp (-(h * x)) := Real.exp_pos _
          nlinarith
      _ ≤ Real.exp (h * x) * Real.exp (-(h * x)) := by simpa [mul_comm] using hmul
      _ = 1 := by rw [← Real.exp_add]; simp
  rw [Real.norm_eq_abs, abs_of_nonneg (mul_nonneg hx (Real.exp_pos _).le)]
  rcases le_total x h with hxh | hxh
  · have hbd : x * Real.exp (-(h * x)) ≤ 1 / h := by
      rw [le_div_iff₀ hh]
      calc x * Real.exp (-(h * x)) * h = h * x * Real.exp (-(h * x)) := by ring
        _ ≤ 1 := hexpprod
    linarith [sq_nonneg x]
  · have he : Real.exp (-(h * x)) ≤ 1 := by
      rw [Real.exp_le_one_iff]
      have hnonneg : 0 ≤ h * x := mul_nonneg hh.le hx
      linarith
    have hm := mul_le_mul_of_nonneg_left he hx
    have hxbound : x ≤ 1 + x ^ 2 := by nlinarith [sq_nonneg (x - 1)]
    have hinv : 0 ≤ 1 / h := by simpa [one_div] using inv_nonneg.mpr hh.le
    calc x * Real.exp (-(h * x)) ≤ x * 1 := hm
      _ = x := mul_one x
      _ ≤ 1 + x ^ 2 := hxbound
      _ ≤ 1 + 1 / h + x ^ 2 := by linarith

/-- Restore the real Laplace bridge on canonical volume laws from the accepted
summation theorem. The external factor is the full-law ghost-hit probability at
`o` (a translation-invariant model gives the needed inequality at every vertex). -/
theorem restoration_volumeLaw_of_degree (π ρ : Sym2 V → unitInterval)
    (hρπ : ∀ e : Sym2 V, ρ e ≤ π e) (o : V) {h : NNReal} (hh : 0 < h)
    {r C α : ℝ} (hr : 0 < r) (hC : 0 ≤ C) (hα : 0 ≤ α)
    (hfinρ : ∀ᵐ ω ∂(edgeMeasure ρ), clusterVol ω o ≠ ⊤)
    (hfinπ : ∀ᵐ ω ∂(edgeMeasure π), clusterVol ω o ≠ ⊤)
    (hintρ : Integrable (fun ω : Config V =>
      (clusterVol ω o).toReal * Real.exp (-(h : ℝ) * (clusterVol ω o).toReal))
      (edgeMeasure ρ))
    (hD : ∀ x : V, (∑' y : V, ENNReal.ofReal ((shiftProb π ρ (s(x, y)) : unitInterval) : ℝ))
      ≤ ENNReal.ofReal (C * r ^ (-α)))
    (hG : ∀ y : V, ghostHits π h y ≤ ghostHits π h o) :
    lapDefect (volumeLaw ρ o) (h : ℝ) ≤ lapDefect (volumeLaw π o) (h : ℝ) ∧
    lapDefect (volumeLaw π o) (h : ℝ) ≤ lapDefect (volumeLaw ρ o) (h : ℝ) +
      C * r ^ (-α) * (∫ x, x * Real.exp (-(h : ℝ) * x) ∂volumeLaw ρ o) *
        lapDefect (volumeLaw π o) (h : ℝ) := by
  have hrest := ghostHits_le_add_weightedGhostMass π ρ h hρπ hh o
    (ENNReal.ofReal (C * r ^ (-α))) (ghostHits π h o) hD hG
  have hwform := weightedGhostMass_eq_ofReal ρ h hh o hfinρ hintρ
  have hwne : weightedGhostMass ρ h o ≠ ⊤ := by rw [hwform]; exact ENNReal.ofReal_ne_top
  have hcutne : ghostHits ρ h o ≠ ⊤ := by
    unfold ghostHits; exact measure_ne_top _ _
  have hfullne : ghostHits π h o ≠ ⊤ := by
    unfold ghostHits; exact measure_ne_top _ _
  have hmulne : ENNReal.ofReal (C * r ^ (-α)) * weightedGhostMass ρ h o *
      ghostHits π h o ≠ ⊤ :=
    ENNReal.mul_ne_top (ENNReal.mul_ne_top ENNReal.ofReal_ne_top hwne) hfullne
  have hrhs : ghostHits ρ h o + ENNReal.ofReal (C * r ^ (-α)) *
      weightedGhostMass ρ h o * ghostHits π h o ≠ ⊤ :=
    ENNReal.add_ne_top.mpr ⟨hcutne, hmulne⟩
  have hreal : (ghostHits π h o).toReal ≤ (ghostHits ρ h o +
      ENNReal.ofReal (C * r ^ (-α)) * weightedGhostMass ρ h o * ghostHits π h o).toReal :=
    (ENNReal.toReal_le_toReal hfullne hrhs).2 hrest
  rw [ENNReal.toReal_add hcutne hmulne] at hreal
  have hdreal : (ENNReal.ofReal (C * r ^ (-α))).toReal = C * r ^ (-α) := by
    apply ENNReal.toReal_ofReal
    positivity
  rw [ENNReal.toReal_mul, ENNReal.toReal_mul, hdreal, hwform,
    ENNReal.toReal_ofReal (integral_nonneg_of_ae (Filter.Eventually.of_forall fun _ =>
      mul_nonneg ENNReal.toReal_nonneg (Real.exp_pos _).le))] at hreal
  have hlow := lapDefect_volumeLaw_eq_ghostHits ρ h hh o hfinρ
  have hhigh := lapDefect_volumeLaw_eq_ghostHits π h hh o hfinπ
  have hweight := integral_weighted_volumeLaw_eq_weightedGhostMass ρ h hh o hfinρ hintρ
  have hmono : ghostHits ρ h o ≤ ghostHits π h o := ghost_prob_mono hρπ h o
  have hmono' : (ghostHits ρ h o).toReal ≤ (ghostHits π h o).toReal :=
    (ENNReal.toReal_le_toReal hcutne hfullne).2 hmono
  have hwto : (weightedGhostMass ρ h o).toReal =
      ∫ ω, (clusterVol ω o).toReal * Real.exp (-(h : ℝ) * (clusterVol ω o).toReal)
        ∂edgeMeasure ρ := by
    rw [hwform]
    exact ENNReal.toReal_ofReal (integral_nonneg_of_ae (Filter.Eventually.of_forall fun _ =>
      mul_nonneg ENNReal.toReal_nonneg (Real.exp_pos _).le))
  rw [hlow, hhigh, hweight, hwto]
  exact ⟨hmono', hreal⟩

end PercLib.CriticalLRP

#print axioms PercLib.CriticalLRP.integrable_mul_exp_neg_of_secondMoment
#print axioms PercLib.CriticalLRP.restoration_volumeLaw_of_degree

namespace PercLib.CriticalLRP

open PercLib.CriticalLRP.Analysis PercLib.CriticalLRP.Analysis.I32

variable {V : Type*} [Countable V]

/-- The weighted exponential integrability transported from a volume law to configurations. -/
theorem integrable_volumeLaw_weighted_config (π : Sym2 V → unitInterval) (o : V)
    {h : NNReal} (hh : 0 < h)
    (hsec : Integrable (fun x : ℝ => x ^ 2) (volumeLaw π o)) :
    Integrable (fun ω : Config V =>
      (clusterVol ω o).toReal * Real.exp (-(h : ℝ) * (clusterVol ω o).toReal))
      (edgeMeasure π) := by
  have hm : Measurable (fun ω : Config V => (clusterVol ω o).toReal) :=
    ENNReal.measurable_toReal.comp (measurable_clusterVol o)
  have hg : AEStronglyMeasurable (fun x : ℝ => x * Real.exp (-(h : ℝ) * x))
      (volumeLaw π o) := by fun_prop
  have hb := integrable_mul_exp_neg_of_secondMoment (μ := volumeLaw π o) hh
    (volumeLaw_Iio_zero π o) hsec
  have hmapped : Integrable ((fun x : ℝ => x * Real.exp (-(h : ℝ) * x)) ∘
      (fun ω : Config V => (clusterVol ω o).toReal)) (edgeMeasure π) := by
    apply (integrable_map_measure hg hm.aemeasurable).mp
    simpa [volumeLaw] using hb
  exact hmapped

/-- **Proposition I.3.2 on canonical percolation volume laws.** The restoration
hypothesis is replaced by the actual monotone coupling, the source's restored-degree
row bound, and translation invariance of the full-law ghost probability. The first
and second moment hypotheses, weak convergence, the absence of a zero atom, and the
regularly varying promptly scale determine the exact `A3` MGF/tail constants. -/
theorem prop_I_3_2_volume_family (πinf : Sym2 V → unitInterval)
    (π : ℝ → Sym2 V → unitInterval) (o : V) (Qinf : Measure ℝ)
    {f : ℝ → ℝ} {a α A1 A2 C : ℝ}
    (ha : 0 < a) (hα : 0 < α) (hA1 : 0 < A1) (hA2 : 0 < A2) (hC : 0 < C)
    (hmeas : Measurable f) (hrv : RegularlyVaryingAtTop f (a * α))
    (hmono : ∀ r e, π r e ≤ πinf e)
    (hfin : ∀ r, ∀ᵐ ω ∂(edgeMeasure (π r)), clusterVol ω o ≠ ⊤)
    (hfininf : ∀ᵐ ω ∂(edgeMeasure πinf), clusterVol ω o ≠ ⊤)
    (hint1 : ∀ r, Integrable (fun x : ℝ => x) (volumeLaw (π r) o))
    (hint2 : ∀ r, Integrable (fun x : ℝ => x ^ 2) (volumeLaw (π r) o))
    (hEpos : ∀ r, 0 < mean (volumeLaw (π r) o))
    [∀ r, IsProbabilityMeasure (sizeBiasedLaw (volumeLaw (π r) o))]
    [IsProbabilityMeasure Qinf]
    (hQinf : Qinf (Iio 0) = 0) (hQinf0 : Qinf {(0 : ℝ)} = 0)
    (hconv : Tendsto (fun r => Measure.toProbabilityMeasure
      (sizeBiasedLaw (volumeLaw (π r) o))) atTop
      (𝓝 (Measure.toProbabilityMeasure Qinf)))
    (hE1 : Tendsto (fun r => mean (volumeLaw (π r) o) / (A1 * r ^ α)) atTop (𝓝 1))
    (hψ2 : Tendsto (fun r => sbMean (volumeLaw (π r) o) / (A2 * f r)) atTop (𝓝 1))
    (hD : ∀ᶠ r in atTop, ∀ x : V,
      (∑' y : V, ENNReal.ofReal ((shiftProb πinf (π r) (s(x, y)) : unitInterval) : ℝ))
        ≤ ENNReal.ofReal (C * r ^ (-α)))
    (hG : ∀ h : NNReal, ∀ y : V, ghostHits πinf h y ≤ ghostHits πinf h o) :
    ∃ A3 : ℝ, 0 < A3 ∧ Tendsto (A3cand A1 A2 a Qinf) atTop (𝓝 A3) ∧
      let D : RVPosData f (a * α) := RVPosData.of_moment (by positivity) hmeas hrv hA2
        (Filter.Eventually.of_forall fun r => I32Endpoint.sbMean_nonneg (hint2 r) (hEpos r)) hψ2
      Tendsto (fun h : ℝ => lapDefect (volumeLaw πinf o) h /
          (A3 * (D.genInv (1 / h) ^ α * h))) (𝓝[>] (0 : ℝ)) (𝓝 1) ∧
        Tendsto (fun x : ℝ => (volumeLaw πinf o (Ici x)).toReal /
          ((A3 / Real.Gamma (1 / a)) * (D.genInv x ^ α / x))) atTop (𝓝 1) := by
  let (r : ℝ) : IsProbabilityMeasure (volumeLaw (π r) o) :=
    isProbabilityMeasure_volumeLaw (π r) o
  have hprob : ∀ r, IsProbabilityMeasure (sizeBiasedLaw (volumeLaw (π r) o)) := by
    intro r
    exact inferInstance
  have hSpos : ∀ r, 0 < sbMean (volumeLaw (π r) o) := by
    intro r
    let : IsProbabilityMeasure (volumeLaw (π r) o) := isProbabilityMeasure_volumeLaw (π r) o
    apply lt_of_lt_of_le (hEpos r)
    exact I32Endpoint.mean_le_sbMean (μ := volumeLaw (π r) o)
      (volumeLaw_Iio_zero (π r) o) (hint1 r) (hint2 r) (hEpos r)
  have hI35 : ∀ᶠ r in atTop, ∀ h > 0,
      lapDefect (volumeLaw (π r) o) h ≤ lapDefect (volumeLaw πinf o) h ∧
      lapDefect (volumeLaw πinf o) h ≤ lapDefect (volumeLaw (π r) o) h +
        C * r ^ (-α) * (∫ x, x * Real.exp (-(h * x)) ∂(volumeLaw (π r) o)) *
          lapDefect (volumeLaw πinf o) h := by
    filter_upwards [hD, eventually_ge_atTop (1 : ℝ)] with r hrow hr
    intro h hh
    let h' : NNReal := ⟨h, hh.le⟩
    have hres := restoration_volumeLaw_of_degree (πinf) (π r) (hmono r) o (h := h') hh
      (lt_of_lt_of_le one_pos hr) hC.le hα.le (hfin r) hfininf
      (integrable_volumeLaw_weighted_config (π r) o hh (hint2 r))
      hrow (hG h')
    have hcoe : (h' : ℝ) = h := rfl
    simpa only [hcoe, neg_mul] using hres
  exact prop_I_3_2_of_restoration (fun r => volumeLaw (π r) o) (volumeLaw πinf o) Qinf
    ha hα hA1 hA2 hC hmeas hrv (fun r => isProbabilityMeasure_volumeLaw (π r) o)
    (fun r => volumeLaw_Iio_zero (π r) o) (volumeLaw_Iio_zero πinf o)
    hint1 hint2 hEpos hSpos hprob hQinf hQinf0 hconv hE1 hψ2 hI35

end PercLib.CriticalLRP

#print axioms PercLib.CriticalLRP.integrable_volumeLaw_weighted_config
#print axioms PercLib.CriticalLRP.prop_I_3_2_volume_family
