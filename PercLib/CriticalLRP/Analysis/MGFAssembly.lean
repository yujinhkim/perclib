/-
Migration source: https://github.com/yujinhkim/Critical-Long-range-percolation
Integration revision: 3b3d1d0e43ef940bfaa2292ee5c2ee094ac4edbf
Licence: Apache-2.0 for the PercLib Lean sources and tooling; see third_party/critical-lrp/.
External provenance and modifications are recorded in the file-specific notices below.
-/

/-
# Moving-scale MGF and ghost-restoration assembly for Proposition I.3.2

This module uses the infimum-based generalized inverse of an arbitrary measurable
regularly varying `f`; no order-isomorphism, monotonicity, or continuity hypothesis
is imposed on `f`.

The fixed-rate moving-scale cutoff limit has the exact source constant
`A1 * A2 ^ (-(1/a)) * λ ^ (-(a - 1)/a) * ∫ kern λ dQ∞`.
The full-law restoration estimate then supplies the ghost comparison and gives the
uncut MGF asymptotic, once the normalized large-rate limit defining `A3` is supplied.

That `A3`-limit existence and positivity is **not** claimed here. Nor is the final
percolation instantiation claimed: see the named hypotheses of
`mgf_of_fullLawGhostRatio` and `fullLawGhostRatio_of_restoration`.
-/
module

public import PercLib.CriticalLRP.Analysis.WeakKernels
public import PercLib.CriticalLRP.Analysis.VolumeTail

set_option linter.unusedSectionVars false
set_option linter.unusedSimpArgs false
set_option linter.unnecessarySimpa false
set_option linter.unusedTactic false
set_option linter.unusedVariables false

set_option autoImplicit true

@[expose] public section

open Filter Set MeasureTheory
open scoped Topology ENNReal

namespace PercLib.CriticalLRP.Analysis.I32

noncomputable section

/-- The Laplace defect `E[1 - e^{-h X}]`. -/
def lapDefect (mu : Measure ℝ) (h : ℝ) : ℝ := ∫ x, (1 - Real.exp (-(h * x))) ∂mu

theorem lapDefect_nonneg {mu : Measure ℝ} (hmu : mu (Iio 0) = 0) {h : ℝ} (hh : 0 < h) :
    0 ≤ lapDefect mu h := by
  unfold lapDefect
  refine integral_nonneg_of_ae ?_
  filter_upwards [ae_nonneg_of_Iio hmu] with x hx
  have h2 : Real.exp (-(h * x)) ≤ 1 := by
    rw [Real.exp_le_one_iff]
    nlinarith
  exact sub_nonneg.mpr h2

/-- **The separated full-law ghost input.**  This is the ratio form of the
full-law restoration estimate (I.3.1), i.e. the content of the source's
(I.3.5)--(I.3.6), transported to the level-filled scale
`r_λ(h) = g (λ / (A₂ h))`: for every tolerance `η` there is a rate threshold `Λ`
such that for every `λ ≥ Λ` the uncut and cut-off Laplace defects at that scale
compare within the factor `(1-η)⁻¹`.

It is derived below in `fullLawGhostRatio_of_restoration` from the full-law
restoration estimate. It remains an interface rather than a disguised assumption
in the MGF theorem, making the remaining probabilistic obligation precise. -/
def FullLawGhostRatio (muinf : Measure ℝ) (mu : ℝ → Measure ℝ) (g : ℝ → ℝ) (A2 : ℝ) : Prop :=
  ∀ η : ℝ, 0 < η → η ≤ 1 / 2 → ∃ Λ : ℝ, 0 < Λ ∧ ∀ lam : ℝ, Λ ≤ lam →
    ∀ᶠ h : ℝ in 𝓝[>] (0 : ℝ),
      lapDefect (mu (g (lam / (A2 * h)))) h ≤ lapDefect muinf h ∧
      lapDefect muinf h ≤ lapDefect (mu (g (lam / (A2 * h)))) h * (1 - η)⁻¹

end

end PercLib.CriticalLRP.Analysis.I32

namespace PercLib.CriticalLRP.Analysis.I32

noncomputable section

/-- **Stage 1 at the source's moving scale**, for a fixed rate `λ`.

With `r_λ(h) = g (λ / (A₂ h))` the generalized inverse of `f` at the level-filled
argument, the cut-off Laplace defect satisfies

  `E_{μ_{r_λ(h)}}[1 - e^{-h|K|}] / (g(1/h)^α h)`
      `→ (A₁ ∫ (1-e^{-λy})/y dQ_∞ / λ) * (λ/A₂)^(1/a)`.

The four factors are exactly the four source limits: the first moment ratio, the
level-filled rate `h Ê_r → λ`, the weak limit of the size-biased kernel integrals,
and the inverse-scaling ratio `(r_λ(h))^α / g(1/h)^α → (λ/A₂)^(1/a)`.

No exact order-inverse cancellation is used: `r_λ(h)` is *not* assumed to equal
`g(1/h)`, only the regularly varying ratio law is applied. -/
theorem cutoff_defect_ratio
    (mu : ℝ → Measure ℝ) (Qinf : Measure ℝ)
    {f : ℝ → ℝ} {ρ : ℝ} (D : RVPosData f ρ)
    (hmu : ∀ r, mu r (Iio 0) = 0)
    (hEpos : ∀ r, 0 < mean (mu r))
    (hSpos : ∀ r, 0 < sbMean (mu r))
    (hprob : ∀ r, IsProbabilityMeasure (sizeBiasedLaw (mu r)))
    [IsProbabilityMeasure Qinf]
    (hQinf : Qinf (Iio 0) = 0) (hQinf0 : Qinf {(0 : ℝ)} = 0)
    (hconv : Tendsto (fun r => Measure.toProbabilityMeasure (sizeBiasedLaw (mu r))) atTop
      (𝓝 (Measure.toProbabilityMeasure Qinf)))
    {A1 A2 a α : ℝ} (hA1 : 0 < A1) (hA2 : 0 < A2) (ha : 0 < a) (hα : 0 < α)
    (hρα : ρ = a * α)
    (hE1 : Tendsto (fun r => mean (mu r) / (A1 * r ^ α)) atTop (𝓝 1))
    (hψdiv : Tendsto (fun r => sbMean (mu r) / f r) atTop (𝓝 A2))
    {lam : ℝ} (hlam : 0 < lam) :
    Tendsto (fun h : ℝ =>
        (∫ x, (1 - Real.exp (-(h * x))) ∂(mu (D.genInv (lam / (A2 * h)))))
          / (D.genInv (1 / h) ^ α * h)) (𝓝[>] (0 : ℝ))
      (𝓝 ((A1 * (∫ y, kern lam y ∂Qinf) / lam) * ((lam / A2) ^ (1 / a)))) := by
  have hrfun : Tendsto (fun h : ℝ => D.genInv (lam / (A2 * h))) (𝓝[>] (0 : ℝ)) atTop :=
    D.tendsto_genInv_atTop.comp (tendsto_level_arg hA2 hlam)
  have hrate : Tendsto (fun h : ℝ => h * sbMean (mu (D.genInv (lam / (A2 * h)))))
      (𝓝[>] (0 : ℝ)) (𝓝 lam) :=
    D.tendsto_level_filled_of_tendsto_div (f := f) hA2 hlam hψdiv
  have hker : Tendsto (fun h : ℝ =>
      ∫ y, kern (h * sbMean (mu (D.genInv (lam / (A2 * h))))) y
        ∂(sizeBiasedLaw (mu (D.genInv (lam / (A2 * h))))) ) (𝓝[>] (0 : ℝ))
      (𝓝 (∫ y, kern lam y ∂Qinf)) := by
    have hmain := I32Weak.tendsto_integral_kern_comp (L := atTop) (L' := 𝓝[>] (0 : ℝ))
      (Qr := fun r => Measure.toProbabilityMeasure (sizeBiasedLaw (mu r)))
      (Q := Measure.toProbabilityMeasure Qinf) hconv
      (fun r => by
        simp only [Measure.coe_toProbabilityMeasure]
        exact sizeBiasedLaw_Iio_zero (hmu r) (hSpos r))
      (fun r => by
        simp only [Measure.coe_toProbabilityMeasure]
        exact I32Weak.sizeBiasedLaw_singleton_zero (hSpos r).ne')
      (by simp only [Measure.coe_toProbabilityMeasure]; exact hQinf)
      (by simp only [Measure.coe_toProbabilityMeasure]; exact hQinf0)
      hrfun hrate hlam
    simpa only [Measure.coe_toProbabilityMeasure] using hmain
  have hscale := D.tendsto_level_normalization (f := f) ha hα hρα hA2 hlam
  have hE1c : Tendsto (fun h : ℝ =>
      mean (mu (D.genInv (lam / (A2 * h)))) / (A1 * (D.genInv (lam / (A2 * h))) ^ α))
      (𝓝[>] (0 : ℝ)) (𝓝 1) := hE1.comp hrfun
  have hA2c : Tendsto (fun h : ℝ =>
      A1 / (h * sbMean (mu (D.genInv (lam / (A2 * h)))))) (𝓝[>] (0 : ℝ)) (𝓝 (A1 / lam)) :=
    tendsto_const_nhds.div hrate hlam.ne'
  have hprod := (((hE1c.mul hA2c).mul hker).mul hscale)
  have hval : (1 * (A1 / lam) * (∫ y, kern lam y ∂Qinf)) * ((lam / A2) ^ (1 / a))
      = (A1 * (∫ y, kern lam y ∂Qinf) / lam) * ((lam / A2) ^ (1 / a)) := by ring
  rw [hval] at hprod
  refine hprod.congr' ?_
  filter_upwards [self_mem_nhdsWithin] with h hh
  have hh0 : 0 < h := hh
  have hrpos : 0 < D.genInv (lam / (A2 * h)) := D.genInv_pos _
  have hgpos : 0 < D.genInv (1 / h) := D.genInv_pos _
  have hS : sbMean (mu (D.genInv (lam / (A2 * h)))) ≠ 0 := (hSpos _).ne'
  have hEm : mean (mu (D.genInv (lam / (A2 * h)))) ≠ 0 := (hEpos _).ne'
  have hA1ne : A1 ≠ 0 := hA1.ne'
  have hrp : D.genInv (lam / (A2 * h)) ^ α ≠ 0 := (Real.rpow_pos_of_pos hrpos α).ne'
  have hgp : D.genInv (1 / h) ^ α ≠ 0 := (Real.rpow_pos_of_pos hgpos α).ne'
  have hlap := laplace_eq_sizeBiased (mu := mu (D.genInv (lam / (A2 * h))))
    (hmu (D.genInv (lam / (A2 * h)))) (hEpos _) (hSpos _) h
  show (mean (mu (D.genInv (lam / (A2 * h)))) / (A1 * D.genInv (lam / (A2 * h)) ^ α))
      * (A1 / (h * sbMean (mu (D.genInv (lam / (A2 * h))))))
      * (∫ y, kern (h * sbMean (mu (D.genInv (lam / (A2 * h))))) y
          ∂(sizeBiasedLaw (mu (D.genInv (lam / (A2 * h))))))
      * (D.genInv (lam / (A2 * h)) ^ α / D.genInv (1 / h) ^ α)
    = (∫ x, (1 - Real.exp (-(h * x))) ∂(mu (D.genInv (lam / (A2 * h)))))
      / (D.genInv (1 / h) ^ α * h)
  rw [hlap]
  field_simp

end

end PercLib.CriticalLRP.Analysis.I32

namespace PercLib.CriticalLRP.Analysis.I32

noncomputable section

/-- The constant bookkeeping: the fixed-rate Stage 1 answer `A₁ J / λ` times the
inverse-scaling factor `(λ/A₂)^(1/a)` is the source's
`(A₁/A₂^{1/a}) λ^{-(a-1)/a} J`. -/
theorem const_eq {A1 A2 a lam J : ℝ} (hA2 : 0 < A2) (hlam : 0 < lam) (ha : 0 < a) :
    (A1 * J / lam) * (lam / A2) ^ (1 / a)
      = A1 * A2 ^ (-(1 / a)) * lam ^ (-(a - 1) / a) * J := by
  have h1 : lam ^ (-(a - 1) / a) = lam ^ (1 / a) / lam := by
    rw [show -(a - 1) / a = 1 / a - 1 by field_simp; ring, Real.rpow_sub hlam, Real.rpow_one]
  rw [Real.div_rpow hlam.le hA2.le, Real.rpow_neg hA2.le, h1]
  field_simp

/-- **Stage 1 at the source's moving scale, in the source's constant form.**
See `cutoff_defect_ratio`; here the limit is written as
`A₁ A₂^{-1/a} λ^{-(a-1)/a} ∫ (1-e^{-λy})/y dQ_∞`, which is the bracket of (I.3.7). -/
theorem cutoff_defect_ratio_source
    (mu : ℝ → Measure ℝ) (Qinf : Measure ℝ)
    {f : ℝ → ℝ} {ρ : ℝ} (D : RVPosData f ρ)
    (hmu : ∀ r, mu r (Iio 0) = 0)
    (hEpos : ∀ r, 0 < mean (mu r))
    (hSpos : ∀ r, 0 < sbMean (mu r))
    (hprob : ∀ r, IsProbabilityMeasure (sizeBiasedLaw (mu r)))
    [IsProbabilityMeasure Qinf]
    (hQinf : Qinf (Iio 0) = 0) (hQinf0 : Qinf {(0 : ℝ)} = 0)
    (hconv : Tendsto (fun r => Measure.toProbabilityMeasure (sizeBiasedLaw (mu r))) atTop
      (𝓝 (Measure.toProbabilityMeasure Qinf)))
    {A1 A2 a α : ℝ} (hA1 : 0 < A1) (hA2 : 0 < A2) (ha : 0 < a) (hα : 0 < α)
    (hρα : ρ = a * α)
    (hE1 : Tendsto (fun r => mean (mu r) / (A1 * r ^ α)) atTop (𝓝 1))
    (hψdiv : Tendsto (fun r => sbMean (mu r) / f r) atTop (𝓝 A2))
    {lam : ℝ} (hlam : 0 < lam) :
    Tendsto (fun h : ℝ =>
        (∫ x, (1 - Real.exp (-(h * x))) ∂(mu (D.genInv (lam / (A2 * h)))))
          / (D.genInv (1 / h) ^ α * h)) (𝓝[>] (0 : ℝ))
      (𝓝 (A1 * A2 ^ (-(1 / a)) * lam ^ (-(a - 1) / a)
        * (∫ y, kern lam y ∂Qinf))) := by
  have hmain := cutoff_defect_ratio mu Qinf D hmu hEpos hSpos hprob hQinf hQinf0 hconv
    hA1 hA2 ha hα hρα hE1 hψdiv hlam
  have hval : (A1 * (∫ y, kern lam y ∂Qinf) / lam) * ((lam / A2) ^ (1 / a))
      = A1 * A2 ^ (-(1 / a)) * lam ^ (-(a - 1) / a) * (∫ y, kern lam y ∂Qinf) :=
    const_eq hA2 hlam ha
  rwa [hval] at hmain

end

end PercLib.CriticalLRP.Analysis.I32


namespace PercLib.CriticalLRP.Analysis.I32

noncomputable section

/-- The full-law ghost comparison transfers the moving-scale cutoff limits to the uncut
law. This is the analytic assembly following (I.3.6) and (I.3.7); the probabilistic
restoration estimate is isolated in `FullLawGhostRatio`. -/
theorem mgf_of_fullLawGhostRatio
    (mu : ℝ → Measure ℝ) (muinf : Measure ℝ) (Qinf : Measure ℝ)
    {f : ℝ → ℝ} {ρ : ℝ} (D : RVPosData f ρ)
    (hmu : ∀ r, mu r (Iio 0) = 0)
    (_hmuinf : muinf (Iio 0) = 0)
    (hEpos : ∀ r, 0 < mean (mu r))
    (hSpos : ∀ r, 0 < sbMean (mu r))
    (hprob : ∀ r, IsProbabilityMeasure (sizeBiasedLaw (mu r)))
    [IsProbabilityMeasure Qinf]
    (hQinf : Qinf (Iio 0) = 0) (hQinf0 : Qinf {(0 : ℝ)} = 0)
    (hconv : Tendsto (fun r => Measure.toProbabilityMeasure (sizeBiasedLaw (mu r))) atTop
      (𝓝 (Measure.toProbabilityMeasure Qinf)))
    {A1 A2 a α A3 : ℝ} (hA1 : 0 < A1) (hA2 : 0 < A2) (ha : 0 < a) (hα : 0 < α)
    (hρα : ρ = a * α)
    (hE1 : Tendsto (fun r => mean (mu r) / (A1 * r ^ α)) atTop (𝓝 1))
    (hψdiv : Tendsto (fun r => sbMean (mu r) / f r) atTop (𝓝 A2))
    (hJlim : Tendsto (fun lam => A1 * A2 ^ (-(1 / a)) * lam ^ (-(a - 1) / a)
      * (∫ y, kern lam y ∂Qinf)) atTop (𝓝 A3))
    (hGhost : FullLawGhostRatio muinf mu D.genInv A2) :
    Tendsto (fun h : ℝ => lapDefect muinf h / (D.genInv (1 / h) ^ α * h))
      (𝓝[>] (0 : ℝ)) (𝓝 A3) := by
  classical
  rw [Metric.tendsto_nhds]
  intro ε hε
  obtain ⟨ε', hε'0, hε'1, hε'ε⟩ : ∃ ε' : ℝ, 0 < ε' ∧ ε' ≤ 1 ∧ ε' < ε :=
    ⟨min (ε / 2) 1, lt_min (by linarith) one_pos, min_le_right _ _,
      lt_of_le_of_lt (min_le_left _ _) (by linarith)⟩
  let η : ℝ := min (1 / 2) (ε' / (16 * (|A3| + 1)))
  have hη0 : 0 < η := by dsimp [η]; positivity
  have hηhalf : η ≤ 1 / 2 := min_le_left _ _
  have hηbound : 2 * η * (|A3| + 1) ≤ ε' / 4 := by
    have hηle : η ≤ ε' / (16 * (|A3| + 1)) := min_le_right _ _
    have hnonneg : (0 : ℝ) ≤ 2 * (|A3| + 1) := by positivity
    have hmul := mul_le_mul_of_nonneg_right hηle hnonneg
    have hcalc : 2 * (ε' / (16 * (|A3| + 1))) * (|A3| + 1) = ε' / 8 := by
      have hne : |A3| + 1 ≠ 0 := by positivity
      field_simp
      ring
    dsimp [η] at hcalc ⊢
    linarith [hmul]
  obtain ⟨Λ, hΛ0, hΛ⟩ := hGhost η hη0 hηhalf
  have hJε : ∀ᶠ lam in atTop,
      |A1 * A2 ^ (-(1 / a)) * lam ^ (-(a - 1) / a)
        * (∫ y, kern lam y ∂Qinf) - A3| ≤ ε' / 4 := by
    have h := hJlim.eventually (Metric.ball_mem_nhds A3 (by positivity : 0 < ε' / 4))
    filter_upwards [h] with lam hl
    rw [Real.dist_eq] at hl
    exact hl.le
  obtain ⟨Λ1, hΛ1⟩ := eventually_atTop.1 hJε
  let lam : ℝ := max (max Λ Λ1) 1
  have hlamΛ : Λ ≤ lam := le_trans (le_max_left _ _) (le_max_left _ _)
  have hlamΛ1 : Λ1 ≤ lam := le_trans (le_max_right _ _) (le_max_left _ _)
  have hlam1 : (1 : ℝ) ≤ lam := le_max_right _ _
  have hlam0 : 0 < lam := lt_of_lt_of_le one_pos hlam1
  let c : ℝ := A1 * A2 ^ (-(1 / a)) * lam ^ (-(a - 1) / a)
    * (∫ y, kern lam y ∂Qinf)
  have hcA : |c - A3| ≤ ε' / 4 := hΛ1 lam hlamΛ1
  have hcut := cutoff_defect_ratio_source mu Qinf D hmu hEpos hSpos hprob
    hQinf hQinf0 hconv hA1 hA2 ha hα hρα hE1 hψdiv hlam0
  have hcut' : Tendsto (fun h : ℝ =>
      lapDefect (mu (D.genInv (lam / (A2 * h)))) h /
        (D.genInv (1 / h) ^ α * h)) (𝓝[>] (0 : ℝ)) (𝓝 c) := by
    simpa only [lapDefect, c] using hcut
  have hYclo : ∀ᶠ h in 𝓝[>] (0 : ℝ),
      |lapDefect (mu (D.genInv (lam / (A2 * h)))) h /
        (D.genInv (1 / h) ^ α * h) - c| ≤ ε' / 4 := by
    have h := hcut'.eventually (Metric.ball_mem_nhds c (by positivity : 0 < ε' / 4))
    filter_upwards [h] with x hx
    rw [Real.dist_eq] at hx
    exact hx.le
  have hgh : ∀ᶠ h in 𝓝[>] (0 : ℝ),
      lapDefect (mu (D.genInv (lam / (A2 * h)))) h ≤ lapDefect muinf h ∧
      lapDefect muinf h ≤ lapDefect (mu (D.genInv (lam / (A2 * h)))) h * (1 - η)⁻¹ :=
    hΛ lam hlamΛ
  have hηinv : (1 - η)⁻¹ ≤ 1 + 2 * η := by
    rw [inv_eq_one_div, div_le_iff₀ (by linarith : (0 : ℝ) < 1 - η)]
    nlinarith
  filter_upwards [hYclo, hgh, self_mem_nhdsWithin] with h hY hcomp hh
  have hh0 : 0 < h := hh
  have hW : 0 < D.genInv (1 / h) ^ α * h :=
    mul_pos (Real.rpow_pos_of_pos (D.genInv_pos _) _) hh0
  have hLnn : 0 ≤ lapDefect (mu (D.genInv (lam / (A2 * h)))) h :=
    lapDefect_nonneg (hmu _) hh0
  have hYnn : 0 ≤ lapDefect (mu (D.genInv (lam / (A2 * h)))) h /
      (D.genInv (1 / h) ^ α * h) := div_nonneg hLnn hW.le
  have hlow : lapDefect (mu (D.genInv (lam / (A2 * h)))) h /
      (D.genInv (1 / h) ^ α * h) ≤ lapDefect muinf h / (D.genInv (1 / h) ^ α * h) :=
    (div_le_div_iff_of_pos_right hW).mpr hcomp.1
  have hupp : lapDefect muinf h / (D.genInv (1 / h) ^ α * h) ≤
      (lapDefect (mu (D.genInv (lam / (A2 * h)))) h /
        (D.genInv (1 / h) ^ α * h)) * (1 + 2 * η) := by
    calc lapDefect muinf h / (D.genInv (1 / h) ^ α * h)
        ≤ (lapDefect (mu (D.genInv (lam / (A2 * h)))) h * (1 - η)⁻¹) /
          (D.genInv (1 / h) ^ α * h) :=
          (div_le_div_iff_of_pos_right hW).mpr hcomp.2
      _ = (lapDefect (mu (D.genInv (lam / (A2 * h)))) h /
          (D.genInv (1 / h) ^ α * h)) * (1 - η)⁻¹ := by ring
      _ ≤ (lapDefect (mu (D.genInv (lam / (A2 * h)))) h /
          (D.genInv (1 / h) ^ α * h)) * (1 + 2 * η) :=
          mul_le_mul_of_nonneg_left hηinv hYnn
  have hYlo : c - ε' / 4 ≤ lapDefect (mu (D.genInv (lam / (A2 * h)))) h /
      (D.genInv (1 / h) ^ α * h) := by
    have habs := abs_le.mp hY
    linarith
  have hYhi : lapDefect (mu (D.genInv (lam / (A2 * h)))) h /
      (D.genInv (1 / h) ^ α * h) ≤ c + ε' / 4 := by
    have habs := abs_le.mp hY
    linarith
  have hcLo : A3 - ε' / 4 ≤ c := by
    have habs := abs_le.mp hcA
    linarith
  have hcHi : c ≤ A3 + ε' / 4 := by
    have habs := abs_le.mp hcA
    linarith
  have hsmall : c + ε' / 4 ≤ |A3| + 1 := by
    have habs := abs_le.mp hcA
    have hle := le_abs_self A3
    linarith
  have hmul : 2 * η * (c + ε' / 4) ≤ ε' / 4 :=
    le_trans (mul_le_mul_of_nonneg_left hsmall (by linarith : (0 : ℝ) ≤ 2 * η)) hηbound
  rw [Real.dist_eq, abs_lt]
  constructor
  · linarith
  · have hfactor : (c + ε' / 4) * (1 + 2 * η) ≤ A3 + ε' := by
      calc (c + ε' / 4) * (1 + 2 * η)
          = (c + ε' / 4) + 2 * η * (c + ε' / 4) := by ring
        _ ≤ (A3 + ε' / 4 + ε' / 4) + ε' / 4 := by linarith
        _ ≤ A3 + ε' := by linarith
    have hscale : (lapDefect (mu (D.genInv (lam / (A2 * h)))) h /
        (D.genInv (1 / h) ^ α * h)) * (1 + 2 * η) ≤
        (c + ε' / 4) * (1 + 2 * η) :=
      mul_le_mul_of_nonneg_right hYhi (by positivity)
    linarith

end

end PercLib.CriticalLRP.Analysis.I32



namespace PercLib.CriticalLRP.Analysis.I32

noncomputable section

/-- The original restoration inequality, with its full-law external ghost-hit factor,
implies the ratio interface used in the MGF assembly. The exponential control comes
from weak convergence at the level-filled moving rate, not from an added uniform moment
hypothesis. -/
theorem fullLawGhostRatio_of_restoration
    (mu : ℝ → Measure ℝ) (muinf : Measure ℝ) (Qinf : Measure ℝ)
    {f : ℝ → ℝ} {ρ : ℝ} (D : RVPosData f ρ)
    (hmu : ∀ r, mu r (Iio 0) = 0) (hmuinf : muinf (Iio 0) = 0)
    (hEpos : ∀ r, 0 < mean (mu r)) (hSpos : ∀ r, 0 < sbMean (mu r))
    (hprob : ∀ r, IsProbabilityMeasure (sizeBiasedLaw (mu r)))
    [IsProbabilityMeasure Qinf] (hQinf0 : Qinf {(0 : ℝ)} = 0)
    (hconv : Tendsto (fun r => Measure.toProbabilityMeasure (sizeBiasedLaw (mu r))) atTop
      (𝓝 (Measure.toProbabilityMeasure Qinf)))
    {A1 A2 α C : ℝ} (hA1 : 0 < A1) (hA2 : 0 < A2) (_hα : 0 < α) (hC : 0 < C)
    (hE1 : Tendsto (fun r => mean (mu r) / (A1 * r ^ α)) atTop (𝓝 1))
    (hψdiv : Tendsto (fun r => sbMean (mu r) / f r) atTop (𝓝 A2))
    (hI35 : ∀ᶠ r in atTop, ∀ h > 0,
      lapDefect (mu r) h ≤ lapDefect muinf h ∧
      lapDefect muinf h ≤ lapDefect (mu r) h +
        C * r ^ (-α) * (∫ x, x * Real.exp (-(h * x)) ∂(mu r)) * lapDefect muinf h) :
    FullLawGhostRatio muinf mu D.genInv A2 := by
  classical
  intro η hη hηhalf
  obtain ⟨η', hη'0, hη'half, hη'le⟩ : ∃ η' : ℝ, 0 < η' ∧ η' ≤ 1 / 2 ∧ η' ≤ η :=
    ⟨min η (1 / 2), lt_min hη (by norm_num), min_le_right _ _, min_le_left _ _⟩
  let T : ℝ := η' / (8 * (C * A1))
  have hT0 : 0 < T := by dsimp [T]; positivity
  have hexp0 := I32Weak.tendsto_integral_exp_abs_atTop (Q := Qinf) hQinf0
  have hexpsmall : ∀ᶠ lam in atTop,
      (∫ y, Real.exp (-(lam * |y|)) ∂Qinf) ≤ T / 2 := by
    have h := hexp0.eventually (Metric.ball_mem_nhds 0 (by positivity : 0 < T / 2))
    filter_upwards [h] with lam hl
    rw [Real.dist_eq, sub_zero] at hl
    have hnn : 0 ≤ ∫ y, Real.exp (-(lam * |y|)) ∂Qinf := integral_nonneg fun y => (Real.exp_pos _).le
    have habs : |∫ y, Real.exp (-(lam * |y|)) ∂Qinf| =
        ∫ y, Real.exp (-(lam * |y|)) ∂Qinf := abs_of_nonneg hnn
    rw [habs] at hl
    exact hl.le
  obtain ⟨Λ0, hΛ0⟩ := eventually_atTop.1 hexpsmall
  refine ⟨max Λ0 1, lt_of_lt_of_le one_pos (le_max_right _ _), ?_⟩
  intro lam hlam
  have hlam1 : (1 : ℝ) ≤ lam := le_trans (le_max_right _ _) hlam
  have hlam0 : 0 < lam := lt_of_lt_of_le one_pos hlam1
  have hlarge : Λ0 ≤ lam := le_trans (le_max_left _ _) hlam
  have hJs0 : (∫ y, Real.exp (-(lam * |y|)) ∂Qinf) ≤ T / 2 := hΛ0 lam hlarge
  have hrfun : Tendsto (fun h : ℝ => D.genInv (lam / (A2 * h))) (𝓝[>] (0 : ℝ)) atTop :=
    D.tendsto_genInv_atTop.comp (tendsto_level_arg hA2 hlam0)
  have hrate : Tendsto (fun h : ℝ => h * sbMean (mu (D.genInv (lam / (A2 * h)))))
      (𝓝[>] (0 : ℝ)) (𝓝 lam) :=
    D.tendsto_level_filled_of_tendsto_div (f := f) hA2 hlam0 hψdiv
  have hEbd : ∀ᶠ h : ℝ in 𝓝[>] (0 : ℝ),
      0 < D.genInv (lam / (A2 * h)) ∧
      mean (mu (D.genInv (lam / (A2 * h)))) /
        (A1 * (D.genInv (lam / (A2 * h))) ^ α) ≤ 2 := by
    have hb := hE1.eventually (eventually_le_nhds (by norm_num : (1 : ℝ) < 2))
    filter_upwards [hrfun.eventually hb, Filter.Eventually.of_forall (fun h => D.genInv_pos
      (lam / (A2 * h)))] with h hmean hr
    exact ⟨hr, hmean⟩
  have hexpbase := I32Weak.tendsto_integral_exp_abs_of_tendsto_rate (L := 𝓝[>] (0 : ℝ))
    (Qr := fun h => Measure.toProbabilityMeasure (sizeBiasedLaw
      (mu (D.genInv (lam / (A2 * h)))))) (Q := Measure.toProbabilityMeasure Qinf)
    (hconv.comp hrfun) hrate hlam0
  have hexpconv : ∀ᶠ h : ℝ in 𝓝[>] (0 : ℝ),
      (∫ y, Real.exp (-(h * sbMean (mu (D.genInv (lam / (A2 * h)))) * |y|))
        ∂(sizeBiasedLaw (mu (D.genInv (lam / (A2 * h)))))) ≤ T := by
    have ht : (0 : ℝ) < T - T / 2 := by linarith
    have h := hexpbase.eventually (Metric.ball_mem_nhds _ ht)
    simp only [Measure.coe_toProbabilityMeasure] at h
    filter_upwards [h] with h hh
    rw [Real.dist_eq] at hh
    have hl := (abs_lt.mp hh).2
    linarith
  have hI35' := hrfun.eventually hI35
  filter_upwards [hI35', hEbd, hexpconv, self_mem_nhdsWithin] with h hrest hEr hJ hh
  have hh0 : 0 < h := hh
  have hrpos : 0 < D.genInv (lam / (A2 * h)) := hEr.1
  have hEratio := hEr.2
  have hrpow : 0 < (D.genInv (lam / (A2 * h))) ^ α := Real.rpow_pos_of_pos hrpos α
  have hmean_le : mean (mu (D.genInv (lam / (A2 * h)))) ≤
      2 * (A1 * (D.genInv (lam / (A2 * h))) ^ α) := by
    rw [div_le_iff₀ (mul_pos hA1 hrpow)] at hEratio
    linarith
  have hmean_scale : mean (mu (D.genInv (lam / (A2 * h)))) *
      (D.genInv (lam / (A2 * h))) ^ (-α) ≤ 2 * A1 := by
    rw [Real.rpow_neg hrpos.le, ← div_eq_mul_inv, div_le_iff₀ hrpow]
    linarith
  have hexpform : (∫ y, Real.exp (-(h * sbMean (mu (D.genInv (lam / (A2 * h)))) * y))
        ∂(sizeBiasedLaw (mu (D.genInv (lam / (A2 * h)))))) ≤ T := by
    calc (∫ y, Real.exp (-(h * sbMean (mu (D.genInv (lam / (A2 * h)))) * y))
          ∂(sizeBiasedLaw (mu (D.genInv (lam / (A2 * h))))))
        = ∫ y, Real.exp (-(h * sbMean (mu (D.genInv (lam / (A2 * h)))) * |y|))
          ∂(sizeBiasedLaw (mu (D.genInv (lam / (A2 * h))))) := by
          apply integral_congr_ae
          filter_upwards [ae_nonneg_of_Iio (sizeBiasedLaw_Iio_zero (hmu _) (hSpos _))] with y hy
          rw [abs_of_nonneg hy]
      _ ≤ T := hJ
  have hJnn : 0 ≤ ∫ y, Real.exp (-(h * sbMean (mu (D.genInv (lam / (A2 * h)))) * y))
      ∂(sizeBiasedLaw (mu (D.genInv (lam / (A2 * h))))) :=
    integral_nonneg fun y => (Real.exp_pos _).le
  have hstepRest := (hrest h hh0).2
  rw [exp_eq_sizeBiased (hmu _) (hEpos _) (hSpos _)] at hstepRest
  have hcorr : C * (D.genInv (lam / (A2 * h))) ^ (-α) *
      (mean (mu (D.genInv (lam / (A2 * h)))) *
        (∫ y, Real.exp (-(h * sbMean (mu (D.genInv (lam / (A2 * h)))) * y))
          ∂(sizeBiasedLaw (mu (D.genInv (lam / (A2 * h))))))) ≤ η' / 4 := by
    have hfac : C * (mean (mu (D.genInv (lam / (A2 * h)))) *
        (D.genInv (lam / (A2 * h))) ^ (-α)) ≤ C * (2 * A1) :=
      mul_le_mul_of_nonneg_left (by simpa [mul_comm] using hmean_scale) hC.le
    calc C * (D.genInv (lam / (A2 * h))) ^ (-α) *
        (mean (mu (D.genInv (lam / (A2 * h)))) *
          (∫ y, Real.exp (-(h * sbMean (mu (D.genInv (lam / (A2 * h)))) * y))
            ∂(sizeBiasedLaw (mu (D.genInv (lam / (A2 * h)))))))
        = (C * (mean (mu (D.genInv (lam / (A2 * h)))) *
            (D.genInv (lam / (A2 * h))) ^ (-α))) *
          (∫ y, Real.exp (-(h * sbMean (mu (D.genInv (lam / (A2 * h)))) * y))
            ∂(sizeBiasedLaw (mu (D.genInv (lam / (A2 * h)))))) := by ring
      _ ≤ (C * (2 * A1)) * T :=
        mul_le_mul hfac hexpform hJnn (by positivity)
      _ = η' / 4 := by dsimp [T]; field_simp; ring
  have hlinf_nonneg : 0 ≤ lapDefect muinf h := lapDefect_nonneg hmuinf hh0
  have hmul := mul_le_mul_of_nonneg_right hcorr hlinf_nonneg
  have hkey : lapDefect muinf h * (1 - η') ≤
      lapDefect (mu (D.genInv (lam / (A2 * h)))) h := by
    have hset : (1 - η' / 4) * lapDefect muinf h ≤
        lapDefect (mu (D.genInv (lam / (A2 * h)))) h := by
      calc (1 - η' / 4) * lapDefect muinf h
          = lapDefect muinf h - (η' / 4) * lapDefect muinf h := by ring
        _ ≤ lapDefect muinf h - (C * (D.genInv (lam / (A2 * h))) ^ (-α) *
            (mean (mu (D.genInv (lam / (A2 * h)))) *
              (∫ y, Real.exp (-(h * sbMean (mu (D.genInv (lam / (A2 * h)))) * y))
                ∂(sizeBiasedLaw (mu (D.genInv (lam / (A2 * h)))))))) * lapDefect muinf h := by
            linarith
        _ ≤ lapDefect (mu (D.genInv (lam / (A2 * h)))) h := by linarith [hstepRest]
    have heta : (1 - η') * lapDefect muinf h ≤ (1 - η' / 4) * lapDefect muinf h :=
      mul_le_mul_of_nonneg_right (by linarith) hlinf_nonneg
    simpa [mul_comm] using heta.trans hset
  constructor
  · exact (hrest h hh0).1
  · have hη'denom : (1 - η') ≠ 0 := by linarith
    have hscale : (1 - η')⁻¹ ≤ (1 - η)⁻¹ := by
      rw [inv_le_inv₀ (by linarith : (0 : ℝ) < 1 - η') (by linarith : (0 : ℝ) < 1 - η)]
      linarith
    calc lapDefect muinf h = (lapDefect muinf h * (1 - η')) * (1 - η')⁻¹ := by field_simp
      _ ≤ lapDefect (mu (D.genInv (lam / (A2 * h)))) h * (1 - η')⁻¹ := by
        exact mul_le_mul_of_nonneg_right hkey (inv_nonneg.mpr (by linarith))
      _ ≤ lapDefect (mu (D.genInv (lam / (A2 * h)))) h * (1 - η)⁻¹ := by
        exact mul_le_mul_of_nonneg_left hscale (lapDefect_nonneg (hmu _) hh0)

end

end PercLib.CriticalLRP.Analysis.I32

#print axioms PercLib.CriticalLRP.Analysis.I32.mgf_of_fullLawGhostRatio
#print axioms PercLib.CriticalLRP.Analysis.I32.fullLawGhostRatio_of_restoration
