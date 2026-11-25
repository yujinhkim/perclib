/-
Migration source: https://github.com/yujinhkim/Critical-Long-range-percolation
Integration revision: 3b3d1d0e43ef940bfaa2292ee5c2ee094ac4edbf
Licence: Apache-2.0 for the PercLib Lean sources and tooling; see third_party/critical-lrp/.
External provenance and modifications are recorded in the file-specific notices below.
-/

/-
# The `A3` limit of Proposition I.3.2: existence and positivity

Source: Tom Hutchcroft, *Critical long-range percolation I: High effective dimension*
(arXiv:2508.18807v1), Proposition I.3.2, lines 1560-1669 of the supplied extract.

The constant is defined by the *implicitly convergent* limit

  `A3 = (A1 / A2^(1/a)) * lim_{λ → ∞} λ^(-(a-1)/a) ∫_0^∞ (1 - e^(-λx))/x dQ∞(x)`.

`hJlim` is an input of `mgf_of_fullLawGhostRatio` (see `Base.lean`, a verbatim copy of
`.scratch/i32/MGFAssembly.lean`).  The results below show that it is *not* an extra
assumption:

* `FullLawGhostRatio` is the source's (I.3.5)-(I.3.6) in the form in which the source
  actually uses it: a *single* threshold `Λ = Λ(η)` such that the un-cut and cut-off
  Laplace defects compare within `(1-η)⁻¹` for **every** `λ ≥ Λ` simultaneously.
* `A3cand_relCauchy` shows that this uniformity forces the candidate constants
  `c(λ) = A1 A2^(-1/a) λ^(-(a-1)/a) ∫ (1-e^(-λy))/y dQ∞` to be *relatively* Cauchy:
  `c λ ≤ (1-η)⁻¹ c λ'` for all `λ, λ' ≥ Λ(η)`.
* `tendsto_of_relCauchy` shows that a nonnegative relatively Cauchy function on a tail
  converges, because `limsup c ≤ (1+η) liminf c` for every `η > 0`.
* `a3Limit_exists` concludes: the `λ → ∞` limit defining `A3` exists.  No monotonicity
  or continuity of `λ ↦ ∫ (1-e^(-λy))/y dQ∞` is used, and no order isomorphism.
* `a3_mgf_of_fullLawGhostRatio` re-runs the source's assembly with `hJlim` discharged
  and, in addition, proves `A3 > 0`, which is what the Tauberian step (I.3.3) /
  Theorem I.2.11 needs for a nonzero normalizer.
-/
module

public import PercLib.CriticalLRP.Analysis.MGFAssembly
public import PercLib.CriticalLRP.Analysis.I32Endpoint

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

/-! ## 1. The candidate constant `A3` -/

/-- The source's `A3` integrand, i.e. `λ ↦ A1 A2^(-1/a) λ^(-(a-1)/a) ∫ (1-e^(-λy))/y dQ∞`. -/
def A3cand (A1 A2 a : ℝ) (Qinf : Measure ℝ) (lam : ℝ) : ℝ :=
  A1 * A2 ^ (-(1 / a)) * lam ^ (-(a - 1) / a) * (∫ y, kern lam y ∂Qinf)

theorem A3cand_nonneg {A1 A2 a : ℝ} {Qinf : Measure ℝ}
    (hA1 : 0 < A1) (hA2 : 0 < A2) (hQ : Qinf (Iio 0) = 0) {lam : ℝ} (hlam : 0 < lam) :
    0 ≤ A3cand A1 A2 a Qinf lam := by
  unfold A3cand
  have h1 : 0 < A2 ^ (-(1 / a)) := Real.rpow_pos_of_pos hA2 _
  have h2 : 0 < lam ^ (-(a - 1) / a) := Real.rpow_pos_of_pos hlam _
  have h3 : 0 ≤ ∫ y, kern lam y ∂Qinf :=
    integral_nonneg_of_ae (by
      filter_upwards [ae_nonneg_of_Iio hQ] with y hy
      exact kern_nonneg hlam hy)
  exact mul_nonneg (mul_nonneg (mul_nonneg hA1.le h1.le) h2.le) h3

/-- **Strict positivity of the kernel integral.**  This is where source hypothesis 4
(`Q∞ {0} = 0`) enters: without it `Q∞ = δ_0` gives a vanishing integral. -/
theorem integral_kern_pos {Q : Measure ℝ} [IsProbabilityMeasure Q]
    (hQpos : Q (Iio 0) = 0) (hQ0 : Q {(0 : ℝ)} = 0) {lam : ℝ} (hlam : 0 < lam) :
    0 < ∫ y, kern lam y ∂Q := by
  have hsup := ae_nonneg_of_Iio hQpos
  have hnn : 0 ≤ᵐ[Q] fun y => kern lam y := by
    filter_upwards [hsup] with y hy
    exact kern_nonneg hlam hy
  have hint : Integrable (fun y => kern lam y) Q := by
    refine Integrable.of_bound (measurable_kern lam).aestronglyMeasurable lam ?_
    filter_upwards [hsup] with y hy
    rw [Real.norm_eq_abs, abs_of_nonneg (kern_nonneg hlam hy)]
    exact kern_le_rate hlam hy
  rw [integral_pos_iff_support_of_nonneg_ae hnn hint]
  have hsupp : Function.support (fun y => kern lam y) = ({(0 : ℝ)} : Set ℝ)ᶜ := by
    ext y
    simp only [Function.mem_support, Set.mem_compl_iff, Set.mem_singleton_iff]
    constructor
    · intro hy h0
      have hz : kern lam 0 = 0 := by simp [kern]
      exact hy (by rw [h0]; exact hz)
    · intro hy hc
      unfold kern at hc
      rcases div_eq_zero_iff.mp hc with h | h
      · have h1 : Real.exp (-(lam * y)) = 1 := by linarith
        have h2 : -(lam * y) = 0 := by
          refine Real.exp_injective ?_
          simpa using h1
        have h4 : lam * y = 0 := by linarith
        rcases mul_eq_zero.mp h4 with h5 | h5
        · exact absurd h5 hlam.ne'
        · exact hy h5
      · exact hy h
  rw [hsupp]
  have hcomp : Q ({(0 : ℝ)} : Set ℝ)ᶜ = 1 := by
    rw [measure_compl (measurableSet_singleton (0 : ℝ)) (measure_ne_top Q _), hQ0,
      measure_univ, tsub_zero]
  rw [hcomp]
  norm_num

theorem A3cand_pos {A1 A2 a : ℝ} {Qinf : Measure ℝ} [IsProbabilityMeasure Qinf]
    (hA1 : 0 < A1) (hA2 : 0 < A2) (hQ : Qinf (Iio 0) = 0) (hQ0 : Qinf {(0 : ℝ)} = 0)
    {lam : ℝ} (hlam : 0 < lam) : 0 < A3cand A1 A2 a Qinf lam := by
  unfold A3cand
  have h1 : 0 < A2 ^ (-(1 / a)) := Real.rpow_pos_of_pos hA2 _
  have h2 : 0 < lam ^ (-(a - 1) / a) := Real.rpow_pos_of_pos hlam _
  have h3 : 0 < ∫ y, kern lam y ∂Qinf := integral_kern_pos hQ hQ0 hlam
  exact mul_pos (mul_pos (mul_pos hA1 h1) h2) h3

/-! ## 2. Relative Cauchy sequences on a tail converge -/

/-- **Relative Cauchy criterion.**  A function that is nonnegative on a tail and whose
tail values are mutually comparable up to `1 + ε` converges.  The proof does not use
monotonicity: `limsup c ≤ (1+ε) liminf c` for every `ε > 0` is enough. -/
theorem tendsto_of_relCauchy {c : ℝ → ℝ} {Λ₀ : ℝ}
    (hnn : ∀ x : ℝ, Λ₀ ≤ x → 0 ≤ c x)
    (hrel : ∀ ε : ℝ, 0 < ε → ∃ Λ : ℝ, ∀ x : ℝ, Λ ≤ x → ∀ y : ℝ, Λ ≤ y →
      c x ≤ (1 + ε) * c y) :
    ∃ L : ℝ, Tendsto c atTop (𝓝 L) := by
  obtain ⟨Λ₁, hΛ₁⟩ := hrel 1 one_pos
  set L₁ : ℝ := max Λ₁ Λ₀ with hL₁
  have hL₁Λ₁ : Λ₁ ≤ L₁ := le_max_left _ _
  have hL₁Λ₀ : Λ₀ ≤ L₁ := le_max_right _ _
  have hbdd : ∀ x : ℝ, L₁ ≤ x → c x ≤ 2 * c L₁ := by
    intro x hx
    have h1 := hΛ₁ x (le_trans hL₁Λ₁ hx) L₁ hL₁Λ₁
    linarith
  have hMnn : 0 ≤ 2 * c L₁ := by
    have := hnn L₁ hL₁Λ₀
    linarith
  have hcau : Cauchy (Filter.map c atTop) := by
    rw [Metric.cauchy_iff]
    refine ⟨inferInstance, ?_⟩
    intro ε hε
    obtain ⟨Λ₂, hΛ₂⟩ := hrel (ε / (2 * c L₁ + 1)) (by positivity)
    refine ⟨c '' Set.Ici (max L₁ Λ₂), ?_, ?_⟩
    · rw [Filter.mem_map]
      refine Filter.mem_atTop_sets.mpr ⟨max L₁ Λ₂, fun b hb => ?_⟩
      simp only [Set.mem_preimage]
      exact Set.mem_image_of_mem c hb
    · intro u hu v hv
      obtain ⟨x, hx, rfl⟩ := hu
      obtain ⟨y, hy, rfl⟩ := hv
      have hx1 : L₁ ≤ x := le_trans (le_max_left _ _) hx
      have hy1 : L₁ ≤ y := le_trans (le_max_left _ _) hy
      have hx2 : Λ₂ ≤ x := le_trans (le_max_right _ _) hx
      have hy2 : Λ₂ ≤ y := le_trans (le_max_right _ _) hy
      have hxy := hΛ₂ x hx2 y hy2
      have hyx := hΛ₂ y hy2 x hx2
      have hcx : c x ≤ 2 * c L₁ := hbdd x hx1
      have hcy : c y ≤ 2 * c L₁ := hbdd y hy1
      have hηnn : 0 ≤ ε / (2 * c L₁ + 1) := by positivity
      have hstep : ε / (2 * c L₁ + 1) * (2 * c L₁) < ε := by
        rw [div_mul_eq_mul_div, div_lt_iff₀ (by positivity)]
        nlinarith
      have hdiff1 : c x - c y ≤ ε / (2 * c L₁ + 1) * (2 * c L₁) := by
        have h1 : ε / (2 * c L₁ + 1) * c y ≤ ε / (2 * c L₁ + 1) * (2 * c L₁) :=
          mul_le_mul_of_nonneg_left hcy hηnn
        linarith
      have hdiff2 : c y - c x ≤ ε / (2 * c L₁ + 1) * (2 * c L₁) := by
        have h1 : ε / (2 * c L₁ + 1) * c x ≤ ε / (2 * c L₁ + 1) * (2 * c L₁) :=
          mul_le_mul_of_nonneg_left hcx hηnn
        linarith
      have hkey : |c x - c y| ≤ ε / (2 * c L₁ + 1) * (2 * c L₁) := by
        rw [abs_sub_le_iff]
        exact ⟨hdiff1, hdiff2⟩
      rw [Real.dist_eq]
      exact lt_of_le_of_lt hkey hstep
  exact cauchy_map_iff_exists_tendsto.mp hcau

end

end PercLib.CriticalLRP.Analysis.I32

/-! ## 3. The uniform ghost comparison forces relative Cauchy-ness -/

namespace PercLib.CriticalLRP.Analysis.I32

noncomputable section

/-- **The restoration comparison forces the `A3` candidates to be relatively Cauchy.**

`FullLawGhostRatio` is (I.3.5)-(I.3.6) with the quantifier order the source uses:
*some* `Λ = Λ(η)` makes the uncut/cut-off comparison hold for **all** `λ ≥ Λ`.  Then,
using the fixed-rate limit (I.3.7) at two rates `λ, λ' ≥ Λ` and letting `h ↓ 0`,
the candidate values satisfy `c λ ≤ (1-η)⁻¹ c λ'`.

Note what is *not* used: monotonicity of `λ ↦ ∫ (1-e^{-λy})/y dQ∞`, continuity of that
function, or any order isomorphism.  The single input is the uniform comparison. -/
theorem A3cand_relCauchy
    (mu : ℝ → Measure ℝ) (muinf : Measure ℝ) (Qinf : Measure ℝ)
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
    (hGhost : FullLawGhostRatio muinf mu D.genInv A2) :
    ∀ ε : ℝ, 0 < ε → ∃ Λ : ℝ, ∀ x : ℝ, Λ ≤ x → ∀ y : ℝ, Λ ≤ y →
      A3cand A1 A2 a Qinf x ≤ (1 + ε) * A3cand A1 A2 a Qinf y := by
  have hinv_general : ∀ η : ℝ, 0 < η → η ≤ 1 / 2 → (1 - η)⁻¹ ≤ 1 + 2 * η := by
    intro η hη0 hηh
    rw [inv_eq_one_div, div_le_iff₀ (by linarith : (0 : ℝ) < 1 - η)]
    nlinarith [mul_nonneg hη0.le (by linarith : (0 : ℝ) ≤ 1 - 2 * η)]
  intro ε hε
  obtain ⟨η, hη0, hηhalf, hηle⟩ : ∃ η : ℝ, 0 < η ∧ η ≤ 1 / 2 ∧ (1 - η)⁻¹ ≤ 1 + ε := by
    refine ⟨min (1 / 2) (ε / 2), lt_min (by norm_num) (by linarith), min_le_left _ _, ?_⟩
    have h1 : (1 - min (1 / 2) (ε / 2))⁻¹ ≤ 1 + 2 * min (1 / 2) (ε / 2) :=
      hinv_general _ (lt_min (by norm_num) (by linarith)) (min_le_left _ _)
    have h2 := min_le_right (1 / 2 : ℝ) (ε / 2)
    linarith
  obtain ⟨Λ, hΛ0, hΛ⟩ := hGhost η hη0 hηhalf
  refine ⟨max Λ 1, ?_⟩
  intro x hx y hy
  have hxΛ : Λ ≤ x := le_trans (le_max_left _ _) hx
  have hyΛ : Λ ≤ y := le_trans (le_max_left _ _) hy
  have hxpos : 0 < x := lt_of_lt_of_le one_pos (le_trans (le_max_right _ _) hx)
  have hypos : 0 < y := lt_of_lt_of_le one_pos (le_trans (le_max_right _ _) hy)
  have hlimx : Tendsto (fun h : ℝ => lapDefect (mu (D.genInv (x / (A2 * h)))) h /
      (D.genInv (1 / h) ^ α * h)) (𝓝[>] (0 : ℝ)) (𝓝 (A3cand A1 A2 a Qinf x)) := by
    have h := cutoff_defect_ratio_source (mu := mu) (Qinf := Qinf) (D := D) hmu hEpos hSpos
      hprob hQinf hQinf0 hconv hA1 hA2 ha hα hρα hE1 hψdiv hxpos
    simpa only [lapDefect, A3cand] using h
  have hlimy : Tendsto (fun h : ℝ => lapDefect (mu (D.genInv (y / (A2 * h)))) h /
      (D.genInv (1 / h) ^ α * h)) (𝓝[>] (0 : ℝ)) (𝓝 (A3cand A1 A2 a Qinf y)) := by
    have h := cutoff_defect_ratio_source (mu := mu) (Qinf := Qinf) (D := D) hmu hEpos hSpos
      hprob hQinf hQinf0 hconv hA1 hA2 ha hα hρα hE1 hψdiv hypos
    simpa only [lapDefect, A3cand] using h
  have hev : ∀ᶠ h : ℝ in 𝓝[>] (0 : ℝ),
      lapDefect (mu (D.genInv (x / (A2 * h)))) h / (D.genInv (1 / h) ^ α * h) ≤
        (lapDefect (mu (D.genInv (y / (A2 * h)))) h / (D.genInv (1 / h) ^ α * h)) *
          (1 - η)⁻¹ := by
    filter_upwards [hΛ x hxΛ, hΛ y hyΛ, self_mem_nhdsWithin] with h hxle hyle hh
    have hh0 : 0 < h := hh
    have hW : 0 < D.genInv (1 / h) ^ α * h :=
      mul_pos (Real.rpow_pos_of_pos (D.genInv_pos _) _) hh0
    have hstep : lapDefect (mu (D.genInv (x / (A2 * h)))) h ≤
        lapDefect (mu (D.genInv (y / (A2 * h)))) h * (1 - η)⁻¹ :=
      le_trans hxle.1 hyle.2
    calc lapDefect (mu (D.genInv (x / (A2 * h)))) h / (D.genInv (1 / h) ^ α * h)
        ≤ (lapDefect (mu (D.genInv (y / (A2 * h)))) h * (1 - η)⁻¹) /
            (D.genInv (1 / h) ^ α * h) := (div_le_div_iff_of_pos_right hW).mpr hstep
      _ = (lapDefect (mu (D.genInv (y / (A2 * h)))) h / (D.genInv (1 / h) ^ α * h)) *
            (1 - η)⁻¹ := by ring
  have hkey := le_of_tendsto_of_tendsto hlimx (hlimy.mul_const ((1 - η)⁻¹)) hev
  have hstep2 : A3cand A1 A2 a Qinf y * (1 - η)⁻¹ ≤ (1 + ε) * A3cand A1 A2 a Qinf y := by
    have h : A3cand A1 A2 a Qinf y * (1 - η)⁻¹ ≤ A3cand A1 A2 a Qinf y * (1 + ε) :=
      mul_le_mul_of_nonneg_left hηle (A3cand_nonneg hA1 hA2 hQinf hypos)
    calc A3cand A1 A2 a Qinf y * (1 - η)⁻¹ ≤ A3cand A1 A2 a Qinf y * (1 + ε) := h
      _ = (1 + ε) * A3cand A1 A2 a Qinf y := mul_comm _ _
  exact le_trans hkey hstep2

/-- **The `λ → ∞` limit defining `A3` exists.**  Hence `hJlim`, the last input of
`mgf_of_fullLawGhostRatio`, is a theorem once the restoration comparison is available
in its uniform form. -/
theorem a3Limit_exists
    (mu : ℝ → Measure ℝ) (muinf : Measure ℝ) (Qinf : Measure ℝ)
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
    (hGhost : FullLawGhostRatio muinf mu D.genInv A2) :
    ∃ A3 : ℝ, 0 ≤ A3 ∧ Tendsto (A3cand A1 A2 a Qinf) atTop (𝓝 A3) := by
  have hrel := A3cand_relCauchy (mu := mu) (muinf := muinf) (Qinf := Qinf) (D := D)
    hmu hEpos hSpos hprob hQinf hQinf0 hconv hA1 hA2 ha hα hρα hE1 hψdiv hGhost
  obtain ⟨A3, hA3⟩ := tendsto_of_relCauchy (Λ₀ := 1)
    (fun x hx => A3cand_nonneg hA1 hA2 hQinf (lt_of_lt_of_le one_pos hx)) hrel
  refine ⟨A3, ?_, hA3⟩
  refine ge_of_tendsto hA3 ?_
  filter_upwards [Filter.eventually_ge_atTop (1 : ℝ)] with x hx
  exact A3cand_nonneg hA1 hA2 hQinf (lt_of_lt_of_le one_pos hx)

/-- **Monotone-free sharpening.**  The candidate values do not merely converge: the
limit is above every one of them on the tail.  This is the content of the lower half of
`sandwich`; no monotonicity of `c` is assumed or proved. -/
theorem A3cand_le_of_tendsto
    (mu : ℝ → Measure ℝ) (muinf : Measure ℝ) (Qinf : Measure ℝ)
    {f : ℝ → ℝ} {ρ : ℝ} (D : RVPosData f ρ)
    (hmu : ∀ r, mu r (Iio 0) = 0)
    (hmuinf : muinf (Iio 0) = 0)
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
    (hGhost : FullLawGhostRatio muinf mu D.genInv A2)
    {A3 : ℝ} (hA3 : Tendsto (A3cand A1 A2 a Qinf) atTop (𝓝 A3)) :
    ∀ᶠ lam : ℝ in atTop, A3cand A1 A2 a Qinf lam ≤ A3 := by
  obtain ⟨Λ, hΛ0, hΛ⟩ := hGhost (1 / 2) (by norm_num) (le_refl (1 / 2))
  have hmgf := mgf_of_fullLawGhostRatio (mu := mu) (muinf := muinf) (Qinf := Qinf)
    (D := D) hmu hmuinf hEpos hSpos hprob hQinf hQinf0 hconv hA1 hA2 ha hα hρα hE1
    hψdiv hA3 hGhost
  filter_upwards [Filter.eventually_ge_atTop (max Λ 1)] with x hx
  have hxΛ : Λ ≤ x := le_trans (le_max_left _ _) hx
  have hxpos : 0 < x := lt_of_lt_of_le one_pos (le_trans (le_max_right _ _) hx)
  have hlimx : Tendsto (fun h : ℝ => lapDefect (mu (D.genInv (x / (A2 * h)))) h /
      (D.genInv (1 / h) ^ α * h)) (𝓝[>] (0 : ℝ)) (𝓝 (A3cand A1 A2 a Qinf x)) := by
    have h := cutoff_defect_ratio_source (mu := mu) (Qinf := Qinf) (D := D) hmu hEpos hSpos
      hprob hQinf hQinf0 hconv hA1 hA2 ha hα hρα hE1 hψdiv hxpos
    simpa only [lapDefect, A3cand] using h
  have hev : ∀ᶠ h : ℝ in 𝓝[>] (0 : ℝ),
      lapDefect (mu (D.genInv (x / (A2 * h)))) h / (D.genInv (1 / h) ^ α * h) ≤
        lapDefect muinf h / (D.genInv (1 / h) ^ α * h) := by
    filter_upwards [hΛ x hxΛ, self_mem_nhdsWithin] with h hcomp hh
    have hh0 : 0 < h := hh
    have hW : 0 < D.genInv (1 / h) ^ α * h :=
      mul_pos (Real.rpow_pos_of_pos (D.genInv_pos _) _) hh0
    exact (div_le_div_iff_of_pos_right hW).mpr hcomp.1
  exact le_of_tendsto_of_tendsto hlimx hmgf hev

/-- **Positivity of `A3`.**  The uniform ghost comparison gives `c(λ) ≤ A3`, and
`c(λ) > 0` for every `λ > 0` by hypothesis 4 (`Q∞{0} = 0`) plus the size-biased kernel.
Hence `A3 > 0`, which is what the Tauberian step (I.3.3) needs.

This is *not* derivable from (1)-(4) alone in the abstract: if the ghost comparison is
dropped, `Q∞ = δ_1` and `a > 1` make `A3 = 0`.  The comparison is what rules it out. -/
theorem a3_pos
    (mu : ℝ → Measure ℝ) (muinf : Measure ℝ) (Qinf : Measure ℝ)
    {f : ℝ → ℝ} {ρ : ℝ} (D : RVPosData f ρ)
    (hmu : ∀ r, mu r (Iio 0) = 0)
    (hmuinf : muinf (Iio 0) = 0)
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
    (hGhost : FullLawGhostRatio muinf mu D.genInv A2)
    {A3 : ℝ} (hA3 : Tendsto (A3cand A1 A2 a Qinf) atTop (𝓝 A3)) :
    0 < A3 := by
  have hle := A3cand_le_of_tendsto (mu := mu) (muinf := muinf) (Qinf := Qinf) (D := D)
    hmu hmuinf hEpos hSpos hprob hQinf hQinf0 hconv hA1 hA2 ha hα hρα hE1 hψdiv hGhost hA3
  obtain ⟨Λ', hΛ'⟩ := Filter.eventually_atTop.1 hle
  obtain ⟨Λ, hΛ0, _⟩ := hGhost (1 / 2) (by norm_num) (le_refl (1 / 2))
  set lam : ℝ := max Λ' (max Λ 1) with hlam
  have hle' : A3cand A1 A2 a Qinf lam ≤ A3 := hΛ' lam (le_max_left _ _)
  have hlampos : 0 < lam :=
    lt_of_lt_of_le one_pos (le_trans (le_max_right _ _) (le_max_right _ _))
  have hpos : 0 < A3cand A1 A2 a Qinf lam := A3cand_pos hA1 hA2 hQinf hQinf0 hlampos
  linarith

/-- **The assembly of Proposition I.3.2 with `hJlim` discharged and positivity added.**

Given the moment asymptotics (1)-(2), the weak convergence (3), the absence of an atom
at zero (4), and the full-law restoration comparison in its uniform form (I.3.5)-(I.3.6),
there is a constant `A3` such that
* `A3 > 0`;
* `λ ↦ A1 A2^{-1/a} λ^{-(a-1)/a} ∫ (1-e^{-λy})/y dQ∞` converges to `A3` (the implicit
  limit in the definition of `A3`);
* the uncut Laplace defect satisfies `E[1-e^{-h|K|}] / (f^{-1}(1/h)^a h) → A3`, i.e.
  (I.3.2). -/
theorem a3_mgf_of_fullLawGhostRatio
    (mu : ℝ → Measure ℝ) (muinf : Measure ℝ) (Qinf : Measure ℝ)
    {f : ℝ → ℝ} {ρ : ℝ} (D : RVPosData f ρ)
    (hmu : ∀ r, mu r (Iio 0) = 0)
    (hmuinf : muinf (Iio 0) = 0)
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
    (hGhost : FullLawGhostRatio muinf mu D.genInv A2) :
    ∃ A3 : ℝ, 0 < A3 ∧ Tendsto (A3cand A1 A2 a Qinf) atTop (𝓝 A3) ∧
      Tendsto (fun h : ℝ => lapDefect muinf h / (D.genInv (1 / h) ^ α * h))
        (𝓝[>] (0 : ℝ)) (𝓝 A3) := by
  obtain ⟨A3, -, hA3⟩ := a3Limit_exists (mu := mu) (muinf := muinf) (Qinf := Qinf) (D := D)
    hmu hEpos hSpos hprob hQinf hQinf0 hconv hA1 hA2 ha hα hρα hE1 hψdiv hGhost
  have hmgf := mgf_of_fullLawGhostRatio (mu := mu) (muinf := muinf) (Qinf := Qinf)
    (D := D) hmu hmuinf hEpos hSpos hprob hQinf hQinf0 hconv hA1 hA2 ha hα hρα hE1
    hψdiv hA3 hGhost
  have hpos := a3_pos (mu := mu) (muinf := muinf) (Qinf := Qinf) (D := D)
    hmu hmuinf hEpos hSpos hprob hQinf hQinf0 hconv hA1 hA2 ha hα hρα hE1 hψdiv hGhost hA3
  exact ⟨A3, hpos, hA3, hmgf⟩

/-! ## 4. The positivity boundary: a Dirac limit law gives `A3 = 0` -/

/-- Kernel integral against the Dirac law at `1`. -/
theorem integral_kern_dirac_one (s : ℝ) :
    ∫ y, kern s y ∂(Measure.dirac (1 : ℝ)) = 1 - Real.exp (-s) := by
  rw [integral_dirac]
  simp [kern]

/-- **A Dirac limit law makes `A3` vanish.**  For `Q∞ = δ₁` and `a > 1` the whole
`A3` family tends to `0`, so `A3 = 0` (the limit exists but is zero).

Consequently positivity is *not* a consequence of hypotheses (1)-(4) plus existence of
the limit: it requires the ghost comparison, which (by `a3_pos`) rules this case out. -/
theorem A3cand_dirac_one_tendsto_zero {A1 A2 a : ℝ} (ha : 1 < a) :
    Tendsto (A3cand A1 A2 a (Measure.dirac (1 : ℝ))) atTop (𝓝 0) := by
  have ha0 : (0 : ℝ) < a := by linarith
  have hβ : 0 < (a - 1) / a := div_pos (by linarith) ha0
  have hexp : Tendsto (fun lam : ℝ => 1 - Real.exp (-lam)) atTop (𝓝 1) := by
    have h : Tendsto (fun lam : ℝ => 1 - Real.exp (-lam)) atTop (𝓝 (1 - 0)) :=
      tendsto_const_nhds.sub Real.tendsto_exp_neg_atTop_nhds_zero
    simpa using h
  have hpow : Tendsto (fun lam : ℝ => lam ^ (-(a - 1) / a)) atTop (𝓝 0) := by
    have h : Tendsto (fun lam : ℝ => lam ^ (-((a - 1) / a))) atTop (𝓝 0) :=
      tendsto_rpow_neg_atTop hβ
    simpa only [neg_div] using h
  have hprod : Tendsto (fun lam : ℝ => lam ^ (-(a - 1) / a) * (1 - Real.exp (-lam)))
      atTop (𝓝 (0 * 1)) := hpow.mul hexp
  have hmain : Tendsto (fun lam : ℝ => A1 * A2 ^ (-(1 / a)) *
      (lam ^ (-(a - 1) / a) * (1 - Real.exp (-lam)))) atTop
      (𝓝 (A1 * A2 ^ (-(1 / a)) * (0 * 1))) := tendsto_const_nhds.mul hprod
  have h0 : A1 * A2 ^ (-(1 / a)) * (0 * 1) = 0 := by ring
  rw [h0] at hmain
  refine hmain.congr' ?_
  filter_upwards with lam
  unfold A3cand
  rw [integral_kern_dirac_one]
  ring

end

end PercLib.CriticalLRP.Analysis.I32

#print axioms PercLib.CriticalLRP.Analysis.I32.A3cand_dirac_one_tendsto_zero

#print axioms PercLib.CriticalLRP.Analysis.I32.tendsto_of_relCauchy
#print axioms PercLib.CriticalLRP.Analysis.I32.integral_kern_pos
#print axioms PercLib.CriticalLRP.Analysis.I32.A3cand_relCauchy
#print axioms PercLib.CriticalLRP.Analysis.I32.a3Limit_exists
#print axioms PercLib.CriticalLRP.Analysis.I32.A3cand_le_of_tendsto
#print axioms PercLib.CriticalLRP.Analysis.I32.a3_pos
#print axioms PercLib.CriticalLRP.Analysis.I32.a3_mgf_of_fullLawGhostRatio


namespace PercLib.CriticalLRP.Analysis.I32

noncomputable section

/-- **The complete MGF and volume-tail package of Proposition I.3.2**, conditional on
its full-law restoration comparison. The normalized large-rate candidate defining
`A3` is proved to converge to a positive constant; it is not taken as a premise.
The first two moment integrabilities are used only for Jensen's inequality, which
rules out `a < 1` and legitimizes the Karamata conversion. -/
theorem a3_ne_zero
    (mu : ℝ → Measure ℝ) (muinf : Measure ℝ) (Qinf : Measure ℝ)
    {f : ℝ → ℝ} {ρ : ℝ} (D : RVPosData f ρ)
    (hmu : ∀ r, mu r (Iio 0) = 0)
    (hmuinf : muinf (Iio 0) = 0)
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
    (hGhost : FullLawGhostRatio muinf mu D.genInv A2)
    {A3 : ℝ} (hA3 : Tendsto (A3cand A1 A2 a Qinf) atTop (𝓝 A3)) :
    A3 ≠ 0 :=
  (a3_pos (mu := mu) (muinf := muinf) (Qinf := Qinf) (D := D) hmu hmuinf hEpos hSpos
    hprob hQinf hQinf0 hconv hA1 hA2 ha hα hρα hE1 hψdiv hGhost hA3).ne'

/-- **Proposition I.3.2, (I.3.3), with `A3` produced and positive.** -/
theorem tail_asymptotic_of_fullLawGhostRatio
    (mu : ℝ → Measure ℝ) (muinf : Measure ℝ) (Qinf : Measure ℝ)
    {f : ℝ → ℝ} {ρ : ℝ} (D : RVPosData f ρ)
    (hmu : ∀ r, mu r (Iio 0) = 0)
    (hmuinf : muinf (Iio 0) = 0)
    [IsProbabilityMeasure muinf]
    (hEpos : ∀ r, 0 < mean (mu r))
    (hSpos : ∀ r, 0 < sbMean (mu r))
    (hprob : ∀ r, IsProbabilityMeasure (sizeBiasedLaw (mu r)))
    [IsProbabilityMeasure Qinf]
    (hQinf : Qinf (Iio 0) = 0) (hQinf0 : Qinf {(0 : ℝ)} = 0)
    (hconv : Tendsto (fun r => Measure.toProbabilityMeasure (sizeBiasedLaw (mu r))) atTop
      (𝓝 (Measure.toProbabilityMeasure Qinf)))
    {A1 A2 a α : ℝ} (hA1 : 0 < A1) (hA2 : 0 < A2) (ha : 0 < a) (hα : 0 < α)
    (ha1 : 1 / a ≤ 1)
    (hρα : ρ = a * α)
    (hE1 : Tendsto (fun r => mean (mu r) / (A1 * r ^ α)) atTop (𝓝 1))
    (hψdiv : Tendsto (fun r => sbMean (mu r) / f r) atTop (𝓝 A2))
    (hGhost : FullLawGhostRatio muinf mu D.genInv A2)
    (hrvInv : RegularlyVaryingAtTop D.genInv (1 / (a * α))) :
    ∃ A3 : ℝ, 0 < A3 ∧
      Tendsto (fun x : ℝ => (muinf (Ici x)).toReal /
        ((A3 / Real.Gamma (1 / a)) * (D.genInv x ^ α / x))) atTop (𝓝 1) := by
  obtain ⟨A3, hpos, -, hmgf⟩ := a3_mgf_of_fullLawGhostRatio (mu := mu) (muinf := muinf)
    (Qinf := Qinf) (D := D) hmu hmuinf hEpos hSpos hprob hQinf hQinf0 hconv hA1 hA2 ha hα
    hρα hE1 hψdiv hGhost
  have hA3ne : A3 ≠ 0 := hpos.ne'
  -- normalised MGF asymptotic
  have hdiv : Tendsto (fun h : ℝ =>
      (lapDefect muinf h / (D.genInv (1 / h) ^ α * h)) / A3) (𝓝[>] (0 : ℝ)) (𝓝 (A3 / A3)) :=
    hmgf.div_const A3
  have hone : A3 / A3 = 1 := div_self hA3ne
  rw [hone] at hdiv
  have hmain : Tendsto (fun h : ℝ =>
      (∫ s, (1 - Real.exp (-(h * s))) ∂muinf) /
        (A3 * (D.genInv (1 / h) ^ α * h))) (𝓝[>] (0 : ℝ)) (𝓝 1) := by
    refine hdiv.congr' ?_
    filter_upwards [self_mem_nhdsWithin] with h hh
    have hh0 : 0 < h := hh
    have hW : D.genInv (1 / h) ^ α * h ≠ 0 :=
      (mul_pos (Real.rpow_pos_of_pos (D.genInv_pos _) _) hh0).ne'
    show lapDefect muinf h / (D.genInv (1 / h) ^ α * h) / A3
      = (∫ s, (1 - Real.exp (-(h * s))) ∂muinf) / (A3 * (D.genInv (1 / h) ^ α * h))
    simp only [lapDefect]
    field_simp
  have hmono : Monotone D.genInv := fun x y hxy => D.genInv_mono hxy
  have hmeas : Measurable D.genInv := hmono.measurable
  have hgpos : ∀ᶠ x : ℝ in atTop, 0 < D.genInv x :=
    Eventually.of_forall fun x =>
      lt_of_lt_of_le one_pos (le_trans D.one_le_threshold (D.le_genInv x))
  have htail := PercLib.CriticalLRP.VolumeTail.tail_asymptotic_of_mgf_inverse
    (μ := muinf) hmuinf ha hα ha1 hmeas hrvInv hgpos hA3ne hmain
  exact ⟨A3, hpos, htail⟩


theorem prop_I_3_2_of_fullLawGhostRatio
    (mu : ℝ → Measure ℝ) (muinf : Measure ℝ) (Qinf : Measure ℝ)
    {f : ℝ → ℝ} {ρ : ℝ} (D : RVPosData f ρ)
    (hmuProb : ∀ r, IsProbabilityMeasure (mu r)) [IsProbabilityMeasure muinf]
    (hmu : ∀ r, mu r (Iio 0) = 0) (hmuinf : muinf (Iio 0) = 0)
    (hint1 : ∀ r, Integrable (fun x : ℝ => x) (mu r))
    (hint2 : ∀ r, Integrable (fun x : ℝ => x ^ 2) (mu r))
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
    (hGhost : FullLawGhostRatio muinf mu D.genInv A2) :
    ∃ A3 : ℝ, 0 < A3 ∧ Tendsto (A3cand A1 A2 a Qinf) atTop (𝓝 A3) ∧
      Tendsto (fun h : ℝ => lapDefect muinf h / (A3 * (D.genInv (1 / h) ^ α * h)))
        (𝓝[>] (0 : ℝ)) (𝓝 1) ∧
      Tendsto (fun x : ℝ => (muinf (Ici x)).toReal /
        ((A3 / Real.Gamma (1 / a)) * (D.genInv x ^ α / x))) atTop (𝓝 1) := by
  let := fun r => hmuProb r
  have hψ2 : Tendsto (fun r => sbMean (mu r) / (A2 * f r)) atTop (𝓝 1) := by
    have hmul := hψdiv.div_const A2
    rw [div_self hA2.ne'] at hmul
    refine hmul.congr' ?_
    filter_upwards [D.rv.1] with r hf
    field_simp
  have hφ : ∀ᶠ r in atTop, 0 ≤ sbMean (mu r) :=
    Filter.Eventually.of_forall fun r => I32Endpoint.sbMean_nonneg (hint2 r) (hEpos r)
  have hge : ∀ᶠ r in atTop, mean (mu r) ≤ sbMean (mu r) :=
    Filter.Eventually.of_forall fun r => I32Endpoint.mean_le_sbMean
      (hmu r) (hint1 r) (hint2 r) (hEpos r)
  have hrv : RegularlyVaryingAtTop f (a * α) := by simpa [hρα] using D.rv
  have hone := I32Endpoint.one_le_of_moment_asymptotics hA1 hA2 hα ha
    D.measurable_f hrv hφ hge hE1 hψ2
  have ha1 : 1 / a ≤ 1 := by
    rw [div_le_one ha]
    exact hone
  let : IsProbabilityMeasure muinf := inferInstance
  obtain ⟨A3, hA3pos, hA3lim, hM⟩ := a3_mgf_of_fullLawGhostRatio mu muinf Qinf D
    hmu hmuinf hEpos hSpos hprob hQinf hQinf0 hconv
    hA1 hA2 ha hα hρα hE1 hψdiv hGhost
  have hmain : Tendsto (fun h : ℝ => lapDefect muinf h /
      (A3 * (D.genInv (1 / h) ^ α * h))) (𝓝[>] (0 : ℝ)) (𝓝 1) := by
    have h := hM.div_const A3
    rw [div_self hA3pos.ne'] at h
    refine h.congr' ?_
    filter_upwards with h
    rw [div_div, mul_comm]
  have hgrv : RegularlyVaryingAtTop D.genInv (1 / (a * α)) :=
    (D.genInv_volumeTail_data (f := f) (ρ := ρ) ha hα hρα).2.2
  have htail := VolumeTail.tail_asymptotic_of_mgf_inverse muinf hmuinf ha hα ha1
    D.measurable_genInv hgrv (Filter.Eventually.of_forall D.genInv_pos)
    hA3pos.ne' hmain
  exact ⟨A3, hA3pos, hA3lim, hmain, htail⟩

end

end PercLib.CriticalLRP.Analysis.I32

#print axioms PercLib.CriticalLRP.Analysis.I32.prop_I_3_2_of_fullLawGhostRatio
