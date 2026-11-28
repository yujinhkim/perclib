/-
Copyright (c) 2026 PercLib contributors. Released under Apache 2.0.

Accepted and independently rebuilt from Ultramath `smwznoz6j`, member m5.
Latest independent rebuild at production HEAD `16d9f2aa1e83afeda3fc66117e38ed3352b2e567`; reviewed scratch source `.scratch/review-smwznoz6j/m5/Main.lean`.

Swarm `smwznoz6j`, member `m5`, direction `d1` — (F) I.4.20 Case-3 dependency closure.

Production base `a42ae967cb8649dffa6f108a7a474602dd8a0d76`, branch `work/yujinhkim-critical-lrp-orchestration`.

# Case 3 of Proposition I.4.20 with the §I.4.1 structural inputs derived from `(HD)(3)`

The production Case-3 consumers of Proposition I.4.20 all carry the triangle finiteness

  `hTri : TriTail.openTriangleSelf M.kernel M.kernel_nonneg M.betaCrit 0 < ⊤`

as a *separate* hypothesis, even where they simultaneously assume Case 3 of `(HD)`.  The
`TriangleFromHD` package proves `hTri` — and the log-integrability/vanishing of the open-triangle
tail `hTail` of Lemma I.4.3 — from `(HD)(3)`, by the two convolution stages of (I.4.12) plus the
bridge `∇_{β_c}(0,x) = ofReal (τ * τ * τ)(x)`.  Until now nothing in the I.4.20 tree consumed that
derivation.

This file wires the derivation into the actual I.4.20 consumers:

* `hTri_of_case3HD`, `hTail_of_case3HD`, `case3TriangleTailData_of_case3HD` — the two §I.4.1
  inputs from the literal `Case3HD` predicate (p. 9 of Hutchcroft, *Critical long-range
  percolation I*, arXiv:2508.18807v1);
* `case3_hAend_hAmid_cutPoly_source_of_case3HD_of_critical_divergence` and
  `case3_i421_cutPoly_source_of_case3HD_of_critical_divergence` — the direct and normalized
  Case-3 conclusions with `hTri` deleted and the first-moment asymptotic taken from the paper's
  critical-mean divergence `E_{β_c}|K_0| = ⊤`;
* `firstMomentAsymptotic_of_critical_divergence_ae` — the assembly's reusable first-moment step,
  with the cutoff-mass finiteness derived from the second cutoff moment and the uniform defect
  bound derived from the defect limit;
* `case3_hAend_hAmid_cutPoly_source_of_case3HD` and `exists_case3_i421_cutPoly_source_of_case3HD`
  (plus the `∀ ℓ` form `forall_case3_i421_cutPoly_source_of_case3HD`) — the strongest assemblies
  here: `hTri`, `hTail`, the first-moment asymptotic `hP`, the lower comparison `hgm` (from the
  uncut critical volume tail) and the root moment range (from a finite first cutoff moment) are
  all derived.  What is left is the source's own list: `(HD)(3)`, `E_{β_c}|K_0| = ⊤`, the
  off-corner envelope/continuity package, the vanishing of the (I.4.6) defect, the uncut
  volume-tail bound, a finite critical cutoff first moment, and the induction indices.

Nothing here is an instance of `_no_hRV2`, and no step re-derives `(HD)(3)`: the only probabilistic
input about the critical two-point function is the literal `Case3HD` hypothesis itself.
-/
module

public import PercLib.CriticalLRP.VolumeMoments.HigherMoments.I420Case3.SplitPolygon.AllMoments
public import PercLib.CriticalLRP.VolumeMoments.HigherMoments.I420Case3.CriticalDivergence
public import PercLib.CriticalLRP.Analysis.Cutoff.OffCorner.AeDerivativeHandoff
public import PercLib.CriticalLRP.Analysis.SecondMomentCase3.TriangleFromHD.Main
public import PercLib.CriticalLRP.VolumeMoments.HigherMoments.I420Case3.HDClosure.Defs

set_option linter.style.longLine false
set_option linter.hashCommand false
@[expose] public section

noncomputable section

open MeasureTheory Measure ProbabilityTheory unitInterval Filter Topology
open scoped ENNReal NNReal Topology

namespace PercLib.CriticalLRP

namespace Orchestration
namespace SourceModelData

variable (M : SourceModelData)

/-! ## §0 The two §I.4.1 structural inputs from `(HD)(3)` -/

/-- **Case 3 of `(HD)` gives Kozma's triangle condition** `∇_{β_c}(0,0) < ⊤`. -/
theorem hTri_of_case3HD (h : M.Case3HD) :
    TriTail.openTriangleSelf M.kernel M.kernel_nonneg M.betaCrit 0 < ⊤ :=
  M.openTriangleSelf_lt_top_of_case3 h

/-- **Case 3 of `(HD)` gives the open-triangle tail limit** `∇_r → 0` (Lemma I.4.3, Case 3), in
the `M.nablaTail` shape consumed by `I420Case3`. -/
theorem hTail_of_case3HD (h : M.Case3HD) :
    Tendsto (fun r : ℝ => (M.nablaTail r).toReal) atTop (𝓝 0) :=
  (M.isLogErrorFunction_nablaTail_of_case3 h).2

/-- `Case3TriangleTailData` follows from the literal `Case3HD` predicate. -/
theorem case3TriangleTailData_of_case3HD (h : M.Case3HD) : M.Case3TriangleTailData :=
  ⟨M.hTri_of_case3HD h, M.isLogErrorFunction_nablaTail_of_case3 h⟩

end SourceModelData
end Orchestration

namespace I420Case3

open Orchestration

/-! ## §1 The direct endpoint / middle-index consumer without `hTri` -/

/-- **Case 3 of Proposition I.4.20, direct form, with `hTri` derived from `(HD)(3)`.**

Same conclusion as `LowerTwoPoint.case3_hAend_hAmid_cutPoly_source_of_HD_case3_of_critical_divergence`
(the ratio limits at the genuine source balls), but the triangle finiteness is no longer an
independent hypothesis: it is `openTriangleSelf_lt_top_of_case3` applied to the same `(HD)(3)`
data.  Every other input is retained verbatim, in particular the lower comparison `hgm` and the
root moment range. -/
theorem case3_hAend_hAmid_cutPoly_source_of_case3HD_of_critical_divergence (M : SourceModelData)
    (hHD3 : M.Case3HD)
    (htop : M.uncutMean M.betaCrit = ⊤)
    {f' h : ℝ → ℝ} {C r₀ : ℝ}
    (hfin : ∀ᶠ r : ℝ in atTop, M.cutMassAt r 0 ≠ ⊤)
    (hβ : (0 : ℝ) < M.betaCrit) (hr₀ : 0 < r₀)
    (hderiv : ∀ t : ℝ, r₀ ≤ t →
      HasDerivAt (fun r => (M.cutMassAt r 0).toReal) (f' t) t)
    (hpos : ∀ t : ℝ, r₀ ≤ t → 0 < (M.cutMassAt t 0).toReal)
    (hode : ∀ t : ℝ, r₀ ≤ t →
      f' t = (M.betaCrit : ℝ) * (1 - h t) * t ^ (-M.α - 1) *
        ((M.cutMassAt t 0).toReal) ^ 2)
    (hmeas : Measurable h) (hhedge : ∀ t : ℝ, r₀ ≤ t → |h t| ≤ C)
    (h0 : Tendsto h atTop (𝓝 0))
    (𝓔 : ℕ → Finset (Sym2 M.V)) (h𝓔mono : Monotone 𝓔)
    (h𝓔 : ∀ e : Sym2 M.V, ∃ n, e ∈ 𝓔 n) (p : ℕ) (hp : 3 ≤ p)
    {θ : ℝ} (hθ0 : 0 < θ) (hθ1 : θ < 1)
    (hMa : ∀ (r : ℝ), 1 ≤ r → ∀ ℓ : ℕ, ℓ ≤ p →
      I420Case1.powMomentAt (M.cutProb r) (ℓ + 1) (0 : M.V) ≠ ⊤)
    {c3 : ℝ} (hc3 : 0 < c3)
    (hgm : ∀ᶠ r in atTop, c3 * momOf (fun r => M.cutProb r) (0 : M.V) 1 r ^ 3
      ≤ momOf (fun r => M.cutProb r) (0 : M.V) 2 r) :
    Tendsto (fun r => I420Case1.mixedExclR (M.cutProb r) (0 : M.V) 1 p
          (BallAverage.ball_finite M r).toFinset /
        (ballCard (fun r => (BallAverage.ball_finite M r).toFinset) r *
          (momOf (fun r => M.cutProb r) (0 : M.V) 1 r *
            momOf (fun r => M.cutProb r) (0 : M.V) p r))) atTop (𝓝 1) ∧
      ∀ ℓ, 1 ≤ ℓ → ℓ ≤ p - 2 → Tendsto
        (fun r => I420Case1.mixedExclR (M.cutProb r) (0 : M.V) (ℓ + 1) (p - ℓ)
            (BallAverage.ball_finite M r).toFinset /
          (ballCard (fun r => (BallAverage.ball_finite M r).toFinset) r *
            (momOf (fun r => M.cutProb r) (0 : M.V) (ℓ + 1) r *
              momOf (fun r => M.cutProb r) (0 : M.V) (p - ℓ) r))) atTop (𝓝 1) :=
  LowerTwoPoint.case3_hAend_hAmid_cutPoly_source_of_HD_case3_of_critical_divergence M
    (M.case3HD_iff_hd_third.mp hHD3) (M.hTri_of_case3HD hHD3) htop hfin hβ hr₀ hderiv hpos
    hode hmeas hhedge h0 𝓔 h𝓔mono h𝓔 p hp hθ0 hθ1 hMa hc3 hgm

#print axioms case3_hAend_hAmid_cutPoly_source_of_case3HD_of_critical_divergence

/-! ## §2 The normalized `(I.4.21)` consumer without `hTri` -/

/-- **Case 3 of Proposition I.4.20, normalized form, with `hTri` derived from `(HD)(3)`.**

Same conclusion as `LowerTwoPoint.case3_i421_cutPoly_source_of_HD_case3_of_critical_divergence`,
with the triangle finiteness supplied by `TriangleFromHD` instead of assumed.  The root moment
range stays an explicit input of the induction. -/
theorem case3_i421_cutPoly_source_of_case3HD_of_critical_divergence (M : SourceModelData)
    (hHD3 : M.Case3HD)
    (htop : M.uncutMean M.betaCrit = ⊤)
    {f' h : ℝ → ℝ} {C r₀ : ℝ}
    (hfin : ∀ᶠ r : ℝ in atTop, M.cutMassAt r 0 ≠ ⊤)
    (hβ : (0 : ℝ) < M.betaCrit) (hr₀ : 0 < r₀)
    (hderiv : ∀ t : ℝ, r₀ ≤ t →
      HasDerivAt (fun r => (M.cutMassAt r 0).toReal) (f' t) t)
    (hpos : ∀ t : ℝ, r₀ ≤ t → 0 < (M.cutMassAt t 0).toReal)
    (hode : ∀ t : ℝ, r₀ ≤ t →
      f' t = (M.betaCrit : ℝ) * (1 - h t) * t ^ (-M.α - 1) *
        ((M.cutMassAt t 0).toReal) ^ 2)
    (hmeas : Measurable h) (hhedge : ∀ t : ℝ, r₀ ≤ t → |h t| ≤ C)
    (h0 : Tendsto h atTop (𝓝 0))
    (𝓔 : ℕ → Finset (Sym2 M.V)) (h𝓔mono : Monotone 𝓔)
    (h𝓔 : ∀ e : Sym2 M.V, ∃ n, e ∈ 𝓔 n) (p ℓ : ℕ) (hp : 1 ≤ p) (hℓ : ℓ + 1 ≤ p)
    {θ : ℝ} (hθ0 : 0 < θ) (hθ1 : θ < 1)
    (hmom : ∀ r : ℝ, 1 ≤ r → ∀ m : ℕ, 1 ≤ m → m ≤ p + 1 →
      I420Case1.powMomentAt (M.cutProb r) m (0 : M.V) ≠ ⊤)
    {c3 : ℝ} (hc3 : 0 < c3)
    (hgm : ∀ᶠ r in atTop, c3 * momOf (fun r => M.cutProb r) (0 : M.V) 1 r ^ 3
      ≤ momOf (fun r => M.cutProb r) (0 : M.V) 2 r) :
    ∃ c₁ C₁ : ℝ, 0 < c₁ ∧ 0 < C₁ ∧
      Tendsto (fun r => discR (M.cutProb r) (0 : M.V) (ℓ + 1) (p - ℓ)
          (BallAverage.ball_finite M r).toFinset /
        biasTarget (momOf (fun r => M.cutProb r) (0 : M.V) 1 r)
          (momOf (fun r => M.cutProb r) (0 : M.V) 2 r) p) atTop (𝓝 0) :=
  LowerTwoPoint.case3_i421_cutPoly_source_of_HD_case3_of_critical_divergence M
    (M.case3HD_iff_hd_third.mp hHD3) (M.hTri_of_case3HD hHD3) htop hfin hβ hr₀ hderiv hpos
    hode hmeas hhedge h0 𝓔 h𝓔mono h𝓔 p ℓ hp hℓ hθ0 hθ1 hmom hc3 hgm

#print axioms case3_i421_cutPoly_source_of_case3HD_of_critical_divergence

/-! ## §3 The reusable first-moment step

The paper's proof of Proposition I.4.2 uses the divergence of the uncut critical mean,
`E_{β_c}|K_0| = ⊤`, not the pointwise two-point lower bound `hlow` of Theorem I.2.14 (which needs
`α < 1` and is therefore unavailable at `d = 6, α = 2`).  `SourceModelData.first_moment_asymptotic_ae_of_critical_divergence`
implements that route on the a.e. off-corner analysis.  This lemma only supplies its two
bookkeeping inputs: eventual finiteness of the cutoff mass (from the second cutoff moment) and a
uniform bound on the (I.4.6) defect (from its vanishing). -/

/-- **The (I.4.6)-route first-moment asymptotic at the actual source balls**, with the cutoff-mass
finiteness and the uniform defect bound derived rather than assumed. -/
theorem firstMomentAsymptotic_of_critical_divergence_ae (M : SourceModelData)
    (htop : M.uncutMean M.betaCrit = ⊤)
    (T : ℕ → Finset M.V) (hTmono : Monotone T) (hT : ∀ y : M.V, ∃ n, y ∈ T n)
    (Se : ℕ → Finset (Sym2 M.V)) (hSmono : Monotone Se)
    (hS : ∀ e : Sym2 M.V, ∃ n, e ∈ Se n)
    {R a₀ r₀ : ℝ} (hRpos : 0 < R) (hRa₀ : R < a₀) (ha₀r₀ : a₀ < r₀)
    (hβ : (0 : ℝ) < M.betaCrit)
    (hlowenv : ∀ s : ℝ, R < s →
      (1 / 2) * s ^ (-(M.d : ℝ) - M.α - 1) ≤ |deriv M.K s|)
    (huppenv : ∀ s : ℝ, R < s →
      |deriv M.K s| ≤ 2 * s ^ (-(M.d : ℝ) - M.α - 1))
    (h2 : ∀ t : ℝ, a₀ ≤ t → M.cutMoment 2 t ≠ ⊤)
    (hcontinf : ∀ y : M.V, ∀ r : ℝ, a₀ ≤ r → ContinuousAt
      (sMomentInfFlux (0 : M.V) {y} (fun _ => (1 : ℝ)) M.cutProb M.cutEdgeDeriv) r)
    (hK : ∀ r : ℝ, a₀ ≤ r → ContinuousAt (fun r' => deriv M.K r') r)
    (hex : ∀ r : ℝ, a₀ ≤ r → ContinuousAt M.exclScalar r)
    (h0 : Tendsto (cutError M) atTop (𝓝 0)) :
    Tendsto (fun r : ℝ => (M.cutMassAt r 0).toReal
      / ((M.α / (M.betaCrit : ℝ)) * r ^ M.α)) atTop (𝓝 1) := by
  have hfin : ∀ᶠ r : ℝ in atTop, M.cutMassAt r 0 ≠ ⊤ :=
    Filter.eventually_atTop.2 ⟨max a₀ 1, fun t ht =>
      ne_top_of_le_ne_top (h2 t (le_trans (le_max_left _ _) ht))
        (E1Sign.cutMassAt_le_cutMoment_two M t)⟩
  obtain ⟨N, hN⟩ := (Metric.tendsto_atTop.1 h0) 1 zero_lt_one
  obtain ⟨Rdef, hRdef⟩ := eventually_atTop.1
    (Filter.eventually_atTop.2 ⟨N, fun t ht => by
      have hle : |cutError M t| ≤ 1 := by
        have h := hN t ht
        rw [Real.dist_eq, sub_zero] at h
        exact le_of_lt h
      simpa using hle⟩)
  have ha₀ : a₀ < max r₀ Rdef := lt_of_lt_of_le ha₀r₀ (le_max_left _ _)
  have hbound : ∀ t : ℝ, max r₀ Rdef ≤ t → |cutError M t| ≤ 1 := fun t ht =>
    hRdef t (le_trans (le_max_right _ _) ht)
  exact M.first_moment_asymptotic_ae_of_critical_divergence T hTmono hT Se hSmono hS
    hRpos hRa₀ ha₀ hβ hlowenv huppenv h2 hcontinf hK hex htop hfin
    (C := 1) hbound h0

#print axioms firstMomentAsymptotic_of_critical_divergence_ae

/-! ## §4 The full closures: `hTri`, `hTail`, `hP`, `hgm` and the root moments derived -/

/-- **Case 3 of Proposition I.4.20 at the genuine source balls, from `(HD)(3)`, the
critical-mean divergence, the off-corner envelope package, the uncut critical volume tail and a
finite critical cutoff first moment.**

The conclusion is the normalized (I.4.21) discrepancy limit.  The hypotheses `hTri`, `hTail`,
`hP`, `hgm`, the root moment range, the measurability of the defect, the absolute continuity of
the cutoff mass, and the eventual finiteness of the cutoff mass are all *derived*; the list kept
is exactly the set of source inputs listed in the file header. -/
theorem exists_case3_i421_cutPoly_source_of_case3HD (M : SourceModelData)
    (hHD3 : M.Case3HD)
    (htop : M.uncutMean M.betaCrit = ⊤)
    (T : ℕ → Finset M.V) (hTmono : Monotone T) (hT : ∀ y : M.V, ∃ n, y ∈ T n)
    (Se : ℕ → Finset (Sym2 M.V)) (hSmono : Monotone Se)
    (hS : ∀ e : Sym2 M.V, ∃ n, e ∈ Se n)
    {R a₀ r₀ : ℝ} (hRpos : 0 < R) (hRa₀ : R < a₀) (ha₀r₀ : a₀ < r₀)
    (hβ : (0 : ℝ) < M.betaCrit)
    (hlowenv : ∀ s : ℝ, R < s →
      (1 / 2) * s ^ (-(M.d : ℝ) - M.α - 1) ≤ |deriv M.K s|)
    (huppenv : ∀ s : ℝ, R < s →
      |deriv M.K s| ≤ 2 * s ^ (-(M.d : ℝ) - M.α - 1))
    (h2 : ∀ t : ℝ, a₀ ≤ t → M.cutMoment 2 t ≠ ⊤)
    (hcontinf : ∀ y : M.V, ∀ r : ℝ, a₀ ≤ r → ContinuousAt
      (sMomentInfFlux (0 : M.V) {y} (fun _ => (1 : ℝ)) M.cutProb M.cutEdgeDeriv) r)
    (hK : ∀ r : ℝ, a₀ ≤ r → ContinuousAt (fun r' => deriv M.K r') r)
    (hex : ∀ r : ℝ, a₀ ≤ r → ContinuousAt M.exclScalar r)
    (h0 : Tendsto (cutError M) atTop (𝓝 0))
    (𝓔 : ℕ → Finset (Sym2 M.V)) (h𝓔mono : Monotone 𝓔)
    (h𝓔 : ∀ e : Sym2 M.V, ∃ n, e ∈ 𝓔 n) (p ℓ : ℕ) (hp : 1 ≤ p) (hℓ : ℓ + 1 ≤ p)
    {θ : ℝ} (hθ0 : 0 < θ) (hθ1 : θ < 1)
    {Cvol : ℝ} (hCvol : 0 ≤ Cvol)
    (hVolTail : ∀ n : ℕ, 1 ≤ n →
      M.criticalLaw {ω : Config M.V | (n : ℝ≥0∞) ≤ clusterVol ω (0 : M.V)} ≤
        Analysis.Route3.tailEnvelope Cvol n)
    (h1 : ∀ r : ℝ, 1 ≤ r → M.cutMoment 1 r ≠ ⊤) :
    ∃ c₀ C₀ : ℝ, 0 < c₀ ∧ 0 < C₀ ∧
      Tendsto (fun r => discR (M.cutProb r) (0 : M.V) (ℓ + 1) (p - ℓ)
          (BallAverage.ball_finite M r).toFinset /
        biasTarget (momOf (fun r => M.cutProb r) (0 : M.V) 1 r)
          (momOf (fun r => M.cutProb r) (0 : M.V) 2 r) p) atTop (𝓝 0) := by
  have hData := M.case3TriangleTailData_of_case3HD hHD3
  exact exists_case3_i421_cutPoly_source_of_tail_of_first M
    (firstMomentAsymptotic_of_critical_divergence_ae M htop T hTmono hT Se hSmono hS
      hRpos hRa₀ ha₀r₀ hβ hlowenv huppenv h2 hcontinf hK hex h0)
    hData.openTriangle_lt_top 𝓔 h𝓔mono h𝓔 p ℓ hp hℓ hθ0 hθ1
    hData.tendsto_nablaTail hCvol hVolTail h1

#print axioms exists_case3_i421_cutPoly_source_of_case3HD

/-- **The `(I.4.21)` decorrelation estimate for every `0 ≤ ℓ ≤ p − 1`.**

The paper's second induction (proof of Proposition I.4.20) needs the normalized estimate for
*every* `ℓ` in that range, not just one; this is the uniformly quantified form of
`exists_case3_i421_cutPoly_source_of_case3HD`, with the same hypotheses. -/
theorem forall_case3_i421_cutPoly_source_of_case3HD (M : SourceModelData)
    (hHD3 : M.Case3HD)
    (htop : M.uncutMean M.betaCrit = ⊤)
    (T : ℕ → Finset M.V) (hTmono : Monotone T) (hT : ∀ y : M.V, ∃ n, y ∈ T n)
    (Se : ℕ → Finset (Sym2 M.V)) (hSmono : Monotone Se)
    (hS : ∀ e : Sym2 M.V, ∃ n, e ∈ Se n)
    {R a₀ r₀ : ℝ} (hRpos : 0 < R) (hRa₀ : R < a₀) (ha₀r₀ : a₀ < r₀)
    (hβ : (0 : ℝ) < M.betaCrit)
    (hlowenv : ∀ s : ℝ, R < s →
      (1 / 2) * s ^ (-(M.d : ℝ) - M.α - 1) ≤ |deriv M.K s|)
    (huppenv : ∀ s : ℝ, R < s →
      |deriv M.K s| ≤ 2 * s ^ (-(M.d : ℝ) - M.α - 1))
    (h2 : ∀ t : ℝ, a₀ ≤ t → M.cutMoment 2 t ≠ ⊤)
    (hcontinf : ∀ y : M.V, ∀ r : ℝ, a₀ ≤ r → ContinuousAt
      (sMomentInfFlux (0 : M.V) {y} (fun _ => (1 : ℝ)) M.cutProb M.cutEdgeDeriv) r)
    (hK : ∀ r : ℝ, a₀ ≤ r → ContinuousAt (fun r' => deriv M.K r') r)
    (hex : ∀ r : ℝ, a₀ ≤ r → ContinuousAt M.exclScalar r)
    (h0 : Tendsto (cutError M) atTop (𝓝 0))
    (𝓔 : ℕ → Finset (Sym2 M.V)) (h𝓔mono : Monotone 𝓔)
    (h𝓔 : ∀ e : Sym2 M.V, ∃ n, e ∈ 𝓔 n) (p : ℕ) (hp : 1 ≤ p)
    {θ : ℝ} (hθ0 : 0 < θ) (hθ1 : θ < 1)
    {Cvol : ℝ} (hCvol : 0 ≤ Cvol)
    (hVolTail : ∀ n : ℕ, 1 ≤ n →
      M.criticalLaw {ω : Config M.V | (n : ℝ≥0∞) ≤ clusterVol ω (0 : M.V)} ≤
        Analysis.Route3.tailEnvelope Cvol n)
    (h1 : ∀ r : ℝ, 1 ≤ r → M.cutMoment 1 r ≠ ⊤) :
    ∀ ℓ : ℕ, ℓ + 1 ≤ p → ∃ c₀ C₀ : ℝ, 0 < c₀ ∧ 0 < C₀ ∧
      Tendsto (fun r => discR (M.cutProb r) (0 : M.V) (ℓ + 1) (p - ℓ)
          (BallAverage.ball_finite M r).toFinset /
        biasTarget (momOf (fun r => M.cutProb r) (0 : M.V) 1 r)
          (momOf (fun r => M.cutProb r) (0 : M.V) 2 r) p) atTop (𝓝 0) :=
  fun ℓ hℓ => exists_case3_i421_cutPoly_source_of_case3HD M hHD3 htop T hTmono hT Se hSmono hS
    hRpos hRa₀ ha₀r₀ hβ hlowenv huppenv h2 hcontinf hK hex h0 𝓔 h𝓔mono h𝓔 p ℓ hp hℓ hθ0 hθ1
    hCvol hVolTail h1

#print axioms forall_case3_i421_cutPoly_source_of_case3HD

/-- **Case 3 of Proposition I.4.20, direct (unnormalized) form**, with the same derived inputs as
`exists_case3_i421_cutPoly_source_of_case3HD`: the endpoint and middle-index ratio limits at the
genuine source balls. -/
theorem case3_hAend_hAmid_cutPoly_source_of_case3HD (M : SourceModelData)
    (hHD3 : M.Case3HD)
    (htop : M.uncutMean M.betaCrit = ⊤)
    (T : ℕ → Finset M.V) (hTmono : Monotone T) (hT : ∀ y : M.V, ∃ n, y ∈ T n)
    (Se : ℕ → Finset (Sym2 M.V)) (hSmono : Monotone Se)
    (hS : ∀ e : Sym2 M.V, ∃ n, e ∈ Se n)
    {R a₀ r₀ : ℝ} (hRpos : 0 < R) (hRa₀ : R < a₀) (ha₀r₀ : a₀ < r₀)
    (hβ : (0 : ℝ) < M.betaCrit)
    (hlowenv : ∀ s : ℝ, R < s →
      (1 / 2) * s ^ (-(M.d : ℝ) - M.α - 1) ≤ |deriv M.K s|)
    (huppenv : ∀ s : ℝ, R < s →
      |deriv M.K s| ≤ 2 * s ^ (-(M.d : ℝ) - M.α - 1))
    (h2 : ∀ t : ℝ, a₀ ≤ t → M.cutMoment 2 t ≠ ⊤)
    (hcontinf : ∀ y : M.V, ∀ r : ℝ, a₀ ≤ r → ContinuousAt
      (sMomentInfFlux (0 : M.V) {y} (fun _ => (1 : ℝ)) M.cutProb M.cutEdgeDeriv) r)
    (hK : ∀ r : ℝ, a₀ ≤ r → ContinuousAt (fun r' => deriv M.K r') r)
    (hex : ∀ r : ℝ, a₀ ≤ r → ContinuousAt M.exclScalar r)
    (h0 : Tendsto (cutError M) atTop (𝓝 0))
    (𝓔 : ℕ → Finset (Sym2 M.V)) (h𝓔mono : Monotone 𝓔)
    (h𝓔 : ∀ e : Sym2 M.V, ∃ n, e ∈ 𝓔 n) (p : ℕ) (hp : 3 ≤ p)
    {θ : ℝ} (hθ0 : 0 < θ) (hθ1 : θ < 1)
    {Cvol : ℝ} (hCvol : 0 ≤ Cvol)
    (hVolTail : ∀ n : ℕ, 1 ≤ n →
      M.criticalLaw {ω : Config M.V | (n : ℝ≥0∞) ≤ clusterVol ω (0 : M.V)} ≤
        Analysis.Route3.tailEnvelope Cvol n)
    (h1 : ∀ r : ℝ, 1 ≤ r → M.cutMoment 1 r ≠ ⊤) :
    Tendsto (fun r => I420Case1.mixedExclR (M.cutProb r) (0 : M.V) 1 p
          (BallAverage.ball_finite M r).toFinset /
        (ballCard (fun r => (BallAverage.ball_finite M r).toFinset) r *
          (momOf (fun r => M.cutProb r) (0 : M.V) 1 r *
            momOf (fun r => M.cutProb r) (0 : M.V) p r))) atTop (𝓝 1) ∧
      ∀ ℓ, 1 ≤ ℓ → ℓ ≤ p - 2 → Tendsto
        (fun r => I420Case1.mixedExclR (M.cutProb r) (0 : M.V) (ℓ + 1) (p - ℓ)
            (BallAverage.ball_finite M r).toFinset /
          (ballCard (fun r => (BallAverage.ball_finite M r).toFinset) r *
            (momOf (fun r => M.cutProb r) (0 : M.V) (ℓ + 1) r *
              momOf (fun r => M.cutProb r) (0 : M.V) (p - ℓ) r))) atTop (𝓝 1) := by
  have hData := M.case3TriangleTailData_of_case3HD hHD3
  exact case3_hAend_hAmid_cutPoly_source_of_tail_of_first M
    (firstMomentAsymptotic_of_critical_divergence_ae M htop T hTmono hT Se hSmono hS
      hRpos hRa₀ ha₀r₀ hβ hlowenv huppenv h2 hcontinf hK hex h0)
    hData.openTriangle_lt_top 𝓔 h𝓔mono h𝓔 p hp hθ0 hθ1
    hData.tendsto_nablaTail hCvol hVolTail h1

#print axioms case3_hAend_hAmid_cutPoly_source_of_case3HD

end I420Case3

/-! ## §5 A note on the near-diagonal reading of `Case3HD`

In the source, `(log ‖x − y‖)^{-1}` is used with the convention that the nearest-neighbour distance
is `1`, where the factor is `+∞` and the bound is vacuous.  In Lean, `(Real.log 1)⁻¹ = 0`, so the
same literal formula is *maximally strong* there.  The two lemmas below record the exact
consequence: `Case3HD` forces `ρ > 1` on every pair whose connection probability is positive, i.e.
it requires the closed unit ball of the normalized source norm to contain no nonzero lattice point
that the critical two-point function charges.

This is a statement about the formalized hypothesis, not a claim that `Case3HD` is unattainable:
`ρ = 2 ‖·‖_∞` satisfies `unitBall_volume` in every dimension and has `ρ ≥ 2` off the diagonal. -/

namespace Orchestration
namespace SourceModelData

variable (M : SourceModelData)

/-- **`Case3HD` fails at a pair with `ρ ≤ 1` and positive connection probability.**  The Lean
reading of the factor `(log ρ)^{-1}` is `≤ 0` there, so the claimed two-point bound becomes
`twoPoint ≤ 0`. -/
theorem not_case3HD_of_srcNorm_le_one {x y : M.V} (hxy : x ≠ y)
    (hpos : 0 < M.twoPoint M.betaCrit x y)
    (hρ : M.S.ρ (toVec (x - y)) ≤ 1) : ¬ M.Case3HD := by
  rintro ⟨-, -, C, hC, hb⟩
  have hρpos : 0 < M.S.ρ (toVec (x - y)) := M.S.ρ_pos _ (by
    intro hc
    exact hxy (by
      funext i
      have h1 : (((x i : ℤ) - (y i : ℤ) : ℤ) : ℝ) = 0 := by
        simpa [toVec] using congrFun hc i
      have h2 : (x i : ℤ) - (y i : ℤ) = 0 := by exact_mod_cast h1
      exact sub_eq_zero.mp h2))
  have hlog : Real.log (M.S.ρ (toVec (x - y))) ≤ 0 := Real.log_nonpos hρpos.le hρ
  have hinv : (Real.log (M.S.ρ (toVec (x - y))))⁻¹ ≤ 0 := inv_nonpos.mpr hlog
  have hpow : (0 : ℝ) < (M.S.ρ (toVec (x - y))) ^ (-(M.d : ℝ) + 2) :=
    Real.rpow_pos_of_pos hρpos _
  have hle0 : C * (Real.log (M.S.ρ (toVec (x - y))))⁻¹
      * (M.S.ρ (toVec (x - y))) ^ (-(M.d : ℝ) + 2) ≤ 0 :=
    mul_nonpos_of_nonpos_of_nonneg
      (mul_nonpos_of_nonneg_of_nonpos hC.le hinv) hpow.le
  have := hb x y hxy
  linarith

/-- **The constraint carried by `Case3HD`:** on every pair with positive connection probability,
the normalized source norm of the difference exceeds one. -/
theorem one_lt_srcNorm_of_case3HD (h : M.Case3HD) {x y : M.V} (hxy : x ≠ y)
    (hpos : 0 < M.twoPoint M.betaCrit x y) : 1 < M.S.ρ (toVec (x - y)) := by
  by_contra hcon
  exact M.not_case3HD_of_srcNorm_le_one hxy hpos (not_lt.1 hcon) h

end SourceModelData
end Orchestration

/-! ## §6 Axiom audit of the derivation chain this file depends on

These are not part of the deliverable's statements; they certify that the `hTri`/`hTail`
derivation and every consumer used above are sorry-free, so the three standard axioms reported
for the theorems of §1–§5 are the only axiomatic content of the assembly. -/

#print axioms PercLib.CriticalLRP.Orchestration.SourceModelData.openTriangleSelf_lt_top_of_case3
#print axioms PercLib.CriticalLRP.Orchestration.SourceModelData.not_case3HD_of_srcNorm_le_one
#print axioms PercLib.CriticalLRP.Orchestration.SourceModelData.one_lt_srcNorm_of_case3HD
#print axioms PercLib.CriticalLRP.Orchestration.SourceModelData.hTri_of_case3HD
#print axioms PercLib.CriticalLRP.Orchestration.SourceModelData.hTail_of_case3HD
#print axioms PercLib.CriticalLRP.Orchestration.SourceModelData.case3TriangleTailData_of_case3HD
#print axioms PercLib.CriticalLRP.Orchestration.SourceModelData.isLogErrorFunction_nablaTail_of_case3
#print axioms PercLib.CriticalLRP.Orchestration.SourceModelData.first_moment_asymptotic_ae_of_critical_divergence
#print axioms PercLib.CriticalLRP.I420Case3.exists_case3_i421_cutPoly_source_of_tail_of_first
#print axioms PercLib.CriticalLRP.I420Case3.case3_hAend_hAmid_cutPoly_source_of_tail_of_first
#print axioms PercLib.CriticalLRP.LowerTwoPoint.case3_i421_cutPoly_source_of_HD_case3_of_critical_divergence

end PercLib.CriticalLRP
