/-
Copyright (c) 2026 PercLib contributors. Released under Apache 2.0.

# Large-distance HD(3) closures of the normalized Case-3 decorrelation estimates

This uses the established `TriangleFromHD.LargeDistance.Bridge` implications. It
corrects the short-distance issue in `HDClosure/Main.lean` without removing any
of the actual volume-tail, sharpness, continuity, defect, or derivative inputs.
The older `Case3HD` consumers remain available as legacy conditional wrappers,
but the products exported here do not require that literal hypothesis. No
nontrivial critical large-distance estimate is constructed.

Accepted and independently rebuilt from the full-closure part of `smwznoz6j/m5`,
with `Case3HD` replaced by `Case3HDLarge`. Review at production HEAD
`bd25afb1130f7fe93446b447f9a68a4d3aba08cc`.
-/
module

public import PercLib.CriticalLRP.VolumeMoments.HigherMoments.I420Case3.HDClosure.Main
public import PercLib.CriticalLRP.Analysis.SecondMomentCase3.TriangleFromHD.LargeDistance.Bridge

/-! ## I.4.21 and direct decorrelation from the large-distance HD premise

These preserve the original conclusions and genuine probabilistic inputs while
using only the positive-log majorant whose critical estimate is still open.
-/

set_option linter.style.longLine false
set_option linter.hashCommand false
@[expose] public section

noncomputable section

open MeasureTheory Measure ProbabilityTheory unitInterval Filter Topology
open scoped ENNReal NNReal Topology

namespace PercLib.CriticalLRP.Orchestration.SourceModelData

variable (M : SourceModelData)

/-- The finite triangle from the large-distance HD(3) premise. -/
theorem hTri_of_case3HDLarge (h : M.Case3HDLarge) :
    TriTail.openTriangleSelf M.kernel M.kernel_nonneg M.betaCrit 0 < ⊤ :=
  M.openTriangleSelf_lt_top_of_case3HDLarge h

/-- The logarithmic-integrable/vanishing tail from the large-distance premise. -/
theorem hTail_of_case3HDLarge (h : M.Case3HDLarge) :
    Tendsto (fun r : ℝ => (M.nablaTail r).toReal) atTop (𝓝 0) :=
  (M.isLogErrorFunction_nablaTail_of_case3HDLarge h).2

/-- The reusable structural input package from the large-distance premise. -/
theorem case3TriangleTailData_of_case3HDLarge (h : M.Case3HDLarge) :
    M.Case3TriangleTailData :=
  ⟨M.hTri_of_case3HDLarge h, M.isLogErrorFunction_nablaTail_of_case3HDLarge h⟩

end PercLib.CriticalLRP.Orchestration.SourceModelData

namespace PercLib.CriticalLRP.I420Case3

open PercLib.CriticalLRP.Orchestration

/-! ## §4 The full closures: `hTri`, `hTail`, `hP`, `hgm` and the root moments derived -/

/-- **Case 3 of Proposition I.4.20 at the genuine source balls, from `(HD)(3)`, the
critical-mean divergence, the off-corner envelope package, the uncut critical volume tail and a
finite critical cutoff first moment.**

The conclusion is the normalized (I.4.21) discrepancy limit.  The hypotheses `hTri`, `hTail`,
`hP`, `hgm`, the root moment range, the measurability of the defect, the absolute continuity of
the cutoff mass, and the eventual finiteness of the cutoff mass are all *derived*; the list kept
is exactly the set of source inputs listed in the file header. -/
theorem exists_case3_i421_cutPoly_source_of_case3HDLarge (M : SourceModelData)
    (hHD3 : M.Case3HDLarge)
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
  have hData := M.case3TriangleTailData_of_case3HDLarge hHD3
  exact exists_case3_i421_cutPoly_source_of_tail_of_first M
    (firstMomentAsymptotic_of_critical_divergence_ae M htop T hTmono hT Se hSmono hS
      hRpos hRa₀ ha₀r₀ hβ hlowenv huppenv h2 hcontinf hK hex h0)
    hData.openTriangle_lt_top 𝓔 h𝓔mono h𝓔 p ℓ hp hℓ hθ0 hθ1
    hData.tendsto_nablaTail hCvol hVolTail h1

#print axioms exists_case3_i421_cutPoly_source_of_case3HDLarge

/-- **The `(I.4.21)` decorrelation estimate for every `0 ≤ ℓ ≤ p − 1`.**

The paper's second induction (proof of Proposition I.4.20) needs the normalized estimate for
*every* `ℓ` in that range, not just one; this is the uniformly quantified form of
`exists_case3_i421_cutPoly_source_of_case3HDLarge`, with the same hypotheses. -/
theorem forall_case3_i421_cutPoly_source_of_case3HDLarge (M : SourceModelData)
    (hHD3 : M.Case3HDLarge)
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
  fun ℓ hℓ => exists_case3_i421_cutPoly_source_of_case3HDLarge M hHD3 htop T hTmono hT Se hSmono hS
    hRpos hRa₀ ha₀r₀ hβ hlowenv huppenv h2 hcontinf hK hex h0 𝓔 h𝓔mono h𝓔 p ℓ hp hℓ hθ0 hθ1
    hCvol hVolTail h1

#print axioms forall_case3_i421_cutPoly_source_of_case3HDLarge

/-- **Case 3 of Proposition I.4.20, direct (unnormalized) form**, with the same derived inputs as
`exists_case3_i421_cutPoly_source_of_case3HDLarge`: the endpoint and middle-index ratio limits at the
genuine source balls. -/
theorem case3_hAend_hAmid_cutPoly_source_of_case3HDLarge (M : SourceModelData)
    (hHD3 : M.Case3HDLarge)
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
  have hData := M.case3TriangleTailData_of_case3HDLarge hHD3
  exact case3_hAend_hAmid_cutPoly_source_of_tail_of_first M
    (firstMomentAsymptotic_of_critical_divergence_ae M htop T hTmono hT Se hSmono hS
      hRpos hRa₀ ha₀r₀ hβ hlowenv huppenv h2 hcontinf hK hex h0)
    hData.openTriangle_lt_top 𝓔 h𝓔mono h𝓔 p hp hθ0 hθ1
    hData.tendsto_nablaTail hCvol hVolTail h1

#print axioms case3_hAend_hAmid_cutPoly_source_of_case3HDLarge

end PercLib.CriticalLRP.I420Case3

/-! ## Axiom audit -/

#print axioms PercLib.CriticalLRP.Orchestration.SourceModelData.hTri_of_case3HDLarge
#print axioms PercLib.CriticalLRP.Orchestration.SourceModelData.hTail_of_case3HDLarge
#print axioms PercLib.CriticalLRP.Orchestration.SourceModelData.case3TriangleTailData_of_case3HDLarge
#print axioms PercLib.CriticalLRP.I420Case3.exists_case3_i421_cutPoly_source_of_case3HDLarge
#print axioms PercLib.CriticalLRP.I420Case3.forall_case3_i421_cutPoly_source_of_case3HDLarge
#print axioms PercLib.CriticalLRP.I420Case3.case3_hAend_hAmid_cutPoly_source_of_case3HDLarge
