/-
Ultramath swarm `smwzlje3f`, member `m8`, direction `d1` (brief direction (H)).

Copyright (c) 2026 PercLib contributors. Released under Apache 2.0.

Accepted and independently rebuilt from Ultramath `smwzlje3f`.
Production base `a59bc6c22aba42e69160666c17feac870d4cb887`; reviewed scratch source `.ultramath/smwzlje3f/m8/I420Consumer.lean`.

Production worktree read (read-only): `.scratch/critical-lrp-orchestration`,
HEAD `5d2d681b941eb1c687f1ba17e6a798b8f0175aa0`, Lean pin `leanprover/lean4:v4.35.0`.

# The I.4.19 / I.4.20 consumer with Proposition I.4.15 Case 3 *derived*, not assumed

`RatioInduction/Handoff.case3_moment_three_bound_of_HD_case3` concludes the paper's cubic bound

`E|K|³ ≤ (1+o(1))·3·(E|K|²/E|K|)²·E|K|`

from the Case-3 decorrelation limits.  Its hypothesis `hRV2` is

`RegularlyVaryingAtTop (fun r => E_{β_c,r}|K|²) (3α)`,

which is *exactly the conclusion of Proposition I.4.15, Case 3* — so as stated the I.4.20 step
assumes the theorem whose proof it is a step of.  Production has since proved that conclusion from
the paper's own hypotheses with the `(2,1)` product gap in place of the refuted `q = 0` star
(`ProductGap/SourceConsumer.secondMoment_asymptotic_case3_of_source_p21`, via
`regularlyVarying_two_of_source_p21`).

This file removes `hRV2` from the consumer and replaces it by the inputs that theorem actually
consumes at the model:

* `hac`, `hae` — the corner-safe radial regularity of `r ↦ E_{β_c,r}|K|²` (absolute continuity
  on compact windows and the a.e. identity
  `d/dr E|K|² = β_c(-K')(r)·(excluded masses)`); the measurability of the right-hand side is
  *derived* from tail finiteness of the second moment, so it is not an input,
* `hP` — the first-moment asymptotic (Proposition I.4.2),
* `hTri`, `hF` — the finite triangle condition and the open-triangle log-radial bound
  (Lemma I.4.13), with its constants `C₀`, `p`,

all of which are already paper-level inputs of the Case-3 route.  Nothing else changes: the
`(HD)(3)` package, the first-moment ODE data, the root moment range `hMa`, the moment gap `hgm`
(in the `momOf` spelling, which is `rfl`-equal to the `cutMoment` spelling of the product route),
the derivative identity, the normalization and the conclusion are verbatim those of
`case3_moment_three_bound_of_HD_case3`.

`h1`/`h2` — the finiteness of the first two cutoff moments on the whole tail `[r₀,∞)` that the
product route asks for — are **derived** here from `hMa` (root moment range up to order `4` at
`r ≥ 1`) and the radius monotonicity `cutMoment_monotone`; they are not new hypotheses.

No `sorry`, no custom axioms, no weakened constants or normalizations.
-/
module

public import PercLib.CriticalLRP.VolumeMoments.HigherMoments.I420Case3.RatioInduction.Handoff
public import PercLib.CriticalLRP.Analysis.SecondMomentCase3.ProductGap.SourceConsumer
public import PercLib.CriticalLRP.Analysis.AEHigherMoments.CubicModel
public import PercLib.CriticalLRP.VolumeMoments.HigherMoments.I420Case3.RatioInduction.Asymptotic
public import PercLib.CriticalLRP.Analysis.SecondMomentMeasurability.Consumers

/-! # The I.4.19 cubic bound with the Case-3 second-moment regular variation derived -/

noncomputable section

open MeasureTheory Filter Topology Set
open scoped ENNReal Topology

set_option linter.unusedSectionVars false

@[expose] public section

namespace PercLib.CriticalLRP

namespace I420Case3

open Orchestration
open PercLib.CriticalLRP.VolumeMoments.HigherMoments
open PercLib.CriticalLRP.Analysis.AE

variable (M : SourceModelData)

/-- **Finiteness of the first two cutoff moments on the whole tail**, from the root moment range
`hMa` at `r ≥ 1` plus the radius monotonicity of the cutoff moment. -/
theorem cutMoment_one_two_ne_top_of_hMa {r₀ : ℝ}
    (hMa : ∀ (r : ℝ), 1 ≤ r → ∀ ℓ : ℕ, ℓ ≤ 3 →
      I420Case1.powMomentAt (M.cutProb r) (ℓ + 1) (0 : M.V) ≠ ⊤) :
    (∀ t : ℝ, r₀ ≤ t → M.cutMoment 1 t ≠ ⊤) ∧
      (∀ t : ℝ, r₀ ≤ t → M.cutMoment 2 t ≠ ⊤) := by
  have hkey : ∀ m : ℕ, 1 ≤ m → m ≤ 2 → ∀ t : ℝ, M.cutMoment m t ≠ ⊤ := by
    intro m hm1 hm2 t
    rcases le_or_gt 1 t with hge | hlt
    · have h := hMa t hge (m - 1) (by omega)
      rwa [M.powMomentAt_cutProb_eq_cutMoment, Nat.sub_add_cancel hm1] at h
    · have h := hMa 1 le_rfl (m - 1) (by omega)
      rw [M.powMomentAt_cutProb_eq_cutMoment, Nat.sub_add_cancel hm1] at h
      exact ne_top_of_le_ne_top h (M.cutMoment_monotone m hlt.le)
  exact ⟨fun t _ => hkey 1 (by omega) (by omega) t, fun t _ => hkey 2 (by omega) (by omega) t⟩

/-- **The Case-3 second-moment regular variation of the product route**, in the `momOf`
spelling used by the higher-moment packet (`momOf_cutProb_eq_toReal_cutMoment` is `rfl`).

Assembled here from the two halves that make the dependency visible:

* the **numerator half** — `p2ExclError_tendsto_zero_of_source_p21`, i.e. `𝓔_{2,r} → 0` from the
  proved `(2,1)` product gap plus the moment gap and the triangle/log-radial inputs;
* the **analytic half** — `regularlyVarying_two_of_hP_of_ae_deriv_no_hmR`, the ODE
  `f' ∼ (3α/r)f` passage, which is already free of the measurability input `Measurable
  M.rhsScalarTwo` (`SecondMomentMeasurability.Consumers` derives that from `h2`). -/
theorem momOf_two_regularlyVarying_of_source_p21 (hα : 0 < M.α) {r₀ : ℝ} (hr₀ : 0 < r₀)
    (hβ : (M.betaCrit : ℝ) ≠ 0)
    (hac : ∀ R : ℝ, r₀ ≤ R → AbsolutelyContinuousOnInterval
      (fun r : ℝ => (M.cutMoment 2 r).toReal) r₀ R)
    (hae : ∀ᵐ t ∂(volume.restrict (Ici r₀)),
      HasDerivAt (fun r : ℝ => (M.cutMoment 2 r).toReal) (M.rhsScalarTwo t) t)
    (h1 : ∀ t : ℝ, r₀ ≤ t → M.cutMoment 1 t ≠ ⊤)
    (h2 : ∀ t : ℝ, r₀ ≤ t → M.cutMoment 2 t ≠ ⊤)
    (hP : Tendsto (fun r : ℝ => (M.cutMassAt r 0).toReal
      / ((M.α / (M.betaCrit : ℝ)) * r ^ M.α)) atTop (𝓝 1))
    (hTri : TriTail.openTriangleSelf M.kernel M.kernel_nonneg M.betaCrit 0 < ⊤)
    {C₀ p : ℝ} (hC₀ : 0 ≤ C₀) (hp : 1 < p)
    (hF : Analysis.LogRadialBound (fun y : M.V => M.S.dist (0 : M.V) y)
      (fun y : M.V => TriTail.openTriangle M.kernel M.kernel_nonneg M.betaCrit 0 y) C₀ p)
    {c3 : ℝ} (hc3 : 0 < c3)
    (hgm : ∀ᶠ r : ℝ in atTop, c3 * (M.cutMassAt r 0).toReal ^ 3 ≤ (M.cutMoment 2 r).toReal) :
    Analysis.RegularlyVaryingAtTop
      (fun r => I420Case3.momOf (fun r => M.cutProb r) (0 : M.V) 2 r) (3 * M.α) :=
  M.regularlyVarying_two_of_hP_of_ae_deriv_no_hmR hα hr₀ hβ hac hae h1 h2 hP
    (M.p2ExclError_tendsto_zero_of_source_p21 h1 h2 hP hTri hC₀ hp hF hc3 hgm)

/-- **The cubic (I.4.19) upper moment bound at the actual source cutoff family, with the
Case-3 regular variation of `E|K|²` derived rather than assumed.**

This is `case3_moment_three_bound_of_HD_case3` with the hypothesis

`hRV2 : RegularlyVaryingAtTop (fun r => E_{β_c,r}|K|²) (3α)`

— the conclusion of Proposition I.4.15, Case 3 — replaced by the model inputs `hac`, `hae`,
`hP` and the triangle/log-radial data `hTri`, `hF`, `C₀`, `p`.  The product-gap Case-3 numerator
consumer `secondMoment_asymptotic_case3_of_source_p21` supplies the rest.  Every other hypothesis
and the conclusion are unchanged. -/
theorem case3_moment_three_bound_of_HD_case3_of_p21 (M : SourceModelData)
    (hHD3 : M.d = 6 ∧ M.α = 2 ∧ ∃ C : ℝ, 0 < C ∧ ∀ x y : M.V, x ≠ y →
      M.twoPoint M.betaCrit x y ≤ C * (Real.log (M.S.ρ (toVec (x - y))))⁻¹ *
        (M.S.ρ (toVec (x - y))) ^ (-(M.d : ℝ) + 2))
    (hTri : TriTail.openTriangleSelf M.kernel M.kernel_nonneg M.betaCrit 0 < ⊤)
    {f' h : ℝ → ℝ} {c C r₀ : ℝ} (hc : 0 < c) (hαd : M.α < (M.d : ℝ))
    (hlow : ∀ x : M.V, x ≠ 0 →
      c * (M.S.dist 0 x) ^ (-(M.d : ℝ) + M.α) ≤ M.twoPoint M.betaCrit 0 x)
    (hfin : ∀ᶠ r : ℝ in atTop, M.cutMassAt r 0 ≠ ⊤)
    (hβ : (0 : ℝ) < M.betaCrit) (hr₀ : 0 < r₀)
    (hderiv : ∀ t, r₀ ≤ t →
      HasDerivAt (fun r => (M.cutMassAt r 0).toReal) (f' t) t)
    (hpos : ∀ t, r₀ ≤ t → 0 < (M.cutMassAt t 0).toReal)
    (hode : ∀ t, r₀ ≤ t →
      f' t = (M.betaCrit : ℝ) * (1 - h t) * t ^ (-M.α - 1) *
        ((M.cutMassAt t 0).toReal) ^ 2)
    (hmeas : Measurable h) (hhedge : ∀ t, r₀ ≤ t → |h t| ≤ C)
    (h0 : Tendsto h atTop (𝓝 0))
    (𝓔 : ℕ → Finset (Sym2 M.V)) (h𝓔mono : Monotone 𝓔)
    (h𝓔 : ∀ e : Sym2 M.V, ∃ n, e ∈ 𝓔 n)
    {θ : ℝ} (hθ0 : 0 < θ) (hθ1 : θ < 1)
    (hMa : ∀ (r : ℝ), 1 ≤ r → ∀ ℓ : ℕ, ℓ ≤ 3 →
      I420Case1.powMomentAt (M.cutProb r) (ℓ + 1) (0 : M.V) ≠ ⊤)
    {c3 : ℝ} (hc3 : 0 < c3)
    (hgm : ∀ᶠ r in atTop, c3 * momOf (fun r => M.cutProb r) (0 : M.V) 1 r ^ 3
      ≤ momOf (fun r => M.cutProb r) (0 : M.V) 2 r)
    (hmommeas1 : Measurable (fun r =>
      momOf (fun r => M.cutProb r) (0 : M.V) 1 r))
    (hmommeas2 : Measurable (fun r =>
      momOf (fun r => M.cutProb r) (0 : M.V) 2 r))
    (hRV1 : Analysis.RegularlyVaryingAtTop
      (fun r => momOf (fun r => M.cutProb r) (0 : M.V) 1 r) M.α)
    (hac : ∀ R : ℝ, r₀ ≤ R → AbsolutelyContinuousOnInterval
      (fun r : ℝ => (M.cutMoment 2 r).toReal) r₀ R)
    (hae : ∀ᵐ t ∂(volume.restrict (Ici r₀)),
      HasDerivAt (fun r : ℝ => (M.cutMoment 2 r).toReal) (M.rhsScalarTwo t) t)
    (hP : Tendsto (fun r : ℝ => (M.cutMassAt r 0).toReal
      / ((M.α / (M.betaCrit : ℝ)) * r ^ M.α)) atTop (𝓝 1))
    {C₀ p : ℝ} (hC₀ : 0 ≤ C₀) (hp : 1 < p)
    (hF : Analysis.LogRadialBound (fun y : M.V => M.S.dist (0 : M.V) y)
      (fun y : M.V => TriTail.openTriangle M.kernel M.kernel_nonneg M.betaCrit 0 y) C₀ p)
    {cr : ℝ → ℝ} (hcr0 : ∀ r, 0 < r → 0 ≤ cr r)
    (hderivId : ∀ r : ℝ, 0 < r → HasDerivAt
      (fun s => momOf (fun s => M.cutProb s) (0 : M.V) 3 s)
      (cr r * ∑ ℓ ∈ Finset.range 3, ((Nat.choose 3 ℓ : ℕ) : ℝ) *
        I420Case1.mixedExclR (M.cutProb r) (0 : M.V) (ℓ + 1) (3 - ℓ)
          (BallAverage.ball_finite M r).toFinset) r)
    (hcnorm : ∀ ε > 0, ∀ᶠ r in atTop,
      cr r * I420Case3.ballCard (fun r =>
          (BallAverage.ball_finite M r).toFinset) r *
        momOf (fun r => M.cutProb r) (0 : M.V) 1 r * r ≤ (1 + ε) * M.α) :
    ∀ ε > 0, ∀ᶠ r in atTop,
      momOf (fun r => M.cutProb r) (0 : M.V) 3 r ≤
        (1 + ε) * mixedMoment 3 (fun m r =>
          momOf (fun r => M.cutProb r) (0 : M.V) m r) r := by
  obtain ⟨h1, h2⟩ := cutMoment_one_two_ne_top_of_hMa M hMa
  have hgm' : ∀ᶠ r : ℝ in atTop, c3 * (M.cutMassAt r 0).toReal ^ 3
      ≤ (M.cutMoment 2 r).toReal := by
    filter_upwards [hgm] with r hr
    simpa only [momOf_cutProb_eq_toReal_cutMoment, ← M.cutMassAt_zero_eq_cutMoment r]
      using hr
  have hRV2 : Analysis.RegularlyVaryingAtTop
      (fun r => momOf (fun r => M.cutProb r) (0 : M.V) 2 r) (3 * M.α) :=
    momOf_two_regularlyVarying_of_source_p21 M M.hα hr₀ hβ.ne' hac hae h1 h2 hP hTri
      hC₀ hp hF hc3 hgm'
  exact case3_moment_three_bound_of_HD_case3 M hHD3 hTri hc hαd hlow hfin hβ hr₀ hderiv hpos
    hode hmeas hhedge h0 𝓔 h𝓔mono h𝓔 hθ0 hθ1 hMa hc3 hgm hmommeas1 hmommeas2 hRV1 hRV2 hcr0
    hderivId hcnorm

/-- **The corner-safe cubic (I.4.19) bound with the Case-3 regular variation of `E|K|²`
derived rather than assumed.**

This is `CubicModel.case3_moment_three_bound_of_HD_case3_ae` — the a.e./off-corner form of the
cubic packet — with `hRV2` replaced by the model inputs `hac`, `hae`, the first-moment
asymptotic `hP`, and the triangle / open-triangle log-radial data `hTri`, `hF`, `C₀`, `p`.  Here
the two finiteness inputs of the product route are taken directly from the theorem's own
`h2 : ∀ t ≥ a₀, E|K|²(t) ≠ ⊤` (since `a₀ < r₀`), so `hMa` plays no role in the replacement. -/
theorem case3_moment_three_bound_of_HD_case3_ae_of_p21 (M : SourceModelData)
    (hHD3 : M.d = 6 ∧ M.α = 2 ∧ ∃ C : ℝ, 0 < C ∧ ∀ x y : M.V, x ≠ y →
      M.twoPoint M.betaCrit x y ≤ C * (Real.log (M.S.ρ (toVec (x - y))))⁻¹ *
        (M.S.ρ (toVec (x - y))) ^ (-(M.d : ℝ) + 2))
    (hTri : TriTail.openTriangleSelf M.kernel M.kernel_nonneg M.betaCrit 0 < ⊤)
    (T : ℕ → Finset M.V) (hTmono : Monotone T) (hT : ∀ y : M.V, ∃ n, y ∈ T n)
    (Se : ℕ → Finset (Sym2 M.V)) (hSmono : Monotone Se) (hS : ∀ e : Sym2 M.V, ∃ n, e ∈ Se n)
    {R a₀ r₀ c C : ℝ} (hRpos : 0 < R) (hRa₀ : R < a₀) (ha₀r₀ : a₀ < r₀)
    (hβ : (0 : ℝ) < M.betaCrit) (hc : 0 < c) (hαd : M.α < (M.d : ℝ))
    (hlowenv : ∀ s : ℝ, R < s → (1 / 2) * s ^ (-(M.d : ℝ) - M.α - 1) ≤ |deriv M.K s|)
    (huppenv : ∀ s : ℝ, R < s → |deriv M.K s| ≤ 2 * s ^ (-(M.d : ℝ) - M.α - 1))
    (h2 : ∀ t : ℝ, a₀ ≤ t → M.cutMoment 2 t ≠ ⊤)
    (hcontinf : ∀ y : M.V, ∀ r : ℝ, a₀ ≤ r → ContinuousAt
      (sMomentInfFlux (0 : M.V) {y} (fun _ => (1 : ℝ)) M.cutProb M.cutEdgeDeriv) r)
    (hK : ∀ r : ℝ, a₀ ≤ r → ContinuousAt (fun r' => deriv M.K r') r)
    (hex : ∀ r : ℝ, a₀ ≤ r → ContinuousAt M.exclScalar r)
    (hmeas : Measurable (cutError M))
    (hC : ∀ t : ℝ, r₀ ≤ t → |cutError M t| ≤ C)
    (h0 : Tendsto (cutError M) atTop (𝓝 0))
    (hlow : ∀ x : M.V, x ≠ 0 →
      c * (M.S.dist 0 x) ^ (-(M.d : ℝ) + M.α) ≤ M.twoPoint M.betaCrit 0 x)
    (hfin : ∀ᶠ r : ℝ in atTop, M.cutMassAt r 0 ≠ ⊤)
    (𝓔 : ℕ → Finset (Sym2 M.V)) (h𝓔mono : Monotone 𝓔)
    (h𝓔 : ∀ e : Sym2 M.V, ∃ n, e ∈ 𝓔 n)
    {θ : ℝ} (hθ0 : 0 < θ) (hθ1 : θ < 1)
    (hMa : ∀ (r : ℝ), 1 ≤ r → ∀ ℓ : ℕ, ℓ ≤ 3 →
      I420Case1.powMomentAt (M.cutProb r) (ℓ + 1) (0 : M.V) ≠ ⊤)
    {c3 : ℝ} (hc3 : 0 < c3)
    (hgm : ∀ᶠ r in atTop, c3 * momOf (fun r => M.cutProb r) (0 : M.V) 1 r ^ 3
      ≤ momOf (fun r => M.cutProb r) (0 : M.V) 2 r)
    (hmommeas1 : Measurable (fun r =>
      momOf (fun r => M.cutProb r) (0 : M.V) 1 r))
    (hmommeas2 : Measurable (fun r =>
      momOf (fun r => M.cutProb r) (0 : M.V) 2 r))
    (hmommeas3 : Measurable (fun r =>
      momOf (fun r => M.cutProb r) (0 : M.V) 3 r))
    (hRV1 : Analysis.RegularlyVaryingAtTop
      (fun r => momOf (fun r => M.cutProb r) (0 : M.V) 1 r) M.α)
    (hac : ∀ R' : ℝ, r₀ ≤ R' → AbsolutelyContinuousOnInterval
      (fun r : ℝ => (M.cutMoment 2 r).toReal) r₀ R')
    (hae : ∀ᵐ t ∂(volume.restrict (Ici r₀)),
      HasDerivAt (fun r : ℝ => (M.cutMoment 2 r).toReal) (M.rhsScalarTwo t) t)
    (hP : Tendsto (fun r : ℝ => (M.cutMassAt r 0).toReal
      / ((M.α / (M.betaCrit : ℝ)) * r ^ M.α)) atTop (𝓝 1))
    {C₀ p : ℝ} (hC₀ : 0 ≤ C₀) (hp : 1 < p)
    (hF : Analysis.LogRadialBound (fun y : M.V => M.S.dist (0 : M.V) y)
      (fun y : M.V => TriTail.openTriangle M.kernel M.kernel_nonneg M.betaCrit 0 y) C₀ p)
    {cr : ℝ → ℝ} (hcr0 : ∀ r, 0 < r → 0 ≤ cr r)
    (hac3 : AbsolutelyContinuousOnTail
      (fun r => momOf (fun r => M.cutProb r) (0 : M.V) 3 r) r₀)
    (hSm : Measurable (fun r => cr r * ∑ ℓ ∈ Finset.range 3,
      ((Nat.choose 3 ℓ : ℕ) : ℝ) *
        I420Case1.mixedExclR (M.cutProb r) (0 : M.V) (ℓ + 1) (3 - ℓ)
          (BallAverage.ball_finite M r).toFinset))
    (hderivId : ∀ᵐ r ∂(volume.restrict (Set.Ici r₀)), HasDerivAt
      (fun s => momOf (fun s => M.cutProb s) (0 : M.V) 3 s)
      (cr r * ∑ ℓ ∈ Finset.range 3, ((Nat.choose 3 ℓ : ℕ) : ℝ) *
        I420Case1.mixedExclR (M.cutProb r) (0 : M.V) (ℓ + 1) (3 - ℓ)
          (BallAverage.ball_finite M r).toFinset) r)
    (hcnorm : ∀ ε > 0, ∀ᶠ r in atTop,
      cr r * I420Case3.ballCard (fun r =>
          (BallAverage.ball_finite M r).toFinset) r *
        momOf (fun r => M.cutProb r) (0 : M.V) 1 r * r ≤ (1 + ε) * M.α) :
    ∀ ε > 0, ∀ᶠ r in atTop,
      momOf (fun r => M.cutProb r) (0 : M.V) 3 r ≤
        (1 + ε) * mixedMoment 3 (fun m r =>
          momOf (fun r => M.cutProb r) (0 : M.V) m r) r := by
  have hr₀ : 0 < r₀ := lt_trans hRpos (lt_trans hRa₀ ha₀r₀)
  have hgm' : ∀ᶠ r : ℝ in atTop, c3 * (M.cutMassAt r 0).toReal ^ 3
      ≤ (M.cutMoment 2 r).toReal := by
    filter_upwards [hgm] with r hr
    simpa only [momOf_cutProb_eq_toReal_cutMoment, ← M.cutMassAt_zero_eq_cutMoment r]
      using hr
  have hRV2 : Analysis.RegularlyVaryingAtTop
      (fun r => momOf (fun r => M.cutProb r) (0 : M.V) 2 r) (3 * M.α) :=
    momOf_two_regularlyVarying_of_source_p21 M M.hα hr₀ hβ.ne'
      (fun R' hR' => hac R' hR') hae
      (fun t ht => M.cutMoment_one_ne_top_of_two (h2 t (le_trans ha₀r₀.le ht)))
      (fun t ht => h2 t (le_trans ha₀r₀.le ht)) hP hTri hC₀ hp hF hc3 hgm'
  exact case3_moment_three_bound_of_HD_case3_ae M hHD3 hTri T hTmono hT Se hSmono hS
    hRpos hRa₀ ha₀r₀ hβ hc hαd hlowenv huppenv h2 hcontinf hK hex hmeas hC h0 hlow hfin
    𝓔 h𝓔mono h𝓔 hθ0 hθ1 hMa hc3 hgm hmommeas1 hmommeas2 hmommeas3 hRV1 hRV2 hcr0 hac3 hSm
    hderivId hcnorm

/-- **The `p = 3` assertion of Proposition I.4.20 at the source model, with the Case-3 regular
variation of `E|K|²` derived rather than assumed.**

This is `RatioInduction.Asymptotic.case3_moment_three_asymptotic_of_HD_case3` — the full `p = 3`
second-induction statement (`E|K|³ ~ 3 (E|K|²/E|K|)² E|K|` together with regular variation of
`E|K|³` of index `5α`) — with

`hRV2 : RegularlyVaryingAtTop (fun r => E_{β_c,r}|K|²) (3α)`

replaced by the model inputs `hac`, `hae`, the first-moment asymptotic `hP` and the
triangle / open-triangle log-radial data `hTri`, `hF`, `C₀`, `p`.  The two cutoff-moment
finiteness inputs of the product route are derived from `hMa`, and the moment gap is the same
`hgm` (its `momOf` spelling is `rfl`-equal to the `cutMassAt`/`cutMoment` spelling of the product
numerator consumer).  Nothing else changes. -/
theorem case3_moment_three_asymptotic_of_HD_case3_of_p21 (M : SourceModelData)
    (hHD3 : M.d = 6 ∧ M.α = 2 ∧ ∃ C : ℝ, 0 < C ∧ ∀ x y : M.V, x ≠ y →
      M.twoPoint M.betaCrit x y ≤ C * (Real.log (M.S.ρ (toVec (x - y))))⁻¹ *
        (M.S.ρ (toVec (x - y))) ^ (-(M.d : ℝ) + 2))
    (hTri : TriTail.openTriangleSelf M.kernel M.kernel_nonneg M.betaCrit 0 < ⊤)
    {f' h : ℝ → ℝ} {c C r₀ : ℝ} (hc : 0 < c) (hαd : M.α < (M.d : ℝ))
    (hlow : ∀ x : M.V, x ≠ 0 →
      c * (M.S.dist 0 x) ^ (-(M.d : ℝ) + M.α) ≤ M.twoPoint M.betaCrit 0 x)
    (hfin : ∀ᶠ r : ℝ in atTop, M.cutMassAt r 0 ≠ ⊤)
    (hβ : (0 : ℝ) < M.betaCrit) (hr₀ : 0 < r₀)
    (hderiv : ∀ t, r₀ ≤ t →
      HasDerivAt (fun r => (M.cutMassAt r 0).toReal) (f' t) t)
    (hpos : ∀ t, r₀ ≤ t → 0 < (M.cutMassAt t 0).toReal)
    (hode : ∀ t, r₀ ≤ t →
      f' t = (M.betaCrit : ℝ) * (1 - h t) * t ^ (-M.α - 1) *
        ((M.cutMassAt t 0).toReal) ^ 2)
    (hmeas : Measurable h) (hhedge : ∀ t, r₀ ≤ t → |h t| ≤ C)
    (h0 : Tendsto h atTop (𝓝 0))
    (𝓔 : ℕ → Finset (Sym2 M.V)) (h𝓔mono : Monotone 𝓔)
    (h𝓔 : ∀ e : Sym2 M.V, ∃ n, e ∈ 𝓔 n)
    {θ : ℝ} (hθ0 : 0 < θ) (hθ1 : θ < 1)
    (hMa : ∀ (r : ℝ), 1 ≤ r → ∀ ℓ : ℕ, ℓ ≤ 3 →
      I420Case1.powMomentAt (M.cutProb r) (ℓ + 1) (0 : M.V) ≠ ⊤)
    {c3 : ℝ} (hc3 : 0 < c3)
    (hgm : ∀ᶠ r in atTop, c3 * I420Case3.momOf (fun r => M.cutProb r) (0 : M.V) 1 r ^ 3
      ≤ I420Case3.momOf (fun r => M.cutProb r) (0 : M.V) 2 r)
    (hmommeas1 : Measurable (fun r =>
      I420Case3.momOf (fun r => M.cutProb r) (0 : M.V) 1 r))
    (hmommeas2 : Measurable (fun r =>
      I420Case3.momOf (fun r => M.cutProb r) (0 : M.V) 2 r))
    (hRV1 : Analysis.RegularlyVaryingAtTop
      (fun r => I420Case3.momOf (fun r => M.cutProb r) (0 : M.V) 1 r) M.α)
    (hac : ∀ R' : ℝ, r₀ ≤ R' → AbsolutelyContinuousOnInterval
      (fun r : ℝ => (M.cutMoment 2 r).toReal) r₀ R')
    (hae : ∀ᵐ t ∂(volume.restrict (Ici r₀)),
      HasDerivAt (fun r : ℝ => (M.cutMoment 2 r).toReal) (M.rhsScalarTwo t) t)
    (hP : Tendsto (fun r : ℝ => (M.cutMassAt r 0).toReal
      / ((M.α / (M.betaCrit : ℝ)) * r ^ M.α)) atTop (𝓝 1))
    {C₀ p : ℝ} (hC₀ : 0 ≤ C₀) (hp : 1 < p)
    (hF : Analysis.LogRadialBound (fun y : M.V => M.S.dist (0 : M.V) y)
      (fun y : M.V => TriTail.openTriangle M.kernel M.kernel_nonneg M.betaCrit 0 y) C₀ p)
    {cr : ℝ → ℝ}
    (hderivId : ∀ r : ℝ, 0 < r → HasDerivAt
      (fun s => I420Case3.momOf (fun s => M.cutProb s) (0 : M.V) 3 s)
      (cr r * ∑ ℓ ∈ Finset.range 3, ((Nat.choose 3 ℓ : ℕ) : ℝ) *
        I420Case1.mixedExclR (M.cutProb r) (0 : M.V) (ℓ + 1) (3 - ℓ)
          (BallAverage.ball_finite M r).toFinset) r)
    (hcT : Tendsto (fun r => r * cr r *
      I420Case3.ballCard (fun r => (BallAverage.ball_finite M r).toFinset) r *
        I420Case3.momOf (fun r => M.cutProb r) (0 : M.V) 1 r) atTop (𝓝 M.α)) :
    Tendsto (fun r => I420Case3.momOf (fun r => M.cutProb r) (0 : M.V) 3 r /
        mixedMoment 3 (fun m r => I420Case3.momOf (fun r => M.cutProb r) (0 : M.V) m r) r)
        atTop (𝓝 1) ∧
      Analysis.RegularlyVaryingAtTop
        (fun r => I420Case3.momOf (fun r => M.cutProb r) (0 : M.V) 3 r)
        ((2 * (3 : ℝ) - 1) * M.α) := by
  obtain ⟨h1, h2⟩ := cutMoment_one_two_ne_top_of_hMa M hMa
  have hgm' : ∀ᶠ r : ℝ in atTop, c3 * (M.cutMassAt r 0).toReal ^ 3
      ≤ (M.cutMoment 2 r).toReal := by
    filter_upwards [hgm] with r hr
    simpa only [momOf_cutProb_eq_toReal_cutMoment, ← M.cutMassAt_zero_eq_cutMoment r]
      using hr
  have hRV2 : Analysis.RegularlyVaryingAtTop
      (fun r => I420Case3.momOf (fun r => M.cutProb r) (0 : M.V) 2 r) (3 * M.α) :=
    momOf_two_regularlyVarying_of_source_p21 M M.hα hr₀ hβ.ne' hac hae h1 h2 hP hTri
      hC₀ hp hF hc3 hgm'
  exact case3_moment_three_asymptotic_of_HD_case3 M hHD3 hTri hc hαd hlow hfin hβ hr₀ hderiv
    hpos hode hmeas hhedge h0 𝓔 h𝓔mono h𝓔 hθ0 hθ1 hMa hc3 hgm hmommeas1 hmommeas2 hRV1 hRV2
    hderivId hcT

end I420Case3

end PercLib.CriticalLRP
