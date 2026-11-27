/-
Copyright (c) 2026 PercLib contributors. Released under Apache 2.0.

Integrated and independently rebuilt from accepted Ultramath `smwypth8o`, member `m2`.
Swarm `smwypth8o`, member `m2`, direction (2).

The **cubic packet at the actual source cutoff family**, with the everywhere derivative identity of
Lemma I.4.1 replaced by its off-corner (a.e.) form.

`I420Case3.case3_moment_three_bound_of_HD_case3`
(`VolumeMoments/HigherMoments/I420Case3/RatioInduction/Handoff.lean`) concludes

`E|K|³ ≤ (1+o(1)) · 3 · (E|K|²/E|K|)² · E|K|` at `momOf (fun r => M.cutProb r) 0 ·`

from, among other inputs,

* a **pointwise** first-moment derivative `hderiv : ∀ t, r₀ ≤ t → HasDerivAt cutMassReal (f' t) t`
  together with the pointwise ODE `hode` and positivity `hpos` (only to obtain the Case-3
  decorrelation limits `hAend`, `hAmid`), and
* the **pointwise** third-moment derivative identity
  `hderivId : ∀ r, 0 < r → HasDerivAt (mom 3) (cr r * ∑ ℓ, C(3,ℓ) A ℓ r) r`.

Its own docstring records that the global form of the second input is "an honest remaining
obstruction", since the shipped derivative theorem for the cutoff mass is an off-corner statement.

The theorem below replaces both global pointwise inputs by their genuine a.e. forms; the
third-moment absolute continuity and a.e. identity remain explicit model hypotheses:

* the first-moment input is the corner-safe package of
  `Analysis/Cutoff/OffCorner/AeDerivativeHandoff.case3_hAend_hAmid_cutPoly_source_of_HD_case3_ae`
  (window-uniform off-corner data, a.e. ODE, derived absolute continuity of the cutoff mass);
* the third-moment input is absolute continuity of `r ↦ momOf (fun r => M.cutProb r) 0 3 r` on
  compact windows of a tail plus the same derivative identity a.e. on that tail.

Every remaining premise is explicit; nothing is derived from an upper moment inequality.
-/
module

public import PercLib.CriticalLRP.Analysis.AEHigherMoments.ThreeRatio
public import PercLib.CriticalLRP.Analysis.Cutoff.OffCorner.AeDerivativeHandoff
public import PercLib.CriticalLRP.VolumeMoments.HigherMoments.I420Case3.RatioInduction.Handoff


/-! # Almost-everywhere higher-moment interface: CubicModel -/

set_option autoImplicit false
set_option linter.style.multiGoal false

open MeasureTheory Filter Topology
open scoped ENNReal Topology

@[expose] public section

namespace PercLib.CriticalLRP

namespace I420Case3

open Orchestration
open PercLib.CriticalLRP.VolumeMoments.HigherMoments
open PercLib.CriticalLRP.Analysis.AE

/-- **The cubic (I.4.19) upper moment bound at the actual source cutoff family, corner-safe.**

Same conclusion as `case3_moment_three_bound_of_HD_case3`, with `hderiv`/`hpos`/`hode` replaced by
the window-uniform off-corner data of the accepted off-corner handoff and with the third-moment
derivative identity required only almost everywhere. -/
theorem case3_moment_three_bound_of_HD_case3_ae (M : SourceModelData)
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
    (hRV2 : Analysis.RegularlyVaryingAtTop
      (fun r => momOf (fun r => M.cutProb r) (0 : M.V) 2 r) (3 * M.α))
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
  obtain ⟨hAend, hAmid⟩ :=
    case3_hAend_hAmid_cutPoly_source_of_HD_case3_ae M hHD3 hTri T hTmono hT Se hSmono hS
      hRpos hRa₀ ha₀r₀ hβ hc hαd hlowenv huppenv h2 hcontinf hK hex hmeas hC h0 hlow hfin
      𝓔 h𝓔mono h𝓔 3 (by norm_num) hθ0 hθ1 hMa hc3 hgm
  have hmom := momOf_cutProb_pos_three M hMa
  have hmass : ∀ x, 0 < x →
      (fun ℓ r => I420Case1.mixedExclR (M.cutProb r) (0 : M.V) (ℓ + 1) (3 - ℓ)
        (BallAverage.ball_finite M r).toFinset) 0 x =
      (fun ℓ r => I420Case1.mixedExclR (M.cutProb r) (0 : M.V) (ℓ + 1) (3 - ℓ)
        (BallAverage.ball_finite M r).toFinset) (3 - 1) x := by
    intro x _
    exact mixedExclR_cutProb_swap M x 1 3 _
  have hr₀ : 0 < r₀ := lt_trans hRpos (lt_trans hRa₀ ha₀r₀)
  exact moment_upper_bound_three_ratio_of_pos_ae (mom := fun m r =>
      momOf (fun r => M.cutProb r) (0 : M.V) m r) M.hα hmom hmommeas3 hmommeas1 hmommeas2
    hRV1 hRV2 hr₀ hac3 hSm hderivId (fun x hx => ballCard_pos M hx) hcr0 hmass hAend hAmid hcnorm

end I420Case3

end PercLib.CriticalLRP

set_option linter.hashCommand false

#print axioms PercLib.CriticalLRP.I420Case3.case3_moment_three_bound_of_HD_case3_ae
