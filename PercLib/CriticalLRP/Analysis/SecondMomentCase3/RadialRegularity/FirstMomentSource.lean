/-
Ultramath swarm `smwzlje3f`, member `m3`, direction `d2`.

Copyright (c) 2026 PercLib contributors. Released under Apache 2.0.

Accepted and independently rebuilt from Ultramath `smwzlje3f` with m3/m7 sources.
Integration based on production commit `caf06cb0a9face27c4dce7b4a13703d40d4568ac`.

Built against production commit `5d2d681b941eb1c687f1ba17e6a798b8f0175aa0`
(branch `work/yujinhkim-critical-lrp-orchestration`, Lean `v4.35.0`).  Nothing here is
integrated: this file lives in the swarm member's own directory and is meant as a handoff.

# Case 3: the first-moment inputs of the `(2,1)`-product consumer, discharged

`Analysis/SecondMomentCase3/ProductGap/SourceConsumer.lean` leaves, among others, the three
first-moment quantities

* `hP : E_{β_c,r}|K| / ((α/β_c) r^α) → 1`,
* `hlogH : LogarithmicallyIntegrable M.p2H` (`H_r = (β_c/α) r^{-α} E_{β_c,r}|K| - 1`),
* `hlogE0 : LogarithmicallyIntegrable (PivotFlux.cutE0 M)`

as explicit inputs of `secondMoment_asymptotic_case3_of_source_p21`.  Those three are exactly
the two assertions of Proposition I.4.2 in Case 3 (the triangle condition) together with the
standing regularity of the cutoff kernel.

`FirstMomentLogError.lean` already derives the three from a *lower-level* list
(`case3_firstMoment_inputs`), but that list still contains the composite defect `hE1`, its
tail bound `hC`, its vanishing `h0`, and the divergence `hinf : cutMassReal → ∞`.  This file
removes those four as well:

* `eventually_cutMoment_one_ne_top` / `eventually_cutMassAt_ne_top` — the eventual finiteness
  hypotheses are consequences of the second-moment finiteness `h2`, not independent inputs;
* `tendsto_cutMassReal_atTop_of_uncutMean_eq_top` — the divergence `χ_r → ∞` is
  `E_{β_c}|K| = ∞` transported through the landed cutoff-moment limit
  (`I42C.tendsto_cutMassAt_atTop_nhds_top` + `I42C.tendsto_cutMassAt_toReal_atTop`);
* `isLogErrorFunction_cutE1_of_triangle`, `tendsto_cutError_of_triangle`,
  `exists_tail_bound_abs_cutError` — `E_{1,r}` is a log-error function under the triangle
  condition and the open-triangle radial log bound (Lemma I.4.13), whence `Ē_{1,r} → 0`
  and a constant tail bound;
* `case3_firstMoment_inputs_of_triangle` — the bundle: `hP`, `hlogH`, `hlogE0` from
  `hβ > 0`, the kernel power bounds, `h2`, the continuity triple, `E_{β_c}|K| = ∞`,
  the triangle condition, and the open-triangle radial log bound.

The hypotheses `hTri`, `{C₀, p}`, `hC₀`, `hp`, `hF` are *the same objects* that
`secondMoment_asymptotic_case3_of_source_p21` already carries for the `(2,1)` polygon bundle,
so passing them through the first-moment step adds no hypothesis at all.

## Source statements (read from `attachments/i-want-you-to-ljpx/tom1.pdf`)

**Proposition I.4.2** (p. 35). *Suppose that at least one of the following is true:*
1. `d > 3α`.  2. `d = 3α` *and* (Hydro).  3. *The triangle condition holds.*
*Then* `E_{β_c,r}|K| ∼ (α/β_c) r^α`.  *If either `d > 3α` or the triangle condition holds and
`∇_r` is logarithmically integrable then the error in this approximation*
`H_r := (β_c/α) r^{-α} E_{β_c,r}|K| − 1` *is logarithmically integrable.*

**Proposition I.4.15, Case 3** (pp. 46–47) uses exactly the first-moment outputs
`E_{β_c,r}|K| ⪰ r^α` and `E_{β_c,r}|K|² ⪰ (E_{β_c,r}|K|)³` produced by that route.

Scope: this is **not** a proof of Proposition I.4.20, and **not** a completion of Cases 1–2 of
Proposition I.4.15.  It discharges three named inputs of the Case-3 `(2,1)` consumer only.
-/

module

public import PercLib.CriticalLRP.Analysis.SecondMomentCase3.ProductGap.SourceConsumer
public import PercLib.CriticalLRP.Analysis.SecondMomentCase3.FirstMomentLogError
public import PercLib.CriticalLRP.VolumeMoments.FirstMoment.Divergence
public import PercLib.Percolation.Bond.ProfileRegularity
public import PercLib.CriticalLRP.VolumeMoments.HigherMoments.I420Case3.SplitPolygon.DirectSource

/-! # First-moment inputs for the direct Case-3 product-gap consumer -/

set_option linter.style.longLine false

@[expose] public section

noncomputable section

open MeasureTheory Filter Topology Set
open scoped ENNReal Topology

namespace PercLib.CriticalLRP
namespace Orchestration
namespace SourceModelData

variable (M : SourceModelData)

/-! ## Eventual finiteness from the second cutoff moment -/

/-- `∀ᶠ r, E_{β_c,r}|K| ≠ ⊤` from finiteness of the second cutoff moment on a tail. -/
theorem eventually_cutMoment_one_ne_top {a₀ : ℝ}
    (h2 : ∀ t : ℝ, a₀ ≤ t → M.cutMoment 2 t ≠ ⊤) :
    ∀ᶠ r : ℝ in atTop, M.cutMoment 1 r ≠ ⊤ := by
  filter_upwards [eventually_ge_atTop a₀] with r hr
  exact ne_top_of_le_ne_top (h2 r hr) (M.cutMoment_one_le_cutMoment_two r)

/-- `∀ᶠ r, E_{β_c,r}|K 1_0| ≠ ⊤` from finiteness of the second cutoff moment on a tail. -/
theorem eventually_cutMassAt_ne_top_of_cutMoment_two {a₀ : ℝ}
    (h2 : ∀ t : ℝ, a₀ ≤ t → M.cutMoment 2 t ≠ ⊤) :
    ∀ᶠ r : ℝ in atTop, M.cutMassAt r 0 ≠ ⊤ := by
  filter_upwards [eventually_ge_atTop a₀] with r hr
  exact ne_top_of_le_ne_top (h2 r hr) (E1Sign.cutMassAt_le_cutMoment_two M r)

/-! ## The divergence `χ_r → ∞` from `E_{β_c}|K| = ∞`

The paper's Case 3 of Proposition I.4.2 needs `E_{β_c,r}|K| → ∞`; this is the curve
`r ↦ E_{β_c,r}|K| = M.cutMassAt r 0` at its own critical parameter.  The passage from the
uncut critical mean to the cutoff curve is the landed `tendsto_cutMoment`. -/

/-- **`χ_r → ∞`** (`hinf`) from the uncut critical first moment being infinite. -/
theorem tendsto_cutMassReal_atTop_of_uncutMean_eq_top
    (htop : M.uncutMean M.betaCrit = ⊤)
    (hfin : ∀ᶠ r : ℝ in atTop, M.cutMassAt r 0 ≠ ⊤) :
    Tendsto M.cutMassReal atTop atTop := by
  exact I42C.tendsto_cutMassAt_toReal_atTop M
    (I42C.tendsto_cutMassAt_atTop_nhds_top M htop) hfin

/-! ## The composite defect `Ē_{1,r}` under the triangle condition -/

/-- The truncated-law defect `E_{1,r}` is a logarithmically integrable error function under the
triangle condition and the open-triangle radial log bound (Lemma I.4.13 of the source). -/
theorem isLogErrorFunction_cutE1_of_triangle
    (hTri : TriTail.openTriangleSelf M.kernel M.kernel_nonneg M.betaCrit 0 < ⊤)
    (h1fin : ∀ᶠ r : ℝ in atTop, M.cutMoment 1 r ≠ ⊤)
    {C₁ p : ℝ} (hC₁ : 0 ≤ C₁) (hp : 1 < p)
    (hF : Analysis.LogRadialBound (fun y : M.V => M.S.dist 0 y)
      (fun y : M.V => TriTail.openTriangle M.kernel M.kernel_nonneg M.betaCrit 0 y) C₁ p) :
    Analysis.IsLogErrorFunction (fun r : ℝ => PivotFlux.cutE1 M r) :=
  CutoffDefect.isLogErrorFunction_cutE1_unconditional M hTri h1fin hC₁ hp hF

/-- **`Ē_{1,r} → 0`**: the composite standardization/truncation defect vanishes on the tail. -/
theorem tendsto_cutError_of_triangle
    (hTri : TriTail.openTriangleSelf M.kernel M.kernel_nonneg M.betaCrit 0 < ⊤)
    (h1fin : ∀ᶠ r : ℝ in atTop, M.cutMoment 1 r ≠ ⊤)
    {C₁ p : ℝ} (hC₁ : 0 ≤ C₁) (hp : 1 < p)
    (hF : Analysis.LogRadialBound (fun y : M.V => M.S.dist 0 y)
      (fun y : M.V => TriTail.openTriangle M.kernel M.kernel_nonneg M.betaCrit 0 y) C₁ p) :
    Tendsto (I420Case3.cutError M) atTop (𝓝 0) := by
  have hE1 := M.isLogErrorFunction_cutE1_of_triangle hTri h1fin hC₁ hp hF
  exact CornerSafe.tendsto_one_sub_mul (PivotFlux.tendsto_cutE0 M) hE1.2

/-- A constant tail bound for `|Ē_{1,r}|` above any radius, from its vanishing. -/
theorem exists_tail_bound_abs_cutError
    (h0 : Tendsto (I420Case3.cutError M) atTop (𝓝 0)) (a₀ : ℝ) :
    ∃ r₁ : ℝ, a₀ < r₁ ∧ ∀ t : ℝ, r₁ ≤ t → |I420Case3.cutError M t| ≤ 1 := by
  obtain ⟨N, hN⟩ := (Metric.tendsto_atTop.1 h0) 1 zero_lt_one
  refine ⟨max (a₀ + 1) (N + 1), ?_, ?_⟩
  · exact lt_of_lt_of_le (by linarith) (le_max_left _ _)
  · intro t ht
    have htN : N ≤ t :=
      le_trans (by linarith : N ≤ N + 1) (le_trans (le_max_right _ _) ht)
    have h := hN t htN
    rw [Real.dist_eq, sub_zero] at h
    exact le_of_lt h

end SourceModelData
end Orchestration
end PercLib.CriticalLRP

namespace PercLib.CriticalLRP
namespace Orchestration
namespace SourceModelData

variable (M : SourceModelData)

/-! ## The bundle: Proposition I.4.2, Case 3, without `hE1`, `hC`, `h0`, `hinf` -/

/-- **`hP`, `hlogH`, `hlogE0` from source-level Case-3 hypotheses.**

Compare `case3_firstMoment_inputs`: the composite defect `hE1`, its tail bound `hC`, its
vanishing `h0` and the divergence `hinf` are all *derived* here.  What remains is

* the kernel tail pair `hlow`, `hupp` (`K'(s) ≍ s^{-d-α-1}`) and the continuity triple,
* the second cutoff moment `h2` (which also supplies both eventual finiteness hypotheses),
* `E_{β_c}|K| = ∞` (`htop`), the source's critical-mean divergence,
* the triangle condition `hTri` and the open-triangle radial log bound `hF` — the *same* two
  objects that the `(2,1)` product-gap consumer carries. -/
theorem case3_firstMoment_inputs_of_triangle
    (hβ : (0 : ℝ) < M.betaCrit) {a₀ : ℝ}
    (T : ℕ → Finset M.V) (hTmono : Monotone T) (hT : ∀ y : M.V, ∃ n, y ∈ T n)
    (S : ℕ → Finset (Sym2 M.V)) (hSmono : Monotone S) (hS : ∀ e : Sym2 M.V, ∃ n, e ∈ S n)
    {R : ℝ} (hRpos : 0 < R) (hRa₀ : R < a₀)
    (hlow : ∀ s : ℝ, R < s → (1 / 2) * s ^ (-(M.d : ℝ) - M.α - 1) ≤ |deriv M.K s|)
    (hupp : ∀ s : ℝ, R < s → |deriv M.K s| ≤ 2 * s ^ (-(M.d : ℝ) - M.α - 1))
    (h2 : ∀ t : ℝ, a₀ ≤ t → M.cutMoment 2 t ≠ ⊤)
    (hcontinf : ∀ y : M.V, ∀ r : ℝ, a₀ ≤ r → ContinuousAt
      (sMomentInfFlux (0 : M.V) {y} (fun _ => (1 : ℝ)) M.cutProb M.cutEdgeDeriv) r)
    (hK : ∀ r : ℝ, a₀ ≤ r → ContinuousAt (fun r' => deriv M.K r') r)
    (hex : ∀ r : ℝ, a₀ ≤ r → ContinuousAt M.exclScalar r)
    (htop : M.uncutMean M.betaCrit = ⊤)
    (hTri : TriTail.openTriangleSelf M.kernel M.kernel_nonneg M.betaCrit 0 < ⊤)
    {C₁ p : ℝ} (hC₁ : 0 ≤ C₁) (hp : 1 < p)
    (hF : Analysis.LogRadialBound (fun y : M.V => M.S.dist 0 y)
      (fun y : M.V => TriTail.openTriangle M.kernel M.kernel_nonneg M.betaCrit 0 y) C₁ p) :
    Tendsto (fun r : ℝ => (M.cutMassAt r 0).toReal
        / ((M.α / (M.betaCrit : ℝ)) * r ^ M.α)) atTop (𝓝 1)
      ∧ Analysis.LogarithmicallyIntegrable M.p2H
      ∧ Analysis.LogarithmicallyIntegrable (PivotFlux.cutE0 M) := by
  have h1fin := M.eventually_cutMoment_one_ne_top h2
  have hfin := M.eventually_cutMassAt_ne_top_of_cutMoment_two h2
  have hE1 := M.isLogErrorFunction_cutE1_of_triangle hTri h1fin hC₁ hp hF
  have h0 := M.tendsto_cutError_of_triangle hTri h1fin hC₁ hp hF
  have hinf := M.tendsto_cutMassReal_atTop_of_uncutMean_eq_top htop hfin
  obtain ⟨r₁, ha₀r₁, hC⟩ := M.exists_tail_bound_abs_cutError h0 a₀
  exact M.case3_firstMoment_inputs hβ T hTmono hT S hSmono hS hRpos hRa₀ ha₀r₁ hlow hupp h2
    hcontinf hK hex hinf hE1 hC h0

end SourceModelData
end Orchestration
end PercLib.CriticalLRP

namespace PercLib.CriticalLRP
namespace Orchestration
namespace SourceModelData

variable (M : SourceModelData)

/-! ## The `(2,1)`-product Case-3 consumer with the first-moment inputs discharged

`secondMoment_asymptotic_case3_of_source_p21` carries `hP`, `hlogH`, `hlogE0` alongside the
triangle condition `hTri` and the open-triangle radial log bound `hF`.  Since the first-moment
bundle consumes *the same* `hTri`, `hF` and `{C₀, p}`, the replacement adds exactly one
hypothesis — the source's critical-mean divergence `M.uncutMean M.betaCrit = ⊤` — and removes
`hP`, `hlogH`, `hlogE0`.  The first cutoff moment finiteness `h1` is likewise removed: it is
`cutMoment 1 ≤ cutMoment 2`. -/

/-- **Proposition I.4.15, Case 3, with the first-moment inputs discharged and the `(2,1)`
product gap in place of the `p = 3`, `q = 0` star.** -/
theorem secondMoment_asymptotic_case3_of_source_p21_firstMoment
    (hα : 0 < M.α) {r₀ : ℝ} (hr₀ : 0 < r₀)
    (hβ : (0 : ℝ) < M.betaCrit)
    (hac : ∀ R : ℝ, r₀ ≤ R → AbsolutelyContinuousOnInterval
      (fun r : ℝ => (M.cutMoment 2 r).toReal) r₀ R)
    (hae : ∀ᵐ t ∂(volume.restrict (Ici r₀)),
      HasDerivAt (fun r : ℝ => (M.cutMoment 2 r).toReal) (M.rhsScalarTwo t) t)
    {a₀ : ℝ}
    (h2 : ∀ t : ℝ, r₀ ≤ t → M.cutMoment 2 t ≠ ⊤)
    (hTri : TriTail.openTriangleSelf M.kernel M.kernel_nonneg M.betaCrit 0 < ⊤)
    {C₀ p : ℝ} (hC₀ : 0 ≤ C₀) (hp : 1 < p)
    (hF : Analysis.LogRadialBound (fun y : M.V => M.S.dist (0 : M.V) y)
      (fun y : M.V => TriTail.openTriangle M.kernel M.kernel_nonneg M.betaCrit 0 y) C₀ p)
    (hmeasE2 : Measurable M.p2ExclError) (hmeasEbar : Measurable M.p2Ebar)
    (T : ℕ → Finset M.V) (hTmono : Monotone T) (hT : ∀ y : M.V, ∃ n, y ∈ T n)
    (S : ℕ → Finset (Sym2 M.V)) (hSmono : Monotone S) (hS : ∀ e : Sym2 M.V, ∃ n, e ∈ S n)
    {R : ℝ} (hRpos : 0 < R) (hRa₀ : R < a₀)
    (hlow : ∀ s : ℝ, R < s → (1 / 2) * s ^ (-(M.d : ℝ) - M.α - 1) ≤ |deriv M.K s|)
    (hupp : ∀ s : ℝ, R < s → |deriv M.K s| ≤ 2 * s ^ (-(M.d : ℝ) - M.α - 1))
    (hcontinf : ∀ y : M.V, ∀ r : ℝ, a₀ ≤ r → ContinuousAt
      (sMomentInfFlux (0 : M.V) {y} (fun _ => (1 : ℝ)) M.cutProb M.cutEdgeDeriv) r)
    (hK : ∀ r : ℝ, a₀ ≤ r → ContinuousAt (fun r' => deriv M.K r') r)
    (hex : ∀ r : ℝ, a₀ ≤ r → ContinuousAt M.exclScalar r)
    (htop : M.uncutMean M.betaCrit = ⊤)
    {c3 : ℝ} (hc3 : 0 < c3)
    (hgm : ∀ᶠ r : ℝ in atTop, c3 * (M.cutMassAt r 0).toReal ^ 3 ≤ (M.cutMoment 2 r).toReal) :
    ∃ A : ℝ, 0 < A ∧ Tendsto
      (fun r : ℝ => (M.cutMoment 2 r).toReal / r ^ (3 * M.α)) atTop (𝓝 A) := by
  obtain ⟨hP, hlogH, hlogE0⟩ :=
    M.case3_firstMoment_inputs_of_triangle (a₀ := max a₀ r₀) hβ T hTmono hT S hSmono hS
      hRpos (lt_of_lt_of_le hRa₀ (le_max_left a₀ r₀)) hlow hupp
      (fun t ht => h2 t (le_trans (le_max_right a₀ r₀) ht))
      (fun y r hr => hcontinf y r (le_trans (le_max_left a₀ r₀) hr))
      (fun r hr => hK r (le_trans (le_max_left a₀ r₀) hr))
      (fun r hr => hex r (le_trans (le_max_left a₀ r₀) hr))
      htop hTri hC₀ hp hF
  refine M.secondMoment_asymptotic_case3_of_source_p21 hα hr₀ (ne_of_gt hβ) hac hae ?_ h2 hP
    hTri hC₀ hp hF hmeasE2 hmeasEbar hlogH hlogE0 hc3 hgm
  intro t ht
  exact ne_top_of_le_ne_top (h2 t ht) (M.cutMoment_one_le_cutMoment_two t)

/-- The regularly-varying conclusion of Proposition I.4.15 in Case 3, with the first-moment
inputs discharged. -/
theorem regularlyVarying_two_of_source_p21_firstMoment
    (hα : 0 < M.α) {r₀ : ℝ} (hr₀ : 0 < r₀)
    (hβ : (0 : ℝ) < M.betaCrit)
    (hac : ∀ R : ℝ, r₀ ≤ R → AbsolutelyContinuousOnInterval
      (fun r : ℝ => (M.cutMoment 2 r).toReal) r₀ R)
    (hmR : Measurable M.rhsScalarTwo)
    (hae : ∀ᵐ t ∂(volume.restrict (Ici r₀)),
      HasDerivAt (fun r : ℝ => (M.cutMoment 2 r).toReal) (M.rhsScalarTwo t) t)
    {a₀ : ℝ}
    (h2 : ∀ t : ℝ, r₀ ≤ t → M.cutMoment 2 t ≠ ⊤)
    (hTri : TriTail.openTriangleSelf M.kernel M.kernel_nonneg M.betaCrit 0 < ⊤)
    {C₀ p : ℝ} (hC₀ : 0 ≤ C₀) (hp : 1 < p)
    (hF : Analysis.LogRadialBound (fun y : M.V => M.S.dist (0 : M.V) y)
      (fun y : M.V => TriTail.openTriangle M.kernel M.kernel_nonneg M.betaCrit 0 y) C₀ p)
    (T : ℕ → Finset M.V) (hTmono : Monotone T) (hT : ∀ y : M.V, ∃ n, y ∈ T n)
    (S : ℕ → Finset (Sym2 M.V)) (hSmono : Monotone S) (hS : ∀ e : Sym2 M.V, ∃ n, e ∈ S n)
    {R : ℝ} (hRpos : 0 < R) (hRa₀ : R < a₀)
    (hlow : ∀ s : ℝ, R < s → (1 / 2) * s ^ (-(M.d : ℝ) - M.α - 1) ≤ |deriv M.K s|)
    (hupp : ∀ s : ℝ, R < s → |deriv M.K s| ≤ 2 * s ^ (-(M.d : ℝ) - M.α - 1))
    (hcontinf : ∀ y : M.V, ∀ r : ℝ, a₀ ≤ r → ContinuousAt
      (sMomentInfFlux (0 : M.V) {y} (fun _ => (1 : ℝ)) M.cutProb M.cutEdgeDeriv) r)
    (hK : ∀ r : ℝ, a₀ ≤ r → ContinuousAt (fun r' => deriv M.K r') r)
    (hex : ∀ r : ℝ, a₀ ≤ r → ContinuousAt M.exclScalar r)
    (htop : M.uncutMean M.betaCrit = ⊤)
    {c3 : ℝ} (hc3 : 0 < c3)
    (hgm : ∀ᶠ r : ℝ in atTop, c3 * (M.cutMassAt r 0).toReal ^ 3 ≤ (M.cutMoment 2 r).toReal) :
    Analysis.RegularlyVaryingAtTop (fun r : ℝ => (M.cutMoment 2 r).toReal) (3 * M.α) := by
  obtain ⟨hP, -, -⟩ :=
    M.case3_firstMoment_inputs_of_triangle (a₀ := max a₀ r₀) hβ T hTmono hT S hSmono hS
      hRpos (lt_of_lt_of_le hRa₀ (le_max_left a₀ r₀)) hlow hupp
      (fun t ht => h2 t (le_trans (le_max_right a₀ r₀) ht))
      (fun y r hr => hcontinf y r (le_trans (le_max_left a₀ r₀) hr))
      (fun r hr => hK r (le_trans (le_max_left a₀ r₀) hr))
      (fun r hr => hex r (le_trans (le_max_left a₀ r₀) hr))
      htop hTri hC₀ hp hF
  refine M.regularlyVarying_two_of_source_p21 hα hr₀ (ne_of_gt hβ) hac hmR hae ?_ h2 hP hTri
    hC₀ hp hF hc3 hgm
  intro t ht
  exact ne_top_of_le_ne_top (h2 t ht) (M.cutMoment_one_le_cutMoment_two t)

end SourceModelData
end Orchestration
end PercLib.CriticalLRP

namespace PercLib.CriticalLRP

namespace I420Case3

open Orchestration

/-! ## Connection to the `I.4.20` Case-3 consumer

`SplitPolygon/DirectSource.lean` proves the direct Case-3 ratio limits
(`case3_hAend_hAmid_cutPoly_source`) from `hP` and the polygon/split data.  The wrapper below
replaces that `hP` hypothesis by the source-level first-moment package, so the I.4.20 path no
longer receives the first-moment asymptotic as an input.  Nothing else in the I.4.20 statement
is changed: the higher/`p`-th moment finiteness `hMa`, `hMb`, the homogeneity `hhom`, the tail
`hTail`, the second-moment gap `hgm`, the triangle condition and the open-triangle radial log
bound are all retained verbatim. -/

/-- **Case 3 of the I.4.20 ratio limits with the first-moment asymptotic discharged.** -/
theorem case3_hAend_hAmid_cutPoly_source_of_source_firstMoment (M : SourceModelData)
    (hβ : (0 : ℝ) < M.betaCrit)
    (T : ℕ → Finset M.V) (hTmono : Monotone T) (hT : ∀ y : M.V, ∃ n, y ∈ T n)
    (S : ℕ → Finset (Sym2 M.V)) (hSmono : Monotone S) (hS : ∀ e : Sym2 M.V, ∃ n, e ∈ S n)
    {R a₀ : ℝ} (hRpos : 0 < R) (hRa₀ : R < a₀)
    (hlow : ∀ s : ℝ, R < s → (1 / 2) * s ^ (-(M.d : ℝ) - M.α - 1) ≤ |deriv M.K s|)
    (hupp : ∀ s : ℝ, R < s → |deriv M.K s| ≤ 2 * s ^ (-(M.d : ℝ) - M.α - 1))
    (h2 : ∀ t : ℝ, a₀ ≤ t → M.cutMoment 2 t ≠ ⊤)
    (hcontinf : ∀ y : M.V, ∀ r : ℝ, a₀ ≤ r → ContinuousAt
      (sMomentInfFlux (0 : M.V) {y} (fun _ => (1 : ℝ)) M.cutProb M.cutEdgeDeriv) r)
    (hK : ∀ r : ℝ, a₀ ≤ r → ContinuousAt (fun r' => deriv M.K r') r)
    (hex : ∀ r : ℝ, a₀ ≤ r → ContinuousAt M.exclScalar r)
    (htop : M.uncutMean M.betaCrit = ⊤)
    (hTri : TriTail.openTriangleSelf M.kernel M.kernel_nonneg M.betaCrit 0 < ⊤)
    {C₁ pF : ℝ} (hC₁ : 0 ≤ C₁) (hpF : 1 < pF)
    (hF : Analysis.LogRadialBound (fun y : M.V => M.S.dist 0 y)
      (fun y : M.V => TriTail.openTriangle M.kernel M.kernel_nonneg M.betaCrit 0 y) C₁ pF)
    (𝓔 : ℕ → Finset (Sym2 M.V)) (h𝓔mono : Monotone 𝓔)
    (h𝓔 : ∀ e : Sym2 M.V, ∃ n, e ∈ 𝓔 n) (p : ℕ) (hp : 3 ≤ p)
    {θ : ℝ} (hθ0 : 0 < θ) (hθ1 : θ < 1)
    (hTail : Tendsto (fun r => (M.nablaTail r).toReal) atTop (𝓝 0))
    (hhom : ∀ (r : ℝ), 1 ≤ r → ∀ (ℓ : ℕ), ℓ + 1 ≤ p →
      ∀ y ∈ (BallAverage.ball_finite M r).toFinset,
        I420Case1.powMomentAt (M.cutProb r) (p - ℓ) y =
          I420Case1.powMomentAt (M.cutProb r) (p - ℓ) 0)
    (hMa : ∀ (r : ℝ), 1 ≤ r → ∀ ℓ : ℕ, ℓ ≤ p →
      I420Case1.powMomentAt (M.cutProb r) (ℓ + 1) (0 : M.V) ≠ ⊤)
    (hMb : ∀ (r : ℝ), 1 ≤ r → ∀ (ℓ : ℕ), ℓ + 1 ≤ p →
      ∀ y ∈ (BallAverage.ball_finite M r).toFinset,
        I420Case1.powMomentAt (M.cutProb r) (p - ℓ) y ≠ ⊤)
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
              momOf (fun r => M.cutProb r) (0 : M.V) (p - ℓ) r))) atTop (𝓝 1) := by
  obtain ⟨hP, -, -⟩ := M.case3_firstMoment_inputs_of_triangle hβ T hTmono hT S hSmono hS
    hRpos hRa₀ hlow hupp h2 hcontinf hK hex htop hTri hC₁ hpF hF
  exact case3_hAend_hAmid_cutPoly_source M hP hTri 𝓔 h𝓔mono h𝓔 p hp hθ0 hθ1 hTail hhom hMa
    hMb hc3 hgm

end I420Case3

end PercLib.CriticalLRP

/-! ## Axiom audit -/

set_option linter.hashCommand false

#print axioms PercLib.CriticalLRP.Orchestration.SourceModelData.eventually_cutMoment_one_ne_top
#print axioms PercLib.CriticalLRP.Orchestration.SourceModelData.eventually_cutMassAt_ne_top_of_cutMoment_two
#print axioms PercLib.CriticalLRP.Orchestration.SourceModelData.tendsto_cutMassReal_atTop_of_uncutMean_eq_top
#print axioms PercLib.CriticalLRP.Orchestration.SourceModelData.isLogErrorFunction_cutE1_of_triangle
#print axioms PercLib.CriticalLRP.Orchestration.SourceModelData.tendsto_cutError_of_triangle
#print axioms PercLib.CriticalLRP.Orchestration.SourceModelData.exists_tail_bound_abs_cutError
#print axioms PercLib.CriticalLRP.Orchestration.SourceModelData.case3_firstMoment_inputs_of_triangle
#print axioms PercLib.CriticalLRP.Orchestration.SourceModelData.secondMoment_asymptotic_case3_of_source_p21_firstMoment
#print axioms PercLib.CriticalLRP.Orchestration.SourceModelData.regularlyVarying_two_of_source_p21_firstMoment
#print axioms PercLib.CriticalLRP.I420Case3.case3_hAend_hAmid_cutPoly_source_of_source_firstMoment

namespace PercLib.CriticalLRP
namespace Orchestration
namespace SourceModelData

variable (M : SourceModelData)

/-! ## Removing the kernel and exhaustion hypotheses

Three further packages are *not* inputs of the source model:

* `0 < M.α` is the structure field `M.hα`;
* the two-sided kernel tail bound `(1/2) s^{-d-α-1} ≤ |K'(s)| ≤ 2 s^{-d-α-1}` on a tail is
  `SourceModelData.exists_deriv_bounds`, straight from the structure field `exists_error`
  (`|K'(r)| = (1 + δ r) r^{-d-α-1}`, `δ → 0`);
* the vertex and edge exhaustions exist because `M.V = Fin M.d → ℤ` is countable. -/

/-- A monotone finite exhaustion of the vertex set. -/
theorem exists_vertex_exhaustion :
    ∃ T : ℕ → Finset M.V, Monotone T ∧ ∀ y : M.V, ∃ n, y ∈ T n :=
  PercLib.Percolation.Bond.exists_finset_exhaustion

/-- A monotone finite exhaustion of the edge set. -/
theorem exists_edge_exhaustion :
    ∃ S : ℕ → Finset (Sym2 M.V), Monotone S ∧ ∀ e : Sym2 M.V, ∃ n, e ∈ S n :=
  PercLib.Percolation.Bond.exists_finset_exhaustion

/-- **Proposition I.4.2, Case 3, at the literal cutoff law, from the source model alone.** -/
theorem case3_firstMoment_inputs_of_source
    (hβ : (0 : ℝ) < M.betaCrit) {a₀ : ℝ}
    (h2 : ∀ t : ℝ, a₀ ≤ t → M.cutMoment 2 t ≠ ⊤)
    (hcontinf : ∀ y : M.V, ∀ r : ℝ, a₀ ≤ r → ContinuousAt
      (sMomentInfFlux (0 : M.V) {y} (fun _ => (1 : ℝ)) M.cutProb M.cutEdgeDeriv) r)
    (hK : ∀ r : ℝ, a₀ ≤ r → ContinuousAt (fun r' => deriv M.K r') r)
    (hex : ∀ r : ℝ, a₀ ≤ r → ContinuousAt M.exclScalar r)
    (htop : M.uncutMean M.betaCrit = ⊤)
    (hTri : TriTail.openTriangleSelf M.kernel M.kernel_nonneg M.betaCrit 0 < ⊤)
    {C₁ p : ℝ} (hC₁ : 0 ≤ C₁) (hp : 1 < p)
    (hF : Analysis.LogRadialBound (fun y : M.V => M.S.dist 0 y)
      (fun y : M.V => TriTail.openTriangle M.kernel M.kernel_nonneg M.betaCrit 0 y) C₁ p) :
    Tendsto (fun r : ℝ => (M.cutMassAt r 0).toReal
        / ((M.α / (M.betaCrit : ℝ)) * r ^ M.α)) atTop (𝓝 1)
      ∧ Analysis.LogarithmicallyIntegrable M.p2H
      ∧ Analysis.LogarithmicallyIntegrable (PivotFlux.cutE0 M) := by
  obtain ⟨R, hRpos, -, hlow, hupp⟩ := M.exists_deriv_bounds
  obtain ⟨T, hTmono, hT⟩ := M.exists_vertex_exhaustion
  obtain ⟨S, hSmono, hS⟩ := M.exists_edge_exhaustion
  have hA : a₀ ≤ max a₀ R + 1 := le_trans (le_max_left a₀ R) (by linarith)
  refine M.case3_firstMoment_inputs_of_triangle (a₀ := max a₀ R + 1) hβ T hTmono hT S hSmono
    hS hRpos (lt_of_le_of_lt (le_max_right a₀ R) (by linarith)) hlow hupp
    (fun t ht => h2 t (le_trans hA ht))
    (fun y r hr => hcontinf y r (le_trans hA hr))
    (fun r hr => hK r (le_trans hA hr)) (fun r hr => hex r (le_trans hA hr))
    htop hTri hC₁ hp hF

end SourceModelData
end Orchestration
end PercLib.CriticalLRP

namespace PercLib.CriticalLRP
namespace Orchestration
namespace SourceModelData

variable (M : SourceModelData)

/-! ## The headline consumers: `hP`, `hlogH`, `hlogE0` no longer appear

These are `secondMoment_asymptotic_case3_of_source_p21` and
`regularlyVarying_two_of_source_p21` with

* `hα` (the structure field `M.hα`),
* `h1` (from `cutMoment 1 ≤ cutMoment 2` and `h2`),
* `hP`, `hlogH`, `hlogE0` (Proposition I.4.2, Case 3, by `case3_firstMoment_inputs_of_source`),
* the kernel tail pair and the vertex/edge exhaustions

all removed.  What is added is `E_{β_c}|K| = ∞` (`htop`) together with the continuity triple
`hcontinf`, `hK`, `hex`, which are regularity of the source model rather than asymptotic
statements. -/

/-- **Proposition I.4.15, Case 3, from the source model and the `(2,1)` product gap.** -/
theorem secondMoment_asymptotic_case3_p21_hP_discharged
    {r₀ : ℝ} (hr₀ : 0 < r₀)
    (hβ : (0 : ℝ) < M.betaCrit)
    (hac : ∀ R : ℝ, r₀ ≤ R → AbsolutelyContinuousOnInterval
      (fun r : ℝ => (M.cutMoment 2 r).toReal) r₀ R)
    (hae : ∀ᵐ t ∂(volume.restrict (Ici r₀)),
      HasDerivAt (fun r : ℝ => (M.cutMoment 2 r).toReal) (M.rhsScalarTwo t) t)
    (h2 : ∀ t : ℝ, r₀ ≤ t → M.cutMoment 2 t ≠ ⊤)
    (hTri : TriTail.openTriangleSelf M.kernel M.kernel_nonneg M.betaCrit 0 < ⊤)
    {C₀ p : ℝ} (hC₀ : 0 ≤ C₀) (hp : 1 < p)
    (hF : Analysis.LogRadialBound (fun y : M.V => M.S.dist (0 : M.V) y)
      (fun y : M.V => TriTail.openTriangle M.kernel M.kernel_nonneg M.betaCrit 0 y) C₀ p)
    (hmeasE2 : Measurable M.p2ExclError) (hmeasEbar : Measurable M.p2Ebar)
    {a₀ : ℝ}
    (hcontinf : ∀ y : M.V, ∀ r : ℝ, a₀ ≤ r → ContinuousAt
      (sMomentInfFlux (0 : M.V) {y} (fun _ => (1 : ℝ)) M.cutProb M.cutEdgeDeriv) r)
    (hK : ∀ r : ℝ, a₀ ≤ r → ContinuousAt (fun r' => deriv M.K r') r)
    (hex : ∀ r : ℝ, a₀ ≤ r → ContinuousAt M.exclScalar r)
    (htop : M.uncutMean M.betaCrit = ⊤)
    {c3 : ℝ} (hc3 : 0 < c3)
    (hgm : ∀ᶠ r : ℝ in atTop, c3 * (M.cutMassAt r 0).toReal ^ 3 ≤ (M.cutMoment 2 r).toReal) :
    ∃ A : ℝ, 0 < A ∧ Tendsto
      (fun r : ℝ => (M.cutMoment 2 r).toReal / r ^ (3 * M.α)) atTop (𝓝 A) := by
  obtain ⟨R, hRpos, -, hlow, hupp⟩ := M.exists_deriv_bounds
  obtain ⟨T, hTmono, hT⟩ := M.exists_vertex_exhaustion
  obtain ⟨S, hSmono, hS⟩ := M.exists_edge_exhaustion
  have hA : a₀ ≤ max (max a₀ r₀) R + 1 :=
    le_trans (le_trans (le_max_left a₀ r₀) (le_max_left _ R)) (by linarith)
  have hAr : r₀ ≤ max (max a₀ r₀) R + 1 :=
    le_trans (le_trans (le_max_right a₀ r₀) (le_max_left _ R)) (by linarith)
  have hR : R < max (max a₀ r₀) R + 1 := lt_of_le_of_lt (le_max_right _ R) (by linarith)
  exact M.secondMoment_asymptotic_case3_of_source_p21_firstMoment
    (a₀ := max (max a₀ r₀) R + 1) M.hα hr₀ hβ hac hae
    h2 hTri hC₀ hp hF hmeasE2 hmeasEbar
    T hTmono hT S hSmono hS hRpos hR hlow hupp
    (fun y r hr => hcontinf y r (le_trans hA hr)) (fun r hr => hK r (le_trans hA hr))
    (fun r hr => hex r (le_trans hA hr)) htop hc3 hgm

/-- The regularly-varying half of Proposition I.4.15, Case 3, from the source model and the
`(2,1)` product gap. -/
theorem regularlyVarying_two_p21_hP_discharged
    {r₀ : ℝ} (hr₀ : 0 < r₀)
    (hβ : (0 : ℝ) < M.betaCrit)
    (hac : ∀ R : ℝ, r₀ ≤ R → AbsolutelyContinuousOnInterval
      (fun r : ℝ => (M.cutMoment 2 r).toReal) r₀ R)
    (hmR : Measurable M.rhsScalarTwo)
    (hae : ∀ᵐ t ∂(volume.restrict (Ici r₀)),
      HasDerivAt (fun r : ℝ => (M.cutMoment 2 r).toReal) (M.rhsScalarTwo t) t)
    (h2 : ∀ t : ℝ, r₀ ≤ t → M.cutMoment 2 t ≠ ⊤)
    (hTri : TriTail.openTriangleSelf M.kernel M.kernel_nonneg M.betaCrit 0 < ⊤)
    {C₀ p : ℝ} (hC₀ : 0 ≤ C₀) (hp : 1 < p)
    (hF : Analysis.LogRadialBound (fun y : M.V => M.S.dist (0 : M.V) y)
      (fun y : M.V => TriTail.openTriangle M.kernel M.kernel_nonneg M.betaCrit 0 y) C₀ p)
    {a₀ : ℝ}
    (hcontinf : ∀ y : M.V, ∀ r : ℝ, a₀ ≤ r → ContinuousAt
      (sMomentInfFlux (0 : M.V) {y} (fun _ => (1 : ℝ)) M.cutProb M.cutEdgeDeriv) r)
    (hK : ∀ r : ℝ, a₀ ≤ r → ContinuousAt (fun r' => deriv M.K r') r)
    (hex : ∀ r : ℝ, a₀ ≤ r → ContinuousAt M.exclScalar r)
    (htop : M.uncutMean M.betaCrit = ⊤)
    {c3 : ℝ} (hc3 : 0 < c3)
    (hgm : ∀ᶠ r : ℝ in atTop, c3 * (M.cutMassAt r 0).toReal ^ 3 ≤ (M.cutMoment 2 r).toReal) :
    Analysis.RegularlyVaryingAtTop (fun r : ℝ => (M.cutMoment 2 r).toReal) (3 * M.α) := by
  obtain ⟨R, hRpos, -, hlow, hupp⟩ := M.exists_deriv_bounds
  obtain ⟨T, hTmono, hT⟩ := M.exists_vertex_exhaustion
  obtain ⟨S, hSmono, hS⟩ := M.exists_edge_exhaustion
  have hA : a₀ ≤ max (max a₀ r₀) R + 1 :=
    le_trans (le_trans (le_max_left a₀ r₀) (le_max_left _ R)) (by linarith)
  have hAr : r₀ ≤ max (max a₀ r₀) R + 1 :=
    le_trans (le_trans (le_max_right a₀ r₀) (le_max_left _ R)) (by linarith)
  have hR : R < max (max a₀ r₀) R + 1 := lt_of_le_of_lt (le_max_right _ R) (by linarith)
  exact M.regularlyVarying_two_of_source_p21_firstMoment (a₀ := max (max a₀ r₀) R + 1) M.hα
    hr₀ hβ hac hmR hae h2 hTri hC₀ hp hF T hTmono hT
    S hSmono hS hRpos hR hlow hupp
    (fun y r hr => hcontinf y r (le_trans hA hr)) (fun r hr => hK r (le_trans hA hr))
    (fun r hr => hex r (le_trans hA hr)) htop hc3 hgm

end SourceModelData
end Orchestration
end PercLib.CriticalLRP

namespace PercLib.CriticalLRP

namespace I420Case3

open Orchestration

/-- **Case 3 of the I.4.20 ratio limits with `hP` discharged from the source model.** -/
theorem case3_hAend_hAmid_cutPoly_source_hP_discharged (M : SourceModelData)
    (hβ : (0 : ℝ) < M.betaCrit)
    (hTri : TriTail.openTriangleSelf M.kernel M.kernel_nonneg M.betaCrit 0 < ⊤)
    {C₁ pF : ℝ} (hC₁ : 0 ≤ C₁) (hpF : 1 < pF)
    (hF : Analysis.LogRadialBound (fun y : M.V => M.S.dist 0 y)
      (fun y : M.V => TriTail.openTriangle M.kernel M.kernel_nonneg M.betaCrit 0 y) C₁ pF)
    {a₀ : ℝ}
    (hcontinf : ∀ y : M.V, ∀ r : ℝ, a₀ ≤ r → ContinuousAt
      (sMomentInfFlux (0 : M.V) {y} (fun _ => (1 : ℝ)) M.cutProb M.cutEdgeDeriv) r)
    (hK : ∀ r : ℝ, a₀ ≤ r → ContinuousAt (fun r' => deriv M.K r') r)
    (hex : ∀ r : ℝ, a₀ ≤ r → ContinuousAt M.exclScalar r)
    (h2 : ∀ t : ℝ, a₀ ≤ t → M.cutMoment 2 t ≠ ⊤)
    (htop : M.uncutMean M.betaCrit = ⊤)
    (𝓔 : ℕ → Finset (Sym2 M.V)) (h𝓔mono : Monotone 𝓔)
    (h𝓔 : ∀ e : Sym2 M.V, ∃ n, e ∈ 𝓔 n) (p : ℕ) (hp : 3 ≤ p)
    {θ : ℝ} (hθ0 : 0 < θ) (hθ1 : θ < 1)
    (hTail : Tendsto (fun r => (M.nablaTail r).toReal) atTop (𝓝 0))
    (hhom : ∀ (r : ℝ), 1 ≤ r → ∀ (ℓ : ℕ), ℓ + 1 ≤ p →
      ∀ y ∈ (BallAverage.ball_finite M r).toFinset,
        I420Case1.powMomentAt (M.cutProb r) (p - ℓ) y =
          I420Case1.powMomentAt (M.cutProb r) (p - ℓ) 0)
    (hMa : ∀ (r : ℝ), 1 ≤ r → ∀ ℓ : ℕ, ℓ ≤ p →
      I420Case1.powMomentAt (M.cutProb r) (ℓ + 1) (0 : M.V) ≠ ⊤)
    (hMb : ∀ (r : ℝ), 1 ≤ r → ∀ (ℓ : ℕ), ℓ + 1 ≤ p →
      ∀ y ∈ (BallAverage.ball_finite M r).toFinset,
        I420Case1.powMomentAt (M.cutProb r) (p - ℓ) y ≠ ⊤)
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
              momOf (fun r => M.cutProb r) (0 : M.V) (p - ℓ) r))) atTop (𝓝 1) := by
  obtain ⟨hP, -, -⟩ := M.case3_firstMoment_inputs_of_source hβ h2 hcontinf hK hex htop hTri
    hC₁ hpF hF
  exact case3_hAend_hAmid_cutPoly_source M hP hTri 𝓔 h𝓔mono h𝓔 p hp hθ0 hθ1 hTail hhom hMa
    hMb hc3 hgm

end I420Case3

end PercLib.CriticalLRP

/-! ## Axiom audit (headline theorems) -/

set_option linter.hashCommand false

#print axioms PercLib.CriticalLRP.Orchestration.SourceModelData.exists_vertex_exhaustion
#print axioms PercLib.CriticalLRP.Orchestration.SourceModelData.exists_edge_exhaustion
#print axioms PercLib.CriticalLRP.Orchestration.SourceModelData.case3_firstMoment_inputs_of_source
#print axioms PercLib.CriticalLRP.Orchestration.SourceModelData.secondMoment_asymptotic_case3_p21_hP_discharged
#print axioms PercLib.CriticalLRP.Orchestration.SourceModelData.regularlyVarying_two_p21_hP_discharged
#print axioms PercLib.CriticalLRP.I420Case3.case3_hAend_hAmid_cutPoly_source_hP_discharged
