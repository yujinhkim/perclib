/-
Ultramath swarm `smwzlje3f`, member `m6`, direction `d6` (campaign direction (B)).

Copyright (c) 2026 PercLib contributors. Released under Apache 2.0.

Accepted and independently rebuilt from Ultramath `smwzlje3f`.
Production base `a59bc6c22aba42e69160666c17feac870d4cb887`; reviewed scratch source `.ultramath/smwzlje3f/m6/Main.lean`.

# The first two cutoff moments are *not* residual inputs of the Case-3 wrapper

`SourceModelData.secondMoment_asymptotic_case3_of_source_p21` (production commit
`5d2d681b941eb1c687f1ba17e6a798b8f0175aa0`,
`PercLib/CriticalLRP/Analysis/SecondMomentCase3/ProductGap/SourceConsumer.lean`) retains
`h1`, `h2` and `hβ` among its explicit inputs.  This file proves that all three are consequences
of the *first-moment asymptotic* `hP` that the wrapper already retains, so they can be removed
from the retained list without weakening the theorem.

The route is production's uniform lower comparison
(`Analysis/Polygon/ChiInput.lean`, `exists_chi_lower_uniform_and_finite`): `hP` gives `c₀ > 0`
with `c₀ r^α ≤ (M.cutMassAt r 0).toReal` for *every* `r > 0`, and a positive `toReal` value
excludes `⊤`; monotonicity of the cutoff moment in the radius carries this down from the
threshold of the limit to every positive radius.  Then the ordinary atlas bound
(`cutMoment_ne_top_of_one`, "a finite first cutoff moment gives every higher cutoff moment")
gives all orders at once.

Nothing here assumes a subcritical regime, a finite critical susceptibility, or a subcritical
moment.  In particular the sharpness input `M.SubcriticalFiniteMean` — the only premise under
which production previously derived cutoff finiteness
(`cutMoment_ne_top_of_subcritical_first`) — is *not* needed: `hP` alone forces finiteness of every
cutoff moment at every positive radius.  That is the precise answer to "which subcritical /
uniform-in-r first-moment input is missing": none is missing once `hP` is available.

The file also contains the corresponding consumer replacements:

* `secondMoment_asymptotic_case3_of_source_p21_minimal` — the same conclusion as the landed
  wrapper, with `h1`, `h2` and `hβ` removed;
* `p2ExclError_tendsto_zero_of_source_p21_minimal` and
  `logIntegrable_p2ExclError_of_source_p21_minimal` — the two intermediate Case-3 conclusions,
  likewise with `h1`, `h2` removed;
* `rootMomentsFiniteUpTo_of_hP` — the all-order finiteness shape `hMa` of the `I420Case3`
  consumers, from `hP`;
* `case3_hAend_hAmid_cutPoly_source_of_HD_case3_divergence_of_subcritical_first` — the
  `I.4.20` Case-3 assembly with **both** `h2` and `hMa` removed, replacing the strictly stronger
  subcritical *second*-moment premise of
  `case3_hAend_hAmid_cutPoly_source_of_HD_case3_divergence_of_subcritical_second` by
  `M.SubcriticalFiniteMean` (subcritical *first* moment).

All results are stated for the infinite-volume normalized source model `SourceModelData`; no
finite torus, no cutoff substitute.  No `sorry`, no `admit`, no `native_decide`, no custom axiom.
-/
module

public import PercLib.CriticalLRP.Analysis.SecondMomentCase3.FiniteMoments.Defs
public import PercLib.CriticalLRP.Analysis.Polygon.ChiInput
public import PercLib.CriticalLRP.Analysis.SecondMomentCase3.ProductGap.SourceConsumer
public import PercLib.CriticalLRP.Analysis.Cutoff.OffCorner.SubcriticalAllMoments
public import PercLib.CriticalLRP.Analysis.Cutoff.SecondMoment.Covariance
public import PercLib.CriticalLRP.VolumeMoments.HigherMoments.I420Case3.CriticalDivergence

@[expose] public section

noncomputable section

open MeasureTheory Measure ProbabilityTheory unitInterval Filter Topology Set
open scoped ENNReal NNReal Topology BigOperators

set_option autoImplicit false
set_option linter.unusedSectionVars false
set_option linter.hashCommand false
set_option linter.style.longLine false

namespace PercLib.CriticalLRP
namespace Orchestration
namespace SourceModelData

open PercLib.CriticalLRP.I418C.ChiInput

variable (M : SourceModelData)

/-! ## 1. `hP` forces finiteness of every cutoff moment at every positive radius -/

/-- **The critical parameter is positive as soon as the first-moment asymptotic holds**
(production `ChiInput.betaCrit_pos_of_tendsto_chi_div`, restated in the model
namespace).  This removes `hβ` from the Case-3 wrapper: its `(M.betaCrit : ℝ) ≠ 0` is literal. -/
theorem betaCrit_pos_of_firstMoment_asymptotic
    (hP : Tendsto (fun r : ℝ => (M.cutMassAt r 0).toReal
      / ((M.α / (M.betaCrit : ℝ)) * r ^ M.α)) atTop (𝓝 1)) :
    0 < (M.betaCrit : ℝ) :=
  betaCrit_pos_of_tendsto_chi_div M hP

/-- **Uniform lower comparison plus finiteness, from `hP`** (production
`exists_chi_lower_uniform_and_finite`, restated in the model namespace). -/
theorem exists_chi_lower_uniform_and_finite_of_firstMoment_asymptotic
    (hP : Tendsto (fun r : ℝ => (M.cutMassAt r 0).toReal
      / ((M.α / (M.betaCrit : ℝ)) * r ^ M.α)) atTop (𝓝 1)) :
    ∃ c₀ : ℝ, 0 < c₀ ∧ ∀ r : ℝ, 0 < r →
      c₀ * r ^ M.α ≤ (M.cutMassAt r 0).toReal ∧ M.cutMassAt r 0 ≠ ⊤ :=
  exists_chi_lower_uniform_and_finite M (M.betaCrit_pos_of_firstMoment_asymptotic hP) hP

/-- **Every positive cutoff moment is finite at every positive radius, from `hP`.**

The first moment is finite at every `r > 0` because `hP` gives a positive uniform lower bound
for `(M.cutMassAt r 0).toReal = (M.cutMoment 1 r).toReal`; every higher moment then follows from
the ordinary atlas bound `cutMoment_ne_top_of_one`. -/
theorem allCutoffMomentsFinite_of_firstMoment_asymptotic
    (hP : Tendsto (fun r : ℝ => (M.cutMassAt r 0).toReal
      / ((M.α / (M.betaCrit : ℝ)) * r ^ M.α)) atTop (𝓝 1)) :
    M.AllCutoffMomentsFinite := by
  obtain ⟨c₀, hc₀, hχu⟩ := M.exists_chi_lower_uniform_and_finite_of_firstMoment_asymptotic hP
  intro r hr q _hq
  have h1 : M.cutMoment 1 r ≠ ⊤ := by
    rw [← M.cutMassAt_zero_eq_cutMoment r]
    exact (hχu r hr).2
  exact cutMoment_ne_top_of_one M r h1 q

/-- **The literal `h1` of the Case-3 wrapper, from `hP`, at any threshold `r₀`** (the threshold
may be non-positive; below `1` monotonicity of the cutoff moment in the radius applies). -/
theorem cutoffMomentsFinite_of_firstMoment_asymptotic
    (hP : Tendsto (fun r : ℝ => (M.cutMassAt r 0).toReal
      / ((M.α / (M.betaCrit : ℝ)) * r ^ M.α)) atTop (𝓝 1)) (r₀ : ℝ) :
    M.CutoffMomentsFinite r₀ := by
  intro t _ht
  rcases lt_or_ge 0 t with ht0 | ht0
  · exact M.allCutoffMomentsFinite_of_firstMoment_asymptotic hP t ht0 1 le_rfl
  · exact ne_top_of_le_ne_top
      (M.allCutoffMomentsFinite_of_firstMoment_asymptotic hP 1 one_pos 1 le_rfl)
      (M.cutMoment_monotone 1 (le_trans ht0 zero_le_one))

/-- **The literal `h2` of the Case-3 wrapper, from `hP`, at any threshold `r₀`.** -/
theorem cutoffSecondMomentsFinite_of_firstMoment_asymptotic
    (hP : Tendsto (fun r : ℝ => (M.cutMassAt r 0).toReal
      / ((M.α / (M.betaCrit : ℝ)) * r ^ M.α)) atTop (𝓝 1)) (r₀ : ℝ) :
    M.CutoffSecondMomentsFinite r₀ := by
  intro t _ht
  rcases lt_or_ge 0 t with ht0 | ht0
  · exact M.allCutoffMomentsFinite_of_firstMoment_asymptotic hP t ht0 2 (by norm_num)
  · exact ne_top_of_le_ne_top
      (M.allCutoffMomentsFinite_of_firstMoment_asymptotic hP 1 one_pos 2 (by norm_num))
      (M.cutMoment_monotone 2 (le_trans ht0 zero_le_one))

/-- **`hP` forces divergence of the *uncut* critical first moment**, i.e. the paper's own input
`E_{β_c}|K_0| = ⊤` of the `I.4.20` Case-3 consumers (`htop`).

So the Case-3 hypotheses are *not* compatible with a finite critical susceptibility: the uniform
lower comparison `χ(r) ⪰ r^α` is exactly the statement that the cutoff means diverge as `r → ∞`,
which production records as `uncut_firstMoment_eq_top_of_chi_lower`.  (Restated in the model
namespace; the arithmetic is production's `ChiInput.uncut_firstMoment_eq_top_of_chi_lower`.) -/
theorem uncutMean_eq_top_of_firstMoment_asymptotic
    (hP : Tendsto (fun r : ℝ => (M.cutMassAt r 0).toReal
      / ((M.α / (M.betaCrit : ℝ)) * r ^ M.α)) atTop (𝓝 1)) :
    M.uncutMean M.betaCrit = ⊤ := by
  obtain ⟨c₀, hc₀, hχu⟩ := M.exists_chi_lower_uniform_and_finite_of_firstMoment_asymptotic hP
  exact uncut_firstMoment_eq_top_of_chi_lower M hc₀ (fun r hr => (hχu r hr).1)

/-! ## 2. The two retained moments are one input, and the threshold is irrelevant -/

/-- `h1` and `h2` are the *same* proposition: `|K_0| ≥ 1` gives `‖K_0‖₁ ≤ ‖K_0‖₂`, and a finite
first moment gives every higher moment. -/
theorem cutoffMomentsFinite_iff_cutoffSecondMomentsFinite (r₀ : ℝ) :
    M.CutoffMomentsFinite r₀ ↔ M.CutoffSecondMomentsFinite r₀ := by
  constructor
  · intro h1 t ht
    exact cutMoment_ne_top_of_one M t (h1 t ht) 2
  · intro h2 t ht
    exact M.cutMoment_one_ne_top_of_two (h2 t ht)

/-- `h1` at *any* threshold is the same as finiteness at every positive radius: above the
threshold it is the hypothesis, below it monotonicity of the cutoff moment in the radius
(`cutMoment_monotone`) reduces to the threshold value. -/
theorem cutoffMomentsFinite_iff_forall_pos {r₀ : ℝ} (hr₀ : 0 < r₀) :
    M.CutoffMomentsFinite r₀ ↔ ∀ t : ℝ, 0 < t → M.cutMoment 1 t ≠ ⊤ := by
  constructor
  · intro h t ht
    rcases le_or_gt r₀ t with hle | hlt
    · exact h t hle
    · exact ne_top_of_le_ne_top (h r₀ le_rfl) (M.cutMoment_monotone 1 (le_of_lt hlt))
  · intro h t ht
    exact h t (lt_of_lt_of_le hr₀ ht)

/-! ## 3. The all-order finiteness shape `hMa` of the `I420Case3` consumers -/

/-- **The `hMa` shape from first-moment finiteness at `r ≥ 1`.**  `powMomentAt (M.cutProb r) m 0`
is literally `M.cutMoment m r` (`powMomentAt_cutProb_eq_cutMoment`). -/
theorem rootMomentsFiniteUpTo_of_first
    (h : ∀ r : ℝ, 1 ≤ r → M.cutMoment 1 r ≠ ⊤) (p : ℕ) :
    M.RootMomentsFiniteUpTo p := by
  intro r hr ℓ _hℓ
  exact cutMoment_ne_top_of_one M r (h r hr) (ℓ + 1)

/-- **The `hMa` shape from `hP`.** -/
theorem rootMomentsFiniteUpTo_of_firstMoment_asymptotic
    (hP : Tendsto (fun r : ℝ => (M.cutMassAt r 0).toReal
      / ((M.α / (M.betaCrit : ℝ)) * r ^ M.α)) atTop (𝓝 1)) (p : ℕ) :
    M.RootMomentsFiniteUpTo p := by
  refine M.rootMomentsFiniteUpTo_of_first (fun r hr => ?_) p
  exact M.allCutoffMomentsFinite_of_firstMoment_asymptotic hP r
    (lt_of_lt_of_le zero_lt_one hr) 1 le_rfl

/-- **The `hMa` shape from `h2` on a tail `[r₀, ∞)` with `r₀ > 0`.**

No new premise: above `r₀` the second moment is finite, and below `r₀` monotonicity of the
cutoff moment in the radius reduces to the value at `max r r₀`.  This is why `hMa` is not an
independent input of the `I420Case3` Case-3 consumers: it follows from the second cutoff moment
that those same consumers already assume. -/
theorem rootMomentsFiniteUpTo_of_cutoffSecond {r₀ : ℝ}
    (h2 : M.CutoffSecondMomentsFinite r₀) (p : ℕ) :
    M.RootMomentsFiniteUpTo p := by
  intro r _hr ℓ _hℓ
  have hR : M.cutMoment 1 (max r r₀) ≠ ⊤ :=
    M.cutMoment_one_ne_top_of_two (h2 (max r r₀) (le_max_right _ _))
  exact ne_top_of_le_ne_top (cutMoment_ne_top_of_one M (max r r₀) hR (ℓ + 1))
    (M.cutMoment_monotone (ℓ + 1) (le_max_left _ _))

/-- **Eventual finiteness of the cutoff mass gives every cutoff moment at every radius.**

`hfin : ∀ᶠ r in atTop, M.cutMassAt r 0 ≠ ⊤` is the shape the abstract `I.4.20` Case-3 consumers
carry.  Above the threshold `hfin` is `M.cutMassAt r 0 = M.cutMoment 1 r`; below it, monotonicity
of the cutoff moment in the radius reduces to the value at `max r N`.  So the all-order inputs
`hMa` and `hmom` of those consumers are not independent of `hfin`. -/
theorem allCutoffMomentsFinite_of_eventually_cutMass
    (hfin : ∀ᶠ r : ℝ in atTop, M.cutMassAt r 0 ≠ ⊤) :
    M.AllCutoffMomentsFinite := by
  obtain ⟨N, hN⟩ := eventually_atTop.1 hfin
  intro r _hr q _hq
  have hRmass : M.cutMassAt (max r N) 0 ≠ ⊤ := hN (max r N) (le_max_right _ _)
  have hR : M.cutMoment 1 (max r N) ≠ ⊤ := by
    rwa [M.cutMassAt_zero_eq_cutMoment] at hRmass
  exact ne_top_of_le_ne_top (cutMoment_ne_top_of_one M (max r N) hR q)
    (M.cutMoment_monotone q (le_max_left _ _))

/-- **The `hMa` shape from eventual cutoff-mass finiteness.** -/
theorem rootMomentsFiniteUpTo_of_eventually_cutMass
    (hfin : ∀ᶠ r : ℝ in atTop, M.cutMassAt r 0 ≠ ⊤) (p : ℕ) :
    M.RootMomentsFiniteUpTo p := by
  intro r hr ℓ _hℓ
  exact M.allCutoffMomentsFinite_of_eventually_cutMass hfin r
    (lt_of_lt_of_le zero_lt_one hr) (ℓ + 1) (by omega)

end SourceModelData

/-! ## 4. Case-3 consumer replacements with `h1`, `h2`, `hβ` removed -/

namespace SourceModelData

variable (M : SourceModelData)

/-- **Case 3: `𝓔_{2,r} → 0`, with `h1` and `h2` derived from `hP`.** -/
theorem p2ExclError_tendsto_zero_of_source_p21_minimal {r₀ : ℝ}
    (hP : Tendsto (fun r : ℝ => (M.cutMassAt r 0).toReal
      / ((M.α / (M.betaCrit : ℝ)) * r ^ M.α)) atTop (𝓝 1))
    (hTri : TriTail.openTriangleSelf M.kernel M.kernel_nonneg M.betaCrit 0 < ⊤)
    {C₀ p : ℝ} (hC₀ : 0 ≤ C₀) (hp : 1 < p)
    (hF : Analysis.LogRadialBound (fun y : M.V => M.S.dist (0 : M.V) y)
      (fun y : M.V => TriTail.openTriangle M.kernel M.kernel_nonneg M.betaCrit 0 y) C₀ p)
    {c3 : ℝ} (hc3 : 0 < c3)
    (hgm : ∀ᶠ r : ℝ in atTop, c3 * (M.cutMassAt r 0).toReal ^ 3 ≤ (M.cutMoment 2 r).toReal) :
    Tendsto M.p2ExclError atTop (𝓝 0) :=
  M.p2ExclError_tendsto_zero_of_source_p21
    (M.cutoffMomentsFinite_of_firstMoment_asymptotic hP r₀)
    (M.cutoffSecondMomentsFinite_of_firstMoment_asymptotic hP r₀)
    hP hTri hC₀ hp hF hc3 hgm

/-- **Logarithmic integrability of `𝓔_{2,r}`, with `h1` and `h2` derived from `hP`.** -/
theorem logIntegrable_p2ExclError_of_source_p21_minimal {r₀ : ℝ}
    (hmeas : Measurable M.p2ExclError)
    (hP : Tendsto (fun r : ℝ => (M.cutMassAt r 0).toReal
      / ((M.α / (M.betaCrit : ℝ)) * r ^ M.α)) atTop (𝓝 1))
    (hTri : TriTail.openTriangleSelf M.kernel M.kernel_nonneg M.betaCrit 0 < ⊤)
    {C₀ p : ℝ} (hC₀ : 0 ≤ C₀) (hp : 1 < p)
    (hF : Analysis.LogRadialBound (fun y : M.V => M.S.dist (0 : M.V) y)
      (fun y : M.V => TriTail.openTriangle M.kernel M.kernel_nonneg M.betaCrit 0 y) C₀ p)
    {c3 : ℝ} (hc3 : 0 < c3)
    (hgm : ∀ᶠ r : ℝ in atTop, c3 * (M.cutMassAt r 0).toReal ^ 3 ≤ (M.cutMoment 2 r).toReal) :
    Analysis.LogarithmicallyIntegrable M.p2ExclError :=
  M.logIntegrable_p2ExclError_of_source_p21
    (M.cutoffMomentsFinite_of_firstMoment_asymptotic hP r₀)
    (M.cutoffSecondMomentsFinite_of_firstMoment_asymptotic hP r₀)
    hmeas hP hTri hC₀ hp hF hc3 hgm

/-- **Proposition I.4.15, Case 3 (`E_{β_c,r}|K|² ∼ A r^{3α}`), with `h1`, `h2` and `hβ`
removed.**  The retained inputs are the source's own: the radius-picture AC/AE data `hac`,
`hae`, the first-moment asymptotic `hP`, the triangle condition `hTri`, the open-triangle
log-radial bound `hF`, the measurability/logarithmic-integrability obligations
`hmeasE2`, `hmeasEbar`, `hlogH`, `hlogE0`, and the moment gap `hgm` at `c₃ > 0`. -/
theorem secondMoment_asymptotic_case3_of_source_p21_minimal (hα : 0 < M.α) {r₀ : ℝ}
    (hr₀ : 0 < r₀)
    (hac : ∀ R : ℝ, r₀ ≤ R → AbsolutelyContinuousOnInterval
      (fun r : ℝ => (M.cutMoment 2 r).toReal) r₀ R)
    (hae : ∀ᵐ t ∂(volume.restrict (Ici r₀)),
      HasDerivAt (fun r : ℝ => (M.cutMoment 2 r).toReal) (M.rhsScalarTwo t) t)
    (hP : Tendsto (fun r : ℝ => (M.cutMassAt r 0).toReal
      / ((M.α / (M.betaCrit : ℝ)) * r ^ M.α)) atTop (𝓝 1))
    (hTri : TriTail.openTriangleSelf M.kernel M.kernel_nonneg M.betaCrit 0 < ⊤)
    {C₀ p : ℝ} (hC₀ : 0 ≤ C₀) (hp : 1 < p)
    (hF : Analysis.LogRadialBound (fun y : M.V => M.S.dist (0 : M.V) y)
      (fun y : M.V => TriTail.openTriangle M.kernel M.kernel_nonneg M.betaCrit 0 y) C₀ p)
    (hmeasE2 : Measurable M.p2ExclError) (hmeasEbar : Measurable M.p2Ebar)
    (hlogH : Analysis.LogarithmicallyIntegrable M.p2H)
    (hlogE0 : Analysis.LogarithmicallyIntegrable (PivotFlux.cutE0 M))
    {c3 : ℝ} (hc3 : 0 < c3)
    (hgm : ∀ᶠ r : ℝ in atTop, c3 * (M.cutMassAt r 0).toReal ^ 3 ≤ (M.cutMoment 2 r).toReal) :
    ∃ A : ℝ, 0 < A ∧ Tendsto
      (fun r : ℝ => (M.cutMoment 2 r).toReal / r ^ (3 * M.α)) atTop (𝓝 A) :=
  M.secondMoment_asymptotic_case3_of_source_p21 hα hr₀
    (ne_of_gt (M.betaCrit_pos_of_firstMoment_asymptotic hP)) hac hae
    (M.cutoffMomentsFinite_of_firstMoment_asymptotic hP r₀)
    (M.cutoffSecondMomentsFinite_of_firstMoment_asymptotic hP r₀)
    hP hTri hC₀ hp hF hmeasE2 hmeasEbar hlogH hlogE0 hc3 hgm

end SourceModelData
end Orchestration

/-! ## 5. The `I.4.20` Case-3 assembly with `hMa` — and then `h2` — removed

The base theorem `case3_hAend_hAmid_cutPoly_source_of_HD_case3_divergence` retains the second
cutoff moment `h2` *and* the all-order root moment finiteness `hMa`.

* `case3_hAend_hAmid_cutPoly_source_of_HD_case3_divergence_noRootMoments` removes `hMa` with **no
  new hypothesis**: `hMa` follows from `h2` alone
  (`rootMomentsFiniteUpTo_of_cutoffSecond`), by monotone transfer of the second cutoff moment in
  the radius combined with the ordinary atlas bound.  This also removes `hMa` from the sharper
  instances `..._of_subcritical_second` (which replaces `h2` by the subcritical second moment).
* `case3_hAend_hAmid_cutPoly_source_of_HD_case3_divergence_of_subcritical_first` removes `h2` as
  well, using production's `SubcriticalFiniteMean` (the named sharpness input
  `∀ β < β_c, E_β|K_0| ≠ ⊤`) through `cutMoment_ne_top_of_subcritical_first`; this is the weaker
  subcritical **first** moment, not the subcritical second moment used by
  `..._of_subcritical_second`.

On the Case-3 `I.4.15` wrapper path, where the first-moment asymptotic `hP` is an input, `h2`
itself is derivable (`cutoffSecondMomentsFinite_of_firstMoment_asymptotic`), so both `h2` and
`hMa` disappear there without any sharpness input at all. -/

namespace LowerTwoPoint

open PercLib.CriticalLRP.Orchestration

variable (M : SourceModelData)

theorem case3_hAend_hAmid_cutPoly_source_of_HD_case3_divergence_noRootMoments
    (hHD3 : M.d = 6 ∧ M.α = 2 ∧ ∃ C : ℝ, 0 < C ∧ ∀ x y : M.V, x ≠ y →
      M.twoPoint M.betaCrit x y ≤ C * (Real.log (M.S.ρ (toVec (x - y))))⁻¹ *
        (M.S.ρ (toVec (x - y))) ^ (-(M.d : ℝ) + 2))
    (hTri : TriTail.openTriangleSelf M.kernel M.kernel_nonneg M.betaCrit 0 < ⊤)
    (htop : M.uncutMean M.betaCrit = ⊤)
    {F' : ℝ → ℝ} {r₀ : ℝ}
    (hβ : (0 : ℝ) < M.betaCrit) (hr₀ : 0 < r₀)
    (h2 : ∀ t : ℝ, r₀ ≤ t → M.cutMoment 2 t ≠ ⊤)
    (hderiv : ∀ t : ℝ, r₀ ≤ t →
      HasDerivAt (fun r => (M.cutMassAt r 0).toReal) (F' t) t)
    (hflux : ∀ t : ℝ, r₀ ≤ t →
      F' t = (M.betaCrit : ℝ) * |deriv M.K t| * (E1Sign.exclMass M t).toReal)
    (hmeas : Measurable (I420Case3.cutError M))
    (h0 : Tendsto (I420Case3.cutError M) atTop (𝓝 0))
    (𝓔 : ℕ → Finset (Sym2 M.V)) (h𝓔mono : Monotone 𝓔)
    (h𝓔 : ∀ e : Sym2 M.V, ∃ n, e ∈ 𝓔 n) (p : ℕ) (hp : 3 ≤ p)
    {θ : ℝ} (hθ0 : 0 < θ) (hθ1 : θ < 1)
    {c3 : ℝ} (hc3 : 0 < c3)
    (hgm : ∀ᶠ r in atTop, c3 * I420Case3.momOf (fun r => M.cutProb r) (0 : M.V) 1 r ^ 3
      ≤ I420Case3.momOf (fun r => M.cutProb r) (0 : M.V) 2 r) :
    Tendsto (fun r => I420Case1.mixedExclR (M.cutProb r) (0 : M.V) 1 p
          (BallAverage.ball_finite M r).toFinset /
        (I420Case3.ballCard (fun r => (BallAverage.ball_finite M r).toFinset) r *
          (I420Case3.momOf (fun r => M.cutProb r) (0 : M.V) 1 r *
            I420Case3.momOf (fun r => M.cutProb r) (0 : M.V) p r))) atTop (𝓝 1) ∧
      ∀ ℓ, 1 ≤ ℓ → ℓ ≤ p - 2 → Tendsto
        (fun r => I420Case1.mixedExclR (M.cutProb r) (0 : M.V) (ℓ + 1) (p - ℓ)
            (BallAverage.ball_finite M r).toFinset /
          (I420Case3.ballCard (fun r => (BallAverage.ball_finite M r).toFinset) r *
            (I420Case3.momOf (fun r => M.cutProb r) (0 : M.V) (ℓ + 1) r *
              I420Case3.momOf (fun r => M.cutProb r) (0 : M.V) (p - ℓ) r))) atTop (𝓝 1) := by
  have hMa : ∀ (r : ℝ), 1 ≤ r → ∀ ℓ : ℕ, ℓ ≤ p →
      I420Case1.powMomentAt (M.cutProb r) (ℓ + 1) (0 : M.V) ≠ ⊤ := by
    intro r hr ℓ hℓ
    rw [M.powMomentAt_cutProb_eq_cutMoment]
    exact M.rootMomentsFiniteUpTo_of_cutoffSecond h2 p r hr ℓ hℓ
  exact case3_hAend_hAmid_cutPoly_source_of_HD_case3_divergence M hHD3 hTri htop hβ hr₀ h2
    hderiv hflux hmeas h0 𝓔 h𝓔mono h𝓔 p hp hθ0 hθ1 hMa hc3 hgm

theorem case3_hAend_hAmid_cutPoly_source_of_HD_case3_divergence_of_subcritical_first
    (hHD3 : M.d = 6 ∧ M.α = 2 ∧ ∃ C : ℝ, 0 < C ∧ ∀ x y : M.V, x ≠ y →
      M.twoPoint M.betaCrit x y ≤ C * (Real.log (M.S.ρ (toVec (x - y))))⁻¹ *
        (M.S.ρ (toVec (x - y))) ^ (-(M.d : ℝ) + 2))
    (hTri : TriTail.openTriangleSelf M.kernel M.kernel_nonneg M.betaCrit 0 < ⊤)
    (htop : M.uncutMean M.betaCrit = ⊤)
    {F' : ℝ → ℝ} {r₀ : ℝ}
    (hβ : (0 : ℝ) < M.betaCrit) (hsub : M.SubcriticalFiniteMean) (hr₀ : 0 < r₀)
    (hderiv : ∀ t : ℝ, r₀ ≤ t →
      HasDerivAt (fun r => (M.cutMassAt r 0).toReal) (F' t) t)
    (hflux : ∀ t : ℝ, r₀ ≤ t →
      F' t = (M.betaCrit : ℝ) * |deriv M.K t| * (E1Sign.exclMass M t).toReal)
    (hmeas : Measurable (I420Case3.cutError M))
    (h0 : Tendsto (I420Case3.cutError M) atTop (𝓝 0))
    (𝓔 : ℕ → Finset (Sym2 M.V)) (h𝓔mono : Monotone 𝓔)
    (h𝓔 : ∀ e : Sym2 M.V, ∃ n, e ∈ 𝓔 n) (p : ℕ) (hp : 3 ≤ p)
    {θ : ℝ} (hθ0 : 0 < θ) (hθ1 : θ < 1)
    {c3 : ℝ} (hc3 : 0 < c3)
    (hgm : ∀ᶠ r in atTop, c3 * I420Case3.momOf (fun r => M.cutProb r) (0 : M.V) 1 r ^ 3
      ≤ I420Case3.momOf (fun r => M.cutProb r) (0 : M.V) 2 r) :
    Tendsto (fun r => I420Case1.mixedExclR (M.cutProb r) (0 : M.V) 1 p
          (BallAverage.ball_finite M r).toFinset /
        (I420Case3.ballCard (fun r => (BallAverage.ball_finite M r).toFinset) r *
          (I420Case3.momOf (fun r => M.cutProb r) (0 : M.V) 1 r *
            I420Case3.momOf (fun r => M.cutProb r) (0 : M.V) p r))) atTop (𝓝 1) ∧
      ∀ ℓ, 1 ≤ ℓ → ℓ ≤ p - 2 → Tendsto
        (fun r => I420Case1.mixedExclR (M.cutProb r) (0 : M.V) (ℓ + 1) (p - ℓ)
            (BallAverage.ball_finite M r).toFinset /
          (I420Case3.ballCard (fun r => (BallAverage.ball_finite M r).toFinset) r *
            (I420Case3.momOf (fun r => M.cutProb r) (0 : M.V) (ℓ + 1) r *
              I420Case3.momOf (fun r => M.cutProb r) (0 : M.V) (p - ℓ) r))) atTop (𝓝 1) := by
  have hβ0 : (0 : ℝ≥0) < M.betaCrit := by exact_mod_cast hβ
  refine case3_hAend_hAmid_cutPoly_source_of_HD_case3_divergence_noRootMoments M hHD3 hTri htop
    hβ hr₀ (fun t ht => ?_) hderiv hflux hmeas h0 𝓔 h𝓔mono h𝓔 p hp hθ0 hθ1 hc3 hgm
  exact cutMoment_ne_top_of_subcritical_first M hβ0 hsub (lt_of_lt_of_le hr₀ ht) 2

theorem case3_hAend_hAmid_cutPoly_source_of_HD_case3_of_critical_divergence_noRootMoments
    (M : SourceModelData)
    (hHD3 : M.d = 6 ∧ M.α = 2 ∧ ∃ C : ℝ, 0 < C ∧ ∀ x y : M.V, x ≠ y →
      M.twoPoint M.betaCrit x y ≤ C * (Real.log (M.S.ρ (toVec (x - y))))⁻¹ *
        (M.S.ρ (toVec (x - y))) ^ (-(M.d : ℝ) + 2))
    (hTri : TriTail.openTriangleSelf M.kernel M.kernel_nonneg M.betaCrit 0 < ⊤)
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
    {c3 : ℝ} (hc3 : 0 < c3)
    (hgm : ∀ᶠ r in atTop, c3 * I420Case3.momOf (fun r => M.cutProb r) (0 : M.V) 1 r ^ 3
      ≤ I420Case3.momOf (fun r => M.cutProb r) (0 : M.V) 2 r) :
    Tendsto (fun r => I420Case1.mixedExclR (M.cutProb r) (0 : M.V) 1 p
          (BallAverage.ball_finite M r).toFinset /
        (I420Case3.ballCard (fun r => (BallAverage.ball_finite M r).toFinset) r *
          (I420Case3.momOf (fun r => M.cutProb r) (0 : M.V) 1 r *
            I420Case3.momOf (fun r => M.cutProb r) (0 : M.V) p r))) atTop (𝓝 1) ∧
      ∀ ℓ, 1 ≤ ℓ → ℓ ≤ p - 2 → Tendsto
        (fun r => I420Case1.mixedExclR (M.cutProb r) (0 : M.V) (ℓ + 1) (p - ℓ)
            (BallAverage.ball_finite M r).toFinset /
          (I420Case3.ballCard (fun r => (BallAverage.ball_finite M r).toFinset) r *
            (I420Case3.momOf (fun r => M.cutProb r) (0 : M.V) (ℓ + 1) r *
              I420Case3.momOf (fun r => M.cutProb r) (0 : M.V) (p - ℓ) r))) atTop (𝓝 1) := by
  have hMa : ∀ (r : ℝ), 1 ≤ r → ∀ ℓ : ℕ, ℓ ≤ p →
      I420Case1.powMomentAt (M.cutProb r) (ℓ + 1) (0 : M.V) ≠ ⊤ := by
    intro r hr ℓ hℓ
    rw [M.powMomentAt_cutProb_eq_cutMoment]
    exact M.rootMomentsFiniteUpTo_of_eventually_cutMass hfin p r hr ℓ hℓ
  exact I420Case3.case3_hAend_hAmid_cutPoly_source_of_finite M
    (first_moment_asymptotic_of_critical_divergence M htop hfin hβ hr₀ hderiv hpos hode
      hmeas hhedge h0)
    hTri 𝓔 h𝓔mono h𝓔 p hp hθ0 hθ1
    (M.isLogErrorFunction_nablaTail_of_HD_case2_or_case3 (Or.inr hHD3)).2 hMa hc3 hgm

theorem case3_i421_cutPoly_source_of_HD_case3_of_critical_divergence_noRootMoments
    (M : SourceModelData)
    (hHD3 : M.d = 6 ∧ M.α = 2 ∧ ∃ C : ℝ, 0 < C ∧ ∀ x y : M.V, x ≠ y →
      M.twoPoint M.betaCrit x y ≤ C * (Real.log (M.S.ρ (toVec (x - y))))⁻¹ *
        (M.S.ρ (toVec (x - y))) ^ (-(M.d : ℝ) + 2))
    (hTri : TriTail.openTriangleSelf M.kernel M.kernel_nonneg M.betaCrit 0 < ⊤)
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
    {c3 : ℝ} (hc3 : 0 < c3)
    (hgm : ∀ᶠ r in atTop, c3 * I420Case3.momOf (fun r => M.cutProb r) (0 : M.V) 1 r ^ 3
      ≤ I420Case3.momOf (fun r => M.cutProb r) (0 : M.V) 2 r) :
    ∃ c₁ C₁ : ℝ, 0 < c₁ ∧ 0 < C₁ ∧
      Tendsto (fun r => I420Case3.discR (M.cutProb r) (0 : M.V) (ℓ + 1) (p - ℓ)
          (BallAverage.ball_finite M r).toFinset /
        I420Case3.biasTarget (I420Case3.momOf (fun r => M.cutProb r) (0 : M.V) 1 r)
          (I420Case3.momOf (fun r => M.cutProb r) (0 : M.V) 2 r) p) atTop (𝓝 0) := by
  have hmom : ∀ r : ℝ, 1 ≤ r → ∀ m : ℕ, 1 ≤ m → m ≤ p + 1 →
      I420Case1.powMomentAt (M.cutProb r) m (0 : M.V) ≠ ⊤ := by
    intro r hr m hm1 _
    rw [M.powMomentAt_cutProb_eq_cutMoment]
    exact M.allCutoffMomentsFinite_of_eventually_cutMass hfin r
      (lt_of_lt_of_le zero_lt_one hr) m hm1
  have hMa : ∀ r : ℝ, 1 ≤ r →
      I420Case1.powMomentAt (M.cutProb r) (ℓ + 1) (0 : M.V) ≠ ⊤ :=
    fun r hr => hmom r hr (ℓ + 1) (by omega) (by omega)
  have hMb : ∀ (r : ℝ), 1 ≤ r → ∀ y ∈ (BallAverage.ball_finite M r).toFinset,
      I420Case1.powMomentAt (M.cutProb r) (p - ℓ) y ≠ ⊤ := by
    intro r hr y _
    rw [I420Case3.powMomentAt_cutProb_apply_eq_zero M r (p - ℓ) y]
    have hidx : p - ℓ - 1 + 1 = p - ℓ := by omega
    rw [← hidx]
    exact hmom r hr (p - ℓ - 1 + 1) (by omega) (by omega)
  exact I420Case3.exists_case3_i421_cutPoly_source M
    (first_moment_asymptotic_of_critical_divergence M htop hfin hβ hr₀ hderiv hpos hode
      hmeas hhedge h0)
    hTri 𝓔 h𝓔mono h𝓔 p ℓ hp hℓ hθ0 hθ1
    (M.isLogErrorFunction_nablaTail_of_HD_case2_or_case3 (Or.inr hHD3)).2
    hMa hMb hc3 hgm

/-! ## 6. The interface from the `I.4.15`-Case-3 first-moment input to the `I.4.20`-Case-3 output

Assuming the paper's first-moment asymptotic `hP` (Prop. I.4.2) instead of deriving it from
`E_{β_c}|K₀| = ⊤` plus the `(I.4.6)` ODE, the landed
`I420Case3.case3_hAend_hAmid_cutPoly_source_of_finite` needs only `hTri`, the `(I.4.19)` net data
`𝓔, p, θ`, the logarithmic vanishing of the triangle tail `∇` (from (HD) Case 3), and `hgm`.  Its
last finiteness input `hMa` is supplied by `hP`, so the whole decorrelation output of `I.4.20` Case 3
follows from `hP` plus that structural data:

`{hP, hTri, hgm} ∪ {(HD)-Case-3 data (for the ∇-tail), (I.4.19) net and order data}`.

No `htop`, no `hfin`, no `h2`, no `hMa`, no `hderiv`/`hflux`/`hpos`/`hode`, no `hmeas`, no lower
two-point bound `hlow`, and no radius AC/AE data are needed on this interface.  This is a
*strengthening of the hypotheses* of the landed consumer (which derives `hP` internally), and it is
stated as such: it locates the exact frontier between Proposition I.4.15 Case 3 and the `I.4.20`
Case-3 assembly, it is not an unconditional statement about the model. -/

theorem case3_hAend_hAmid_cutPoly_source_of_firstMoment_asymptotic
    (M : SourceModelData)
    (hHD3 : M.d = 6 ∧ M.α = 2 ∧ ∃ C : ℝ, 0 < C ∧ ∀ x y : M.V, x ≠ y →
      M.twoPoint M.betaCrit x y ≤ C * (Real.log (M.S.ρ (toVec (x - y))))⁻¹ *
        (M.S.ρ (toVec (x - y))) ^ (-(M.d : ℝ) + 2))
    (hTri : TriTail.openTriangleSelf M.kernel M.kernel_nonneg M.betaCrit 0 < ⊤)
    (hP : Tendsto (fun r : ℝ => (M.cutMassAt r 0).toReal
      / ((M.α / (M.betaCrit : ℝ)) * r ^ M.α)) atTop (𝓝 1))
    (𝓔 : ℕ → Finset (Sym2 M.V)) (h𝓔mono : Monotone 𝓔)
    (h𝓔 : ∀ e : Sym2 M.V, ∃ n, e ∈ 𝓔 n) (p : ℕ) (hp : 3 ≤ p)
    {θ : ℝ} (hθ0 : 0 < θ) (hθ1 : θ < 1)
    {c3 : ℝ} (hc3 : 0 < c3)
    (hgm : ∀ᶠ r in atTop, c3 * I420Case3.momOf (fun r => M.cutProb r) (0 : M.V) 1 r ^ 3
      ≤ I420Case3.momOf (fun r => M.cutProb r) (0 : M.V) 2 r) :
    Tendsto (fun r => I420Case1.mixedExclR (M.cutProb r) (0 : M.V) 1 p
          (BallAverage.ball_finite M r).toFinset /
        (I420Case3.ballCard (fun r => (BallAverage.ball_finite M r).toFinset) r *
          (I420Case3.momOf (fun r => M.cutProb r) (0 : M.V) 1 r *
            I420Case3.momOf (fun r => M.cutProb r) (0 : M.V) p r))) atTop (𝓝 1) ∧
      ∀ ℓ, 1 ≤ ℓ → ℓ ≤ p - 2 → Tendsto
        (fun r => I420Case1.mixedExclR (M.cutProb r) (0 : M.V) (ℓ + 1) (p - ℓ)
            (BallAverage.ball_finite M r).toFinset /
          (I420Case3.ballCard (fun r => (BallAverage.ball_finite M r).toFinset) r *
            (I420Case3.momOf (fun r => M.cutProb r) (0 : M.V) (ℓ + 1) r *
              I420Case3.momOf (fun r => M.cutProb r) (0 : M.V) (p - ℓ) r))) atTop (𝓝 1) := by
  have hMa : ∀ (r : ℝ), 1 ≤ r → ∀ ℓ : ℕ, ℓ ≤ p →
      I420Case1.powMomentAt (M.cutProb r) (ℓ + 1) (0 : M.V) ≠ ⊤ := by
    intro r hr ℓ hℓ
    rw [M.powMomentAt_cutProb_eq_cutMoment]
    exact M.rootMomentsFiniteUpTo_of_firstMoment_asymptotic hP p r hr ℓ hℓ
  exact I420Case3.case3_hAend_hAmid_cutPoly_source_of_finite M hP hTri 𝓔 h𝓔mono h𝓔 p hp
    hθ0 hθ1 (M.isLogErrorFunction_nablaTail_of_HD_case2_or_case3 (Or.inr hHD3)).2 hMa hc3 hgm

end LowerTwoPoint

end PercLib.CriticalLRP

/-! ## Axiom audit -/

#print axioms
  PercLib.CriticalLRP.Orchestration.SourceModelData.betaCrit_pos_of_firstMoment_asymptotic
#print axioms
  PercLib.CriticalLRP.Orchestration.SourceModelData.exists_chi_lower_uniform_and_finite_of_firstMoment_asymptotic
#print axioms
  PercLib.CriticalLRP.Orchestration.SourceModelData.allCutoffMomentsFinite_of_firstMoment_asymptotic
#print axioms
  PercLib.CriticalLRP.Orchestration.SourceModelData.cutoffMomentsFinite_of_firstMoment_asymptotic
#print axioms
  PercLib.CriticalLRP.Orchestration.SourceModelData.cutoffSecondMomentsFinite_of_firstMoment_asymptotic
#print axioms
  PercLib.CriticalLRP.Orchestration.SourceModelData.uncutMean_eq_top_of_firstMoment_asymptotic
#print axioms
  PercLib.CriticalLRP.Orchestration.SourceModelData.cutoffMomentsFinite_iff_cutoffSecondMomentsFinite
#print axioms
  PercLib.CriticalLRP.Orchestration.SourceModelData.cutoffMomentsFinite_iff_forall_pos
#print axioms
  PercLib.CriticalLRP.Orchestration.SourceModelData.rootMomentsFiniteUpTo_of_first
#print axioms
  PercLib.CriticalLRP.Orchestration.SourceModelData.rootMomentsFiniteUpTo_of_firstMoment_asymptotic
#print axioms
  PercLib.CriticalLRP.Orchestration.SourceModelData.rootMomentsFiniteUpTo_of_cutoffSecond
#print axioms
  PercLib.CriticalLRP.Orchestration.SourceModelData.allCutoffMomentsFinite_of_eventually_cutMass
#print axioms
  PercLib.CriticalLRP.Orchestration.SourceModelData.rootMomentsFiniteUpTo_of_eventually_cutMass
#print axioms
  PercLib.CriticalLRP.Orchestration.SourceModelData.p2ExclError_tendsto_zero_of_source_p21_minimal
#print axioms
  PercLib.CriticalLRP.Orchestration.SourceModelData.logIntegrable_p2ExclError_of_source_p21_minimal
#print axioms
  PercLib.CriticalLRP.Orchestration.SourceModelData.secondMoment_asymptotic_case3_of_source_p21_minimal
#print axioms
  PercLib.CriticalLRP.LowerTwoPoint.case3_hAend_hAmid_cutPoly_source_of_HD_case3_divergence_noRootMoments
#print axioms
  PercLib.CriticalLRP.LowerTwoPoint.case3_hAend_hAmid_cutPoly_source_of_HD_case3_divergence_of_subcritical_first
#print axioms
  PercLib.CriticalLRP.LowerTwoPoint.case3_hAend_hAmid_cutPoly_source_of_HD_case3_of_critical_divergence_noRootMoments
#print axioms
  PercLib.CriticalLRP.LowerTwoPoint.case3_i421_cutPoly_source_of_HD_case3_of_critical_divergence_noRootMoments
#print axioms
  PercLib.CriticalLRP.LowerTwoPoint.case3_hAend_hAmid_cutPoly_source_of_firstMoment_asymptotic
