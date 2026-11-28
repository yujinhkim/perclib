/-
Copyright (c) 2026 PercLib contributors. Released under Apache 2.0.

Accepted and independently rebuilt from Ultramath `smwzqts7r`, member m4.
Latest independent rebuild at production HEAD `e2b5cf635f5a2ffb1c7f203271de1c0a7ef3ad2b`;
reviewed scratch source `.scratch/review-smwzqts7r/m4/CaseTwoRV.lean`.
-/

/-
# Proposition I.4.15, Case 2: the assembled regular-variation conclusion

Hutchcroft, *Critical long-range percolation I*, arXiv:2508.18807v1,
Proposition I.4.15 and its proof, Cases 1--2 (displays (I.4.14)--(I.4.18)).

Production state at HEAD `e2b5cf635f5a`:
* `CaseTwo.p2ExclError_tendsto_zero_of_caseTwo'` proves `E_{2,r} → 0` from
  `hP`, `Hydro`, eventual finiteness of the second moment and Lemma I.4.16 at
  `p = 6, k = 2` (`CaseTwo.SixthMomentMixed`), but
* `SourceModelData.regularlyVarying_two_of_hP_of_ae_deriv` consumes `E_{2,r} → 0`
  and nothing in production connects the two.

This file supplies the missing link, and the reductions around it:
hP/Hydro/SixthMomentMixed ⟹ `E_{2,r} → 0` ⟹ regular variation of index `3α`.

Everything is over the model's own cutoff law; no new hypothesis is introduced.
-/
module

public import PercLib.CriticalLRP.Analysis.SecondMomentCase2.Source.Defs
public import PercLib.CriticalLRP.Analysis.SecondMomentMeasurability.Consumers
public import PercLib.CriticalLRP.Analysis.SecondMomentTail

set_option autoImplicit false
set_option linter.hashCommand false
set_option linter.style.longLine false

@[expose] public section

noncomputable section

open MeasureTheory Filter Topology Set
open scoped ENNReal NNReal Topology

namespace PercLib.CriticalLRP.Orchestration

namespace SourceModelData

variable (M : SourceModelData)

/-! ## 1. Case 2 with a separate eventual second-moment finiteness input -/

/-- **Case 2 of Proposition I.4.15, assembled.**  From
`hP`, `Hydro`, eventual finiteness of `E|K|²` and Lemma I.4.16 at `p = 6, k = 2`
(the single named missing combinatorial input `CaseTwo.SixthMomentMixed`),
together with the corner-safe radial regularity `hac`/`hae` of the second cutoff
moment, `r ↦ E_{βc,r}|K|²` is regularly varying of index `3α`.

The chain is `p2ExclError_tendsto_zero_of_caseTwo'` (the landed Case-2 error
estimate) fed into `regularlyVarying_two_of_hP_of_ae_deriv_no_hmR` (the landed
analytic ODE/regular-variation step).  Nothing else enters. -/
theorem regularlyVarying_two_of_caseTwo
    (hα : 0 < M.α) {r₀ : ℝ} (hr₀ : 0 < r₀)
    (hκ : 0 < M.α / (M.betaCrit : ℝ))
    (hd : (M.d : ℝ) = 3 * M.α)
    (hac : ∀ R : ℝ, r₀ ≤ R → AbsolutelyContinuousOnInterval
      (fun r : ℝ => (M.cutMoment 2 r).toReal) r₀ R)
    (hae : ∀ᵐ t ∂(volume.restrict (Ici r₀)),
      HasDerivAt (fun r : ℝ => (M.cutMoment 2 r).toReal) (M.rhsScalarTwo t) t)
    (h1 : ∀ t : ℝ, r₀ ≤ t → M.cutMoment 1 t ≠ ⊤)
    (h2 : ∀ t : ℝ, r₀ ≤ t → M.cutMoment 2 t ≠ ⊤)
    (hP : Tendsto (fun r : ℝ => (M.cutMassAt r 0).toReal
      / ((M.α / (M.betaCrit : ℝ)) * r ^ M.α)) atTop (𝓝 1))
    (hH : Hydro M)
    (h6 : ∀ᶠ r : ℝ in atTop,
      M.cutMoment 6 r ≤ (945 : ℝ≥0∞) * (M.cutMoment 2 r) ^ 2 * (M.cutMoment 1 r) ^ 5) :
    Analysis.RegularlyVaryingAtTop (fun r : ℝ => (M.cutMoment 2 r).toReal) (3 * M.α) := by
  have hβ : (M.betaCrit : ℝ) ≠ 0 := by
    intro h0
    rw [h0, div_zero] at hκ
    exact lt_irrefl 0 hκ
  have hE2 : Tendsto M.p2ExclError atTop (𝓝 0) :=
    CaseTwo.p2ExclError_tendsto_zero_of_caseTwo' M hd hκ hP hH
      ((eventually_ge_atTop r₀).mono fun r hr => h2 r hr) h6
  exact M.regularlyVarying_two_of_hP_of_ae_deriv_no_hmR hα hr₀ hβ hac hae h1 h2 hP hE2

/-! ## 2. The no-separate-`h2` version

`hP` is the normalized first-moment asymptotic, so it already forces finiteness
of *every* cutoff moment at every radius: `cutMoment_one_ne_top_of_asymptotic`
gives `E|K| < ∞` everywhere and `cutMoment_ne_top_of_one` transfers it upward.
So neither the first- nor the second-moment finiteness has to be assumed
separately. -/

/-- **Case 2 assembled with both finiteness inputs discharged by `hP`.** -/
theorem regularlyVarying_two_of_caseTwo_of_hP
    (hα : 0 < M.α) {r₀ : ℝ} (hr₀ : 0 < r₀)
    (hκ : 0 < M.α / (M.betaCrit : ℝ))
    (hd : (M.d : ℝ) = 3 * M.α)
    (hac : ∀ R : ℝ, r₀ ≤ R → AbsolutelyContinuousOnInterval
      (fun r : ℝ => (M.cutMoment 2 r).toReal) r₀ R)
    (hae : ∀ᵐ t ∂(volume.restrict (Ici r₀)),
      HasDerivAt (fun r : ℝ => (M.cutMoment 2 r).toReal) (M.rhsScalarTwo t) t)
    (hP : Tendsto (fun r : ℝ => (M.cutMassAt r 0).toReal
      / ((M.α / (M.betaCrit : ℝ)) * r ^ M.α)) atTop (𝓝 1))
    (hH : Hydro M)
    (h6 : ∀ᶠ r : ℝ in atTop,
      M.cutMoment 6 r ≤ (945 : ℝ≥0∞) * (M.cutMoment 2 r) ^ 2 * (M.cutMoment 1 r) ^ 5) :
    Analysis.RegularlyVaryingAtTop (fun r : ℝ => (M.cutMoment 2 r).toReal) (3 * M.α) := by
  have h1 : ∀ t : ℝ, M.cutMoment 1 t ≠ ⊤ :=
    M.cutMoment_one_ne_top_of_asymptotic (c := M.α / (M.betaCrit : ℝ)) hP
  have h2 : ∀ t : ℝ, M.cutMoment 2 t ≠ ⊤ := fun t =>
    cutMoment_ne_top_of_one M t (h1 t) 2
  exact M.regularlyVarying_two_of_caseTwo hα hr₀ hκ hd hac hae
    (fun t _ => h1 t) (fun t _ => h2 t) hP hH h6

/-! ## 3. The `momOf` spelling used by the higher-moment packet -/

/-- **Case 2 in the higher-moment packet's `momOf` vocabulary.**  `momOf` is
definitionally `(M.cutMoment m ·).toReal`, so this is the same statement. -/
theorem momOf_two_regularlyVarying_of_caseTwo_of_hP
    (hα : 0 < M.α) {r₀ : ℝ} (hr₀ : 0 < r₀)
    (hκ : 0 < M.α / (M.betaCrit : ℝ))
    (hd : (M.d : ℝ) = 3 * M.α)
    (hac : ∀ R : ℝ, r₀ ≤ R → AbsolutelyContinuousOnInterval
      (fun r : ℝ => (M.cutMoment 2 r).toReal) r₀ R)
    (hae : ∀ᵐ t ∂(volume.restrict (Ici r₀)),
      HasDerivAt (fun r : ℝ => (M.cutMoment 2 r).toReal) (M.rhsScalarTwo t) t)
    (hP : Tendsto (fun r : ℝ => (M.cutMassAt r 0).toReal
      / ((M.α / (M.betaCrit : ℝ)) * r ^ M.α)) atTop (𝓝 1))
    (hH : Hydro M)
    (h6 : ∀ᶠ r : ℝ in atTop,
      M.cutMoment 6 r ≤ (945 : ℝ≥0∞) * (M.cutMoment 2 r) ^ 2 * (M.cutMoment 1 r) ^ 5) :
    Analysis.RegularlyVaryingAtTop
      (fun r : ℝ => I420Case3.momOf (fun r => M.cutProb r) (0 : M.V) 2 r) (3 * M.α) :=
  M.regularlyVarying_two_of_caseTwo_of_hP hα hr₀ hκ hd hac hae hP hH h6


/-- **Case 2 from the exact named source input.**  This is
`regularlyVarying_two_of_caseTwo_of_hP` with the eventual form of Lemma I.4.16
at `p = 6, k = 2` specialised to its source shape `CaseTwo.SixthMomentMixed`
(which quantifies over every nonnegative radius). -/
theorem regularlyVarying_two_of_caseTwo_of_sixthMomentMixed
    (hα : 0 < M.α) {r₀ : ℝ} (hr₀ : 0 < r₀)
    (hκ : 0 < M.α / (M.betaCrit : ℝ))
    (hd : (M.d : ℝ) = 3 * M.α)
    (hac : ∀ R : ℝ, r₀ ≤ R → AbsolutelyContinuousOnInterval
      (fun r : ℝ => (M.cutMoment 2 r).toReal) r₀ R)
    (hae : ∀ᵐ t ∂(volume.restrict (Ici r₀)),
      HasDerivAt (fun r : ℝ => (M.cutMoment 2 r).toReal) (M.rhsScalarTwo t) t)
    (hP : Tendsto (fun r : ℝ => (M.cutMassAt r 0).toReal
      / ((M.α / (M.betaCrit : ℝ)) * r ^ M.α)) atTop (𝓝 1))
    (hH : Hydro M)
    (h6 : CaseTwo.SixthMomentMixed M) :
    Analysis.RegularlyVaryingAtTop (fun r : ℝ => (M.cutMoment 2 r).toReal) (3 * M.α) :=
  M.regularlyVarying_two_of_caseTwo_of_hP hα hr₀ hκ hd hac hae hP hH
    ((eventually_ge_atTop (0 : ℝ)).mono fun r hr => h6 r hr)

/-- **The higher-moment side-premise packet with its second-moment input
*derived*.**  `SourceModelData.momOf_packet` takes
`RegularlyVaryingAtTop (momOf · 2) (3α)` as its single independent input — the
packet's `h2`, described there as matching Proposition I.4.15 / gap WS002.
Case 2 of I.4.15 supplies exactly that input, so the whole packet follows from
`hP`, `Hydro`, `d = 3α`, Lemma I.4.16 at `p = 6, k = 2` and the radial
regularity `hac`/`hae`. -/
theorem momOf_packet_of_caseTwo_of_hP
    (hα : 0 < M.α) {r₀ : ℝ} (hr₀ : 0 < r₀)
    (hκ : 0 < M.α / (M.betaCrit : ℝ))
    (hd : (M.d : ℝ) = 3 * M.α)
    (hac : ∀ R : ℝ, r₀ ≤ R → AbsolutelyContinuousOnInterval
      (fun r : ℝ => (M.cutMoment 2 r).toReal) r₀ R)
    (hae : ∀ᵐ t ∂(volume.restrict (Ici r₀)),
      HasDerivAt (fun r : ℝ => (M.cutMoment 2 r).toReal) (M.rhsScalarTwo t) t)
    (hP : Tendsto (fun r : ℝ => (M.cutMassAt r 0).toReal
      / ((M.α / (M.betaCrit : ℝ)) * r ^ M.α)) atTop (𝓝 1))
    (hH : Hydro M)
    (h6 : ∀ᶠ r : ℝ in atTop,
      M.cutMoment 6 r ≤ (945 : ℝ≥0∞) * (M.cutMoment 2 r) ^ 2 * (M.cutMoment 1 r) ^ 5) :
    (∀ m : ℕ, ∀ r : ℝ, 0 < r →
        0 < I420Case3.momOf (fun r => M.cutProb r) (0 : M.V) m r) ∧
      Measurable (fun r : ℝ => I420Case3.momOf (fun r => M.cutProb r) (0 : M.V) 1 r) ∧
      Measurable (fun r : ℝ => I420Case3.momOf (fun r => M.cutProb r) (0 : M.V) 2 r) ∧
      Analysis.RegularlyVaryingAtTop
        (fun r : ℝ => I420Case3.momOf (fun r => M.cutProb r) (0 : M.V) 1 r) M.α ∧
      Analysis.RegularlyVaryingAtTop
        (fun r : ℝ => I420Case3.momOf (fun r => M.cutProb r) (0 : M.V) 2 r) (3 * M.α) := by
  have hβ : (M.betaCrit : ℝ) ≠ 0 := by
    intro h0
    rw [h0, div_zero] at hκ
    exact lt_irrefl 0 hκ
  exact M.momOf_packet hα hβ hP
    (M.momOf_two_regularlyVarying_of_caseTwo_of_hP hα hr₀ hκ hd hac hae hP hH h6)

/-- **The Case-2 analogue of the two-sided cube comparison.**  At `d = 3α` the
second cutoff moment is comparable to the cube of the first only up to a
*slowly varying* factor: `momOf 2 / (momOf 1)³` is regularly varying of index
`0`, i.e. slowly varying.  (Case 1 upgrades this to bounded two-sided constants;
at `d = 3α` the paper's Theorem III.1.2 shows the slowly varying factor is a
genuine logarithmic correction, so no bounded comparison is expected in
general.) -/
theorem slowlyVarying_momOf_two_div_cube
    (hα : 0 < M.α) {r₀ : ℝ} (hr₀ : 0 < r₀)
    (hκ : 0 < M.α / (M.betaCrit : ℝ))
    (hd : (M.d : ℝ) = 3 * M.α)
    (hac : ∀ R : ℝ, r₀ ≤ R → AbsolutelyContinuousOnInterval
      (fun r : ℝ => (M.cutMoment 2 r).toReal) r₀ R)
    (hae : ∀ᵐ t ∂(volume.restrict (Ici r₀)),
      HasDerivAt (fun r : ℝ => (M.cutMoment 2 r).toReal) (M.rhsScalarTwo t) t)
    (hP : Tendsto (fun r : ℝ => (M.cutMassAt r 0).toReal
      / ((M.α / (M.betaCrit : ℝ)) * r ^ M.α)) atTop (𝓝 1))
    (hH : Hydro M)
    (h6 : ∀ᶠ r : ℝ in atTop,
      M.cutMoment 6 r ≤ (945 : ℝ≥0∞) * (M.cutMoment 2 r) ^ 2 * (M.cutMoment 1 r) ^ 5) :
    Analysis.SlowlyVaryingAtTop
      (fun r : ℝ => I420Case3.momOf (fun r => M.cutProb r) (0 : M.V) 2 r
        / (I420Case3.momOf (fun r => M.cutProb r) (0 : M.V) 1 r) ^ 3) := by
  have hβ : (M.betaCrit : ℝ) ≠ 0 := by
    intro h0
    rw [h0, div_zero] at hκ
    exact lt_irrefl 0 hκ
  have h2 := M.momOf_two_regularlyVarying_of_caseTwo_of_hP hα hr₀ hκ hd hac hae hP hH h6
  have h1 := M.momOf_one_regularlyVarying hα hβ hP
  have hcube := Analysis.regularlyVaryingAtTop_pow_three (g := fun r : ℝ =>
    I420Case3.momOf (fun r => M.cutProb r) (0 : M.V) 1 r) h1
  have hmul := h2.mul hcube.inv
  have hzero : 3 * M.α + -(3 * M.α) = 0 := by ring
  rw [hzero] at hmul
  refine Analysis.RegularlyVaryingAtTop.congr' ?_ hmul
  filter_upwards with x
  rw [div_eq_mul_inv]

/-! ## 4. Case 2 from the integrated radius identity only

The pointwise a.e. identity `hae` and absolute continuity `hac` are not extra
model inputs: both follow from the *integrated* form of (I.4.14)/(I.4.15) on
every radius window, which is the shape a monotone-convergence exchange of the
finite-window Russo identity produces.  This section records that reduction, so
that the Case-2 chain has a single radial input rather than three. -/

/-- **Case 2 assembled from the integrated radius identity.**  If on every
window `[r₀,R]` the second cutoff moment is the primitive of `M.rhsScalarTwo`,
then `hP`, `Hydro`, `d = 3α` and Lemma I.4.16 at `p = 6, k = 2` give regular
variation of index `3α` — with `hac` and `hae` derived, not assumed. -/
theorem regularlyVarying_two_of_caseTwo_of_integrated_identity
    (hα : 0 < M.α) {r₀ : ℝ} (hr₀ : 0 < r₀)
    (hκ : 0 < M.α / (M.betaCrit : ℝ))
    (hd : (M.d : ℝ) = 3 * M.α)
    (hint : ∀ R : ℝ, r₀ ≤ R →
      IntervalIntegrable (fun t : ℝ => M.rhsScalarTwo t) volume r₀ R)
    (hid : ∀ R : ℝ, r₀ ≤ R → ∀ x ∈ Set.Icc r₀ R,
      ∫ t in r₀..x, M.rhsScalarTwo t = M.cutMomentReal 2 x - M.cutMomentReal 2 r₀)
    (hP : Tendsto (fun r : ℝ => (M.cutMassAt r 0).toReal
      / ((M.α / (M.betaCrit : ℝ)) * r ^ M.α)) atTop (𝓝 1))
    (hH : Hydro M)
    (h6 : ∀ᶠ r : ℝ in atTop,
      M.cutMoment 6 r ≤ (945 : ℝ≥0∞) * (M.cutMoment 2 r) ^ 2 * (M.cutMoment 1 r) ^ 5) :
    Analysis.RegularlyVaryingAtTop (fun r : ℝ => (M.cutMoment 2 r).toReal) (3 * M.α) :=
  M.regularlyVarying_two_of_caseTwo_of_hP hα hr₀ hκ hd
    (Smwyvlg99M1.absolutelyContinuousOnInterval_toReal_two_of_forall_identity M hint hid)
    (Smwyvlg99M1.ae_hasDerivAt_toReal_two_of_forall_identity M hint hid)
    hP hH h6

/-- **The integrated identity is not a weaker input.**  Conversely to
`regularlyVarying_two_of_caseTwo_of_integrated_identity`: absolute continuity on
every tail window together with the a.e. identity `hae` implies the integrated
identity `hid` used there.  So the two Case-2 radial interfaces are equivalent,
and the integrated form is exactly the remaining measure-theoretic obligation. -/
theorem forall_identity_of_hac_hae
    {r₀ : ℝ}
    (hac : ∀ R : ℝ, r₀ ≤ R → AbsolutelyContinuousOnInterval
      (fun r : ℝ => (M.cutMoment 2 r).toReal) r₀ R)
    (hae : ∀ᵐ t ∂(volume.restrict (Ici r₀)),
      HasDerivAt (fun r : ℝ => (M.cutMoment 2 r).toReal) (M.rhsScalarTwo t) t) :
    ∀ R : ℝ, r₀ ≤ R → ∀ x ∈ Set.Icc r₀ R,
      ∫ t in r₀..x, M.rhsScalarTwo t = M.cutMomentReal 2 x - M.cutMomentReal 2 r₀ := by
  have hae' : ∀ᵐ t ∂(volume : Measure ℝ), t ∈ Set.Ici r₀ →
      HasDerivAt (fun r : ℝ => (M.cutMoment 2 r).toReal) (M.rhsScalarTwo t) t :=
    (ae_restrict_iff' measurableSet_Ici).mp hae
  intro R hR x hx
  exact Smwyvlg99M1.integral_eq_sub_of_absolutelyContinuousOnInterval_of_ae_hasDerivAt
    (f := fun r : ℝ => (M.cutMoment 2 r).toReal) (g := M.rhsScalarTwo) hx.1
    (hac x hx.1) (by
      filter_upwards [hae'] with t ht hmem
      exact ht (Set.mem_Ici.mpr (le_of_lt hmem.1)))

/-! ## 5. The sharp positive power-law limit: an extra hypothesis, not a Case-2 consequence

Case 2 supplies `Ē_{2,r} → 0` and nothing more.  The sharp conclusion
`E_{βc,r}|K|² ~ A r^{3α}` with `A > 0` additionally needs the *logarithmic
integrability* of `Ē_{2,r}` along `dr/r` — the hypothesis the paper obtains in
Case 1 (`d > 3α`) and in Case 3 under `∇_r` log-integrable, and which is simply
false in general at `d < 6`, `α = d/3` (Hutchcroft, Theorem III.1.2: there are
logarithmic corrections to `r^{3α}` scaling there).  It is therefore stated here
as an explicit extra input and is *not* part of the Case-2 theorem. -/

/-- **The `d = 3α` Case-2 sharp limit, conditional on logarithmic
integrability of the normalized error.** -/
theorem tendsto_div_two_of_caseTwo_of_hP
    (hα : 0 < M.α) {r₀ : ℝ} (hr₀ : 0 < r₀)
    (hκ : 0 < M.α / (M.betaCrit : ℝ))
    (hd : (M.d : ℝ) = 3 * M.α)
    (hac : ∀ R : ℝ, r₀ ≤ R → AbsolutelyContinuousOnInterval
      (fun r : ℝ => (M.cutMoment 2 r).toReal) r₀ R)
    (hae : ∀ᵐ t ∂(volume.restrict (Ici r₀)),
      HasDerivAt (fun r : ℝ => (M.cutMoment 2 r).toReal) (M.rhsScalarTwo t) t)
    (hP : Tendsto (fun r : ℝ => (M.cutMassAt r 0).toReal
      / ((M.α / (M.betaCrit : ℝ)) * r ^ M.α)) atTop (𝓝 1))
    (hH : Hydro M)
    (h6 : ∀ᶠ r : ℝ in atTop,
      M.cutMoment 6 r ≤ (945 : ℝ≥0∞) * (M.cutMoment 2 r) ^ 2 * (M.cutMoment 1 r) ^ 5)
    (hlog : Analysis.LogarithmicallyIntegrable M.p2Ebar) :
    ∃ A : ℝ, 0 < A ∧ Tendsto
      (fun r : ℝ => (M.cutMoment 2 r).toReal / r ^ (3 * M.α)) atTop (𝓝 A) := by
  have hβ : (M.betaCrit : ℝ) ≠ 0 := by
    intro h0
    rw [h0, div_zero] at hκ
    exact lt_irrefl 0 hκ
  have h1 : ∀ t : ℝ, M.cutMoment 1 t ≠ ⊤ :=
    M.cutMoment_one_ne_top_of_asymptotic (c := M.α / (M.betaCrit : ℝ)) hP
  have h2 : ∀ t : ℝ, M.cutMoment 2 t ≠ ⊤ := fun t =>
    cutMoment_ne_top_of_one M t (h1 t) 2
  have hE2 : Tendsto M.p2ExclError atTop (𝓝 0) :=
    CaseTwo.p2ExclError_tendsto_zero_of_caseTwo' M hd hκ hP hH
      ((eventually_ge_atTop r₀).mono fun r _ => h2 r) h6
  exact M.tendsto_div_two_of_hP hα hr₀ hβ hac hae
    (fun t _ => h1 t) (fun t _ => h2 t) hP hE2 hlog

end SourceModelData

end PercLib.CriticalLRP.Orchestration

/-! ## 6. Why regular variation is the right Case-2 conclusion

The abstract content of (I.4.15) is the linear ODE `f' = a (1 - E) f / t` with
`E → 0`.  The conclusion the paper draws from it is regular variation of index
`a`.  This section records, kernel-checked, that this is exactly what the
hypotheses support: the hypothesis `E → 0` alone is consistent with
`f t / t ^ a → 0`, so no sharp positive limit can be extracted from the
Case-2 error estimate without the additional logarithmic-integrability input.

The witness is `a = 1`, `E t = 1 / log t`, `f t = t / log t`.  Then
`t f' / f = 1 - 1 / log t`, so the ODE holds with `E = 1 / log t → 0`, while
`f t / t = 1 / log t → 0`.  This is an abstract witness for the ODE shape, not
a statement about the percolation model. -/

namespace PercLib.CriticalLRP.Analysis

/-- The Case-2 error profile `t ↦ 1 / log t` is measurable. -/
theorem measurable_inv_log : Measurable (fun t : ℝ => (Real.log t)⁻¹) :=
  Real.measurable_log.inv

/-- The Case-2 error profile `t ↦ 1 / log t` vanishes at infinity. -/
theorem tendsto_inv_log : Tendsto (fun t : ℝ => (Real.log t)⁻¹) atTop (𝓝 0) :=
  Real.tendsto_log_atTop.inv_tendsto_atTop

/-- `t ↦ t / log t` satisfies the linear ODE of (I.4.15) with index `a = 1` and
error `E t = (log t)⁻¹`. -/
theorem hasDerivAt_div_log {t : ℝ} (ht : 1 < t) :
    HasDerivAt (fun x : ℝ => x / Real.log x)
      (1 * (1 - (Real.log t)⁻¹) * (t / Real.log t) / t) t := by
  have ht0 : (0 : ℝ) < t := lt_trans one_pos ht
  have hlog : Real.log t ≠ 0 := (Real.log_pos ht).ne'
  have h := (hasDerivAt_id t).div (Real.hasDerivAt_log ht0.ne') hlog
  refine h.congr_deriv ?_
  change (1 * Real.log t - t * t⁻¹) / Real.log t ^ 2
      = 1 * (1 - (Real.log t)⁻¹) * (t / Real.log t) / t
  field_simp

/-- `t ↦ t / log t` is regularly varying of index `1`. -/
theorem regularlyVarying_div_log : RegularlyVaryingAtTop (fun t : ℝ => t / Real.log t) 1 := by
  constructor
  · filter_upwards [eventually_gt_atTop (1 : ℝ)] with x hx
    have hlog : (0 : ℝ) < Real.log x := Real.log_pos hx
    positivity
  · intro l hl
    have hg : Tendsto (fun x : ℝ => (Real.log x)⁻¹) atTop (𝓝 0) := tendsto_inv_log
    have hden : Tendsto (fun x : ℝ => Real.log l * (Real.log x)⁻¹ + 1) atTop (𝓝 1) := by
      have h1 : Tendsto (fun x : ℝ => Real.log l * (Real.log x)⁻¹) atTop (𝓝 (Real.log l * 0)) :=
        tendsto_const_nhds.mul hg
      have h2 : Tendsto (fun x : ℝ => Real.log l * (Real.log x)⁻¹ + 1) atTop
          (𝓝 (Real.log l * 0 + 1)) := h1.add tendsto_const_nhds
      simpa using h2
    have hinv : Tendsto (fun x : ℝ => (Real.log l * (Real.log x)⁻¹ + 1)⁻¹) atTop (𝓝 1) := by
      have h := hden.inv₀ (by norm_num : (1 : ℝ) ≠ 0)
      simpa using h
    have hquot : Tendsto (fun x : ℝ => Real.log x / (Real.log l + Real.log x)) atTop (𝓝 1) := by
      refine Filter.Tendsto.congr' ?_ hinv
      filter_upwards [eventually_gt_atTop (1 : ℝ)] with x hx
      have hlog : Real.log x ≠ 0 := (Real.log_pos hx).ne'
      field_simp
    have hlim : Tendsto (fun x : ℝ => l * (Real.log x / (Real.log l + Real.log x)))
        atTop (𝓝 (l * 1)) := tendsto_const_nhds.mul hquot
    simp only [Real.rpow_one, mul_one] at hlim ⊢
    refine Filter.Tendsto.congr' ?_ hlim
    filter_upwards [eventually_gt_atTop (1 : ℝ)] with x hx
    have hx0 : (0 : ℝ) < x := lt_trans one_pos hx
    rw [Real.log_mul hl.ne' hx0.ne']
    field_simp

/-- **No sharp positive power-law limit follows from the Case-2 error estimate
alone.**  There are a measurable error `E` with `E → 0` and a positive function
`f` satisfying `f' = a (1 - E) f / t` at every `t > 1`, such that `f` is
regularly varying of index `a` while `f t / t ^ a → 0`; in particular no
`A > 0` with `f ~ A t ^ a` exists.

So the Case-2 output `Ē_{2,r} → 0` is consistent with regular variation of
index `3α` and incompatible with a positive constant limit only after the
additional logarithmic-integrability hypothesis; the sharp form is genuinely
extra data (the paper obtains it in Case 1 and under `∇_r` log-integrable in
Case 3). -/
theorem exists_ode_regularlyVarying_not_sharp :
    ∃ (f E : ℝ → ℝ) (a : ℝ), 0 < a ∧ Measurable E ∧ Tendsto E atTop (𝓝 0) ∧
      (∀ t : ℝ, 1 < t → HasDerivAt f (a * (1 - E t) * f t / t) t) ∧
      RegularlyVaryingAtTop f a ∧
      ¬ ∃ A : ℝ, 0 < A ∧ Tendsto (fun t : ℝ => f t / t ^ a) atTop (𝓝 A) := by
  refine ⟨fun t : ℝ => t / Real.log t, fun t : ℝ => (Real.log t)⁻¹, 1, one_pos,
    measurable_inv_log, tendsto_inv_log, ?_, regularlyVarying_div_log, ?_⟩
  · intro t ht
    simpa using hasDerivAt_div_log ht
  · rintro ⟨A, hA, hT⟩
    have heq : (fun t : ℝ => (t / Real.log t) / t ^ (1 : ℝ)) =ᶠ[atTop]
        (fun t : ℝ => (Real.log t)⁻¹) := by
      filter_upwards [eventually_gt_atTop (1 : ℝ)] with t ht
      have ht0 : (0 : ℝ) < t := lt_trans one_pos ht
      have hlog : Real.log t ≠ 0 := (Real.log_pos ht).ne'
      rw [Real.rpow_one]
      field_simp
    have hT' : Tendsto (fun t : ℝ => (Real.log t)⁻¹) atTop (𝓝 A) :=
      Filter.Tendsto.congr' heq hT
    have hzero : A = 0 := tendsto_nhds_unique hT' tendsto_inv_log
    linarith

end PercLib.CriticalLRP.Analysis

/-! ## 7. Axiom audit -/

set_option linter.hashCommand false

#print axioms PercLib.CriticalLRP.Orchestration.SourceModelData.regularlyVarying_two_of_caseTwo
#print axioms
  PercLib.CriticalLRP.Orchestration.SourceModelData.regularlyVarying_two_of_caseTwo_of_hP
#print axioms
  PercLib.CriticalLRP.Orchestration.SourceModelData.momOf_two_regularlyVarying_of_caseTwo_of_hP
#print axioms
  PercLib.CriticalLRP.Orchestration.SourceModelData.regularlyVarying_two_of_caseTwo_of_sixthMomentMixed
#print axioms
  PercLib.CriticalLRP.Orchestration.SourceModelData.momOf_packet_of_caseTwo_of_hP
#print axioms
  PercLib.CriticalLRP.Orchestration.SourceModelData.slowlyVarying_momOf_two_div_cube
#print axioms
  PercLib.CriticalLRP.Orchestration.SourceModelData.regularlyVarying_two_of_caseTwo_of_integrated_identity
#print axioms
  PercLib.CriticalLRP.Orchestration.SourceModelData.forall_identity_of_hac_hae
#print axioms
  PercLib.CriticalLRP.Orchestration.SourceModelData.tendsto_div_two_of_caseTwo_of_hP
#print axioms PercLib.CriticalLRP.Analysis.measurable_inv_log
#print axioms PercLib.CriticalLRP.Analysis.tendsto_inv_log
#print axioms PercLib.CriticalLRP.Analysis.hasDerivAt_div_log
#print axioms PercLib.CriticalLRP.Analysis.regularlyVarying_div_log
#print axioms PercLib.CriticalLRP.Analysis.exists_ode_regularlyVarying_not_sharp
