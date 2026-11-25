/-
Copyright (c) 2026 PercLib contributors. Released under Apache 2.0.

# The `ℝ≥0∞ → ℝ` transfer for the `p = 2` paper sum

Swarm `smwvc1d9z`, member `m3`, direction `d2`

Integration donor: `.ultramath/smwvc1d9z/m3/ToReal.lean`, checked at `a6a74fb05eb13da61d4ce2cb87e2f55e7bd7c31f`. (referee / integration audit).

`Main.lintegral_p2PaperSum_eq_p2RHS` identifies the **`ℝ≥0∞`-valued** expectation of the paper's
`p = 2` double sum with the source's right-hand side `M.p2RHS r = exclMassQuad r + 2 * exclMassSqLin r`:

  `∫⁻ ω, p2PaperSum M r ω ∂(M.cutLaw r) = M.p2RHS r`.

The `p = 2` target of the project is however **real-valued**
(`SecondMoment/Defs.rhsScalarTwo`, `SecondMoment/FTC`): the derivative value is
`M.rhsScalarTwo r = M.coeffRHS r * (M.p2RHS r).toReal`, an honest `ℝ`-number, and it has to be
compared with `∫ ω, (paper sum) ∂(M.cutLaw r)` under the `cutLaw`.  The passage
`∫⁻ ↦ ∫` is *not* free: it needs

* measurability of `ω ↦ p2PaperSum M r ω` (available as `Basic.measurable_p2PaperSum`);
* a.e.-finiteness of the integrand under `M.cutLaw r`, which is exactly what a finite `p = 2` RHS
  buys (`M.p2RhsMass_ne_top`, from a finite **first** cut-off moment — no new hypothesis);
* `Integrable` of the real integrand, if any real-side manipulation is to be legal.

This file closes that step.  The output is the real-valued identity

  `∫ ω, (p2PaperSum M r ω).toReal ∂(M.cutLaw r) = (M.p2RHS r).toReal`

and, with the coefficient `M.coeffRHS r` carried along, the exact shape consumed by the FTC file:

  `M.rhsScalarTwo r = M.coeffRHS r * ∫ ω, (p2PaperSum M r ω).toReal ∂(M.cutLaw r)`.

Two further points that the `ℝ≥0∞` statement hides and that a real consumer needs:

* `(x).toReal = 0` for `x = ⊤`, so a real statement about `|K_0|` needs `clusterVol ω v ≠ ⊤`
  **simultaneously at every vertex**.  Since `M.V = Fin M.d → ℤ` is countable, the per-vertex
  translation-invariance computation `lintegral_clusterVol_pow_vertex` upgrades to the a.e.
  statement `∀ᵐ ω, ∀ v, clusterVol ω v ≠ ⊤` — this is `ae_forall_lt_top_clusterVol` below, and it
  is what the per-edge laws (which need `hK`, `hKx`, `hKy` at once) must be fed.
* the paper's double sum `∑_{b ∈ K_0} ∑_{c ∈ B_r(b)} …` has to be recovered from the `tsum`, so
  the `tsum`-`toReal` interchange is recorded too (`toReal_p2PaperSum_eq_tsum`).

Everything here is `ℝ`-valued bookkeeping on top of the landed `ℝ≥0∞` identities.  **No radius is
differentiated, no flux is interchanged, and nothing is claimed about `cutMomentReal 2`.**  The
hypotheses that are *not* discharged here are stated in `RESULTS.md`.
-/
module

public import PercLib.CriticalLRP.Analysis.Cutoff.SecondMoment.Transport.Defs
public import PercLib.CriticalLRP.Analysis.Cutoff.SecondMoment.Transport.Basic
public import PercLib.CriticalLRP.Analysis.Cutoff.SecondMoment.Transport.Main
public import PercLib.CriticalLRP.Analysis.Cutoff.SecondMoment.Finiteness
public import PercLib.CriticalLRP.Analysis.Cutoff.CutoffMomentContinuity

/-!
# From the `ℝ≥0∞` `p = 2` identity to its real-valued form

Section 1: a.e. finiteness of the paper sum, of every cluster volume, and of every summand.
Section 2: the `lintegral`-to-`integral` transfer and its consequences for `rhsScalarTwo`.
Section 3: the same with the pipeline's moment hypothesis instead of an explicit RHS finiteness.
Section 4: the doubly indexed real series, i.e. the paper's displayed sum.
-/

set_option autoImplicit false
set_option linter.hashCommand false
set_option linter.style.longLine false

@[expose] public section

noncomputable section

open MeasureTheory
open scoped ENNReal NNReal

namespace PercLib.CriticalLRP

namespace PivotFlux

open Orchestration

variable (M : SourceModelData)

attribute [local instance] Classical.propDecidable

/-! ## 1. A.e. finiteness -/

/-- **The paper sum is a.e. finite** as soon as the `p = 2` right-hand side is.  A finite
`lintegral` of an `ℝ≥0∞`-valued function forces the function to be finite a.e.,
so `Main.lintegral_p2PaperSum_eq_p2RHS` transfers the finiteness of `M.p2RHS r` to the
integrand.  No measurability is needed for this step but it is available
(`Basic.measurable_p2PaperSum`). -/
theorem ae_lt_top_p2PaperSum (r : ℝ) (h : M.p2RHS r ≠ ⊤) :
    ∀ᵐ ω ∂(M.cutLaw r), p2PaperSum M r ω < ⊤ := by
  refine MeasureTheory.ae_lt_top (measurable_p2PaperSum M r) ?_
  rw [lintegral_p2PaperSum_eq_p2RHS]
  exact h

/-- **Every cluster volume is a.e. finite, at a single vertex.**  The `p`-th cut-off moment is
translation invariant (`lintegral_clusterVol_pow_vertex`), so finiteness of the first moment at
the origin gives finiteness of `clusterVol ω v` for the fixed vertex `v`. -/
theorem ae_lt_top_clusterVol (r : ℝ) (v : M.V) (h1 : M.cutMoment 1 r ≠ ⊤) :
    ∀ᵐ ω ∂(M.cutLaw r), clusterVol ω v < ⊤ := by
  refine MeasureTheory.ae_lt_top (measurable_clusterVol v) ?_
  have h : ∫⁻ ω, clusterVol ω v ∂(M.cutLaw r) = M.cutMoment 1 r := by
    rw [show (∫⁻ ω, clusterVol ω v ∂(M.cutLaw r))
        = ∫⁻ ω, clusterVol ω v ^ (1 : ℕ) ∂(M.cutLaw r) from by simp,
      M.lintegral_clusterVol_pow_vertex r v 1]
  rw [h]
  exact h1

/-- **Every cluster volume is a.e. finite, simultaneously at every vertex.**

`M.V = Fin M.d → ℤ` is countable, so the countably many exceptional null sets of
`ae_lt_top_clusterVol` can be intersected.  This is the form the per-edge (oriented) laws need,
because the single-edge increment of `(clusterVol · 0).toReal ^ 2` involves `clusterVol` at the
anchor and at both endpoints of the edge at the same time.

The hypothesis is a finite **first** cut-off moment; it is *not* an extra assumption of the
formalisation, it is the same `M.cutMoment 1 r ≠ ⊤` that already appears in
`SecondMoment/Finiteness.p2RhsMass_ne_top`. -/
theorem ae_forall_lt_top_clusterVol (r : ℝ) (h1 : M.cutMoment 1 r ≠ ⊤) :
    ∀ᵐ ω ∂(M.cutLaw r), ∀ v : M.V, clusterVol ω v < ⊤ := by
  rw [ae_all_iff]
  exact fun v => ae_lt_top_clusterVol M r v h1

/-- `configIndicator` of any set is at most one. -/
theorem configIndicator_le_one (s : Set (Config M.V)) (ω : Config M.V) :
    configIndicator s ω ≤ 1 := by
  unfold configIndicator
  by_cases h : ω ∈ s
  · rw [Set.indicator_of_mem h]
  · rw [Set.indicator_of_notMem h]
    simp

/-- **The `p = 1` pivotal weight is at most the target cluster volume of `c`.**  Each of the
three indicators of `pivotWeight` is at most `1`, so the weight is dominated by its only
non-indicator factor, `|K_c|`. -/
theorem pivotWeight_le_clusterVol (r : ℝ) (ω : Config M.V) (a b c : M.V) :
    pivotWeight M r ω a b c ≤ clusterVol ω c := by
  unfold pivotWeight
  calc configIndicator {ω' : Config M.V | Connects ω' a b} ω *
        (if M.S.dist c b ≤ r then 1 else 0) *
          configIndicator {ω' : Config M.V | ¬ Connects ω' b c} ω * clusterVol ω c
      ≤ 1 * 1 * 1 * clusterVol ω c := by
        gcongr
        · exact configIndicator_le_one M _ ω
        · split <;> norm_num
        · exact configIndicator_le_one M _ ω
    _ = clusterVol ω c := by ring

/-- **The `p = 2` pivotal weight is at most the square of the target cluster volume.** -/
theorem pivotWeightSq_le_clusterVol_sq (r : ℝ) (ω : Config M.V) (a b c : M.V) :
    pivotWeightSq M r ω a b c ≤ clusterVol ω c ^ 2 := by
  unfold pivotWeightSq
  calc configIndicator {ω' : Config M.V | Connects ω' a b} ω *
        (if M.S.dist c b ≤ r then 1 else 0) *
          configIndicator {ω' : Config M.V | ¬ Connects ω' b c} ω * clusterVol ω c ^ 2
      ≤ 1 * 1 * 1 * clusterVol ω c ^ 2 := by
        gcongr
        · exact configIndicator_le_one M _ ω
        · split <;> norm_num
        · exact configIndicator_le_one M _ ω
    _ = clusterVol ω c ^ 2 := by ring

/-- **Every summand of the `p = 2` paper sum is a.e. finite.**  Immediate from
`ae_forall_lt_top_clusterVol` together with the two domination lemmas above: the summand is
`2 * |K_0| * pivotWeight 0 b c + pivotWeightSq 0 b c`, which is at most
`2 * |K_0| * |K_c| + |K_c| ^ 2`.

This is what a real consumer needs in order to read the paper's displayed summand
`1(c ∉ K_0) (2 |K_0| |K_c| + |K_c|^2)` as a real number. -/
theorem ae_forall_lt_top_p2Weight (r : ℝ) (h1 : M.cutMoment 1 r ≠ ⊤) :
    ∀ᵐ ω ∂(M.cutLaw r), ∀ b c : M.V, p2Weight M r ω b c < ⊤ := by
  rw [ae_all_iff]
  refine fun b => ?_
  rw [ae_all_iff]
  refine fun c => ?_
  have h : ∀ᵐ ω ∂(M.cutLaw r), clusterVol ω (0 : M.V) < ⊤ ∧ clusterVol ω c < ⊤ :=
    (ae_forall_lt_top_clusterVol M r h1).mono fun ω hω =>
      ⟨hω 0, hω c⟩
  refine h.mono fun ω hω => ?_
  have hw : pivotWeight M r ω (0 : M.V) b c < ⊤ :=
    lt_of_le_of_lt (pivotWeight_le_clusterVol M r ω 0 b c) hω.2
  have hsq : pivotWeightSq M r ω (0 : M.V) b c < ⊤ :=
    lt_of_le_of_lt (pivotWeightSq_le_clusterVol_sq M r ω 0 b c)
      (ENNReal.pow_lt_top hω.2)
  exact lt_of_le_of_lt (by
    refine add_le_add (mul_le_mul' (mul_le_mul' le_rfl le_rfl) le_rfl) le_rfl) (by
    exact ENNReal.add_lt_top.mpr
      ⟨ENNReal.mul_lt_top (ENNReal.mul_lt_top (by norm_num) hω.1) hw, hsq⟩)

/-! ## 2. The `lintegral`-to-`integral` transfer -/

/-- **The real-valued `p = 2` paper-sum identity.**

This is the exact `ℝ≥0∞ → ℝ` transfer of `Main.lintegral_p2PaperSum_eq_p2RHS`:
`MeasureTheory.integral_toReal` converts the `ℝ`-valued integral of the real part into the real
part of the `ℝ≥0∞`-valued integral, and a.e.-finiteness (`ae_lt_top_p2PaperSum`) is precisely its
side condition.  The only hypothesis is finiteness of the source's `p = 2` right-hand side, which
`SecondMoment/Finiteness.p2RhsMass_ne_top` discharges from a finite first cut-off moment. -/
theorem integral_toReal_p2PaperSum (r : ℝ) (h : M.p2RHS r ≠ ⊤) :
    ∫ ω, (p2PaperSum M r ω).toReal ∂(M.cutLaw r) = (M.p2RHS r).toReal := by
  rw [MeasureTheory.integral_toReal (measurable_p2PaperSum M r).aemeasurable
      (ae_lt_top_p2PaperSum M r h),
    lintegral_p2PaperSum_eq_p2RHS]

/-- **The real paper sum is `L¹` at `cutLaw r`.**  Needed for every subsequent real-side
manipulation (dominated convergence, `intervalIntegral`, moving the coefficient `M.coeffRHS r`
through the integral).  Again no hypothesis beyond finiteness of `M.p2RHS r`. -/
theorem integrable_toReal_p2PaperSum (r : ℝ) (h : M.p2RHS r ≠ ⊤) :
    Integrable (fun ω => (p2PaperSum M r ω).toReal) (M.cutLaw r) := by
  refine ⟨(measurable_p2PaperSum M r).aemeasurable.ennreal_toReal.aestronglyMeasurable, ?_⟩
  rw [MeasureTheory.hasFiniteIntegral_iff_ofReal
    (Filter.Eventually.of_forall fun ω => ENNReal.toReal_nonneg)]
  calc ∫⁻ ω, ENNReal.ofReal ((p2PaperSum M r ω).toReal) ∂(M.cutLaw r)
      = ∫⁻ ω, p2PaperSum M r ω ∂(M.cutLaw r) :=
        lintegral_congr_ae ((ae_lt_top_p2PaperSum M r h).mono fun ω hω =>
          ENNReal.ofReal_toReal hω.ne)
    _ = M.p2RHS r := lintegral_p2PaperSum_eq_p2RHS M r
    _ < ⊤ := lt_top_iff_ne_top.mpr h

/-- **The real paper-sum expectation in the source's two-term form**, with the binomial
coefficient `2` visible on the `|K|^2 |K_y|` term and no `toReal` of a sum: this is
`E[ |K_0| ∑_{y ∈ B_r, y ∉ K_0} |K_y|^2 ] + 2 E[ |K_0|^2 ∑_{y ∈ B_r, y ∉ K_0} |K_y| ]` at
`cutLaw r`.  It is the real-number fidelity statement for Lemma I.4.1 at `p = 2`. -/
theorem integral_toReal_p2PaperSum_eq_source (r : ℝ) (hq : M.exclMassQuad r ≠ ⊤)
    (hp : M.exclMassSqLin r ≠ ⊤) :
    ∫ ω, (p2PaperSum M r ω).toReal ∂(M.cutLaw r)
      = (M.exclMassQuad r).toReal + 2 * (M.exclMassSqLin r).toReal := by
  have h : M.p2RHS r ≠ ⊤ :=
    ENNReal.add_ne_top.mpr ⟨hq, ENNReal.mul_ne_top (by norm_num) hp⟩
  have hdef : M.p2RHS r = M.exclMassQuad r + 2 * M.exclMassSqLin r := rfl
  rw [integral_toReal_p2PaperSum M r h, hdef,
    ENNReal.toReal_add hq (ENNReal.mul_ne_top (by norm_num) hp), ENNReal.toReal_mul]
  norm_num

/-- **The derivative value `M.rhsScalarTwo r` is the coefficient times the real paper sum.**
This is the shape the FTC file consumes: the accepted `p = 2` right-hand side of (I.4.1) is
`β_c (-K'(r))` times the honest real-number expectation of the paper's double sum. -/
theorem rhsScalarTwo_eq_integral_toReal_p2PaperSum (r : ℝ) (h : M.p2RHS r ≠ ⊤) :
    M.rhsScalarTwo r = M.coeffRHS r * ∫ ω, (p2PaperSum M r ω).toReal ∂(M.cutLaw r) := by
  change M.coeffRHS r * (M.p2RHS r).toReal = _
  rw [integral_toReal_p2PaperSum M r h]

/-- The same with the coefficient `M.coeffRHS r` moved **inside** the integral.  This is the form
in which the `p = 2` derivative density appears as `β_c (-K'(r))` times the paper summand
integrated against the cut-off law. -/
theorem rhsScalarTwo_eq_integral_coeffRHS_mul (r : ℝ) (h : M.p2RHS r ≠ ⊤) :
    M.rhsScalarTwo r
      = ∫ ω, M.coeffRHS r * (p2PaperSum M r ω).toReal ∂(M.cutLaw r) := by
  rw [MeasureTheory.integral_const_mul, ← rhsScalarTwo_eq_integral_toReal_p2PaperSum M r h]

/-! ## 3. The same under the pipeline's moment hypothesis -/

/-- **The `p = 2` real paper-sum expectation from a finite first cut-off moment.**  The
finiteness of `M.p2RHS r` is *derived*, not assumed: `SecondMoment/Finiteness.p2RhsMass_ne_top`
gets it from `M.cutMoment 1 r ≠ ⊤` through the landed second- and fourth-moment transfers. -/
theorem integral_toReal_p2PaperSum_of_firstMoment {c : ℝ} (hc : 0 < c)
    (hρ : ∀ z : M.V, M.S.ρ (toVec z) = c * (FiniteVolume.linfNorm z : ℝ)) {r : ℝ}
    (hr : 0 < r) (h1 : M.cutMoment 1 r ≠ ⊤) :
    ∫ ω, (p2PaperSum M r ω).toReal ∂(M.cutLaw r) = (M.p2RHS r).toReal :=
  integral_toReal_p2PaperSum M r (M.p2RhsMass_ne_top hc hρ hr h1)

/-- **The derivative value in real paper-sum form, from a finite first cut-off moment.** -/
theorem rhsScalarTwo_eq_integral_toReal_p2PaperSum_of_firstMoment {c : ℝ} (hc : 0 < c)
    (hρ : ∀ z : M.V, M.S.ρ (toVec z) = c * (FiniteVolume.linfNorm z : ℝ)) {r : ℝ}
    (hr : 0 < r) (h1 : M.cutMoment 1 r ≠ ⊤) :
    M.rhsScalarTwo r = M.coeffRHS r * ∫ ω, (p2PaperSum M r ω).toReal ∂(M.cutLaw r) :=
  rhsScalarTwo_eq_integral_toReal_p2PaperSum M r (M.p2RhsMass_ne_top hc hρ hr h1)

/-- The `L¹` statement of Section 2 from a finite first cut-off moment. -/
theorem integrable_toReal_p2PaperSum_of_firstMoment {c : ℝ} (hc : 0 < c)
    (hρ : ∀ z : M.V, M.S.ρ (toVec z) = c * (FiniteVolume.linfNorm z : ℝ)) {r : ℝ}
    (hr : 0 < r) (h1 : M.cutMoment 1 r ≠ ⊤) :
    Integrable (fun ω => (p2PaperSum M r ω).toReal) (M.cutLaw r) :=
  integrable_toReal_p2PaperSum M r (M.p2RhsMass_ne_top hc hρ hr h1)

/-! ## 4. The paper's displayed double sum, as a real series -/

/-- **The `tsum`-`toReal` interchange**: on the event where the paper sum is finite, the real
number `(p2PaperSum ω).toReal` *is* the paper's displayed doubly indexed real series
`∑_b ∑_c (2 |K_0| |K_c| + |K_c|^2)`-weight.  This is the pointwise half of "source meaning
preserved": no `⊤` is silently read as `0`. -/
theorem toReal_p2PaperSum_eq_tsum (r : ℝ) (ω : Config M.V) (h : p2PaperSum M r ω ≠ ⊤) :
    (p2PaperSum M r ω).toReal
      = ∑' b : M.V, ∑' c : M.V, (p2Weight M r ω b c).toReal := by
  have hinner : ∀ b : M.V, ∑' c : M.V, p2Weight M r ω b c ≠ ⊤ := by
    intro b
    refine ne_top_of_le_ne_top h ?_
    simpa only [p2PaperSum] using
      ENNReal.le_tsum (f := fun b : M.V => ∑' c : M.V, p2Weight M r ω b c) b
  rw [show p2PaperSum M r ω = ∑' b : M.V, ∑' c : M.V, p2Weight M r ω b c from rfl,
    ENNReal.tsum_toReal_eq hinner]
  exact tsum_congr fun b =>
    ENNReal.tsum_toReal_eq fun c => ne_top_of_le_ne_top (hinner b) (ENNReal.le_tsum c)

/-- The pointwise interchange, a.e. under `cutLaw r`, from finiteness of the `p = 2` RHS. -/
theorem ae_toReal_p2PaperSum_eq_tsum (r : ℝ) (h : M.p2RHS r ≠ ⊤) :
    ∀ᵐ ω ∂(M.cutLaw r),
      (p2PaperSum M r ω).toReal
        = ∑' b : M.V, ∑' c : M.V, (p2Weight M r ω b c).toReal :=
  (ae_lt_top_p2PaperSum M r h).mono fun ω hω => toReal_p2PaperSum_eq_tsum M r ω hω.ne

/-- **The expectation of the paper's displayed real double sum is the source's `p = 2`
right-hand side.**  This is `Main.lintegral_p2PaperSum_eq_p2RHS` with the paper's own real
series on the left instead of an `ℝ≥0∞` `lintegral`. -/
theorem integral_tsum_p2Weight_toReal (r : ℝ) (h : M.p2RHS r ≠ ⊤) :
    ∫ ω, (∑' b : M.V, ∑' c : M.V, (p2Weight M r ω b c).toReal) ∂(M.cutLaw r)
      = (M.p2RHS r).toReal := by
  have hsym : (fun ω => ∑' b : M.V, ∑' c : M.V, (p2Weight M r ω b c).toReal)
      =ᵐ[M.cutLaw r] fun ω => (p2PaperSum M r ω).toReal := by
    filter_upwards [ae_toReal_p2PaperSum_eq_tsum M r h] with ω hω using hω.symm
  rw [integral_congr_ae hsym, integral_toReal_p2PaperSum M r h]

/-- **The derivative value as the coefficient times the expectation of the paper's displayed real
double sum.** -/
theorem rhsScalarTwo_eq_coeffRHS_mul_integral_tsum (r : ℝ) (h : M.p2RHS r ≠ ⊤) :
    M.rhsScalarTwo r
      = M.coeffRHS r
        * ∫ ω, (∑' b : M.V, ∑' c : M.V, (p2Weight M r ω b c).toReal) ∂(M.cutLaw r) := by
  change M.coeffRHS r * (M.p2RHS r).toReal = _
  rw [integral_tsum_p2Weight_toReal M r h]

/-- The same from a finite first cut-off moment. -/
theorem rhsScalarTwo_eq_coeffRHS_mul_integral_tsum_of_firstMoment {c : ℝ} (hc : 0 < c)
    (hρ : ∀ z : M.V, M.S.ρ (toVec z) = c * (FiniteVolume.linfNorm z : ℝ)) {r : ℝ}
    (hr : 0 < r) (h1 : M.cutMoment 1 r ≠ ⊤) :
    M.rhsScalarTwo r
      = M.coeffRHS r
        * ∫ ω, (∑' b : M.V, ∑' c : M.V, (p2Weight M r ω b c).toReal) ∂(M.cutLaw r) :=
  rhsScalarTwo_eq_coeffRHS_mul_integral_tsum M r (M.p2RhsMass_ne_top hc hρ hr h1)

/-! ## 5. Referee cross-check: the same transfer on the landed `p = 1` chain

The transfer above is not `p = 2`-specific.  Applied to the landed `p = 1` identity
`PivotFlux.lintegral_paperSum_eq_exclMass` it must reproduce the landed real-valued `p = 1`
derivative weight `M.rhsScalar r = M.coeffRHS r * M.exclScalar r`.  It does, which is the
check that the `toReal` step is faithful and does not smuggle in a spurious `⊤ ↦ 0`. -/

/-- Measurability of the `p = 1` paper sum (not landed; used only for the cross-check). -/
theorem measurable_paperSum (r : ℝ) : Measurable fun ω : Config M.V => paperSum M r ω :=
  Measurable.tsum fun b => Measurable.tsum fun c => measurable_pivotWeight M r 0 b c

/-- The `p = 1` paper sum is a.e. finite at a finite excluded mass. -/
theorem ae_lt_top_paperSum (r : ℝ) (h : E1Sign.exclMass M r ≠ ⊤) :
    ∀ᵐ ω ∂(M.cutLaw r), paperSum M r ω < ⊤ := by
  refine MeasureTheory.ae_lt_top (measurable_paperSum M r) ?_
  rw [lintegral_paperSum_eq_exclMass]
  exact h

/-- **The real `p = 1` paper sum integrates to the real excluded mass.** -/
theorem integral_toReal_paperSum (r : ℝ) (h : E1Sign.exclMass M r ≠ ⊤) :
    ∫ ω, (paperSum M r ω).toReal ∂(M.cutLaw r) = (E1Sign.exclMass M r).toReal := by
  rw [MeasureTheory.integral_toReal (measurable_paperSum M r).aemeasurable
      (ae_lt_top_paperSum M r h),
    lintegral_paperSum_eq_exclMass]

/-- **Cross-check: the landed `p = 1` derivative weight is the coefficient times the real paper
sum.**  Since `M.rhsScalar r = M.coeffRHS r * M.exclScalar r` and
`M.exclScalar r = (E1Sign.exclMass M r).toReal`, this is `integral_toReal_paperSum` read
backwards; it shows the `p = 2` theorem `rhsScalarTwo_eq_integral_toReal_p2PaperSum` has exactly
the same shape as the landed `p = 1` weight, so the two are comparable. -/
theorem rhsScalar_eq_integral_toReal_paperSum (r : ℝ) (h : E1Sign.exclMass M r ≠ ⊤) :
    M.rhsScalar r = M.coeffRHS r * ∫ ω, (paperSum M r ω).toReal ∂(M.cutLaw r) := by
  change M.coeffRHS r * (E1Sign.exclMass M r).toReal = _
  rw [integral_toReal_paperSum M r h]

/-! ## 6. Source-meaning check: the double sum has no diagonal term -/

/-- Every vertex is connected to itself. -/
theorem connects_self (ω : Config M.V) (v : M.V) : Connects ω v v :=
  SimpleGraph.Reachable.refl v

/-- **The diagonal of the `p = 2` paper sum vanishes.**  The paper's double sum
`∑_{b ∈ K_0} ∑_{c ∈ B_r(b)} 1(c ∉ K_0) …` is over *distinct* pairs: both `pivotWeight` and
`pivotWeightSq` carry the indicator of the closed event `¬ Connects ω b c`, which is empty at
`c = b`.  Consequently `p2PaperSum` never receives a diagonal contribution, and an
ordered-pair-to-unordered-edge (`Sym2`) count needs no diagonal correction term.

*(Recorded because the corresponding count is a separate direction of this swarm; the count
itself is not proved here.)* -/
theorem p2Weight_diag (r : ℝ) (ω : Config M.V) (b : M.V) : p2Weight M r ω b b = 0 := by
  have hz : configIndicator {ω' : Config M.V | ¬ Connects ω' b b} ω = 0 := by
    simp [configIndicator]
  unfold p2Weight pivotWeight pivotWeightSq
  simp only [hz]
  ring

end PivotFlux

end PercLib.CriticalLRP

end

/-! ## Axiom audit of every public statement of this file -/

#print axioms PercLib.CriticalLRP.PivotFlux.ae_lt_top_p2PaperSum
#print axioms PercLib.CriticalLRP.PivotFlux.ae_lt_top_clusterVol
#print axioms PercLib.CriticalLRP.PivotFlux.ae_forall_lt_top_clusterVol
#print axioms PercLib.CriticalLRP.PivotFlux.configIndicator_le_one
#print axioms PercLib.CriticalLRP.PivotFlux.pivotWeight_le_clusterVol
#print axioms PercLib.CriticalLRP.PivotFlux.pivotWeightSq_le_clusterVol_sq
#print axioms PercLib.CriticalLRP.PivotFlux.ae_forall_lt_top_p2Weight
#print axioms PercLib.CriticalLRP.PivotFlux.integral_toReal_p2PaperSum
#print axioms PercLib.CriticalLRP.PivotFlux.integrable_toReal_p2PaperSum
#print axioms PercLib.CriticalLRP.PivotFlux.integral_toReal_p2PaperSum_eq_source
#print axioms PercLib.CriticalLRP.PivotFlux.rhsScalarTwo_eq_integral_toReal_p2PaperSum
#print axioms PercLib.CriticalLRP.PivotFlux.rhsScalarTwo_eq_integral_coeffRHS_mul
#print axioms PercLib.CriticalLRP.PivotFlux.integral_toReal_p2PaperSum_of_firstMoment
#print axioms PercLib.CriticalLRP.PivotFlux.rhsScalarTwo_eq_integral_toReal_p2PaperSum_of_firstMoment
#print axioms PercLib.CriticalLRP.PivotFlux.integrable_toReal_p2PaperSum_of_firstMoment
#print axioms PercLib.CriticalLRP.PivotFlux.toReal_p2PaperSum_eq_tsum
#print axioms PercLib.CriticalLRP.PivotFlux.ae_toReal_p2PaperSum_eq_tsum
#print axioms PercLib.CriticalLRP.PivotFlux.integral_tsum_p2Weight_toReal
#print axioms PercLib.CriticalLRP.PivotFlux.rhsScalarTwo_eq_coeffRHS_mul_integral_tsum
#print axioms PercLib.CriticalLRP.PivotFlux.rhsScalarTwo_eq_coeffRHS_mul_integral_tsum_of_firstMoment

set_option linter.hashCommand false in
#print axioms PercLib.CriticalLRP.PivotFlux.ae_lt_top_p2PaperSum
#print axioms PercLib.CriticalLRP.PivotFlux.ae_lt_top_clusterVol
#print axioms PercLib.CriticalLRP.PivotFlux.ae_forall_lt_top_clusterVol
#print axioms PercLib.CriticalLRP.PivotFlux.pivotWeight_le_clusterVol
#print axioms PercLib.CriticalLRP.PivotFlux.pivotWeightSq_le_clusterVol_sq
#print axioms PercLib.CriticalLRP.PivotFlux.ae_forall_lt_top_p2Weight
#print axioms PercLib.CriticalLRP.PivotFlux.measurable_paperSum
#print axioms PercLib.CriticalLRP.PivotFlux.ae_lt_top_paperSum
#print axioms PercLib.CriticalLRP.PivotFlux.integral_toReal_paperSum
#print axioms PercLib.CriticalLRP.PivotFlux.rhsScalar_eq_integral_toReal_paperSum
#print axioms PercLib.CriticalLRP.PivotFlux.connects_self
#print axioms PercLib.CriticalLRP.PivotFlux.p2Weight_diag
