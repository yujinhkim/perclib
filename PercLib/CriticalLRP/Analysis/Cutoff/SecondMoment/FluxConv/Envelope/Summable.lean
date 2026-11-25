/-
Copyright (c) 2026 PercLib contributors. Released under Apache 2.0.

Swarm `smwvhhc1v`, member `m2`, direction (B).

# The summable envelope of the fixed-radius `p = 2` flux: expectation and limit

This file finishes `hfluxConv` at a fixed radius: the missing input of
`FluxConv.Insertion.tendsto_windowFlux_of_envelope` is the per-edge integrability and the
`|cutEdgeDeriv r e|`-weighted **summability** of the means of the envelope.  Both are derived here
from the fourth cutoff moment and the two comparison results:

* the pointwise comparison of the two marked `p = 2` weights (`Compare.lean`, direction (A),
  consumed here without reproof);
* the summation of the cubic connection correction `∑_b ∑_c 3|K_0|² 1(0↔b) 1(b↔c) ≤ 3|K_0|⁴`
  (`Corr.lean`).

The chain is, in the `ℝ≥0∞` world (no finiteness hypothesis anywhere):

`∑_e E[unexclEdgeWeight(· \\ {e}) 0 e]`
`  ≤ ∑_e E[unexclEdgeWeight(·) 0 e]`          (monotonicity in the configuration)
`  = E[∑_e unexclEdgeWeight(·) 0 e]`           (`lintegral_tsum`)
`  = E[∑_b ∑_c unexclPairWeight(·) 0 b c]`     (base `tsum_unexclEdgeWeight_eq`)
`  ≤ E[p2PaperSum + 3|K_0|⁴] = p2RHS + 3 cutMoment 4`   (comparison, correction, `Flux/Main`)

and then, with `|cutEdgeDeriv r e| ≤ coeffRHS r` (`abs_cutEdgeDeriv_le`) and the fact that the
envelope *is* the unexcluded ghost on the differentiating support,

`∑_e 2|cutEdgeDeriv r e| ∫ envelope_e ≤ 2 coeffRHS r (p2RHS r + 3 cutMoment 4 r) < ∞`.

Note that the `cutEdgeClosedWeight ≤ 1` factor is *not* used as a separate hypothesis: the
coefficient estimate `|cutEdgeDeriv| ≤ coeffRHS` already contains it, so no product structure and no
closure probability enters.  The unweighted bound is `p2RHS + 3 cutMoment 4`, of the shape the
paper's `p = 2` window estimate produces; the constant `2 coeffRHS` is carried explicitly.

The `cutMassAt r 0 ≠ ⊤` and `p2RHS r ≠ ⊤` hypotheses of the landed insertion theorem are *derived*
here from `cutMoment 4 r ≠ ⊤` and `1 ≤ |K_0|`, so the final statement only assumes `0 < r` and a
finite fourth cutoff moment.  No radius derivative, no uniform-in-radius majorant and no
`Input`-style axiom appears.
-/
module

public import PercLib.CriticalLRP.Analysis.Cutoff.SecondMoment.FluxConv.Envelope.Reindex
public import PercLib.CriticalLRP.Analysis.Cutoff.SecondMoment.FluxConv.Envelope.Correction
public import PercLib.CriticalLRP.Analysis.Cutoff.SecondMoment.FluxConv.Envelope.Compare

/-!
# Summability of the coefficient-weighted envelope and the fixed-radius limit
-/

set_option autoImplicit false
set_option linter.hashCommand false
set_option linter.style.longLine false
set_option linter.unusedSectionVars false
set_option linter.unreachableTactic false

@[expose] public section

noncomputable section

open MeasureTheory Filter
open scoped ENNReal NNReal Topology BigOperators

namespace PercLib.CriticalLRP

namespace Orchestration

namespace SourceModelData

variable (M : SourceModelData)

attribute [local instance] Classical.propDecidable

/-! ## 1. The summed comparison of the unexcluded weight with the paper sum -/

/-- **`∑_b ∑_c unexclPairWeight ≤ p2PaperSum + 3 |K_0|⁴`.**  The pointwise comparison of direction
(A) is summed with `ENNReal.tsum_add`, and the cubic connection correction is bounded by
`Corr.tsum_tsum_connCorr_le`. -/
theorem tsum_tsum_unexclPairWeight_le (r : ℝ) (ω : Config M.V) :
    (∑' b : M.V, ∑' c : M.V, unexclPairWeight M r ω (0 : M.V) b c)
      ≤ PivotFlux.p2PaperSum M r ω + 3 * clusterVol ω (0 : M.V) ^ 4 := by
  have hpt : ∀ b c : M.V, unexclPairWeight M r ω (0 : M.V) b c ≤
      PivotFlux.p2Weight M r ω b c + 3 * clusterVol ω (0 : M.V) ^ 2 *
        configIndicator {ω' : Config M.V | Connects ω' (0 : M.V) b} ω *
          configIndicator {ω' : Config M.V | Connects ω' b c} ω :=
    fun b c => unexclPairWeight_le_p2Weight_add M r ω b c
  calc (∑' b : M.V, ∑' c : M.V, unexclPairWeight M r ω (0 : M.V) b c)
      ≤ ∑' b : M.V, ∑' c : M.V, (PivotFlux.p2Weight M r ω b c +
          3 * clusterVol ω (0 : M.V) ^ 2 *
            configIndicator {ω' : Config M.V | Connects ω' (0 : M.V) b} ω *
              configIndicator {ω' : Config M.V | Connects ω' b c} ω) :=
        ENNReal.tsum_le_tsum fun b => ENNReal.tsum_le_tsum fun c => hpt b c
    _ = ∑' b : M.V, ((∑' c : M.V, PivotFlux.p2Weight M r ω b c) +
          ∑' c : M.V, 3 * clusterVol ω (0 : M.V) ^ 2 *
            configIndicator {ω' : Config M.V | Connects ω' (0 : M.V) b} ω *
              configIndicator {ω' : Config M.V | Connects ω' b c} ω) :=
        tsum_congr fun b => ENNReal.tsum_add
    _ = (∑' b : M.V, ∑' c : M.V, PivotFlux.p2Weight M r ω b c) +
          ∑' b : M.V, ∑' c : M.V, 3 * clusterVol ω (0 : M.V) ^ 2 *
            configIndicator {ω' : Config M.V | Connects ω' (0 : M.V) b} ω *
              configIndicator {ω' : Config M.V | Connects ω' b c} ω :=
        ENNReal.tsum_add
    _ ≤ PivotFlux.p2PaperSum M r ω + 3 * clusterVol ω (0 : M.V) ^ 4 :=
        add_le_add le_rfl (tsum_tsum_connCorr_le M ω)

/-! ## 2. Measurability of the paper sum -/

/-- The paper double sum is measurable in the configuration. -/
theorem measurable_p2PaperSum (r : ℝ) :
    Measurable fun ω : Config M.V => PivotFlux.p2PaperSum M r ω :=
  Measurable.tsum fun b => Measurable.tsum fun c => PivotFlux.measurable_p2Weight M r b c

/-! ## 3. The expectation of the unexcluded double sum -/

/-- **`E[∑_b ∑_c unexclPairWeight] ≤ p2RHS + 3 cutMoment 4`.** -/
theorem lintegral_tsum_tsum_unexclPairWeight_le (r : ℝ) :
    ∫⁻ ω, (∑' b : M.V, ∑' c : M.V, unexclPairWeight M r ω (0 : M.V) b c) ∂(M.cutLaw r)
      ≤ M.p2RHS r + 3 * M.cutMoment 4 r := by
  calc ∫⁻ ω, (∑' b : M.V, ∑' c : M.V, unexclPairWeight M r ω (0 : M.V) b c) ∂(M.cutLaw r)
      ≤ ∫⁻ ω, (PivotFlux.p2PaperSum M r ω + 3 * clusterVol ω (0 : M.V) ^ 4)
          ∂(M.cutLaw r) :=
        lintegral_mono fun ω => tsum_tsum_unexclPairWeight_le M r ω
    _ = (∫⁻ ω, PivotFlux.p2PaperSum M r ω ∂(M.cutLaw r)) +
          ∫⁻ ω, (3 : ℝ≥0∞) * clusterVol ω (0 : M.V) ^ 4 ∂(M.cutLaw r) :=
        lintegral_add_left (M.measurable_p2PaperSum r) _
    _ = M.p2RHS r + 3 * M.cutMoment 4 r := by
        rw [PivotFlux.lintegral_p2PaperSum_eq_p2RHS,
          lintegral_const_mul (3 : ℝ≥0∞) ((measurable_clusterVol (0 : M.V)).pow_const 4)]
        rfl

/-! ## 4. The edge sum of the closed (unexcluded) ghost means -/

/-- **`∑_e E[unexclEdgeWeight(· \\ {e}) 0 e] ≤ p2RHS + 3 cutMoment 4`.**  This is the
`p = 2` window mass estimate, in `ℝ≥0∞`, with no finiteness hypothesis. -/
theorem tsum_lintegral_unexclEdgeWeight_sdiff_le (r : ℝ) :
    (∑' e : Sym2 M.V, ∫⁻ ω, unexclEdgeWeight M r (ω \ {e}) (0 : M.V) e ∂(M.cutLaw r))
      ≤ M.p2RHS r + 3 * M.cutMoment 4 r := by
  calc (∑' e : Sym2 M.V, ∫⁻ ω, unexclEdgeWeight M r (ω \ {e}) (0 : M.V) e ∂(M.cutLaw r))
      ≤ ∑' e : Sym2 M.V, ∫⁻ ω, unexclEdgeWeight M r ω (0 : M.V) e ∂(M.cutLaw r) :=
        ENNReal.tsum_le_tsum fun e =>
          lintegral_mono fun ω => unexclEdgeWeight_sdiff_le M r ω (0 : M.V) e
    _ = ∫⁻ ω, ∑' e : Sym2 M.V, unexclEdgeWeight M r ω (0 : M.V) e ∂(M.cutLaw r) :=
        (lintegral_tsum fun e =>
          (measurable_unexclEdgeWeight M r (0 : M.V) e).aemeasurable).symm
    _ = ∫⁻ ω, (∑' b : M.V, ∑' c : M.V, unexclPairWeight M r ω (0 : M.V) b c)
          ∂(M.cutLaw r) := by
        simp only [tsum_unexclEdgeWeight_eq]
    _ ≤ M.p2RHS r + 3 * M.cutMoment 4 r := lintegral_tsum_tsum_unexclPairWeight_le M r

/-- The total edge mass is finite as soon as the fourth cutoff moment is. -/
theorem p2RHS_add_three_cutMoment_four_ne_top (r : ℝ) (h4 : M.cutMoment 4 r ≠ ⊤) :
    M.p2RHS r + 3 * M.cutMoment 4 r ≠ ⊤ :=
  ENNReal.add_ne_top.mpr
    ⟨M.p2RHS_ne_top_of_fourth h4, ENNReal.mul_ne_top (by norm_num) h4⟩

/-- **Every single edge has a finite unexcluded ghost mean.** -/
theorem lintegral_unexclEdgeWeight_sdiff_ne_top (r : ℝ) (h4 : M.cutMoment 4 r ≠ ⊤)
    (e : Sym2 M.V) :
    ∫⁻ ω, unexclEdgeWeight M r (ω \ {e}) (0 : M.V) e ∂(M.cutLaw r) ≠ ⊤ :=
  ne_top_of_le_ne_top (M.p2RHS_add_three_cutMoment_four_ne_top r h4)
    (le_trans
      (ENNReal.le_tsum
        (f := fun e : Sym2 M.V =>
          ∫⁻ ω, unexclEdgeWeight M r (ω \ {e}) (0 : M.V) e ∂(M.cutLaw r)) e)
      (tsum_lintegral_unexclEdgeWeight_sdiff_le M r))

/-! ## 5. The cubic merge majorant is integrable -/

/-- The second cutoff moment is dominated by the fourth, because `1 ≤ |K_0|`. -/
theorem cutMoment_two_le_cutMoment_four (r : ℝ) : M.cutMoment 2 r ≤ M.cutMoment 4 r :=
  lintegral_mono fun ω =>
    pow_le_pow_right₀ (E1Sign.one_le_clusterVol M ω (0 : M.V)) (by norm_num)

/-- **`∫ bigEdge e ≤ 8 cutMoment 2`**: the cubic merge majorant `2|K_0|² + 3|K_x|² + 3|K_y|²` has
mean `8` cutoff second moments by translation invariance of the cutoff law. -/
theorem lintegral_bigEdge_le (r : ℝ) (e : Sym2 M.V) :
    ∫⁻ ω, bigEdge M ω e ∂(M.cutLaw r) ≤ 8 * M.cutMoment 2 r := by
  induction e using Sym2.ind with
  | h x y =>
    rw [show (fun ω : Config M.V => bigEdge M ω s(x, y)) = fun ω => bigPair M ω x y from
      funext fun ω => bigEdge_mk M ω x y]
    simp only [bigPair]
    have hm1 : Measurable fun ω : Config M.V =>
        2 * clusterVol ω (0 : M.V) ^ 2 + 3 * clusterVol ω x ^ 2 :=
      (((measurable_clusterVol (0 : M.V)).pow_const 2).const_mul 2).add
        (((measurable_clusterVol x).pow_const 2).const_mul 3)
    have h0 : ∫⁻ ω : Config M.V, 2 * clusterVol ω (0 : M.V) ^ 2 ∂(M.cutLaw r)
        = 2 * M.cutMoment 2 r := by
      rw [lintegral_const_mul (2 : ℝ≥0∞) ((measurable_clusterVol (0 : M.V)).pow_const 2),
        M.lintegral_clusterVol_pow_vertex r (0 : M.V) 2]
    have hx : ∫⁻ ω : Config M.V, 3 * clusterVol ω x ^ 2 ∂(M.cutLaw r)
        = 3 * M.cutMoment 2 r := by
      rw [lintegral_const_mul (3 : ℝ≥0∞) ((measurable_clusterVol x).pow_const 2),
        M.lintegral_clusterVol_pow_vertex r x 2]
    have hy : ∫⁻ ω : Config M.V, 3 * clusterVol ω y ^ 2 ∂(M.cutLaw r)
        = 3 * M.cutMoment 2 r := by
      rw [lintegral_const_mul (3 : ℝ≥0∞) ((measurable_clusterVol y).pow_const 2),
        M.lintegral_clusterVol_pow_vertex r y 2]
    rw [lintegral_add_left hm1,
      lintegral_add_left (((measurable_clusterVol (0 : M.V)).pow_const 2).const_mul 2),
      h0, hx, hy]
    rw [show 2 * M.cutMoment 2 r + 3 * M.cutMoment 2 r + 3 * M.cutMoment 2 r
      = 8 * M.cutMoment 2 r from by ring]

/-- The same bound at the closed configuration `ω \ {e}`. -/
theorem lintegral_bigEdge_sdiff_le (r : ℝ) (e : Sym2 M.V) :
    ∫⁻ ω, bigEdge M (ω \ {e}) e ∂(M.cutLaw r) ≤ 8 * M.cutMoment 2 r :=
  le_trans
    (lintegral_mono fun ω =>
      bigEdge_mono M (γ := ω \ {e}) (γ' := ω) (fun _ ha => Set.mem_of_mem_sdiff ha) e)
    (lintegral_bigEdge_le M r e)

/-! ## 6. Finiteness and integrability of the envelope -/

/-- **The envelope has a finite mean at every edge.**  On the differentiating support it is the
unexcluded ghost (bounded in total by `p2RHS + 3 cutMoment 4`), and off it the cubic majorant
(bounded by `8 cutMoment 2`). -/
theorem lintegral_envelopeE_le (r : ℝ) (e : Sym2 M.V) :
    ∫⁻ ω, envelopeE M r e ω ∂(M.cutLaw r)
      ≤ (M.p2RHS r + 3 * M.cutMoment 4 r) + 8 * M.cutMoment 2 r := by
  have hmeasA : Measurable fun ω : Config M.V =>
      unexclEdgeWeight M r (ω \ {e}) (0 : M.V) e :=
    (measurable_unexclEdgeWeight M r (0 : M.V) e).comp
      (PercLib.Probability.measurable_diff_singleton e)
  have hA : ∫⁻ ω, unexclEdgeWeight M r (ω \ {e}) (0 : M.V) e ∂(M.cutLaw r)
      ≤ M.p2RHS r + 3 * M.cutMoment 4 r :=
    le_trans
      (ENNReal.le_tsum
        (f := fun e : Sym2 M.V =>
          ∫⁻ ω, unexclEdgeWeight M r (ω \ {e}) (0 : M.V) e ∂(M.cutLaw r)) e)
      (tsum_lintegral_unexclEdgeWeight_sdiff_le M r)
  have hB : ∫⁻ ω, (if M.cutEdgeDeriv r e = 0 then bigEdge M (ω \ {e}) e else 0)
        ∂(M.cutLaw r) ≤ 8 * M.cutMoment 2 r := by
    refine le_trans (lintegral_mono fun ω => ?_) (lintegral_bigEdge_sdiff_le M r e)
    split_ifs with h
    · exact le_rfl
    · exact zero_le
  simp only [envelopeE]
  rw [lintegral_add_left hmeasA]
  exact add_le_add hA hB

/-- The envelope's `ℝ≥0∞` mean is finite under a finite fourth cutoff moment. -/
theorem lintegral_envelopeE_ne_top (r : ℝ) (h4 : M.cutMoment 4 r ≠ ⊤) (e : Sym2 M.V) :
    ∫⁻ ω, envelopeE M r e ω ∂(M.cutLaw r) ≠ ⊤ := by
  refine ne_top_of_le_ne_top ?_ (lintegral_envelopeE_le M r e)
  exact ENNReal.add_ne_top.mpr
    ⟨M.p2RHS_add_three_cutMoment_four_ne_top r h4,
      ENNReal.mul_ne_top (by norm_num)
        (ne_top_of_le_ne_top h4 (cutMoment_two_le_cutMoment_four M r))⟩

/-- **The envelope is integrable at every edge.** -/
theorem integrable_envelope (r : ℝ) (h4 : M.cutMoment 4 r ≠ ⊤) (e : Sym2 M.V) :
    Integrable (M.envelope r e) (M.cutLaw r) := by
  refine ⟨(measurable_envelope M r e).aestronglyMeasurable, ?_⟩
  rw [hasFiniteIntegral_iff_ofReal (f := M.envelope r e)
    (Filter.Eventually.of_forall fun ω => ENNReal.toReal_nonneg)]
  exact lt_of_le_of_lt (lintegral_mono fun ω => ENNReal.ofReal_toReal_le)
    (Ne.lt_top (M.lintegral_envelopeE_ne_top r h4 e))

/-- The mean of the envelope, as the `toReal` of its `ℝ≥0∞` mean. -/
theorem integral_envelope_eq_toReal (r : ℝ) (h4 : M.cutMoment 4 r ≠ ⊤) (e : Sym2 M.V) :
    ∫ ω, M.envelope r e ω ∂(M.cutLaw r)
      = (∫⁻ ω, envelopeE M r e ω ∂(M.cutLaw r)).toReal :=
  integral_toReal (measurable_envelopeE M r e).aemeasurable
    (ae_lt_top (measurable_envelopeE M r e) (M.lintegral_envelopeE_ne_top r h4 e))

/-! ## 7. The coefficient-weighted edge bound -/

/-- **`2 |cutEdgeDeriv r e| ∫ envelope_e ≤ 2 coeffRHS r · E[unexclEdgeWeight(· \\ {e}) 0 e]`.**

On the differentiating support the envelope is the unexcluded ghost, so its mean is the closed
ghost mean; off it the left side vanishes.  The coefficient enters only through
`abs_cutEdgeDeriv_le`, which already contains the `cutEdgeClosedWeight ≤ 1` factor. -/
theorem two_deriv_mul_integral_envelope_le (r : ℝ) (hr : 0 < r) (h4 : M.cutMoment 4 r ≠ ⊤)
    (e : Sym2 M.V) :
    2 * (|M.cutEdgeDeriv r e| * ∫ ω, M.envelope r e ω ∂(M.cutLaw r))
      ≤ 2 * M.coeffRHS r *
          (∫⁻ ω, unexclEdgeWeight M r (ω \ {e}) (0 : M.V) e ∂(M.cutLaw r)).toReal := by
  by_cases h : M.cutEdgeDeriv r e = 0
  · simp only [h, abs_zero, zero_mul, mul_zero]
    exact mul_nonneg (mul_nonneg (by norm_num) (M.coeffRHS_nonneg hr)) ENNReal.toReal_nonneg
  · have hcongr : ∫⁻ ω, envelopeE M r e ω ∂(M.cutLaw r)
        = ∫⁻ ω, unexclEdgeWeight M r (ω \ {e}) (0 : M.V) e ∂(M.cutLaw r) :=
      lintegral_congr_ae (Filter.Eventually.of_forall fun ω => envelopeE_eq_of_support M r e ω h)
    have hint : ∫ ω, M.envelope r e ω ∂(M.cutLaw r)
        = (∫⁻ ω, unexclEdgeWeight M r (ω \ {e}) (0 : M.V) e ∂(M.cutLaw r)).toReal := by
      rw [M.integral_envelope_eq_toReal r h4 e, hcongr]
    rw [hint]
    calc 2 * (|M.cutEdgeDeriv r e| *
          (∫⁻ ω, unexclEdgeWeight M r (ω \ {e}) (0 : M.V) e ∂(M.cutLaw r)).toReal)
        ≤ 2 * (M.coeffRHS r *
            (∫⁻ ω, unexclEdgeWeight M r (ω \ {e}) (0 : M.V) e ∂(M.cutLaw r)).toReal) := by
          gcongr
          exact M.abs_cutEdgeDeriv_le hr e
      _ = 2 * M.coeffRHS r *
            (∫⁻ ω, unexclEdgeWeight M r (ω \ {e}) (0 : M.V) e ∂(M.cutLaw r)).toReal := by
          ring

/-! ## 8. Summability of the coefficient-weighted means -/

/-- **The coefficient-weighted means of the envelope are summable.**  This is exactly the
summability hypothesis of `FluxConv.Insertion.tendsto_windowFlux_of_envelope`. -/
theorem summable_two_deriv_mul_integral_envelope (r : ℝ) (hr : 0 < r)
    (h4 : M.cutMoment 4 r ≠ ⊤) :
    Summable fun e : Sym2 M.V =>
      2 * (|M.cutEdgeDeriv r e| * ∫ ω, M.envelope r e ω ∂(M.cutLaw r)) := by
  have hI : Summable fun e : Sym2 M.V =>
      (∫⁻ ω, unexclEdgeWeight M r (ω \ {e}) (0 : M.V) e ∂(M.cutLaw r)).toReal :=
    ENNReal.summable_toReal
      (ne_top_of_le_ne_top (M.p2RHS_add_three_cutMoment_four_ne_top r h4)
        (tsum_lintegral_unexclEdgeWeight_sdiff_le M r))
  refine Summable.of_nonneg_of_le (fun e => ?_) (fun e => ?_) (hI.mul_left (2 * M.coeffRHS r))
  · have hnn : 0 ≤ ∫ ω, M.envelope r e ω ∂(M.cutLaw r) :=
      integral_nonneg fun ω => envelope_nonneg M r e ω
    exact mul_nonneg (by norm_num) (mul_nonneg (abs_nonneg _) hnn)
  · exact M.two_deriv_mul_integral_envelope_le r hr h4 e

/-! ## 9. The fixed-radius limit -/

/-- **`hfluxConv` at a fixed radius.**  A finite fourth cutoff moment gives the fixed-radius
window-flux convergence along every monotone exhausting family of finite edge windows:

`M.windowFlux (S n) r → M.rhsScalarTwo r`.

Both residual hypotheses of the landed insertion theorem (`cutMassAt r 0 ≠ ⊤` and
`p2RHS r ≠ ⊤`) are derived, not assumed: `cutMassAt r 0 = cutMoment 1 r ≤ cutMoment 4 r` and
`p2RHS_ne_top_of_fourth`.  No radius derivative and no uniform-in-radius majorant is claimed. -/
theorem tendsto_windowFlux_of_cutMoment_four (r : ℝ) (hr : 0 < r)
    (h4 : M.cutMoment 4 r ≠ ⊤) (S : ℕ → Finset (Sym2 M.V)) (hSmono : Monotone S)
    (hSexh : ∀ e : Sym2 M.V, ∃ n, e ∈ S n) :
    Tendsto (fun n => M.windowFlux (S n) r) atTop (𝓝 (M.rhsScalarTwo r)) := by
  have hmom : M.cutMoment 1 r ≤ M.cutMoment 4 r :=
    lintegral_mono fun ω =>
      pow_le_pow_right₀ (E1Sign.one_le_clusterVol M ω (0 : M.V)) (by norm_num)
  have h1 : M.cutMassAt r (0 : M.V) ≠ ⊤ := by
    have h1c : M.cutMoment 1 r ≠ ⊤ := ne_top_of_le_ne_top h4 hmom
    simpa only [cutMassAt, cutMoment, pow_one] using h1c
  exact M.tendsto_windowFlux_of_envelope r hr S hSmono hSexh h1
    (M.p2RHS_ne_top_of_fourth h4) (M.envelope r)
    (fun e => M.integrable_envelope r h4 e)
    (fun e => Filter.Eventually.of_forall (envelope_nonneg M r e))
    (M.summable_two_deriv_mul_integral_envelope r hr h4)
    (fun n e => M.ae_abs_flipDiff_cutFun_le_envelope r h1 S n e)
    (fun e => M.ae_abs_flipDiff_le_envelope r h1 e)

/-- **The `hfluxConv` interface of the landed orchestration**, at positive radii.  The downstream
`Integrated/Assembly` consumes `∀ t, Tendsto (fun n => M.windowFlux (S n) t) atTop (𝓝 (M.rhsScalarTwo t))`;
this is that statement restricted to `t > 0`, which is the range on which the fixed-radius
estimate is meaningful, under the pointwise scalar input `cutMoment 4 t ≠ ⊤`.  No radius
derivative and no uniform-in-radius majorant is used. -/
theorem hfluxConv_of_cutMoment_four (S : ℕ → Finset (Sym2 M.V)) (hSmono : Monotone S)
    (hSexh : ∀ e : Sym2 M.V, ∃ n, e ∈ S n)
    (h4 : ∀ t : ℝ, 0 < t → M.cutMoment 4 t ≠ ⊤) :
    ∀ t : ℝ, 0 < t →
      Tendsto (fun n => M.windowFlux (S n) t) atTop (𝓝 (M.rhsScalarTwo t)) :=
  fun t ht => M.tendsto_windowFlux_of_cutMoment_four t ht (h4 t ht) S hSmono hSexh

end SourceModelData

end Orchestration

end PercLib.CriticalLRP

end

/-! ## Axiom audit -/

namespace PercLib.CriticalLRP.Orchestration.SourceModelData

#print axioms tsum_tsum_unexclPairWeight_le
#print axioms measurable_p2PaperSum
#print axioms lintegral_tsum_tsum_unexclPairWeight_le
#print axioms tsum_lintegral_unexclEdgeWeight_sdiff_le
#print axioms p2RHS_add_three_cutMoment_four_ne_top
#print axioms lintegral_unexclEdgeWeight_sdiff_ne_top
#print axioms cutMoment_two_le_cutMoment_four
#print axioms lintegral_bigEdge_le
#print axioms lintegral_bigEdge_sdiff_le
#print axioms lintegral_envelopeE_le
#print axioms lintegral_envelopeE_ne_top
#print axioms integrable_envelope
#print axioms integral_envelope_eq_toReal
#print axioms two_deriv_mul_integral_envelope_le
#print axioms summable_two_deriv_mul_integral_envelope
#print axioms tendsto_windowFlux_of_cutMoment_four
#print axioms hfluxConv_of_cutMoment_four

end PercLib.CriticalLRP.Orchestration.SourceModelData
