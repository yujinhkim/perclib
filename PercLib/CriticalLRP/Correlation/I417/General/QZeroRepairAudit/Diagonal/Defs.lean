/-
Ultramath swarm `smwznoz6j`, member `m3`, direction `d9` (campaign direction (J)).

Copyright (c) 2026 PercLib contributors. Released under Apache 2.0.

Accepted and independently rebuilt from Ultramath `smwznoz6j`, member m3.
Latest independent rebuild at production HEAD `16d9f2aa1e83afeda3fc66117e38ed3352b2e567`; reviewed scratch source `.scratch/review-smwznoz6j/m3/Defs.lean`.

# The q = 0, p = 3 tree-graph side, and the diagonal of the covariance target

Source: Tom Hutchcroft, *Critical long-range percolation I: High effective dimension*,
arXiv:2508.18807v1, §I.2 display **(I.2.3)** (printed p. 20):

  `E_β |K|^p ≤ (2p − 3)!! (E_β |K|)^{2p−1}`   for every integer `p ≥ 1`,

read at `p = 3`: `E|K|^3 ≤ 3 (E|K|)^5`.  The sharper mixed form displayed in the Case-3
discussion (printed p. 44, from Lemma I.4.16 with `p = 3`, `k = 1`) is
`E|K|^3 ≤ 3 E|K|^2 (E|K|)^2`, which implies the `(E|K|)^5` form as soon as (I.2.3) at `p = 2`
gives `E|K|^2 ≤ (E|K|)^3`; the native expansion in production proves the `(E|K|)^5` form
directly, and that is the form used here.

Production (`PercLib.CriticalLRP.Correlation.ThirdMoment.ArmDecomposition`) proves the
native third-moment tree bound `third_moment_native` for *any* translation-invariant edge
profile on a countable abelian group.  This file instantiates it at the model's own
range-cutoff law `M.cutLaw r = edgeMeasure (M.cutProb r)` — the kernel is the model's
normalized-norm profile `radialSym M.S (cutoffProfile M.K r)`, **not** the ℓ^∞ profile of
`CutoffKernel.cutoffSymKernel` — so that the bound applies to `M.cutMoment 3 r` itself.

Everything here is unconditional: no triangle condition, no moment finiteness, no
`HasCovBound`, no star hypothesis.
-/
module

public import PercLib.CriticalLRP.Correlation.I417.General.QZeroRepairAudit.ProductGap
public import PercLib.CriticalLRP.Correlation.CutoffThirdMoment
public import PercLib.CriticalLRP.Correlation.FourthMoment.MixedK2.Transport
public import PercLib.CriticalLRP.Analysis.Cutoff.Translation
public import PercLib.CriticalLRP.Analysis.Cutoff.Defect.Defs

/-! # Tree-graph third moment at the model cutoff law -/

set_option autoImplicit false
set_option linter.unusedSectionVars false
set_option linter.hashCommand false
set_option linter.style.longLine false

@[expose] public section

noncomputable section

open MeasureTheory Measure ProbabilityTheory unitInterval Filter
open scoped ENNReal NNReal Topology BigOperators
open PercLib.CriticalLRP.TreeExpansion
open PercLib.Percolation.Bond (law tau)

namespace PercLib.CriticalLRP
namespace Orchestration
namespace SourceModelData

attribute [local instance] Classical.propDecidable

variable (M : SourceModelData)

/-! ## §1 Translation invariance of the model's cutoff profile -/

/-- The opening probability of the range-cutoff law is invariant under the edge translation
`{x,y} ↦ {x+g, y+g}`.  This is `cutKernel` invariance (`Analysis/Cutoff/Translation.lean`)
read through `bernoulliEdgeProb`. -/
theorem cutProb_shift (r : ℝ) (x y g : M.V) :
    M.cutProb r (s(x + g, y + g)) = M.cutProb r (s(x, y)) := by
  have h := M.cutEdgeProb_shift r g (s(x, y))
  rw [Sym2.map_mk] at h
  exact h

/-- The two-point function of the cutoff law is translation invariant, in the `ℝ≥0∞`
form `tau` consumed by the native tree expansion. -/
theorem cutProb_tau_hinv (r : ℝ) :
    ∀ a b : M.V, tau (M.cutProb r) a b = tau (M.cutProb r) 0 (b - a) :=
  FivePoint.tau_hinv (M.cutProb r) (fun x y g => M.cutProb_shift r x y g)

/-- The model's cutoff law is the bond law of its cutoff opening profile. -/
theorem cutLaw_eq_law_cutProb (r : ℝ) :
    M.cutLaw r = Percolation.Bond.law (M.cutProb r) :=
  edgeMeasure_eq_law (M.cutProb r)

/-- `cardFun` is the model's cluster-volume functional, so the `p`-th cutoff moment is the
`p`-th moment of `cardFun (cluster · 0)` under the cutoff law. -/
theorem lintegral_cardFun_pow_eq_cutMoment (r : ℝ) (p : ℕ) :
    ∫⁻ ω, Percolation.cardFun (cluster ω (0 : M.V)) ^ p ∂(M.cutLaw r) = M.cutMoment p r := by
  simp only [cutMoment, Percolation.cardFun_eq_encard, clusterVol_eq_encard]

/-! ## §2 The third cutoff moment is at most `3 χ^5` -/

/-- **The tree-graph inequality (I.2.3) at `p = 3`, at the model's cutoff law:**
`E_{β_c,r}|K|^3 ≤ 3 (E_{β_c,r}|K|)^5`.

The constant `3 = (2·3 − 3)!!` counts the plane binary trees with three labelled non-root
leaves.  This is the `(E|K|)^5` form of (I.2.3); the sharper mixed form
`E|K|^3 ≤ 3 E|K|^2 (E|K|)^2` of the source's Case-3 discussion would additionally need
(I.2.3) at `p = 2`.  No finiteness hypothesis is used. -/
theorem cutMoment_three_le_three_mul_pow_five (r : ℝ) :
    M.cutMoment 3 r ≤ 3 * M.cutMoment 1 r ^ 5 := by
  have h := TreeExpansion.Native.third_moment_native (V := M.V) (M.cutProb r)
    (M.cutProb_tau_hinv r)
  rw [← M.cutLaw_eq_law_cutProb r] at h
  have h1 : ∫⁻ ω, Percolation.cardFun (cluster ω (0 : M.V)) ∂(M.cutLaw r) = M.cutMoment 1 r := by
    simpa only [pow_one] using M.lintegral_cardFun_pow_eq_cutMoment r 1
  rwa [M.lintegral_cardFun_pow_eq_cutMoment r 3, h1] at h

/-! ## §3 A weight-`1` form of the additive star target -/

/-- **The additive star repair with the `χ^5` correction weighted by `1` instead of by
`T_{β_c,r}(0,y)`.**  This is the weakest form of the `q = 0`, `p = 3` star target that still
keeps the source's two diagram terms: it asks only for
`E[1(y ∈ K_0)|K_0|³] ≤ C₃ T³(0,y) χ⁴ + C₄ T⁴(0,y) χ³ + C₅ χ^5`.

`QZeroRepairAudit.SourceModelData.HasAdditiveStar` is the case where the last term carries the
weight `T(0,y)`; since `T(0,y) ≤ 1`, that target implies this one for `C₅ ≥ 0`
(`hasUniformWeightStar_of_hasAdditiveStar`), and this file proves the `(C₃,C₄,C₅) = (1,2,3)`
instance unconditionally. -/
def HasUniformWeightStar (C3 C4 C5 : ℝ) : Prop :=
  ∀ r : ℝ, 1 ≤ r → ∀ y : M.V,
    (M.connCubeVertexMass r y).toReal ≤
      C3 * I418C.polyK (M.cutTwoPoint r) 3 (0 : M.V) y * M.chiReal r ^ 4 +
        C4 * I418C.polyK (M.cutTwoPoint r) 4 (0 : M.V) y * M.chiReal r ^ 3 +
        C5 * M.chiReal r ^ 5

/-- `HasAdditiveStar` implies the weight-`1` form, because `T_{β_c,r}(0,y) ≤ 1`. -/
theorem hasUniformWeightStar_of_hasAdditiveStar {C3 C4 C5 : ℝ} (hC5 : 0 ≤ C5)
    (h : PercLib.CriticalLRP.QZeroRepairAudit.SourceModelData.HasAdditiveStar M C3 C4 C5) :
    M.HasUniformWeightStar C3 C4 C5 := by
  intro r hr y
  have hT := M.cutTwoPoint_le_one r (0 : M.V) y
  have hχ : (0 : ℝ) ≤ M.chiReal r := ENNReal.toReal_nonneg
  have hχ5 : (0 : ℝ) ≤ M.chiReal r ^ 5 := pow_nonneg hχ 5
  have hle : C5 * M.cutTwoPoint r (0 : M.V) y * M.chiReal r ^ 5 ≤ C5 * M.chiReal r ^ 5 := by
    have h1 : C5 * M.cutTwoPoint r (0 : M.V) y ≤ C5 * 1 := by
      exact mul_le_mul_of_nonneg_left hT hC5
    calc C5 * M.cutTwoPoint r (0 : M.V) y * M.chiReal r ^ 5
        ≤ C5 * 1 * M.chiReal r ^ 5 := mul_le_mul_of_nonneg_right h1 hχ5
      _ = C5 * M.chiReal r ^ 5 := by ring
  linarith [h r hr y]

end SourceModelData
end Orchestration
end PercLib.CriticalLRP

end

/-! ## Axiom audit -/

#print axioms PercLib.CriticalLRP.Orchestration.SourceModelData.hasUniformWeightStar_of_hasAdditiveStar
#print axioms PercLib.CriticalLRP.Orchestration.SourceModelData.cutProb_shift
#print axioms PercLib.CriticalLRP.Orchestration.SourceModelData.cutProb_tau_hinv
#print axioms PercLib.CriticalLRP.Orchestration.SourceModelData.cutLaw_eq_law_cutProb
#print axioms PercLib.CriticalLRP.Orchestration.SourceModelData.cutMoment_three_le_three_mul_pow_five
