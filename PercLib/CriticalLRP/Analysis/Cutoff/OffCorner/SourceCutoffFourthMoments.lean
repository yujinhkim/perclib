/-
Copyright (c) 2026 PercLib contributors. Released under Apache 2.0.

# The fourth cut-off cluster moment from the first

`TreeExpansion.FivePoint.fourth_moment_le` bounds the fourth cluster moment of a
translation-invariant Bernoulli bond law by `15 * (∫⁻ |K|)^7`.  That is the `p = 4`
instance of the tree-graph inequality (I.2.3),
`E_β |K|^p ≤ (2p-3)!! (E_β |K|)^{2p-1}`, since `(2 * 4 - 3)!! = 15` and `2 * 4 - 1 = 7`;
the paper uses precisely this instance, `E_{β_c,r} |K|^4 ≼ (E_{β_c,r} |K|)^7`, in (I.4.9)
inside the proof of Lemma I.4.10.

This file feeds the generic bound the Definition I.1.5 cut-off kernel
`CutoffKernel.cutoffSymKernel K d r` and transfers it to the source-model vocabulary
`M.cutMoment p r` of `Analysis/Cutoff/OffCorner/SourceCutoffMoments.lean`, at the
rescaled profile `t ↦ M.K (c * t)` and radius `r / c` used there.

Everything rests on one input for the finiteness conclusions: finiteness of the *first*
cut-off moment at the same radius (the inequality itself is unconditional in `ℝ≥0∞`).
No statement about general `p` is made, and the uncut power-law theorem
`latticeLongRange_fourth_moment_ne_top_of_firstMoment` is not used.  For the source
witness, whose norm is `ρ v = 2 ‖v‖∞`, the scale is `c = 2`.
-/
module

public import PercLib.CriticalLRP.Correlation.FourthMoment.Bridge
public import PercLib.CriticalLRP.Correlation.FourthMoment.MixedK2.Transport
public import PercLib.CriticalLRP.Analysis.Cutoff.OffCorner.SourceCutoffMoments
public import PercLib.CriticalLRP.MassTransportI41

/-!
# Fourth cut-off moment transfer

The generic native fourth-moment bound is instantiated at the loop-safe Definition I.1.5
cut-off kernel, where translation invariance of the bond law follows from invariance of
the kernel under simultaneous translation of both endpoints.  The resulting inequality
and its finiteness corollary are then transported along the exact law identification
`cutLaw_eq_native` / `cutMoment_eq_native`, and specialised to the explicit source
witness with normalisation constant `c = 2`.
-/

set_option autoImplicit false
set_option linter.hashCommand false

@[expose] public section

open MeasureTheory
open scoped ENNReal NNReal

namespace PercLib.CriticalLRP.TreeExpansion.Native

open PercLib.CriticalLRP
open PercLib.Percolation.Bond

/-! ## Translation invariance of the cut-off bond law -/

/-- **Translation invariance of the cut-off bond law.**  Translating both endpoints of a
pair by the same lattice vector leaves the edge-open probability
`1 - exp (-β J_r)` unchanged, because the cut-off kernel is a function of the difference
only.  This is the hypothesis `hq` consumed by `FivePoint.tau_hinv`; the two-point form
`tau π a b = tau π 0 (b - a)` is derived from it there, not assumed. -/
theorem bernoulliEdgeProb_cutoffSymKernel_shift {d : ℕ} {K : ℝ → ℝ}
    (hK : AntitoneOn K (Set.Ioi 0)) {r : ℝ} (hr : 0 < r) (β : NNReal)
    (x y g : Fin d → ℤ) :
    bernoulliEdgeProb (CutoffKernel.cutoffSymKernel K d r)
        (CutoffKernel.cutoffSymKernel_nonneg hK hr) β s(x + g, y + g) =
      bernoulliEdgeProb (CutoffKernel.cutoffSymKernel K d r)
        (CutoffKernel.cutoffSymKernel_nonneg hK hr) β s(x, y) := by
  have h := bernoulliEdgeProb_shift (CutoffKernel.cutoffSymKernel_shift K d r)
    (CutoffKernel.cutoffSymKernel_nonneg hK hr) β g s(x, y)
  simpa only [Sym2.map_mk] using h

/-! ## The native cut-off fourth moment -/

/-- **The ordinary fourth tree-moment bound at the Definition I.1.5 cut-off kernel.**
No moment-finiteness hypothesis: the inequality is valid in `ℝ≥0∞`, with the right side
infinite whenever the first moment is.  The translation-invariance input is discharged
from the kernel, not assumed. -/
theorem fourth_moment_cutoff {d : ℕ} {K : ℝ → ℝ} (hK : AntitoneOn K (Set.Ioi 0))
    {r : ℝ} (hr : 0 < r) (β : NNReal) :
    (∫⁻ ω, (Percolation.cardFun (cluster ω (0 : Fin d → ℤ))) ^ 4
        ∂(longRangeMeasure (CutoffKernel.cutoffSymKernel K d r)
          (CutoffKernel.cutoffSymKernel_nonneg hK hr) β)) ≤
      15 * (∫⁻ ω, Percolation.cardFun (cluster ω (0 : Fin d → ℤ))
        ∂(longRangeMeasure (CutoffKernel.cutoffSymKernel K d r)
          (CutoffKernel.cutoffSymKernel_nonneg hK hr) β)) ^ 7 := by
  have h := FivePoint.fourth_moment_le
    (bernoulliEdgeProb (CutoffKernel.cutoffSymKernel K d r)
      (CutoffKernel.cutoffSymKernel_nonneg hK hr) β)
    (FivePoint.tau_hinv _ (bernoulliEdgeProb_cutoffSymKernel_shift hK hr β))
  simpa only [longRangeMeasure] using h

/-- **The fourth cut-off moment is finite from the first.**  Immediate from
`fourth_moment_cutoff`: a finite first moment raised to the seventh power is finite. -/
theorem cutoff_fourthMoment_ne_top_of_firstMoment {d : ℕ} {K : ℝ → ℝ}
    (hK : AntitoneOn K (Set.Ioi 0)) {r : ℝ} (hr : 0 < r) (β : NNReal)
    (hfirst : (∫⁻ ω, Percolation.cardFun (cluster ω (0 : Fin d → ℤ))
      ∂(longRangeMeasure (CutoffKernel.cutoffSymKernel K d r)
        (CutoffKernel.cutoffSymKernel_nonneg hK hr) β)) ≠ ⊤) :
    (∫⁻ ω, (Percolation.cardFun (cluster ω (0 : Fin d → ℤ))) ^ 4
      ∂(longRangeMeasure (CutoffKernel.cutoffSymKernel K d r)
        (CutoffKernel.cutoffSymKernel_nonneg hK hr) β)) ≠ ⊤ := by
  refine ne_top_of_le_ne_top ?_ (fourth_moment_cutoff hK hr β)
  exact ENNReal.mul_ne_top (by norm_num) (ENNReal.pow_ne_top hfirst)

end PercLib.CriticalLRP.TreeExpansion.Native

namespace PercLib.CriticalLRP.Orchestration

open PercLib.CriticalLRP

/-! ## Transfer to the source-model vocabulary -/

/-- **The fourth source cut-off moment from the first, as an inequality.**  For a source
norm that is `c` times the `ℓ∞` norm, `M.cutKernel r` is literally the native cut-off
kernel with profile `t ↦ M.K (c * t)` at radius `r / c`, so the native tree bound becomes
`M.cutMoment 4 r ≤ 15 * (M.cutMoment 1 r) ^ 7`.  The domain restriction `0 < r` is
required by the law identification `cutMoment_eq_native`. -/
theorem cutMoment_four_le (M : SourceModelData) {c : ℝ} (hc : 0 < c)
    (hρ : ∀ z : M.V, M.S.ρ (toVec z) = c * (FiniteVolume.linfNorm z : ℝ)) {r : ℝ}
    (hr : 0 < r) :
    M.cutMoment 4 r ≤ 15 * (M.cutMoment 1 r) ^ 7 := by
  have hKanti : AntitoneOn (fun t => M.K (c * t)) (Set.Ioi 0) := by
    intro s hs t ht hst
    exact M.K_antitone (mul_pos hc hs) (mul_pos hc ht)
      (mul_le_mul_of_nonneg_left hst hc.le)
  have hr' : 0 < r / c := by positivity
  have h := TreeExpansion.Native.fourth_moment_cutoff (d := M.d) hKanti hr' M.betaCrit
  rw [cutMoment_eq_native M hc hρ hr 4, cutMoment_eq_native M hc hρ hr 1]
  simpa only [pow_one] using h

/-- **The fourth source cut-off moment is finite from the first.** -/
theorem cutMoment_four_ne_top_of_one (M : SourceModelData) {c : ℝ} (hc : 0 < c)
    (hρ : ∀ z : M.V, M.S.ρ (toVec z) = c * (FiniteVolume.linfNorm z : ℝ)) {r : ℝ}
    (hr : 0 < r) (h1 : M.cutMoment 1 r ≠ ⊤) :
    M.cutMoment 4 r ≠ ⊤ := by
  refine ne_top_of_le_ne_top ?_ (cutMoment_four_le M hc hρ hr)
  exact ENNReal.mul_ne_top (by norm_num) (ENNReal.pow_ne_top h1)

/-! ## The explicit source witness, `ρ v = 2 ‖v‖∞` -/

namespace Witness

/-- **`p = 4` at the source witness, from the first moment.**  The normalisation constant
is `c = 2`, the exact scale of the witness norm, not a cosmetic choice: its
nearest-neighbour cut-off radius is `2`. -/
theorem sourceModelWitness_cutMoment_four_ne_top (d : ℕ) (hd : 1 ≤ d) (α : ℝ)
    (hα : 0 < α) {r : ℝ} (hr : 0 < r)
    (h1 : (sourceModelWitness d hd α hα).cutMoment 1 r ≠ ⊤) :
    (sourceModelWitness d hd α hα).cutMoment 4 r ≠ ⊤ :=
  cutMoment_four_ne_top_of_one _ (by norm_num) (sourceModelWitness_dist_eq d hd α hα) hr h1

/-- **The fourth-moment inequality at the source witness.** -/
theorem sourceModelWitness_cutMoment_four_le (d : ℕ) (hd : 1 ≤ d) (α : ℝ)
    (hα : 0 < α) {r : ℝ} (hr : 0 < r) :
    (sourceModelWitness d hd α hα).cutMoment 4 r ≤
      15 * ((sourceModelWitness d hd α hα).cutMoment 1 r) ^ 7 :=
  cutMoment_four_le _ (by norm_num) (sourceModelWitness_dist_eq d hd α hα) hr

end Witness

end PercLib.CriticalLRP.Orchestration

/-! ## Axiom audit -/

#print axioms PercLib.CriticalLRP.TreeExpansion.Native.bernoulliEdgeProb_cutoffSymKernel_shift
#print axioms PercLib.CriticalLRP.TreeExpansion.Native.fourth_moment_cutoff
#print axioms PercLib.CriticalLRP.TreeExpansion.Native.cutoff_fourthMoment_ne_top_of_firstMoment
#print axioms PercLib.CriticalLRP.Orchestration.cutMoment_four_le
#print axioms PercLib.CriticalLRP.Orchestration.cutMoment_four_ne_top_of_one
#print axioms PercLib.CriticalLRP.Orchestration.Witness.sourceModelWitness_cutMoment_four_ne_top
#print axioms PercLib.CriticalLRP.Orchestration.Witness.sourceModelWitness_cutMoment_four_le
