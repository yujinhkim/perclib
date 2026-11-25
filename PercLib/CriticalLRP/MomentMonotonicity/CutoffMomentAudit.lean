/-
Copyright (c) 2026 PercLib contributors. Released under Apache 2.0.

# `hutchcroft.i.1.5.step.cutoffmoments` at the source cut-off law: what the obligation is

Source: T. Hutchcroft, *Critical long-range percolation I: High effective dimension*,
arXiv:2508.18807v1, Definition I.1.5 (`P_{β,r}`, kernel `J_r = 1(·≠·, ‖·‖ ≤ r) ∫_{‖·‖}^r |J'|`)
and §I.1.1 Theorem I.1.6 (`E_{β_c,r}|K|^p < ∞` for every `p ≥ 1`, at every finite `r`).

The obligation is recorded in the graph as `hutchcroft.i.1.5.step.cutoffmoments`; the
packet's own NOTE says it "needs a subcritical first-moment estimate plus e.g. the
tree-graph moment inequality, not merely a.s. finiteness of the cluster".  This file
proves the part of that route that is available at the source cut-off law, and pins down
exactly what a *support* bound could and could not contribute:

* `cutoff_powMoment_eq_iSup_box` — for the Definition I.1.5 kernel
  `CutoffKernel.cutoffSymKernel` (loop-safe: `J_r(x,x) = 0`) the `p`-th cluster moment at
  `P_{β,r}` is the supremum of the box moments `∫⁻ |K ∩ B_n|^p`;
* `cutoff_window_powMoment_ne_top` — each box moment is finite, with bound `|B_n|^p`;
* `cutoff_powMoment_ne_top_iff_uniform_box` — therefore the `p`-th moment is finite **iff**
  the box moments are uniformly bounded in `n`; the finite support of `J_r` gives the
  finiteness of each term and never the uniformity;
* `SourceModelData.cutMoment_ne_top_iff_uniform_box` — the same statement in the
  `Orchestration.Defs` vocabulary `M.cutMoment p r`, which is the shape used by the
  downstream roots.

The remaining inputs are named, not assumed here: subcritical finiteness of the uncut
first moment at the reduced parameter `β_c(1 − K r / K 1)` (`CutoffDominated.lintegral_
clusterVol_cutoff_ne_top`'s `hfin`) and the all-order tree-graph moment bound
(`TreeExpansion.Moment.moment_bound_expectation`, which needs `BKIncreasing` and a finite
weighted graph).  Neither is manufactured here.

No new definitions, no `sorry`, no `admit`, no `native_decide`, no custom axioms.
-/
module

public import PercLib.CriticalLRP.VolumeMoments.SecondMomentWindow
public import PercLib.CriticalLRP.CutoffDominated
public import PercLib.CriticalLRP.Orchestration.Defs
public import PercLib.CriticalLRP.MomentMonotonicity.MomentTransfer
public import PercLib.CriticalLRP.MomentMonotonicity.WindowMoments

set_option autoImplicit true

set_option linter.unusedSectionVars false
set_option linter.unusedVariables false

@[expose] public section

open MeasureTheory Measure ProbabilityTheory unitInterval
open scoped ENNReal

attribute [local instance] Classical.propDecidable

namespace PercLib.CriticalLRP.CutoffMomentAudit

open FiniteVolume CutoffKernel Hvol

variable {d : ℕ} {K : ℝ → ℝ}

/-- **The `p`-th moment at the cut-off law is the supremum of its box moments.**  Kernel
`J_r` of Definition I.1.5 (loop-safe `cutoffSymKernel`), arbitrary `p ≥ 0` as a natural
number, no finiteness or subcriticality hypothesis. -/
theorem cutoff_powMoment_eq_iSup_box (hK : AntitoneOn K (Set.Ioi 0)) {r : ℝ} (hr : 0 < r)
    (β : NNReal) (o : Fin d → ℤ) (p : ℕ) :
    (∫⁻ ω, clusterVol ω o ^ p ∂(longRangeMeasure (cutoffSymKernel K d r)
        (cutoffSymKernel_nonneg hK hr) β))
      = ⨆ n, ∫⁻ ω, clusterVolIn ω o ((box d n : Finset (Fin d → ℤ)) : Set (Fin d → ℤ)) ^ p
          ∂(longRangeMeasure (cutoffSymKernel K d r) (cutoffSymKernel_nonneg hK hr) β) :=
  lintegral_clusterVol_pow_eq_iSup_window _ o (fun n => box d n) box_cofinal (fun a b hab => box_mono hab) p

/-- **Each box moment at the cut-off law is finite** (bound `|B_n|^p`). -/
theorem cutoff_window_powMoment_ne_top (hK : AntitoneOn K (Set.Ioi 0)) {r : ℝ} (hr : 0 < r)
    (β : NNReal) (o : Fin d → ℤ) (p n : ℕ) :
    (∫⁻ ω, clusterVolIn ω o ((box d n : Finset (Fin d → ℤ)) : Set (Fin d → ℤ)) ^ p
        ∂(longRangeMeasure (cutoffSymKernel K d r) (cutoffSymKernel_nonneg hK hr) β)) ≠ ⊤ :=
  window_powMoment_ne_top _ o (box d n) p

/-- **The `p`-th cut-off moment is finite iff the box moments are uniformly bounded.**
This is the exact content of the finite-support observation: `J_r(x,y) ≠ 0` only for
`‖y − x‖_∞ ≤ r`, so every box moment is finite, but the finiteness of the full moment is
*uniformity* in the box, i.e. a percolation-theoretic statement about the range-`r` law,
not a support statement. -/
theorem cutoff_powMoment_ne_top_iff_uniform_box (hK : AntitoneOn K (Set.Ioi 0)) {r : ℝ}
    (hr : 0 < r) (β : NNReal) (o : Fin d → ℤ) (p : ℕ) :
    (∫⁻ ω, clusterVol ω o ^ p ∂(longRangeMeasure (cutoffSymKernel K d r)
        (cutoffSymKernel_nonneg hK hr) β)) ≠ ⊤ ↔
      ∃ C : ℝ≥0∞, C ≠ ⊤ ∧ ∀ n,
        (∫⁻ ω, clusterVolIn ω o ((box d n : Finset (Fin d → ℤ)) : Set (Fin d → ℤ)) ^ p
          ∂(longRangeMeasure (cutoffSymKernel K d r) (cutoffSymKernel_nonneg hK hr) β)) ≤ C :=
  powMoment_ne_top_iff_uniform_window _ o (fun n => box d n) box_cofinal (fun a b hab => box_mono hab) p

/-- The `p = 2` case of `cutoff_powMoment_eq_iSup_box` agrees with the committed
`Hvol.secondMoment_eq_iSup_box` (they are the same statement, one proved through the
connection sums, one through monotone convergence of truncated volumes). -/
example (q : Sym2 (Fin d → ℤ) → unitInterval) (x : Fin d → ℤ) :
    (∫⁻ ω, clusterVol ω x ^ 2 ∂(edgeMeasure q))
      = ⨆ n, ∫⁻ ω, clusterVolIn ω x ((box d n : Finset (Fin d → ℤ)) : Set (Fin d → ℤ)) ^ 2
          ∂(edgeMeasure q) :=
  lintegral_clusterVol_pow_eq_iSup_window q x (fun n => box d n) box_cofinal (fun a b hab => box_mono hab) 2

/-- The `p = 1` case: the first moment is the supremum of the box first moments. -/
example (q : Sym2 (Fin d → ℤ) → unitInterval) (x : Fin d → ℤ) :
    (∫⁻ ω, clusterVol ω x ∂(edgeMeasure q))
      = ⨆ n, ∫⁻ ω, clusterVolIn ω x ((box d n : Finset (Fin d → ℤ)) : Set (Fin d → ℤ))
          ∂(edgeMeasure q) := by
  simpa only [pow_one] using
    lintegral_clusterVol_pow_eq_iSup_window q x (fun n => box d n) box_cofinal (fun a b hab => box_mono hab) 1

/-! ## The same statement in the `Orchestration.Defs` vocabulary -/

open PercLib.CriticalLRP.Orchestration

-- Unfolding `M.cutLaw` to the underlying `edgeMeasure` is definitionally heavy.
/-- **The obligation `hutchcroft.i.1.5.step.cutoffmoments` is exactly a uniform-in-box
bound.**  In the source-model vocabulary, `M.cutMoment p r` is finite iff the moments of
the box intersections `|K_0 ∩ B_n|` are uniformly bounded.  Every single box moment is
finite (`cutWindowMoment_ne_top`); the uniformity is the whole obligation. -/
theorem SourceModelData.cutMoment_ne_top_iff_uniform_box (M : SourceModelData) (p : ℕ)
    (r : ℝ) (hr : 0 < r) :
    M.cutMoment p r ≠ ⊤ ↔
      ∃ C : ℝ≥0∞, C ≠ ⊤ ∧ ∀ n,
        (∫⁻ ω, clusterVolIn ω (0 : M.V) ((box M.d n : Finset M.V) : Set M.V) ^ p
          ∂(M.cutLaw r)) ≤ C := by
  have h := powMoment_ne_top_iff_uniform_window
    (q := bernoulliEdgeProb (M.cutKernel r) (M.cutKernel_nonneg r) M.betaCrit)
    (v := (0 : M.V)) (F := fun n => box M.d n) box_cofinal
    (fun a b hab => box_mono hab) p
  simpa only [SourceModelData.cutMoment, SourceModelData.cutLaw, longRangeMeasure] using h

/-- Each box moment of the source cut-off law is finite, with the bound `|B_n|^p`. -/
theorem SourceModelData.cutWindowMoment_ne_top (M : SourceModelData) (p n : ℕ) (r : ℝ) :
    (∫⁻ ω, clusterVolIn ω (0 : M.V) ((box M.d n : Finset M.V) : Set M.V) ^ p
        ∂(M.cutLaw r)) ≠ ⊤ := by
  have h := window_powMoment_ne_top
    (q := bernoulliEdgeProb (M.cutKernel r) (M.cutKernel_nonneg r) M.betaCrit)
    (v := (0 : M.V)) (box M.d n) p
  simpa only [SourceModelData.cutLaw, longRangeMeasure] using h

end PercLib.CriticalLRP.CutoffMomentAudit

/-! ## Axiom audit -/

#print axioms PercLib.CriticalLRP.CutoffMomentAudit.cutoff_powMoment_eq_iSup_box
#print axioms PercLib.CriticalLRP.CutoffMomentAudit.cutoff_window_powMoment_ne_top
#print axioms PercLib.CriticalLRP.CutoffMomentAudit.cutoff_powMoment_ne_top_iff_uniform_box
#print axioms PercLib.CriticalLRP.CutoffMomentAudit.SourceModelData.cutMoment_ne_top_iff_uniform_box
#print axioms PercLib.CriticalLRP.CutoffMomentAudit.SourceModelData.cutWindowMoment_ne_top
