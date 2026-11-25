module

public import PercLib.CriticalLRP.Analysis.Cutoff.ConnMassRegularity.Main

/-!
# Strict pair-mass integrands and general-base escape events

Definitions for the pair-mass continuity proof. The strict pair-mass window is the left-limit
carrier; escape events take arbitrary roots and finite unions of roots. No theorem conclusion
or moment-finiteness assertion is part of this definition layer.
-/

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

/-- The mark-space integrand of `E1Sign.pairMass M r`. -/
noncomputable def pairMarkFun (r : ℝ) : (Sym2 M.V → ℝ) → ℝ≥0∞ :=
  fun u => M.markVol r u *
    ∑ y ∈ E1Sign.ballF M r, clusterVol (atParameter (M.cutProb r) u) y

/-- The mark-space integrand of the *strict*-window pair mass. -/
noncomputable def pairMarkFunLt (r : ℝ) : (Sym2 M.V → ℝ) → ℝ≥0∞ :=
  fun u => M.markVol r u *
    ∑ y ∈ M.ballFLt r, clusterVol (atParameter (M.cutProb r) u) y

/-- The strict-window pair mass: the left limit of `E1Sign.pairMass` at `r`. -/
noncomputable def pairMassLt (r : ℝ) : ℝ≥0∞ :=
  ∫⁻ u, M.pairMarkFunLt r u ∂(markMeasure M.V)

/-- Marks for which the cut-off cluster of `v` leaves the lattice ball of radius `R`.  This is the
general-base version of `SourceModelData.markEscape`, which is stated at the origin only. -/
def markEscapeAt (r R : ℝ) (v : M.V) : Set (Sym2 M.V → ℝ) :=
  {u | ∃ x : M.V, x ∉ M.ball R ∧ Connects (atParameter (M.cutProb r) u) v x}

/-- Marks at which the cut-off cluster of *some* point of the finite set `s` leaves the ball of
radius `R`. -/
def markEscapeUnion (r R : ℝ) (s : Finset M.V) : Set (Sym2 M.V → ℝ) :=
  ⋃ v ∈ (s : Set M.V), M.markEscapeAt r R v

end SourceModelData

end PercLib.CriticalLRP.Orchestration
