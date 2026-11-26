/-
Independently rebuilt cross-check for `MarkedJoint.Relabel.Main` from `smwwxbtza`, member `m1`.
Production integration revision: `54054b7051903bd4990d0dc78cdfcb61d0676288`.
-/

module

public import PercLib.CriticalLRP.Correlation.I417.MarkedJoint.Relabel.Main
public import PercLib.CriticalLRP.Correlation.I417.MarkedJoint.Main

/-! Cross-check the relabelled polygon evaluation against the integrated marked atlas bound. -/

set_option autoImplicit false
set_option linter.unusedSectionVars false
set_option linter.style.longLine false
set_option linter.hashCommand false

open scoped ENNReal

@[expose] public section

namespace PercLib.CriticalLRP.I417MarkedRelabel

open PercLib.CriticalLRP (connSet edgeMeasure)
open PercLib.CriticalLRP.TreeExpansion

variable {W : Type*}

/-! ## Cross-check against the pending production marked package

`PercLib.CriticalLRP.I417Marked.markedAtlasBound` (the *pending* `I417Marked`/`Defs.lean`) is the
same sum as `markedAtlasSum`, only with the pin written as a raw `if` instead of a set indicator.
This file records the identity, so that the pending bound can be evaluated with the shape
relabelling of this direction. -/

theorem markedAtlasSum_eq_markedAtlasBound (π : Sym2 W → unitInterval) (x w : W) (p : ℕ) :
    markedAtlasSum π x w p = PercLib.CriticalLRP.I417Marked.markedAtlasBound π x w p := by
  classical
  refine tsum_congr fun t => tsum_congr fun φ => tsum_congr fun y => ?_
  by_cases h : y (Fin.last p) = w
  · rw [pinLast_of_mem h, ite_eq_left h, one_mul]
  · rw [pinLast_of_notMem h, ite_eq_right h, zero_mul]

/-- **The same polygon bound, but using the pending production marked atlas bound as the
starting point.**  This is the independent cross-check of the assembly step. -/
theorem jointPow_le_markedPolygonBound_via_pending {W : Type*} [Countable W] [DecidableEq W]
    (π : Sym2 W → unitInterval) (hπ : ∀ e, π e < 1) (χ : ℝ≥0∞)
    (hχ : ∀ v, ∑' y, edgeMeasure π (connSet v y) = χ) (x w : W) (p : ℕ) :
    I417Gen.jointPow π x p w ≤
      I417Marked.markedPolygonBound χ (fun u v => edgeMeasure π (connSet u v)) p x w := by
  classical
  refine (I417Marked.jointPow_le_markedAtlasBound π hπ x w p).trans (le_of_eq ?_)
  rw [← markedAtlasSum_eq_markedAtlasBound]
  rw [markedAtlasSum_eq_labelledMarkedDiagram]
  exact I417Marked.labelledMarkedDiagram_eq_polygon (fun u v => edgeMeasure π (connSet u v))
    χ hχ p x w

namespace Audit

#print axioms PercLib.CriticalLRP.I417Marked.jointPow_le_markedAtlasBound
#print axioms PercLib.CriticalLRP.I417Marked.labelEvent_markedExtend
#print axioms PercLib.CriticalLRP.I417Marked.tsum_markedExtend
#print axioms markedAtlasSum_eq_markedAtlasBound
#print axioms jointPow_le_markedPolygonBound_via_pending

end Audit

end PercLib.CriticalLRP.I417MarkedRelabel
