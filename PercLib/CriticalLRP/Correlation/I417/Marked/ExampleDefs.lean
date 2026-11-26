/- Reuses the independently verified small marked shapes from `MarkedAtlas`. -/
module

public import PercLib.CriticalLRP.Correlation.I417.Marked.Defs
public import PercLib.CriticalLRP.TreeExpansion.AtlasRealization.MarkedAtlas.ExampleDefs
public import PercLib.CriticalLRP.TreeExpansion.AtlasRealization.MarkedAtlas.TwoLeaf

/-!
# Small labelled marked shapes

These are the same physical tree shapes classified in `MarkedAtlas`, expressed in the
namespace used by the marked-depth coefficient computations.
-/
@[expose] public section

set_option autoImplicit false
set_option linter.unusedSectionVars false
set_option linter.unusedFintypeInType false
set_option linter.unusedDecidableInType false

namespace PercLib.CriticalLRP.I417Marked

open PercLib.CriticalLRP.TreeExpansion

/-- The two-leaf tree with the ordinary arm on the left and the mark on the right. -/
noncomputable def ltOnOneLeft : LTon (Label 1) (Finset.univ : Finset (Label 1)) :=
  MarkedAtlas.markShapeP1a

/-- The two-leaf tree with the mark on the left and the ordinary arm on the right. -/
noncomputable def ltOnOneRight : LTon (Label 1) (Finset.univ : Finset (Label 1)) :=
  MarkedAtlas.markShapeP1b

/-- The two labelled orderings are genuinely different shapes. -/
theorem ltOnOneLeft_ne_right : ltOnOneLeft ≠ ltOnOneRight :=
  MarkedAtlas.markShapeP1a_ne_markShapeP1b

/-- The unique one-leaf shape at zero ordinary arms. -/
noncomputable def ltOnZeroLeaf : LTon (Label 0) (Finset.univ : Finset (Label 0)) :=
  MarkedAtlas.markShapeP0

end PercLib.CriticalLRP.I417Marked
