/-
Copyright (c) 2026 PercLib contributors. Released under Apache 2.0.

# Mark-space objects used for continuity of the cutoff mass

These local mark-space artifacts describe escaping a finite ball, changing
edges within it, and the threshold-null set. They are the objects supporting
continuity of the genuine SourceModelData mass; no derivative is asserted.

Reviewed and recovered from the last uncompleted packet of Ultramath
`smwtrtcqs` direction d4, member `m4`, `CutMassContinuity.lean`.
-/
module

public import PercLib.CriticalLRP.Analysis.Cutoff.Defs
public import PercLib.CriticalLRP.CutoffLimit
public import PercLib.CriticalLRP.Analysis.BallAverage
public import PercLib.CriticalLRP.CountableProduct.Compatibility
public import PercLib.CriticalLRP.CountableProduct.Marks

/-! # Escape, box-change, and mark-volume definitions -/

@[expose] public section

open scoped ENNReal

namespace PercLib.CriticalLRP.Orchestration

namespace SourceModelData

variable (M : SourceModelData)

/-- Marks for which the cluster of the origin under the cut-off at radius `r` leaves the lattice
ball of radius `R`. -/
def markEscape (r R : ℝ) : Set (Sym2 M.V → ℝ) :=
  {u | ∃ x : M.V, x ∉ M.ball R ∧ Connects (atParameter (M.cutProb r) u) 0 x}

/-- The edges with both endpoints in the lattice ball of radius `R`. -/
noncomputable def boxEdges (R : ℝ) : Finset (Sym2 M.V) :=
  (PercLib.CriticalLRP.BallAverage.ball_finite M R).toFinset.sym2

/-- Marks at which some edge *inside* the lattice ball changes its cut-off probability between
the radii `r₀` and `r`. -/
def markBoxChange (r0 r R : ℝ) : Set (Sym2 M.V → ℝ) :=
  {u | ∃ e ∈ M.boxEdges R, (M.cutProb r0 e : ℝ) ≤ u e ∧ u e < (M.cutProb r e : ℝ)}

/-- The limit of the box-change events along a decreasing family of radii: marks sitting exactly
at one of the old cut-off probabilities on an edge of the box. -/
def boxNull (r0 R : ℝ) : Set (Sym2 M.V → ℝ) :=
  {u | ∃ e ∈ M.boxEdges R, u e = (M.cutProb r0 e : ℝ)}

/-- The cluster volume of the origin as a function on the mark space. -/
noncomputable def markVol (r : ℝ) : (Sym2 M.V → ℝ) → ℝ≥0∞ :=
  fun u => clusterVol (atParameter (M.cutProb r) u) 0

end SourceModelData

end PercLib.CriticalLRP.Orchestration
