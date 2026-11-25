/-
Copyright (c) 2026 PercLib contributors. Released under Apache 2.0.

Critical LRP I, `p = 2`: the source power-law coefficient and its compact-window bound.

Swarm `smwvfwkks`, member `m2`, direction (C).  Independently built definition layer.
-/
module

public import PercLib.CriticalLRP.Analysis.Cutoff.SecondMoment.Integrated.Completion
public import PercLib.CriticalLRP.Analysis.Cutoff.CornerRadii.Defs
public import PercLib.CriticalLRP.Analysis.Cutoff.OffCorner.PowerLawDeriv

/-!
# The source coefficient `β_c (-J'(r))` as an explicit power

`SourceModelData.coeffRHS r = β_c (-K'(r))` is the scalar coefficient of the `p = 2` radius
identity, and `rhsScalarTwo r = coeffRHS r * (p2RHS r).toReal` its right-hand side.  For the
explicit power-law witness `sourceModelWitness d hd α hα` (Hutchcroft, *Critical long-range
percolation I*, Definition I.1.3 with logarithmic error `δ ≡ 0`) the derivative is
`K'(r) = -r^{-d-α-1}` at every positive radius, so the coefficient is the pure power
`β_c r^{-d-α-1}`.

This file names that power, and the exact supremum `|β_c| a^{-d-α-1}` of its modulus on the
halfline `[a, ∞)` with `a > 0`, so that the coefficient bound consumed by
`SecondMoment/Integrated/Assembly` can be stated as an identity in the source's own constants
rather than as an abstract `C`.  No theorem is asserted here; every statement is in `Main.lean`.
-/

set_option autoImplicit false
set_option linter.style.longLine false

@[expose] public section

noncomputable section

namespace PercLib.CriticalLRP.Orchestration.Witness

open PercLib.CriticalLRP.Orchestration

/-- The **source power-law coefficient** `β r^{-d-α-1}`.  For the kernel of Definition I.1.3 with
`δ ≡ 0` and derivative `K'(r) = -r^{-d-α-1}`, this is exactly `β |J'(r)|`. -/
noncomputable def powLawCoeff (β : ℝ) (d : ℕ) (α r : ℝ) : ℝ :=
  β * r ^ (-(d : ℝ) - α - 1)

/-- The **compact-window coefficient bound** `|β| a^{-d-α-1}`.  For `a > 0` the modulus
`r ↦ |β| r^{-d-α-1}` is decreasing on `(0, ∞)`, so this is its exact supremum on `[a, ∞)`. -/
noncomputable def powLawCoeffBound (β : ℝ) (d : ℕ) (α a : ℝ) : ℝ :=
  |β| * a ^ (-(d : ℝ) - α - 1)

end PercLib.CriticalLRP.Orchestration.Witness

/-! ## A canonical exhaustive edge-window family of the witness lattice

The witness graph is `ℤ^d` with the norm `ρ(v) = 2‖v‖`.  The theorem layer needs a monotone family
of finite edge windows exhausting `Sym2 (Fin d → ℤ)`; the boxes `[-n, n]^d` supply one explicitly,
so that the flux hypotheses of the integrated assembly can be stated for a fixed family instead of
an arbitrary one. -/

namespace PercLib.CriticalLRP.Orchestration.Witness

/-- The vertex box `[-n, n]^d` of the witness lattice `ℤ^d`, as a finset. -/
noncomputable def boxVerts (d : ℕ) (n : ℕ) : Finset (Fin d → ℤ) :=
  Fintype.piFinset fun _ => Finset.Icc (-(n : ℤ)) (n : ℤ)

/-- The **canonical finite edge window** of the witness model: all pairs of vertices of the box
`[-n, n]^d`.  These windows are monotone in `n` and exhaust the edge set `Sym2 (Fin d → ℤ)`. -/
noncomputable def boxEdges (d : ℕ) (n : ℕ) : Finset (Sym2 (Fin d → ℤ)) :=
  (boxVerts d n).sym2

end PercLib.CriticalLRP.Orchestration.Witness

/-! ## Radii attained by source vertices

The positive-`r` equivalence between off-sphere and off-corner, countability and the
almost-everywhere off-corner derivative are proved in `AlmostEverywhere.lean`. -/

namespace PercLib.CriticalLRP.Orchestration.SourceModelData

/-- The radii attained by the source norm at some lattice vertex, including the origin. -/
def sphereRadii (M : SourceModelData) : Set ℝ :=
  Set.range fun y : M.V => M.S.ρ (toVec y)

/-- The off-sphere condition, negating that a source vertex has radius exactly `r`. -/
def OffSphere (M : SourceModelData) (r : ℝ) : Prop := r ∉ M.sphereRadii

end PercLib.CriticalLRP.Orchestration.SourceModelData

end
