/-
Slot diagrams for the `k = 2` two-joint/three-single regroupings of the six-terminal arm system
at the split positions `j = 0`, `j = 5` and `j = 6`.

Swarm `smwxfstjy`, member `m2`, direction d3 (`REMAINING-SPLIT-EVALUATIONS`).

The event-level regroupings at these three split positions are the production theorems
`SixPoint.SplitPattern.combSystem_twoJointThree_zero`, `..._five` and `..._six`: each puts the
configuration in a `TwoJointThreeCert` of two joint connection events with a shared spine and
three two-point events.  Here we record, for each of the three positions, exactly the
five-factor product that fivefold BK produces, and the free-vertex slot that remains after the
witnesses which do not occur in the product have been absorbed into the events.

The factor order below is copied literally from the three certificate statements, so the slot
is the right-hand side of `twoJointThree_le` with `jointP`/`tau` notation.  The free vertices are
`v, c` at `j = 0`, `c, w` at `j = 5` and `v, w` at `j = 6`; in particular the landing point `c`
has disappeared from the product at `j = 6` and the two spine vertices `u, w` have disappeared
at `j = 0`.  Nothing is evaluated in this file.
-/
module

public import PercLib.CriticalLRP.Correlation.SixPoint.TwoJointEval.Five

/-!
# Split evaluation and event bridges (`j = 0,5,6`)

The specified root placement is part of each evaluation. Other splits and the final moment assembly
remain open.-/


/-!
# Slot diagrams at the split positions `0`, `5`, `6`

Definitions only; the evaluations are in `Peel.lean` and the event-level bridges in
`Bridge.lean`.
-/

open Set MeasureTheory
open scoped ENNReal BigOperators
open PercLib.Percolation.Bond
open PercLib.CriticalLRP.TreeExpansion.FivePoint

@[expose] public section

namespace PercLib.CriticalLRP.SixPoint.SplitEval

variable {V : Type*}

/-! ## Split position `j = 0`: the landing point lies on the arm `b₀ — u` -/

/-- **The `j = 0` two-joint product.**  The star at `u` is the joint pair `b₁, c` with spine `v`,
the star at `w` is the joint pair `b₃, b₄` with spine `v`, and the residual two-point factors are
`b₂ — v`, `b₀ — c` and `t — c`.

This is the right-hand side of `combSystem_twoJointThree_zero` after fivefold BK, in the
`jointP`/`tau` vocabulary: it is exactly the product
`law π (conn b₁ v ∩ conn c v) * (law π (conn b₃ v ∩ conn b₄ v) * (law π (conn b₂ v) *
(law π (conn b₀ c) * law π (conn t c))))`. -/
noncomputable def prodZero (π : Sym2 V → unitInterval) (b0 b1 b2 b3 b4 t v c : V) : ℝ≥0∞ :=
  jointP π b1 c v * (jointP π b3 b4 v * (tau π b2 v * (tau π b0 c * tau π t c)))

/-- **The `j = 0` slot.**  The two free vertices `v` and `c` of `prodZero` are summed; the six
terminals stay free.  The order `c` then `v` is the order of the union bound over the two
existential witnesses of the split. -/
noncomputable def slotZero (π : Sym2 V → unitInterval) (b0 b1 b2 b3 b4 t : V) : ℝ≥0∞ :=
  ∑' c, ∑' v, prodZero π b0 b1 b2 b3 b4 t v c

/-! ## Split position `j = 5`: the landing point lies on the spine `u — v` -/

/-- **The `j = 5` two-joint product.**  The star at `u` is the joint pair `b₀, b₁` with spine `c`,
the star at `v` is the joint pair `b₂, c` with spine `w`, and the residual two-point factors are
`b₃ — w`, `b₄ — w` and `t — c`. -/
noncomputable def prodFive (π : Sym2 V → unitInterval) (b0 b1 b2 b3 b4 t c w : V) : ℝ≥0∞ :=
  jointP π b0 b1 c * (jointP π b2 c w * (tau π b3 w * (tau π b4 w * tau π t c)))

/-- **The `j = 5` slot.**  The two free vertices `c` and `w` of `prodFive` are summed. -/
noncomputable def slotFive (π : Sym2 V → unitInterval) (b0 b1 b2 b3 b4 t : V) : ℝ≥0∞ :=
  ∑' c, ∑' w, prodFive π b0 b1 b2 b3 b4 t c w

/-! ## Split position `j = 6`: the landing point lies on the spine `v — w` -/

/-- **The `j = 6` two-joint product.**  The star at `u` is the joint pair `b₀, b₁` with spine `v`,
the star at `c` is the joint pair `v, t` with spine `w`, and the residual two-point factors are
`b₂ — v`, `b₃ — w` and `b₄ — w`. -/
noncomputable def prodSix (π : Sym2 V → unitInterval) (b0 b1 b2 b3 b4 t v w : V) : ℝ≥0∞ :=
  jointP π b0 b1 v * (jointP π v t w * (tau π b2 v * (tau π b3 w * tau π b4 w)))

/-- **The `j = 6` slot.**  The two free vertices `v` and `w` of `prodSix` are summed. -/
noncomputable def slotSix (π : Sym2 V → unitInterval) (b0 b1 b2 b3 b4 t : V) : ℝ≥0∞ :=
  ∑' v, ∑' w, prodSix π b0 b1 b2 b3 b4 t v w

/-! ## Reindexing devices for the seven nested sums

Each slot evaluations sums five terminals and two free vertices.  These permutations only say how
the seven indices of the peel order sit in the order in which the assembly's terminal sums arrive;
they carry no mathematical content. -/

/-- `j = 0`: the peel order `(v, c, b₂, b₃, b₄, b₀, t)` inside the assembly order
`(b₀, b₂, b₃, b₄, t, c, v)`. -/
def permZero : Equiv.Perm (Fin 7) := Equiv.swap 0 5 * Equiv.swap 1 6

/-- `j = 5`: the peel order `(c, w, b₃, b₄, t, b₀, b₁)` inside the assembly order
`(b₀, b₁, b₃, b₄, t, c, w)`. -/
def permFive : Equiv.Perm (Fin 7) := Equiv.swap 0 5 * Equiv.swap 1 6

/-- `j = 6`: the peel order `(v, w, b₃, b₄, b₂, b₀, b₁)` inside the assembly order
`(b₀, b₁, b₂, b₃, b₄, v, w)`. -/
def permSix : Equiv.Perm (Fin 7) := Equiv.swap 0 5 * Equiv.swap 1 6 * Equiv.swap 2 4

end PercLib.CriticalLRP.SixPoint.SplitEval
