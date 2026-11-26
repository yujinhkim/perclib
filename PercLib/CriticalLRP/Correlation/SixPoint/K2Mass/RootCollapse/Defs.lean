/-
Swarm `smwxii2d9`, member `m3`, direction `d1` (`ROOT-CLASS-COLLAPSE`).

Definitions for the **root-class collapse** of the `p = 5`, `k = 2` shape masses.

`SixPoint.pat : Fin 15 → (Fin 5 → Fin 5)` assigns the five comb terms of the six-terminal
shape to the vector slots `![x, y, z, w, q]`; the sixth terminal `t` is slot `5` and is not
part of the pattern.  `SixShape` therefore reads the comb leaves of pattern `k` as the vector

  `fun i => slotVec x u (pat k i)`,   `slotVec x u = ![x, u 0, u 1, u 2, u 3]`,

with `u = ![y, z, w, q, t]` the five summed terminals.  The point of these definitions is that
the *mass* `shapeMass π x k j y z w q r` only sees the pattern through that leaf vector, and
the total `shapeTotal` is a single sum over all `u : Fin 5 → V`.  Permuting the five summed
coordinates is then one application of `SixPoint.TwoJointEval.tsum_fin5_perm`, which is how the
fifteen labelled patterns are collapsed onto the two root classes without any new hypothesis.
-/
module

public import PercLib.CriticalLRP.Correlation.SixPoint.K2Mass.Main

/-!
# The leaf tuple of a labelled pattern and the collapsed mass

Nothing here is a new mathematical hypothesis: `leafMass` is the shape event of
`K2Mass.shapeMass` written as a function of the leaf tuple and the sixth terminal, and
`shapeTotal5` is `K2Mass.shapeTotal` with the five terminal sums bundled into `Fin 5 → V`.
-/

open Set MeasureTheory
open scoped ENNReal BigOperators
open PercLib.Percolation.Bond
open PercLib.CriticalLRP.TreeExpansion.FivePoint
open PercLib.CriticalLRP.TreeExpansion.SixPoint

@[expose] public section

namespace PercLib.CriticalLRP.TreeExpansion.SixPoint.K2Mass

variable {V : Type*}

/-- The five comb slots with the root pinned in slot `0`: `slotVec x u = ![x, u 0, u 1, u 2, u 3]`.
The five terminal coordinates `u` are `![y, z, w, q, t]`, so `slotVec` drops the sixth terminal
`u 4 = t` and puts the (fixed) root `x` in slot `0`. -/
def slotVec (x : V) (u : Fin 5 → V) : Fin 5 → V := ![x, u 0, u 1, u 2, u 3]

@[simp] theorem slotVec_zero (x : V) (u : Fin 5 → V) : slotVec x u 0 = x := rfl
@[simp] theorem slotVec_one (x : V) (u : Fin 5 → V) : slotVec x u 1 = u 0 := rfl
@[simp] theorem slotVec_two (x : V) (u : Fin 5 → V) : slotVec x u 2 = u 1 := rfl
@[simp] theorem slotVec_three (x : V) (u : Fin 5 → V) : slotVec x u 3 = u 2 := rfl
@[simp] theorem slotVec_four (x : V) (u : Fin 5 → V) : slotVec x u 4 = u 3 := rfl

/-- **The mass of one six-terminal shape event, as a function of the comb leaves.**  `L` is the
tuple of the five comb leaves in slot order and `t` the sixth terminal; the four internal
witnesses `c, u, v, w'` are summed inside the measure, exactly as in `K2Mass.shapeMass`. -/
noncomputable def leafMass (π : Sym2 V → unitInterval) (j : Fin 7) (L : Fin 5 → V) (t : V) :
    ℝ≥0∞ :=
  law π (⋃ c : V, ⋃ u : V, ⋃ v : V, ⋃ w' : V,
    {ω : PercLib.CriticalLRP.Config V |
      CombSystem (PercLib.CriticalLRP.openGraph ω) (L 0) (L 1) (L 2) (L 3) (L 4) t u v w' c j})

/-- **The total mass of shape `(k, j)` as one sum over the five free terminals.**  This is
`shapeTotal` with the five nested sums over `y, z, w, q, t` bundled into a single sum over
`Fin 5 → V`; only in this form can the pattern `pat k` be absorbed into a coordinate
permutation of the summation index. -/
noncomputable def shapeTotal5 (π : Sym2 V → unitInterval) (x : V) (k : Fin 15) (j : Fin 7) :
    ℝ≥0∞ :=
  ∑' u : Fin 5 → V, leafMass π j (fun i => slotVec x u (pat k i)) (u 4)

end PercLib.CriticalLRP.TreeExpansion.SixPoint.K2Mass
