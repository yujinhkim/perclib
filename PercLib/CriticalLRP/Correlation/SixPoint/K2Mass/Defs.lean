/-
Swarm `smwxh86dl`, member `m3`, direction `d3` (`MOMENT-ARITHMETIC-CLOSURE`).

Definitions for the `p = 5`, `k = 2` shape-mass assembly.

The `k = 2` route to Lemma I.4.16 needs, for each of the `105 = 15 * 7` six-terminal split
shapes, a bound on the **mass** of the shape event (the five non-root terminals summed over
all of `V`).  Production at HEAD proves such mass bounds at the middle split `j = 2`
(`SixPoint.TwoJointEval.Assembly`, all fifteen labelled patterns) but nowhere else, and the
existing analytic consumers (`fifth_moment_le_of_105diagrams`,
`MixedK2.Assembly.fifth_moment_le_of_hubDiagrams`) take a per-diagram *pointwise* premise
instead, so the proved mass bounds cannot be plugged into them.

These definitions name the mass and the cost so that the assembly in `Main.lean` can consume
mass bounds directly, with no pointwise diagram premise.

Nothing here is a new mathematical hypothesis: `shapeMass` is the left-hand side of
`sixPoint_le_sixShapeChunk` at the terminal vector `![0, y, z, w, q, r]`, and `shapeCost` is
the value `(E|K|²)²(E|K|)³` in the normalisation in which the production evaluations state
their conclusions.
-/
module

public import PercLib.CriticalLRP.Correlation.SixPoint.Attachment.Assembly
public import PercLib.CriticalLRP.Correlation.SixPoint.TwoJointEval.Assembly
public import PercLib.CriticalLRP.Correlation.SixPoint.Ordinary.Consumer
public import PercLib.CriticalLRP.Correlation.SixPoint.MixedK2.Assembly

/-!
# Shape masses and the `k = 2` normalizations

Only middle-split masses are discharged unconditionally here. Other mass bounds stay conditional.
-/

open Set MeasureTheory
open scoped ENNReal BigOperators
open PercLib.Percolation.Bond
open PercLib.CriticalLRP.TreeExpansion.FivePoint

@[expose] public section

namespace PercLib.CriticalLRP.TreeExpansion.SixPoint.K2Mass

variable {V : Type*}

/-- The six-terminal vector of the fivefold moment expansion with root `x` and free
terminals `y, z, w, q, r`: the root sits in slot `0`, the four comb leaves of the shape
in slots `1 … 4` and the sixth arm `t` in slot `5`. -/
def shapeVec (x y z w q r : V) : Fin 6 → V := ![x, y, z, w, q, r]

@[simp] theorem shapeVec_zero (x y z w q r : V) : shapeVec x y z w q r 0 = x := rfl
@[simp] theorem shapeVec_one (x y z w q r : V) : shapeVec x y z w q r 1 = y := rfl
@[simp] theorem shapeVec_two (x y z w q r : V) : shapeVec x y z w q r 2 = z := rfl
@[simp] theorem shapeVec_three (x y z w q r : V) : shapeVec x y z w q r 3 = w := rfl
@[simp] theorem shapeVec_four (x y z w q r : V) : shapeVec x y z w q r 4 = q := rfl
@[simp] theorem shapeVec_five (x y z w q r : V) : shapeVec x y z w q r 5 = r := rfl

/-- **The mass of one six-terminal split shape.**  `k : Fin 15` is the labelling of the five
comb leaves and `j : Fin 7` the split arm; the four internal witnesses `c, u, v, w` are
summed *inside* the measure of the union, exactly as produced by
`sixPoint_le_sixShapeChunk`. -/
noncomputable def shapeMass (π : Sym2 V → unitInterval) (x : V) (k : Fin 15) (j : Fin 7)
    (y z w q r : V) : ℝ≥0∞ :=
  law π (⋃ c : V, ⋃ u : V, ⋃ v : V, ⋃ w' : V,
    {ω : PercLib.CriticalLRP.Config V |
      SixShape (PercLib.CriticalLRP.openGraph ω) k j c u v w' (shapeVec x y z w q r)})

@[simp] theorem shapeMass_apply (π : Sym2 V → unitInterval) (x : V) (k : Fin 15) (j : Fin 7)
    (y z w q r : V) :
    shapeMass π x k j y z w q r =
      law π (⋃ c : V, ⋃ u : V, ⋃ v : V, ⋃ w' : V,
        {ω : PercLib.CriticalLRP.Config V |
          SixShape (PercLib.CriticalLRP.openGraph ω) k j c u v w'
            ![x, y, z, w, q, r]}) := rfl

/-- The total mass of shape `(k, j)`: all five non-root terminals summed. -/
noncomputable def shapeTotal (π : Sym2 V → unitInterval) (x : V) (k : Fin 15) (j : Fin 7) :
    ℝ≥0∞ :=
  ∑' y, ∑' z, ∑' w, ∑' q, ∑' r, shapeMass π x k j y z w q r

/-- **The `k = 2` cost** `(E|K|²)²(E|K|)³`, in the normalisation used by every production
slot evaluation (`secondMoment`, and `firstMoment` unfolded to `∑' x, tau π 0 x`). -/
noncomputable def shapeCost (π : Sym2 V → unitInterval) (x : V) : ℝ≥0∞ :=
  secondMoment π x ^ 2 * (∑' y, tau π x y) ^ 3

end PercLib.CriticalLRP.TreeExpansion.SixPoint.K2Mass

namespace PercLib.CriticalLRP.TreeExpansion.SixPoint.K2Mass

variable {V : Type*}

/-- The five free terminals of the moment expansion bundled as one `Fin 5 → V` index, with the
root `0` in slot `0` of the six-terminal vector: `X 0 = y`, `X 1 = z`, `X 2 = w`, `X 3 = q` are
the four free comb leaves and `X 4 = r` is the sixth terminal `t`. -/
def freeVec [Zero V] (X : Fin 5 → V) : Fin 6 → V := ![0, X 0, X 1, X 2, X 3, X 4]

/-- The mass of shape `(k, j)` as a function of the five free terminals bundled as `Fin 5 → V`. -/
noncomputable def freeMass [Zero V] (π : Sym2 V → unitInterval) (k : Fin 15) (j : Fin 7)
    (X : Fin 5 → V) : ℝ≥0∞ :=
  law π (⋃ c : V, ⋃ u : V, ⋃ v : V, ⋃ w' : V,
    {ω : PercLib.CriticalLRP.Config V |
      SixShape (PercLib.CriticalLRP.openGraph ω) k j c u v w' (freeVec X)})

def patSlot0 : Fin 15 := ⟨6, by decide⟩

/-- The canonical pattern with the root in comb slot `2`. -/
def patSlot2 : Fin 15 := ⟨0, by decide⟩

end PercLib.CriticalLRP.TreeExpansion.SixPoint.K2Mass
