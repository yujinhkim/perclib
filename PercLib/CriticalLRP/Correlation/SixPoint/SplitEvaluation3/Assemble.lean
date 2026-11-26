/-
Swarm `smwxk27m7`, member `m2`, direction (G) `VERIFY-AND-ASSEMBLE-FINAL`.

# Assembly: the `p = 5`, `k = 2` fifth moment from the split `j = 4` alone

This file combines, into a single compiled theorem, the off-middle canonical root-class shape
bounds that the swarm now holds:

* `j = 0, 1, 5, 6` at both canonical root sockets — this member, `Main.lean`;
* `j = 3` at both canonical root sockets — member `m1` under direction `d2`
  (`J3-EVENT-BRIDGE`), re-read from `.ultramath/smwxk27m7/m1/` and recompiled here as
  `M1J3Defs.lean` / `M1J3Event.lean` / `M1J3Slot.lean` / `M1J3Shape.lean`.  Those four files
  are verbatim copies of `m1`'s sources with only the module names changed (`Defs` →
  `M1J3Defs`, `J3Event` → `M1J3Event`, `J3Slot` → `M1J3Slot`), so that `m1`'s `Defs` cannot
  shadow this member's `Defs`; nothing else was altered;
* `j = 2` — production's `K2Mass.shapeTotal_mid_le`, no hypothesis;
* the passage from the `15 × 7` labelled shape masses to the two root classes —
  production's `K2Mass.fifth_moment_k2_le_of_rootSlot_bounds`.

What is left is exactly one thing: the two canonical root-socket shape masses at the split
position `j = 4`.  `fifth_moment_k2_le_of_rootSlot_four` below takes those two inequalities as
its only hypothesis beyond `hq`.
-/
module

public import PercLib.CriticalLRP.Correlation.SixPoint.SplitEvaluation3.Main
public import PercLib.CriticalLRP.Correlation.SixPoint.SplitEvaluation2.J3.J3Shape

/-!
# End-to-end assembly
-/

open Set MeasureTheory
open scoped ENNReal BigOperators
open PercLib.Percolation.Bond
open PercLib.CriticalLRP.TreeExpansion.FivePoint
open PercLib.CriticalLRP.TreeExpansion.SixPoint
open PercLib.CriticalLRP.TreeExpansion.SixPoint.K2Mass

@[expose] public section

namespace PercLib.CriticalLRP.SixPoint.SplitEval3

set_option linter.style.longLine false
set_option linter.style.setOption false

variable {V : Type*}

/-- **`Lemma I.4.16` at `p = 5`, `k = 2`, from the split `j = 4` alone.**

The only hypotheses on `π` are the profile invariance `hq`; `V` is a countable additive
commutative group and no moment is assumed finite.  All of `j = 0, 1, 2, 3, 5, 6` is discharged
inside the proof, so the whole fifth-moment bound rests on the two shape masses of the split
position `j = 4`. -/
theorem fifth_moment_k2_le_of_rootSlot_four [Countable V] [AddCommGroup V]
    (π : Sym2 V → unitInterval)
    (hq : ∀ x y g : V, π s(x + g, y + g) = π s(x, y))
    (h0₄ : shapeTotal π 0 patSlot0 4 ≤ shapeCost π 0)
    (h2₄ : shapeTotal π 0 patSlot2 4 ≤ shapeCost π 0) :
    ∫⁻ ω, (PercLib.CriticalLRP.Percolation.cardFun
        (PercLib.CriticalLRP.cluster ω (0 : V))) ^ 5 ∂(law π) ≤
      105 * (∫⁻ ω, (PercLib.CriticalLRP.Percolation.cardFun
          (PercLib.CriticalLRP.cluster ω (0 : V))) ^ 2 ∂(law π)) ^ 2 *
        (∫⁻ ω, PercLib.CriticalLRP.Percolation.cardFun
          (PercLib.CriticalLRP.cluster ω (0 : V)) ∂(law π)) ^ 3 := by
  refine fifth_moment_k2_le_of_rootSlot_bounds π hq (fun j hj => ?_) (fun j hj => ?_)
  · fin_cases j
    · exact shapeTotal_patSlot0_zero_le π hq
    · exact shapeTotal_patSlot0_one_le π hq
    · exact absurd rfl hj
    · exact PercLib.CriticalLRP.SixPoint.SplitEval2.J3.shapeTotal_rootSlot0_three_le π hq
    · exact h0₄
    · exact shapeTotal_patSlot0_five_le π hq
    · exact shapeTotal_patSlot0_six_le π hq
  · fin_cases j
    · exact shapeTotal_patSlot2_zero_le π hq
    · exact shapeTotal_patSlot2_one_le π hq
    · exact absurd rfl hj
    · exact PercLib.CriticalLRP.SixPoint.SplitEval2.J3.shapeTotal_rootSlot2_three_le π hq
    · exact h2₄
    · exact shapeTotal_patSlot2_five_le π hq
    · exact shapeTotal_patSlot2_six_le π hq

/-- **The same statement with the split `j = 3` also taken as a hypothesis**, so that the
assembly does not depend on `m1`'s directory at all.  This is the form recorded in
`Main.lean` as `fifth_moment_k2_le_of_rootSlot_three_four`. -/
theorem fifth_moment_k2_le_of_rootSlot_three_four' [Countable V] [AddCommGroup V]
    (π : Sym2 V → unitInterval)
    (hq : ∀ x y g : V, π s(x + g, y + g) = π s(x, y))
    (h0₃ : shapeTotal π 0 patSlot0 3 ≤ shapeCost π 0)
    (h2₃ : shapeTotal π 0 patSlot2 3 ≤ shapeCost π 0)
    (h0₄ : shapeTotal π 0 patSlot0 4 ≤ shapeCost π 0)
    (h2₄ : shapeTotal π 0 patSlot2 4 ≤ shapeCost π 0) :
    ∫⁻ ω, (PercLib.CriticalLRP.Percolation.cardFun
        (PercLib.CriticalLRP.cluster ω (0 : V))) ^ 5 ∂(law π) ≤
      105 * (∫⁻ ω, (PercLib.CriticalLRP.Percolation.cardFun
          (PercLib.CriticalLRP.cluster ω (0 : V))) ^ 2 ∂(law π)) ^ 2 *
        (∫⁻ ω, PercLib.CriticalLRP.Percolation.cardFun
          (PercLib.CriticalLRP.cluster ω (0 : V)) ∂(law π)) ^ 3 :=
  fifth_moment_k2_le_of_rootSlot_three_four π hq h0₃ h2₃ h0₄ h2₄

end PercLib.CriticalLRP.SixPoint.SplitEval3
