/-
Swarm `smwxk27m7`, member `m1`, direction `d2` (`J3-EVENT-BRIDGE`).

The two canonical root-class shape-mass bounds at split position `j = 3`.

`K2Mass.shapeTotal π 0 patSlot0 3` is the total mass of the shape event of the identity
pattern `patSlot0 = 6` at split `3` (root `b₀` in comb slot `0`, i.e. the root is the ear of
the first joint group), and `K2Mass.shapeTotal π 0 patSlot2 3` the same for `patSlot2 = 0`
(root `b₂` in comb slot `2`, i.e. the root is a two-point-function endpoint).  Both are
bounded by `K2Mass.shapeCost π 0 = (E|K|²)²(E|K|)³`:

* `sixShape_union_le_three` (from `J3Slot.lean`) bounds the mass, with the four internal
  witnesses still summed inside the measure, by the `slotProd2 π 3` diagram summed over the
  landing point `c` and the shared spine target `v`;
* the five terminal sums of `shapeTotal` and those two sums are then permuted into the peel
  order of the accepted socket evaluations `slotU2_three_tsum` / `slotV2_three_tsum` by
  `tsum_slot3_root0` / `tsum_slot3_root2`, which is `ENNReal.tsum_comm` for seven variables
  (no finiteness);
* the socket evaluation then returns `monomial2 π 0`, which is `shapeCost π 0`.

Only `[Countable V]`, `[AddCommGroup V]` and the profile invariance
`hq : ∀ x y g, π s(x+g,y+g) = π s(x,y)` are used.  No independence, no `hpoint`, no
finiteness of any moment.
-/
module

public import PercLib.CriticalLRP.Correlation.SixPoint.SplitEvaluation2.J3.J3Slot
public import PercLib.CriticalLRP.Correlation.SixPoint.K2Mass.RootCollapse.Main

/-!
# `j = 3`: the two canonical root-class shape-mass bounds
-/

open Set MeasureTheory
open scoped ENNReal BigOperators
open PercLib.Percolation.Bond
open PercLib.Probability
open PercLib.CriticalLRP.TreeExpansion.FivePoint
open PercLib.CriticalLRP.TreeExpansion.SixPoint
open PercLib.CriticalLRP.TreeExpansion.FivePoint
open PercLib.CriticalLRP.TreeExpansion.SixPoint.K2Mass
open PercLib.CriticalLRP.SixPoint.SplitEval2
open PercLib.CriticalLRP.SixPoint.SplitEval2.RootSocket
open PercLib.CriticalLRP.SixPoint.TwoJointEval
open PercLib.CriticalLRP.SixPoint.SplitEval2.J3

@[expose] public section

namespace PercLib.CriticalLRP.SixPoint.SplitEval2.J3

variable {V : Type*}

/-! ## The one-shape mass bound, with the witnesses inside the measure -/

/-- **Root in comb slot `0` at `j = 3`.**  The identity pattern `patSlot0 = 6` puts the root `x`
in comb slot `0`, so `x` is the first ear of the joint group `(b₀, b₁) @ v` and the four free
comb leaves are `y, z, w, q` with sixth terminal `r`.

The four internal witnesses `c, u, v, w'` stay summed *inside* the measure: this is
`combSystem_union_le_three` instantiated at the leaf tuple of the pattern, so no shape is
identified with another and no diagram is factored. -/
theorem shapeMass_rootSlot0_three_le [Countable V] (π : Sym2 V → unitInterval)
    (x y z w q r : V) :
    shapeMass π x patSlot0 3 y z w q r ≤
      ∑' c : V, ∑' v : V, slotProd2 π 3 v c x y z w q r := by
  have h := combSystem_union_le_three (V := V) π
    (shapeVec x y z w q r (lift5 (pat patSlot0 0)))
    (shapeVec x y z w q r (lift5 (pat patSlot0 1)))
    (shapeVec x y z w q r (lift5 (pat patSlot0 2)))
    (shapeVec x y z w q r (lift5 (pat patSlot0 3)))
    (shapeVec x y z w q r (lift5 (pat patSlot0 4)))
    (shapeVec x y z w q r 5)
  exact h

/-- **Root in comb slot `2` at `j = 3`.**  The pattern `patSlot2 = 0` puts the root `x` in comb
slot `2`, so `x` is the endpoint of the two-point factor `x — v` and the four free comb leaves
are `y, z, w, q` with sixth terminal `r`. -/
theorem shapeMass_rootSlot2_three_le [Countable V] (π : Sym2 V → unitInterval)
    (x y z w q r : V) :
    shapeMass π x patSlot2 3 y z w q r ≤
      ∑' c : V, ∑' v : V, slotProd2 π 3 v c y z x w q r := by
  have h := combSystem_union_le_three (V := V) π
    (shapeVec x y z w q r (lift5 (pat patSlot2 0)))
    (shapeVec x y z w q r (lift5 (pat patSlot2 1)))
    (shapeVec x y z w q r (lift5 (pat patSlot2 2)))
    (shapeVec x y z w q r (lift5 (pat patSlot2 3)))
    (shapeVec x y z w q r (lift5 (pat patSlot2 4)))
    (shapeVec x y z w q r 5)
  exact h

/-! ## The two root-class total masses -/

/-- **`shapeTotal π 0 patSlot0 3 ≤ shapeCost π 0`.**  Root in comb socket `b₀`. -/
theorem shapeTotal_rootSlot0_three_le [Countable V] [AddCommGroup V]
    (π : Sym2 V → unitInterval)
    (hq : ∀ x y g : V, π s(x + g, y + g) = π s(x, y)) :
    shapeTotal π 0 patSlot0 3 ≤ shapeCost π 0 := by
  refine (ENNReal.tsum_le_tsum fun y => ENNReal.tsum_le_tsum fun z =>
    ENNReal.tsum_le_tsum fun w => ENNReal.tsum_le_tsum fun q =>
    ENNReal.tsum_le_tsum fun r => shapeMass_rootSlot0_three_le π 0 y z w q r).trans_eq ?_
  refine (tsum_slot3_root0 (b0 := (0 : V)) π).trans ?_
  simpa only [shapeCost, monomial2] using slotU2_three_tsum π hq (0 : V)

/-- **`shapeTotal π 0 patSlot2 3 ≤ shapeCost π 0`.**  Root in comb socket `b₂`. -/
theorem shapeTotal_rootSlot2_three_le [Countable V] [AddCommGroup V]
    (π : Sym2 V → unitInterval)
    (hq : ∀ x y g : V, π s(x + g, y + g) = π s(x, y)) :
    shapeTotal π 0 patSlot2 3 ≤ shapeCost π 0 := by
  refine (ENNReal.tsum_le_tsum fun y => ENNReal.tsum_le_tsum fun z =>
    ENNReal.tsum_le_tsum fun w => ENNReal.tsum_le_tsum fun q =>
    ENNReal.tsum_le_tsum fun r => shapeMass_rootSlot2_three_le π 0 y z w q r).trans_eq ?_
  refine (tsum_slot3_root2 (b2 := (0 : V)) π).trans ?_
  simpa only [shapeCost, monomial2] using slotV2_three_tsum π hq (0 : V)

/-- **Both canonical root sockets at `j = 3`.**  This is the exact pair of hypotheses that
`K2Mass.fifth_moment_k2_le_of_rootSlot_bounds` consumes at the split `j = 3`. -/
theorem shapeTotal_rootSlot_three_le [Countable V] [AddCommGroup V]
    (π : Sym2 V → unitInterval)
    (hq : ∀ x y g : V, π s(x + g, y + g) = π s(x, y)) :
    shapeTotal π 0 patSlot0 3 ≤ shapeCost π 0 ∧
      shapeTotal π 0 patSlot2 3 ≤ shapeCost π 0 :=
  ⟨shapeTotal_rootSlot0_three_le π hq, shapeTotal_rootSlot2_three_le π hq⟩

/-- **All fifteen labelled patterns at `j = 3`.**  The root-class collapse
(`K2Mass.shapeTotal_eq_rootSlot`) turns the two canonical bounds into one bound for each of the
`15` patterns, with no hypothesis on `π` beyond the profile invariance.  This is the form that
`K2Mass.fifth_moment_k2_le_of_shapeTotal` consumes. -/
theorem shapeTotal_three_le [Countable V] [AddCommGroup V] (π : Sym2 V → unitInterval)
    (hq : ∀ x y g : V, π s(x + g, y + g) = π s(x, y)) (k : Fin 15) :
    shapeTotal π 0 k 3 ≤ shapeCost π 0 := by
  rcases shapeTotal_eq_rootSlot π 0 k 3 with h | h
  · rw [h]; exact shapeTotal_rootSlot0_three_le π hq
  · rw [h]; exact shapeTotal_rootSlot2_three_le π hq

/-! ## What `j = 3` closes in the `105`-shape assembly

`K2Mass.fifth_moment_k2_le_of_rootSlot_bounds` needs one mass bound for each of the two
canonical root classes at each of the six off-middle splits, and `K2Mass.shapeTotal_mid_le`
supplies `j = 2`.  The pair proved above removes `j = 3` from the hypothesis, so the fifth
moment follows from the ten bounds at `j = 0, 1, 4, 5, 6` alone. -/

/-- **The `k = 2` fifth-moment bound from the five remaining splits only.**  Compared with
`K2Mass.fifth_moment_k2_le_of_rootSlot_bounds`, the two hypotheses are required only at
`j ≠ 2` *and* `j ≠ 3`; the split `j = 3` is discharged by
`shapeTotal_rootSlot_three_le`, and `j = 2` by the production `shapeTotal_mid_le`. -/
theorem fifth_moment_k2_le_of_rootSlot_bounds_away [Countable V] [AddCommGroup V]
    (π : Sym2 V → unitInterval)
    (hq : ∀ x y g : V, π s(x + g, y + g) = π s(x, y))
    (h0 : ∀ j : Fin 7, j ≠ 2 → j ≠ 3 → shapeTotal π 0 patSlot0 j ≤ shapeCost π 0)
    (h2 : ∀ j : Fin 7, j ≠ 2 → j ≠ 3 → shapeTotal π 0 patSlot2 j ≤ shapeCost π 0) :
    ∫⁻ ω, (PercLib.CriticalLRP.Percolation.cardFun
        (PercLib.CriticalLRP.cluster ω (0 : V))) ^ 5 ∂(law π) ≤
      105 * (∫⁻ ω, (PercLib.CriticalLRP.Percolation.cardFun
          (PercLib.CriticalLRP.cluster ω (0 : V))) ^ 2 ∂(law π)) ^ 2 *
        (∫⁻ ω, PercLib.CriticalLRP.Percolation.cardFun
          (PercLib.CriticalLRP.cluster ω (0 : V)) ∂(law π)) ^ 3 := by
  refine fifth_moment_k2_le_of_rootSlot_bounds π hq (fun j hj => ?_) (fun j hj => ?_)
  · by_cases h3 : j = 3
    · subst h3
      exact shapeTotal_rootSlot0_three_le π hq
    · exact h0 j hj h3
  · by_cases h3 : j = 3
    · subst h3
      exact shapeTotal_rootSlot2_three_le π hq
    · exact h2 j hj h3

end PercLib.CriticalLRP.SixPoint.SplitEval2.J3
