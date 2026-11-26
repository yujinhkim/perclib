/- Independently rebuilt from `smwx3hvzx`, member `m1` finding f1.
Production integration revision: `c491c66109f24f38fa27cbccbcc52d11a14a8c33`.

The `p = 3`, `k = 1` mixed moment bound, assembled through the hub evaluation.

Source: Lemma I.4.16 of T. Hutchcroft, *Critical long-range percolation I: High effective
dimension*, arXiv:2508.18807v1, p. 44:

  `E|K|^3 <= 3 sum_{x,y,z,w} P(0 <-> x, w) P(w <-> y) P(w <-> z) = 3 E|K|^2 (E|K|)^2`.

## Route (not through `third_moment_mixed_le`)

1. `lintegral_cardFun_cube_eq` expands `E|K_0|^3` into the three-point connection sum.
2. The three-point event is covered by the three hub-diagram families of `triple_cover`
   (production, walk-based); each family member is production's `StarPairEvent`, identified with
   the hub-indexed diagram `hubDiagJoint` by `hubDiagJoint_eq_starPairEvent`.
3. Each hub diagram is evaluated by **threefold BK at the hub** with the pair slot kept joint:
   `law (hubDiagJoint) <= jointP π o x w * (τ w y * τ w z)`
   (`edgeMeasure_hubDiagJoint_le_hubSplitValue`).  The first factor is the three-point function
   at the hub, not a product of two two-point factors.
4. The sums over the hub position and the free pair point give the second moment
   (`hubPairSum_eq_secondMoment`, via `tsum_jointP_centre`, i.e. translation invariance), and the
   two leaf sums give the first moment (`tau_row_sum`), so the total is
   `3 * secondMoment * firstMoment * firstMoment` (`hubSplitSum_eq`).

Assumptions: a countable vertex type with an additive commutative group structure, and *full*
translation invariance of the edge law (`π s(x + g, y + g) = π s(x, y)`); the latter is exactly
what makes `tau` invariant and what the hub-position sums use.  No moment finiteness is assumed
(everything is `ℝ≥0∞`), and no properness, box, or finite-truncation substitute is used.
-/
module

public import PercLib.CriticalLRP.TreeExpansion.AtlasRealization.Canonical.Hub.Evaluation.Summation

/-!
# Assembly of the `p = 3`, `k = 1` bound
-/

@[expose] public section

open MeasureTheory Measure
open scoped ENNReal BigOperators
open PercLib.Percolation.Bond (tau law conn)
open PercLib.CriticalLRP.TreeExpansion (StarPairEvent triple_cover tsum_move_last_four
  tsum_swap_fst_third lintegral_cardFun_cube_eq)
open PercLib.CriticalLRP.TreeExpansion.FivePoint (jointP secondMoment firstMoment)

set_option linter.unusedSectionVars false
set_option linter.unusedFintypeInType false
set_option linter.unusedDecidableInType false

namespace HubJointEval

variable {V : Type*} [Countable V] [AddCommGroup V]

/-- **One hub family is bounded by the hub-split evaluation, sum over the hub included.** -/
theorem tsum_hubSplitEvent_le (π : Sym2 V → unitInterval) (hπ : ∀ e, π e < 1) (o x y z : V) :
    law π (⋃ w, StarPairEvent (V := V) o x y z w)
      ≤ ∑' w, hubSplitValue π o x y z w := by
  refine (measure_iUnion_le (fun w => StarPairEvent (V := V) o x y z w)).trans ?_
  refine ENNReal.tsum_le_tsum fun w => ?_
  rw [← hubDiagJoint_eq_starPairEvent o x y z w]
  exact edgeMeasure_hubDiagJoint_le_hubSplitValue π hπ o x y z w

/-- **The per-triple bound**: the probability that all three of `a, b, c` lie in the cluster of
`0` is at most the sum over hubs of the three hub-split blocks, one for each choice of which
point of `a, b, c` is carried jointly with `0` on the parent arm. -/
theorem triple_le_hubSplitSum (π : Sym2 V → unitInterval) (hπ : ∀ e, π e < 1) (a b c : V) :
    law π (conn 0 a ∩ conn 0 b ∩ conn 0 c)
      ≤ ∑' w, (hubSplitValue π 0 a b c w + hubSplitValue π 0 b a c w
          + hubSplitValue π 0 c a b w) := by
  have h1 := tsum_hubSplitEvent_le (V := V) π hπ 0 a b c
  have h2 := tsum_hubSplitEvent_le (V := V) π hπ 0 b a c
  have h3 := tsum_hubSplitEvent_le (V := V) π hπ 0 c a b
  refine (measure_mono (triple_cover (V := V) a b c)).trans ?_
  refine (measure_union_le _ _).trans ?_
  refine (add_le_add (measure_union_le _ _) le_rfl).trans ?_
  refine (add_le_add (add_le_add h1 h2) h3).trans (le_of_eq ?_)
  rw [ENNReal.tsum_add, ENNReal.tsum_add]

/-- **The hub-summed evaluation of the three-point sum.**  This is the source's
`3 sum_{x,y,z,w} P(0 <-> x,w) P(w <-> y) P(w <-> z)`, evaluated as
`3 * secondMoment * firstMoment * firstMoment`. -/
theorem tsum_triple_hubSplit_eq (π : Sym2 V → unitInterval)
    (hq : ∀ x y g : V, π s(x + g, y + g) = π s(x, y)) :
    (∑' a, ∑' b, ∑' c, ∑' w,
        (hubSplitValue π 0 a b c w + hubSplitValue π 0 b a c w
          + hubSplitValue π 0 c a b w))
      = 3 * (secondMoment π 0 * (firstMoment π 0 * firstMoment π 0)) := by
  have hsplit : ∀ a b c : V,
      (∑' w, (hubSplitValue π 0 a b c w + hubSplitValue π 0 b a c w
          + hubSplitValue π 0 c a b w))
      = (∑' w, hubSplitValue π 0 a b c w) + (∑' w, hubSplitValue π 0 b a c w)
        + (∑' w, hubSplitValue π 0 c a b w) := by
    intro a b c
    rw [ENNReal.tsum_add, ENNReal.tsum_add]
  rw [tsum_congr fun a => tsum_congr fun b => tsum_congr fun c => hsplit a b c]
  simp only [ENNReal.tsum_add]
  have h1 : (∑' a, ∑' b, ∑' c, ∑' w, hubSplitValue π 0 a b c w) = hubSplitSum π 0 := by
    rw [hubSplitSum]
    exact tsum_move_last_four (fun a b c w => hubSplitValue π 0 a b c w)
  have hswap2 : (∑' d, ∑' a, ∑' b, ∑' c, hubSplitValue π 0 b a c d)
      = (∑' d, ∑' b, ∑' a, ∑' c, hubSplitValue π 0 b a c d) := by
    refine tsum_congr fun d => ?_
    exact ENNReal.tsum_comm (f := fun a b => ∑' c, hubSplitValue π 0 b a c d)
  have hswap3 : (∑' d, ∑' a, ∑' b, ∑' c, hubSplitValue π 0 c a b d)
      = (∑' d, ∑' c, ∑' a, ∑' b, hubSplitValue π 0 c a b d) := by
    refine tsum_congr fun d => ?_
    refine (tsum_congr fun a => ENNReal.tsum_comm
      (f := fun b c' => hubSplitValue π 0 c' a b d)).trans ?_
    exact ENNReal.tsum_comm (f := fun a c' => ∑' b, hubSplitValue π 0 c' a b d)
  have h2 : (∑' a, ∑' b, ∑' c, ∑' w, hubSplitValue π 0 b a c w) = hubSplitSum π 0 := by
    rw [tsum_move_last_four (fun a b c w => hubSplitValue π 0 b a c w), hswap2, hubSplitSum]
  have h3 : (∑' a, ∑' b, ∑' c, ∑' w, hubSplitValue π 0 c a b w) = hubSplitSum π 0 := by
    rw [tsum_move_last_four (fun a b c w => hubSplitValue π 0 c a b w), hswap3, hubSplitSum]
  rw [h1, h2, h3, hubSplitSum_eq π hq 0]
  ring

/-- **The `p = 3`, `k = 1` mixed moment bound through the hub evaluation.**

`E|K_0|^3 <= 3 E|K_0|^2 E|K_0|^2`, with the three-point slot kept as a joint pair at a summed
hub position and the two remaining slots as single two-point functions. -/
theorem third_moment_hub_le (π : Sym2 V → unitInterval) (hπ : ∀ e, π e < 1)
    (hq : ∀ x y g : V, π s(x + g, y + g) = π s(x, y)) :
    ∫⁻ ω, (PercLib.CriticalLRP.Percolation.cardFun
        (PercLib.CriticalLRP.cluster ω 0)) ^ 3 ∂(law π)
      ≤ 3 * (secondMoment π 0 * (firstMoment π 0 * firstMoment π 0)) := by
  rw [lintegral_cardFun_cube_eq π 0]
  refine (ENNReal.tsum_le_tsum fun a => ENNReal.tsum_le_tsum fun b =>
    ENNReal.tsum_le_tsum fun c => triple_le_hubSplitSum (V := V) π hπ a b c).trans
      (le_of_eq ?_)
  exact tsum_triple_hubSplit_eq (V := V) π hq

/-- The same bound in the source's own shape `3 (E|K|)^2 E|K|^2`. -/
theorem third_moment_hub_le' (π : Sym2 V → unitInterval) (hπ : ∀ e, π e < 1)
    (hq : ∀ x y g : V, π s(x + g, y + g) = π s(x, y)) :
    ∫⁻ ω, (PercLib.CriticalLRP.Percolation.cardFun
        (PercLib.CriticalLRP.cluster ω 0)) ^ 3 ∂(law π)
      ≤ 3 * (firstMoment π 0) ^ 2 * secondMoment π 0 := by
  refine (third_moment_hub_le π hπ hq).trans (le_of_eq ?_)
  rw [pow_two]
  rw [mul_comm (secondMoment π 0) (firstMoment π 0 * firstMoment π 0)]
  rw [← mul_assoc, mul_assoc]

end HubJointEval
