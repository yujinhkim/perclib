/-
Swarm `smwxk27m7`, member `m1`, direction `d2` (`J3-EVENT-BRIDGE`).

The measure-level half of the `j = 3` bridge: from the event inclusion of `J3Event.lean`
through fivefold BK and the union bound over the two genuinely free vertices, to the
production slot diagram `slotProd2 π 3` summed over `i₂ = c` and `i₁ = v`.

The two interior vertices `u` (centre of the first star) and `w` (centre of the second star)
are *eliminated by inclusion* before any union bound, because they no longer occur on the
right-hand side: the star certificates already contain them.  Only the two vertices that do
occur, the landing point `c` and the shared spine target `v`, are union-bounded with
`measure_iUnion_le`.  So the bound is weaker only by the union bound over `V × V`, exactly as
in the accepted middle-split bridge `TwoJointEval.combSystem_union_le`.

No independence, no `hpoint`, no finiteness: only `[Countable V]` for the two union bounds.
-/
module

public import PercLib.CriticalLRP.Correlation.SixPoint.SplitEvaluation2.J3.J3Event

/-!
# `j = 3`: BK bound, union bound, and the terminal reordering

The measure-level half of the bridge, plus the pure sevenfold reordering step that moves the
five terminal sums and the two free-vertex sums into the peel order of the accepted socket
evaluations.
-/

open Set MeasureTheory
open scoped ENNReal BigOperators
open PercLib.Percolation.Bond
open PercLib.Probability
open PercLib.CriticalLRP.TreeExpansion.FivePoint
open PercLib.CriticalLRP.TreeExpansion.SixPoint
open PercLib.CriticalLRP.TreeExpansion.SixPoint.SplitPattern
open PercLib.CriticalLRP.SixPoint.SplitEval2
open PercLib.CriticalLRP.SixPoint.TwoJointEval
open PercLib.CriticalLRP.SixPoint.SplitEval2.J3

@[expose] public section

namespace PercLib.CriticalLRP.SixPoint.SplitEval2.J3

variable {V : Type*}

/-! ## Fivefold BK at the `j = 3` grouping -/

/-- **The `j = 3` regrouping costs the `slotProd2 π 3` diagram.**  This is
`twoJointThree_le` applied to the two joint groups `(b₀,b₁)@v`, `(b₄,c)@v` and the three
two-point groups `b₂—v`, `b₃—c`, `t—c`, written in the `jointP`/`tau` vocabulary of the
production slot diagram. -/
theorem twoJointThree_le_slot3 [Countable V] (π : Sym2 V → unitInterval)
    (b0 b1 b2 b3 b4 t v c : V) :
    law π (TwoJointThreeCert (conn b0 v ∩ conn b1 v) (conn b4 v ∩ conn c v)
        (conn b2 v) (conn b3 c) (conn t c)) ≤
      slotProd2 π 3 v c b0 b1 b2 b3 b4 t := by
  have h := twoJointThree_le (V := V) π
    ((isUpperSet_conn b0 v).inter (isUpperSet_conn b1 v))
    ((isUpperSet_conn b4 v).inter (isUpperSet_conn c v))
    (isUpperSet_conn b2 v) (isUpperSet_conn b3 c) (isUpperSet_conn t c)
  simpa only [jointP, tau, slotProd2] using h

/-- **The one-witness `j = 3` bound**, free vertices still fixed: the probability of the
`CombSystem` split at comb arm `3` through the four witnesses `u, v, w, c` is at most
`slotProd2 π 3 v c`. -/
theorem combSystem_three_le [Countable V] (π : Sym2 V → unitInterval)
    (b0 b1 b2 b3 b4 t u v w c : V) :
    law π {ω : Config V | CombSystem (openGraph ω) b0 b1 b2 b3 b4 t u v w c 3} ≤
      slotProd2 π 3 v c b0 b1 b2 b3 b4 t :=
  (measure_mono (combSystem_twoJointThree_three (V := V) b0 b1 b2 b3 b4 t u v w c)).trans
    (twoJointThree_le_slot3 π b0 b1 b2 b3 b4 t v c)

/-! ## The union bound over the two surviving free vertices -/

/-- **The `j = 3` bridge with the interior witnesses summed inside the measure.**  The
probability that the six-terminal arm system can be split at comb arm `3` *somewhere*, with
the shared spine target `v` and the `b₄`-star centre `u` and the landing point `c` and the
`b₄`-star centre `w` all existentially quantified, is at most the slot diagram summed over
the two vertices that survive in it. -/
theorem combSystem_union_le_three [Countable V] (π : Sym2 V → unitInterval)
    (b0 b1 b2 b3 b4 t : V) :
    law π (⋃ c : V, ⋃ u : V, ⋃ v : V, ⋃ w : V,
        {ω : PercLib.CriticalLRP.Config V |
          CombSystem (openGraph ω) b0 b1 b2 b3 b4 t u v w c 3}) ≤
      ∑' c : V, ∑' v : V, slotProd2 π 3 v c b0 b1 b2 b3 b4 t := by
  classical
  have hsub : (⋃ c : V, ⋃ u : V, ⋃ v : V, ⋃ w : V,
      {ω : PercLib.CriticalLRP.Config V |
        CombSystem (openGraph ω) b0 b1 b2 b3 b4 t u v w c 3}) ⊆
      (⋃ c : V, ⋃ v : V, TwoJointThreeCert (conn b0 v ∩ conn b1 v)
        (conn b4 v ∩ conn c v) (conn b2 v) (conn b3 c) (conn t c)) := by
    intro ω hω
    simp only [Set.mem_iUnion] at hω ⊢
    obtain ⟨c, u, v, w, hw⟩ := hω
    exact ⟨c, v, combSystem_twoJointThree_three (V := V) b0 b1 b2 b3 b4 t u v w c hw⟩
  calc law π (⋃ c : V, ⋃ u : V, ⋃ v : V, ⋃ w : V,
        {ω : PercLib.CriticalLRP.Config V |
          CombSystem (openGraph ω) b0 b1 b2 b3 b4 t u v w c 3})
      ≤ law π (⋃ c : V, ⋃ v : V, TwoJointThreeCert (conn b0 v ∩ conn b1 v)
          (conn b4 v ∩ conn c v) (conn b2 v) (conn b3 c) (conn t c)) :=
        measure_mono hsub
    _ ≤ ∑' c : V, ∑' v : V, law π (TwoJointThreeCert (conn b0 v ∩ conn b1 v)
          (conn b4 v ∩ conn c v) (conn b2 v) (conn b3 c) (conn t c)) := by
        refine (measure_iUnion_le (μ := law π) (s := fun c : V => ⋃ v : V,
          TwoJointThreeCert (conn b0 v ∩ conn b1 v) (conn b4 v ∩ conn c v)
            (conn b2 v) (conn b3 c) (conn t c))).trans ?_
        exact ENNReal.tsum_le_tsum fun c => measure_iUnion_le (μ := law π) (s := fun v : V =>
          TwoJointThreeCert (conn b0 v ∩ conn b1 v) (conn b4 v ∩ conn c v)
            (conn b2 v) (conn b3 c) (conn t c))
    _ ≤ ∑' c : V, ∑' v : V, slotProd2 π 3 v c b0 b1 b2 b3 b4 t :=
        ENNReal.tsum_le_tsum fun c => ENNReal.tsum_le_tsum fun v =>
          twoJointThree_le_slot3 π b0 b1 b2 b3 b4 t v c

/-- **The same bound at the production six-shape interface.**  The five comb terminals are
read off the six-terminal vector `T` through the pattern `pat k`, exactly as in
`SixPoint.SixShape`; the sixth terminal is `T 5`. -/
theorem sixShape_union_le_three [Countable V] (π : Sym2 V → unitInterval) (k : Fin 15)
    (T : Fin 6 → V) :
    law π (⋃ c : V, ⋃ u : V, ⋃ v : V, ⋃ w : V,
        {ω : PercLib.CriticalLRP.Config V |
          SixShape (openGraph ω) k 3 c u v w T}) ≤
      ∑' c : V, ∑' v : V,
        slotProd2 π 3 v c (T (lift5 (pat k 0))) (T (lift5 (pat k 1)))
          (T (lift5 (pat k 2))) (T (lift5 (pat k 3))) (T (lift5 (pat k 4))) (T 5) :=
  combSystem_union_le_three (V := V) π _ _ _ _ _ _

/-! ## The sevenfold reordering into the peel order of the socket evaluations -/

/-- **Reordering for the root in comb slot `0`.**  The order in which the mass sums the five
terminals and the two free vertices (`y, z, w, q, r` then `c`, `v`) is permuted into the peel
order `(i₁, b1, b2, b4, i₂, t, b3)` of `RootSocket.slotU2_three_tsum`.  This is
`ENNReal.tsum_comm` for seven variables: `TwoJointEval.tsum_seven_perm` at `permSocket3`. -/
theorem tsum_slot3_root0 {b0 : V} (π : Sym2 V → unitInterval) :
    (∑' y, ∑' z, ∑' w, ∑' q, ∑' r, ∑' c, ∑' v, slotProd2 π 3 v c b0 y z w q r) =
      (∑' i₁, ∑' b1, ∑' b2, ∑' b4, ∑' i₂, ∑' t, ∑' b3,
        slotProd2 π 3 i₁ i₂ b0 b1 b2 b3 b4 t) := by
  have h := tsum_seven_perm (V := V) permSocket3
    (fun a0 a1 a2 a3 a4 a5 a6 => slotProd2 π 3 a0 a4 b0 a1 a2 a6 a3 a5)
  simpa only [permSocket3, Equiv.coe_fn_mk, Fin.isValue, Matrix.cons_val_zero,
    Matrix.cons_val_one, Matrix.cons_val_two, Matrix.cons_val_three, Matrix.cons_val_four,
    Matrix.head_cons, Matrix.tail_cons, Matrix.cons_val] using h

/-- **Reordering for the root in comb slot `2`.**  The same permutation, in the peel order
`(i₁, b0, b1, b4, i₂, t, b3)` of `RootSocket.slotV2_three_tsum`. -/
theorem tsum_slot3_root2 {b2 : V} (π : Sym2 V → unitInterval) :
    (∑' y, ∑' z, ∑' w, ∑' q, ∑' r, ∑' c, ∑' v, slotProd2 π 3 v c y z b2 w q r) =
      (∑' i₁, ∑' b0, ∑' b1, ∑' b4, ∑' i₂, ∑' t, ∑' b3,
        slotProd2 π 3 i₁ i₂ b0 b1 b2 b3 b4 t) := by
  have h := tsum_seven_perm (V := V) permSocket3
    (fun a0 a1 a2 a3 a4 a5 a6 => slotProd2 π 3 a0 a4 a1 a2 b2 a6 a3 a5)
  simpa only [permSocket3, Equiv.coe_fn_mk, Fin.isValue, Matrix.cons_val_zero,
    Matrix.cons_val_one, Matrix.cons_val_two, Matrix.cons_val_three, Matrix.cons_val_four,
    Matrix.head_cons, Matrix.tail_cons, Matrix.cons_val] using h

end PercLib.CriticalLRP.SixPoint.SplitEval2.J3
