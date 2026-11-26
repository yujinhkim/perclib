/-
Ultramath swarm `smwxenel0`, member `m1`, direction d2 (`TWO-JOINT-MIDDLE-EVALUATION`).

Event-to-slot bridge for the one accepted middle (`j = 2`) split.

`combSystem_twoJointThree_le` bounds the probability of `CombSystem ... 2` at *fixed*
witnesses `u, v, w, c`.  The assembly sums the four free vertices `c, u, v, w` of the
arm system, so the honest one-split statement has those four existential witnesses
inside the event.  Two of them (`u`, the shared spine vertex of the first joint pair, and
`w`, the shared vertex of the `b3, b4` arms) no longer occur in the accepted product —
they have been absorbed into the joint connection events.  Here they are eliminated by a
containment, before any union bound, and the remaining two genuine free vertices `c` and
`v` are summed by the union bound and the event-level BK of `twoJointThree_le`.
-/
module

public import PercLib.CriticalLRP.Correlation.SixPoint.TwoJointThree.Bound
public import PercLib.CriticalLRP.Correlation.SixPoint.TwoJointEval.Defs

/-!
# Event-to-slot bridge for the middle `CombSystem` split

Only the middle split is evaluated; other splits and the moment assembly remain open.
-/


open Set MeasureTheory
open scoped ENNReal BigOperators
open PercLib.Percolation.Bond
open PercLib.Probability
open PercLib.CriticalLRP.TreeExpansion.FivePoint
open PercLib.CriticalLRP.TreeExpansion.SixPoint

@[expose] public section

namespace PercLib.CriticalLRP.SixPoint.TwoJointEval

variable {V : Type*}

/-- **One middle-split slot bound, free vertices included.**  The probability that the
six-terminal arm system can be split at comb arm `2` somewhere, with the shared-spine
vertex and the `b3, b4` meeting vertex existentially quantified, is at most the
two-joint slot diagram `midSlotK2`.

This is the free-vertex-summed form of the accepted `combSystem_twoJointThree_le`; the
five-terminal two-point functions are still free, and no constant is lost. -/
theorem combSystem_union_le [Countable V] (π : Sym2 V → unitInterval) (b0 b1 b2 b3 b4 t : V) :
    law π (⋃ c : V, ⋃ u : V, ⋃ v : V, ⋃ w : V,
        {ω : PercLib.CriticalLRP.Config V |
          CombSystem (openGraph ω) b0 b1 b2 b3 b4 t u v w c 2}) ≤
      midSlotK2 π b0 b1 b2 b3 b4 t := by
  classical
  have hsub : (⋃ c : V, ⋃ u : V, ⋃ v : V, ⋃ w : V,
      {ω : PercLib.CriticalLRP.Config V |
        CombSystem (openGraph ω) b0 b1 b2 b3 b4 t u v w c 2}) ⊆
      (⋃ c : V, ⋃ v : V, TwoJointThreeCert (conn b0 v ∩ conn b1 v)
        (conn b3 v ∩ conn b4 v) (conn b2 c) (conn c v) (conn t c)) := by
    intro ω hω
    simp only [Set.mem_iUnion] at hω ⊢
    obtain ⟨c, u, v, w, hw⟩ := hω
    exact ⟨c, v, combSystem_twoJointThree (V := V) b0 b1 b2 b3 b4 t u v w c hw⟩
  calc law π (⋃ c : V, ⋃ u : V, ⋃ v : V, ⋃ w : V,
        {ω : PercLib.CriticalLRP.Config V |
          CombSystem (openGraph ω) b0 b1 b2 b3 b4 t u v w c 2})
      ≤ law π (⋃ c : V, ⋃ v : V, TwoJointThreeCert (conn b0 v ∩ conn b1 v)
          (conn b3 v ∩ conn b4 v) (conn b2 c) (conn c v) (conn t c)) :=
        measure_mono hsub
    _ ≤ ∑' c : V, ∑' v : V, law π (TwoJointThreeCert (conn b0 v ∩ conn b1 v)
          (conn b3 v ∩ conn b4 v) (conn b2 c) (conn c v) (conn t c)) := by
        refine (measure_iUnion_le (μ := law π) (s := fun c : V => ⋃ v : V,
          TwoJointThreeCert (conn b0 v ∩ conn b1 v) (conn b3 v ∩ conn b4 v)
            (conn b2 c) (conn c v) (conn t c))).trans ?_
        exact ENNReal.tsum_le_tsum fun c => measure_iUnion_le (μ := law π) (s := fun v : V =>
          TwoJointThreeCert (conn b0 v ∩ conn b1 v) (conn b3 v ∩ conn b4 v)
            (conn b2 c) (conn c v) (conn t c))
    _ ≤ ∑' c : V, ∑' v : V, twoJointProd π b0 b1 b2 b3 b4 t v c :=
        ENNReal.tsum_le_tsum fun c => ENNReal.tsum_le_tsum fun v => by
          simpa only [twoJointProd, jointP, tau] using
            twoJointThree_le (V := V) π
              ((isUpperSet_conn b0 v).inter (isUpperSet_conn b1 v))
              ((isUpperSet_conn b3 v).inter (isUpperSet_conn b4 v))
              (isUpperSet_conn b2 c) (isUpperSet_conn c v) (isUpperSet_conn t c)
    _ = midSlotK2 π b0 b1 b2 b3 b4 t := midSlotK2_swap π b0 b1 b2 b3 b4 t

/-- **The same slot bound at the production six-shape interface**, i.e. for the `k`-th of
the fifteen labelled patterns and the middle split `j = 2`, with the five comb terminals
read off the six-terminal vector `T` exactly as in `SixPoint.SixShape`. -/
theorem sixShape_union_le [Countable V] (π : Sym2 V → unitInterval) (k : Fin 15)
    (T : Fin 6 → V) :
    law π (⋃ c : V, ⋃ u : V, ⋃ v : V, ⋃ w : V,
        {ω : PercLib.CriticalLRP.Config V | SixShape (openGraph ω) k 2 c u v w T}) ≤
      midSlotK2 π (T (lift5 (PercLib.CriticalLRP.TreeExpansion.FivePoint.pat k 0)))
        (T (lift5 (PercLib.CriticalLRP.TreeExpansion.FivePoint.pat k 1)))
        (T (lift5 (PercLib.CriticalLRP.TreeExpansion.FivePoint.pat k 2)))
        (T (lift5 (PercLib.CriticalLRP.TreeExpansion.FivePoint.pat k 3)))
        (T (lift5 (PercLib.CriticalLRP.TreeExpansion.FivePoint.pat k 4))) (T 5) :=
  combSystem_union_le (V := V) π _ _ _ _ _ _

end PercLib.CriticalLRP.SixPoint.TwoJointEval
