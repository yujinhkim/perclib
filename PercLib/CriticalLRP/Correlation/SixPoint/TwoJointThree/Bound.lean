/-
Swarm `smwxdrsgz`, member `m3`, direction `SOURCE-FAITHFUL-HUB-COVER-REPAIR`.

The BK consequence of the `k = 2` regrouping at the middle split `j = 2`.

`combSystem_twoJointThree` puts the configuration in the two-joint/three-single
certificate; fivefold BK then costs it the product of the five group
probabilities.  The product is exactly the paper's `k = 2` pattern:
two three-point functions (`E|K|^2` each after summing the pair) and
`2p - 1 - 3k = 3` two-point functions (`E|K|` each).
-/
module

public import PercLib.CriticalLRP.Correlation.SixPoint.TwoJointThree.Regroup



public import PercLib.Probability.OpenEventHarris

/-!
# The BK bound for one middle `CombSystem` split

This is one event-certificate grouping, not a proved moment evaluation.
-/

open Set MeasureTheory
open scoped ENNReal BigOperators
open PercLib.Percolation.Bond
open PercLib.Probability
open PercLib.CriticalLRP.TreeExpansion.SixPoint

@[expose] public section

namespace PercLib.CriticalLRP.TreeExpansion.SixPoint

variable {V : Type*}

/-- **The `k = 2` two-joint/three-single BK bound at the middle split.**  The six-terminal arm
system split at comb arm `2` costs at most the product of its two joint pair probabilities and
its three two-point probabilities.  No `hpoint` premise and no pointwise leaf domination is
used: the arm system is the production `CombSystem`, and the two hub-like vertices `v` and `c`
occur once each in the product. -/
theorem combSystem_twoJointThree_le [Countable V] (π : Sym2 V → unitInterval)
    (b0 b1 b2 b3 b4 t u v w c : V) :
    law π {ω : Config V | CombSystem (openGraph ω) b0 b1 b2 b3 b4 t u v w c 2} ≤
      law π (conn b0 v ∩ conn b1 v) * (law π (conn b3 v ∩ conn b4 v) *
        (law π (conn b2 c) * (law π (conn c v) * law π (conn t c)))) := by
  refine (measure_mono (combSystem_twoJointThree (V := V) b0 b1 b2 b3 b4 t u v w c)).trans ?_
  exact twoJointThree_le π ((isUpperSet_conn b0 v).inter (isUpperSet_conn b1 v))
    ((isUpperSet_conn b3 v).inter (isUpperSet_conn b4 v))
    (isUpperSet_conn b2 c) (isUpperSet_conn c v) (isUpperSet_conn t c)

end PercLib.CriticalLRP.TreeExpansion.SixPoint
