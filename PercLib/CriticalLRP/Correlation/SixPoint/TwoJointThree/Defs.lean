/-
One finite-certificate grouping from `smwxdrsgz/m3`, independently rebuilt with production imports.
Only `combSystem_twoJointThree` at the middle comb split is proved, together with its fivefold
BK bound. The other splits, its slot evaluation and the final moment assembly remain open.
-/
module

public import PercLib.CriticalLRP.Correlation.FourthMoment.MixedK2.Event
public import PercLib.CriticalLRP.Correlation.SixPoint.Attachment.Split

/-!
# Two joint and three single finite certificates

This is an event-level grouping, not a proved moment evaluation.
-/

open Set MeasureTheory
open scoped ENNReal BigOperators
open PercLib.Percolation.Bond
open PercLib.Probability

@[expose] public section

namespace PercLib.CriticalLRP.TreeExpansion.SixPoint

variable {V : Type*}

/-! ## The `k = 2` two-joint/three-single certificate -/

/-- **The `k = 2` certificate event.**  Two joint groups with shared spines and three single
two-point groups, carried by five pairwise disjoint finite open certificates.

This is definitionally the production five-group BK object `FivePoint.FiveGroupEvent`; the
name records which group is a joint pair and which is a singleton, which is exactly the
paper's `k` "three-point functions" and `2p - 1 - 3k` "two-point functions". -/
def TwoJointThreeCert (J0 J1 S0 S1 S2 : Set (Config V)) : Set (Config V) :=
  FivePoint.FiveGroupEvent J0 J1 S0 S1 S2

/-- **Fivefold BK for the `k = 2` grouping**: two joint groups and three singleton groups with
pairwise disjoint certificates cost the product of the five probabilities.  The joint groups are
*not* split; each keeps its shared spine inside one certificate set. -/
theorem twoJointThree_le [Countable V] (π : Sym2 V → unitInterval)
    {J0 J1 S0 S1 S2 : Set (Config V)}
    (hJ0 : IsUpperSet J0) (hJ1 : IsUpperSet J1) (hS0 : IsUpperSet S0)
    (hS1 : IsUpperSet S1) (hS2 : IsUpperSet S2) :
    law π (TwoJointThreeCert J0 J1 S0 S1 S2) ≤
      law π J0 * (law π J1 * (law π S0 * (law π S1 * law π S2))) :=
  FivePoint.fiveGroup_le π hJ0 hJ1 hS0 hS1 hS2

/-! ## The paper's count at `p = 5`, `k = 2` -/

/-- Arithmetic of the paper's count at `p = 5`, `k = 2`: the nine tree edges split as two
3-star blocks plus `2p - 1 - 3k = 3` residual edges. -/
theorem two_mul_three_add_residual : 2 * 3 + (2 * 5 - 1 - 3 * 2) = 9 := by norm_num

/-- `k = 2` is admissible at `p = 5`, i.e. `k <= ceil ((p-1)/2)`. -/
theorem two_le_ceil_half_four : 2 <= (5 - 1 + 1) / 2 := by norm_num

end PercLib.CriticalLRP.TreeExpansion.SixPoint
