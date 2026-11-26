/-
Ultramath swarm `smwxenel0`, member `m1`, direction d2 (`TWO-JOINT-MIDDLE-EVALUATION`).

Definitions only.  The subject is the accepted event-level BK regrouping of one middle
(`j = 2`) split of the six-terminal arm system, `SixPoint.combSystem_twoJointThree_le`,
and its free-vertex evaluation towards the `p = 5`, `k = 2` case of Lemma I.4.16.

The accepted bound (READ-ONLY production) is

  law π {ω | CombSystem (openGraph ω) b0 b1 b2 b3 b4 t u v w c 2}
    ≤ law π (conn b0 v ∩ conn b1 v) * (law π (conn b3 v ∩ conn b4 v)
        * (law π (conn b2 c) * (law π (conn c v) * law π (conn t c)))),

i.e. two *joint* pairs sharing the centre `v` and three residual two-point factors whose
own shared vertex is the split point `c`.  `twoJointProd` is exactly that product, and
`midSlotK2` is the slot diagram obtained from it by summing the two free vertices `v`
and `c` that the product depends on.  No probability is bounded here.
-/
module

public import PercLib.CriticalLRP.Correlation.SixPoint.TwoJointThree.Bound
public import PercLib.CriticalLRP.Correlation.FourthMoment.MixedK2.Transport

/-!
# The two-joint middle slot and terminal reindexing helpers

Only the middle split is evaluated; other splits and the moment assembly remain open.
-/


open Set MeasureTheory
open scoped ENNReal BigOperators
open PercLib.Percolation.Bond
open PercLib.CriticalLRP.TreeExpansion.FivePoint

@[expose] public section

namespace PercLib.CriticalLRP.SixPoint.TwoJointEval

variable {V : Type*}

/-- **The `j = 2` two-joint product.**  Two joint connection probabilities at the common
centre `v` (ears `b0, b1` and `b3, b4`) and three residual two-point factors, the latter
forming the chain `b2 - c - v` and the ear `t - c` at the split point `c`.

This is the right-hand side of `SixPoint.combSystem_twoJointThree_le`, written in the
`jointP`/`tau` vocabulary. -/
noncomputable def twoJointProd (π : Sym2 V → unitInterval) (b0 b1 b2 b3 b4 t v c : V) : ℝ≥0∞ :=
  jointP π b0 b1 v * (jointP π b3 b4 v * (tau π b2 c * (tau π c v * tau π t c)))

/-- **The `j = 2` two-joint slot diagram.**  The two free vertices of `twoJointProd`, the
shared joint centre `v` and the split point `c`, are summed.  The five terminals stay
free, exactly as in the production `SixPoint.slotU`. -/
noncomputable def midSlotK2 (π : Sym2 V → unitInterval) (b0 b1 b2 b3 b4 t : V) : ℝ≥0∞ :=
  ∑' v, ∑' c, twoJointProd π b0 b1 b2 b3 b4 t v c

/-- The same slot with the split point summed first.  This is the order produced by the
union bound over `⋃ c, ⋃ v` of the certificate events. -/
theorem midSlotK2_swap (π : Sym2 V → unitInterval) (b0 b1 b2 b3 b4 t : V) :
    (∑' c, ∑' v, twoJointProd π b0 b1 b2 b3 b4 t v c) = midSlotK2 π b0 b1 b2 b3 b4 t :=
  ENNReal.tsum_comm

/-! ## A reindexing device

The slot has seven free indices (`v, c` and the five terminals).  Putting them in the
order in which they can be peeled off one at a time needs a permutation of seven nested
extended sums; `fin7Prod` is only the bookkeeping that lets `Equiv.tsum_eq` do it.  It
carries no mathematical content. -/

/-- `Fin 7 → V` as a sevenfold product. -/
def fin7Prod : (Fin 7 → V) ≃ V × V × V × V × V × V × V where
  toFun X := (X 0, X 1, X 2, X 3, X 4, X 5, X 6)
  invFun p := ![p.1, p.2.1, p.2.2.1, p.2.2.2.1, p.2.2.2.2.1, p.2.2.2.2.2.1,
    p.2.2.2.2.2.2]
  left_inv X := by funext i; fin_cases i <;> rfl
  right_inv p := by
    obtain ⟨a, b, c, d, e, f, g⟩ := p
    rfl

/-- The permutation `(b1, b2, b3, b4, t, v, c) ↦ (v, b1, b3, b4, c, b2, t)`, which puts
the seven indices of the root-joint peel in order. -/
def permJoint : Equiv.Perm (Fin 7) where
  toFun := ![5, 0, 2, 3, 6, 1, 4]
  invFun := ![1, 5, 2, 3, 6, 0, 4]
  left_inv := by intro i; fin_cases i <;> rfl
  right_inv := by intro i; fin_cases i <;> rfl

/-- The permutation `(b0, b1, b3, b4, t, v, c) ↦ (c, v, b4, b3, b1, b0, t)`, which puts
the seven indices of the root-on-chain peel in order. -/
def permChain : Equiv.Perm (Fin 7) where
  toFun := ![6, 5, 3, 2, 1, 0, 4]
  invFun := ![5, 4, 3, 2, 6, 1, 0]
  left_inv := by intro i; fin_cases i <;> rfl
  right_inv := by intro i; fin_cases i <;> rfl

end PercLib.CriticalLRP.SixPoint.TwoJointEval
namespace PercLib.CriticalLRP.SixPoint.TwoJointEval

variable {V : Type*}

/-- `Fin 5 → V` as a fivefold product.  Same role as `fin7Prod`: pure bookkeeping for the
terminal reindexing, no mathematical content. -/
def fin5Prod : (Fin 5 → V) ≃ V × V × V × V × V where
  toFun X := (X 0, X 1, X 2, X 3, X 4)
  invFun p := ![p.1, p.2.1, p.2.2.1, p.2.2.2.1, p.2.2.2.2]
  left_inv X := by funext i; fin_cases i <;> rfl
  right_inv p := by
    obtain ⟨a, b, c, d, e⟩ := p
    rfl

end PercLib.CriticalLRP.SixPoint.TwoJointEval
