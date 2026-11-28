/-
Accepted and independently rebuilt from Ultramath `smwzqts7r`, member m1.
Production review base `e2b5cf635f5a2ffb1c7f203271de1c0a7ef3ad2b`;
reviewed scratch source `.scratch/review-smwzqts7r/m1/Defs.lean`.
-/

/-
Ultramath `smwzqts7r`, member `m1`, direction `d2`.

# The `p = 6`, `k = 2` two-hub slot diagrams

Hutchcroft, *Critical long-range percolation I*, arXiv:2508.18807v1, Lemma I.4.16
("Generalized tree-graph inequality", p. 43):

  `E_β |K|^p ≤ (2p-3)!! (E_β |K|^2)^k (E_β |K|)^{2p-1-3k}` for `0 ≤ k ≤ ⌈(p-1)/2⌉`.

At `p = 6`, `k = 2` this reads `E|K|^6 ≤ 945 (E|K|^2)^2 (E|K|)^{12-1-6} = 945 (E|K|^2)^2 (E|K|)^5`,
which is exactly the predicate `CaseTwo.SixthMomentMixed` of production
(`PercLib/CriticalLRP/Analysis/SecondMomentCase2/Source/Defs.lean`).

This file only *defines* the `p = 6` analogue of the landed `p = 5`, `k = 2` two-hub slot
diagram of `PercLib.CriticalLRP.TreeExpansion.HubK2` (`hubStar`, `slotK2`): two hubs, each
carrying one joint pair of free leaves (`jointP`, which sums to `E|K|^2`) and one two-point
link to the root, plus the two residual free leaves of the six-leaf pattern.  No theorem
conclusion is asserted here.
-/
module

public import PercLib.CriticalLRP.Correlation.SixPoint.MixedK2.Eval
public import PercLib.CriticalLRP.Analysis.SecondMomentCase2.Source.Defs

/-! Two-hub six-point diagram definitions; these are not a claimed valid cover. -/

@[expose] public section

noncomputable section

open MeasureTheory Filter Topology Set
open scoped ENNReal NNReal Topology
open PercLib.Percolation.Bond
open PercLib.Probability

namespace PercLib.CriticalLRP.TreeExpansion.HubK2

open PercLib.CriticalLRP.TreeExpansion.FivePoint

variable {V : Type*} [Countable V]

/-- **Two-hub `p = 6`, `k = 2` integrand.**  Two joint pairs `a b` at `c₁` and `d e` at `c₂`,
one two-point link from the root `o` to each hub, and the two residual free leaves `f`, `g`
attached at `c₁` and `c₂` respectively.  Its leaf sum is `(E|K|^2)^2 (E|K|)^4`. -/
noncomputable def hubStarSix (π : Sym2 V → unitInterval) (o a b d e f g c1 c2 : V) : ℝ≥0∞ :=
  (jointP π a b c1 * tau π o c1) * (jointP π d e c2 * tau π o c2) * (tau π f c1 * tau π g c2)

/-- **The `p = 6`, `k = 2` slot diagram.**  Both hubs are summed; the six free leaves are read
through the labelling `σ` of the six slots (two leaves for each joint, two residual leaves). -/
noncomputable def slotK2Six (π : Sym2 V → unitInterval) (σ : Equiv.Perm (Fin 6)) (o : V)
    (L : Fin 6 → V) : ℝ≥0∞ :=
  ∑' c1, ∑' c2,
    hubStarSix π o (L (σ 0)) (L (σ 1)) (L (σ 2)) (L (σ 3)) (L (σ 4)) (L (σ 5)) c1 c2

/-- The sixfold joint connection event in the coordinate spelling used by the pointwise
cover. -/
def sixConnSet (o y z w q r s : V) : Set (Config V) :=
  conn o y ∩ conn o z ∩ conn o w ∩ conn o q ∩ conn o r ∩ conn o s

theorem measurableSet_sixConnSet (o y z w q r s : V) :
    MeasurableSet (sixConnSet o y z w q r s) := by
  unfold sixConnSet
  exact ((((measurableSet_conn o y).inter (measurableSet_conn o z)).inter
    (measurableSet_conn o w)).inter (measurableSet_conn o q)).inter
    (measurableSet_conn o r) |>.inter (measurableSet_conn o s)

/-! ## The residual, isolated exactly

The *only* statement this run does not prove.  It is the deterministic combinatorial input of
the proof of Lemma I.4.16 — the union bound over the `(2p-3)!! = 9!! = 945` binary trees with
six labelled leaves, followed by the BK inequality and the `k = 2` regrouping — namely a cover
of the sixfold joint connection event by the `945` slot diagrams.

The family `pat` of `945` leaf labellings is arbitrary: `tsum_slotK2Six` shows that the value
of a slot diagram does not depend on the labelling, so the event side is free to choose it.
-/
def SixCover (π : Sym2 V → unitInterval) (o : V) (pat : Fin 945 → Equiv.Perm (Fin 6)) : Prop :=
  ∀ y z w q r s : V,
    law π (sixConnSet o y z w q r s) ≤
      ∑' t : Fin 945, slotK2Six π (pat t) o ![y, z, w, q, r, s]

/-- The per-shape mass bound of the source (the `k = 2`, `p = 6` exponent pattern
`(E|K|^2)^2 (E|K|)^5`).  This one *is* proved for the two-hub slot family, by
`tsum_slotK2Six`. -/
def SixShapeMass (π : Sym2 V → unitInterval) (o : V) : Prop :=
  (∑' L : Fin 6 → V, slotK2Six π (Equiv.refl (Fin 6)) o L)
    ≤ secondMoment π o ^ 2 * (∑' x, tau π o x) ^ 5

/-- The abstract `p = 6`, `k = 2` moment inequality at the native law, in the source's own
shape `E|K|^6 ≤ 945 (E|K|^2)^2 (E|K|)^5`. -/
def SixthMomentLe (π : Sym2 V → unitInterval) (o : V) : Prop :=
  ∫⁻ ω, (PercLib.CriticalLRP.Percolation.cardFun
      (PercLib.CriticalLRP.cluster ω o)) ^ 6 ∂(law π) ≤
    945 * (∫⁻ ω, (PercLib.CriticalLRP.Percolation.cardFun
        (PercLib.CriticalLRP.cluster ω o)) ^ 2 ∂(law π)) ^ 2 *
      (∫⁻ ω, PercLib.CriticalLRP.Percolation.cardFun
        (PercLib.CriticalLRP.cluster ω o) ∂(law π)) ^ 5

end PercLib.CriticalLRP.TreeExpansion.HubK2
