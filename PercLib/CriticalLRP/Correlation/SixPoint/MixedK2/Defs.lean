/- Integrated from independently rebuilt Ultramath work.
Base revision 8445f0b1fb57bf8fc0c08b2dfd29df64f3f01576.
Scratch source: ../../.ultramath/smwvk712v/m4/Defs.lean; module paths rewritten.
-/

module

public import PercLib.CriticalLRP.Correlation.FourthMoment.MixedK2.Slot
public import PercLib.CriticalLRP.Correlation.SixPoint.MomentAssembly

/-!
Hub-star diagrams for the `p = 5`, `k = 2` instance of Hutchcroft's generalized tree-graph
inequality (Lemma I.4.16).

The `k = 2` regrouping of the nine-arm tree splits the arms into two 3-stars around two
distinguished hub vertices plus the three remaining arms.  After the BK step each hub
contributes one *joint* pair (two free leaves measured from the same hub, summing to the
native second moment `E|K|^2`) and one two-point link to the root (which makes the hub sum
converge), and the three residual arms contribute two-point factors (`E|K|` each).  The
evaluation `E|K|^5 ≤ 105 (E|K|^2)^2 (E|K|)^3` therefore needs the two-hub diagram below,
with the two hubs `c₁`, `c₂` summed and the five free leaves summed.

`hubStar` is the unscaled integrand: leaves `a b` at hub `c₁`, leaves `d e` at hub `c₂`,
one residual leaf `f` attached to `c₁`, root `o` linked to both hubs.  `slotK2` is the
slot diagram for a leaf labelling `σ`; the evaluation in `Eval.lean` shows it is *independent*
of `σ`, so the event side may choose its own labelling family.
-/

open Set MeasureTheory
open scoped ENNReal BigOperators
open PercLib.Percolation.Bond
open PercLib.Probability

@[expose] public section

namespace PercLib.CriticalLRP.TreeExpansion.HubK2

open PercLib.CriticalLRP.TreeExpansion.FivePoint

variable {V : Type*}

/-- **Two-hub `k = 2` integrand.**  Two joint pairs measured from the hubs `c₁`, `c₂`, one
two-point link from the root `o` to each hub, and one residual two-point factor at `c₁`. -/
noncomputable def hubStar (π : Sym2 V → unitInterval) (o a b d e f c1 c2 : V) : ℝ≥0∞ :=
  (jointP π a b c1 * tau π o c1) * (jointP π d e c2 * tau π o c2) * (tau π f c1)

/-- **The `p = 5`, `k = 2` slot diagram.**  Both hubs are summed; the five free leaves are read
through the labelling `σ` of the five slots (two leaves for each joint, one residual leaf). -/
noncomputable def slotK2 (π : Sym2 V → unitInterval) (σ : Equiv.Perm (Fin 5)) (o : V)
    (L : Fin 5 → V) : ℝ≥0∞ :=
  ∑' c1, ∑' c2,
    hubStar π o (L (σ 0)) (L (σ 1)) (L (σ 2)) (L (σ 3)) (L (σ 4)) c1 c2

/-! ## Auxiliary indexing and chain diagrams -/

/-- `Fin 5 → V` as a product of five copies of `V`. -/
def fin5Prod : (Fin 5 → V) ≃ V × V × V × V × V where
  toFun X := (X 0, X 1, X 2, X 3, X 4)
  invFun p := ![p.1, p.2.1, p.2.2.1, p.2.2.2.1, p.2.2.2.2]
  left_inv X := by funext i; fin_cases i <;> rfl
  right_inv p := by obtain ⟨a, b, c, d, e⟩ := p; rfl

/-- The chain integrand: the second hub is reached from the first along the spine. -/
noncomputable def hubChain (π : Sym2 V → unitInterval) (o a b d e f c1 c2 : V) : ℝ≥0∞ :=
  (jointP π a b c1 * tau π o c1) * (jointP π d e c2 * tau π c1 c2) * (tau π f c2)

/-- The chain slot diagram with leaf labelling `σ`. -/
noncomputable def slotChain (π : Sym2 V → unitInterval) (σ : Equiv.Perm (Fin 5)) (o : V)
    (L : Fin 5 → V) : ℝ≥0∞ :=
  ∑' c1, ∑' c2,
    hubChain π o (L (σ 0)) (L (σ 1)) (L (σ 2)) (L (σ 3)) (L (σ 4)) c1 c2

end PercLib.CriticalLRP.TreeExpansion.HubK2
