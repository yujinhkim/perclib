module

public import PercLib.CriticalLRP.Correlation.I417.General.Main
public import PercLib.CriticalLRP.TreeExpansion.AtlasRealization.Canonical.Join

/-!
# The marked joint-moment bound: labelled carrier, label equivalence and the bound alias

Source: T. Hutchcroft, *Critical long-range percolation I: High effective dimension*,
arXiv:2508.18807v1, Lemma I.4.17 (arbitrary `p`), the marked (base) side of the two-copy
expansion.

The canonical marked joint moment is

`I417Gen.jointPow π x p w = E[|K_x|^p 1(w ∈ K_x)]`,

the `p`-fold cluster moment of `x` through the marked vertex `w`.  The target of this
development is the explicit **canonical atlas/BK** bound for it, obtained from the
production covering theorem `CanonAtlas.exists_canonical_realization` and the canonical
finite-index BK law `PercLib.CriticalLRP.edgeMeasure_bk_list`:

`jointPow π x p w ≤ ∑_t ∑_φ ∑_y [y (last p) = w] · atlasProduct π x y t φ`,

where `t` runs over the fully labelled binary shapes with `p+1` leaves (labels
`Fin (p+1)`), `φ` over the positions of the internal vertices of `t`, and `y` over the
`p+1`-tuples of terminal vertices; the product `atlasProduct` is the BK product over the
`2 (p+1) - 1` atlas edges of `t` at `x`, `y`, `φ`.

The **last** label `Fin.last p` is the mark, and the sum over `y` keeps only the tuples whose
last terminal is the physical vertex `w` (`if y (Fin.last p) = w then 1 else 0`).  The first
`p` labels are the arms of the moment.  This file introduces the labelled carrier
`Fin (p+1) → V` for that description, the explicit label equivalence between the arm
labelling `Fin p → V` and the marked carrier with the last label pinned at `w`, and a name
for the atlas/BK right-hand side.  No probability statement is made here.

## Why the pinning has to be an equivalence, not an inclusion

`tsum_labelEvent_inter` writes the marked moment as a sum over `f : Fin p → V` of the
probabilities of `labelEvent x f ∩ connSet x w`.  The covering theorem `CanonAtlas` is stated
for a terminal map on *all* labels of the shape, so the arm tuple and the mark have to be
combined into one map `Fin (p+1) → V` whose *last* value is literally `w`.  The map

`markedExtend w : (Fin p → V) → (Fin (p+1) → V)`,  `f ↦ Fin.snoc f w`,

is injective with image exactly the tuples with last entry `w`; `markedSubtypeEquiv` records
that bijection as an `Equiv` (`Fin.init` is the inverse).  Together with the identification
`labelEvent x (markedExtend w f) = labelEvent x f ∩ connSet x w` (proved in
`PercLib.CriticalLRP.Correlation.I417.MarkedJoint.Label`), this is the transport that lets the
`(p+1)`-labelled canonical atlas bound be summed back against the `p`-armed moment.
-/

@[expose] public section

open scoped ENNReal

attribute [local instance] Classical.propDecidable

namespace PercLib.CriticalLRP.I417Marked

/-- The **marked carrier map**: the `p` arms of `x` together with the mark `w` in the last
label `Fin.last p`.  This is the terminal map `Fin (p+1) → V` at which the canonical atlas
covering theorem is applied. -/
def markedExtend {V : Type*} (w : V) {p : ℕ} (f : Fin p → V) : Fin (p + 1) → V :=
  Fin.snoc f w

/-- The marked carrier takes the physical value `w` at the marking label `Fin.last p`. -/
@[simp]
theorem markedExtend_last {V : Type*} (w : V) {p : ℕ} (f : Fin p → V) :
    markedExtend w f (Fin.last p) = w :=
  Fin.snoc_last (α := fun _ => V) w f

/-- On the arm labels `Fin.castSucc i`, the marked carrier is the arm vertex `f i`. -/
@[simp]
theorem markedExtend_castSucc {V : Type*} (w : V) {p : ℕ} (f : Fin p → V) (i : Fin p) :
    markedExtend w f i.castSucc = f i :=
  Fin.snoc_castSucc (α := fun _ => V) w f i

/-- **The explicit label equivalence** between the arm labelling `Fin p → V` and the
`(p+1)`-labelled marked carriers whose last label is pinned at the physical vertex `w`.

The forward map is `f ↦ Fin.snoc f w` and the inverse is `y ↦ Fin.init y`, so the marking
label `Fin.last p` is carried to `w` and back: `markedSubtypeEquiv_apply_last` below records
the preservation of the marked terminal. -/
def markedSubtypeEquiv {V : Type*} (w : V) (p : ℕ) :
    (Fin p → V) ≃ {y : Fin (p + 1) → V // y (Fin.last p) = w} where
  toFun f := ⟨markedExtend w f, markedExtend_last w f⟩
  invFun y := Fin.init y.1
  left_inv f := by
    funext i
    simp [markedExtend, Fin.init]
  right_inv y := by
    obtain ⟨y, hy⟩ := y
    refine Subtype.ext ?_
    change Fin.snoc (Fin.init y) w = y
    rw [← hy]
    exact Fin.snoc_init_self y

/-- The label equivalence applied to an arm tuple is the marked carrier map. -/
@[simp]
theorem markedSubtypeEquiv_apply {V : Type*} (w : V) {p : ℕ} (f : Fin p → V) :
    (markedSubtypeEquiv w p f).1 = markedExtend w f :=
  rfl

/-- **The marked terminal is preserved by the label equivalence**: the last label of the
carrier corresponding to `f` is the physical vertex `w`, for every arm tuple `f`. -/
theorem markedSubtypeEquiv_apply_last {V : Type*} (w : V) {p : ℕ} (f : Fin p → V) :
    (markedSubtypeEquiv w p f).1 (Fin.last p) = w :=
  (markedSubtypeEquiv w p f).2

/-- **The marked atlas/BK right-hand side** of the arbitrary-`p` joint-moment bound: the
sum over the fully labelled `(p+1)`-leaf shapes, the positions of their internal vertices,
and the terminal tuples pinned at the marked vertex `w` in the last label, of the product
of the connection probabilities along the atlas edges.

The indicator `if y (Fin.last p) = w then 1 else 0` is the pinning of the *physical* last
terminal at `w`; by `markedAtlasBound_eq_tsum_markedExtend` (in
`PercLib.CriticalLRP.Correlation.I417.MarkedJoint.Label`) the
`y`-sum over the pinned tuples is exactly the sum over the arm family `Fin p → V`. -/
noncomputable def markedAtlasBound {V : Type*} (π : Sym2 V → unitInterval) (x w : V)
    (p : ℕ) : ℝ≥0∞ :=
  ∑' t : PercLib.CriticalLRP.TreeExpansion.LTon (Fin (p + 1))
      (Finset.univ : Finset (Fin (p + 1))),
    ∑' φ : t.1.IPos → V, ∑' y : Fin (p + 1) → V,
      (if y (Fin.last p) = w then 1 else 0) * CanonAtlas.Measure.atlasProduct π x y t.1 φ

end PercLib.CriticalLRP.I417Marked
