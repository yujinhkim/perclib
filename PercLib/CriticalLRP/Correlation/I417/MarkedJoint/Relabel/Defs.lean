/-
Independently reviewed and integrated UltraMath work: swarm `smwwxbtza`, member `m1`,
direction B. Production integration revision:
`54054b7051903bd4990d0dc78cdfcb61d0676288`, Lean 4.35.0.
The unsubmitted candidate was `.ultramath/smwwxbtza/m1/Defs.lean`.
-/

module

public import PercLib.CriticalLRP.Correlation.I417.Marked.Diagram
public import PercLib.CriticalLRP.Correlation.I417.General.Main
public import PercLib.CriticalLRP.Correlation.I417.MarkedJoint.Defs

/-! Definitions for relabelling marked canonical atlas diagrams.  The physical last mark
is preserved by an explicit label equivalence; the marked carrier is reused from
`PercLib.CriticalLRP.Correlation.I417.MarkedJoint.Defs`. -/

set_option autoImplicit false
set_option linter.unusedSectionVars false
set_option linter.style.longLine false
set_option linter.hashCommand false

open scoped ENNReal

@[expose] public section

namespace PercLib.CriticalLRP.I417MarkedRelabel

open PercLib.CriticalLRP.TreeExpansion
open PercLib.CriticalLRP.TreeExpansion.Real (AEdge srcPos dstPos rootPos childPos)
open PercLib.CriticalLRP.I417Marked (Label markLabel armLabel labelledMarkedDiagram)
open PercLib.CriticalLRP.I417Marked (markedExtend markedSubtypeEquiv)


universe u

variable {V : Type*}

/-! ## The label equivalence `Fin (p+1) ≃ Fin p ⊕ PUnit` -/

/-- The label of `Fin (p+1)` at a given index: the arms for `Fin p` and the mark on the last. -/
def labelOfFin (p : ℕ) : Fin (p + 1) → Label p :=
  Fin.lastCases (markLabel p) (fun j => armLabel p j)

/-- The index in `Fin (p+1)` of a label: the mark goes to the last index. -/
def finOfLabel (p : ℕ) : Label p → Fin (p + 1) :=
  Sum.elim (fun j => Fin.castSucc j) (fun _ => Fin.last p)

theorem finOfLabel_labelOfFin (p : ℕ) (i : Fin (p + 1)) :
    finOfLabel p (labelOfFin p i) = i := by
  refine Fin.lastCases (motive := fun i => finOfLabel p (labelOfFin p i) = i) ?_ ?_ i
  · simp [labelOfFin, finOfLabel, markLabel]
  · intro j
    simp [labelOfFin, finOfLabel, armLabel]

theorem labelOfFin_finOfLabel (p : ℕ) (l : Label p) :
    labelOfFin p (finOfLabel p l) = l := by
  rcases l with j | u
  · simp [finOfLabel, labelOfFin, armLabel]
  · cases u
    simp [finOfLabel, labelOfFin, markLabel]

/-- **The label equivalence `Fin (p+1) ≃ Fin p ⊕ PUnit`** sending the last index to the mark. -/
noncomputable def finLabelEquiv (p : ℕ) : Fin (p + 1) ≃ Label p where
  toFun := labelOfFin p
  invFun := finOfLabel p
  left_inv := finOfLabel_labelOfFin p
  right_inv := labelOfFin_finOfLabel p

@[simp] theorem finLabelEquiv_apply (p : ℕ) (i : Fin (p + 1)) :
    finLabelEquiv p i = labelOfFin p i := rfl

/-- The label equivalence sends the last index to the mark. -/
@[simp] theorem finLabelEquiv_last (p : ℕ) : finLabelEquiv p (Fin.last p) = markLabel p := by
  simp [finLabelEquiv, labelOfFin]

/-! ## Transport of internal positions along a relabelling -/

/-- **Internal positions are transported along a leaf relabelling.**  The tree shape is
unchanged by `RTree.mapLabel`, so the internal vertices of `t.mapLabel f` and of `t` are in
canonical bijection. -/
noncomputable def iposMapLabelEquiv {α β : Type u} (f : α → β) :
    (t : RTree α) → RTree.IPos (t.mapLabel f) ≃ RTree.IPos t
  | RTree.leaf _ => Equiv.refl _
  | RTree.node l r =>
      (iposMapLabelEquiv f l).sumCongr ((iposMapLabelEquiv f r).sumCongr (Equiv.refl PUnit))

theorem iposMapLabelEquiv_leaf {α β : Type u} (f : α → β) (a : α)
    (u : RTree.IPos ((RTree.leaf a).mapLabel f)) : (iposMapLabelEquiv f (RTree.leaf a)) u = u.elim :=
  u.elim

@[simp] theorem iposMapLabelEquiv_inl {α β : Type u} (f : α → β) {l r : RTree α}
    (u : RTree.IPos (l.mapLabel f)) :
    iposMapLabelEquiv f (RTree.node l r) (Sum.inl u) = Sum.inl (iposMapLabelEquiv f l u) := rfl

@[simp] theorem iposMapLabelEquiv_inr_inl {α β : Type u} (f : α → β) {l r : RTree α}
    (v : RTree.IPos (r.mapLabel f)) :
    iposMapLabelEquiv f (RTree.node l r) (Sum.inr (Sum.inl v))
      = Sum.inr (Sum.inl (iposMapLabelEquiv f r v)) := rfl

@[simp] theorem iposMapLabelEquiv_inr_inr {α β : Type u} (f : α → β) {l r : RTree α}
    (w : PUnit) :
    iposMapLabelEquiv f (RTree.node l r) (Sum.inr (Sum.inr w)) = Sum.inr (Sum.inr w) := rfl

/-- **Atlas edges are transported along a leaf relabelling.** -/
noncomputable def aedgeEquiv {α β : Type u} (f : α → β) (t : RTree α) :
    AEdge (t.mapLabel f) ≃ AEdge t :=
  ((iposMapLabelEquiv f t).prodCongr (Equiv.refl Bool)).sumCongr (Equiv.refl PUnit)

@[simp] theorem aedgeEquiv_inl {α β : Type u} (f : α → β) (t : RTree α)
    (u : RTree.IPos (t.mapLabel f)) (b : Bool) :
    aedgeEquiv f t (Sum.inl (u, b)) = Sum.inl (iposMapLabelEquiv f t u, b) := rfl

@[simp] theorem aedgeEquiv_inr {α β : Type u} (f : α → β) (t : RTree α) (w : PUnit) :
    aedgeEquiv f t (Sum.inr w) = Sum.inr w := rfl

/-! ## The vertex maps unfold structurally -/

@[simp] theorem srcPos_inl {α : Type u} (t : RTree α) (φ : t.IPos → V) (c : V)
    (i : t.IPos) (b : Bool) : srcPos t φ c (Sum.inl (i, b)) = φ i := rfl

@[simp] theorem srcPos_inr {α : Type u} (t : RTree α) (φ : t.IPos → V) (c : V) (w : PUnit) :
    srcPos t φ c (Sum.inr w) = c := rfl

@[simp] theorem dstPos_inl {α : Type u} (t : RTree α) (φ : t.IPos → V) (y : α → V)
    (i : t.IPos) (b : Bool) : dstPos t φ y (Sum.inl (i, b)) = childPos t φ y i b := rfl

@[simp] theorem dstPos_inr {α : Type u} (t : RTree α) (φ : t.IPos → V) (y : α → V) (w : PUnit) :
    dstPos t φ y (Sum.inr w) = rootPos t φ y := rfl

@[simp] theorem rootPos_leaf {α : Type u} (a : α) (φ : (RTree.leaf a : RTree α).IPos → V)
    (y : α → V) : rootPos (RTree.leaf a) φ y = y a := rfl

@[simp] theorem rootPos_node {α : Type u} (l r : RTree α) (φ : (RTree.node l r).IPos → V)
    (y : α → V) : rootPos (RTree.node l r) φ y = φ (Sum.inr (Sum.inr ⟨⟩)) := rfl

@[simp] theorem childPos_node_inl {α : Type u} (l r : RTree α)
    (φ : (RTree.node l r).IPos → V) (y : α → V) (i : l.IPos) (b : Bool) :
    childPos (RTree.node l r) φ y (Sum.inl i) b = childPos l (fun v => φ (Sum.inl v)) y i b := rfl

@[simp] theorem childPos_node_inr_inl {α : Type u} (l r : RTree α)
    (φ : (RTree.node l r).IPos → V) (y : α → V) (j : r.IPos) (b : Bool) :
    childPos (RTree.node l r) φ y (Sum.inr (Sum.inl j)) b
      = childPos r (fun w => φ (Sum.inr (Sum.inl w))) y j b := rfl

@[simp] theorem childPos_node_root {α : Type u} (l r : RTree α)
    (φ : (RTree.node l r).IPos → V) (y : α → V) (w : PUnit) (b : Bool) :
    childPos (RTree.node l r) φ y (Sum.inr (Sum.inr w)) b
      = if b then rootPos r (fun w => φ (Sum.inr (Sum.inl w))) y
        else rootPos l (fun v => φ (Sum.inl v)) y := rfl

/-! ## The atlas edge product in the form used by `posSumWtE` -/

/-- The Atlas product attached to the atlas edges of `t` at root `c`, terminals `y` and internal
positions `φ`, for an **arbitrary** label type `α`.  On `α = Fin q` it is by definition
`CanonAtlas.Measure.atlasProduct`, and on `k u v = edgeMeasure π (connSet u v)` its `φ`-sum is
`TreeExpansion.Real.posSumWtE`. -/
noncomputable def atlasEdgeProduct {V : Type*} (π : Sym2 V → unitInterval)
    {α : Type u} (c : V) (y : α → V) (t : RTree α) (φ : t.IPos → V) : ℝ≥0∞ :=
  ∏ e : AEdge t, edgeMeasure π (connSet (srcPos t φ c e) (dstPos t φ y e))

/-- On the `Fin q`-labelled shapes this is production's `atlasProduct`. -/
theorem atlasEdgeProduct_eq_atlasProduct {V : Type*} (π : Sym2 V → unitInterval)
    {q : ℕ} (x : V) (f : Fin q → V) (t : RTree (Fin q)) (φ : t.IPos → V) :
    atlasEdgeProduct π x f t φ = CanonAtlas.Measure.atlasProduct π x f t φ := rfl

/-! ## Relabelling the fully labelled shape family -/

/-- The relabelling of a fully labelled shape by a label equivalence is fully labelled. -/
theorem ltOnMapLabel_leaves {α β : Type u} [DecidableEq α] [DecidableEq β] [Fintype α]
    [Fintype β] (e : α ≃ β) (t : LTon α (Finset.univ : Finset α)) :
    (t.1.mapLabel e).leaves.Nodup ∧ (t.1.mapLabel e).leaves.toFinset = Finset.univ := by
  refine ⟨?_, ?_⟩
  · rw [RTree.leaves_mapLabel]
    exact t.2.1.map e.injective
  · ext b
    rw [List.mem_toFinset, RTree.leaves_mapLabel, List.mem_map]
    constructor
    · rintro ⟨a, -, rfl⟩
      exact Finset.mem_univ _
    · intro _
      exact ⟨e.symm b, by rw [← List.mem_toFinset, t.2.2]; exact Finset.mem_univ _,
        e.apply_symm_apply b⟩

/-- The relabelling of a fully labelled shape. -/
noncomputable def ltOnMapLabel {α β : Type u} [DecidableEq α] [DecidableEq β] [Fintype α]
    [Fintype β] (e : α ≃ β) (t : LTon α (Finset.univ : Finset α)) :
    LTon β (Finset.univ : Finset β) :=
  ⟨t.1.mapLabel e, ltOnMapLabel_leaves e t⟩

theorem ltOnMapLabel_injective {α β : Type u} [DecidableEq α] [DecidableEq β] [Fintype α]
    [Fintype β] (e : α ≃ β) : Function.Injective (ltOnMapLabel e) := by
  intro a b h
  have h' : a.1.mapLabel e = b.1.mapLabel e := congrArg Subtype.val h
  exact Subtype.ext (RTree.mapLabel_injective e.injective h')

theorem ltOnMapLabel_surjective {α β : Type u} [DecidableEq α] [DecidableEq β] [Fintype α]
    [Fintype β] (e : α ≃ β) : Function.Surjective (ltOnMapLabel e) := by
  intro t
  refine ⟨⟨t.1.mapLabel e.symm, ltOnMapLabel_leaves e.symm t⟩, ?_⟩
  refine Subtype.ext ?_
  change (t.1.mapLabel e.symm).mapLabel e = t.1
  rw [RTree.mapLabel_mapLabel]
  have hfun : (fun a => e (e.symm a)) = id := funext fun a => e.apply_symm_apply a
  rw [hfun, RTree.mapLabel_id]

/-- **The fully labelled shape family is invariant under a label equivalence.** -/
noncomputable def ltOnMapLabelEquiv {α β : Type u} [DecidableEq α] [DecidableEq β] [Fintype α]
    [Fintype β] (e : α ≃ β) : LTon α (Finset.univ : Finset α) ≃ LTon β (Finset.univ) :=
  Equiv.ofBijective (ltOnMapLabel e) ⟨ltOnMapLabel_injective e, ltOnMapLabel_surjective e⟩

@[simp] theorem ltOnMapLabelEquiv_apply {α β : Type u} [DecidableEq α] [DecidableEq β]
    [Fintype α] [Fintype β] (e : α ≃ β) (t : LTon α (Finset.univ : Finset α)) :
    ltOnMapLabelEquiv e t = ltOnMapLabel e t := rfl

@[simp] theorem ltOnMapLabel_coe {α β : Type u} [DecidableEq α] [DecidableEq β] [Fintype α]
    [Fintype β] (e : α ≃ β) (t : LTon α (Finset.univ : Finset α)) :
    (ltOnMapLabel e t).1 = t.1.mapLabel e := rfl

/-! ## A function-space equivalence induced by an equivalence of the domains -/

/-- Post-composition with the inverse of an equivalence, on function spaces. -/
def piEquivOfEquiv {γ δ : Type*} (e : δ ≃ γ) (W : Type*) : (γ → W) ≃ (δ → W) where
  toFun f := fun d => f (e d)
  invFun f := fun c => f (e.symm c)
  left_inv f := by funext c; exact congrArg f (e.apply_symm_apply c)
  right_inv f := by funext d; exact congrArg f (e.symm_apply_apply d)

@[simp] theorem piEquivOfEquiv_apply {γ δ : Type*} (e : δ ≃ γ) (W : Type*) (f : γ → W)
    (d : δ) : piEquivOfEquiv e W f d = f (e d) := rfl

@[simp] theorem piEquivOfEquiv_apply_eq {γ δ : Type*} (e : δ ≃ γ) (W : Type*) (f : γ → W) :
    piEquivOfEquiv e W f = fun d => f (e d) := rfl

/-! ## The pins, as set indicators -/

/-- The pin at the last label: `1` on the tuples whose last entry is `w`.  Written as a set
indicator so that the term carries no decidability instance. -/
noncomputable def pinLast {W : Type*} (w : W) {p : ℕ} (y : Fin (p + 1) → W) : ℝ≥0∞ :=
  ({y' : Fin (p + 1) → W | y' (Fin.last p) = w} : Set (Fin (p + 1) → W)).indicator
    (fun _ => (1 : ℝ≥0∞)) y

theorem pinLast_of_mem {W : Type*} {w : W} {p : ℕ} {y : Fin (p + 1) → W}
    (h : y (Fin.last p) = w) : pinLast w y = 1 :=
  Set.indicator_of_mem (s := {y' : Fin (p + 1) → W | y' (Fin.last p) = w})
    (f := fun _ => (1 : ℝ≥0∞)) h

theorem pinLast_of_notMem {W : Type*} {w : W} {p : ℕ} {y : Fin (p + 1) → W}
    (h : ¬ y (Fin.last p) = w) : pinLast w y = 0 :=
  Set.indicator_of_notMem (s := {y' : Fin (p + 1) → W | y' (Fin.last p) = w})
    (f := fun _ => (1 : ℝ≥0∞)) h

/-- The pin at the mark label. -/
noncomputable def pinMark {W : Type*} (w : W) {p : ℕ} (y : Label p → W) : ℝ≥0∞ :=
  ({y' : Label p → W | y' (markLabel p) = w} : Set (Label p → W)).indicator
    (fun _ => (1 : ℝ≥0∞)) y

theorem pinMark_of_mem {W : Type*} {w : W} {p : ℕ} {y : Label p → W}
    (h : y (markLabel p) = w) : pinMark w y = 1 :=
  Set.indicator_of_mem (s := {y' : Label p → W | y' (markLabel p) = w})
    (f := fun _ => (1 : ℝ≥0∞)) h

theorem pinMark_of_notMem {W : Type*} {w : W} {p : ℕ} {y : Label p → W}
    (h : ¬ y (markLabel p) = w) : pinMark w y = 0 :=
  Set.indicator_of_notMem (s := {y' : Label p → W | y' (markLabel p) = w})
    (f := fun _ => (1 : ℝ≥0∞)) h

/-! ## The marked atlas sum, using the integrated marked carrier -/

/-- **The marked atlas sum**: over the fully labelled `(p+1)`-leaf shapes and the positions of
their internal vertices, the atlas products at the terminal tuples whose last label is the
physical vertex `w`. -/
noncomputable def markedAtlasSum {W : Type*} (π : Sym2 W → unitInterval) (x w : W) (p : ℕ) :
    ℝ≥0∞ :=
  ∑' t : LTon (Fin (p + 1)) (Finset.univ : Finset (Fin (p + 1))),
    ∑' φ : t.1.IPos → W, ∑' y : Fin (p + 1) → W,
      pinLast w y * CanonAtlas.Measure.atlasProduct π x y t.1 φ

end PercLib.CriticalLRP.I417MarkedRelabel
