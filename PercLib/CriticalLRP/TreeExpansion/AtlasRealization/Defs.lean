/- Integrated from independently rebuilt Ultramath work.
Production base 70b027b0634874e65ce4bf8ec8fc8a7835e658e7.
Scratch source: repository-root .ultramath/smwwnvyp3/m4/.
-/

/-
Independent definitions for the present swarm member (target B).

Formalizes the *atlas realization* of a terminal-connected percolation configuration used in
the proof of Lemma I.4.16 (generalized tree-graph inequality) of

  T. Hutchcroft, *Critical long-range percolation I: High effective dimension*,
  arXiv:2508.18807v1, pp. 43--45.

The source proof takes a union bound over the combinatorial structures of a binary tree
connecting the origin to `p` labelled vertices: a rooted binary tree shape with `p` labelled
leaves, one further (root) leaf, and an assignment of a cluster vertex to every internal
vertex, together with edge-disjoint open paths for the `2p - 1` edges of the resulting
*atlas*.  Nothing of that realization exists in production: `TreeExpansion/Atlas` contains
only the shape side (addresses, depth parity, 3-stars, hub edge partitions) and the
tree-graph layer only the ordinary recursion.  This file fixes the data.

## Modelling choices, and why they are faithful

* `RTree α` is production's rooted binary tree with leaves labelled by `α`.  A *shape* for
  the labelled terminals is an `RTree α` whose leaf list is nodup and has leaf set the given
  finite label set `Z` (`IsLabelledShape`); this is exactly production's `LTon α Z`, so the
  shape family is the `(2p - 3)!!` family and not the leaf permutations of one chain.
* Leaf positions are not free: the leaf carrying label `a` sits at the terminal vertex `y a`.
  Only the internal vertices get free positions `φ`, which is the paper's "sum over relevant
  vertices".  Distinct internal vertices of the shape remain distinct positions of the shape
  even when `φ` gives them the same vertex, which is exactly the situation in BK, where
  disjointness is a property of *edges*, not vertices.
* `AEdge t` enumerates the `2p - 1` atlas edges: the two down edges of every internal vertex,
  plus the single edge joining the root leaf to the root of `t` (for `t` a single leaf this is
  the edge from the root leaf to that leaf, so `p = 1` gives one edge, matching production's
  `RTree.AtlasEdge` cardinality `2 * numLeaves - 1`).
* `srcPos`/`dstPos` give the two *ends* of an atlas edge: the internal end `φ u` (or the root
  leaf's vertex `c`), and the child end, which is `φ` of the child when the child is internal
  and the terminal `y a` of the label `a` when the child is a leaf.
* `IsRealization` says: every atlas edge carries a set of open edges `wit e ⊆ s` connecting
  its two ends, and distinct atlas edges carry *disjoint* sets.  Nonemptiness is not
  required: an empty witness is allowed exactly when the two ends coincide, which is the
  degenerate case where the source's product of connection probabilities carries a factor
  `P(w ↔ w) = 1`.  No edge of `s` is ever used by two different atlas edges, so degenerate
  edges cannot be charged to two different disjoint pieces.

The covering theorem `Real.exists_realization` (in `Realize.lean`) is the missing
all-configurations step: for every configuration and every label set connected to the root it
produces such a shape and such a realization.  The probabilistic consumer (union bound over
shapes and positions, then BK) is in `Cover.lean`.
-/
module

public import PercLib.CriticalLRP.TreeExpansion.BranchSplit
public import PercLib.CriticalLRP.TreeExpansion.LabelledWeights
public import PercLib.CriticalLRP.TreeExpansion.Atlas.Structure
public import PercLib.CriticalLRP.TreeGraph.ThreePoint

/-! Atlas realization, covering and defs lemmas. -/

@[expose] public section

set_option autoImplicit false
set_option linter.unusedSectionVars false
set_option linter.unusedFintypeInType false
set_option linter.unusedDecidableInType false

namespace PercLib.CriticalLRP.TreeExpansion.Real

open Finset
open PercLib.CriticalLRP.TreeGraph (Conn)

variable {V : Type*} [DecidableEq V]
variable {E : Type*} [Fintype E] [DecidableEq E]
variable {α : Type*} [DecidableEq α]

/-! ### The edges of the atlas -/

/-- The edges of the atlas of `t`: the down edge of each internal vertex to its `false`
child, the down edge to its `true` child, and the root edge joining the root leaf to the root
of `t`.  (`Sum.inl (u, b)` is the down edge of the internal vertex `u` in direction `b`;
`Sum.inr` is the root edge.) -/
abbrev AEdge (t : RTree α) : Type := (t.IPos × Bool) ⊕ PUnit

instance instFintypeAEdge (t : RTree α) : Fintype (AEdge t) := by
  unfold AEdge; infer_instance

instance instDecidableEqAEdge (t : RTree α) : DecidableEq (AEdge t) := by
  unfold AEdge; infer_instance

/-- The vertex at the root of the shape `t`: the terminal at that position when `t` is a
leaf, and the position of the internal root otherwise. -/
def rootPos : (t : RTree α) → (t.IPos → V) → (α → V) → V
  | RTree.leaf a, _, y => y a
  | RTree.node _ _, φ, _ => φ (Sum.inr (Sum.inr ⟨⟩))

/-- The vertex at the child of the internal vertex `u` in the child direction `b`. -/
def childPos : (t : RTree α) → (t.IPos → V) → (α → V) → t.IPos → Bool → V
  | RTree.leaf _, _, _, u, _ => nomatch u
  | RTree.node l r, φ, y, u, b => match u with
    | Sum.inl u => childPos l (fun v => φ (Sum.inl v)) y u b
    | Sum.inr (Sum.inl v) => childPos r (fun w => φ (Sum.inr (Sum.inl w))) y v b
    | Sum.inr (Sum.inr _) => if b then rootPos r (fun w => φ (Sum.inr (Sum.inl w))) y
        else rootPos l (fun v => φ (Sum.inl v)) y

/-- The upper end of an atlas edge: the internal vertex itself, or the root leaf's vertex. -/
def srcPos (t : RTree α) (φ : t.IPos → V) (c : V) : AEdge t → V
  | Sum.inl (u, _) => φ u
  | Sum.inr _ => c

/-- The lower end of an atlas edge: the child position. -/
def dstPos (t : RTree α) (φ : t.IPos → V) (y : α → V) : AEdge t → V
  | Sum.inl (u, b) => childPos t φ y u b
  | Sum.inr _ => rootPos t φ y

/-! ### Shapes with a prescribed leaf-label set -/

/-- The leaf list of `t` is injective and has leaf set `Z`: the shape family for the labelled
terminals `Z`.  This is definitionally production's `LTon α Z`. -/
def IsLabelledShape (t : RTree α) (Z : Finset α) : Prop :=
  t.leaves.Nodup ∧ t.leaves.toFinset = Z

/-! ### Realizations -/

/-- A realization of the atlas of `t` inside the configuration `s`: distinct atlas edges are
witnessed by pairwise edge-disjoint sets of open edges of `s` connecting their two ends.
`c` is the vertex at the root leaf, `φ` the positions of the internal vertices and `y` the
positions of the terminal leaves. -/
structure IsRealization (ends : E → Sym2 V) (s : Finset E) (y : α → V) (c : V)
    {t : RTree α} (φ : t.IPos → V) (wit : AEdge t → Finset E) : Prop where
  /-- every witness is a set of open edges -/
  subset : ∀ e, wit e ⊆ s
  /-- distinct atlas edges have disjoint witnesses; no open edge is charged twice -/
  disjoint : ∀ e e', e ≠ e' → Disjoint (wit e) (wit e')
  /-- each witness connects the two ends of its atlas edge -/
  conn : ∀ e, Conn ends (wit e) (srcPos t φ c e) (dstPos t φ y e)

/-! ### The one-step split of a terminal-connected configuration

The data produced at a single branch point: three pairwise disjoint open edge sets, one
joining the current root `v` to the branch point `w`, and two carrying the two nonempty groups
of labels out of `w`.  It is stated relative to a *given* witness set `W` (the incoming
connection), so that all pieces stay inside `W` and hence inside the incoming witness of the
enclosing diagram. -/

/-- The one-step decomposition at a branch point, relative to a given witness set `W`. -/
def SplitAt (ends : E → Sym2 V) (W : Finset E) (v : V) (y : α → V) (Z A : Finset α)
    (w : V) (W0 WA WB : Finset E) : Prop :=
  A ⊆ Z ∧ A.Nonempty ∧ (Z \ A).Nonempty ∧
  W0 ⊆ W ∧ WA ⊆ W ∧ WB ⊆ W ∧
  Disjoint W0 WA ∧ Disjoint W0 WB ∧ Disjoint WA WB ∧
  Conn ends W0 v w ∧
  (∀ a ∈ A, Conn ends WA w (y a)) ∧
  (∀ b ∈ Z \ A, Conn ends WB w (y b))

/-! ### Composition of realizations -/

/-- The position of an internal vertex of `node l r` read off the two halves. -/
def pushPhi {l r : RTree α} (w : V) (φl : l.IPos → V) (φr : r.IPos → V) :
    (RTree.node l r).IPos → V
  | Sum.inl u => φl u
  | Sum.inr (Sum.inl v) => φr v
  | Sum.inr (Sum.inr _) => w

theorem srcPos_inl {t : RTree α} (φ : t.IPos → V) (c : V) (u : t.IPos) (b : Bool) :
    srcPos t φ c (Sum.inl (u, b)) = φ u := rfl

theorem dstPos_inl {t : RTree α} (φ : t.IPos → V) (y : α → V) (u : t.IPos)
    (b : Bool) : dstPos t φ y (Sum.inl (u, b)) = childPos t φ y u b := rfl

theorem srcPos_root {t : RTree α} (φ : t.IPos → V) (c : V) (x : PUnit) :
    srcPos t φ c (Sum.inr x) = c := rfl

theorem dstPos_root {t : RTree α} (φ : t.IPos → V) (y : α → V) (x : PUnit) :
    dstPos t φ y (Sum.inr x) = rootPos t φ y := rfl

@[simp] theorem rootPos_leaf (a : α) (φ : (RTree.leaf a).IPos → V) (y : α → V) :
    rootPos (RTree.leaf a) φ y = y a := rfl

@[simp] theorem rootPos_node (l r : RTree α) (φ : (RTree.node l r).IPos → V) (y : α → V) :
    rootPos (RTree.node l r) φ y = φ (Sum.inr (Sum.inr ⟨⟩)) := rfl

/-! ### Splitting the atlas edges of a composite shape

The `2 * (pL + pR) - 1` atlas edges of `node l r` are the `2 pL - 1` edges of `l`, the
`2 pR - 1` edges of `r`, and the one new root edge; `aedgeSumFun` is that splitting, an
explicit bijection, used to transfer the disjointness of the witnesses of the two halves to
the composite.  The three families of lemmas below are stated on the pieces themselves, so
that every composite atlas edge is handled through the piece it belongs to. -/

/-- Splitting the atlas edges of `node l r` into the edges of `l`, the edges of `r`, and the
new root edge. -/
def aedgeSumFun {l r : RTree α} : AEdge (RTree.node l r) → AEdge l ⊕ AEdge r ⊕ PUnit
  | Sum.inl (Sum.inl u, b) => Sum.inl (Sum.inl (u, b))
  | Sum.inl (Sum.inr (Sum.inl v), b) => Sum.inr (Sum.inl (Sum.inl (v, b)))
  | Sum.inl (Sum.inr (Sum.inr _), false) => Sum.inl (Sum.inr ⟨⟩)
  | Sum.inl (Sum.inr (Sum.inr _), true) => Sum.inr (Sum.inl (Sum.inr ⟨⟩))
  | Sum.inr x => Sum.inr (Sum.inr x)

/-- The inverse splitting. -/
def aedgeSumInv {l r : RTree α} : AEdge l ⊕ AEdge r ⊕ PUnit → AEdge (RTree.node l r)
  | Sum.inl (Sum.inl (u, b)) => Sum.inl (Sum.inl u, b)
  | Sum.inl (Sum.inr x) => Sum.inl (Sum.inr (Sum.inr x), false)
  | Sum.inr (Sum.inl (Sum.inl (v, b))) => Sum.inl (Sum.inr (Sum.inl v), b)
  | Sum.inr (Sum.inl (Sum.inr x)) => Sum.inl (Sum.inr (Sum.inr x), true)
  | Sum.inr (Sum.inr x) => Sum.inr x

theorem aedgeSumInv_fun {l r : RTree α} (e : AEdge (RTree.node l r)) :
    aedgeSumInv (aedgeSumFun e) = e := by
  rcases e with (⟨u, b⟩ | x)
  · rcases u with (u | u | ⟨⟩)
    · rfl
    · rfl
    · cases b <;> rfl
  · rfl

theorem aedgeSumFun_inv {l r : RTree α} (s : AEdge l ⊕ AEdge r ⊕ PUnit) :
    aedgeSumFun (aedgeSumInv s) = s := by
  rcases s with (⟨u, b⟩ | x) | (⟨v, b⟩ | x) <;> rfl

/-- The atlas edges of `node l r` split into those of `l`, those of `r`, and the root edge. -/
noncomputable def aedgeSumEquiv (l r : RTree α) :
    AEdge (RTree.node l r) ≃ AEdge l ⊕ AEdge r ⊕ PUnit where
  toFun := aedgeSumFun
  invFun := aedgeSumInv
  left_inv := aedgeSumInv_fun
  right_inv := aedgeSumFun_inv

/-- The witness of an atlas edge of `node l r`: the piece it belongs to, and the incoming
witness `W0` on the new root edge. -/
def pushWit {l r : RTree α} (W0 : Finset E) (witL : AEdge l → Finset E)
    (witR : AEdge r → Finset E) (e : AEdge (RTree.node l r)) : Finset E :=
  match aedgeSumFun e with
  | Sum.inl a => witL a
  | Sum.inr (Sum.inl b) => witR b
  | Sum.inr (Sum.inr _) => W0

section Pieces

variable {l r : RTree α} {W0 : Finset E} {witL : AEdge l → Finset E}
  {witR : AEdge r → Finset E} {φL : l.IPos → V} {φR : r.IPos → V} {y : α → V} {c w : V}

theorem pushWit_inl (a : AEdge l) :
    pushWit W0 witL witR (aedgeSumInv (Sum.inl a)) = witL a := by
  rcases a with (⟨u, b⟩ | x) <;> rfl

theorem pushWit_inr_inl (b : AEdge r) :
    pushWit W0 witL witR (aedgeSumInv (Sum.inr (Sum.inl b))) = witR b := by
  rcases b with (⟨v, b⟩ | x) <;> rfl

theorem pushWit_none (x : PUnit) :
    pushWit W0 witL witR (aedgeSumInv (Sum.inr (Sum.inr x))) = W0 := rfl

theorem srcPos_piece_inl (a : AEdge l) :
    srcPos (RTree.node l r) (pushPhi w φL φR) c (aedgeSumInv (Sum.inl a)) =
      srcPos l φL w a := by
  rcases a with (⟨u, b⟩ | x) <;> rfl

theorem dstPos_piece_inl (a : AEdge l) :
    dstPos (RTree.node l r) (pushPhi w φL φR) y (aedgeSumInv (Sum.inl a)) =
      dstPos l φL y a := by
  rcases a with (⟨u, b⟩ | x) <;> rfl

theorem srcPos_piece_inr_inl (b : AEdge r) :
    srcPos (RTree.node l r) (pushPhi w φL φR) c (aedgeSumInv (Sum.inr (Sum.inl b))) =
      srcPos r φR w b := by
  rcases b with (⟨v, b⟩ | x) <;> rfl

theorem dstPos_piece_inr_inl (b : AEdge r) :
    dstPos (RTree.node l r) (pushPhi w φL φR) y (aedgeSumInv (Sum.inr (Sum.inl b))) =
      dstPos r φR y b := by
  rcases b with (⟨v, b⟩ | x) <;> rfl

theorem srcPos_piece_none (x : PUnit) :
    srcPos (RTree.node l r) (pushPhi w φL φR) c (aedgeSumInv (Sum.inr (Sum.inr x))) = c := rfl

theorem dstPos_piece_none (x : PUnit) :
    dstPos (RTree.node l r) (pushPhi w φL φR) y (aedgeSumInv (Sum.inr (Sum.inr x))) = w := rfl

theorem aedgeSumFun_eq_of_eq_inv_inl {e : AEdge (RTree.node l r)} {a : AEdge l}
    (h : e = aedgeSumInv (Sum.inl a)) : aedgeSumFun e = Sum.inl a := by rw [h, aedgeSumFun_inv]

theorem aedgeSumFun_eq_of_eq_inv_inr_inl {e : AEdge (RTree.node l r)} {b : AEdge r}
    (h : e = aedgeSumInv (Sum.inr (Sum.inl b))) : aedgeSumFun e = Sum.inr (Sum.inl b) := by
  rw [h, aedgeSumFun_inv]

theorem aedgeSumFun_eq_of_eq_inv_none {e : AEdge (RTree.node l r)} {x : PUnit}
    (h : e = aedgeSumInv (Sum.inr (Sum.inr x))) : aedgeSumFun e = Sum.inr (Sum.inr x) := by
  rw [h, aedgeSumFun_inv]

end Pieces

/-! ## Realization and disjoint-occurrence events -/

/-- Disjoint occurrence `∘` of an arbitrary finite family of events: pairwise disjoint witness
sets inside the configuration, each already satisfying its event.  This is production's
`DisjOccK` with a general finite index type. -/
def DisjOcc {ι : Type*} (A : ι → Set (Finset E)) : Set (Finset E) :=
  {ω | ∃ W : ι → Finset E, (∀ i, W i ⊆ ω) ∧ (∀ i, W i ∈ A i) ∧
    ∀ i j, i ≠ j → Disjoint (W i) (W j)}


/-- The connection event of a single atlas edge: its two ends are connected by open edges. -/
def ConnEvent (ends : E → Sym2 V) (y : α → V) (c : V) (t : RTree α) (φ : t.IPos → V)
    (e : AEdge t) : Set (Finset E) :=
  {ω | Conn ends ω (srcPos t φ c e) (dstPos t φ y e)}

/-- The diagram event of the shape `t` with internal positions `φ`: the configuration contains
pairwise edge-disjoint witnesses for all `2 #t.leaves - 1` atlas edges.  This is precisely the
disjoint occurrence of the atlas-edge connection events, hence a single joint event. -/
def DiagEvent (ends : E → Sym2 V) (y : α → V) (c : V) (t : RTree α)
    (φ : t.IPos → V) : Set (Finset E) :=
  {ω | ∃ wit : AEdge t → Finset E, IsRealization ends ω y c φ wit}


end PercLib.CriticalLRP.TreeExpansion.Real
