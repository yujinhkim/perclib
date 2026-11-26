/-
Independent UltraMath work, swarm `smwwsmqji`, member `m1`.
Production base `50c2eed0682a7e1b078ae771dbef463ebe00701d`, Lean 4.35.0 (read-only package
`.scratch/critical-lrp-orchestration`). Nothing outside this directory is modified.
-/
module

public import PercLib.CriticalLRP.TreeExpansion.Count
public import PercLib.CriticalLRP.TreeExpansion.Orbit
public import PercLib.CriticalLRP.TreeExpansion.LabelledWeights
public import PercLib.CriticalLRP.TreeExpansion.AtlasRealization.WeightBridge.Orbit
public import PercLib.CriticalLRP.TreeExpansion.AtlasRealization.Defs

/-!
# New definitions of the child-swap orbit count

`RTree α` (`TreeExpansion/Basic.lean`) is a type of *plane* (ordered) rooted binary trees, and
`RTree.swapFiber t` (`TreeExpansion/Orbit.lean`) is the finite set of plane trees obtained from
`t` by independently exchanging the two children at vertices.  The present file packages that
relation as a `Setoid`, and introduces

* `swapOrbits`: the finite set of child-swap orbits of the fully labelled family `RTree.LT α`,
  as a `Finset (Finset (RTree α))` — the honest finite index set of *non-plane* diagrams;
* `orbitRep` and `transversal`: a classically chosen fundamental domain, i.e. exactly one plane
  representative per orbit (the "one representative per child-swap orbit" of the union bound).

The partition, the counting of orbits and the transversal sum identities are proved in
`OrbitCount/Partition.lean` and `OrbitCount/Transversal.lean`.
-/

set_option autoImplicit false

@[expose] public section

namespace PercLib.CriticalLRP.TreeExpansion

namespace RTree

variable {α : Type*}

/-- `swapRel t t'` says that the plane tree `t'` is obtained from the plane tree `t` by
independently exchanging the two children at some vertices: `t` and `t'` are two plane
presentations of one non-plane rooted binary tree. -/
def swapRel [DecidableEq α] (t t' : RTree α) : Prop := t' ∈ swapFiber t

theorem swapRel_refl [DecidableEq α] (t : RTree α) : swapRel t t := swapFiber_self t

theorem swapRel_symm [DecidableEq α] {t t' : RTree α} (h : swapRel t t') : swapRel t' t :=
  swapFiber_symm h

/-- Child swapping is transitive: an orbit determines its members (`swapFiber_congr`). -/
theorem swapRel_trans [DecidableEq α] {t t' t'' : RTree α}
    (h : swapRel t t') (h' : swapRel t' t'') : swapRel t t'' := by
  have h1 : t' ∈ swapFiber t := h
  have h2 : t'' ∈ swapFiber t' := h'
  rw [swapFiber_congr h1] at h2
  exact h2

/-- The child-swap equivalence relation on plane trees.  Its equivalence classes are the
non-plane rooted binary trees underlying the plane trees, and the class of `t` is
`swapFiber t`. -/
def swapSetoid (α : Type*) [DecidableEq α] : Setoid (RTree α) where
  r := swapRel
  iseqv := ⟨swapRel_refl, fun h => swapRel_symm h, fun h h' => swapRel_trans h h'⟩

theorem swapSetoid_r_iff [DecidableEq α] (t t' : RTree α) :
    (swapSetoid α).r t t' ↔ t' ∈ swapFiber t := Iff.rfl

variable [Fintype α] [DecidableEq α] [Fintype (LT α)]

/-- The finite family of child-swap orbits of the fully labelled trees over `α`: one element per
non-plane tree with `Fintype.card α` distinctly labelled leaves. -/
def swapOrbits (α : Type*) [Fintype α] [DecidableEq α] [Fintype (LT α)] :
    Finset (Finset (RTree α)) :=
  Finset.univ.image (fun t : LT α => swapFiber t.val)

/-- The chosen plane representative of a child-swap orbit. -/
noncomputable def orbitRep (α : Type*) [Fintype α] [DecidableEq α] [Fintype (LT α)]
    (S : {S : Finset (RTree α) // S ∈ swapOrbits α}) : RTree α :=
  (Classical.choose (Finset.mem_image.mp S.2)).val

/-- A fundamental domain for the child-swap action on fully labelled trees: exactly one plane
representative of each orbit. -/
noncomputable def transversal (α : Type*) [Fintype α] [DecidableEq α] [Fintype (LT α)] :
    Finset (RTree α) :=
  (swapOrbits α).attach.image (orbitRep α)

end RTree

/-- **The child-swap transport hypothesis** (the precise remaining gap of the shape count).

`SwapTransport ends y c` says that exchanging children does not change the family of diagram
events: for every plane tree `t`, every `t'` obtained from it by child swaps and every atlas
position assignment `φ` of `t`, there is a position assignment `φ'` of `t'` whose diagram event
contains the diagram event of `(t, φ)`.  The intended proof keeps the open witness sets and only
composes the child-swap position bijection with the atlas-edge matching that preserves the
unordered pair of ends; this file states the hypothesis explicitly and proves what it implies.

It is *not* a restatement of a probability bound: it is a statement about `DiagEvent` sets
(`AtlasRealization.Defs`), independent of any measure or of `RTree.wtL`. -/
def SwapTransport {V : Type*} {E : Type*} {α : Type*} [DecidableEq α]
    (ends : E → Sym2 V) (y : α → V) (c : V) : Prop :=
  ∀ (t t' : RTree α), t' ∈ RTree.swapFiber t → ∀ φ : t.IPos → V,
    ∃ φ' : t'.IPos → V, Real.DiagEvent ends y c t φ ⊆ Real.DiagEvent ends y c t' φ'

end PercLib.CriticalLRP.TreeExpansion
