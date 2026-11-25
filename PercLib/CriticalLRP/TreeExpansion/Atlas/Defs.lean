/- Integrated from reviewed Ultramath combinatorics.
Production base e387aba5a75e414ca007951b6333ffa5af720573.
Scratch source: ../../.ultramath/smwvlmbqa/m1/Defs.lean; module paths rewritten.
-/

module

public import PercLib.CriticalLRP.TreeExpansion.Basic
public import PercLib.CriticalLRP.VolumeMoments.DFactorial

/-!
# Atlases of Lemma I.4.16: addresses, depth-parity classes, star edges, hub sets

This file fixes the finite combinatorial objects used by the proof of Lemma I.4.16
(generalised tree-graph inequality) of

  T. Hutchcroft, *Critical long-range percolation I: High effective dimension*,
  arXiv:2508.18807v1, pp. 43--45,

and it is written against the **current production** tree layer
`PercLib.CriticalLRP.TreeExpansion.Basic` and the production double factorial
`PercLib.CriticalLRP.VolumeMoments.M`.  It replaces the earlier attempt in
`.ultramath/smwvk712v/m8/`, which was written against the obsolete
`CriticalLongRangePercolation` module and namespace; nothing of that directory is trusted
here, only the statements that this file proves about production `RTree`.

The paper says:

> "partitioning the internal vertices of the binary tree into bipartite classes: since there
> are `p - 1` internal vertices, the larger of these bipartite classes must have size at
> least `⌈(p-1)/2⌉`. Taking a subset of this class of size `k`, this lets us partition the
> edges of the tree into the 3-stars around each vertex in this set and the remaining edges
> of the tree that are not adjacent to a vertex in this set."

The **atlas** attached to production `t : RTree α` with `p = t.numLeaves` leaves is the tree
obtained by adjoining one further leaf `0` above the root of `t`.  In the atlas

* the internal vertices are the internal vertices of `t` — `p - 1` of them, production's
  `RTree.card_ipos`; production's `RTree.IPos t` *is* that vertex type;
* the leaves are the `p` leaves of `t` together with the root leaf `0`;
* every internal vertex has degree three, so the atlas has `2p - 1` edges
  (`RTree.card_atlasEdge_leaves` below).

Every atlas edge other than the one to the root leaf joins an internal vertex to one of its
two children, so edges are encoded by their **down** endpoint: `RTree.AtlasEdge t` is
(internal address, child bit) together with one exceptional `Sum.inr` summand for the root
edge.  The *up* edge of an internal vertex `v` is the down edge of its parent, so the 3-star
of `v` — its two child edges and its parent edge — is a three-element set of atlas edges.

Internal vertices are addressed by words in `List Bool` (`[]` is the root of `t`, `false`
and `true` pick the left and the right child), which makes the depth parity `s.length % 2`
the bipartition of the internal vertices, and `List.dropLast` the parent map.  The root leaf
of the atlas is encoded as `none : Option (List Bool)` (`RTree.atlasLeaves`).

## Main definitions

* `RTree.subAt` — the subtree at an address;
* `RTree.ipaths` — addresses of the internal vertices (`p - 1` of them);
* `RTree.lpaths` — addresses of the leaves of `t` (`p` of them);
* `RTree.atlasLeaves` — the leaves of the atlas (`p + 1` of them, root leaf `none`);
* `RTree.AtlasEdge` — the `2p - 1` edges of the atlas, as a finite type;
* `RTree.upEdge`, `RTree.star` — the up edge and the 3-star of an internal vertex;
* `RTree.evenHubs`, `RTree.oddHubs` — the two bipartite classes of internal vertices;
* `RTree.hubEdges`, `RTree.offHubEdges` — the atlas edges incident with, respectively not
  adjacent to, a set of hubs given by addresses;
* `RTree.iposOfPath`, `RTree.pathOf` — the bijection between internal addresses and
  production's internal vertices `RTree.IPos t` (round trips in `Bridge.lean`);
* `RTree.iposDepth`, `RTree.iposEvenHubs`, `RTree.iposOddHubs` — depth and the bipartition
  classes on `RTree.IPos t`;
* `RTree.hubEdgesIpos`, `RTree.offHubEdgesIpos` — the same edge sets for a hub set given by
  production vertices.

## Files of the layer

* `Defs.lean` — the definitions above (this file);
* `Hub.lean` — bipartition counts, hub selection, 3-star disjointness and cardinality, the
  three leaf arms at a hub;
* `Edges.lean` — `#AtlasEdge t = 2p - 1` and the honest edge partition at a hub set;
* `Bridge.lean` — internal addresses are production's internal vertices, and hub selection
  on `RTree.IPos`;
* `Interface.lean` — the arithmetic a consumer needs (`3k ≤ 2p - 1`, exponent bookkeeping)
  and same-parity vertices are not adjacent;
* `Arms.lean` — the three nonempty arms at a hub in the atlas leaf set;
* `Check.lean` — the `p = 6`, `k = 2` instance used in Case 2 of the paper is non-vacuous;
* `Audit.lean`, `audit.sh` — standard-axiom audit.

No probability is formalised here: the BK step itself is **not** in this layer, see
`README.md`.
-/

@[expose] public section

set_option autoImplicit false

namespace PercLib.CriticalLRP.TreeExpansion

namespace RTree

variable {α : Type*}

/-! ### Addresses -/

/-- The subtree of `t` reached by following the address `s` (`false` = left, `true` =
right). -/
def subAt : (t : RTree α) → List Bool → Option (RTree α)
  | t, [] => some t
  | leaf _, _ :: _ => none
  | node l _, false :: s => subAt l s
  | node _ r, true :: s => subAt r s

@[simp] theorem subAt_nil (t : RTree α) : subAt t [] = some t := by
  cases t <;> rfl

@[simp] theorem subAt_node_false (l r : RTree α) (s : List Bool) :
    subAt (node l r) (false :: s) = subAt l s := rfl

@[simp] theorem subAt_node_true (l r : RTree α) (s : List Bool) :
    subAt (node l r) (true :: s) = subAt r s := rfl

@[simp] theorem subAt_leaf_cons (a : α) (b : Bool) (s : List Bool) :
    subAt (leaf a) (b :: s) = none := by
  cases b <;> rfl

/-- Concatenating addresses. -/
theorem subAt_append (t : RTree α) (p u : List Bool) :
    subAt t (p ++ u) = (subAt t p).bind (fun T => subAt T u) := by
  induction p generalizing t with
  | nil => rw [List.nil_append, subAt_nil]; rfl
  | cons b p ih =>
      cases t with
      | leaf a => cases b <;> rfl
      | node l r => cases b <;> exact ih _

/-- Addresses of the internal vertices of a rooted binary tree. -/
def ipaths : (t : RTree α) → Finset (List Bool)
  | leaf _ => ∅
  | node l r =>
      insert [] ((ipaths l).image (fun s => false :: s) ∪
        (ipaths r).image (fun s => true :: s))

/-- Addresses of the leaves of a rooted binary tree. -/
def lpaths : (t : RTree α) → Finset (List Bool)
  | leaf _ => {[]}
  | node l r =>
      (lpaths l).image (fun s => false :: s) ∪ (lpaths r).image (fun s => true :: s)

theorem mem_lpaths : ∀ (t : RTree α) (s : List Bool),
    s ∈ lpaths t ↔ ∃ a : α, subAt t s = some (leaf a)
  | leaf _, s => by
      cases s with
      | nil => simp [lpaths]
      | cons b s => cases b <;> simp [lpaths]
  | node l r, s => by
      cases s with
      | nil => simp [lpaths]
      | cons b s => cases b with
          | false => simp [lpaths, mem_lpaths l s]
          | true => simp [lpaths, mem_lpaths r s]

theorem mem_ipaths : ∀ (t : RTree α) (s : List Bool),
    s ∈ ipaths t ↔ ∃ l r : RTree α, subAt t s = some (node l r)
  | leaf _, s => by
      cases s with
      | nil => simp [ipaths]
      | cons b s => cases b <;> simp [ipaths]
  | node l r, s => by
      cases s with
      | nil => simp [ipaths]
      | cons b s => cases b with
          | false => simp [ipaths, mem_ipaths l s]
          | true => simp [ipaths, mem_ipaths r s]

/-- The parent of an internal vertex is internal. -/
theorem dropLast_mem_ipaths {t : RTree α} {s : List Bool} (hs : s ∈ ipaths t)
    (hne : s ≠ []) : s.dropLast ∈ ipaths t := by
  obtain ⟨l, r, hl⟩ := (mem_ipaths t s).mp hs
  have hsplit : s.dropLast ++ [s.getLast hne] = s := List.dropLast_append_getLast hne
  rw [← hsplit, subAt_append] at hl
  cases hT : subAt t s.dropLast with
  | none => rw [hT] at hl; simp at hl
  | some T =>
      rw [hT] at hl
      simp only [Option.bind_some] at hl
      cases T with
      | leaf a => simp at hl
      | node l' r' => exact (mem_ipaths t s.dropLast).mpr ⟨l', r', hT⟩

/-! ### The edges of the atlas -/

/-- The edges of the atlas of `t`: the down edge from the internal vertex `v` to its `b`
child, together with (as the exceptional `Sum.inr` summand) the edge joining the root of `t`
to the root leaf `0`. -/
abbrev AtlasEdge (t : RTree α) : Type := ({s : List Bool // s ∈ ipaths t} × Bool) ⊕ PUnit

instance instFintypeAtlasEdge (t : RTree α) : Fintype (AtlasEdge t) := by
  unfold AtlasEdge
  infer_instance

instance instDecidableEqAtlasEdge (t : RTree α) : DecidableEq (AtlasEdge t) := by
  unfold AtlasEdge
  infer_instance

/-- The *up* edge of an internal vertex: the edge joining it to its parent, which for the
root is the edge to the root leaf `0`. -/
noncomputable def upEdge (t : RTree α) (s : List Bool) (hs : s ∈ ipaths t) : AtlasEdge t :=
  if h : s = [] then Sum.inr ⟨⟩
  else
    Sum.inl ((⟨s.dropLast, dropLast_mem_ipaths hs h⟩, s.getLast h) :
      {u : List Bool // u ∈ ipaths t} × Bool)

/-- The **3-star** at the internal vertex with address `s`: its two down edges and its up
edge. -/
noncomputable def star (t : RTree α) (s : List Bool) (hs : s ∈ ipaths t) :
    Finset (AtlasEdge t) :=
  {Sum.inl (⟨s, hs⟩, false), Sum.inl (⟨s, hs⟩, true), upEdge t s hs}

theorem mem_star {t : RTree α} {s : List Bool} (hs : s ∈ ipaths t) {e : AtlasEdge t} :
    e ∈ star t s hs ↔
      e = Sum.inl (⟨s, hs⟩, false) ∨ e = Sum.inl (⟨s, hs⟩, true) ∨ e = upEdge t s hs := by
  simp [star]

/-! ### The bipartite classes of the internal vertices -/

/-- The bipartite class of internal vertices at even depth. -/
def evenHubs (t : RTree α) : Finset (List Bool) :=
  (ipaths t).filter (fun s => s.length % 2 = 0)

/-- The bipartite class of internal vertices at odd depth. -/
def oddHubs (t : RTree α) : Finset (List Bool) :=
  (ipaths t).filter (fun s => s.length % 2 = 1)


/-! ### Hub edge sets -/

/-- The edges of the atlas that are incident with the hub set `S`. -/
noncomputable def hubEdges (t : RTree α) (S : Finset (List Bool)) (hS : S ⊆ ipaths t) :
    Finset (AtlasEdge t) :=
  S.attach.biUnion (fun p => star t p.1 (hS p.2))

/-- The atlas edges that are **not** adjacent to the hub set `S`. -/
noncomputable def offHubEdges (t : RTree α) (S : Finset (List Bool))
    (hS : S ⊆ ipaths t) : Finset (AtlasEdge t) :=
  Finset.univ \ hubEdges t S hS

/-! ### The same objects on production's internal vertices `IPos` -/

/-- The internal vertex of `t` lying at the address `s`. -/
def iposOfPath : (t : RTree α) → (s : List Bool) → s ∈ ipaths t → IPos t
  | leaf _, _, hs => absurd hs (by simp [ipaths])
  | node _ _, [], _ => Sum.inr (Sum.inr ⟨⟩)
  | node l _, false :: s, hs => Sum.inl (iposOfPath l s (by simpa [ipaths] using hs))
  | node _ r, true :: s, hs => Sum.inr (Sum.inl (iposOfPath r s (by simpa [ipaths] using hs)))

/-- The address of an internal vertex. -/
def pathOf : (t : RTree α) → IPos t → {s : List Bool // s ∈ ipaths t}
  | leaf _, v => nomatch v
  | node l _, Sum.inl a =>
      ⟨false :: (pathOf l a).1, by
        refine Finset.mem_insert_of_mem (Finset.mem_union_left _ ?_)
        exact Finset.mem_image.mpr ⟨_, (pathOf l a).2, rfl⟩⟩
  | node _ r, Sum.inr (Sum.inl b) =>
      ⟨true :: (pathOf r b).1, by
        refine Finset.mem_insert_of_mem (Finset.mem_union_right _ ?_)
        exact Finset.mem_image.mpr ⟨_, (pathOf r b).2, rfl⟩⟩
  | node _ _, Sum.inr (Sum.inr _) => ⟨[], by simp [ipaths]⟩

/-- The depth of an internal vertex: the length of its address. -/
def iposDepth (t : RTree α) (v : IPos t) : ℕ := (pathOf t v).1.length

/-- The bipartition class of internal vertices at even depth. -/
def iposEvenHubs (t : RTree α) : Finset (IPos t) :=
  Finset.univ.filter (fun v => iposDepth t v % 2 = 0)

/-- The bipartition class of internal vertices at odd depth. -/
def iposOddHubs (t : RTree α) : Finset (IPos t) :=
  Finset.univ.filter (fun v => iposDepth t v % 2 = 1)

/-! ### Hub edge sets of a set of production vertices -/

/-- The 3-stars of a set of hubs, as a set of atlas edges. -/
noncomputable def hubEdgesIpos (t : RTree α) (S : Finset (IPos t)) : Finset (AtlasEdge t) :=
  S.attach.biUnion (fun p => star t (pathOf t p.1).1 (pathOf t p.1).2)

/-- The atlas edges not adjacent to a set of hubs. -/
noncomputable def offHubEdgesIpos (t : RTree α) (S : Finset (IPos t)) :
    Finset (AtlasEdge t) :=
  Finset.univ \ hubEdgesIpos t S

/-! ### The leaves of the atlas -/

/-- The leaves of the atlas of `t`: its `p` leaves together with the root leaf `0`, encoded as
`none`. -/
def atlasLeaves (t : RTree α) : Finset (Option (List Bool)) :=
  insert none ((lpaths t).image some)


/-- A concrete atlas with `6` leaves (a `Fin 6`-labelled tree). -/
def atlasSix : RTree (Fin 6) :=
  node (node (leaf 0) (leaf 1)) (node (node (leaf 2) (leaf 3)) (node (leaf 4) (leaf 5)))

end RTree

end PercLib.CriticalLRP.TreeExpansion
