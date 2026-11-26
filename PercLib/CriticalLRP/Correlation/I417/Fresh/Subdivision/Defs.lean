/-
Independently rebuilt and integrated from the accepted `smwx6p0op/m2` artifact
`.ultramath/smwx6p0op/m2/GQDepth`. Production integration revision:
`c83993396c566d21a0abe4051ed84dd6dab6093e`. The coordinator uses the production
namespace and fully qualified imports; this package is diagram infrastructure,
not an event-cover theorem.
-/
module

public import PercLib.CriticalLRP.Correlation.I417.Base.Defs

/-!
Independently built for swarm `smwx6p0op`, member `m2`, direction DEPTH-RANGE-I417.

# The subdivided-edge fresh diagram family of Lemma I.4.17, at arbitrary `q`

Source: T. Hutchcroft, *Critical long-range percolation I: High effective dimension*,
arXiv:2508.18807v1, Lemma I.4.17 and its proof (supplied PDF pp. 45--46):

> "We obtain a bound in terms of tree diagrams with two pinned vertices at `x` and `y`, with
> `2p+2q+1` edges in total, some number `3 ≤ ℓ ≤ p+q+1` of them belong to the path connecting `x`
> and `y`."

The marked (base) side of that expansion is production's `I417Base.tsum_wtE_marked`: a rooted binary
tree on `p+1` leaves, one leaf (the mark `w`) pinned, worth `χ^(2p+1-ℓ)·T^ℓ(x,w)` with
`ℓ = RTree.depth t q` the marked-leaf depth.  That is `2p+1` edges, and production groups the whole
family into `∑_{ℓ} C_ℓ χ^(2p+1-ℓ) T^ℓ` (`I417Base.marked_diagram_by_depth`).

The **fresh** side carries the remaining `2q` edges.  In it the mark `w` is *not* a leaf: it lies on
an open path from `y` to the terminal arm `g j`, i.e. it **subdivides an edge** of a binary tree
whose `q` leaves are the arms.  This file defines that diagram and its weight:

* `treeTot k t v` — the fully summed tree-graph weight `∑_{leaf values} wtE k t · v`, worth
  `χ^(2n-1)` for an `n`-leaf `t` (production's `I417Base.tsum_wtE`);
* `subW k t q ℓ v w` — the weight of the diagram carried by `t` with the edge above the leaf `q`
  subdivided, the subdivision point pinned at `w`, and everything else summed.  `ℓ` is the distance
  from `v` to `w`, i.e. the depth of the arm leaf `q` in the **unsubdivided** tree; the diagram has
  `2·numLeaves t` edges in total, of which `ℓ` lie on the `v`--`w` path;
* `subMono` — the source monomial `χ^(2q-ℓ)·T^ℓ(v,w)` that `subW` evaluates to;
* `freshPoly` — the coefficient-weighted fresh polynomial `∑_{ℓ∈[1,q]} C_ℓ χ^(2q-ℓ) T^ℓ(v,w)`.

`ℓ = 1` is the degenerate subdivision of the edge *above* the whole tree (the mark sits directly
below `y`); `ℓ = RTree.depth t q` is the subdivision of the edge above the arm leaf `q`, which
allows the mark to coincide with an arm value — exactly the `w = g j` degeneration that the fresh
event's `DisjointOccurrence` admits.  Both are genuine members of the family; the sum over arm
values is what absorbs them, and no separate case split is needed.

Definitions only in this file.
-/

open scoped ENNReal NNReal

set_option linter.unusedSectionVars false

@[expose] public section

namespace PercLib.CriticalLRP.I417Fresh.Subdivision

open PercLib.CriticalLRP.TreeExpansion
open PercLib.CriticalLRP.I417Base

universe u

variable {V : Type*} [Countable V] [DecidableEq V]

/-- **The fully summed tree weight.**  `treeTot k t v = ∑' leaf values, wtE k t · v`: the total
weight of a rooted binary tree `t` hanging below the pinned vertex `v`, every vertex below `v`
summed over.  For a kernel with constant row sum `χ` this is `χ^(2·numLeaves t - 1)`
(production's `I417Base.tsum_wtE`). -/
noncomputable def treeTot {α : Type u} (k : V → V → ℝ≥0∞) (t : RTree α) (v : V) : ℝ≥0∞ :=
  ∑' y : t.LeafPos → V, wtE k t y v

/-- **The subdivided-edge fresh diagram.**  `subW k t q ℓ v w` is the weight of the diagram in which
the rooted binary tree `t` (rooted one edge below the pinned vertex `v`) has the edge above the leaf
position `q` subdivided, with the subdivision point pinned at `w` and *all* leaf values and internal
vertices summed over.

`ℓ` is the distance from `v` to `w` in the subdivided diagram, equivalently the depth of the leaf
`q` in the **unsubdivided** tree; the interesting range is `1 ≤ ℓ ≤ RTree.depth t q`.  The diagram
has `2 * t.numLeaves` edges, `ℓ` of them on the `v`--`w` path.

* `ℓ = 1`: the subdivided edge is the one above the whole tree, so `w` is the tree's root, and all
  of `t` hangs below the pinned `w`;
* `ℓ = n + 2` at a node: the edge lies deeper, inside the child on the path to `q`; the other
  child hangs off the path vertex `u` and is fully summed, contributing `treeTot`.

Values of `ℓ` outside `1 ≤ ℓ ≤ RTree.depth t q` are unused (`0` for a node; the leaf branch ignores
`ℓ`); every statement about `subW` below carries the range hypothesis explicitly. -/
noncomputable def subW {α : Type u} (k : V → V → ℝ≥0∞) :
    (t : RTree α) → t.LeafPos → ℕ → V → V → ℝ≥0∞
  | .leaf a, _, _, v, w => k v w * treeTot k (.leaf a) w
  | .node _ _, Sum.inl _, 0, _, _ => 0
  | .node l r, Sum.inl _, 1, v, w => k v w * treeTot k (.node l r) w
  | .node _l r, Sum.inl q, n + 2, v, w =>
      ∑' u, k v u * subW k _l q (n + 1) u w * treeTot k r u
  | .node _l _r, Sum.inr _, 0, _, _ => 0
  | .node l r, Sum.inr _, 1, v, w => k v w * treeTot k (.node l r) w
  | .node l r, Sum.inr q, n + 2, v, w =>
      ∑' u, k v u * treeTot k l u * subW k r q (n + 1) u w

/-- **The source monomial** of a fresh `q`-arm diagram whose mark has path-depth `ℓ`:
`χ^(2q-ℓ)·T^ℓ(v,w)`.  Exponent plus power is exactly `2q`, the number of fresh edges printed in
Lemma I.4.17's `2p+2q+1 = (2p+1) + 2q` split. -/
noncomputable def subMono (k : V → V → ℝ≥0∞) (χ : ℝ≥0∞) (q ℓ : ℕ) (v w : V) : ℝ≥0∞ :=
  χ ^ (2 * q - ℓ) * iterPow k ℓ v w

/-- **The coefficient-weighted fresh polynomial** in the source normalization:
`freshPoly k χ q C v w = ∑_{ℓ∈[1,q]} C ℓ · χ^(2q-ℓ) T^ℓ(v,w)`.

`C ℓ` is meant to be the number of diagrams of the fresh family whose mark has depth `ℓ`; it is a
*coefficient supplied by the consumer*, produced as a finite cardinality by
`fresh_family_by_depth`.  No term of this polynomial is dropped: the `ℓ = q` term
(`χ^q T^q`) is what carries the deepest possible arm. -/
noncomputable def freshPoly (k : V → V → ℝ≥0∞) (χ : ℝ≥0∞) (q : ℕ) (C : ℕ → ℕ) (v w : V) : ℝ≥0∞ :=
  ∑ ℓ ∈ Finset.Icc 1 q, (C ℓ : ℝ≥0∞) * (χ ^ (2 * q - ℓ) * iterPow k ℓ v w)

/-- **The comb**: `combTree n` is the rooted binary tree with `n+1` leaves whose rightmost leaf has
depth `n+1` — the deepest possible for that leaf count (`RTree.depth_le_numLeaves`).  It is the
shape that attains the upper end `ℓ = q` of the fresh depth range. -/
def combTree : ℕ → RTree Unit
  | 0 => .leaf ()
  | n + 1 => .node (.leaf ()) (combTree n)

/-- **The deep leaf of the comb**: the leaf position of `combTree n` at depth `n+1`. -/
def combDeepPos : (n : ℕ) → (combTree n).LeafPos
  | 0 => ⟨⟩
  | n + 1 => Sum.inr (combDeepPos n)

/-- The two-leaf tree. -/
abbrev twoLeaf : RTree Bool := RTree.node (RTree.leaf true) (RTree.leaf false)

/-- The three-leaf shape with a leaf at depth three. -/
abbrev threeLeaf : RTree Bool := RTree.node (RTree.leaf true) (RTree.node (RTree.leaf false)
  (RTree.leaf true))


end PercLib.CriticalLRP.I417Fresh.Subdivision
