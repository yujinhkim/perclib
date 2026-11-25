/- Integrated from independently rebuilt Ultramath work.
Production base 59c03cea394d5ba573e5d23b06d0f394d065b380.
Scratch source: ../../.ultramath/smwvp122a/m4/Defs.lean.
-/

module

public import Mathlib.Data.Fintype.Pi
public import Mathlib.Data.Fintype.Card
public import Mathlib.Data.Finset.Card
public import Mathlib.Data.Fin.Basic

/-!
# The root-in-pair chain shape misses a six-vertex tree

`V = Fin 6` carries the five-edge tree `treeEdges` with centre `0`:

```text
4 - 3 - 0 - 1 - 2      and the leaf 5 attached to the centre 0.
```

For a labelling `(a, b, d, e, f)` of the five non-root vertices and hubs `c1`, `c2`,
the chain diagram asks for five pairwise edge-disjoint witnesses:

* `steinerCard 0 a c1` edges for the joint event `{0, a, c1}` connected,
* `pathCard b c1` edges for the arm `b ↔ c1`,
* `steinerCard d e c2` edges for the joint event `{d, e, c2}` connected,
* `pathCard c1 c2` edges for the spine,
* `pathCard f c2` edges for the arm `f ↔ c2`.

In a tree each witness is forced to contain the unique minimal connector, so the
sum `chainCost` is a lower bound for the total number of open edges needed by any
realization of the diagram on this tree.  `Main.lean` proves that this sum is at
least `6` for *every* labelling and *every* pair of hubs, while connecting all six
vertices only needs the `5` edges of the tree.

Consequently, with the tree itself as the ambient graph, the percolation parameter
`p ∈ (0,1)` and the law that opens the five tree edges with probability `p`, the
left side of the pointwise bound equals `p ^ 5`, while the right side is at most
`105 * 36 * p ^ 6` (`105` leaf labellings times at most `36` hub pairs, each
diagram at most `p ^ chainCost ≤ p ^ 6` by the BK inequality).  Hence the bound
fails whenever `p < 1 / (105 * 36)`.  That numerical comparison is recorded here as
prose; only the combinatorial cost bound is proved below.
-/

@[expose] public section

namespace ChainRefute

/-- The six vertices of the counterexample tree. -/
abbrev V : Type := Fin 6

/-- The vertices on the `true` side of each of the five edges of the tree, in the
edge order `(0,1)`, `(0,3)`, `(0,5)`, `(1,2)`, `(3,4)`.

Removing the `i`-th edge splits the tree into the two listed parts, so this table is
exactly the `i`-th edge cut. -/
def sideSet (i : Fin 5) : Finset V :=
  if (i : ℕ) = 0 then {0, 3, 4, 5}
  else if (i : ℕ) = 1 then {0, 1, 2, 5}
  else if (i : ℕ) = 2 then {0, 1, 2, 3, 4}
  else if (i : ℕ) = 3 then {0, 1, 3, 4, 5}
  else {0, 1, 2, 3, 5}

/-- The side of the `i`-th edge cut containing `v`, as a Boolean. -/
def side (i : Fin 5) (v : V) : Bool := decide (v ∈ sideSet i)

/-- `sep i a b` holds when the `i`-th edge of the tree lies on the `a`–`b` path,
equivalently when it separates `a` from `b`. -/
def sep (i : Fin 5) (a b : V) : Bool := side i a != side i b

/-- The number of edges of the unique `a`–`b` path in the tree. -/
def pathCard (a b : V) : ℕ := (Finset.univ.filter (fun i : Fin 5 => sep i a b = true)).card

/-- The number of edges of the unique minimal subtree spanning `a`, `b` and `c`.
An edge lies in that subtree exactly when it separates some two of the three
vertices, since every leaf of the minimal subtree is one of them. -/
def steinerCard (a b c : V) : ℕ :=
  (Finset.univ.filter
    (fun i : Fin 5 => (sep i a b || sep i a c || sep i b c) = true)).card

/-- Lower bound for the number of tree edges that must be open for the root-in-pair
chain diagram with joint vertices `{0, a, c1}` and `{d, e, c2}`, arms `b ↔ c1` and
`f ↔ c2`, and spine `c1 ↔ c2`, to be realized on the tree.

In a tree the witness of each connection event contains the unique minimal
connector, so each of the five summands is a lower bound for the number of distinct
open edges used by that witness.  Summing gives a lower bound for the total cost,
which is what the BK inequality converts into `p ^ chainCost`. -/
def chainCost (a b d e f c1 c2 : V) : ℕ :=
  steinerCard 0 a c1 + pathCard b c1 + steinerCard d e c2 + pathCard c1 c2 + pathCard f c2

/-- The number of tree edges. -/
theorem card_edgeIndex : Fintype.card (Fin 5) = 5 := rfl

end ChainRefute
