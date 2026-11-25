/- Definitions for the compiled path example of Atlas realization. -/

module

public import PercLib.CriticalLRP.TreeExpansion.AtlasRealization.Cover

/-! A three-vertex path with a root at its interior vertex. -/

@[expose] public section

namespace PercLib.CriticalLRP.TreeExpansion.Real

/-- The two path edges: `0` joins `0, 1` and `1` joins `1, 2`. -/
def pathEnds : Fin 2 → Sym2 (Fin 3) := ![s(0, 1), s(1, 2)]

/-- The configuration with both path edges open. -/
def pathConf : Finset (Fin 2) := {0, 1}


/-- The two-leaf shape. -/
def exShape : RTree (Fin 2) := RTree.node (RTree.leaf 0) (RTree.leaf 1)

/-- The single internal vertex of the shape sits at the middle vertex `1`. -/
def exPhi : exShape.IPos → Fin 3 := fun _ => 1

/-- The terminals: label `0` at vertex `0`, label `1` at vertex `2`. -/
def exY : Fin 2 → Fin 3 := ![0, 2]

/-- The witnesses of the three atlas edges: the root edge is trivial, the left child edge is the
first path edge, the right child edge is the second. -/
def exWit : AEdge exShape → Finset (Fin 2)
  | Sum.inl (Sum.inl u, _) => nomatch u
  | Sum.inl (Sum.inr (Sum.inl v), _) => nomatch v
  | Sum.inl (Sum.inr (Sum.inr _), false) => {0}
  | Sum.inl (Sum.inr (Sum.inr _), true) => {1}
  | Sum.inr _ => ∅


end PercLib.CriticalLRP.TreeExpansion.Real
