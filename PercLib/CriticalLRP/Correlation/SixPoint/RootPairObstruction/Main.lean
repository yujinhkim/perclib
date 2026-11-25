/- Integrated from independently rebuilt Ultramath work.
Production base 59c03cea394d5ba573e5d23b06d0f394d065b380.
Scratch source: ../../.ultramath/smwvp122a/m4/Main.lean.
-/

module

public import PercLib.CriticalLRP.Correlation.SixPoint.RootPairObstruction.Defs
public import Mathlib.Data.Fintype.Pi

/-!
# A six-vertex tree no root-in-pair chain diagram can reach

**Scope.**  What is proved here is a finite, purely combinatorial statement about the
six-vertex tree `T` of `Defs.lean`.  It is *not* a statement about a transitive
weighted graph: `T` is not vertex-transitive, and no percolation law, root
independence, moment identity or BK argument is formalized here.  In
particular nothing below says that the pointwise premise
`HubRoot.fifth_moment_mixed_k2_le_of_chainRootBound` fails for the transitive lattice
law of the source.  What it does say is that the chain shape is not a universal
combinatorial cover: on `T` the five minimal connectors of the diagram can never be
made pairwise edge-disjoint, so on `T` the diagram family cannot reproduce the
connection event at the tree's own cost no matter how the five leaf roles are
assigned or where the two hubs are placed.  Since the production family `pat` is a
list of leaf permutations of this one shape, relabelling cannot repair it, and the
next obligation is the shape-indexed atlas realization rather than another
relabelling sweep.

`T` has five edges (centre `0` with legs `0-1-2`, `0-3-4`, `0-5`) and connects all
six of its vertices; the root is the centre and the five summed leaves are the other
five vertices.  For every bijective labelling of the five leaf roles and every pair
of hubs, the five witnesses of the diagram need at least `6` edges in total, and `6`
is attained, so the gap is exactly one edge.

The `example`s pin the definitions to the actual geometry of the tree.
-/

@[expose] public section

namespace ChainRefute

/-- The `0`–`2` path is `0 - 1 - 2`. -/
example : pathCard 0 2 = 2 := by decide

/-- The minimal subtree of `{0, 2, 4}` is `0 - 1 - 2` together with `0 - 3 - 4`. -/
example : steinerCard 0 2 4 = 4 := by decide

/-- The minimal subtree of `{0, 5, 4}` is `0 - 5` together with `0 - 3 - 4`. -/
example : steinerCard 0 5 4 = 3 := by decide

/-- The minimal subtree spanning the three leaves `2`, `4`, `5` is the whole tree. -/
example : steinerCard 2 4 5 = 5 := by decide

/-- The bound of `chainCost_ge_six` is attained: the identity labelling with both hubs
at the centre costs exactly the six edges that bound. -/
example : chainCost 1 2 3 4 5 0 0 = 6 := by decide

end ChainRefute

namespace ChainRefute

set_option maxRecDepth 100000 in
-- `decide` reduces the checker over all 120 labelings and all 36 hub pairs at once;
-- the kernel evaluation of that finite enumeration needs more recursion depth than
-- the default 1000.  The option is scoped to this declaration only.
set_option maxHeartbeats 8000000 in
-- The same kernel evaluation needs more than the default 200000 heartbeats.
/-- **The chain cost exceeds the tree cost.**  For every bijective labelling `L` of
the five leaf roles and every pair of hubs, the five witnesses of the root-in-pair
chain diagram need at least six edges in total, whereas six vertices are connected by
the five edges of `T`. -/
theorem chainCost_ge_six (L : Fin 5 → Fin 5) (hL : (Finset.univ.image L).card = 5)
    (c1 c2 : V) :
    6 ≤ chainCost ((L 0).succ) ((L 1).succ) ((L 2).succ) ((L 3).succ) ((L 4).succ) c1 c2 := by
  revert hL
  revert L
  revert c1
  revert c2
  decide

/-- The obstruction in the shape of the production family: the slot diagrams of
`HubRoot.slotChainRoot` are indexed by permutations of the five leaves, and every
such permutation is covered here. -/
theorem chainCost_ge_six_perm (σ : Equiv.Perm (Fin 5)) (c1 c2 : V) :
    6 ≤ chainCost ((σ 0).succ) ((σ 1).succ) ((σ 2).succ) ((σ 3).succ) ((σ 4).succ) c1 c2 :=
  chainCost_ge_six (⇑σ) (by simp) c1 c2

end ChainRefute
