/- Integrated from independently rebuilt Ultramath work.
Production base 3b6ff818cd3ac1a9cee99dcfff154a2ff4f85095.
Scratch source: ../../.ultramath/smwvp122a/m3/ProofCover.lean.
-/

module

public import PercLib.CriticalLRP.Correlation.FourPoint.ProofTree
public import Mathlib.Combinatorics.SimpleGraph.Connectivity.Subgraph

/-!
The four-point cover for vertices in a common component of an arbitrary graph.

The tree statement (`tree_cover`) is transported along graph homomorphisms (`hasCover_map`), so it
suffices to find a spanning tree of the connected component of the root.

The cover is stated with the three terminals `x, y, z` inside the same component as `o`; since the
walks supplied by `tree_cover` live in the spanning tree of that component, the result is a
statement about `G` with no tree hypothesis left.
-/

@[expose] public section

namespace PercLib.CriticalLRP.FourPoint

set_option linter.unusedSectionVars false
set_option linter.unusedDecidableInType false

variable {V : Type*} [DecidableEq V]

/-- An injective map of vertices induces an injective map on unordered pairs. -/
theorem sym2_map_injective {α β : Type*} {f : α → β} (hf : Function.Injective f) :
    Function.Injective (Sym2.map f) := by
  intro a b h
  induction a using Sym2.ind with
  | h x y =>
    induction b using Sym2.ind with
    | h x' y' =>
      simp only [Sym2.map_mk, Sym2.eq, Sym2.rel_iff] at h ⊢
      obtain ⟨h1, h2⟩ | ⟨h1, h2⟩ := h
      · exact Or.inl ⟨hf h1, hf h2⟩
      · exact Or.inr ⟨hf h1, hf h2⟩

/-- The cover is invariant under an injective graph homomorphism. -/
theorem hasCover_map {W : Type*} [DecidableEq W] {G : SimpleGraph V} {G' : SimpleGraph W}
    (f : G →g G') (hf : Function.Injective f) {o x y z : V} (h : HasCover G o x y z) :
    HasCover G' (f o) (f x) (f y) (f z) := by
  obtain ⟨w, t, u, v, P, Q, R, S, hfin, h1, h2, h3⟩ := h
  have hsym : Function.Injective (Sym2.map f) := sym2_map_injective hf
  refine ⟨f w, f t, f u, f v, P.map f, Q.map f, R.map f, S.map f, ?_, ?_, ?_, ?_⟩
  · have hm := congrArg (Finset.map ⟨f, hf⟩) hfin
    simpa [Finset.map_insert] using hm
  · rw [SimpleGraph.Walk.edges_map, SimpleGraph.Walk.edges_map, SimpleGraph.Walk.edges_map,
      ← List.map_append]
    exact List.Disjoint.map hsym h1
  · rw [SimpleGraph.Walk.edges_map, SimpleGraph.Walk.edges_map, SimpleGraph.Walk.edges_map,
      ← List.map_append]
    exact List.Disjoint.map hsym h2
  · rw [SimpleGraph.Walk.edges_map, SimpleGraph.Walk.edges_map]
    exact List.Disjoint.map hsym h3

/-- The cover transfers from a spanning subtree. -/
theorem cover_of_tree_le {G T : SimpleGraph V} (hTG : T ≤ G) (hT : T.IsTree) (o x y z : V) :
    HasCover G o x y z := by
  have h : HasCover T o x y z := tree_cover hT o x y z
  exact hasCover_map (f := SimpleGraph.Hom.ofLE hTG) (fun _ _ hab => hab) h

/-- **The four-point cover.**  If `x`, `y` and `z` lie in the component of `o`, then there are a
centre `w`, a partition `{t, u, v} = {x, y, z}` and walks `o → w`, `t → w`, `u → w`, `v → w` whose
edge lists give the joint cluster `{o ↔ t, w}` and the two disjoint arms `w ↔ u`, `w ↔ v`. -/
theorem cover_of_reachable {G : SimpleGraph V} (o x y z : V)
    (hx : G.Reachable o x) (hy : G.Reachable o y) (hz : G.Reachable o z) :
    HasCover G o x y z := by
  classical
  set C := G.connectedComponentMk o with hC
  have ho : o ∈ C.supp := SimpleGraph.ConnectedComponent.connectedComponentMk_mem
  have hx' : x ∈ C.supp := by
    rw [SimpleGraph.ConnectedComponent.mem_supp_iff]
    exact SimpleGraph.ConnectedComponent.sound hx.symm
  have hy' : y ∈ C.supp := by
    rw [SimpleGraph.ConnectedComponent.mem_supp_iff]
    exact SimpleGraph.ConnectedComponent.sound hy.symm
  have hz' : z ∈ C.supp := by
    rw [SimpleGraph.ConnectedComponent.mem_supp_iff]
    exact SimpleGraph.ConnectedComponent.sound hz.symm
  obtain ⟨T', hle, hT'⟩ :=
    (SimpleGraph.ConnectedComponent.connected_toSimpleGraph C).exists_isTree_le
  have h := tree_cover hT' ⟨o, ho⟩ ⟨x, hx'⟩ ⟨y, hy'⟩ ⟨z, hz'⟩
  have hmap := hasCover_map
    (f := C.toSimpleGraph_hom.comp (SimpleGraph.Hom.ofLE hle)) (hf := Subtype.val_injective) h
  simpa [SimpleGraph.ConnectedComponent.toSimpleGraph_hom_apply] using hmap

end PercLib.CriticalLRP.FourPoint
