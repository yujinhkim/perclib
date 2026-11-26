/- Integrated from independently rebuilt Ultramath work.
Production base 50c2eed0682a7e1b078ae771dbef463ebe00701d.
Scratch source: repository-root .ultramath/.
-/

/-
Swarm smwwr4usj / member m1: the geometry of a hub's 3-star in the realized atlas.

Integrated base: production commit `6b7eb1107b03297e4df33585eeac818682adb1d2`, Lean 4.35.0.

`HubStarJoint` (in `Defs.lean`) is the disjoint occurrence of the three connection events of the
3-star at a hub.  For it to be a *three-point* value in the sense of the proof of Lemma I.4.16 —
three arms from **one** vertex `w` — the three edges of the star must share an endpoint.  This
file proves exactly that, for the realized atlas:

* `childPos_iposOfPath_app`: the child end of the down edge of an internal vertex is the
  position of that child; this is the `IPos`/`childPos` commutation that the realized atlas
  (`Real.childPos`) and the address layer (`Atlas.iposOfPath`) need in order to agree;
* `hubStarAEdges_incident`: every edge of the 3-star of `v` is incident with `φ v`;
* `hubStarAEdges_eq`: every edge of the 3-star of `v` is either the down edge of `v` in one of
  the two child directions (source `φ v`) or the up edge of `v` (target `φ v`).

Consequently `HubStarJoint` is the joint event "the configuration connects the single vertex
`φ v` to its parent side and to both children, by three pairwise disjoint open edge sets".
-/
module

public import PercLib.CriticalLRP.TreeExpansion.AtlasRealization.Hub.Main

/-! # Coordinates of hub-star edges and of the hub itself

The internal address map `pathOf` and its inverse `iposOfPath` identify hub slots with
realized atlas edges. `upEdge_dstPos` proves that the parent edge always ends at the hub position.
Its source need not be that position: `src_upEdge` distinguishes the root-leaf coordinate from
an internal parent vertex. This is the root-versus-parent distinction needed for joint-hub
diagram evaluation.
-/

set_option autoImplicit false
set_option linter.unusedSectionVars false
set_option linter.unusedFintypeInType false
set_option linter.unusedDecidableInType false

@[expose] public section

namespace PercLib.CriticalLRP.TreeExpansion.Real

open Finset

variable {V : Type*} [DecidableEq V]
variable {α : Type*} [DecidableEq α]

/-- **The child end of a down edge is the child's own position.**  Stated for the address form:
the position `childPos` of the child of the internal vertex at address `p` in direction `b` is the
`φ`-position of the internal vertex at address `p ++ [b]`.  (The address `p ++ [b]` is internal
exactly because `p` is, so no leaf position can occur here.) -/
theorem childPos_iposOfPath_app (t : RTree α) (p : List Bool) (hp : p ∈ RTree.ipaths t)
    (b : Bool) (hpb : p ++ [b] ∈ RTree.ipaths t) (φ : t.IPos → V) (y : α → V) :
    childPos t φ y (RTree.iposOfPath t p hp) b = φ (RTree.iposOfPath t (p ++ [b]) hpb) := by
  induction t generalizing p with
  | leaf a => simp [RTree.ipaths] at hp
  | node l r ihl ihr =>
      match p with
      | [] =>
          cases b
          · have hpb0 : ([] : List Bool) ∈ RTree.ipaths l := by
              obtain ⟨l', r', h⟩ :=
                (RTree.mem_ipaths (RTree.node l r) ([] ++ [false])).mp hpb
              exact (RTree.mem_ipaths l []).mpr ⟨l', r', by simpa using h⟩
            cases l with
            | leaf a => simp [RTree.ipaths] at hpb0
            | node l1 l2 => simp [RTree.iposOfPath, childPos]
          · have hpb0 : ([] : List Bool) ∈ RTree.ipaths r := by
              obtain ⟨l', r', h⟩ :=
                (RTree.mem_ipaths (RTree.node l r) ([] ++ [true])).mp hpb
              exact (RTree.mem_ipaths r []).mpr ⟨l', r', by simpa using h⟩
            cases r with
            | leaf a => simp [RTree.ipaths] at hpb0
            | node r1 r2 => simp [RTree.iposOfPath, childPos]
      | false :: s =>
          have hp' : s ∈ RTree.ipaths l := by
            obtain ⟨l', r', h⟩ := (RTree.mem_ipaths (RTree.node l r) (false :: s)).mp hp
            exact (RTree.mem_ipaths l s).mpr ⟨l', r', by simpa using h⟩
          have hpb' : s ++ [b] ∈ RTree.ipaths l := by
            obtain ⟨l', r', h⟩ :=
              (RTree.mem_ipaths (RTree.node l r) ((false :: s) ++ [b])).mp hpb
            exact (RTree.mem_ipaths l (s ++ [b])).mpr ⟨l', r', by simpa using h⟩
          have h := ihl (p := s) (hp := hp') (hpb := hpb') (φ := fun v => φ (Sum.inl v))
          simpa [RTree.iposOfPath, childPos, List.cons_append] using h
      | true :: s =>
          have hp' : s ∈ RTree.ipaths r := by
            obtain ⟨l', r', h⟩ := (RTree.mem_ipaths (RTree.node l r) (true :: s)).mp hp
            exact (RTree.mem_ipaths r s).mpr ⟨l', r', by simpa using h⟩
          have hpb' : s ++ [b] ∈ RTree.ipaths r := by
            obtain ⟨l', r', h⟩ :=
              (RTree.mem_ipaths (RTree.node l r) ((true :: s) ++ [b])).mp hpb
            exact (RTree.mem_ipaths r (s ++ [b])).mpr ⟨l', r', by simpa using h⟩
          have h := ihr (p := s) (hp := hp') (hpb := hpb') (φ := fun v => φ (Sum.inr (Sum.inl v)))
          simpa [RTree.iposOfPath, childPos, List.cons_append] using h


/-! ### The transported edges and the ends of a 3-star -/

theorem atlasEdgeEquiv_inl (t : RTree α) (s : List Bool) (hs : s ∈ RTree.ipaths t)
    (b : Bool) :
    atlasEdgeEquiv t (Sum.inl ((⟨s, hs⟩ : {s // s ∈ RTree.ipaths t}), b)) =
      Sum.inl (RTree.iposOfPath t s hs, b) := rfl

theorem atlasEdgeEquiv_root (t : RTree α) (x : PUnit) :
    atlasEdgeEquiv t (Sum.inr x) = Sum.inr x := rfl

/-- **The up edge of an internal vertex ends at that vertex.**  This is where the address form
`RTree.upEdge` and the realized position `Real.childPos`/`Real.dstPos` are made to agree. -/
theorem upEdge_dstPos (t : RTree α) (s : List Bool) (hs : s ∈ RTree.ipaths t)
    (φ : t.IPos → V) (y : α → V) :
    dstPos t φ y (atlasEdgeEquiv t (RTree.upEdge t s hs)) = φ (RTree.iposOfPath t s hs) := by
  rw [RTree.upEdge]
  split_ifs with h
  · cases h
    rw [atlasEdgeEquiv_root, dstPos_root]
    cases t with
    | leaf a => simp [RTree.ipaths] at hs
    | node l r => rfl
  · rw [atlasEdgeEquiv_inl]
    have hmem : s.dropLast ++ [s.getLast h] ∈ RTree.ipaths t := by
      rw [List.dropLast_append_getLast h]; exact hs
    have hpos : RTree.iposOfPath t (s.dropLast ++ [s.getLast h]) hmem =
        RTree.iposOfPath t s hs :=
      RTree.pathOf_injective t (Subtype.ext (by
        rw [RTree.pathOf_iposOfPath, RTree.pathOf_iposOfPath,
          List.dropLast_append_getLast h]))
    rw [dstPos_inl, childPos_iposOfPath_app t s.dropLast (RTree.dropLast_mem_ipaths hs h)
      (s.getLast h) hmem φ y, hpos]

/-- **The 3-star of a hub consists of its two down edges and its up edge.** -/
theorem hubStarAEdges_eq (t : RTree α) (v : t.IPos) :
    hubStarAEdges t v =
      {Sum.inl (v, false), Sum.inl (v, true),
        atlasEdgeEquiv t (RTree.upEdge t (RTree.pathOf t v).1 (RTree.pathOf t v).2)} := by
  rw [hubStarAEdges, RTree.star, Finset.image_insert, Finset.image_insert,
    Finset.image_singleton, atlasEdgeEquiv_inl, atlasEdgeEquiv_inl, RTree.iposOfPath_pathOf]

/-- **Every edge of the 3-star of `v` is incident with `φ v`**: the two down edges start at
`φ v`, the up edge ends at `φ v`.  Hence `HubStarJoint` is a joint event at the single vertex
`φ v` with three arms — the three-point value of the source proof. -/
theorem hubStarAEdges_incident (t : RTree α) (φ : t.IPos → V) (y : α → V) (c : V)
    (v : t.IPos) {e : AEdge t} (he : e ∈ hubStarAEdges t v) :
    srcPos t φ c e = φ v ∨ dstPos t φ y e = φ v := by
  rw [mem_hubStarAEdges] at he
  obtain ⟨e₀, he₀, rfl⟩ := he
  rw [RTree.mem_star] at he₀
  rcases he₀ with h | h | h
  · rw [h, atlasEdgeEquiv_inl]
    exact Or.inl (congrArg φ (RTree.iposOfPath_pathOf t v))
  · rw [h, atlasEdgeEquiv_inl]
    exact Or.inl (congrArg φ (RTree.iposOfPath_pathOf t v))
  · rw [h]
    exact Or.inr (by rw [upEdge_dstPos, RTree.iposOfPath_pathOf])

/-- **The root correction is the root edge, counted exactly once.**  For the root internal
vertex the up edge of the 3-star is the atlas root edge `Sum.inr ⟨⟩` (joining the root leaf to
the root of `t`), not a parent down edge; together with `card_hubStarAEdges` (`= 3`) and
`hubStarAEdges_eq` this says that the root hub contributes the root edge once and adds no
duplicate of a parent edge. -/
theorem rootEdge_mem_hubStarAEdges (t : RTree α) (v : t.IPos)
    (hv : (RTree.pathOf t v).1 = []) : Sum.inr ⟨⟩ ∈ hubStarAEdges t v := by
  have h : RTree.upEdge t (RTree.pathOf t v).1 (RTree.pathOf t v).2 = Sum.inr ⟨⟩ := by
    simp [RTree.upEdge, hv]
  rw [hubStarAEdges_eq, h, atlasEdgeEquiv_root]
  simp

/--
The up edge's source is the root-leaf coordinate for a root edge, or the parent internal
vertex.
Its source need not be the hub `φ v`, even though its destination is always `φ v`.
This is the positional distinction needed by the parent/pair slot evaluation. -/
theorem src_upEdge (t : RTree α) (s : List Bool) (hs : s ∈ RTree.ipaths t)
    (φ : t.IPos → V) (c : V) :
    srcPos t φ c (atlasEdgeEquiv t (RTree.upEdge t s hs)) =
      if h : s = [] then c else
        φ (RTree.iposOfPath t s.dropLast (RTree.dropLast_mem_ipaths hs h)) := by
  rw [RTree.upEdge]
  split_ifs with h
  · cases h
    rw [atlasEdgeEquiv_root]
    rfl
  · rw [atlasEdgeEquiv_inl]
    rfl

end PercLib.CriticalLRP.TreeExpansion.Real
