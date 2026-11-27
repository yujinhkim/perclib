/-
Ultramath swarm `smwziumdb`, member `m6`, direction `d1` (branch-and-root tree count).

Copyright (c) 2026 PercLib contributors. Released under Apache 2.0.

Accepted and independently rebuilt from Ultramath `smwziumdb`.
Supporting integration based on production commit `5d2d681b941eb1c687f1ba17e6a798b8f0175aa0`.

# The branch-and-root tree count of the `q = 0`, `p = 3` star

Source: T. Hutchcroft, *Critical long-range percolation I: High effective dimension*,
arXiv:2508.18807v1, Section I.2.1 p. 22, inequalities (I.2.2) and (I.2.3), and the
`(p,q) = (3,0)` instance which is what the proof of Proposition I.4.15 Case 3 consumes
(pp. 45-47).

The tree-graph inequality (I.2.2) at five leaves reads

  `P(x₀ ↔ x₁ ↔ … ↔ x₄) ≤ ∑_{T ∈ 𝒯₄} ∑_{internal vertices} ∏_{edges} P(u ↔ v)`

where `𝒯₄` is a set of *representatives of isomorphism classes of trees with leaves
`0,1,2,3,4` labelled and all non-leaf vertices unlabelled of degree 3*.  Such a tree has three
internal vertices and seven edges; it is a rooted binary tree with four labelled leaves below a
root leaf `0`, and the number of isomorphism classes is `5!! = 15`.

The repository (`PercLib.CriticalLRP.TreeExpansion`) carries the tree-graph inequality
(`treeGraphBound_of_bk'`) and the tree-sum recursion (`TS_recursion`), but for the size of the
tree family it only carries the *inequality* `card_LT_fin_le`
(`#(plane trees on p labels) ≤ 2^(p-1)·M(p-1)`); the *exact* branch-and-root count at four
leaves, and the collapse of the plane count `120` onto the non-plane count `15` through the
normalization `2^{-(p-1)}` of `TS`, are not in the repository.

## What this file defines

`reps Z` is the canonical family of representatives of the non-plane rooted binary trees with
leaf set `Z`: for `|Z| = 1` it is `{leaf a}`, and otherwise

  `reps Z = ⋃_{A ∈ splits Z a₀} ⋃_{l ∈ reps A} { node l r | r ∈ reps (Z \ A) }`

with `splits Z a₀` the family of nonempty proper subsets of `Z` containing `a₀` — exactly the
index set of production's `TS_recursion`.  Since `splits` carries one member of each unordered
split, `reps Z` contains exactly one orientation of each non-plane tree; `RTree.wtL` is
invariant under exchanging the two children, so the orientation is irrelevant to the weight.

`Main.lean` proves `TS k Z y v = ∑ t ∈ reps Z, wtL k t y v` for every finite nonempty `Z`, i.e.
that the `2^{-(|Z|-1)}` normalization of `TS` is exactly the quotient of the plane tree family
by the internal-node child swaps.  At `Z = Fin 4` this yields the exact fifteen-term
branch-and-root evaluation of the `(p,q) = (3,0)` star, the count `15`, the path-length
distribution `(3, 6, 6)` for `ℓ = 2, 3, 4`, the shape multiplicities `(3, 3, 3, 6)` of the
accepted `m1` atlas, and the identification of the fifteen representatives with `m1`'s fifteen
seven-edge atlas diagrams.

The fuel parameter of `repsAux` exists only so that the definition is structurally recursive
and hence *computable*; `repsAux_eq` shows that `Z.card` units of fuel always suffice, so the
counts in `Main.lean` are decided by evaluation rather than asserted.
-/
module

public import PercLib.CriticalLRP.TreeExpansion.TreeSumRecursionFull
public import Mathlib

/-! # Canonical branch-and-root representatives and atlas codes -/

@[expose] public section

noncomputable section

open Finset

namespace PercLib.CriticalLRP.QZeroStarCount

open PercLib.CriticalLRP.TreeExpansion

set_option linter.unusedSectionVars false

variable {α : Type*} [LinearOrder α] [Inhabited α]

/-! ## The canonical branch-and-root family -/

/-- The canonical branch point of a label set: its least element.  Using a canonical basepoint
makes `reps` a function of `Z` alone, so the family below is deterministic and, for
`α = Fin 4`, computable.  The junk value on the empty set is never used. -/
def base (Z : Finset α) : α := if h : Z.Nonempty then Z.min' h else default

theorem base_mem {Z : Finset α} (hZ : Z.Nonempty) : base Z ∈ Z := by
  unfold base
  rw [dite_eq_left hZ]
  exact Finset.min'_mem _ hZ

/-- The canonical family of representatives of the non-plane rooted binary trees with leaf set
`Z`, with a fuel parameter.

This is the branch-and-root recursion of (I.2.2): either `Z` is a singleton (one leaf), or one
cuts at the root into the two halves of a split `A ∈ splits Z a₀` and recurses. -/
def repsAux : (n : ℕ) → Finset α → Finset (RTree α)
  | 0, _ => ∅
  | n + 1, Z =>
      if Z.card ≤ 1 then Z.image RTree.leaf
      else
        (splits Z (base Z)).biUnion fun A =>
          (repsAux n A).biUnion fun l => (repsAux n (Z \ A)).image (RTree.node l)

/-- **The canonical branch-and-root family** of the non-plane rooted binary trees with leaf set
`Z`: exactly one orientation of each isomorphism class of rooted binary trees whose leaves are
labelled by `Z`.  The root of such a tree plays the role of the branch point one edge below the
pinned root vertex `x` of (I.2.2). -/
def reps (Z : Finset α) : Finset (RTree α) := repsAux Z.card Z

theorem repsAux_succ (n : ℕ) (Z : Finset α) :
    repsAux (n + 1) Z =
      if Z.card ≤ 1 then Z.image RTree.leaf
      else
        (splits Z (base Z)).biUnion fun A =>
          (repsAux n A).biUnion fun l => (repsAux n (Z \ A)).image (RTree.node l) := rfl

/-- `reps` unfolded one fuel step, for a set of at least two elements. -/
theorem reps_eq_repsAux_succ {Z : Finset α} (h : 1 ≤ Z.card) :
    reps Z = repsAux (Z.card - 1 + 1) Z := by
  change repsAux Z.card Z = repsAux (Z.card - 1 + 1) Z
  congr 1
  omega

theorem repsAux_succ_of_one_le {n : ℕ} {Z : Finset α} (h : Z.card ≤ 1) :
    repsAux (n + 1) Z = Z.image RTree.leaf := by
  rw [repsAux_succ, ite_eq_left h]

theorem repsAux_succ_of_not_le {n : ℕ} {Z : Finset α} (h : ¬ Z.card ≤ 1) :
    repsAux (n + 1) Z =
      (splits Z (base Z)).biUnion fun A =>
        (repsAux n A).biUnion fun l => (repsAux n (Z \ A)).image (RTree.node l) := by
  rw [repsAux_succ, ite_eq_right h]

/-- Fuel monotonicity: `Z.card` units of fuel always suffice. -/
theorem repsAux_eq : ∀ (k : ℕ) (Z : Finset α), Z.card ≤ k → repsAux k Z = reps Z := by
  intro k
  induction k using Nat.strong_induction_on with
  | _ k ih =>
    intro Z hk
    rcases k with _ | j
    · have hZ : Z = ∅ := Finset.card_eq_zero.mp (by omega)
      subst hZ
      rfl
    · rcases Nat.eq_zero_or_pos Z.card with h0 | hpos
      · have hZ : Z = ∅ := Finset.card_eq_zero.mp h0
        subst hZ
        rw [repsAux_succ_of_one_le (n := j) (by simp), reps]
        rfl
      · rcases Nat.lt_or_ge Z.card 2 with h1 | h2
        · have h1' : Z.card ≤ 1 := by omega
          have hc1 : Z.card = 1 := by omega
          have hZj : repsAux (j + 1) Z = Z.image RTree.leaf := repsAux_succ_of_one_le (n := j) h1'
          have hZ1 : repsAux (0 + 1) Z = Z.image RTree.leaf :=
            repsAux_succ_of_one_le (n := 0) (Z := Z) h1'
          have hR : reps Z = repsAux (0 + 1) Z := by rw [reps, hc1]
          rw [hZj, hR, hZ1]
        · have hpos0 : ¬ Z.card ≤ 1 := by omega
          have hR : reps Z = repsAux (Z.card - 1 + 1) Z := reps_eq_repsAux_succ (by omega)
          have hltA : ∀ B ∈ splits Z (base Z), B.card < Z.card := by
            intro B hB
            exact Finset.card_lt_card (Finset.ssubset_iff_subset_ne.mpr
              ⟨(mem_splits hB).1, (mem_splits hB).2.2.1⟩)
          have hltB : ∀ B ∈ splits Z (base Z), (Z \ B).card < Z.card := by
            intro B hB
            refine Finset.card_lt_card (Finset.ssubset_iff_subset_ne.mpr
              ⟨Finset.sdiff_subset, ?_⟩)
            intro hEq
            obtain ⟨a, ha⟩ := (mem_splits hB).2.1
            have hsub : B ⊆ Z \ B := by rw [hEq]; exact (mem_splits hB).1
            exact (Finset.mem_sdiff.mp (hsub ha)).2 ha
          have hZj : Z.card - 1 ≤ j := by omega
          have hkey : ∀ B : Finset α, B.card < Z.card →
              repsAux j B = repsAux (Z.card - 1) B := by
            intro B hlt
            have hB1 : B.card ≤ j := by omega
            have hB2 : B.card ≤ Z.card - 1 := by omega
            have h1 : repsAux j B = reps B := ih j (by omega) B hB1
            have h2 : repsAux (Z.card - 1) B = reps B :=
              ih (Z.card - 1) (by omega) B hB2
            rw [h1, h2]
          ext t
          rw [hR, repsAux_succ_of_not_le (n := j) hpos0,
            repsAux_succ_of_not_le (n := Z.card - 1) hpos0]
          simp only [Finset.mem_biUnion, Finset.mem_image]
          constructor
          · rintro ⟨A, hA, l, hl, r, hr, rfl⟩
            rw [hkey A (hltA A hA)] at hl
            rw [hkey (Z \ A) (hltB A hA)] at hr
            exact ⟨A, hA, l, hl, r, hr, rfl⟩
          · rintro ⟨A, hA, l, hl, r, hr, rfl⟩
            rw [← hkey A (hltA A hA)] at hl
            rw [← hkey (Z \ A) (hltB A hA)] at hr
            exact ⟨A, hA, l, hl, r, hr, rfl⟩

/-- The defining recursion of `reps` at a set with at least two elements. -/
theorem reps_eq {Z : Finset α} (h : 2 ≤ Z.card) :
    reps Z =
      (splits Z (base Z)).biUnion fun A =>
        (reps A).biUnion fun l => (reps (Z \ A)).image (RTree.node l) := by
  have hR : reps Z = repsAux (Z.card - 1 + 1) Z := reps_eq_repsAux_succ (by omega)
  have hAc : ∀ A ∈ splits Z (base Z), A.card ≤ Z.card - 1 := by
    intro A hA
    have hlt : A.card < Z.card := Finset.card_lt_card
      (Finset.ssubset_iff_subset_ne.mpr ⟨(mem_splits hA).1, (mem_splits hA).2.2.1⟩)
    omega
  have hBc : ∀ A ∈ splits Z (base Z), (Z \ A).card ≤ Z.card - 1 := by
    intro A hA
    have hlt : (Z \ A).card < Z.card :=
      Finset.card_lt_card (Finset.ssubset_iff_subset_ne.mpr ⟨Finset.sdiff_subset, by
        intro hEq
        obtain ⟨a, ha⟩ := (mem_splits hA).2.1
        have hsub : A ⊆ Z \ A := by rw [hEq]; exact (mem_splits hA).1
        exact (Finset.mem_sdiff.mp (hsub ha)).2 ha⟩)
    omega
  ext t
  rw [hR, repsAux_succ_of_not_le (n := Z.card - 1) (by omega)]
  simp only [Finset.mem_biUnion, Finset.mem_image]
  constructor
  · rintro ⟨A, hA, l, hl, r, hr, rfl⟩
    rw [repsAux_eq _ A (hAc A hA)] at hl
    rw [repsAux_eq _ (Z \ A) (hBc A hA)] at hr
    exact ⟨A, hA, l, hl, r, hr, rfl⟩
  · rintro ⟨A, hA, l, hl, r, hr, rfl⟩
    rw [← repsAux_eq _ A (hAc A hA)] at hl
    rw [← repsAux_eq _ (Z \ A) (hBc A hA)] at hr
    exact ⟨A, hA, l, hl, r, hr, rfl⟩

/-- The label set of every representative is `Z`. -/
theorem leaves_reps : ∀ (n : ℕ), ∀ (Z : Finset α), Z.card = n →
    ∀ ⦃t : RTree α⦄, t ∈ reps Z → t.leaves.toFinset = Z := by
  intro n
  induction n using Nat.strong_induction_on with
  | _ n ih =>
    intro Z hc t ht
    rcases Nat.eq_zero_or_pos Z.card with h0 | hpos
    · have hZ : Z = ∅ := Finset.card_eq_zero.mp h0
      subst hZ
      rw [reps, h0] at ht
      exact absurd ht (Finset.notMem_empty t)
    · rcases Nat.lt_or_ge Z.card 2 with h1 | h2
      · have hc1 : Z.card = 1 := by omega
        obtain ⟨a, rfl⟩ := Finset.card_eq_one.mp hc1
        have hRa : reps ({a} : Finset α) = repsAux 1 {a} := by rw [reps]; simp
        rw [hRa, repsAux_succ_of_one_le (n := 0) (by simp), Finset.mem_image] at ht
        obtain ⟨b, hb, rfl⟩ := ht
        rw [Finset.mem_singleton] at hb
        subst hb
        simp
      · rw [reps_eq h2, Finset.mem_biUnion] at ht
        obtain ⟨A, hA, ht⟩ := ht
        rw [Finset.mem_biUnion] at ht
        obtain ⟨l, hl, ht⟩ := ht
        rw [Finset.mem_image] at ht
        obtain ⟨r, hr, rfl⟩ := ht
        have hAZ := (mem_splits hA).1
        have hAcard : A.card < Z.card := Finset.card_lt_card
          (Finset.ssubset_iff_subset_ne.mpr ⟨hAZ, (mem_splits hA).2.2.1⟩)
        have hBcard : (Z \ A).card < Z.card :=
          Finset.card_lt_card (Finset.ssubset_iff_subset_ne.mpr ⟨Finset.sdiff_subset, by
            intro hEq
            obtain ⟨a, ha⟩ := (mem_splits hA).2.1
            have hsub : A ⊆ Z \ A := by rw [hEq]; exact hAZ
            exact (Finset.mem_sdiff.mp (hsub ha)).2 ha⟩)
        rw [RTree.leaves_node, List.toFinset_append, ih A.card (by omega) A rfl hl,
          ih (Z \ A).card (by omega) (Z \ A) rfl hr, Finset.union_sdiff_of_subset hAZ]

/-- The label set of a representative, in applicative form. -/
theorem leaves_reps_of {Z : Finset α} ⦃t : RTree α⦄ (ht : t ∈ reps Z) :
    t.leaves.toFinset = Z :=
  leaves_reps Z.card Z rfl ht

/-! ## The atlas path length, the shape classifier, and the atlas edge coding -/

/-- The label of the leftmost leaf. -/
def leftmost : RTree α → α
  | RTree.leaf a => a
  | RTree.node l _ => leftmost l

/-- The depth of the leftmost leaf.  In a member of `reps Z` the children at every node are
ordered by their least leaf label, so the leftmost leaf carries the least label of `Z`; at
`Z = Fin 4` this is the depth of the leaf labelled `0`, the target `y` of the star. -/
def depthZero : RTree α → ℕ
  | RTree.leaf _ => 0
  | RTree.node l _ => 1 + depthZero l

/-- The length `ℓ` of the tree path from the pinned root `x` to the target leaf `y`: the root
`x` sits one edge above the top internal vertex of a representative. -/
def ellOf (t : RTree (Fin 4)) : ℕ := 1 + depthZero t

/-- The four shapes of the accepted `m1` atlas of Lemma I.4.17 at `(p,q) = (3,0)`: `ℓ = 2`;
`ℓ = 3` balanced (`threeA`: the extra label sits at the `y`-node, a cherry at its parent);
`ℓ = 3` chain (`threeB`: a cherry at the `y`-node, the extra label at its parent); and `ℓ = 4`
chain (`four`: one label at each of the three path nodes). -/
inductive Shape : Type
  | two : Shape
  | threeA : Shape
  | threeB : Shape
  | four : Shape
  deriving DecidableEq, Repr

/-- The shape classifier.  The patterns are matched on the tree structure alone, so this is a
computable function and the multiplicities in `Main.lean` are decided, not assumed. -/
def shapeOf : RTree (Fin 4) → Shape
  | RTree.node (RTree.leaf _) _ => Shape.two
  | RTree.node (RTree.node (RTree.leaf _) (RTree.leaf _)) _ => Shape.threeA
  | RTree.node (RTree.node (RTree.leaf _) _) (RTree.leaf _) => Shape.threeB
  | _ => Shape.four

/-- The atlas node number of a leaf label: `0 = y ↦ 4`, `1 = x₁ ↦ 5`, `2 = x₂ ↦ 6`,
`3 = x₃ ↦ 7`, matching the coding of `m1`'s `atlasDiagrams`. -/
def leafNode : Fin 4 → ℕ
  | 0 => 4
  | 1 => 5
  | 2 => 6
  | _ => 7

/-- The edge list of a representative in the atlas node coding: node `0` is the pinned root
`x`, the internal vertices of `t` are numbered `1, 2, 3` in depth-first order, and the leaf
labelled `a` is numbered `leafNode a`.  The root `x` receives one edge to the top internal
vertex of `t`, so every edge list has seven edges. -/
def atlasEdgesAux : RTree (Fin 4) → ℕ → ℕ → ℕ × List (ℕ × ℕ)
  | RTree.leaf a, i, p => (i, [(p, leafNode a)])
  | RTree.node l r, i, p =>
      let e1 := atlasEdgesAux l (i + 1) i
      let e2 := atlasEdgesAux r e1.1 i
      (e2.1, (p, i) :: (e1.2 ++ e2.2))

/-- The seven-edge atlas diagram of a representative. -/
def atlasEdges (t : RTree (Fin 4)) : List (ℕ × ℕ) := (atlasEdgesAux t 1 0).2

/-- The fifteen seven-edge diagrams of the accepted `m1` atlas of Lemma I.4.17 at
`(p,q) = (3,0)`, reproduced verbatim from `smwzg77c3/m1/Defs.atlasDiagrams` (node coding
`0 = x`, `1,2,3` the internal vertices, `4 = y`, `5,6,7 = x₁,x₂,x₃`).  `Main.lean`
(`atlasDiagramSets`) proves that this list is exactly the fifteen canonical branch-and-root
representatives of `reps (Fin 4)`, read in the same node coding: it is complete and
duplicate-free. -/
def atlasDiagramsRef : List (List (ℕ × ℕ)) :=
  [ [(0, 1), (1, 2), (1, 4), (2, 3), (2, 5), (3, 6), (3, 7)],
    [(0, 1), (1, 2), (1, 4), (2, 3), (2, 6), (3, 5), (3, 7)],
    [(0, 1), (1, 2), (1, 4), (2, 3), (2, 7), (3, 5), (3, 6)],
    [(0, 1), (1, 2), (1, 3), (2, 6), (2, 7), (3, 5), (3, 4)],
    [(0, 1), (1, 2), (1, 3), (2, 6), (2, 4), (3, 5), (3, 7)],
    [(0, 1), (1, 2), (1, 3), (2, 7), (2, 4), (3, 5), (3, 6)],
    [(0, 1), (1, 2), (1, 7), (2, 3), (2, 4), (3, 5), (3, 6)],
    [(0, 1), (1, 2), (1, 6), (2, 3), (2, 4), (3, 5), (3, 7)],
    [(0, 1), (1, 2), (1, 5), (2, 3), (2, 4), (3, 6), (3, 7)],
    [(0, 1), (1, 2), (1, 7), (2, 3), (2, 6), (3, 5), (3, 4)],
    [(0, 1), (1, 2), (1, 7), (2, 3), (2, 5), (3, 6), (3, 4)],
    [(0, 1), (1, 2), (1, 6), (2, 3), (2, 7), (3, 5), (3, 4)],
    [(0, 1), (1, 2), (1, 6), (2, 3), (2, 5), (3, 7), (3, 4)],
    [(0, 1), (1, 2), (1, 5), (2, 3), (2, 7), (3, 6), (3, 4)],
    [(0, 1), (1, 2), (1, 5), (2, 3), (2, 6), (3, 7), (3, 4)]]

/-- The `m1` atlas read as a family of edge sets. -/
def atlasDiagramSets : Finset (Finset (ℕ × ℕ)) :=
  (atlasDiagramsRef.map List.toFinset).toFinset

/-- The six permutations of the three internal vertices `0, 1, 2` (written as a list so that
every statement about it below is decided by evaluation). -/
def perms3 : List (Fin 3 → Fin 3) :=
  [![0, 1, 2], ![1, 0, 2], ![2, 1, 0], ![0, 2, 1], ![1, 2, 0], ![2, 0, 1]]

/-- Relabelling of an atlas node by a permutation of the three internal vertices `1, 2, 3`;
the pinned root `0` and the leaf nodes `4, …, 7` are fixed. -/
def relabelNode (σ : Fin 3 → Fin 3) (n : ℕ) : ℕ :=
  if h : 1 ≤ n ∧ n ≤ 3 then (σ ⟨n - 1, by omega⟩).val + 1 else n

/-- Relabelling of an atlas diagram by a permutation of the internal vertices. -/
def relabelDiagram (σ : Fin 3 → Fin 3) (s : Finset (ℕ × ℕ)) : Finset (ℕ × ℕ) :=
  s.image fun e => (relabelNode σ e.1, relabelNode σ e.2)

/-- Two atlas diagrams are *isomorphic* when they differ only by the labelling of the three
unlabelled internal vertices — exactly the equivalence used in the "representatives of
isomorphism classes" of (I.2.2).  This is a `Bool`-valued test so that all statements about it
are decided by evaluation. -/
def diagramIsoB (s t : Finset (ℕ × ℕ)) : Bool :=
  perms3.any fun σ => relabelDiagram σ s == t

/-- `DiagramIso s t` is the propositional form of `diagramIsoB`. -/
def DiagramIso (s t : Finset (ℕ × ℕ)) : Prop := diagramIsoB s t = true

/-- The isomorphism class of a diagram, as a `Finset` of diagrams. -/
def isoClass (s : Finset (ℕ × ℕ)) : Finset (Finset (ℕ × ℕ)) :=
  (perms3.map fun σ => relabelDiagram σ s).toFinset

/-- The family of atlas diagrams of the canonical representatives. -/
def repsDiagramSets : Finset (Finset (ℕ × ℕ)) :=
  (reps (Finset.univ : Finset (Fin 4))).image fun t => (atlasEdges t).toFinset

end PercLib.CriticalLRP.QZeroStarCount
