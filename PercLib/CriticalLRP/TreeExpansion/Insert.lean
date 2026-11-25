/-
Migration source: https://github.com/yujinhkim/Critical-Long-range-percolation
Integration revision: 3b3d1d0e43ef940bfaa2292ee5c2ee094ac4edbf
Licence: Apache-2.0 for the PercLib Lean sources and tooling; see third_party/critical-lrp/.
External provenance and modifications are recorded in the file-specific notices below.
-/

/-
Insertion of a new leaf above a vertex of a rooted binary tree, and the resulting
"peeling" surjection used to count leaf-labelled trees.

Combinatorial layer for the constant `(2p − 3)!!` in inequality (I.2.3) of

  T. Hutchcroft, *Critical long-range percolation I: High effective dimension*,
  arXiv:2508.18807v1, Section I.2.1, p. 22.

`RTree.insertAt f b left t p` replaces the subtree of `t` at the vertex `p` by a node
with children `leaf b` and that subtree (relabelled by `f`); `left` chooses on which side
the new leaf is placed. In the unrooted picture this inserts a new leaf above the vertex
`p`. Consequently

* `RTree.leaves_insertAt`: the new leaf label is added to the multiset of leaf labels;
* `RTree.exists_insertAt`: **every** tree with at least two leaves and exactly one leaf
  labelled `Sum.inr ()` arises as `insertAt` from a tree over `α`, a vertex, and a side.
  This is the surjectivity behind
  `#{trees with p+1 leaves} ≤ 2·(2p−1)·#{trees with p leaves}`, hence behind the
  double-factorial count of (I.2.3).

Note that `RTree` is a type of *plane* (ordered) trees; a non-plane tree with `p` leaves
and distinct leaf labels has exactly `2^(p−1)` orderings, which is how the factor
`2^(p−1)` enters `RTree.card_labelled`.

Note also the position type: `Pos (node l r) = Pos l ⊕ (Pos r ⊕ PUnit)` (since `⊕` is
right-associative); the root of a node is `Sum.inr (Sum.inr ⟨⟩)` and `RTree.root` gives the
root of an arbitrary tree.
-/
module

public import Mathlib
public import PercLib.CriticalLRP.TreeExpansion.Weight

set_option linter.unusedSectionVars false
set_option linter.unusedSimpArgs false
set_option linter.unnecessarySimpa false
set_option linter.unusedTactic false
set_option linter.unusedVariables false

set_option autoImplicit true

set_option autoImplicit false

@[expose] public section

namespace PercLib.CriticalLRP.TreeExpansion

open Finset

namespace RTree

variable {α : Type*} {β : Type*} {γ : Type*}

/-- The root, as a position. -/
def root : (t : RTree α) → Pos t
  | leaf _ => ⟨⟩
  | node _ _ => Sum.inr (Sum.inr ⟨⟩)

/-- A node carrying the new leaf `b` on a chosen side and the subtree `s` on the other. -/
def mk (left : Bool) (b : β) (s : RTree β) : RTree β :=
  if left then node (leaf b) s else node s (leaf b)

/-- Insertion of a new leaf labelled `b` above the vertex `p` of `t`, relabelling the old
leaves by `f`; `left` chooses the side of the new leaf. -/
def insertAt (f : α → β) (b : β) (left : Bool) : (t : RTree α) → Pos t → RTree β
  | leaf a, _ => mk left b (leaf (f a))
  | node l r, Sum.inl p => node (insertAt f b left l p) (r.mapLabel f)
  | node l r, Sum.inr (Sum.inl p) => node (l.mapLabel f) (insertAt f b left r p)
  | node l r, Sum.inr (Sum.inr _) => mk left b (node (l.mapLabel f) (r.mapLabel f))

theorem insertAt_root (f : α → β) (b : β) (left : Bool) (t : RTree α) :
    insertAt f b left t (root t) = mk left b (t.mapLabel f) := by
  cases t with
  | leaf a => rfl
  | node l r => rfl


/-! ### Elementary properties -/

theorem mapLabel_mapLabel (f : α → β) (g : β → γ) (t : RTree α) :
    (t.mapLabel f).mapLabel g = t.mapLabel fun a => g (f a) := by
  induction t with
  | leaf a => rfl
  | node l r ihl ihr => simp [mapLabel, ihl, ihr]

theorem mapLabel_injective {f : α → β} (hf : Function.Injective f) :
    Function.Injective (mapLabel f) := by
  intro t
  induction t with
  | leaf a =>
      intro t' h
      cases t' with
      | leaf a' => simp only [mapLabel, leaf.injEq] at h; rw [hf h]
      | node l r => simp [mapLabel] at h
  | node l r ihl ihr =>
      intro t' h
      cases t' with
      | leaf a => simp [mapLabel] at h
      | node l' r' =>
          simp only [mapLabel, node.injEq] at h
          rw [ihl h.1, ihr h.2]

theorem mk_isNode (left : Bool) (b : β) (s : RTree β) :
    ∃ l r : RTree β, mk left b s = node l r := by
  cases left
  · exact ⟨s, leaf b, rfl⟩
  · exact ⟨leaf b, s, rfl⟩

theorem mk_leaves (left : Bool) (b : β) (s : RTree β) :
    (mk left b s).leaves = if left then b :: s.leaves else s.leaves ++ [b] := by
  cases left <;> rfl

/-- The inserted tree is always a node. -/
theorem insertAt_isNode (f : α → β) (b : β) (left : Bool) (t : RTree α) (p : Pos t) :
    ∃ l r : RTree β, insertAt f b left t p = node l r := by
  cases t with
  | leaf a => exact mk_isNode left b (leaf (f a))
  | node l r =>
      cases p with
      | inl p => exact ⟨_, _, rfl⟩
      | inr p =>
          cases p with
          | inl p => exact ⟨_, _, rfl⟩
          | inr _ => exact mk_isNode left b (node (l.mapLabel f) (r.mapLabel f))

/-- Inserting a label into a list keeps the multiset of labels. -/
theorem perm_cons_append_cons {x : List α} {b : α} {y : List α} :
    List.Perm (x ++ (b :: y)) (b :: (x ++ y)) := by
  have h1 : x ++ (b :: y) = (x ++ [b]) ++ y := by simp
  rw [h1]
  exact List.Perm.append_right y
    (List.perm_append_comm (l₁ := x) (l₂ := [b]))

/-- The leaves of a tree with an inserted leaf: the new label is added to the multiset of
leaf labels. -/
theorem leaves_insertAt (f : α → β) (b : β) (left : Bool) :
    ∀ (t : RTree α) (p : Pos t),
      List.Perm (insertAt f b left t p).leaves (b :: t.leaves.map f) := by
  intro t
  induction t with
  | leaf a =>
      intro p
      cases p
      cases left
      · show List.Perm ((leaf (f a)).leaves ++ [b]) _
        exact List.Perm.swap b (f a) []
      · show List.Perm (b :: (leaf (f a)).leaves) _
        simp [leaves_leaf]
  | node l r ihl ihr =>
      intro p
      cases p with
      | inl p =>
          show List.Perm ((insertAt f b left l p).leaves ++ (r.mapLabel f).leaves)
            (b :: (l.node r).leaves.map f)
          rw [leaves_mapLabel, leaves_node, List.map_append]
          exact (List.Perm.append_right _ (ihl p)).trans (by rw [List.cons_append])
      | inr p =>
          cases p with
          | inl p =>
              show List.Perm ((l.mapLabel f).leaves ++ (insertAt f b left r p).leaves)
                (b :: (l.node r).leaves.map f)
              rw [leaves_mapLabel, leaves_node, List.map_append]
              exact (List.Perm.append_left _ (ihr p)).trans perm_cons_append_cons
          | inr _ =>
              show List.Perm (mk left b (node (l.mapLabel f) (r.mapLabel f))).leaves
                (b :: (l.node r).leaves.map f)
              rw [mk_leaves, leaves_node, leaves_mapLabel, leaves_mapLabel, leaves_node]
              simp only [List.map_append]
              cases left
              · show List.Perm ((List.map f l.leaves ++ List.map f r.leaves) ++ [b])
                  (b :: (List.map f l.leaves ++ List.map f r.leaves))
                exact List.perm_append_comm
              · exact List.Perm.refl _

theorem mk_mapLabel (g : β → γ) (left : Bool) (b : β) (s : RTree β) :
    (mk left b s).mapLabel g = mk left (g b) (s.mapLabel g) := by
  cases left <;> rfl

/-- Relabelling commutes with insertion, at the same vertex. -/
theorem mapLabel_insertAt (g : β → γ) (f : α → β) (b : β) (left : Bool) :
    ∀ (t : RTree α) (p : Pos t),
      (insertAt f b left t p).mapLabel g = insertAt (fun a => g (f a)) (g b) left t p := by
  intro t
  induction t with
  | leaf a =>
      intro p
      cases p
      cases left <;> rfl
  | node l r ihl ihr =>
      intro p
      cases p with
      | inl p =>
          show (node (insertAt f b left l p) (r.mapLabel f)).mapLabel g = _
          rw [mapLabel, mapLabel_mapLabel, ihl p]
          rfl
      | inr p =>
          cases p with
          | inl p =>
              show (node (l.mapLabel f) (insertAt f b left r p)).mapLabel g = _
              rw [mapLabel, mapLabel_mapLabel, ihr p]
              rfl
          | inr _ =>
              show (mk left b (node (l.mapLabel f) (r.mapLabel f))).mapLabel g = _
              rw [mk_mapLabel, mapLabel, mapLabel_mapLabel, mapLabel_mapLabel]
              rfl

/-! ### The peeling direction -/

variable [DecidableEq α]

/-- A tree all of whose labels lie in the range of `f` is a relabelling. -/
theorem exists_mapLabel_of_forall (f : α → β) :
    ∀ (t : RTree β), (∀ c ∈ t.leaves, ∃ a : α, f a = c) → ∃ t₀ : RTree α, t₀.mapLabel f = t := by
  intro t
  induction t with
  | leaf c =>
      intro h
      obtain ⟨a, ha⟩ := h c (by simp)
      exact ⟨leaf a, by simp [mapLabel, ha]⟩
  | node l r ihl ihr =>
      intro h
      obtain ⟨l₀, hl⟩ := ihl fun c hc => h c (by simp [hc])
      obtain ⟨r₀, hr⟩ := ihr fun c hc => h c (by simp [hc])
      exact ⟨node l₀ r₀, by simp [mapLabel, hl, hr]⟩

/-- The label `Sum.inr ()` does not occur in the image of `Sum.inl` on a list. -/
theorem count_inr_map_inl (l : List α) :
    (l.map (Sum.inl : α → α ⊕ PUnit)).count (Sum.inr ⟨⟩) = 0 := by
  induction l with
  | nil => rfl
  | cons a t ih => simp [List.count_cons, ih]

/-- A tree with no `Sum.inr ()` leaf has all its labels in the range of `Sum.inl`. -/
theorem exists_inl_of_count_zero {t : RTree (α ⊕ PUnit)}
    (h : t.leaves.count (Sum.inr ⟨⟩) = 0) : ∀ c ∈ t.leaves, ∃ a : α, (Sum.inl a : α ⊕ PUnit) = c := by
  intro c hc
  rcases c with a | u
  · exact ⟨a, rfl⟩
  · exfalso
    have hu : u = ⟨⟩ := Subsingleton.elim u ⟨⟩
    subst hu
    have hpos := List.count_pos_iff.mpr hc
    omega

/-- A single-leaf tree with exactly one `Sum.inr ()` and at least two leaves: impossible. -/
theorem eq_inr_of_leaf_count {c : α ⊕ PUnit}
    (h : (RTree.leaf c).leaves.count (Sum.inr ⟨⟩) = 1) : c = Sum.inr ⟨⟩ := by
  have hc : ([c] : List (α ⊕ PUnit)).count (Sum.inr ⟨⟩) = 1 := h
  rw [List.count_cons, List.count_nil] at hc
  rcases c with a | u
  · simp at hc
  · have hu : u = ⟨⟩ := Subsingleton.elim u ⟨⟩
    rw [hu]

/-- **Peeling.** A tree over `α ⊕ PUnit` with at least two leaves in which the label
`Sum.inr ()` occurs exactly once is obtained by inserting that label above some vertex of
a tree over `α`. -/
theorem exists_insertAt :
    ∀ (t : RTree (α ⊕ PUnit)), 2 ≤ t.numLeaves → t.leaves.count (Sum.inr ⟨⟩) = 1 →
      ∃ (t₀ : RTree α) (p : Pos t₀) (left : Bool),
        insertAt (Sum.inl : α → α ⊕ PUnit) (Sum.inr ⟨⟩) left t₀ p = t := by
  intro t
  induction t with
  | leaf c =>
      intro h2 _
      simp only [numLeaves_leaf] at h2
      omega
  | node l r ihl ihr =>
      intro _ h
      rw [leaves_node, List.count_append] at h
      have hl1 : l.leaves.count (Sum.inr ⟨⟩) ≤ 1 := by omega
      have hr1 : r.leaves.count (Sum.inr ⟨⟩) ≤ 1 := by omega
      rcases Nat.eq_zero_or_pos (l.leaves.count (Sum.inr ⟨⟩)) with h0 | hpos
      · -- the new leaf is in the right subtree
        have h1 : r.leaves.count (Sum.inr ⟨⟩) = 1 := by omega
        obtain ⟨l₀, hl₀⟩ := exists_mapLabel_of_forall (Sum.inl : α → α ⊕ PUnit) l
          (exists_inl_of_count_zero h0)
        cases r with
        | leaf c =>
            have hc : c = Sum.inr (⟨⟩ : PUnit) := eq_inr_of_leaf_count h1
            subst hc
            exact ⟨l₀, root l₀, false, by
              rw [insertAt_root]
              show mk false (Sum.inr ⟨⟩) (l₀.mapLabel (Sum.inl : α → α ⊕ PUnit))
                = node l (leaf (Sum.inr ⟨⟩))
              rw [mk, hl₀]
              rfl⟩
        | node rl rr =>
            have hr2 : 2 ≤ (node rl rr).numLeaves := by
              rw [numLeaves_node]; have := numLeaves_pos rl; have := numLeaves_pos rr; omega
            obtain ⟨r₀, p₀, left₀, hrp⟩ := ihr hr2 h1
            exact ⟨node l₀ r₀, Sum.inr (Sum.inl p₀), left₀, by
              show node (l₀.mapLabel (Sum.inl : α → α ⊕ PUnit))
                (insertAt Sum.inl (Sum.inr ⟨⟩) left₀ r₀ p₀) = node l (node rl rr)
              rw [hl₀, hrp]⟩
      · -- the new leaf is in the left subtree
        have h1 : l.leaves.count (Sum.inr ⟨⟩) = 1 := by omega
        have h2 : r.leaves.count (Sum.inr ⟨⟩) = 0 := by omega
        obtain ⟨r₀, hr₀⟩ := exists_mapLabel_of_forall (Sum.inl : α → α ⊕ PUnit) r
          (exists_inl_of_count_zero h2)
        cases l with
        | leaf c =>
            have hc : c = Sum.inr (⟨⟩ : PUnit) := eq_inr_of_leaf_count h1
            subst hc
            exact ⟨r₀, root r₀, true, by
              rw [insertAt_root]
              show mk true (Sum.inr ⟨⟩) (r₀.mapLabel (Sum.inl : α → α ⊕ PUnit))
                = node (leaf (Sum.inr ⟨⟩)) r
              rw [mk, hr₀]
              rfl⟩
        | node ll lr =>
            have hl2 : 2 ≤ (node ll lr).numLeaves := by
              rw [numLeaves_node]; have := numLeaves_pos ll; have := numLeaves_pos lr; omega
            obtain ⟨l₀, p₀, left₀, hlp⟩ := ihl hl2 h1
            exact ⟨node l₀ r₀, Sum.inl p₀, left₀, by
              show node (insertAt Sum.inl (Sum.inr ⟨⟩) left₀ l₀ p₀)
                (r₀.mapLabel (Sum.inl : α → α ⊕ PUnit)) = node (node ll lr) r
              rw [hlp, hr₀]⟩

end RTree

end PercLib.CriticalLRP.TreeExpansion
