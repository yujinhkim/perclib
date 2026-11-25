/-
Migration source: https://github.com/yujinhkim/Critical-Long-range-percolation
Integration revision: 3b3d1d0e43ef940bfaa2292ee5c2ee094ac4edbf
Licence: Apache-2.0 for the PercLib Lean sources and tooling; see third_party/critical-lrp/.
External provenance and modifications are recorded in the file-specific notices below.
-/

/-
The leaf-label form of the tree weight, and trees whose leaf-label *set* is a prescribed
finset.  This is the combinatorial layer of the tree-graph inequality (I.2.2) of

  T. Hutchcroft, *Critical long-range percolation I: High effective dimension*,
  arXiv:2508.18807v1, Section I.2.1, p. 22.
-/
module

public import Mathlib
public import PercLib.CriticalLRP.TreeExpansion.Moments

set_option linter.unusedSectionVars false
set_option linter.unusedSimpArgs false
set_option linter.unnecessarySimpa false
set_option linter.unusedTactic false
set_option linter.unusedVariables false

set_option autoImplicit true

set_option autoImplicit false
set_option linter.unusedSectionVars false
set_option maxHeartbeats 1000000

@[expose] public section

namespace PercLib.CriticalLRP.TreeExpansion

open Finset
open Classical

namespace RTree

variable {α : Type*} {β : Type*} {V : Type*} [Fintype V]

/-! ### The leaf-label weight -/

/-- The tree weight, with the leaf labelled `a` carrying the value `y a`. -/
noncomputable def wtL (k : V → V → ℝ) : RTree α → (α → V) → V → ℝ
  | leaf a, y, v => k v (y a)
  | node l r, y, v => ∑ w : V, k v w * wtL k l y w * wtL k r y w

@[simp] theorem wtL_leaf (k : V → V → ℝ) (a : α) (y : α → V) (v : V) :
    wtL k (leaf a) y v = k v (y a) := rfl

theorem wtL_node (k : V → V → ℝ) (l r : RTree α) (y : α → V) (v : V) :
    wtL k (node l r) y v = ∑ w : V, k v w * wtL k l y w * wtL k r y w := rfl

/-- `wtL` agrees with the repository's leaf-position weight. -/
theorem wt_eq_wtL (k : V → V → ℝ) (t : RTree α) :
    ∀ (y : α → V) (v : V), wt k t (fun q => y (leafOfPos t q)) v = wtL k t y v := by
  induction t with
  | leaf a => intro y v; rfl
  | node l r ihl ihr =>
      intro y v
      rw [wt, wtL_node]
      refine Finset.sum_congr rfl fun w _ => ?_
      simp only [leafOfPos]
      rw [ihl, ihr]

/-- Relabelling the leaves: a leaf label `a` becomes `f a`, and the value function is
precomposed with `f`. -/
theorem wtL_mapLabel (k : V → V → ℝ) (f : α → β) (t : RTree α) :
    ∀ (y : β → V) (v : V), wtL k (t.mapLabel f) y v = wtL k t (fun a => y (f a)) v := by
  induction t with
  | leaf a => intro y v; rfl
  | node l r ihl ihr =>
      intro y v
      rw [mapLabel, wtL_node, wtL_node]
      exact Finset.sum_congr rfl fun w _ => by rw [ihl y w, ihr y w]

/-- The tree weight only depends on the values at the leaves. -/
theorem wtL_congr (k : V → V → ℝ) {y y' : α → V} (t : RTree α)
    (h : ∀ a ∈ t.leaves, y a = y' a) (v : V) : wtL k t y v = wtL k t y' v := by
  induction t generalizing v with
  | leaf a => simp only [wtL_leaf]; rw [h a (by simp)]
  | node l r ihl ihr =>
      rw [wtL_node, wtL_node]
      refine Finset.sum_congr rfl fun w _ => ?_
      rw [ihl (fun a ha => h a (by simp [ha])) w, ihr (fun a ha => h a (by simp [ha])) w]

/-- `mapLabel` only depends on the values of the relabelling on the leaves. -/
theorem mapLabel_congr_leaves {f g : α → β} {t : RTree α}
    (h : ∀ a ∈ t.leaves, f a = g a) : t.mapLabel f = t.mapLabel g := by
  induction t with
  | leaf a => simp only [mapLabel]; rw [h a (by simp)]
  | node l r ihl ihr =>
      simp only [mapLabel]
      rw [ihl (fun a ha => h a (by simp [ha])), ihr (fun a ha => h a (by simp [ha]))]

/-- A tree over an empty label type does not exist. -/
theorem isEmpty_of_isEmpty [IsEmpty α] : IsEmpty (RTree α) :=
  ⟨fun t => by induction t with
    | leaf a => exact isEmptyElim a
    | node l r ihl ihr => exact ihl⟩

theorem leaves_ne_nil (t : RTree α) : t.leaves ≠ [] := by
  have hpos := numLeaves_pos t
  intro h
  rw [numLeaves, h] at hpos
  simp at hpos

theorem exists_mem_leaves (t : RTree α) : ∃ a, a ∈ t.leaves :=
  List.exists_mem_of_ne_nil _ (leaves_ne_nil t)

end RTree

/-! ### Trees with a prescribed leaf-label set -/

/-- Trees over `α` whose leaves are labelled injectively, using exactly the labels of `Z`. -/
abbrev LTon (α : Type*) [DecidableEq α] (Z : Finset α) : Type _ :=
  {t : RTree α // t.leaves.Nodup ∧ t.leaves.toFinset = Z}

/-- A finite-type instance for the fully labelled trees of an arbitrary finite label type. -/
@[instance_reducible] noncomputable def fintypeLT {α : Type*} [Fintype α] [DecidableEq α] :
    Fintype (RTree.LT α) :=
  Fintype.ofEquiv (RTree.LT (Fin (Fintype.card α)))
    (RTree.LTEquiv (Fintype.equivFin α).symm)

namespace LTon

variable {α : Type*} [DecidableEq α]

theorem leaves_nodup {Z : Finset α} (t : LTon α Z) : t.val.leaves.Nodup := t.2.1

theorem leaves_toFinset {Z : Finset α} (t : LTon α Z) : t.val.leaves.toFinset = Z := t.2.2

theorem leaves_subset {Z : Finset α} (t : LTon α Z) {a : α} (ha : a ∈ t.val.leaves) : a ∈ Z := by
  rw [← t.2.2, List.mem_toFinset]
  exact ha

theorem nonempty_of_mem {Z : Finset α} (t : LTon α Z) : Z.Nonempty := by
  obtain ⟨a, ha⟩ := RTree.exists_mem_leaves t.val
  exact ⟨a, t.leaves_subset ha⟩

/-- The map `Z`-labelled tree ↦ `↥Z`-fully-labelled tree. -/
noncomputable def ofLT {Z : Finset α} (u : RTree.LT ↥Z) : LTon α Z :=
  ⟨u.1.mapLabel Subtype.val,
    by
      rw [RTree.leaves_mapLabel]
      refine ⟨u.2.1.map Subtype.val_injective, ?_⟩
      ext a
      simp only [List.mem_toFinset, List.mem_map, Finset.mem_image, Finset.mem_univ, true_and]
      constructor
      · rintro ⟨b, -, rfl⟩; exact b.2
      · intro ha
        exact ⟨⟨a, ha⟩, RTree.mem_leaves_of_fullyLabelled u.2 ⟨a, ha⟩, rfl⟩⟩

theorem ofLT_injective {Z : Finset α} : Function.Injective (ofLT (α := α) (Z := Z)) := by
  intro u u' h
  have h' : u.1.mapLabel Subtype.val = u'.1.mapLabel Subtype.val := congrArg Subtype.val h
  exact Subtype.ext (RTree.mapLabel_injective Subtype.val_injective h')

theorem ofLT_surjective {Z : Finset α} : Function.Surjective (ofLT (α := α) (Z := Z)) := by
  intro t
  obtain ⟨c₀, hc₀⟩ := t.nonempty_of_mem
  set φ : α → ↥Z := fun a => if h : a ∈ Z then ⟨a, h⟩ else ⟨c₀, hc₀⟩ with hφ
  have hφval : ∀ a ∈ (t : RTree α).leaves, (φ a).val = a := by
    intro a ha
    simp only [hφ]
    rw [dite_eq_left (t.leaves_subset ha)]
  have hinj : ∀ a ∈ (t : RTree α).leaves, ∀ b ∈ (t : RTree α).leaves, φ a = φ b → a = b := by
    intro a ha b hb hab
    rw [← hφval a ha, ← hφval b hb, hab]
  have hlen : ((t : RTree α).leaves.map φ).length = Fintype.card ↥Z := by
    rw [List.length_map, Fintype.card_coe, ← List.toFinset_card_of_nodup t.2.1, t.2.2]
  refine ⟨⟨(t : RTree α).mapLabel φ, ?_⟩, ?_⟩
  · -- the relabelled tree is fully labelled by `↥Z`
    rw [RTree.FullyLabelled, RTree.leaves_mapLabel]
    exact ⟨t.2.1.map_on hinj, hlen⟩
  · -- and it maps back to `t`
    apply Subtype.ext
    show ((t : RTree α).mapLabel φ).mapLabel Subtype.val = (t : RTree α)
    rw [RTree.mapLabel_mapLabel,
      RTree.mapLabel_congr_leaves (f := fun a => Subtype.val (φ a)) (g := id)
        (fun a ha => hφval a ha),
      RTree.mapLabel_id]

/-- Trees with leaf set `Z` correspond to trees fully labelled by `↥Z`. -/
noncomputable def equiv (Z : Finset α) : RTree.LT ↥Z ≃ LTon α Z :=
  Equiv.ofBijective ofLT ⟨ofLT_injective, ofLT_surjective⟩

noncomputable instance instFintype {Z : Finset α} : Fintype (LTon α Z) :=
  haveI : Fintype (RTree.LT ↥Z) := fintypeLT
  Fintype.ofEquiv (RTree.LT ↥Z) (equiv Z)

end LTon

end PercLib.CriticalLRP.TreeExpansion
