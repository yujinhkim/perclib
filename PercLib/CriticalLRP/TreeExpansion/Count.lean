/-
Migration source: https://github.com/yujinhkim/Critical-Long-range-percolation
Integration revision: 3b3d1d0e43ef940bfaa2292ee5c2ee094ac4edbf
Licence: Apache-2.0 for the PercLib Lean sources and tooling; see third_party/critical-lrp/.
External provenance and modifications are recorded in the file-specific notices below.
-/

/-
Counting leaf-labelled rooted binary trees: the double factorial `(2p − 3)!!` of
inequality (I.2.3) of

  T. Hutchcroft, *Critical long-range percolation I: High effective dimension*,
  arXiv:2508.18807v1, Section I.2.1, p. 22:

"the combinatorial factor `(2p−3)!!` counts the number of trees with `p+1` leaves labelled
`{0, ..., p}` and with all other vertices unlabelled and of degree 3".

`RTree` is a type of *plane* (ordered) trees. A non-plane tree with `p ≥ 1` labelled
leaves has exactly `2^(p−1)` orderings (there are `p−1` internal vertices and no
automorphism fixes all leaves), so

  `#{non-plane trees with p leaves} = #{plane trees with p leaves} / 2^(p−1)`.

The file proves for the plane count `T p = Fintype.card (LT (Fin p))`

* `card_LT_sum`    : `T' (α ⊕ PUnit) ≤ 2·(2·#α−1)·T' α`  (the peeling surjection),
* `card_LT_iterate`: `T' (Option^[n] PUnit) ≤ 2^n·(2n−1)!!`,
* `card_LT_fin`    : `T p ≤ 2^(p−1)·(2p−3)!!`,

which is `#{non-plane trees with p leaves} ≤ (2p−3)!!` after dividing by `2^(p−1)`;
equality holds, but only the upper bound is needed for (I.2.3). The paper's double
factorial is `PercLib.CriticalLRP.VolumeMoments.M (p−1)`.
-/
module

public import Mathlib
public import PercLib.CriticalLRP.TreeExpansion.Insert

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

universe u

variable {α : Type*} {β : Type*}

/-- A tree is *fully labelled* by a finite type `α` when every label occurs exactly once. -/
def FullyLabelled [Fintype α] (t : RTree α) : Prop :=
  t.leaves.Nodup ∧ t.leaves.length = Fintype.card α

theorem fullyLabelled_mapLabel [Fintype α] [Fintype β] {e : α ≃ β} {t : RTree α}
    (h : FullyLabelled t) : FullyLabelled (t.mapLabel e) := by
  obtain ⟨h1, h2⟩ := h
  refine ⟨?_, ?_⟩
  · rw [leaves_mapLabel]
    exact h1.map e.injective
  · rw [leaves_mapLabel, List.length_map, h2, Fintype.card_congr e]

theorem fullyLabelled_of_mapLabel [Fintype α] [Fintype β] {e : α ≃ β}
    {t : RTree α} (h : FullyLabelled (t.mapLabel e)) : FullyLabelled t := by
  obtain ⟨h1, h2⟩ := h
  rw [leaves_mapLabel] at h1 h2
  refine ⟨?_, ?_⟩
  · exact h1.of_map
  · rw [← List.length_map (f := ⇑e), h2, Fintype.card_congr e]

theorem mapLabel_id (t : RTree α) : t.mapLabel id = t := by
  induction t with
  | leaf a => rfl
  | node l r ihl ihr => simp [mapLabel, ihl, ihr]

variable [Fintype α]

/-- Every label occurs in a fully labelled tree. -/
theorem mem_leaves_of_fullyLabelled {t : RTree α} (h : FullyLabelled t)
    (a : α) : a ∈ t.leaves := by
  classical
  obtain ⟨h1, h2⟩ := h
  have hc : t.leaves.toFinset.card = Fintype.card α := by
    rw [List.toFinset_card_of_nodup h1, h2]
  have huniv : t.leaves.toFinset = Finset.univ := Finset.eq_univ_of_card _ hc
  have hmem : a ∈ t.leaves.toFinset := by rw [huniv]; exact Finset.mem_univ a
  exact List.mem_toFinset.mp hmem

theorem count_of_fullyLabelled [DecidableEq α] {t : RTree α} (h : FullyLabelled t) (a : α) :
    t.leaves.count a = 1 := by
  have hle : t.leaves.count a ≤ 1 := List.nodup_iff_count_le_one.mp h.1 a
  have hpos : 0 < t.leaves.count a := List.count_pos_iff.mpr (mem_leaves_of_fullyLabelled h a)
  omega

/-! ### The family of fully labelled trees -/

/-- Rooted binary trees whose leaves are labelled by `α`, each label occurring once. -/
def LT (α : Type u) [Fintype α] : Type u := {t : RTree α // FullyLabelled t}

noncomputable instance instDecidableEqLT : DecidableEq (LT α) := Classical.decEq _

/-- Relabelling identifies the families over equivalent label types. -/
def LTEquiv [Fintype β] (e : α ≃ β) : LT α ≃ LT β where
  toFun t := ⟨t.val.mapLabel e, fullyLabelled_mapLabel t.2⟩
  invFun t := ⟨t.val.mapLabel e.symm, fullyLabelled_mapLabel t.2⟩
  left_inv t := by
    apply Subtype.ext
    show (t.val.mapLabel e).mapLabel e.symm = t.val
    rw [mapLabel_mapLabel]
    have : (fun a => e.symm (e a)) = id := by funext a; exact e.symm_apply_apply a
    rw [this, mapLabel_id]
  right_inv t := by
    apply Subtype.ext
    show (t.val.mapLabel e.symm).mapLabel e = t.val
    rw [mapLabel_mapLabel]
    have : (fun a => e (e.symm a)) = id := by funext a; exact e.apply_symm_apply a
    rw [this, mapLabel_id]

/-! ### Insertion into fully labelled trees, and peeling -/

theorem sum_inl_injective : Function.Injective (Sum.inl : α → α ⊕ PUnit) := fun _ _ h => Sum.inl.inj h

theorem sum_inr_not_mem_map_inl (l : List α) : (Sum.inr ⟨⟩ : α ⊕ PUnit) ∉ l.map Sum.inl := by
  intro h
  obtain ⟨a, -, ha⟩ := List.mem_map.mp h
  simp at ha

/-- Insertion into a fully labelled tree gives a fully labelled tree. -/
theorem fullyLabelled_insertAt [DecidableEq α] {t : RTree α} (ht : FullyLabelled t)
    (q : Pos t) (left : Bool) :
    FullyLabelled (insertAt (Sum.inl : α → α ⊕ PUnit) (Sum.inr ⟨⟩) left t q) := by
  have hperm := leaves_insertAt (Sum.inl : α → α ⊕ PUnit) (Sum.inr ⟨⟩) left t q
  constructor
  · refine hperm.nodup_iff.mpr ?_
    exact List.Nodup.cons (sum_inr_not_mem_map_inl _) (ht.1.map sum_inl_injective)
  · have hlen := hperm.length_eq
    simp only [List.length_cons, List.length_map] at hlen
    rw [hlen, ht.2, Fintype.card_sum, Fintype.card_punit]

/-- The insertion map out of `(tree, vertex, side)`. -/
noncomputable def insertMap [DecidableEq α] :
    (Σ t : LT α, Pos t.val × Bool) → LT (α ⊕ PUnit) :=
  fun q => ⟨insertAt (Sum.inl : α → α ⊕ PUnit) (Sum.inr ⟨⟩) q.2.2 q.1.val q.2.1,
    fullyLabelled_insertAt q.1.2 q.2.1 q.2.2⟩

theorem count_one_of_fullyLabelled_sum [DecidableEq α] {t : RTree (α ⊕ PUnit)}
    (h : FullyLabelled t) : t.leaves.count (Sum.inr ⟨⟩) = 1 := by
  have hle : t.leaves.count (Sum.inr ⟨⟩) ≤ 1 := List.nodup_iff_count_le_one.mp h.1 _
  have hpos : 0 < t.leaves.count (Sum.inr ⟨⟩) :=
    List.count_pos_iff.mpr (mem_leaves_of_fullyLabelled h _)
  omega

theorem insertMap_surjective [DecidableEq α] [Nonempty α] :
    Function.Surjective (insertMap (α := α)) := by
  rintro ⟨s, hs⟩
  have hnum : s.numLeaves = Fintype.card α + 1 := by
    have h1 : s.numLeaves = Fintype.card (α ⊕ PUnit) := hs.2
    rw [h1, Fintype.card_sum, Fintype.card_punit]
  have h2 : 2 ≤ s.numLeaves := by
    rw [hnum]
    have : 0 < Fintype.card α := Fintype.card_pos_iff.mpr ‹Nonempty α›
    omega
  have hcount : s.leaves.count (Sum.inr ⟨⟩) = 1 := count_one_of_fullyLabelled_sum hs
  obtain ⟨t, q, left, hins⟩ := exists_insertAt s h2 hcount
  have htfull : FullyLabelled t := by
    have hperm := leaves_insertAt (Sum.inl : α → α ⊕ PUnit) (Sum.inr ⟨⟩) left t q
    rw [hins] at hperm
    obtain ⟨h1, h2⟩ := hs
    rw [hperm.nodup_iff] at h1
    refine ⟨(List.nodup_cons.mp h1).2.of_map, ?_⟩
    have hlen := hperm.length_eq
    simp only [List.length_cons, List.length_map] at hlen
    rw [h2] at hlen
    rw [Fintype.card_sum, Fintype.card_punit] at hlen
    omega
  exact ⟨⟨⟨t, htfull⟩, q, left⟩, Subtype.ext hins⟩

/-! ### The counting recursion -/

noncomputable instance instFintypeLTSum [DecidableEq α] [Nonempty α] [Fintype (LT α)] :
    Fintype (LT (α ⊕ PUnit)) :=
  Fintype.ofSurjective (insertMap (α := α)) insertMap_surjective

/-- **The counting recursion.** `T' (α ⊕ PUnit) ≤ 2·(2·#α − 1)·T' α`: every fully
labelled tree with `#α + 1` leaves is obtained by inserting one leaf above one of the
`2·#α − 1` vertices of a fully labelled tree with `#α` leaves, in one of two ways. -/
theorem card_LT_sum [DecidableEq α] [Nonempty α] [Fintype (LT α)] :
    Fintype.card (LT (α ⊕ PUnit)) ≤ 2 * (2 * Fintype.card α - 1) * Fintype.card (LT α) := by
  have h := Fintype.card_le_of_surjective (insertMap (α := α)) insertMap_surjective
  calc Fintype.card (LT (α ⊕ PUnit))
      ≤ Fintype.card (Σ t : LT α, Pos t.val × Bool) := h
    _ = ∑ t : LT α, Fintype.card (Pos t.val × Bool) := by rw [Fintype.card_sigma]
    _ = ∑ _t : LT α, (2 * (2 * Fintype.card α - 1)) := by
        refine Finset.sum_congr rfl fun t _ => ?_
        have hle : (t : LT α).1.numLeaves = Fintype.card α := t.2.2
        rw [Fintype.card_prod, Fintype.card_bool, card_pos, hle]
        exact Nat.mul_comm _ 2
    _ = 2 * (2 * Fintype.card α - 1) * Fintype.card (LT α) := by
        rw [Finset.sum_const, Finset.card_univ, smul_eq_mul, mul_comm]

/-! ### The finite label types `Fin n` -/

/-- The equivalence `Fin (n+1) ≃ Fin n ⊕ PUnit` sending `0` to the extra point. -/
def finSuccEquivSum (n : ℕ) : Fin (n+1) ≃ Fin n ⊕ PUnit.{1} where
  toFun := Fin.cases (Sum.inr ⟨⟩) (fun j => Sum.inl j)
  invFun := Sum.elim Fin.succ (fun _ => 0)
  left_inv := by
    intro i
    refine Fin.cases ?_ (fun j => ?_) i
    · rfl
    · rfl
  right_inv := by
    intro s
    rcases s with j | u
    · rfl
    · obtain rfl : u = ⟨⟩ := Subsingleton.elim u ⟨⟩
      rfl

/-- The unique fully labelled tree over a single label. -/
def theLT1 : LT (Fin 1) :=
  ⟨leaf 0, by
    refine ⟨?_, ?_⟩
    · simp
    · simp [numLeaves]⟩

theorem eq_theLT1 (s : LT (Fin 1)) : s = theLT1 := by
  obtain ⟨t, ht⟩ := s
  have hnum : t.numLeaves = 1 := by
    show t.leaves.length = 1
    rw [ht.2]
    simp
  cases t with
  | leaf a =>
      obtain rfl : a = 0 := Subsingleton.elim a 0
      rfl
  | node l r =>
      exfalso
      rw [numLeaves_node] at hnum
      have h1 : 0 < l.numLeaves := numLeaves_pos l
      have h2 : 0 < r.numLeaves := numLeaves_pos r
      omega

instance instIsEmptyLTFinZero : IsEmpty (LT (Fin 0)) := ⟨fun t => by
  have h := t.2.2
  rw [show Fintype.card (Fin 0) = 0 from rfl] at h
  exact absurd h (Nat.pos_iff_ne_zero.mp t.1.numLeaves_pos)⟩

noncomputable instance instFintypeLTFin : (n : ℕ) → Fintype (LT (Fin n))
  | 0 => Fintype.ofIsEmpty
  | 1 => haveI : Subsingleton (LT (Fin 1)) := ⟨fun a b => (eq_theLT1 a).trans (eq_theLT1 b).symm⟩
      Fintype.ofSubsingleton theLT1
  | k + 2 => by
      haveI : Fintype (LT (Fin (k+1))) := instFintypeLTFin (k+1)
      haveI : Nonempty (Fin (k+1)) := ⟨⟨0, Nat.succ_pos k⟩⟩
      exact Fintype.ofEquiv (LT (Fin (k+1) ⊕ PUnit.{1}))
        (LTEquiv (finSuccEquivSum (k+1))).symm

theorem card_LT_fin_one : Fintype.card (LT (Fin 1)) = 1 := by
  classical
  refine Fintype.card_eq_one_iff.mpr ⟨theLT1, fun s => eq_theLT1 s⟩

/-- **The counting recursion for `Fin n`.** -/
theorem card_LT_fin_succ (n : ℕ) :
    Fintype.card (LT (Fin (n+2))) ≤ 2 * (2 * (n+1) - 1) * Fintype.card (LT (Fin (n+1))) := by
  have : Nonempty (Fin (n+1)) := ⟨⟨0, Nat.succ_pos n⟩⟩
  have h := card_LT_sum (α := Fin (n+1))
  rw [← Fintype.card_congr (LTEquiv (finSuccEquivSum (n+1)))] at h
  simpa using h

/-- **The double factorial bound.** A non-plane tree with `n` labelled leaves has exactly
`2^(n−1)` plane orderings, so this says that the number of non-plane trees with `n`
labelled leaves, i.e. with `n−1` unlabelled degree-three internal vertices, is at most
`(2n−3)!!` — the factor in (I.2.3). -/
theorem card_LT_fin_le : ∀ n : ℕ,
    Fintype.card (LT (Fin n)) ≤ 2 ^ (n - 1) * VolumeMoments.M (n - 1)
  | 0 => by
      have h0 : Fintype.card (LT (Fin 0)) = 0 := Fintype.card_eq_zero_iff.mpr instIsEmptyLTFinZero
      rw [h0]
      simp
  | 1 => by
      rw [card_LT_fin_one]
      simp
  | n + 2 => by
      have hrec := card_LT_fin_succ n
      have ih := card_LT_fin_le (n+1)
      have hM : VolumeMoments.M (n+1) = (2 * n + 1) * VolumeMoments.M n :=
        VolumeMoments.M_succ n
      have hexp : 2 * (2 * (n+1) - 1) = 2 * (2 * n + 1) := by omega
      rw [hexp] at hrec
      have hidx : (n + 1) - 1 = n := rfl
      rw [hidx] at ih
      have hgoal : (n + 2) - 1 = n + 1 := rfl
      rw [hgoal]
      calc Fintype.card (LT (Fin (n+2)))
          ≤ 2 * (2 * n + 1) * Fintype.card (LT (Fin (n+1))) := hrec
        _ ≤ 2 * (2 * n + 1) * (2 ^ n * VolumeMoments.M n) :=
            Nat.mul_le_mul_left _ ih
        _ = 2 ^ (n + 1) * VolumeMoments.M (n + 1) := by
            rw [hM]
            ring

end RTree

end PercLib.CriticalLRP.TreeExpansion
