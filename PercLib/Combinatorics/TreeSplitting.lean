/-
Copyright (c) 2026 PercLib contributors. Released under Apache 2.0.
New proofs, written for package Q-66 (issue 373, roadmap T-6), using mathlib's
`SimpleGraph.fromEdgeSet`, walks and finite sets. Source motivation: T. Hutchcroft,
arXiv:2008.11197v2, §2.1, the tree-splitting step in the proof of Theorem 2.3.
No source text or code is copied.
-/
module

public import Mathlib.Combinatorics.SimpleGraph.Acyclic
public import Mathlib.Algebra.Order.BigOperators.Group.Finset
public import Mathlib.Basic.Real.Basic
public import Mathlib.Tactic.Linarith
public import Mathlib.Tactic.Positivity
public import Mathlib.Tactic.NormNum
public import Mathlib.Tactic.Ring
public import Mathlib.Tactic.FinCases

/-! # Splitting a marked finite connected edge set into connected pieces

A finite edge set `E` (no loops) is *connected* when any two endpoints of its edges are
joined in `SimpleGraph.fromEdgeSet E`. A piece is a set of edges; its marked vertices are
the vertices of `A` that are endpoints of its edges.

`exists_connected_split`: if `E` is connected, every marked vertex is an endpoint of an
edge of `E`, `k ≥ 1` and `N = |A| ≥ 3^k`, then `E` is partitioned into at least
`3^(k-1) + 1` nonempty connected pieces, each with at least `3^(-k) N` and strictly fewer
than `3^(1-k) N` marked vertices, whose endpoints cover every endpoint of `E`.

**Generalisation, stated explicitly.** The issue asks for a finite tree. Acyclicity is not
used, so the statement is proved for every finite connected loopless edge set; the tree
case is `exists_connected_split_of_isTree`, for a tree on a finite vertex type.

The proof is the greedy bottom-up split: at a vertex `x` with an edge `s(x, c)`, the
edges other than `s(x, c)` split into those reachable from `c` and the rest, which are
reachable from `x`; each part is split recursively with one *open* piece of weight below
`w` touching the root, and open pieces are merged and closed once their weight reaches
`w = N / 3^k ≥ 1`.
-/

@[expose] public section
noncomputable section

open SimpleGraph Finset
open scoped Classical

namespace PercLib

variable {V : Type*}

/-! ### Reachability in the graph of an edge set -/

/-- Two endpoints of one edge of `F` are joined in the graph of `F`. -/
theorem reachable_fromEdgeSet_of_mem {F : Set (Sym2 V)} {e : Sym2 V} (he : e ∈ F)
    {u v : V} (hu : u ∈ e) (hv : v ∈ e) : (fromEdgeSet F).Reachable u v := by
  revert he hu hv
  refine Sym2.ind (fun p q => ?_) e
  intro he hu hv
  rw [Sym2.mem_iff] at hu hv
  by_cases hpq : p = q
  · subst hpq
    rcases hu with rfl | rfl <;> rcases hv with rfl | rfl <;> exact Reachable.rfl
  · have hadj : (fromEdgeSet F).Adj p q := (fromEdgeSet_adj _).2 ⟨he, hpq⟩
    rcases hu with rfl | rfl <;> rcases hv with rfl | rfl
    exacts [Reachable.rfl, hadj.reachable, hadj.symm.reachable, Reachable.rfl]

/-- After deleting the edge `s(x, c)`, what was reachable from a vertex reachable from `x`
or `c` is still reachable from `x` or from `c`. -/
theorem reachable_diff_or {E : Set (Sym2 V)} {x c u v : V}
    (h : (fromEdgeSet E).Reachable u v)
    (hu : (fromEdgeSet (E \ {s(x, c)})).Reachable x u ∨
      (fromEdgeSet (E \ {s(x, c)})).Reachable c u) :
    (fromEdgeSet (E \ {s(x, c)})).Reachable x v ∨
      (fromEdgeSet (E \ {s(x, c)})).Reachable c v := by
  obtain ⟨p⟩ := h
  induction p with
  | nil => exact hu
  | @cons a b d hadj p ih =>
    apply ih
    rw [fromEdgeSet_adj] at hadj
    by_cases he : s(a, b) = s(x, c)
    · have hb : b ∈ s(x, c) := he ▸ Sym2.mem_mk_right a b
      rcases Sym2.mem_iff.1 hb with rfl | rfl
      · exact Or.inl Reachable.rfl
      · exact Or.inr Reachable.rfl
    · have hadj' : (fromEdgeSet (E \ {s(x, c)})).Adj a b :=
        (fromEdgeSet_adj _).2 ⟨Set.mem_sdiff_of_mem hadj.1 he, hadj.2⟩
      rcases hu with hu | hu
      · exact Or.inl (hu.trans hadj'.reachable)
      · exact Or.inr (hu.trans hadj'.reachable)

/-- A walk from a vertex reachable from `a` stays inside any edge set `S` that contains
every edge of `F` with an endpoint reachable from `a`. -/
theorem reachable_of_closed {F S : Set (Sym2 V)} {a u v : V}
    (hS : ∀ e ∈ F, ∀ w ∈ e, (fromEdgeSet F).Reachable a w → e ∈ S)
    (hu : (fromEdgeSet F).Reachable a u) (hu' : (fromEdgeSet S).Reachable a u)
    (hv : (fromEdgeSet F).Reachable u v) : (fromEdgeSet S).Reachable a v := by
  obtain ⟨p⟩ := hv
  induction p with
  | nil => exact hu'
  | @cons b d t hadj p ih =>
    have h1 := (fromEdgeSet_adj _).1 hadj
    have hadj' : (fromEdgeSet S).Adj b d :=
      (fromEdgeSet_adj _).2 ⟨hS _ h1.1 b (Sym2.mem_mk_left b d) hu, h1.2⟩
    exact ih (hu.trans hadj.reachable) (hu'.trans hadj'.reachable)

/-- The edges of `F` with an endpoint reachable from `a` form a set in which every one of
their endpoints is reachable from `a`. -/
theorem reachable_filter_reachable (F : Finset (Sym2 V)) (a : V) {v : V}
    (hv : ∃ e ∈ F.filter (fun e => ∃ w ∈ e, (fromEdgeSet (F : Set (Sym2 V))).Reachable a w),
      v ∈ e) :
    (fromEdgeSet ((F.filter (fun e => ∃ w ∈ e,
      (fromEdgeSet (F : Set (Sym2 V))).Reachable a w) : Finset (Sym2 V)) :
        Set (Sym2 V))).Reachable a v := by
  obtain ⟨e, he, hve⟩ := hv
  obtain ⟨heF, w, hwe, haw⟩ := Finset.mem_filter.1 he
  have hav : (fromEdgeSet (F : Set (Sym2 V))).Reachable a v :=
    haw.trans (reachable_fromEdgeSet_of_mem (Finset.mem_coe.2 heF) hwe hve)
  refine reachable_of_closed (F := (F : Set (Sym2 V))) ?_ Reachable.rfl Reachable.rfl hav
  intro e' he' w' hw' haw'
  exact Finset.mem_coe.2 (Finset.mem_filter.2 ⟨Finset.mem_coe.1 he', w', hw', haw'⟩)

/-- A vertex joined to a different vertex is an endpoint of an edge. -/
theorem exists_mem_of_reachable_ne {S : Set (Sym2 V)} {a v : V}
    (h : (fromEdgeSet S).Reachable a v) (hne : a ≠ v) : ∃ e ∈ S, a ∈ e := by
  obtain ⟨p⟩ := h
  cases p with
  | nil => exact absurd rfl hne
  | cons h _ => exact ⟨_, ((fromEdgeSet_adj _).1 h).1, Sym2.mem_mk_left _ _⟩

/-- The union of two connected edge sets with a common endpoint is connected. -/
theorem connected_union {P Q : Finset (Sym2 V)}
    (hP : ∀ u v, (∃ e ∈ P, u ∈ e) → (∃ e ∈ P, v ∈ e) →
      (fromEdgeSet (P : Set (Sym2 V))).Reachable u v)
    (hQ : ∀ u v, (∃ e ∈ Q, u ∈ e) → (∃ e ∈ Q, v ∈ e) →
      (fromEdgeSet (Q : Set (Sym2 V))).Reachable u v)
    {z : V} (hzP : ∃ e ∈ P, z ∈ e) (hzQ : ∃ e ∈ Q, z ∈ e) :
    ∀ u v, (∃ e ∈ P ∪ Q, u ∈ e) → (∃ e ∈ P ∪ Q, v ∈ e) →
      (fromEdgeSet ((P ∪ Q : Finset (Sym2 V)) : Set (Sym2 V))).Reachable u v := by
  have hmP : fromEdgeSet (P : Set (Sym2 V)) ≤ fromEdgeSet ((P ∪ Q : Finset _) : Set _) :=
    fromEdgeSet_mono (by simp)
  have hmQ : fromEdgeSet (Q : Set (Sym2 V)) ≤ fromEdgeSet ((P ∪ Q : Finset _) : Set _) :=
    fromEdgeSet_mono (by simp)
  have hz : ∀ u, (∃ e ∈ P ∪ Q, u ∈ e) →
      (fromEdgeSet ((P ∪ Q : Finset (Sym2 V)) : Set (Sym2 V))).Reachable u z := by
    rintro u ⟨e, he, hue⟩
    rcases Finset.mem_union.1 he with he | he
    · exact (hP u z ⟨e, he, hue⟩ hzP).mono hmP
    · exact (hQ u z ⟨e, he, hue⟩ hzQ).mono hmQ
  intro u v hu hv
  exact (hz u hu).trans (hz v hv).symm

/-- If the edges of a connected `E` lie in `O` or in a piece of `C`, then a vertex of `O`
joined to a vertex of a piece produces a common vertex of `O` and some piece. -/
theorem exists_common_vertex {E O : Finset (Sym2 V)} {C : Finset (Finset (Sym2 V))}
    (hcov : ∀ e ∈ E, e ∈ O ∨ ∃ P ∈ C, e ∈ P) {u v : V}
    (h : (fromEdgeSet (E : Set (Sym2 V))).Reachable u v)
    (hu : ∃ e ∈ O, u ∈ e) (hv : ∃ P ∈ C, ∃ e ∈ P, v ∈ e) :
    ∃ z, (∃ e ∈ O, z ∈ e) ∧ ∃ P ∈ C, ∃ e ∈ P, z ∈ e := by
  obtain ⟨p⟩ := h
  induction p with
  | nil => exact ⟨_, hu, hv⟩
  | @cons a b d hadj p ih =>
    have h1 := (fromEdgeSet_adj _).1 hadj
    rcases hcov _ (Finset.mem_coe.1 h1.1) with hO | ⟨P, hP, heP⟩
    · exact ih ⟨_, hO, Sym2.mem_mk_right a b⟩ hv
    · exact ⟨a, hu, P, hP, _, heP, Sym2.mem_mk_left a b⟩

/-! ### Bookkeeping for partitions of an edge set -/

private theorem part_close {E U : Finset (Sym2 V)} {C : Finset (Finset (Sym2 V))}
    (h : (∀ P ∈ C, P ⊆ E) ∧ U ⊆ E ∧ (∀ e ∈ E, e ∈ U ∨ ∃ P ∈ C, e ∈ P) ∧
      (∀ P ∈ C, Disjoint P U) ∧ (C : Set (Finset (Sym2 V))).PairwiseDisjoint id) :
    (∀ P ∈ insert U C, P ⊆ E) ∧ (∅ : Finset (Sym2 V)) ⊆ E ∧
      (∀ e ∈ E, e ∈ (∅ : Finset (Sym2 V)) ∨ ∃ P ∈ insert U C, e ∈ P) ∧
      (∀ P ∈ insert U C, Disjoint P ∅) ∧
      ((insert U C : Finset (Finset (Sym2 V))) : Set (Finset (Sym2 V))).PairwiseDisjoint id := by
  obtain ⟨h1, h2, h3, h4, h5⟩ := h
  refine ⟨?_, Finset.empty_subset _, ?_, fun _ _ => Finset.disjoint_empty_right _, ?_⟩
  · intro P hP
    rcases Finset.mem_insert.1 hP with rfl | hP
    · exact h2
    · exact h1 P hP
  · intro e he
    rcases h3 e he with h | ⟨P, hP, heP⟩
    · exact Or.inr ⟨U, Finset.mem_insert_self _ _, h⟩
    · exact Or.inr ⟨P, Finset.mem_insert_of_mem hP, heP⟩
  · rw [Finset.coe_insert]
    exact h5.insert fun P hP _ => (h4 P hP).symm

private theorem part_union {E₁ E₂ O₁ O₂ : Finset (Sym2 V)} {C₁ C₂ : Finset (Finset (Sym2 V))}
    (hE : Disjoint E₁ E₂)
    (h₁ : (∀ P ∈ C₁, P ⊆ E₁) ∧ O₁ ⊆ E₁ ∧ (∀ e ∈ E₁, e ∈ O₁ ∨ ∃ P ∈ C₁, e ∈ P) ∧
      (∀ P ∈ C₁, Disjoint P O₁) ∧ (C₁ : Set (Finset (Sym2 V))).PairwiseDisjoint id)
    (h₂ : (∀ P ∈ C₂, P ⊆ E₂) ∧ O₂ ⊆ E₂ ∧ (∀ e ∈ E₂, e ∈ O₂ ∨ ∃ P ∈ C₂, e ∈ P) ∧
      (∀ P ∈ C₂, Disjoint P O₂) ∧ (C₂ : Set (Finset (Sym2 V))).PairwiseDisjoint id) :
    (∀ P ∈ C₁ ∪ C₂, P ⊆ E₁ ∪ E₂) ∧ O₁ ∪ O₂ ⊆ E₁ ∪ E₂ ∧
      (∀ e ∈ E₁ ∪ E₂, e ∈ O₁ ∪ O₂ ∨ ∃ P ∈ C₁ ∪ C₂, e ∈ P) ∧
      (∀ P ∈ C₁ ∪ C₂, Disjoint P (O₁ ∪ O₂)) ∧
      ((C₁ ∪ C₂ : Finset (Finset (Sym2 V))) : Set (Finset (Sym2 V))).PairwiseDisjoint id := by
  obtain ⟨a1, a2, a3, a4, a5⟩ := h₁
  obtain ⟨b1, b2, b3, b4, b5⟩ := h₂
  refine ⟨?_, Finset.union_subset_union a2 b2, ?_, ?_, ?_⟩
  · intro P hP
    rcases Finset.mem_union.1 hP with hP | hP
    · exact (a1 P hP).trans Finset.subset_union_left
    · exact (b1 P hP).trans Finset.subset_union_right
  · intro e he
    rcases Finset.mem_union.1 he with he | he
    · rcases a3 e he with h | ⟨P, hP, heP⟩
      · exact Or.inl (Finset.mem_union_left _ h)
      · exact Or.inr ⟨P, Finset.mem_union_left _ hP, heP⟩
    · rcases b3 e he with h | ⟨P, hP, heP⟩
      · exact Or.inl (Finset.mem_union_right _ h)
      · exact Or.inr ⟨P, Finset.mem_union_right _ hP, heP⟩
  · intro P hP
    rcases Finset.mem_union.1 hP with hP | hP
    · exact Finset.disjoint_union_right.2 ⟨a4 P hP,
        Finset.disjoint_of_subset_left (a1 P hP) (Finset.disjoint_of_subset_right b2 hE)⟩
    · exact Finset.disjoint_union_right.2 ⟨Finset.disjoint_of_subset_left (b1 P hP)
        (Finset.disjoint_of_subset_right a2 hE.symm), b4 P hP⟩
  · rw [Finset.coe_union]
    refine a5.union b5 fun P hP Q hQ _ => ?_
    exact Finset.disjoint_of_subset_left (a1 P hP) (Finset.disjoint_of_subset_right (b1 Q hQ) hE)

private theorem part_insert {E O : Finset (Sym2 V)} {C : Finset (Finset (Sym2 V))}
    {f : Sym2 V} (hf : f ∉ E)
    (h : (∀ P ∈ C, P ⊆ E) ∧ O ⊆ E ∧ (∀ e ∈ E, e ∈ O ∨ ∃ P ∈ C, e ∈ P) ∧
      (∀ P ∈ C, Disjoint P O) ∧ (C : Set (Finset (Sym2 V))).PairwiseDisjoint id) :
    (∀ P ∈ C, P ⊆ insert f E) ∧ insert f O ⊆ insert f E ∧
      (∀ e ∈ insert f E, e ∈ insert f O ∨ ∃ P ∈ C, e ∈ P) ∧
      (∀ P ∈ C, Disjoint P (insert f O)) ∧ (C : Set (Finset (Sym2 V))).PairwiseDisjoint id := by
  obtain ⟨h1, h2, h3, h4, h5⟩ := h
  refine ⟨fun P hP => (h1 P hP).trans (Finset.subset_insert _ _),
    Finset.insert_subset_insert _ h2, ?_, ?_, h5⟩
  · intro e he
    rcases Finset.mem_insert.1 he with rfl | he
    · exact Or.inl (Finset.mem_insert_self _ _)
    · rcases h3 e he with h | h
      · exact Or.inl (Finset.mem_insert_of_mem h)
      · exact Or.inr h
  · intro P hP
    refine Finset.disjoint_insert_right.2 ⟨fun hfP => hf (h1 P hP hfP), h4 P hP⟩

/-! ### The greedy split -/

/-- Close an open piece once its weight reaches `w`. -/
private theorem close_or_open (W : Finset (Sym2 V) → ℕ) (w : ℝ) {E U : Finset (Sym2 V)}
    {C : Finset (Finset (Sym2 V))} (x : V)
    (hC : ∀ P ∈ C, P.Nonempty ∧ (∀ u v, (∃ e ∈ P, u ∈ e) → (∃ e ∈ P, v ∈ e) →
        (fromEdgeSet (P : Set (Sym2 V))).Reachable u v) ∧
      w ≤ (W P : ℝ) ∧ ((W P : ℝ) < 2 * w ∨ W P ≤ 2))
    (hU : U = ∅ ∨ (U.Nonempty ∧ (∀ u v, (∃ e ∈ U, u ∈ e) → (∃ e ∈ U, v ∈ e) →
        (fromEdgeSet (U : Set (Sym2 V))).Reachable u v) ∧
      (∃ e ∈ U, x ∈ e) ∧ ((W U : ℝ) < 2 * w ∨ W U ≤ 2)))
    (hP : (∀ P ∈ C, P ⊆ E) ∧ U ⊆ E ∧ (∀ e ∈ E, e ∈ U ∨ ∃ P ∈ C, e ∈ P) ∧
      (∀ P ∈ C, Disjoint P U) ∧ (C : Set (Finset (Sym2 V))).PairwiseDisjoint id) :
    ∃ (C' : Finset (Finset (Sym2 V))) (O : Finset (Sym2 V)),
      (∀ P ∈ C', P.Nonempty ∧ (∀ u v, (∃ e ∈ P, u ∈ e) → (∃ e ∈ P, v ∈ e) →
          (fromEdgeSet (P : Set (Sym2 V))).Reachable u v) ∧
        w ≤ (W P : ℝ) ∧ ((W P : ℝ) < 2 * w ∨ W P ≤ 2)) ∧
      (O = ∅ ∨ ((∀ u v, (∃ e ∈ O, u ∈ e) → (∃ e ∈ O, v ∈ e) →
          (fromEdgeSet (O : Set (Sym2 V))).Reachable u v) ∧
        (∃ e ∈ O, x ∈ e) ∧ (W O : ℝ) < w)) ∧
      ((∀ P ∈ C', P ⊆ E) ∧ O ⊆ E ∧ (∀ e ∈ E, e ∈ O ∨ ∃ P ∈ C', e ∈ P) ∧
        (∀ P ∈ C', Disjoint P O) ∧ (C' : Set (Finset (Sym2 V))).PairwiseDisjoint id) := by
  rcases hU with rfl | ⟨hne, hcn, hx, hW⟩
  · exact ⟨C, ∅, hC, Or.inl rfl, hP⟩
  by_cases hlt : (W U : ℝ) < w
  · exact ⟨C, U, hC, Or.inr ⟨hcn, hx, hlt⟩, hP⟩
  · refine ⟨insert U C, ∅, ?_, Or.inl rfl, part_close hP⟩
    intro P hP'
    rcases Finset.mem_insert.1 hP' with rfl | hP'
    · exact ⟨hne, hcn, not_lt.1 hlt, hW⟩
    · exact hC P hP'

/-- The recursive step: a partition into closed pieces of weight in `[w, 2w)` (or at most
two) and one open piece of weight below `w` containing the root `x`. -/
private theorem greedy_split (W : Finset (Sym2 V) → ℕ)
    (hW1 : ∀ P Q, W (P ∪ Q) ≤ W P + W Q)
    (hW2 : ∀ (O : Finset (Sym2 V)) (x c : V), (∃ e ∈ O, c ∈ e) → W (insert s(x, c) O) ≤ W O + 1)
    (hW3 : ∀ x c : V, W {s(x, c)} ≤ 2)
    (w : ℝ) (hw : 1 ≤ w) (n : ℕ) :
    ∀ E : Finset (Sym2 V), E.card ≤ n → (∀ e ∈ E, ¬ e.IsDiag) →
      (∀ u v, (∃ e ∈ E, u ∈ e) → (∃ e ∈ E, v ∈ e) →
        (fromEdgeSet (E : Set (Sym2 V))).Reachable u v) →
      ∀ x, (∃ e ∈ E, x ∈ e) →
      ∃ (C : Finset (Finset (Sym2 V))) (O : Finset (Sym2 V)),
        (∀ P ∈ C, P.Nonempty ∧ (∀ u v, (∃ e ∈ P, u ∈ e) → (∃ e ∈ P, v ∈ e) →
            (fromEdgeSet (P : Set (Sym2 V))).Reachable u v) ∧
          w ≤ (W P : ℝ) ∧ ((W P : ℝ) < 2 * w ∨ W P ≤ 2)) ∧
        (O = ∅ ∨ ((∀ u v, (∃ e ∈ O, u ∈ e) → (∃ e ∈ O, v ∈ e) →
            (fromEdgeSet (O : Set (Sym2 V))).Reachable u v) ∧
          (∃ e ∈ O, x ∈ e) ∧ (W O : ℝ) < w)) ∧
        ((∀ P ∈ C, P ⊆ E) ∧ O ⊆ E ∧ (∀ e ∈ E, e ∈ O ∨ ∃ P ∈ C, e ∈ P) ∧
          (∀ P ∈ C, Disjoint P O) ∧ (C : Set (Finset (Sym2 V))).PairwiseDisjoint id) := by
  induction n with
  | zero =>
    intro E hE _ _ x hx
    obtain ⟨e, he, _⟩ := hx
    have : E = ∅ := Finset.card_eq_zero.1 (Nat.le_zero.1 hE)
    simp [this] at he
  | succ n ih =>
  intro E hE hdiag hconn x hx
  obtain ⟨e₀, he₀, hxe₀⟩ := hx
  obtain ⟨c, rfl⟩ := Sym2.mem_iff_exists.1 hxe₀
  have hxc : x ≠ c := fun h => hdiag _ he₀ (Sym2.mk_isDiag_iff.2 h)
  set f : Sym2 V := s(x, c) with hfdef
  set F := E.erase f with hFdef
  have hFcoe : ((F : Finset (Sym2 V)) : Set (Sym2 V)) = (E : Set (Sym2 V)) \ {f} :=
    Finset.coe_erase f E
  have hFcard : F.card ≤ n := by
    rw [hFdef, Finset.card_erase_of_mem he₀]; omega
  set Ec := F.filter (fun e => ∃ v ∈ e, (fromEdgeSet (F : Set (Sym2 V))).Reachable c v)
    with hEc
  set Ex := F.filter (fun e => ¬ ∃ v ∈ e, (fromEdgeSet (F : Set (Sym2 V))).Reachable c v)
    with hEx
  have hEcF : Ec ⊆ F := Finset.filter_subset _ _
  have hExF : Ex ⊆ F := Finset.filter_subset _ _
  have hFE : F ⊆ E := Finset.erase_subset _ _
  have hfF : f ∉ F := Finset.notMem_erase f E
  -- the dichotomy after deleting `f`
  have hdich : ∀ v, (∃ e ∈ E, v ∈ e) →
      (fromEdgeSet (F : Set (Sym2 V))).Reachable x v ∨
        (fromEdgeSet (F : Set (Sym2 V))).Reachable c v := by
    intro v hv
    rw [hFcoe]
    exact reachable_diff_or (hconn x v ⟨f, he₀, hxe₀⟩ hv) (Or.inl Reachable.rfl)
  -- the `c` side
  have hc_side : ∃ (C : Finset (Finset (Sym2 V))) (O : Finset (Sym2 V)),
      (∀ P ∈ C, P.Nonempty ∧ (∀ u v, (∃ e ∈ P, u ∈ e) → (∃ e ∈ P, v ∈ e) →
          (fromEdgeSet (P : Set (Sym2 V))).Reachable u v) ∧
        w ≤ (W P : ℝ) ∧ ((W P : ℝ) < 2 * w ∨ W P ≤ 2)) ∧
      (O = ∅ ∨ ((∀ u v, (∃ e ∈ O, u ∈ e) → (∃ e ∈ O, v ∈ e) →
          (fromEdgeSet (O : Set (Sym2 V))).Reachable u v) ∧
        (∃ e ∈ O, c ∈ e) ∧ (W O : ℝ) < w)) ∧
      ((∀ P ∈ C, P ⊆ Ec) ∧ O ⊆ Ec ∧ (∀ e ∈ Ec, e ∈ O ∨ ∃ P ∈ C, e ∈ P) ∧
        (∀ P ∈ C, Disjoint P O) ∧ (C : Set (Finset (Sym2 V))).PairwiseDisjoint id) := by
    rcases Finset.eq_empty_or_nonempty Ec with h | h
    · refine ⟨∅, ∅, by simp, Or.inl rfl, by simp, Finset.empty_subset _, ?_, by simp, by simp⟩
      intro e he; rw [h] at he; simp at he
    · have hreach := fun v (hv : ∃ e ∈ Ec, v ∈ e) => reachable_filter_reachable F c hv
      have hcmem : ∃ e ∈ Ec, c ∈ e := by
        obtain ⟨e, he⟩ := h
        by_cases hce : c = e.out.1
        · exact ⟨e, he, hce ▸ Sym2.out_fst_mem e⟩
        · exact exists_mem_of_reachable_ne (hreach _ ⟨e, he, Sym2.out_fst_mem e⟩) hce
      refine ih Ec ((Finset.card_le_card hEcF).trans hFcard)
        (fun e he => hdiag e (hFE (hEcF he))) ?_ c hcmem
      intro u v hu hv
      exact (hreach u hu).symm.trans (hreach v hv)
  -- the `x` side
  have hx_side : ∃ (C : Finset (Finset (Sym2 V))) (O : Finset (Sym2 V)),
      (∀ P ∈ C, P.Nonempty ∧ (∀ u v, (∃ e ∈ P, u ∈ e) → (∃ e ∈ P, v ∈ e) →
          (fromEdgeSet (P : Set (Sym2 V))).Reachable u v) ∧
        w ≤ (W P : ℝ) ∧ ((W P : ℝ) < 2 * w ∨ W P ≤ 2)) ∧
      (O = ∅ ∨ ((∀ u v, (∃ e ∈ O, u ∈ e) → (∃ e ∈ O, v ∈ e) →
          (fromEdgeSet (O : Set (Sym2 V))).Reachable u v) ∧
        (∃ e ∈ O, x ∈ e) ∧ (W O : ℝ) < w)) ∧
      ((∀ P ∈ C, P ⊆ Ex) ∧ O ⊆ Ex ∧ (∀ e ∈ Ex, e ∈ O ∨ ∃ P ∈ C, e ∈ P) ∧
        (∀ P ∈ C, Disjoint P O) ∧ (C : Set (Finset (Sym2 V))).PairwiseDisjoint id) := by
    rcases Finset.eq_empty_or_nonempty Ex with h | h
    · refine ⟨∅, ∅, by simp, Or.inl rfl, by simp, Finset.empty_subset _, ?_, by simp, by simp⟩
      intro e he; rw [h] at he; simp at he
    · obtain ⟨e₁, he₁⟩ := h
      obtain ⟨he₁F, hnc⟩ := Finset.mem_filter.1 he₁
      have hx1 := hdich _ ⟨e₁, hFE he₁F, Sym2.out_fst_mem e₁⟩
      have hxv₁ : (fromEdgeSet (F : Set (Sym2 V))).Reachable x e₁.out.1 :=
        hx1.resolve_right fun h => hnc ⟨_, Sym2.out_fst_mem e₁, h⟩
      have hncx : ¬ (fromEdgeSet (F : Set (Sym2 V))).Reachable c x :=
        fun h => hnc ⟨_, Sym2.out_fst_mem e₁, h.trans hxv₁⟩
      have hExeq : Ex = F.filter
          (fun e => ∃ v ∈ e, (fromEdgeSet (F : Set (Sym2 V))).Reachable x v) := by
        rw [hEx]
        refine Finset.filter_congr fun e heF => ⟨fun hn => ?_, fun ⟨v, hv, hxv⟩ => ?_⟩
        · refine ⟨e.out.1, Sym2.out_fst_mem e, ?_⟩
          exact (hdich _ ⟨e, hFE heF, Sym2.out_fst_mem e⟩).resolve_right
            fun h => hn ⟨_, Sym2.out_fst_mem e, h⟩
        · rintro ⟨u, hu, hcu⟩
          exact hncx (hcu.trans ((reachable_fromEdgeSet_of_mem
            (Finset.mem_coe.2 heF) hu hv).trans hxv.symm))
      have hreach : ∀ v, (∃ e ∈ Ex, v ∈ e) →
          (fromEdgeSet (Ex : Set (Sym2 V))).Reachable x v := by
        intro v hv
        rw [hExeq] at hv ⊢
        exact reachable_filter_reachable F x hv
      have hxmem : ∃ e ∈ Ex, x ∈ e := by
        by_cases hxe : x = e₁.out.1
        · exact ⟨e₁, he₁, hxe ▸ Sym2.out_fst_mem e₁⟩
        · exact exists_mem_of_reachable_ne (hreach _ ⟨e₁, he₁, Sym2.out_fst_mem e₁⟩) hxe
      refine ih Ex ((Finset.card_le_card hExF).trans hFcard)
        (fun e he => hdiag e (hFE (hExF he))) ?_ x hxmem
      intro u v hu hv
      exact (hreach u hu).symm.trans (hreach v hv)
  obtain ⟨C₁, O₁, hC₁, hO₁, hP₁⟩ := hc_side
  obtain ⟨C₂, O₂, hC₂, hO₂, hP₂⟩ := hx_side
  -- the piece `B = O₁ ∪ {f}`, open at `x`
  have hfEc : f ∉ Ec := fun h => hfF (hEcF h)
  have hcnf : ∀ u v, (∃ e ∈ ({f} : Finset (Sym2 V)), u ∈ e) →
      (∃ e ∈ ({f} : Finset (Sym2 V)), v ∈ e) →
      (fromEdgeSet (({f} : Finset (Sym2 V)) : Set (Sym2 V))).Reachable u v := by
    rintro u v ⟨e, he, hue⟩ ⟨e', he', hve⟩
    rw [Finset.mem_singleton] at he he'
    subst he he'
    exact reachable_fromEdgeSet_of_mem (by simp) hue hve
  have hB : insert f O₁ = ∅ ∨ ((insert f O₁).Nonempty ∧
      (∀ u v, (∃ e ∈ insert f O₁, u ∈ e) → (∃ e ∈ insert f O₁, v ∈ e) →
        (fromEdgeSet ((insert f O₁ : Finset (Sym2 V)) : Set (Sym2 V))).Reachable u v) ∧
      (∃ e ∈ insert f O₁, x ∈ e) ∧
      ((W (insert f O₁) : ℝ) < 2 * w ∨ W (insert f O₁) ≤ 2)) := by
    refine Or.inr ⟨Finset.insert_nonempty _ _, ?_, ⟨f, Finset.mem_insert_self _ _, hxe₀⟩, ?_⟩
    · rcases hO₁ with rfl | ⟨hcn, hc, _⟩
      · simpa using hcnf
      · rw [Finset.insert_eq]
        exact connected_union hcnf hcn ⟨f, Finset.mem_singleton_self _, Sym2.mem_mk_right x c⟩ hc
    · rcases hO₁ with rfl | ⟨_, hc, hlt⟩
      · right; simpa using hW3 x c
      · left
        have h := hW2 O₁ x c hc
        have h' : (W (insert f O₁) : ℝ) ≤ W O₁ + 1 := by exact_mod_cast h
        linarith
  obtain ⟨C₁', Ob, hC₁', hOb, hP₁'⟩ :=
    close_or_open W w x hC₁ hB (part_insert hfEc hP₁)
  have hdisj : Disjoint (insert f Ec) Ex := by
    rw [Finset.disjoint_insert_left]
    exact ⟨fun h => hfF (hExF h), Finset.disjoint_filter_filter_not _ _ _⟩
  have hPU := part_union hdisj hP₁' hP₂
  have hEeq : insert f Ec ∪ Ex = E := by
    rw [Finset.insert_union, hEc, hEx, Finset.filter_union_filter_not_eq, hFdef,
      Finset.insert_erase he₀]
  rw [hEeq] at hPU
  have hU : Ob ∪ O₂ = ∅ ∨ ((Ob ∪ O₂).Nonempty ∧
      (∀ u v, (∃ e ∈ Ob ∪ O₂, u ∈ e) → (∃ e ∈ Ob ∪ O₂, v ∈ e) →
        (fromEdgeSet ((Ob ∪ O₂ : Finset (Sym2 V)) : Set (Sym2 V))).Reachable u v) ∧
      (∃ e ∈ Ob ∪ O₂, x ∈ e) ∧
      ((W (Ob ∪ O₂) : ℝ) < 2 * w ∨ W (Ob ∪ O₂) ≤ 2)) := by
    rcases hOb with rfl | ⟨hcnb, hxb, hWb⟩
    · rcases hO₂ with rfl | ⟨hcn2, hx2, hW2'⟩
      · left; simp
      · right
        rw [Finset.empty_union]
        have ⟨e, he, _⟩ := hx2
        exact ⟨⟨e, he⟩, hcn2, hx2, Or.inl (by linarith)⟩
    · rcases hO₂ with rfl | ⟨hcn2, hx2, hW2'⟩
      · right
        rw [Finset.union_empty]
        have ⟨e, he, _⟩ := hxb
        exact ⟨⟨e, he⟩, hcnb, hxb, Or.inl (by linarith)⟩
      · right
        obtain ⟨e, he, hxe⟩ := hxb
        refine ⟨⟨e, Finset.mem_union_left _ he⟩, connected_union hcnb hcn2 ⟨e, he, hxe⟩ hx2,
          ⟨e, Finset.mem_union_left _ he, hxe⟩, Or.inl ?_⟩
        have h := hW1 Ob O₂
        have h' : (W (Ob ∪ O₂) : ℝ) ≤ W Ob + W O₂ := by exact_mod_cast h
        linarith
  have hCU : ∀ P ∈ C₁' ∪ C₂, P.Nonempty ∧ (∀ u v, (∃ e ∈ P, u ∈ e) → (∃ e ∈ P, v ∈ e) →
        (fromEdgeSet (P : Set (Sym2 V))).Reachable u v) ∧
      w ≤ (W P : ℝ) ∧ ((W P : ℝ) < 2 * w ∨ W P ≤ 2) := by
    intro P hP
    rcases Finset.mem_union.1 hP with hP | hP
    · exact hC₁' P hP
    · exact hC₂ P hP
  exact close_or_open W w x hCU hU hPU

/-! ### The splitting theorem -/

/-- **Splitting a marked connected edge set** (Q-66, input to the BK step of T-6). Let `E`
be a finite loopless edge set whose graph is connected on the endpoints of `E` (a finite
tree is a special case), `A` a set of `N = |A|` marked endpoints, `k ≥ 1` and
`N ≥ 3^k`. Then `E` is partitioned into `m ≥ 3^(k-1) + 1` nonempty connected pieces,
each with at least `N / 3^k` and fewer than `3 N / 3^k` marked vertices among the
endpoints of its edges, and the pieces' endpoints cover every endpoint of `E`. -/
theorem exists_connected_split (E : Finset (Sym2 V)) (hdiag : ∀ e ∈ E, ¬ e.IsDiag)
    (hconn : ∀ u v, (∃ e ∈ E, u ∈ e) → (∃ e ∈ E, v ∈ e) →
      (fromEdgeSet (E : Set (Sym2 V))).Reachable u v)
    (A : Finset V) (hA : ∀ a ∈ A, ∃ e ∈ E, a ∈ e) (k : ℕ) (hk : 1 ≤ k)
    (hN : 3 ^ k ≤ A.card) :
    ∃ C : Finset (Finset (Sym2 V)),
      3 ^ (k - 1) + 1 ≤ C.card ∧
      (∀ P ∈ C, P ⊆ E) ∧ (∀ e ∈ E, ∃ P ∈ C, e ∈ P) ∧
      (C : Set (Finset (Sym2 V))).PairwiseDisjoint id ∧
      (∀ P ∈ C, P.Nonempty ∧
        (∀ u v, (∃ e ∈ P, u ∈ e) → (∃ e ∈ P, v ∈ e) →
          (fromEdgeSet (P : Set (Sym2 V))).Reachable u v) ∧
        (A.card : ℝ) / 3 ^ k ≤ ((A.filter fun a => ∃ e ∈ P, a ∈ e).card : ℝ) ∧
        ((A.filter fun a => ∃ e ∈ P, a ∈ e).card : ℝ) < 3 * (A.card : ℝ) / 3 ^ k) ∧
      (∀ v, (∃ e ∈ E, v ∈ e) → ∃ P ∈ C, ∃ e ∈ P, v ∈ e) := by
  obtain ⟨W, hWdef⟩ : ∃ W : Finset (Sym2 V) → ℕ,
      ∀ P, W P = (A.filter fun a => ∃ e ∈ P, a ∈ e).card := ⟨_, fun _ => rfl⟩
  have hW1 : ∀ P Q, W (P ∪ Q) ≤ W P + W Q := by
    intro P Q
    rw [hWdef, hWdef, hWdef]
    refine (Finset.card_le_card ?_).trans (Finset.card_union_le _ _)
    intro a ha
    obtain ⟨haA, e, he, hae⟩ := Finset.mem_filter.1 ha
    rcases Finset.mem_union.1 he with he | he
    · exact Finset.mem_union_left _ (Finset.mem_filter.2 ⟨haA, e, he, hae⟩)
    · exact Finset.mem_union_right _ (Finset.mem_filter.2 ⟨haA, e, he, hae⟩)
  have hW2 : ∀ (O : Finset (Sym2 V)) (x c : V), (∃ e ∈ O, c ∈ e) →
      W (insert s(x, c) O) ≤ W O + 1 := by
    intro O x c hc
    rw [hWdef, hWdef]
    refine (Finset.card_le_card (t := insert x (A.filter fun a => ∃ e ∈ O, a ∈ e))
      ?_).trans (Finset.card_insert_le _ _)
    intro a ha
    obtain ⟨haA, e, he, hae⟩ := Finset.mem_filter.1 ha
    rcases Finset.mem_insert.1 he with rfl | he
    · rcases Sym2.mem_iff.1 hae with rfl | rfl
      · exact Finset.mem_insert_self _ _
      · exact Finset.mem_insert_of_mem (Finset.mem_filter.2 ⟨haA, hc⟩)
    · exact Finset.mem_insert_of_mem (Finset.mem_filter.2 ⟨haA, e, he, hae⟩)
  have hW3 : ∀ x c : V, W {s(x, c)} ≤ 2 := by
    intro x c
    rw [hWdef]
    refine (Finset.card_le_card (t := {x, c}) ?_).trans Finset.card_le_two
    intro a ha
    obtain ⟨_, e, he, hae⟩ := Finset.mem_filter.1 ha
    rw [Finset.mem_singleton] at he
    subst he
    rcases Sym2.mem_iff.1 hae with rfl | rfl <;> simp
  have hWmono : ∀ P Q : Finset (Sym2 V), P ⊆ Q → W P ≤ W Q := by
    intro P Q hPQ
    rw [hWdef, hWdef]
    exact Finset.card_le_card fun a ha => by
      obtain ⟨haA, e, he, hae⟩ := Finset.mem_filter.1 ha
      exact Finset.mem_filter.2 ⟨haA, e, hPQ he, hae⟩
  -- the scale `w = N / 3^k ≥ 1`
  set N := A.card with hNdef
  have h3k : (0 : ℝ) < 3 ^ k := by positivity
  set w : ℝ := (N : ℝ) / 3 ^ k with hwdef
  have hw : 1 ≤ w := by
    rw [hwdef, le_div_iff₀ h3k, one_mul]; exact_mod_cast hN
  have hNpos : 0 < N := lt_of_lt_of_le (by positivity) hN
  obtain ⟨a₀, ha₀⟩ := Finset.card_pos.1 hNpos
  obtain ⟨e₀, he₀, hae₀⟩ := hA a₀ ha₀
  obtain ⟨C, O, hC, hO, h1, h2, h3, h4, h5⟩ :=
    greedy_split W hW1 hW2 hW3 w hw E.card E le_rfl hdiag hconn a₀ ⟨e₀, he₀, hae₀⟩
  -- the weight of the whole edge set is `N`
  have hWE : ∀ Q : Finset (Sym2 V), E ⊆ Q → N ≤ W Q := by
    intro Q hEQ
    rw [hWdef, hNdef]
    refine Finset.card_le_card fun a ha => ?_
    obtain ⟨e, he, hae⟩ := hA a ha
    exact Finset.mem_filter.2 ⟨ha, e, hEQ he, hae⟩
  -- merge the open piece into a closed piece it touches
  have hfinal : ∃ D : Finset (Finset (Sym2 V)),
      (∀ P ∈ D, P ⊆ E) ∧ (∀ e ∈ E, ∃ P ∈ D, e ∈ P) ∧
      (D : Set (Finset (Sym2 V))).PairwiseDisjoint id ∧
      (∀ P ∈ D, P.Nonempty ∧
        (∀ u v, (∃ e ∈ P, u ∈ e) → (∃ e ∈ P, v ∈ e) →
          (fromEdgeSet (P : Set (Sym2 V))).Reachable u v) ∧
        w ≤ (W P : ℝ) ∧ (W P : ℝ) < 3 * w) := by
    have hgood : ∀ P ∈ C, (W P : ℝ) < 3 * w := by
      intro P hP
      rcases (hC P hP).2.2.2 with h | h
      · linarith
      · have : (W P : ℝ) ≤ 2 := by exact_mod_cast h
        linarith
    rcases hO with rfl | ⟨hcnO, hxO, hWO⟩
    · refine ⟨C, h1, fun e he => ?_, h5, fun P hP => ⟨(hC P hP).1, (hC P hP).2.1,
        (hC P hP).2.2.1, hgood P hP⟩⟩
      rcases h3 e he with h | h
      · simp at h
      · exact h
    -- the pieces are not all open
    obtain ⟨P₀, hP₀⟩ : C.Nonempty := by
      rw [Finset.nonempty_iff_ne_empty]
      intro hCe
      have hEO : E ⊆ O := fun e he => by
        rcases h3 e he with h | ⟨P, hP, _⟩
        · exact h
        · simp [hCe] at hP
      have := hWE O hEO
      have : (N : ℝ) ≤ W O := by exact_mod_cast this
      have hwN : w ≤ N := by
        rw [hwdef, div_le_iff₀ h3k]
        have : (1 : ℝ) ≤ 3 ^ k := one_le_pow₀ (by norm_num)
        have : (0 : ℝ) ≤ N := Nat.cast_nonneg _
        nlinarith
      linarith
    obtain ⟨eO, heO, haO⟩ := hxO
    obtain ⟨e₁, he₁⟩ := (hC P₀ hP₀).1
    obtain ⟨z, hzO, P, hP, hzP⟩ := exists_common_vertex h3
      (hconn a₀ e₁.out.1 ⟨eO, h2 heO, haO⟩ ⟨e₁, h1 P₀ hP₀ he₁, Sym2.out_fst_mem e₁⟩)
      ⟨eO, heO, haO⟩ ⟨P₀, hP₀, e₁, he₁, Sym2.out_fst_mem e₁⟩
    refine ⟨insert (P ∪ O) (C.erase P), ?_, ?_, ?_, ?_⟩
    · intro Q hQ
      rcases Finset.mem_insert.1 hQ with rfl | hQ
      · exact Finset.union_subset (h1 P hP) h2
      · exact h1 Q (Finset.mem_of_mem_erase hQ)
    · intro e he
      rcases h3 e he with h | ⟨Q, hQ, heQ⟩
      · exact ⟨P ∪ O, Finset.mem_insert_self _ _, Finset.mem_union_right _ h⟩
      · by_cases hQP : Q = P
        · subst hQP
          exact ⟨Q ∪ O, Finset.mem_insert_self _ _, Finset.mem_union_left _ heQ⟩
        · exact ⟨Q, Finset.mem_insert_of_mem (Finset.mem_erase.2 ⟨hQP, hQ⟩), heQ⟩
    · rw [Finset.coe_insert]
      refine (h5.subset (by simp)).insert fun Q hQ hne => ?_
      have hQ' := Finset.mem_erase.1 (Finset.mem_coe.1 hQ)
      refine Finset.disjoint_union_left.2 ⟨?_, (h4 Q hQ'.2).symm⟩
      exact h5 hP hQ'.2 (Ne.symm hQ'.1)
    · intro Q hQ
      rcases Finset.mem_insert.1 hQ with rfl | hQ
      · obtain ⟨hne, hcn, hlo, hhi⟩ := hC P hP
        refine ⟨Finset.Nonempty.mono Finset.subset_union_left hne,
          connected_union hcn hcnO hzP hzO, ?_, ?_⟩
        · have := hWmono P (P ∪ O) Finset.subset_union_left
          have : (W P : ℝ) ≤ W (P ∪ O) := by exact_mod_cast this
          linarith
        · have h := hW1 P O
          have h' : (W (P ∪ O) : ℝ) ≤ W P + W O := by exact_mod_cast h
          rcases hhi with hhi | hhi
          · linarith
          · have : (W P : ℝ) ≤ 2 := by exact_mod_cast hhi
            linarith
      · have hQ' := Finset.mem_of_mem_erase hQ
        exact ⟨(hC Q hQ').1, (hC Q hQ').2.1, (hC Q hQ').2.2.1, hgood Q hQ'⟩
  obtain ⟨D, hD1, hD2, hD3, hD4⟩ := hfinal
  -- count the pieces
  have hDne : D.Nonempty := by
    obtain ⟨P, hP, _⟩ := hD2 e₀ he₀
    exact ⟨P, hP⟩
  have hsum : (N : ℝ) < D.card * (3 * w) := by
    have hNle : N ≤ ∑ P ∈ D, W P := by
      rw [hNdef]
      refine (Finset.card_le_card (t := D.biUnion fun P =>
        A.filter fun a => ∃ e ∈ P, a ∈ e) ?_).trans Finset.card_biUnion_le |>.trans
        (le_of_eq (Finset.sum_congr rfl fun P _ => (hWdef P).symm))
      intro a ha
      obtain ⟨e, he, hae⟩ := hA a ha
      obtain ⟨P, hP, heP⟩ := hD2 e he
      exact Finset.mem_biUnion.2 ⟨P, hP, Finset.mem_filter.2 ⟨ha, e, heP, hae⟩⟩
    have hNle' : (N : ℝ) ≤ ∑ P ∈ D, (W P : ℝ) := by exact_mod_cast hNle
    have hlt : ∑ P ∈ D, (W P : ℝ) < ∑ _P ∈ D, 3 * w :=
      Finset.sum_lt_sum_of_nonempty hDne fun P hP => (hD4 P hP).2.2.2
    rw [Finset.sum_const, nsmul_eq_mul] at hlt
    linarith
  have hcard : 3 ^ (k - 1) + 1 ≤ D.card := by
    have h1 : (N : ℝ) < D.card * (3 * N / 3 ^ k) := by
      rw [hwdef] at hsum; convert hsum using 2; ring
    have hNpos' : (0 : ℝ) < N := by exact_mod_cast hNpos
    have h2 : (3 : ℝ) ^ k < 3 * D.card := by
      rw [mul_div_assoc', lt_div_iff₀ h3k] at h1
      nlinarith
    have h3 : 3 ^ k < 3 * D.card := by exact_mod_cast h2
    have h4 : 3 ^ k = 3 * 3 ^ (k - 1) := by
      rw [← pow_succ']; congr 1; omega
    omega
  refine ⟨D, hcard, hD1, hD2, hD3, fun P hP => ?_, ?_⟩
  · obtain ⟨hne, hcn, hlo, hhi⟩ := hD4 P hP
    refine ⟨hne, hcn, ?_, ?_⟩
    · rw [← hWdef]; exact hlo
    · rw [← hWdef]; convert hhi using 1; rw [hwdef]; ring
  · rintro v ⟨e, he, hve⟩
    obtain ⟨P, hP, heP⟩ := hD2 e he
    exact ⟨P, hP, e, heP, hve⟩

/-- **The tree case.** A finite tree with `N ≥ 3^k` marked vertices, `k ≥ 1`: its edge set
is partitioned into at least `3^(k-1) + 1` nonempty connected pieces, each with at least
`N / 3^k` and fewer than `3 N / 3^k` marked endpoints, covering every vertex. -/
theorem exists_connected_split_of_isTree [Fintype V] {T : SimpleGraph V}
    (hT : T.IsTree) (A : Finset V) (k : ℕ) (hk : 1 ≤ k) (hN : 3 ^ k ≤ A.card) :
    ∃ C : Finset (Finset (Sym2 V)),
      3 ^ (k - 1) + 1 ≤ C.card ∧
      (∀ P ∈ C, (P : Set (Sym2 V)) ⊆ T.edgeSet) ∧ (∀ e ∈ T.edgeSet, ∃ P ∈ C, e ∈ P) ∧
      (C : Set (Finset (Sym2 V))).PairwiseDisjoint id ∧
      (∀ P ∈ C, P.Nonempty ∧
        (∀ u v, (∃ e ∈ P, u ∈ e) → (∃ e ∈ P, v ∈ e) →
          (fromEdgeSet (P : Set (Sym2 V))).Reachable u v) ∧
        (A.card : ℝ) / 3 ^ k ≤ ((A.filter fun a => ∃ e ∈ P, a ∈ e).card : ℝ) ∧
        ((A.filter fun a => ∃ e ∈ P, a ∈ e).card : ℝ) < 3 * (A.card : ℝ) / 3 ^ k) ∧
      (∀ v, ∃ P ∈ C, ∃ e ∈ P, v ∈ e) := by
  set E : Finset (Sym2 V) := T.edgeSet.toFinset with hE
  have hEcoe : (E : Set (Sym2 V)) = T.edgeSet := by rw [hE, Set.coe_toFinset]
  -- every vertex is an endpoint of an edge, since there are at least two vertices
  have h2 : 1 < Fintype.card V := by
    have : 3 ≤ A.card := le_trans (by
      calc 3 = 3 ^ 1 := by norm_num
        _ ≤ 3 ^ k := Nat.pow_le_pow_right (by norm_num) hk) hN
    exact lt_of_lt_of_le (by omega) (this.trans (Finset.card_le_univ A))
  have hvert : ∀ v, ∃ e ∈ E, v ∈ e := by
    intro v
    obtain ⟨u, hu⟩ := Fintype.exists_ne_of_one_lt_card h2 v
    obtain ⟨p⟩ := hT.connected.preconnected v u
    cases p with
    | nil => exact absurd rfl hu
    | cons h _ => exact ⟨_, by rw [hE, Set.mem_toFinset]; exact h, Sym2.mem_mk_left _ _⟩
  obtain ⟨C, h1, h2, h3, h4, h5, _⟩ := exists_connected_split E
    (fun e he => T.not_isDiag_of_mem_edgeSet (by rwa [hE, Set.mem_toFinset] at he))
    (fun u v _ _ => by rw [hEcoe, fromEdgeSet_edgeSet]; exact hT.connected.preconnected u v)
    A (fun a _ => hvert a) k hk hN
  refine ⟨C, h1, fun P hP => ?_, fun e he => h3 e (by rwa [hE, Set.mem_toFinset]), h4, h5,
    fun v => ?_⟩
  · rw [← hEcoe]; exact_mod_cast h2 P hP
  · obtain ⟨e, he, hve⟩ := hvert v
    obtain ⟨P, hP, heP⟩ := h3 e he
    exact ⟨P, hP, e, heP, hve⟩

/-! ### Non-vacuity (D-5): a path on three vertices, all marked, `k = 1` -/

/-- The path `0 - 1 - 2` on `Fin 3` with every vertex marked satisfies the hypotheses with
`k = 1`, `N = 3`, and the conclusion provides at least two pieces. -/
example : ∃ C : Finset (Finset (Sym2 (Fin 3))), 2 ≤ C.card ∧
    ∀ P ∈ C, P.Nonempty ∧ P ⊆ {s(0, 1), s(1, 2)} := by
  have hconn : ∀ u v : Fin 3, (∃ e ∈ ({s(0, 1), s(1, 2)} : Finset (Sym2 (Fin 3))), u ∈ e) →
      (∃ e ∈ ({s(0, 1), s(1, 2)} : Finset (Sym2 (Fin 3))), v ∈ e) →
      (fromEdgeSet (({s(0, 1), s(1, 2)} : Finset (Sym2 (Fin 3))) : Set (Sym2 (Fin 3)))).Reachable
        u v := by
    have h01 : (fromEdgeSet (({s(0, 1), s(1, 2)} : Finset (Sym2 (Fin 3))) :
        Set (Sym2 (Fin 3)))).Adj 0 1 := (fromEdgeSet_adj _).2 ⟨by simp, by decide⟩
    have h12 : (fromEdgeSet (({s(0, 1), s(1, 2)} : Finset (Sym2 (Fin 3))) :
        Set (Sym2 (Fin 3)))).Adj 1 2 := (fromEdgeSet_adj _).2 ⟨by simp, by decide⟩
    have hall : ∀ u : Fin 3, (fromEdgeSet (({s(0, 1), s(1, 2)} : Finset (Sym2 (Fin 3))) :
        Set (Sym2 (Fin 3)))).Reachable 0 u := by
      intro u
      fin_cases u
      · exact Reachable.rfl
      · exact h01.reachable
      · exact h01.reachable.trans h12.reachable
    intro u v _ _
    exact (hall u).symm.trans (hall v)
  have hdiag : ∀ e ∈ ({s(0, 1), s(1, 2)} : Finset (Sym2 (Fin 3))), ¬ e.IsDiag := by
    intro e he
    simp only [Finset.mem_insert, Finset.mem_singleton] at he
    rcases he with rfl | rfl <;> simp
  have hA : ∀ a ∈ (Finset.univ : Finset (Fin 3)),
      ∃ e ∈ ({s(0, 1), s(1, 2)} : Finset (Sym2 (Fin 3))), a ∈ e := by
    intro a _
    fin_cases a
    · exact ⟨s(0, 1), by simp, Sym2.mem_mk_left _ _⟩
    · exact ⟨s(0, 1), by simp, Sym2.mem_mk_right _ _⟩
    · exact ⟨s(1, 2), by simp, Sym2.mem_mk_right _ _⟩
  obtain ⟨C, hC, hsub, _, _, hP, _⟩ := exists_connected_split {s(0, 1), s(1, 2)}
    hdiag hconn Finset.univ hA 1 le_rfl (by simp)
  exact ⟨C, by simpa using hC, fun P hP' => ⟨(hP P hP').1, hsub P hP'⟩⟩

end PercLib
