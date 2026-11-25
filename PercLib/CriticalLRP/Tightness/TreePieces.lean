/-
Migration source: https://github.com/yujinhkim/Critical-Long-range-percolation
Integration revision: 3b3d1d0e43ef940bfaa2292ee5c2ee094ac4edbf
Licence: Apache-2.0 for the PercLib Lean sources and tooling; see third_party/critical-lrp/.
External provenance and modifications are recorded in the file-specific notices below.
-/

/-
# Tree partition lemma: the combinatorial core of Hutchcroft's Theorem I.2.3

Reference: T. Hutchcroft, *Critical long-range percolation I: High effective dimension*,
arXiv:2508.18807v1, Theorem I.2.3, whose proof (following T. Hutchcroft, *Power-law bounds for
critical long-range percolation below the upper-critical dimension*, arXiv:2008.11197,
Section 2.1) rests on

* a combinatorial lemma decomposing a tree into edge-disjoint connected pieces, each containing
  a prescribed number of marked vertices, and
* the BK inequality applied to the disjoint witnesses supplied by those pieces.

This file formalises the combinatorial part for a finite rooted tree presented by a parent map
`pp`, in the "absolute threshold" form needed for the BK step: from `3^k * lam` marked vertices we
produce `3^(k-1)+1` pairwise edge-disjoint rooted pieces, each containing between `lam` and
`2*lam-1` marked vertices, and the leftover outside the pieces contains fewer than `lam`.  The
counting exponent `3^(k-1)+1` is exactly the one used for (2.8)/(2.9) of the source.

The root is fixed and is the unique periodic point. This avoids the unsatisfiable stronger
assumption that a self-map of a nonempty finite type has no nontrivial periodic point.

Structure of the proof:
`exists_piece` extracts one piece from a `pp`-closed region `S` (a region closed under parents,
which is what remains of the tree after earlier pieces have been removed);
`piecesOf` iterates the extraction, removing each piece's edges, and records the invariants
needed to count the pieces and to see that they are edge-disjoint.

No analysis, probability or percolation is used: this is pure finite combinatorics.
-/
module

public import Mathlib

set_option linter.unusedSectionVars false
set_option linter.unusedSimpArgs false
set_option linter.unnecessarySimpa false
set_option linter.unusedTactic false
set_option linter.unusedVariables false

set_option autoImplicit true

@[expose] public section

namespace Hutchcroft

open Finset

variable {V : Type*} [Fintype V] [DecidableEq V]

/-! ### Descendants and children of a parent map -/

/-- `desc pp v` is the set of vertices whose `pp`-orbit hits `v`, i.e. the descendants of `v`. -/
noncomputable def desc (pp : V → V) (v : V) : Finset V := by
  classical
  exact univ.filter (fun x => ∃ n : ℕ, pp^[n] x = v)

/-- The `pp`-children of `v`: all vertices `c ≠ v` with `pp c = v`. -/
noncomputable def kids (pp : V → V) (v : V) : Finset V := by
  classical
  exact univ.filter (fun c => pp c = v ∧ c ≠ v)

section Basic

variable {pp : V → V}

lemma mem_desc {v x : V} : x ∈ desc pp v ↔ ∃ n : ℕ, pp^[n] x = v := by
  classical simp [desc]

lemma mem_kids {v c : V} : c ∈ kids pp v ↔ pp c = v ∧ c ≠ v := by
  classical simp [kids]

lemma self_mem_desc (v : V) : v ∈ desc pp v := by
  rw [mem_desc]; exact ⟨0, rfl⟩

lemma desc_mono {v c : V} (h : pp c = v) : desc pp c ⊆ desc pp v := by
  intro x hx
  rw [mem_desc] at hx ⊢
  obtain ⟨n, hn⟩ := hx
  exact ⟨n + 1, by rw [Function.iterate_succ_apply', hn, h]⟩

lemma mem_desc_trans {v y x : V} (hy : y ∈ desc pp v) (hx : x ∈ desc pp y) :
    x ∈ desc pp v := by
  rw [mem_desc] at hy hx ⊢
  obtain ⟨n, hn⟩ := hy
  obtain ⟨m, hm⟩ := hx
  exact ⟨m + n, by rw [Nat.add_comm m n, Function.iterate_add_apply, hm, hn]⟩

lemma desc_mono_mem {c y : V} (h : y ∈ desc pp c) : desc pp y ⊆ desc pp c :=
  fun _ hx => mem_desc_trans h hx

/-- A member of `desc x` other than `x` has its parent in `desc x`. -/
lemma pp_mem_desc_of_mem_desc {c x : V} (hx : x ∈ desc pp c) (hne : x ≠ c) :
    pp x ∈ desc pp c := by
  rw [mem_desc] at hx ⊢
  obtain ⟨n, hn⟩ := hx
  cases n with
  | zero =>
      simp only [Function.iterate_zero_apply] at hn
      exact absurd hn hne
  | succ m =>
      exact ⟨m, by rw [Function.iterate_succ_apply] at hn; exact hn⟩

/-- A vertex of `desc v` other than `v` lies in `desc c` for a child `c` of `v`. -/
lemma exists_kid_of_mem_desc {v x : V} (hx : x ∈ desc pp v) (hne : x ≠ v) :
    ∃ c ∈ kids pp v, x ∈ desc pp c := by
  classical
  rw [mem_desc] at hx
  obtain ⟨N, hN⟩ := hx
  have hex : ∃ n : ℕ, pp^[n] x = v := ⟨N, hN⟩
  set n := Nat.find hex with hn_def
  have hspec : pp^[n] x = v := Nat.find_spec hex
  have hmin : ∀ k : ℕ, pp^[k] x = v → n ≤ k := fun k hk => Nat.find_min' hex hk
  have hpos : 1 ≤ n := by
    rcases Nat.eq_zero_or_pos n with h | h
    · exfalso
      rw [h] at hspec
      simp only [Function.iterate_zero_apply] at hspec
      exact hne hspec
    · exact h
  refine ⟨pp^[n - 1] x, ?_, ?_⟩
  · rw [mem_kids]
    refine ⟨?_, ?_⟩
    · have h2 : pp^[n - 1 + 1] x = v := by
        rw [Nat.sub_add_cancel hpos]; exact hspec
      rw [Function.iterate_succ_apply'] at h2
      exact h2
    · intro heq
      have := hmin (n - 1) heq
      omega
  · rw [mem_desc]
    exact ⟨n - 1, rfl⟩

end Basic

/-! ### Rooted forests and their unique periodic point -/

section RootedForest

variable {pp : V → V} {r : V}

/-- `IsRootedForest pp r`: `r` is a fixed point of the parent map `pp` and every vertex has `r` as
an ancestor.  This is the correct (satisfiable) replacement for the cycle-freeness hypothesis of
`Tightness/TreePieces.lean`. -/
def IsRootedForest (pp : V → V) (r : V) : Prop :=
  pp r = r ∧ ∀ x : V, ∃ n : ℕ, pp^[n] x = r

/-- The root is fixed by every iterate. -/
lemma isRootedForest_fix (h : IsRootedForest pp r) (k : ℕ) : pp^[k] r = r := by
  obtain ⟨hfix, -⟩ := h
  induction k with
  | zero => rfl
  | succ j ih => rw [Function.iterate_succ_apply', ih, hfix]

/-- **The only periodic point of a rooted forest is the root.** -/
lemma isRootedForest_periodic (h : IsRootedForest pp r) {n : ℕ} (hn : 1 ≤ n) {x : V}
    (hx : pp^[n] x = x) : x = r := by
  classical
  obtain ⟨hfix, hroot⟩ := h
  have hfixn : ∀ k : ℕ, pp^[k] r = r := fun k => isRootedForest_fix ⟨hfix, hroot⟩ k
  have hstep : ∀ q : ℕ, pp^[n * q] x = x := by
    intro q
    induction q with
    | zero => simp
    | succ j ih =>
        have h1 : n * (j + 1) = n * j + n := by ring
        rw [h1, Function.iterate_add_apply, hx, ih]
  obtain ⟨m, hm⟩ := hroot x
  have hle : m ≤ n * m := Nat.le_mul_of_pos_left m hn
  calc x = pp^[n * m] x := (hstep m).symm
    _ = pp^[n * m - m] (pp^[m] x) := by
          rw [← Function.iterate_add_apply, Nat.sub_add_cancel hle]
    _ = pp^[n * m - m] r := by rw [hm]
    _ = r := hfixn _

/-- A child's parent is not a descendant of that child (the tree-order property that replaces
cycle-freeness in the extraction argument). -/
lemma parent_not_mem_desc_of_isRootedForest (h : IsRootedForest pp r) {v c : V}
    (hc : c ∈ kids pp v) : v ∉ desc pp c := by
  classical
  obtain ⟨hfix, hroot⟩ := h
  intro hv
  rw [mem_desc] at hv
  obtain ⟨n, hn⟩ := hv
  have hne : c ≠ v := (mem_kids.mp hc).2
  have hpc : pp c = v := (mem_kids.mp hc).1
  have hn1 : 1 ≤ n := by
    rcases Nat.eq_zero_or_pos n with h0 | h0
    · exfalso; rw [h0] at hn; simp only [Function.iterate_zero_apply] at hn; exact hne hn.symm
    · exact h0
  -- `pp^[n + 1] v = pp c = v`, so `v` is periodic, hence `v = r`, hence `c = pp^[n] v = v`
  have hcyc : pp^[n + 1] v = v := by
    rw [Function.iterate_succ_apply', hn, hpc]
  have hvr : v = r := isRootedForest_periodic ⟨hfix, hroot⟩ (by omega) hcyc
  have hcv : c = v := by
    rw [← hn, hvr]
    exact isRootedForest_fix ⟨hfix, hroot⟩ n
  exact hne hcv


end RootedForest

/-! ### Regions closed under `pp`, and rooted pieces -/

/-- A finite region closed under taking parents. -/
def PPClosed (pp : V → V) (S : Finset V) : Prop := ∀ x ∈ S, pp x ∈ S

/-- `IsRootedPiece pp v P`: `P` is the vertex set of the subtree of the (pruned) tree rooted
at `v`: `v ∈ P`, `P` is closed under parents inside `P`, and every element of `P` has `v` as an
ancestor.  Such a set is connected in the graph whose edges are the parent edges. -/
def IsRootedPiece (pp : V → V) (v : V) (P : Finset V) : Prop :=
  v ∈ P ∧ (∀ x ∈ P, x ≠ v → pp x ∈ P) ∧ (∀ x ∈ P, ∃ n : ℕ, pp^[n] x = v)

lemma isRootedPiece_subset_desc {v : V} {P : Finset V} (h : IsRootedPiece pp v P) :
    P ⊆ desc pp v := by
  intro x hx
  rw [mem_desc]
  exact h.2.2 x hx

lemma desc_subset_insert_biUnion (v : V) :
    desc pp v ⊆ insert v ((kids pp v).biUnion (fun c => desc pp c)) := by
  classical
  intro x hx
  by_cases h : x = v
  · simp [h]
  · obtain ⟨c, hc, hxc⟩ := exists_kid_of_mem_desc hx h
    exact Finset.mem_insert_of_mem (Finset.mem_biUnion.mpr ⟨c, hc, hxc⟩)

lemma mem_desc_of_kid {v c : V} (h : c ∈ kids pp v) : desc pp c ⊆ desc pp v :=
  desc_mono (mem_kids.mp h).1

lemma insert_biUnion_subset_desc {v : V} {C : Finset V} (hC : C ⊆ kids pp v) :
    insert v (C.biUnion (fun c => desc pp c)) ⊆ desc pp v := by
  intro x hx
  rcases Finset.mem_insert.mp hx with h | hx'
  · rw [h]; exact self_mem_desc v
  · obtain ⟨c, hc, hxc⟩ := Finset.mem_biUnion.mp hx'
    exact mem_desc_of_kid (hC hc) hxc

/-- Iterates of a point in a `pp`-closed region stay in the region. -/
lemma iter_mem_of_ppClosed {S : Finset V} (hS : PPClosed pp S) {y : V} (hy : y ∈ S) (n : ℕ) :
    pp^[n] y ∈ S := by
  induction n with
  | zero => simpa using hy
  | succ m ih =>
      have h := hS _ ih
      simpa [Function.iterate_succ_apply'] using h

/-- A `pp`-closed region containing a descendant of `c` contains `c` (ancestors of points of
a `pp`-closed region stay in the region). -/
lemma ancestor_mem_of_ppClosed {S : Finset V} (hS : PPClosed pp S) {c y : V} (hy : y ∈ S)
    (hxy : y ∈ desc pp c) : c ∈ S := by
  rw [mem_desc] at hxy
  obtain ⟨n, hn⟩ := hxy
  rw [← hn]
  exact iter_mem_of_ppClosed hS hy n

/-! ### One-step extraction from a `pp`-closed region -/

section Extract

/-- **One-piece extraction.** If `S` is a `pp`-closed region all of whose points descend from `ρ`
and `S` contains at least `lam ≥ 2` marked vertices, then there are a centre `v ∈ S` and a set
`C ⊆ kids v` such that the rooted piece `P = S ∩ ({v} ∪ ⋃_{c ∈ C} desc c)` carries between `lam`
and `2*lam - 1` marked vertices. -/
theorem exists_piece {r : V} (hforest : IsRootedForest pp r)
    (A : Finset V) {lam : ℕ} (hlam : 2 ≤ lam)
    (S : Finset V) (hS : PPClosed pp S) {ρ : V} (hρS : ρ ∈ S) (hSsub : S ⊆ desc pp ρ)
    (hcount : lam ≤ (A ∩ S).card) :
    ∃ (v : V) (C : Finset V), v ∈ S ∧ C ⊆ kids pp v ∧
      IsRootedPiece pp v (S ∩ insert v (C.biUnion (fun c => desc pp c))) ∧
      lam ≤ (A ∩ S ∩ insert v (C.biUnion (fun c => desc pp c))).card ∧
      (A ∩ S ∩ insert v (C.biUnion (fun c => desc pp c))).card ≤ 2 * lam - 1 := by
  classical
  have hfix := hforest.1
  have hroot := hforest.2
  set T : Finset V := univ.filter (fun v => v ∈ S ∧ lam ≤ (A ∩ S ∩ desc pp v).card) with hTdef
  have hρT : ρ ∈ T := by
    refine Finset.mem_filter.mpr ⟨Finset.mem_univ _, hρS, ?_⟩
    have hsub : A ∩ S ∩ desc pp ρ = A ∩ S := by
      ext x
      exact ⟨fun h => (Finset.mem_inter.mp h).1,
        fun h => Finset.mem_inter.mpr ⟨h, hSsub (Finset.mem_inter.mp h).2⟩⟩
    rw [hsub]; exact hcount
  obtain ⟨v, hvT, hvmin⟩ := Finset.exists_mem_eq_sup T ⟨ρ, hρT⟩
    (fun v => (Finset.univ : Finset V).card - (desc pp v).card)
  obtain ⟨hvS, hvadm⟩ := (Finset.mem_filter.mp hvT).2
  -- minimality of `v`: every child of `v` has fewer than `lam` marked descendants in `S`
  have hsmall : ∀ c ∈ kids pp v, (A ∩ S ∩ desc pp c).card < lam := by
    intro c hc
    by_contra hcon
    push Not at hcon
    have hcS : c ∈ S := by
      have hne : (A ∩ S ∩ desc pp c).Nonempty := by
        rw [← Finset.card_pos]; omega
      obtain ⟨y, hy⟩ := hne
      have hyS : y ∈ S := (Finset.mem_inter.mp (Finset.mem_inter.mp hy).1).2
      have hyd : y ∈ desc pp c := (Finset.mem_inter.mp hy).2
      exact ancestor_mem_of_ppClosed hS hyS hyd
    have hcT : c ∈ T :=
      Finset.mem_filter.mpr ⟨Finset.mem_univ _, hcS, hcon⟩
    have h1 : (desc pp v).card ≤ (desc pp c).card := by
      have hsup : (Finset.univ : Finset V).card - (desc pp c).card ≤
          (Finset.univ : Finset V).card - (desc pp v).card := by
        rw [← hvmin]
        exact Finset.le_sup
          (f := fun v => (Finset.univ : Finset V).card - (desc pp v).card) hcT
      have h2 := Finset.card_le_card (Finset.subset_univ (desc pp c) :
        desc pp c ⊆ (Finset.univ : Finset V))
      have h3 := Finset.card_le_card (Finset.subset_univ (desc pp v) :
        desc pp v ⊆ (Finset.univ : Finset V))
      omega
    have h2 : (desc pp c).card < (desc pp v).card := by
      have hsub : desc pp c ⊆ desc pp v := desc_mono (mem_kids.mp hc).1
      rcases lt_or_ge (desc pp c).card (desc pp v).card with h | h
      · exact h
      · exfalso
        have heq : desc pp c = desc pp v := Finset.eq_of_subset_of_card_le hsub h
        have hv : v ∈ desc pp c := heq ▸ self_mem_desc v
        exact parent_not_mem_desc_of_isRootedForest ⟨hfix, hroot⟩ hc hv
    omega
  -- the family of admissible child sets
  set F : Finset V → ℕ := fun C => (A ∩ S ∩ insert v (C.biUnion (fun c => desc pp c))).card
    with hFdef
  have hkidsF : lam ≤ F (kids pp v) := by
    have hsub : A ∩ S ∩ desc pp v ⊆
        A ∩ S ∩ insert v ((kids pp v).biUnion (fun c => desc pp c)) := by
      intro x hx
      obtain ⟨hxAS, hxd⟩ := Finset.mem_inter.mp hx
      exact Finset.mem_inter.mpr ⟨hxAS,
        desc_subset_insert_biUnion v hxd⟩
    calc lam ≤ (A ∩ S ∩ desc pp v).card := hvadm
      _ ≤ F (kids pp v) := Finset.card_le_card hsub
  set U : Finset (Finset V) := (kids pp v).powerset.filter (fun C => lam ≤ F C) with hUdef
  have hU : U.Nonempty :=
    ⟨kids pp v, Finset.mem_filter.mpr ⟨Finset.mem_powerset.mpr subset_rfl, hkidsF⟩⟩
  obtain ⟨C, hCU, hCmin⟩ := Finset.exists_mem_eq_sup U hU (fun C => (kids pp v).card - C.card)
  have hCsub : C ⊆ kids pp v := Finset.mem_powerset.mp (Finset.mem_filter.mp hCU).1
  have hCF : lam ≤ F C := (Finset.mem_filter.mp hCU).2
  have hCmin' : ∀ C' ⊆ kids pp v, lam ≤ F C' → C.card ≤ C'.card := by
    intro C' hC'sub hC'F
    have hC'U : C' ∈ U :=
      Finset.mem_filter.mpr ⟨Finset.mem_powerset.mpr hC'sub, hC'F⟩
    have h1 : (kids pp v).card - C'.card ≤ (kids pp v).card - C.card := by
      rw [← hCmin]
      exact Finset.le_sup (f := fun C => (kids pp v).card - C.card) hC'U
    have h2 := Finset.card_le_card hCsub
    have h3 := Finset.card_le_card hC'sub
    omega
  have hCne : C.Nonempty := by
    rcases Finset.eq_empty_or_nonempty C with h | h
    · exfalso
      have h1 : F C ≤ 1 := by
        have h2 : C.biUnion (fun c => desc pp c) = ∅ := by rw [h]; simp
        have h3 : insert v (C.biUnion (fun c => desc pp c)) = ({v} : Finset V) := by
          rw [h2]; simp
        have h4 : F C = (A ∩ S ∩ ({v} : Finset V)).card := by
          simp only [hFdef, h3]
        rw [h4]
        calc (A ∩ S ∩ ({v} : Finset V)).card ≤ ({v} : Finset V).card :=
              Finset.card_le_card Finset.inter_subset_right
          _ = 1 := Finset.card_singleton v
      omega
    · exact h
  obtain ⟨c, hcC⟩ := hCne
  have hcKids : c ∈ kids pp v := hCsub hcC
  have hsmallc := hsmall c hcKids
  have herase : F (C.erase c) < lam := by
    by_contra hcon
    push Not at hcon
    have hsub : C.erase c ⊆ kids pp v :=
      (Finset.erase_subset c C).trans hCsub
    have h1 := hCmin' (C.erase c) hsub hcon
    have h2 : (C.erase c).card < C.card := Finset.card_erase_lt_of_mem hcC
    omega
  have hbound : F C ≤ F (C.erase c) + (A ∩ S ∩ desc pp c).card := by
    have hsub : insert v (C.biUnion (fun c' => desc pp c')) ⊆
        insert v ((C.erase c).biUnion (fun c' => desc pp c')) ∪ desc pp c := by
      intro x hx
      rcases Finset.mem_insert.mp hx with h | hx'
      · rw [h]
        exact Finset.mem_union.mpr (Or.inl (Finset.mem_insert.mpr (Or.inl rfl)))
      · obtain ⟨c', hc', hxc'⟩ := Finset.mem_biUnion.mp hx'
        by_cases hcc : c' = c
        · rw [hcc] at hxc'
          exact Finset.mem_union.mpr (Or.inr hxc')
        · exact Finset.mem_union.mpr (Or.inl (Finset.mem_insert.mpr
            (Or.inr (Finset.mem_biUnion.mpr ⟨c', Finset.mem_erase.mpr ⟨hcc, hc'⟩, hxc'⟩))))
    have hsub2 : A ∩ S ∩ insert v (C.biUnion (fun c' => desc pp c')) ⊆
        (A ∩ S ∩ insert v ((C.erase c).biUnion (fun c' => desc pp c'))) ∪
          (A ∩ S ∩ desc pp c) := by
      intro x hx
      obtain ⟨hxAS, hxT⟩ := Finset.mem_inter.mp hx
      rcases Finset.mem_union.mp (hsub hxT) with h | h
      · exact Finset.mem_union.mpr (Or.inl (Finset.mem_inter.mpr ⟨hxAS, h⟩))
      · exact Finset.mem_union.mpr (Or.inr (Finset.mem_inter.mpr ⟨hxAS, h⟩))
    calc F C ≤ ((A ∩ S ∩ insert v ((C.erase c).biUnion (fun c' => desc pp c'))) ∪
          (A ∩ S ∩ desc pp c)).card := Finset.card_le_card hsub2
      _ ≤ _ := Finset.card_union_le _ _
  refine ⟨v, C, hvS, hCsub, ?_, ?_, ?_⟩
  · refine ⟨Finset.mem_inter.mpr ⟨hvS, Finset.mem_insert.mpr (Or.inl rfl)⟩, ?_, ?_⟩
    · intro x hx hxv
      obtain ⟨hxS, hxins⟩ := Finset.mem_inter.mp hx
      have hx' : x ∈ C.biUnion (fun c' => desc pp c') := by
        rcases Finset.mem_insert.mp hxins with h | h
        · exact absurd h hxv
        · exact h
      obtain ⟨c', hc', hxc'⟩ := Finset.mem_biUnion.mp hx'
      have hpc' : pp c' = v := (mem_kids.mp (hCsub hc')).1
      by_cases hxc : x = c'
      · have hpx : pp x = v := by rw [hxc, hpc']
        exact Finset.mem_inter.mpr
          ⟨hpx ▸ hvS, hpx ▸ Finset.mem_insert.mpr (Or.inl rfl)⟩
      · have hppc' : pp x ∈ desc pp c' := pp_mem_desc_of_mem_desc hxc' hxc
        refine Finset.mem_inter.mpr ⟨hS x hxS, ?_⟩
        exact Finset.mem_insert.mpr
          (Or.inr (Finset.mem_biUnion.mpr ⟨c', hc', hppc'⟩))
    · intro x hx
      rcases Finset.mem_insert.mp (Finset.mem_inter.mp hx).2 with h | h
      · exact ⟨0, h⟩
      · obtain ⟨c', hc', hxc'⟩ := Finset.mem_biUnion.mp h
        rw [mem_desc] at hxc'
        obtain ⟨n, hn⟩ := hxc'
        exact ⟨n + 1, by rw [Function.iterate_succ_apply', hn, (mem_kids.mp (hCsub hc')).1]⟩
  · exact hCF
  · show F C ≤ 2 * lam - 1
    omega


end Extract

/-- A member of `desc x` of the form `pp y` with `y ∈ desc x`. -/
lemma mem_desc_self_one {x : V} : x ∈ desc pp (pp x) := by
  rw [mem_desc]
  exact ⟨1, by rw [Function.iterate_one]⟩

/-! ### Iterating the extraction, and the counting bound -/

section Iterate

/-- **Iterated extraction.** From a `pp`-closed region `S` we extract a family of rooted pieces,
pairwise edge-disjoint, each carrying between `lam` and `2*lam-1` marked vertices, and such that
all but at most `lam-1` of the marked vertices of `S` lie in the pieces. -/
theorem exists_pieces_aux {r : V} (hforest : IsRootedForest pp r)
    (A : Finset V) {lam : ℕ} (hlam : 2 ≤ lam) :
    ∀ (n : ℕ) (ρ : V) (S : Finset V), PPClosed pp S → ρ ∈ S → S ⊆ desc pp ρ →
      (A ∩ S).card ≤ n →
      ∃ s : Finset (V × Finset V),
        (∀ p ∈ s, IsRootedPiece pp p.1 p.2) ∧
        (∀ p ∈ s, p.2 ⊆ S) ∧
        (∀ p ∈ s, lam ≤ (A ∩ p.2).card ∧ (A ∩ p.2).card ≤ 2 * lam - 1) ∧
        (∀ p ∈ s, ∀ q ∈ s, p ≠ q → Disjoint (p.2.erase p.1) (q.2.erase q.1)) ∧
        (A ∩ S).card ≤ (∑ p ∈ s, (A ∩ p.2).card) + (lam - 1) := by
  classical
  have hfix := hforest.1
  have hroot := hforest.2
  intro n
  induction n using Nat.strongRecOn with
  | ind n ih =>
    intro ρ S hS hρS hSsub hn
    by_cases hcount : lam ≤ (A ∩ S).card
    · obtain ⟨v, C, hvS, hCkids, hpiece, hlow, hhigh⟩ :=
        exists_piece hforest A hlam S hS hρS hSsub hcount
      set P : Finset V := S ∩ insert v (C.biUnion (fun c => desc pp c)) with hPdef
      have hPsub : P ⊆ S := Finset.inter_subset_left
      have hPins : P ⊆ insert v (C.biUnion (fun c => desc pp c)) := Finset.inter_subset_right
      have hlowP : lam ≤ (A ∩ P).card := by
        rw [hPdef, ← Finset.inter_assoc]
        exact hlow
      have hhighP : (A ∩ P).card ≤ 2 * lam - 1 := by
        rw [hPdef, ← Finset.inter_assoc]
        exact hhigh
      set S' : Finset V := S \ P.erase v with hS'def
      -- the pruned region is still `pp`-closed
      have hS'closed : PPClosed pp S' := by
        intro x hx
        obtain ⟨hxS, hxP⟩ := Finset.mem_sdiff.mp hx
        refine Finset.mem_sdiff.mpr ⟨hS x hxS, ?_⟩
        intro hmem
        obtain ⟨hppne, hppP⟩ := Finset.mem_erase.mp hmem
        have hins : pp x ∈ insert v (C.biUnion (fun c => desc pp c)) := hPins hppP
        rcases Finset.mem_insert.mp hins with h | h
        · exact hppne h
        · obtain ⟨c, hc, hppxc⟩ := Finset.mem_biUnion.mp h
          have hxc : x ∈ desc pp c := desc_mono_mem hppxc mem_desc_self_one
          have hcKids : c ∈ kids pp v := hCkids hc
          have hxv : x ≠ v := by
            intro hxv_eq
            exact parent_not_mem_desc_of_isRootedForest ⟨hfix, hroot⟩ hcKids (hxv_eq ▸ hxc)
          exact hxP (Finset.mem_erase.mpr ⟨hxv, Finset.mem_inter.mpr
            ⟨hxS, Finset.mem_insert.mpr (Or.inr (Finset.mem_biUnion.mpr ⟨c, hc, hxc⟩))⟩⟩)
      have hρS' : ρ ∈ S' := by
        refine Finset.mem_sdiff.mpr ⟨hρS, ?_⟩
        intro hmem
        obtain ⟨hρne, hρP⟩ := Finset.mem_erase.mp hmem
        have hins : ρ ∈ insert v (C.biUnion (fun c => desc pp c)) := hPins hρP
        have hvdesc : v ∈ desc pp ρ := hSsub hvS
        rcases Finset.mem_insert.mp hins with h | h
        · exact hρne h
        · obtain ⟨c, hc, hρc⟩ := Finset.mem_biUnion.mp h
          have hcdesc : c ∈ desc pp v :=
            mem_desc_of_kid (hCkids hc) (self_mem_desc c)
          have hρdesc : ρ ∈ desc pp v := desc_mono_mem hcdesc hρc
          rw [mem_desc] at hρdesc hvdesc
          obtain ⟨a, ha⟩ := hρdesc
          obtain ⟨b, hb⟩ := hvdesc
          have ha1 : 1 ≤ a := by
            rcases Nat.eq_zero_or_pos a with h0 | h0
            · exfalso
              rw [h0] at ha
              simp only [Function.iterate_zero_apply] at ha
              exact hρne ha
            · exact h0
          have hcyc : pp^[a + b] ρ = ρ := by
            rw [Nat.add_comm a b, Function.iterate_add_apply, ha, hb]
          have hρr : ρ = r := isRootedForest_periodic ⟨hfix, hroot⟩ (by omega) hcyc
          have hvr : v = r := by
            rw [← ha, hρr]
            exact isRootedForest_fix ⟨hfix, hroot⟩ a
          exact hρne (hρr.trans hvr.symm)
      have hS'sub : S' ⊆ desc pp ρ :=
        fun x hx => hSsub (Finset.mem_sdiff.mp hx).1
      -- the marked count strictly decreases
      have hlt : (A ∩ S').card < (A ∩ S).card := by
        have hsub : A ∩ S' ⊆ A ∩ S := fun x hx =>
          Finset.mem_inter.mpr ⟨(Finset.mem_inter.mp hx).1,
            (Finset.mem_sdiff.mp (Finset.mem_inter.mp hx).2).1⟩
        have hex : ∃ x, x ∈ A ∩ S ∧ x ∉ S' := by
          have h3 : 2 ≤ (A ∩ P).card := le_trans hlam hlowP
          have hex2 : ∃ x ∈ A ∩ P, x ≠ v := by
            by_contra hcon
            simp only [not_exists, not_and] at hcon
            have hsub1 : A ∩ P ⊆ ({v} : Finset V) := fun x hx =>
              Finset.mem_singleton.mpr (by simpa using hcon x hx)
            have h4 := Finset.card_le_card hsub1
            rw [Finset.card_singleton] at h4
            omega
          obtain ⟨x, hxP, hxv⟩ := hex2
          refine ⟨x, Finset.mem_inter.mpr
            ⟨(Finset.mem_inter.mp hxP).1, hPsub (Finset.mem_inter.mp hxP).2⟩, ?_⟩
          intro hxS'
          have hxPe : x ∈ P.erase v :=
            Finset.mem_erase.mpr ⟨hxv, (Finset.mem_inter.mp hxP).2⟩
          exact (Finset.mem_sdiff.mp hxS').2 hxPe
        obtain ⟨x, hxAS, hxS'⟩ := hex
        rcases lt_or_ge (A ∩ S').card (A ∩ S).card with h | h
        · exact h
        · exfalso
          have heq : A ∩ S' = A ∩ S := Finset.eq_of_subset_of_card_le hsub h
          have hx2 : x ∈ A ∩ S' := by rw [heq]; exact hxAS
          exact hxS' (Finset.mem_inter.mp hx2).2
      obtain ⟨s', h1, h2, h3, h4, h5⟩ :=
        ih (A ∩ S').card (by omega) ρ S' hS'closed hρS' hS'sub le_rfl
      have hPnotsub : ¬ P ⊆ S' := by
        intro hsub
        have h1' : P.erase v ⊆ S' := (Finset.erase_subset v P).trans hsub
        have hempty : P.erase v = ∅ := by
          apply Finset.eq_empty_iff_forall_notMem.mpr
          intro x hx
          have hxS' : x ∈ S' := h1' hx
          exact (Finset.mem_sdiff.mp hxS').2 hx
        have hcard : (A ∩ P).card ≤ 1 := by
          have hsub1 : A ∩ P ⊆ ({v} : Finset V) := by
            intro x hx
            have hxP : x ∈ P := (Finset.mem_inter.mp hx).2
            by_cases hxv : x = v
            · exact Finset.mem_singleton.mpr hxv
            · exfalso
              have hxe : x ∈ P.erase v := Finset.mem_erase.mpr ⟨hxv, hxP⟩
              rw [hempty] at hxe
              exact absurd hxe (Finset.notMem_empty x)
          have h4 := Finset.card_le_card hsub1
          rw [Finset.card_singleton] at h4
          exact h4
        omega
      have hnotmem : (v, P) ∉ s' := by
        intro hmem
        exact hPnotsub (h2 (v, P) hmem)
      refine ⟨insert (v, P) s', ?_, ?_, ?_, ?_, ?_⟩
      · intro p hp
        rcases Finset.mem_insert.mp hp with rfl | hp'
        · exact hpiece
        · exact h1 p hp'
      · intro p hp
        rcases Finset.mem_insert.mp hp with rfl | hp'
        · exact hPsub
        · exact (h2 p hp').trans (Finset.sdiff_subset)
      · intro p hp
        rcases Finset.mem_insert.mp hp with rfl | hp'
        · exact ⟨hlowP, hhighP⟩
        · exact h3 p hp'
      · intro p hp q hq hpq
        rcases Finset.mem_insert.mp hp with rfl | hp' <;> rcases Finset.mem_insert.mp hq with rfl | hq'
        · exact absurd rfl hpq
        · exact Finset.disjoint_left.mpr fun x hx hx2 =>
            (Finset.mem_sdiff.mp (h2 q hq' (Finset.mem_erase.mp hx2).2)).2 hx
        · exact Finset.disjoint_left.mpr fun x hx hx2 =>
            (Finset.mem_sdiff.mp (h2 p hp' (Finset.mem_erase.mp hx).2)).2 hx2
        · exact h4 p hp' q hq' hpq
      · have hsum : (∑ p ∈ insert (v, P) s', (A ∩ p.2).card)
            = (A ∩ P).card + ∑ p ∈ s', (A ∩ p.2).card := by
          rw [Finset.sum_insert hnotmem]
        have hsplit : A ∩ S ⊆ (A ∩ P) ∪ (A ∩ S') := by
          intro x hx
          obtain ⟨hxA, hxS⟩ := Finset.mem_inter.mp hx
          by_cases hxP : x ∈ P
          · exact Finset.mem_union.mpr (Or.inl (Finset.mem_inter.mpr ⟨hxA, hxP⟩))
          · have hx' : x ∈ S' := by
              refine Finset.mem_sdiff.mpr ⟨hxS, ?_⟩
              intro hxPe
              exact hxP (Finset.mem_erase.mp hxPe).2
            exact Finset.mem_union.mpr (Or.inr (Finset.mem_inter.mpr ⟨hxA, hx'⟩))
        have hcard : (A ∩ S).card ≤ (A ∩ P).card + (A ∩ S').card :=
          (Finset.card_le_card hsplit).trans (Finset.card_union_le _ _)
        rw [hsum]
        omega
    · refine ⟨∅, ?_, ?_, ?_, ?_, ?_⟩
      · simp
      · simp
      · simp
      · simp
      · have h0 : (∑ p ∈ (∅ : Finset (V × Finset V)), (A ∩ p.2).card) = 0 := by simp
        rw [h0, Nat.zero_add]
        omega


end Iterate

/-! ### The counting arithmetic -/

section Arithmetic

/-- The elementary inequality behind the exponent `3^(k-1)`. -/
lemma key_ineq {lam k : ℕ} (hk : 1 ≤ k) (hlam : 1 ≤ lam) :
    3 ^ (k - 1) * (2 * lam - 1) + (lam - 1) < 3 ^ k * lam := by
  have hk' : k - 1 + 1 = k := Nat.sub_add_cancel hk
  have h3 : 3 ^ k * lam = 3 * (3 ^ (k - 1) * lam) := by
    have h3' : 3 ^ k = 3 * 3 ^ (k - 1) := by
      conv_lhs => rw [← hk']
      rw [pow_succ']
    rw [h3']
    ring
  have hA1 : 1 ≤ 3 ^ (k - 1) := by
    have h := pow_pos (by norm_num : (0 : ℕ) < 3) (k - 1)
    omega
  have hstep : 3 ^ (k - 1) * (2 * lam - 1) + 3 ^ (k - 1) = 2 * (3 ^ (k - 1) * lam) := by
    have h2 : (2 * lam - 1).succ = 2 * lam := by omega
    rw [← Nat.mul_succ, h2]
    ring
  have hle : lam ≤ 3 ^ (k - 1) * lam := by
    calc lam = 1 * lam := (one_mul lam).symm
      _ ≤ 3 ^ (k - 1) * lam := Nat.mul_le_mul_right lam hA1
  have hAeq : 3 ^ (k - 1) * (2 * lam - 1) = 2 * (3 ^ (k - 1) * lam) - 3 ^ (k - 1) := by
    omega
  have hlt : lam - 1 < 3 ^ (k - 1) * lam := lt_of_lt_of_le (by omega) hle
  have h1 : 2 * (3 ^ (k - 1) * lam) - 3 ^ (k - 1) + (lam - 1) ≤
      2 * (3 ^ (k - 1) * lam) + (lam - 1) := by
    have := Nat.sub_le (2 * (3 ^ (k - 1) * lam)) (3 ^ (k - 1))
    omega
  have h2 : 2 * (3 ^ (k - 1) * lam) + (lam - 1) <
      2 * (3 ^ (k - 1) * lam) + 3 ^ (k - 1) * lam := by omega
  have h4 : 2 * (3 ^ (k - 1) * lam) + 3 ^ (k - 1) * lam = 3 * (3 ^ (k - 1) * lam) := by
    ring
  rw [h3, hAeq]
  omega

/-- **Counting bound.** If `m` pieces each carry at most `2*lam-1` marked vertices and together
with a leftover of at most `lam-1` they exhaust at least `3^k * lam` marked vertices, then there
are at least `3^(k-1)+1` pieces. -/
lemma count_bound {m lam k : ℕ} (hk : 1 ≤ k) (hlam : 1 ≤ lam)
    (h : 3 ^ k * lam ≤ m * (2 * lam - 1) + (lam - 1)) : 3 ^ (k - 1) + 1 ≤ m := by
  by_contra hcon
  have hm : m ≤ 3 ^ (k - 1) := by omega
  have hmono : m * (2 * lam - 1) ≤ 3 ^ (k - 1) * (2 * lam - 1) :=
    Nat.mul_le_mul_right _ hm
  have hkey := key_ineq hk hlam
  omega

end Arithmetic

/-! ### The tree partition lemma -/

section Main

/-- **Tree partition lemma (finite case), absolute-threshold form.**

Let `pp r = r`, let every vertex of the finite vertex set `V` reach `r` along `pp`,
and let `A` be a set of marked vertices with
`3^k * lam ≤ #A`, where `lam ≥ 2` and `k ≥ 1`.  Then `V` can be covered, up to a leftover of at
most `lam - 1` marked vertices, by rooted pieces `(v, P)` — sets `P` containing `v` that are closed
under parents inside `P` and in which every point has `v` as an ancestor — such that
* there are at least `3^(k-1)+1` of them,
* each piece carries between `lam` and `2*lam-1` marked vertices, and
* the pieces are pairwise edge-disjoint (`P.erase v` indexes the parent edges of the piece).

Such pieces are exactly the disjoint witnesses used in the proof of Theorem I.2.3: inside a
configuration in which the parent edges of a piece are open, all vertices of the piece are
connected, so each piece is a witness for the event that a cluster meets the marked set in at
least `lam` vertices.  The BK inequality then gives the `3^(k-1)+1`-fold product bound (2.8). -/
theorem exists_tree_pieces {r : V} (hforest : IsRootedForest pp r)
    (A : Finset V) {lam k : ℕ} (hlam : 2 ≤ lam) (hk : 1 ≤ k)
    (hA : 3 ^ k * lam ≤ A.card) :
    ∃ s : Finset (V × Finset V), 3 ^ (k - 1) + 1 ≤ s.card ∧
      (∀ p ∈ s, IsRootedPiece pp p.1 p.2) ∧
      (∀ p ∈ s, lam ≤ (A ∩ p.2).card ∧ (A ∩ p.2).card ≤ 2 * lam - 1) ∧
      (∀ p ∈ s, ∀ q ∈ s, p ≠ q → Disjoint (p.2.erase p.1) (q.2.erase q.1)) := by
  classical
  have hfix := hforest.1
  have hroot := hforest.2
  have hclosed : PPClosed pp (Finset.univ : Finset V) := fun x _ => Finset.mem_univ _
  have hsub : (Finset.univ : Finset V) ⊆ desc pp r := by
    intro x _
    rw [mem_desc]
    exact hroot x
  have hcard : (A ∩ (Finset.univ : Finset V)).card ≤ A.card := by
    rw [Finset.inter_univ]
  obtain ⟨s, h1, h2, h3, h4, h5⟩ :=
    exists_pieces_aux hforest A hlam A.card r Finset.univ hclosed (Finset.mem_univ r) hsub hcard
  refine ⟨s, ?_, h1, h3, h4⟩
  have hsum_le : (∑ p ∈ s, (A ∩ p.2).card) ≤ s.card * (2 * lam - 1) := by
    calc (∑ p ∈ s, (A ∩ p.2).card) ≤ ∑ p ∈ s, (2 * lam - 1) := by
          apply Finset.sum_le_sum
          intro p hp
          exact (h3 p hp).2
      _ = s.card * (2 * lam - 1) := by
          simp [Finset.sum_const, nsmul_eq_mul]
  have hAcard : (A ∩ (Finset.univ : Finset V)).card = A.card := by rw [Finset.inter_univ]
  have hmain : 3 ^ k * lam ≤ s.card * (2 * lam - 1) + (lam - 1) := by
    calc 3 ^ k * lam ≤ A.card := hA
      _ = (A ∩ (Finset.univ : Finset V)).card := hAcard.symm
      _ ≤ (∑ p ∈ s, (A ∩ p.2).card) + (lam - 1) := h5
      _ ≤ s.card * (2 * lam - 1) + (lam - 1) := by
          have := hsum_le
          omega
  exact count_bound hk (by omega) hmain


end Main

/-! ### Pieces are connected: the BK witness property -/

section Connectivity

/-- While the `pp`-chain has not yet reached the root of the piece, it stays inside the piece. -/
lemma iter_mem_piece {v : V} {P : Finset V} (h : IsRootedPiece pp v P) {z : V} (hz : z ∈ P)
    {k : ℕ} (hk : ∀ i, i < k → pp^[i] z ≠ v) : pp^[k] z ∈ P := by
  induction k with
  | zero => simpa using hz
  | succ j ih =>
      rw [Function.iterate_succ_apply']
      exact h.2.1 _ (ih (fun i hi => hk i (by omega))) (hk j (by omega))

/-- If the `pp`-chain of `z ∈ P` reaches the root of the piece, then `z` is connected to the root
by open parent edges. -/
lemma reach_root {v : V} {P : Finset V} (h : IsRootedPiece pp v P) (adj : V → V → Prop)
    (hopen : ∀ x ∈ P, x ≠ v → adj x (pp x)) {z : V} (hz : z ∈ P) {n : ℕ}
    (hn : pp^[n] z = v) : Relation.ReflTransGen adj z v := by
  classical
  have hex : ∃ m : ℕ, pp^[m] z = v := ⟨n, hn⟩
  set k := Nat.find hex with hkdef
  have hspec : pp^[k] z = v := Nat.find_spec hex
  have hmin : ∀ i, i < k → pp^[i] z ≠ v := by
    intro i hi hcon
    have hle := Nat.find_min' hex hcon
    omega
  have key : ∀ j, j ≤ k → Relation.ReflTransGen adj z (pp^[j] z) := by
    intro j hj
    induction j with
    | zero => simpa using Relation.ReflTransGen.refl (r := adj) (a := z)
    | succ i ih =>
        have hi : i ≤ k := by omega
        have hzi : pp^[i] z ∈ P := iter_mem_piece h hz (fun l hl => hmin l (by omega))
        have hne : pp^[i] z ≠ v := hmin i (by omega)
        have hstep : adj (pp^[i] z) (pp (pp^[i] z)) := hopen _ hzi hne
        rw [Function.iterate_succ_apply']
        exact (ih hi).tail hstep
  have := key k le_rfl
  rwa [hspec] at this

/-- Reversal of a reachability chain in a symmetric relation. -/
lemma reflTransGen_symm {adj : V → V → Prop} (hsymm : Std.Symm adj) {a b : V}
    (h : Relation.ReflTransGen adj a b) : Relation.ReflTransGen adj b a := by
  induction h with
  | refl => exact Relation.ReflTransGen.refl
  | tail _ hbc ih => exact ih.head (hsymm.symm _ _ hbc)

/-- **Pieces are connected witnesses.**  Let `adj` be a symmetric adjacency relation on `V` and
suppose every parent edge inside a rooted piece is `adj` (e.g. open, in a percolation
configuration).  Then all vertices of the piece lie in a single `adj`-component.  In the setting
of Theorem I.2.3 each piece is therefore a witness — in the sense used by the BK inequality — for
the event that some cluster meets the marked set in at least `lam` vertices. -/
theorem isRootedPiece_reachable (adj : V → V → Prop) (hsymm : Std.Symm adj)
    {v : V} {P : Finset V} (h : IsRootedPiece pp v P)
    (hopen : ∀ x ∈ P, x ≠ v → adj x (pp x)) {x y : V} (hx : x ∈ P) (hy : y ∈ P) :
    Relation.ReflTransGen adj x y := by
  obtain ⟨n, hn⟩ := h.2.2 x hx
  obtain ⟨m, hm⟩ := h.2.2 y hy
  have h1 : Relation.ReflTransGen adj x v := reach_root h adj hopen hx hn
  have h2 : Relation.ReflTransGen adj y v := reach_root h adj hopen hy hm
  exact h1.trans (reflTransGen_symm hsymm h2)

end Connectivity

end Hutchcroft
