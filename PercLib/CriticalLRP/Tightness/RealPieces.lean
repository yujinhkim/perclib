/-
Migration source: https://github.com/yujinhkim/Critical-Long-range-percolation
Integration revision: 3b3d1d0e43ef940bfaa2292ee5c2ee094ac4edbf
Licence: Apache-2.0 for the PercLib Lean sources and tooling; see third_party/critical-lrp/.
External provenance and modifications are recorded in the file-specific notices below.
-/

/-
# Real-threshold tree pieces: the extraction behind (2.10)/(2.11) at non-integral `λ`

Reference: T. Hutchcroft, *Power-law bounds for critical long-range percolation below the
upper-critical dimension*, arXiv:2008.11197v2, Section 2.1: Lemma 2.4 and the displays
(2.8), (2.9), (2.10), (2.11).

The source prints `Theorem 2.3` for `k ≥ 0`. At `k = 0` its exponent is
`3^(-1)+1 = 4/3`, so (2.8) asserts `P(A) ≤ P(A)^(4/3)`, which fails as soon as
`0 < P(A) < 1` (natural subtraction in Lean is not the source's exponent). The proof uses
Lemma 2.4, which is stated for `k ≥ 1` (it produces `m ≥ 3^(k-1)+1 ≥ 2` pieces).  Everything
here therefore assumes `k ≥ 1`, matching the proof and not the printed statement.

The source also stresses that `λ` need not be an integer.  The repository's
`Tightness/TreePieces.lean` proves the finite tree-piece partition for an **integer** threshold
`lam : ℕ`, with piece counts in `[lam, 2*lam-1]`.  That form cannot be instantiated at a
non-integral `λ ≥ 1`: to certify "the piece carries at least `λ` marked vertices" one needs an
integer threshold `μ ≥ λ`, but the hypothesis `3^k * μ ≤ #A` of the integer lemma may then fail.
An integer threshold therefore does not suffice by monotonicity alone; this file avoids that loss.

This file supplies the missing real-threshold statement:

* `exists_piece_real` — one-piece extraction: from a `pp`-closed region carrying `≥ λ` marked
  vertices, extract a rooted piece with a marked count in `[λ, 2λ)`.
* `exists_pieces_real_aux` — the iterated extraction, leaving a remainder carrying `< λ`
  marked vertices.
* `count_bound_real` — the counting arithmetic: `m` pieces with counts `< 2λ` plus a remainder
  `< λ` covering `≥ 3^k λ` force `m ≥ 3^(k-1)+1`.
* `exists_tree_pieces_real` — the real-threshold tree partition lemma, `λ ≥ 1` real, `k ≥ 1`.
* `exists_open_pieces_real` — the percolation-level form: disjoint open witness sets inside one
  cluster of `r`, each pointing at a set `t ⊆ Λ` of `≥ λ` window vertices connected through its
  own witness edges.  This is the input (2.11) uses for BK.

The proofs are the arguments of `Tightness/TreePieces.lean` and of the source's Lemma 2.4, with
the integer comparisons on marked counts replaced by real ones.  Two features of the real case
deserve note:

* the upper bound is the strict `count < 2λ`, not `count ≤ 2λ-1`; the greedy choice of `C`
  overshoots by fewer than `λ` marked vertices, which is exactly `[λ, 2λ)`;
* the pruned-region iteration of `TreePieces.lean` removes the parent edges of a piece but keeps
  its root, so progress needs the piece to carry a marked vertex other than its root.  That
  holds automatically for `λ ≥ 2` (`count ≥ λ ≥ 2`).  For `lam = 1` a single marked vertex is already
  an admissible piece, and `exists_tree_pieces_real` handles that endpoint separately with
  singleton pieces, so no `Nat` subtraction of exponents or thresholds is ever needed.

No `sorry`, no `native_decide`, no custom axioms.
-/
module

public import PercLib.CriticalLRP.Tightness.ClusterWitness
public import PercLib.CriticalLRP.Tightness.RootSpine

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

/-! ### One-piece extraction at a real threshold -/

section ExtractReal

variable {pp : V → V}

/-- **One-piece extraction, real threshold.**  If `S` is a `pp`-closed region all of whose points
descend from `ρ` and `S` carries at least `lam ≥ 2` marked vertices, then there are a centre
`v ∈ S` and a set `C ⊆ kids v` such that the rooted piece
`P = S ∩ ({v} ∪ ⋃_{c ∈ C} desc c)` carries between `lam` and `2*lam` (strictly) marked vertices.

The upper bound is strict because the greedy choice of `C` overshoots by fewer than `lam`: the
last child contributes `< lam` and before it the count was already `≥ lam`. -/
theorem exists_piece_real {r : V} (hforest : IsRootedForest pp r)
    (A : Finset V) {lam : ℝ} (hlam : 1 < lam)
    (S : Finset V) (hS : PPClosed pp S) {ρ : V} (hρS : ρ ∈ S) (hSsub : S ⊆ desc pp ρ)
    (hcount : lam ≤ ((A ∩ S).card : ℝ)) :
    ∃ (v : V) (C : Finset V), v ∈ S ∧ C ⊆ kids pp v ∧
      IsRootedPiece pp v (S ∩ insert v (C.biUnion (fun c => desc pp c))) ∧
      lam ≤ ((A ∩ S ∩ insert v (C.biUnion (fun c => desc pp c))).card : ℝ) ∧
      ((A ∩ S ∩ insert v (C.biUnion (fun c => desc pp c))).card : ℝ) < 2 * lam := by
  classical
  have hfix := hforest.1
  have hroot := hforest.2
  -- the vertices whose descendant set already carries `lam` marked vertices of `S`
  set T : Finset V :=
    univ.filter (fun v => v ∈ S ∧ lam ≤ ((A ∩ S ∩ desc pp v).card : ℝ)) with hTdef
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
  have hsmall : ∀ c ∈ kids pp v, ((A ∩ S ∩ desc pp c).card : ℝ) < lam := by
    intro c hc
    by_contra hcon
    push Not at hcon
    have hcS : c ∈ S := by
      have hpos : 0 < (A ∩ S ∩ desc pp c).card := by
        have h2 : (1 : ℝ) < ((A ∩ S ∩ desc pp c).card : ℝ) := lt_of_lt_of_le hlam hcon
        have h2' : (1 : ℕ) < (A ∩ S ∩ desc pp c).card := by exact_mod_cast h2
        omega
      obtain ⟨y, hy⟩ := Finset.card_pos.mp hpos
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
  -- the family of admissible child sets, by marked count
  set F : Finset V → ℕ := fun C => (A ∩ S ∩ insert v (C.biUnion (fun c => desc pp c))).card
    with hFdef
  have hkidsF : lam ≤ (F (kids pp v) : ℝ) := by
    have hsub : A ∩ S ∩ desc pp v ⊆
        A ∩ S ∩ insert v ((kids pp v).biUnion (fun c => desc pp c)) := by
      intro x hx
      obtain ⟨hxAS, hxd⟩ := Finset.mem_inter.mp hx
      exact Finset.mem_inter.mpr ⟨hxAS,
        desc_subset_insert_biUnion v hxd⟩
    calc lam ≤ ((A ∩ S ∩ desc pp v).card : ℝ) := hvadm
      _ ≤ ((F (kids pp v) : ℕ) : ℝ) := by
          have hc := Finset.card_le_card hsub
          exact_mod_cast hc
  set U : Finset (Finset V) := (kids pp v).powerset.filter (fun C => lam ≤ (F C : ℝ))
    with hUdef
  have hU : U.Nonempty :=
    ⟨kids pp v, Finset.mem_filter.mpr ⟨Finset.mem_powerset.mpr subset_rfl, hkidsF⟩⟩
  -- choose an admissible `C` of minimal cardinality: the greedy stopping set
  obtain ⟨C, hCU, hCmin⟩ := Finset.exists_mem_eq_sup U hU (fun C => (kids pp v).card - C.card)
  have hCsub : C ⊆ kids pp v := Finset.mem_powerset.mp (Finset.mem_filter.mp hCU).1
  have hCF : lam ≤ (F C : ℝ) := (Finset.mem_filter.mp hCU).2
  have hCmin' : ∀ C' ⊆ kids pp v, lam ≤ (F C' : ℝ) → C.card ≤ C'.card := by
    intro C' hC'sub hC'F
    have hC'U : C' ∈ U :=
      Finset.mem_filter.mpr ⟨Finset.mem_powerset.mpr hC'sub, hC'F⟩
    have h1 : (kids pp v).card - C'.card ≤ (kids pp v).card - C.card := by
      rw [← hCmin]
      exact Finset.le_sup (f := fun C => (kids pp v).card - C.card) hC'U
    have h2 := Finset.card_le_card hCsub
    have h3 := Finset.card_le_card hC'sub
    omega
  -- the piece is a rooted piece
  have hpiece : IsRootedPiece pp v (S ∩ insert v (C.biUnion (fun c => desc pp c))) := by
    refine ⟨Finset.mem_inter.mpr ⟨hvS, Finset.mem_insert.mpr (Or.inl rfl)⟩, ?_, ?_⟩
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
  refine ⟨v, C, hvS, hCsub, hpiece, hCF, ?_⟩
  -- the strict upper bound: an empty `C` gives at most the root itself
  rcases Finset.eq_empty_or_nonempty C with hC0 | hCne
  · subst hC0
    have h1 : (F (∅ : Finset V) : ℝ) ≤ 1 := by
      have h2 : (∅ : Finset V).biUnion (fun c => desc pp c) = ∅ := by simp
      have h3 : insert v ((∅ : Finset V).biUnion (fun c => desc pp c)) = ({v} : Finset V) := by
        rw [h2]; simp
      have h4 : F (∅ : Finset V) = (A ∩ S ∩ ({v} : Finset V)).card := by
        simp only [hFdef, h3]
      rw [h4]
      have h5 : (A ∩ S ∩ ({v} : Finset V)).card ≤ ({v} : Finset V).card :=
        Finset.card_le_card Finset.inter_subset_right
      rw [Finset.card_singleton] at h5
      exact_mod_cast h5
    linarith
  · obtain ⟨c, hcC⟩ := hCne
    have hcKids : c ∈ kids pp v := hCsub hcC
    have hsmallc := hsmall c hcKids
    have herase : (F (C.erase c) : ℝ) < lam := by
      by_contra hcon
      push Not at hcon
      have hsub : C.erase c ⊆ kids pp v := (Finset.erase_subset c C).trans hCsub
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
    have := hbound
    have hcast : ((F C : ℕ) : ℝ) ≤ (F (C.erase c) : ℝ) +
        ((A ∩ S ∩ desc pp c).card : ℝ) := by
      have := hbound
      push_cast
      exact_mod_cast this
    linarith

end ExtractReal

/-! ### The counting arithmetic at a real threshold -/

section ArithmeticReal

/-- **Counting bound, real threshold.**  If `m` pieces carry fewer than `2λ` marked vertices each,
the leftover carries fewer than `λ`, and together they cover at least `3^k λ`, then
`m ≥ 3^(k-1)+1`.  The comparison `m > 3^(k-1)` comes from
`(3^k-1)/2 ≥ 3^(k-1)`; no threshold is ever rounded, so a non-integral `λ` is handled exactly. -/
theorem count_bound_real {ι : Type*} (s : Finset ι) (c : ι → ℕ) {lam : ℝ} {k : ℕ}
    {leftover : ℕ} (hk : 1 ≤ k) (hlam : 1 ≤ lam)
    (hhigh : ∀ i ∈ s, (c i : ℝ) < 2 * lam)
    (hleft : (leftover : ℝ) < lam)
    (htot : 3 ^ k * lam ≤ ((∑ i ∈ s, c i) + leftover : ℕ)) :
    3 ^ (k - 1) + 1 ≤ s.card := by
  have h3 : (0 : ℝ) < (3 : ℝ) ^ (k - 1) := pow_pos (by norm_num) _
  have h3ge : (1 : ℝ) ≤ (3 : ℝ) ^ (k - 1) := one_le_pow₀ (by norm_num)
  have h3k : (3 : ℝ) ^ k = 3 * (3 : ℝ) ^ (k - 1) := by
    have h : k - 1 + 1 = k := Nat.sub_add_cancel hk
    conv_lhs => rw [← h]
    rw [pow_succ']
  by_contra hcon
  have hm : s.card ≤ 3 ^ (k - 1) := by
    have : s.card < 3 ^ (k - 1) + 1 := Nat.lt_of_not_le hcon
    omega
  have hcard : (s.card : ℝ) ≤ (3 : ℝ) ^ (k - 1) := by exact_mod_cast hm
  have hsum_lt : (∑ i ∈ s, (c i : ℝ)) < s.card * (2 * lam) := by
    calc (∑ i ∈ s, (c i : ℝ)) < ∑ _i ∈ s, (2 * lam) := by
          refine Finset.sum_lt_sum (fun i hi => (hhigh i hi).le) ?_
          rcases Finset.eq_empty_or_nonempty s with h | h
          · rw [h] at htot; simp at htot; nlinarith
          · obtain ⟨i, hi⟩ := h
            exact ⟨i, hi, hhigh i hi⟩
      _ = s.card * (2 * lam) := by rw [Finset.sum_const, nsmul_eq_mul]
  have hcast : ((∑ i ∈ s, c i : ℕ) : ℝ) = ∑ i ∈ s, (c i : ℝ) := by push_cast; rfl
  have htot' : 3 ^ k * lam ≤ ((∑ i ∈ s, c i : ℕ) : ℝ) + leftover := by
    have hc : (3 ^ k * lam : ℝ) ≤ (((∑ i ∈ s, c i) + leftover : ℕ) : ℝ) := by
      exact_mod_cast htot
    push_cast at hc
    linarith
  have hstep : (s.card : ℝ) * (2 * lam) ≤ (3 : ℝ) ^ (k - 1) * (2 * lam) :=
    mul_le_mul_of_nonneg_right hcard (by linarith : (0:ℝ) ≤ 2 * lam)
  have hkey : (3 : ℝ) ^ (k - 1) * (2 * lam) + lam ≤ 3 ^ k * lam := by
    rw [h3k]
    nlinarith [h3ge, hlam]
  have h1 : 3 ^ k * lam ≤ (s.card : ℝ) * (2 * lam) + leftover := by linarith
  have h2 : (s.card : ℝ) * (2 * lam) + leftover < (3 : ℝ) ^ (k - 1) * (2 * lam) + lam := by
    linarith
  linarith [hkey]

end ArithmeticReal

/-! ### Iterated extraction and the real-threshold tree partition -/

section IterateReal

/-- **Iterated extraction, real threshold.**  From a `pp`-closed region `S` we extract a family of
rooted pieces, pairwise edge-disjoint, each carrying a number of marked vertices in `[lam, 2*lam)`,
together with a surviving `pp`-closed remainder carrying fewer than `lam` marked vertices, such
that the marked vertices of `S` are covered by the pieces and the remainder.

The region is pruned by removing the parent edges of each piece but keeping its root, so that the
remaining branches stay attached; this is why `lam ≥ 2` is needed here: a piece with `≥ 2` marked
vertices and `lam ≥ 2` contains a marked vertex other than its root, so the marked count strictly
decreases and the recursion terminates.  (`exists_tree_pieces_real` covers `1 ≤ lam < 2` by
one-vertex pieces, where no such argument is available or needed.) -/
theorem exists_pieces_real_aux {r : V} (hforest : IsRootedForest pp r)
    (A : Finset V) {lam : ℝ} (hlam : 1 < lam) :
    ∀ (n : ℕ) (ρ : V) (S : Finset V), PPClosed pp S → ρ ∈ S → S ⊆ desc pp ρ →
      (A ∩ S).card ≤ n →
      ∃ (s : Finset (V × Finset V)) (S' : Finset V),
        PPClosed pp S' ∧
        (∀ p ∈ s, IsRootedPiece pp p.1 p.2) ∧
        (∀ p ∈ s, p.2 ⊆ S) ∧
        (∀ p ∈ s, lam ≤ ((A ∩ p.2).card : ℝ) ∧ ((A ∩ p.2).card : ℝ) < 2 * lam) ∧
        (∀ p ∈ s, ∀ q ∈ s, p ≠ q → Disjoint (p.2.erase p.1) (q.2.erase q.1)) ∧
        ((A ∩ S').card : ℝ) < lam ∧
        (A ∩ S).card ≤ (∑ p ∈ s, (A ∩ p.2).card) + (A ∩ S').card := by
  classical
  have hfix := hforest.1
  have hroot := hforest.2
  intro n
  induction n using Nat.strongRecOn with
  | ind n ih =>
    intro ρ S hS hρS hSsub hn
    by_cases hcount : lam ≤ ((A ∩ S).card : ℝ)
    · obtain ⟨v, C, hvS, hCkids, hpiece, hlow, hhigh⟩ :=
        exists_piece_real hforest A hlam S hS hρS hSsub hcount
      set P : Finset V := S ∩ insert v (C.biUnion (fun c => desc pp c)) with hPdef
      have hPsub : P ⊆ S := Finset.inter_subset_left
      have hPins : P ⊆ insert v (C.biUnion (fun c => desc pp c)) := Finset.inter_subset_right
      have hlowP : lam ≤ ((A ∩ P).card : ℝ) := by
        rw [hPdef, ← Finset.inter_assoc]
        exact hlow
      have hhighP : ((A ∩ P).card : ℝ) < 2 * lam := by
        rw [hPdef, ← Finset.inter_assoc]
        exact hhigh
      -- the piece carries at least two marked vertices
      have hP2 : 2 ≤ (A ∩ P).card := by
        have h2 : (1 : ℝ) < ((A ∩ P).card : ℝ) := lt_of_lt_of_le hlam hlowP
        have h2' : (1 : ℕ) < (A ∩ P).card := by exact_mod_cast h2
        omega
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
      -- the marked count strictly decreases: a piece has a marked vertex off its root
      have hlt : (A ∩ S').card < (A ∩ S).card := by
        have hsub : A ∩ S' ⊆ A ∩ S := fun x hx =>
          Finset.mem_inter.mpr ⟨(Finset.mem_inter.mp hx).1,
            (Finset.mem_sdiff.mp (Finset.mem_inter.mp hx).2).1⟩
        have hex : ∃ x, x ∈ A ∩ S ∧ x ∉ S' := by
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
      obtain ⟨s', S'', hS''closed, h1, h2, h3, h4, h5, h6⟩ :=
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
      refine ⟨insert (v, P) s', S'', hS''closed, ?_, ?_, ?_, ?_, h5, ?_⟩
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
    · -- the region already carries fewer than `lam` marked vertices: nothing to extract
      refine ⟨∅, S, hS, ?_, ?_, ?_, ?_, ?_, ?_⟩
      · simp
      · simp
      · simp
      · simp
      · simpa using not_le.mp hcount
      · simp

end IterateReal

section MainReal

/-- **Tree partition lemma (finite case), real thresholds.**  Let `pp r = r`, let every vertex of
the finite vertex set `V` reach `r` along `pp`, let `lam ≥ 1` be **real** and `k ≥ 1`, and let `A`
be a set of marked vertices with `3^k * lam ≤ #A`.  Then there are at least `3^(k-1)+1` rooted
pieces `(v, P)`, pairwise edge-disjoint (`P.erase v` indexes the parent edges of the piece), each
carrying a number of marked vertices in `[lam, 2*lam)`.

This is the source's Lemma 2.4 count at its own threshold `λ` — the source stresses that `λ`
need not be an integer — in the absolute-threshold form used by (2.10)/(2.11).  Note the strict
upper bound `< 2*lam`; for non-integral `lam` it is strictly weaker than any integer bound
`≤ 2*lam-1`. -/
theorem exists_tree_pieces_real {r : V} (hforest : IsRootedForest pp r)
    (A : Finset V) {lam : ℝ} {k : ℕ} (hlam : 1 ≤ lam) (hk : 1 ≤ k)
    (hA : 3 ^ k * lam ≤ (A.card : ℝ)) :
    ∃ s : Finset (V × Finset V), 3 ^ (k - 1) + 1 ≤ s.card ∧
      (∀ p ∈ s, IsRootedPiece pp p.1 p.2) ∧
      (∀ p ∈ s, lam ≤ ((A ∩ p.2).card : ℝ) ∧ ((A ∩ p.2).card : ℝ) < 2 * lam) ∧
      (∀ p ∈ s, ∀ q ∈ s, p ≠ q → Disjoint (p.2.erase p.1) (q.2.erase q.1)) := by
  classical
  have hroot := hforest.2
  rcases eq_or_lt_of_le hlam with hone | hone
  · -- `lam = 1`: one-vertex pieces already have a count in `[1, 2) = [lam, 2 lam)`
    have h3k : (3 : ℝ) ^ k ≤ (A.card : ℝ) := by
      have h1 : (3 : ℝ) ^ k * 1 ≤ 3 ^ k * lam :=
        mul_le_mul_of_nonneg_left hlam (pow_nonneg (by norm_num) k)
      linarith
    have h3k' : 3 ^ k ≤ A.card := by exact_mod_cast h3k
    have hcard : 3 ^ (k - 1) + 1 ≤ A.card := by
      have h1 : 1 ≤ 3 ^ (k - 1) := Nat.one_le_pow _ _ (by norm_num)
      have h2 : 3 ^ (k - 1) + 1 ≤ 3 ^ k := by
        have h3 : 3 ^ k = 3 ^ (k - 1) * 3 := by
          have h4 : k - 1 + 1 = k := Nat.sub_add_cancel hk
          conv_lhs => rw [← h4]
          rw [pow_succ', Nat.mul_comm]
        omega
      omega
    have hinj : Function.Injective (fun v : V => (v, ({v} : Finset V))) := by
      intro a b hab
      simpa using congrArg Prod.fst hab
    refine ⟨A.image (fun v => (v, ({v} : Finset V))), ?_, ?_, ?_, ?_⟩
    · rw [Finset.card_image_of_injective _ hinj]; exact hcard
    · intro p hp
      obtain ⟨v, -, rfl⟩ := Finset.mem_image.mp hp
      refine ⟨Finset.mem_singleton_self v, ?_, ?_⟩
      · intro x hx hxv
        rw [Finset.mem_singleton] at hx
        exact absurd hx hxv
      · intro x hx
        exact ⟨0, Finset.mem_singleton.mp hx⟩
    · intro p hp
      obtain ⟨v, hv, rfl⟩ := Finset.mem_image.mp hp
      have h1 : (A ∩ ({v} : Finset V)).card = 1 := by
        have h2 : A ∩ ({v} : Finset V) = ({v} : Finset V) := by
          ext x
          simp only [Finset.mem_inter, Finset.mem_singleton]
          exact ⟨fun h => h.2, fun h => ⟨by rw [h]; exact hv, h⟩⟩
        rw [h2, Finset.card_singleton]
      rw [h1, ← hone]
      norm_num
    · intro p hp q hq hpq
      obtain ⟨v, -, rfl⟩ := Finset.mem_image.mp hp
      obtain ⟨w, -, rfl⟩ := Finset.mem_image.mp hq
      have h : v ≠ w := by
        intro hvw
        exact hpq (by rw [hvw])
      simp [h]
  · -- `lam > 1`: prune the region until fewer than `lam` marked vertices remain
    obtain ⟨s, S', -, h1, h2, h3, h4, h5, h6⟩ :=
      exists_pieces_real_aux hforest A hone A.card r (Finset.univ : Finset V)
        (fun _ _ => Finset.mem_univ _) (Finset.mem_univ r)
        (fun x _ => by rw [mem_desc]; exact hroot x) (by simp)
    have htot : 3 ^ k * lam ≤ ((∑ p ∈ s, (A ∩ p.2).card) + (A ∩ S').card : ℕ) := by
      have h6' : ((A ∩ (Finset.univ : Finset V)).card : ℝ) ≤
          (((∑ p ∈ s, (A ∩ p.2).card) + (A ∩ S').card : ℕ) : ℝ) := by
        exact_mod_cast h6
      have h7 : ((A ∩ (Finset.univ : Finset V)).card : ℝ) = (A.card : ℝ) := by
        rw [Finset.inter_univ]
      linarith
    exact ⟨s, count_bound_real s (fun p => (A ∩ p.2).card) hk hlam
      (fun p hp => (h3 p hp).2) h5 htot, h1, h3, h4⟩

end MainReal

/-! ### Percolation level: disjoint open witnesses at a real threshold -/

section PercolationReal

open PercLib.CriticalLRP.Percolation

attribute [local instance] Classical.propDecidable

variable {E : Type*} [DecidableEq E] [Nonempty E]
variable (G : BondGraph V E) (ω : Set E) (r : V)

/-- **Disjoint open witnesses for the `3^k λ`-to-`λ` step at a real threshold.**

Let `Λ` be a finite window, `lam ≥ 1` real and `k ≥ 1`, and suppose the cluster of `r` contains
at least `3^k * lam` vertices of `Λ`.  Then there is a family of at least `3^(k-1)+1` rooted pieces
of the BFS parent tree of the cluster such that

* every piece carries between `lam` and `2*lam` (strictly) marked vertices of the window,
* the parent-edge set `pieceWt v P` of each piece is a set of **open** edges, and these sets are
  **pairwise disjoint**,
* each piece is **connected through its own witness set**, so it certifies, using only its own
  edges, that a cluster meets `Λ` in at least `lam` vertices — with a specific set `t ⊆ Λ` of `≥ λ`
  vertices and a specific centre `u` connected to all of `t`.

The last clause is the pointed-witness form needed for (2.11): the piece containing the root
witnesses the event `{|K_u ∩ Λ| ≥ λ}`, and the others witness `{|Kmax(Λ)| ≥ λ}`.  At a
non-integral `lam` the upper bound `2*lam` is strictly larger than any integer bound
`2*lam - 1`, and the counting is done on the integer marked counts against the real threshold. -/
theorem exists_open_pieces_real (Λ : Finset V) {lam : ℝ} {k : ℕ} (hlam : 1 ≤ lam) (hk : 1 ≤ k)
    (hΛ : 3 ^ k * lam ≤ ((markSet G ω r Λ).card : ℝ)) :
    ∃ s : Finset (Cl G ω r × Finset (Cl G ω r)),
      3 ^ (k - 1) + 1 ≤ s.card ∧
      (∀ p ∈ s, IsRootedPiece (bfsParent G ω r) p.1 p.2) ∧
      (∀ p ∈ s, lam ≤ ((markSet G ω r Λ ∩ p.2).card : ℝ) ∧
        ((markSet G ω r Λ ∩ p.2).card : ℝ) < 2 * lam) ∧
      (∀ p ∈ s, (pieceWt G ω r p.1 p.2 : Set E) ⊆ ω) ∧
      (∀ p ∈ s, ∀ q ∈ s, p ≠ q →
        Disjoint (pieceWt G ω r p.1 p.2) (pieceWt G ω r q.1 q.2)) ∧
      (∀ p ∈ s, ∃ t : Finset V, t ⊆ Λ ∧ lam ≤ (t.card : ℝ) ∧ ∃ u : V, ∀ y ∈ t,
        Conn G ((pieceWt G ω r p.1 p.2 : Finset E) : Set E) u y) := by
  classical
  obtain ⟨s, hcard, hpiece, hmark, hdisj⟩ :=
    exists_tree_pieces_real (bfsParent_isRootedForest G ω r) (markSet G ω r Λ) hlam hk hΛ
  refine ⟨s, hcard, hpiece, hmark, ?_, ?_, ?_⟩
  · intro p hp
    exact pieceWt_subset G ω r (hpiece p hp)
  · intro p hp q hq hpq
    exact pieceWt_disjoint G ω r (hdisj p hp q hq hpq) (hpiece p hp) (hpiece q hq)
  · intro p hp
    obtain ⟨v, P⟩ := p
    have hP : IsRootedPiece (bfsParent G ω r) v P := hpiece _ hp
    have hpos : 0 < (markSet G ω r Λ ∩ P).card := by
      have h1 : (1 : ℝ) ≤ ((markSet G ω r Λ ∩ P).card : ℝ) := le_trans hlam (hmark _ hp).1
      have h1' : (1 : ℕ) ≤ (markSet G ω r Λ ∩ P).card := by exact_mod_cast h1
      omega
    have hne' : (markSet G ω r Λ ∩ P).Nonempty := Finset.card_pos.mp hpos
    obtain ⟨u, hu⟩ := hne'
    have huP : u ∈ P := (Finset.mem_inter.mp hu).2
    refine ⟨(markSet G ω r Λ ∩ P).image (Subtype.val : Cl G ω r → V), ?_, ?_, u, ?_⟩
    · intro y hy
      obtain ⟨a, ha, rfl⟩ := Finset.mem_image.mp hy
      exact (mem_markSet G ω r).mp (Finset.mem_inter.mp ha).1
    · rw [Finset.card_image_of_injective _ (fun a b h => Subtype.ext h)]
      exact (hmark _ hp).1
    · intro y hy
      obtain ⟨a, ha, rfl⟩ := Finset.mem_image.mp hy
      exact piece_conn_pieceWt G ω r hP huP (Finset.mem_inter.mp ha).2

end PercolationReal


/-! ### A distinguished root-spine piece at a real threshold -/

section RootSpineReal

variable {pp : V → V} {r : V}

/-- The real tree partition, with one chosen piece enlarged to a rooted piece at the common root.
The spine keeps the real lower marked-count bound and is disjoint from all other piece cores. -/
theorem exists_root_spine_pieces_real {A : Finset V} {lam : ℝ} {k : ℕ}
    (hforest : IsRootedForest pp r) (hlam : 1 ≤ lam) (hk : 1 ≤ k)
    (hA : 3 ^ k * lam ≤ (A.card : ℝ)) :
    ∃ (s : Finset (V × Finset V)) (j : V × Finset V) (Q : Finset V),
      3 ^ (k - 1) + 1 ≤ s.card ∧ j ∈ s ∧
      (∀ p ∈ s, IsRootedPiece pp p.1 p.2) ∧
      (∀ p ∈ s, lam ≤ ((A ∩ p.2).card : ℝ) ∧ ((A ∩ p.2).card : ℝ) < 2 * lam) ∧
      (∀ p ∈ s, ∀ q ∈ s, p ≠ q → Disjoint (p.2.erase p.1) (q.2.erase q.1)) ∧
      IsRootedPiece pp r Q ∧ j.2 ⊆ Q ∧ lam ≤ ((A ∩ Q).card : ℝ) ∧
      (∀ q ∈ s, q ≠ j → Disjoint (Q.erase r) (q.2.erase q.1)) := by
  classical
  obtain ⟨s, hcard, hpiece, hmark, hdisj⟩ :=
    exists_tree_pieces_real hforest A hlam hk hA
  have hne : s.Nonempty := by
    rw [Finset.nonempty_iff_ne_empty]
    intro he
    rw [he] at hcard
    simp at hcard
  have hmark1 : ∀ p ∈ s, 1 ≤ (A ∩ p.2).card := by
    intro p hp
    have h : (1 : ℝ) ≤ ((A ∩ p.2).card : ℝ) := hlam.trans (hmark p hp).1
    exact_mod_cast h
  obtain ⟨j, hjs, Q, hQpiece, hjsub, hQmark, hQdisj⟩ :=
    exists_root_spine_piece_of_root hforest.2 hforest.1 s hne hpiece hdisj hmark1
  refine ⟨s, j, Q, hcard, hjs, hpiece, hmark, hdisj, hQpiece, hjsub, ?_, hQdisj⟩
  have hsub : A ∩ j.2 ⊆ A ∩ Q := by
    intro x hx
    exact Finset.mem_inter.mpr ⟨(Finset.mem_inter.mp hx).1, hjsub (Finset.mem_inter.mp hx).2⟩
  have hc := Finset.card_le_card hsub
  have hc' : (((A ∩ j.2).card : ℕ) : ℝ) ≤ ((A ∩ Q).card : ℝ) := by exact_mod_cast hc
  exact (hmark j hjs).1.trans hc'

end RootSpineReal

/-! ### Consistency with the integer-threshold statement

The real-threshold theorem must not lose the repository's integer result
(`Tightness/TreePieces.lean`, `exists_tree_pieces`): at integral `lam ≥ 2` it recovers it, with the
strict real bound `count < 2*lam` converted back to `count ≤ 2*lam-1` by integrality of the count. -/

section Consistency

variable {pp : V → V}

/-- **The integer-threshold tree partition follows from the real-threshold one.**  This is a
statement-fidelity check: the real-threshold lemma is a genuine generalisation of the repository's
integer lemma at `lam ≥ 2`, with the same number `3^(k-1)+1` of pieces and the same
edge-disjointness. -/
theorem exists_tree_pieces_of_real {r : V} (hforest : IsRootedForest pp r)
    (A : Finset V) {lam k : ℕ} (hlam : 2 ≤ lam) (hk : 1 ≤ k)
    (hA : 3 ^ k * lam ≤ A.card) :
    ∃ s : Finset (V × Finset V), 3 ^ (k - 1) + 1 ≤ s.card ∧
      (∀ p ∈ s, IsRootedPiece pp p.1 p.2) ∧
      (∀ p ∈ s, lam ≤ (A ∩ p.2).card ∧ (A ∩ p.2).card ≤ 2 * lam - 1) ∧
      (∀ p ∈ s, ∀ q ∈ s, p ≠ q → Disjoint (p.2.erase p.1) (q.2.erase q.1)) := by
  classical
  have hlam1 : (1 : ℝ) ≤ (lam : ℝ) := by
    have : (1 : ℕ) ≤ lam := le_trans (by norm_num) hlam
    exact_mod_cast this
  have hA' : 3 ^ k * (lam : ℝ) ≤ ((A.card : ℕ) : ℝ) := by
    have : 3 ^ k * (lam : ℝ) = ((3 ^ k * lam : ℕ) : ℝ) := by push_cast; ring
    rw [this]
    exact_mod_cast hA
  obtain ⟨s, h1, h2, h3, h4⟩ := exists_tree_pieces_real hforest A hlam1 hk hA'
  refine ⟨s, h1, h2, ?_, h4⟩
  intro p hp
  obtain ⟨hl, hu⟩ := h3 p hp
  refine ⟨?_, ?_⟩
  · exact_mod_cast hl
  · have hu' : (A ∩ p.2).card < 2 * lam := by
      have h2' : ((A ∩ p.2).card : ℝ) < ((2 * lam : ℕ) : ℝ) := by
        push_cast
        exact hu
      exact_mod_cast h2'
    omega

end Consistency
