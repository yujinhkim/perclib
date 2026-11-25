/-
Copyright (c) 2026 PercLib contributors. Released under Apache 2.0.
New proofs, written for package Q-72 (issue 379), on the D-2 interface and the rooted-tree
conventions of `PercLib.Models.Tree`, using mathlib's `BinaryTree.treesOfNumNodesEq` and
`catalan`. No source text or code is copied.
-/
module

public import PercLib.Models.Tree
public import PercLib.Percolation.Bond.ClusterLaw
public import PercLib.Probability.FiniteEnergy.Insertion
public import Mathlib.Combinatorics.Enumerative.Catalan.Tree
public import Mathlib.Combinatorics.Enumerative.Catalan.Basic

/-!
# Bond percolation on the rooted binary tree: the Catalan law of the root cluster

Vertices are words `List (Fin 2)`, the root is `[]`, the parent of `w` is `w.tail`, and the
profile is `p` on tree edges and `0` on other pairs (any value on the diagonal). For every
`n ≥ 1` and `p ∈ [0, 1]`,

`P(|K([])| = n, K([]) finite) = (1/(n+1)) · C(2n, n) · p^(n-1) · (1 - p)^(n+1)`

(`binaryTree_law_cluster_card_eq`; the Catalan form is `binaryTree_law_cluster_card_eq_catalan`).

A finite root cluster is a finite set `C` of words that contains `[]` and is closed under
`tail`; it is the root cluster exactly when its `n - 1` edges `s(w.tail, w)` are open and its
`n + 1` boundary edges `s(w, b :: w)`, `b :: w ∉ C`, are closed. Such sets with `n`
elements correspond to binary trees with `n` nodes: a tree `node l r` gives `[]` together
with the words of `l` followed by `0` and those of `r` followed by `1`.

This file adds no definition.
-/

@[expose] public section
noncomputable section

open MeasureTheory Set PercLib.Probability PercLib.Percolation.Bond
open scoped ENNReal

namespace PercLib.Models

/-! ### Tail-closed sets of words and binary trees -/

private theorem drop_mem_of_tail_closed {C : Finset (List (Fin 2))}
    (hC : ∀ w ∈ C, w.tail ∈ C) {w : List (Fin 2)} (hw : w ∈ C) (m : ℕ) : w.drop m ∈ C := by
  induction m with
  | zero => simpa using hw
  | succ m ih =>
    have := hC _ ih
    rwa [List.tail_drop] at this

private theorem nil_mem_of_tail_closed {C : Finset (List (Fin 2))}
    (hC : ∀ w ∈ C, w.tail ∈ C) (hne : C.Nonempty) : [] ∈ C := by
  obtain ⟨w, hw⟩ := hne
  simpa using drop_mem_of_tail_closed hC hw w.length

private theorem append_singleton_ne_nil (u : List (Fin 2)) (b : Fin 2) : u ++ [b] ≠ [] := by
  simp

private theorem append_singleton_inj {u v : List (Fin 2)} {a b : Fin 2}
    (h : u ++ [a] = v ++ [b]) : u = v ∧ a = b := by
  have := List.append_inj' h rfl
  exact ⟨this.1, by simpa using this.2⟩

private theorem tail_append_singleton (u : List (Fin 2)) (b : Fin 2) :
    (u ++ [b]).tail = if u = [] then [] else u.tail ++ [b] := by
  rcases u with _ | ⟨c, u⟩ <;> simp

/-- The finite sets built from binary trees. -/
private theorem tree_sets (φ : BinaryTree Unit → Finset (List (Fin 2)))
    (hnil : φ .nil = ∅)
    (hnode : ∀ a l r, φ (.node a l r) =
      insert [] ((φ l).image (· ++ [0]) ∪ (φ r).image (· ++ [1]))) :
    (∀ t, (φ t).card = t.numNodes) ∧ Function.Injective φ ∧
      (∀ t, ∀ w ∈ φ t, w.tail ∈ φ t) ∧
      (∀ C : Finset (List (Fin 2)), (∀ w ∈ C, w.tail ∈ C) → ∃ t, φ t = C) := by
  classical
  -- membership of `u ++ [b]` in a node
  have hmem : ∀ a l r (u : List (Fin 2)) (b : Fin 2),
      u ++ [b] ∈ φ (.node a l r) ↔ (b = 0 ∧ u ∈ φ l) ∨ (b = 1 ∧ u ∈ φ r) := by
    intro a l r u b
    rw [hnode]
    simp only [Finset.mem_insert, Finset.mem_union, Finset.mem_image]
    constructor
    · rintro (h | ⟨v, hv, h⟩ | ⟨v, hv, h⟩)
      · exact absurd h (append_singleton_ne_nil u b)
      · obtain ⟨rfl, rfl⟩ := append_singleton_inj h
        exact Or.inl ⟨rfl, hv⟩
      · obtain ⟨rfl, rfl⟩ := append_singleton_inj h
        exact Or.inr ⟨rfl, hv⟩
    · rintro (⟨rfl, h⟩ | ⟨rfl, h⟩)
      · exact Or.inr (Or.inl ⟨u, h, rfl⟩)
      · exact Or.inr (Or.inr ⟨u, h, rfl⟩)
  have hnilmem : ∀ a l r, [] ∈ φ (.node a l r) := fun a l r => by
    rw [hnode]; exact Finset.mem_insert_self _ _
  refine ⟨?_, ?_, ?_, ?_⟩
  · intro t
    induction t with
    | nil => simp [hnil]
    | node a l r hl hr =>
      rw [hnode, Finset.card_insert_of_notMem, Finset.card_union_of_disjoint,
        Finset.card_image_of_injective _ (List.append_left_injective [0]),
        Finset.card_image_of_injective _ (List.append_left_injective [1]), hl, hr,
        BinaryTree.numNodes]
      · rw [Finset.disjoint_left]
        intro w h1 h2
        obtain ⟨u, -, rfl⟩ := Finset.mem_image.1 h1
        obtain ⟨v, -, h⟩ := Finset.mem_image.1 h2
        have := (append_singleton_inj h).2
        exact absurd this (by decide)
      · simp only [Finset.mem_union, Finset.mem_image, not_or, not_exists, not_and]
        exact ⟨fun u _ => append_singleton_ne_nil u 0, fun u _ => append_singleton_ne_nil u 1⟩
  · intro t₁
    induction t₁ with
    | nil =>
      intro t₂ h
      cases t₂ with
      | nil => rfl
      | node a l r =>
        have := hnilmem a l r
        rw [← h, hnil] at this
        simp at this
    | node a l r hl hr =>
      intro t₂ h
      cases t₂ with
      | nil =>
        have := hnilmem a l r
        rw [h, hnil] at this
        simp at this
      | node a' l' r' =>
        have ha : a = a' := rfl
        have hl' : φ l = φ l' := by
          ext u
          have h1 := hmem a l r u 0
          have h2 := hmem a' l' r' u 0
          rw [h] at h1
          simp only [true_and, Fin.zero_eq_one_iff, OfNat.ofNat_ne_one, false_and,
            or_false] at h1 h2
          rw [← h1, h2]
        have hr' : φ r = φ r' := by
          ext u
          have h1 := hmem a l r u 1
          have h2 := hmem a' l' r' u 1
          rw [h] at h1
          simp only [Fin.one_eq_zero_iff, OfNat.ofNat_ne_one, false_and, true_and,
            false_or] at h1 h2
          rw [← h1, h2]
        rw [ha, hl hl', hr hr']
  · intro t
    induction t with
    | nil => simp [hnil]
    | node a l r hl hr =>
      intro w hw
      rw [hnode] at hw
      rcases Finset.mem_insert.1 hw with rfl | hw
      · exact hnilmem a l r
      · rcases Finset.mem_union.1 hw with h | h <;>
        · obtain ⟨u, hu, rfl⟩ := Finset.mem_image.1 h
          rw [tail_append_singleton]
          split_ifs with hu0
          · exact hnilmem a l r
          · rw [hnode]
            first
            | exact Finset.mem_insert_of_mem (Finset.mem_union_left _
                (Finset.mem_image_of_mem _ (hl u hu)))
            | exact Finset.mem_insert_of_mem (Finset.mem_union_right _
                (Finset.mem_image_of_mem _ (hr u hu)))
  · intro C
    induction hn : C.card using Nat.strong_induction_on generalizing C with
    | _ n ih =>
    intro hC
    rcases Finset.eq_empty_or_nonempty C with rfl | hne
    · exact ⟨.nil, hnil⟩
    have h0 : [] ∈ C := nil_mem_of_tail_closed hC hne
    set L := C.preimage (· ++ [0]) (List.append_left_injective [0]).injOn with hL
    set R := C.preimage (· ++ [1]) (List.append_left_injective [1]).injOn with hR
    have hclosed : ∀ b : Fin 2, ∀ u ∈ C.preimage (· ++ [b]) (List.append_left_injective [b]).injOn,
        u.tail ∈ C.preimage (· ++ [b]) (List.append_left_injective [b]).injOn := by
      intro b u hu
      rw [Finset.mem_preimage] at hu ⊢
      by_cases hu0 : u = []
      · subst hu0; simpa using hu
      · have := hC _ hu
        rw [tail_append_singleton] at this
        simpa [hu0] using this
    have hsub : ∀ b : Fin 2,
        (C.preimage (· ++ [b]) (List.append_left_injective [b]).injOn).image (· ++ [b]) ⊆
          C.erase [] := by
      intro b w hw
      obtain ⟨u, hu, rfl⟩ := Finset.mem_image.1 hw
      exact Finset.mem_erase.2 ⟨append_singleton_ne_nil u b,
        (Finset.mem_preimage (f := fun x => x ++ [b])).1 hu⟩
    have hcardb : ∀ b : Fin 2,
        (C.preimage (· ++ [b]) (List.append_left_injective [b]).injOn).card < n := by
      intro b
      have := Finset.card_le_card (hsub b)
      rw [Finset.card_image_of_injective _ (List.append_left_injective [b]),
        Finset.card_erase_of_mem h0] at this
      have hpos := Finset.card_pos.2 hne
      have hCn : C.card = n := hn
      omega
    have hcardL : L.card < n := hcardb 0
    have hcardR : R.card < n := hcardb 1
    obtain ⟨tl, htl⟩ := ih _ hcardL L rfl (hclosed 0)
    obtain ⟨tr, htr⟩ := ih _ hcardR R rfl (hclosed 1)
    refine ⟨.node () tl tr, ?_⟩
    rw [hnode, htl, htr]
    ext w
    simp only [Finset.mem_insert, Finset.mem_union, Finset.mem_image, hL, hR,
      Finset.mem_preimage]
    constructor
    · rintro (rfl | ⟨u, hu, rfl⟩ | ⟨u, hu, rfl⟩)
      · exact h0
      · exact hu
      · exact hu
    · intro hw
      by_cases hw0 : w = []
      · exact Or.inl hw0
      · right
        have hdec := (List.dropLast_append_getLast hw0).symm
        rcases Fin.exists_fin_two.1 ⟨w.getLast hw0, rfl⟩ with hb | hb
        · left
          refine ⟨w.dropLast, ?_, ?_⟩
          · rw [hb] at hdec; rw [← hdec]; exact hw
          · rw [hb] at hdec; exact hdec.symm
        · right
          refine ⟨w.dropLast, ?_, ?_⟩
          · rw [hb] at hdec; rw [← hdec]; exact hw
          · rw [hb] at hdec; exact hdec.symm

/-! ### The root cluster equal to a tail-closed set -/

/-- For a configuration of tree edges and a tail-closed `C` containing the root, the root
cluster is `C` exactly when the edges inside `C` are open and the boundary edges are
closed. -/
theorem cluster_nil_eq_iff_of_subset {ω : Config (List (Fin 2))}
    (hω : ω ⊆ (SimpleGraph.fromRel fun u w : List (Fin 2) => ∃ b, w = b :: u).edgeSet)
    {C : Finset (List (Fin 2))} (h0 : [] ∈ C) (hC : ∀ w ∈ C, w.tail ∈ C) :
    cluster ω [] = (C : Set (List (Fin 2))) ↔
      (∀ w ∈ C, w ≠ [] → s(w.tail, w) ∈ ω) ∧ (∀ w ∈ C, ∀ b, b :: w ∉ C → s(w, b :: w) ∉ ω) := by
  have hmemK : ∀ w, w ∈ cluster ω [] ↔ ∀ m < w.length, s(w.drop (m + 1), w.drop m) ∈ ω :=
    fun w => reachable_nil_iff_of_subset hω w
  constructor
  · intro hK
    refine ⟨fun w hw hw0 => ?_, fun w hw b hb hω' => ?_⟩
    · have hwK : w ∈ cluster ω [] := by rw [hK]; exact hw
      have := (hmemK w).1 hwK 0 (List.length_pos_iff.2 hw0)
      simpa using this
    · have hwK : w ∈ cluster ω [] := by rw [hK]; exact hw
      have hadj : (openGraph ω).Adj w (b :: w) := (openGraph_adj_iff ω w (b :: w)).2
        ⟨hω', fun h => by have := congrArg List.length h; simp at this⟩
      have : b :: w ∈ cluster ω [] := SimpleGraph.Reachable.trans hwK hadj.reachable
      rw [hK] at this
      exact hb this
  · rintro ⟨hint, hbd⟩
    ext w
    rw [hmemK]
    constructor
    · intro h
      induction w with
      | nil => exact h0
      | cons b u ih =>
        have hu : u ∈ C := ih fun m hm => by simpa using h (m + 1) (by simp; omega)
        by_contra hbu
        exact hbd u hu b hbu (by simpa using h 0 (by simp))
    · intro hw m hm
      have hdm := drop_mem_of_tail_closed hC hw m
      have hne : w.drop m ≠ [] := by
        rw [Ne, List.drop_eq_nil_iff]; omega
      have := hint _ hdm hne
      rwa [List.tail_drop] at this

/-! ### The probability of one cluster shape -/

/-- **One cluster shape.** For a tail-closed `C` with `n ≥ 1` elements,
`P(K([]) = C) = p^(n-1) (1-p)^(n+1)`. -/
theorem binaryTree_law_cluster_eq (p : unitInterval) (q : Sym2 (List (Fin 2)) → unitInterval)
    (hq : ∀ e, ¬ e.IsDiag → q e =
      if e ∈ (SimpleGraph.fromRel fun u w : List (Fin 2) => ∃ b, w = b :: u).edgeSet then p
        else 0)
    {C : Finset (List (Fin 2))} (h0 : [] ∈ C) (hC : ∀ w ∈ C, w.tail ∈ C) :
    law q {ω | cluster ω [] = (C : Set (List (Fin 2)))} =
      (unitInterval.toNNReal p : ℝ≥0∞) ^ (C.card - 1) *
        (unitInterval.toNNReal (unitInterval.symm p) : ℝ≥0∞) ^ (C.card + 1) := by
  classical
  set G := SimpleGraph.fromRel fun u w : List (Fin 2) => ∃ b, w = b :: u
  set q₀ : Sym2 (List (Fin 2)) → unitInterval := fun e => if e ∈ G.edgeSet then p else 0
  have hdiag : law q {ω | cluster ω [] = (C : Set (List (Fin 2)))} =
      law q₀ {ω | cluster ω [] = (C : Set (List (Fin 2)))} := by
    refine law_event_eq_of_offDiagonal q q₀ (fun e he => hq e he)
      (measurableSet_cluster_eq_finset [] C h0) fun ω ω' h => ?_
    simp only [mem_ofPred_eq, cluster]
    rw [← openGraph_sdiff_diagSet ω, h, openGraph_sdiff_diagSet]
  rw [hdiag]
  have hsupp : ∀ᵐ ω ∂law q₀, ω ⊆ G.edgeSet :=
    ae_config_subset_host G q₀ fun e he => by simp [q₀, he]
  -- the interior and boundary edges
  set I : Finset (Sym2 (List (Fin 2))) := (C.erase []).image fun w => s(w.tail, w) with hI
  set P : Finset (List (Fin 2) × Fin 2) :=
    (C ×ˢ (Finset.univ : Finset (Fin 2))).filter fun x => x.2 :: x.1 ∉ C with hP
  set D : Finset (Sym2 (List (Fin 2))) := P.image fun x => s(x.1, x.2 :: x.1) with hD
  have hlen : ∀ {u v : List (Fin 2)}, u = v → u.length = v.length := fun h => h ▸ rfl
  have hIcard : I.card = C.card - 1 := by
    rw [hI, Finset.card_image_of_injOn, Finset.card_erase_of_mem h0]
    intro w hw v hv hwv
    have hw0 := (Finset.mem_erase.1 hw).1
    have hv0 := (Finset.mem_erase.1 hv).1
    rcases Sym2.eq_iff.1 hwv with ⟨_, h⟩ | ⟨h1, h2⟩
    · exact h
    · have e1 := hlen h1
      have e2 := hlen h2
      simp only [List.length_tail] at e1 e2
      have := List.length_pos_iff.2 hw0
      have := List.length_pos_iff.2 hv0
      omega
  have hDcard : D.card = C.card + 1 := by
    rw [hD, Finset.card_image_of_injOn]
    · have hsplit := Finset.card_filter_add_card_filter_not
        (s := C ×ˢ (Finset.univ : Finset (Fin 2))) (p := fun x => x.2 :: x.1 ∈ C)
      rw [Finset.card_product, Finset.card_univ, Fintype.card_fin] at hsplit
      have hin : ((C ×ˢ (Finset.univ : Finset (Fin 2))).filter
          fun x => x.2 :: x.1 ∈ C).card = C.card - 1 := by
        rw [← Finset.card_erase_of_mem h0]
        refine Finset.card_bij (fun x _ => x.2 :: x.1) ?_ ?_ ?_
        · intro x hx
          exact Finset.mem_erase.2 ⟨List.cons_ne_nil _ _, (Finset.mem_filter.1 hx).2⟩
        · intro x hx y hy hxy
          obtain ⟨h1, h2⟩ := List.cons_eq_cons.1 hxy
          exact Prod.ext h2 h1
        · intro w hw
          obtain ⟨hw0, hwC⟩ := Finset.mem_erase.1 hw
          obtain ⟨b, u, rfl⟩ := List.exists_cons_of_ne_nil hw0
          refine ⟨(u, b), Finset.mem_filter.2 ⟨Finset.mem_product.2 ⟨?_, Finset.mem_univ _⟩,
            hwC⟩, rfl⟩
          simpa using hC _ hwC
      have hpos : 1 ≤ C.card := Finset.card_pos.2 ⟨_, h0⟩
      rw [hP]
      omega
    · intro x _ y _ hxy
      rcases Sym2.eq_iff.1 hxy with ⟨h1, h2⟩ | ⟨h1, h2⟩
      · obtain ⟨h3, -⟩ := List.cons_eq_cons.1 h2
        exact Prod.ext h1 h3
      · have e1 := hlen h1
        have e2 := hlen h2
        simp only [List.length_cons] at e1 e2
        omega
  have hdisj : Disjoint I D := by
    rw [Finset.disjoint_left]
    intro e heI heD
    obtain ⟨w, hw, rfl⟩ := Finset.mem_image.1 heI
    obtain ⟨x, hx, hxe⟩ := Finset.mem_image.1 heD
    obtain ⟨hxC, hxn⟩ := Finset.mem_filter.1 hx
    rcases Sym2.eq_iff.1 hxe with ⟨h1, h2⟩ | ⟨h1, h2⟩
    · exact hxn (h2 ▸ (Finset.mem_erase.1 hw).2)
    · have e1 := hlen h1
      have e2 := hlen h2
      simp only [List.length_cons, List.length_tail] at e1 e2
      omega
  -- the cluster event is a.s. a finite pattern
  have hpat : law q₀ {ω | cluster ω [] = (C : Set (List (Fin 2)))} =
      law q₀ {ω : Config (List (Fin 2)) | ω ∩ ((I ∪ D : Finset _) : Set _) = (I : Set _)} := by
    refine measure_congr ?_
    filter_upwards [hsupp] with ω hω
    refine propext ?_
    show cluster ω [] = (C : Set (List (Fin 2))) ↔ ω ∩ ((I ∪ D : Finset _) : Set _) = (I : Set _)
    rw [cluster_nil_eq_iff_of_subset hω h0 hC]
    have hI' : (∀ w ∈ C, w ≠ [] → s(w.tail, w) ∈ ω) ↔ ∀ e ∈ I, e ∈ ω := by
      constructor
      · intro h e he
        obtain ⟨w, hw, rfl⟩ := Finset.mem_image.1 he
        exact h w (Finset.mem_erase.1 hw).2 (Finset.mem_erase.1 hw).1
      · intro h w hw hw0
        exact h _ (Finset.mem_image.2 ⟨w, Finset.mem_erase.2 ⟨hw0, hw⟩, rfl⟩)
    have hD' : (∀ w ∈ C, ∀ b, b :: w ∉ C → s(w, b :: w) ∉ ω) ↔ ∀ e ∈ D, e ∉ ω := by
      constructor
      · intro h e he
        obtain ⟨x, hx, rfl⟩ := Finset.mem_image.1 he
        obtain ⟨hxC, hxn⟩ := Finset.mem_filter.1 hx
        exact h x.1 (Finset.mem_product.1 hxC).1 x.2 hxn
      · intro h w hw b hb
        exact h _ (Finset.mem_image.2 ⟨(w, b), Finset.mem_filter.2
          ⟨Finset.mem_product.2 ⟨hw, Finset.mem_univ _⟩, hb⟩, rfl⟩)
    rw [hI', hD']
    constructor
    · rintro ⟨hi, hd⟩
      ext e
      simp only [Set.mem_inter_iff, Finset.coe_union, Set.mem_union, Finset.mem_coe]
      constructor
      · rintro ⟨heω, heI | heD⟩
        · exact heI
        · exact absurd heω (hd e heD)
      · intro heI
        exact ⟨hi e heI, Or.inl heI⟩
    · intro h
      refine ⟨fun e he => ?_, fun e he heω => ?_⟩
      · have : e ∈ (I : Set _) := he
        rw [← h] at this
        exact this.1
      · have : e ∈ ω ∩ ((I ∪ D : Finset _) : Set _) :=
          ⟨heω, by simp only [Finset.coe_union, Set.mem_union, Finset.mem_coe]; exact Or.inr he⟩
        rw [h] at this
        exact Finset.disjoint_left.1 hdisj this he
  rw [hpat]
  have hpat2 := prodBernoulli_inter_pattern q₀ (I ∪ D) I Finset.subset_union_left Set.univ
    MeasurableSet.univ (fun _ _ _ => Iff.rfl)
  rw [Set.univ_inter] at hpat2
  change prodBernoulli q₀ _ = _
  rw [hpat2, measure_univ, one_mul, Finset.union_sdiff_left,
    Finset.sdiff_eq_self_of_disjoint hdisj.symm]
  have hIval : ∀ e ∈ I, (unitInterval.toNNReal (q₀ e) : ℝ≥0∞) =
      (unitInterval.toNNReal p : ℝ≥0∞) := by
    intro e he
    obtain ⟨w, hw, rfl⟩ := Finset.mem_image.1 he
    obtain ⟨b, u, rfl⟩ := List.exists_cons_of_ne_nil (Finset.mem_erase.1 hw).1
    have hedge : s((b :: u).tail, b :: u) ∈ G.edgeSet := by
      rw [SimpleGraph.mem_edgeSet, kTree_adj_iff]
      exact Or.inl ⟨b, rfl⟩
    simp only [q₀, hedge, ite_true]
  have hDval : ∀ e ∈ D, (unitInterval.toNNReal (unitInterval.symm (q₀ e)) : ℝ≥0∞) =
      (unitInterval.toNNReal (unitInterval.symm p) : ℝ≥0∞) := by
    intro e he
    obtain ⟨x, -, rfl⟩ := Finset.mem_image.1 he
    have hedge : s(x.1, x.2 :: x.1) ∈ G.edgeSet := by
      rw [SimpleGraph.mem_edgeSet, kTree_adj_iff]
      exact Or.inl ⟨x.2, rfl⟩
    simp only [q₀, hedge, ite_true]
  rw [Finset.prod_congr rfl hIval, Finset.prod_congr rfl hDval, Finset.prod_const,
    Finset.prod_const, hIcard, hDcard]

/-! ### The Catalan law -/

/-- **The Catalan law of the finite root cluster**, Catalan form: for `n ≥ 1`,
`P(|K([])| = n, K([]) finite) = Cat(n) · p^(n-1) · (1-p)^(n+1)`. -/
theorem binaryTree_law_cluster_card_eq_catalan (p : unitInterval)
    (q : Sym2 (List (Fin 2)) → unitInterval)
    (hq : ∀ e, ¬ e.IsDiag → q e =
      if e ∈ (SimpleGraph.fromRel fun u w : List (Fin 2) => ∃ b, w = b :: u).edgeSet then p
        else 0)
    {n : ℕ} (hn : 1 ≤ n) :
    law q {ω | (cluster ω []).ncard = n ∧ (cluster ω []).Finite} =
      (catalan n : ℝ≥0∞) * (unitInterval.toNNReal p : ℝ≥0∞) ^ (n - 1) *
        (unitInterval.toNNReal (unitInterval.symm p) : ℝ≥0∞) ^ (n + 1) := by
  classical
  set G := SimpleGraph.fromRel fun u w : List (Fin 2) => ∃ b, w = b :: u
  set q₀ : Sym2 (List (Fin 2)) → unitInterval := fun e => if e ∈ G.edgeSet then p else 0
  -- the event as a disjoint union over finite sets
  have hunion : {ω : Config (List (Fin 2)) | (cluster ω []).ncard = n ∧ (cluster ω []).Finite} =
      ⋃ C : Finset (List (Fin 2)),
        {ω : Config (List (Fin 2)) | C.card = n ∧ cluster ω [] = (C : Set (List (Fin 2)))} := by
    ext ω
    simp only [Set.mem_ofPred_eq, Set.mem_iUnion]
    constructor
    · rintro ⟨hc, hfin⟩
      refine ⟨hfin.toFinset, ?_, by simp⟩
      rw [← hc, Set.ncard_eq_toFinset_card _ hfin]
    · rintro ⟨C, hc, hK⟩
      rw [hK]
      exact ⟨by rw [Set.ncard_coe_finset, hc], C.finite_toSet⟩
  have hmeas : ∀ C : Finset (List (Fin 2)), MeasurableSet
      {ω : Config (List (Fin 2)) | C.card = n ∧ cluster ω [] = (C : Set (List (Fin 2)))} := by
    intro C
    by_cases h0 : [] ∈ C
    · have : {ω : Config (List (Fin 2)) | C.card = n ∧ cluster ω [] = (C : Set (List (Fin 2)))} =
          {_ω | C.card = n} ∩ {ω | cluster ω [] = (C : Set (List (Fin 2)))} := rfl
      rw [this]
      exact (MeasurableSet.const _).inter (measurableSet_cluster_eq_finset [] C h0)
    · have : {ω : Config (List (Fin 2)) | C.card = n ∧ cluster ω [] = (C : Set (List (Fin 2)))} =
          ∅ := by
        apply Set.eq_empty_of_forall_notMem
        rintro ω ⟨-, hK⟩
        have := mem_cluster_self ω ([] : List (Fin 2))
        rw [hK] at this
        exact h0 this
      rw [this]; exact MeasurableSet.empty
  have hdisj : Pairwise (Function.onFun Disjoint fun C : Finset (List (Fin 2)) =>
      {ω : Config (List (Fin 2)) | C.card = n ∧ cluster ω [] = (C : Set (List (Fin 2)))}) := by
    intro C C' hCC'
    rw [Function.onFun, Set.disjoint_left]
    rintro ω ⟨-, h1⟩ ⟨-, h2⟩
    exact hCC' (Finset.coe_injective (h1.symm.trans h2))
  rw [hunion, measure_iUnion hdisj hmeas]
  -- the binary trees
  obtain ⟨φ, hnil, hnode⟩ : ∃ φ : BinaryTree Unit → Finset (List (Fin 2)), φ .nil = ∅ ∧
      ∀ a l r, φ (.node a l r) =
        insert [] ((φ l).image (· ++ [0]) ∪ (φ r).image (· ++ [1])) :=
    ⟨fun t => BinaryTree.rec (motive := fun _ => Finset (List (Fin 2))) ∅
      (fun _ _ _ fl fr => insert [] (fl.image (· ++ [0]) ∪ fr.image (· ++ [1]))) t,
      rfl, fun _ _ _ => rfl⟩
  obtain ⟨hφcard, hφinj, hφclosed, hφsurj⟩ := tree_sets φ hnil hnode
  set T := (BinaryTree.treesOfNumNodesEq n).image φ with hT
  -- terms outside `T` vanish
  have hzero : ∀ C ∉ T, law q {ω : Config (List (Fin 2)) |
      C.card = n ∧ cluster ω [] = (C : Set (List (Fin 2)))} = 0 := by
    intro C hC
    by_cases hcard : C.card = n
    · by_cases hcl : ∀ w ∈ C, w.tail ∈ C
      · exfalso
        obtain ⟨t, rfl⟩ := hφsurj C hcl
        exact hC (Finset.mem_image.2 ⟨t, BinaryTree.mem_treesOfNumNodesEq.2
          (by rw [← hφcard]; exact hcard), rfl⟩)
      · -- a.s. the root cluster is tail-closed
        push Not at hcl
        obtain ⟨w, hwC, hwt⟩ := hcl
        have hdiag : law q {ω : Config (List (Fin 2)) |
            C.card = n ∧ cluster ω [] = (C : Set (List (Fin 2)))} ≤
            law q {ω : Config (List (Fin 2)) | cluster ω [] = (C : Set (List (Fin 2)))} :=
          measure_mono fun ω h => h.2
        refine le_antisymm (hdiag.trans ?_) zero_le
        by_cases h0 : [] ∈ C
        · rw [law_event_eq_of_offDiagonal q q₀ (fun e he => hq e he)
            (measurableSet_cluster_eq_finset [] C h0) fun ω ω' h => by
              simp only [mem_ofPred_eq, cluster]
              rw [← openGraph_sdiff_diagSet ω, h, openGraph_sdiff_diagSet]]
          have hsupp : ∀ᵐ ω ∂law q₀, ω ⊆ G.edgeSet :=
            ae_config_subset_host G q₀ fun e he => by simp [q₀, he]
          refine le_of_eq (measure_eq_zero_iff_ae_notMem.2 ?_)
          filter_upwards [hsupp] with ω hω hK
          have hK : cluster ω [] = (C : Set (List (Fin 2))) := hK
          have hwK : w ∈ cluster ω [] := by rw [hK]; exact hwC
          have hpath := (reachable_nil_iff_of_subset hω w).1 hwK
          have htK : w.tail ∈ cluster ω [] := by
            refine (reachable_nil_iff_of_subset hω w.tail).2 fun m hm => ?_
            have := hpath (m + 1) (by simp at hm; omega)
            rw [← List.tail_drop_eq_drop_tail, ← List.tail_drop_eq_drop_tail, List.tail_drop,
              List.tail_drop]
            exact this
          rw [hK] at htK
          exact hwt htK
        · have hempty : {ω : Config (List (Fin 2)) |
              cluster ω [] = (C : Set (List (Fin 2)))} = ∅ := by
            refine Set.eq_empty_of_forall_notMem fun ω hK => h0 ?_
            have := mem_cluster_self ω ([] : List (Fin 2))
            rw [show cluster ω [] = (C : Set (List (Fin 2))) from hK] at this
            exact this
          rw [hempty, measure_empty]
    · refine le_antisymm (le_of_eq ?_) zero_le
      rw [show {ω : Config (List (Fin 2)) |
          C.card = n ∧ cluster ω [] = (C : Set (List (Fin 2)))} = ∅ from
        Set.eq_empty_of_forall_notMem fun ω h => hcard h.1, measure_empty]
  rw [tsum_eq_sum hzero]
  -- terms in `T`
  have hval : ∀ C ∈ T, law q {ω : Config (List (Fin 2)) |
      C.card = n ∧ cluster ω [] = (C : Set (List (Fin 2)))} =
      (unitInterval.toNNReal p : ℝ≥0∞) ^ (n - 1) *
        (unitInterval.toNNReal (unitInterval.symm p) : ℝ≥0∞) ^ (n + 1) := by
    intro C hC
    obtain ⟨t, ht, rfl⟩ := Finset.mem_image.1 hC
    have hcard : (φ t).card = n := by
      rw [hφcard]; exact BinaryTree.mem_treesOfNumNodesEq.1 ht
    have hne : (φ t).Nonempty := Finset.card_pos.1 (by omega)
    have h0 := nil_mem_of_tail_closed (hφclosed t) hne
    have : {ω : Config (List (Fin 2)) |
        (φ t).card = n ∧ cluster ω [] = ((φ t : Finset _) : Set (List (Fin 2)))} =
        {ω | cluster ω [] = ((φ t : Finset _) : Set (List (Fin 2)))} := by
      ext ω; simp [hcard]
    rw [this, binaryTree_law_cluster_eq p q hq h0 (hφclosed t), hcard]
  rw [Finset.sum_congr rfl hval, Finset.sum_const, nsmul_eq_mul, hT,
    Finset.card_image_of_injective _ hφinj, BinaryTree.treesOfNumNodesEq_card_eq_catalan,
    mul_assoc]

/-- **The Catalan law of the finite root cluster** (wiki tag 9K6O): for every `n ≥ 1` and
`p ∈ [0, 1]`,
`P(|K([])| = n, K([]) finite) = (1/(n+1)) · C(2n, n) · p^(n-1) · (1-p)^(n+1)`,
with `0^0 = 1`. -/
theorem binaryTree_law_cluster_card_eq (p : unitInterval)
    (q : Sym2 (List (Fin 2)) → unitInterval)
    (hq : ∀ e, ¬ e.IsDiag → q e =
      if e ∈ (SimpleGraph.fromRel fun u w : List (Fin 2) => ∃ b, w = b :: u).edgeSet then p
        else 0)
    {n : ℕ} (hn : 1 ≤ n) :
    law q {ω | (cluster ω []).ncard = n ∧ (cluster ω []).Finite} =
      ENNReal.ofReal (1 / ((n : ℝ) + 1) * ((2 * n).choose n : ℝ) * (p : ℝ) ^ (n - 1) *
        (1 - (p : ℝ)) ^ (n + 1)) := by
  rw [binaryTree_law_cluster_card_eq_catalan p q hq hn]
  have hcat : (catalan n : ℝ) = 1 / ((n : ℝ) + 1) * ((2 * n).choose n : ℝ) := by
    have h := succ_mul_catalan_eq_centralBinom n
    rw [Nat.centralBinom_eq_two_mul_choose] at h
    have h' : ((n : ℝ) + 1) * catalan n = ((2 * n).choose n : ℝ) := by exact_mod_cast h
    field_simp
    linarith
  have hp0 : (0 : ℝ) ≤ p := p.2.1
  have hp1 : (0 : ℝ) ≤ 1 - p := by linarith [p.2.2]
  rw [← hcat, ENNReal.ofReal_mul (by positivity), ENNReal.ofReal_mul (by positivity),
    ENNReal.ofReal_natCast, ENNReal.ofReal_pow hp0, ENNReal.ofReal_pow hp1]
  congr 2
  · rw [ENNReal.ofReal_eq_coe_nnreal hp0]; rfl
  · rw [ENNReal.ofReal_eq_coe_nnreal hp1]; rfl

/-! ### Non-vacuity (D-5): `n = 1` and `n = 2` -/

/-- `n = 1`: probability `(1-p)^2`. -/
example (p : unitInterval) :
    law (fun e : Sym2 (List (Fin 2)) =>
        if e ∈ (SimpleGraph.fromRel fun u w : List (Fin 2) => ∃ b, w = b :: u).edgeSet then p
          else 0)
      {ω | (cluster ω []).ncard = 1 ∧ (cluster ω []).Finite} =
      ENNReal.ofReal ((1 - (p : ℝ)) ^ 2) := by
  rw [binaryTree_law_cluster_card_eq p _ (fun _ _ => rfl) le_rfl]
  congr 1
  norm_num

/-- `n = 2`: probability `2 p (1-p)^3`. -/
example (p : unitInterval) :
    law (fun e : Sym2 (List (Fin 2)) =>
        if e ∈ (SimpleGraph.fromRel fun u w : List (Fin 2) => ∃ b, w = b :: u).edgeSet then p
          else 0)
      {ω | (cluster ω []).ncard = 2 ∧ (cluster ω []).Finite} =
      ENNReal.ofReal (2 * (p : ℝ) * (1 - (p : ℝ)) ^ 3) := by
  rw [binaryTree_law_cluster_card_eq p _ (fun _ _ => rfl) (by norm_num)]
  congr 1
  norm_num [Nat.choose]

end PercLib.Models
