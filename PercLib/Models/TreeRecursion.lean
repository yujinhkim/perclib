/-
Copyright (c) 2026 PercLib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

New proofs for issue 197 (Q-37, the depth recursion), written on 2026-11-15 by PROVER-E.
No upstream proof is copied. The recursion is the standard Galton–Watson recursion for
binomial offspring (G. Grimmett, *Percolation*, 2nd ed., 1999, the rooted tree example).
-/
module

public import PercLib.Models.Tree
public import PercLib.Probability.ProdBernoulliIndependence
public import PercLib.Probability.Transport.Pullback

/-!
# Bond percolation on the rooted `k`-ary tree: the depth recursion

With the conventions of `PercLib.Models.Tree` (children of `u` are `b :: u`), let `B n` be
the event that some word `w` of length `n` has every edge on its way to the root open. A
word of length `n + 1` is `u ++ [a]`, and its edges are the edge `s([], [a])` together with
the images of the edges of `u` under `v ↦ v ++ [a]`. The `k` events obtained this way depend
on disjoint sets of pairs, and each subtree is a copy of the whole tree. Hence, with
`p` the open probability of tree edges,

`P(B (n + 1)) = 1 - (1 - p P(B n))^k` (`law_depth_succ`).

This file adds no definition.
-/

@[expose] public section

open MeasureTheory Set PercLib.Probability PercLib.Percolation.Bond
open scoped ENNReal

namespace PercLib.Models

variable {k : ℕ}

/-! ### Independence of events on disjoint coordinate sets (private helpers) -/

private theorem measurable_image_val' {ι : Type*} (S : Set ι) :
    Measurable fun u : Set S => (Subtype.val '' u : Set ι) := by
  classical
  refine Measurable.of_mem fun i => ?_
  by_cases hi : i ∈ S
  · have : (fun u : Set S => i ∈ Subtype.val '' u) = fun u => (⟨i, hi⟩ : S) ∈ u := by
      funext u; simp [hi]
    rw [this]
    exact measurable_set_mem _
  · have : (fun u : Set S => i ∈ Subtype.val '' u) = fun _ => False := by
      funext u; simp [hi]
    rw [this]
    exact measurable_const

private theorem inter_of_determined {ι : Type*} (p : ι → unitInterval)
    (S T : Set ι) (hST : Disjoint S T) {E F : Set (Set ι)} (hE : MeasurableSet E)
    (hF : MeasurableSet F) (hEd : ∀ ω, ω ∈ E ↔ ω ∩ S ∈ E) (hFd : ∀ ω, ω ∈ F ↔ ω ∩ T ∈ F) :
    prodBernoulli p (E ∩ F) = prodBernoulli p E * prodBernoulli p F := by
  have himg : ∀ (R : Set ι) (ω : Set ι), Subtype.val '' {i : R | (i : ι) ∈ ω} = ω ∩ R := by
    intro R ω
    ext i
    simp [and_comm]
  have hE' : E = {ω | {i : S | (i : ι) ∈ ω} ∈ (fun u : Set S => Subtype.val '' u) ⁻¹' E} := by
    ext ω
    simp only [mem_ofPred_eq, mem_preimage, himg]
    exact hEd ω
  have hF' : F = {ω | {i : T | (i : ι) ∈ ω} ∈ (fun u : Set T => Subtype.val '' u) ⁻¹' F} := by
    ext ω
    simp only [mem_ofPred_eq, mem_preimage, himg]
    exact hFd ω
  have h := prodBernoulli_block_inter p S T hST _ _ (measurable_image_val' S hE)
    (measurable_image_val' T hF)
  rw [← hE', ← hF'] at h
  have hEF : E ∩ F = {ω | {i : S | (i : ι) ∈ ω} ∈ (fun u : Set S => Subtype.val '' u) ⁻¹' E ∧
      {i : T | (i : ι) ∈ ω} ∈ (fun u : Set T => Subtype.val '' u) ⁻¹' F} := by
    ext ω
    simp only [mem_inter_iff, mem_ofPred_eq, mem_preimage, himg]
    exact and_congr (hEd ω) (hFd ω)
  rw [hEF]
  exact h

private theorem biInter_of_determined {ι α : Type*} (p : ι → unitInterval) (s : Finset α)
    (S : α → Set ι) (hS : ∀ a ∈ s, ∀ b ∈ s, a ≠ b → Disjoint (S a) (S b))
    (E : α → Set (Set ι)) (hE : ∀ a ∈ s, MeasurableSet (E a))
    (hEd : ∀ a ∈ s, ∀ ω, ω ∈ E a ↔ ω ∩ S a ∈ E a) :
    prodBernoulli p (⋂ a ∈ s, E a) = ∏ a ∈ s, prodBernoulli p (E a) := by
  classical
  induction s using Finset.induction_on with
  | empty => simp
  | insert a s ha ih =>
    have hS' : ∀ b ∈ s, ∀ c ∈ s, b ≠ c → Disjoint (S b) (S c) := fun b hb c hc =>
      hS b (Finset.mem_insert_of_mem hb) c (Finset.mem_insert_of_mem hc)
    rw [Finset.set_biInter_insert, Finset.prod_insert ha,
      ← ih hS' (fun b hb => hE b (Finset.mem_insert_of_mem hb))
        (fun b hb => hEd b (Finset.mem_insert_of_mem hb))]
    refine inter_of_determined p (S a) (⋃ b ∈ s, S b) ?_ (hE a (Finset.mem_insert_self a s))
      (Finset.measurableSet_biInter s fun b hb => hE b (Finset.mem_insert_of_mem hb))
      (hEd a (Finset.mem_insert_self a s)) ?_
    · refine Set.disjoint_iUnion₂_right.2 fun b hb => hS a (Finset.mem_insert_self a s) b
        (Finset.mem_insert_of_mem hb) fun h => ha (h ▸ hb)
    · intro ω
      simp only [mem_iInter]
      refine forall₂_congr fun b hb => ?_
      rw [hEd b (Finset.mem_insert_of_mem hb) ω,
        hEd b (Finset.mem_insert_of_mem hb) (ω ∩ ⋃ c ∈ s, S c)]
      have : ω ∩ (⋃ c ∈ s, S c) ∩ S b = ω ∩ S b := by
        ext i
        simp only [mem_inter_iff, mem_iUnion]
        exact ⟨fun h => ⟨h.1.1, h.2⟩, fun h => ⟨⟨h.1, b, hb, h.2⟩, h.2⟩⟩
      rw [this]

/-! ### The depth events -/

/-- An edge of `u ++ [a]` below the top is the image of the corresponding edge of `u`. -/
theorem edge_append_singleton (u : List (Fin k)) (a : Fin k) {m : ℕ} (hm : m < u.length) :
    s((u ++ [a]).drop (m + 1), (u ++ [a]).drop m) =
      Sym2.map (fun v => v ++ [a]) s(u.drop (m + 1), u.drop m) := by
  rw [List.drop_append_of_le_length (by omega), List.drop_append_of_le_length (by omega)]
  rfl

/-- The top edge of `u ++ [a]` is `s([], [a])`. -/
theorem edge_append_singleton_top (u : List (Fin k)) (a : Fin k) :
    s((u ++ [a]).drop (u.length + 1), (u ++ [a]).drop u.length) = s([], [a]) := by
  rw [List.drop_left, List.drop_eq_nil_of_le (by simp)]

/-- **A word of depth `n + 1` is `u ++ [a]`**: reaching depth `n + 1` along open edges means
opening `s([], [a])` and reaching depth `n` in the subtree of `[a]`. -/
theorem depth_succ_iff (ω : Config (List (Fin k))) (n : ℕ) :
    (∃ w : List (Fin k), w.length = n + 1 ∧ ∀ m < n + 1, s(w.drop (m + 1), w.drop m) ∈ ω) ↔
      ∃ a : Fin k, s([], [a]) ∈ ω ∧ ∃ u : List (Fin k), u.length = n ∧
        ∀ m < n, Sym2.map (fun v => v ++ [a]) s(u.drop (m + 1), u.drop m) ∈ ω := by
  constructor
  · rintro ⟨w, hw, h⟩
    have hne : w ≠ [] := by rintro rfl; simp at hw
    set u := w.dropLast
    set a := w.getLast hne
    have hwu : w = u ++ [a] := (List.dropLast_append_getLast hne).symm
    have hu : u.length = n := by simp [u, hw]
    refine ⟨a, ?_, u, hu, fun m hm => ?_⟩
    · have := h n (by omega)
      rwa [hwu, ← hu, edge_append_singleton_top] at this
    · have := h m (by omega)
      rwa [hwu, edge_append_singleton u a (by omega)] at this
  · rintro ⟨a, ha, u, hu, h⟩
    refine ⟨u ++ [a], by simp [hu], fun m hm => ?_⟩
    rcases Nat.lt_succ_iff_lt_or_eq.1 hm with hm | rfl
    · rw [edge_append_singleton u a (by omega)]
      exact h m hm
    · rw [← hu, edge_append_singleton_top]
      exact ha

/-- The depth events are measurable. -/
theorem measurableSet_depth_open (n : ℕ) :
    MeasurableSet {ω : Config (List (Fin k)) |
      ∃ w : List (Fin k), w.length = n ∧ ∀ m < n, s(w.drop (m + 1), w.drop m) ∈ ω} := by
  have : {ω : Config (List (Fin k)) |
      ∃ w : List (Fin k), w.length = n ∧ ∀ m < n, s(w.drop (m + 1), w.drop m) ∈ ω} =
      ⋃ w : List (Fin k), {_ω : Config (List (Fin k)) | w.length = n} ∩
        ⋂ m : ℕ, ⋂ (_ : m < n), {ω : Config (List (Fin k)) | s(w.drop (m + 1), w.drop m) ∈ ω} := by
    ext ω
    simp
  rw [this]
  exact MeasurableSet.iUnion fun w => (MeasurableSet.const _).inter
    (MeasurableSet.iInter fun m => MeasurableSet.iInter fun _ => measurableSet_mem _)

/-- Appending a letter is injective on unordered pairs of words. -/
theorem injective_map_append (a : Fin k) :
    Function.Injective (Sym2.map fun v : List (Fin k) => v ++ [a]) :=
  Sym2.map.injective fun _ _ h => List.append_cancel_right h

/-- Appending a letter preserves and reflects tree edges. -/
theorem map_append_mem_edgeSet_iff (a : Fin k) (e : Sym2 (List (Fin k))) :
    Sym2.map (fun v => v ++ [a]) e ∈
        (SimpleGraph.fromRel fun u w : List (Fin k) => ∃ b, w = b :: u).edgeSet ↔
      e ∈ (SimpleGraph.fromRel fun u w : List (Fin k) => ∃ b, w = b :: u).edgeSet := by
  induction e using Sym2.ind with
  | _ x y =>
  rw [Sym2.map_mk, SimpleGraph.mem_edgeSet, SimpleGraph.mem_edgeSet, kTree_adj_iff,
    kTree_adj_iff]
  simp only [← List.cons_append, List.append_left_inj]

/-- The canonical tree profile is invariant under appending a letter. -/
theorem tree_profile_comp_map_append (p : unitInterval) (a : Fin k) :
    ((fun e => if e ∈ (SimpleGraph.fromRel fun u w : List (Fin k) => ∃ b, w = b :: u).edgeSet
        then p else 0) ∘ Sym2.map fun v : List (Fin k) => v ++ [a]) =
      fun e => if e ∈ (SimpleGraph.fromRel fun u w : List (Fin k) => ∃ b, w = b :: u).edgeSet
        then p else 0 := by
  classical
  funext e
  simp only [Function.comp_apply, map_append_mem_edgeSet_iff]

/-- An edge `s(u.drop (m+1), u.drop m)` with `m < |u|` is not a loop. -/
theorem not_isDiag_edge (u : List (Fin k)) {m : ℕ} (hm : m < u.length) :
    ¬ (s(u.drop (m + 1), u.drop m) : Sym2 (List (Fin k))).IsDiag := by
  rw [Sym2.mk_isDiag_iff]
  intro h
  have := congrArg List.length h
  simp only [List.length_drop] at this
  omega

/-- **The depth recursion.** With open probability `p` on tree edges and `0` elsewhere,
`P(B (n + 1)) = 1 - (1 - p P(B n))^k`, where `B n` is the event that the edges from some
word of length `n` to the root are all open. -/
theorem law_depth_succ (p : unitInterval) (n : ℕ) :
    law (fun e : Sym2 (List (Fin k)) =>
        if e ∈ (SimpleGraph.fromRel fun u w : List (Fin k) => ∃ b, w = b :: u).edgeSet then p
          else 0)
      {ω | ∃ w : List (Fin k), w.length = n + 1 ∧
        ∀ m < n + 1, s(w.drop (m + 1), w.drop m) ∈ ω} =
    1 - (1 - (unitInterval.toNNReal p : ℝ≥0∞) *
      law (fun e : Sym2 (List (Fin k)) =>
        if e ∈ (SimpleGraph.fromRel fun u w : List (Fin k) => ∃ b, w = b :: u).edgeSet then p
          else 0)
        {ω | ∃ w : List (Fin k), w.length = n ∧ ∀ m < n, s(w.drop (m + 1), w.drop m) ∈ ω}) ^ k := by
  classical
  set G := SimpleGraph.fromRel fun u w : List (Fin k) => ∃ b, w = b :: u
  set q₀ : Sym2 (List (Fin k)) → unitInterval := fun e => if e ∈ G.edgeSet then p else 0
  set B : ℕ → Set (Config (List (Fin k))) := fun n =>
    {ω | ∃ w : List (Fin k), w.length = n ∧ ∀ m < n, s(w.drop (m + 1), w.drop m) ∈ ω}
  set f : Fin k → Sym2 (List (Fin k)) → Sym2 (List (Fin k)) := fun a =>
    Sym2.map fun v => v ++ [a]
  set H : Fin k → Set (Config (List (Fin k))) := fun a =>
    {ω | s([], [a]) ∈ ω} ∩ {ω | (f a) ⁻¹' ω ∈ B n}
  set S : Fin k → Set (Sym2 (List (Fin k))) := fun a =>
    {e | ¬ e.IsDiag ∧ ∀ v ∈ e, v = [] ∨ v.getLast? = some a}
  change prodBernoulli q₀ (B (n + 1)) = 1 - (1 - _ * prodBernoulli q₀ (B n)) ^ k
  have hdecomp : B (n + 1) = ⋃ a, H a := by
    ext ω
    simp only [B, H, f, mem_iUnion, mem_inter_iff, mem_ofPred_eq, mem_preimage]
    exact depth_succ_iff ω n
  have hBm : MeasurableSet (B n) := measurableSet_depth_open n
  have hpullm : ∀ a, Measurable fun ω : Config (List (Fin k)) => (f a) ⁻¹' ω := fun a =>
    Measurable.of_mem fun e => (measurableSet_mem (f a e)).mem
  have hHm : ∀ a, MeasurableSet (H a) := fun a =>
    (measurableSet_mem _).inter (hpullm a hBm)
  have hpull : ∀ a, prodBernoulli q₀ {ω | (f a) ⁻¹' ω ∈ B n} = prodBernoulli q₀ (B n) := by
    intro a
    rw [prodBernoulli_preimage_preimage q₀ (injective_map_append a) hBm]
    simp only [q₀, G]
    rw [tree_profile_comp_map_append]
  have hedge : ∀ a : Fin k, prodBernoulli q₀ {ω | s([], [a]) ∈ ω} =
      (unitInterval.toNNReal p : ℝ≥0∞) := by
    intro a
    rw [prodBernoulli_setOf_mem]
    have : s(([] : List (Fin k)), [a]) ∈ G.edgeSet := by
      rw [SimpleGraph.mem_edgeSet, kTree_adj_iff]
      exact Or.inl ⟨a, rfl⟩
    simp only [q₀, this, ite_true]
  have hfT : ∀ a e, ∀ v ∈ f a e, v.getLast? = some a := by
    intro a e v hv
    obtain ⟨y, -, rfl⟩ := Sym2.mem_map.1 hv
    exact List.getLast?_concat
  have hH : ∀ a, prodBernoulli q₀ (H a) = (unitInterval.toNNReal p : ℝ≥0∞) *
      prodBernoulli q₀ (B n) := by
    intro a
    rw [← hedge a, ← hpull a]
    refine inter_of_determined q₀ {s([], [a])} {e | ∀ v ∈ e, v.getLast? = some a} ?_
      (measurableSet_mem _) (hpullm a hBm) ?_ ?_
    · refine Set.disjoint_singleton_left.2 fun h => ?_
      have := h [] (Sym2.mem_mk_left _ _)
      simp at this
    · intro ω
      simp
    · intro ω
      have : (f a) ⁻¹' (ω ∩ {e | ∀ v ∈ e, v.getLast? = some a}) = (f a) ⁻¹' ω := by
        ext e
        simp only [mem_preimage, mem_inter_iff, mem_ofPred_eq, and_iff_left_iff_imp]
        exact fun _ => hfT a e
      simp only [mem_ofPred_eq, this]
  have hS0 : ∀ a, s(([] : List (Fin k)), [a]) ∈ S a := by
    intro a
    refine ⟨by rw [Sym2.mk_isDiag_iff]; simp, fun v hv => ?_⟩
    rcases Sym2.mem_iff.1 hv with rfl | rfl
    · exact Or.inl rfl
    · exact Or.inr rfl
  have hSe : ∀ a (u : List (Fin k)) m, m < u.length → f a s(u.drop (m + 1), u.drop m) ∈ S a := by
    intro a u m hm
    refine ⟨?_, fun v hv => Or.inr (hfT a _ v hv)⟩
    simp only [f, Sym2.map_mk, Sym2.mk_isDiag_iff]
    intro h
    have := congrArg List.length h
    simp only [List.length_append, List.length_drop, List.length_singleton] at this
    omega
  have hdisj : ∀ a ∈ (Finset.univ : Finset (Fin k)), ∀ b ∈ (Finset.univ : Finset (Fin k)),
      a ≠ b → Disjoint (S a) (S b) := by
    intro a _ b _ hab
    refine Set.disjoint_left.2 fun e hea heb => ?_
    induction e using Sym2.ind with
    | _ x y =>
    have hxy : x ≠ y := by
      intro h
      exact hea.1 (Sym2.mk_isDiag_iff.2 h)
    by_cases hx : x = []
    · have hy : y ≠ [] := fun h => hxy (hx.trans h.symm)
      have h1 := (hea.2 y (Sym2.mem_mk_right x y)).resolve_left hy
      have h2 := (heb.2 y (Sym2.mem_mk_right x y)).resolve_left hy
      exact hab (Option.some_injective _ (h1.symm.trans h2))
    · have h1 := (hea.2 x (Sym2.mem_mk_left x y)).resolve_left hx
      have h2 := (heb.2 x (Sym2.mem_mk_left x y)).resolve_left hx
      exact hab (Option.some_injective _ (h1.symm.trans h2))
  have hHd : ∀ a ∈ (Finset.univ : Finset (Fin k)), ∀ ω, ω ∈ (H a)ᶜ ↔ ω ∩ S a ∈ (H a)ᶜ := by
    intro a _ ω
    refine not_congr ?_
    simp only [H, B, mem_inter_iff, mem_ofPred_eq, mem_preimage]
    refine and_congr ⟨fun h => ⟨h, hS0 a⟩, fun h => h.1⟩
      (exists_congr fun u => and_congr_right fun hu => forall₂_congr fun m hm => ?_)
    exact ⟨fun h => ⟨h, hSe a u m (hu ▸ hm)⟩, fun h => h.1⟩
  calc prodBernoulli q₀ (B (n + 1)) = prodBernoulli q₀ (⋃ a, H a) := by rw [hdecomp]
    _ = 1 - prodBernoulli q₀ (⋃ a, H a)ᶜ := by
        rw [prob_compl_eq_one_sub (MeasurableSet.iUnion hHm),
          ENNReal.sub_sub_cancel ENNReal.one_ne_top prob_le_one]
    _ = 1 - prodBernoulli q₀ (⋂ a ∈ (Finset.univ : Finset (Fin k)), (H a)ᶜ) := by
        rw [compl_iUnion]
        simp
    _ = 1 - ∏ a ∈ (Finset.univ : Finset (Fin k)), prodBernoulli q₀ (H a)ᶜ := by
        rw [biInter_of_determined q₀ Finset.univ S hdisj (fun a => (H a)ᶜ)
          (fun a _ => (hHm a).compl) hHd]
    _ = 1 - ∏ _a ∈ (Finset.univ : Finset (Fin k)),
          (1 - (unitInterval.toNNReal p : ℝ≥0∞) * prodBernoulli q₀ (B n)) := by
        congr 1
        refine Finset.prod_congr rfl fun a _ => ?_
        rw [prob_compl_eq_one_sub (hHm a), hH a]
    _ = _ := by rw [Finset.prod_const, Finset.card_univ, Fintype.card_fin]

/-! ### The recursion map `g(s) = 1 - (1 - p s)^k` -/

/-- Strict Bernoulli inequality. -/
theorem one_sub_mul_lt_pow {x : ℝ} (hx0 : 0 < x) (hx1 : x ≤ 1) (j : ℕ) :
    1 - ((j + 2 : ℕ) : ℝ) * x < (1 - x) ^ (j + 2) := by
  induction j with
  | zero =>
    push_cast
    nlinarith [sq_pos_of_pos hx0]
  | succ j ih =>
    have h1 : 0 ≤ 1 - x := by linarith
    push_cast at ih ⊢
    rw [pow_succ]
    nlinarith [mul_le_mul_of_nonneg_right ih.le h1, mul_pos hx0 hx0]

/-- A second-order upper bound for `(1 - x)^k`. -/
theorem pow_one_sub_le_quad {x : ℝ} (hx0 : 0 ≤ x) (hx1 : x ≤ 1) (k : ℕ) :
    (1 - x) ^ k ≤ 1 - k * x + (k * x) ^ 2 / 2 := by
  induction k with
  | zero => simp
  | succ k ih =>
    have h1 : 0 ≤ 1 - x := by linarith
    have hk : (0 : ℝ) ≤ k := Nat.cast_nonneg k
    rw [pow_succ]
    calc (1 - x) ^ k * (1 - x) ≤ (1 - k * x + (k * x) ^ 2 / 2) * (1 - x) :=
          mul_le_mul_of_nonneg_right ih h1
      _ ≤ 1 - ((k + 1 : ℕ) : ℝ) * x + (((k + 1 : ℕ) : ℝ) * x) ^ 2 / 2 := by
          push_cast
          nlinarith [mul_nonneg (mul_nonneg hk hk) (mul_nonneg (mul_nonneg hx0 hx0) hx0),
            mul_nonneg hx0 hx0]

/-- The recursion map is monotone on `[0, 1]`. -/
theorem recursion_mono {p : ℝ} (hp0 : 0 ≤ p) (hp1 : p ≤ 1) (k : ℕ) {s t : ℝ}
    (ht : t ≤ 1) (hst : s ≤ t) :
    1 - (1 - p * s) ^ k ≤ 1 - (1 - p * t) ^ k := by
  have h1 : 0 ≤ 1 - p * t := by nlinarith
  have h2 : 1 - p * t ≤ 1 - p * s := by nlinarith
  have := pow_le_pow_left₀ h1 h2 k
  linarith

/-- **Supercritical lower bound.** If `k p > 1` there is `c ∈ (0, 1]` with `g(c) ≥ c`. -/
theorem exists_le_recursion {p : ℝ} (hp0 : 0 ≤ p) (hp1 : p ≤ 1) {k : ℕ}
    (hkp : 1 < (k : ℝ) * p) :
    ∃ c : ℝ, 0 < c ∧ c ≤ 1 ∧ c ≤ 1 - (1 - p * c) ^ k := by
  set r : ℝ := (k : ℝ) * p
  refine ⟨min 1 ((r - 1) / r ^ 2), lt_min one_pos (div_pos (by linarith) (by positivity)),
    min_le_left _ _, ?_⟩
  set c := min 1 ((r - 1) / r ^ 2)
  have hc0 : 0 < c := lt_min one_pos (div_pos (by linarith) (by positivity))
  have hc1 : c ≤ 1 := min_le_left _ _
  have hcr : r ^ 2 * c ≤ r - 1 := by
    have : c ≤ (r - 1) / r ^ 2 := min_le_right _ _
    rw [le_div_iff₀ (by positivity)] at this
    linarith
  have hx0 : 0 ≤ p * c := mul_nonneg hp0 hc0.le
  have hx1 : p * c ≤ 1 := by nlinarith
  have hq := pow_one_sub_le_quad hx0 hx1 k
  have hkx : (k : ℝ) * (p * c) = r * c := by ring
  rw [hkx] at hq
  nlinarith [mul_pos hc0 hc0]

/-- **Subcritical and critical contraction.** If `k ≥ 1`, `k p ≤ 1` and `p < 1`, then
`g(s) < s` for `s ∈ (0, 1]`. -/
theorem recursion_lt {p : ℝ} (hp0 : 0 ≤ p) (hp1 : p < 1) {k : ℕ} (hk : 1 ≤ k)
    (hkp : (k : ℝ) * p ≤ 1) {s : ℝ} (hs0 : 0 < s) (hs1 : s ≤ 1) :
    1 - (1 - p * s) ^ k < s := by
  rcases Nat.lt_or_ge k 2 with hk2 | hk2
  · have : k = 1 := by omega
    subst this
    simp only [pow_one]
    nlinarith
  · rcases eq_or_lt_of_le hp0 with hp | hp
    · subst hp
      simp only [zero_mul, sub_zero, one_pow, sub_self]
      exact hs0
    · obtain ⟨j, rfl⟩ : ∃ j, k = j + 2 := ⟨k - 2, by omega⟩
      have h := one_sub_mul_lt_pow (mul_pos hp hs0) (by nlinarith) j
      have : ((j + 2 : ℕ) : ℝ) * (p * s) ≤ s := by
        rw [← mul_assoc]
        nlinarith
      linarith

/-! ### The threshold of the `k`-ary tree -/

/-- **Percolation on the rooted `k`-ary tree.** With open probability `p` on tree edges and
`0` on the other pairs (any value on the diagonal), the root cluster is infinite with
positive probability exactly when `k p > 1` or `p = 1`. -/
theorem law_cluster_nil_infinite_pos_iff (hk : 1 ≤ k) (p : unitInterval)
    (q : Sym2 (List (Fin k)) → unitInterval)
    (hq : ∀ e, ¬ e.IsDiag → q e =
      if e ∈ (SimpleGraph.fromRel fun u w : List (Fin k) => ∃ b, w = b :: u).edgeSet then p
        else 0) :
    0 < law q {ω | (cluster ω []).Infinite} ↔ 1 < (k : ℝ) * (p : ℝ) ∨ p = 1 := by
  classical
  set G := SimpleGraph.fromRel fun u w : List (Fin k) => ∃ b, w = b :: u
  set q₀ : Sym2 (List (Fin k)) → unitInterval := fun e => if e ∈ G.edgeSet then p else 0
  set B : ℕ → Set (Config (List (Fin k))) := fun n =>
    {ω | ∃ w : List (Fin k), w.length = n ∧ ∀ m < n, s(w.drop (m + 1), w.drop m) ∈ ω}
  have hdiag : law q {ω | (cluster ω []).Infinite} = law q₀ {ω | (cluster ω []).Infinite} := by
    refine law_event_eq_of_offDiagonal q q₀ (fun e he => hq e he)
      (measurableSet_cluster_infinite _) fun ω ω' h => ?_
    simp only [mem_ofPred_eq, cluster]
    rw [← openGraph_sdiff_diagSet ω, h, openGraph_sdiff_diagSet]
  have hsupp : ∀ᵐ ω ∂law q₀, ω ⊆ G.edgeSet :=
    ae_config_subset_host G q₀ fun e he => by simp [q₀, he]
  have hinf : law q₀ {ω | (cluster ω []).Infinite} = law q₀ (⋂ n, B n) := by
    refine measure_congr ?_
    filter_upwards [hsupp] with ω hω
    refine propext ?_
    rw [mem_iInter]
    exact cluster_nil_infinite_iff hω
  have hanti : Antitone B := by
    refine antitone_nat_of_succ_le fun n ω hω => ?_
    obtain ⟨w, hw, h⟩ := hω
    refine ⟨w.drop 1, by simp [hw], fun m hm => ?_⟩
    have := h (m + 1) (by omega)
    simpa [List.drop_drop, Nat.add_comm, Nat.add_left_comm] using this
  have hB0 : B 0 = univ := eq_univ_of_forall fun ω => ⟨[], rfl, fun m hm => absurd hm (by omega)⟩
  have hθ : law q₀ (⋂ n, B n) = ⨅ n, law q₀ (B n) :=
    hanti.measure_iInter (fun n => (measurableSet_depth_open n).nullMeasurableSet)
      ⟨0, measure_ne_top _ _⟩
  set f : ℕ → ℝ := fun n => (law q₀ (B n)).toReal
  have hfx : ∀ n, law q₀ (B n) = ENNReal.ofReal (f n) := fun n =>
    (ENNReal.ofReal_toReal (measure_ne_top _ _)).symm
  have hf0 : ∀ n, 0 ≤ f n := fun n => ENNReal.toReal_nonneg
  have hf1 : ∀ n, f n ≤ 1 := fun n => by
    have := ENNReal.toReal_mono ENNReal.one_ne_top (prob_le_one (μ := law q₀) (s := B n))
    simpa using this
  have hp : ((unitInterval.toNNReal p : ℝ≥0∞)).toReal = (p : ℝ) := rfl
  have hp0 : (0 : ℝ) ≤ p := p.2.1
  have hp1 : (p : ℝ) ≤ 1 := p.2.2
  have hfrec : ∀ n, f (n + 1) = 1 - (1 - p * f n) ^ k := by
    intro n
    have h := law_depth_succ (k := k) p n
    change law q₀ (B (n + 1)) = 1 - (1 - _ * law q₀ (B n)) ^ k at h
    have hx : (unitInterval.toNNReal p : ℝ≥0∞) * law q₀ (B n) ≤ 1 :=
      mul_le_one' (by exact_mod_cast unitInterval.le_one p) prob_le_one
    have hy : (1 - (unitInterval.toNNReal p : ℝ≥0∞) * law q₀ (B n)) ^ k ≤ 1 :=
      pow_le_one₀ zero_le tsub_le_self
    change (law q₀ (B (n + 1))).toReal = _
    rw [h, ENNReal.toReal_sub_of_le hy ENNReal.one_ne_top, ENNReal.toReal_pow,
      ENNReal.toReal_sub_of_le hx ENNReal.one_ne_top, ENNReal.toReal_mul, hp]
    simp [f]
  rw [hdiag, hinf, hθ]
  constructor
  · intro hpos
    by_contra hcon
    push Not at hcon
    obtain ⟨hkp, hpne⟩ := hcon
    have hp1' : (p : ℝ) < 1 := lt_of_le_of_ne hp1 fun h => hpne (Subtype.ext h)
    have hfanti : Antitone f := fun m n hmn =>
      ENNReal.toReal_mono (measure_ne_top _ _) (measure_mono (hanti hmn))
    have htend : Filter.Tendsto f Filter.atTop (nhds (⨅ n, f n)) :=
      tendsto_atTop_ciInf hfanti ⟨0, fun _ ⟨n, hn⟩ => hn ▸ hf0 n⟩
    set L := ⨅ n, f n
    have hL0 : 0 ≤ L := le_ciInf hf0
    have hL1 : L ≤ 1 := (ciInf_le ⟨0, fun _ ⟨n, hn⟩ => hn ▸ hf0 n⟩ 0).trans (hf1 0)
    have hgc : Continuous fun s : ℝ => 1 - (1 - p * s) ^ k := by fun_prop
    have h1 : Filter.Tendsto (fun n => f (n + 1)) Filter.atTop
        (nhds (1 - (1 - p * L) ^ k)) := by
      simp_rw [hfrec]
      exact (hgc.tendsto L).comp htend
    have h2 : Filter.Tendsto (fun n => f (n + 1)) Filter.atTop (nhds L) :=
      (Filter.tendsto_add_atTop_iff_nat 1).2 htend
    have hfix : 1 - (1 - p * L) ^ k = L := tendsto_nhds_unique h1 h2
    have hL : L = 0 := by
      by_contra hL
      have := recursion_lt hp0 hp1' hk hkp (lt_of_le_of_ne hL0 (Ne.symm hL)) hL1
      linarith
    have hle : (⨅ n, law q₀ (B n)) ≤ ENNReal.ofReal L := by
      refine ge_of_tendsto' (ENNReal.tendsto_ofReal htend) fun n => ?_
      rw [← hfx n]
      exact iInf_le _ n
    rw [hL, ENNReal.ofReal_zero] at hle
    exact absurd (le_antisymm hle zero_le) hpos.ne'
  · intro h
    obtain ⟨c, hc0, hc1, hcg⟩ : ∃ c : ℝ, 0 < c ∧ c ≤ 1 ∧ c ≤ 1 - (1 - p * c) ^ k := by
      rcases h with hkp | hp1
      · exact exists_le_recursion hp0 hp1 hkp
      · refine ⟨1, one_pos, le_rfl, ?_⟩
        rw [hp1]
        simp [zero_pow (Nat.one_le_iff_ne_zero.1 hk)]
    have hfc : ∀ n, c ≤ f n := by
      intro n
      induction n with
      | zero =>
        have : f 0 = 1 := by simp [f, hB0]
        rw [this]
        exact hc1
      | succ n ih =>
        rw [hfrec]
        exact hcg.trans (recursion_mono hp0 hp1 k (hf1 n) ih)
    refine lt_of_lt_of_le (ENNReal.ofReal_pos.2 hc0) (le_iInf fun n => ?_)
    rw [hfx n]
    exact ENNReal.ofReal_le_ofReal (hfc n)

/-! ### Non-vacuity -/

/-- The binary tree percolates at `p = 3/4` and not at the critical value `p = 1/2`. -/
example :
    0 < law (fun e : Sym2 (List (Fin 2)) =>
        if e ∈ (SimpleGraph.fromRel fun u w : List (Fin 2) => ∃ b, w = b :: u).edgeSet then
          (⟨3 / 4, by norm_num, by norm_num⟩ : unitInterval) else 0)
      {ω | (cluster ω []).Infinite} ∧
    law (fun e : Sym2 (List (Fin 2)) =>
        if e ∈ (SimpleGraph.fromRel fun u w : List (Fin 2) => ∃ b, w = b :: u).edgeSet then
          (⟨1 / 2, by norm_num, by norm_num⟩ : unitInterval) else 0)
      {ω | (cluster ω []).Infinite} = 0 := by
  constructor
  · refine (law_cluster_nil_infinite_pos_iff (k := 2) (by norm_num) _ _
      fun _ _ => rfl).2 (Or.inl ?_)
    change (1 : ℝ) < 2 * (3 / 4)
    norm_num
  · by_contra h
    have := (law_cluster_nil_infinite_pos_iff (k := 2) (by norm_num) _ _ fun _ _ => rfl).1
      (pos_iff_ne_zero.2 h)
    rcases this with h1 | h1
    · change (1 : ℝ) < 2 * (1 / 2) at h1
      norm_num at h1
    · have := congrArg Subtype.val h1
      change (1 / 2 : ℝ) = 1 at this
      norm_num at this

/-- The half-line (`k = 1`) percolates only at `p = 1`. -/
example : 0 < law (fun e : Sym2 (List (Fin 1)) =>
      if e ∈ (SimpleGraph.fromRel fun u w : List (Fin 1) => ∃ b, w = b :: u).edgeSet then
        (1 : unitInterval) else 0)
    {ω | (cluster ω []).Infinite} :=
  (law_cluster_nil_infinite_pos_iff le_rfl _ _ fun _ _ => rfl).2 (Or.inr rfl)

end PercLib.Models
