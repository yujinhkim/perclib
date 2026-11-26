/-
An independently rebuilt direction (Ultramath swarm `smwwt6noq`, member `m2`, direction B).
Production base `4c53bb5a8e76a4358a426adf71169b916b90f51f`.
-/

module

public import PercLib.CriticalLRP.Correlation.I417.Marked.Diagram
public import PercLib.CriticalLRP.Correlation.I417.Marked.ExampleDefs

/-!
# Elementary depth/leaf-count classification and the `p = 0`, `p = 1` evaluations

The marked diagram identity of `I417Marked/Marked.lean` is stated for arbitrary `p`.  This file
supplies what can honestly be computed at the two smallest instances, together with the
elementary binary-tree classification those computations need.

## The classification

* `eq_leaf_of_numLeaves_eq_one`, `eq_node_leaf_leaf_of_numLeaves_eq_two` -- a binary tree with
  `k` leaves is a leaf (`k = 1`) resp. a node of two leaves (`k = 2`);
* `label_zero_eq : Label 0 = Fin 0 ⊕ PUnit` has one element, `label_one_eq` -- it has exactly
  two, `armLabel 1 0` and `markLabel 1`.  Hence `card_ltOn_label_zero` (`= 1`) and
  `card_ltOn_label_one` (`= 2`) for the labelled shape families.
* `markDepth_eq_two` -- at `p = 1` every leaf of a two-leaf tree has depth exactly `2`, so the
  marked leaf of every shape of `markedShapes 1` has depth `2` and `markedCount 1 ℓ` is `2` at
  `ℓ = 2` and `0` elsewhere.

## The evaluations

* `labelledMarkedDiagram_zero` (**unconditional**, for every kernel):
  `labelledMarkedDiagram k 0 x w = T^1(x,w) = k x w`.  At `p = 0` the family has the single
  shape `leaf (Sum.inr ⟨⟩)`, the exponent `2·0+1-1` is `0`, and no constant-row-sum hypothesis
  is used.
* `labelledMarkedDiagram_one` (for a kernel with constant row sum `χ`):
  `labelledMarkedDiagram k 1 x w = 2 · χ · T^2(x,w)`.

## What is *not* claimed

`markedCount p ℓ` for general `p` is not evaluated here: the `(2p-1)!!` total, the binomial
law of the marked depth, and the two-copy `q` side of Lemma I.4.17 all remain open.
-/

set_option autoImplicit false
set_option linter.unusedSectionVars false

open scoped ENNReal NNReal

@[expose] public section

namespace PercLib.CriticalLRP.I417Marked

open PercLib.CriticalLRP.TreeExpansion

universe u v

/-! ## Classifying a binary tree by its number of leaves -/

/-- A binary tree with one leaf is a leaf. -/
theorem eq_leaf_of_numLeaves_eq_one {α : Type u} {t : RTree α} (h : t.numLeaves = 1) :
    ∃ a, t = RTree.leaf a := by
  cases t with
  | leaf a => exact ⟨a, rfl⟩
  | node l r =>
      exfalso
      have h1 : 0 < l.numLeaves := RTree.numLeaves_pos l
      have h2 : 0 < r.numLeaves := RTree.numLeaves_pos r
      rw [RTree.numLeaves_node] at h
      omega

/-- A binary tree with two leaves is a node of two leaves. -/
theorem eq_node_leaf_leaf_of_numLeaves_eq_two {α : Type u} {t : RTree α}
    (h : t.numLeaves = 2) :
    ∃ a b, t = RTree.node (RTree.leaf a) (RTree.leaf b) := by
  cases t with
  | leaf a =>
      rw [RTree.numLeaves_leaf] at h
      omega
  | node l r =>
      have h1 : 0 < l.numLeaves := RTree.numLeaves_pos l
      have h2 : 0 < r.numLeaves := RTree.numLeaves_pos r
      rw [RTree.numLeaves_node] at h
      obtain ⟨a, ha⟩ := eq_leaf_of_numLeaves_eq_one (t := l) (by omega)
      obtain ⟨b, hb⟩ := eq_leaf_of_numLeaves_eq_one (t := r) (by omega)
      exact ⟨a, b, by rw [ha, hb]⟩

/-! ## The `p = 1` case: the marked depth is exactly two -/

/-- **At `p = 1` the marked depth is exactly `2`**: a shape on the two labels is a node of two
leaves, and every leaf of a two-leaf tree has depth `2`. -/
theorem markDepth_eq_two (t : LTon (Label 1) (Finset.univ : Finset (Label 1))) :
    markDepth (markLabel 1) t.1 = 2 := by
  obtain ⟨a, b, hab⟩ := eq_node_leaf_leaf_of_numLeaves_eq_two (numLeaves_ltOn_label 1 t)
  rw [markDepth, hab]
  cases hq : markPos (markLabel 1) (RTree.node (RTree.leaf a) (RTree.leaf b)) with
  | inl u => rfl
  | inr u => rfl

/-- Every marked shape at `p = 1` has marked depth `2`. -/
theorem markedShapes_depth_eq_two :
    ∀ A ∈ markedShapes 1, RTree.depth A.1 A.2 = 2 := by
  intro A hA
  classical
  rw [markedShapes, Finset.mem_image] at hA
  obtain ⟨t, -, ht⟩ := hA
  rw [← ht]
  exact markDepth_eq_two t

/-! ## The `p = 1` label set and its two shapes -/

/-- `Fin 1 ⊕ PUnit` has exactly the two elements `armLabel 1 0` and `markLabel 1`. -/
theorem label_one_eq (a : Label 1) : a = armLabel 1 0 ∨ a = markLabel 1 := by
  rcases a with i | u
  · left
    change Sum.inl i = Sum.inl 0
    rw [Fin.eq_zero i]
  · right
    change Sum.inr u = Sum.inr ⟨⟩
    rfl

/-- The left-labelled two-leaf shape: the arm leaf on the left, the mark on the right. -/
theorem ltOn_label_one_eq (t : LTon (Label 1) (Finset.univ : Finset (Label 1))) :
    t.1 = RTree.node (RTree.leaf (armLabel 1 0)) (RTree.leaf (markLabel 1)) ∨
      t.1 = RTree.node (RTree.leaf (markLabel 1)) (RTree.leaf (armLabel 1 0)) := by
  classical
  obtain ⟨a, b, hab⟩ := eq_node_leaf_leaf_of_numLeaves_eq_two (numLeaves_ltOn_label 1 t)
  have hleaves : t.1.leaves = [a, b] := by rw [hab]; simp
  have hnodup : [a, b].Nodup := by rw [← hleaves]; exact t.2.1
  have hne : a ≠ b := by
    have h := (List.nodup_cons.mp hnodup).1
    simpa using h
  have htof : [a, b].toFinset = (Finset.univ : Finset (Label 1)) := by
    rw [← hleaves]
    exact t.2.2
  have hall : ∀ x : Label 1, x = a ∨ x = b := by
    intro x
    have hx : x ∈ [a, b].toFinset := by rw [htof]; exact Finset.mem_univ x
    rw [List.mem_toFinset] at hx
    simpa using hx
  have hcontr : ¬ (markLabel 1 = armLabel 1 0) := by simp [armLabel, markLabel]
  rcases hall (armLabel 1 0) with h1 | h1
  · have h2 : b = markLabel 1 := by
      rcases hall (markLabel 1) with h2 | h2
      · exact absurd (h2.trans h1.symm) hcontr
      · exact h2.symm
    left
    rw [hab, ← h1, ← h2]
  · have h2 : a = markLabel 1 := by
      rcases hall (markLabel 1) with h2 | h2
      · exact h2.symm
      · exact absurd (h2.trans h1.symm) hcontr
    right
    rw [hab, ← h2, ← h1]

/-- **The labelled shape family at `p = 1` has exactly two elements.** -/
theorem card_ltOn_label_one :
    Fintype.card (LTon (Label 1) (Finset.univ : Finset (Label 1))) = 2 := by
  classical
  rw [← Finset.card_univ]
  have huniv : (Finset.univ : Finset (LTon (Label 1) (Finset.univ : Finset (Label 1))))
      = {ltOnOneLeft, ltOnOneRight} := by
    refine (Finset.eq_univ_iff_forall.mpr ?_).symm
    intro x
    rcases ltOn_label_one_eq x with h | h
    · have hx : x = ltOnOneLeft := Subtype.ext h
      rw [hx]
      exact Finset.mem_insert_self _ _
    · have hx : x = ltOnOneRight := Subtype.ext h
      rw [hx]
      exact Finset.mem_insert_of_mem (Finset.mem_singleton_self _)
  rw [huniv, Finset.card_pair ltOnOneLeft_ne_right]

/-- The number of marked shapes at `p = 1` with marked depth `2`. -/
theorem markedCount_one_two : markedCount 1 2 = 2 := by
  classical
  rw [markedCount,
    Finset.filter_true_of_mem (fun A hA => markedShapes_depth_eq_two A hA),
    card_markedShapes, card_ltOn_label_one]

/-! ## Coherence of the depth-indexed coefficients -/

/-- **No shape has marked depth `0`.**  A leaf is at distance at least one from the root. -/
theorem markedCount_eq_zero_of_lt (p ℓ : ℕ) (h : ℓ < 1) : markedCount p ℓ = 0 := by
  classical
  rw [markedCount]
  have hempty : (markedShapes p).filter (fun A => RTree.depth A.1 A.2 = ℓ) = ∅ := by
    rw [Finset.filter_eq_empty_iff]
    intro A hA heq
    have h1 := markedShapes_depth_pos p A hA
    omega
  rw [hempty, Finset.card_empty]

/-- **No shape of the family has marked depth exceeding `p+1`**: the index set `Icc 1 (p+1)` of
`markedPolygonBound` loses no shape. -/
theorem markedCount_eq_zero_of_gt (p ℓ : ℕ) (h : p + 1 < ℓ) : markedCount p ℓ = 0 := by
  classical
  rw [markedCount]
  have hempty : (markedShapes p).filter (fun A => RTree.depth A.1 A.2 = ℓ) = ∅ := by
    rw [Finset.filter_eq_empty_iff]
    intro A hA heq
    have h1 := markedShapes_depth_le p A hA
    omega
  rw [hempty, Finset.card_empty]

/-- Each coefficient is at most the size of the family. -/
theorem markedCount_le_card (p ℓ : ℕ) : markedCount p ℓ ≤ (markedShapes p).card :=
  Finset.card_filter_le _ _

/-- **The coefficients partition the family**: their sum over the depth range is the number of
labelled marked shapes.  So `markedCount p ·` is a genuine law of the marked depth on the
family, not an assumed sequence of integers. -/
theorem sum_markedCount (p : ℕ) :
    (∑ ℓ ∈ Finset.Icc 1 (p + 1), markedCount p ℓ) = (markedShapes p).card := by
  classical
  exact (Finset.card_eq_sum_card_fiberwise
    (s := markedShapes p) (f := fun A => RTree.depth A.1 A.2) (t := Finset.Icc 1 (p + 1))
    (fun A hA => Finset.mem_Icc.mpr
      ⟨markedShapes_depth_pos p A hA, markedShapes_depth_le p A hA⟩)).symm

/-- **The marked-depth coefficients at `p = 1`**: `2` at `ℓ = 2`, `0` elsewhere. -/
theorem markedCount_one (ℓ : ℕ) : markedCount 1 ℓ = if ℓ = 2 then 2 else 0 := by
  classical
  by_cases h : ℓ = 2
  · subst h
    rw [ite_eq_left rfl]
    exact markedCount_one_two
  · rw [ite_eq_right h, markedCount]
    have hempty : (markedShapes 1).filter (fun A => RTree.depth A.1 A.2 = ℓ) = ∅ := by
      rw [Finset.filter_eq_empty_iff]
      intro A hA heq
      have h2 := markedShapes_depth_eq_two A hA
      omega
    rw [hempty, Finset.card_empty]

/-- **The finite diagram expression at `p = 1`.** -/
theorem markedPolygonBound_one {W : Type v} [DecidableEq W] (χ : ℝ≥0∞)
    (k : W → W → ℝ≥0∞) (x w : W) :
    markedPolygonBound χ k 1 x w = 2 * (χ ^ 1 * I417Base.iterPow k 2 x w) := by
  classical
  rw [markedPolygonBound]
  have hsingle := Finset.sum_eq_single (s := Finset.Icc 1 2)
    (f := fun ℓ : ℕ =>
      (markedCount 1 ℓ : ℝ≥0∞) * (χ ^ (2 * 1 + 1 - ℓ) * I417Base.iterPow k ℓ x w)) 2
    (by
      intro b hb hbne
      rw [markedCount_one, ite_eq_right hbne, Nat.cast_zero, zero_mul])
    (by
      intro hmem
      exact absurd (Finset.mem_Icc.mpr ⟨by norm_num, by norm_num⟩) hmem)
  rw [hsingle, markedCount_one_two]
  norm_num

/-- **`p = 1` evaluation**: for a kernel with constant row sum `χ`, the labelled marked diagram
sum on the two labels is `2 · χ · T^2(x,w)`. -/
theorem labelledMarkedDiagram_one {W : Type v} [DecidableEq W] (k : W → W → ℝ≥0∞) (χ : ℝ≥0∞)
    (hχ : ∀ v, ∑' y, k v y = χ) (x w : W) :
    labelledMarkedDiagram k 1 x w = 2 * (χ ^ 1 * I417Base.iterPow k 2 x w) := by
  rw [labelledMarkedDiagram_eq_polygon k χ hχ 1 x w, markedPolygonBound_one]

/-! ## The `p = 0` case -/

/-- `Fin 0 ⊕ PUnit` has one element, the mark label. -/
theorem label_zero_eq (a : Label 0) : a = markLabel 0 := by
  rcases a with i | u
  · exact Fin.elim0 i
  · change Sum.inr u = Sum.inr ⟨⟩
    rfl

/-- **Every labelled shape at `p = 0` is the single marked leaf.** -/
theorem eq_ltOnZeroLeaf (t : LTon (Label 0) (Finset.univ : Finset (Label 0))) :
    t = ltOnZeroLeaf := by
  classical
  have hnum : t.1.numLeaves = 1 := by
    rw [numLeaves_ltOn t, card_label]
  obtain ⟨a, ha⟩ := eq_leaf_of_numLeaves_eq_one hnum
  refine Subtype.ext ?_
  rw [ha, label_zero_eq a]
  rfl

/-- **The labelled shape family at `p = 0` has exactly one element.** -/
theorem card_ltOn_label_zero :
    Fintype.card (LTon (Label 0) (Finset.univ : Finset (Label 0))) = 1 := by
  classical
  exact Fintype.card_eq_one_iff.mpr ⟨ltOnZeroLeaf, fun t => eq_ltOnZeroLeaf t⟩

/-- **The `p = 0` coefficient is `1`**: the family has one shape and its marked leaf has depth
`1`.  This is read off the partition identity `sum_markedCount` and the cardinality
`card_ltOn_label_zero = 1`, not assumed. -/
theorem markedCount_zero_one : markedCount 0 1 = 1 := by
  classical
  have h := sum_markedCount 0
  rw [Finset.Icc_self, Finset.sum_singleton] at h
  rw [h, card_markedShapes, card_ltOn_label_zero]

/-- **The marked-depth coefficients at `p = 0`**: `1` at `ℓ = 1`, `0` elsewhere. -/
theorem markedCount_zero (ℓ : ℕ) : markedCount 0 ℓ = if ℓ = 1 then 1 else 0 := by
  classical
  by_cases h : ℓ = 1
  · subst h
    rw [ite_eq_left rfl]
    exact markedCount_zero_one
  · rw [ite_eq_right h]
    rcases lt_or_gt_of_ne h with hlt | hgt
    · exact markedCount_eq_zero_of_lt 0 ℓ hlt
    · exact markedCount_eq_zero_of_gt 0 ℓ (by omega)

/-- **The finite diagram expression at `p = 0`**: since the only exponent is `2·0+1-1 = 0`, the
polygon bound is `T^1(x,w)` for **every** `χ` (no row-sum hypothesis).  Together with
`labelledMarkedDiagram_zero` this is an independent cross-check of the `p = 0` evaluation. -/
theorem markedPolygonBound_zero {W : Type v} [DecidableEq W] (χ : ℝ≥0∞)
    (k : W → W → ℝ≥0∞) (x w : W) :
    markedPolygonBound χ k 0 x w = I417Base.iterPow k 1 x w := by
  classical
  rw [markedPolygonBound, Finset.Icc_self, Finset.sum_singleton, markedCount_zero_one]
  simp

/-- **`p = 0` evaluation** (no constant-row-sum hypothesis): the labelled marked diagram sum is
the single shape `leaf (Sum.inr ⟨⟩)` with its leaf pinned at `w`, i.e. `T^1(x,w) = k x w`. -/
theorem labelledMarkedDiagram_zero {W : Type v} [DecidableEq W] (k : W → W → ℝ≥0∞) (x w : W) :
    labelledMarkedDiagram k 0 x w = I417Base.iterPow k 1 x w := by
  classical
  let phi : (Label 0 → W) ≃ W :=
    { toFun := fun y => y (markLabel 0)
      invFun := fun z => fun _ => z
      left_inv := fun y => by
        funext a
        rw [label_zero_eq a]
      right_inv := fun z => rfl }
  have huniv : (Finset.univ : Finset (LTon (Label 0) (Finset.univ : Finset (Label 0))))
      = {ltOnZeroLeaf} := by
    refine Finset.eq_singleton_iff_unique_mem.mpr ⟨Finset.mem_univ _, ?_⟩
    intro x _
    exact eq_ltOnZeroLeaf x
  rw [labelledMarkedDiagram, huniv, Finset.sum_singleton]
  have hleaf : ∀ y : Label 0 → W,
      PercLib.CriticalLRP.TreeExpansion.Real.posSumWtE k ltOnZeroLeaf.1 y x
        = k x (y (markLabel 0)) :=
    fun y => PercLib.CriticalLRP.TreeExpansion.Real.posSumWtE_leaf k (markLabel 0) y x
  simp only [hleaf]
  calc (∑' y : Label 0 → W, (if y (markLabel 0) = w then 1 else 0) * k x (y (markLabel 0)))
      = ∑' z : W, (if z = w then 1 else 0) * k x z :=
        Equiv.tsum_eq phi (fun z : W => (if z = w then 1 else 0) * k x z)
    _ = k x w := I417Base.tsum_indicator_mul (fun z : W => k x z) w
    _ = I417Base.iterPow k 1 x w :=
        (I417Base.tsum_mul_indicator_right (fun z : W => k x z) w).symm

/-- The `p = 0` evaluation in the `markedDiagram` presentation. -/
theorem markedDiagram_zero {W : Type v} [DecidableEq W] (k : W → W → ℝ≥0∞) (x w : W) :
    markedDiagram k 0 x w = I417Base.iterPow k 1 x w := by
  rw [← labelledMarkedDiagram_eq_markedDiagram k 0 x w, labelledMarkedDiagram_zero]

end PercLib.CriticalLRP.I417Marked
