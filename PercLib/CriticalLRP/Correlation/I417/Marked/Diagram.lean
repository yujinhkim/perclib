/- Independently rebuilt and verified at production revision
    eb9b71a3cf20a0fe9906271415f5b17efd80f5ad.
    Original scratch source is recorded below. -/
/-
An independently rebuilt direction (Ultramath swarm `smwwt6noq`, member `m2`, direction B).
Production base `4c53bb5a8e76a4358a426adf71169b916b90f51f`.
-/

module

public import PercLib.CriticalLRP.Correlation.I417.Marked.Defs

/-!
# The label-to-position API and the exact marked diagram reduction

Source: Tom Hutchcroft, *Critical long-range percolation I: high effective dimension*,
arXiv:2508.18807v1, Lemma I.4.17 and its proof (PDF p. 45):

> "Expanding each of these probabilities out as in the proof of the tree-graph inequality
> yields the claim: We obtain a bound in terms of tree diagrams with two pinned vertices at
> `x` and `y`, with `2p+2q+1` edges in total, some number `3 ≤ ℓ ≤ p+q+1` of which belong to
> the path connecting `x` and `y`. [...] In each case, `C_{p,q,ℓ}` counts the number of
> diagrams in the bound in which the path connecting `x` and `y` has length `ℓ`."

Production already contains the *analytic* half of that sentence, for an **arbitrary** finite
family of marked diagrams: `I417Base.tsum_wtE_marked` (one marked diagram of marked depth `ℓ`
is worth `χ^(2p+1-ℓ) T^ℓ(x,w)`, whatever the shape) and
`I417Base.marked_diagram_by_depth` (a finite family collapses to
`∑_ℓ C_ℓ χ^(2p+1-ℓ) T^ℓ(x,w)`).

What production does not have is the **combinatorial** half at the labelled level for the base
event of Lemma I.4.17, `E[|K_x|^p 1(w ∈ K_x)]`, whose terminal set is the *labelled* set
`Fin p ⊕ PUnit` with one distinguished mark.  This file supplies it:

* `markPos_spec`, `markPos_unique`, `existsUnique_markPos`, `card_filter_markPos` -- the marked
  leaf position is *determined by the mark label*, exactly one position carries it, and a
  shape family can therefore be indexed by labelled trees rather than by `(tree, position)`
  pairs chosen by hand;
* `depth_pos`, `markDepth_pos`, `markDepth_le`, `numLeaves_ltOn` -- the elementary depth
  constraints: a `p+1`-leaf tree has its marked leaf at depth `ℓ` with `1 ≤ ℓ ≤ p+1`, so the
  polygon sum of the source is over `ℓ ∈ [1, p+1]` and every exponent `2p+1-ℓ` is untruncated;
* `markedDiagram_eq_polygon` -- the finite *marked* diagram sum of the genuine labelled family
  `markedShapes p` equals `markedPolygonBound`, by real instantiation of
  `I417Base.marked_diagram_by_depth` (so the coefficients are the explicit cardinalities
  `markedCount p ℓ`);
* `labelledMarkedDiagram_eq_polygon` -- the same sum in **label form**: leaf labels summed
  over, the mark pinned at `w`, and each shape weighted by the *atlas product over its
  internal positions* (`Real.posSumWtE`, i.e. the finite `∑_φ ∏_e k (src e) (dst e)` of
  `AtlasRealization.WeightBridge`).  This is the shape of the right-hand side of
  `Real.prob_le_sum_shapes`, and `Real.posSumWtE_eq_wtE` is the bridge used.

Two small reindexing lemmas are proved here because production does not have them for the
labelled family: `leafOfPos_bijective` (`leafOfPos` is a bijection onto the label set for an
injectively labelled shape whose leaf set is *all* labels) and `tsum_label_eq_tsum_leafPos`
(change of variables from label assignments to leaf-position assignments).

## Source discrepancies

None: this file is the diagram (combinatorial-analytic) layer only.  The only hypothesis is a
**constant row sum** `χ` for the kernel, the abstract form of `E|K_v| = E|K|`.  Nothing is
claimed about the value of `markedCount p ℓ` for general `p`; the `(2p-1)!!` total and the
two-copy `q` side are open.
-/

set_option autoImplicit false
set_option linter.unusedSectionVars false

open scoped ENNReal NNReal

@[expose] public section

namespace PercLib.CriticalLRP.I417Marked

open PercLib.CriticalLRP.TreeExpansion

universe u v

/-! ## The marked leaf position is determined by the mark label -/

/-- **The label-to-position spec**: the leaf position chosen by `markPos` really does carry the
label `m`, whenever `m` occurs as a leaf label. -/
theorem markPos_spec {α : Type u} [DecidableEq α] {m : α} {t : RTree α} (h : m ∈ t.leaves) :
    RTree.leafOfPos t (markPos m t) = m := by
  simp only [markPos, h, ↓reduceDIte]
  exact Classical.choose_spec (RTree.exists_leafOfPos t m h)

/-- **Uniqueness of the marked leaf position**: on an injectively labelled tree there is at most
one leaf position carrying the label `m`. -/
theorem markPos_unique {α : Type u} [DecidableEq α] {m : α} {t : RTree α}
    (hnodup : t.leaves.Nodup) {q : t.LeafPos} (hq : RTree.leafOfPos t q = m)
    (h : m ∈ t.leaves) : q = markPos m t :=
  RTree.leafOfPos_injective hnodup (by rw [hq, markPos_spec h])

/-- **Exactly one leaf position carries the marked label.** -/
theorem existsUnique_markPos {α : Type u} {m : α} {t : RTree α}
    (hnodup : t.leaves.Nodup) (h : m ∈ t.leaves) :
    ∃! q : t.LeafPos, RTree.leafOfPos t q = m := by
  classical
  exact ⟨markPos m t, markPos_spec h, fun _ hq => markPos_unique hnodup hq h⟩

/-- **One** leaf position carries the marked label: its cardinality count is `1`, not assumed. -/
theorem card_filter_markPos {α : Type u} [DecidableEq α] {m : α} {t : RTree α}
    (hnodup : t.leaves.Nodup) (h : m ∈ t.leaves) :
    (Finset.univ.filter (fun q : t.LeafPos => RTree.leafOfPos t q = m)).card = 1 := by
  refine Finset.card_eq_one.mpr ⟨markPos m t, ?_⟩
  ext q
  simp only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_singleton]
  exact ⟨fun hq => markPos_unique hnodup hq h, fun hq => by rw [hq, markPos_spec h]⟩

/-! ## The elementary depth constraints -/

/-- **Every leaf of a binary tree hangs at depth at least one.**  (`RTree.depth` counts the
edges of the root-to-leaf path, so a leaf of a single-leaf tree has depth `1`.) -/
theorem depth_pos {α : Type u} : ∀ (t : RTree α) (q : t.LeafPos), 1 ≤ RTree.depth t q
  | RTree.leaf _, _ => le_refl 1
  | RTree.node l _, Sum.inl q => by
      have h : 1 ≤ RTree.depth l q := depth_pos l q
      change 1 ≤ RTree.depth l q + 1
      omega
  | RTree.node _ r, Sum.inr q => by
      have h : 1 ≤ RTree.depth r q := depth_pos r q
      change 1 ≤ RTree.depth r q + 1
      omega

/-- The marked depth is at least one. -/
theorem markDepth_pos {α : Type u} [DecidableEq α] (m : α) (t : RTree α) :
    1 ≤ markDepth m t :=
  depth_pos t (markPos m t)

/-- The marked depth is at most the number of leaves. -/
theorem markDepth_le_numLeaves {α : Type u} [DecidableEq α] (m : α) (t : RTree α) :
    markDepth m t ≤ t.numLeaves :=
  RTree.depth_le_numLeaves t (markPos m t)

/-- **A labelled shape on all of `Fin p ⊕ PUnit` has exactly `p+1` leaves**, because its leaf
list is a nodup list with leaf set the whole label set. -/
theorem numLeaves_ltOn {α : Type u} [Fintype α] [DecidableEq α]
    (t : LTon α (Finset.univ : Finset α)) : t.1.numLeaves = Fintype.card α := by
  have h := t.2
  rw [RTree.numLeaves, ← List.toFinset_card_of_nodup h.1, h.2, Finset.card_univ]

/-- The mark label occurs as a leaf label of a shape on all of `Fin p ⊕ PUnit`. -/
theorem markLabel_mem (p : ℕ) (t : LTon (Label p) (Finset.univ : Finset (Label p))) :
    markLabel p ∈ t.1.leaves := by
  rw [← List.mem_toFinset, t.2.2]
  exact Finset.mem_univ _

/-- **The marked depth bound at `p`**: for a labelled shape on all of `Fin p ⊕ PUnit` the marked
leaf has depth `1 ≤ ℓ ≤ p+1`.  Consequently the source's polygon sum runs over `ℓ ∈ [1,p+1]`
and every exponent `2p+1-ℓ` is an untruncated subtraction. -/
theorem markDepth_le (p : ℕ) (t : LTon (Label p) (Finset.univ : Finset (Label p))) :
    markDepth (markLabel p) t.1 ≤ p + 1 := by
  have h := markDepth_le_numLeaves (markLabel p) t.1
  have h2 : t.1.numLeaves = p + 1 := by
    rw [numLeaves_ltOn t, Fintype.card_sum, Fintype.card_fin, Fintype.card_punit]
  omega

/-! ## The marked shape family -/

/-- **The cardinality of the label type**: `p` arm labels and one mark. -/
theorem card_label (p : ℕ) : Fintype.card (Label p) = p + 1 := by
  rw [Fintype.card_sum, Fintype.card_fin, Fintype.card_punit]

/-- A labelled shape on all of `Fin p ⊕ PUnit` has `p+1` leaves. -/
theorem numLeaves_ltOn_label (p : ℕ) (t : LTon (Label p) (Finset.univ : Finset (Label p))) :
    t.1.numLeaves = p + 1 := by
  rw [numLeaves_ltOn t, card_label p]

/-- Every marked shape of the family has `p+1` leaves. -/
theorem markedShapes_numLeaves (p : ℕ) : ∀ A ∈ markedShapes p, A.1.numLeaves = p + 1 := by
  intro A hA
  classical
  rw [markedShapes, Finset.mem_image] at hA
  obtain ⟨t, -, ht⟩ := hA
  rw [← ht]
  exact numLeaves_ltOn_label p t

/-- Every marked shape of the family has marked depth at least one. -/
theorem markedShapes_depth_pos (p : ℕ) : ∀ A ∈ markedShapes p, 1 ≤ RTree.depth A.1 A.2 := by
  intro A hA
  classical
  rw [markedShapes, Finset.mem_image] at hA
  obtain ⟨t, -, ht⟩ := hA
  rw [← ht]
  exact depth_pos t.1 (markPos (markLabel p) t.1)

/-- Every marked shape of the family has marked depth at most `p+1`. -/
theorem markedShapes_depth_le (p : ℕ) : ∀ A ∈ markedShapes p, RTree.depth A.1 A.2 ≤ p + 1 := by
  intro A hA
  classical
  rw [markedShapes, Finset.mem_image] at hA
  obtain ⟨t, -, ht⟩ := hA
  rw [← ht]
  exact markDepth_le p t

/-- The family has one shape per labelled tree on all of `Fin p ⊕ PUnit`, so its cardinality is
the number of labelled shapes -- the coefficient `markedCount` is counting a genuine family. -/
theorem card_markedShapes (p : ℕ) :
    (markedShapes p).card = Fintype.card (LTon (Label p) (Finset.univ : Finset (Label p))) := by
  classical
  have hinj : Function.Injective
      (fun t : LTon (Label p) (Finset.univ : Finset (Label p)) =>
        (⟨t.1, markPos (markLabel p) t.1⟩ : MarkedShape p)) :=
    fun a b hab => Subtype.ext (congrArg Sigma.fst hab)
  rw [markedShapes, Finset.card_image_of_injective _ hinj, Finset.card_univ]

/-- **Reindexing the family by the labelled trees it comes from.** -/
theorem sum_markedShapes {p : ℕ} {M : Type*} [AddCommMonoid M] (F : MarkedShape p → M) :
    (∑ A ∈ markedShapes p, F A) =
      ∑ t : LTon (Label p) (Finset.univ : Finset (Label p)),
        F ⟨t.1, markPos (markLabel p) t.1⟩ := by
  classical
  have hinj : Set.InjOn
      (fun t : LTon (Label p) (Finset.univ : Finset (Label p)) =>
        (⟨t.1, markPos (markLabel p) t.1⟩ : MarkedShape p))
      ↑(Finset.univ : Finset (LTon (Label p) (Finset.univ : Finset (Label p)))) :=
    fun a _ b _ hab => Subtype.ext (congrArg Sigma.fst hab)
  rw [markedShapes, Finset.sum_image (f := F) hinj]

/-! ## The labelled diagram sum reduces to the marked diagram sum -/

/-- **`leafOfPos` is a bijection** for an injectively labelled tree whose leaf set is *all* of
the finite label type: it is injective by `Nodup`, and surjective because every label occurs. -/
theorem leafOfPos_bijective {α : Type u} [Fintype α] [DecidableEq α]
    (t : LTon α (Finset.univ : Finset α)) : Function.Bijective (RTree.leafOfPos t.1) := by
  refine ⟨RTree.leafOfPos_injective t.2.1, fun a => ?_⟩
  exact RTree.exists_leafOfPos t.1 a (by
    rw [← List.mem_toFinset, t.2.2]
    exact Finset.mem_univ a)

/-- **Change of variables from label assignments to leaf-position assignments**, for a labelling
that is a bijection onto the label set. -/
theorem tsum_label_eq_tsum_leafPos {α : Type u} [Fintype α] [DecidableEq α] {W : Type v}
    (t : LTon α (Finset.univ : Finset α)) (G : (t.1.LeafPos → W) → ℝ≥0∞) :
    (∑' y : α → W, G (fun q => y (RTree.leafOfPos t.1 q))) =
      ∑' ζ : t.1.LeafPos → W, G ζ := by
  classical
  let e : t.1.LeafPos ≃ α := Equiv.ofBijective (RTree.leafOfPos t.1) (leafOfPos_bijective t)
  let φ : (α → W) ≃ (t.1.LeafPos → W) :=
    { toFun := fun (y : α → W) (q : t.1.LeafPos) => y (RTree.leafOfPos t.1 q)
      invFun := fun (ζ : t.1.LeafPos → W) (a : α) => ζ (e.symm a)
      left_inv := fun (y : α → W) => by
        funext a
        exact congrArg y (Equiv.apply_symm_apply e a)
      right_inv := fun (ζ : t.1.LeafPos → W) => by
        funext q
        exact congrArg ζ (Equiv.symm_apply_apply e q) }
  exact Equiv.tsum_eq φ G

/-- **One labelled shape's contribution.**  The atlas product over the internal positions of a
labelled shape, summed over all label assignments with the mark pinned at `w`, is the tree
weight with the leaf carrying the mark pinned at `w`. -/
theorem labelled_shape_eq {W : Type v} [DecidableEq W] (k : W → W → ℝ≥0∞) (p : ℕ) (x w : W)
    (t : LTon (Label p) (Finset.univ : Finset (Label p))) :
    (∑' y : Label p → W,
        (if y (markLabel p) = w then 1 else 0) *
          PercLib.CriticalLRP.TreeExpansion.Real.posSumWtE k t.1 y x)
      = ∑' ζ : t.1.LeafPos → W,
          (if ζ (markPos (markLabel p) t.1) = w then 1 else 0) * I417Base.wtE k t.1 ζ x := by
  classical
  have h1 : (∑' y : Label p → W,
        (if y (markLabel p) = w then 1 else 0) *
          PercLib.CriticalLRP.TreeExpansion.Real.posSumWtE k t.1 y x)
      = ∑' y : Label p → W,
          (if y (RTree.leafOfPos t.1 (markPos (markLabel p) t.1)) = w then 1 else 0) *
            I417Base.wtE k t.1 (fun q => y (RTree.leafOfPos t.1 q)) x := by
    refine tsum_congr fun y => ?_
    have hpos : y (RTree.leafOfPos t.1 (markPos (markLabel p) t.1)) = y (markLabel p) := by
      rw [markPos_spec (markLabel_mem p t)]
    rw [hpos, PercLib.CriticalLRP.TreeExpansion.Real.posSumWtE_eq_wtE k t.1 y x]
  rw [h1]
  exact tsum_label_eq_tsum_leafPos (W := W) t (G := fun (ζ : t.1.LeafPos → W) =>
    (if ζ (markPos (markLabel p) t.1) = w then 1 else 0) * I417Base.wtE k t.1 ζ x)

/-- **The label form of the marked diagram sum is the marked diagram sum.** -/
theorem labelledMarkedDiagram_eq_markedDiagram {W : Type v} [DecidableEq W]
    (k : W → W → ℝ≥0∞) (p : ℕ) (x w : W) :
    labelledMarkedDiagram k p x w = markedDiagram k p x w := by
  classical
  rw [labelledMarkedDiagram, markedDiagram, sum_markedShapes]
  exact Finset.sum_congr rfl fun t _ => labelled_shape_eq k p x w t

/-! ## The exact marked diagram reduction -/

/-- **The finite marked diagram sum of the genuine labelled family collapses to the finite
diagram expression.**  For a kernel with constant row sum `χ`, the sum over the labelled marked
shapes `A` of the family -- each contributing its tree weight `wtE k A.1 · x` with the marked
leaf `A.2` pinned at `w` -- equals

  `∑_{ℓ=1}^{p+1} markedCount p ℓ · χ^(2p+1-ℓ) · T^ℓ(x,w)`.

This is a real instantiation of the production theorem `I417Base.marked_diagram_by_depth`
(itself built on `tsum_wtE_marked` and `pathW_eq_iterPow`), with the family, its leaf count and
its depth range *proved*, not assumed.  The coefficient `markedCount p ℓ` is the explicit
cardinality `#{A ∈ markedShapes p | depth A = ℓ}`. -/
theorem markedDiagram_eq_polygon {W : Type v} [DecidableEq W] (k : W → W → ℝ≥0∞) (χ : ℝ≥0∞)
    (hχ : ∀ v, ∑' y, k v y = χ) (p : ℕ) (x w : W) :
    markedDiagram k p x w = markedPolygonBound χ k p x w := by
  have h := I417Base.marked_diagram_by_depth k χ hχ p 1 (p + 1) (markedShapes p)
    (markedShapes_numLeaves p) (markedShapes_depth_pos p) (markedShapes_depth_le p) x w
  simpa only [markedDiagram, markedPolygonBound, markedCount] using h

/-- **The capstone, in the form matching the right-hand side of `Real.prob_le_sum_shapes`.**
The labelled marked diagram sum -- leaf labels summed over, the mark pinned at `w`, each shape
weighted by the sum over its internal positions of the atlas edge product -- is exactly the
finite expression `∑_{ℓ=1}^{p+1} markedCount p ℓ · χ^(2p+1-ℓ) · T^ℓ(x,w)`. -/
theorem labelledMarkedDiagram_eq_polygon {W : Type v} [DecidableEq W] (k : W → W → ℝ≥0∞)
    (χ : ℝ≥0∞) (hχ : ∀ v, ∑' y, k v y = χ) (p : ℕ) (x w : W) :
    labelledMarkedDiagram k p x w = markedPolygonBound χ k p x w := by
  rw [labelledMarkedDiagram_eq_markedDiagram, markedDiagram_eq_polygon k χ hχ p x w]

end PercLib.CriticalLRP.I417Marked
