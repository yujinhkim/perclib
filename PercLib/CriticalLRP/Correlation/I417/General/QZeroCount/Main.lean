/-
Ultramath swarm `smwziumdb`, member `m6`, direction `d1` (branch-and-root tree count).

Copyright (c) 2026 PercLib contributors. Released under Apache 2.0.

Accepted and independently rebuilt from Ultramath `smwziumdb`.
Supporting integration based on production commit `5d2d681b941eb1c687f1ba17e6a798b8f0175aa0`.

# The branch-and-root evaluation of the `(p,q) = (3,0)` star tree sum

Source: T. Hutchcroft, *Critical long-range percolation I: High effective dimension*,
arXiv:2508.18807v1, (I.2.2)–(I.2.3) p. 22, and Lemma I.4.17 / Proposition I.4.15 Case 3
(pp. 45-47).

`Defs.lean` defines `reps Z`, the canonical family of representatives of the non-plane rooted
binary trees with leaf set `Z`, by the branch-and-root recursion of (I.2.2) over the split
family `splits Z (base Z)` of production's `TS_recursion`.

This file proves the exact evaluation

  `TS k Z y v = ∑ t ∈ reps Z, RTree.wtL k t y v`     (`TS_eq_sum_reps`)

for every finite nonempty label set `Z`.  Equivalently (`sum_LT_eq_sum_reps`), the sum of
`wtL` over *all* plane rooted binary trees with `p` leaves — the object production normalizes
by `2^{-(p-1)}` in `treeSum k p v x` — is exactly `2^(p-1)` times the sum over the `reps`,
because a non-plane class has `2^(p-1)` orientations, one per internal node.

At `Z = Fin 4` this gives, by evaluation:

* `card_reps_four`  : the *count* `#{reps (Fin 4)} = 15 = 5!!`, the number of isomorphism
  classes of trees with five labelled leaves and all non-leaf vertices of degree three
  (the `(2p-3)!!` of (I.2.3) at `p = 4`);
* `ell_two_card`, `ell_three_card`, `ell_four_card` : the distribution `(3, 6, 6)` of the
  length `ℓ` of the tree path from the pinned root `x` to the target leaf `y`;
* `shape_two_card`, `shape_threeA_card`, `shape_threeB_card`, `shape_four_card` : the
  multiplicities `(3, 3, 3, 6)` of the four shapes of the accepted `m1` atlas
  (`3·shapeTwo + 3·shapeThreeA + 3·shapeThreeB + 6·shapeFour`);
* `atlasEdges_image` : the fifteen representatives are exactly `m1`'s fifteen seven-edge
  atlas diagrams, so that list is complete and duplicate-free.

## Consequence for the `ℓ`-range of Lemma I.4.17

Lemma I.4.17 asserts a range `3 ≤ ℓ ≤ p + q + 1`.  At `(p,q) = (3,0)` this would say
`ℓ ∈ {3,4}`; `ell_two_card` shows that the direct tree-graph evaluation of the `(3,0)` star
has **three** summands with `ℓ = 2`, so the printed range is not available at `q = 0`.  This
matches the accepted `m1` finding (`Defs.shapeTwo`, `no_uniform_ell_two_absorption`), now
derived from the branch-and-root recursion itself rather than from a hand-made list.
-/
module

public import PercLib.CriticalLRP.TreeExpansion.TreeSumRecursionFull
public import Mathlib
public import PercLib.CriticalLRP.Correlation.I417.General.QZeroCount.Defs

/-! # Exact evaluation and arithmetic of the branch-and-root tree family -/

@[expose] public section

noncomputable section

open Finset

namespace PercLib.CriticalLRP.QZeroStarCount

open PercLib.CriticalLRP.TreeExpansion
open PercLib.CriticalLRP.TreeGraph

set_option linter.unusedSectionVars false
set_option maxRecDepth 400000

variable {α : Type*} [LinearOrder α] [Inhabited α]

/-! ## Factoring a two-sided tree sum -/

/-- Pulling a threefold sum apart: the algebraic step of the branch-and-root recursion, in the
form needed for `Finset`-indexed label families. -/
theorem sum_finset_factor {ι κ V : Type*} [Fintype V]
    {s : Finset ι} {t : Finset κ} (f : V → ℝ) (A : ι → V → ℝ) (B : κ → V → ℝ) :
    (∑ i ∈ s, ∑ j ∈ t, ∑ w : V, f w * A i w * B j w)
      = ∑ w : V, f w * ((∑ i ∈ s, A i w) * (∑ j ∈ t, B j w)) := by
  calc ∑ i ∈ s, ∑ j ∈ t, ∑ w : V, f w * A i w * B j w
      = ∑ i ∈ s, ∑ w : V, ∑ j ∈ t, f w * A i w * B j w :=
        Finset.sum_congr rfl fun i _ => Finset.sum_comm
    _ = ∑ w : V, ∑ i ∈ s, ∑ j ∈ t, f w * A i w * B j w := Finset.sum_comm
    _ = ∑ w : V, ∑ i ∈ s, (f w * A i w) * (∑ j ∈ t, B j w) := by
        refine Finset.sum_congr rfl fun w _ => Finset.sum_congr rfl fun i _ => ?_
        rw [Finset.mul_sum]
    _ = ∑ w : V, (∑ i ∈ s, f w * A i w) * (∑ j ∈ t, B j w) := by
        refine Finset.sum_congr rfl fun w _ => ?_
        exact (Finset.sum_mul ..).symm
    _ = ∑ w : V, f w * ((∑ i ∈ s, A i w) * (∑ j ∈ t, B j w)) := by
        refine Finset.sum_congr rfl fun w _ => ?_
        rw [← Finset.mul_sum]
        ring

/-- The tree sum at a single label, with no `DecidableEq` hypothesis on the vertex type. -/
theorem TS_singleton' {V : Type*} [Fintype V] (k : V → V → ℝ) (a : α) (y : α → V) (v : V) :
    TS k ({a} : Finset α) y v = k v (y a) := by
  rw [TS, OnTrees, show ({a} : Finset α).card = 1 by simp]
  norm_num
  have hsub : Subsingleton (LTon α {a}) :=
    PercLib.CriticalLRP.TreeGraph.LTon.subsingleton_singleton a
  rw [Finset.sum_eq_single (⟨RTree.leaf a, by simp⟩ : LTon α {a})]
  · simp
  · intro b _ hb
    exact absurd (hsub.elim b _) hb
  · intro h
    exact absurd (Finset.mem_univ _) h

/-! ## The exact branch-and-root evaluation of the tree sum -/

/-- **The branch-and-root evaluation of the tree sum.**  For every finite nonempty label set
`Z`, the normalized tree sum `TS` of (I.2.2) equals the sum of the leaf-labelled weights over
the canonical representatives of the non-plane trees with leaf set `Z`.

Proof: strong induction on `Z.card`.  At `|Z| = 1` both sides are `k v (y a)`.  For `|Z| ≥ 2`,
`TS_recursion` cuts `TS k Z y v` at the branch point into the splits `A ∈ splits Z (base Z)`, and
`reps_eq` cuts `reps Z` the same way; the two cuts agree term by term after
`Finset.sum_biUnion` (the pieces are disjoint by `leaves_reps`), `Finset.sum_image` (the two
children are recovered from the parent), `RTree.wtL_node`, `sum_finset_factor`, and the
induction hypothesis at the two smaller leaf sets `A` and `Z \ A`. -/
theorem TS_eq_sum_reps {V : Type*} [Fintype V] (k : V → V → ℝ) (y : α → V) :
    ∀ (n : ℕ) (Z : Finset α) (v : V), Z.card = n → Z.Nonempty →
      TS k Z y v = ∑ t ∈ reps Z, RTree.wtL k t y v := by
  intro n
  induction n using Nat.strong_induction_on with
  | _ n ih =>
    intro Z v hc hZ
    have hpos : 0 < Z.card := Finset.card_pos.mpr hZ
    rcases Nat.lt_or_ge Z.card 2 with h1 | h2
    · -- a single label
      have hc1 : Z.card = 1 := by omega
      obtain ⟨a, rfl⟩ := Finset.card_eq_one.mp hc1
      have hR : reps ({a} : Finset α) = {RTree.leaf a} := by
        rw [show reps ({a} : Finset α) = repsAux 1 {a} from rfl,
          repsAux_succ_of_one_le (n := 0) (by simp)]
        simp
      have hsum : (∑ t ∈ ({RTree.leaf a} : Finset (RTree α)), RTree.wtL k t y v)
          = k v (y a) := by
        rw [Finset.sum_singleton, RTree.wtL_leaf]
      refine (TS_singleton' k a y v).trans ?_
      rw [hR]
      exact hsum.symm
    · -- at least two labels: cut both sides at the branch point
      have ha₀ : base Z ∈ Z := base_mem hZ
      -- disjointness of the split pieces
      have hdisj : Set.PairwiseDisjoint (↑(splits Z (base Z)) : Set (Finset α))
          (fun A => (reps A).biUnion fun l => (reps (Z \ A)).image (RTree.node l)) := by
        rintro A hA B hB hne
        have hd : Disjoint ((reps A).biUnion fun l => (reps (Z \ A)).image (RTree.node l))
            ((reps B).biUnion fun l => (reps (Z \ B)).image (RTree.node l)) := by
          rw [Finset.disjoint_left]
          intro t htA htB
          simp only [Finset.mem_biUnion, Finset.mem_image] at htA htB
          obtain ⟨l, hl, r, hr, rfl⟩ := htA
          obtain ⟨l', hl', r', hr', hEq⟩ := htB
          have hll : l = l' := ((RTree.node.injEq l' r' l r).mp hEq).1.symm
          subst hll
          exact hne ((leaves_reps_of hl).symm.trans (leaves_reps_of hl'))
        exact hd
      -- disjointness of the two children at a fixed split
      have hdisj2 : ∀ A ∈ splits Z (base Z),
          Set.PairwiseDisjoint (↑(reps A) : Set (RTree α))
            (fun l => (reps (Z \ A)).image (RTree.node l)) := by
        rintro A hA l hl l' hl' hne
        have hd : Disjoint ((reps (Z \ A)).image (RTree.node l))
            ((reps (Z \ A)).image (RTree.node l')) := by
          rw [Finset.disjoint_left]
          intro t ht ht'
          simp only [Finset.mem_image] at ht ht'
          obtain ⟨r, hr, rfl⟩ := ht
          obtain ⟨r', hr', hEq⟩ := ht'
          exact hne (((RTree.node.injEq l' r' l r).mp hEq).1).symm
        exact hd
      -- the two children are recovered from the parent
      have hinj : ∀ A ∈ splits Z (base Z), ∀ l ∈ reps A,
          Set.InjOn (RTree.node l) ↑(reps (Z \ A)) := by
        intro A hA l hl r hr r' hr' hEq
        exact ((RTree.node.injEq l r l r').mp hEq).2
      -- cardinality bounds for the induction hypothesis
      have hAne : ∀ A ∈ splits Z (base Z), A.Nonempty := fun A hA => (mem_splits hA).2.1
      have hBne : ∀ A ∈ splits Z (base Z), (Z \ A).Nonempty := by
        intro A hA
        rw [Finset.sdiff_nonempty]
        intro hsub
        exact (mem_splits hA).2.2.1 (Finset.Subset.antisymm (mem_splits hA).1 hsub)
      have hAcard : ∀ A ∈ splits Z (base Z), A.card < n := by
        intro A hA
        have := Finset.card_lt_card
          (Finset.ssubset_iff_subset_ne.mpr ⟨(mem_splits hA).1, (mem_splits hA).2.2.1⟩)
        omega
      have hBcard : ∀ A ∈ splits Z (base Z), (Z \ A).card < n := by
        intro A hA
        have hlt : (Z \ A).card < Z.card :=
          Finset.card_lt_card (Finset.ssubset_iff_subset_ne.mpr ⟨Finset.sdiff_subset, by
            intro hEq
            obtain ⟨a, ha⟩ := (mem_splits hA).2.1
            have hsub : A ⊆ Z \ A := by rw [hEq]; exact (mem_splits hA).1
            exact (Finset.mem_sdiff.mp (hsub ha)).2 ha⟩)
        omega
      rw [reps_eq h2, TS_recursion k y v ha₀ h2, Finset.sum_biUnion hdisj]
      refine Finset.sum_congr rfl fun A hA => ?_
      rw [Finset.sum_biUnion (hdisj2 A hA)]
      rw [Finset.sum_congr rfl fun l hl => Finset.sum_image (hinj A hA l hl)]
      simp only [RTree.wtL_node]
      rw [sum_finset_factor (f := fun w => k v w) (A := fun l w => RTree.wtL k l y w)
        (B := fun r w => RTree.wtL k r y w) (s := reps A) (t := reps (Z \ A))]
      refine Finset.sum_congr rfl fun w _ => ?_
      rw [← ih A.card (hAcard A hA) A w rfl (hAne A hA),
        ← ih (Z \ A).card (hBcard A hA) (Z \ A) w rfl (hBne A hA)]
      ring

/-! ## Consequences at four labels -/

/-- The tree sum at four labels is the sum over the fifteen canonical representatives. -/
theorem TS_fin_four_eq_sum_reps {V : Type*} [Fintype V] (k : V → V → ℝ)
    (y : Fin 4 → V) (v : V) :
    TS k (Finset.univ : Finset (Fin 4)) y v
      = ∑ t ∈ reps (Finset.univ : Finset (Fin 4)), RTree.wtL k t y v :=
  TS_eq_sum_reps k y 4 Finset.univ v (by simp) ⟨(0 : Fin 4), Finset.mem_univ 0⟩

/-- **`#{reps (Fin 4)} = 15`**: the number of isomorphism classes of trees with five labelled
leaves and all non-leaf vertices of degree three, i.e. the `(2p-3)!!` of (I.2.3) at `p = 4`. -/
theorem card_reps_four : (reps (Finset.univ : Finset (Fin 4))).card = 15 := by
  decide

/-- Three of the fifteen representatives have tree path `x → y` of length `ℓ = 2`. -/
theorem ell_two_card :
    ((reps (Finset.univ : Finset (Fin 4))).filter (fun t => ellOf t = 2)).card = 3 := by
  decide

/-- Six have `ℓ = 3`. -/
theorem ell_three_card :
    ((reps (Finset.univ : Finset (Fin 4))).filter (fun t => ellOf t = 3)).card = 6 := by
  decide

/-- Six have `ℓ = 4`. -/
theorem ell_four_card :
    ((reps (Finset.univ : Finset (Fin 4))).filter (fun t => ellOf t = 4)).card = 6 := by
  decide

/-- No representative has `ℓ` outside `{2, 3, 4}`. -/
theorem ell_mem :
    ∀ t ∈ reps (Finset.univ : Finset (Fin 4)), ellOf t = 2 ∨ ellOf t = 3 ∨ ellOf t = 4 := by
  decide

/-- The leftmost leaf of every canonical representative carries the least label, `0`; hence
`depthZero` (and with it `ellOf`) measures the depth of the target leaf `y`. -/
theorem leftmost_reps_four :
    ∀ t ∈ reps (Finset.univ : Finset (Fin 4)), leftmost t = 0 := by
  decide

/-- The `ℓ = 2` shape has multiplicity three. -/
theorem shape_two_card :
    ((reps (Finset.univ : Finset (Fin 4))).filter (fun t => shapeOf t = Shape.two)).card = 3 := by
  decide

/-- The `ℓ = 3` balanced shape has multiplicity three. -/
theorem shape_threeA_card :
    ((reps (Finset.univ : Finset (Fin 4))).filter (fun t => shapeOf t = Shape.threeA)).card
      = 3 := by
  decide

/-- The `ℓ = 3` chain shape has multiplicity three. -/
theorem shape_threeB_card :
    ((reps (Finset.univ : Finset (Fin 4))).filter (fun t => shapeOf t = Shape.threeB)).card
      = 3 := by
  decide

/-- The `ℓ = 4` chain shape has multiplicity six. -/
theorem shape_four_card :
    ((reps (Finset.univ : Finset (Fin 4))).filter (fun t => shapeOf t = Shape.four)).card
      = 6 := by
  decide

/-- Every representative is in exactly one of the four shape classes. -/
theorem shape_cases :
    ∀ t ∈ reps (Finset.univ : Finset (Fin 4)),
      shapeOf t = Shape.two ∨ shapeOf t = Shape.threeA ∨ shapeOf t = Shape.threeB
        ∨ shapeOf t = Shape.four := by
  decide

/-- The shape class `two` is exactly the class with `ℓ = 2`. -/
theorem shape_two_iff_ell_two :
    (reps (Finset.univ : Finset (Fin 4))).filter (fun t => shapeOf t = Shape.two)
      = (reps (Finset.univ : Finset (Fin 4))).filter (fun t => ellOf t = 2) := by
  decide

/-- The two `ℓ = 3` shape classes together are exactly the class with `ℓ = 3`. -/
theorem shape_three_iff_ell_three :
    (reps (Finset.univ : Finset (Fin 4))).filter
        (fun t => shapeOf t = Shape.threeA ∨ shapeOf t = Shape.threeB)
      = (reps (Finset.univ : Finset (Fin 4))).filter (fun t => ellOf t = 3) := by
  decide

/-- The shape class `four` is exactly the class with `ℓ = 4`. -/
theorem shape_four_iff_ell_four :
    (reps (Finset.univ : Finset (Fin 4))).filter (fun t => shapeOf t = Shape.four)
      = (reps (Finset.univ : Finset (Fin 4))).filter (fun t => ellOf t = 4) := by
  decide

/-- Each representative has exactly seven edges in its atlas diagram (the `2p + 2q + 1 = 7`
of Lemma I.4.17 at `(p,q) = (3,0)`). -/
theorem atlasEdges_length :
    ∀ t ∈ reps (Finset.univ : Finset (Fin 4)), (atlasEdges t).length = 7 := by
  decide

/-- **The `m1` atlas is exactly the branch-and-root family.**  The fifteen seven-edge diagrams
of the accepted `m1` atlas are precisely the fifteen canonical representatives of
`reps (Fin 4)`, read in the `m1` node coding.  Together with `card_reps_four` this proves that
the `m1` list is complete (it misses no isomorphism class of five-leaf trees) and
duplicate-free. -/
theorem atlasDiagramSets_card : atlasDiagramSets.card = 15 := by
  decide

/-- Every one of the fifteen `m1` atlas diagrams is (up to relabelling the three internal
vertices) one of the fifteen canonical branch-and-root representatives. -/
theorem atlasDiagramSets_iso_reps :
    ∀ l ∈ atlasDiagramSets, ∃ t ∈ reps (Finset.univ : Finset (Fin 4)),
      (atlasEdges t).toFinset ∈ isoClass l := by
  decide

/-- Conversely, every canonical representative is (up to internal relabelling) one of the
fifteen `m1` atlas diagrams. -/
theorem reps_iso_atlasDiagramSets :
    ∀ t ∈ reps (Finset.univ : Finset (Fin 4)), ∃ l ∈ atlasDiagramSets,
      (atlasEdges t).toFinset ∈ isoClass l := by
  decide


/-- The fifteen `m1` diagrams are pairwise non-isomorphic: no member of `atlasDiagramSets` is
isomorphic to a different member. -/
theorem atlasDiagramSets_pairwise :
    (atlasDiagramSets.biUnion fun l => (isoClass l ∩ atlasDiagramSets).erase l).card = 0 := by
  decide

/-- The fifteen canonical representatives are pairwise non-isomorphic, so the branch-and-root
family really is a family of *representatives* of isomorphism classes. -/
theorem repsDiagramSets_pairwise :
    (repsDiagramSets.biUnion fun s => (isoClass s ∩ repsDiagramSets).erase s).card = 0 := by
  decide

/-- **The `m1` atlas is the branch-and-root family.**  The isomorphism closure of the fifteen
canonical representatives is exactly the isomorphism closure of the fifteen `m1` atlas diagrams:
up to relabelling the unlabelled internal vertices the two lists are the same family.  Combined
with `card_reps_four` (`15` representatives), `atlasDiagramSets_card` (`15` diagrams) and the
pairwise non-isomorphism of both families, this says that the `m1` list is complete — it omits
no isomorphism class of trees with five labelled leaves — and duplicate-free. -/
theorem atlasIsoClosure_eq :
    (repsDiagramSets.biUnion isoClass) = (atlasDiagramSets.biUnion isoClass) := by
  decide

/-- **The normalization of `TS` is exact.**  The sum of the leaf-labelled weights over *all*
plane rooted binary trees with four leaves — the object production normalizes by `2^{-(p-1)}`
in `treeSum k p v x` — is exactly `2^3 = 8` times the sum over the fifteen non-plane
representatives, because each non-plane class has one orientation per internal vertex. -/
theorem sum_LT_fin_four {V : Type*} [Fintype V] (k : V → V → ℝ) (y : Fin 4 → V) (v : V) :
    ∑ t : RTree.LT (Fin 4), RTree.wtL k t.1 y v
      = 8 * ∑ t ∈ reps (Finset.univ : Finset (Fin 4)), RTree.wtL k t y v := by
  have h1 : TS k (Finset.univ : Finset (Fin 4)) y v
      = (1 / 8) * ∑ t : LTon (Fin 4) (Finset.univ : Finset (Fin 4)), RTree.wtL k t.1 y v := by
    rw [TS, OnTrees]
    norm_num
  have h2 : (∑ t : LTon (Fin 4) (Finset.univ : Finset (Fin 4)), RTree.wtL k t.1 y v)
      = ∑ t : RTree.LT (Fin 4), RTree.wtL k t.1 y v :=
    Fintype.sum_equiv (LTon.equivLT 4) _ _ (fun t => rfl)
  have h3 : (1 / 8) * (∑ t : RTree.LT (Fin 4), RTree.wtL k t.1 y v)
      = ∑ t ∈ reps (Finset.univ : Finset (Fin 4)), RTree.wtL k t y v := by
    rw [← h2, ← h1, TS_fin_four_eq_sum_reps]
  linarith [h3]

end PercLib.CriticalLRP.QZeroStarCount
