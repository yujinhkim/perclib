/-
Migration source: https://github.com/yujinhkim/Critical-Long-range-percolation
Integration revision: 3b3d1d0e43ef940bfaa2292ee5c2ee094ac4edbf
Licence: Apache-2.0 for the PercLib Lean sources and tooling; see third_party/critical-lrp/.
External provenance and modifications are recorded in the file-specific notices below.
-/

/-
The *tree weight* of a rooted binary tree and the summation lemma that produces the
constant `(E|K|)^{2p−1}` in inequality (I.2.3) of

  T. Hutchcroft, *Critical long-range percolation I: High effective dimension*,
  arXiv:2508.18807v1, Section I.2.1, p. 22.

For a kernel `k : V → V → ℝ` (in the application `k a b = P(a ↔ b)`) and a rooted tree
`t` with leaves labelled by points, `wt k t y v` is the sum over all assignments of
values in `V` to the *internal* vertices of the product of `k` over the edges of `t`,
where the root is assigned `v` and the leaf positions are assigned by `y`.

The main result, `RTree.sum_wt`, is the identity

  `∑ y : (leaves → V), wt k t y v = S^(2·#leaves − 1)`  whenever  `∑ b, k a b = S`

for every `a`. It is the purely combinatorial summation that, applied to the tree-graph
inequality (I.2.2), turns each tree term into `(E|K|)^{2p−1}` — the step preceding
(I.2.3). The identity is uniform in the tree: every leaf-labelled tree with `p` leaves
contributes the same value `S^(2p−1)`.
-/
module

public import Mathlib
public import PercLib.CriticalLRP.TreeExpansion.Basic

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

variable {α : Type*} {V : Type*} [Fintype V]

/-! ### Leaf labels of positions -/

/-- The leaf label carried by a leaf position. -/
def leafOfPos : (t : RTree α) → LeafPos t → α
  | leaf a, _ => a
  | node _ _, Sum.inl p => leafOfPos _ p
  | node _ _, Sum.inr p => leafOfPos _ p

/-! ### The tree weight -/

/-- `wt k t y v`: the sum over all assignments of values in `V` to the internal vertices
of `t` of the product of `k` over the edges, where the root is assigned `v` (so that the
edge from the parent of the root, if any, contributes `k (parent) v`) and the leaf
position `p` is assigned `y p`. -/
noncomputable def wt (k : V → V → ℝ) : (t : RTree α) → (LeafPos t → V) → V → ℝ
  | leaf _, y, v => k v (y ⟨⟩)
  | node l r, y, v =>
      ∑ w : V, k v w * wt k l (fun p => y (Sum.inl p)) w * wt k r (fun p => y (Sum.inr p)) w

/-! ### The summation identity -/

private lemma sum_punit_arrow {M : Type*} [AddCommMonoid M] (f : V → M) :
    (∑ y : PUnit → V, f (y ⟨⟩)) = ∑ z : V, f z := by
  refine Fintype.sum_equiv (Equiv.funUnique PUnit V : (PUnit → V) ≃ V)
    (fun y : PUnit → V => f (y ⟨⟩)) (fun z : V => f z) ?_
  intro y
  simp

private lemma sum_sum_sum_factor {ι κ : Type*} [Fintype ι] [Fintype κ]
    (f : V → ℝ) (A : ι → V → ℝ) (B : κ → V → ℝ) :
    (∑ i, ∑ j, ∑ w : V, f w * A i w * B j w)
      = ∑ w : V, f w * ((∑ i, A i w) * (∑ j, B j w)) := by
  have h1 : ∀ i, (∑ j, ∑ w : V, f w * A i w * B j w)
      = ∑ w : V, ∑ j, f w * A i w * B j w := fun i => Finset.sum_comm
  calc (∑ i, ∑ j, ∑ w : V, f w * A i w * B j w)
      = ∑ i, ∑ w : V, ∑ j, f w * A i w * B j w := Finset.sum_congr rfl fun i _ => h1 i
    _ = ∑ w : V, ∑ i, ∑ j, f w * A i w * B j w := Finset.sum_comm
    _ = ∑ w : V, f w * ((∑ i, A i w) * (∑ j, B j w)) := by
        refine Finset.sum_congr rfl fun w _ => ?_
        have h2 : ∀ i, (∑ j, f w * A i w * B j w) = (f w * A i w) * (∑ j, B j w) := by
          intro i
          rw [Finset.mul_sum]
        rw [Finset.sum_congr rfl fun i _ => h2 i, ← Finset.sum_mul, ← Finset.mul_sum]
        exact mul_assoc _ _ _

/-- **The tree-weight summation identity.** For a kernel whose row sums are all equal to
`S`, every rooted tree with `p` leaves contributes, after summing over the values at all
of its leaves and internal vertices, exactly `S^(2p−1)`, independently of its shape. -/
theorem sum_wt (k : V → V → ℝ) (S : ℝ) (hS : ∀ v : V, ∑ y : V, k v y = S) :
    ∀ (t : RTree α) (v : V),
      (∑ y : LeafPos t → V, wt k t y v) = S ^ (2 * t.numLeaves - 1) := by
  intro t
  induction t with
  | leaf a =>
    intro v
    have h : (∑ y : LeafPos (leaf a) → V, wt k (leaf a) y v) = S := by
      refine (sum_punit_arrow (fun z : V => k v z)).trans (hS v)
    rw [h]
    show S = S ^ (2 * 1 - 1)
    norm_num
  | node l r ihl ihr =>
    intro v
    have hl : 0 < l.numLeaves := numLeaves_pos l
    have hr : 0 < r.numLeaves := numLeaves_pos r
    have hsplit : (∑ y : LeafPos (node l r) → V, wt k (node l r) y v)
        = ∑ y1 : LeafPos l → V, ∑ y2 : LeafPos r → V,
            ∑ w : V, k v w * wt k l y1 w * wt k r y2 w := by
      calc (∑ y : LeafPos (node l r) → V, wt k (node l r) y v)
          = ∑ y : LeafPos (node l r) → V, ∑ w : V,
              k v w * wt k l (fun p => y (Sum.inl p)) w *
                wt k r (fun p => y (Sum.inr p)) w :=
            Finset.sum_congr rfl fun y _ => by simp only [wt]
        _ = ∑ p : (LeafPos l → V) × (LeafPos r → V), ∑ w : V,
              k v w * wt k l p.1 w * wt k r p.2 w := by
            refine Fintype.sum_equiv (Equiv.sumArrowEquivProdArrow (LeafPos l) (LeafPos r) V)
              (fun y : LeafPos (node l r) → V => ∑ w : V,
                k v w * wt k l (fun p => y (Sum.inl p)) w *
                  wt k r (fun p => y (Sum.inr p)) w)
              (fun p : (LeafPos l → V) × (LeafPos r → V) => ∑ w : V,
                k v w * wt k l p.1 w * wt k r p.2 w) ?_
            intro y
            rfl
        _ = ∑ y1 : LeafPos l → V, ∑ y2 : LeafPos r → V,
              ∑ w : V, k v w * wt k l y1 w * wt k r y2 w :=
            Fintype.sum_prod_type _
    rw [hsplit, sum_sum_sum_factor (fun w => k v w) (fun y1 w => wt k l y1 w)
      (fun y2 w => wt k r y2 w)]
    have hfac : ∀ w : V, (∑ y1 : LeafPos l → V, wt k l y1 w) *
        (∑ y2 : LeafPos r → V, wt k r y2 w)
        = S ^ (2 * l.numLeaves - 1) * S ^ (2 * r.numLeaves - 1) := by
      intro w
      rw [ihl w, ihr w]
    rw [Finset.sum_congr rfl fun w _ => by rw [hfac w]]
    rw [← Finset.sum_mul, hS v, numLeaves_node]
    have e1 : (2 * l.numLeaves - 1) + (2 * r.numLeaves - 1) + 1
        = 2 * (l.numLeaves + r.numLeaves) - 1 := by omega
    calc S * (S ^ (2 * l.numLeaves - 1) * S ^ (2 * r.numLeaves - 1))
        = S ^ ((2 * l.numLeaves - 1) + (2 * r.numLeaves - 1)) * S := by
          rw [pow_add]; ring
      _ = S ^ ((2 * l.numLeaves - 1) + (2 * r.numLeaves - 1) + 1) :=
          (pow_succ S ((2 * l.numLeaves - 1) + (2 * r.numLeaves - 1))).symm
      _ = S ^ (2 * (l.numLeaves + r.numLeaves) - 1) := by rw [e1]

end RTree

end PercLib.CriticalLRP.TreeExpansion
