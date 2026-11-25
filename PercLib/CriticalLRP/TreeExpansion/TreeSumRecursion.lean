/-
Migration source: https://github.com/yujinhkim/Critical-Long-range-percolation
Integration revision: 3b3d1d0e43ef940bfaa2292ee5c2ee094ac4edbf
Licence: Apache-2.0 for the PercLib Lean sources and tooling; see third_party/critical-lrp/.
External provenance and modifications are recorded in the file-specific notices below.
-/

/-
The recursion step of the tree-graph inequality (I.2.2), at the level of tree sums.

`OnTrees k Z y v` is the sum of the weights `RTree.wtL` over all rooted binary trees whose
leaves are labelled injectively by the finset `Z` (each label used once), the root carrying
the value `v` and the leaf labelled `a` the value `y a`; `TS` is the normalization
`TS k Z y v = 2^{-(|Z|-1)}·OnTrees k Z y v` of (I.2.2).

`TS_split_le` is the recursion step used for the tree-graph inequality: for disjoint
finsets `Z₁`, `Z₂` and a nonnegative kernel,
`∑_w k v w · TS Z₁ w · TS Z₂ w ≤ TS (Z₁ ∪ Z₂) v`.
It is proved by injecting `(left, right)` pairs of trees into the trees on `Z₁ ∪ Z₂` twice,
once with the two sides exchanged, which supplies the factor `2` of the normalization.
-/
module

public import Mathlib
public import PercLib.CriticalLRP.TreeExpansion.LabelledWeights

set_option autoImplicit true

set_option autoImplicit false
set_option linter.unusedSectionVars false
set_option maxHeartbeats 2000000

@[expose] public section

namespace PercLib.CriticalLRP.TreeExpansion

open Finset
open Classical

variable {α : Type*} [DecidableEq α] {V : Type*} [Fintype V]

/-- The sum of the tree weights over all trees whose leaves are labelled by exactly `Z`. -/
noncomputable def OnTrees (k : V → V → ℝ) (Z : Finset α) (y : α → V) (v : V) : ℝ :=
  ∑ t : LTon α Z, RTree.wtL k t.1 y v

/-- The normalized tree sum of (I.2.2). -/
noncomputable def TS (k : V → V → ℝ) (Z : Finset α) (y : α → V) (v : V) : ℝ :=
  (1 / 2 ^ (Z.card - 1)) * OnTrees k Z y v

namespace RTree

theorem wtL_nonneg {k : V → V → ℝ} (hk : ∀ a b, 0 ≤ k a b) (t : RTree α) (y : α → V) (v : V) :
    0 ≤ wtL k t y v := by
  induction t generalizing v with
  | leaf a => exact hk _ _
  | node l r ihl ihr =>
      rw [wtL_node]
      exact Finset.sum_nonneg fun w _ => mul_nonneg (mul_nonneg (hk _ _) (ihl w)) (ihr w)

end RTree

theorem OnTrees_nonneg {k : V → V → ℝ} (hk : ∀ a b, 0 ≤ k a b) (Z : Finset α) (y : α → V)
    (v : V) : 0 ≤ OnTrees k Z y v :=
  Finset.sum_nonneg fun t _ => RTree.wtL_nonneg hk t.1 y v

theorem TS_nonneg {k : V → V → ℝ} (hk : ∀ a b, 0 ≤ k a b) (Z : Finset α) (y : α → V)
    (v : V) : 0 ≤ TS k Z y v := by
  rw [TS]
  exact mul_nonneg (by positivity) (OnTrees_nonneg hk Z y v)


namespace LTon

variable {Z₁ Z₂ : Finset α}

theorem node_mem (h : Disjoint Z₁ Z₂) {l r : RTree α}
    (hl : l.leaves.Nodup ∧ l.leaves.toFinset = Z₁)
    (hr : r.leaves.Nodup ∧ r.leaves.toFinset = Z₂) :
    (RTree.node l r).leaves.Nodup ∧ (RTree.node l r).leaves.toFinset = Z₁ ∪ Z₂ := by
  rw [RTree.leaves_node]
  refine ⟨?_, ?_⟩
  · rw [List.nodup_append]
    refine ⟨hl.1, hr.1, ?_⟩
    intro a ha b hb hab
    have h1 : a ∈ Z₁ := by rw [← hl.2]; exact List.mem_toFinset.mpr ha
    have h2 : b ∈ Z₂ := by rw [← hr.2]; exact List.mem_toFinset.mpr hb
    have h2' : a ∉ Z₂ := (Finset.disjoint_left.mp h) h1
    exact h2' (hab ▸ h2)
  · rw [List.toFinset_append, hl.2, hr.2]

/-- Building a tree from a left subtree on `Z₁` and a right subtree on `Z₂`. -/
noncomputable def node (h : Disjoint Z₁ Z₂) (l : LTon α Z₁) (r : LTon α Z₂) :
    LTon α (Z₁ ∪ Z₂) :=
  ⟨RTree.node l.1 r.1, node_mem h l.2 r.2⟩

/-- Building the mirrored tree, with the two subtrees exchanged. -/
noncomputable def nodeSwap (h : Disjoint Z₁ Z₂) (p : LTon α Z₁ × LTon α Z₂) :
    LTon α (Z₁ ∪ Z₂) :=
  ⟨RTree.node p.2.1 p.1.1, by
    have hmem := node_mem h.symm p.2.2 p.1.2
    rwa [Finset.union_comm] at hmem⟩

theorem node_injective (h : Disjoint Z₁ Z₂) :
    Function.Injective (fun p : LTon α Z₁ × LTon α Z₂ => node h p.1 p.2) := by
  rintro ⟨l, r⟩ ⟨l', r'⟩ heq
  have h' : RTree.node l.1 r.1 = RTree.node l'.1 r'.1 := congrArg Subtype.val heq
  rw [RTree.node.injEq] at h'
  obtain ⟨h1, h2⟩ := h'
  rw [Subtype.ext h1, Subtype.ext h2]

theorem nodeSwap_injective (h : Disjoint Z₁ Z₂) :
    Function.Injective (fun p : LTon α Z₁ × LTon α Z₂ => nodeSwap h p) := by
  rintro ⟨l, r⟩ ⟨l', r'⟩ heq
  have h' : RTree.node r.1 l.1 = RTree.node r'.1 l'.1 := congrArg Subtype.val heq
  rw [RTree.node.injEq] at h'
  obtain ⟨h1, h2⟩ := h'
  rw [Subtype.ext h2, Subtype.ext h1]

end LTon

/-! ### The two-sided injection bound -/

theorem sum_node_le {k : V → V → ℝ} (hk : ∀ a b, 0 ≤ k a b) {Z₁ Z₂ : Finset α}
    (h : Disjoint Z₁ Z₂) (y : α → V) (v : V) :
    (∑ p : LTon α Z₁ × LTon α Z₂,
        ∑ w : V, k v w * RTree.wtL k p.1.1 y w * RTree.wtL k p.2.1 y w)
      ≤ OnTrees k (Z₁ ∪ Z₂) y v := by
  rw [OnTrees]
  have hinj := LTon.node_injective (Z₁ := Z₁) (Z₂ := Z₂) h
  have hstep : (∑ p : LTon α Z₁ × LTon α Z₂,
      ∑ w : V, k v w * RTree.wtL k p.1.1 y w * RTree.wtL k p.2.1 y w)
      = ∑ p : LTon α Z₁ × LTon α Z₂, RTree.wtL k (LTon.node h p.1 p.2).1 y v := by
    refine Finset.sum_congr rfl fun p _ => ?_
    simp only [LTon.node, RTree.wtL_node]
  let Sf : Finset (LTon α (Z₁ ∪ Z₂)) := (Finset.univ : Finset (LTon α Z₁ × LTon α Z₂)).image
    (fun p => LTon.node h p.1 p.2)
  have himg : (∑ t ∈ Sf, RTree.wtL k t.1 y v)
      = ∑ p : LTon α Z₁ × LTon α Z₂, RTree.wtL k (LTon.node h p.1 p.2).1 y v :=
    Finset.sum_image (fun p _ p' _ hpq => hinj hpq)
  rw [hstep, ← himg]
  exact Finset.sum_le_sum_of_subset_of_nonneg (Finset.subset_univ _)
    (fun t _ _ => RTree.wtL_nonneg hk t.1 y v)

theorem sum_node_le_swap {k : V → V → ℝ} (hk : ∀ a b, 0 ≤ k a b) {Z₁ Z₂ : Finset α}
    (h : Disjoint Z₁ Z₂) (y : α → V) (v : V) :
    (∑ p : LTon α Z₁ × LTon α Z₂,
        ∑ w : V, k v w * RTree.wtL k p.1.1 y w * RTree.wtL k p.2.1 y w)
      ≤ OnTrees k (Z₁ ∪ Z₂) y v := by
  have hsymm : (∑ p : LTon α Z₁ × LTon α Z₂,
      ∑ w : V, k v w * RTree.wtL k p.1.1 y w * RTree.wtL k p.2.1 y w)
      = ∑ p : LTon α Z₁ × LTon α Z₂,
        ∑ w : V, k v w * RTree.wtL k p.2.1 y w * RTree.wtL k p.1.1 y w := by
    refine Finset.sum_congr rfl fun p _ => Finset.sum_congr rfl fun w _ => ?_
    ring
  rw [hsymm, OnTrees]
  have hinj := LTon.nodeSwap_injective (Z₁ := Z₁) (Z₂ := Z₂) h
  have hstep : (∑ p : LTon α Z₁ × LTon α Z₂,
      ∑ w : V, k v w * RTree.wtL k p.2.1 y w * RTree.wtL k p.1.1 y w)
      = ∑ p : LTon α Z₁ × LTon α Z₂, RTree.wtL k (LTon.nodeSwap h p).1 y v := by
    refine Finset.sum_congr rfl fun p _ => ?_
    simp only [LTon.nodeSwap, RTree.wtL_node]
  let Sf : Finset (LTon α (Z₁ ∪ Z₂)) := (Finset.univ : Finset (LTon α Z₁ × LTon α Z₂)).image
    (fun p => LTon.nodeSwap h p)
  have himg : (∑ t ∈ Sf, RTree.wtL k t.1 y v)
      = ∑ p : LTon α Z₁ × LTon α Z₂, RTree.wtL k (LTon.nodeSwap h p).1 y v :=
    Finset.sum_image (fun p _ p' _ hpq => hinj hpq)
  rw [hstep, ← himg]
  exact Finset.sum_le_sum_of_subset_of_nonneg (Finset.subset_univ _)
    (fun t _ _ => RTree.wtL_nonneg hk t.1 y v)

/-- The tree sum only depends on the values at the labels of `Z`. -/
theorem TS_congr {k : V → V → ℝ} {y y' : α → V} {Z : Finset α}
    (h : ∀ a ∈ Z, y a = y' a) (v : V) : TS k Z y v = TS k Z y' v := by
  rw [TS, TS, OnTrees, OnTrees]
  congr 1
  refine Finset.sum_congr rfl fun t _ => ?_
  exact RTree.wtL_congr k t.1 (fun a ha => h a (t.2.2 ▸ List.mem_toFinset.mpr ha)) v

/-- Factoring a double tree sum: the algebraic step of the recursion. -/
private theorem factor_sum {ι κ : Type*} [Fintype ι] [Fintype κ]
    (c₁ c₂ : ℝ) (k : V → V → ℝ) (f : ι → V → ℝ) (g : κ → V → ℝ) (v : V) :
    (∑ w : V, k v w * (c₁ * ∑ i, f i w) * (c₂ * ∑ j, g j w))
      = c₁ * c₂ * ∑ p : ι × κ, ∑ w : V, k v w * f p.1 w * g p.2 w := by
  -- expand the left-hand side into a triple sum
  have hbody : ∀ w : V, k v w * (c₁ * ∑ i, f i w) * (c₂ * ∑ j, g j w)
      = ∑ i, ∑ j, (c₁ * c₂) * (k v w * f i w * g j w) := by
    intro w
    have h1 : c₁ * (∑ i, f i w) = ∑ i, c₁ * f i w := Finset.mul_sum ..
    have h2 : c₂ * (∑ j, g j w) = ∑ j, c₂ * g j w := Finset.mul_sum ..
    rw [h1, h2]
    have h3 : k v w * (∑ i, c₁ * f i w) = ∑ i, k v w * (c₁ * f i w) := Finset.mul_sum ..
    rw [h3]
    have h4 : (∑ i, k v w * (c₁ * f i w)) * (∑ j, c₂ * g j w)
        = ∑ i, ∑ j, (k v w * (c₁ * f i w)) * (c₂ * g j w) := Finset.sum_mul_sum ..
    rw [h4]
    exact Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => by ring
  simp only [hbody]
  rw [Finset.sum_comm]
  conv_lhs => enter [2, i]; rw [Finset.sum_comm]
  rw [Finset.mul_sum, Fintype.sum_prod_type]
  refine Finset.sum_congr rfl fun i _ => ?_
  refine Finset.sum_congr rfl fun j _ => ?_
  rw [Finset.mul_sum]

/-- **The recursion step**: `∑_w k v w · TS Z₁ w · TS Z₂ w ≤ TS (Z₁ ∪ Z₂) v` for disjoint
nonempty label sets and a nonnegative kernel. -/
theorem TS_split_le {k : V → V → ℝ} (hk : ∀ a b, 0 ≤ k a b) {Z₁ Z₂ : Finset α}
    (h : Disjoint Z₁ Z₂) (h₁ : Z₁.Nonempty) (h₂ : Z₂.Nonempty) (y : α → V) (v : V) :
    (∑ w : V, k v w * TS k Z₁ y w * TS k Z₂ y w) ≤ TS k (Z₁ ∪ Z₂) y v := by
  classical
  set a := Z₁.card with ha
  set b := Z₂.card with hb
  have ha1 : 1 ≤ a := Finset.card_pos.mpr h₁
  have hb1 : 1 ≤ b := Finset.card_pos.mpr h₂
  have hne : Z₁ ≠ Z₂ := by
    intro heq
    obtain ⟨x, hx⟩ := h₁
    exact ((Finset.disjoint_left.mp h) hx) (heq ▸ hx)
  have hcard : (Z₁ ∪ Z₂).card = a + b := Finset.card_union_of_disjoint h
  -- the double tree sum
  set D : ℝ := ∑ p : LTon α Z₁ × LTon α Z₂,
      ∑ w : V, k v w * RTree.wtL k p.1.1 y w * RTree.wtL k p.2.1 y w with hDdef
  -- the left-hand side is a multiple of `D`
  have hL : (∑ w : V, k v w * TS k Z₁ y w * TS k Z₂ y w)
      = (1 / 2 ^ (a - 1)) * (1 / 2 ^ (b - 1)) * D := by
    rw [hDdef]
    simp only [TS, OnTrees]
    exact factor_sum (1 / 2 ^ (a - 1)) (1 / 2 ^ (b - 1)) k
      (fun l : LTon α Z₁ => fun w => RTree.wtL k l.1 y w)
      (fun r : LTon α Z₂ => fun w => RTree.wtL k r.1 y w) v
  -- the two symmetric injections of `D` into the trees on `Z₁ ∪ Z₂`
  set S₁ : Finset (LTon α (Z₁ ∪ Z₂)) := (Finset.univ : Finset (LTon α Z₁ × LTon α Z₂)).image
    (fun p => LTon.node h p.1 p.2) with hS₁
  set S₂ : Finset (LTon α (Z₁ ∪ Z₂)) := (Finset.univ : Finset (LTon α Z₁ × LTon α Z₂)).image
    (fun p => LTon.nodeSwap h p) with hS₂
  have hS₁sum : (∑ t ∈ S₁, RTree.wtL k t.1 y v) = D := by
    rw [hDdef, hS₁]
    exact Finset.sum_image
      (f := fun t : LTon α (Z₁ ∪ Z₂) => RTree.wtL k t.1 y v)
      (g := fun p : LTon α Z₁ × LTon α Z₂ => LTon.node h p.1 p.2)
      (fun p _ p' _ hpq => LTon.node_injective h hpq)
  have hS₂sum : (∑ t ∈ S₂, RTree.wtL k t.1 y v) = D := by
    rw [hDdef, hS₂]
    rw [Finset.sum_image
      (f := fun t : LTon α (Z₁ ∪ Z₂) => RTree.wtL k t.1 y v)
      (g := fun p : LTon α Z₁ × LTon α Z₂ => LTon.nodeSwap h p)
      (fun p _ p' _ hpq => LTon.nodeSwap_injective h hpq)]
    refine Finset.sum_congr rfl fun p _ => ?_
    simp only [LTon.nodeSwap, RTree.wtL_node]
    exact Finset.sum_congr rfl fun w _ => by ring
  have hdisj : Disjoint S₁ S₂ := by
    rw [Finset.disjoint_left]
    intro t ht1 ht2
    obtain ⟨p, -, hp⟩ := Finset.mem_image.mp ht1
    obtain ⟨q, -, hq⟩ := Finset.mem_image.mp ht2
    have h1 : (LTon.node h p.1 p.2).1 = (LTon.nodeSwap h q).1 := by rw [hp, hq]
    have h2 : RTree.node p.1.1 p.2.1 = RTree.node q.2.1 q.1.1 := h1
    rw [RTree.node.injEq] at h2
    obtain ⟨h3, -⟩ := h2
    have h4 : Z₁ = Z₂ := by
      calc Z₁ = p.1.1.leaves.toFinset := p.1.2.2.symm
        _ = q.2.1.leaves.toFinset := by rw [h3]
        _ = Z₂ := q.2.2.2
    exact hne h4
  have hD : 2 * D ≤ OnTrees k (Z₁ ∪ Z₂) y v := by
    have hunion : (∑ t ∈ S₁ ∪ S₂, RTree.wtL k t.1 y v)
        = (∑ t ∈ S₁, RTree.wtL k t.1 y v) + (∑ t ∈ S₂, RTree.wtL k t.1 y v) :=
      Finset.sum_union hdisj
    have hle : (∑ t ∈ S₁ ∪ S₂, RTree.wtL k t.1 y v)
        ≤ ∑ t : LTon α (Z₁ ∪ Z₂), RTree.wtL k t.1 y v :=
      Finset.sum_le_sum_of_subset_of_nonneg (Finset.subset_univ _)
        (fun t _ _ => RTree.wtL_nonneg hk t.1 y v)
    rw [hunion, hS₁sum, hS₂sum] at hle
    rw [OnTrees]
    linarith
  -- the arithmetic
  have hpos : (0 : ℝ) < (1 / 2 ^ (a - 1)) * (1 / 2 ^ (b - 1)) := by positivity
  have h2a : (2 : ℝ) ^ (a + b - 1) = 2 ^ (a - 1) * 2 ^ (b - 1) * 2 := by
    rw [← pow_add, ← pow_succ]
    congr 1
    omega
  rw [hL, TS, OnTrees, hcard, h2a]
  rw [show (1 / (2 ^ (a - 1) * 2 ^ (b - 1) * 2) : ℝ)
      = (1 / 2 ^ (a - 1)) * (1 / 2 ^ (b - 1)) * (1 / 2) by field_simp]
  calc (1 / 2 ^ (a - 1)) * (1 / 2 ^ (b - 1)) * D
      = ((1 / 2 ^ (a - 1)) * (1 / 2 ^ (b - 1))) * D := by ring
    _ ≤ ((1 / 2 ^ (a - 1)) * (1 / 2 ^ (b - 1))) * (OnTrees k (Z₁ ∪ Z₂) y v / 2) := by
        refine mul_le_mul_of_nonneg_left ?_ (le_of_lt hpos)
        linarith
    _ = (1 / 2 ^ (a - 1)) * (1 / 2 ^ (b - 1)) * (1 / 2) *
          OnTrees k (Z₁ ∪ Z₂) y v := by ring

end PercLib.CriticalLRP.TreeExpansion
