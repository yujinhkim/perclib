/-
Migration source: https://github.com/yujinhkim/Critical-Long-range-percolation
Integration revision: 3b3d1d0e43ef940bfaa2292ee5c2ee094ac4edbf
Licence: Apache-2.0 for the PercLib Lean sources and tooling; see third_party/critical-lrp/.
External provenance and modifications are recorded in the file-specific notices below.
-/

/-
**The tree-sum recursion identity (I.2.2) and the cluster-moment bound (I.2.3).**

Hutchcroft, *Critical long-range percolation I: High effective dimension*,
arXiv:2508.18807v1, Section I.2.1, p. 22.

This file proves, with no additional hypotheses:

* `TS_recursion` : the tree-sum recursion
  `TS Z v = ∑_{A ∋ a₀, A ⊆ Z, A ≠ Z, A ≠ ∅} ∑_w k v w · TS A w · TS (Z \ A) w`
  for every finite label set `Z` with `2 ≤ Z.card` and every basepoint `a₀ ∈ Z`;
* `treeSumRecursionAt` : the hypothesis `TreeSumRecursionAt` of `treeGraphBound_of_bk`, for
  every `m`;
* `treeGraphBound_of_bk'` : the tree-graph inequality (I.2.2) for all `k`, from the BK
  inequality alone;
* `moment_bound_of_bk` and `moment_bound_of_bk_expectation` : the cluster-moment bound
  (I.2.3) `E|K|^p ≤ (2p−3)!! (E|K|)^{2p−1}` for every integer `p ≥ 1`, from BK plus
  translation invariance of the two-point function.

The proof of the recursion is the root-cutting bijection: the map
`(A, l, r) ↦ node l r` from trees on the two halves of a split of `Z` to trees on `Z`
is a bijection onto the trees whose root has left half `A`, and pairing `A` with `Z \ A`
shows that exactly half of the total tree weight sits over the splits at a basepoint.
-/
module

public import Mathlib
public import PercLib.CriticalLRP.TreeExpansion.TreeGraphInequality
public import PercLib.CriticalLRP.TreeExpansion.Moment
public import PercLib.CriticalLRP.TreeExpansion.ThreePointBridge
public import PercLib.CriticalLRP.VolumeMoments.Convolution

set_option linter.unusedSectionVars false
set_option linter.unusedSimpArgs false
set_option linter.unnecessarySimpa false
set_option linter.unusedTactic false
set_option linter.unusedVariables false

set_option autoImplicit true

set_option autoImplicit false
set_option linter.unusedSectionVars false
set_option maxHeartbeats 2000000

@[expose] public section

namespace PercLib.CriticalLRP.TreeExpansion

open Finset
open Classical

variable {α : Type*} [DecidableEq α] {V : Type*} [Fintype V]

namespace RTree

/-- Mirror a tree: exchange the two children at every node. -/
def swap (t : RTree α) : RTree α :=
  match t with
  | leaf a => leaf a
  | node l r => node (swap r) (swap l)

@[simp] theorem leaves_swap (t : RTree α) : (swap t).leaves = t.leaves.reverse := by
  induction t with
  | leaf a => rfl
  | node l r ihl ihr =>
      simp only [swap, leaves_node, ihl, ihr, List.reverse_append]

@[simp] theorem swap_leaf (a : α) : swap (leaf a) = leaf a := rfl

theorem swap_node (l r : RTree α) : swap (node l r) = node (swap r) (swap l) := rfl

@[simp] theorem swap_swap (t : RTree α) : swap (swap t) = t := by
  induction t with
  | leaf a => rfl
  | node l r ihl ihr => rw [swap_node, swap_node, ihl, ihr]

/-- Mirroring preserves the weight. -/
theorem wtL_swap (k : V → V → ℝ) (t : RTree α) (y : α → V) (v : V) :
    wtL k (swap t) y v = wtL k t y v := by
  induction t generalizing v with
  | leaf a => rfl
  | node l r ihl ihr =>
      rw [swap_node, wtL_node, wtL_node]
      refine Finset.sum_congr rfl fun w _ => ?_
      rw [ihl w, ihr w]
      ring

/-- The left child of a node (`leaf a` itself at a leaf, as a junk value). -/
def leftPart : RTree α → RTree α
  | leaf a => leaf a
  | node l _ => l

/-- The right child of a node (`leaf a` itself at a leaf, as a junk value). -/
def rightPart : RTree α → RTree α
  | leaf a => leaf a
  | node _ r => r

@[simp] theorem leftPart_node (l r : RTree α) : leftPart (node l r) = l := rfl
@[simp] theorem rightPart_node (l r : RTree α) : rightPart (node l r) = r := rfl

/-- The set of labels on the left child (`∅` at a leaf). -/
def leftLeaves : RTree α → Finset α
  | leaf _ => ∅
  | node l _ => l.leaves.toFinset

/-- The set of labels on the right child (`∅` at a leaf). -/
def rightLeaves : RTree α → Finset α
  | leaf _ => ∅
  | node _ r => r.leaves.toFinset

@[simp] theorem leftLeaves_node (l r : RTree α) :
    leftLeaves (node l r) = l.leaves.toFinset := rfl

@[simp] theorem rightLeaves_node (l r : RTree α) :
    rightLeaves (node l r) = r.leaves.toFinset := rfl

@[simp] theorem leftLeaves_leaf (a : α) : leftLeaves (leaf a) = ∅ := rfl
@[simp] theorem rightLeaves_leaf (a : α) : rightLeaves (leaf a) = ∅ := rfl

theorem leftLeaves_swap (t : RTree α) : leftLeaves (swap t) = rightLeaves t := by
  cases t with
  | leaf a => rfl
  | node l r =>
      rw [swap_node, leftLeaves_node, rightLeaves_node, leaves_swap, List.toFinset_reverse]

/-- A label of a nodup tree lies on the left exactly when it does not lie on the right. -/
theorem mem_leftLeaves_iff_not_mem_rightLeaves {l r : RTree α}
    (hnd : (node l r).leaves.Nodup) {a₀ : α} (ha₀ : a₀ ∈ (node l r).leaves) :
    a₀ ∈ leftLeaves (node l r) ↔ a₀ ∉ rightLeaves (node l r) := by
  rw [leftLeaves_node, rightLeaves_node]
  have hnd' : (l.leaves ++ r.leaves).Nodup := hnd
  obtain ⟨hl, hr, hdisj⟩ := List.nodup_append.mp hnd'
  constructor
  · intro h1 h2
    exact hdisj a₀ (List.mem_toFinset.mp h1) a₀ (List.mem_toFinset.mp h2) rfl
  · intro h2
    rcases List.mem_append.mp ha₀ with h | h
    · exact List.mem_toFinset.mpr h
    · exact absurd (List.mem_toFinset.mpr h) h2

/-- Every tree in `LTon α Z` with `2 ≤ Z.card` is a node. -/
theorem LTon.isNode {Z : Finset α} (h2 : 2 ≤ Z.card) (t : LTon α Z) :
    ∃ l r, (t : RTree α) = node l r := by
  obtain ⟨tl, hnd, htf⟩ := t
  cases tl with
  | leaf a =>
      exfalso
      rw [← htf] at h2
      simp at h2
  | node l r => exact ⟨l, r, rfl⟩

/-- The mirror of a tree on `Z` is again a tree on `Z`. -/
def swapLTon {Z : Finset α} (t : LTon α Z) : LTon α Z :=
  ⟨swap t.1, by
    rw [leaves_swap]
    refine ⟨List.nodup_reverse.mpr t.2.1, ?_⟩
    rw [List.toFinset_reverse, t.2.2]⟩

@[simp] theorem swapLTon_val {Z : Finset α} (t : LTon α Z) :
    (swapLTon t : RTree α) = swap t.1 := rfl

@[simp] theorem swapLTon_swapLTon {Z : Finset α} (t : LTon α Z) :
    swapLTon (swapLTon t) = t := by
  apply Subtype.ext
  simp

end RTree


open Finset
open Classical

variable {α : Type*} [DecidableEq α] {V : Type*} [Fintype V]

namespace RTree

theorem node_injEq {l r l' r' : RTree α} : node l r = node l' r' ↔ l = l' ∧ r = r' := by
  constructor
  · intro h
    injection h with h1 h2
    exact ⟨h1, h2⟩
  · rintro ⟨rfl, rfl⟩; rfl

/-- `LTon α ∅` is empty. -/
theorem LTon.isEmpty_empty : IsEmpty (LTon α (∅ : Finset α)) :=
  ⟨fun t => by
    obtain ⟨a, ha⟩ := exists_mem_leaves (t : RTree α)
    have h : a ∈ (∅ : Finset α) := by rw [← t.2.2]; exact List.mem_toFinset.mpr ha
    exact absurd h (Finset.notMem_empty a)⟩

end RTree

/-- The splits of `Z` at the basepoint `a₀`: nonempty proper subsets containing `a₀`. -/
def splits (Z : Finset α) (a₀ : α) : Finset (Finset α) :=
  Z.powerset.filter (fun A => A.Nonempty ∧ A ≠ Z ∧ a₀ ∈ A)

theorem mem_splits {Z : Finset α} {a₀ : α} {A : Finset α} (hA : A ∈ splits Z a₀) :
    A ⊆ Z ∧ A.Nonempty ∧ A ≠ Z ∧ a₀ ∈ A := by
  rw [splits, Finset.mem_filter, Finset.mem_powerset] at hA
  exact ⟨hA.1, hA.2.1, hA.2.2.1, hA.2.2.2⟩

/-- A tree on `Z` built from a split `A ⊆ Z` and trees on the two halves. -/
noncomputable def mkNode {Z A : Finset α} (hAZ : A ⊆ Z) (l : LTon α A) (r : LTon α (Z \ A)) :
    LTon α Z :=
  ⟨RTree.node l.1 r.1, by
    rw [RTree.leaves_node]
    refine ⟨?_, ?_⟩
    · rw [List.nodup_append]
      refine ⟨l.2.1, r.2.1, ?_⟩
      intro a ha b hb hab
      have haA : a ∈ A := by rw [← l.2.2]; exact List.mem_toFinset.mpr ha
      have hbZ : b ∈ Z \ A := by rw [← r.2.2]; exact List.mem_toFinset.mpr hb
      exact (Finset.mem_sdiff.mp hbZ).2 (hab ▸ haA)
    · rw [List.toFinset_append, l.2.2, r.2.2, Finset.union_sdiff_of_subset hAZ]⟩

@[simp] theorem mkNode_val {Z A : Finset α} (hAZ : A ⊆ Z) (l : LTon α A)
    (r : LTon α (Z \ A)) : (mkNode hAZ l r : RTree α) = RTree.node l.1 r.1 := rfl

theorem leftLeaves_mkNode {Z A : Finset α} (hAZ : A ⊆ Z) (l : LTon α A)
    (r : LTon α (Z \ A)) : RTree.leftLeaves (mkNode hAZ l r).1 = A := by
  rw [mkNode_val, RTree.leftLeaves_node, l.2.2]

/-- The data of a `Z`-labelled tree cut at its root. -/
abbrev RootCut (Z : Finset α) :=
  Σ A : {A : Finset α // A ∈ Z.powerset}, LTon α A.1 × LTon α (Z \ A.1)

theorem RootCut_injective {Z : Finset α} :
    Function.Injective
      (fun p : RootCut (α := α) Z => mkNode (Finset.mem_powerset.mp p.1.2) p.2.1 p.2.2) := by
  rintro ⟨⟨A, hA⟩, ⟨l, r⟩⟩ ⟨⟨A', hA'⟩, ⟨l', r'⟩⟩ heq
  have hv : RTree.node l.1 r.1 = RTree.node l'.1 r'.1 := congrArg Subtype.val heq
  obtain ⟨h1, h2⟩ := RTree.node_injEq.mp hv
  have e1 : l.1.leaves.toFinset = A := l.2.2
  have e2 : l'.1.leaves.toFinset = A' := l'.2.2
  have hAA : A = A' := by rw [← e1, ← e2, h1]
  subst hAA
  have hl : l = l' := Subtype.ext h1
  have hr : r = r' := Subtype.ext h2
  subst hl
  subst hr
  rfl

theorem RootCut_surjective {Z : Finset α} (h2 : 2 ≤ Z.card) :
    Function.Surjective
      (fun p : RootCut (α := α) Z => mkNode (Finset.mem_powerset.mp p.1.2) p.2.1 p.2.2) := by
  intro t
  obtain ⟨l, r, hlr⟩ := RTree.LTon.isNode h2 t
  have hnd : (RTree.node l r).leaves.Nodup := hlr ▸ t.2.1
  have hZ' : (RTree.node l r).leaves.toFinset = Z := hlr ▸ t.2.2
  rw [RTree.leaves_node, List.toFinset_append] at hZ'
  obtain ⟨hl, hr, hdisj⟩ := List.nodup_append.mp hnd
  have hsub : l.leaves.toFinset ⊆ Z := by
    rw [← hZ']; exact Finset.subset_union_left
  have hmem : ∀ a, a ∈ l.leaves.toFinset ∨ a ∈ r.leaves.toFinset ↔ a ∈ Z := by
    intro a; rw [← hZ', Finset.mem_union]
  have hdisj' : Disjoint l.leaves.toFinset r.leaves.toFinset := by
    rw [Finset.disjoint_left]
    intro a ha hb
    exact hdisj a (List.mem_toFinset.mp ha) a (List.mem_toFinset.mp hb) rfl
  have htf : r.leaves.toFinset = Z \ l.leaves.toFinset := by
    ext a
    rw [Finset.mem_sdiff]
    constructor
    · intro ha
      exact ⟨(hmem a).mp (Or.inr ha), fun hc => Finset.disjoint_left.mp hdisj' hc ha⟩
    · rintro ⟨hz, hnot⟩
      rcases (hmem a).mpr hz with h | h
      · exact absurd h hnot
      · exact h
  refine ⟨⟨⟨l.leaves.toFinset, Finset.mem_powerset.mpr hsub⟩,
    (⟨l, hl, rfl⟩, ⟨r, hr, htf⟩)⟩, ?_⟩
  apply Subtype.ext
  show RTree.node l r = (t : RTree α)
  rw [hlr]

/-- The tree sum over all splits of `Z`: the total weight of pairs of trees on complementary
parts. -/
noncomputable def pairSum (k : V → V → ℝ) (Z : Finset α) (y : α → V) (v : V)
    (A : Finset α) : ℝ :=
  ∑ l : LTon α A, ∑ r : LTon α (Z \ A), RTree.wtL k (RTree.node l.1 r.1) y v

theorem sum_powerset_pairSum {Z : Finset α} (h2 : 2 ≤ Z.card) (k : V → V → ℝ) (y : α → V)
    (v : V) :
    ∑ A ∈ Z.powerset, pairSum k Z y v A = ∑ t : LTon α Z, RTree.wtL k t.1 y v := by
  classical
  rw [Finset.sum_subtype (p := fun A : Finset α => A ∈ Z.powerset) Z.powerset
    (fun A => Iff.rfl) (fun A => pairSum k Z y v A)]
  have h1 : (∑ A : {A : Finset α // A ∈ Z.powerset}, pairSum k Z y v A.1)
      = ∑ A : {A : Finset α // A ∈ Z.powerset},
        ∑ p : LTon α A.1 × LTon α (Z \ A.1),
          RTree.wtL k (RTree.node p.1.1 p.2.1) y v := by
    refine Finset.sum_congr rfl fun A _ => ?_
    exact (Fintype.sum_prod_type (fun p : LTon α A.1 × LTon α (Z \ A.1) =>
      RTree.wtL k (RTree.node p.1.1 p.2.1) y v)).symm
  rw [h1]
  have h3 : (∑ A : {A : Finset α // A ∈ Z.powerset},
        ∑ p : LTon α A.1 × LTon α (Z \ A.1), RTree.wtL k (RTree.node p.1.1 p.2.1) y v)
      = ∑ x : RootCut (α := α) Z, RTree.wtL k (RTree.node x.2.1.1 x.2.2.1) y v :=
    (Fintype.sum_sigma (fun x : RootCut (α := α) Z =>
      RTree.wtL k (RTree.node x.2.1.1 x.2.2.1) y v)).symm
  rw [h3]
  refine Fintype.sum_bijective
    (fun p : RootCut (α := α) Z => mkNode (Finset.mem_powerset.mp p.1.2) p.2.1 p.2.2)
    ⟨RootCut_injective, RootCut_surjective h2⟩
    (fun p => RTree.wtL k (RTree.node p.2.1.1 p.2.2.1) y v)
    (fun t => RTree.wtL k t.1 y v) (fun p => rfl)


open Finset
open Classical

variable {α : Type*} [DecidableEq α] {V : Type*} [Fintype V]

/-! ### Reversing a split does not change the pair sum -/

theorem pairSum_sdiff {Z A : Finset α} (hAZ : A ⊆ Z) (k : V → V → ℝ) (y : α → V) (v : V) :
    pairSum k Z y v (Z \ A) = pairSum k Z y v A := by
  rw [pairSum, pairSum, Finset.sdiff_sdiff_eq_self hAZ, Finset.sum_comm]
  refine Finset.sum_congr rfl fun r _ => Finset.sum_congr rfl fun l _ => ?_
  rw [RTree.wtL_node, RTree.wtL_node]
  exact Finset.sum_congr rfl fun w _ => by ring

theorem pairSum_self (k : V → V → ℝ) (Z : Finset α) (y : α → V) (v : V) :
    pairSum k Z y v Z = 0 := by
  have := RTree.LTon.isEmpty_empty (α := α)
  rw [pairSum, Finset.sdiff_self]
  simp

theorem pairSum_empty (k : V → V → ℝ) (Z : Finset α) (y : α → V) (v : V) :
    pairSum k Z y v ∅ = 0 := by
  have := RTree.LTon.isEmpty_empty (α := α)
  rw [pairSum]
  simp

/-! ### The half-turn symmetry of the splits -/

theorem sum_filter_not_eq_sum_filter {Z : Finset α} {a₀ : α} (ha₀ : a₀ ∈ Z) (f : Finset α → ℝ)
    (hf : ∀ A ⊆ Z, f (Z \ A) = f A) :
    ∑ A ∈ Z.powerset.filter (fun A => a₀ ∉ A), f A
      = ∑ A ∈ Z.powerset.filter (fun A => a₀ ∈ A), f A := by
  refine Finset.sum_bij (fun A _ => Z \ A) ?_ ?_ ?_ ?_
  · intro A hA
    rw [Finset.mem_filter, Finset.mem_powerset] at hA ⊢
    exact ⟨Finset.sdiff_subset, Finset.mem_sdiff.mpr ⟨ha₀, hA.2⟩⟩
  · intro A hA A' hA' heq
    rw [Finset.mem_filter, Finset.mem_powerset] at hA hA'
    calc A = Z \ (Z \ A) := (Finset.sdiff_sdiff_eq_self hA.1).symm
      _ = Z \ (Z \ A') := by rw [heq]
      _ = A' := Finset.sdiff_sdiff_eq_self hA'.1
  · intro B hB
    rw [Finset.mem_filter, Finset.mem_powerset] at hB
    refine ⟨Z \ B, ?_, ?_⟩
    · rw [Finset.mem_filter, Finset.mem_powerset]
      exact ⟨Finset.sdiff_subset, by simp [Finset.mem_sdiff, hB.2]⟩
    · exact Finset.sdiff_sdiff_eq_self hB.1
  · intro A hA
    rw [Finset.mem_filter, Finset.mem_powerset] at hA
    exact (hf A hA.1).symm

/-- The subsets of `Z` containing `a₀` are the splits together with `Z` itself. -/
theorem filter_mem_eq_insert {Z : Finset α} {a₀ : α} (ha₀ : a₀ ∈ Z) :
    Z.powerset.filter (fun A => a₀ ∈ A) = insert Z (splits Z a₀) := by
  ext A
  simp only [splits, Finset.mem_insert, Finset.mem_filter, Finset.mem_powerset]
  constructor
  · rintro ⟨hsub, hmem⟩
    by_cases hAZ : A = Z
    · exact Or.inl hAZ
    · exact Or.inr ⟨hsub, ⟨a₀, hmem⟩, hAZ, hmem⟩
  · rintro (rfl | ⟨hsub, -, -, hmem⟩)
    · exact ⟨le_rfl, ha₀⟩
    · exact ⟨hsub, hmem⟩

/-- **The doubling identity**: the total tree weight on `Z` is twice the sum of the pair sums
over the splits of `Z` at any basepoint. -/
theorem two_mul_sum_splits_pairSum {Z : Finset α} {a₀ : α} (ha₀ : a₀ ∈ Z) (h2 : 2 ≤ Z.card)
    (k : V → V → ℝ) (y : α → V) (v : V) :
    2 * ∑ A ∈ splits Z a₀, pairSum k Z y v A = ∑ t : LTon α Z, RTree.wtL k t.1 y v := by
  have htot := sum_powerset_pairSum (k := k) (y := y) (v := v) h2
  have hsym := sum_filter_not_eq_sum_filter (Z := Z) (a₀ := a₀) ha₀
    (fun A => pairSum k Z y v A) (fun A hA => pairSum_sdiff hA k y v)
  have hsplit := Finset.sum_filter_add_sum_filter_not (Z.powerset) (fun A => a₀ ∈ A)
    (fun A => pairSum k Z y v A)
  have hins := filter_mem_eq_insert (Z := Z) (a₀ := a₀) ha₀
  have hZmem : Z ∉ splits Z a₀ := by
    simp only [splits, Finset.mem_filter]
    exact fun h => h.2.2.1 rfl
  have hins' : ∑ A ∈ Z.powerset.filter (fun A => a₀ ∈ A), pairSum k Z y v A
      = pairSum k Z y v Z + ∑ A ∈ splits Z a₀, pairSum k Z y v A := by
    rw [hins, Finset.sum_insert hZmem]
  have hZ0 := pairSum_self k Z y v
  linarith [htot, hsym, hsplit, hins', hZ0]

/-! ### The factorization of the tree sum at a split -/

/-- Factoring a double tree sum at a split: the algebraic step of the recursion. -/
theorem factor_pair {ι κ : Type*} [Fintype ι] [Fintype κ]
    (c₁ c₂ : ℝ) (k : V → V → ℝ) (f : ι → V → ℝ) (g : κ → V → ℝ) (v : V) :
    (∑ w : V, k v w * (c₁ * ∑ i, f i w) * (c₂ * ∑ j, g j w))
      = c₁ * c₂ * ∑ p : ι × κ, ∑ w : V, k v w * f p.1 w * g p.2 w := by
  have hbody : ∀ w : V, k v w * (c₁ * ∑ i, f i w) * (c₂ * ∑ j, g j w)
      = ∑ i, ∑ j, (c₁ * c₂) * (k v w * f i w * g j w) := by
    intro w
    rw [Finset.mul_sum, Finset.mul_sum, Finset.mul_sum, Finset.sum_mul_sum]
    exact Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => by ring
  simp only [hbody]
  rw [Finset.sum_comm]
  conv_lhs => enter [2, i]; rw [Finset.sum_comm]
  rw [Finset.mul_sum, Fintype.sum_prod_type]
  refine Finset.sum_congr rfl fun i _ => ?_
  refine Finset.sum_congr rfl fun j _ => ?_
  rw [Finset.mul_sum]

/-- The recursion term at a split factorizes into the two normalized tree sums. -/
theorem TS_split_factor {Z A : Finset α} (hAZ : A ⊆ Z) (k : V → V → ℝ) (y : α → V) (v : V) :
    ∑ w : V, k v w * TS k A y w * TS k (Z \ A) y w
      = (1 / 2 ^ (A.card - 1)) * (1 / 2 ^ ((Z \ A).card - 1)) * pairSum k Z y v A := by
  have h1 : (∑ w : V, k v w * TS k A y w * TS k (Z \ A) y w)
      = (1 / 2 ^ (A.card - 1) : ℝ) * (1 / 2 ^ ((Z \ A).card - 1) : ℝ) *
        ∑ p : LTon α A × LTon α (Z \ A), ∑ w : V,
          k v w * RTree.wtL k p.1.1 y w * RTree.wtL k p.2.1 y w := by
    simpa only [TS, OnTrees] using
      factor_pair (1 / 2 ^ (A.card - 1)) (1 / 2 ^ ((Z \ A).card - 1)) k
        (fun l : LTon α A => fun w => RTree.wtL k l.1 y w)
        (fun r : LTon α (Z \ A) => fun w => RTree.wtL k r.1 y w) v
  rw [h1, pairSum, Fintype.sum_prod_type]
  congr 1

/-! ### The recursion identity -/

/-- **The tree-sum recursion identity** (I.2.2) for an arbitrary label finset. -/
theorem TS_recursion {Z : Finset α} (k : V → V → ℝ) (y : α → V) (v : V) {a₀ : α}
    (ha₀ : a₀ ∈ Z) (h2 : 2 ≤ Z.card) :
    TS k Z y v = ∑ A ∈ splits Z a₀, ∑ w : V, k v w * TS k A y w * TS k (Z \ A) y w := by
  classical
  set n := Z.card with hn
  have hcoef : ∀ A ∈ splits Z a₀,
      (1 / 2 ^ (A.card - 1) : ℝ) * (1 / 2 ^ ((Z \ A).card - 1) : ℝ) * pairSum k Z y v A
        = (1 / 2 ^ (n - 2) : ℝ) * pairSum k Z y v A := by
    intro A hA
    obtain ⟨hAZ, hne, hneZ, hmem⟩ := mem_splits hA
    have hcard : (Z \ A).card + A.card = n := by
      rw [hn]; exact Finset.card_sdiff_add_card_eq_card hAZ
    have hA1 : 1 ≤ A.card := Finset.card_pos.mpr hne
    have hbne : (Z \ A).Nonempty := by
      rw [Finset.sdiff_nonempty]
      intro hsub
      exact hneZ (Finset.Subset.antisymm hAZ hsub)
    have hb1 : 1 ≤ (Z \ A).card := Finset.card_pos.mpr hbne
    have hxy : (2 : ℝ) ^ (A.card - 1) * (2 : ℝ) ^ ((Z \ A).card - 1) = (2 : ℝ) ^ (n - 2) := by
      rw [← pow_add]
      congr 1
      omega
    rw [← hxy]
    have hx : (2 : ℝ) ^ (A.card - 1) ≠ 0 := by positivity
    have hy : (2 : ℝ) ^ ((Z \ A).card - 1) ≠ 0 := by positivity
    field_simp
  have hstep : ∑ A ∈ splits Z a₀, ∑ w : V, k v w * TS k A y w * TS k (Z \ A) y w
      = (1 / 2 ^ (n - 2) : ℝ) * ∑ A ∈ splits Z a₀, pairSum k Z y v A := by
    rw [Finset.mul_sum]
    exact Finset.sum_congr rfl fun A hA => by
      rw [TS_split_factor (mem_splits hA).1]
      exact hcoef A hA
  have hmain := two_mul_sum_splits_pairSum (Z := Z) (a₀ := a₀) ha₀ h2 k y v
  have hTS : TS k Z y v = (1 / 2 ^ (n - 1) : ℝ) * ∑ t : LTon α Z, RTree.wtL k t.1 y v := by
    rw [TS, OnTrees, hn]
  have hpow : (2 : ℝ) ^ (n - 1) = (2 : ℝ) ^ (n - 2) * 2 := by
    rw [show n - 1 = n - 2 + 1 by omega, pow_succ]
  have hcoef2 : (1 / 2 ^ (n - 1) : ℝ) * 2 = 1 / 2 ^ (n - 2) := by
    rw [hpow]
    have h2' : (2 : ℝ) ^ (n - 2) ≠ 0 := by positivity
    field_simp
  have hexp : (1 / 2 ^ (n - 1) : ℝ) * ∑ t : LTon α Z, RTree.wtL k t.1 y v
      = (1 / 2 ^ (n - 2) : ℝ) * ∑ A ∈ splits Z a₀, pairSum k Z y v A := by
    rw [← hmain, ← mul_assoc, hcoef2]
  rw [hTS, hexp, ← hstep]


open Finset
open Classical
open PercLib.CriticalLRP.TreeGraph

variable {α : Type*} [DecidableEq α] {V : Type*} [Fintype V]

/-- At two labels the split family at the basepoint `0` is the singleton `{{0}}`. -/
theorem splits_fin_two : splits (Finset.univ : Finset (Fin 2)) (0 : Fin 2) = {{0}} := by
  decide

/-- The recursion at two labels, with the two singleton tree sums evaluated. -/
theorem TS_two_via_recursion (k : V → V → ℝ) (y : Fin 2 → V) (v : V) :
    TS k (Finset.univ : Finset (Fin 2)) y v
      = ∑ w : V, k v w * k w (y 0) * k w (y 1) := by
  have h2 : 2 ≤ (Finset.univ : Finset (Fin 2)).card := by simp
  have hrec := TS_recursion (Z := (Finset.univ : Finset (Fin 2))) k y v
    (a₀ := (0 : Fin 2)) (by simp) h2
  rw [hrec, splits_fin_two, Finset.sum_singleton]
  have h1 : (Finset.univ : Finset (Fin 2)) \ {0} = {1} := by decide
  rw [h1]
  refine Finset.sum_congr rfl fun w _ => ?_
  rw [TS_singleton, TS_singleton]

/-- **Consistency check**: the recursive formula for the tree sum agrees with the direct
computation of the tree sum from its definition at two labels. -/
theorem TS_two_direct (k : V → V → ℝ) (y : Fin 2 → V) (v : V) :
    TS k (Finset.univ : Finset (Fin 2)) y v
      = ∑ w : V, k v w * k w (y 0) * k w (y 1) := by
  rw [TS_univ_eq_treeSum, treeSum_two]


open Finset
open Classical
open PercLib.CriticalLRP.TreeGraph
open PercLib.CriticalLRP.VolumeMoments

variable {α : Type*} [DecidableEq α]

/-- Map a proper subset `B` of `Z.erase a₀` to the split `insert a₀ B` of `Z`. -/
theorem sum_splits_eq_sum_erase {Z : Finset α} {a₀ : α} (ha₀ : a₀ ∈ Z) (h2 : 2 ≤ Z.card)
    (g : ℕ → ℝ) :
    ∑ A ∈ splits Z a₀, g (A.card - 1) * g ((Z \ A).card - 1)
      = ∑ B ∈ (Z.erase a₀).powerset.erase (Z.erase a₀), g B.card *
          g ((Z.erase a₀).card - B.card - 1) := by
  classical
  set s := Z.erase a₀ with hs
  have hsZ : s ⊆ Z := Finset.erase_subset a₀ Z
  have ha₀s : a₀ ∉ s := Finset.notMem_erase a₀ Z
  have hcard : Z.card = s.card + 1 := by
    rw [hs, Finset.card_erase_of_mem ha₀]; omega
  refine Eq.symm ?_
  refine Finset.sum_bij (fun B _ => insert a₀ B) ?_ ?_ ?_ ?_
  · -- the image lies in the splits
    intro B hB
    rw [Finset.mem_erase, Finset.mem_powerset] at hB
    obtain ⟨hBs, hBsub⟩ := hB
    have ha₀B : a₀ ∉ B := fun h => ha₀s (hBsub h)
    have hinsZ : insert a₀ B ⊆ Z := Finset.insert_subset ha₀ (hBsub.trans hsZ)
    have hneZ : insert a₀ B ≠ Z := by
      intro heq
      have : B = s := by rw [← Finset.erase_insert ha₀B, heq, hs]
      exact hBs this
    rw [splits, Finset.mem_filter, Finset.mem_powerset]
    exact ⟨hinsZ, Finset.insert_nonempty _ _, hneZ, Finset.mem_insert_self a₀ B⟩
  · -- injectivity
    intro B hB B' hB' heq
    rw [Finset.mem_erase, Finset.mem_powerset] at hB hB'
    have h1 : a₀ ∉ B := fun h => ha₀s (hB.2 h)
    have h2 : a₀ ∉ B' := fun h => ha₀s (hB'.2 h)
    have h3 := congrArg (fun t => Finset.erase t a₀) heq
    rwa [Finset.erase_insert h1, Finset.erase_insert h2] at h3
  · -- surjectivity
    intro A hA
    obtain ⟨hAZ, hneA, hneZ, hmem⟩ := mem_splits hA
    have ha₀A : a₀ ∈ A := hmem
    refine ⟨A.erase a₀, ?_, Finset.insert_erase ha₀A⟩
    rw [Finset.mem_erase, Finset.mem_powerset, hs]
    refine ⟨?_, ?_⟩
    · intro hEq
      have h1 : insert a₀ (A.erase a₀) = insert a₀ (Z.erase a₀) := by rw [hEq]
      rw [Finset.insert_erase ha₀A, Finset.insert_erase ha₀] at h1
      exact hneZ h1
    · intro x hx
      rw [Finset.mem_erase] at hx
      exact Finset.mem_erase.mpr ⟨hx.1, hAZ hx.2⟩
  · -- the values agree
    intro B hB
    rw [Finset.mem_erase, Finset.mem_powerset] at hB
    obtain ⟨hBs, hBsub⟩ := hB
    have ha₀B : a₀ ∉ B := fun h => ha₀s (hBsub h)
    have hins : (insert a₀ B).card = B.card + 1 := Finset.card_insert_of_notMem ha₀B
    have hsub : insert a₀ B ⊆ Z := Finset.insert_subset ha₀ (hBsub.trans hsZ)
    have hcompl : (Z \ insert a₀ B).card = s.card - B.card := by
      rw [Finset.card_sdiff, Finset.inter_eq_left.mpr hsub, hins]
      omega
    show g B.card * g (s.card - B.card - 1) = g ((insert a₀ B).card - 1) *
      g ((Z \ insert a₀ B).card - 1)
    rw [hins, hcompl, Nat.add_sub_cancel]

/-- Summing a function of the cardinality over a powerset. -/
theorem sum_powerset_card (s : Finset α) (g : ℕ → ℝ) :
    ∑ B ∈ s.powerset, g B.card = ∑ j ∈ Finset.range (s.card + 1), (s.card.choose j : ℝ) * g j := by
  rw [Finset.sum_powerset]
  refine Finset.sum_congr rfl fun j _ => ?_
  rw [Finset.sum_powersetCard]
  simp [nsmul_eq_mul, mul_comm]

/-- **The split sum of the recursion for the constant kernel is the double factorial.** -/
theorem sum_splits_M {Z : Finset α} {a₀ : α} (ha₀ : a₀ ∈ Z) (h2 : 2 ≤ Z.card) :
    ∑ A ∈ splits Z a₀, (M (A.card - 1) : ℝ) * (M ((Z \ A).card - 1) : ℝ)
      = (M (Z.card - 1) : ℝ) := by
  classical
  rw [sum_splits_eq_sum_erase ha₀ h2 (fun n => (M n : ℝ))]
  set s := Z.erase a₀ with hs
  have hcard : Z.card = s.card + 1 := by
    rw [hs, Finset.card_erase_of_mem ha₀]; omega
  have hm : 1 ≤ s.card := by omega
  have hmem : s ∈ s.powerset := Finset.mem_powerset.mpr (Finset.Subset.refl s)
  set m := s.card with hmdef
  -- the fibre term at the full set
  have htop : (M m : ℝ) * (M (m - m - 1) : ℝ) = (M m : ℝ) := by
    simp
  -- the powerset sum minus the full set
  have herase : ∑ B ∈ s.powerset.erase s, (M B.card : ℝ) * (M (m - B.card - 1) : ℝ)
      = (∑ B ∈ s.powerset, (M B.card : ℝ) * (M (m - B.card - 1) : ℝ)) - (M m : ℝ) := by
    have h := Finset.sum_erase_add (s := s.powerset) (a := s)
      (f := fun B => (M B.card : ℝ) * (M (m - B.card - 1) : ℝ)) hmem
    have hval : (M s.card : ℝ) * (M (m - s.card - 1) : ℝ) = (M m : ℝ) := by
      rw [hmdef]; exact htop
    rw [hval] at h
    linarith
  have hp := sum_powerset_card (s := s) (fun k => (M k : ℝ) * (M (m - k - 1) : ℝ))
  rw [herase, hp]
  -- split off the last term of the range sum
  rw [Finset.sum_range_succ]
  have hlast : (m.choose m : ℝ) * ((M m : ℝ) * (M (m - m - 1) : ℝ)) = (M m : ℝ) := by
    simp
  rw [hlast]
  -- the remaining sum is `SA m`
  have hSA : (∑ j ∈ Finset.range m, (m.choose j : ℝ) * ((M j : ℝ) * (M (m - j - 1) : ℝ)))
      = (SA m : ℝ) := by
    rw [SA]
    push_cast
    refine Finset.sum_congr rfl fun j hj => ?_
    rw [Finset.mem_range] at hj
    rw [show m - j - 1 = m - 1 - j by omega]
  rw [hSA, lemma_I_4_23 m hm, hcard]
  norm_num

/-- **The constant-kernel tree sum is the double factorial**: for the kernel `k ≡ 1` on a
one-point vertex set, the normalised tree sum equals `(2|Z|−3)!!`, the number of non-plane
rooted binary trees with `|Z|` labelled leaves. -/
theorem TS_const_punit : ∀ (n : ℕ) (Z : Finset α), Z.card = n → Z.Nonempty →
    ∀ (y : α → PUnit) (v : PUnit),
      TS (fun _ _ => (1 : ℝ)) Z y v = (M (Z.card - 1) : ℝ) := by
  intro n
  induction n using Nat.strong_induction_on with
  | _ n ih =>
    intro Z hZ hne y v
    have hpun : ∀ f : PUnit → ℝ, (∑ w : PUnit, f w) = f PUnit.unit := by
      intro f
      refine Finset.sum_eq_single PUnit.unit ?_ ?_
      · intro b _ hb
        exact absurd (Subsingleton.elim b PUnit.unit) hb
      · intro h
        exact absurd (Finset.mem_univ _) h
    rcases Nat.lt_or_ge Z.card 2 with h1 | h2
    · have hc : Z.card = 1 := by
        have := Finset.card_pos.mpr hne
        omega
      obtain ⟨a, rfl⟩ := Finset.card_eq_one.mp hc
      rw [TS_singleton]
      norm_num
    · obtain ⟨a₀, ha₀⟩ := hne
      rw [TS_recursion (k := fun _ _ => (1 : ℝ)) y v ha₀ h2]
      have hterm : ∀ A ∈ splits Z a₀,
          (∑ w : PUnit, (1 : ℝ) * TS (fun _ _ => (1 : ℝ)) A y w *
            TS (fun _ _ => (1 : ℝ)) (Z \ A) y w)
            = (M (A.card - 1) : ℝ) * (M ((Z \ A).card - 1) : ℝ) := by
        intro A hA
        obtain ⟨hAZ, hneA, hneZ, hmem⟩ := mem_splits hA
        have hltA : A.card < n := by
          have hss : A ⊂ Z := Finset.ssubset_iff_subset_ne.mpr ⟨hAZ, hneZ⟩
          have := Finset.card_lt_card hss
          omega
        have hbne : (Z \ A).Nonempty := by
          rw [Finset.sdiff_nonempty]
          intro hsub
          exact hneZ (Finset.Subset.antisymm hAZ hsub)
        have hltB : (Z \ A).card < n := by
          have hne2 : Z \ A ≠ Z := by
            intro h
            obtain ⟨x, hx⟩ := hneA
            have hx2 : x ∈ Z \ A := by rw [h]; exact hAZ hx
            exact (Finset.mem_sdiff.mp hx2).2 hx
          have hss : Z \ A ⊂ Z := Finset.ssubset_iff_subset_ne.mpr ⟨Finset.sdiff_subset, hne2⟩
          have := Finset.card_lt_card hss
          omega
        rw [hpun]
        rw [ih A.card hltA A rfl hneA y PUnit.unit,
          ih (Z \ A).card hltB (Z \ A) rfl hbne y PUnit.unit]
        ring
      rw [Finset.sum_congr rfl hterm]
      exact sum_splits_M ha₀ h2

end PercLib.CriticalLRP.TreeExpansion
namespace PercLib.CriticalLRP.TreeGraph

open Finset
open PercLib.CriticalLRP.TreeExpansion

variable {V : Type*} [Fintype V] [DecidableEq V]
variable {E : Type*} [Fintype E] [DecidableEq E]

/-- **The tree-sum recursion holds for every label count** (the hypothesis `TreeSumRecursionAt`
of `treeGraphBound_of_bk`), for any kernel and any `m`. -/
theorem treeSumRecursionAt (k : V → V → ℝ) (m : ℕ) : TreeSumRecursionAt k m := by
  intro Z y v a₀ ha₀ h2
  exact TS_recursion k y v ha₀ h2

/-- **The tree-graph inequality (I.2.2)**, unconditionally from the BK inequality. -/
theorem treeGraphBound_of_bk' {ends : E → Sym2 V} (pr : E → ℝ) (hp : ∀ e, 0 ≤ pr e)
    (hp1 : ∀ e, pr e ≤ 1) (hBK : BKIncreasing pr) :
    TreeGraphBound pr ends (twoPoint pr ends) :=
  treeGraphBound_of_bk pr hp hp1 hBK (fun m => treeSumRecursionAt (twoPoint pr ends) m)

end PercLib.CriticalLRP.TreeGraph
namespace PercLib.CriticalLRP.TreeExpansion


open PercLib.CriticalLRP.TreeGraph

variable {V : Type*} [Fintype V] [DecidableEq V] [AddCommGroup V]
variable {E : Type*} [Fintype E] [DecidableEq E]

/-- **Inequality (I.2.3)**, unconditionally from the BK inequality: for a Bernoulli bond
percolation with two-point function `twoPoint pr ends`, under translation invariance of the
two-point function, the `q`-th moment of the cluster volume is at most
`(2q-3)!! (E|K|)^{2q-1}`. -/
theorem moment_bound_of_bk (pr : E → ℝ) (hp : ∀ e, 0 ≤ pr e) (hp1 : ∀ e, pr e ≤ 1)
    (ends : E → Sym2 V) (o : V)
    (hinv : ∀ a b : V, twoPoint pr ends a b = twoPoint pr ends o (b - a))
    (hBK : BKIncreasing pr) (q : ℕ) (hq : 1 ≤ q) :
    (∑ x : Fin q → V, prob pr {s | ∀ i : Fin q, Conn ends s o (x i)})
      ≤ (VolumeMoments.M (q - 1) : ℝ) * (clusterVolume pr ends o) ^ (2 * q - 1) :=
  moment_bound_of_tree_graph pr hp hp1 ends o hinv
    (treeGraphBound_of_bk' pr hp hp1 hBK) q hq


open Finset
open PercLib.CriticalLRP.TreeGraph

variable {V : Type*} [Fintype V] [DecidableEq V] [AddCommGroup V]
variable {E : Type*} [Fintype E] [DecidableEq E]

/-- **Inequality (I.2.3)** in the paper's form `E_β|K_o|^q ≤ (2q−3)!! (E_β|K_o|)^{2q−1}`,
unconditionally from the BK inequality: the only hypotheses are the Bernoulli weights, the
translation invariance of the two-point function, and BK itself. -/
theorem moment_bound_of_bk_expectation
    (pr : E → ℝ) (hp : ∀ e, 0 ≤ pr e) (hp1 : ∀ e, pr e ≤ 1)
    (ends : E → Sym2 V) (o : V)
    (hinv : ∀ a b : V, twoPoint pr ends a b = twoPoint pr ends o (b - a))
    (hBK : BKIncreasing pr) (q : ℕ) (hq : 1 ≤ q) :
    expectReal pr (fun s => (clusterVol ends s o : ℝ) ^ q)
      ≤ (VolumeMoments.M (q - 1) : ℝ) * (clusterVolume pr ends o) ^ (2 * q - 1) := by
  rw [clusterMoment_eq_expectation]
  exact moment_bound_of_bk pr hp hp1 ends o hinv hBK q hq

/-- The same bound on `E|K_o|^q` with the combinatorial factor `(2q−3)!!` spelled as
`VolumeMoments.M (q−1)`, in the summation form used throughout the development. -/
theorem clusterMoment_le_dfactorial
    (pr : E → ℝ) (hp : ∀ e, 0 ≤ pr e) (hp1 : ∀ e, pr e ≤ 1)
    (ends : E → Sym2 V) (o : V)
    (hinv : ∀ a b : V, twoPoint pr ends a b = twoPoint pr ends o (b - a))
    (hBK : BKIncreasing pr) (q : ℕ) (hq : 1 ≤ q) :
    expectReal pr (fun s => (clusterVol ends s o : ℝ) ^ q)
      ≤ (VolumeMoments.M (q - 1) : ℝ) * (expectReal pr (fun s => (clusterVol ends s o : ℝ)))
          ^ (2 * q - 1) := by
  refine le_trans (moment_bound_of_bk_expectation pr hp hp1 ends o hinv hBK q hq) ?_
  rw [← expectation_clusterVol pr ends o]

end PercLib.CriticalLRP.TreeExpansion
