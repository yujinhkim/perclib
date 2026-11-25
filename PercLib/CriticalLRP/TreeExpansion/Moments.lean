/-
Migration source: https://github.com/yujinhkim/Critical-Long-range-percolation
Integration revision: 3b3d1d0e43ef940bfaa2292ee5c2ee094ac4edbf
Licence: Apache-2.0 for the PercLib Lean sources and tooling; see third_party/critical-lrp/.
External provenance and modifications are recorded in the file-specific notices below.
-/

/-
The derivation of the cluster-moment bound (I.2.3) from the tree-graph inequality
(I.2.2) of

  T. Hutchcroft, *Critical long-range percolation I: High effective dimension*,
  arXiv:2508.18807v1, Section I.2.1, p. 22.

The paper's (I.2.2) reads

  `P_β(x₀,...,x_k all connected) ≤ ∑_{T ∈ T_k} ∑_{x_{k+1},...,x_{2k−1}} ∏_{i<j, i∼j} P_β(x_i ↔ x_j)`

with `T_k` the isomorphism classes of trees with leaves labelled `0,...,k` and all other
vertices unlabelled of degree 3, and (I.2.3) reads

  `E_β|K|^p ≤ (2p−3)!! (E_β|K|)^{2p−1}`.

Rooting an unrooted tree with leaves `0,...,k` at the leaf `0` and suppressing the
resulting degree-2 vertex turns `T_k` into the non-plane rooted binary trees with leaves
`1,...,k`. Accordingly the tree sum of (I.2.2) is realised here as `2^{-(k−1)}` times the
sum over *plane* rooted trees (`treeSum` below): each non-plane tree with `k` labelled
leaves has exactly `2^(k−1)` plane orderings.

`TreeGraphBound` below is the explicit hypothesis (I.2.2) in this form: it is the
content of the tree-graph inequality, which the paper derives from the BK inequality
(and which this file does not prove). Everything else in the passage from (I.2.2) to
(I.2.3) is proved here:

* `RTree.sum_wt_labelled`: for a kernel with constant row sums `S`, every rooted tree
  with `k` labelled leaves contributes exactly `S^(2k−1)` after summing over the free
  leaves and the internal vertices;
* `RTree.card_LT_fin_le`: there are at most `2^(k−1)·(2k−3)!!` plane trees, i.e.
  `(2k−3)!!` non-plane trees, with `k` labelled leaves;
* `moment_bound_of_tree_graph`: the moment bound (I.2.3).
-/
module

public import Mathlib
public import PercLib.CriticalLRP.TreeExpansion.Count
public import PercLib.CriticalLRP.TreeGraph.ClusterMoments

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
open PercLib.CriticalLRP.TreeGraph

namespace RTree

variable {α : Type*} {V : Type*}

/-! ### The label of a leaf position, and its basic properties -/

theorem leafOfPos_mem : ∀ (t : RTree α) (q : LeafPos t), leafOfPos t q ∈ t.leaves
  | leaf a, _ => by simp [leafOfPos]
  | node l r, Sum.inl q => by
      simp only [leafOfPos, leaves_node]
      exact List.mem_append_left _ (leafOfPos_mem l q)
  | node l r, Sum.inr q => by
      simp only [leafOfPos, leaves_node]
      exact List.mem_append_right _ (leafOfPos_mem r q)

theorem exists_leafOfPos : ∀ (t : RTree α) (a : α), a ∈ t.leaves → ∃ q : LeafPos t, leafOfPos t q = a
  | leaf b, a, h => ⟨⟨⟩, by
      have hab : a = b := by simpa using h
      simpa [leafOfPos] using hab.symm⟩
  | node l r, a, h => by
      rw [leaves_node] at h
      rcases List.mem_append.mp h with h | h
      · obtain ⟨q, hq⟩ := exists_leafOfPos l a h
        exact ⟨Sum.inl q, hq⟩
      · obtain ⟨q, hq⟩ := exists_leafOfPos r a h
        exact ⟨Sum.inr q, hq⟩

theorem leafOfPos_injective : ∀ {t : RTree α}, t.leaves.Nodup → Function.Injective (leafOfPos t)
  | leaf a, _, x, y, _ => by cases x; cases y; rfl
  | node l r, h, x, y, hxy => by
      rw [leaves_node] at h
      obtain ⟨hl, hr, hdisj⟩ := List.nodup_append.mp h
      match x, y with
      | Sum.inl p, Sum.inl q =>
          exact congrArg Sum.inl (leafOfPos_injective hl hxy)
      | Sum.inl p, Sum.inr q =>
          exact absurd hxy (hdisj (leafOfPos l p) (leafOfPos_mem l p)
            (leafOfPos r q) (leafOfPos_mem r q))
      | Sum.inr p, Sum.inl q =>
          exact absurd hxy.symm (hdisj (leafOfPos l q) (leafOfPos_mem l q)
            (leafOfPos r p) (leafOfPos_mem r p))
      | Sum.inr p, Sum.inr q =>
          exact congrArg Sum.inr (leafOfPos_injective hr hxy)

/-! ### The tree sum of a leaf-labelled tree -/

variable [Fintype V]

/-- **The tree weight identity for labelled trees.** For a kernel whose row sums are all
`S`, summing the tree weight of a fully labelled tree over the values at its leaves gives
`S^(2k−1)`, where `k` is the number of leaves. -/
theorem sum_wt_labelled (k : V → V → ℝ) (S : ℝ) (hS : ∀ v : V, ∑ y : V, k v y = S)
    {p : ℕ} {t : RTree (Fin p)} (ht : FullyLabelled t) (v : V) :
    (∑ x : Fin p → V, wt k t (fun q => x (leafOfPos t q)) v) = S ^ (2 * p - 1) := by
  classical
  have hbij : Function.Bijective (leafOfPos t) :=
    ⟨leafOfPos_injective ht.1,
      fun a => exists_leafOfPos t a (mem_leaves_of_fullyLabelled ht a)⟩
  set e := Equiv.ofBijective (leafOfPos t) hbij with he
  have h1 : (∑ x : Fin p → V, wt k t (fun q => x (leafOfPos t q)) v)
      = ∑ y : LeafPos t → V, wt k t y v := by
    refine Fintype.sum_equiv (Equiv.arrowCongr e (Equiv.refl V)).symm _ _ ?_
    intro x
    rfl
  have hlen : t.numLeaves = p := by
    have h := ht.2
    rw [Fintype.card_fin] at h
    exact h
  rw [h1, sum_wt k S hS t v, hlen]

end RTree

/-! ### The tree-graph inequality (I.2.2), and the moment bound (I.2.3) -/

variable {V : Type*} [Fintype V] [DecidableEq V] [AddCommGroup V]
variable {E : Type*} [Fintype E] [DecidableEq E]

/-- **The tree sum of (I.2.2)**: `2^{-(k-1)}` times the sum over plane rooted binary trees
with `k` leaves of the product of the two-point function over the edges, the root being
pinned at `v` and the `j`-th leaf at `x j`. The factor `2^{-(k-1)}` converts the plane
count into the count of non-plane trees used in the paper. -/
noncomputable def treeSum (k : V → V → ℝ) (m : ℕ) (v : V) (x : Fin m → V) : ℝ :=
  (1 / 2 ^ (m - 1)) * ∑ t : RTree.LT (Fin m),
    RTree.wt k t.val (fun q => x (RTree.leafOfPos t.val q)) v

/-- **Hypothesis (I.2.2)** (the tree-graph inequality), in rooted form: for every
`k ≥ 1`, the probability that `x 0, ..., x k` are all connected is at most the tree sum. -/
def TreeGraphBound (pr : E → ℝ) (ends : E → Sym2 V) (k : V → V → ℝ) : Prop :=
  ∀ (m : ℕ), 1 ≤ m → ∀ x : Fin (m + 1) → V,
    prob pr {s | ∀ i : Fin (m + 1), Conn ends s (x 0) (x i)}
      ≤ treeSum k m (x 0) (fun j => x (Fin.succ j))

/-- **Inequality (I.2.3)**, derived from the tree-graph inequality (I.2.2).

For Bernoulli bond percolation on a finite weighted graph with two-point function
`twoPoint pr ends` satisfying the translation invariance `P(a ↔ b) = T(b − a)`, the
`q`-th moment of the cluster volume of any vertex `o` satisfies

  `E|K_o|^q ≤ (2q−3)!! (E|K_o|)^{2q−1}`,

with `(2q−3)!! = VolumeMoments.M (q−1)` and `E|K_o| = clusterVolume pr ends o` written as
the total mass `∑_y P(o ↔ y)` of the two-point function. The left-hand side is written
as the sum over `x : Fin q → V` of `P(o ↔ x_0, ..., o ↔ x_{q−1})`, which is exactly
`E|K_o|^q` (`clusterMoment_eq_expectation` in `Moment.lean`).

The BK inequality is *not* a hypothesis here: it is already encapsulated in
`TreeGraphBound`, which is (I.2.2). -/
theorem moment_bound_of_tree_graph
    (pr : E → ℝ) (hp : ∀ e, 0 ≤ pr e) (hp1 : ∀ e, pr e ≤ 1)
    (ends : E → Sym2 V) (o : V)
    (hinv : ∀ a b : V, twoPoint pr ends a b = twoPoint pr ends o (b - a))
    (hTG : TreeGraphBound pr ends (twoPoint pr ends))
    (q : ℕ) (hq : 1 ≤ q) :
    (∑ x : Fin q → V, prob pr {s | ∀ i : Fin q, Conn ends s o (x i)})
      ≤ (VolumeMoments.M (q - 1) : ℝ) * (clusterVolume pr ends o) ^ (2 * q - 1) := by
  classical
  set S : ℝ := clusterVolume pr ends o with hSdef
  have hS0 : 0 ≤ S := by
    rw [hSdef, clusterVolume]
    exact Finset.sum_nonneg fun y _ => prob_nonneg hp hp1 _
  have hS : ∀ v : V, ∑ y : V, twoPoint pr ends v y = S := by
    intro v
    rw [hSdef]
    simp only [clusterVolume]
    exact twoPoint_total_eq pr ends o hinv v
  -- step 1: apply the tree-graph inequality termwise
  have hstep : ∀ x : Fin q → V,
      prob pr {s | ∀ i : Fin q, Conn ends s o (x i)}
        ≤ treeSum (twoPoint pr ends) q o x := by
    intro x
    set y : Fin (q + 1) → V := Fin.cases o x with hy
    have hy0 : y 0 = o := rfl
    have hysucc : ∀ j : Fin q, y (Fin.succ j) = x j := fun j => rfl
    have hTG' := hTG q hq y
    have hfun : (fun j => y (Fin.succ j)) = x := funext hysucc
    rw [hfun] at hTG'
    have hset : {s | ∀ i : Fin q, Conn ends s o (x i)}
        = {s | ∀ i : Fin (q + 1), Conn ends s (y 0) (y i)} := by
      ext s
      constructor
      · intro h i
        rw [hy0]
        refine Fin.cases ?_ (fun j => ?_) i
        · exact conn_refl ends s o
        · exact h j
      · intro h i
        exact h (Fin.succ i)
    rw [hset]
    exact hTG'
  -- step 2: sum over the free leaves and evaluate each tree
  have hsum : ∀ t : RTree.LT (Fin q),
      (∑ x : Fin q → V, RTree.wt (twoPoint pr ends) t.val
        (fun r => x (RTree.leafOfPos t.val r)) o) = S ^ (2 * q - 1) := by
    intro t
    exact RTree.sum_wt_labelled (twoPoint pr ends) S hS t.2 o
  calc (∑ x : Fin q → V, prob pr {s | ∀ i : Fin q, Conn ends s o (x i)})
      ≤ ∑ x : Fin q → V, treeSum (twoPoint pr ends) q o x :=
        Finset.sum_le_sum fun x _ => hstep x
    _ = (1 / 2 ^ (q - 1)) * ∑ x : Fin q → V, ∑ t : RTree.LT (Fin q),
          RTree.wt (twoPoint pr ends) t.val (fun r => x (RTree.leafOfPos t.val r)) o := by
        rw [Finset.mul_sum]
        exact Finset.sum_congr rfl fun x _ => rfl
    _ = (1 / 2 ^ (q - 1)) * ∑ t : RTree.LT (Fin q),
          ∑ x : Fin q → V, RTree.wt (twoPoint pr ends) t.val
            (fun r => x (RTree.leafOfPos t.val r)) o := by
        rw [Finset.sum_comm]
    _ = (1 / 2 ^ (q - 1)) * ∑ _t : RTree.LT (Fin q), S ^ (2 * q - 1) := by
        rw [Finset.sum_congr rfl fun t _ => hsum t]
    _ = (1 / 2 ^ (q - 1)) * ((Fintype.card (RTree.LT (Fin q)) : ℝ) * S ^ (2 * q - 1)) := by
        rw [Finset.sum_const, Finset.card_univ, nsmul_eq_mul]
    _ ≤ (1 / 2 ^ (q - 1)) * ((2 ^ (q - 1) * (VolumeMoments.M (q - 1) : ℝ)) *
          S ^ (2 * q - 1)) := by
        refine mul_le_mul_of_nonneg_left ?_ (by positivity)
        refine mul_le_mul_of_nonneg_right ?_ (pow_nonneg hS0 _)
        exact_mod_cast RTree.card_LT_fin_le q
    _ = (VolumeMoments.M (q - 1) : ℝ) * S ^ (2 * q - 1) := by
        have h2 : (2 : ℝ) ^ (q - 1) ≠ 0 := by positivity
        field_simp
    _ = (VolumeMoments.M (q - 1) : ℝ) * (clusterVolume pr ends o) ^ (2 * q - 1) := by
        rw [hSdef]

end PercLib.CriticalLRP.TreeExpansion
