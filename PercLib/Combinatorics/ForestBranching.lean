/-
Copyright (c) 2026 PercLib contributors. Released under Apache 2.0.
New finite-forest degree accounting from mathlib's tree edge count and handshaking
identity. No encounter-point or probabilistic uniqueness statement is assumed.
-/
module

public import Mathlib.Combinatorics.SimpleGraph.Star
public import Mathlib.Tactic.Linarith
public import Mathlib.Tactic.NormNum

@[expose] public section
noncomputable section
open Finset
open scoped Classical
namespace PercLib
variable {W : Type*} [Fintype W]

/-- The signed degree excess of a finite tree is minus two, including the singleton tree. -/
theorem tree_sum_degree_sub_two (T : SimpleGraph W) [DecidableRel T.Adj] (hT : T.IsTree) :
    ∑ v : W, ((T.degree v : ℤ)-2) = -2 := by
  have hc := hT.card_edgeFinset
  have hd := T.sum_degrees_eq_twice_card_edges
  have hd' : (∑ v : W, (T.degree v : ℤ)) = 2 * T.edgeFinset.card := by exact_mod_cast hd
  have hc' : (T.edgeFinset.card : ℤ) + 1 = Fintype.card W := by exact_mod_cast hc
  simp only [sum_sub_distrib,sum_const,card_univ,nsmul_eq_mul]
  omega

/-- Finite sums can be partitioned by connected-component supports. -/
theorem sum_vertices_eq_sum_components (T : SimpleGraph W)
    [Fintype T.ConnectedComponent] {R : Type*} [AddCommMonoid R] (f : W → R) :
    ∑ v, f v = ∑ c : T.ConnectedComponent, ∑ v : c.supp, f v := by
  let e : (Σ c : T.ConnectedComponent, c.supp) ≃ W :=
    { toFun := fun a => a.2.val
      invFun := fun v => ⟨T.connectedComponentMk v,⟨v,rfl⟩⟩
      left_inv := by
        rintro ⟨c,⟨v,hv⟩⟩
        have hc : T.connectedComponentMk v = c := hv
        subst c
        rfl
      right_inv := fun _ => rfl }
  rw [← e.sum_comp f,Fintype.sum_sigma]
  rfl

/-- Passing to a component preserves the degree of each of its vertices. -/
theorem degree_component (T : SimpleGraph W) [DecidableRel T.Adj]
    (c : T.ConnectedComponent) (v : c.supp) : c.toSimpleGraph.degree v = T.degree v := by
  convert! SimpleGraph.degree_induce_of_neighborSet_subset
    (fun _ hw => c.mem_supp_of_adj_mem_supp v.property hw) using 1
  unfold SimpleGraph.degree
  congr 1
  ext w
  simp only [SimpleGraph.mem_neighborFinset]
  rfl

/-- Euler's degree-excess identity for a finite forest, with signed subtraction. -/
theorem forest_sum_degree_sub_two (T : SimpleGraph W) [DecidableRel T.Adj]
    (hT : T.IsAcyclic) :
    ∑ v : W, ((T.degree v : ℤ)-2) = -2 * Nat.card T.ConnectedComponent := by
  let : Fintype T.ConnectedComponent := Fintype.ofFinite _
  rw [sum_vertices_eq_sum_components T]
  have hc (c : T.ConnectedComponent) : (∑ v : c.supp, ((T.degree v : ℤ)-2)) = -2 := by
    have ht := tree_sum_degree_sub_two c.toSimpleGraph (hT.isTree_connectedComponent c)
    simp only [degree_component] at ht
    convert! ht using 1
  simp only [hc,sum_const,card_univ,nsmul_eq_mul,Nat.card_eq_fintype_card]
  exact mul_comm _ _

/-- A nontrivial finite tree has at least two more leaves than branch vertices. -/
theorem tree_card_branch_add_two_le_leaves (T : SimpleGraph W) [DecidableRel T.Adj]
    [Nontrivial W] (hT : T.IsTree) :
    (univ.filter fun v => 3 ≤ T.degree v).card + 2 ≤
      (univ.filter fun v => T.degree v = 1).card := by
  have hpoint (v : W) : (if 3 ≤ T.degree v then (1:ℤ) else 0) ≤
      ((T.degree v : ℤ)-2) + (if T.degree v = 1 then 1 else 0) := by
    have hp := hT.preconnected.degree_pos_of_nontrivial v
    split_ifs <;> omega
  have hsum := sum_le_sum (s := (univ : Finset W)) (fun v _ => hpoint v)
  rw [sum_add_distrib,tree_sum_degree_sub_two T hT] at hsum
  have hb : (∑ v : W, if 3 ≤ T.degree v then (1:ℤ) else 0) =
      (univ.filter fun v => 3 ≤ T.degree v).card := by simp
  have hl : (∑ v : W, if T.degree v = 1 then (1:ℤ) else 0) =
      (univ.filter fun v => T.degree v = 1).card := by simp
  rw [hb,hl] at hsum
  omega

/-- Every finite tree has no more branch vertices than leaves, including its singleton case. -/
theorem tree_card_branch_le_leaves (T : SimpleGraph W) [DecidableRel T.Adj] (hT : T.IsTree) :
    (univ.filter fun v => 3 ≤ T.degree v).card ≤
      (univ.filter fun v => T.degree v = 1).card := by
  cases subsingleton_or_nontrivial W with
  | inl h =>
    simp only [SimpleGraph.degree_eq_zero_of_subsingleton]
    simp
  | inr h => exact (Nat.le_add_right _ 2).trans (tree_card_branch_add_two_le_leaves T hT)

/-- Summing the tree inequalities over components gives the finite-forest branch bound. -/
theorem forest_card_branch_le_leaves (T : SimpleGraph W) [DecidableRel T.Adj]
    (hT : T.IsAcyclic) :
    (univ.filter fun v => 3 ≤ T.degree v).card ≤
      (univ.filter fun v => T.degree v = 1).card := by
  let : Fintype T.ConnectedComponent := Fintype.ofFinite _
  have hb := sum_vertices_eq_sum_components T (fun v => if 3 ≤ T.degree v then (1:ℕ) else 0)
  have hl := sum_vertices_eq_sum_components T (fun v => if T.degree v = 1 then (1:ℕ) else 0)
  calc
    _ = ∑ c : T.ConnectedComponent, (univ.filter fun v : c.supp => 3 ≤ c.toSimpleGraph.degree v).card := by
      simpa only [card_eq_sum_ones,sum_filter,degree_component] using hb
    _ ≤ ∑ c : T.ConnectedComponent, (univ.filter fun v : c.supp => c.toSimpleGraph.degree v = 1).card :=
      sum_le_sum (fun c _ => tree_card_branch_le_leaves c.toSimpleGraph (hT.isTree_connectedComponent c))
    _ = _ := by simpa only [card_eq_sum_ones,sum_filter,degree_component] using hl.symm

/-- If every leaf lies in L, the number of branch vertices is at most |L|-2. -/
theorem tree_card_branch_le_card_sub_two (T : SimpleGraph W) [DecidableRel T.Adj]
    (hT : T.IsTree) (L : Finset W) (hL : ∀ v, T.degree v = 1 → v ∈ L)
    (hcard : 2 ≤ L.card) :
    (univ.filter fun v => 3 ≤ T.degree v).card ≤ L.card - 2 := by
  have hnon : Nontrivial W := Fintype.one_lt_card_iff_nontrivial.mp
    (lt_of_lt_of_le (by omega : 1 < L.card) (card_le_univ L))
  have hl : (univ.filter fun v => T.degree v = 1).card ≤ L.card :=
    card_le_card (fun v hv => hL v (mem_filter.mp hv).2)
  have hb := tree_card_branch_add_two_le_leaves T hT
  omega

-- The empty forest and singleton tree have no branch vertices; neither has leaves.
example : (univ.filter fun v : Empty => 3 ≤ (⊥ : SimpleGraph Empty).degree v).card = 0 := by simp
example : (∑ v : Unit, (((⊥ : SimpleGraph Unit).degree v : ℤ)-2)) = -2 := by simp

-- A star with k≥3 leaves has exactly one branch vertex and k leaves.
example (k : ℕ) (hk : 3 ≤ k) :
    let T := SimpleGraph.starGraph (0 : Fin (k+1))
    T.IsTree ∧ (univ.filter fun v => 3 ≤ T.degree v).card = 1 ∧
      (univ.filter fun v => T.degree v = 1).card = k := by
  dsimp
  refine ⟨SimpleGraph.isTree_starGraph _,?_,?_⟩
  · have he : (univ.filter fun v : Fin (k+1) =>
        3 ≤ (SimpleGraph.starGraph (0 : Fin (k+1))).degree v) = {0} := by
      ext v
      by_cases hv : v = 0
      · subst v; simp [SimpleGraph.degree_starGraph_center,hk]
      · simp [hv,SimpleGraph.degree_starGraph_of_ne_center hv]
    rw [he,card_singleton]
  · have he : (univ.filter fun v : Fin (k+1) =>
        (SimpleGraph.starGraph (0 : Fin (k+1))).degree v = 1) = univ.erase 0 := by
      ext v
      by_cases hv : v = 0
      · subst v; simp [SimpleGraph.degree_starGraph_center]; omega
      · simp [hv,SimpleGraph.degree_starGraph_of_ne_center hv]
    rw [he]
    simp

-- The three-vertex path is the two-leaf star, with no branch vertices.
example :
    let T := SimpleGraph.starGraph (0 : Fin 3)
    T.IsTree ∧ (univ.filter fun v => 3 ≤ T.degree v).card = 0 := by
  dsimp
  refine ⟨SimpleGraph.isTree_starGraph _,?_⟩
  have he : (univ.filter fun v : Fin 3 => 3 ≤ (SimpleGraph.starGraph (0 : Fin 3)).degree v) = ∅ := by
    ext v
    by_cases hv : v = 0
    · subst v; simp [SimpleGraph.degree_starGraph_center]
    · simp [SimpleGraph.degree_starGraph_of_ne_center hv]
  rw [he,card_empty]

end PercLib
