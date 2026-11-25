/-
Copyright (c) 2026 PercLib contributors. Released under Apache 2.0.

Five-point tree-graph infrastructure supplied by Ultramath `smwpj8umm` member m2
and integrated from a verified candidate. The full deterministic five-point
realization and fourth-moment theorem are not asserted by these modules.
-/
module

/-
The five-point (four-plus-one-point) tree-graph input, the level needed for the fourth
cluster moment `E|K|⁴ ≤ 15 (E|K|)⁷`.

The paper's tree-graph inequality (I.2.2) at `k = 4` concerns five points
`root, x₁, x₂, x₃, x₄` all in one component and the fifteen rooted binary trees with the
four labelled leaves `x₁..x₄` (`(2·4−3)!! = 5!! = 15`).  Every such tree is one of

* **comb** (12 labelled shapes): spine `u₁—u₂—u₃` with leaf `x₁` at `u₁`, `x₂` at `u₂`
  and `{x₃, x₄}` at `u₃`  — the choice of the ordered pair `(x₁, x₂)` is free (4·3 = 12);
* **balanced** (3 labelled shapes): `root` at `u`, the pairs `{x₁,x₂}` at `v` and
  `{x₃,x₄}` at `w`, spines `u—v` and `u—w`  — the pairing is free (3).

Each shape is carried by seven pairwise edge-disjoint walks (the tree has
`2·4 − 1 = 7` edges).  The disjointness is stated with `List.Pairwise List.Disjoint`, the
exact condition consumed by seven-fold BK.
-/
public import PercLib.CriticalLRP.Correlation.FourthMoment.BK

open Set MeasureTheory
open scoped ENNReal
open PercLib.Percolation.Bond
open PercLib.CriticalLRP.TreeExpansion

@[expose] public section

namespace PercLib.CriticalLRP.TreeExpansion.FivePoint

variable {V : Type*}

/-! ### Extracting a pair of entries from `List.Pairwise` -/

theorem pairwise_get_nat {α : Type*} {l : List α} {R : α → α → Prop} (h : l.Pairwise R)
    {i j : ℕ} (hi : i < l.length) (hj : j < l.length) (hij : i < j) :
    R (l.get ⟨i, hi⟩) (l.get ⟨j, hj⟩) :=
  (List.pairwise_iff_get.mp h) ⟨i, hi⟩ ⟨j, hj⟩ (by simpa using hij)

/-! ### The two shape families -/

/-- **Comb shape.**  Seven walks with pairwise disjoint edge lists:
`root → u₁`, `x₁ → u₁`, `u₁ → u₂`, `x₂ → u₂`, `u₂ → u₃`, `x₃ → u₃`, `x₄ → u₃`.
Coincidences `u₁ = u₂`, `u₂ = u₃` (empty spines) are allowed, as in the four-point
`ShapeWitness`; they are the degenerate combs. -/
def CombWitness (G : SimpleGraph V) (root x₁ x₂ x₃ x₄ : V) : Prop :=
  ∃ (u₁ u₂ u₃ : V) (p : G.Walk root u₁) (a₁ : G.Walk x₁ u₁) (s₁ : G.Walk u₁ u₂)
    (a₂ : G.Walk x₂ u₂) (s₂ : G.Walk u₂ u₃) (a₃ : G.Walk x₃ u₃) (a₄ : G.Walk x₄ u₃),
    [p.edges, a₁.edges, s₁.edges, a₂.edges, s₂.edges, a₃.edges, a₄.edges].Pairwise
      List.Disjoint

/-- **Balanced shape.**  Seven walks with pairwise disjoint edge lists:
`root → u`, `u → v`, `x₁ → v`, `x₂ → v`, `u → w`, `x₃ → w`, `x₄ → w`. -/
def BalWitness (G : SimpleGraph V) (root x₁ x₂ x₃ x₄ : V) : Prop :=
  ∃ (u v w : V) (p : G.Walk root u) (s₁ : G.Walk u v) (a₁ : G.Walk x₁ v) (a₂ : G.Walk x₂ v)
    (s₂ : G.Walk u w) (a₃ : G.Walk x₃ w) (a₄ : G.Walk x₄ w),
    [p.edges, s₁.edges, a₁.edges, a₂.edges, s₂.edges, a₃.edges, a₄.edges].Pairwise
      List.Disjoint

/-- **The five-point arm decomposition hypothesis** (`k = 4` of the paper's tree-graph
inequality, deterministic part).  One of the fifteen rooted binary trees with the four
labelled leaves `x₁, x₂, x₃, x₄` below `root` is realised by seven pairwise edge-disjoint
walks.

The twelve combs are indexed by the ordered pair of the two shallow leaves
`(x₁ at u₁, x₂ at u₂)`; the remaining two leaves sit at the common deep branch vertex
`u₃`, whose order is immaterial and fixed here as `(x₃, x₄)`.  The three balanced trees are
indexed by the split of the leaves into two unordered pairs. -/
def Harm5 (G : SimpleGraph V) (root x₁ x₂ x₃ x₄ : V) : Prop :=
  -- twelve combs
  CombWitness G root x₁ x₂ x₃ x₄ ∨ CombWitness G root x₁ x₃ x₂ x₄ ∨
  CombWitness G root x₁ x₄ x₂ x₃ ∨ CombWitness G root x₂ x₁ x₃ x₄ ∨
  CombWitness G root x₂ x₃ x₁ x₄ ∨ CombWitness G root x₂ x₄ x₁ x₃ ∨
  CombWitness G root x₃ x₁ x₂ x₄ ∨ CombWitness G root x₃ x₂ x₁ x₄ ∨
  CombWitness G root x₃ x₄ x₁ x₂ ∨ CombWitness G root x₄ x₁ x₂ x₃ ∨
  CombWitness G root x₄ x₂ x₁ x₃ ∨ CombWitness G root x₄ x₃ x₁ x₂ ∨
  -- three balanced trees
  BalWitness G root x₁ x₂ x₃ x₄ ∨ BalWitness G root x₁ x₃ x₂ x₄ ∨
  BalWitness G root x₁ x₄ x₂ x₃

/-- The configuration-level form of `Harm5`: in every configuration in which the five
vertices are connected, one of the fifteen shapes is certified.  This is the exact
deterministic hypothesis consumed by the measure bounds. -/
def Harm5Event (root x₁ x₂ x₃ x₄ : V) : Set (Config V) :=
  {ω | PercLib.CriticalLRP.Connects ω root x₁ → PercLib.CriticalLRP.Connects ω root x₂ →
        PercLib.CriticalLRP.Connects ω root x₃ → PercLib.CriticalLRP.Connects ω root x₄ →
        Harm5 (PercLib.CriticalLRP.openGraph ω) root x₁ x₂ x₃ x₄}


/-! ### Shape events (seven disjoint finite certificates) -/

/-- The event that the comb shape `(root, x₁, x₂; x₃, x₄)` at branch vertices
`u₁, u₂, u₃` is certified by seven pairwise disjoint finite open sets. -/
def CombEvent (root x₁ x₂ x₃ x₄ u₁ u₂ u₃ : V) : Set (Config V) :=
  {ω | ∃ W₀ W₁ W₂ W₃ W₄ W₅ W₆ : Set (Sym2 V),
    W₀.Finite ∧ W₁.Finite ∧ W₂.Finite ∧ W₃.Finite ∧ W₄.Finite ∧ W₅.Finite ∧ W₆.Finite ∧
    W₀ ⊆ ω ∧ W₁ ⊆ ω ∧ W₂ ⊆ ω ∧ W₃ ⊆ ω ∧ W₄ ⊆ ω ∧ W₅ ⊆ ω ∧ W₆ ⊆ ω ∧
    W₀ ∈ conn root u₁ ∧ W₁ ∈ conn x₁ u₁ ∧ W₂ ∈ conn u₁ u₂ ∧ W₃ ∈ conn x₂ u₂ ∧
    W₄ ∈ conn u₂ u₃ ∧ W₅ ∈ conn x₃ u₃ ∧ W₆ ∈ conn x₄ u₃ ∧
    Disjoint W₀ W₁ ∧ Disjoint W₀ W₂ ∧ Disjoint W₀ W₃ ∧ Disjoint W₀ W₄ ∧
      Disjoint W₀ W₅ ∧ Disjoint W₀ W₆ ∧
    Disjoint W₁ W₂ ∧ Disjoint W₁ W₃ ∧ Disjoint W₁ W₄ ∧ Disjoint W₁ W₅ ∧ Disjoint W₁ W₆ ∧
    Disjoint W₂ W₃ ∧ Disjoint W₂ W₄ ∧ Disjoint W₂ W₅ ∧ Disjoint W₂ W₆ ∧
    Disjoint W₃ W₄ ∧ Disjoint W₃ W₅ ∧ Disjoint W₃ W₆ ∧
    Disjoint W₄ W₅ ∧ Disjoint W₄ W₆ ∧ Disjoint W₅ W₆}

/-- The event that the balanced shape `(root; {x₁,x₂} | {x₃,x₄})` at branch vertices
`u, v, w` is certified by seven pairwise disjoint finite open sets. -/
def BalEvent (root x₁ x₂ x₃ x₄ u v w : V) : Set (Config V) :=
  {ω | ∃ W₀ W₁ W₂ W₃ W₄ W₅ W₆ : Set (Sym2 V),
    W₀.Finite ∧ W₁.Finite ∧ W₂.Finite ∧ W₃.Finite ∧ W₄.Finite ∧ W₅.Finite ∧ W₆.Finite ∧
    W₀ ⊆ ω ∧ W₁ ⊆ ω ∧ W₂ ⊆ ω ∧ W₃ ⊆ ω ∧ W₄ ⊆ ω ∧ W₅ ⊆ ω ∧ W₆ ⊆ ω ∧
    W₀ ∈ conn root u ∧ W₁ ∈ conn u v ∧ W₂ ∈ conn x₁ v ∧ W₃ ∈ conn x₂ v ∧
    W₄ ∈ conn u w ∧ W₅ ∈ conn x₃ w ∧ W₆ ∈ conn x₄ w ∧
    Disjoint W₀ W₁ ∧ Disjoint W₀ W₂ ∧ Disjoint W₀ W₃ ∧ Disjoint W₀ W₄ ∧
      Disjoint W₀ W₅ ∧ Disjoint W₀ W₆ ∧
    Disjoint W₁ W₂ ∧ Disjoint W₁ W₃ ∧ Disjoint W₁ W₄ ∧ Disjoint W₁ W₅ ∧ Disjoint W₁ W₆ ∧
    Disjoint W₂ W₃ ∧ Disjoint W₂ W₄ ∧ Disjoint W₂ W₅ ∧ Disjoint W₂ W₆ ∧
    Disjoint W₃ W₄ ∧ Disjoint W₃ W₅ ∧ Disjoint W₃ W₆ ∧
    Disjoint W₄ W₅ ∧ Disjoint W₄ W₆ ∧ Disjoint W₅ W₆}

/-! ### From walks to certificates -/

theorem combEvent_mem [Countable V] {ω : Config V} {root x₁ x₂ x₃ x₄ : V}
    (h : CombWitness (PercLib.CriticalLRP.openGraph ω) root x₁ x₂ x₃ x₄) :
    ω ∈ ⋃ u₁, ⋃ u₂, ⋃ u₃, CombEvent (V := V) root x₁ x₂ x₃ x₄ u₁ u₂ u₃ := by
  obtain ⟨u₁, u₂, u₃, p, a₁, s₁, a₂, s₂, a₃, a₄, hd⟩ := h
  refine Set.mem_iUnion.mpr ⟨u₁, Set.mem_iUnion.mpr ⟨u₂, Set.mem_iUnion.mpr ⟨u₃, ?_⟩⟩⟩
  have d01 : Disjoint (walkEdges p) (walkEdges a₁) :=
    disjoint_walkEdges _ _ (by simpa using pairwise_get_nat hd (i := 0) (j := 1) (by simp) (by simp) (by simp))
  have d02 : Disjoint (walkEdges p) (walkEdges s₁) :=
    disjoint_walkEdges _ _ (by simpa using pairwise_get_nat hd (i := 0) (j := 2) (by simp) (by simp) (by simp))
  have d03 : Disjoint (walkEdges p) (walkEdges a₂) :=
    disjoint_walkEdges _ _ (by simpa using pairwise_get_nat hd (i := 0) (j := 3) (by simp) (by simp) (by simp))
  have d04 : Disjoint (walkEdges p) (walkEdges s₂) :=
    disjoint_walkEdges _ _ (by simpa using pairwise_get_nat hd (i := 0) (j := 4) (by simp) (by simp) (by simp))
  have d05 : Disjoint (walkEdges p) (walkEdges a₃) :=
    disjoint_walkEdges _ _ (by simpa using pairwise_get_nat hd (i := 0) (j := 5) (by simp) (by simp) (by simp))
  have d06 : Disjoint (walkEdges p) (walkEdges a₄) :=
    disjoint_walkEdges _ _ (by simpa using pairwise_get_nat hd (i := 0) (j := 6) (by simp) (by simp) (by simp))
  have d12 : Disjoint (walkEdges a₁) (walkEdges s₁) :=
    disjoint_walkEdges _ _ (by simpa using pairwise_get_nat hd (i := 1) (j := 2) (by simp) (by simp) (by simp))
  have d13 : Disjoint (walkEdges a₁) (walkEdges a₂) :=
    disjoint_walkEdges _ _ (by simpa using pairwise_get_nat hd (i := 1) (j := 3) (by simp) (by simp) (by simp))
  have d14 : Disjoint (walkEdges a₁) (walkEdges s₂) :=
    disjoint_walkEdges _ _ (by simpa using pairwise_get_nat hd (i := 1) (j := 4) (by simp) (by simp) (by simp))
  have d15 : Disjoint (walkEdges a₁) (walkEdges a₃) :=
    disjoint_walkEdges _ _ (by simpa using pairwise_get_nat hd (i := 1) (j := 5) (by simp) (by simp) (by simp))
  have d16 : Disjoint (walkEdges a₁) (walkEdges a₄) :=
    disjoint_walkEdges _ _ (by simpa using pairwise_get_nat hd (i := 1) (j := 6) (by simp) (by simp) (by simp))
  have d23 : Disjoint (walkEdges s₁) (walkEdges a₂) :=
    disjoint_walkEdges _ _ (by simpa using pairwise_get_nat hd (i := 2) (j := 3) (by simp) (by simp) (by simp))
  have d24 : Disjoint (walkEdges s₁) (walkEdges s₂) :=
    disjoint_walkEdges _ _ (by simpa using pairwise_get_nat hd (i := 2) (j := 4) (by simp) (by simp) (by simp))
  have d25 : Disjoint (walkEdges s₁) (walkEdges a₃) :=
    disjoint_walkEdges _ _ (by simpa using pairwise_get_nat hd (i := 2) (j := 5) (by simp) (by simp) (by simp))
  have d26 : Disjoint (walkEdges s₁) (walkEdges a₄) :=
    disjoint_walkEdges _ _ (by simpa using pairwise_get_nat hd (i := 2) (j := 6) (by simp) (by simp) (by simp))
  have d34 : Disjoint (walkEdges a₂) (walkEdges s₂) :=
    disjoint_walkEdges _ _ (by simpa using pairwise_get_nat hd (i := 3) (j := 4) (by simp) (by simp) (by simp))
  have d35 : Disjoint (walkEdges a₂) (walkEdges a₃) :=
    disjoint_walkEdges _ _ (by simpa using pairwise_get_nat hd (i := 3) (j := 5) (by simp) (by simp) (by simp))
  have d36 : Disjoint (walkEdges a₂) (walkEdges a₄) :=
    disjoint_walkEdges _ _ (by simpa using pairwise_get_nat hd (i := 3) (j := 6) (by simp) (by simp) (by simp))
  have d45 : Disjoint (walkEdges s₂) (walkEdges a₃) :=
    disjoint_walkEdges _ _ (by simpa using pairwise_get_nat hd (i := 4) (j := 5) (by simp) (by simp) (by simp))
  have d46 : Disjoint (walkEdges s₂) (walkEdges a₄) :=
    disjoint_walkEdges _ _ (by simpa using pairwise_get_nat hd (i := 4) (j := 6) (by simp) (by simp) (by simp))
  have d56 : Disjoint (walkEdges a₃) (walkEdges a₄) :=
    disjoint_walkEdges _ _ (by simpa using pairwise_get_nat hd (i := 5) (j := 6) (by simp) (by simp) (by simp))
  refine ⟨walkEdges p, walkEdges a₁, walkEdges s₁, walkEdges a₂,
    walkEdges s₂, walkEdges a₃, walkEdges a₄, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact walkEdges_finite _
  · exact walkEdges_finite _
  · exact walkEdges_finite _
  · exact walkEdges_finite _
  · exact walkEdges_finite _
  · exact walkEdges_finite _
  · exact walkEdges_finite _
  · exact walkEdges_subset _
  · exact walkEdges_subset _
  · exact walkEdges_subset _
  · exact walkEdges_subset _
  · exact walkEdges_subset _
  · exact walkEdges_subset _
  · exact walkEdges_subset _
  · exact mem_conn_walkEdges _
  · exact mem_conn_walkEdges _
  · exact mem_conn_walkEdges _
  · exact mem_conn_walkEdges _
  · exact mem_conn_walkEdges _
  · exact mem_conn_walkEdges _
  · exact mem_conn_walkEdges _
  · exact d01
  · exact d02
  · exact d03
  · exact d04
  · exact d05
  · exact d06
  · exact d12
  · exact d13
  · exact d14
  · exact d15
  · exact d16
  · exact d23
  · exact d24
  · exact d25
  · exact d26
  · exact d34
  · exact d35
  · exact d36
  · exact d45
  · exact d46
  · exact d56

theorem balEvent_mem [Countable V] {ω : Config V} {root x₁ x₂ x₃ x₄ : V}
    (h : BalWitness (PercLib.CriticalLRP.openGraph ω) root x₁ x₂ x₃ x₄) :
    ω ∈ ⋃ u, ⋃ v, ⋃ w, BalEvent (V := V) root x₁ x₂ x₃ x₄ u v w := by
  obtain ⟨u, v, w, p, s₁, a₁, a₂, s₂, a₃, a₄, hd⟩ := h
  refine Set.mem_iUnion.mpr ⟨u, Set.mem_iUnion.mpr ⟨v, Set.mem_iUnion.mpr ⟨w, ?_⟩⟩⟩
  have d01 : Disjoint (walkEdges p) (walkEdges s₁) :=
    disjoint_walkEdges _ _ (by simpa using pairwise_get_nat hd (i := 0) (j := 1) (by simp) (by simp) (by simp))
  have d02 : Disjoint (walkEdges p) (walkEdges a₁) :=
    disjoint_walkEdges _ _ (by simpa using pairwise_get_nat hd (i := 0) (j := 2) (by simp) (by simp) (by simp))
  have d03 : Disjoint (walkEdges p) (walkEdges a₂) :=
    disjoint_walkEdges _ _ (by simpa using pairwise_get_nat hd (i := 0) (j := 3) (by simp) (by simp) (by simp))
  have d04 : Disjoint (walkEdges p) (walkEdges s₂) :=
    disjoint_walkEdges _ _ (by simpa using pairwise_get_nat hd (i := 0) (j := 4) (by simp) (by simp) (by simp))
  have d05 : Disjoint (walkEdges p) (walkEdges a₃) :=
    disjoint_walkEdges _ _ (by simpa using pairwise_get_nat hd (i := 0) (j := 5) (by simp) (by simp) (by simp))
  have d06 : Disjoint (walkEdges p) (walkEdges a₄) :=
    disjoint_walkEdges _ _ (by simpa using pairwise_get_nat hd (i := 0) (j := 6) (by simp) (by simp) (by simp))
  have d12 : Disjoint (walkEdges s₁) (walkEdges a₁) :=
    disjoint_walkEdges _ _ (by simpa using pairwise_get_nat hd (i := 1) (j := 2) (by simp) (by simp) (by simp))
  have d13 : Disjoint (walkEdges s₁) (walkEdges a₂) :=
    disjoint_walkEdges _ _ (by simpa using pairwise_get_nat hd (i := 1) (j := 3) (by simp) (by simp) (by simp))
  have d14 : Disjoint (walkEdges s₁) (walkEdges s₂) :=
    disjoint_walkEdges _ _ (by simpa using pairwise_get_nat hd (i := 1) (j := 4) (by simp) (by simp) (by simp))
  have d15 : Disjoint (walkEdges s₁) (walkEdges a₃) :=
    disjoint_walkEdges _ _ (by simpa using pairwise_get_nat hd (i := 1) (j := 5) (by simp) (by simp) (by simp))
  have d16 : Disjoint (walkEdges s₁) (walkEdges a₄) :=
    disjoint_walkEdges _ _ (by simpa using pairwise_get_nat hd (i := 1) (j := 6) (by simp) (by simp) (by simp))
  have d23 : Disjoint (walkEdges a₁) (walkEdges a₂) :=
    disjoint_walkEdges _ _ (by simpa using pairwise_get_nat hd (i := 2) (j := 3) (by simp) (by simp) (by simp))
  have d24 : Disjoint (walkEdges a₁) (walkEdges s₂) :=
    disjoint_walkEdges _ _ (by simpa using pairwise_get_nat hd (i := 2) (j := 4) (by simp) (by simp) (by simp))
  have d25 : Disjoint (walkEdges a₁) (walkEdges a₃) :=
    disjoint_walkEdges _ _ (by simpa using pairwise_get_nat hd (i := 2) (j := 5) (by simp) (by simp) (by simp))
  have d26 : Disjoint (walkEdges a₁) (walkEdges a₄) :=
    disjoint_walkEdges _ _ (by simpa using pairwise_get_nat hd (i := 2) (j := 6) (by simp) (by simp) (by simp))
  have d34 : Disjoint (walkEdges a₂) (walkEdges s₂) :=
    disjoint_walkEdges _ _ (by simpa using pairwise_get_nat hd (i := 3) (j := 4) (by simp) (by simp) (by simp))
  have d35 : Disjoint (walkEdges a₂) (walkEdges a₃) :=
    disjoint_walkEdges _ _ (by simpa using pairwise_get_nat hd (i := 3) (j := 5) (by simp) (by simp) (by simp))
  have d36 : Disjoint (walkEdges a₂) (walkEdges a₄) :=
    disjoint_walkEdges _ _ (by simpa using pairwise_get_nat hd (i := 3) (j := 6) (by simp) (by simp) (by simp))
  have d45 : Disjoint (walkEdges s₂) (walkEdges a₃) :=
    disjoint_walkEdges _ _ (by simpa using pairwise_get_nat hd (i := 4) (j := 5) (by simp) (by simp) (by simp))
  have d46 : Disjoint (walkEdges s₂) (walkEdges a₄) :=
    disjoint_walkEdges _ _ (by simpa using pairwise_get_nat hd (i := 4) (j := 6) (by simp) (by simp) (by simp))
  have d56 : Disjoint (walkEdges a₃) (walkEdges a₄) :=
    disjoint_walkEdges _ _ (by simpa using pairwise_get_nat hd (i := 5) (j := 6) (by simp) (by simp) (by simp))
  refine ⟨walkEdges p, walkEdges s₁, walkEdges a₁, walkEdges a₂,
    walkEdges s₂, walkEdges a₃, walkEdges a₄, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact walkEdges_finite _
  · exact walkEdges_finite _
  · exact walkEdges_finite _
  · exact walkEdges_finite _
  · exact walkEdges_finite _
  · exact walkEdges_finite _
  · exact walkEdges_finite _
  · exact walkEdges_subset _
  · exact walkEdges_subset _
  · exact walkEdges_subset _
  · exact walkEdges_subset _
  · exact walkEdges_subset _
  · exact walkEdges_subset _
  · exact walkEdges_subset _
  · exact mem_conn_walkEdges _
  · exact mem_conn_walkEdges _
  · exact mem_conn_walkEdges _
  · exact mem_conn_walkEdges _
  · exact mem_conn_walkEdges _
  · exact mem_conn_walkEdges _
  · exact mem_conn_walkEdges _
  · exact d01
  · exact d02
  · exact d03
  · exact d04
  · exact d05
  · exact d06
  · exact d12
  · exact d13
  · exact d14
  · exact d15
  · exact d16
  · exact d23
  · exact d24
  · exact d25
  · exact d26
  · exact d34
  · exact d35
  · exact d36
  · exact d45
  · exact d46
  · exact d56


/-! ### The fifteen seven-factor diagrams -/

/-- The seven-factor diagram associated to one comb labelling. -/
noncomputable def combDiagram (π : Sym2 V → unitInterval) (root x₁ x₂ x₃ x₄ : V) : ℝ≥0∞ :=
  ∑' u₁, ∑' u₂, ∑' u₃,
    tau π root u₁ * tau π x₁ u₁ * tau π u₁ u₂ * tau π x₂ u₂ * tau π u₂ u₃ *
      tau π x₃ u₃ * tau π x₄ u₃

/-- The seven-factor diagram associated to one balanced labelling. -/
noncomputable def balDiagram (π : Sym2 V → unitInterval) (root x₁ x₂ x₃ x₄ : V) : ℝ≥0∞ :=
  ∑' u, ∑' v, ∑' w,
    tau π root u * tau π u v * tau π x₁ v * tau π x₂ v * tau π u w *
      tau π x₃ w * tau π x₄ w

/-- The sum of the twelve comb and three balanced diagrams, in the same order as `Harm5`. -/
noncomputable def fivePointDiagram (π : Sym2 V → unitInterval) (root x₁ x₂ x₃ x₄ : V) : ℝ≥0∞ :=
  combDiagram π root x₁ x₂ x₃ x₄ + combDiagram π root x₁ x₃ x₂ x₄ +
  combDiagram π root x₁ x₄ x₂ x₃ + combDiagram π root x₂ x₁ x₃ x₄ +
  combDiagram π root x₂ x₃ x₁ x₄ + combDiagram π root x₂ x₄ x₁ x₃ +
  combDiagram π root x₃ x₁ x₂ x₄ + combDiagram π root x₃ x₂ x₁ x₄ +
  combDiagram π root x₃ x₄ x₁ x₂ + combDiagram π root x₄ x₁ x₂ x₃ +
  combDiagram π root x₄ x₂ x₁ x₃ + combDiagram π root x₄ x₃ x₁ x₂ +
  balDiagram π root x₁ x₂ x₃ x₄ + balDiagram π root x₁ x₃ x₂ x₄ +
  balDiagram π root x₁ x₄ x₂ x₃

/-! ### Union events for all fifteen tree shapes -/

def combShapeEvent (root x₁ x₂ x₃ x₄ : V) : Set (Config V) :=
  ⋃ u₁, ⋃ u₂, ⋃ u₃, CombEvent (V := V) root x₁ x₂ x₃ x₄ u₁ u₂ u₃

def balShapeEvent (root x₁ x₂ x₃ x₄ : V) : Set (Config V) :=
  ⋃ u, ⋃ v, ⋃ w, BalEvent (V := V) root x₁ x₂ x₃ x₄ u v w

/-- The fifteen events as a finite indexed family, in the same order as `Harm5`. -/
def fivePointShapeEvent (k : Fin 15) (root x₁ x₂ x₃ x₄ : V) : Set (Config V) :=
  ![combShapeEvent root x₁ x₂ x₃ x₄, combShapeEvent root x₁ x₃ x₂ x₄,
    combShapeEvent root x₁ x₄ x₂ x₃, combShapeEvent root x₂ x₁ x₃ x₄,
    combShapeEvent root x₂ x₃ x₁ x₄, combShapeEvent root x₂ x₄ x₁ x₃,
    combShapeEvent root x₃ x₁ x₂ x₄, combShapeEvent root x₃ x₂ x₁ x₄,
    combShapeEvent root x₃ x₄ x₁ x₂, combShapeEvent root x₄ x₁ x₂ x₃,
    combShapeEvent root x₄ x₂ x₁ x₃, combShapeEvent root x₄ x₃ x₁ x₂,
    balShapeEvent root x₁ x₂ x₃ x₄, balShapeEvent root x₁ x₃ x₂ x₄,
    balShapeEvent root x₁ x₄ x₂ x₃] k

/-- The fifteen diagrams as the matching finite indexed family. -/
noncomputable def fivePointIndexedDiagram (π : Sym2 V → unitInterval) (k : Fin 15)
    (root x₁ x₂ x₃ x₄ : V) : ℝ≥0∞ :=
  ![combDiagram π root x₁ x₂ x₃ x₄, combDiagram π root x₁ x₃ x₂ x₄,
    combDiagram π root x₁ x₄ x₂ x₃, combDiagram π root x₂ x₁ x₃ x₄,
    combDiagram π root x₂ x₃ x₁ x₄, combDiagram π root x₂ x₄ x₁ x₃,
    combDiagram π root x₃ x₁ x₂ x₄, combDiagram π root x₃ x₂ x₁ x₄,
    combDiagram π root x₃ x₄ x₁ x₂, combDiagram π root x₄ x₁ x₂ x₃,
    combDiagram π root x₄ x₂ x₁ x₃, combDiagram π root x₄ x₃ x₁ x₂,
    balDiagram π root x₁ x₂ x₃ x₄, balDiagram π root x₁ x₃ x₂ x₄,
    balDiagram π root x₁ x₄ x₂ x₃] k

/-! ### Non-vacuity of the new shape predicates -/

example : CombWitness (⊤ : SimpleGraph PUnit) () () () () () := by
  refine ⟨(), (), (), .nil, .nil, .nil, .nil, .nil, .nil, .nil, ?_⟩
  simp

example : BalWitness (⊤ : SimpleGraph PUnit) () () () () () := by
  refine ⟨(), (), (), .nil, .nil, .nil, .nil, .nil, .nil, .nil, ?_⟩
  simp

example : Harm5 (⊤ : SimpleGraph PUnit) () () () () () := by
  apply Or.inl
  refine ⟨(), (), (), .nil, .nil, .nil, .nil, .nil, .nil, .nil, ?_⟩
  simp



/-! ### The fifteen normalized slot patterns and its four-terminal H shape -/

def pat : Fin 15 → (Fin 5 → Fin 5) :=
  ![![1, 2, 0, 3, 4], ![1, 3, 0, 2, 4], ![1, 4, 0, 2, 3],
    ![0, 2, 1, 3, 4], ![0, 3, 1, 2, 4], ![0, 4, 1, 2, 3],
    ![0, 1, 2, 3, 4], ![0, 3, 2, 1, 4], ![0, 4, 2, 1, 3],
    ![0, 1, 3, 2, 4], ![0, 2, 3, 1, 4], ![0, 4, 3, 1, 2],
    ![0, 1, 4, 2, 3], ![0, 2, 4, 1, 3], ![0, 3, 4, 1, 2]]

/-- The unlabelled slot pattern: two leaves at `u`, one at `v`, two at `w`. -/
def slotPat : Fin 5 → Fin 3 := ![0, 0, 1, 2, 2]

/-- **The comb arm system.**  Seven walks with prescribed endpoints: two leaves at `u`, one leaf
at `v`, two leaves at `w`, and the spine `u — v — w`.  The single hypothesis on the edge lists is
that their concatenation has no repeated edge; equivalently every one of the seven walks is a
trail and the seven edge lists are pairwise disjoint (`CombSlots.nodup` and
`CombSlots.pairwise_disjoint` below recover that form, which is what the BK inequality consumes). -/
def CombSlots (G : SimpleGraph V) (b0 b1 b2 b3 b4 u v w : V) : Prop :=
  ∃ (p0 : G.Walk b0 u) (p1 : G.Walk b1 u) (p2 : G.Walk b2 v)
    (p3 : G.Walk b3 w) (p4 : G.Walk b4 w) (s1 : G.Walk u v) (s2 : G.Walk v w),
    (p0.edges ++ p1.edges ++ p2.edges ++ p3.edges ++ p4.edges ++ s1.edges ++ s2.edges).Nodup

/-- `CombSlots` for the `k`-th labelled comb on the five terminals `T`. -/
def CombShape (G : SimpleGraph V) (k : Fin 15) (u v w : V) (T : Fin 5 → V) : Prop :=
  CombSlots G (T (pat k 0)) (T (pat k 1)) (T (pat k 2)) (T (pat k 3)) (T (pat k 4)) u v w

/-- The seven connection events of the `k`-th labelled comb. -/
def combEvents (k : Fin 15) (u v w : V) (T : Fin 5 → V) : Fin 7 → Set (Config V) :=
  ![conn (T (pat k 0)) u, conn (T (pat k 1)) u, conn (T (pat k 2)) v,
    conn (T (pat k 3)) w, conn (T (pat k 4)) w, conn u v, conn v w]

/-- The seven endpoint pairs of the `k`-th labelled comb, as a `Fin 7`-family. -/
def combPair (k : Fin 15) (u v w : V) (T : Fin 5 → V) : Fin 7 → V × V :=
  ![(T (pat k 0), u), (T (pat k 1), u), (T (pat k 2), v), (T (pat k 3), w), (T (pat k 4), w),
    (u, v), (v, w)]

/-- **The seven-certificate event.**  The event that seven pairwise disjoint finite sets of open
edges certify the seven events `A 0, …, A 6`.  This is the event the BK inequality bounds. -/
def Certs7 (A : Fin 7 → Set (Config V)) : Set (Config V) :=
  {ω | ∃ W : Fin 7 → Set (Sym2 V),
        (∀ j, (W j).Finite) ∧ (∀ j, W j ⊆ ω) ∧ (∀ j, W j ∈ A j) ∧
        (∀ i j, i ≠ j → Disjoint (W i) (W j))}

end FivePoint
end PercLib.CriticalLRP.TreeExpansion

namespace PercLib.CriticalLRP.TreeExpansion
namespace FivePoint

variable {V : Type*}

/-- **The four-terminal binary (H-shaped) arm system.**  Five walks: two leaves `a0, a1` at `u`,
two leaves `a2, a3` at `v`, and the spine `u — v`, with the concatenation of the five edge lists
having no repeated edge.  This is the four-leaf binary tree with `2 * 4 - 3 = 5` edge-disjoint
arms; it is the object the proved third-moment reduction uses (`ShapeWitness`), recorded here in
slot form so that a fifth leaf can be attached to any of its five arms. -/
def Slots4 (G : SimpleGraph V) (a0 a1 a2 a3 u v : V) : Prop :=
  ∃ (p0 : G.Walk a0 u) (p1 : G.Walk a1 u) (p2 : G.Walk a2 v) (p3 : G.Walk a3 v) (s : G.Walk u v),
    (p0.edges ++ p1.edges ++ p2.edges ++ p3.edges ++ s.edges).Nodup

end PercLib.CriticalLRP.TreeExpansion.FivePoint
