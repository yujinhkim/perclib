/-
Copyright (c) 2026 PercLib contributors. Released under Apache 2.0.

# Deterministic BFS partitions, cluster exhaustion and queried-edge geometry.

Accepted from independent submission `smwpalb9h` direction D2.
No generation-moment induction or cluster-moment finiteness is asserted here.
-/
module

/-
Private swarm module (member m2, swarm smwpalb9h), direction 2.

Deterministic invariants of the frontier exploration on the repository's actual
`Config (Sym2 V)` / `cluster`, with no finiteness or degree hypothesis.
-/
public import PercLib.CriticalLRP.Exploration.BFS.Defs

set_option autoImplicit false


@[expose] public section

noncomputable section

open MeasureTheory Set PercLib.Percolation.Bond
open scoped ENNReal BigOperators

namespace PercLib.CriticalLRP.Exploration.BFS

variable {V : Type*}

/-! ### The partition `P k ⊔ A k ⊔ U k = univ` -/

theorem partition_aux (ω : Config V) (o : V) (k : ℕ) :
    Disjoint (P ω o k) (A ω o k) ∧ Disjoint (P ω o k) (U ω o k) ∧
      Disjoint (A ω o k) (U ω o k) ∧ P ω o k ∪ A ω o k ∪ U ω o k = univ := by
  induction k with
  | zero =>
      refine ⟨?_, ?_, ?_, ?_⟩ <;>
        simp [P_zero, A_zero, U_zero, Set.disjoint_left]
  | succ k ih =>
      obtain ⟨hPA, hPU, hAU, hunion⟩ := ih
      have hA'U : A ω o (k + 1) ⊆ U ω o k := gen_subset_U ω o k
      refine ⟨?_, ?_, ?_, ?_⟩
      · rw [Set.disjoint_left]
        intro x hx hx'
        rw [P_succ] at hx
        rcases hx with hx | hx
        · exact (Set.disjoint_left.mp hPU hx) (hA'U hx')
        · exact (Set.disjoint_left.mp hAU hx) (hA'U hx')
      · rw [Set.disjoint_left]
        intro x hx hx'
        rw [P_succ] at hx
        rw [U_succ] at hx'
        rcases hx with hx | hx
        · exact (Set.disjoint_left.mp hPU hx) hx'.1
        · exact (Set.disjoint_left.mp hAU hx) hx'.1
      · rw [Set.disjoint_left]
        intro x hx hx'
        rw [U_succ] at hx'
        exact hx'.2 hx
      · rw [P_succ, U_succ, Set.union_assoc, Set.union_sdiff_cancel hA'U, ← hunion]

theorem disjoint_P_A (ω : Config V) (o : V) (k : ℕ) :
    Disjoint (P ω o k) (A ω o k) := (partition_aux ω o k).1

theorem disjoint_P_U (ω : Config V) (o : V) (k : ℕ) :
    Disjoint (P ω o k) (U ω o k) := (partition_aux ω o k).2.1

theorem disjoint_A_U (ω : Config V) (o : V) (k : ℕ) :
    Disjoint (A ω o k) (U ω o k) := (partition_aux ω o k).2.2.1

theorem union_state (ω : Config V) (o : V) (k : ℕ) :
    P ω o k ∪ A ω o k ∪ U ω o k = univ := (partition_aux ω o k).2.2.2

theorem not_mem_U_of_mem_P {ω : Config V} {o x : V} {k : ℕ} (h : x ∈ P ω o k) :
    x ∉ U ω o k :=
  Set.disjoint_left.mp (disjoint_P_U ω o k) h

theorem not_mem_U_of_mem_A {ω : Config V} {o x : V} {k : ℕ} (h : x ∈ A ω o k) :
    x ∉ U ω o k :=
  Set.disjoint_left.mp (disjoint_A_U ω o k) h

theorem not_mem_A_of_mem_P {ω : Config V} {o x : V} {k : ℕ} (h : x ∈ P ω o k) :
    x ∉ A ω o k :=
  Set.disjoint_left.mp (disjoint_P_A ω o k) h

theorem mem_U_of_not_mem_P_of_not_mem_A {ω : Config V} {o x : V} {k : ℕ}
    (hP : x ∉ P ω o k) (hA : x ∉ A ω o k) : x ∈ U ω o k := by
  have h : x ∈ P ω o k ∪ A ω o k ∪ U ω o k := by rw [union_state]; exact Set.mem_univ x
  simpa [hP, hA] using h

theorem U_eq_compl (ω : Config V) (o : V) (k : ℕ) :
    U ω o k = (P ω o k ∪ A ω o k)ᶜ := by
  ext x
  constructor
  · intro hx h
    rcases h with hP | hA
    · exact (not_mem_U_of_mem_P hP) hx
    · exact (not_mem_U_of_mem_A hA) hx
  · intro hx
    exact mem_U_of_not_mem_P_of_not_mem_A (fun h => hx (Or.inl h)) (fun h => hx (Or.inr h))

/-! ### Monotonicity and the identification `P k = ⋃_{j<k} A j` -/

theorem P_subset_succ (ω : Config V) (o : V) (k : ℕ) : P ω o k ⊆ P ω o (k + 1) := by
  rw [P_succ]; exact Set.subset_union_left

theorem P_mono (ω : Config V) (o : V) {i j : ℕ} (h : i ≤ j) : P ω o i ⊆ P ω o j := by
  induction h with
  | refl => exact subset_rfl
  | step _ ih => exact ih.trans (P_subset_succ ω o _)

theorem U_succ_subset (ω : Config V) (o : V) (k : ℕ) : U ω o (k + 1) ⊆ U ω o k := by
  rw [U_succ]; exact Set.sdiff_subset

theorem A_subset_P_succ (ω : Config V) (o : V) (k : ℕ) : A ω o k ⊆ P ω o (k + 1) := by
  rw [P_succ]; exact Set.subset_union_right

theorem P_succ_sdiff (ω : Config V) (o : V) (k : ℕ) :
    P ω o (k + 1) \ P ω o k = A ω o k := by
  rw [P_succ]
  ext x
  constructor
  · rintro ⟨hx | hx, hx'⟩
    · exact absurd hx hx'
    · exact hx
  · intro hx
    exact ⟨Or.inr hx, fun h => (not_mem_A_of_mem_P h) hx⟩

theorem P_eq_iUnion (ω : Config V) (o : V) (k : ℕ) :
    P ω o k = ⋃ j : {j : ℕ // j < k}, A ω o j := by
  induction k with
  | zero =>
      rw [P_zero]
      symm
      apply Set.eq_empty_iff_forall_notMem.mpr
      intro x hx
      obtain ⟨j, -⟩ := Set.mem_iUnion.mp hx
      exact Nat.not_lt_zero j.1 j.2
  | succ k ih =>
      rw [P_succ, ih]
      ext x
      constructor
      · rintro (hx | hx)
        · obtain ⟨j, hj⟩ := Set.mem_iUnion.mp hx
          exact Set.mem_iUnion.mpr ⟨⟨j.1, Nat.lt_trans j.2 (Nat.lt_succ_self k)⟩, hj⟩
        · exact Set.mem_iUnion.mpr ⟨⟨k, Nat.lt_succ_self k⟩, hx⟩
      · intro hx
        obtain ⟨j, hj⟩ := Set.mem_iUnion.mp hx
        rcases Nat.lt_succ_iff_lt_or_eq.mp j.2 with h | h
        · exact Or.inl (Set.mem_iUnion.mpr ⟨⟨j.1, h⟩, hj⟩)
        · exact Or.inr (by simpa [h] using hj)

theorem A_subset_P_of_lt {ω : Config V} {o : V} {j k : ℕ} (h : j < k) :
    A ω o j ⊆ P ω o k := by
  rw [P_eq_iUnion]
  intro x hx
  exact Set.mem_iUnion.mpr ⟨⟨j, h⟩, hx⟩

/-- Generations are pairwise disjoint. -/
theorem pairwiseDisjoint_A (ω : Config V) (o : V) :
    Pairwise (fun i j => Disjoint (A ω o i) (A ω o j)) := by
  intro i j hij
  rcases lt_or_gt_of_ne hij with hlt | hgt
  · rw [Set.disjoint_left]
    intro x hxi hxj
    exact (not_mem_A_of_mem_P (A_subset_P_of_lt hlt hxi)) hxj
  · rw [Set.disjoint_left]
    intro x hxi hxj
    exact (not_mem_A_of_mem_P (A_subset_P_of_lt hgt hxj)) hxi

/-! ### The exploration exhausts the cluster -/

/-- Every generation consists of vertices reachable from the root. -/
theorem A_subset_cluster (ω : Config V) (o : V) (k : ℕ) : A ω o k ⊆ cluster ω o := by
  induction k with
  | zero =>
      intro y hy
      rw [A_zero] at hy
      rw [Set.mem_singleton_iff] at hy
      rw [hy]
      exact PercLib.Percolation.Bond.mem_cluster_self ω o
  | succ k ih =>
      rw [A_succ]
      rintro y ⟨hyU, x, hxA, hxy⟩
      have hxne : x ≠ y := by
        intro h
        exact (not_mem_U_of_mem_A (h ▸ hxA)) hyU
      exact (ih hxA).trans ((mem_cluster_iff ω x y).mpr (mem_conn_of_mem hxne hxy))

/-- The union of all generations is closed under open edges. -/
theorem mem_iUnion_A_of_mem_of_mem {ω : Config V} {o : V} {x y : V}
    (hx : x ∈ ⋃ k, A ω o k) (hxy : s(x, y) ∈ ω) :
    y ∈ ⋃ k, A ω o k := by
  rw [Set.mem_iUnion] at hx ⊢
  obtain ⟨k, hk⟩ := hx
  by_cases hyU : y ∈ U ω o k
  · exact ⟨k + 1, by rw [A_succ]; exact ⟨hyU, x, hk, hxy⟩⟩
  · have hy : y ∈ P ω o k ∪ A ω o k := by
      have h : y ∈ P ω o k ∪ A ω o k ∪ U ω o k := by rw [union_state]; exact Set.mem_univ y
      simpa [hyU] using h
    rcases hy with hyP | hyA
    · rw [P_eq_iUnion] at hyP
      obtain ⟨j, hj⟩ := Set.mem_iUnion.mp hyP
      exact ⟨j.1, hj⟩
    · exact ⟨k, hyA⟩

/-- The root cluster is exactly the union of all generations. -/
theorem cluster_eq_iUnion_A (ω : Config V) (o : V) :
    cluster ω o = ⋃ k, A ω o k := by
  apply le_antisymm
  · intro y hy
    rw [PercLib.Percolation.Bond.mem_cluster_iff] at hy
    change (openGraph ω).Reachable o y at hy
    rw [SimpleGraph.reachable_iff_reflTransGen] at hy
    induction hy with
    | refl => exact Set.mem_iUnion.mpr ⟨0, by rw [A_zero]; exact rfl⟩
    | tail _ hr ih =>
        rw [openGraph_adj_iff] at hr
        exact mem_iUnion_A_of_mem_of_mem ih hr.1
  · intro y hy
    rw [Set.mem_iUnion] at hy
    obtain ⟨k, hk⟩ := hy
    exact A_subset_cluster ω o k hk

/-! ### Edges: queried set `E(A k, U k)`, revealed set `R k` -/

/-- The edge map `(x,y) ↦ s(x,y)` is injective on `A × U` when `A` and `U` are disjoint. -/
theorem edgeMap_injOn {A U : Set V} (h : Disjoint A U) :
    InjOn (fun p : V × V => s(p.1, p.2)) (A ×ˢ U) := by
  rintro ⟨x, y⟩ hx ⟨x', y'⟩ hx' heq
  simp only [Set.mem_prod] at hx hx'
  obtain ⟨hxA, hyU⟩ := hx
  obtain ⟨hx'A, hy'U⟩ := hx'
  rcases Sym2.eq_iff.mp heq with ⟨hxx', hyy'⟩ | ⟨hxy', -⟩
  · exact Prod.ext hxx' hyy'
  · have hxy'' : x = y' := hxy'
    exact ((Set.disjoint_left.mp h (hxy'' ▸ hxA)) hy'U).elim

theorem edgeSet_eq_image (A U : Set V) :
    edgeSet A U = (fun p : V × V => s(p.1, p.2)) '' (A ×ˢ U) := by
  ext e
  constructor
  · rintro ⟨x, hx, y, hy, rfl⟩
    exact ⟨(x, y), ⟨hx, hy⟩, rfl⟩
  · rintro ⟨⟨x, y⟩, ⟨hx, hy⟩, rfl⟩
    exact ⟨x, hx, y, hy, rfl⟩

theorem queried_encard_eq (ω : Config V) (o : V) (k : ℕ) :
    (queried ω o k).encard = (A ω o k ×ˢ U ω o k).encard := by
  rw [queried, edgeSet_eq_image]
  exact (edgeMap_injOn (disjoint_A_U ω o k)).encard_image

/-- Each newly discovered vertex yields a distinct open edge of the queried set:
the generation is dominated by the open edges of `E(A k, U k)`. -/
theorem gen_encard_le_queried (ω : Config V) (o : V) (k : ℕ) :
    (gen ω o k).encard ≤ (queried ω o k ∩ ω).encard := by
  classical
  let par : gen ω o k → V := fun y => Classical.choose y.2.2
  have hpar_mem : ∀ y : gen ω o k, par y ∈ A ω o k :=
    fun y => (Classical.choose_spec y.2.2).1
  have hpar_edge : ∀ y : gen ω o k, s(par y, y.1) ∈ ω :=
    fun y => (Classical.choose_spec y.2.2).2
  have hinj : Function.Injective (fun y : gen ω o k => s(par y, y.1)) := by
    intro y y' heq
    have hpair : (par y, y.1) = (par y', y'.1) :=
      edgeMap_injOn (disjoint_A_U ω o k)
        ⟨hpar_mem y, gen_subset_U ω o k y.2⟩
        ⟨hpar_mem y', gen_subset_U ω o k y'.2⟩ heq
    exact Subtype.ext (Prod.mk.injEq .. ▸ hpair).2
  have himg : (fun y : gen ω o k => s(par y, y.1)) '' univ ⊆ queried ω o k ∩ ω := by
    rintro e ⟨y, -, rfl⟩
    exact ⟨⟨par y, hpar_mem y, y.1, gen_subset_U ω o k y.2, rfl⟩, hpar_edge y⟩
  calc (gen ω o k).encard = (univ : Set (gen ω o k)).encard := by simp
    _ = ((fun y : gen ω o k => s(par y, y.1)) '' univ).encard :=
        hinj.injOn.encard_image.symm
    _ ≤ (queried ω o k ∩ ω).encard := Set.encard_mono himg

/-- Edge sets of distinct frontier vertices are disjoint: the row-sum budget of
`E(A k, U k)` is spent once per frontier vertex. -/
theorem disjoint_edgeSet_singleton {A U : Set V} (h : Disjoint A U) {x x' : V}
    (hx : x ∈ A) (hx' : x' ∈ A) (hne : x ≠ x') :
    Disjoint (edgeSet {x} U) (edgeSet {x'} U) := by
  rw [Set.disjoint_left]
  rintro e ⟨x₀, hx₀, y, hyU, rfl⟩ ⟨x₁, hx₁, y', hy'U, heq⟩
  simp only [Set.mem_singleton_iff] at hx₀ hx₁
  subst hx₀
  subst hx₁
  rcases Sym2.eq_iff.mp heq with ⟨rfl, -⟩ | ⟨hxy', -⟩
  · exact hne rfl
  · exact (Set.disjoint_left.mp h hx) (hxy'.symm ▸ hy'U)

/-- The revealed set `R k` contains no edge of the currently queried set. -/
theorem disjoint_revealed_queried (ω : Config V) (o : V) (k : ℕ) :
    Disjoint (revealed ω o k) (queried ω o k) := by
  rw [Set.disjoint_left]
  rintro e ⟨v, hvP, hve⟩ ⟨x, hxA, y, hyU, rfl⟩
  rw [Sym2.mem_iff] at hve
  rcases hve with hvx | hvy
  · exact (not_mem_A_of_mem_P (hvx ▸ hvP)) hxA
  · exact (not_mem_U_of_mem_P (hvy ▸ hvP)) hyU

theorem revealed_mono (ω : Config V) (o : V) {i j : ℕ} (h : i ≤ j) :
    revealed ω o i ⊆ revealed ω o j := by
  rintro e ⟨v, hv, hve⟩
  exact ⟨v, P_mono ω o h hv, hve⟩

theorem queried_subset_revealed_succ (ω : Config V) (o : V) (k : ℕ) :
    queried ω o k ⊆ revealed ω o (k + 1) := by
  rintro e ⟨x, hxA, y, -, rfl⟩
  exact ⟨x, A_subset_P_succ ω o k hxA, by simp⟩

theorem seen_subset_revealed (ω : Config V) (o : V) (k : ℕ) :
    seen ω o k ⊆ revealed ω o k := by
  intro e he
  rw [seen, Set.mem_iUnion] at he
  obtain ⟨j, hje⟩ := he
  exact revealed_mono ω o (Nat.succ_le_of_lt j.2) (queried_subset_revealed_succ ω o j.1 hje)

theorem seen_mono (ω : Config V) (o : V) {i j : ℕ} (h : i ≤ j) :
    seen ω o i ⊆ seen ω o j := by
  intro e he
  rw [seen, Set.mem_iUnion] at he ⊢
  obtain ⟨k, hke⟩ := he
  exact ⟨⟨k.1, Nat.lt_of_lt_of_le k.2 h⟩, hke⟩



/-! ### The cluster as the root together with disjoint generations -/

theorem pairwiseDisjoint_gen (ω : Config V) (o : V) :
    Pairwise (fun i j => Disjoint (gen ω o i) (gen ω o j)) := by
  intro i j hij
  exact pairwiseDisjoint_A ω o (by omega)

theorem disjoint_singleton_iUnion_gen (ω : Config V) (o : V) :
    Disjoint ({o} : Set V) (⋃ k, gen ω o k) := by
  rw [Set.disjoint_left]
  intro x hx hy
  rw [Set.mem_singleton_iff] at hx
  rw [hx] at hy
  rw [Set.mem_iUnion] at hy
  obtain ⟨k, hk⟩ := hy
  have hoP : o ∈ P ω o (k + 1) := by
    have hoA : o ∈ A ω o 0 := by simp
    exact P_mono ω o (Nat.succ_le_succ (Nat.zero_le k)) (A_subset_P_succ ω o 0 hoA)
  exact not_mem_A_of_mem_P hoP hk

/-- **The exploration exhausts the cluster**: the root together with the
disjoint generations `G (k+1) = A (k+1)` is exactly the root cluster. -/
theorem cluster_eq_insert_iUnion_gen (ω : Config V) (o : V) :
    cluster ω o = insert o (⋃ k, gen ω o k) := by
  rw [cluster_eq_iUnion_A]
  ext x
  constructor
  · intro hx
    rw [Set.mem_iUnion] at hx
    obtain ⟨k, hk⟩ := hx
    rcases k with _ | k
    · exact Or.inl hk
    · exact Or.inr (Set.mem_iUnion.mpr ⟨k, hk⟩)
  · rintro (hx | hx)
    · exact Set.mem_iUnion.mpr ⟨0, by simpa using hx⟩
    · obtain ⟨k, hk⟩ := Set.mem_iUnion.mp hx
      exact Set.mem_iUnion.mpr ⟨k + 1, hk⟩

/-- Each newly discovered vertex carries an open edge of `E(A_k,U_k)` which is
not in the revealed set `R_k`. -/
theorem exists_unrevealed_edge_of_mem_gen (ω : Config V) (o : V) (k : ℕ) {y : V}
    (hy : y ∈ gen ω o k) :
    ∃ x ∈ A ω o k, s(x, y) ∈ ω ∧ s(x, y) ∈ queried ω o k ∧
      s(x, y) ∉ revealed ω o k := by
  obtain ⟨hyU, x, hxA, hxy⟩ := hy
  refine ⟨x, hxA, hxy, ⟨x, hxA, y, hyU, rfl⟩, ?_⟩
  intro h
  exact (Set.disjoint_left.mp (disjoint_revealed_queried ω o k) h) ⟨x, hxA, y, hyU, rfl⟩

/-- The newly discovered vertices of one generation can be assigned pairwise
distinct open edges of `E(A_k,U_k)`, all outside the revealed set `R_k`. -/
theorem exists_injective_unrevealed_edge (ω : Config V) (o : V) (k : ℕ) :
    ∃ f : gen ω o k → Sym2 V, Function.Injective f ∧
      (∀ y, f y ∈ queried ω o k ∩ ω) ∧ (∀ y, f y ∉ revealed ω o k) := by
  classical
  let par : gen ω o k → V := fun y => Classical.choose y.2.2
  have hmem : ∀ y : gen ω o k, par y ∈ A ω o k :=
    fun y => (Classical.choose_spec y.2.2).1
  have hedge : ∀ y : gen ω o k, s(par y, y.1) ∈ ω :=
    fun y => (Classical.choose_spec y.2.2).2
  refine ⟨fun y => s(par y, y.1), ?_, ?_, ?_⟩
  · intro y y' heq
    have hpair : (par y, y.1) = (par y', y'.1) :=
      edgeMap_injOn (disjoint_A_U ω o k)
        ⟨hmem y, gen_subset_U ω o k y.2⟩
        ⟨hmem y', gen_subset_U ω o k y'.2⟩ heq
    exact Subtype.ext (Prod.mk.injEq .. ▸ hpair).2
  · intro y
    exact ⟨⟨par y, hmem y, y.1, gen_subset_U ω o k y.2, rfl⟩, hedge y⟩
  · intro y h
    exact (Set.disjoint_left.mp (disjoint_revealed_queried ω o k) h)
      ⟨par y, hmem y, y.1, gen_subset_U ω o k y.2, rfl⟩

end PercLib.CriticalLRP.Exploration.BFS
