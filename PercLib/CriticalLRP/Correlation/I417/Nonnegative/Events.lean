/- Integrated from independently rebuilt Ultramath work, base revision 75f8858d8e30ea17b20f9ff1d216bc1508c01ce2.
Scratch source: ../../.ultramath/smwpwq50m/m1/I417A/Events.lean ; module path rewritten only.
-/

/-
# Hutchcroft Lemma I.4.17, direction A: the labelled connection events

Structural facts about the labelled events `labelEvent x f = {ω | ∀ i, f i ∈ K_x}`:
measurability, monotonicity, finite witnesses, BK, and — the mathematical heart of the
nonnegativity half of Lemma I.4.17 — the fact that two labelled events which hold at a
configuration where `x` is *not* connected to `y` have edge-disjoint witnesses.

The last point is what replaces the printed proof's invalid step `K_y ⊆ K~_y`
(`not_cluster_subset_forceOn_compl` in `Correlation/TwoClusterGap.lean`): no restoration
coupling is used here at all, and no inclusion of clusters is claimed.
-/
module

public import PercLib.CriticalLRP.Correlation.I417.Nonnegative.Defs
public import PercLib.CriticalLRP.Correlation.TwoClusterGap

set_option linter.unusedSectionVars false

@[expose] public section

open MeasureTheory Measure ProbabilityTheory unitInterval
open scoped ENNReal

namespace PercLib.CriticalLRP

namespace I417A

variable {V : Type*} [Countable V]

theorem labelEvent_eq_iInter (x : V) {p : ℕ} (f : Fin p → V) :
    labelEvent x f = ⋂ i, connSet x (f i) := by
  ext ω
  simp only [labelEvent, Set.mem_ofPred_eq, Set.mem_iInter, connSet, mem_cluster_iff]

theorem measurableSet_labelEvent (x : V) {p : ℕ} (f : Fin p → V) :
    MeasurableSet (labelEvent x f) := by
  rw [labelEvent_eq_iInter]
  exact MeasurableSet.iInter fun i => measurableSet_connSet x (f i)

theorem isUpperSet_labelEvent (x : V) {p : ℕ} (f : Fin p → V) :
    IsUpperSet (labelEvent x f) := by
  intro ω ω' hωω' h
  exact fun i => connects_mono hωω' (h i)

/-- A finite witness for `labelEvent x f`: the union of the edges of chosen open walks. -/
theorem finiteWitness_labelEvent (x : V) {p : ℕ} (f : Fin p → V) :
    Percolation.FiniteWitness (labelEvent x f) := by
  classical
  intro ω hω
  have hconn : ∀ i, Connects ω x (f i) := fun i => mem_cluster_iff.mp (hω i)
  choose w hw using fun i => pathConnects_iff.mpr (hconn i)
  refine ⟨Finset.univ.biUnion (fun i => (w i).edges.toFinset), ?_, ?_⟩
  · intro e he
    simp only [Finset.mem_coe, Finset.mem_biUnion, Finset.mem_univ, true_and,
      List.mem_toFinset] at he
    obtain ⟨i, hi⟩ := he
    exact hw i e hi
  · intro i
    refine pathConnects_iff.mp ⟨w i, fun e he => ?_⟩
    simp only [Finset.mem_coe, Finset.mem_biUnion, Finset.mem_univ, true_and,
      List.mem_toFinset]
    exact ⟨i, he⟩

/-- **Disjoint witnesses from non-connection.** If `x` is not connected to `y` but the labelled
events of `x` and of `y` both hold, then those two events occur disjointly: the edge sets of any
open witnesses cannot meet, since a shared edge would put both endpoints in both clusters. -/
theorem labelEvent_disjointOccurrence {ω : Config V} {x y : V} {p q : ℕ}
    (f : Fin p → V) (g : Fin q → V)
    (hf : ω ∈ labelEvent x f) (hg : ω ∈ labelEvent y g)
    (hxy : ¬ Connects ω x y) :
    ω ∈ Percolation.DisjointOccurrence (labelEvent x f) (labelEvent y g) := by
  classical
  have hconnx : ∀ i, Connects ω x (f i) := fun i => mem_cluster_iff.mp (hf i)
  have hconny : ∀ j, Connects ω y (g j) := fun j => mem_cluster_iff.mp (hg j)
  choose wx hwx using fun i => pathConnects_iff.mpr (hconnx i)
  choose wy hwy using fun j => pathConnects_iff.mpr (hconny j)
  refine ⟨Finset.univ.biUnion (fun i => (wx i).edges.toFinset),
    Finset.univ.biUnion (fun j => (wy j).edges.toFinset), ?_, ?_, ?_, ?_, ?_⟩
  · intro e he
    simp only [Finset.mem_coe, Finset.mem_biUnion, Finset.mem_univ, true_and,
      List.mem_toFinset] at he
    obtain ⟨i, hi⟩ := he
    exact hwx i e hi
  · intro e he
    simp only [Finset.mem_coe, Finset.mem_biUnion, Finset.mem_univ, true_and,
      List.mem_toFinset] at he
    obtain ⟨j, hj⟩ := he
    exact hwy j e hj
  · -- disjointness of the two witness sets
    refine Finset.disjoint_left.mpr fun e he he' => ?_
    simp only [Finset.mem_biUnion, Finset.mem_univ, true_and, List.mem_toFinset] at he he'
    obtain ⟨i, hi⟩ := he
    obtain ⟨j, hj⟩ := he'
    induction e using Sym2.ind with
    | _ a b =>
      have hax : a ∈ cluster ω x :=
        mem_cluster_of_mem_support (wx i) (hwx i) a
          (SimpleGraph.Walk.mem_support_iff_exists_mem_edges.mpr
            (Or.inr ⟨s(a, b), hi, Sym2.mem_mk_left a b⟩))
      have hay : a ∈ cluster ω y :=
        mem_cluster_of_mem_support (wy j) (hwy j) a
          (SimpleGraph.Walk.mem_support_iff_exists_mem_edges.mpr
            (Or.inr ⟨s(a, b), hj, Sym2.mem_mk_left a b⟩))
      exact hxy (connects_trans (mem_cluster_iff.mp hax) (connects_symm (mem_cluster_iff.mp hay)))
  · -- the `x`-event holds inside the witness set
    intro i
    refine mem_cluster_iff.mpr (pathConnects_iff.mp ⟨wx i, fun e he => ?_⟩)
    simp only [Finset.mem_coe, Finset.mem_biUnion, Finset.mem_univ, true_and,
      List.mem_toFinset]
    exact ⟨i, he⟩
  · intro j
    refine mem_cluster_iff.mpr (pathConnects_iff.mp ⟨wy j, fun e he => ?_⟩)
    simp only [Finset.mem_coe, Finset.mem_biUnion, Finset.mem_univ, true_and,
      List.mem_toFinset]
    exact ⟨j, he⟩

/-- BK for labelled events, in `ℝ≥0∞` form. -/
theorem bk_labelEvent_ennreal (π : Sym2 V → unitInterval) (hπ : ∀ e, π e < 1)
    (x y : V) {p q : ℕ} (f : Fin p → V) (g : Fin q → V) :
    (edgeMeasure π) (Percolation.DisjointOccurrence (labelEvent x f) (labelEvent y g))
      ≤ (edgeMeasure π) (labelEvent x f) * (edgeMeasure π) (labelEvent y g) := by
  have h := edgeMeasure_bk π hπ (labelEvent x f) (labelEvent y g)
    (isUpperSet_labelEvent x f) (isUpperSet_labelEvent y g)
    (finiteWitness_labelEvent x f) (finiteWitness_labelEvent y g)
  refine (ENNReal.toReal_le_toReal (measure_ne_top _ _)
    (ENNReal.mul_ne_top (measure_ne_top _ _) (measure_ne_top _ _))).mp ?_
  rw [ENNReal.toReal_mul]
  exact h

/-! ## Member and ancestor identities for the concrete `p = 2, q = 1` case -/

/-- Cluster membership is symmetric in the two endpoints. -/
theorem mem_cluster_comm {ω : Config V} {x y : V} :
    y ∈ cluster ω x ↔ x ∈ cluster ω y := by
  rw [mem_cluster_iff, mem_cluster_iff]
  exact ⟨connects_symm, connects_symm⟩

/-- `y ∈ K_x` is exactly the connection event; this is the source's dichotomy, and it is the
`notConnSet` that the exact expansion uses. -/
theorem notConnSet_eq (x y : V) :
    notConnSet x y = {ω : Config V | y ∉ cluster ω x} := by
  ext ω
  simp only [notConnSet, Set.mem_ofPred_eq, mem_cluster_iff]

/-- The exact deficit summand in the source's language: `f i ∈ K_x` for all `i`, `g j ∈ K_y`
for all `j`, and `y ∉ K_x`. -/
theorem deficitEvent_eq (x y : V) {p q : ℕ} (f : Fin p → V) (g : Fin q → V) :
    deficitEvent x y f g = labelEvent x f ∩ labelEvent y g ∩ {ω : Config V | y ∉ cluster ω x} := by
  rw [deficitEvent, notConnSet_eq]

/-- The trivial labelled event `(x, …, x)` holds at every configuration: a cluster contains
its root. -/
theorem mem_labelEvent_self (x : V) (p : ℕ) (ω : Config V) :
    ω ∈ labelEvent (V := V) x (fun _ : Fin p => x) := by
  intro i
  exact cluster_mem_self ω x

/-- The constant labelled event `(x, …, x)` is the whole space. -/
theorem labelEvent_const_eq_univ (x : V) (p : ℕ) :
    labelEvent (V := V) x (fun _ : Fin p => x) = Set.univ := by
  ext ω
  simp only [labelEvent, Set.mem_ofPred_eq, Set.mem_univ, iff_true]
  intro i
  exact cluster_mem_self ω x

/-- Its probability is `1`. -/
theorem measure_labelEvent_const (π : Sym2 V → unitInterval) (x : V) (p : ℕ) :
    (edgeMeasure π) (labelEvent (V := V) x (fun _ : Fin p => x)) = 1 := by
  rw [labelEvent_const_eq_univ]
  exact measure_univ

/-- **The trivial labelling contributes exactly the non-connection event.**  For the constant
labellings `f ≡ x`, `g ≡ y` the exact deficit summand is `{x ↮ y}`: this is the source's
`y ∈ K_x` term, and its BK bound is `μ(A_f)·μ(B_g) = 1`. -/
theorem deficitEvent_const (x y : V) (p q : ℕ) :
    deficitEvent (V := V) x y (fun _ : Fin p => x) (fun _ : Fin q => y) = notConnSet x y := by
  rw [deficitEvent, labelEvent_const_eq_univ x p, labelEvent_const_eq_univ y q]
  simp

/-- The `p = 1, q = 1` case of `deficitEvent_const`. -/
theorem deficitEvent_trivial (x y : V) :
    deficitEvent (V := V) x y (fun _ : Fin 1 => x) (fun _ : Fin 1 => y) = notConnSet x y :=
  deficitEvent_const x y 1 1

/-- Clusters of two non-connected vertices are disjoint. -/
theorem cluster_disjoint_of_notConn {ω : Config V} {x y : V} (h : ¬ Connects ω x y) :
    Disjoint (cluster ω x) (cluster ω y) := by
  rw [Set.disjoint_left]
  intro v hvx hvy
  exact h (connects_trans (mem_cluster_iff.mp hvx) (connects_symm (mem_cluster_iff.mp hvy)))

/-- On the connection event the two clusters coincide, so the cluster cardinals agree. -/
theorem cardFun_cluster_eq_of_conn {ω : Config V} {x y : V} (h : Connects ω x y) :
    Percolation.cardFun (cluster ω x) = Percolation.cardFun (cluster ω y) := by
  rw [cluster_eq_iff.mpr h]

/-- On the connection event the mixed cluster monomial collapses to a pure power. -/
theorem cardFun_pow_mul_eq_of_conn {ω : Config V} {x y : V} (h : Connects ω x y) (p q : ℕ) :
    Percolation.cardFun (cluster ω x) ^ p * Percolation.cardFun (cluster ω y) ^ q =
      Percolation.cardFun (cluster ω x) ^ (p + q) := by
  rw [cardFun_cluster_eq_of_conn h, ← pow_add]

/-- There is a configuration joining any two vertices. -/
theorem exists_connects (x y : V) : ∃ ω : Config V, Connects ω x y := by
  refine ⟨Set.univ, ?_⟩
  rcases eq_or_ne x y with rfl | hne
  · exact SimpleGraph.Reachable.refl x
  · rw [Connects, SimpleGraph.reachable_iff_reflTransGen]
    exact Relation.ReflTransGen.single (by
      rw [openGraph_adj]
      exact ⟨hne, Set.mem_univ _⟩)

/-- **The printed intermediate event is strictly larger than the exact one.**  The labelled
events of `x` and of `y` do *not* force non-connection, so `labelEvent x f ∩ labelEvent y g`
alone cannot be the deficit summand; the factor `1(x ↮ y)` is genuinely needed.  This is why
the exact expansion (`deficitEvent`) keeps `notConnSet` explicitly. -/
theorem not_labelEvent_subset_notConn (x y : V) :
    ¬ (labelEvent (V := V) x (fun _ : Fin 1 => x) ⊆ notConnSet x y) := by
  intro hsub
  obtain ⟨ω, hc⟩ := exists_connects (V := V) x y
  exact hsub (mem_labelEvent_self x 1 ω) hc

end I417A

end PercLib.CriticalLRP
