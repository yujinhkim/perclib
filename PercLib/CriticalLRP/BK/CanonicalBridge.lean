/-
Migration source: https://github.com/yujinhkim/Critical-Long-range-percolation
Integration revision: 3b3d1d0e43ef940bfaa2292ee5c2ee094ac4edbf
Licence: Apache-2.0 for the PercLib Lean sources and tooling; see third_party/critical-lrp/.
External provenance and modifications are recorded in the file-specific notices below.
-/

/-
# Bridging the general edge-Bernoulli BK law to the canonical countable model

Source: Tom Hutchcroft, *Critical long-range percolation I: High effective dimension*,
arXiv:2508.18807v1, §I.2.1 (Harris--FKG, BK, Lemma I.2.1, Lemma I.2.2) and §I.1.2 (the law `P_β`).

The repository has two descriptions of the same probability space:

* `PercLib.CriticalLRP.Config V = Set (Sym2 V)` with `edgeMeasure π`, the *canonical* countable
  model of §I.1.2 used by every later section (`cluster`, `clusterVol`, `InInfiniteCluster`, ...);
* `PercLib.CriticalLRP.Percolation.BondGraph V E` with the general edge-dependent Bernoulli law
  `edgeLaw p` on `Set E`, where the BK inequality `bkEdge`, FKG `association_edge_finiteWitness`
  and their graph consequences `twoCluster_bk`, `threePoint_bk`, `bk_list` are proved.

This file transports those results to the canonical model, so that all of §I.3--§I.5 can cite BK
in the form in which it is actually applied.  Nothing here is new mathematics; the content is the
exact interface (`edgeMeasure = edgeLaw`, the identity bond graph, `Conn ↔ Connects`) together with
the discharge of the hypothesis `p e < 1` for the paper's law `P_β`.

No `sorry`, no custom axioms.
-/
module

public import PercLib.CriticalLRP.BK.GraphConsequences
public import PercLib.CriticalLRP.CountableProduct.Lattice
public import PercLib.CriticalLRP.CountableProduct.Marks

set_option autoImplicit true

set_option linter.unusedSectionVars false

@[expose] public section

open MeasureTheory Measure ProbabilityTheory unitInterval
open scoped ENNReal

namespace PercLib.CriticalLRP

/-! ## The law -/

variable {V : Type*} [Countable V]

/-- **The canonical model is the general edge-Bernoulli law.**  `edgeMeasure π` (§I.1.2, the
independent-edge product measure on `Sym2 V → Prop`) is definitionally the edge-dependent
Bernoulli product law `Percolation.edgeLaw π` on which BK and Harris--FKG are proved. -/
theorem edgeMeasure_eq_edgeLaw (π : Sym2 V → unitInterval) :
    edgeMeasure π = Percolation.edgeLaw π := by
  rw [Percolation.edgeLaw_eq_infinitePi, edgeMeasure_eq_infinitePi]

/-- Translation of an event through the law identity. -/
theorem edgeMeasure_real_eq_edgeLaw (π : Sym2 V → unitInterval) (A : Set (Config V)) :
    (edgeMeasure π).real A = (Percolation.edgeLaw π).real A := by
  rw [edgeMeasure_eq_edgeLaw]

/-! ## BK and Harris--FKG on the canonical model -/

/-- **BK inequality on the canonical model** (§I.2.1): for increasing events with finite
witnesses, `P(A ∘ B) ≤ P(A) P(B)`. -/
theorem edgeMeasure_bk (π : Sym2 V → unitInterval) (hπ : ∀ e, π e < 1)
    (A B : Set (Config V)) (hA : IsUpperSet A) (hB : IsUpperSet B)
    (hfA : Percolation.FiniteWitness A) (hfB : Percolation.FiniteWitness B) :
    (edgeMeasure π).real (Percolation.DisjointOccurrence A B) ≤
      (edgeMeasure π).real A * (edgeMeasure π).real B := by
  rw [edgeMeasure_eq_edgeLaw]
  exact Percolation.bkEdge π hπ A B hA hB hfA hfB

/-- **Harris--FKG on the canonical model** (§I.2.1): increasing events are non-negatively
correlated. -/
theorem edgeMeasure_fkg (π : Sym2 V → unitInterval)
    (A B : Set (Config V)) (hA : IsUpperSet A) (hB : IsUpperSet B)
    (hfA : Percolation.FiniteWitness A) (hfB : Percolation.FiniteWitness B) :
    (edgeMeasure π).real A * (edgeMeasure π).real B ≤
      (edgeMeasure π).real (A ∩ B) := by
  rw [edgeMeasure_eq_edgeLaw]
  exact Percolation.association_edge_finiteWitness π A B hA hB hfA hfB

/-- **Iterated BK on the canonical model**: `P(A₁ ∘ ⋯ ∘ A_k) ≤ ∏ P(Aᵢ)`. -/
theorem edgeMeasure_bk_list (π : Sym2 V → unitInterval) (hπ : ∀ e, π e < 1)
    (As : List (Set (Config V)))
    (hA : ∀ A ∈ As, IsUpperSet A) (hf : ∀ A ∈ As, Percolation.FiniteWitness A) :
    (edgeMeasure π).real (Percolation.DisjointOccurrenceList As) ≤
      (As.map (fun A => (edgeMeasure π).real A)).prod := by
  rw [edgeMeasure_eq_edgeLaw]
  exact Percolation.bk_list π hπ As hA hf

/-! ## The identity bond graph: `Conn` is `Connects` -/

/-- The canonical model as a general bond graph: every unordered pair of vertices is its own
edge.  The diagonal pair is a self-loop, which does not affect connectivity. -/
def idBondGraph (V : Type*) : Percolation.BondGraph V (Sym2 V) := id

/-- **`Conn` in the identity bond graph is `Connects` in the open subgraph.** -/
theorem conn_idBondGraph_iff (ω : Config V) (x y : V) :
    Percolation.Conn (idBondGraph V) ω x y ↔ Connects ω x y := by
  rw [Connects, SimpleGraph.reachable_iff_reflTransGen]
  constructor
  · intro h
    induction h with
    | refl => exact Relation.ReflTransGen.refl
    | @tail b c _ hbc ih =>
      obtain ⟨e, he, rfl⟩ := hbc
      by_cases hbc' : b = c
      · subst hbc'; exact ih
      · exact ih.tail (by rw [openGraph_adj]; exact ⟨hbc', he⟩)
  · intro h
    induction h with
    | refl => exact Relation.ReflTransGen.refl
    | @tail b c _ hbc ih =>
      rw [openGraph_adj] at hbc
      exact ih.tail ⟨s(b, c), hbc.2, rfl⟩

/-- **The cluster of `x` in the general bond-graph picture is the open-graph cluster.** -/
theorem cluster_idBondGraph (ω : Config V) (x : V) :
    Percolation.cluster (idBondGraph V) ω x = cluster ω x := by
  ext y
  rw [mem_cluster_iff]
  exact conn_idBondGraph_iff ω x y

/-- An event is determined by the cluster of `x` (paper: an event of the form `{F(K_x) ≥ t}`). -/
def ClusterEvent (x : V) (A : Set (Config V)) : Prop :=
  ∀ ω ω' : Config V, cluster ω x = cluster ω' x → (ω ∈ A ↔ ω' ∈ A)

theorem clusterDeterminedAt_idBondGraph_iff (x : V) (A : Set (Config V)) :
    Percolation.ClusterDeterminedAt (idBondGraph V) x A ↔ ClusterEvent x A := by
  constructor
  · intro h ω ω' hc
    refine h ω ω' ?_
    rw [cluster_idBondGraph, cluster_idBondGraph, hc]
  · intro h ω ω' hc
    refine h ω ω' ?_
    rw [← cluster_idBondGraph, ← cluster_idBondGraph, hc]

theorem connEvent_idBondGraph (x y : V) :
    Percolation.connEvent (idBondGraph V) x y = {ω : Config V | Connects ω x y} := by
  ext ω
  exact conn_idBondGraph_iff ω x y

/-- `x ↔ y`: the connection event of §I.2.1. -/
def connSet (x y : V) : Set (Config V) := {ω | Connects ω x y}

/-- `x ↔ y ↮ z ↔ w`: `x ↔ y` and `z ↔ w` in *different* clusters (§I.2.1, Lemma I.2.2). -/
def apartSet (x y z w : V) : Set (Config V) :=
  {ω | Connects ω x y ∧ Connects ω z w ∧ ¬ Connects ω x z}

/-- `x ↔ y ↔ z ↔ w`: all four points in one cluster (§I.2.1, Lemma I.2.2). -/
def allConnSet (x y z w : V) : Set (Config V) :=
  {ω | Connects ω x y ∧ Connects ω y z ∧ Connects ω z w}

theorem connSet_eq (x y : V) : connSet x y = {ω : Config V | Connects ω x y} := rfl

theorem isUpper_connSet (x y : V) : IsUpperSet (connSet x y) :=
  isIncreasing_connects x y

theorem finiteWitness_connSet (x y : V) : Percolation.FiniteWitness (connSet x y) := by
  have h : connSet x y = {ω : Config V | Percolation.Conn (idBondGraph V) ω x y} := by
    ext ω
    show Connects ω x y ↔ Percolation.Conn (idBondGraph V) ω x y
    exact (conn_idBondGraph_iff ω x y).symm
  rw [h]
  exact Percolation.finiteWitness_conn (idBondGraph V) x y

theorem measurableSet_connSet (x y : V) : MeasurableSet (connSet x y) :=
  measurableSet_connects x y

theorem clusterEvent_connSet (x y : V) : ClusterEvent x (connSet x y) := by
  intro ω ω' h
  show Connects ω x y ↔ Connects ω' x y
  rw [← mem_cluster_iff, ← mem_cluster_iff, h]

theorem apartSet_eq (x y z w : V) : apartSet x y z w =
    {ω : Config V | Percolation.Conn (idBondGraph V) ω x y ∧
      Percolation.Conn (idBondGraph V) ω z w ∧ ¬ Percolation.Conn (idBondGraph V) ω x z} := by
  ext ω
  simp only [apartSet, Set.mem_ofPred_eq]
  rw [← conn_idBondGraph_iff ω x y, ← conn_idBondGraph_iff ω z w,
    ← conn_idBondGraph_iff ω x z]

theorem allConnSet_eq (x y z w : V) : allConnSet x y z w =
    {ω : Config V | Percolation.Conn (idBondGraph V) ω x y ∧
      Percolation.Conn (idBondGraph V) ω y z ∧ Percolation.Conn (idBondGraph V) ω z w} := by
  ext ω
  simp only [allConnSet, Set.mem_ofPred_eq]
  rw [← conn_idBondGraph_iff ω x y, ← conn_idBondGraph_iff ω y z,
    ← conn_idBondGraph_iff ω z w]

/-! ## Lemma I.2.1 (indicator form) and Lemma I.2.2 on the canonical model -/

/-- **Lemma I.2.1(i), canonical model.**  For increasing finitely witnessed events `A`, `B`
determined by the clusters of `x` and `y` respectively,
`P(A ∩ B ∩ {x ↮ y}) ≤ P(A) P(B)`. -/
theorem edgeMeasure_twoCluster_bk (π : Sym2 V → unitInterval) (hπ : ∀ e, π e < 1)
    (x y : V) (A B : Set (Config V))
    (hA : IsUpperSet A) (hfA : Percolation.FiniteWitness A) (hdA : ClusterEvent x A)
    (hB : IsUpperSet B) (hfB : Percolation.FiniteWitness B) (hdB : ClusterEvent y B) :
    (edgeMeasure π).real (A ∩ B ∩ {ω | ¬ Connects ω x y}) ≤
      (edgeMeasure π).real A * (edgeMeasure π).real B := by
  rw [edgeMeasure_eq_edgeLaw]
  have hEvents : {ω : Config V | ¬ Connects ω x y} =
      {ω : Config V | ¬ Percolation.Conn (idBondGraph V) ω x y} := by
    ext ω
    exact (not_congr (conn_idBondGraph_iff ω x y)).symm
  rw [hEvents]
  exact Percolation.twoCluster_bk (idBondGraph V) π hπ x y A B hA hfA
    ((clusterDeterminedAt_idBondGraph_iff x A).2 hdA) hB hfB
    ((clusterDeterminedAt_idBondGraph_iff y B).2 hdB)

/-- **Lemma I.2.1(ii), canonical model.** -/
theorem edgeMeasure_twoCluster_middle (π : Sym2 V → unitInterval) (hπ : ∀ e, π e < 1)
    (x y : V) (A B : Set (Config V))
    (hA : IsUpperSet A) (hfA : Percolation.FiniteWitness A)
    (hB : IsUpperSet B) (hfB : Percolation.FiniteWitness B) :
    (edgeMeasure π).real A * (edgeMeasure π).real B -
        (edgeMeasure π).real (A ∩ B ∩ {ω | Connects ω x y}) ≤
      (edgeMeasure π).real (A ∩ B ∩ {ω | ¬ Connects ω x y}) := by
  rw [edgeMeasure_eq_edgeLaw]
  have h1 : {ω : Config V | Connects ω x y} =
      {ω : Config V | Percolation.Conn (idBondGraph V) ω x y} := by
    ext ω
    exact (conn_idBondGraph_iff ω x y).symm
  have h2 : {ω : Config V | ¬ Connects ω x y} =
      {ω : Config V | ¬ Percolation.Conn (idBondGraph V) ω x y} := by
    ext ω
    exact (not_congr (conn_idBondGraph_iff ω x y)).symm
  rw [h1, h2]
  exact Percolation.twoCluster_middle (idBondGraph V) π hπ x y A B hA hfA hB hfB

/-- **Lemma I.2.1(iii), canonical model.** -/
theorem edgeMeasure_twoCluster_upper (π : Sym2 V → unitInterval) (hπ : ∀ e, π e < 1)
    (x y : V) (A B : Set (Config V))
    (hA : IsUpperSet A) (hfA : Percolation.FiniteWitness A) (hdA : ClusterEvent x A)
    (hB : IsUpperSet B) (hfB : Percolation.FiniteWitness B) (hdB : ClusterEvent y B) :
    0 ≤ (edgeMeasure π).real (A ∩ B) - (edgeMeasure π).real A * (edgeMeasure π).real B ∧
      (edgeMeasure π).real (A ∩ B) - (edgeMeasure π).real A * (edgeMeasure π).real B ≤
        (edgeMeasure π).real (A ∩ B ∩ {ω | Connects ω x y}) := by
  rw [edgeMeasure_eq_edgeLaw]
  have h1 : {ω : Config V | Connects ω x y} =
      {ω : Config V | Percolation.Conn (idBondGraph V) ω x y} := by
    ext ω
    exact (conn_idBondGraph_iff ω x y).symm
  rw [h1]
  exact Percolation.twoCluster_upper (idBondGraph V) π hπ x y A B hA hfA
    ((clusterDeterminedAt_idBondGraph_iff x A).2 hdA) hB hfB
    ((clusterDeterminedAt_idBondGraph_iff y B).2 hdB)

/-- **Lemma I.2.2, canonical model.**  For all `x y z w`,
`0 ≤ P(x↔y) P(z↔w) - P(x↔y ↮ z↔w) ≤ P(x↔y↔z↔w)`. -/
theorem edgeMeasure_threePoint (π : Sym2 V → unitInterval) (hπ : ∀ e, π e < 1)
    (x y z w : V) :
    0 ≤ (edgeMeasure π).real (connSet x y) * (edgeMeasure π).real (connSet z w) -
          (edgeMeasure π).real (apartSet x y z w) ∧
      (edgeMeasure π).real (connSet x y) * (edgeMeasure π).real (connSet z w) -
          (edgeMeasure π).real (apartSet x y z w) ≤ (edgeMeasure π).real (allConnSet x y z w) := by
  rw [edgeMeasure_eq_edgeLaw]
  have h1 : connSet x y = Percolation.connEvent (idBondGraph V) x y := by
    ext ω; exact (conn_idBondGraph_iff ω x y).symm
  have h2 : connSet z w = Percolation.connEvent (idBondGraph V) z w := by
    ext ω; exact (conn_idBondGraph_iff ω z w).symm
  have h3 : apartSet x y z w = Percolation.apartEvent (idBondGraph V) x y z w := by
    rw [apartSet_eq]
    rfl
  have h4 : allConnSet x y z w = Percolation.allConnEvent (idBondGraph V) x y z w := by
    rw [allConnSet_eq]
    rfl
  rw [h1, h2, h3, h4]
  exact Percolation.threePoint_bk (idBondGraph V) π hπ x y z w

/-! ## The paper's law `P_β` -/

/-- For finite `β` and a finite nonnegative kernel the edge probability `1 - e^{-β J_e}` is
strictly below one, which is the hypothesis of `bkEdge`. -/
theorem bernoulliEdgeProb_lt_one {J : Sym2 V → ℝ} (hJ : ∀ e, 0 ≤ J e) (β : NNReal)
    (e : Sym2 V) : bernoulliEdgeProb J hJ β e < 1 := by
  rw [← Subtype.coe_lt_coe, bernoulliEdgeProb_coe]
  have hpos : 0 < Real.exp (-((β : ℝ) * J e)) := Real.exp_pos _
  have hone : ((1 : unitInterval) : ℝ) = 1 := rfl
  rw [hone]
  linarith

/-- **BK for the paper's law `P_β`** on the canonical countable model, at every `β ≥ 0`. -/
theorem longRangeMeasure_bk {J : Sym2 V → ℝ} (hJ : ∀ e, 0 ≤ J e) (β : NNReal)
    (A B : Set (Config V)) (hA : IsUpperSet A) (hB : IsUpperSet B)
    (hfA : Percolation.FiniteWitness A) (hfB : Percolation.FiniteWitness B) :
    (longRangeMeasure J hJ β).real (Percolation.DisjointOccurrence A B) ≤
      (longRangeMeasure J hJ β).real A * (longRangeMeasure J hJ β).real B :=
  edgeMeasure_bk _ (fun e => bernoulliEdgeProb_lt_one hJ β e) A B hA hB hfA hfB

/-- **Harris--FKG for `P_β`.** -/
theorem longRangeMeasure_fkg {J : Sym2 V → ℝ} (hJ : ∀ e, 0 ≤ J e) (β : NNReal)
    (A B : Set (Config V)) (hA : IsUpperSet A) (hB : IsUpperSet B)
    (hfA : Percolation.FiniteWitness A) (hfB : Percolation.FiniteWitness B) :
    (longRangeMeasure J hJ β).real A * (longRangeMeasure J hJ β).real B ≤
      (longRangeMeasure J hJ β).real (A ∩ B) :=
  edgeMeasure_fkg _ A B hA hB hfA hfB

/-- **Lemma I.2.1(i) for `P_β`.** -/
theorem longRangeMeasure_twoCluster_bk {J : Sym2 V → ℝ} (hJ : ∀ e, 0 ≤ J e) (β : NNReal)
    (x y : V) (A B : Set (Config V))
    (hA : IsUpperSet A) (hfA : Percolation.FiniteWitness A) (hdA : ClusterEvent x A)
    (hB : IsUpperSet B) (hfB : Percolation.FiniteWitness B) (hdB : ClusterEvent y B) :
    (longRangeMeasure J hJ β).real (A ∩ B ∩ {ω | ¬ Connects ω x y}) ≤
      (longRangeMeasure J hJ β).real A * (longRangeMeasure J hJ β).real B :=
  edgeMeasure_twoCluster_bk _ (fun e => bernoulliEdgeProb_lt_one hJ β e) x y A B
    hA hfA hdA hB hfB hdB

/-- **Lemma I.2.2 for `P_β`.** -/
theorem longRangeMeasure_threePoint {J : Sym2 V → ℝ} (hJ : ∀ e, 0 ≤ J e) (β : NNReal)
    (x y z w : V) :
    0 ≤ (longRangeMeasure J hJ β).real (connSet x y) * (longRangeMeasure J hJ β).real (connSet z w) -
          (longRangeMeasure J hJ β).real (apartSet x y z w) ∧
      (longRangeMeasure J hJ β).real (connSet x y) * (longRangeMeasure J hJ β).real (connSet z w) -
          (longRangeMeasure J hJ β).real (apartSet x y z w) ≤
        (longRangeMeasure J hJ β).real (allConnSet x y z w) :=
  edgeMeasure_threePoint _ (fun e => bernoulliEdgeProb_lt_one hJ β e) x y z w

end PercLib.CriticalLRP
