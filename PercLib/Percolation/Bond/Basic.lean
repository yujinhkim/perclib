/-
Bond percolation interface for this project (DECISIONS D-2), written on 2026-11-13.

The proofs of `measurableSet_isChain_openGraph`, `conn_eq_iUnion`, `measurableSet_conn`,
`cluster_infinite_eq_iInter` and `measurableSet_cluster_infinite` are adapted from the
site-percolation proofs in Percolation after Anthropic, prompted by Ahmed Bou-Rabee,
produced with ChatGPT and Claude, Apache License 2.0, at pinned revision
a5cc72bd7627f313abbb00bcb47616678abbeb35:
https://github.com/nitromannitol/percolation-after-anthropic/blob/a5cc72bd7627f313abbb00bcb47616678abbeb35/Hypergraph/SiteStatements.lean
(lines 308-374 at that revision). They reach this file through this project's adapted
copy, PercLib/Models/Site/Basic.lean. The upstream licence and the retained notices are
in third_party/percolation/LICENSE and third_party/percolation/NOTICE.

Modified for this project: site configurations (sets of open vertices) replaced by bond
configurations (sets of open unordered pairs); the open site graph replaced by
SimpleGraph.fromEdgeSet, so a walk step needs an open pair of distinct vertices instead of
a host edge with two open endpoints; the closed-vertex case removed, because a bond
cluster always contains its base vertex. The other declarations in this file are new.
-/
module

public import PercLib.Probability.ProdBernoulli
public import Mathlib.Combinatorics.SimpleGraph.Connectivity.Connected
public import Mathlib.Basic.Real.ENatENNReal
public import Mathlib.Data.Set.Card
public import Mathlib.MeasureTheory.Integral.Lebesgue.Basic

/-!
# Bond percolation: configurations, connections and clusters

This module fixes the interface of `docs/DECISIONS.md`, D-2.

* A bond configuration on a vertex type `V` is a set of unordered pairs, `Set (Sym2 V)`:
  the set of open pairs.
* The law is `PercLib.Probability.prodBernoulli q` for `q : Sym2 V → unitInterval`.
* The open graph is `SimpleGraph.fromEdgeSet ω`. That construction discards loops, so
  the value of `q` on the diagonal never matters and is never a hypothesis.
* There is no host graph. Every pair of distinct vertices is a potential edge.
* `Countable V` is a hypothesis of the measurability statements only.
* The cluster of a vertex always contains that vertex, so its volume is at least one.
  The volume is `ℕ∞`-valued and the susceptibility is `ℝ≥0∞`-valued.

The measurability arguments follow those for site percolation in
`PercLib.Models.Site.Basic`: a connection is a countable union, over lists of vertices,
of finite intersections of one-edge cylinder events.
-/

@[expose] public section

noncomputable section

open MeasureTheory Set PercLib.Probability
open scoped ENNReal

namespace PercLib.Percolation.Bond

variable {V : Type*}

/-- A bond configuration: the set of open unordered pairs of vertices. -/
abbrev Config (V : Type*) : Type _ := Set (Sym2 V)

/-- Independent bond percolation: the pair `e` is open with probability `q e`,
independently over pairs. -/
def law (q : Sym2 V → unitInterval) : Measure (Config V) := prodBernoulli q

instance instIsProbabilityMeasureLaw (q : Sym2 V → unitInterval) :
    IsProbabilityMeasure (law q) :=
  instIsProbabilityMeasureProdBernoulli q

/-- The graph of open edges. Open loops are discarded. -/
def openGraph (ω : Config V) : SimpleGraph V := SimpleGraph.fromEdgeSet ω

/-- The event that `x` and `y` are joined by a path of open edges. -/
def conn (x y : V) : Set (Config V) := {ω | (openGraph ω).Reachable x y}

/-- The open cluster of `x`: the vertices joined to `x` by a path of open edges.
It always contains `x`. -/
def cluster (ω : Config V) (x : V) : Set V := {y | (openGraph ω).Reachable x y}

/-- The two-point function: the probability that `x` and `y` are connected. -/
def tau (q : Sym2 V → unitInterval) (x y : V) : ℝ≥0∞ := law q (conn x y)

/-- The susceptibility at `x`: the expected number of vertices in the cluster of `x`. -/
def chi (q : Sym2 V → unitInterval) (x : V) : ℝ≥0∞ :=
  ∫⁻ ω, ((cluster ω x).encard : ℝ≥0∞) ∂(law q)

/-! ### The conventions, pinned down -/

/-- Two vertices are adjacent in the open graph exactly when they are distinct and the
pair is open. -/
theorem openGraph_adj_iff (ω : Config V) (x y : V) :
    (openGraph ω).Adj x y ↔ s(x, y) ∈ ω ∧ x ≠ y :=
  SimpleGraph.fromEdgeSet_adj ω

/-- The open graph grows with the configuration. -/
theorem openGraph_mono {ω ω' : Config V} (h : ω ⊆ ω') : openGraph ω ≤ openGraph ω' :=
  SimpleGraph.fromEdgeSet_mono h

/-- With no open pair, the open graph has no edge. -/
theorem openGraph_empty : openGraph (∅ : Config V) = ⊥ :=
  SimpleGraph.fromEdgeSet_empty

theorem mem_conn_iff (ω : Config V) (x y : V) :
    ω ∈ conn x y ↔ (openGraph ω).Reachable x y := Iff.rfl

theorem mem_cluster_iff (ω : Config V) (x y : V) :
    y ∈ cluster ω x ↔ ω ∈ conn x y := Iff.rfl

/-- Connection is reflexive: every vertex is connected to itself in every
configuration. -/
theorem conn_self (x : V) : conn x x = (Set.univ : Set (Config V)) :=
  Set.eq_univ_of_forall fun _ => SimpleGraph.Reachable.refl x

/-- Connection is symmetric. -/
theorem conn_symm (x y : V) : (conn x y : Set (Config V)) = conn y x := by
  ext ω
  exact SimpleGraph.reachable_comm

/-- Connection is transitive. -/
theorem conn_trans {ω : Config V} {x y z : V} (hxy : ω ∈ conn x y) (hyz : ω ∈ conn y z) :
    ω ∈ conn x z :=
  SimpleGraph.Reachable.trans hxy hyz

/-- Connection is an increasing event. -/
theorem conn_mono {ω ω' : Config V} (h : ω ⊆ ω') {x y : V} (hxy : ω ∈ conn x y) :
    ω' ∈ conn x y :=
  SimpleGraph.Reachable.mono (openGraph_mono h) hxy

/-- An open pair of distinct vertices connects its endpoints: the connection event is
not empty when it should not be. -/
theorem mem_conn_of_mem {ω : Config V} {x y : V} (hxy : x ≠ y) (h : s(x, y) ∈ ω) :
    ω ∈ conn x y :=
  SimpleGraph.Adj.reachable ((openGraph_adj_iff ω x y).2 ⟨h, hxy⟩)

/-- With no open pair, a vertex is connected only to itself: the connection event is not
everything when it should not be. -/
theorem empty_mem_conn_iff (x y : V) : (∅ : Config V) ∈ conn x y ↔ x = y := by
  rw [mem_conn_iff, openGraph_empty]
  exact SimpleGraph.reachable_bot

/-- A vertex belongs to its own cluster. -/
theorem mem_cluster_self (ω : Config V) (x : V) : x ∈ cluster ω x :=
  SimpleGraph.Reachable.refl x

/-- Membership in a cluster is symmetric. -/
theorem mem_cluster_comm (ω : Config V) (x y : V) : y ∈ cluster ω x ↔ x ∈ cluster ω y :=
  SimpleGraph.reachable_comm

/-- With no open pair, every cluster is a single vertex. -/
theorem cluster_empty (x : V) : cluster (∅ : Config V) x = {x} := by
  ext y
  rw [mem_cluster_iff, empty_mem_conn_iff, Set.mem_singleton_iff, eq_comm]

/-- A cluster has at least one vertex. -/
theorem one_le_encard_cluster (ω : Config V) (x : V) : 1 ≤ (cluster ω x).encard :=
  Set.one_le_encard_iff_nonempty.2 ⟨x, mem_cluster_self ω x⟩

/-- A vertex is connected to itself with probability one. -/
theorem tau_self (q : Sym2 V → unitInterval) (x : V) : tau q x x = 1 := by
  rw [tau, conn_self, measure_univ]

/-- The two-point function is symmetric. -/
theorem tau_comm (q : Sym2 V → unitInterval) (x y : V) : tau q x y = tau q y x := by
  rw [tau, tau, conn_symm]

/-- The two-point function is at most one. -/
theorem tau_le_one (q : Sym2 V → unitInterval) (x y : V) : tau q x y ≤ 1 :=
  prob_le_one

/-! ### Measurability -/

/-- An open walk along a given list of vertices is a finite intersection of one-edge
cylinder events. -/
theorem measurableSet_isChain_openGraph (a : V) (l : List V) :
    MeasurableSet {ω : Config V | List.IsChain (openGraph ω).Adj (a :: l)} := by
  induction l generalizing a with
  | nil => simp
  | cons b l ih =>
    have hset : {ω : Config V | List.IsChain (openGraph ω).Adj (a :: b :: l)} =
        ({ω : Config V | s(a, b) ∈ ω} ∩ {_ω : Config V | a ≠ b}) ∩
          {ω | List.IsChain (openGraph ω).Adj (b :: l)} := by
      ext ω
      simp only [List.isChain_cons_cons, openGraph_adj_iff, Set.mem_ofPred_eq,
        Set.mem_inter_iff]
    rw [hset]
    exact ((measurableSet_mem _).inter (MeasurableSet.const _)).inter (ih b)

/-- The connection event as a union over the lists of vertices that witness an open
walk. -/
theorem conn_eq_iUnion (x y : V) :
    (conn x y : Set (Config V)) =
      ⋃ l : List V, {ω : Config V | List.IsChain (openGraph ω).Adj (x :: l) ∧
        (x :: l).getLast (List.cons_ne_nil _ _) = y} := by
  ext ω
  simp only [conn, Set.mem_ofPred_eq, Set.mem_iUnion]
  rw [SimpleGraph.reachable_iff_reflTransGen]
  constructor
  · exact List.exists_isChain_cons_of_relationReflTransGen
  · rintro ⟨l, hl, hy⟩
    exact List.relationReflTransGen_of_exists_isChain_cons l hl hy

/-- The connection event is measurable when there are countably many vertices. -/
theorem measurableSet_conn [Countable V] (x y : V) :
    MeasurableSet (conn x y : Set (Config V)) := by
  rw [conn_eq_iUnion]
  refine MeasurableSet.iUnion fun l => ?_
  have hset : {ω : Config V | List.IsChain (openGraph ω).Adj (x :: l) ∧
      (x :: l).getLast (List.cons_ne_nil _ _) = y} =
        {ω : Config V | List.IsChain (openGraph ω).Adj (x :: l)} ∩
          {_ω | (x :: l).getLast (List.cons_ne_nil _ _) = y} := by
    ext ω; simp
  rw [hset]
  exact (measurableSet_isChain_openGraph x l).inter (MeasurableSet.const _)

/-- The cluster of `x` is infinite exactly when it leaves every finite set of
vertices. -/
theorem cluster_infinite_eq_iInter (x : V) :
    {ω : Config V | (cluster ω x).Infinite} =
      ⋂ F : Finset V, ⋃ y ∈ (↑F : Set V)ᶜ, conn x y := by
  ext ω
  simp only [Set.mem_ofPred_eq, Set.mem_iInter, Set.mem_iUnion, Set.mem_compl_iff,
    Finset.mem_coe, exists_prop, ← mem_cluster_iff]
  constructor
  · intro hinf F
    obtain ⟨y, hy, hyF⟩ := hinf.exists_notMem_finset F
    exact ⟨y, hyF, hy⟩
  · intro h hfin
    obtain ⟨y, hyF, hy⟩ := h hfin.toFinset
    exact hyF (hfin.mem_toFinset.2 hy)

/-- The event that the cluster of `x` is infinite is measurable when there are countably
many vertices. -/
theorem measurableSet_cluster_infinite [Countable V] (x : V) :
    MeasurableSet {ω : Config V | (cluster ω x).Infinite} := by
  rw [cluster_infinite_eq_iInter]
  exact MeasurableSet.iInter fun F =>
    MeasurableSet.biUnion (Set.to_countable _) fun y _ => measurableSet_conn x y

/-! ### Non-vacuity

Compiled witnesses that the definitions are neither empty nor trivial in the smallest
relevant case, the two-point vertex type `Bool`. -/

/-- With every pair open, the two vertices of `Bool` are connected. -/
example : (Set.univ : Config Bool) ∈ conn false true :=
  mem_conn_of_mem (by decide) (Set.mem_univ _)

/-- With no pair open, the two vertices of `Bool` are not connected. -/
example : (∅ : Config Bool) ∉ conn false true := by
  rw [empty_mem_conn_iff]
  decide

/-- With no pair open, the cluster of a vertex has exactly one element. -/
example : (cluster (∅ : Config Bool) false).encard = 1 := by
  rw [cluster_empty, Set.encard_singleton]

end PercLib.Percolation.Bond

end
