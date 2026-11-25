/-
Adapted from Percolation after Anthropic, prompted by Ahmed Bou-Rabee,
produced with ChatGPT and Claude. Apache License 2.0.
Pinned source: a5cc72bd7627f313abbb00bcb47616678abbeb35.
Sources:
https://github.com/nitromannitol/percolation-after-anthropic/blob/a5cc72bd7627f313abbb00bcb47616678abbeb35/Hypergraph/SiteStatements.lean
https://github.com/nitromannitol/percolation-after-anthropic/blob/a5cc72bd7627f313abbb00bcb47616678abbeb35/PercolationAudit/SiteCriticality/SolutionBasic.lean

The Site and zdGraph vocabulary originates in PercolationContinuity,
Copyright 2026 Anthropic, PBC, at commit 795efb86f191735c5481675763537cfb4ff37e55.
See third_party/percolation/LICENSE and third_party/percolation/NOTICE.

Modified for this project on 2026-11-12: namespace, focused imports, Lean 4.35 public
declarations, and removal of unrelated imports and later theorem families.
The mathematical definitions and selected proofs below retain their source
statements. No criticality theorem is copied or assumed.
Moved on 2026-11-12 from Percolation/Site/Basic.lean to Models/Site/Basic.lean, with the
namespace changed from Percolation.Site to Models.Site under the project root
(docs/DECISIONS.md, D-3). Renamed on 2026-11-13: the project root namespace and library
became PercLib (D-11). No definition, statement or proof was changed by either step.
-/
module

public import PercLib.Probability.ProdBernoulli
public import Mathlib.Combinatorics.SimpleGraph.Hasse
public import Mathlib.MeasureTheory.Measure.Real

/-!
# Site configurations, connection events and the critical parameter

Selected foundational definitions and proofs from the sources cited above.
In particular a closed vertex has empty open cluster, and the event of an
infinite cluster is measurable on a countable graph.

The lattice vocabulary and the infimum defining the critical parameter agree
with the upstream comparator vocabulary. This module does not contain the
upstream theorem that the percolation probability vanishes at the critical parameter.
-/

@[expose] public section

noncomputable section

open MeasureTheory Set PercLib.Probability

namespace PercLib.Models.Site

/-- A vertex of the integer lattice. -/
abbrev LatticeSite (d : ℕ) : Type := Fin d → ℤ

/-- The nearest-neighbour lattice graph, represented by the Hasse graph. -/
abbrev zdGraph (d : ℕ) : SimpleGraph (LatticeSite d) := SimpleGraph.hasse (LatticeSite d)

/-- A site configuration: the set of open vertices. -/
abbrev SiteConfig (V : Type*) : Type _ := Set V

variable {V : Type*}

/-- The graph of open vertices: an edge of `G` survives when both of its endpoints are open. -/
def openSiteGraph (G : SimpleGraph V) (ω : SiteConfig V) : SimpleGraph V :=
  SimpleGraph.fromRel fun x y => G.Adj x y ∧ x ∈ ω ∧ y ∈ ω

/-- The open cluster of `x`: empty when `x` is closed, and otherwise the set of vertices joined to
`x` by a path of open vertices. -/
def siteCluster (G : SimpleGraph V) (ω : SiteConfig V) (x : V) : Set V :=
  {y | x ∈ ω ∧ (openSiteGraph G ω).Reachable x y}

/-- The event that `x` and `y` are joined by a path of open vertices. -/
def siteConn (G : SimpleGraph V) (x y : V) : Set (SiteConfig V) :=
  {ω | x ∈ ω ∧ (openSiteGraph G ω).Reachable x y}

/-- The event that `x` is connected to some vertex of `A`. -/
def siteConnSet (G : SimpleGraph V) (x : V) (A : Set V) : Set (SiteConfig V) :=
  ⋃ a ∈ A, siteConn G x a

/-- Site percolation with vertex probabilities `w`: each vertex is open independently. -/
def siteBernoulli (w : V → unitInterval) : Measure (SiteConfig V) := prodBernoulli w

instance instIsProbabilityMeasureSiteBernoulli (w : V → unitInterval) :
    IsProbabilityMeasure (siteBernoulli w) :=
  instIsProbabilityMeasureProdBernoulli w

/-- Site percolation on an arbitrary graph: the probability that the open cluster of `x` is
infinite when every vertex is open with probability `p`. -/
def thetaSiteOn (G : SimpleGraph V) (x : V) (p : unitInterval) : ℝ :=
  (siteBernoulli (fun _ : V => p)).real {ω | (siteCluster G ω x).Infinite}

/-- Adjacency in the open site graph: an edge of `G` with both endpoints open. -/
theorem openSiteGraph_adj_iff' (G : SimpleGraph V) (ω : Set V) (x y : V) :
    (openSiteGraph G ω).Adj x y ↔ G.Adj x y ∧ x ∈ ω ∧ y ∈ ω := by
  constructor
  · rintro ⟨-, hor⟩
    rcases hor with ⟨h, hx, hy⟩ | ⟨h, hy, hx⟩
    · exact ⟨h, hx, hy⟩
    · exact ⟨h.symm, hx, hy⟩
  · rintro ⟨h, hx, hy⟩
    exact ⟨h.ne, Or.inl ⟨h, hx, hy⟩⟩

/-! ### Sanity checks on the conventions

These pin down the reading of the definitions, so that the statements below can be checked rather
than taken on trust. -/

/-- A closed vertex is connected to nothing, not even to itself. -/
theorem siteConn_self (G : SimpleGraph V) (x : V) : siteConn G x x = {ω | x ∈ ω} := by
  ext ω
  exact ⟨fun h => h.1, fun h => ⟨h, SimpleGraph.Reachable.refl x⟩⟩

/-- The open cluster of a closed vertex is empty. -/
theorem siteCluster_of_notMem (G : SimpleGraph V) (ω : Set V) {x : V} (hx : x ∉ ω) :
    siteCluster G ω x = ∅ := by
  ext y
  exact ⟨fun h => absurd h.1 hx, fun h => absurd h (Set.notMem_empty y)⟩

/-- A vertex of its own open cluster: an open vertex lies in its cluster. -/
theorem mem_siteCluster_self (G : SimpleGraph V) (ω : Set V) {x : V} (hx : x ∈ ω) :
    x ∈ siteCluster G ω x :=
  ⟨hx, SimpleGraph.Reachable.refl x⟩

/-- Every vertex of the open cluster of an open vertex is itself open. -/
theorem mem_of_mem_siteCluster (G : SimpleGraph V) (ω : Set V) {x y : V}
    (h : y ∈ siteCluster G ω x) : y ∈ ω := by
  obtain ⟨hx, hr⟩ := h
  obtain ⟨p⟩ := hr
  induction p with
  | nil => exact hx
  | cons hadj q ih => exact ih ((openSiteGraph_adj_iff' G ω _ _).1 hadj).2.2

/-- Two adjacent open vertices are connected: the connection event is not empty when it should not
be. -/
theorem siteConn_of_adj (G : SimpleGraph V) {ω : Set V} {x y : V} (h : G.Adj x y)
    (hx : x ∈ ω) (hy : y ∈ ω) : ω ∈ siteConn G x y :=
  ⟨hx, SimpleGraph.Adj.reachable ((openSiteGraph_adj_iff' G ω x y).2 ⟨h, hx, hy⟩)⟩

/-- Connection requires both endpoints to be open. -/
theorem siteConn_subset (G : SimpleGraph V) (x y : V) :
    siteConn G x y ⊆ {ω | x ∈ ω ∧ y ∈ ω} := by
  rintro ω ⟨hx, hr⟩
  exact ⟨hx, mem_of_mem_siteCluster G ω ⟨hx, hr⟩⟩


/-- An open walk is a chain of one-vertex cylinder events. -/
theorem measurableSet_isChain_openSiteGraph (G : SimpleGraph V) :
    ∀ (a : V) (l : List V),
      MeasurableSet {ω : SiteConfig V | List.IsChain (openSiteGraph G ω).Adj (a :: l)} := by
  intro a l
  induction l generalizing a with
  | nil => simp
  | cons b l ih =>
    have hset : {ω : SiteConfig V | List.IsChain (openSiteGraph G ω).Adj (a :: b :: l)} =
        (({_ω : SiteConfig V | G.Adj a b} ∩ {ω : SiteConfig V | a ∈ ω}) ∩
            {ω : SiteConfig V | b ∈ ω}) ∩
          {ω | List.IsChain (openSiteGraph G ω).Adj (b :: l)} := by
      ext ω
      simp only [List.isChain_cons_cons, openSiteGraph_adj_iff', Set.mem_ofPred_eq,
        Set.mem_inter_iff, and_assoc]
    rw [hset]
    exact (((MeasurableSet.const _).inter (measurableSet_mem _)).inter
      (measurableSet_mem _)).inter (ih b)

/-- `{x ↔ y}` as a union over the finite lists of vertices witnessing an open walk. -/
theorem siteConn_eq_iUnion (G : SimpleGraph V) (x y : V) :
    siteConn G x y = {ω : SiteConfig V | x ∈ ω} ∩
      ⋃ l : List V, {ω : SiteConfig V | List.IsChain (openSiteGraph G ω).Adj (x :: l) ∧
        (x :: l).getLast (List.cons_ne_nil _ _) = y} := by
  ext ω
  simp only [siteConn, Set.mem_ofPred_eq, Set.mem_inter_iff, Set.mem_iUnion]
  rw [and_congr_right_iff]
  intro _
  rw [SimpleGraph.reachable_iff_reflTransGen]
  constructor
  · exact List.exists_isChain_cons_of_relationReflTransGen
  · rintro ⟨l, hl, hy⟩
    exact List.relationReflTransGen_of_exists_isChain_cons l hl hy

/-- The event that `x` and `y` are joined by an open path is measurable. -/
theorem measurableSet_siteConn [Countable V] (G : SimpleGraph V) (x y : V) :
    MeasurableSet (siteConn G x y) := by
  rw [siteConn_eq_iUnion]
  refine (measurableSet_mem _).inter (MeasurableSet.iUnion fun l => ?_)
  have hset : {ω : SiteConfig V | List.IsChain (openSiteGraph G ω).Adj (x :: l) ∧
      (x :: l).getLast (List.cons_ne_nil _ _) = y} =
        {ω : SiteConfig V | List.IsChain (openSiteGraph G ω).Adj (x :: l)} ∩
          {_ω | (x :: l).getLast (List.cons_ne_nil _ _) = y} := by
    ext ω; simp
  rw [hset]
  exact (measurableSet_isChain_openSiteGraph G x l).inter (MeasurableSet.const _)

/-- The open cluster of `x` is infinite exactly when it leaves every finite set of vertices. -/
theorem siteInfinite_eq_iInter (G : SimpleGraph V) (x : V) :
    {ω : SiteConfig V | (siteCluster G ω x).Infinite} =
      ⋂ F : Finset V, ⋃ y ∈ (↑F : Set V)ᶜ, siteConn G x y := by
  ext ω
  simp only [Set.mem_ofPred_eq, Set.mem_iInter, Set.mem_iUnion, Set.mem_compl_iff,
    Finset.mem_coe, exists_prop, siteCluster, siteConn]
  constructor
  · intro hinf F
    obtain ⟨y, hy, hyF⟩ := hinf.exists_notMem_finset F
    exact ⟨y, hyF, hy⟩
  · intro h hfin
    obtain ⟨y, hyF, hy⟩ := h hfin.toFinset
    exact hyF (hfin.mem_toFinset.2 hy)

/-- The event that the open cluster of `x` is infinite is measurable. -/
theorem measurableSet_siteInfinite [Countable V] (G : SimpleGraph V) (x : V) :
    MeasurableSet {ω : SiteConfig V | (siteCluster G ω x).Infinite} := by
  rw [siteInfinite_eq_iInter]
  exact MeasurableSet.iInter fun F =>
    MeasurableSet.biUnion (Set.to_countable _) fun y _ => measurableSet_siteConn G x y


/-- The percolation probability of site percolation on `ℤ^d` at parameter `p`: the probability that
the open cluster of the origin is infinite. -/
noncomputable def thetaSite (d : ℕ) (p : unitInterval) : ℝ :=
  thetaSiteOn (zdGraph d) (0 : LatticeSite d) p

/-- The critical parameter of site percolation on `ℤ^d`: the infimum of the parameters at which the
origin percolates, together with `1`. -/
noncomputable def criticalProbSite (d : ℕ) : ℝ :=
  sInf ({p : ℝ | ∃ h : p ∈ unitInterval, 0 < thetaSite d ⟨p, h⟩} ∪ {1})

/-- The set whose infimum defines the critical parameter consists of nonnegative numbers. -/
theorem criticalProbSite_nonneg_mem (d : ℕ) :
    ∀ p ∈ ({p : ℝ | ∃ h : p ∈ unitInterval, 0 < thetaSite d ⟨p, h⟩} ∪ {1}), 0 ≤ p := by
  rintro p (⟨h, -⟩ | h)
  · exact h.1
  · rw [Set.mem_singleton_iff] at h
    rw [h]; exact zero_le_one

/-- The critical parameter lies in the unit interval. -/
theorem criticalProbSite_mem_Icc (d : ℕ) : criticalProbSite d ∈ Set.Icc (0 : ℝ) 1 :=
  ⟨le_csInf ⟨1, Or.inr rfl⟩ (criticalProbSite_nonneg_mem d),
    csInf_le ⟨0, criticalProbSite_nonneg_mem d⟩ (Or.inr rfl)⟩

/-- The critical parameter as a point of the unit interval, so that it can be fed to `thetaSite`. -/
noncomputable def criticalProbSiteI (d : ℕ) : unitInterval :=
  ⟨criticalProbSite d, criticalProbSite_mem_Icc d⟩

end PercLib.Models.Site
end

