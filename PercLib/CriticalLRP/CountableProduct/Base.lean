/-
Migration source: https://github.com/yujinhkim/Critical-Long-range-percolation
Integration revision: 3b3d1d0e43ef940bfaa2292ee5c2ee094ac4edbf
Licence: Apache-2.0 for the PercLib Lean sources and tooling; see third_party/critical-lrp/.
External provenance and modifications are recorded in the file-specific notices below.
-/

/-
Long-range percolation on a countable vertex set: the configuration space, the
independent-edge law, clusters, and the *genuine* infinite-cluster predicate.

Source: Tom Hutchcroft, *Critical long-range percolation I: High effective dimension*,
arXiv:2508.18807v1.

* §I.1.2, p. 6: "In long-range percolation on `Z^d`, we define a random graph with vertex
  set `Z^d` and where each pair of vertices `x ≠ y` forms an edge `{x,y}` with probability
  `1 - e^{-β J(x,y)}`, independently of all other pairs, where `β ≥ 0` is a parameter and
  `J : Z^d × Z^d → [0,∞)` is a kernel that is symmetric and translation-invariant in the
  sense that `J(x,y) = J(y,x) = J(0,y-x)`."  Edges included in the configuration are
  *open*, connected components are *clusters*, `P_β` is the law, and
  `β_c := inf{β ≥ 0 : an infinite cluster exists P_β-a.s.}`.
* `|K|`, the *volume* of a cluster, is the number of its vertices (Section I.2.1 onwards);
  it is an extended natural number and may be `∞`.  "`K` always denotes the cluster of the
  origin."

## Design

This module uses the native `PercLib.Percolation.Bond` bond interface. The
compatibility abbreviation `edgeMeasure` is native `Bond.law`, not an independently
defined product measure. `Connects` is reachability in the native open graph and
`cluster` is the native cluster. The cluster volume is the coerced `encard` of that
cluster. The old sum-of-indicators identity is proved, rather than built into a rival
representation of volume. `edgeMeasure_eq_infinitePi` explicitly bridges native
`prodBernoulli` to the predicate-indexed product representation used below.

`SimpleGraph.fromEdgeSet` discards diagonal pairs, so diagonal coordinates do not
change connectivity. The real-valued tail behavior of infinite volume is treated
only through the explicit tail-or-infinite events established in the consumer
modules; it is not assumed away. The generalized edge-labelled `BondGraph` model in
`BK/Graph.lean` is separate from this canonical complete-graph bond interface.

## Provenance

The integration revision supplied the original countable-product development. During
migration its canonical configuration, law, graph and cluster were replaced by the
native PercLib interfaces, with compatibility aliases and proof repairs. This module
retains the original path-walk and cardinality calculations where they are useful.
The native source's file-level notices remain in the imported PercLib modules; the
migration source and modification notices are retained above.
-/
module

public import Mathlib
public import PercLib.Percolation.Bond.Susceptibility
public import PercLib.Probability.BKEndpoints
public import PercLib.Probability.Cylinder
public import PercLib.Probability.ProdBernoulliIndependence

set_option linter.unusedSectionVars false
set_option linter.unusedSimpArgs false
set_option linter.unnecessarySimpa false
set_option linter.unusedTactic false
set_option linter.unusedVariables false

set_option autoImplicit true

set_option linter.unusedSectionVars false

@[expose] public section

open MeasureTheory Measure ProbabilityTheory unitInterval
open scoped ENNReal

namespace PercLib.CriticalLRP

/-! ## The configuration space and the independent-edge law -/

/-- A configuration of bond percolation on the complete graph with vertex set `V`: the set
of open edges, i.e. a set of unordered pairs of vertices. -/
abbrev Config (V : Type*) := PercLib.Percolation.Bond.Config V

/-- `Config V` is definitionally `Sym2 V → Prop`, the product type on which
`Measure.infinitePi` lives. -/
theorem config_eq_pi (V : Type*) : Config V = (Sym2 V → Prop) := rfl

section Space

variable {V : Type*} [Countable V]

/-- **Bernoulli bond percolation on the complete graph.**  Edges are open independently,
edge `e` with probability `π e`.  This is the law `P_β` of §I.1.2 with
`π ⟨x,y⟩ = 1 - exp(-β J(x,y))`. -/
noncomputable abbrev edgeMeasure (π : Sym2 V → unitInterval) : Measure (Config V) :=
  PercLib.Percolation.Bond.law π

/-- The transported product representation of native `prodBernoulli`, in the direct
predicate form used by the long-range proofs. -/
theorem edgeMeasure_eq_infinitePi (π : Sym2 V → unitInterval) :
    edgeMeasure π = Measure.infinitePi (X := fun _ : Sym2 V => Prop)
      (fun e => bernoulliMeasure (True : Prop) (False : Prop) (π e)) := by
  rw [edgeMeasure, PercLib.Percolation.Bond.law, PercLib.Probability.prodBernoulli_eq_map]
  change (Measure.infinitePi (X := fun _ : Sym2 V => Prop)
    (fun e => bernoulliMeasure (True : Prop) (False : Prop) (π e))).map id = _
  rw [Measure.map_id]

/-- **Cylinder formula.**  The probability that every edge of a finite set `s` is open is
the product of the per-edge probabilities. -/
theorem edgeMeasure_cylinder (π : Sym2 V → unitInterval) (s : Finset (Sym2 V)) :
    edgeMeasure π {ω : Config V | ∀ e ∈ s, e ∈ ω} =
      ∏ e ∈ s, (toNNReal (π e) : ℝ≥0∞) := by
  rw [edgeMeasure, PercLib.Percolation.Bond.law]
  simpa only [Set.subset_def, Finset.mem_coe] using
    PercLib.Probability.prodBernoulli_subset π s

/-- **Independence.**  The coordinate projections `ω ↦ (e ∈ ω)` are independent: the
"independently of all other pairs" clause of §I.1.2. -/
theorem iIndepFun_edgeMeasure (π : Sym2 V → unitInterval) :
    iIndepFun (fun e (ω : Config V) => ω e) (edgeMeasure π) :=
  PercLib.Probability.prodBernoulli_iIndepFun_mem π

/-- Degenerate case `π ≡ 1`: every edge is open, so the law is the point mass at the
complete configuration. -/
theorem edgeMeasure_one : edgeMeasure (fun _ : Sym2 V => (1 : unitInterval)) =
    dirac (Set.univ : Config V) := by
  rw [edgeMeasure, PercLib.Percolation.Bond.law]
  simpa only [Set.mem_univ, ite_true] using
    PercLib.Probability.prodBernoulli_deterministic (Set.univ : Set (Sym2 V))

/-- An event is **increasing** if it is preserved by turning closed edges into open edges
(the hypothesis of the Harris–FKG inequality, §I.2.1, and of the monotone coupling in
`β`).  This is Mathlib's `IsUpperSet` for the inclusion order on configurations. -/
abbrev IsIncreasing (A : Set (Config V)) : Prop := IsUpperSet A

end Space

/-! ## The open subgraph, connectivity and clusters -/

section Cluster

variable {V : Type*} [Countable V]

/-- The open subgraph of a configuration. -/
abbrev openGraph (ω : Config V) : SimpleGraph V :=
  PercLib.Percolation.Bond.openGraph ω

theorem openGraph_adj {ω : Config V} {x y : V} :
    (openGraph ω).Adj x y ↔ x ≠ y ∧ s(x,y) ∈ ω := by
  rw [PercLib.Percolation.Bond.openGraph_adj_iff]
  exact and_comm

/-- `x` and `y` are connected by a path of open edges. -/
abbrev Connects (ω : Config V) (x y : V) : Prop :=
  (PercLib.Percolation.Bond.openGraph ω).Reachable x y

/-- The cluster of `v`, using PercLib's native `Set (Sym2 V)` bond interface. -/
abbrev cluster (ω : Config V) (v : V) : Set V := PercLib.Percolation.Bond.cluster ω v

theorem mem_cluster_iff {ω : Config V} {v w : V} : w ∈ cluster ω v ↔ Connects ω v w :=
  Iff.rfl

theorem cluster_mem_self (ω : Config V) (v : V) : v ∈ cluster ω v :=
  mem_cluster_iff.mpr (SimpleGraph.Reachable.refl v)

theorem cluster_eq_iff {ω : Config V} {v w : V} : cluster ω v = cluster ω w ↔ Connects ω v w := by
  constructor
  · intro h
    rw [← mem_cluster_iff, h]
    exact cluster_mem_self ω w
  · intro h
    apply Set.Subset.antisymm <;> intro x hx
    · exact mem_cluster_iff.mpr (h.symm.trans (mem_cluster_iff.mp hx))
    · exact mem_cluster_iff.mpr (h.trans (mem_cluster_iff.mp hx))

theorem connects_refl (ω : Config V) (v : V) : Connects ω v v :=
  SimpleGraph.Reachable.refl v

theorem connects_symm {ω : Config V} {v w : V} (h : Connects ω v w) : Connects ω w v :=
  SimpleGraph.Reachable.symm h

theorem connects_trans {ω : Config V} {u v w : V} (h₁ : Connects ω u v) (h₂ : Connects ω v w) :
    Connects ω u w :=
  SimpleGraph.Reachable.trans h₁ h₂

/-! ### Connectivity as an explicit walk of open edges -/

/-- `PathConnects ω v w`: there is a walk from `v` to `w` in the *complete* graph all of
whose edges are open in `ω`.  The witness type does not depend on `ω`, which is what makes
the connection event measurable. -/
def PathConnects (ω : Config V) (v w : V) : Prop :=
  ∃ p : (⊤ : SimpleGraph V).Walk v w, ∀ e ∈ p.edges, e ∈ ω

theorem exists_walk_top_of_walk {ω : Config V} :
    ∀ {v w : V} (p : (openGraph ω).Walk v w),
      ∃ q : (⊤ : SimpleGraph V).Walk v w, q.edges = p.edges
  | _, _, .nil => ⟨.nil, rfl⟩
  | _, _, .cons h p' => by
      obtain ⟨q, hq⟩ := exists_walk_top_of_walk p'
      refine ⟨.cons ?_ q, ?_⟩
      · rw [SimpleGraph.top_adj]
        exact (openGraph_adj.1 h).1
      · simp [SimpleGraph.Walk.edges_cons, hq]

theorem exists_walk_openGraph_of_walk_top {ω : Config V} :
    ∀ {v w : V} (p : (⊤ : SimpleGraph V).Walk v w), (∀ e ∈ p.edges, e ∈ ω) →
      ∃ q : (openGraph ω).Walk v w, q.edges = p.edges
  | _, _, .nil, _ => ⟨.nil, rfl⟩
  | _, _, .cons h p', hω => by
      obtain ⟨q, hq⟩ := exists_walk_openGraph_of_walk_top p'
        (fun e he => hω e (by simp [SimpleGraph.Walk.edges_cons, he]))
      refine ⟨.cons ?_ q, ?_⟩
      · rw [openGraph_adj]
        exact ⟨(SimpleGraph.top_adj _ _).1 h, hω _ (by simp [SimpleGraph.Walk.edges_cons])⟩
      · simp [SimpleGraph.Walk.edges_cons, hq]

theorem edgeSet_openGraph_subset {ω : Config V} : (openGraph ω).edgeSet ⊆ ω := by
  rintro ⟨x, y⟩ he
  rw [SimpleGraph.mem_edgeSet, openGraph_adj] at he
  exact he.2

theorem pathConnects_iff {ω : Config V} {v w : V} : PathConnects ω v w ↔ Connects ω v w := by
  constructor
  · rintro ⟨p, hp⟩
    obtain ⟨q, -⟩ := exists_walk_openGraph_of_walk_top p hp
    exact q.reachable
  · intro h
    obtain ⟨p⟩ := h
    obtain ⟨q, hq⟩ := exists_walk_top_of_walk p
    refine ⟨q, fun e he => ?_⟩
    have he' : e ∈ p.edges := by rw [← hq]; exact he
    exact edgeSet_openGraph_subset (p.edges_subset_edgeSet he')

/-! ### Monotonicity of connection events -/

theorem connects_mono {ω ω' : Config V} (h : ∀ e, e ∈ ω → e ∈ ω') {v w : V}
    (hv : Connects ω v w) : Connects ω' v w := by
  rw [← pathConnects_iff] at hv ⊢
  obtain ⟨p, hp⟩ := hv
  exact ⟨p, fun e he => h e (hp e he)⟩

theorem cluster_mono {ω ω' : Config V} (h : ∀ e, e ∈ ω → e ∈ ω') (v : V) :
    cluster ω v ⊆ cluster ω' v := by
  intro w hw
  rw [mem_cluster_iff] at hw ⊢
  exact connects_mono h hw

theorem isIncreasing_connects (v w : V) : IsIncreasing {ω : Config V | Connects ω v w} :=
  fun _ _ h hv => connects_mono h hv

theorem isIncreasing_cluster_mem (v w : V) : IsIncreasing {ω : Config V | w ∈ cluster ω v} :=
  fun _ _ h hv => cluster_mono h v hv

/-! ### Measurability of connectivity and of clusters -/

theorem measurableSet_allOpen (s : Finset (Sym2 V)) :
    MeasurableSet {ω : Config V | ∀ e ∈ s, e ∈ ω} := by
  classical
  induction s using Finset.induction with
  | empty => simp
  | insert a s ha ih =>
    have h : {ω : Config V | ∀ e ∈ insert a s, e ∈ ω}
        = {ω : Config V | a ∈ ω} ∩ {ω : Config V | ∀ e ∈ s, e ∈ ω} := by
      ext ω; simp [Finset.forall_mem_insert]
    rw [h]
    exact (measurableSet_mem a).inter ih

theorem measurableSet_pathConnects (v w : V) :
    MeasurableSet {ω : Config V | PathConnects ω v w} := by
  classical
  have h : {ω : Config V | PathConnects ω v w} = ⋃ (s : Finset (Sym2 V)),
      {ω : Config V | (∃ p : (⊤ : SimpleGraph V).Walk v w, p.edges.toFinset = s) ∧
        ∀ e ∈ s, e ∈ ω} := by
    ext ω
    simp only [Set.mem_ofPred_eq, Set.mem_iUnion]
    constructor
    · rintro ⟨p, hp⟩
      exact ⟨p.edges.toFinset, ⟨p, rfl⟩, fun e he => hp e (by simpa using he)⟩
    · rintro ⟨s, ⟨p, rfl⟩, hs⟩
      exact ⟨p, fun e he => hs e (by simpa using he)⟩
  rw [h]
  refine MeasurableSet.iUnion fun s => ?_
  by_cases hex : ∃ p : (⊤ : SimpleGraph V).Walk v w, p.edges.toFinset = s
  · rw [show {ω : Config V | (∃ p : (⊤ : SimpleGraph V).Walk v w, p.edges.toFinset = s) ∧
        ∀ e ∈ s, e ∈ ω} = {ω : Config V | ∀ e ∈ s, e ∈ ω} from by ext ω; simp [hex]]
    exact measurableSet_allOpen s
  · rw [show {ω : Config V | (∃ p : (⊤ : SimpleGraph V).Walk v w, p.edges.toFinset = s) ∧
        ∀ e ∈ s, e ∈ ω} = (∅ : Set (Config V)) from by ext ω; simp [hex]]
    exact MeasurableSet.empty

theorem measurableSet_connects (v w : V) :
    MeasurableSet {ω : Config V | Connects ω v w} := by
  rw [show {ω : Config V | Connects ω v w} = {ω : Config V | PathConnects ω v w} from
    Set.ext fun ω => (pathConnects_iff).symm]
  exact measurableSet_pathConnects v w

/-- **The cluster of a vertex is a measurable event.** -/
theorem measurableSet_cluster_mem (v w : V) :
    MeasurableSet {ω : Config V | w ∈ cluster ω v} := by
  rw [show {ω : Config V | w ∈ cluster ω v} = {ω : Config V | Connects ω v w} from
    Set.ext fun ω => mem_cluster_iff]
  exact measurableSet_connects v w

/-! ## The cluster volume `|K_v|` as a cardinality

The paper's `|K|` is the number of vertices in the cluster, an extended natural.  We define
it as an `ℝ≥0∞`-valued sum of indicators (which is manifestly measurable, and is the form
used for the moment computations) and prove it equals the `ℝ≥0∞`-cardinality of the
cluster.  Hence `|K_v| = ⊤ ↔ K_v` is infinite, which is the paper's "infinite cluster". -/

/-- The volume `|K_v|` of the cluster of `v`. -/
noncomputable abbrev clusterVol (ω : Config V) (v : V) : ℝ≥0∞ :=
  ((PercLib.Percolation.Bond.cluster ω v).encard : ℝ≥0∞)

theorem clusterVol_eq_tsum (ω : Config V) (v : V) : clusterVol ω v =
    ∑' w : V, (cluster ω v).indicator (fun _ => (1 : ℝ≥0∞)) w := by
  have h : ∀ w : V, (cluster ω v).indicator (fun _ => (1 : ℝ≥0∞)) w =
      (PercLib.Percolation.Bond.conn v w).indicator (fun _ => (1 : ℝ≥0∞)) ω := by
    intro w
    by_cases hc : ω ∈ PercLib.Percolation.Bond.conn v w
    · have hw : w ∈ cluster ω v := mem_cluster_iff.mpr
        ((PercLib.Percolation.Bond.mem_conn_iff ω v w).mp hc)
      rw [Set.indicator_of_mem hw, Set.indicator_of_mem hc]
    · have hw : w ∉ cluster ω v := fun hw => hc
        ((PercLib.Percolation.Bond.mem_conn_iff ω v w).mpr (mem_cluster_iff.mp hw))
      rw [Set.indicator_of_notMem hw, Set.indicator_of_notMem hc]
  simp_rw [h]
  exact PercLib.Percolation.Bond.encard_cluster_eq_tsum ω v

/-- For a finite set, the `ℝ≥0∞`-cardinality is the `ℝ≥0∞`-coercion of the `ncard`. -/
theorem encard_coe_eq_ncard_coe {s : Set V} (hs : s.Finite) :
    (s.encard : ℝ≥0∞) = (s.ncard : ℝ≥0∞) := by
  rw [← hs.coe_toFinset]
  norm_cast

/-- The `ℝ≥0∞`-valued sum of the indicators of a set is its `ℝ≥0∞`-cardinality. -/
theorem tsum_indicator_eq_encard (s : Set V) :
    (∑' w : V, s.indicator (fun _ => (1 : ℝ≥0∞)) w) = (s.encard : ℝ≥0∞) := by
  classical
  rw [ENNReal.tsum_eq_iSup_sum]
  have hterm : ∀ t : Finset V,
      (∑ w ∈ t, s.indicator (fun _ => (1 : ℝ≥0∞)) w) = ((t.filter (· ∈ s)).card : ℝ≥0∞) := by
    intro t
    have h1 : ∀ w, s.indicator (fun _ => (1 : ℝ≥0∞)) w = if w ∈ s then 1 else 0 := by
      intro w; by_cases hw : w ∈ s <;> simp [Set.indicator_apply, hw]
    simp only [h1]
    rw [Finset.sum_boole]
  simp only [hterm]
  by_cases hs : s.Finite
  · have hle : ∀ t : Finset V, ((t.filter (· ∈ s)).card : ℝ≥0∞) ≤ (s.encard : ℝ≥0∞) := by
      intro t
      have hsub : ((t.filter (· ∈ s) : Finset V) : Set V) ⊆ s := by
        intro x hx
        exact (Finset.mem_filter.1 (Finset.mem_coe.1 hx)).2
      have hF : (((t.filter (· ∈ s) : Finset V) : Set V).encard : ℝ≥0∞)
          = ((t.filter (· ∈ s)).card : ℝ≥0∞) := by
        rw [encard_coe_eq_ncard_coe (Finset.finite_toSet _), Set.ncard_coe_finset]
      rw [← hF]
      exact_mod_cast Set.encard_le_encard hsub
    refine le_antisymm (iSup_le hle) ?_
    have h1 : ((hs.toFinset.filter (· ∈ s)).card : ℝ≥0∞) = (s.encard : ℝ≥0∞) := by
      have hfilter : hs.toFinset.filter (· ∈ s) = hs.toFinset := by
        ext x
        simp only [Finset.mem_filter]
        exact ⟨fun h => h.1, fun hx => ⟨hx, by rw [← hs.coe_toFinset]; exact hx⟩⟩
      have h2 : (s.encard : ℝ≥0∞) = ((hs.toFinset).card : ℝ≥0∞) := by
        have he : (s.encard : ℝ≥0∞) = (((hs.toFinset : Finset V) : Set V).encard : ℝ≥0∞) := by
          rw [hs.coe_toFinset]
        rw [he, encard_coe_eq_ncard_coe (Finset.finite_toSet _), Set.ncard_coe_finset]
      rw [hfilter, h2]
    exact le_iSup_of_le hs.toFinset (le_of_eq h1.symm)
  · have hmem : s.Infinite := hs
    have hnat : ∀ n : ℕ, (n : ℝ≥0∞) ≤ ⨆ t : Finset V, ((t.filter (· ∈ s)).card : ℝ≥0∞) := by
      intro n
      obtain ⟨t, ht, hcard⟩ := hmem.exists_subset_card_eq n
      have hfil : t.filter (· ∈ s) = t := by
        refine Finset.filter_true_of_mem fun x hx => ?_
        exact ht (Finset.mem_coe.1 hx)
      have hb : (n : ℝ≥0∞) = ((t.filter (· ∈ s)).card : ℝ≥0∞) := by rw [hfil, hcard]
      rw [hb]
      exact le_iSup (fun u : Finset V => ((u.filter (· ∈ s)).card : ℝ≥0∞)) t
    have htop : (s.encard : ℝ≥0∞) = ⊤ := by
      rw [Set.encard_eq_top_iff.mpr hmem]
      simp
    have hsup : (⨆ t : Finset V, ((t.filter (· ∈ s)).card : ℝ≥0∞)) = ⊤ := by
      refine le_antisymm le_top ?_
      rw [← ENNReal.iSup_natCast]
      exact iSup_le hnat
    rw [htop, hsup]

theorem clusterVol_eq_encard (ω : Config V) (v : V) :
    clusterVol ω v = ((cluster ω v).encard : ℝ≥0∞) := rfl

/-- **`v` lies in an infinite cluster** (paper §I.1.2: `|K_v| = ∞`). -/
def InInfiniteCluster (ω : Config V) (v : V) : Prop := clusterVol ω v = ⊤

/-- **The genuine infinite-cluster condition**: the cluster of `v` is an infinite set of
vertices.  This is the form used everywhere below and by the rest of the campaign. -/
theorem inInfiniteCluster_iff_infinite (ω : Config V) (v : V) :
    InInfiniteCluster ω v ↔ (cluster ω v).Infinite := by
  rw [InInfiniteCluster, clusterVol_eq_encard]
  have h : ((cluster ω v).encard : ℝ≥0∞) = ⊤ ↔ (cluster ω v).encard = ⊤ := by simp
  rw [h, Set.encard_eq_top_iff]

/-- `v` lies in an infinite cluster iff for every `n` there are `n` distinct vertices
connected to `v`. -/
theorem inInfiniteCluster_iff_finset (ω : Config V) (v : V) :
    InInfiniteCluster ω v ↔ ∀ n : ℕ, ∃ t : Finset V, t.card = n ∧ ∀ x ∈ t, Connects ω v x := by
  rw [inInfiniteCluster_iff_infinite]
  constructor
  · intro h n
    obtain ⟨t, ht, hcard⟩ := h.exists_subset_card_eq n
    exact ⟨t, hcard, fun x hx => by
      rw [← mem_cluster_iff]; exact ht (Finset.mem_coe.1 hx)⟩
  · intro h
    by_contra hfin
    have hf : (cluster ω v).Finite := Set.not_infinite.1 hfin
    obtain ⟨t, htcard, ht⟩ := h (hf.toFinset.card + 1)
    have hsub : (t : Set V) ⊆ cluster ω v := fun x hx => by
      rw [mem_cluster_iff]; exact ht x (Finset.mem_coe.1 hx)
    have h1 : t.card ≤ hf.toFinset.card := by
      rw [← Set.ncard_eq_toFinset_card _ hf, ← Set.ncard_coe_finset t]
      exact Set.ncard_le_ncard hsub hf
    omega

theorem measurable_clusterVol (v : V) : Measurable fun ω : Config V => clusterVol ω v := by
  have h : (fun ω : Config V => clusterVol ω v) =
      fun ω => ∑' w : V, (cluster ω v).indicator (fun _ => (1 : ℝ≥0∞)) w := by
    funext ω; exact clusterVol_eq_tsum ω v
  rw [h]
  refine Measurable.tsum fun w => ?_
  exact Measurable.indicator measurable_const (measurableSet_cluster_mem v w)

theorem measurableSet_inInfiniteCluster (v : V) :
    MeasurableSet {ω : Config V | InInfiniteCluster ω v} :=
  measurable_clusterVol v (measurableSet_singleton ⊤)

/-- Measurability of the infinite-cluster event directly from its `Finset` form. -/
theorem measurableSet_inInfiniteCluster' (v : V) :
    MeasurableSet {ω : Config V | InInfiniteCluster ω v} := by
  classical
  have h : {ω : Config V | InInfiniteCluster ω v} =
      ⋂ n : ℕ, ⋃ t : {t : Finset V // t.card = n},
        ⋂ x ∈ (t : Finset V), {ω : Config V | Connects ω v x} := by
    ext ω
    simp only [Set.mem_ofPred_eq, Set.mem_iInter, Set.mem_iUnion]
    rw [inInfiniteCluster_iff_finset]
    constructor
    · rintro h n
      obtain ⟨t, hc, hx⟩ := h n
      exact ⟨⟨t, hc⟩, fun x hxt => hx x hxt⟩
    · rintro h n
      obtain ⟨⟨t, hc⟩, hx⟩ := h n
      exact ⟨t, hc, fun x hxt => hx x hxt⟩
  rw [h]
  refine MeasurableSet.iInter fun n => ?_
  refine MeasurableSet.iUnion fun t => ?_
  exact MeasurableSet.biInter (t.1.countable_toSet) fun x _ => measurableSet_connects v x

theorem isIncreasing_inInfiniteCluster (v : V) :
    IsIncreasing {ω : Config V | InInfiniteCluster ω v} := by
  intro ω ω' h hω
  have h1 : InInfiniteCluster ω v := hω
  have h2 : InInfiniteCluster ω' v := by
    rw [inInfiniteCluster_iff_infinite] at h1 ⊢
    exact h1.mono (cluster_mono h v)
  exact h2

/-- **"There exists an infinite cluster"** (paper §I.1.2), the event whose probability is
required to be one in the definition of `β_c`. -/
def existsInfiniteClusterEvent (V : Type*) [Countable V] : Set (Config V) :=
  {ω | ∃ v, InInfiniteCluster ω v}

theorem mem_existsInfiniteClusterEvent {ω : Config V} :
    ω ∈ existsInfiniteClusterEvent V ↔ ∃ v, InInfiniteCluster ω v := Iff.rfl

theorem measurableSet_existsInfiniteCluster :
    MeasurableSet (existsInfiniteClusterEvent V) := by
  rw [show existsInfiniteClusterEvent V = ⋃ v, {ω : Config V | InInfiniteCluster ω v} from
    Set.ext fun ω => by simp [existsInfiniteClusterEvent]]
  exact MeasurableSet.iUnion fun v => measurableSet_inInfiniteCluster v

theorem isIncreasing_existsInfiniteCluster :
    IsIncreasing (existsInfiniteClusterEvent V) := by
  intro ω ω' h hω
  obtain ⟨v, hv⟩ := hω
  exact ⟨v, isIncreasing_inInfiniteCluster v h hv⟩

/-- The **percolation probability** `θ_π(v) = P_π(|K_v| = ∞)`. -/
noncomputable def percolationProb (π : Sym2 V → unitInterval) (v : V) : ℝ≥0∞ :=
  edgeMeasure π {ω : Config V | InInfiniteCluster ω v}

theorem percolationProb_le_one (π : Sym2 V → unitInterval) (v : V) :
    percolationProb π v ≤ 1 := by
  rw [percolationProb, ← measure_univ (μ := edgeMeasure π)]
  exact measure_mono (Set.subset_univ _)

/-- The probability that an infinite cluster exists. -/
noncomputable def percolationEventProb (π : Sym2 V → unitInterval) : ℝ≥0∞ :=
  edgeMeasure π (existsInfiniteClusterEvent V)

theorem percolationProb_le_percolationEventProb (π : Sym2 V → unitInterval) (v : V) :
    percolationProb π v ≤ percolationEventProb π := by
  refine measure_mono ?_
  intro ω hω
  exact ⟨v, hω⟩

/-! ### The empty configuration -/

theorem openGraph_empty : openGraph (∅ : Config V) = (⊥ : SimpleGraph V) :=
  PercLib.Percolation.Bond.openGraph_empty

theorem connects_empty_iff {v w : V} : Connects (∅ : Config V) v w ↔ v = w :=
  PercLib.Percolation.Bond.empty_mem_conn_iff v w

theorem cluster_empty (v : V) : cluster (∅ : Config V) v = {v} := by
  ext w
  rw [mem_cluster_iff, connects_empty_iff, Set.mem_singleton_iff, eq_comm]

theorem not_inInfiniteCluster_empty (v : V) : ¬ InInfiniteCluster (∅ : Config V) v := by
  rw [inInfiniteCluster_iff_infinite, cluster_empty]
  exact Set.not_infinite.mpr (Set.finite_singleton v)

/-- With all edges open the cluster of every vertex is the whole vertex set. -/
theorem cluster_univ (v : V) : cluster (Set.univ : Config V) v = Set.univ := by
  ext w
  rw [mem_cluster_iff]
  constructor
  · intro _; exact Set.mem_univ w
  · intro _
    by_cases h : w = v
    · subst h; exact connects_refl _ _
    · exact SimpleGraph.Adj.reachable (by rw [openGraph_adj]; exact ⟨Ne.symm h, Set.mem_univ _⟩)

/-- The complete configuration has an infinite cluster as soon as `V` is infinite; this shows
that `InInfiniteCluster` is not vacuous. -/
theorem inInfiniteCluster_univ [Infinite V] (v : V) :
    InInfiniteCluster (Set.univ : Config V) v := by
  rw [inInfiniteCluster_iff_infinite, cluster_univ]
  exact Set.infinite_univ


end Cluster

end PercLib.CriticalLRP
