/-
Migration source: https://github.com/yujinhkim/Critical-Long-range-percolation
Integration revision: 3b3d1d0e43ef940bfaa2292ee5c2ee094ac4edbf
Licence: Apache-2.0 for the PercLib Lean sources and tooling; see third_party/critical-lrp/.
External provenance and modifications are recorded in the file-specific notices below.
-/

/-
Bridge from native `PercLib` bond percolation to the migrated long-range vocabulary.

The imported native definitions and proofs are in
`PercLib/Percolation/Bond/Basic.lean`, `PercLib/Percolation/Bond/ClusterTails.lean`,
and the corresponding `PercLib/Probability` modules. Their source, revision and
licensing notices are retained in those modules and in `third_party/`. No obsolete
vendored PercLib snapshot, source notes or wiki prose is copied in this migration.

The migrated canonical configuration, law and cluster are native definitions through
compatibility abbreviations, with explicit identities below. The `PercLib` cluster-tail
statements can therefore be used in the paper's vocabulary, and the paper's
`{|K_v ∩ Λ| ≥ k}` events
inherit the `PercLib` finite-open-witness machinery:

* `edgeMeasure_eq_law` — `edgeMeasure π` is exactly `PercLib.Percolation.Bond.law π`
  (the definitions differ only by a `Measure.comap` along the identity).
* `mem_conn_iff`, `cluster_eq_perclib` — identical open graphs, connections and clusters.
* `clusterTail_iff_perclib` — the two spellings of `{|K_v ∩ Λ| ≥ k}` agree.
* `measurableSet_clusterTail` — the event is measurable on a countable vertex set.
* `clusterTail_iff_exists_finset`, `exists_finset_of_clusterTail` — a finite open-edge
  witness: the event holds iff `k` vertices of `Λ` are joined to `v`, and if it holds in `ω`
  it already holds in some finite `F ⊆ ω`.
* `isUpperSet_clusterTail`, `monotone_clusterTail_restrict` — the event is increasing, and
  restricting configurations to increasing finite edge sets gives a monotone family.
* `clusterTail_eq_iUnion_restrict`, `edgeMeasure_clusterTail_eq_iSup` — the event is the
  union of its restrictions to any increasing exhaustive sequence of finite edge sets, and
  its probability is the supremum of the restricted probabilities.
* `tendsto_edgeMeasure_clusterTail` — those probabilities converge to it.
* `edgeMeasure_clusterTail_le_of_truncation` — a uniform bound on every finite truncation
  bounds the full tail probability: the transfer principle for mass/tail bounds.
* `clusterTail_eq_biUnion`, `edgeMeasure_clusterTail_le_sum` — the event is a finite union
  of intersections of connection events, giving the `k`-subset union bound.

No `sorry`, no custom axioms.
-/
module

public import PercLib.Percolation.Bond.ClusterTails
public import PercLib.CriticalLRP.CountableProduct.Base

set_option linter.unusedSectionVars false
set_option linter.unusedSimpArgs false
set_option linter.unnecessarySimpa false
set_option linter.unusedTactic false
set_option linter.unusedVariables false

set_option autoImplicit true

@[expose] public section

open MeasureTheory Set
open scoped ENNReal

namespace PercLib.CriticalLRP

/-! ## The two spellings of the model -/

/-- **The laws agree.** The migrated `edgeMeasure` is a compatibility abbreviation for
native `PercLib` bond law, rather than a separately defined product measure. -/
theorem edgeMeasure_eq_law (π : Sym2 V → unitInterval) :
    edgeMeasure π = PercLib.Percolation.Bond.law π := rfl

variable {V : Type*}

/-- `PercLib`'s `conn` event is this repository's `Connects`: both are reachability in
`SimpleGraph.fromEdgeSet ω`. -/
theorem mem_conn_iff (ω : Config V) (v w : V) :
    ω ∈ PercLib.Percolation.Bond.conn v w ↔ Connects ω v w :=
  Iff.rfl

variable [Countable V]

/-- The migrated canonical cluster is the native `PercLib` cluster via its compatibility
abbreviation. -/
theorem cluster_eq_perclib (ω : Config V) (v : V) :
    PercLib.Percolation.Bond.cluster ω v = cluster ω v := rfl

/-- The two spellings of the cluster-tail event `{|K_v ∩ Λ| ≥ k}` agree. -/
theorem clusterTail_iff_perclib (ω : Config V) (v : V) (Λ : Finset V) (k : ℕ) :
    (k ≤ (cluster ω v ∩ (Λ : Set V)).ncard) ↔
      k ≤ (PercLib.Percolation.Bond.cluster ω v ∩ (Λ : Set V)).ncard := by
  rw [cluster_eq_perclib]

/-- Set form of `clusterTail_iff_perclib`, for the event itself rather than a configuration. -/
theorem clusterTail_eq_perclib (v : V) (Λ : Finset V) (k : ℕ) :
    {ω : Config V | k ≤ (cluster ω v ∩ (Λ : Set V)).ncard}
      = {ω : Config V | k ≤ (PercLib.Percolation.Bond.cluster ω v ∩ (Λ : Set V)).ncard} := by
  ext ω
  exact clusterTail_iff_perclib ω v Λ k

/-! ## Transport of the `PercLib` cluster-tail API -/

/-- The cluster-tail event is measurable.  (Transported from
`PercLib.Percolation.Bond.measurableSet_cluster_tail`: the event is a countable union of
finite intersections of connection events.) -/
theorem measurableSet_clusterTail (v : V) (Λ : Finset V) (k : ℕ) :
    MeasurableSet {ω : Config V | k ≤ (cluster ω v ∩ (Λ : Set V)).ncard} := by
  rw [clusterTail_eq_perclib]
  exact PercLib.Percolation.Bond.measurableSet_cluster_tail v Λ k

/-- **Finite positive witness.**  `{|K_v ∩ Λ| ≥ k}` holds iff `k` distinct vertices of `Λ`
are joined to `v`.  (Transported from
`PercLib.Percolation.Bond.cluster_tail_iff_exists_finset`.) -/
theorem clusterTail_iff_exists_finset (ω : Config V) (v : V) (Λ : Finset V) (k : ℕ) :
    k ≤ (cluster ω v ∩ (Λ : Set V)).ncard ↔
      ∃ S : Finset V, S ⊆ Λ ∧ S.card = k ∧ ∀ x ∈ S, Connects ω v x :=
  PercLib.Percolation.Bond.cluster_tail_iff_exists_finset ω v Λ k

/-- **Finite open-edge witness.**  If `{|K_v ∩ Λ| ≥ k}` holds in `ω`, it already holds in some
finite set of open edges `F ⊆ ω`.  This is the hypothesis of the finite-witness Harris
inequality, and it is what makes the event visible to a finite model.
(Transported from `PercLib.Percolation.Bond.exists_finset_of_cluster_tail`.) -/
theorem exists_finset_of_clusterTail {ω : Config V} (v : V) (Λ : Finset V) (k : ℕ)
    (h : k ≤ (cluster ω v ∩ (Λ : Set V)).ncard) :
    ∃ F : Finset (Sym2 V), (F : Config V) ⊆ ω ∧
      k ≤ (cluster (F : Config V) v ∩ (Λ : Set V)).ncard := by
  obtain ⟨F, hF, hc⟩ := PercLib.Percolation.Bond.exists_finset_of_cluster_tail v Λ k
    ((clusterTail_iff_perclib ω v Λ k).mp h)
  exact ⟨F, hF, (clusterTail_iff_perclib (F : Config V) v Λ k).mpr hc⟩

/-- The cluster-tail event is increasing in the configuration.  (Transported from
`PercLib.Percolation.Bond.isUpperSet_cluster_tail`.) -/
theorem isUpperSet_clusterTail (v : V) (Λ : Finset V) (k : ℕ) :
    IsUpperSet {ω : Config V | k ≤ (cluster ω v ∩ (Λ : Set V)).ncard} := by
  intro ω ω' h hω
  exact (clusterTail_iff_perclib ω' v Λ k).mpr
    (PercLib.Percolation.Bond.isUpperSet_cluster_tail v Λ k h
      ((clusterTail_iff_perclib ω v Λ k).mp hω))

/-- Restricting configurations to an increasing family of finite edge sets gives a monotone
family of cluster-tail events.  (The argument is that of
`PercLib.Percolation.Bond.monotone_cluster_tail_restrict`, through `isUpperSet_clusterTail`.) -/
theorem monotone_clusterTail_restrict (v : V) (Λ : Finset V) (k : ℕ)
    {E : ℕ → Finset (Sym2 V)} (hE : Monotone E) :
    Monotone fun n => {ω : Config V |
      k ≤ (cluster (ω ∩ (E n : Set (Sym2 V))) v ∩ (Λ : Set V)).ncard} := by
  intro n m hnm ω hω
  exact isUpperSet_clusterTail v Λ k (Set.inter_subset_inter_right _
    (Finset.coe_subset.mpr (hE hnm))) hω

/-- **Recovery from finite edge sets.**  For any increasing sequence `E n` of finite edge sets
that exhausts the edge set, the cluster-tail event is the union of its restrictions to `E n`.
(Transported from `PercLib.Percolation.Bond.cluster_tail_eq_iUnion_restrict`.) -/
theorem clusterTail_eq_iUnion_restrict (v : V) (Λ : Finset V) (k : ℕ)
    {E : ℕ → Finset (Sym2 V)} (hE : Monotone E) (hcover : ∀ e, ∃ n, e ∈ E n) :
    {ω : Config V | k ≤ (cluster ω v ∩ (Λ : Set V)).ncard}
      = ⋃ n, {ω : Config V |
          k ≤ (cluster (ω ∩ (E n : Set (Sym2 V))) v ∩ (Λ : Set V)).ncard} :=
  PercLib.Percolation.Bond.cluster_tail_eq_iUnion_restrict (V := V) v Λ k hE hcover

/-- **Probabilities converge along any increasing exhaustive finite-edge sequence.**
(Transported from `PercLib.Percolation.Bond.tendsto_cluster_tail_probability` through
`edgeMeasure_eq_law`.) -/
theorem tendsto_edgeMeasure_clusterTail (π : Sym2 V → unitInterval) (v : V) (Λ : Finset V)
    (k : ℕ) {E : ℕ → Finset (Sym2 V)} (hE : Monotone E) (hcover : ∀ e, ∃ n, e ∈ E n) :
    Filter.Tendsto (fun n => edgeMeasure π {ω : Config V |
        k ≤ (cluster (ω ∩ (E n : Set (Sym2 V))) v ∩ (Λ : Set V)).ncard})
      Filter.atTop
      (nhds (edgeMeasure π {ω : Config V | k ≤ (cluster ω v ∩ (Λ : Set V)).ncard})) := by
  exact PercLib.Percolation.Bond.tendsto_cluster_tail_probability (q := π) v Λ k hE hcover

/-- **Supremum form.**  The tail probability is the supremum of the truncated probabilities.
This is what lets a uniform bound on finite edge sets pass to the full event, and it is the
form in which the quantity is actually computed. -/
theorem edgeMeasure_clusterTail_eq_iSup (π : Sym2 V → unitInterval) (v : V) (Λ : Finset V)
    (k : ℕ) {E : ℕ → Finset (Sym2 V)} (hE : Monotone E) (hcover : ∀ e, ∃ n, e ∈ E n) :
    edgeMeasure π {ω : Config V | k ≤ (cluster ω v ∩ (Λ : Set V)).ncard}
      = ⨆ n, edgeMeasure π {ω : Config V |
          k ≤ (cluster (ω ∩ (E n : Set (Sym2 V))) v ∩ (Λ : Set V)).ncard} := by
  rw [clusterTail_eq_iUnion_restrict v Λ k hE hcover]
  exact (monotone_clusterTail_restrict v Λ k hE).measure_iUnion

/-- **Transfer principle for tail bounds.**  A bound that holds for every finite truncation
holds for the full cluster-tail probability. -/
theorem edgeMeasure_clusterTail_le_of_truncation (π : Sym2 V → unitInterval) (v : V)
    (Λ : Finset V) (k : ℕ) {E : ℕ → Finset (Sym2 V)} (hE : Monotone E)
    (hcover : ∀ e, ∃ n, e ∈ E n) {p : ℝ≥0∞}
    (h : ∀ n, edgeMeasure π {ω : Config V |
        k ≤ (cluster (ω ∩ (E n : Set (Sym2 V))) v ∩ (Λ : Set V)).ncard} ≤ p) :
    edgeMeasure π {ω : Config V | k ≤ (cluster ω v ∩ (Λ : Set V)).ncard} ≤ p := by
  rw [edgeMeasure_clusterTail_eq_iSup π v Λ k hE hcover]
  exact iSup_le h

/-- **The event as a finite union.**  `{|K_v ∩ Λ| ≥ k}` is the union, over the `k`-subsets
`S` of `Λ`, of the event that every vertex of `S` is joined to `v`.
(From `clusterTail_iff_exists_finset`.) -/
theorem clusterTail_eq_biUnion (v : V) (Λ : Finset V) (k : ℕ) :
    {ω : Config V | k ≤ (cluster ω v ∩ (Λ : Set V)).ncard}
      = ⋃ S ∈ Λ.powersetCard k, ⋂ x ∈ S, {ω : Config V | Connects ω v x} := by
  ext ω
  simp only [Set.mem_ofPred_eq, Set.mem_iUnion, Set.mem_iInter]
  constructor
  · intro h
    obtain ⟨S, hS, hc, hconn⟩ := (clusterTail_iff_exists_finset ω v Λ k).mp h
    exact ⟨S, Finset.mem_powersetCard.mpr ⟨hS, hc⟩, fun x hx => hconn x hx⟩
  · rintro ⟨S, hS, hconn⟩
    obtain ⟨hSΛ, hcard⟩ := Finset.mem_powersetCard.mp hS
    exact (clusterTail_iff_exists_finset ω v Λ k).mpr
      ⟨S, hSΛ, hcard, fun x hx => hconn x hx⟩

/-- **Union bound.**  The cluster-tail probability is at most the sum, over the `k`-subsets of
`Λ`, of the probability that all of `S` is connected to `v`. -/
theorem edgeMeasure_clusterTail_le_sum (π : Sym2 V → unitInterval) (v : V) (Λ : Finset V)
    (k : ℕ) :
    edgeMeasure π {ω : Config V | k ≤ (cluster ω v ∩ (Λ : Set V)).ncard}
      ≤ ∑ S ∈ Λ.powersetCard k,
          edgeMeasure π (⋂ x ∈ S, {ω : Config V | Connects ω v x}) := by
  rw [clusterTail_eq_biUnion]
  exact measure_biUnion_finset_le _ _

end PercLib.CriticalLRP
