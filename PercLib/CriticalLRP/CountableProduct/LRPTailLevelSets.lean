/-
Migration source: https://github.com/yujinhkim/Critical-Long-range-percolation
Integration revision: 3b3d1d0e43ef940bfaa2292ee5c2ee094ac4edbf
Licence: Apache-2.0 for the PercLib Lean sources and tooling; see third_party/critical-lrp/.
External provenance and modifications are recorded in the file-specific notices below.
-/

/-
The cluster-tail bridge of `Bridge.lean` applied to the paper's volume tail
`{|K_x| ≥ n}` (`clusterCardLarge`), so that the finite-cutoff bounds of `Bridge.lean` apply
to the events used in §I.2/I.4.

Source of the glue: the vendored Apache-2.0 `PercLib` subset in `ThirdParty`
(tomhutchcroft/lrp, revision 3c0755b692bb6fa71ff6521ce423948feae4fe40).  See
`ThirdParty/README.md`.  No notes or wiki material is used.

* `clusterCardLarge_eq_iUnion_finset` — `{|K_x| ≥ n}` is the union of the finite-domain tails
  `{|K_x ∩ Λ| ≥ n}` over finite vertex sets `Λ`.
* `clusterTail_mono_finset` — the finite-domain tail grows with the domain.
* `edgeMeasure_clusterCardLarge_eq_iSup` — its probability is the supremum of the
  finite-domain tail probabilities.
* `edgeMeasure_clusterCardLarge_le_of_finset` — a bound that holds in every finite vertex
  domain bounds `P(|K_x| ≥ n)`.
* `edgeMeasure_clusterCardLarge_le_of_finite` — a bound that holds in every finite vertex
  domain **and** every finite edge set bounds `P(|K_x| ≥ n)`: the fully finite cutoff
  statement, which is the form in which such bounds are proved.

No `sorry`, no custom axioms.
-/
module

public import PercLib.CriticalLRP.CountableProduct.LRPTailBounds
public import PercLib.CriticalLRP.CountableProduct.ClusterLevelSets

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

variable {V : Type*} [Countable V]

/-- **`{|K_x| ≥ n}` as a union of finite vertex domains.**  At least `n` vertices of `x`'s
cluster are connected to `x` iff some finite vertex set `Λ` contains `n` of them. -/
theorem clusterCardLarge_eq_iUnion_finset (x : V) (n : ℕ) :
    clusterCardLarge x n
      = ⋃ Λ : Finset V, {ω : Config V | n ≤ (cluster ω x ∩ (Λ : Set V)).ncard} := by
  ext ω
  rw [clusterCardLarge, Set.mem_ofPred_eq, Set.mem_iUnion]
  constructor
  · rintro ⟨t, ht, hconn⟩
    refine ⟨t, ?_⟩
    have hsub : (t : Set V) ⊆ cluster ω x ∩ (t : Set V) :=
      fun y hy => ⟨mem_cluster_iff.mpr (hconn y hy), hy⟩
    refine le_trans ht ?_
    calc t.card = (t : Set V).ncard := (Set.ncard_coe_finset t).symm
      _ ≤ (cluster ω x ∩ (t : Set V)).ncard :=
        Set.ncard_le_ncard hsub (t.finite_toSet.subset Set.inter_subset_right)
  · rintro ⟨Λ, hΛ⟩
    obtain ⟨S, -, hcard, hconn⟩ := (clusterTail_iff_exists_finset ω x Λ n).mp hΛ
    exact ⟨S, le_of_eq hcard.symm, hconn⟩

omit [Countable V] in
/-- The finite-domain tail grows with the vertex domain. -/
theorem clusterTail_mono_finset (x : V) (n : ℕ) {Λ Λ' : Finset V} (h : Λ ⊆ Λ') :
    {ω : Config V | n ≤ (cluster ω x ∩ (Λ : Set V)).ncard}
      ⊆ {ω : Config V | n ≤ (cluster ω x ∩ (Λ' : Set V)).ncard} := by
  intro ω hω
  exact le_trans hω (Set.ncard_le_ncard (Set.inter_subset_inter_right _ (Finset.coe_subset.mpr h))
    (Λ'.finite_toSet.subset Set.inter_subset_right))

/-- **Tail probability as a supremum over finite vertex domains.**  This is the form in which
`P(|K_x| ≥ n)` is computed: every finite-domain tail is a finite union (hence visible to a
finite model), and the probability of the tail is the supremum over the domains. -/
theorem edgeMeasure_clusterCardLarge_eq_iSup (π : Sym2 V → unitInterval) (x : V) (n : ℕ) :
    edgeMeasure π (clusterCardLarge x n)
      = ⨆ Λ : Finset V,
          edgeMeasure π {ω : Config V | n ≤ (cluster ω x ∩ (Λ : Set V)).ncard} := by
  classical
  have hd : Directed (· ⊆ ·) (fun Λ : Finset V =>
      {ω : Config V | n ≤ (cluster ω x ∩ (Λ : Set V)).ncard}) := by
    intro Λ₁ Λ₂
    exact ⟨Λ₁ ∪ Λ₂, clusterTail_mono_finset x n Finset.subset_union_left,
      clusterTail_mono_finset x n Finset.subset_union_right⟩
  rw [clusterCardLarge_eq_iUnion_finset]
  exact hd.measure_iUnion

/-- **Mass/tail transfer (vertex cutoffs).**  A bound that holds in every finite vertex domain
bounds the probability of `{|K_x| ≥ n}`. -/
theorem edgeMeasure_clusterCardLarge_le_of_finset (π : Sym2 V → unitInterval) (x : V) (n : ℕ)
    {p : ℝ≥0∞}
    (h : ∀ Λ : Finset V,
      edgeMeasure π {ω : Config V | n ≤ (cluster ω x ∩ (Λ : Set V)).ncard} ≤ p) :
    edgeMeasure π (clusterCardLarge x n) ≤ p := by
  rw [edgeMeasure_clusterCardLarge_eq_iSup π x n]
  exact iSup_le h

/-- **Finite edge witness for a finite domain.**  Every occurrence of `{|K_x ∩ Λ| ≥ n}` is
already an occurrence after restricting the configuration to some finite set `E` of edges: this
is `exists_finset_of_clusterTail` read as a union over finite edge sets. -/
theorem clusterTail_eq_iUnion_finset_edges (x : V) (Λ : Finset V) (n : ℕ) :
    {ω : Config V | n ≤ (cluster ω x ∩ (Λ : Set V)).ncard}
      = ⋃ E : Finset (Sym2 V),
          {ω : Config V | n ≤ (cluster (ω ∩ (E : Set (Sym2 V))) x ∩ (Λ : Set V)).ncard} := by
  ext ω
  rw [Set.mem_ofPred_eq, Set.mem_iUnion]
  constructor
  · intro hω
    obtain ⟨F, hF, hc⟩ := exists_finset_of_clusterTail x Λ n hω
    refine ⟨F, ?_⟩
    rw [Set.mem_ofPred_eq, Set.inter_eq_right.mpr hF]
    exact hc
  · rintro ⟨E, hE⟩
    exact isUpperSet_clusterTail x Λ n Set.inter_subset_left hE

/-- **Tail probability as a supremum over finite edge sets**, at a fixed vertex domain. -/
theorem edgeMeasure_clusterTail_eq_iSup_finset_edges (π : Sym2 V → unitInterval) (x : V)
    (Λ : Finset V) (n : ℕ) :
    edgeMeasure π {ω : Config V | n ≤ (cluster ω x ∩ (Λ : Set V)).ncard}
      = ⨆ E : Finset (Sym2 V),
          edgeMeasure π {ω : Config V | n ≤ (cluster (ω ∩ (E : Set (Sym2 V))) x ∩
            (Λ : Set V)).ncard} := by
  classical
  have hd : Directed (· ⊆ ·) (fun E : Finset (Sym2 V) =>
      {ω : Config V | n ≤ (cluster (ω ∩ (E : Set (Sym2 V))) x ∩ (Λ : Set V)).ncard}) := by
    intro E₁ E₂
    refine ⟨E₁ ∪ E₂, ?_, ?_⟩
    · intro ω hω
      exact isUpperSet_clusterTail x Λ n
        (Set.inter_subset_inter_right (ω : Set (Sym2 V))
          (Finset.coe_subset.mpr Finset.subset_union_left)) hω
    · intro ω hω
      exact isUpperSet_clusterTail x Λ n
        (Set.inter_subset_inter_right (ω : Set (Sym2 V))
          (Finset.coe_subset.mpr Finset.subset_union_right)) hω
  rw [clusterTail_eq_iUnion_finset_edges x Λ n]
  exact hd.measure_iUnion

/-- **Mass/tail transfer (vertex and edge cutoffs).**  A bound that holds in every finite
vertex domain and every finite edge set bounds `P(|K_x| ≥ n)`.  This is the fully finite
statement: both the domain of the cluster and the set of edges that may be open are finite,
so the hypothesis is a finite computation for each cutoff. -/
theorem edgeMeasure_clusterCardLarge_le_of_finite (π : Sym2 V → unitInterval) (x : V) (n : ℕ)
    {p : ℝ≥0∞}
    (h : ∀ (Λ : Finset V) (E : Finset (Sym2 V)),
      edgeMeasure π {ω : Config V | n ≤ (cluster (ω ∩ (E : Set (Sym2 V))) x ∩
        (Λ : Set V)).ncard} ≤ p) :
    edgeMeasure π (clusterCardLarge x n) ≤ p := by
  refine edgeMeasure_clusterCardLarge_le_of_finset π x n (fun Λ => ?_)
  rw [edgeMeasure_clusterTail_eq_iSup_finset_edges π x Λ n]
  exact iSup_le (fun E => h Λ E)

end PercLib.CriticalLRP
