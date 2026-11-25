/-
Migration source: https://github.com/yujinhkim/Critical-Long-range-percolation
Integration revision: 3b3d1d0e43ef940bfaa2292ee5c2ee094ac4edbf
Licence: Apache-2.0 for the PercLib Lean sources and tooling; see third_party/critical-lrp/.
External provenance and modifications are recorded in the file-specific notices below.
-/

/-
# Level sets of the cluster volume in the canonical model, and their two-cluster BK bound

Source: Tom Hutchcroft, *Critical long-range percolation I: High effective dimension*,
arXiv:2508.18807v1, Lemma I.2.1 (p. 21).  The lemma is stated for increasing non-negative
functions `F`, `G` of the clusters `K_x`, `K_y`.  The paper's applications (e.g. (I.4.16), the
proof of Proposition I.4.15) use functionals of the cluster *volume*, so the relevant level sets are

  `{|K_x| ≥ n} = {ω | there are n distinct vertices connected to x}`,

which are increasing and finitely witnessed (`clusterCardLarge`).  Their intersection over `n` is
the infinite-cluster event, which is *not* finitely witnessed.

This file provides those events on the canonical model and the corresponding indicator form of
Lemma I.2.1(i) for every edge-dependent percolation law, in particular for `P_β`.

No `sorry`, no custom axioms.
-/
module

public import PercLib.CriticalLRP.BK.CanonicalBridge
public import PercLib.CriticalLRP.BK.BKApprox

set_option autoImplicit true

set_option linter.unusedSectionVars false

@[expose] public section

open MeasureTheory Measure ProbabilityTheory unitInterval Filter
open scoped ENNReal NNReal Topology

namespace PercLib.CriticalLRP

attribute [local instance] Classical.propDecidable

variable {V : Type*} [Countable V]

/-- **`{|K_x| ≥ n}`**: at least `n` vertices are connected to `x`. -/
def clusterCardLarge (x : V) (n : ℕ) : Set (Config V) :=
  {ω | ∃ t : Finset V, n ≤ t.card ∧ ∀ y ∈ t, Connects ω x y}

theorem clusterCardLarge_eq_percolation (x : V) (n : ℕ) :
    clusterCardLarge x n = Percolation.clusterLarge (idBondGraph V) x n := by
  ext ω
  constructor
  · rintro ⟨t, ht, hc⟩
    exact ⟨t, ht, fun y hy => (conn_idBondGraph_iff ω x y).mpr (hc y hy)⟩
  · rintro ⟨t, ht, hc⟩
    exact ⟨t, ht, fun y hy => (conn_idBondGraph_iff ω x y).mp (hc y hy)⟩

theorem clusterCardLarge_upper (x : V) (n : ℕ) : IsUpperSet (clusterCardLarge x n) := by
  rintro ω ω' h ⟨t, ht, hc⟩
  exact ⟨t, ht, fun y hy => connects_mono (fun e he => h he) (hc y hy)⟩

theorem finiteWitness_clusterCardLarge (x : V) (n : ℕ) :
    Percolation.FiniteWitness (clusterCardLarge x n) := by
  rw [clusterCardLarge_eq_percolation]
  exact Percolation.finiteWitness_clusterLarge (idBondGraph V) x n

theorem measurableSet_clusterCardLarge (x : V) (n : ℕ) :
    MeasurableSet (clusterCardLarge x n) :=
  Percolation.measurableSet_finiteWitness _ (clusterCardLarge_upper x n)
    (finiteWitness_clusterCardLarge x n)

theorem clusterCardLarge_antitone (x : V) : Antitone (clusterCardLarge x) := by
  intro m n hmn ω ⟨t, ht, hc⟩
  exact ⟨t, le_trans hmn ht, hc⟩

/-- `{|K_x| ≥ n}` is determined by the cluster of `x`. -/
theorem clusterEvent_clusterCardLarge (x : V) (n : ℕ) : ClusterEvent x (clusterCardLarge x n) := by
  intro ω ω' h
  have hc : ∀ y, Connects ω x y ↔ Connects ω' x y := by
    intro y
    rw [← mem_cluster_iff, ← mem_cluster_iff, h]
  constructor
  · rintro ⟨t, ht, hconn⟩
    exact ⟨t, ht, fun y hy => (hc y).mp (hconn y hy)⟩
  · rintro ⟨t, ht, hconn⟩
    exact ⟨t, ht, fun y hy => (hc y).mpr (hconn y hy)⟩

/-- The infinite cluster event is the intersection of the level sets `{|K_x| ≥ n}`. -/
theorem clusterInfinite_eq_iInter (x : V) :
    {ω : Config V | (cluster ω x).Infinite} = ⋂ n, clusterCardLarge x n := by
  ext ω
  simp only [Set.mem_iInter, Set.mem_ofPred_eq, clusterCardLarge]
  constructor
  · intro h n
    obtain ⟨t, ht, hcard⟩ := h.exists_subset_card_eq n
    exact ⟨t, hcard.ge, fun y hy => mem_cluster_iff.mp (ht (Finset.mem_coe.1 hy))⟩
  · intro h hfin
    obtain ⟨t, ht, hc⟩ := h (hfin.toFinset.card + 1)
    have hsub : t ⊆ hfin.toFinset := fun y hy => hfin.mem_toFinset.mpr (mem_cluster_iff.mpr (hc y hy))
    have := Finset.card_le_card hsub
    omega

/-- **Lemma I.2.1(i) for cluster volumes**: the indicator form of the two-cluster inequality for
the level sets `{|K_x| ≥ n}`, `{|K_y| ≥ m}`. -/
theorem edgeMeasure_twoCluster_card (π : Sym2 V → unitInterval) (hπ : ∀ e, π e < 1)
    (x y : V) (n m : ℕ) :
    (edgeMeasure π).real (clusterCardLarge x n ∩ clusterCardLarge y m ∩
        {ω | ¬ Connects ω x y}) ≤
      (edgeMeasure π).real (clusterCardLarge x n) * (edgeMeasure π).real (clusterCardLarge y m) :=
  edgeMeasure_twoCluster_bk π hπ x y _ _ (clusterCardLarge_upper x n)
    (finiteWitness_clusterCardLarge x n) (clusterEvent_clusterCardLarge x n)
    (clusterCardLarge_upper y m) (finiteWitness_clusterCardLarge y m)
    (clusterEvent_clusterCardLarge y m)

/-- Lemma I.2.1(i) for cluster volumes, for the paper's law `P_β` at every `β ≥ 0`. -/
theorem longRangeMeasure_twoCluster_card {J : Sym2 V → ℝ} (hJ : ∀ e, 0 ≤ J e) (β : NNReal)
    (x y : V) (n m : ℕ) :
    (longRangeMeasure J hJ β).real (clusterCardLarge x n ∩ clusterCardLarge y m ∩
        {ω | ¬ Connects ω x y}) ≤
      (longRangeMeasure J hJ β).real (clusterCardLarge x n) *
        (longRangeMeasure J hJ β).real (clusterCardLarge y m) :=
  edgeMeasure_twoCluster_card _ (fun e => bernoulliEdgeProb_lt_one hJ β e) x y n m

/-- The complementary form of the two-cluster inequality used in (I.4.16): with
`1(x ↮ y) = 1 - 1(x ↔ y)`, the *lower* bound on the correlation. -/
theorem longRangeMeasure_twoCluster_card_ge {J : Sym2 V → ℝ} (hJ : ∀ e, 0 ≤ J e) (β : NNReal)
    (x y : V) (n m : ℕ) :
    (longRangeMeasure J hJ β).real (clusterCardLarge x n) *
        (longRangeMeasure J hJ β).real (clusterCardLarge y m) -
      (longRangeMeasure J hJ β).real (clusterCardLarge x n ∩ clusterCardLarge y m ∩
        {ω | Connects ω x y}) ≤
      (longRangeMeasure J hJ β).real (clusterCardLarge x n ∩ clusterCardLarge y m ∩
        {ω | ¬ Connects ω x y}) := by
  have h := edgeMeasure_twoCluster_middle (bernoulliEdgeProb J hJ β)
    (fun e => bernoulliEdgeProb_lt_one hJ β e) x y (clusterCardLarge x n) (clusterCardLarge y m)
    (clusterCardLarge_upper x n) (finiteWitness_clusterCardLarge x n)
    (clusterCardLarge_upper y m) (finiteWitness_clusterCardLarge y m)
  exact h

end PercLib.CriticalLRP
