/-
Migration source: https://github.com/yujinhkim/Critical-Long-range-percolation
Integration revision: 3b3d1d0e43ef940bfaa2292ee5c2ee094ac4edbf
Licence: Apache-2.0 for the PercLib Lean sources and tooling; see third_party/critical-lrp/.
External provenance and modifications are recorded in the file-specific notices below.
-/

module

public import PercLib.CriticalLRP.BK.Finite
public import PercLib.CriticalLRP.TreeGraph.ThreePoint
public import PercLib.CriticalLRP.TreeGraph.ClusterMoments
public import PercLib.CriticalLRP.TreeGraph.Extended

set_option autoImplicit true

/-!
# Discharging `LRPTree.BKIncreasing`

Member m1's tree-graph development (`LRPTree`, direction F) takes the increasing-case BK
inequality for `Fin`-indexed families of increasing events as an explicit hypothesis
`LRPTree.BKIncreasing p`.  This file **proves** that hypothesis (for edge probabilities `< 1`, which
is the case of the paper's cut-off kernels `1 - exp (-(β J_r))`) from the BK inequality of
`BKFin.lean`, on the finite edge type used there.

The bridge is the identity `prob p B = (edgeLaw p').real {ω : Set E | toFs ω ∈ B}` between the
`Finset E`-indexed finite Bernoulli law of the root project and the `Set E`-indexed product law
`edgeLaw` of `EdgeBK.lean` (for finite `E` every subset is a finset).
-/

set_option maxHeartbeats 1000000
set_option linter.unusedSectionVars false

@[expose] public section

namespace PercLib.CriticalLRP.TreeGraph

open MeasureTheory PercLib.CriticalLRP PercLib.CriticalLRP.Percolation
open scoped ENNReal NNReal

variable {V : Type*} [DecidableEq V] {E : Type*} [Fintype E] [DecidableEq E]

noncomputable section

/-- The unit-interval parameter associated with a real parameter in `[0,1]`. -/
def toI (p : E → ℝ) (hp0 : ∀ e, 0 ≤ p e) (hp1 : ∀ e, p e ≤ 1) : E → unitInterval :=
  fun e => ⟨p e, hp0 e, hp1 e⟩

theorem toI_coe (p : E → ℝ) (hp0 : ∀ e, 0 ≤ p e) (hp1 : ∀ e, p e ≤ 1) (e : E) :
    (toI p hp0 hp1 e : ℝ) = p e := rfl

/-- The finset underlying a subset of a finite type. -/
noncomputable def toFs (ω : Set E) : Finset E := by
  classical exact Finset.univ.filter (fun e => e ∈ ω)

theorem mem_toFs {ω : Set E} {e : E} : e ∈ toFs ω ↔ e ∈ ω := by
  simp [toFs]

theorem coe_toFs (ω : Set E) : (toFs ω : Set E) = ω := by
  ext e
  simp [mem_toFs]

theorem toFs_coe (s : Finset E) : toFs (s : Set E) = s := by
  ext e
  simp [mem_toFs]

theorem toFs_subset_iff {ω : Set E} {s : Finset E} : (s : Set E) ⊆ ω ↔ s ⊆ toFs ω := by
  constructor
  · intro h x hx
    rw [mem_toFs]
    exact h hx
  · intro h x hx
    rw [← mem_toFs]
    exact h hx

/-- Atom of `edgeLaw` against the finite configuration law. -/
theorem edgeLaw_real_singleton_toFs (p : E → ℝ) (hp0 : ∀ e, 0 ≤ p e) (hp1 : ∀ e, p e ≤ 1)
    (ω : Set E) :
    (edgeLaw (toI p hp0 hp1)).real {ω} = PercLib.CriticalLRP.configurationLaw p (toFs ω) := by
  rw [edgeLaw_real_singleton]
  simp only [PercLib.CriticalLRP.configurationLaw]
  refine Finset.prod_congr rfl fun e _ => ?_
  by_cases h : e ∈ ω <;> simp [h, mem_toFs, toI_coe]

/-- The finite Bernoulli law of the root project, transported to `Set E`. -/
theorem prob_eq_edgeLaw (p : E → ℝ) (hp0 : ∀ e, 0 ≤ p e) (hp1 : ∀ e, p e ≤ 1)
    (B : Set (Finset E)) :
    prob p B = (edgeLaw (toI p hp0 hp1)).real {ω : Set E | toFs ω ∈ B} := by
  classical
  have h1 : prob p B = ∑ s : Finset E,
      PercLib.CriticalLRP.configurationLaw p s * (if s ∈ B then (1 : ℝ) else 0) := rfl
  have h2 : (edgeLaw (toI p hp0 hp1)).real {ω : Set E | toFs ω ∈ B}
      = ∑ s : Finset E,
        PercLib.CriticalLRP.configurationLaw p s * (if s ∈ B then (1 : ℝ) else 0) := by
    set S : Finset (Set E) := Finset.univ.filter (fun ω : Set E => toFs ω ∈ B) with hS
    have hsplit : (edgeLaw (toI p hp0 hp1)).real {ω : Set E | toFs ω ∈ B}
        = ∑ ω ∈ S, (edgeLaw (toI p hp0 hp1)).real ({ω} : Set (Set E)) := by
      rw [← measureReal_biUnion_finset]
      · congr 1
        ext ω
        simp [hS]
      · intro a _ b _ hab
        exact Set.disjoint_singleton.mpr hab
      · intro a _
        exact MeasurableSet.singleton a
    have hfilter : (∑ s : Finset E,
        PercLib.CriticalLRP.configurationLaw p s * (if s ∈ B then (1 : ℝ) else 0))
        = ∑ s ∈ Finset.univ.filter (fun s : Finset E => s ∈ B),
          PercLib.CriticalLRP.configurationLaw p s := by
      rw [Finset.sum_filter]
      refine Finset.sum_congr rfl fun s _ => ?_
      by_cases h : s ∈ B <;> simp [h]
    rw [hsplit, hfilter]
    refine Finset.sum_bij (fun (ω : Set E) _ => toFs ω) ?_ ?_ ?_ ?_
    · intro ω hω
      simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hω ⊢
      simpa [hS] using hω
    · intro a _ b _ hab
      rw [← coe_toFs a, ← coe_toFs b, hab]
    · intro s hs
      exact ⟨(s : Set E), by simpa [hS, toFs_coe] using hs, by rw [toFs_coe]⟩
    · intro ω hω
      exact edgeLaw_real_singleton_toFs p hp0 hp1 ω
  rw [h1, h2]

/-- Membership in m1's `DisjOccK` corresponds to membership in `DisjointOccurrenceFin` after
passing from `Finset E` to `Set E`. -/
theorem toFs_mem_disjOccK_iff {k : ℕ} (A : Fin k → Set (Finset E)) (ω : Set E) :
    toFs ω ∈ DisjOccK A ↔
      ω ∈ DisjointOccurrenceFin (fun i => {ω : Set E | toFs ω ∈ A i}) := by
  constructor
  · rintro ⟨W, hsub, hmem, hdisj⟩
    exact ⟨W, fun i => toFs_subset_iff.mpr (hsub i), fun i => by simpa [toFs_coe] using hmem i,
      hdisj⟩
  · rintro ⟨W, hsub, hmem, hdisj⟩
    exact ⟨W, fun i => toFs_subset_iff.mp (hsub i), fun i => by simpa [toFs_coe] using hmem i,
      hdisj⟩

/-- **`BKIncreasing` is a theorem**, not a hypothesis. -/
theorem BKIncreasing_of_bkFin (p : E → ℝ) (hp0 : ∀ e, 0 ≤ p e) (hp1 : ∀ e, p e < 1) :
    BKIncreasing p := by
  intro k A hA
  classical
  let A' : Fin k → Set (Set E) := fun i => {ω : Set E | toFs ω ∈ A i}
  have hupper : ∀ i, IsUpperSet (A' i) := by
    intro i
    refine fun a b hab ha => hA i (s := toFs a) ha (t := toFs b) ?_
    intro x hx
    rw [mem_toFs]
    exact hab (by rw [← mem_toFs]; exact hx)
  have hwit : ∀ i, FiniteWitness (A' i) := by
    intro i ω hω
    refine ⟨toFs ω, ?_, ?_⟩
    · intro x hx
      exact mem_toFs.mp hx
    · show toFs ((toFs ω : Set E)) ∈ A i
      rwa [toFs_coe]
  have hbk := bk_fin (toI p hp0 fun e => (hp1 e).le)
    (fun e => show (toI p hp0 (fun e => (hp1 e).le) e : ℝ) < 1 by
      simpa [toI] using hp1 e)
    A' hupper hwit
  calc prob p (DisjOccK A)
      = (edgeLaw (toI p hp0 fun e => (hp1 e).le)).real
          {ω : Set E | toFs ω ∈ DisjOccK A} :=
        prob_eq_edgeLaw p hp0 _ _
    _ = (edgeLaw (toI p hp0 fun e => (hp1 e).le)).real (DisjointOccurrenceFin A') := by
        rw [show {ω : Set E | toFs ω ∈ DisjOccK A} = DisjointOccurrenceFin A' from by
          ext ω
          exact toFs_mem_disjOccK_iff A ω]
    _ ≤ ∏ i, (edgeLaw (toI p hp0 fun e => (hp1 e).le)).real (A' i) := hbk
    _ = ∏ i, prob p (A i) := by
        refine Finset.prod_congr rfl fun i _ => ?_
        exact (prob_eq_edgeLaw p hp0 _ (A i)).symm

end

end PercLib.CriticalLRP.TreeGraph

namespace PercLib.CriticalLRP.TreeGraph

open MeasureTheory PercLib.CriticalLRP PercLib.CriticalLRP.Percolation
open scoped ENNReal NNReal

variable {V : Type*} [DecidableEq V] {E : Type*} [Fintype E] [DecidableEq E]

noncomputable section

/-- **Tree-graph inequality (I.2.1)**, with the BK hypothesis discharged. -/
theorem three_point_tree_graph' {p : E → ℝ} (hp : ∀ e, 0 ≤ p e) (hp1 : ∀ e, p e < 1)
    (ends : E → Sym2 V) (x y z : V) :
    prob p {s | Conn ends s x y ∧ Conn ends s x z}
      ≤ ∑ w ∈ candF ends x y z, prob p {s | Conn ends s x w} *
          prob p {s | Conn ends s w y} * prob p {s | Conn ends s w z} :=
  three_point_tree_graph hp (fun e => (hp1 e).le) (BKIncreasing_of_bkFin p hp hp1) ends x y z

/-- **Tree-graph moment bound (I.2.3), `p = 2`**, with the BK hypothesis discharged. -/
theorem second_moment_le' {V : Type*} [DecidableEq V] [Fintype V] [AddCommGroup V]
    {E : Type*} [Fintype E] [DecidableEq E] (p : E → ℝ) (hp : ∀ e, 0 ≤ p e) (hp1 : ∀ e, p e < 1)
    (ends : E → Sym2 V) (o : V)
    (hinv : ∀ a b : V, twoPoint p ends a b = twoPoint p ends o (b - a)) :
    clusterVolSq p ends o ≤ (clusterVolume p ends o) ^ 3 :=
  second_moment_le p hp (fun e => (hp1 e).le) (BKIncreasing_of_bkFin p hp hp1) ends o hinv

/-- **(I.2.1) with the extended sum over all vertices**, with the BK hypothesis discharged. -/
theorem three_point_tree_graph_tsum' {V : Type*} [DecidableEq V] [AddCommGroup V]
    {E : Type*} [Fintype E] [DecidableEq E] (p : E → ℝ) (hp : ∀ e, 0 ≤ p e) (hp1 : ∀ e, p e < 1)
    (ends : E → Sym2 V) (x y z : V) :
    ENNReal.ofReal (prob p {s | Conn ends s x y ∧ Conn ends s x z})
      ≤ ∑' w : V, twoPointE p ends x w * twoPointE p ends w y * twoPointE p ends w z :=
  three_point_tree_graph_tsum p hp (fun e => (hp1 e).le) (BKIncreasing_of_bkFin p hp hp1) ends x y z

/-- **Cluster second-moment bound (I.2.3), `p = 2`, infinite vertex set**, with the BK hypothesis
discharged. -/
theorem second_moment_le_infinite' {V : Type*} [DecidableEq V] [AddCommGroup V]
    {E : Type*} [Fintype E] [DecidableEq E] (p : E → ℝ) (hp : ∀ e, 0 ≤ p e) (hp1 : ∀ e, p e < 1)
    (ends : E → Sym2 V) (o : V)
    (hinv : ∀ a b : V, twoPointE p ends a b = twoPointE p ends o (b - a)) :
    clusterVolSqE p ends o ≤ (clusterVolumeE p ends o) ^ 3 :=
  second_moment_le_infinite p hp (fun e => (hp1 e).le) (BKIncreasing_of_bkFin p hp hp1) ends o hinv

end

end PercLib.CriticalLRP.TreeGraph
