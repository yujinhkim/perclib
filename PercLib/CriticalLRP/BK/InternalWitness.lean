/-
Migration source: https://github.com/yujinhkim/Critical-Long-range-percolation
Integration revision: 3b3d1d0e43ef940bfaa2292ee5c2ee094ac4edbf
Licence: Apache-2.0 for the PercLib Lean sources and tooling; see third_party/critical-lrp/.
External provenance and modifications are recorded in the file-specific notices below.
-/

/-
# Lemma I.2.1 for general increasing functionals: the Borel/continuity-from-below lift

The file `LemmaI21.lean` reduces Lemma I.2.1(i) of Hutchcroft, arXiv:2508.18807v1, p. 21, to the
indicator inequality for the level sets `{F (K_x) > s}`, `{G (K_y) > t}`.  The indicator
inequality available in `BK/GraphConsequences.lean` (`twoCluster_bk`) covers increasing events that
are finitely witnessed *and determined by the cluster of the relevant vertex*.

Here we extend the indicator inequality to increasing events of the form `{F (K_x) > s}` for
arbitrary functionals `F` of vertex sets that are

* monotone under inclusion, and
* continuous from below: `F (K_x) = ⨆_n F (K_x ∩ E_n)` for a finite exhaustion `E_n ↑ E`;

this class contains the functionals used later in the paper (`F (K) = |K|^p`,
`F (K) = 1{|K| ≥ n}`, and more generally `φ (|K|)` for monotone `φ` with the convention
`φ (∞) = ⨆ φ`).

The proof does not need the general Borel BK inequality: instead of approximating the event from
below by arbitrary finitely witnessed events (whose witnesses may fall outside the clusters), we use
witnesses *internal to the cluster of `x`*.  These exist because the cluster of `x` in `ω ∩ E_n` is
spanned by the edges of `ω ∩ E_n` that are internal to `K_x (ω)`.
-/
module

public import PercLib.CriticalLRP.BK.GraphConsequences
public import PercLib.CriticalLRP.BK.LayerCake
public import PercLib.CriticalLRP.BK.FunctionalIndicator

set_option linter.unusedSectionVars false
set_option linter.unusedSimpArgs false
set_option linter.unnecessarySimpa false
set_option linter.unusedTactic false
set_option linter.unusedVariables false

set_option autoImplicit true

@[expose] public section

namespace PercLib.CriticalLRP

open MeasureTheory ProbabilityTheory
open scoped ENNReal NNReal

namespace Percolation
universe u v
variable {V : Type u} {E : Type v}

section Exhaustion
attribute [local instance] Classical.propDecidable
variable {G : BondGraph V E}

/-- The cluster of `x` in `ω ∩ E_n` increases with `n`. -/
theorem monotone_cluster_inter (𝓔 : ℕ → Finset E) (h𝓔 : Monotone 𝓔) (ω : Set E) (x : V) :
    Monotone fun n => cluster G (ω ∩ (𝓔 n : Set E)) x := by
  intro m n hmn
  exact cluster_mono (Set.inter_subset_inter_right _ (Finset.coe_subset.mpr (h𝓔 hmn))) x

/-- If the finite sets `E_n` cover the edge set, then for every configuration the clusters of `x`
in `ω ∩ E_n` increase to the cluster of `x` in `ω`. -/
theorem cluster_eq_iUnion_inter (𝓔 : ℕ → Finset E) (h𝓔mono : Monotone 𝓔)
    (h𝓔 : ∀ e : E, ∃ n, e ∈ 𝓔 n) (ω : Set E) (x : V) :
    cluster G ω x = ⋃ n, cluster G (ω ∩ (𝓔 n : Set E)) x := by
  ext y
  refine ⟨fun hy => ?_, fun hy => ?_⟩
  · induction hy with
    | refl => exact Set.mem_iUnion.mpr ⟨0, conn_refl G _ x⟩
    | @tail b c hab hbc ih =>
      obtain ⟨n, hn⟩ := Set.mem_iUnion.mp ih
      obtain ⟨e, he, hGe⟩ := hbc
      obtain ⟨m, hm⟩ := h𝓔 e
      refine Set.mem_iUnion.mpr ⟨max n m, ?_⟩
      have hsub : ω ∩ (𝓔 n : Set E) ⊆ ω ∩ (𝓔 (max n m) : Set E) :=
        Set.inter_subset_inter_right _ (Finset.coe_subset.mpr (h𝓔mono (le_max_left n m)))
      have hem : e ∈ (𝓔 (max n m) : Set E) :=
        Finset.coe_subset.mpr (h𝓔mono (le_max_right n m)) hm
      exact (conn_mono G hsub hn).tail ⟨e, ⟨he, hem⟩, hGe⟩
  · obtain ⟨n, hn⟩ := Set.mem_iUnion.mp hy
    exact cluster_mono Set.inter_subset_left x hn

end Exhaustion

section InternalWitness
attribute [local instance] Classical.propDecidable
variable {G : BondGraph V E}

/-- `A` has *internal* witnesses at `x` if every configuration in `A` contains a finite witness for
`A` all of whose edges are internal to the cluster of `x`. -/
def InternalWitnessAt (G : BondGraph V E) (x : V) (A : Set (Set E)) : Prop :=
  ∀ ω ∈ A, ∃ s : Finset E, (s : Set E) ⊆ ω ∧ (s : Set E) ∈ A ∧
    ∀ e ∈ s, ∀ v, v ∈ G e → v ∈ cluster G ω x

theorem finiteWitness_of_internalWitnessAt {x : V} {A : Set (Set E)}
    (h : InternalWitnessAt G x A) : FiniteWitness A :=
  fun ω hω => let ⟨s, hs, hsa, _⟩ := h ω hω; ⟨s, hs, hsa⟩

/-- The cluster of `x` in `internalEdges ∩ s` equals the cluster of `x` in `s`, for `s ⊆ ω`. -/
theorem cluster_internal_inter_of_subset {ω s : Set E} (hs : s ⊆ ω) (x : V) :
    cluster G (internalEdges G ω x ∩ s) x = cluster G s x := by
  apply Set.Subset.antisymm
  · exact cluster_mono Set.inter_subset_right x
  · intro y hy
    have hsub : internalEdges G ω x ∩ s ⊆ ω :=
      Set.inter_subset_left.trans Set.inter_subset_left
    induction hy with
    | refl => exact conn_refl G _ x
    | @tail b c hab hbc ih =>
      obtain ⟨e, he, hGe⟩ := hbc
      have ha : b ∈ cluster G ω x := cluster_mono hsub x ih
      have hc : c ∈ cluster G ω x := ha.tail ⟨e, hs he, hGe⟩
      refine ih.tail ⟨e, ⟨⟨hs he, ?_⟩, he⟩, hGe⟩
      intro v hv
      rw [hGe] at hv
      rcases Sym2.mem_iff.mp hv with rfl | rfl
      · exact ha
      · exact hc

/-- The edges of `ω ∩ E_n` that are internal to the cluster of `x`. -/
noncomputable def internalWit (𝓔 : ℕ → Finset E) (ω : Set E) (x : V) (n : ℕ) : Finset E :=
  (𝓔 n).filter (fun e => e ∈ internalEdges G ω x)

theorem coe_internalWit (𝓔 : ℕ → Finset E) (ω : Set E) (x : V) (n : ℕ) :
    (internalWit 𝓔 (G := G) ω x n : Set E) = internalEdges G ω x ∩ (𝓔 n : Set E) := by
  ext e
  simp [internalWit, and_comm]

/-- `internalWit` spans the cluster of `x` in `ω ∩ E_n`. -/
theorem cluster_internalWit (𝓔 : ℕ → Finset E) (ω : Set E) (x : V) (n : ℕ) :
    cluster G (internalWit 𝓔 (G := G) ω x n : Set E) x
      = cluster G (ω ∩ (𝓔 n : Set E)) x := by
  rw [coe_internalWit]
  have h : internalEdges G ω x ∩ (𝓔 n : Set E)
      = internalEdges G ω x ∩ (ω ∩ (𝓔 n : Set E)) := by
    ext e
    simp only [Set.mem_inter_iff]
    constructor
    · rintro ⟨h1, h2⟩; exact ⟨h1, h1.1, h2⟩
    · rintro ⟨h1, -, h2⟩; exact ⟨h1, h2⟩
  rw [h]
  exact cluster_internal_inter_of_subset Set.inter_subset_left x

/-- **Internal witnesses for level sets of functionals of the truncated cluster.** -/
theorem internalWitnessAt_level (𝓔 : ℕ → Finset E) {F : Set V → ℝ} (x : V) (n : ℕ) (s : ℝ) :
    InternalWitnessAt G x {ω : Set E | s < F (cluster G (ω ∩ (𝓔 n : Set E)) x)} := by
  intro ω hω
  refine ⟨internalWit 𝓔 (G := G) ω x n, ?_, ?_, ?_⟩
  · rw [coe_internalWit]
    exact fun e he => he.1.1
  · show s < F (cluster G ((internalWit 𝓔 (G := G) ω x n : Set E) ∩ (𝓔 n : Set E)) x)
    have h1 : (internalWit 𝓔 (G := G) ω x n : Set E) ∩ (𝓔 n : Set E)
        = (internalWit 𝓔 (G := G) ω x n : Set E) := by
      rw [coe_internalWit]; exact Set.inter_eq_left.mpr Set.inter_subset_right
    rw [h1, cluster_internalWit]
    exact hω
  · intro e he v hv
    have he' : e ∈ (internalWit 𝓔 (G := G) ω x n : Set E) := by exact_mod_cast he
    rw [coe_internalWit] at he'
    exact he'.1.2 v hv

/-- Level sets of monotone functionals of the truncated cluster are increasing events. -/
theorem isUpperSet_level_trunc (𝓔 : ℕ → Finset E) {F : Set V → ℝ}
    (hF : ∀ S T : Set V, S ⊆ T → F S ≤ F T) (x : V) (n : ℕ) (s : ℝ) :
    IsUpperSet {ω : Set E | s < F (cluster G (ω ∩ (𝓔 n : Set E)) x)} := by
  intro ω ω' hω h
  exact lt_of_lt_of_le h (hF _ _ (cluster_mono (Set.inter_subset_inter_left _ hω) x))

/-- Level sets of monotone functionals of the truncated cluster increase with `n`. -/
theorem monotone_level_trunc (𝓔 : ℕ → Finset E) (h𝓔 : Monotone 𝓔) {F : Set V → ℝ}
    (hF : ∀ S T : Set V, S ⊆ T → F S ≤ F T) (x : V) (s : ℝ) :
    Monotone fun n => {ω : Set E | s < F (cluster G (ω ∩ (𝓔 n : Set E)) x)} := by
  intro m n hmn ω hω
  exact lt_of_lt_of_le hω (hF _ _ (monotone_cluster_inter 𝓔 h𝓔 ω x hmn))

end InternalWitness

section BKInternal
attribute [local instance] Classical.propDecidable

/-- **Two-cluster BK inequality with internal witnesses.**  This is `twoCluster_bk` with the
cluster-determined hypothesis replaced by the (weaker, and for truncated level sets provable)
requirement that witnesses can be taken inside the clusters. -/
theorem twoCluster_bk_internal [Countable E] (G : BondGraph V E) (p : E → unitInterval)
    (hp : ∀ e, p e < 1) (x y : V) (A B : Set (Set E)) (hA : IsUpperSet A)
    (hAi : InternalWitnessAt G x A) (hB : IsUpperSet B) (hBi : InternalWitnessAt G y B) :
    (edgeLaw p).real (A ∩ B ∩ {ω | ¬ Conn G ω x y}) ≤ (edgeLaw p).real A * (edgeLaw p).real B := by
  have hfA := finiteWitness_of_internalWitnessAt hAi
  have hfB := finiteWitness_of_internalWitnessAt hBi
  have hsub : A ∩ B ∩ {ω | ¬ Conn G ω x y} ⊆ DisjointOccurrence A B := by
    rintro ω ⟨⟨hωA, hωB⟩, hxy⟩
    obtain ⟨s, hs, hsa, hsi⟩ := hAi ω hωA
    obtain ⟨t, ht, hta, hti⟩ := hBi ω hωB
    exact ⟨s, t, hs, ht, disjoint_of_internal G ω hxy hsi hti, hsa, hta⟩
  exact (measureReal_mono hsub).trans (bkEdge p hp A B hA hB hfA hfB)

/-- `ℝ≥0∞` form of `twoCluster_bk_internal`. -/
theorem twoCluster_bk_internal_ennreal [Countable E] (G : BondGraph V E) (p : E → unitInterval)
    (hp : ∀ e, p e < 1) (x y : V) (A B : Set (Set E)) (hA : IsUpperSet A)
    (hAi : InternalWitnessAt G x A) (hB : IsUpperSet B) (hBi : InternalWitnessAt G y B) :
    (edgeLaw p) (A ∩ B ∩ {ω | ¬ Conn G ω x y}) ≤ (edgeLaw p) A * (edgeLaw p) B := by
  have hreal := twoCluster_bk_internal G p hp x y A B hA hAi hB hBi
  rw [measureReal_def, measureReal_def, measureReal_def, ← ENNReal.toReal_mul] at hreal
  have hne : (edgeLaw p) A * (edgeLaw p) B ≠ ⊤ :=
    ENNReal.mul_ne_top (measure_ne_top _ _) (measure_ne_top _ _)
  exact (ENNReal.toReal_le_toReal (measure_ne_top _ _) hne).mp hreal

/-- Continuity from below for a monotone sequence of sets. -/
theorem measure_iUnion_of_monotone {α : Type*} [MeasurableSpace α] {μ : Measure α}
    {s : ℕ → Set α} (hm : Monotone s) : μ (⋃ n, s n) = ⨆ n, μ (s n) :=
  Directed.measure_iUnion fun i j =>
    ⟨max i j, hm (le_max_left i j), hm (le_max_right i j)⟩

/-- The diagonal sup of a product of monotone `ℝ≥0∞`-valued sequences. -/
theorem iSup_mul_iSup_eq (a b : ℕ → ℝ≥0∞) (ha : Monotone a) (hb : Monotone b) :
    (⨆ n, a n) * (⨆ n, b n) = ⨆ n, a n * b n := by
  apply le_antisymm
  · rw [ENNReal.mul_iSup]
    refine iSup_le fun n => ?_
    rw [ENNReal.iSup_mul]
    refine iSup_le fun m => ?_
    rcases le_total n m with h | h
    · exact le_iSup_of_le m (by gcongr; exact hb h)
    · exact le_iSup_of_le n (by gcongr; exact ha h)
  · exact iSup_le fun n => by gcongr <;> exact le_iSup _ _

/-- **Two-cluster BK for increasing unions of internal-witnessed events.** -/
theorem twoCluster_bk_iUnion [Countable E] (G : BondGraph V E) (p : E → unitInterval)
    (hp : ∀ e, p e < 1) (x y : V) (A B : ℕ → Set (Set E))
    (hA : ∀ n, IsUpperSet (A n)) (hAm : Monotone A) (hAi : ∀ n, InternalWitnessAt G x (A n))
    (hB : ∀ n, IsUpperSet (B n)) (hBm : Monotone B) (hBi : ∀ n, InternalWitnessAt G y (B n)) :
    (edgeLaw p) ((⋃ n, A n) ∩ (⋃ n, B n) ∩ {ω | ¬ Conn G ω x y})
      ≤ (edgeLaw p) (⋃ n, A n) * (edgeLaw p) (⋃ n, B n) := by
  classical
  have hmonoC : Monotone fun n => A n ∩ B n ∩ {ω : Set E | ¬ Conn G ω x y} :=
    fun m n hmn => Set.inter_subset_inter_left _ (Set.inter_subset_inter (hAm hmn) (hBm hmn))
  have hUnion : (⋃ n, A n ∩ B n ∩ {ω : Set E | ¬ Conn G ω x y})
      = (⋃ n, A n) ∩ (⋃ n, B n) ∩ {ω : Set E | ¬ Conn G ω x y} := by
    ext ω
    simp only [Set.mem_iUnion, Set.mem_inter_iff, Set.mem_ofPred_eq]
    constructor
    · rintro ⟨n, ⟨h1, h2⟩, h3⟩
      exact ⟨⟨⟨n, h1⟩, ⟨n, h2⟩⟩, h3⟩
    · rintro ⟨⟨⟨n, h1⟩, ⟨m, h2⟩⟩, h3⟩
      exact ⟨max n m, ⟨hAm (le_max_left n m) h1, hBm (le_max_right n m) h2⟩, h3⟩
  rw [← hUnion, measure_iUnion_of_monotone hmonoC]
  have hstep : ∀ n, (edgeLaw p) (A n ∩ B n ∩ {ω : Set E | ¬ Conn G ω x y})
      ≤ (edgeLaw p) (A n) * (edgeLaw p) (B n) :=
    fun n => twoCluster_bk_internal_ennreal G p hp x y (A n) (B n) (hA n) (hAi n) (hB n) (hBi n)
  calc ⨆ n, (edgeLaw p) (A n ∩ B n ∩ {ω : Set E | ¬ Conn G ω x y})
      ≤ ⨆ n, (edgeLaw p) (A n) * (edgeLaw p) (B n) := iSup_mono hstep
    _ = (⨆ n, (edgeLaw p) (A n)) * (⨆ n, (edgeLaw p) (B n)) :=
        (iSup_mul_iSup_eq _ _ (fun m n hmn => measure_mono (hAm hmn))
          (fun m n hmn => measure_mono (hBm hmn))).symm
    _ = (edgeLaw p) (⋃ n, A n) * (edgeLaw p) (⋃ n, B n) := by
        rw [measure_iUnion_of_monotone hAm, measure_iUnion_of_monotone hBm]

end BKInternal

end Percolation

end PercLib.CriticalLRP
