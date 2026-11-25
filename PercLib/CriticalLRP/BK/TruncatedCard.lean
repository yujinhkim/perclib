/-
Migration source: https://github.com/yujinhkim/Critical-Long-range-percolation
Integration revision: 3b3d1d0e43ef940bfaa2292ee5c2ee094ac4edbf
Licence: Apache-2.0 for the PercLib Lean sources and tooling; see third_party/critical-lrp/.
External provenance and modifications are recorded in the file-specific notices below.
-/

/-
# A concrete functional in the continuity-from-below class: truncated cluster size

The general form of Lemma I.2.1 proved in `LemmaI21Final.lean` applies to monotone functionals
`F` of the cluster that are continuous from below along a finite exhaustion of the edge set.  This
file shows that the class is non-vacuous and contains the functionals of cluster size used in the
moment estimates of Hutchcroft, arXiv:2508.18807v1, Section I.4: the truncated cardinality
`F (K) = min (|K|, m)`.

The key point is that a *finite* cluster of `x` is eventually equal to its truncation to
`ω ∩ E_n` (`eventually_cluster_inter_eq`), while an infinite cluster already contains `m` vertices
in `ω ∩ E_n` for large `n`.

Note that `F (K) = 1 {|K| = ∞}` is *not* of this class: it is monotone but not continuous from
below, and Lemma I.2.1 for it needs the general Borel BK inequality.
-/
module

public import PercLib.CriticalLRP.BK.GraphConsequences
public import PercLib.CriticalLRP.BK.InternalWitness
public import PercLib.CriticalLRP.BK.FunctionalFromBelow

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

section FiniteCluster
attribute [local instance] Classical.propDecidable
variable {G : BondGraph V E}

/-- A finite cluster of `x` is eventually equal to its truncation to `ω ∩ E_n`. -/
theorem eventually_cluster_inter_eq (𝓔 : ℕ → Finset E) (h𝓔mono : Monotone 𝓔)
    (h𝓔 : ∀ e : E, ∃ n, e ∈ 𝓔 n) (ω : Set E) (x : V)
    (hfin : (cluster G ω x).Finite) :
    ∃ N, ∀ n ≥ N, cluster G (ω ∩ (𝓔 n : Set E)) x = cluster G ω x := by
  have hex : ∀ y ∈ hfin.toFinset, ∃ n, y ∈ cluster G (ω ∩ (𝓔 n : Set E)) x := by
    intro y hy
    have h1 : y ∈ ⋃ n, cluster G (ω ∩ (𝓔 n : Set E)) x := by
      rw [← cluster_eq_iUnion_inter 𝓔 h𝓔mono h𝓔 ω x]
      exact hfin.mem_toFinset.mp hy
    exact Set.mem_iUnion.mp h1
  let f : V → ℕ := fun y => if h : y ∈ hfin.toFinset then Classical.choose (hex y h) else 0
  have hf : ∀ y (h : y ∈ hfin.toFinset), y ∈ cluster G (ω ∩ (𝓔 (f y) : Set E)) x := by
    intro y h
    simp only [f, dite_eq_left h]
    exact Classical.choose_spec (hex y h)
  refine ⟨hfin.toFinset.sup f, fun n hn => ?_⟩
  apply Set.Subset.antisymm
  · exact cluster_mono Set.inter_subset_left x
  · intro y hy
    have hy' : y ∈ hfin.toFinset := hfin.mem_toFinset.mpr hy
    refine conn_mono G (Set.inter_subset_inter_right ω
      (Finset.coe_subset.mpr (h𝓔mono hn))) ?_
    exact conn_mono G (Set.inter_subset_inter_right ω
      (Finset.coe_subset.mpr (h𝓔mono (Finset.le_sup hy')))) (hf y hy')

/-- An infinite cluster of `x` contains `m` vertices already in `ω ∩ E_n`, for `n` large. -/
theorem exists_encard_ge_of_infinite (𝓔 : ℕ → Finset E) (h𝓔mono : Monotone 𝓔)
    (h𝓔 : ∀ e : E, ∃ n, e ∈ 𝓔 n) (ω : Set E) (x : V) (m : ℕ)
    (hinf : (cluster G ω x).Infinite) :
    ∃ N, (m : ℕ∞) ≤ (cluster G (ω ∩ (𝓔 N : Set E)) x).encard := by
  obtain ⟨t, htK, htfin, htcard⟩ := hinf.exists_subset_ncard_eq m
  have hex : ∀ y ∈ htfin.toFinset, ∃ n, y ∈ cluster G (ω ∩ (𝓔 n : Set E)) x := by
    intro y hy
    have h1 : y ∈ ⋃ n, cluster G (ω ∩ (𝓔 n : Set E)) x := by
      rw [← cluster_eq_iUnion_inter 𝓔 h𝓔mono h𝓔 ω x]
      exact htK (htfin.mem_toFinset.mp hy)
    exact Set.mem_iUnion.mp h1
  let f : V → ℕ := fun y => if h : y ∈ htfin.toFinset then Classical.choose (hex y h) else 0
  have hf : ∀ y (h : y ∈ htfin.toFinset), y ∈ cluster G (ω ∩ (𝓔 (f y) : Set E)) x := by
    intro y h
    simp only [f, dite_eq_left h]
    exact Classical.choose_spec (hex y h)
  refine ⟨htfin.toFinset.sup f, ?_⟩
  have hle : ∀ y ∈ t, y ∈ cluster G (ω ∩ (𝓔 (htfin.toFinset.sup f) : Set E)) x := by
    intro y hy
    have hy' : y ∈ htfin.toFinset := htfin.mem_toFinset.mpr hy
    exact conn_mono G (Set.inter_subset_inter_right ω
      (Finset.coe_subset.mpr (h𝓔mono (Finset.le_sup hy')))) (hf y hy')
  calc (m : ℕ∞) = (t.ncard : ℕ∞) := by rw [htcard]
    _ = (htfin.toFinset.card : ℕ∞) := by rw [Set.ncard_eq_toFinset_card t htfin]
    _ = t.encard := (htfin.encard_eq_coe_toFinset_card).symm
    _ ≤ (cluster G (ω ∩ (𝓔 (htfin.toFinset.sup f) : Set E)) x).encard := Set.encard_mono hle

end FiniteCluster

section TruncCard
attribute [local instance] Classical.propDecidable

/-- `truncCard m K = min (|K|, m)`, with the convention `min (∞, m) = m` for infinite `K`. -/
noncomputable def truncCard (m : ℕ) (K : Set V) : ℝ :=
  if K.Finite then min ((K.ncard : ℕ) : ℝ) (m : ℝ) else (m : ℝ)

theorem truncCard_nonneg (m : ℕ) (K : Set V) : 0 ≤ truncCard m K := by
  unfold truncCard
  split
  · exact le_min (by positivity) (by positivity)
  · positivity

theorem truncCard_le (m : ℕ) (K : Set V) : truncCard m K ≤ (m : ℝ) := by
  unfold truncCard
  split
  · exact min_le_right _ _
  · exact le_rfl

theorem truncCard_mono (m : ℕ) : Monotone (truncCard (V := V) m) := by
  intro S T hST
  unfold truncCard
  by_cases hS : S.Finite
  · by_cases hT : T.Finite
    · rw [ite_eq_left hS, ite_eq_left hT]
      have h1 : S.ncard ≤ T.ncard := Set.ncard_le_ncard hST hT
      have h2 : ((S.ncard : ℕ) : ℝ) ≤ ((T.ncard : ℕ) : ℝ) := by exact_mod_cast h1
      exact min_le_min h2 le_rfl
    · rw [ite_eq_left hS, ite_eq_right hT]
      exact min_le_right _ _
  · have hT : ¬ T.Finite := fun h => hS (h.subset hST)
    rw [ite_eq_right hS, ite_eq_right hT]

/-- **Continuity from below of `min (|K_x|, m)`** along a finite exhaustion of the edge set. -/
theorem truncCard_cont (𝓔 : ℕ → Finset E) (h𝓔mono : Monotone 𝓔)
    (h𝓔 : ∀ e : E, ∃ n, e ∈ 𝓔 n) (G : BondGraph V E) (x : V) (m : ℕ) :
    ∀ (ω : Set E) (s : ℝ), s < truncCard m (cluster G ω x) →
      ∃ n, s < truncCard m (cluster G (ω ∩ (𝓔 n : Set E)) x) := by
  intro ω s hs
  by_cases hfin : (cluster G ω x).Finite
  · obtain ⟨N, hN⟩ := eventually_cluster_inter_eq 𝓔 h𝓔mono h𝓔 ω x hfin
    exact ⟨N, by rw [hN N le_rfl]; exact hs⟩
  · have hKm : truncCard m (cluster G ω x) = (m : ℝ) := by
      rw [truncCard, ite_eq_right hfin]
    have hsm : s < (m : ℝ) := by rwa [hKm] at hs
    obtain ⟨N, hN⟩ := exists_encard_ge_of_infinite 𝓔 h𝓔mono h𝓔 ω x m hfin
    refine ⟨N, ?_⟩
    by_cases hKfin : (cluster G (ω ∩ (𝓔 N : Set E)) x).Finite
    · rw [truncCard, ite_eq_left hKfin]
      have hge : (m : ℝ) ≤ ((cluster G (ω ∩ (𝓔 N : Set E)) x).ncard : ℝ) := by
        have h1 : (m : ℕ∞) ≤ ((cluster G (ω ∩ (𝓔 N : Set E)) x).ncard : ℕ∞) := by
          rw [hKfin.cast_ncard_eq]
          exact hN
        exact_mod_cast h1
      exact lt_of_lt_of_le hsm (le_min hge le_rfl)
    · rw [truncCard, ite_eq_right hKfin]
      exact hsm

/-- The level sets of `min (|K_x|, m)` as unions of `clusterLarge` events. -/
theorem level_truncCard_eq_iUnion [Countable E] (G : BondGraph V E) (x : V) (m : ℕ) (a : ℝ) :
    {ω : Set E | a < truncCard m (cluster G ω x)}
      = ⋃ n ∈ {n : ℕ | a < min (n : ℝ) (m : ℝ)}, clusterLarge G x n := by
  ext ω
  simp only [Set.mem_ofPred_eq, Set.mem_iUnion, Set.mem_ofPred_eq, clusterLarge]
  constructor
  · intro ha
    by_cases hfin : (cluster G ω x).Finite
    · refine ⟨(cluster G ω x).ncard, ?_, hfin.toFinset, ?_, ?_⟩
      · simpa only [truncCard, ite_eq_left hfin] using ha
      · rw [Set.ncard_eq_toFinset_card _ hfin]
      · intro y hy
        exact hfin.mem_toFinset.mp hy
    · have hm : a < (m : ℝ) := by simpa only [truncCard, ite_eq_right hfin] using ha
      obtain ⟨t, htK, htfin, htcard⟩ := Set.Infinite.exists_subset_ncard_eq hfin m
      refine ⟨m, ?_, htfin.toFinset, ?_, ?_⟩
      · show a < min ((m : ℕ) : ℝ) ((m : ℕ) : ℝ)
        simpa using hm
      · rw [← Set.ncard_eq_toFinset_card t htfin, htcard]
      · intro y hy
        exact htK (htfin.mem_toFinset.mp hy)
  · rintro ⟨n, han, t, htcard, htconn⟩
    have htK : (t : Set V) ⊆ cluster G ω x := fun y hy => htconn y hy
    by_cases hfin : (cluster G ω x).Finite
    · have hle : t.card ≤ (cluster G ω x).ncard := by
        simpa using Set.ncard_le_ncard htK hfin
      have h1 : n ≤ (cluster G ω x).ncard := htcard.trans hle
      have h2 : ((n : ℕ) : ℝ) ≤ (((cluster G ω x).ncard : ℕ) : ℝ) := by exact_mod_cast h1
      have h3 : min (n : ℝ) (m : ℝ) ≤ min ((cluster G ω x).ncard : ℝ) (m : ℝ) :=
        min_le_min h2 le_rfl
      have h4 : a < min ((cluster G ω x).ncard : ℝ) (m : ℝ) := lt_of_lt_of_le han h3
      simpa only [truncCard, ite_eq_left hfin] using h4
    · have h5 : a < (m : ℝ) := lt_of_lt_of_le han (min_le_right _ _)
      simpa only [truncCard, ite_eq_right hfin] using h5

theorem measurableSet_truncCard_level [Countable E] (G : BondGraph V E) (x : V) (m : ℕ) (a : ℝ) :
    MeasurableSet {ω : Set E | a < truncCard m (cluster G ω x)} := by
  rw [level_truncCard_eq_iUnion]
  exact MeasurableSet.biUnion (Set.to_countable _) (fun n _ => measurableSet_clusterLarge G x n)

/-- `min (|K_x|, m)` is a measurable functional of the configuration. -/
theorem measurable_truncCard_cluster [Countable E] (G : BondGraph V E) (x : V) (m : ℕ) :
    Measurable fun ω : Set E => truncCard m (cluster G ω x) :=
  measurable_of_Ioi (fun a => measurableSet_truncCard_level G x m a)

end TruncCard

section LemmaI21Instance
attribute [local instance] Classical.propDecidable

/-- **Lemma I.2.1(i) for truncated cluster sizes**: for all `x`, `y` and `m`, `m'`,
`E[1(x ↮ y) min(|K_x|,m) min(|K_y|,m')] ≤ E min(|K_x|,m) · E min(|K_y|,m')`. -/
theorem twoCluster_truncCard_lintegral [Countable E] (G : BondGraph V E)
    (p : E → unitInterval) (hp : ∀ e, p e < 1) (x y : V) (𝓔 : ℕ → Finset E)
    (h𝓔mono : Monotone 𝓔) (h𝓔 : ∀ e : E, ∃ n, e ∈ 𝓔 n) (m m' : ℕ) :
    ∫⁻ ω, ({ω : Set E | ¬ Conn G ω x y}).indicator (fun _ => (1 : ℝ≥0∞)) ω *
        ENNReal.ofReal (truncCard m (cluster G ω x) * truncCard m' (cluster G ω y))
        ∂(edgeLaw p)
      ≤ (∫⁻ ω, ENNReal.ofReal (truncCard m (cluster G ω x)) ∂(edgeLaw p)) *
          (∫⁻ ω, ENNReal.ofReal (truncCard m' (cluster G ω y)) ∂(edgeLaw p)) :=
  twoCluster_functional_lintegral_le G p hp x y 𝓔 h𝓔mono h𝓔
    (fun S => truncCard_nonneg m S) (fun S => truncCard_nonneg m' S)
    (truncCard_mono m) (truncCard_mono m')
    (truncCard_cont 𝓔 h𝓔mono h𝓔 G x m) (truncCard_cont 𝓔 h𝓔mono h𝓔 G y m')
    (measurable_truncCard_cluster G x m) (measurable_truncCard_cluster G y m')

end LemmaI21Instance

end Percolation

end PercLib.CriticalLRP
