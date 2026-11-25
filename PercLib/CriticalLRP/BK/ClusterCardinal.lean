/-
Migration source: https://github.com/yujinhkim/Critical-Long-range-percolation
Integration revision: 3b3d1d0e43ef940bfaa2292ee5c2ee094ac4edbf
Licence: Apache-2.0 for the PercLib Lean sources and tooling; see third_party/critical-lrp/.
External provenance and modifications are recorded in the file-specific notices below.
-/

/-
# Lemma I.2.1 for the cluster cardinality `|K_x|` (with infinite clusters)

This instantiates the `ℝ≥0∞`-valued form of Lemma I.2.1 (`LemmaI21ENNreal.lean`) with the extended
cluster cardinality, so that infinite clusters are allowed.  This is the form needed for the
cluster-moment bounds of Hutchcroft, arXiv:2508.18807v1, Section I.4:

`E[1(x ↮ y) |K_x| |K_y|] ≤ E|K_x| · E|K_y|`,  `|K| ∈ [0,∞]`.

The functional is written as the supremum

`cardFun S = ⨆ n, n · 1{∃ finite t ⊆ S, n ≤ |t|}`

which equals `|S|` for finite `S` and `⊤` for infinite `S` (`cardFun_eq_ncard`,
`cardFun_eq_top`); in this form monotonicity, continuity from below and measurability are all
immediate, the last because the level sets are literally `clusterLarge`.
-/
module

public import PercLib.CriticalLRP.BK.GraphConsequences
public import PercLib.CriticalLRP.BK.InternalWitness
public import PercLib.CriticalLRP.BK.FunctionalFromBelow
public import PercLib.CriticalLRP.BK.FunctionalENNReal
public import PercLib.CriticalLRP.BK.TruncatedCard

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

section CardFun
attribute [local instance] Classical.propDecidable

/-- The extended cardinality of a set of vertices, as an `ℝ≥0∞`-valued functional written in terms
of its finite subsets. -/
noncomputable def cardFun (S : Set V) : ℝ≥0∞ :=
  ⨆ n : ℕ, (n : ℝ≥0∞) * if ∃ t : Finset V, n ≤ t.card ∧ (t : Set V) ⊆ S then 1 else 0

theorem cardFun_mono : Monotone (cardFun (V := V)) := by
  intro S T hST
  refine iSup_le fun n => ?_
  by_cases h : ∃ t : Finset V, n ≤ t.card ∧ (t : Set V) ⊆ S
  · rw [ite_eq_left h, mul_one]
    obtain ⟨t, ht, htS⟩ := h
    exact le_iSup_of_le n (by rw [ite_eq_left ⟨t, ht, htS.trans hST⟩, mul_one])
  · rw [ite_eq_right h, mul_zero]
    exact zero_le

theorem cardFun_eq_ncard {S : Set V} (h : S.Finite) : cardFun S = (S.ncard : ℝ≥0∞) := by
  refine le_antisymm (iSup_le fun n => ?_) (le_iSup_of_le S.ncard ?_)
  · by_cases hn : ∃ t : Finset V, n ≤ t.card ∧ (t : Set V) ⊆ S
    · rw [ite_eq_left hn, mul_one]
      obtain ⟨t, ht, htS⟩ := hn
      calc (n : ℝ≥0∞) ≤ (t.card : ℝ≥0∞) := by exact_mod_cast ht
        _ = ((t : Set V).ncard : ℝ≥0∞) := by simp
        _ ≤ (S.ncard : ℝ≥0∞) := by exact_mod_cast Set.ncard_le_ncard htS h
    · rw [ite_eq_right hn, mul_zero]
      exact zero_le
  · have hcond : ∃ t : Finset V, S.ncard ≤ t.card ∧ (t : Set V) ⊆ S :=
      ⟨h.toFinset, by rw [Set.ncard_eq_toFinset_card S h], fun y hy => h.mem_toFinset.mp hy⟩
    rw [ite_eq_left hcond, mul_one]

theorem cardFun_eq_top {S : Set V} (h : S.Infinite) : cardFun S = ⊤ := by
  have hn : ∀ n : ℕ, ∃ t : Finset V, n ≤ t.card ∧ (t : Set V) ⊆ S := by
    intro n
    obtain ⟨t, htS, htfin, htcard⟩ := h.exists_subset_ncard_eq n
    exact ⟨htfin.toFinset, by rw [← Set.ncard_eq_toFinset_card t htfin, htcard], by
      intro y hy; exact htS (htfin.mem_toFinset.mp hy)⟩
  rw [eq_top_iff, ← ENNReal.iSup_natCast]
  refine iSup_le fun n => ?_
  rw [cardFun]
  exact le_iSup_of_le n (by rw [ite_eq_left (hn n), mul_one])

/-- The finite-subset functional agrees with extended set cardinality in `ℝ≥0∞`.
This holds for finite and infinite sets alike. -/
theorem cardFun_eq_encard (S : Set V) : cardFun S = (S.encard : ℝ≥0∞) := by
  by_cases h : S.Finite
  · rw [cardFun_eq_ncard h, ← h.cast_ncard_eq]
    rfl
  · rw [cardFun_eq_top h, Set.encard_eq_top h, ENat.toENNReal_top]

theorem cardFun_cont (𝓔 : ℕ → Finset E) (h𝓔mono : Monotone 𝓔) (h𝓔 : ∀ e : E, ∃ n, e ∈ 𝓔 n)
    (G : BondGraph V E) (x : V) :
    ∀ (ω : Set E) (s : ℝ≥0∞), s < cardFun (cluster G ω x) →
      ∃ n, s < cardFun (cluster G (ω ∩ (𝓔 n : Set E)) x) := by
  intro ω s hs
  by_cases hs0 : s = ⊤
  · rw [hs0] at hs; exact absurd hs (not_lt.mpr le_top)
  · -- find a finite set of `s`-beating size inside the cluster
    have hs' : s < ⨆ n : ℕ, (n : ℝ≥0∞) * if ∃ t : Finset V, n ≤ t.card ∧ (t : Set V) ⊆ cluster G ω x then 1 else 0 := hs
    obtain ⟨n, hn⟩ := lt_iSup_iff.mp hs'
    have hcond : ∃ t : Finset V, n ≤ t.card ∧ (t : Set V) ⊆ cluster G ω x := by
      by_contra hc
      rw [ite_eq_right hc, mul_zero] at hn
      exact absurd hn (not_lt.mpr zero_le)
    obtain ⟨t, htcard, htK⟩ := hcond
    have hmem : ∀ y ∈ t, ∃ m, y ∈ cluster G (ω ∩ (𝓔 m : Set E)) x := by
      intro y hy
      have h1 : y ∈ ⋃ m, cluster G (ω ∩ (𝓔 m : Set E)) x := by
        rw [← cluster_eq_iUnion_inter 𝓔 h𝓔mono h𝓔 ω x]
        exact htK hy
      exact Set.mem_iUnion.mp h1
    let f : V → ℕ := fun y => if h : y ∈ t then Classical.choose (hmem y h) else 0
    have hf : ∀ y (h : y ∈ t), y ∈ cluster G (ω ∩ (𝓔 (f y) : Set E)) x := by
      intro y h
      simp only [f, dite_eq_left h]
      exact Classical.choose_spec (hmem y h)
    refine ⟨t.sup f, ?_⟩
    have hsub : (t : Set V) ⊆ cluster G (ω ∩ (𝓔 (t.sup f) : Set E)) x := by
      intro y hy
      have hy' : y ∈ t := hy
      exact conn_mono G (Set.inter_subset_inter_right ω
        (Finset.coe_subset.mpr (h𝓔mono (Finset.le_sup hy')))) (hf y hy')
    have hcond' : ∃ t' : Finset V, n ≤ t'.card ∧ (t' : Set V) ⊆ cluster G (ω ∩ (𝓔 (t.sup f) : Set E)) x :=
      ⟨t, htcard, hsub⟩
    refine lt_of_lt_of_le hn ?_
    rw [ite_eq_left ⟨t, htcard, htK⟩, mul_one, cardFun]
    exact le_iSup_of_le n (by rw [ite_eq_left hcond', mul_one])

theorem measurable_cardFun_cluster [Countable E] (G : BondGraph V E) (x : V) :
    Measurable fun ω : Set E => cardFun (cluster G ω x) := by
  have hfun : (fun ω : Set E => cardFun (cluster G ω x)) = fun ω =>
      ⨆ n : ℕ, (n : ℝ≥0∞) * (clusterLarge G x n).indicator (fun _ => (1 : ℝ≥0∞)) ω := by
    funext ω
    rw [cardFun]
    refine iSup_congr fun n => ?_
    by_cases h : ∃ t : Finset V, n ≤ t.card ∧ (t : Set V) ⊆ cluster G ω x
    · have h' : ω ∈ clusterLarge G x n := h
      rw [ite_eq_left h, Set.indicator_of_mem h', mul_one]
    · have h' : ω ∉ clusterLarge G x n := h
      rw [ite_eq_right h, Set.indicator_of_notMem h', mul_zero]
  rw [hfun]
  exact Measurable.iSup fun n =>
    measurable_const.mul (measurable_const.indicator (measurableSet_clusterLarge G x n))

end CardFun

section Instance
attribute [local instance] Classical.propDecidable

/-- **Lemma I.2.1(i) for the extended cluster cardinality**: for all `x`, `y`,
`E[1(x ↮ y) |K_x| |K_y|] ≤ E|K_x| · E|K_y|` in `ℝ≥0∞`, where `|K| = ⊤` for infinite clusters. -/
theorem twoCluster_cardFun_lintegral [Countable E] (G : BondGraph V E)
    (p : E → unitInterval) (hp : ∀ e, p e < 1) (x y : V) (𝓔 : ℕ → Finset E)
    (h𝓔mono : Monotone 𝓔) (h𝓔 : ∀ e : E, ∃ n, e ∈ 𝓔 n) :
    ∫⁻ ω, ({ω : Set E | ¬ Conn G ω x y}).indicator (fun _ => (1 : ℝ≥0∞)) ω *
        (cardFun (cluster G ω x) * cardFun (cluster G ω y)) ∂(edgeLaw p)
      ≤ (∫⁻ ω, cardFun (cluster G ω x) ∂(edgeLaw p)) *
          (∫⁻ ω, cardFun (cluster G ω y) ∂(edgeLaw p)) :=
  twoCluster_functional_ennreal G p hp x y 𝓔 h𝓔mono h𝓔 cardFun_mono cardFun_mono
    (cardFun_cont 𝓔 h𝓔mono h𝓔 G x) (cardFun_cont 𝓔 h𝓔mono h𝓔 G y)
    (measurable_cardFun_cluster G x) (measurable_cardFun_cluster G y)

end Instance

end Percolation

end PercLib.CriticalLRP
