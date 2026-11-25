/-
Copyright (c) 2026 PercLib contributors. Released under Apache 2.0.

# One-step renewal and one-coordinate independence

Accepted from independent audit `smwp7ai5u` direction D3.  This is a
pruning/independence ingredient, not the higher-moment induction.  The
high-temperature moment recursion and its critical tree-graph input remain open.
-/

module

public import PercLib.CriticalLRP.CountableProduct.Renewal.Defs
public import Mathlib.Data.Set.Card.Arithmetic
public import PercLib.Probability.Coordinate
public import PercLib.Probability.Cylinder

set_option autoImplicit false
set_option linter.unusedSectionVars false

attribute [local instance] Classical.propDecidable

@[expose] public section

open MeasureTheory Set
open PercLib.Percolation.Bond PercLib.Probability
open scoped ENNReal NNReal

namespace PercLib.CriticalLRP.Renewal

variable {V : Type*} [Countable V]

theorem setVol_eq_encard (S : Set V) : setVol S = ((S.encard : ℕ∞) : ℝ≥0∞) := by
  rw [setVol, ← tsum_subtype S (fun _ => (1 : ℝ≥0∞)), ENNReal.tsum_set_one]

theorem setVol_mono {S T : Set V} (h : S ⊆ T) : setVol S ≤ setVol T := by
  refine ENNReal.tsum_le_tsum fun z => ?_
  by_cases hz : z ∈ S
  · rw [Set.indicator_of_mem hz, Set.indicator_of_mem (h hz)]
  · rw [Set.indicator_of_notMem hz]
    exact zero_le

theorem indicator_union_le (S T : Set V) (z : V) :
    (S ∪ T).indicator (fun _ => (1 : ℝ≥0∞)) z
      ≤ S.indicator (fun _ => (1 : ℝ≥0∞)) z + T.indicator (fun _ => (1 : ℝ≥0∞)) z := by
  by_cases hS : z ∈ S
  · rw [Set.indicator_of_mem (mem_union_left T hS), Set.indicator_of_mem hS]
    exact le_add_right le_rfl
  · by_cases hT : z ∈ T
    · rw [Set.indicator_of_mem (mem_union_right S hT), Set.indicator_of_notMem hS,
        Set.indicator_of_mem hT]
      exact le_add_left le_rfl
    · rw [Set.indicator_of_notMem (by simp [hS, hT]), Set.indicator_of_notMem hS,
        Set.indicator_of_notMem hT]
      simp

theorem setVol_union_le (S T : Set V) : setVol (S ∪ T) ≤ setVol S + setVol T := by
  refine (ENNReal.tsum_le_tsum fun z => indicator_union_le S T z).trans (le_of_eq ?_)
  rw [ENNReal.tsum_add]
  rfl

theorem setVol_singleton (a : V) : setVol ({a} : Set V) = 1 := by
  rw [setVol_eq_encard]
  simp

theorem setVol_insert_le (S : Set V) (a : V) : setVol (insert a S) ≤ setVol S + 1 := by
  have h := setVol_union_le ({a} : Set V) S
  rw [Set.singleton_union, setVol_singleton, add_comm] at h
  exact h

theorem setVol_iUnion_le {ι : Type*} (f : ι → Set V) :
    setVol (⋃ i, f i) ≤ ∑' i, setVol (f i) := by
  refine (ENNReal.tsum_le_tsum fun z => ?_).trans (le_of_eq ENNReal.tsum_comm)
  by_cases h : z ∈ ⋃ i, f i
  · obtain ⟨j, hj⟩ := mem_iUnion.1 h
    refine le_trans (le_of_eq ?_) (ENNReal.le_tsum j)
    rw [Set.indicator_of_mem h, Set.indicator_of_mem hj]
  · rw [Set.indicator_of_notMem h]
    exact zero_le



/-! ## The one-step renewal decomposition of the cluster -/

theorem renewTerm_of_pos {ω : Config V} {o y : V} (h : y ≠ o ∧ s(o, y) ∈ ω) :
    renewTerm ω o y = cluster (ω ∩ blockT o) y := by
  refine Set.ext fun z => ⟨fun hz => hz.2.2, fun hz => ⟨h.1, h.2, hz⟩⟩

theorem renewTerm_of_neg {ω : Config V} {o y : V} (h : ¬(y ≠ o ∧ s(o, y) ∈ ω)) :
    renewTerm ω o y = ∅ := by
  refine Set.eq_empty_iff_forall_notMem.2 fun z => ?_
  rintro ⟨h1, h2, -⟩
  exact h ⟨h1, h2⟩

theorem mem_renewTerm {ω : Config V} {o y z : V} (h : z ∈ renewTerm ω o y) :
    y ≠ o ∧ s(o, y) ∈ ω ∧ z ∈ cluster (ω ∩ blockT o) y := h

/-- **The root is isolated once every edge at `o` is closed.** -/
theorem not_mem_cluster_blockT {ω : Config V} {o y : V} (hy : y ≠ o) :
    o ∉ cluster (ω ∩ blockT o) y := by
  intro h
  have h2 : (SimpleGraph.fromEdgeSet (ω ∩ blockT o)).Reachable y o := h
  rw [SimpleGraph.reachable_fromEdgeSet_eq_reflTransGen_toRel] at h2
  rcases Relation.ReflTransGen.cases_tail h2 with rfl | ⟨c, _, hco⟩
  · exact hy rfl
  · exact hco.2 (Sym2.mem_mk_right c o)

/-- Transport of `ReflTransGen` membership along a step-closed set. -/
theorem mem_of_reflTransGen {r : V → V → Prop} {S : Set V}
    (hcl : ∀ x ∈ S, ∀ y, r x y → y ∈ S) {a b : V} (ha : a ∈ S)
    (h : Relation.ReflTransGen r a b) : b ∈ S := by
  induction h with
  | refl => exact ha
  | tail _ hbc ih => exact hcl _ ih _ hbc

/-- **One-step renewal (renewal recursion) for the open cluster.**

Closing every edge at the root `o` splits the cluster of `o` into the root itself together
with the pruned clusters of its open neighbours.  No finiteness, no independence and no
range hypothesis is used: this is a deterministic statement about one configuration. -/
theorem cluster_subset_renewal (ω : Config V) (o : V) :
    cluster ω o ⊆ insert o (⋃ y : V, renewTerm ω o y) := by
  classical
  have hcl : ∀ x ∈ (insert o (⋃ y : V, renewTerm ω o y) : Set V), ∀ y : V,
      Sym2.ToRel ω x y → y ∈ insert o (⋃ y : V, renewTerm ω o y) := by
    intro x hx y hxy
    have hxy' : s(x, y) ∈ ω := hxy
    by_cases hxo : x = o
    · rw [hxo] at hx hxy'
      by_cases hy : y = o
      · rw [hy]; exact Set.mem_insert_iff.2 (Or.inl rfl)
      · refine Set.mem_insert_iff.2 (Or.inr (Set.mem_iUnion.2 ⟨y, ?_⟩))
        exact ⟨hy, hxy', SimpleGraph.Reachable.refl y⟩
    · have hxU : x ∈ ⋃ y : V, renewTerm ω o y := by
        rcases Set.mem_insert_iff.1 hx with h | h
        · exact absurd h hxo
        · exact h
      obtain ⟨y₀, hy₀⟩ := Set.mem_iUnion.1 hxU
      obtain ⟨hy₀ne, hY₀, hxcl⟩ := mem_renewTerm hy₀
      have hxne : x ≠ o := fun h => not_mem_cluster_blockT hy₀ne (h ▸ hxcl)
      by_cases hy : y = o
      · rw [hy]; exact Set.mem_insert_iff.2 (Or.inl rfl)
      · by_cases hyx : y = x
        · rw [hyx]; exact Set.mem_insert_iff.2 (Or.inr hxU)
        · have hstep : s(x, y) ∈ ω ∩ blockT o := by
            refine ⟨hxy', ?_⟩
            intro hmem
            rcases Sym2.mem_iff.1 hmem with h' | h'
            · exact hxne h'.symm
            · exact hy h'.symm
          have hadj : (SimpleGraph.fromEdgeSet (ω ∩ blockT o)).Adj x y := by
            rw [SimpleGraph.fromEdgeSet_adj]
            exact ⟨hstep, fun h => hyx h.symm⟩
          refine Set.mem_insert_iff.2 (Or.inr (Set.mem_iUnion.2 ⟨y₀, ?_⟩))
          exact ⟨hy₀ne, hY₀, SimpleGraph.Reachable.trans hxcl hadj.reachable⟩
  intro z hz
  have h2 : Relation.ReflTransGen (Sym2.ToRel ω) o z := by
    have h3 : (SimpleGraph.fromEdgeSet ω).Reachable o z := hz
    rwa [SimpleGraph.reachable_fromEdgeSet_eq_reflTransGen_toRel] at h3
  exact mem_of_reflTransGen hcl (Set.mem_insert_iff.2 (Or.inl rfl)) h2

/-- **The renewal decomposition in counting measure.** -/
theorem setVol_cluster_le_renewal (ω : Config V) (o : V) :
    setVol (cluster ω o) ≤ 1 + ∑' y : V, setVol (renewTerm ω o y) := by
  refine (setVol_mono (cluster_subset_renewal ω o)).trans ?_
  refine (setVol_insert_le (⋃ y : V, renewTerm ω o y) o).trans ?_
  rw [add_comm (setVol (⋃ y : V, renewTerm ω o y)) 1]
  exact add_le_add (le_refl 1) (setVol_iUnion_le (renewTerm ω o))

/-- **The renewal bound for the cluster volume.** -/
theorem encard_cluster_le_renewal (ω : Config V) (o : V) :
    ((cluster ω o).encard : ℝ≥0∞) ≤ 1 + ∑' y : V, setVol (renewTerm ω o y) := by
  rw [← setVol_eq_encard]
  exact setVol_cluster_le_renewal ω o
/-! ## The renewal recursion in the form consumed by a moment recursion -/

theorem setVol_empty : setVol (∅ : Set V) = 0 := by
  simp [setVol]


/-- The renewal term is the pruned cluster of `y` when `{o,y}` is open, and nothing else. -/
theorem setVol_renewTerm (ω : Config V) (o y : V) :
    setVol (renewTerm ω o y)
      = if (y ≠ o ∧ s(o, y) ∈ ω) then ((cluster (ω ∩ blockT o) y).encard : ℝ≥0∞) else 0 := by
  by_cases hc : y ≠ o ∧ s(o, y) ∈ ω
  · rw [renewTerm_of_pos hc, setVol_eq_encard, ite_eq_left hc]
  · rw [renewTerm_of_neg hc, ite_eq_right hc, setVol_empty]

/-- **The renewal ("branching") recursion for the cluster volume**, with the open-edge
indicators of the root exposed.  This is the shape a moment recursion consumes: the
`q`-th moment of `|K_o|` is bounded by the `q`-th moment of a sum of at most one pruned
cluster per open edge at `o`, and the pruned clusters are measurable functions of the
edges *not* at `o`. -/
theorem encard_cluster_le_offspring (ω : Config V) (o : V) :
    ((cluster ω o).encard : ℝ≥0∞)
      ≤ 1 + ∑' y : V,
          (if (y ≠ o ∧ s(o, y) ∈ ω) then ((cluster (ω ∩ blockT o) y).encard : ℝ≥0∞) else 0) := by
  refine (encard_cluster_le_renewal ω o).trans ?_
  have h : (∑' y : V, setVol (renewTerm ω o y))
      = ∑' y : V,
          (if (y ≠ o ∧ s(o, y) ∈ ω) then ((cluster (ω ∩ blockT o) y).encard : ℝ≥0∞) else 0) :=
    tsum_congr fun y => setVol_renewTerm ω o y
  rw [h]




/-! ## The single-coordinate independence step of the moment recursion -/

/-- **Single-coordinate factorisation for `ℝ≥0∞` lintegrals.**  If `G` depends only on the
coordinates other than `e` (`G ω = G (ω \ {e})`), then averaging the indicator of `e ∈ ω`
against `G` costs exactly the factor `π e`.  This is the one independence step the cluster
moment recursion needs; it is proved from the affine decomposition
`prodBernoulli_eq_smul_add_smul` of the Bernoulli law in one coordinate. -/
theorem lintegral_indicator_mul_of_sdiff_determined
    (π : Sym2 V → unitInterval) (e : Sym2 V) {G : Config V → ℝ≥0∞}
    (hG : Measurable G) (hdet : ∀ ω : Config V, G ω = G (ω \ {e})) :
    ∫⁻ ω, (if e ∈ ω then G ω else 0) ∂(law π)
      = ((unitInterval.toNNReal (π e) : ℝ≥0) : ℝ≥0∞) * ∫⁻ ω, G ω ∂(law π) := by
  classical
  set μ₁ : Measure (Config V) := law (Function.update π e 1) with hμ₁
  set μ₀ : Measure (Config V) := law (Function.update π e 0) with hμ₀
  have hsplit : law π
      = ((unitInterval.toNNReal (π e) : ℝ≥0) : ℝ≥0∞) • μ₁
        + ((unitInterval.toNNReal (unitInterval.symm (π e)) : ℝ≥0) : ℝ≥0∞) • μ₀ :=
    prodBernoulli_eq_smul_add_smul π e
  have hT : Measurable fun ω : Config V => ω \ {e} := measurable_diff_singleton e
  have hmap₁ : μ₁.map (fun ω : Config V => ω \ {e}) = μ₀ := by
    rw [hμ₁, hμ₀]
    show (prodBernoulli (Function.update π e 1)).map (fun ω => ω \ {e}) = prodBernoulli (Function.update π e 0)
    rw [prodBernoulli_map_diff_singleton]
    simp
  have hmap₀ : (law π).map (fun ω : Config V => ω \ {e}) = μ₀ := by
    rw [hμ₀]
    show (prodBernoulli π).map (fun ω => ω \ {e}) = prodBernoulli (Function.update π e 0)
    rw [prodBernoulli_map_diff_singleton]
  have h₁ : ∫⁻ ω, G ω ∂μ₁ = ∫⁻ ω, G ω ∂μ₀ := by
    calc ∫⁻ ω, G ω ∂μ₁ = ∫⁻ ω, G (ω \ {e}) ∂μ₁ :=
          lintegral_congr fun ω => hdet ω
      _ = ∫⁻ ω, G ω ∂(μ₁.map (fun ω : Config V => ω \ {e})) :=
          (lintegral_map hG hT).symm
      _ = ∫⁻ ω, G ω ∂μ₀ := by rw [hmap₁]
  have h₂ : ∫⁻ ω, G ω ∂(law π) = ∫⁻ ω, G ω ∂μ₀ := by
    calc ∫⁻ ω, G ω ∂(law π) = ∫⁻ ω, G (ω \ {e}) ∂(law π) :=
          lintegral_congr fun ω => hdet ω
      _ = ∫⁻ ω, G ω ∂((law π).map (fun ω : Config V => ω \ {e})) :=
          (lintegral_map hG hT).symm
      _ = ∫⁻ ω, G ω ∂μ₀ := by rw [hmap₀]
  have hmem₁ : μ₁ {ω : Config V | e ∈ ω} = 1 := by
    have h := prodBernoulli_subset (Function.update π e 1) ({e} : Finset (Sym2 V))
    have hset : ({ω : Config V | e ∈ ω})
        = {ω : Config V | ((({e} : Finset (Sym2 V)) : Set (Sym2 V)) ⊆ ω)} := by
      ext ω; simp
    rw [show μ₁ {ω : Config V | e ∈ ω}
        = prodBernoulli (Function.update π e 1) {ω : Config V | e ∈ ω} from rfl, hset, h]
    simp
  have hmem₀ : μ₀ {ω : Config V | e ∈ ω} = 0 := by
    have h := prodBernoulli_subset (Function.update π e 0) ({e} : Finset (Sym2 V))
    have hset : ({ω : Config V | e ∈ ω})
        = {ω : Config V | ((({e} : Finset (Sym2 V)) : Set (Sym2 V)) ⊆ ω)} := by
      ext ω; simp
    rw [show μ₀ {ω : Config V | e ∈ ω}
        = prodBernoulli (Function.update π e 0) {ω : Config V | e ∈ ω} from rfl, hset, h]
    simp
  have hint₁ : ∫⁻ ω, (if e ∈ ω then G ω else 0) ∂μ₁ = ∫⁻ ω, G ω ∂μ₁ := by
    refine lintegral_congr_ae ?_
    have hae : ∀ᵐ ω ∂μ₁, e ∈ ω := by
      rw [MeasureTheory.ae_iff]
      have hcompl : μ₁ ({ω : Config V | e ∈ ω}ᶜ) = 0 := by
        rw [MeasureTheory.measure_compl (μ := μ₁) (s := {ω : Config V | e ∈ ω})
          (measurableSet_mem e) (by rw [hmem₁]; simp), hmem₁]
        simp
      simpa [Set.compl_ofPred] using hcompl
    filter_upwards [hae] with ω hω
    rw [ite_eq_left hω]
  have hint₀ : ∫⁻ ω, (if e ∈ ω then G ω else 0) ∂μ₀ = 0 := by
    have hae : ∀ᵐ ω ∂μ₀, ¬ (e ∈ ω) := by
      rw [MeasureTheory.ae_iff]
      simpa using hmem₀
    calc ∫⁻ ω, (if e ∈ ω then G ω else 0) ∂μ₀
        = ∫⁻ _ : Config V, (0 : ℝ≥0∞) ∂μ₀ := by
          refine lintegral_congr_ae ?_
          filter_upwards [hae] with ω hω
          rw [ite_eq_right hω]
      _ = 0 := by simp
  calc ∫⁻ ω, (if e ∈ ω then G ω else 0) ∂(law π)
      = ((unitInterval.toNNReal (π e) : ℝ≥0) : ℝ≥0∞)
          * ∫⁻ ω, (if e ∈ ω then G ω else 0) ∂μ₁
        + ((unitInterval.toNNReal (unitInterval.symm (π e)) : ℝ≥0) : ℝ≥0∞)
          * ∫⁻ ω, (if e ∈ ω then G ω else 0) ∂μ₀ := by
        rw [hsplit, lintegral_add_measure, lintegral_smul_measure, lintegral_smul_measure,
          smul_eq_mul, smul_eq_mul]
    _ = ((unitInterval.toNNReal (π e) : ℝ≥0) : ℝ≥0∞) * ∫⁻ ω, G ω ∂μ₁
        + ((unitInterval.toNNReal (unitInterval.symm (π e)) : ℝ≥0) : ℝ≥0∞) * 0 := by
        rw [hint₁, hint₀]
    _ = ((unitInterval.toNNReal (π e) : ℝ≥0) : ℝ≥0∞) * ∫⁻ ω, G ω ∂(law π) := by
        rw [h₁, ← h₂, mul_zero, add_zero]

/-! ## Axiom audit -/

#print axioms PercLib.CriticalLRP.Renewal.setVol_eq_encard
#print axioms PercLib.CriticalLRP.Renewal.setVol_iUnion_le
#print axioms PercLib.CriticalLRP.Renewal.not_mem_cluster_blockT
#print axioms PercLib.CriticalLRP.Renewal.cluster_subset_renewal
#print axioms PercLib.CriticalLRP.Renewal.encard_cluster_le_renewal
#print axioms PercLib.CriticalLRP.Renewal.setVol_renewTerm
#print axioms PercLib.CriticalLRP.Renewal.encard_cluster_le_offspring
#print axioms PercLib.CriticalLRP.Renewal.lintegral_indicator_mul_of_sdiff_determined

end PercLib.CriticalLRP.Renewal