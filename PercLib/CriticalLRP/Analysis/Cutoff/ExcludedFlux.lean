/-
Member `m3` of swarm `smwtvrwnn`, direction D1C.

The `(1 - q_e)` factor of the literal source derivative weight
`M.cutEdgeDeriv r e = β_c (-K'(r)) exp(-β_c J_r(e))` is *exactly* `1 - q_e(r)`
because `q_e(r) = 1 - exp(-β_c J_r(e))`.  The paper's standardized excluded flux
`β_c |K'| E[ |K_0| Σ_{y ∈ B_r} 1(y ∉ K_0) |K_y| ]` carries no such factor, so the
identification of the literal per-edge Russo flux with the standardized one needs the
statement that multiplying a pivotal flux by `1 - q_e` is the same as transporting the
factor into the law as the probability of the closed event `e ∉ ω`.

This file contains that step, at the level of a general observation `g`:
`(1 - q_e) * pivotalFlux μ g e = ∫ ω, 1{e ∉ ω} * (g (ω ∪ {e}) - g ω) ∂μ`.
The proof is the single-coordinate factorisation of the Bernoulli law (the closed-coordinate
mirror of `Renewal.lintegral_indicator_mul_of_sdiff_determined`), so it uses no conditional
measure, no finite moment and no model hypothesis.
-/
module

public import PercLib.CriticalLRP.CountableProduct.Renewal
public import PercLib.CriticalLRP.RussoInf.FluxBase
public import PercLib.CriticalLRP.Analysis.Cutoff.ExcludedFlux.Defs
public import PercLib.CriticalLRP.BK.TwoCopy

/-!
Closed-coordinate factorization and per-edge excluded-flux identities.  This is an intermediate
package, not the full edge-sum reindexing or ODE-level derivative identity.
-/

set_option autoImplicit false
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false

open MeasureTheory Set
open scoped ENNReal NNReal

@[expose] public section

namespace PercLib.CriticalLRP.Orchestration

attribute [local instance] Classical.propDecidable

variable {V : Type*} [Countable V]

/-! ## The two single-edge replacement maps -/

/-- Forcing the single edge `e` open is the same as adding it to the configuration. -/
theorem forceOn_singleton_open_eq (e : Sym2 V) (ω : Config V) :
    forceOn {e} ({e} : Config V) ω = ω ∪ {e} := by
  ext e'
  by_cases h : e' = e
  · rw [h]; simp [forceOn]
  · simp [forceOn, h]

/-- Forcing the single edge `e` closed is the same as deleting it. -/
theorem forceOn_singleton_closed_eq (e : Sym2 V) (ω : Config V) :
    forceOn {e} (∅ : Config V) ω = ω \ {e} := by
  ext e'
  by_cases h : e' = e
  · rw [h]; simp [forceOn]
  · simp [forceOn, h]

/-- Opening `e` after closing it is just opening it. -/
theorem forceOn_singleton_open_closed (e : Sym2 V) (ω : Config V) :
    forceOn {e} ({e} : Config V) (forceOn {e} (∅ : Config V) ω)
      = forceOn {e} ({e} : Config V) ω := by
  rw [forceOn_singleton_open_eq, forceOn_singleton_closed_eq, forceOn_singleton_open_eq,
    Set.sdiff_union_self]

/-- The map `ω ↦ ω ∪ {e}` is measurable. -/
theorem measurable_union_singleton (e : Sym2 V) :
    Measurable fun ω : Config V => ω ∪ {e} := by
  simpa only [Set.insert_eq, Set.union_comm] using PercLib.Probability.measurable_insert e

/-! ## Single-coordinate factorisation at a closed coordinate -/

/-- **Single-coordinate factorisation at a closed coordinate.**

If `G` depends only on the coordinates other than `e`, then averaging the indicator of the
*closed* event `e ∉ ω` against `G` costs exactly the factor `1 - π e`.  This is the mirror
of `PercLib.CriticalLRP.Renewal.lintegral_indicator_mul_of_sdiff_determined` (which handles
the open event and the factor `π e`); the same affine decomposition of the Bernoulli law in
one coordinate is used. -/
theorem lintegral_compl_indicator_mul_of_sdiff_determined
    (π : Sym2 V → unitInterval) (e : Sym2 V) {G : Config V → ℝ≥0∞}
    (hG : Measurable G) (hdet : ∀ ω : Config V, G ω = G (ω \ {e})) :
    ∫⁻ ω, (if e ∈ ω then 0 else G ω) ∂(PercLib.Percolation.Bond.law π)
      = ((unitInterval.toNNReal (unitInterval.symm (π e)) : ℝ≥0) : ℝ≥0∞)
        * ∫⁻ ω, G ω ∂(PercLib.Percolation.Bond.law π) := by
  classical
  set μ₁ : Measure (Config V) :=
    PercLib.Percolation.Bond.law (Function.update π e 1) with hμ₁
  set μ₀ : Measure (Config V) :=
    PercLib.Percolation.Bond.law (Function.update π e 0) with hμ₀
  have hsplit : PercLib.Percolation.Bond.law π
      = ((unitInterval.toNNReal (π e) : ℝ≥0) : ℝ≥0∞) • μ₁
        + ((unitInterval.toNNReal (unitInterval.symm (π e)) : ℝ≥0) : ℝ≥0∞) • μ₀ :=
    PercLib.Probability.prodBernoulli_eq_smul_add_smul π e
  have hT : Measurable fun ω : Config V => ω \ {e} :=
    PercLib.Probability.measurable_diff_singleton e
  have hmap₀ : (PercLib.Percolation.Bond.law π).map (fun ω : Config V => ω \ {e}) = μ₀ := by
    rw [hμ₀]
    exact PercLib.Probability.prodBernoulli_map_diff_singleton π e
  have h₂ : ∫⁻ ω, G ω ∂(PercLib.Percolation.Bond.law π) = ∫⁻ ω, G ω ∂μ₀ := by
    calc ∫⁻ ω, G ω ∂(PercLib.Percolation.Bond.law π)
        = ∫⁻ ω, G (ω \ {e}) ∂(PercLib.Percolation.Bond.law π) :=
          lintegral_congr fun ω => hdet ω
      _ = ∫⁻ ω, G ω ∂((PercLib.Percolation.Bond.law π).map
            (fun ω : Config V => ω \ {e})) := (lintegral_map hG hT).symm
      _ = ∫⁻ ω, G ω ∂μ₀ := by rw [hmap₀]
  have hmem₁ : μ₁ {ω : Config V | e ∈ ω} = 1 := by
    have h := PercLib.Probability.prodBernoulli_subset
      (Function.update π e 1) ({e} : Finset (Sym2 V))
    have hset : ({ω : Config V | e ∈ ω})
        = {ω : Config V | ((({e} : Finset (Sym2 V)) : Set (Sym2 V)) ⊆ ω)} := by
      ext ω; simp
    rw [show μ₁ {ω : Config V | e ∈ ω}
        = PercLib.Probability.prodBernoulli (Function.update π e 1)
            {ω : Config V | e ∈ ω} from rfl, hset, h]
    simp
  have hmem₀ : μ₀ {ω : Config V | e ∈ ω} = 0 := by
    have h := PercLib.Probability.prodBernoulli_subset
      (Function.update π e 0) ({e} : Finset (Sym2 V))
    have hset : ({ω : Config V | e ∈ ω})
        = {ω : Config V | ((({e} : Finset (Sym2 V)) : Set (Sym2 V)) ⊆ ω)} := by
      ext ω; simp
    rw [show μ₀ {ω : Config V | e ∈ ω}
        = PercLib.Probability.prodBernoulli (Function.update π e 0)
            {ω : Config V | e ∈ ω} from rfl, hset, h]
    simp
  have hint₁ : ∫⁻ ω, (if e ∈ ω then 0 else G ω) ∂μ₁ = 0 := by
    have hae : ∀ᵐ ω ∂μ₁, e ∈ ω := by
      rw [MeasureTheory.ae_iff]
      have hcompl : μ₁ ({ω : Config V | e ∈ ω}ᶜ) = 0 := by
        rw [MeasureTheory.measure_compl (μ := μ₁) (s := {ω : Config V | e ∈ ω})
          (measurableSet_mem e) (by rw [hmem₁]; simp), hmem₁]
        simp
      simpa [Set.compl_ofPred] using hcompl
    calc ∫⁻ ω, (if e ∈ ω then 0 else G ω) ∂μ₁
        = ∫⁻ _ : Config V, (0 : ℝ≥0∞) ∂μ₁ := by
          refine lintegral_congr_ae ?_
          filter_upwards [hae] with ω hω
          rw [ite_eq_left hω]
      _ = 0 := by simp
  have hint₀ : ∫⁻ ω, (if e ∈ ω then 0 else G ω) ∂μ₀ = ∫⁻ ω, G ω ∂μ₀ := by
    have hae : ∀ᵐ ω ∂μ₀, ¬ (e ∈ ω) := by
      rw [MeasureTheory.ae_iff]
      simpa using hmem₀
    refine lintegral_congr_ae ?_
    filter_upwards [hae] with ω hω
    rw [ite_eq_right hω]
  calc ∫⁻ ω, (if e ∈ ω then 0 else G ω) ∂(PercLib.Percolation.Bond.law π)
      = ((unitInterval.toNNReal (π e) : ℝ≥0) : ℝ≥0∞)
          * ∫⁻ ω, (if e ∈ ω then 0 else G ω) ∂μ₁
        + ((unitInterval.toNNReal (unitInterval.symm (π e)) : ℝ≥0) : ℝ≥0∞)
          * ∫⁻ ω, (if e ∈ ω then 0 else G ω) ∂μ₀ := by
        rw [hsplit, lintegral_add_measure, lintegral_smul_measure, lintegral_smul_measure,
          smul_eq_mul, smul_eq_mul]
    _ = ((unitInterval.toNNReal (π e) : ℝ≥0) : ℝ≥0∞) * 0
        + ((unitInterval.toNNReal (unitInterval.symm (π e)) : ℝ≥0) : ℝ≥0∞)
          * ∫⁻ ω, G ω ∂μ₀ := by
        rw [hint₁, hint₀]
    _ = ((unitInterval.toNNReal (unitInterval.symm (π e)) : ℝ≥0) : ℝ≥0∞)
          * ∫⁻ ω, G ω ∂(PercLib.Percolation.Bond.law π) := by
        rw [← h₂]; simp

end PercLib.CriticalLRP.Orchestration

namespace PercLib.CriticalLRP.Orchestration

variable {V : Type*} [Countable V]

attribute [local instance] Classical.propDecidable

/-- **Real-valued single-coordinate factorisation at a closed coordinate**, nonnegative case. -/
theorem integral_compl_indicator_mul_of_sdiff_determined
    (π : Sym2 V → unitInterval) (e : Sym2 V) {G : Config V → ℝ}
    (hG : Measurable G) (hdet : ∀ ω : Config V, G ω = G (ω \ {e}))
    (hnn : ∀ ω : Config V, 0 ≤ G ω) :
    ∫ ω, (if e ∈ ω then 0 else G ω) ∂(PercLib.Percolation.Bond.law π)
      = (1 - (π e : ℝ)) * ∫ ω, G ω ∂(PercLib.Percolation.Bond.law π) := by
  classical
  have hmeas' : Measurable fun ω : Config V => (if e ∈ ω then (0 : ℝ) else G ω) :=
    Measurable.ite (measurableSet_mem e) measurable_const hG
  have hnn' : ∀ ω : Config V, 0 ≤ (if e ∈ ω then (0 : ℝ) else G ω) := by
    intro ω
    by_cases h : e ∈ ω
    · rw [ite_eq_left h]
    · rw [ite_eq_right h]; exact hnn ω
  have hstep := lintegral_compl_indicator_mul_of_sdiff_determined π e
    (G := fun ω : Config V => ENNReal.ofReal (G ω)) hG.ennreal_ofReal
    (fun ω => by rw [hdet ω])
  have hL : ∫ ω, (if e ∈ ω then 0 else G ω) ∂(PercLib.Percolation.Bond.law π)
      = (∫⁻ ω, (if e ∈ ω then 0 else ENNReal.ofReal (G ω))
          ∂(PercLib.Percolation.Bond.law π)).toReal := by
    rw [integral_eq_lintegral_of_nonneg_ae (Filter.Eventually.of_forall hnn')
      hmeas'.aestronglyMeasurable]
    congr 1
    refine lintegral_congr fun ω => ?_
    by_cases h : e ∈ ω <;> simp [h]
  have hR : ∫ ω, G ω ∂(PercLib.Percolation.Bond.law π)
      = (∫⁻ ω, ENNReal.ofReal (G ω)
          ∂(PercLib.Percolation.Bond.law π)).toReal :=
    integral_eq_lintegral_of_nonneg_ae (Filter.Eventually.of_forall hnn)
      hG.aestronglyMeasurable
  have hq : (((unitInterval.toNNReal (unitInterval.symm (π e)) : ℝ≥0) : ℝ≥0∞)).toReal
      = 1 - (π e : ℝ) := by
    rw [← unitInterval.coe_symm_eq (π e)]
    simp
  rw [hL, hR, hstep, ENNReal.toReal_mul, hq]

/-- A measurable function bounded by a constant is integrable for a probability measure. -/
theorem integrable_of_abs_le {μ : Measure (Config V)} [IsProbabilityMeasure μ]
    {G : Config V → ℝ} (hG : Measurable G) {C : ℝ} (hC : ∀ ω : Config V, |G ω| ≤ C) :
    Integrable G μ :=
  Integrable.of_bound hG.aestronglyMeasurable C
    (Filter.Eventually.of_forall fun ω => by rw [Real.norm_eq_abs]; exact hC ω)

/-- **Real-valued single-coordinate factorisation at a closed coordinate**, bounded case. -/
theorem integral_compl_indicator_mul_of_abs_le
    (π : Sym2 V → unitInterval) (e : Sym2 V) {G : Config V → ℝ}
    (hG : Measurable G) (hdet : ∀ ω : Config V, G ω = G (ω \ {e}))
    {C : ℝ} (hC : ∀ ω : Config V, |G ω| ≤ C) :
    ∫ ω, (if e ∈ ω then 0 else G ω) ∂(PercLib.Percolation.Bond.law π)
      = (1 - (π e : ℝ)) * ∫ ω, G ω ∂(PercLib.Percolation.Bond.law π) := by
  classical
  set μ := PercLib.Percolation.Bond.law π with hμ
  have hCnn : 0 ≤ C := le_trans (abs_nonneg (G (∅ : Config V))) (hC ∅)
  have hshift : ∀ ω : Config V, 0 ≤ G ω + C := by
    intro ω
    have := (abs_le.mp (hC ω)).1
    linarith
  have hdetshift : ∀ ω : Config V, G ω + C = G (ω \ {e}) + C := by
    intro ω; rw [hdet ω]
  have hmain := integral_compl_indicator_mul_of_sdiff_determined π e
    (G := fun ω : Config V => G ω + C) (hG.add measurable_const) hdetshift hshift
  have hI1 : Integrable (fun ω : Config V => if e ∈ ω then (0 : ℝ) else G ω) μ := by
    refine integrable_of_abs_le (G := fun ω : Config V => if e ∈ ω then (0 : ℝ) else G ω)
      (Measurable.ite (measurableSet_mem e) measurable_const hG) (C := C) ?_
    intro ω
    by_cases h : e ∈ ω
    · rw [ite_eq_left h, abs_zero]; exact hCnn
    · rw [ite_eq_right h]; exact hC ω
  have hI2 : Integrable G μ := integrable_of_abs_le hG hC
  have hI3 : Integrable (fun ω : Config V => if e ∈ ω then (0 : ℝ) else (1 : ℝ)) μ := by
    refine integrable_of_abs_le (G := fun ω : Config V => if e ∈ ω then (0 : ℝ) else (1 : ℝ))
      (Measurable.ite (measurableSet_mem e) measurable_const measurable_const) (C := 1) ?_
    intro ω
    by_cases h : e ∈ ω
    · rw [ite_eq_left h, abs_zero]; norm_num
    · rw [ite_eq_right h, abs_one]
  have hone : ∫ ω, (if e ∈ ω then (0 : ℝ) else (1 : ℝ)) ∂μ = 1 - (π e : ℝ) := by
    have h := integral_compl_indicator_mul_of_sdiff_determined π e
      (G := fun _ : Config V => (1 : ℝ)) measurable_const (fun ω => rfl) (fun _ => zero_le_one)
    rw [h, integral_const]
    simp
  have hsplit1 : ∫ ω, (if e ∈ ω then 0 else (G ω + C)) ∂μ
      = ∫ ω, (if e ∈ ω then 0 else G ω) ∂μ + C * ∫ ω, (if e ∈ ω then 0 else (1 : ℝ)) ∂μ := by
    rw [← integral_const_mul (μ := μ) C (fun ω : Config V => if e ∈ ω then (0 : ℝ) else (1 : ℝ)),
      ← integral_add (hI1) (hI3.const_mul C)]
    congr 1
    ext ω
    by_cases h : e ∈ ω <;> simp [h]
  rw [hsplit1, hone] at hmain
  have hsplit2 : (1 - (π e : ℝ)) * ∫ ω, (G ω + C) ∂μ
      = (1 - (π e : ℝ)) * ∫ ω, G ω ∂μ + (1 - (π e : ℝ)) * C := by
    rw [integral_add hI2 (integrable_const C), integral_const]
    simp
    ring
  rw [hsplit2] at hmain
  linarith [hmain]

end PercLib.CriticalLRP.Orchestration

namespace PercLib.CriticalLRP.Orchestration

variable {V : Type*} [Countable V]

attribute [local instance] Classical.propDecidable

/-- Deleting a fixed edge twice is deleting it once. -/
theorem sdiff_singleton_idem (e : Sym2 V) (ω : Config V) : (ω \ {e}) \ {e} = ω \ {e} := by
  ext x; by_cases hx : x = e <;> simp [hx]

/-- Adding back the deleted edge recovers the configuration with that edge. -/
theorem sdiff_singleton_union (e : Sym2 V) (ω : Config V) : (ω \ {e}) ∪ {e} = ω ∪ {e} :=
  Set.sdiff_union_self (s := ω) (t := {e})

/-- A configuration from which an absent edge is deleted is itself. -/
theorem sdiff_singleton_of_notMem {e : Sym2 V} {ω : Config V} (h : e ∉ ω) :
    ω \ {e} = ω := by
  ext x; by_cases hx : x = e <;> simp [hx, h]

/-- **The `(1 - q_e)` factor of the literal source derivative weight is absorbed by the
closed-edge event.**

At the actual source model the literal per-edge derivative weight is
`M.cutEdgeDeriv r e = β_c (-K'(r)) exp(-β_c J_r(e))`, and `exp(-β_c J_r(e)) = 1 - q_e(r)`
because `q_e(r) = 1 - exp(-β_c J_r(e))` (`M.cutProb_coe_eq`).  The paper's standardized
excluded flux carries no such factor.  This theorem is the exact identification: multiplying the
pivotal flux by `1 - q_e` is the same as replacing the surviving observation by its increment
across the flip, restricted to the closed event.

No moment finiteness, no domination and no model hypothesis enters: `g` only has to be a bounded
measurable real observation, and the measure is the independent-edge law. -/
theorem one_sub_mul_pivotalFlux_eq (π : Sym2 V → unitInterval) (e : Sym2 V)
    {g : Config V → ℝ} (hG : Measurable g) {C : ℝ} (hC : ∀ ω : Config V, |g ω| ≤ C) :
    (1 - (π e : ℝ)) * pivotalFlux (PercLib.Percolation.Bond.law π) g e
      = ∫ ω, (if e ∈ ω then 0 else (g (ω ∪ {e}) - g ω))
          ∂(PercLib.Percolation.Bond.law π) := by
  classical
  set μ := PercLib.Percolation.Bond.law π with hμ
  have hMsd : Measurable fun ω : Config V => ω \ {e} :=
    PercLib.Probability.measurable_diff_singleton e
  set P : Config V → ℝ := fun ω => g (ω ∪ {e}) with hP
  set Q : Config V → ℝ := fun ω => g (ω \ {e}) with hQ
  have hMP : Measurable P := hG.comp (measurable_union_singleton e)
  have hMQ : Measurable Q := hG.comp hMsd
  have hbP : ∀ ω : Config V, |P ω| ≤ C := fun ω => hC _
  have hbQ : ∀ ω : Config V, |Q ω| ≤ C := fun ω => hC _
  have hIP : Integrable P μ := integrable_of_abs_le hMP hbP
  have hIQ : Integrable Q μ := integrable_of_abs_le hMQ hbQ
  have hMPi : Measurable fun ω : Config V => (if e ∈ ω then (0 : ℝ) else P ω) :=
    Measurable.ite (measurableSet_mem e) measurable_const hMP
  have hMQi : Measurable fun ω : Config V => (if e ∈ ω then (0 : ℝ) else Q ω) :=
    Measurable.ite (measurableSet_mem e) measurable_const hMQ
  have hIPi : Integrable (fun ω : Config V => if e ∈ ω then (0 : ℝ) else P ω) μ :=
    integrable_of_abs_le (C := C) hMPi (by
      intro ω
      by_cases h : e ∈ ω
      · rw [ite_eq_left h]; simpa using (le_trans (abs_nonneg (P ∅)) (hbP ∅))
      · rw [ite_eq_right h]; exact hbP ω)
  have hIQi : Integrable (fun ω : Config V => if e ∈ ω then (0 : ℝ) else Q ω) μ :=
    integrable_of_abs_le (C := C) hMQi (by
      intro ω
      by_cases h : e ∈ ω
      · rw [ite_eq_left h]; simpa using (le_trans (abs_nonneg (Q ∅)) (hbQ ∅))
      · rw [ite_eq_right h]; exact hbQ ω)
  have hAP := integral_compl_indicator_mul_of_abs_le π e hMP
    (fun ω => (congrArg g (sdiff_singleton_union e ω)).symm) hbP
  have hAQ := integral_compl_indicator_mul_of_abs_le π e hMQ
    (fun ω => (congrArg g (sdiff_singleton_idem e ω)).symm) hbQ
  have hflip : pivotalFlux μ g e = ∫ ω, (P ω - Q ω) ∂μ := by
    unfold pivotalFlux
    congr 1
    funext ω
    simp only [flipDiff, forceOn_singleton_open_eq, forceOn_singleton_closed_eq, hP, hQ]
  calc (1 - (π e : ℝ)) * pivotalFlux μ g e
      = (1 - (π e : ℝ)) * ∫ ω, (P ω - Q ω) ∂μ := by rw [hflip]
    _ = (1 - (π e : ℝ)) * (∫ ω, P ω ∂μ - ∫ ω, Q ω ∂μ) := by
        rw [integral_sub hIP hIQ]
    _ = (1 - (π e : ℝ)) * ∫ ω, P ω ∂μ - (1 - (π e : ℝ)) * ∫ ω, Q ω ∂μ := by ring
    _ = (∫ ω, (if e ∈ ω then (0 : ℝ) else P ω) ∂μ)
          - ∫ ω, (if e ∈ ω then (0 : ℝ) else Q ω) ∂μ := by rw [← hAP, ← hAQ]
    _ = ∫ ω, ((if e ∈ ω then (0 : ℝ) else P ω)
          - (if e ∈ ω then (0 : ℝ) else Q ω)) ∂μ := by rw [integral_sub hIPi hIQi]
    _ = ∫ ω, (if e ∈ ω then (0 : ℝ) else (g (ω ∪ {e}) - g ω)) ∂μ := by
        congr 1
        funext ω
        by_cases h : e ∈ ω
        · simp [h]
        · rw [ite_eq_right h, ite_eq_right h, ite_eq_right h]
          simp only [hP, hQ]
          rw [sdiff_singleton_of_notMem h]

end PercLib.CriticalLRP.Orchestration

/-! ## Axiom audit -/

set_option linter.hashCommand false
set_option linter.style.longLine false

#print axioms PercLib.CriticalLRP.Orchestration.forceOn_singleton_open_eq
#print axioms PercLib.CriticalLRP.Orchestration.forceOn_singleton_closed_eq
#print axioms PercLib.CriticalLRP.Orchestration.forceOn_singleton_open_closed
#print axioms PercLib.CriticalLRP.Orchestration.measurable_union_singleton
#print axioms PercLib.CriticalLRP.Orchestration.lintegral_compl_indicator_mul_of_sdiff_determined
#print axioms PercLib.CriticalLRP.Orchestration.integral_compl_indicator_mul_of_sdiff_determined
#print axioms PercLib.CriticalLRP.Orchestration.integrable_of_abs_le
#print axioms PercLib.CriticalLRP.Orchestration.integral_compl_indicator_mul_of_abs_le
#print axioms PercLib.CriticalLRP.Orchestration.sdiff_singleton_idem
#print axioms PercLib.CriticalLRP.Orchestration.sdiff_singleton_union
#print axioms PercLib.CriticalLRP.Orchestration.sdiff_singleton_of_notMem
#print axioms PercLib.CriticalLRP.Orchestration.one_sub_mul_pivotalFlux_eq

/-! ## The literal source flux as a standardized closed-edge cluster-volume increment -/

namespace PercLib.CriticalLRP.Orchestration

open MeasureTheory
open scoped ENNReal NNReal

attribute [local instance] Classical.propDecidable

namespace SourceModelData

variable (M : SourceModelData)

/-- **The literal source derivative weight is `β_c (-K')` times the closed probability.**
On a genuine edge of length `≤ r` (no loop, no out-of-range edge), the derivative weight
`M.cutEdgeDeriv r e = β_c (-K'(r)) exp(-β_c J_r(e))` of `Deriv/Defs` equals
`β_c (-K'(r)) (1 - q_e(r))`: the exponential factor *is* the closed-edge probability. -/
theorem one_sub_cutProb_eq_exp (r : ℝ) {x y : M.V} (hxy : x ≠ y)
    (hdist : M.S.dist x y ≤ r) :
    1 - ((M.cutProb r s(x, y) : unitInterval) : ℝ)
      = Real.exp (-((M.betaCrit : ℝ) *
          FiniteVolume.cutoffProfile M.K r (M.S.dist x y))) := by
  rw [M.cutProb_coe_eq, M.cutKernel_mk, ite_eq_right hxy,
    FiniteVolume.cutoffProfile_of_le hdist]
  ring

/-- **The per-edge standardized flux identity at the actual source model.**

For a genuine edge `{x,y}` of length `≤ r` — the support of the derivative weight — the literal
per-edge Russo flux of the truncated cluster moment `|K_0 ∩ A|` is exactly `β_c (-K'(r))` times
the expectation, on the closed event `{x,y} ∉ ω`, of the cluster-volume increment produced by
opening that edge.

This is the exact reindexing/mass-transport step: the factor `exp(-β_c J_r(e)) = 1 - q_e(r)`
of `M.cutEdgeDeriv` is not a passive scalar that can be pulled out of a random cluster — it
cancels the closed-edge reweighting of the flip law, which is `<closed probability> * (flip law)`.

The statement is per edge: it needs no summability in `e`, no moment finiteness, and no
interchange of `r`-derivative with an infinite sum.  `A` is an arbitrary finite vertex set, so the
observation `|K_0 ∩ A|` is bounded by `|A|`. -/
theorem cutEdgeDeriv_mul_pivotalFlux_eq (A : Finset M.V) {r : ℝ} {x y : M.V} (hxy : x ≠ y)
    (hdist : M.S.dist x y ≤ r) :
    M.cutEdgeDeriv r s(x, y) *
        pivotalFlux (M.cutLaw r) (sMomentTrunc (fun _ => (1 : ℝ)) (0 : M.V) A) s(x, y)
      = (M.betaCrit : ℝ) * (-(deriv M.K r)) *
          ∫ ω, (if s(x, y) ∈ ω then 0 else
              (sMomentTrunc (fun _ => (1 : ℝ)) (0 : M.V) A (ω ∪ {s(x, y)})
                - sMomentTrunc (fun _ => (1 : ℝ)) (0 : M.V) A ω)) ∂(M.cutLaw r) := by
  classical
  have hG : Measurable (sMomentTrunc (fun _ => (1 : ℝ)) (0 : M.V) A) :=
    measurable_sMomentTrunc _ _ _
  have hC : ∀ ω : Config M.V, |sMomentTrunc (fun _ => (1 : ℝ)) (0 : M.V) A ω|
      ≤ (A.card : ℝ) := by
    intro ω
    simpa using abs_sMomentTrunc_le (fun _ => (1 : ℝ)) (0 : M.V) A ω
  have hcoef : M.cutEdgeDeriv r s(x, y)
      = (M.betaCrit : ℝ) * (-(deriv M.K r))
        * (1 - ((M.cutProb r s(x, y) : unitInterval) : ℝ)) := by
    rw [M.cutEdgeDeriv_mk, ite_eq_right hxy, ite_eq_left hdist,
      ← M.one_sub_cutProb_eq_exp r hxy hdist]
  have hflip := one_sub_mul_pivotalFlux_eq (M.cutProb r) s(x, y) hG (C := (A.card : ℝ)) hC
  have hlaw : M.cutLaw r = PercLib.Percolation.Bond.law (M.cutProb r) :=
    M.cutLaw_eq_edgeMeasure r
  rw [hlaw]
  rw [hcoef]
  calc (M.betaCrit : ℝ) * (-(deriv M.K r))
        * (1 - ((M.cutProb r s(x, y) : unitInterval) : ℝ))
        * pivotalFlux (PercLib.Percolation.Bond.law (M.cutProb r))
            (sMomentTrunc (fun _ => (1 : ℝ)) (0 : M.V) A) s(x, y)
      = (M.betaCrit : ℝ) * (-(deriv M.K r))
        * ((1 - ((M.cutProb r s(x, y) : unitInterval) : ℝ))
            * pivotalFlux (PercLib.Percolation.Bond.law (M.cutProb r))
                (sMomentTrunc (fun _ => (1 : ℝ)) (0 : M.V) A) s(x, y)) := by ring
    _ = (M.betaCrit : ℝ) * (-(deriv M.K r))
        * ∫ ω, (if s(x, y) ∈ ω then 0 else
              (sMomentTrunc (fun _ => (1 : ℝ)) (0 : M.V) A (ω ∪ {s(x, y)})
                - sMomentTrunc (fun _ => (1 : ℝ)) (0 : M.V) A ω))
            ∂(PercLib.Percolation.Bond.law (M.cutProb r)) := by rw [hflip]

end SourceModelData

end PercLib.CriticalLRP.Orchestration

/-! ## The cluster-volume increment of opening one edge -/

namespace PercLib.CriticalLRP.Orchestration

variable {V : Type*} [Countable V]

attribute [local instance] Classical.propDecidable

/-- A connection in `ω ∪ {s(x,y)}` already exists in `ω`, or reaches `x`, or reaches `y`.
(Proved by applying the prefix lemma `reflTransGen_union_singleton_or_endpoint` to the path and to
its reverse, which pins down both endpoints of the one added edge.) -/
theorem connects_union_edge_trichotomy (ω : Config V) (o x y v : V)
    (h : Connects (ω ∪ {s(x, y)}) o v) :
    Connects ω o v ∨ Connects ω x v ∨ Connects ω y v := by
  have toC : ∀ a b : V, Relation.ReflTransGen (openGraph ω).Adj a b → Connects ω a b := by
    intro a b hab
    change (openGraph ω).Reachable a b
    rw [SimpleGraph.reachable_iff_reflTransGen]
    exact hab
  have h' : Relation.ReflTransGen (openGraph (ω ∪ {s(x, y)})).Adj o v := by
    rw [← SimpleGraph.reachable_iff_reflTransGen]
    exact h
  rcases reflTransGen_union_singleton_or_endpoint h' with h1 | ⟨w, hw, hw'⟩
  · exact Or.inl (toC o v h1)
  have h'' : Relation.ReflTransGen (openGraph (ω ∪ {s(x, y)})).Adj v o := by
    rw [← SimpleGraph.reachable_iff_reflTransGen]
    exact connects_symm h
  rcases reflTransGen_union_singleton_or_endpoint h'' with h2 | ⟨w', hw', hw''⟩
  · exact Or.inl (connects_symm (toC v o h2))
  rw [Sym2.mem_iff] at hw hw'
  rcases hw with hwx | hwy <;> rcases hw' with hw'x | hw'y
  · rw [hwx] at hw'; rw [hw'x] at hw''
    exact Or.inl (connects_trans (toC o x hw') (connects_symm (toC v x hw'')))
  · rw [hwx] at hw'; rw [hw'y] at hw''
    exact Or.inr (Or.inr (connects_symm (toC v y hw'')))
  · rw [hwy] at hw'; rw [hw'x] at hw''
    exact Or.inr (Or.inl (connects_symm (toC v x hw'')))
  · rw [hwy] at hw'; rw [hw'y] at hw''
    exact Or.inl (connects_trans (toC o y hw') (connects_symm (toC v y hw'')))

/-- **Opening an edge merges only the clusters of its endpoints**: a vertex newly connected to `o`
lies in `cluster ω o`, or in `cluster ω x`, or in `cluster ω y`. -/
theorem mem_cluster_union_edge (ω : Config V) (o x y v : V)
    (hv : v ∈ cluster (ω ∪ {s(x, y)}) o) :
    v ∈ cluster ω o ∨ v ∈ cluster ω x ∨ v ∈ cluster ω y := by
  rcases connects_union_edge_trichotomy ω o x y v hv with h | h | h
  · exact Or.inl (mem_cluster_iff.mpr h)
  · exact Or.inr (Or.inl (mem_cluster_iff.mpr h))
  · exact Or.inr (Or.inr (mem_cluster_iff.mpr h))

/-- If both endpoints of the added edge already lie in the cluster of `o`, opening it changes
nothing. -/
theorem cluster_union_edge_eq_of_mem (ω : Config V) (o x y : V)
    (hx : Connects ω o x) (hy : Connects ω o y) :
    cluster (ω ∪ {s(x, y)}) o = cluster ω o := by
  refine Set.Subset.antisymm (fun v hv => ?_) (PercLib.CriticalLRP.cluster_mono
    (fun e he => Set.mem_union_left _ he) o)
  rcases mem_cluster_union_edge ω o x y v hv with h | h | h
  · exact h
  · exact mem_cluster_iff.mpr (connects_trans hx (mem_cluster_iff.mp h))
  · exact mem_cluster_iff.mpr (connects_trans hy (mem_cluster_iff.mp h))

/-- **The cluster grows by exactly `cluster ω y`.**  If `o` is connected to `x` and `y` is not
connected to `x`, then opening the edge `{x,y}` attaches the whole cluster of `y` to the cluster
of `o`. -/
theorem cluster_union_edge_eq_of_attach (ω : Config V) (o x y : V) (hxy : x ≠ y)
    (hx : Connects ω o x) (hnot : ¬ Connects ω x y) :
    cluster (ω ∪ {s(x, y)}) o = cluster ω o ∪ cluster ω y := by
  refine Set.Subset.antisymm (fun u hu => ?_) (fun u hu => ?_)
  · rcases mem_cluster_union_edge ω o x y u hu with h | h | h
    · exact Set.mem_union_left _ h
    · exact Set.mem_union_left _ (mem_cluster_iff.mpr (connects_trans hx (mem_cluster_iff.mp h)))
    · exact Set.mem_union_right _ h
  · rcases hu with hu | hu
    · exact PercLib.CriticalLRP.cluster_mono (fun e he => Set.mem_union_left _ he) o hu
    · have hstep : (openGraph (ω ∪ {s(x, y)})).Adj x y :=
        openGraph_adj.mpr ⟨hxy, Set.mem_union_right _ (Set.mem_singleton _)⟩
      have hy : Connects (ω ∪ {s(x, y)}) o y :=
        connects_trans (connects_mono (fun e he => Set.mem_union_left _ he) hx)
          (SimpleGraph.Adj.reachable hstep)
      exact mem_cluster_iff.mpr (connects_trans hy
        (connects_mono (fun e he => Set.mem_union_left _ he) (mem_cluster_iff.mp hu)))

/-- Under the attach hypothesis the two clusters are disjoint, so the indicators add. -/
theorem disjoint_cluster_of_not_connects (ω : Config V) (o x y : V)
    (hx : Connects ω o x) (hnot : ¬ Connects ω x y) :
    Disjoint (cluster ω o) (cluster ω y) := by
  refine Set.disjoint_left.mpr ?_
  intro u hu hu'
  exact hnot (connects_trans (connects_symm hx)
    (connects_trans (mem_cluster_iff.mp hu) (connects_symm (mem_cluster_iff.mp hu'))))

end PercLib.CriticalLRP.Orchestration

/-! ## The excluded cluster-volume increment of the truncated cluster moment -/

namespace PercLib.CriticalLRP.Orchestration

variable {V : Type*} [Countable V]

attribute [local instance] Classical.propDecidable

/-- If neither endpoint of the added edge lies in the cluster of `o`, opening it changes nothing. -/
theorem cluster_union_edge_eq_of_not_connects (ω : Config V) (o x y : V)
    (hx : ¬ Connects ω o x) (hy : ¬ Connects ω o y) :
    cluster (ω ∪ {s(x, y)}) o = cluster ω o := by
  refine PercLib.CriticalLRP.cluster_union_singleton_eq ?_
  rw [mem_touchSet]
  rintro ⟨v, hv, hvc⟩
  rw [Sym2.mem_iff] at hv
  rcases hv with rfl | rfl
  · exact hx (mem_cluster_iff.mp hvc)
  · exact hy (mem_cluster_iff.mp hvc)

/-- The pointwise indicator increment.  Opening `{x,y}` changes the indicator of `z` in the
cluster of `o` exactly when `z` lies in the cluster of the endpoint that is *outside* `K_0` while
the other endpoint is inside it — the excluded structure of the paper's flux. -/
theorem indicator_cluster_union_edge_sub (ω : Config V) (o x y z : V) (hxy : x ≠ y) :
    (cluster (ω ∪ {s(x, y)}) o).indicator (fun _ => (1 : ℝ)) z
        - (cluster ω o).indicator (fun _ => (1 : ℝ)) z
      = (if Connects ω o x ∧ ¬ Connects ω o y then
          (cluster ω y).indicator (fun _ => (1 : ℝ)) z else 0)
        + (if Connects ω o y ∧ ¬ Connects ω o x then
          (cluster ω x).indicator (fun _ => (1 : ℝ)) z else 0) := by
  simp only [Set.indicator_apply]
  by_cases hx : Connects ω o x
  · by_cases hy : Connects ω o y
    · rw [cluster_union_edge_eq_of_mem ω o x y hx hy]
      simp [hx, hy]
    · have hnot : ¬ Connects ω x y := fun h => hy (connects_trans hx h)
      have hdisj := disjoint_cluster_of_not_connects ω o x y hx hnot
      rw [cluster_union_edge_eq_of_attach ω o x y hxy hx hnot]
      by_cases hz : z ∈ cluster ω o
      · have hz' : z ∉ cluster ω y := Set.disjoint_left.mp hdisj hz
        simp [hx, hy, hz, hz']
      · by_cases hzy : z ∈ cluster ω y
        · simp [hx, hy, hz, hzy]
        · have hzu : z ∉ cluster ω o ∪ cluster ω y := by
            intro h
            rcases h with h | h
            exacts [hz h, hzy h]
          simp [hx, hy, hz, hzy, hzu]
  · by_cases hy : Connects ω o y
    · have hnot : ¬ Connects ω y x := fun h => hx (connects_trans hy h)
      have hdisj := disjoint_cluster_of_not_connects (ω := ω) (o := o) (x := y) (y := x) hy hnot
      have hcfg : ω ∪ {s(x, y)} = ω ∪ {s(y, x)} := by rw [Sym2.eq_swap]
      rw [hcfg, cluster_union_edge_eq_of_attach (ω := ω) (o := o) (x := y) (y := x)
        hxy.symm hy hnot]
      by_cases hz : z ∈ cluster ω o
      · have hz' : z ∉ cluster ω x := Set.disjoint_left.mp hdisj hz
        simp [hx, hy, hz, hz']
      · by_cases hzx : z ∈ cluster ω x
        · simp [hx, hy, hz, hzx]
        · have hzu : z ∉ cluster ω o ∪ cluster ω x := by
            intro h
            rcases h with h | h
            exacts [hz h, hzx h]
          simp [hx, hy, hz, hzx, hzu]
    · rw [cluster_union_edge_eq_of_not_connects ω o x y hx hy]
      simp [hx, hy]

/-- **The excluded increment of the truncated cluster moment.**

Opening the edge `{x,y}` increases `|K_0 ∩ A|` by exactly `|K_y ∩ A|` when `0` is already connected
to `x` while `y` is not in `K_0`, and by `|K_x ∩ A|` in the mirror case.  In particular the
increment is *supported on the excluded event* `{0 ↔ x} ∩ {y ∉ K_0}`: this is precisely the shape
of the paper's pivotal weight `pivotWeight r ω 0 x y = 1{0↔x} 1(dist(y,x) ≤ r) 1{x↮y} |K_y|`, with
`|K_y|` replaced by the truncated `|K_y ∩ A|`.

No hypothesis on `ω` is needed: if `{x,y}` is already open then both sides vanish. -/
theorem sMomentTrunc_union_edge_sub (A : Finset V) (o : V) (ω : Config V) {x y : V}
    (hxy : x ≠ y) :
    sMomentTrunc (fun _ => (1 : ℝ)) o A (ω ∪ {s(x, y)})
        - sMomentTrunc (fun _ => (1 : ℝ)) o A ω
      = (if Connects ω o x ∧ ¬ Connects ω o y then
          sMomentTrunc (fun _ => (1 : ℝ)) y A ω else 0)
        + (if Connects ω o y ∧ ¬ Connects ω o x then
          sMomentTrunc (fun _ => (1 : ℝ)) x A ω else 0) := by
  have hsum : ∀ (c : Prop) (_ : Decidable c) (g : V → ℝ),
      (∑ z ∈ A, (if c then g z else 0)) = if c then (∑ z ∈ A, g z) else 0 := by
    intro c _ g
    by_cases hc : c
    · rw [ite_eq_left hc]
      exact Finset.sum_congr rfl fun z _ => ite_eq_left hc
    · rw [ite_eq_right hc]
      exact Finset.sum_eq_zero fun z _ => ite_eq_right hc
  simp only [sMomentTrunc]
  rw [← Finset.sum_sub_distrib]
  trans ∑ z ∈ A, ((if Connects ω o x ∧ ¬ Connects ω o y then
        (cluster ω y).indicator (fun _ => (1 : ℝ)) z else 0)
      + (if Connects ω o y ∧ ¬ Connects ω o x then
        (cluster ω x).indicator (fun _ => (1 : ℝ)) z else 0))
  · exact Finset.sum_congr rfl fun z _ => indicator_cluster_union_edge_sub ω o x y z hxy
  · rw [Finset.sum_add_distrib, hsum (Connects ω o x ∧ ¬ Connects ω o y),
      hsum (Connects ω o y ∧ ¬ Connects ω o x)]

end PercLib.CriticalLRP.Orchestration

/-! ## The paper's standardized per-edge flux at the actual source model -/

namespace PercLib.CriticalLRP.Orchestration

open MeasureTheory
open scoped ENNReal NNReal

attribute [local instance] Classical.propDecidable

namespace SourceModelData

variable (M : SourceModelData)

/-- **The literal per-edge Russo flux of the truncated cluster moment, in the paper's
standardized excluded form.**

For a genuine edge `{x,y}` of length `≤ r`, the `e`-th summand of
`sMomentInfFlux (0) A 1 M.cutProb M.cutEdgeDeriv r` equals `β_c (-K'(r))` times the expectation of
the *excluded* increment: on the closed event of `{x,y}`, the increment of `|K_0 ∩ A|` is
`|K_y ∩ A|` when `0 ↔ x` but `y ∉ K_0`, and `|K_x ∩ A|` in the mirror case.

This is `pivotWeight r ω 0 x y + pivotWeight r ω 0 y x` with `|K_c|` replaced by the truncated
`|K_c ∩ A|` and the distance indicator supplied by the hypothesis `hdist`.  The factor
`exp(-β_c J_r(e)) = 1 - q_e(r)` of `M.cutEdgeDeriv` has been absorbed into the closed event, which
is exactly the cancellation that the standardized form needs. -/
theorem cutEdgeDeriv_mul_pivotalFlux_eq_excl (A : Finset M.V) {r : ℝ} {x y : M.V}
    (hxy : x ≠ y) (hdist : M.S.dist x y ≤ r) :
    M.cutEdgeDeriv r s(x, y) *
        pivotalFlux (M.cutLaw r) (sMomentTrunc (fun _ => (1 : ℝ)) (0 : M.V) A) s(x, y)
      = (M.betaCrit : ℝ) * (-(deriv M.K r)) *
          ∫ ω, (if s(x, y) ∈ ω then 0 else
              ((if Connects ω (0 : M.V) x ∧ ¬ Connects ω (0 : M.V) y then
                  sMomentTrunc (fun _ => (1 : ℝ)) y A ω else 0)
                + (if Connects ω (0 : M.V) y ∧ ¬ Connects ω (0 : M.V) x then
                  sMomentTrunc (fun _ => (1 : ℝ)) x A ω else 0)))
            ∂(M.cutLaw r) := by
  rw [M.cutEdgeDeriv_mul_pivotalFlux_eq A hxy hdist]
  have hpt : ∀ ω : Config M.V,
      (if s(x, y) ∈ ω then (0 : ℝ) else
          (sMomentTrunc (fun _ => (1 : ℝ)) (0 : M.V) A (ω ∪ {s(x, y)})
            - sMomentTrunc (fun _ => (1 : ℝ)) (0 : M.V) A ω))
        = (if s(x, y) ∈ ω then (0 : ℝ) else
            ((if Connects ω (0 : M.V) x ∧ ¬ Connects ω (0 : M.V) y then
                sMomentTrunc (fun _ => (1 : ℝ)) y A ω else 0)
              + (if Connects ω (0 : M.V) y ∧ ¬ Connects ω (0 : M.V) x then
                sMomentTrunc (fun _ => (1 : ℝ)) x A ω else 0))) := by
    intro ω
    by_cases h : s(x, y) ∈ ω
    · simp [h]
    · simp only [h, ite_false]
      exact sMomentTrunc_union_edge_sub A (0 : M.V) ω hxy
  rw [show (fun ω => (if s(x, y) ∈ ω then (0 : ℝ) else
        (sMomentTrunc (fun _ => (1 : ℝ)) (0 : M.V) A (ω ∪ {s(x, y)})
          - sMomentTrunc (fun _ => (1 : ℝ)) (0 : M.V) A ω)))
      = (fun ω => (if s(x, y) ∈ ω then (0 : ℝ) else
            ((if Connects ω (0 : M.V) x ∧ ¬ Connects ω (0 : M.V) y then
                sMomentTrunc (fun _ => (1 : ℝ)) y A ω else 0)
              + (if Connects ω (0 : M.V) y ∧ ¬ Connects ω (0 : M.V) x then
                sMomentTrunc (fun _ => (1 : ℝ)) x A ω else 0)))) from funext hpt]

/-- **The standardized per-edge flux is nonnegative.**  On the support of the derivative weight,
with the source's own (nonpositive) slope, the per-edge contribution to `dχ_A/dr` is
`β_c |K'(r)|` times the expectation of a nonnegative excluded increment.  Nothing here needs a
moment: it is the sign of the exact statement. -/
theorem cutEdgeDeriv_mul_pivotalFlux_nonneg (A : Finset M.V) {r : ℝ} {x y : M.V}
    (hxy : x ≠ y) (hdist : M.S.dist x y ≤ r) (hK' : deriv M.K r ≤ 0) :
    0 ≤ M.cutEdgeDeriv r s(x, y) *
        pivotalFlux (M.cutLaw r) (sMomentTrunc (fun _ => (1 : ℝ)) (0 : M.V) A) s(x, y) := by
  rw [M.cutEdgeDeriv_mul_pivotalFlux_eq_excl A hxy hdist]
  have hβ : (0 : ℝ) ≤ (M.betaCrit : ℝ) := M.betaCrit.coe_nonneg
  have hcoef : (0 : ℝ) ≤ (M.betaCrit : ℝ) * (-(deriv M.K r)) := by
    have : (0 : ℝ) ≤ -(deriv M.K r) := by linarith
    exact mul_nonneg hβ this
  refine mul_nonneg hcoef (integral_nonneg fun ω => ?_)
  by_cases h : s(x, y) ∈ ω
  · simp [h]
  · simp only [h, ite_false]
    refine add_nonneg ?_ ?_
    · by_cases c1 : Connects ω (0 : M.V) x ∧ ¬ Connects ω (0 : M.V) y
      · rw [ite_eq_left c1]
        exact sMomentTrunc_nonneg (fun _ => zero_le_one) _ _ _
      · rw [ite_eq_right c1]
    · by_cases c2 : Connects ω (0 : M.V) y ∧ ¬ Connects ω (0 : M.V) x
      · rw [ite_eq_left c2]
        exact sMomentTrunc_nonneg (fun _ => zero_le_one) _ _ _
      · rw [ite_eq_right c2]

end SourceModelData

end PercLib.CriticalLRP.Orchestration

#print axioms PercLib.CriticalLRP.Orchestration.SourceModelData.cutEdgeDeriv_mul_pivotalFlux_nonneg

/-! ## Axiom audit of the increment and standardized-flux declarations -/

namespace PercLib.CriticalLRP.Orchestration

#print axioms PercLib.CriticalLRP.Orchestration.connects_union_edge_trichotomy
#print axioms PercLib.CriticalLRP.Orchestration.mem_cluster_union_edge
#print axioms PercLib.CriticalLRP.Orchestration.cluster_union_edge_eq_of_mem
#print axioms PercLib.CriticalLRP.Orchestration.cluster_union_edge_eq_of_attach
#print axioms PercLib.CriticalLRP.Orchestration.disjoint_cluster_of_not_connects
#print axioms PercLib.CriticalLRP.Orchestration.cluster_union_edge_eq_of_not_connects
#print axioms PercLib.CriticalLRP.Orchestration.indicator_cluster_union_edge_sub
#print axioms PercLib.CriticalLRP.Orchestration.sMomentTrunc_union_edge_sub
#print axioms PercLib.CriticalLRP.Orchestration.SourceModelData.one_sub_cutProb_eq_exp
#print axioms PercLib.CriticalLRP.Orchestration.SourceModelData.cutEdgeDeriv_mul_pivotalFlux_eq
#print axioms PercLib.CriticalLRP.Orchestration.SourceModelData.cutEdgeDeriv_mul_pivotalFlux_eq_excl

end PercLib.CriticalLRP.Orchestration

/-! ## The edge-to-ordered-pair reindexing of the excluded increment -/

namespace PercLib.CriticalLRP.Orchestration

variable {V : Type*} [Countable V]

attribute [local instance] Classical.propDecidable

/-- The pointwise splitting: the edge increment is the sum of the two ordered-pair increments. -/
theorem edgeIncr_mk (d : V → V → Prop) [DecidableRel d] (hd : ∀ a b, (d a b ↔ d b a))
    (ω : Config V) (o : V) (A : Finset V) (x y : V) :
    edgeIncr d hd ω o A s(x, y) = pairIncr d ω o A x y + pairIncr d ω o A y x := by
  simp only [edgeIncr, pairIncr, Sym2.lift_mk]
  by_cases h : d x y
  · have h' : d y x := (hd y x).mpr h
    simp only [h, h', ite_true]
    ring
  · have h' : ¬ d y x := fun hh => h ((hd y x).mp hh)
    simp only [h, h', ite_false, zero_mul]
    ring

/-- A loop contributes nothing. -/
theorem edgeIncr_loop (d : V → V → Prop) [DecidableRel d] (hd : ∀ a b, (d a b ↔ d b a))
    (ω : Config V) (o : V) (A : Finset V) (x : V) :
    edgeIncr d hd ω o A s(x, x) = 0 := by
  rw [edgeIncr_mk]
  simp only [pairIncr]
  by_cases h : Connects ω o x <;> simp [h]

end PercLib.CriticalLRP.Orchestration

/-! ## Axiom audit of the reindexing packet -/

namespace PercLib.CriticalLRP.Orchestration

#print axioms PercLib.CriticalLRP.Orchestration.pairIncr
#print axioms PercLib.CriticalLRP.Orchestration.edgeIncr
#print axioms PercLib.CriticalLRP.Orchestration.edgeIncr_mk
#print axioms PercLib.CriticalLRP.Orchestration.edgeIncr_loop

end PercLib.CriticalLRP.Orchestration
