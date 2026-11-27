/-
Accepted from Ultramath `smwzg77c3`, member `m7`, independently rebuilt.
Production integration based on commit `81c6038182e9a883ffcd3d870aed7cd4829649d4`.
Original direction `d6`.

Copyright (c) 2026 PercLib contributors. Released under Apache 2.0.

# Harris/FKG at an arbitrary vertex: `T(0,y) * E|K_0|^3 <= E[|K_0|^3 1(y in K_0)]`

`Vertex.lean` uses the positive-association lower bound

    E[|K_0|^3 1(y ∈ K_0)] ≥ T(0,y) · E|K_0|^3                             (H)

as an explicit hypothesis.  This file proves it from the landed Harris--FKG machinery, so the
per-vertex constraint (V) becomes unconditional (modulo finiteness of the third cutoff moment).

The route is the labelled expansion, exactly as in `I417Gen.starMoment_eq_tsum_labelEvent`:

* `momentPow_eq_tsum_labelEvent`: `E|K_x|^p = ∑'_f P(labelEvent x f)`;
* `harris_labelEvent_connSet`: Harris (`edgeMeasure_fkg_measurable_ennreal`) applied termwise to
  the two increasing measurable events `labelEvent x f` and `connSet x y`, then `tsum` monotonicity;
* `harris_starMoment`: the two combine to `T(x,y) * E|K_x|^p ≤ starMoment π x y p`;
* `harris_cutMoment`: the cutoff-model form (H), using
  `connCubeVertexMass_eq_starMoment` and `cutTwoPointE_eq_ofReal`.

No `sorry`, no custom axioms, no `⊤ ↦ 0` conversion: the real-valued statement passes through
`ENNReal.toReal_mul` with both factors explicitly finite.
-/
module

public import PercLib.CriticalLRP.Correlation.I417.General.QZeroRepair.Main

/-! # Harris at an arbitrary vertex -/

noncomputable section

open MeasureTheory Measure ProbabilityTheory unitInterval
open scoped ENNReal NNReal BigOperators

set_option linter.unusedSectionVars false
set_option linter.hashCommand false

@[expose] public section

namespace PercLib.CriticalLRP.Smwzg77c3.M7

open PercLib.CriticalLRP Orchestration
open PercLib.CriticalLRP.I418C

variable {V : Type*} [Countable V]

/-- The `p`-th moment of `|K_x|` as the labelled expansion `∑'_f P(f ⊆ K_x)`. -/
theorem momentPow_eq_tsum_labelEvent (π : Sym2 V → unitInterval) (x : V) (p : ℕ) :
    (∫⁻ ω, Percolation.cardFun (cluster ω x) ^ p ∂(edgeMeasure π))
      = ∑' f : Fin p → V, (edgeMeasure π) (I417A.labelEvent x f) := by
  have hterm : ∀ f : Fin p → V,
      (∫⁻ ω, ∏ i, (cluster ω x).indicator (fun _ => (1 : ℝ≥0∞)) (f i) ∂(edgeMeasure π))
        = (edgeMeasure π) (I417A.labelEvent x f) := by
    intro f
    rw [I417A.prod_indicator_eq_indicator]
    exact lintegral_indicator_one (I417A.measurableSet_labelEvent x f)
  have hmeas : ∀ f : Fin p → V,
      AEMeasurable (fun ω => ∏ i, (cluster ω x).indicator (fun _ => (1 : ℝ≥0∞)) (f i))
        (edgeMeasure π) := fun f =>
    (Finset.measurable_prod Finset.univ fun i _ =>
      measurable_const.indicator (measurableSet_cluster_mem x (f i))).aemeasurable
  calc ∫⁻ ω, Percolation.cardFun (cluster ω x) ^ p ∂(edgeMeasure π)
      = ∫⁻ ω, ∑' f : Fin p → V,
          ∏ i, (cluster ω x).indicator (fun _ => (1 : ℝ≥0∞)) (f i) ∂(edgeMeasure π) :=
        lintegral_congr fun ω => I417A.cardFun_pow_eq_tsum (cluster ω x) p
    _ = ∑' f : Fin p → V,
          ∫⁻ ω, ∏ i, (cluster ω x).indicator (fun _ => (1 : ℝ≥0∞)) (f i) ∂(edgeMeasure π) :=
        lintegral_tsum hmeas
    _ = ∑' f : Fin p → V, (edgeMeasure π) (I417A.labelEvent x f) := tsum_congr hterm

/-- **Harris termwise**: `T(x,y) · ∑_f P(f ⊆ K_x) ≤ ∑_f P(f ⊆ K_x, x ↔ y)`. -/
theorem harris_labelEvent_connSet (π : Sym2 V → unitInterval) (x y : V) (p : ℕ) :
    (edgeMeasure π) (connSet x y) * (∑' f : Fin p → V, (edgeMeasure π) (I417A.labelEvent x f))
      ≤ ∑' f : Fin p → V, (edgeMeasure π) (I417A.labelEvent x f ∩ connSet x y) := by
  rw [← ENNReal.tsum_mul_left]
  have hu : IsUpperSet (connSet x y : Set (Config V)) :=
    fun a b hab ha => PercLib.Percolation.Bond.conn_mono hab ha
  refine ENNReal.tsum_le_tsum fun f => ?_
  rw [mul_comm]
  exact PercLib.CriticalLRP.edgeMeasure_fkg_measurable_ennreal π
    (I417A.measurableSet_labelEvent x f) (measurableSet_connSet x y)
    (I417A.isUpperSet_labelEvent x f) hu

/-- **(H) in star form**: the two-point function times the `p`-th moment is at most the connected
star moment. -/
theorem harris_starMoment (π : Sym2 V → unitInterval) (x y : V) (p : ℕ) :
    (edgeMeasure π) (connSet x y) *
        (∫⁻ ω, Percolation.cardFun (cluster ω x) ^ p ∂(edgeMeasure π))
      ≤ I417Gen.starMoment π x y p := by
  rw [I417Gen.starMoment_eq_tsum_labelEvent, momentPow_eq_tsum_labelEvent]
  exact harris_labelEvent_connSet π x y p

end PercLib.CriticalLRP.Smwzg77c3.M7

namespace PercLib.CriticalLRP.Smwzg77c3.M7

open PercLib.CriticalLRP Orchestration

variable (M : SourceModelData)

/-- **(H) in the cutoff model**: `T(0,y) · E|K_0|^3 ≤ E[|K_0|^3 1(y ∈ K_0)]`. -/
theorem harris_cutMoment (r : ℝ) (h3 : M.cutMoment 3 r ≠ ⊤) (y : M.V) :
    M.cutTwoPoint r (0 : M.V) y * (M.cutMoment 3 r).toReal
      ≤ (M.connCubeVertexMass r y).toReal := by
  have h := harris_starMoment (M.cutProb r) (0 : M.V) y 3
  have hconn : (edgeMeasure (M.cutProb r)) (connSet (0 : M.V) y)
      = ENNReal.ofReal (M.cutTwoPoint r (0 : M.V) y) := by
    rw [← M.cutLaw_eq_edgeMeasure]
    exact M.cutTwoPointE_eq_ofReal r 0 y
  have hmom : (∫⁻ ω, Percolation.cardFun (cluster ω (0 : M.V)) ^ 3
        ∂(edgeMeasure (M.cutProb r))) = M.cutMoment 3 r := by
    rw [SourceModelData.cutMoment, ← M.cutLaw_eq_edgeMeasure]
    exact lintegral_congr fun ω => by
      rw [clusterVol_eq_encard, Percolation.cardFun_eq_encard]
  have hstar : I417Gen.starMoment (M.cutProb r) (0 : M.V) y 3 = M.connCubeVertexMass r y :=
    (M.connCubeVertexMass_eq_starMoment r y).symm
  rw [hconn, hmom, hstar] at h
  have hT : ENNReal.ofReal (M.cutTwoPoint r (0 : M.V) y) ≠ ⊤ := ENNReal.ofReal_ne_top
  have hne : M.connCubeVertexMass r y ≠ ⊤ :=
    ne_top_of_le_ne_top h3 (M.connCubeVertexMass_le_cutMoment_three r y)
  calc M.cutTwoPoint r (0 : M.V) y * (M.cutMoment 3 r).toReal
      = (ENNReal.ofReal (M.cutTwoPoint r (0 : M.V) y) * M.cutMoment 3 r).toReal := by
        rw [ENNReal.toReal_mul, ENNReal.toReal_ofReal (M.cutTwoPoint_nonneg r 0 y)]
    _ ≤ (M.connCubeVertexMass r y).toReal := ENNReal.toReal_mono hne h

end PercLib.CriticalLRP.Smwzg77c3.M7

/-! ## Axiom audit -/

#print axioms PercLib.CriticalLRP.Smwzg77c3.M7.momentPow_eq_tsum_labelEvent
#print axioms PercLib.CriticalLRP.Smwzg77c3.M7.harris_labelEvent_connSet
#print axioms PercLib.CriticalLRP.Smwzg77c3.M7.harris_starMoment
#print axioms PercLib.CriticalLRP.Smwzg77c3.M7.harris_cutMoment
