/-
Independently reviewed and integrated from the completed artifact `smwx6p0op/m1`
at `.ultramath/smwx6p0op/m1/M3Q`. Production integration revision:
`3cd318e5a37d0dc889f23bd3baf1b8884e651a27`. The coordinator uses the production
namespace and fully qualified imports; the proof covers `q = 3`, not arbitrary `q`.
-/
module

public import PercLib.CriticalLRP.Correlation.I417.Fresh.Three.Refined.Cover

/-!
Independently built for swarm `smwx6p0op`, member `m1`, direction Q3-MARK-ON-PATH-COVER.

# The `q = 3` fresh-copy factor, bounded six-edge diagram by diagram

For a fixed arm label `j : Fin 3` and the other two labels `i₁, i₂`, the six-edge cover of
`freshMark_subset_shapeQ3` gives, for each arm tuple `g`,

  `P(freshMark y g j w) ≤ ∑_p ∑_q freshShapeSum π y w (g j) (g i₁) (g i₂) p q`,

an eight-term sum of products of **six** two-point factors (sixfold BK, applied to the eight
subdivided binary trees).  This file is the first, per-tuple half of the analytic statement; the
summed evaluation is in `Bound`.

Only `π e < 1` (BK) is used here.
-/

open MeasureTheory Measure ProbabilityTheory unitInterval
open scoped ENNReal NNReal

set_option linter.unusedSectionVars false
set_option linter.unusedDecidableInType false
set_option linter.unusedSimpArgs false

@[expose] public section

namespace PercLib.CriticalLRP.I417FreshThree.Refined

open PercLib.CriticalLRP
open PercLib.CriticalLRP.I417Fresh

variable {V : Type*} [Countable V] [DecidableEq V]

attribute [local instance] Classical.propDecidable

/-! ## Union bounds and BK -/

/-- Union bound for eight sets, with the flat (left-associated) right-hand side. -/
theorem measure_union8_le (π : Sym2 V → unitInterval) (A0 A1 A2 A3 A4 A5 A6 A7 : Set (Config V)) :
    (edgeMeasure π) (((((((A0 ∪ A1) ∪ A2) ∪ A3) ∪ A4) ∪ A5) ∪ A6) ∪ A7) ≤
      (edgeMeasure π) A0 + (edgeMeasure π) A1 + (edgeMeasure π) A2 + (edgeMeasure π) A3 +
        (edgeMeasure π) A4 + (edgeMeasure π) A5 + (edgeMeasure π) A6 + (edgeMeasure π) A7 := by
  refine le_trans (measure_union_le _ _) (add_le_add ?_ le_rfl)
  refine le_trans (measure_union_le _ _) (add_le_add ?_ le_rfl)
  refine le_trans (measure_union_le _ _) (add_le_add ?_ le_rfl)
  refine le_trans (measure_union_le _ _) (add_le_add ?_ le_rfl)
  refine le_trans (measure_union_le _ _) (add_le_add ?_ le_rfl)
  refine le_trans (measure_union_le _ _) (add_le_add ?_ le_rfl)
  exact measure_union_le _ _

/-- **Sixfold BK**: a six-leg diagram has at most the product of its six two-point factors. -/
theorem shapeOf_measure_le (π : Sym2 V → unitInterval) (hπ : ∀ e, π e < 1)
    (L : Fin 6 → V × V) :
    (edgeMeasure π) (ShapeOf L) ≤ ∏ i : Fin 6, tau π (L i).1 (L i).2 := by
  have hU : ∀ i : Fin 6, IsUpperSet (connSet (L i).1 (L i).2) := fun i => isUpper_connSet _ _
  have hF : ∀ i : Fin 6, Percolation.FiniteWitness (connSet (L i).1 (L i).2) :=
    fun i => finiteWitness_connSet _ _
  exact I417Example.bk_fin_ennreal π hπ (fun i : Fin 6 => connSet (L i).1 (L i).2) hU hF

/-- **The per-tuple six-edge bound.**  For every arm tuple `g` and every choice of the selected arm
`j`, the fresh marked event is bounded by the eight six-leg products, summed over the two branch
points. -/
theorem freshMark_measure_le_shapes (π : Sym2 V → unitInterval) (hπ : ∀ e, π e < 1)
    (y w : V) (g : Fin 3 → V) (j i1 i2 : Fin 3) :
    (edgeMeasure π) (I417Gen.freshMark y g j w) ≤
      ∑' p : V, ∑' q : V, freshShapeSum π y w (g j) (g i1) (g i2) p q := by
  have h0 : ∀ p0 q0 : V, (edgeMeasure π) (ShapeOf (legsA0 y w (g j) (g i1) (g i2) p0 q0)) ≤
      tau π y q0 * tau π q0 p0 * tau π p0 w * tau π w (g j) * tau π p0 (g i1) *
        tau π q0 (g i2) := by
    intro p0 q0
    have h := shapeOf_measure_le π hπ (legsA0 y w (g j) (g i1) (g i2) p0 q0)
    rw [Fin.prod_univ_six] at h
    exact h
  have h1 : ∀ p0 q0 : V, (edgeMeasure π) (ShapeOf (legsA1 y w (g j) (g i1) (g i2) p0 q0)) ≤
      tau π p0 q0 * tau π q0 w * tau π y p0 * tau π w (g j) * tau π p0 (g i1) *
        tau π q0 (g i2) := by
    intro p0 q0
    have h := shapeOf_measure_le π hπ (legsA1 y w (g j) (g i1) (g i2) p0 q0)
    rw [Fin.prod_univ_six] at h
    exact h
  have h2 : ∀ p0 q0 : V, (edgeMeasure π) (ShapeOf (legsA2 y w (g j) (g i1) (g i2) p0 q0)) ≤
      tau π w q0 * tau π q0 (g j) * tau π y p0 * tau π p0 w * tau π p0 (g i1) *
        tau π q0 (g i2) := by
    intro p0 q0
    have h := shapeOf_measure_le π hπ (legsA2 y w (g j) (g i1) (g i2) p0 q0)
    rw [Fin.prod_univ_six] at h
    exact h
  have h3 : ∀ p0 q0 : V, (edgeMeasure π) (ShapeOf (legsA3 y w (g j) (g i1) (g i2) p0 q0)) ≤
      tau π p0 q0 * tau π q0 (g i1) * tau π y p0 * tau π p0 w * tau π w (g j) *
        tau π q0 (g i2) := by
    intro p0 q0
    have h := shapeOf_measure_le π hπ (legsA3 y w (g j) (g i1) (g i2) p0 q0)
    rw [Fin.prod_univ_six] at h
    exact h
  have h4 : ∀ p0 q0 : V, (edgeMeasure π) (ShapeOf (legsB0 y w (g j) (g i1) (g i2) p0 q0)) ≤
      tau π y q0 * tau π q0 w * tau π w p0 * tau π p0 (g j) * tau π p0 (g i1) *
        tau π q0 (g i2) := by
    intro p0 q0
    have h := shapeOf_measure_le π hπ (legsB0 y w (g j) (g i1) (g i2) p0 q0)
    rw [Fin.prod_univ_six] at h
    exact h
  have h5 : ∀ p0 q0 : V, (edgeMeasure π) (ShapeOf (legsB1 y w (g j) (g i1) (g i2) p0 q0)) ≤
      tau π w q0 * tau π q0 p0 * tau π y w * tau π p0 (g j) * tau π p0 (g i1) *
        tau π q0 (g i2) := by
    intro p0 q0
    have h := shapeOf_measure_le π hπ (legsB1 y w (g j) (g i1) (g i2) p0 q0)
    rw [Fin.prod_univ_six] at h
    exact h
  have h6 : ∀ p0 q0 : V, (edgeMeasure π) (ShapeOf (legsB2 y w (g j) (g i1) (g i2) p0 q0)) ≤
      tau π p0 q0 * tau π q0 (g j) * tau π y w * tau π w p0 * tau π p0 (g i1) *
        tau π q0 (g i2) := by
    intro p0 q0
    have h := shapeOf_measure_le π hπ (legsB2 y w (g j) (g i1) (g i2) p0 q0)
    rw [Fin.prod_univ_six] at h
    exact h
  have h7 : ∀ p0 q0 : V, (edgeMeasure π) (ShapeOf (legsB3 y w (g j) (g i1) (g i2) p0 q0)) ≤
      tau π p0 q0 * tau π q0 (g i1) * tau π y w * tau π w p0 * tau π p0 (g j) *
        tau π q0 (g i2) := by
    intro p0 q0
    have h := shapeOf_measure_le π hπ (legsB3 y w (g j) (g i1) (g i2) p0 q0)
    rw [Fin.prod_univ_six] at h
    exact h
  refine le_trans (measure_mono (freshMark_subset_shapeQ3 y w g j i1 i2)) ?_
  rw [ShapeQ3]
  refine le_trans (measure_iUnion_le _) (ENNReal.tsum_le_tsum fun p => ?_)
  refine le_trans (measure_iUnion_le _) (ENNReal.tsum_le_tsum fun q => ?_)
  refine le_trans (measure_union8_le π _ _ _ _ _ _ _ _) ?_
  rw [freshShapeSum]
  exact add_le_add (add_le_add (add_le_add (add_le_add (add_le_add (add_le_add (add_le_add
    (h0 (p0 := p) (q0 := q)) (h1 (p0 := p) (q0 := q))) (h2 (p0 := p) (q0 := q)))
    (h3 (p0 := p) (q0 := q))) (h4 (p0 := p) (q0 := q))) (h5 (p0 := p) (q0 := q)))
    (h6 (p0 := p) (q0 := q))) (h7 (p0 := p) (q0 := q))

end PercLib.CriticalLRP.I417FreshThree.Refined
