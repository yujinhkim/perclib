/-
Model and basepoint wrappers for the general marked moment gap of Lemma I.4.17.
The fresh-profile and depth-grouping proofs are reused, not duplicated.
-/
module

public import PercLib.CriticalLRP.Correlation.I417.Composition.Gap
public import PercLib.CriticalLRP.Correlation.I417.General.SourceForm
public import PercLib.CriticalLRP.Correlation.I417.Nonnegative.Main
public import PercLib.CriticalLRP.Correlation.I417.MarkedJoint.Transversal.Lattice

/-! ## Vertex-transitive, basepoint, and canonical-law wrappers
-/

open MeasureTheory Measure ProbabilityTheory unitInterval
open PercLib.Percolation.Bond
open scoped ENNReal NNReal BigOperators

set_option linter.unusedSectionVars false
set_option linter.unusedDecidableInType false
set_option linter.style.longLine false

@[expose] public section

namespace PercLib.CriticalLRP.I417SummedClose

open PercLib.CriticalLRP

variable {V : Type*} [Countable V] [DecidableEq V]

/-- Upper diagram bound in a vertex-transitive model. -/
theorem moment_gap_le_markedGapPoly_of_transitive (π : Sym2 V → unitInterval)
    (hπ : ∀ e, π e < 1) (x y : V)
    (htrans : ∀ v : V, ∃ g : V ≃ V, (∀ e : Sym2 V, π (Sym2.map g e) = π e) ∧ g x = v)
    {p q : ℕ} (hp : 1 ≤ p) (hq : 1 ≤ q) :
    I417A.momentProd π x y p q - I417A.rawDiff π x y p q ≤
      markedGapPoly π p q (I417.meanVol π x) x y :=
  moment_gap_le_markedGapPoly π hπ x y hp hq (I417Example.meanVol_eq_of_transitive π x htrans)

/-- Lemma I.4.17's upper bound with the moment product written at the common basepoint. -/
theorem moment_gap_le_markedGapPoly_basepoint (π : Sym2 V → unitInterval)
    (hπ : ∀ e, π e < 1) (o x y : V)
    (htrans : ∀ v : V, ∃ g : V ≃ V, (∀ e : Sym2 V, π (Sym2.map g e) = π e) ∧ g o = v)
    {p q : ℕ} (hp : 1 ≤ p) (hq : 1 ≤ q) :
    (∫⁻ ω, Percolation.cardFun (cluster ω o) ^ p ∂(edgeMeasure π)) *
        (∫⁻ ω, Percolation.cardFun (cluster ω o) ^ q ∂(edgeMeasure π)) -
      I417A.rawDiff π x y p q ≤ markedGapPoly π p q (I417.meanVol π x) x y := by
  obtain ⟨gx, hgx, hx⟩ := htrans x
  obtain ⟨gy, hgy, hy⟩ := htrans y
  have hpx : (∫⁻ ω, Percolation.cardFun (cluster ω o) ^ p ∂(edgeMeasure π)) =
      ∫⁻ ω, Percolation.cardFun (cluster ω x) ^ p ∂(edgeMeasure π) := by
    rw [← hx]
    exact (TreeExpansion.FivePoint.lintegral_cardFun_pow_permConfig π gx hgx p o).symm
  have hqy : (∫⁻ ω, Percolation.cardFun (cluster ω o) ^ q ∂(edgeMeasure π)) =
      ∫⁻ ω, Percolation.cardFun (cluster ω y) ^ q ∂(edgeMeasure π) := by
    rw [← hy]
    exact (TreeExpansion.FivePoint.lintegral_cardFun_pow_permConfig π gy hgy q o).symm
  rw [hpx, hqy]
  apply moment_gap_le_markedGapPoly_of_transitive π hπ x y ?_ hp hq
  intro v
  obtain ⟨gv, hgv, hvo⟩ := htrans v
  have hgsymm : ∀ e : Sym2 V, π (Sym2.map gx.symm e) = π e := by
    intro e
    induction e using Sym2.ind with
    | _ a b =>
      simpa only [Sym2.map_mk, Equiv.apply_symm_apply] using
        (hgx (Sym2.mk (gx.symm a) (gx.symm b))).symm
  let g : V ≃ V := gx.symm.trans gv
  refine ⟨g, ?_, ?_⟩
  · intro e
    calc
      π (Sym2.map g e) = π (Sym2.map gv (Sym2.map gx.symm e)) := by
        simp [g, Sym2.map_map]
      _ = π (Sym2.map gx.symm e) := hgv (Sym2.map gx.symm e)
      _ = π e := hgsymm e
  · change gv (gx.symm x) = v
    rw [← hx, Equiv.symm_apply_apply, hvo]

/-- Same-basepoint nonnegativity, the other half of Lemma I.4.17's statement. -/
theorem momentDiff_nonneg_basepoint_of_transitive (π : Sym2 V → unitInterval)
    (hπ : ∀ e, π e < 1) (o x y : V) (p q : ℕ)
    (htrans : ∀ v : V, ∃ g : V ≃ V, (∀ e : Sym2 V, π (Sym2.map g e) = π e) ∧ g o = v) :
    I417A.rawDiff π x y p q ≤
      (∫⁻ ω, Percolation.cardFun (cluster ω o) ^ p ∂(edgeMeasure π)) *
        (∫⁻ ω, Percolation.cardFun (cluster ω o) ^ q ∂(edgeMeasure π)) := by
  obtain ⟨gx, hgx, hx⟩ := htrans x
  obtain ⟨gy, hgy, hy⟩ := htrans y
  exact I417A.momentDiff_nonneg_basepoint π hπ o x y p q gx hgx hx gy hgy hy

end PercLib.CriticalLRP.I417SummedClose

namespace PercLib.CriticalLRP.TreeExpansion

/-- Translation data for the canonical power-law profile on a finite `d`-dimensional index. -/
theorem latticeLongRange_profile_transitive (d : ℕ) (α : ℝ) (β : NNReal) (o : Fin d → ℤ) :
    ∀ v : Fin d → ℤ, ∃ g : (Fin d → ℤ) ≃ (Fin d → ℤ),
      (∀ e : Sym2 (Fin d → ℤ),
        bernoulliEdgeProb (lrKernel d α) (lrKernel_nonneg d α) β (Sym2.map g e) =
          bernoulliEdgeProb (lrKernel d α) (lrKernel_nonneg d α) β e) ∧ g o = v := by
  intro v
  let g : (Fin d → ℤ) ≃ (Fin d → ℤ) := Equiv.addRight (v - o)
  refine ⟨g, ?_, ?_⟩
  · intro e
    induction e using Sym2.ind with
    | _ a b =>
      simpa only [Sym2.map_mk, Equiv.coe_addRight, g] using
        lrKernel_unitInterval_translation_of_pair d α β a b (v - o)
  · simp [g]

/-- The source's common-basepoint upper diagram bound at the canonical power-law law. -/
theorem latticeLongRange_moment_gap_le_markedGapPoly (d : ℕ) (α : ℝ) (β : NNReal)
    (o x y : Fin d → ℤ) {p q : ℕ} (hp : 1 ≤ p) (hq : 1 ≤ q) :
    (∫⁻ ω, Percolation.cardFun (cluster ω o) ^ p
        ∂(edgeMeasure (bernoulliEdgeProb (lrKernel d α) (lrKernel_nonneg d α) β))) *
        (∫⁻ ω, Percolation.cardFun (cluster ω o) ^ q
          ∂(edgeMeasure (bernoulliEdgeProb (lrKernel d α) (lrKernel_nonneg d α) β))) -
      I417A.rawDiff (bernoulliEdgeProb (lrKernel d α) (lrKernel_nonneg d α) β) x y p q ≤
        I417SummedClose.markedGapPoly (bernoulliEdgeProb (lrKernel d α) (lrKernel_nonneg d α) β)
          p q (I417.meanVol (bernoulliEdgeProb (lrKernel d α) (lrKernel_nonneg d α) β) x) x y :=
  I417SummedClose.moment_gap_le_markedGapPoly_basepoint _
    (fun e => bernoulliEdgeProb_lt_one (lrKernel_nonneg d α) β e) o x y
    (latticeLongRange_profile_transitive d α β o) hp hq

/-- Nonnegativity in the source's common-basepoint form at the canonical power-law law. -/
theorem latticeLongRange_momentDiff_nonneg_basepoint (d : ℕ) (α : ℝ) (β : NNReal)
    (o x y : Fin d → ℤ) (p q : ℕ) :
    I417A.rawDiff (bernoulliEdgeProb (lrKernel d α) (lrKernel_nonneg d α) β) x y p q ≤
      (∫⁻ ω, Percolation.cardFun (cluster ω o) ^ p
        ∂(edgeMeasure (bernoulliEdgeProb (lrKernel d α) (lrKernel_nonneg d α) β))) *
        (∫⁻ ω, Percolation.cardFun (cluster ω o) ^ q
          ∂(edgeMeasure (bernoulliEdgeProb (lrKernel d α) (lrKernel_nonneg d α) β))) :=
  I417SummedClose.momentDiff_nonneg_basepoint_of_transitive _
    (fun e => bernoulliEdgeProb_lt_one (lrKernel_nonneg d α) β e) o x y p q
    (latticeLongRange_profile_transitive d α β o)

end PercLib.CriticalLRP.TreeExpansion
