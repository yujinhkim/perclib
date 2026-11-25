/- Integrated from independently rebuilt Ultramath work, base revision 75f8858d8e30ea17b20f9ff1d216bc1508c01ce2.
Scratch source: ../../.ultramath/smwpwq50m/m2/I417B/Final.lean ; module path rewritten only.
-/

/-
# The source-level `p = 2`, `q = 1` statement:
# `E|K|² E|K| − E[|Kx|²|Ky|1(x↮y)] ≤ (excess)`

The printed left-hand side of the `p = 2`, `q = 1` display is `E|K|² E|K|`, i.e. the **second
moment** times the **first moment** of `|K|` (the paper parentheseses `(E|K|)^{…}` only on the
right-hand side, where it does mean powers of the mean).  For `p = 2`, `q = 1` that is exactly

  `volSq π x · ∫⁻|Ky| = (∫⁻|Kx(ω)|² dP) · (∫⁻|Ky(ω)| dP)`,

the left-hand side of `I417_p21_le` (`E|K|²` and `E|K|` are root-independent on a transitive
graph).  So the source statement is obtained from `I417_p21_le` by `tsub_le_iff_right` with no
further input; nothing here needs `(E|K|)² ≤ E|K|²`.

The right-hand side of the printed display, `T³(x,y)(E|K|)^4 + 2T⁴(x,y)(E|K|)^3`, uses powers of
the **mean** `E|K| = ∑_w P(x↔w)`.  Passing from the two excess families below to those τ-powers is
the diagram (two-copy tree-graph) side; it is **not** done here.  The gap is exactly a bound on
`jointSq π x w = E[|Kx|² 1(w ∈ Kx)]` together with the fresh τ-factors
`P(y↔w) ∑_z P(w↔z)`; see `REPORT.md` §6.

Warning recorded for the record: replacing the first factor of the source's left-hand side by the
strictly smaller `(E|K|)²` would *weaken* the statement, so no such replacement is made or used
anywhere in the chain.  (`mean_sq_le_volSq` below proves `(E|K|)² ≤ E|K|²`; it is not part of the
chain to the source statement and is not used by any of its consumers.)

No `sorry`, no custom axioms; no definitions.
-/
module

public import PercLib.CriticalLRP.Correlation.I417.Main

open MeasureTheory Measure ProbabilityTheory unitInterval
open scoped ENNReal NNReal

set_option linter.unusedSectionVars false

@[expose] public section

namespace PercLib.CriticalLRP.I417

attribute [local instance] Classical.propDecidable

variable {V : Type*} [Countable V]

/-! ## The two excess families in independent-data form -/

/-- **The source-level statement, additive form.**  `E|K|² · E|K|` is bounded by the excluded
moment plus the `y ∈ Kx` family and the marked-crossing family, the latter two written with their
one-copy factors:

  `(∫⁻|Kx|²)(∫⁻|Ky|) ≤ E[|Kx|²|Ky|1(x↮y)] + E[|Kx|²1(y∈Kx)] ∑_w P(y↔w)`
  `   + ∑_w E[|Kx|²1(w∈Kx)] P(y↔w) ∑_z P(w↔z)`.

Only `π e < 1` is required (for BK on the fresh disjoint occurrence), and it holds for the paper's
law `π e = 1 − exp(−β J e)`. -/
theorem I417_p21_source_le (π : Sym2 V → unitInterval) (hπ : ∀ e, π e < 1) (x y : V) :
    volSq π x * (∫⁻ ω, clusterVol ω y ∂(edgeMeasure π)) ≤
      exclMomentSq π x y +
        jointSq π x y * (∑' y₁ : V, (edgeMeasure π) (connSet y y₁)) +
        (∑' w : V, jointSq π x w *
          ((edgeMeasure π) (connSet y w) *
            (∑' y₁ : V, (edgeMeasure π) (connSet w y₁)))) := by
  refine le_trans (I417_p21_le π x y) ?_
  rw [tsum_yInSet]
  refine le_trans (add_le_add le_rfl (tsum_markSet_le π hπ x y)) ?_
  exact le_of_eq (by ac_rfl)

/-- **The source-level statement in the printed subtractive normalisation.**

  `E|K|² E|K| − E[|Kx|²|Ky|1(x↮y)]`
  `  ≤ E[|Kx|²1(y∈Kx)] ∑_w P(y↔w) + ∑_w E[|Kx|²1(w∈Kx)] P(y↔w) ∑_z P(w↔z)`.

The `ℝ≥0∞` subtraction is the paper's difference whenever the excluded moment is at most
`E|K|² E|K|` (that is the non-negativity half of Lemma I.4.17, a separate claim); if it is larger
the left-hand side is `0` by the `ℝ≥0∞` convention and the inequality still holds. -/
theorem I417_p21_source_tsub_le (π : Sym2 V → unitInterval) (hπ : ∀ e, π e < 1) (x y : V) :
    volSq π x * (∫⁻ ω, clusterVol ω y ∂(edgeMeasure π)) - exclMomentSq π x y ≤
      jointSq π x y * (∑' y₁ : V, (edgeMeasure π) (connSet y y₁)) +
        (∑' w : V, jointSq π x w *
          ((edgeMeasure π) (connSet y w) *
            (∑' y₁ : V, (edgeMeasure π) (connSet w y₁)))) := by
  refine tsub_le_iff_right.mpr ?_
  exact le_trans (I417_p21_source_le π hπ x y) (le_of_eq (by ac_rfl))

/-- The source-level statement with the two excess families kept in their raw two-copy form (no BK
on the fresh copy), i.e. exactly the additive form of the printed difference before the diagram
expansion. -/
theorem I417_p21_source_le_unreduced (π : Sym2 V → unitInterval) (x y : V) :
    volSq π x * (∫⁻ ω, clusterVol ω y ∂(edgeMeasure π)) ≤
      exclMomentSq π x y +
        (∑' x₁ : V, ∑' x₂ : V, ∑' y₁ : V,
          ((edgeMeasure π).prod (edgeMeasure π)) (yInSet x y x₁ x₂ y₁)) +
        (∑' x₁ : V, ∑' x₂ : V, ∑' y₁ : V, ∑' w : V,
          ((edgeMeasure π).prod (edgeMeasure π)) (markSet x y x₁ x₂ y₁ w)) :=
  I417_p21_le π x y

/-! ## The interface to the diagram bound

The two excess families are collected in `I417.excess` (`Defs.lean`), and the source-level
statement reads `E|K|² E|K| − E[|Kx|²|Ky|1(x↮y)] ≤ excess`.  What the printed display
`T³(x,y)(E|K|)^4 + 2T⁴(x,y)(E|K|)^3` needs on top is a bound of `excess` by those two τ-monomials;
that is the diagram/tree-graph side and is **not** proved here.  The next theorem is the (clearly
labelled) conditional consumer that records exactly where such a bound enters. -/

/-- `excess` is the sum of the two families of `I417_p21_source_tsub_le`. -/
theorem excess_eq (π : Sym2 V → unitInterval) (x y : V) :
    excess π x y =
      jointSq π x y * (∑' y₁ : V, (edgeMeasure π) (connSet y y₁)) +
        (∑' w : V, jointSq π x w *
          ((edgeMeasure π) (connSet y w) *
            (∑' y₁ : V, (edgeMeasure π) (connSet w y₁)))) := rfl

/-- The source-level subtractive statement, in terms of `excess`. -/
theorem I417_p21_source_tsub_le_excess (π : Sym2 V → unitInterval) (hπ : ∀ e, π e < 1)
    (x y : V) :
    volSq π x * (∫⁻ ω, clusterVol ω y ∂(edgeMeasure π)) - exclMomentSq π x y ≤
      excess π x y := by
  rw [excess_eq]
  exact I417_p21_source_tsub_le π hπ x y

/-- **Conditional consumer: the printed `p = 2`, `q = 1` display follows from a diagram bound on
`excess`.**  If the two excess families are dominated by `C₃ T³(x,y) χ⁴ + C₄ T⁴(x,y) χ³` (with
`χ = E|K|`, i.e. `meanVol` at either root on a transitive graph), then

  `E|K|² E|K| − E[|Kx|²|Ky|1(x↮y)] ≤ C₃ T³(x,y) (E|K|)⁴ + C₄ T⁴(x,y) (E|K|)³`.

The hypothesis `hDiag` is exactly the missing diagram input; it is not proved here, and this theorem
is *not* the printed display — it only records how the proved source-level inequality composes with
a diagram bound. -/
theorem I417_p21_of_diagram (π : Sym2 V → unitInterval) (hπ : ∀ e, π e < 1) (x y : V)
    (C₃ C₄ : ℝ≥0∞)
    (hDiag : excess π x y ≤
      C₃ * T3 π x y * (meanVol π x) ^ 4 + C₄ * T4 π x y * (meanVol π x) ^ 3) :
    volSq π x * (∫⁻ ω, clusterVol ω y ∂(edgeMeasure π)) - exclMomentSq π x y ≤
      C₃ * T3 π x y * (meanVol π x) ^ 4 + C₄ * T4 π x y * (meanVol π x) ^ 3 :=
  le_trans (I417_p21_source_tsub_le_excess π hπ x y) hDiag

/-- **The printed display in its exact shape**, conditionally on the diagram input.  If

  `excess π x y ≤ T³(x,y) (E|K|)⁴ + 2 T⁴(x,y) (E|K|)³`

then

  `E|K|² E|K| − E[|Kx|²|Ky|1(x↮y)] ≤ T³(x,y) (E|K|)⁴ + 2 T⁴(x,y) (E|K|)³`,

which is the `p = 2`, `q = 1` display of Lemma I.4.17 with `C₃ = 1`, `C₄ = 2`.  The hypothesis is
the diagram/tree-graph bound and is **not** proved here. -/
theorem I417_p21_printed_of_diagram (π : Sym2 V → unitInterval) (hπ : ∀ e, π e < 1) (x y : V)
    (hDiag : excess π x y ≤
      T3 π x y * (meanVol π x) ^ 4 + 2 * T4 π x y * (meanVol π x) ^ 3) :
    volSq π x * (∫⁻ ω, clusterVol ω y ∂(edgeMeasure π)) - exclMomentSq π x y ≤
      T3 π x y * (meanVol π x) ^ 4 + 2 * T4 π x y * (meanVol π x) ^ 3 := by
  have h := I417_p21_of_diagram π hπ x y 1 2 ?_
  · rwa [one_mul] at h
  · rwa [one_mul]

/-! ## Auxiliary: `(E|K|)² ≤ E|K|²`

Not used in the chain above (the source's left-hand side already carries `E|K|²`).  Recorded
because it is the elementary relation between the two possible readings of "`E|K|^2`", so that the
distinction cannot be blurred: `E|K|^2` in the source is the second moment, the *larger* of the
two. -/

/-- **Harrison--FKG for the two connections from the same root**, in `ℝ≥0∞` form:
`P(x↔x₁) P(x↔x₂) ≤ P(x₁, x₂ ∈ Kx)`. -/
theorem tau_mul_tau_le_inter (π : Sym2 V → unitInterval) (x x₁ x₂ : V) :
    (edgeMeasure π) (connSet x x₁) * (edgeMeasure π) (connSet x x₂) ≤
      (edgeMeasure π) (connSet x x₁ ∩ connSet x x₂) := by
  have h := edgeMeasure_fkg π (connSet x x₁) (connSet x x₂) (isUpper_connSet x x₁)
    (isUpper_connSet x x₂) (finiteWitness_connSet x x₁) (finiteWitness_connSet x x₂)
  rw [measureReal_def, measureReal_def, measureReal_def, ← ENNReal.toReal_mul] at h
  refine (ENNReal.toReal_le_toReal ?_ ?_).mp h
  · exact ENNReal.mul_ne_top (measure_ne_top _ _) (measure_ne_top _ _)
  · exact measure_ne_top _ _

/-- `(E|K|)² ≤ E|K|²`: the square of the mean cluster volume is at most the second moment.  This is
the *wrong direction* for bounding the source's left-hand side from above; see the module note. -/
theorem mean_sq_le_volSq (π : Sym2 V → unitInterval) (x : V) :
    (∑' w : V, (edgeMeasure π) (connSet x w)) ^ 2 ≤ volSq π x := by
  have hprod : (∑' w : V, (edgeMeasure π) (connSet x w)) ^ 2 =
      ∑' x₁ : V, ∑' x₂ : V,
        (edgeMeasure π) (connSet x x₁) * (edgeMeasure π) (connSet x x₂) := by
    rw [pow_two, ← ENNReal.tsum_mul_right]
    exact tsum_congr fun x₁ => (ENNReal.tsum_mul_left).symm
  rw [hprod, volSq, ← tsum_tsum_inter_connSet_eq_lintegral]
  exact ENNReal.tsum_le_tsum fun x₁ => ENNReal.tsum_le_tsum fun x₂ =>
    tau_mul_tau_le_inter π x x₁ x₂

end PercLib.CriticalLRP.I417
