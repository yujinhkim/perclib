/- Integrated from independently rebuilt Ultramath work, base revision 75f8858d8e30ea17b20f9ff1d216bc1508c01ce2.
Scratch source: ../../.ultramath/smwpwq50m/m2/I417B/Lattice.lean ; module path rewritten only.
-/

/-
# The source-level `p = 2`, `q = 1` statement in the repository's lattice notation

`twoPointFunction J hJ β x y` is `P_β(x ↔ y)` and `longRangeMeasure J hJ β` is the paper's law
`P_β`; `volSq` is `E|K|²` and `∑' w, twoPointFunction J hJ β y w` is `E|K|`
(`lintegral_clusterVol_eq_tsum_twoPoint`).  This file restates the source-level inequality in those
notations so that it composes with the existing tree-graph / diagram interfaces without rewriting.
On a transitive graph `meanVol` does not depend on the root, so the right-hand side is the paper's
`T³(x,y)(E|K|)^4 + 2T⁴(x,y)(E|K|)^3` once a diagram bound on `excess` is supplied
(`I417_p21_of_diagram`).

No `sorry`, no custom axioms; no definitions.
-/
module

public import PercLib.CriticalLRP.Correlation.I417.CardFun

open MeasureTheory Measure ProbabilityTheory unitInterval
open scoped ENNReal NNReal

set_option linter.unusedSectionVars false

@[expose] public section

namespace PercLib.CriticalLRP.I417

attribute [local instance] Classical.propDecidable

variable {d : ℕ} {J : Sym2 (Fin d → ℤ) → ℝ}

/-- **The source-level statement `E|K|² · E|K| ≤ E[|Kx|²|Ky|1(x↮y)] + excess` for the long-range
law `P_β` of §I.1.2**, with both moments written as τ-sums. -/
theorem I417_p21_lattice_source_le (hJ : ∀ e, 0 ≤ J e) (β : NNReal) (x y : Fin d → ℤ) :
    volSq (bernoulliEdgeProb J hJ β) x *
        (∑' w : Fin d → ℤ, twoPointFunction J hJ β y w) ≤
      exclMomentSq (bernoulliEdgeProb J hJ β) x y +
        jointSq (bernoulliEdgeProb J hJ β) x y *
          (∑' y₁ : Fin d → ℤ, twoPointFunction J hJ β y y₁) +
        (∑' w : Fin d → ℤ, jointSq (bernoulliEdgeProb J hJ β) x w *
          (twoPointFunction J hJ β y w *
            (∑' y₁ : Fin d → ℤ, twoPointFunction J hJ β w y₁))) := by
  have hbridge : (∑' w : Fin d → ℤ, twoPointFunction J hJ β y w) =
      ∫⁻ ω, clusterVol ω y ∂(edgeMeasure (bernoulliEdgeProb J hJ β)) :=
    tsum_connSet_eq_lintegral (bernoulliEdgeProb J hJ β) y
  conv_lhs => rw [hbridge]
  exact I417_p21_source_le (bernoulliEdgeProb J hJ β)
    (fun e => bernoulliEdgeProb_lt_one hJ β e) x y

/-- The same with `E|K|` at the root `y` written as `∫⁻ ω, |K_y(ω)|`. -/
theorem I417_p21_lattice_source_le_lintegral (hJ : ∀ e, 0 ≤ J e) (β : NNReal)
    (x y : Fin d → ℤ) :
    volSq (bernoulliEdgeProb J hJ β) x *
        (∫⁻ ω, clusterVol ω y ∂(longRangeMeasure J hJ β)) ≤
      exclMomentSq (bernoulliEdgeProb J hJ β) x y +
        jointSq (bernoulliEdgeProb J hJ β) x y *
          (∑' y₁ : Fin d → ℤ, twoPointFunction J hJ β y y₁) +
        (∑' w : Fin d → ℤ, jointSq (bernoulliEdgeProb J hJ β) x w *
          (twoPointFunction J hJ β y w *
            (∑' y₁ : Fin d → ℤ, twoPointFunction J hJ β w y₁))) := by
  rw [lintegral_clusterVol_eq_tsum_twoPoint hJ β y]
  exact I417_p21_lattice_source_le hJ β x y

/-- **The printed subtractive form for `P_β`**:
`E|K|² E|K| − E[|Kx|²|Ky|1(x↮y)] ≤ excess`. -/
theorem I417_p21_lattice_source_tsub_le (hJ : ∀ e, 0 ≤ J e) (β : NNReal) (x y : Fin d → ℤ) :
    volSq (bernoulliEdgeProb J hJ β) x *
        (∑' w : Fin d → ℤ, twoPointFunction J hJ β y w) -
        exclMomentSq (bernoulliEdgeProb J hJ β) x y ≤
      excess (bernoulliEdgeProb J hJ β) x y := by
  have hbridge : (∑' w : Fin d → ℤ, twoPointFunction J hJ β y w) =
      ∫⁻ ω, clusterVol ω y ∂(edgeMeasure (bernoulliEdgeProb J hJ β)) :=
    tsum_connSet_eq_lintegral (bernoulliEdgeProb J hJ β) y
  conv_lhs => rw [hbridge]
  exact I417_p21_source_tsub_le_excess (bernoulliEdgeProb J hJ β)
    (fun e => bernoulliEdgeProb_lt_one hJ β e) x y

end PercLib.CriticalLRP.I417
