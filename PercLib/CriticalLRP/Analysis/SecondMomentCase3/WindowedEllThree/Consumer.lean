/-
The Case-3 numerator assembly with the *windowed* `ℓ = 3` input.

Accepted and independently rebuilt from Ultramath `smwzf17v9`, member `m6`, direction `d6`.

`SecondMomentCase3.connCubeMass_toReal_le_of_perVertex_gap` proves

  `E_{β_c,r}[|K|³|K ∩ B_r|] ≤ (C₃ + C₄) Cp |B_r| (∇_{r^c} + r^{-c}) (E_{β_c,r}|K|)⁴`

from the per-vertex inputs `hgap` (Lemma I.4.17 at `p = 3`, `q = 0`), `hT3` (the `ℓ = 3`
polygon bound, per vertex) and `hpoly4` (the `ℓ = 4` polygon bound).  The `ℓ = 4` input is
manufactured at all radii by `I418C.exists_uniform_source_polygon_bound_of_triangle_first_moment_all_radii`;
the `ℓ = 3` input in that per-vertex shape is refuted in `NoGo.lean`.

This file redoes exactly the same summation, but with the `ℓ = 3` input in the *windowed*
form `Defs.WindowedEllThreeGap`:

  `∑_{y ∈ B_r} T³_{β_c,r}(0,y) ≤ Cp |B_r| (∇_{r^c} + r^{-c})`,

which `Windowed.lean` proves from the triangle condition, `χ < ∞` and the ball count.  The
conclusion has the same shape and the same constant structure as the per-vertex version,
so this is a replacement of the false hypothesis by a true one, not a weakening of the
conclusion.  `Defs.windowedEllThreeGap_of_perVertex` shows the new hypothesis is implied by
the old one.
-/
module

public import PercLib.CriticalLRP.Analysis.SecondMomentCase3.WindowedEllThree.Defs
public import PercLib.CriticalLRP.Analysis.SecondMomentCase3.WindowedEllThree.Windowed

/-! # Case-3 numerator assembly with the windowed `ℓ = 3` input -/

set_option linter.style.longLine false

@[expose] public section

noncomputable section

open Filter Topology
open scoped ENNReal NNReal BigOperators

namespace PercLib.CriticalLRP
namespace Orchestration
namespace SourceModelData

variable (M : SourceModelData)

/-- **Case 3, the numerator estimate with the windowed `ℓ = 3` input.**

With the per-vertex Lemma I.4.17 at `p = 3`, `q = 0` (`hgap`), the windowed `ℓ = 3`
polygon input (`hT3sum`), and the `ℓ = 4` polygon input (`hpoly4`), the Case-3 numerator is
at most `(C₃ + C₄) Cp |B_r| (∇_{r^c} + r^{-c}) (E_{β_c,r}|K|)⁴` eventually — the same
statement as `connCubeMass_toReal_le_of_perVertex_gap`, with `hT3` replaced by `hT3sum`. -/
theorem connCubeMass_toReal_le_of_windowedGap {c Cp C3 C4 : ℝ}
    (hC3 : 0 ≤ C3) (hC4 : 0 ≤ C4)
    (hgap : ∀ r : ℝ, 1 ≤ r → ∀ y ∈ E1Sign.ballF M r,
      (M.connCubeVertexMass r y).toReal
        ≤ C3 * I418C.polyK (M.cutTwoPoint r) 3 (0 : M.V) y
            * (M.cutMassAt r 0).toReal ^ 4
          + C4 * I418C.polyK (M.cutTwoPoint r) 4 (0 : M.V) y
            * (M.cutMassAt r 0).toReal ^ 3)
    (hT3sum : M.WindowedEllThreeGap c Cp)
    (hpoly4 : ∀ r : ℝ, 1 ≤ r → ∀ x : M.V,
      I418C.polyK (M.cutTwoPoint r) 4 (0 : M.V) x
        ≤ Cp * M.case3Driver c r * (M.cutMassAt r 0).toReal)
    (hc : ∀ r : ℝ, 1 ≤ r → M.connCubeMass r ≠ ⊤) :
    ∀ᶠ r : ℝ in atTop, (M.connCubeMass r).toReal ≤
      ((C3 + C4) * Cp) * ((M.ball r).ncard : ℝ) * M.case3Driver c r
        * (M.cutMassAt r 0).toReal ^ 4 := by
  filter_upwards [eventually_ge_atTop (1 : ℝ)] with r hr
  rw [M.connCubeMass_toReal_eq_sum_vertex r (hc r hr)]
  set s := E1Sign.ballF M r with hs
  set χ : ℝ := (M.cutMassAt r 0).toReal with hχdef
  set drv : ℝ := M.case3Driver c r with hdrvdef
  have hχ : (0 : ℝ) ≤ χ := ENNReal.toReal_nonneg
  have hdrv : (0 : ℝ) ≤ drv := M.case3Driver_nonneg_of_one_le hr
  have hcard : (s.card : ℝ) = ((M.ball r).ncard : ℝ) := by
    rw [hs, E1Sign.card_ballF M r]
  -- the per-vertex Lemma I.4.17 bound, summed
  have hstep1 : ∑ y ∈ s, (M.connCubeVertexMass r y).toReal
      ≤ ∑ y ∈ s, (C3 * I418C.polyK (M.cutTwoPoint r) 3 (0 : M.V) y * χ ^ 4
          + C4 * I418C.polyK (M.cutTwoPoint r) 4 (0 : M.V) y * χ ^ 3) :=
    Finset.sum_le_sum fun y hy => hgap r hr y hy
  -- the two polygon sums
  have hthree : ∑ y ∈ s, (C3 * I418C.polyK (M.cutTwoPoint r) 3 (0 : M.V) y * χ ^ 4)
      = C3 * χ ^ 4 * M.windowPolyKThree r := by
    rw [show M.windowPolyKThree r
        = ∑ y ∈ s, I418C.polyK (M.cutTwoPoint r) 3 (0 : M.V) y from rfl,
      Finset.mul_sum]
    exact Finset.sum_congr rfl fun y _ => by ring
  -- (the `ℓ = 3` term)
  have hthree_le : C3 * χ ^ 4 * M.windowPolyKThree r ≤ C3 * χ ^ 4 * (Cp * ((M.ball r).ncard : ℝ) * drv) := by
    refine mul_le_mul_of_nonneg_left ?_ (by positivity)
    exact hT3sum r hr
  -- (the `ℓ = 4` term)
  have hfour_le : ∑ y ∈ s, (C4 * I418C.polyK (M.cutTwoPoint r) 4 (0 : M.V) y * χ ^ 3)
      ≤ C4 * χ ^ 3 * (((M.ball r).ncard : ℝ) * (Cp * drv * χ)) := by
    have h1 : ∑ y ∈ s, (C4 * I418C.polyK (M.cutTwoPoint r) 4 (0 : M.V) y * χ ^ 3)
        = C4 * χ ^ 3 * ∑ y ∈ s, I418C.polyK (M.cutTwoPoint r) 4 (0 : M.V) y := by
      rw [Finset.mul_sum]
      exact Finset.sum_congr rfl fun y _ => by ring
    have h2 : ∑ y ∈ s, I418C.polyK (M.cutTwoPoint r) 4 (0 : M.V) y
        ≤ (s.card : ℝ) * (Cp * drv * χ) := by
      have h3 : ∑ y ∈ s, I418C.polyK (M.cutTwoPoint r) 4 (0 : M.V) y
          ≤ ∑ _y ∈ s, Cp * drv * χ :=
        Finset.sum_le_sum fun y _ => hpoly4 r hr y
      have h4 : ∑ _y ∈ s, (Cp * drv * χ) = (s.card : ℝ) * (Cp * drv * χ) := by
        rw [Finset.sum_const, nsmul_eq_mul]
      linarith [h3, le_of_eq h4]
    have h5 : ((s.card : ℝ) * (Cp * drv * χ)) = ((M.ball r).ncard : ℝ) * (Cp * drv * χ) := by
      rw [hcard]
    calc ∑ y ∈ s, (C4 * I418C.polyK (M.cutTwoPoint r) 4 (0 : M.V) y * χ ^ 3)
        = C4 * χ ^ 3 * ∑ y ∈ s, I418C.polyK (M.cutTwoPoint r) 4 (0 : M.V) y := h1
      _ ≤ C4 * χ ^ 3 * ((s.card : ℝ) * (Cp * drv * χ)) := by
          refine mul_le_mul_of_nonneg_left h2 (by positivity)
      _ = C4 * χ ^ 3 * (((M.ball r).ncard : ℝ) * (Cp * drv * χ)) := by rw [h5]
  -- assemble
  have hsum_split : ∑ y ∈ s, (C3 * I418C.polyK (M.cutTwoPoint r) 3 (0 : M.V) y * χ ^ 4
        + C4 * I418C.polyK (M.cutTwoPoint r) 4 (0 : M.V) y * χ ^ 3)
      = C3 * χ ^ 4 * M.windowPolyKThree r
        + ∑ y ∈ s, (C4 * I418C.polyK (M.cutTwoPoint r) 4 (0 : M.V) y * χ ^ 3) := by
    rw [Finset.sum_add_distrib, hthree]
  refine (hstep1.trans (le_of_eq hsum_split)).trans ?_
  have hthree_le' : C3 * χ ^ 4 * M.windowPolyKThree r
      ≤ C3 * χ ^ 4 * (Cp * ((M.ball r).ncard : ℝ) * drv) := hthree_le
  linarith [hthree_le', hfour_le]

/-- **The per-vertex Case-3 assembly, recovered.**  The per-vertex `ℓ = 3` input implies the
windowed one (`Defs.windowedEllThreeGap_of_perVertex`), so the windowed assembly is at least
as applicable as `connCubeMass_toReal_le_of_perVertex_gap`. -/
theorem connCubeMass_toReal_le_of_perVertexGap'
    {c Cp C3 C4 : ℝ} (_hCp : 0 ≤ Cp) (hC3 : 0 ≤ C3) (hC4 : 0 ≤ C4)
    (hgap : ∀ r : ℝ, 1 ≤ r → ∀ y ∈ E1Sign.ballF M r,
      (M.connCubeVertexMass r y).toReal
        ≤ C3 * I418C.polyK (M.cutTwoPoint r) 3 (0 : M.V) y
            * (M.cutMassAt r 0).toReal ^ 4
          + C4 * I418C.polyK (M.cutTwoPoint r) 4 (0 : M.V) y
            * (M.cutMassAt r 0).toReal ^ 3)
    (hT3 : M.PerVertexEllThreeGap c Cp)
    (hpoly4 : ∀ r : ℝ, 1 ≤ r → ∀ x : M.V,
      I418C.polyK (M.cutTwoPoint r) 4 (0 : M.V) x
        ≤ Cp * M.case3Driver c r * (M.cutMassAt r 0).toReal)
    (hc : ∀ r : ℝ, 1 ≤ r → M.connCubeMass r ≠ ⊤) :
    ∀ᶠ r : ℝ in atTop, (M.connCubeMass r).toReal ≤
      ((C3 + C4) * Cp) * ((M.ball r).ncard : ℝ) * M.case3Driver c r
        * (M.cutMassAt r 0).toReal ^ 4 :=
  M.connCubeMass_toReal_le_of_windowedGap hC3 hC4 hgap
    (M.windowedEllThreeGap_of_perVertex hT3) hpoly4 hc

end SourceModelData
end Orchestration
end PercLib.CriticalLRP
