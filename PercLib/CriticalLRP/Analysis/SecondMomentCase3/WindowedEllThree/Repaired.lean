/-
The repaired Case-3 polygon bundle: satisfiable, with the windowed `ℓ = 3` conjunct.

Accepted and independently rebuilt from Ultramath `smwzf17v9`, member `m6`, direction `d6`.

## The two halves of the diagnosis

* `NoGo.not_exists_case3_polygon_bundle`: the bundle of polygon inputs consumed by
  `SecondMomentCase3.secondMoment_asymptotic_case3` — a vanishing logarithmically
  integrable driver together with the *per-vertex* `ℓ = 3` bound
  `∀ y, T³_{β_c,r}(0,y) ≤ Cp (∇_{r^c} + r^{-c})` and the per-vertex `ℓ = 4` bound — is
  **empty**.  (`T³(0,0) ≥ 1` while the driver vanishes.)
* This file: the same bundle with the `ℓ = 3` conjunct in the windowed form
  `Defs.WindowedEllThreeGap` is **provable** from the paper's own inputs: the triangle
  condition `∇_{β_c} < ∞`, the first-moment asymptotic `χ(r) ∼ (α/β_c) r^α`
  (Proposition I.4.2, giving the uniform lower comparison and `χ(r) < ∞`), and the
  open-triangle log-radial bound of Lemma I.4.13 (giving the driver's vanishing and
  logarithmic integrability, `case3Driver_isLogErrorFunction`).  The `ℓ = 4` conjunct is
  the landed Lemma I.4.18 assembly (`source_polygon_bound_tail_cc` at `ell = 4`), run at
  the same exponent `c` as the windowed `ℓ = 3` bound.

The exponent is chosen as `c = min (α/(2d)) (1/2)`: the source's `c` is free ("there exist
positive constants `c` and `C`"), the landed `ℓ ≥ 4` assembly accepts every `c ≤ α/(2d)`,
and the windowed `ℓ = 3` bound needs `c ≤ 1/2`.  No coefficient of the source is changed:
the combinatorial coefficients `C₃, C₄` of Lemma I.4.17 do not appear here at all — they
belong to the still-missing per-vertex moment gap `hgap` (`p = 3`, `q = 0`), which is the
one remaining numerator input.
-/
module

public import PercLib.CriticalLRP.Analysis.SecondMomentCase3.WindowedEllThree.Defs
public import PercLib.CriticalLRP.Analysis.SecondMomentCase3.WindowedEllThree.Windowed
public import PercLib.CriticalLRP.Analysis.SecondMomentCase3.WindowedEllThree.Consumer
public import PercLib.CriticalLRP.Analysis.Polygon.ChiInput
public import PercLib.CriticalLRP.Analysis.Polygon.NearBall

/-! # The repaired Case-3 polygon bundle -/

set_option linter.style.longLine false

@[expose] public section

noncomputable section

open Filter Topology
open scoped ENNReal NNReal BigOperators

namespace PercLib.CriticalLRP
namespace Orchestration
namespace SourceModelData

variable (M : SourceModelData)

/-- **The repaired Case-3 polygon bundle is satisfiable.**

There are `c, Cp > 0`, with `c ≤ 1/2`, such that

* the driver `∇_{r^c} + r^{-c}` vanishes and is logarithmically integrable,
* the *windowed* `ℓ = 3` bound `∑_{y ∈ B_r} T³_{β_c,r}(0,y) ≤ Cp |B_r| (∇_{r^c} + r^{-c})`
  holds for every `r ≥ 1`, and
* the `ℓ = 4` polygon bound `T⁴_{β_c,r}(0,x) ≤ Cp (∇_{r^c} + r^{-c}) χ` holds for every
  `r ≥ 1` and every `x`,

all from Proposition I.4.2's first-moment asymptotic, the triangle condition, and the
open-triangle log-radial bound of Lemma I.4.13.  This is the exact replacement of the
`hcase3` bundle of `secondMoment_asymptotic_case3` whose per-vertex `ℓ = 3` conjunct is
refuted in `NoGo.lean`. -/
theorem exists_repaired_case3_polygon_bundle {C₀ p : ℝ} (hC₀ : 0 ≤ C₀) (hp : 1 < p)
    (hP : Tendsto (fun r : ℝ => (M.cutMassAt r 0).toReal
      / ((M.α / (M.betaCrit : ℝ)) * r ^ M.α)) atTop (𝓝 1))
    (hTri : TriTail.openTriangleSelf M.kernel M.kernel_nonneg M.betaCrit 0 < ⊤)
    (hF : Analysis.LogRadialBound (fun y : M.V => M.S.dist (0 : M.V) y)
      (fun y : M.V => TriTail.openTriangle M.kernel M.kernel_nonneg M.betaCrit 0 y) C₀ p) :
    ∃ c Cp : ℝ, 0 < c ∧ c ≤ 1 / 2 ∧ 0 < Cp ∧
      Tendsto (M.case3Driver c) atTop (𝓝 0) ∧
      Analysis.LogarithmicallyIntegrable (M.case3Driver c) ∧
      M.WindowedEllThreeGap c Cp ∧
      (∀ r : ℝ, 1 ≤ r → ∀ x : M.V,
        I418C.polyK (M.cutTwoPoint r) 4 (0 : M.V) x
          ≤ Cp * M.case3Driver c r * (M.cutMassAt r 0).toReal) := by
  have hβ : 0 < (M.betaCrit : ℝ) := I418C.ChiInput.betaCrit_pos_of_tendsto_chi_div M hP
  obtain ⟨c₀, hc₀, hχu⟩ := I418C.ChiInput.exists_chi_lower_uniform_and_finite M hβ hP
  have hχfin : ∀ r : ℝ, 1 ≤ r → M.cutMassAt r 0 ≠ ⊤ :=
    fun r hr => (hχu r (by linarith)).2
  have hdpos : (0 : ℝ) < (M.d : ℝ) := by exact_mod_cast M.hd
  -- the exponent: small enough for both the `ℓ ≥ 4` assembly and the windowed `ℓ = 3` bound
  obtain ⟨c, hcpos, hcle, hcα⟩ :
      ∃ c : ℝ, 0 < c ∧ c ≤ 1 / 2 ∧ c ≤ M.α / (2 * (M.d : ℝ)) :=
    ⟨min (M.α / (2 * (M.d : ℝ))) (1 / 2),
      lt_min (div_pos M.hα (by positivity)) (by norm_num),
      min_le_right _ _, min_le_left _ _⟩
  -- the windowed `ℓ = 3` bound
  obtain ⟨Cp₃, -, hW⟩ := M.exists_windowedEllThreeGap hcpos hcle hTri hχfin
  -- the `ℓ = 4` bound at the same exponent, from the landed `ℓ ≥ 4` assembly
  obtain ⟨Knear, hKnear, hnear⟩ := I418C.NearBall.exists_near_ball M
  have hB2hB3hlink := M.hB2_hB3_hlink_derived hTri
  obtain ⟨hB2, hB3, hlink⟩ := hB2hB3hlink
  have hpoly4 : ∀ r : ℝ, 1 ≤ r → ∀ x : M.V,
      I418C.polyK (M.cutTwoPoint r) 4 (0 : M.V) x
        ≤ max 1 (M.triSelf * Knear / c₀) * M.case3Driver c r
            * (M.cutMassAt r 0).toReal := by
    intro r hr x
    have hrpos : (0 : ℝ) < r := lt_of_lt_of_le one_pos hr
    have hχfinr : M.cutMassAt r 0 ≠ ⊤ := hχfin r hr
    have hχr : c₀ * r ^ M.α ≤ (M.cutMassAt r 0).toReal := (hχu r hrpos).1
    have hnearR : (1 : ℝ) ≤ r ^ (M.α / (2 * (M.d : ℝ))) :=
      Real.one_le_rpow hr (div_nonneg M.hα.le (by positivity))
    obtain ⟨s, hfar, hcard⟩ := hnear (r ^ (M.α / (2 * (M.d : ℝ)))) hnearR
    have hbound := I418C.source_polygon_bound_tail_cc (c₀ := c₀) (K := Knear)
      (cc := c) (ell := 4) M r (r ^ (M.α / (2 * (M.d : ℝ)))) s hr hc₀ hKnear.le
      hχfinr hTri hB2 hB3 hlink
      (by norm_num) hcα hfar hcard rfl hχr x
    have hpow : (M.cutMassAt r 0).toReal ^ (4 - 3) = (M.cutMassAt r 0).toReal := by norm_num
    rw [hpow] at hbound
    exact hbound
  -- combine the two constants
  refine ⟨c, max Cp₃ (max 1 (M.triSelf * Knear / c₀)), hcpos, hcle,
    lt_of_lt_of_le zero_lt_one (le_trans (le_max_left _ _) (le_max_right _ _)), ?_, ?_, ?_, ?_⟩
  · -- the driver vanishes
    exact (M.case3Driver_isLogErrorFunction hcpos hC₀ hp hF).2
  · -- the driver is logarithmically integrable
    exact (M.case3Driver_isLogErrorFunction hcpos hC₀ hp hF).1
  · -- the windowed `ℓ = 3` bound
    intro r hr
    refine (hW r hr).trans ?_
    have h1 : (0 : ℝ) ≤ ((M.ball r).ncard : ℝ) := by positivity
    have h2 : (0 : ℝ) ≤ M.case3Driver c r := M.case3Driver_nonneg_of_one_le hr
    have hle : Cp₃ ≤ max Cp₃ (max 1 (M.triSelf * Knear / c₀)) := le_max_left _ _
    exact mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right hle h1) h2
  · -- the `ℓ = 4` bound
    intro r hr x
    refine (hpoly4 r hr x).trans ?_
    have h2 : (0 : ℝ) ≤ M.case3Driver c r := M.case3Driver_nonneg_of_one_le hr
    have h3 : (0 : ℝ) ≤ (M.cutMassAt r 0).toReal := ENNReal.toReal_nonneg
    have hle : max 1 (M.triSelf * Knear / c₀)
        ≤ max Cp₃ (max 1 (M.triSelf * Knear / c₀)) := le_max_right _ _
    exact mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right hle h2) h3

end SourceModelData
end Orchestration
end PercLib.CriticalLRP
