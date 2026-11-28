/-
Ultramath swarm `smwzlje3f`, member `m8`, direction `d1` (brief direction (H)).

Copyright (c) 2026 PercLib contributors. Released under Apache 2.0.

Accepted and independently rebuilt from Ultramath `smwzlje3f`.
Production base `a59bc6c22aba42e69160666c17feac870d4cb887`; reviewed scratch source `.ultramath/smwzlje3f/m8/Main.lean`.

Production worktree read (read-only): `.scratch/critical-lrp-orchestration`,
HEAD `5d2d681b941eb1c687f1ba17e6a798b8f0175aa0`, Lean pin `leanprover/lean4:v4.35.0`.

# The product-gap half of the repaired `q = 0` star is a *theorem*

The `q = 0`, `p = 3` per-vertex star target of the source's Case 3,

`E[|K_0|³ 1(y ∈ K_0)] ≤ C₃ T³(0,y) χ⁴ + C₄ T⁴(0,y) χ³`,

is refuted at the diagonal (`QZeroDiagonal.not_hasPerVertexTwoTermHgap`).  The accepted repair chain
(`QZeroRepairAudit`, direction `d5` of swarm `smwziumdb`) factors the star exactly as

`star(y) = gapVert(0,y,1,2) + covVert(0,y,1,2)`

(`connCubeVertexMass_toReal_eq_gapVert_add_covVert`), and then proves

`additive_of_gap_of_cov : HasProductGap C₃ C₄ → HasCovBound C₅ → HasAdditiveStar C₃ C₄ C₅`.

Both halves were *assumed*: `HasProductGap` is the per-vertex Lemma-I.4.17 product gap and
`HasCovBound` is a Harris-type covariance bound.  This file discharges the first half:
`hasProductGap_one_two` proves

`HasProductGap M 1 2`,

i.e. the product gap at the printed constants `C₃ = 1`, `C₄ = 2`, from the *unconditional*
two-copy inequality `I417Example.printed_le` (Lemma I.4.17 at `(p,q) = (2,1)` at the swapped pair,
which is the same object as `(1,2)` at `(0,y)`) — the very inequality the production Case-3
numerator consumer is built on.  Consequently

`hasAdditiveStar_of_covBound : HasCovBound C₅ → HasAdditiveStar 1 2 C₅`

carries **no** product-gap or star hypothesis: the only remaining input of the repaired star is
the covariance bound, which is the audit's own conclusion about where the gap lives.

Nothing here is used to derive the Case-3 numerator — that route (the `(2,1)` numerator) is
already production and is not re-opened.  The point is the dependency graph: the `hgap` field of
`additive_of_gap_of_cov` is no longer an assumption.
-/
module

public import PercLib.CriticalLRP.Correlation.I417.General.QZeroRepairAudit.Sharp
public import PercLib.CriticalLRP.Analysis.SecondMomentCase3.ProductGap.Main

/-! # `HasProductGap` at the printed `(2,1)` constants -/

noncomputable section

open MeasureTheory Measure ProbabilityTheory unitInterval Filter Set
open scoped ENNReal NNReal Topology BigOperators

set_option autoImplicit false
set_option linter.unusedSectionVars false

@[expose] public section

namespace PercLib.CriticalLRP
namespace Orchestration
namespace SourceModelData

open PercLib.CriticalLRP.QZeroRepairAudit (gapVert)

variable (M : SourceModelData)

/-- **`gapVert(0,y,1,2)` is the product-minus-excluded difference at the swapped pair `(y,0)`.**

`prodVert(0,y,1,2) = E|K_0| · E|K_y|²` is the product term of the source's Case-3 numerator at the
window vertex `y` (`E|K_y|² E|K_0|`), and `exclVert(0,y,1,2) = E[|K_0| 1(y ∉ K_0) |K_y|²]` is the
subtracted term; by connectivity symmetry (`1(y ∉ K_0) = 1(0 ∉ K_y)`) the latter is
`I417.exclMomentSq y 0`.  This is `perVertex_case3_eq_p21` read in the `QZeroRepairAudit`
vocabulary. -/
theorem gapVert_zero_y_one_two_eq_perVertex (r : ℝ) (y : M.V) :
    gapVert (M.cutProb r) (0 : M.V) y 1 2
      = I417.volSq (M.cutProb r) y * I417.meanVol (M.cutProb r) (0 : M.V)
        - I417.exclMomentSq (M.cutProb r) y (0 : M.V) := by
  rw [PercLib.CriticalLRP.QZeroRepairAudit.gapVert,
    PercLib.CriticalLRP.QZeroRepairAudit.prodVert,
    PercLib.CriticalLRP.QZeroRepairAudit.exclVert,
    M.powMomentAt_cutProb_eq_cutMoment, M.powMomentAt_cutProb_eq_cutMoment,
    ← M.perVertex_case3_eq_p21 r y,
    mul_comm (M.cutMoment 1 r) (M.cutMoment 2 r)]
  simp only [pow_one]
  rfl

/-- **The per-vertex product gap from the landed `(2,1)` two-copy inequality.**

`I417Example.printed_le` at the pair `(y,0)` bounds
`E|K_y|² E|K_0| − E[|K_y|² 1(0 ∉ K_y) |K_0|]` by `T³(y,0) χ⁴ + 2 T⁴(y,0) χ³`; the `ℓ`-th matrix
powers of the cutoff connection kernel are symmetric (`T3_comm_cutProb`, `T4_comm_cutProb`) and
`χ = E_{β_c,r}|K| = T`, so this is exactly the source's two-term right-hand side at `(0,y)`.

No finiteness of `χ` is needed for the `ℝ≥0∞` form. -/
theorem gapVert_zero_y_one_two_le (r : ℝ) (y : M.V) :
    gapVert (M.cutProb r) (0 : M.V) y 1 2
      ≤ I417.T3 (M.cutProb r) (0 : M.V) y * M.cutMoment 1 r ^ 4
        + 2 * I417.T4 (M.cutProb r) (0 : M.V) y * M.cutMoment 1 r ^ 3 := by
  rw [gapVert_zero_y_one_two_eq_perVertex M r y]
  refine (I417Example.printed_le (M.cutProb r) (fun e => E1Sign.cutProb_lt_one M r e)
    y (0 : M.V) (fun v => M.meanVol_cutProb_eq r v y)).trans (le_of_eq ?_)
  rw [M.T3_comm_cutProb r y (0 : M.V), M.T4_comm_cutProb r y (0 : M.V),
    M.meanVol_cutProb r y]

/-- **`HasProductGap M 1 2`: the per-vertex product gap at the printed constants.**

This is the `hgap` hypothesis of `QZeroRepairAudit.SourceModelData.additive_of_gap_of_cov`, now a
theorem.  The only extra input is finiteness of the first cutoff moment on the tail `r ≥ 1` — needed
solely to pass from the `ℝ≥0∞` inequality to `ℝ` (`T3_toReal_eq_polyK`,
`T4_toReal_eq_polyK`), never as a `⊤ ↦ 0` conversion. -/
theorem hasProductGap_one_two (hχ : ∀ r : ℝ, 1 ≤ r → M.cutMassAt r 0 ≠ ⊤) :
    PercLib.CriticalLRP.QZeroRepairAudit.SourceModelData.HasProductGap M 1 2 := by
  intro r hr y
  have h1 : M.cutMassAt r 0 ≠ ⊤ := hχ r hr
  have h1' : M.cutMoment 1 r ≠ ⊤ := by
    rw [← M.cutMassAt_zero_eq_cutMoment r]; exact h1
  have hT3 : I417.T3 (M.cutProb r) (0 : M.V) y ≠ ⊤ := M.T3_ne_top_cutProb r h1 y
  have hT4 : I417.T4 (M.cutProb r) (0 : M.V) y ≠ ⊤ := M.T4_ne_top_cutProb r h1 y
  have hχ4 : M.cutMoment 1 r ^ 4 ≠ ⊤ := ENNReal.pow_ne_top h1'
  have hχ3 : M.cutMoment 1 r ^ 3 ≠ ⊤ := ENNReal.pow_ne_top h1'
  have hA : I417.T3 (M.cutProb r) (0 : M.V) y * M.cutMoment 1 r ^ 4 ≠ ⊤ :=
    ENNReal.mul_ne_top hT3 hχ4
  have hB : 2 * I417.T4 (M.cutProb r) (0 : M.V) y * M.cutMoment 1 r ^ 3 ≠ ⊤ :=
    ENNReal.mul_ne_top (ENNReal.mul_ne_top (by norm_num) hT4) hχ3
  have hle := ENNReal.toReal_mono (ENNReal.add_ne_top.mpr ⟨hA, hB⟩)
    (gapVert_zero_y_one_two_le M r y)
  have hchi : M.chiReal r = (M.cutMoment 1 r).toReal := by
    rw [PercLib.CriticalLRP.Orchestration.SourceModelData.chiReal,
      M.cutMassAt_zero_eq_cutMoment]
  refine hle.trans (le_of_eq ?_)
  rw [ENNReal.toReal_add hA hB]
  simp only [ENNReal.toReal_mul, ENNReal.toReal_pow, ENNReal.toReal_ofNat,
    M.T3_toReal_eq_polyK r h1 y, M.T4_toReal_eq_polyK r h1 y, hchi]
  norm_num

/-- **The old per-vertex star gap is *strictly stronger* than the product gap.**

`gapVert ≤ starVert` termwise (`QZeroRepairAudit.gapVert_le_starVert`), so
`HasPerVertexTwoTermHgap C₃ C₄` — the campaign's old `hgap`, which
`QZeroDiagonal.no_perVertex_twoTerm_constants` refutes — implies `HasProductGap C₃ C₄`.  Together
with `hasProductGap_one_two` below this is the exact statement of why the Case-3 numerator had to
be re-pointed at the product gap rather than repaired: the old target is a refutable strengthening
of the true one. -/
theorem hasProductGap_of_hasPerVertexTwoTermHgap {C3 C4 : ℝ}
    (hgap : M.HasPerVertexTwoTermHgap C3 C4)
    (h3 : ∀ r : ℝ, 1 ≤ r → M.cutMoment 3 r ≠ ⊤) :
    PercLib.CriticalLRP.QZeroRepairAudit.SourceModelData.HasProductGap M C3 C4 := by
  classical
  let := Encodable.ofCountable (Sym2 M.V)
  intro r hr y
  have hstar : PercLib.CriticalLRP.QZeroRepairAudit.starVert (M.cutProb r) (0 : M.V) y 3
      ≠ ⊤ := by
    rw [PercLib.CriticalLRP.QZeroRepairAudit.SourceModelData.starVert_cutProb_eq_connCubeVertexMass
      M r y]
    exact ne_top_of_le_ne_top (h3 r hr) (M.connCubeVertexMass_le_cutMoment_three r y)
  have hle := ENNReal.toReal_mono hstar
    (PercLib.CriticalLRP.QZeroRepairAudit.gapVert_le_starVert (M.cutProb r)
      (fun e => E1Sign.cutProb_lt_one M r e) (Percolation.edgeExhaustion (E := Sym2 M.V))
      Percolation.edgeExhaustion_mono Percolation.edgeExhaustion_cover (0 : M.V) y 1 2)
  rw [PercLib.CriticalLRP.QZeroRepairAudit.SourceModelData.starVert_cutProb_eq_connCubeVertexMass
    M r y] at hle
  exact hle.trans (hgap r hr y)

/-- **`HasProductGap M 1 2` from the first-moment asymptotic `hP` alone.**

The finiteness hypothesis of `hasProductGap_one_two` is not an extra input of the Case-3 chain:
`hP` (Proposition I.4.2) already forces the first cutoff moment to be finite at *every* radius
(`SourceModelData.cutMoment_one_ne_top_of_asymptotic`: eventual finiteness from `hP`, propagated to
the small radii by the radius monotonicity of the cutoff moment).  Hence the product gap is a
consequence of a retained source input rather than of a new hypothesis. -/
theorem hasProductGap_one_two_of_hP
    (hP : Tendsto (fun r : ℝ => (M.cutMassAt r 0).toReal
      / ((M.α / (M.betaCrit : ℝ)) * r ^ M.α)) atTop (𝓝 1)) :
    PercLib.CriticalLRP.QZeroRepairAudit.SourceModelData.HasProductGap M 1 2 :=
  hasProductGap_one_two M fun r _ => by
    rw [M.cutMassAt_zero_eq_cutMoment r]
    exact M.cutMoment_one_ne_top_of_asymptotic hP r

/-- **The additive repair from the covariance bound alone.**  `additive_of_gap_of_cov` with its
product-gap hypothesis discharged by `hasProductGap_one_two`. -/
theorem hasAdditiveStar_of_covBound {C5 : ℝ}
    (hχ : ∀ r : ℝ, 1 ≤ r → M.cutMassAt r 0 ≠ ⊤)
    (h2 : ∀ r : ℝ, 1 ≤ r → M.cutMoment 2 r ≠ ⊤)
    (h3 : ∀ r : ℝ, 1 ≤ r → M.cutMoment 3 r ≠ ⊤)
    (hcov : PercLib.CriticalLRP.QZeroRepairAudit.SourceModelData.HasCovBound M C5) :
    PercLib.CriticalLRP.QZeroRepairAudit.SourceModelData.HasAdditiveStar M 1 2 C5 :=
  PercLib.CriticalLRP.QZeroRepairAudit.SourceModelData.additive_of_gap_of_cov M
    (hasProductGap_one_two M hχ) hcov h2 h3

/-- **The additive repair from `hP` and the covariance bound alone**, with no finiteness
hypothesis: the product gap is `hasProductGap_one_two_of_hP`. -/
theorem hasAdditiveStar_of_covBound_of_hP {C5 : ℝ}
    (hP : Tendsto (fun r : ℝ => (M.cutMassAt r 0).toReal
      / ((M.α / (M.betaCrit : ℝ)) * r ^ M.α)) atTop (𝓝 1))
    (h2 : ∀ r : ℝ, 1 ≤ r → M.cutMoment 2 r ≠ ⊤)
    (h3 : ∀ r : ℝ, 1 ≤ r → M.cutMoment 3 r ≠ ⊤)
    (hcov : PercLib.CriticalLRP.QZeroRepairAudit.SourceModelData.HasCovBound M C5) :
    PercLib.CriticalLRP.QZeroRepairAudit.SourceModelData.HasAdditiveStar M 1 2 C5 :=
  PercLib.CriticalLRP.QZeroRepairAudit.SourceModelData.additive_of_gap_of_cov M
    (hasProductGap_one_two_of_hP M hP) hcov h2 h3

end SourceModelData
end Orchestration
end PercLib.CriticalLRP
