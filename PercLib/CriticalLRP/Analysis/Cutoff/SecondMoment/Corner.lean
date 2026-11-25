/-
Copyright (c) 2026 PercLib contributors. Released under Apache 2.0.

# The `p = 2` closed/strict corner split of the Lemma I.4.1 right-hand side

Swarm `smwv94uce`, member `m2`, direction `d4`.  Nothing here touches the production tree.

Commit `47aa44c` proves, for the `p = 1` first moment, that at an attained radius the left
derivative sees the strict window `{ρ < r}` and the right derivative the closed window
`{ρ ≤ r}` of the source's `B_r`, and that the two values differ by the shell term.  The
`p = 2` RHS of (I.4.1) has the same closed/strict dichotomy in its window, but here it is
pure bookkeeping: both sides are values of an integral against the *same* law `cutLaw r`, so
no limit is taken and no differentiability is asserted.

What is proved:

* `p2QuadMass_eq_strict_add_shell`, `p2PairMass_eq_strict_add_shell` — each excluded term
  splits exactly as closed window `=` strict window `+` shell.
* `p2RhsMass_eq_strict_add_shell` — consequently
  `M.p2RHS r = M.p2RHSStrict r + M.p2RHSShell r`, i.e. the source's `p = 2` RHS
  with the closed window is the strict-window RHS plus the shell layer of both terms
  (with the coefficient `2` on the `ℓ = 1` shell layer as well).
* `p2RhsMassShell_ne_top` — the shell layer is finite whenever the first cut-off moment is,
  so the discrepancy is a finite real number and not an `∞ - ∞` expression.
* `rhsScalarTwo_sub_eq_shell` — the exact real discrepancy
  `rhsScalarTwo r - rhsScalarTwoStrict r = β_c(-K'(r)) · (shell layer).toReal`.
* `rhsScalarTwo_sub_ne_zero_of_shell` — that discrepancy is nonzero at an attained radius
  with `coeffRHS r ≠ 0` and nonzero shell layer.  This is the `p = 2` analogue of the `p = 1`
  obstruction, and it is why no attained-radius two-sided statement is claimed.
-/
module

public import PercLib.CriticalLRP.Analysis.Cutoff.SecondMoment.Finiteness

/-!
# The closed/strict split of the `p = 2` excluded masses

Window decompositions over `B_r = {ρ < r} ⊔ {ρ = r}`, the induced decomposition of the
two-term RHS, and the exact real discrepancy between the closed-window and strict-window
`p = 2` values.
-/

set_option autoImplicit false
set_option linter.hashCommand false
set_option linter.style.longLine false
set_option linter.unusedSectionVars false

@[expose] public section

noncomputable section

open MeasureTheory
open scoped ENNReal NNReal

namespace PercLib.CriticalLRP.Orchestration

open PercLib.CriticalLRP

namespace SourceModelData

variable (M : SourceModelData)

/-! ## Measurability of the strict and shell integrands -/

/-- The `ℓ = 0` strict-window integrand is measurable. -/
theorem measurable_p2QuadStrictFun (r : ℝ) :
    Measurable fun ω : Config M.V => clusterVol ω (0 : M.V) *
      ∑ y ∈ M.ballFLt r,
        ((cluster ω (0 : M.V))ᶜ).indicator (fun _ => (1 : ℝ≥0∞)) y * clusterVol ω y ^ 2 :=
  (measurable_clusterVol (0 : M.V)).mul (M.measurable_p2WindowSum _ 2)

/-- The `ℓ = 1` strict-window integrand is measurable. -/
theorem measurable_p2PairStrictFun (r : ℝ) :
    Measurable fun ω : Config M.V => clusterVol ω (0 : M.V) ^ 2 *
      ∑ y ∈ M.ballFLt r,
        ((cluster ω (0 : M.V))ᶜ).indicator (fun _ => (1 : ℝ≥0∞)) y * clusterVol ω y :=
  ((measurable_clusterVol (0 : M.V)).pow_const 2).mul
    (by simpa only [pow_one] using M.measurable_p2WindowSum (M.ballFLt r) 1)

/-- The `ℓ = 0` shell integrand is measurable. -/
theorem measurable_p2QuadShellFun (r : ℝ) :
    Measurable fun ω : Config M.V => clusterVol ω (0 : M.V) *
      ∑ y ∈ M.shellF r,
        ((cluster ω (0 : M.V))ᶜ).indicator (fun _ => (1 : ℝ≥0∞)) y * clusterVol ω y ^ 2 :=
  (measurable_clusterVol (0 : M.V)).mul (M.measurable_p2WindowSum _ 2)

/-- The `ℓ = 1` shell integrand is measurable. -/
theorem measurable_p2PairShellFun (r : ℝ) :
    Measurable fun ω : Config M.V => clusterVol ω (0 : M.V) ^ 2 *
      ∑ y ∈ M.shellF r,
        ((cluster ω (0 : M.V))ᶜ).indicator (fun _ => (1 : ℝ≥0∞)) y * clusterVol ω y :=
  ((measurable_clusterVol (0 : M.V)).pow_const 2).mul
    (by simpa only [pow_one] using M.measurable_p2WindowSum (M.shellF r) 1)

/-! ## The exact window decompositions -/

/-- **The `ℓ = 0` term splits over the closed window / strict window / shell.** -/
theorem p2QuadMass_eq_strict_add_shell (r : ℝ) :
    M.exclMassQuad r = M.exclMassQuadLt r + M.exclMassQuadShell r := by
  have hsub : M.ballFLt r ⊆ E1Sign.ballF M r := fun y hy =>
    (E1Sign.mem_ballF M).mpr (le_of_lt (M.mem_ballFLt.mp hy))
  have hsum : ∀ ω : Config M.V,
      (∑ y ∈ E1Sign.ballF M r,
          ((cluster ω (0 : M.V))ᶜ).indicator (fun _ => (1 : ℝ≥0∞)) y * clusterVol ω y ^ 2)
        = (∑ y ∈ M.ballFLt r,
            ((cluster ω (0 : M.V))ᶜ).indicator (fun _ => (1 : ℝ≥0∞)) y * clusterVol ω y ^ 2)
          + ∑ y ∈ M.shellF r,
              ((cluster ω (0 : M.V))ᶜ).indicator (fun _ => (1 : ℝ≥0∞)) y * clusterVol ω y ^ 2 := by
    intro ω
    rw [← Finset.sum_sdiff hsub, M.ballFLt_sdiff_shellF, add_comm]
  have h1 : M.exclMassQuad r = ∫⁻ ω, (clusterVol ω (0 : M.V) *
        (∑ y ∈ M.ballFLt r,
          ((cluster ω (0 : M.V))ᶜ).indicator (fun _ => (1 : ℝ≥0∞)) y * clusterVol ω y ^ 2)
      + clusterVol ω (0 : M.V) *
        (∑ y ∈ M.shellF r,
          ((cluster ω (0 : M.V))ᶜ).indicator (fun _ => (1 : ℝ≥0∞)) y * clusterVol ω y ^ 2))
      ∂(M.cutLaw r) := by
    simp only [exclMassQuad, exclSumQuad]
    exact lintegral_congr fun ω => by rw [hsum ω, mul_add]
  rw [h1, lintegral_add_left (M.measurable_p2QuadStrictFun r)]
  rfl

/-- **The `ℓ = 1` term splits over the closed window / strict window / shell.** -/
theorem p2PairMass_eq_strict_add_shell (r : ℝ) :
    M.exclMassSqLin r = M.exclMassSqLinLt r + M.exclMassSqLinShell r := by
  have hsub : M.ballFLt r ⊆ E1Sign.ballF M r := fun y hy =>
    (E1Sign.mem_ballF M).mpr (le_of_lt (M.mem_ballFLt.mp hy))
  have hsum : ∀ ω : Config M.V,
      (∑ y ∈ E1Sign.ballF M r,
          ((cluster ω (0 : M.V))ᶜ).indicator (fun _ => (1 : ℝ≥0∞)) y * clusterVol ω y)
        = (∑ y ∈ M.ballFLt r,
            ((cluster ω (0 : M.V))ᶜ).indicator (fun _ => (1 : ℝ≥0∞)) y * clusterVol ω y)
          + ∑ y ∈ M.shellF r,
              ((cluster ω (0 : M.V))ᶜ).indicator (fun _ => (1 : ℝ≥0∞)) y * clusterVol ω y := by
    intro ω
    rw [← Finset.sum_sdiff hsub, M.ballFLt_sdiff_shellF, add_comm]
  have h1 : M.exclMassSqLin r = ∫⁻ ω, (clusterVol ω (0 : M.V) ^ 2 *
        (∑ y ∈ M.ballFLt r,
          ((cluster ω (0 : M.V))ᶜ).indicator (fun _ => (1 : ℝ≥0∞)) y * clusterVol ω y)
      + clusterVol ω (0 : M.V) ^ 2 *
        (∑ y ∈ M.shellF r,
          ((cluster ω (0 : M.V))ᶜ).indicator (fun _ => (1 : ℝ≥0∞)) y * clusterVol ω y))
      ∂(M.cutLaw r) := by
    simp only [exclMassSqLin, exclSumLin]
    exact lintegral_congr fun ω => by rw [hsum ω, mul_add]
  rw [h1, lintegral_add_left (M.measurable_p2PairStrictFun r)]
  rfl

/-- **The `p = 2` RHS splits into its strict-window value and the shell layer**, with the
coefficient `2` on the `ℓ = 1` part on both sides. -/
theorem p2RhsMass_eq_strict_add_shell (r : ℝ) :
    M.p2RHS r = M.p2RHSStrict r + M.p2RHSShell r := by
  rw [p2RHS, p2RHSStrict, p2RHSShell, M.p2QuadMass_eq_strict_add_shell r,
    M.p2PairMass_eq_strict_add_shell r]
  ring

/-! ## Monotonicity in the window and finiteness of the shell layer -/

/-- The `ℓ = 0` shell layer is at most the closed-window term. -/
theorem p2QuadShell_le_p2QuadMass (r : ℝ) : M.exclMassQuadShell r ≤ M.exclMassQuad r := by
  rw [M.p2QuadMass_eq_strict_add_shell r]
  exact le_add_left le_rfl

/-- The `ℓ = 1` shell layer is at most the closed-window term. -/
theorem p2PairShell_le_p2PairMass (r : ℝ) : M.exclMassSqLinShell r ≤ M.exclMassSqLin r := by
  rw [M.p2PairMass_eq_strict_add_shell r]
  exact le_add_left le_rfl

/-- The strict-window `p = 2` RHS is at most the closed-window one. -/
theorem p2RhsMassStrict_le_p2RhsMass (r : ℝ) : M.p2RHSStrict r ≤ M.p2RHS r := by
  rw [M.p2RhsMass_eq_strict_add_shell r]
  exact le_add_right le_rfl

/-- **The shell layer of the `p = 2` RHS is at most the closed-window RHS.** -/
theorem p2RhsMassShell_le_p2RhsMass (r : ℝ) : M.p2RHSShell r ≤ M.p2RHS r := by
  rw [p2RHSShell, p2RHS]
  gcongr
  · exact M.p2QuadShell_le_p2QuadMass r
  · exact M.p2PairShell_le_p2PairMass r

/-- **The shell layer is finite** from finiteness of the first cut-off moment, hence the
closed/strict discrepancy at an attained radius is between finite real numbers. -/
theorem p2RhsMassShell_ne_top {c : ℝ} (hc : 0 < c)
    (hρ : ∀ z : M.V, M.S.ρ (toVec z) = c * (FiniteVolume.linfNorm z : ℝ)) {r : ℝ}
    (hr : 0 < r) (h1 : M.cutMoment 1 r ≠ ⊤) : M.p2RHSShell r ≠ ⊤ :=
  ne_top_of_le_ne_top (M.p2RhsMass_ne_top hc hρ hr h1) (M.p2RhsMassShell_le_p2RhsMass r)

/-- **Off a shell**, i.e. whenever `{ρ = r}` carries no lattice point, the closed-window
`p = 2` RHS is the strict-window one.  This is the corner-free case in which the closed and
strict windows of (I.4.1) agree. -/
theorem p2RhsMass_eq_strict_of_shell_empty (r : ℝ) (h : M.shellF r = ∅) :
    M.p2RHS r = M.p2RHSStrict r := by
  have hq : M.exclMassQuadShell r = 0 := by
    simp [exclMassQuadShell, exclSumQuadShell, h]
  have hp : M.exclMassSqLinShell r = 0 := by
    simp [exclMassSqLinShell, exclSumLinShell, h]
  rw [M.p2RhsMass_eq_strict_add_shell r, p2RHSShell, hq, hp, mul_zero, add_zero, add_zero]

/-! ## The exact real discrepancy -/

/-- **The exact closed-versus-strict discrepancy of the real `p = 2` RHS** is `β_c(-K'(r))`
times the shell layer.  This is the `p = 2` analogue of the landed `p = 1` identity
`rhsScalar r - coeffRHS r * exclScalarStrict r = coeffRHS r * (exclMassShell r).toReal`. -/
theorem rhsScalarTwo_sub_eq_shell {r : ℝ} (hs : M.p2RHSStrict r ≠ ⊤)
    (hh : M.p2RHSShell r ≠ ⊤) :
    M.rhsScalarTwo r - M.rhsScalarTwoStrict r = M.coeffRHS r * (M.p2RHSShell r).toReal := by
  have htot : M.p2RHS r ≠ ⊤ := by
    rw [M.p2RhsMass_eq_strict_add_shell r]
    exact ENNReal.add_ne_top.mpr ⟨hs, hh⟩
  rw [rhsScalarTwo, rhsScalarTwoStrict, M.p2RhsMass_eq_strict_add_shell r,
    ENNReal.toReal_add hs hh]
  ring

/-- **The `p = 2` closed/strict discrepancy is nonzero** at a radius with `coeffRHS r ≠ 0`
and a nonzero shell layer.  In particular no attained-radius two-sided formula for the
`p = 2` cut moment can be read off from (I.4.1) with the closed window. -/
theorem rhsScalarTwo_sub_ne_zero_of_shell {r : ℝ} (hc : M.coeffRHS r ≠ 0)
    (hs : M.p2RHSStrict r ≠ ⊤) (hh : M.p2RHSShell r ≠ ⊤)
    (hpos : M.p2RHSShell r ≠ 0) :
    M.rhsScalarTwo r - M.rhsScalarTwoStrict r ≠ 0 := by
  rw [M.rhsScalarTwo_sub_eq_shell hs hh]
  refine mul_ne_zero hc ?_
  exact ENNReal.toReal_ne_zero.mpr ⟨hpos, hh⟩

end SourceModelData

end PercLib.CriticalLRP.Orchestration

/-! ## Axiom audit -/

namespace PercLib.CriticalLRP.Orchestration

#print axioms SourceModelData.p2QuadMass_eq_strict_add_shell
#print axioms SourceModelData.p2PairMass_eq_strict_add_shell
#print axioms SourceModelData.p2RhsMass_eq_strict_add_shell
#print axioms SourceModelData.p2QuadShell_le_p2QuadMass
#print axioms SourceModelData.p2PairShell_le_p2PairMass
#print axioms SourceModelData.p2RhsMassStrict_le_p2RhsMass
#print axioms SourceModelData.p2RhsMassShell_le_p2RhsMass
#print axioms SourceModelData.p2RhsMassShell_ne_top
#print axioms SourceModelData.p2RhsMass_eq_strict_of_shell_empty
#print axioms SourceModelData.rhsScalarTwo_sub_eq_shell
#print axioms SourceModelData.rhsScalarTwo_sub_ne_zero_of_shell

end PercLib.CriticalLRP.Orchestration
