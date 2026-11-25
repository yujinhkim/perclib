/-
Copyright (c) 2026 PercLib contributors. Released under Apache 2.0.

# Nonvanishing of the `p = 2` shell layer at an attained radius

Swarm `smwv94uce`, member `m2`, direction `d4`.  Nothing here touches the production tree.

`Corner.lean` proves the exact `p = 2` closed/strict discrepancy
`rhsScalarTwo r - rhsScalarTwoStrict r = β_c(-K'(r)) · (shell layer).toReal`, and
`rhsScalarTwo_sub_ne_zero_of_shell` turns it into a nonvanishing statement once the shell
layer is known to be nonzero.  This file supplies that last input.

The argument does not repeat the isolated-origin construction of the landed `p = 1`
proof (`RightExcludedMass.Positive`); it *uses* it.  On the shell, every cluster volume is
at least one (`one_le_clusterVol`), so `|K_y| ≤ |K_y|^2` and `|K| ≤ |K|^2`.  Hence both
`p = 2` shell integrands dominate the landed `p = 1` one `M.exclShellFun r`, pointwise and
then in `ℝ≥0∞`:

* `exclShellFun_le_p2QuadShellFun`, `exclShellFun_le_p2PairShellFun`;
* `p2QuadShell_ne_zero_of_shell`, `p2PairShell_ne_zero_of_shell`, from the landed
  `exclMassShell_ne_zero_of_shell` at a positive radius with a nonempty shell;
* `p2RhsMassShell_ne_zero_of_shell` and the fully discharged corner obstruction
  `rhsScalarTwo_sub_ne_zero_of_attained`.

So at an attained radius with `β_c(-K'(r)) ≠ 0` the `p = 2` RHS really does jump between
the strict window `{ρ < r}` and the closed window `{ρ ≤ r}`; no two-sided statement at such
a radius is available from (I.4.1).
-/
module

public import PercLib.CriticalLRP.Analysis.Cutoff.SecondMoment.Corner
public import PercLib.CriticalLRP.Analysis.Cutoff.OffCorner.RightExcludedMass.Positive

/-!
# The `p = 2` shell layer is nonzero at a nonempty shell

Pointwise domination of the landed `p = 1` shell integrand by both `p = 2` shell integrands,
and the resulting nonvanishing of the `p = 2` corner discrepancy.
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

/-! ## Pointwise domination of the landed `p = 1` shell integrand -/

/-- **The landed `p = 1` shell integrand is dominated by the `p = 2` `ℓ = 0` shell
integrand**, because every shell cluster volume is at least one. -/
theorem exclShellFun_le_p2QuadShellFun (r : ℝ) (ω : Config M.V) :
    M.exclShellFun r ω ≤ clusterVol ω (0 : M.V) *
      ∑ y ∈ M.shellF r,
        ((cluster ω (0 : M.V))ᶜ).indicator (fun _ => (1 : ℝ≥0∞)) y * clusterVol ω y ^ 2 := by
  rw [exclShellFun]
  refine mul_le_mul' le_rfl (Finset.sum_le_sum fun y _ => ?_)
  calc ((cluster ω (0 : M.V))ᶜ).indicator (fun _ => (1 : ℝ≥0∞)) y * clusterVol ω y
      ≤ ((cluster ω (0 : M.V))ᶜ).indicator (fun _ => (1 : ℝ≥0∞)) y * clusterVol ω y ^ 2 :=
        mul_le_mul' le_rfl (M.clusterVol_le_sq ω y)
    _ = _ := rfl

/-- **The landed `p = 1` shell integrand is dominated by the `p = 2` `ℓ = 1` shell
integrand.** -/
theorem exclShellFun_le_p2PairShellFun (r : ℝ) (ω : Config M.V) :
    M.exclShellFun r ω ≤ clusterVol ω (0 : M.V) ^ 2 *
      ∑ y ∈ M.shellF r,
        ((cluster ω (0 : M.V))ᶜ).indicator (fun _ => (1 : ℝ≥0∞)) y * clusterVol ω y := by
  rw [exclShellFun]
  refine mul_le_mul' (M.clusterVol_le_sq ω 0) le_rfl

/-! ## Nonvanishing of the `p = 2` shell masses -/

/-- **The `ℓ = 0` shell layer of the `p = 2` RHS is nonzero at a nonempty shell.** -/
theorem p2QuadShell_ne_zero_of_shell {r : ℝ} (hr : 0 < r) (hshell : (M.shellF r).Nonempty) :
    M.exclMassQuadShell r ≠ 0 := by
  have h1 : M.exclMassShell r ≠ 0 := M.exclMassShell_ne_zero_of_shell hr hshell
  have h2 : M.exclMassShell r ≤ M.exclMassQuadShell r :=
    lintegral_mono fun ω => M.exclShellFun_le_p2QuadShellFun r ω
  have hpos : 0 < M.exclMassQuadShell r := lt_of_lt_of_le (pos_iff_ne_zero.mpr h1) h2
  exact hpos.ne'

/-- **The `ℓ = 1` shell layer of the `p = 2` RHS is nonzero at a nonempty shell.** -/
theorem p2PairShell_ne_zero_of_shell {r : ℝ} (hr : 0 < r) (hshell : (M.shellF r).Nonempty) :
    M.exclMassSqLinShell r ≠ 0 := by
  have h1 : M.exclMassShell r ≠ 0 := M.exclMassShell_ne_zero_of_shell hr hshell
  have h2 : M.exclMassShell r ≤ M.exclMassSqLinShell r :=
    lintegral_mono fun ω => M.exclShellFun_le_p2PairShellFun r ω
  have hpos : 0 < M.exclMassSqLinShell r := lt_of_lt_of_le (pos_iff_ne_zero.mpr h1) h2
  exact hpos.ne'

/-- **The whole shell layer of the `p = 2` RHS is nonzero at a nonempty shell.** -/
theorem p2RhsMassShell_ne_zero_of_shell {r : ℝ} (hr : 0 < r)
    (hshell : (M.shellF r).Nonempty) : M.p2RHSShell r ≠ 0 := by
  have hq : M.exclMassQuadShell r ≠ 0 := M.p2QuadShell_ne_zero_of_shell hr hshell
  rw [p2RHSShell]
  exact ne_of_gt (lt_of_lt_of_le (pos_iff_ne_zero.mpr hq) (le_add_right le_rfl))

/-! ## The discharged corner obstruction -/

/-- **At a nonempty shell the `p = 2` RHS jumps**, with the exact size
`β_c(-K'(r)) · (shell layer).toReal`.  All nonvanishing inputs are proved; the finiteness
inputs are moment hypotheses. -/
theorem rhsScalarTwo_sub_ne_zero_of_attained {r : ℝ} (hr : 0 < r)
    (hshell : (M.shellF r).Nonempty) (hc : M.coeffRHS r ≠ 0)
    (hs : M.p2RHSStrict r ≠ ⊤) (hh : M.p2RHSShell r ≠ ⊤) :
    M.rhsScalarTwo r - M.rhsScalarTwoStrict r ≠ 0 :=
  M.rhsScalarTwo_sub_ne_zero_of_shell hc hs hh (M.p2RhsMassShell_ne_zero_of_shell hr hshell)

end SourceModelData

end PercLib.CriticalLRP.Orchestration

/-! ## Axiom audit -/

namespace PercLib.CriticalLRP.Orchestration

#print axioms SourceModelData.exclShellFun_le_p2QuadShellFun
#print axioms SourceModelData.exclShellFun_le_p2PairShellFun
#print axioms SourceModelData.p2QuadShell_ne_zero_of_shell
#print axioms SourceModelData.p2PairShell_ne_zero_of_shell
#print axioms SourceModelData.p2RhsMassShell_ne_zero_of_shell
#print axioms SourceModelData.rhsScalarTwo_sub_ne_zero_of_attained

end PercLib.CriticalLRP.Orchestration
