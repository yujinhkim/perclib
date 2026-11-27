/-
Independently recovered from Ultramath `smwywszgo/m5` findings and rebuilt.

Copyright (c) 2026 PercLib contributors. Released under Apache 2.0.

# The `p = 2` radius picture on windows that contain corner radii

Swarm `smwywszgo`, member `m5`, direction `d7`.

The second-moment development proves the integrated radius identity

`∫ t in a..x, M.rhsScalarTwo t = M.cutMomentReal 2 x - M.cutMomentReal 2 a`

on *off-corner* windows only (`Cutoff.SecondMoment.OffCornerIdentity`), because the finite-window
Russo identity used by the flux side needs differentiability of the edge probability at every
radius of the window.  The downstream consumers
(`SourceModelData.regularlyVarying_two`, `..._caseOne`) instead need absolute continuity and the
a.e. radius derivative on *every* radius window `[r₀, R]`, corner radii included.

This file closes that gap with `PercLib.CriticalLRP.Orchestration.SmwywszgoM5.integral_eq_sub_of_offCorner`.  The route is:

* on every off-corner subwindow `[u,v]` of `[r₀,R]`, the identity holds with base point `u`
  (`M.integral_rhsScalarTwo_eq_sub_of_offCornerWindow`, whose flux inputs are already
  discharged there from `tendsto_windowFlux_of_cutMoment_four_le` and the uniform majorant);
* `M.cutMomentReal 2` is continuous on `[r₀,R]` (`M.continuousOn_cutMomentReal`) and
  `M.rhsScalarTwo` is interval integrable on `[r₀,R]`
  (`M.intervalIntegrable_rhsScalarTwo_of_coeffBound`);
* `M.cornerRadii ∩ [r₀,R]` is finite (`M.finite_cornerRadii_inter_Ioo`);
* hence `x ↦ M.cutMomentReal 2 x - ∫ t in r₀..x, M.rhsScalarTwo t` is continuous on `[r₀,R]` and
  locally constant at every non-corner radius, so it is constant: the identity holds on the whole
  window with the single base point `r₀`.

No one-sided limit of the moment at a corner radius is used, no right/left equality of the
`p = 2` right-hand side at an attained radius is assumed, and no derivative is claimed at a corner
radius.  Feeding the landed consumer wrappers
(`Smwyvlg99M1.absolutelyContinuousOnInterval_toReal_two_of_forall_identity`,
`Smwyvlg99M1.ae_hasDerivAt_toReal_two_of_forall_identity`) then gives the exact shapes
`regularlyVarying_two` consumes:

`hac : ∀ R, r₀ ≤ R → AbsolutelyContinuousOnInterval (fun r => (M.cutMoment 2 r).toReal) r₀ R`
`hae : ∀ᵐ t ∂(volume.restrict (Set.Ici r₀)), HasDerivAt (fun r => (M.cutMoment 2 r).toReal)
        (M.rhsScalarTwo t) t`

Remaining real inputs, unchanged: measurability of `M.rhsScalarTwo` (supplied elsewhere in the
repository), finiteness of the second cutoff moment on the tail, a coefficient bound for
`M.coeffRHS` on each window (derivable from the model's sharpness field via
`M.exists_coeffRHS_bound_of_deriv_decay`), and one monotone edge-exhausting family.

No `sorry`, no `admit`, no `native_decide`, no custom axiom.
-/
module

public import PercLib.CriticalLRP.Analysis.SecondMomentTail
public import PercLib.CriticalLRP.Analysis.Cutoff.SecondMoment.OffCornerIdentity
public import PercLib.CriticalLRP.Analysis.SecondMomentMeasurability.Consumers
public import PercLib.CriticalLRP.Analysis.SecondMomentPrimitiveConsistency

/-!
# Corner-spanning second-moment radius identities
-/

set_option autoImplicit false
set_option linter.style.longLine false
set_option linter.hashCommand false

@[expose] public section
set_option linter.style.haveILetI false

open MeasureTheory Set Filter Topology
open PercLib.CriticalLRP.Orchestration
open scoped ENNReal

namespace PercLib.CriticalLRP.Orchestration.SmwywszgoM5

variable (M : PercLib.CriticalLRP.Orchestration.SourceModelData)

/-- **The corner set of a compact radius window is finite.** -/
theorem finite_cornerRadii_inter_Icc (r₀ R : ℝ) :
    (M.cornerRadii ∩ Icc r₀ R).Finite := by
  have hsub : M.cornerRadii ∩ Icc r₀ R ⊆ (M.cornerRadii ∩ Ioo r₀ R) ∪ ({r₀, R} : Set ℝ) := by
    rintro x ⟨hxc, hxI⟩
    rcases lt_or_eq_of_le hxI.1 with h | h
    · rcases lt_or_eq_of_le hxI.2 with h' | h'
      · exact Or.inl ⟨hxc, h, h'⟩
      · exact Or.inr (by simp [h'])
    · exact Or.inr (by simp [h])
  have hun : ((M.cornerRadii ∩ Ioo r₀ R) ∪ ({r₀, R} : Set ℝ)).Finite :=
    (M.finite_cornerRadii_inter_Ioo r₀ R).union (by simp)
  exact hun.subset hsub

/-- **The integrated `p = 2` radius identity on a window containing corner radii.**  From the
off-corner identity (whose flux inputs are discharged inside
`M.integral_rhsScalarTwo_eq_sub_of_offCornerWindow`), continuity of the second cutoff moment,
interval integrability of `M.rhsScalarTwo` and finiteness of the corner set, the identity holds on
`[r₀,R]` with the single base point `r₀`. -/
theorem integral_rhsScalarTwo_eq_sub_of_cornerRadii {r₀ R : ℝ} (hr₀ : 0 < r₀) (hR : r₀ ≤ R)
    (hmeas : Measurable fun t => M.rhsScalarTwo t)
    {C : ℝ} (hC0 : 0 ≤ C) (hC : ∀ r ∈ Icc r₀ R, |M.coeffRHS r| ≤ C)
    (h2fin : ∀ R : ℝ, r₀ ≤ R → M.cutMoment 2 R ≠ ⊤)
    (S : ℕ → Finset (Sym2 M.V)) (hSmono : Monotone S) (hS : ∀ e : Sym2 M.V, ∃ k, e ∈ S k) :
    ∀ x ∈ Icc r₀ R,
      ∫ t in r₀..x, M.rhsScalarTwo t = M.cutMomentReal 2 x - M.cutMomentReal 2 r₀ := by
  have hint : IntervalIntegrable (fun t => M.rhsScalarTwo t) volume r₀ R :=
    M.intervalIntegrable_rhsScalarTwo_of_coeffBound hR hmeas hC0 hC
      (PercLib.CriticalLRP.CaseOne.cutMoment_four_ne_top_of_two M (h2fin R hR))
  have hcont : ContinuousOn (fun r => M.cutMomentReal 2 r) (Icc r₀ R) := by
    have h2R : M.cutMoment 2 (R + 1) ≠ ⊤ :=
      h2fin (R + 1) (le_trans hR (le_add_of_nonneg_right zero_le_one))
    simpa only [PercLib.CriticalLRP.Orchestration.SourceModelData.cutMomentReal] using
      M.continuousOn_cutMomentReal 2 (by norm_num) hr₀ (lt_add_one R) h2R
  refine integral_eq_sub_of_offCorner (C := M.cornerRadii ∩ Icc r₀ R) hR
    (finite_cornerRadii_inter_Icc M r₀ R) hint hcont ?_
  intro u v hru huv hvR hdisj x hx
  have hoff : M.IsOffCornerWindow u v :=
    ⟨lt_of_lt_of_le hr₀ hru, huv.le, fun r hr hrc => by
      have hmem : r ∈ Icc u v ∩ (M.cornerRadii ∩ Icc r₀ R) :=
        ⟨hr, hrc, le_trans hru hr.1, le_trans hr.2 hvR⟩
      rw [hdisj] at hmem
      exact hmem⟩
  exact M.integral_rhsScalarTwo_eq_sub_of_offCornerWindow hoff S hSmono hS
    (h2fin v (le_trans hru huv.le)) hC0
    (fun r hr => hC r ⟨le_trans hru hr.1, le_trans hr.2 hvR⟩) x hx

/-- **`hac` and `hae` in the shape the regular-variation consumers take.**  On the whole tail
`[r₀, ∞)` the second cutoff moment is absolutely continuous on every window and has derivative
`M.rhsScalarTwo` almost everywhere, with no corner hypothesis anywhere. -/
theorem ac_and_ae_hasDerivAt_toReal_two_of_cornerRadii {r₀ : ℝ} (hr₀ : 0 < r₀)
    (hmeas : Measurable fun t => M.rhsScalarTwo t)
    (hCb : ∀ R : ℝ, r₀ ≤ R → ∃ C, 0 ≤ C ∧ ∀ r ∈ Icc r₀ R, |M.coeffRHS r| ≤ C)
    (h2fin : ∀ R : ℝ, r₀ ≤ R → M.cutMoment 2 R ≠ ⊤)
    (S : ℕ → Finset (Sym2 M.V)) (hSmono : Monotone S) (hS : ∀ e : Sym2 M.V, ∃ k, e ∈ S k) :
    (∀ R : ℝ, r₀ ≤ R →
      AbsolutelyContinuousOnInterval (fun r : ℝ => (M.cutMoment 2 r).toReal) r₀ R) ∧
    (∀ᵐ t ∂(volume.restrict (Set.Ici r₀)),
      HasDerivAt (fun r : ℝ => (M.cutMoment 2 r).toReal) (M.rhsScalarTwo t) t) := by
  have hint : ∀ R : ℝ, r₀ ≤ R →
      IntervalIntegrable (fun t => M.rhsScalarTwo t) volume r₀ R := by
    intro R hR
    obtain ⟨C, hC0, hC⟩ := hCb R hR
    exact M.intervalIntegrable_rhsScalarTwo_of_coeffBound hR hmeas hC0 hC
      (PercLib.CriticalLRP.CaseOne.cutMoment_four_ne_top_of_two M (h2fin R hR))
  have hid : ∀ R : ℝ, r₀ ≤ R → ∀ x ∈ Icc r₀ R,
      ∫ t in r₀..x, M.rhsScalarTwo t = M.cutMomentReal 2 x - M.cutMomentReal 2 r₀ := by
    intro R hR
    obtain ⟨C, hC0, hC⟩ := hCb R hR
    exact integral_rhsScalarTwo_eq_sub_of_cornerRadii M hr₀ hR hmeas hC0 hC h2fin S hSmono hS
  exact ⟨Smwyvlg99M1.absolutelyContinuousOnInterval_toReal_two_of_forall_identity M hint hid,
    Smwyvlg99M1.ae_hasDerivAt_toReal_two_of_forall_identity M hint hid⟩

/-- **The same with the coefficient bound discharged on the far tail.**  Beyond the radius at which
the model's log-error satisfies `|δ| ≤ 1` (`M.exists_coeffRHS_bound_of_deriv_decay`), no coefficient
bound is a hypothesis any more: only measurability, finiteness of the second cutoff moment, and one
monotone edge-exhausting family remain. -/
theorem ac_and_ae_hasDerivAt_toReal_two_of_cornerRadii_tail :
    ∃ r₁ : ℝ, ∀ {r₀ : ℝ}, r₁ ≤ r₀ → 0 < r₀ →
      (hmeas : Measurable fun t => M.rhsScalarTwo t) →
      (h2fin : ∀ R : ℝ, r₀ ≤ R → M.cutMoment 2 R ≠ ⊤) →
      ∀ (S : ℕ → Finset (Sym2 M.V)), Monotone S → (∀ e : Sym2 M.V, ∃ k, e ∈ S k) →
      (∀ R : ℝ, r₀ ≤ R →
        AbsolutelyContinuousOnInterval (fun r : ℝ => (M.cutMoment 2 r).toReal) r₀ R) ∧
      (∀ᵐ t ∂(volume.restrict (Set.Ici r₀)),
        HasDerivAt (fun r : ℝ => (M.cutMoment 2 r).toReal) (M.rhsScalarTwo t) t) := by
  obtain ⟨r₁, hr₁⟩ := Smwyvlg99M1.exists_coeffRHS_bound_of_deriv_decay M
  refine ⟨r₁, fun {r₀} hr₁r₀ hr₀ hmeas h2fin S hSmono hS => ?_⟩
  refine ac_and_ae_hasDerivAt_toReal_two_of_cornerRadii M hr₀ hmeas ?_ h2fin S hSmono hS
  intro R hR
  exact hr₁ r₀ R hr₁r₀ hr₀ hR

/-- The tail AC and a.e. derivative picture, with measurability also derived from `h2fin`.

This is the exact no-`hmR` consumer interface on every positive far-tail window.  It retains tail
finiteness of the second cutoff moment and the monotone edge-exhausting family; it does not assert
differentiability at attained radii or supply any other model data. -/
theorem ac_and_ae_hasDerivAt_toReal_two_of_cornerRadii_tail_no_meas :
    ∃ r₁ : ℝ, ∀ {r₀ : ℝ}, r₁ ≤ r₀ → 0 < r₀ →
      (h2fin : ∀ R : ℝ, r₀ ≤ R → M.cutMoment 2 R ≠ ⊤) →
      ∀ (S : ℕ → Finset (Sym2 M.V)), Monotone S → (∀ e : Sym2 M.V, ∃ k, e ∈ S k) →
      (∀ R : ℝ, r₀ ≤ R →
        AbsolutelyContinuousOnInterval (fun r : ℝ => (M.cutMoment 2 r).toReal) r₀ R) ∧
      (∀ᵐ t ∂(volume.restrict (Set.Ici r₀)),
        HasDerivAt (fun r : ℝ => (M.cutMoment 2 r).toReal) (M.rhsScalarTwo t) t) := by
  refine ac_and_ae_hasDerivAt_toReal_two_of_cornerRadii_tail M |>.imp fun r₁ h => ?_
  intro r₀ hr₁r₀ hr₀ h2fin S hSmono hS
  exact h hr₁r₀ hr₀ (M.measurable_rhsScalarTwo_of_tail h2fin) h2fin S hSmono hS

end PercLib.CriticalLRP.Orchestration.SmwywszgoM5

/-! ## Axiom audit -/

#print axioms PercLib.CriticalLRP.Orchestration.SmwywszgoM5.integral_eq_sub_of_offCorner
#print axioms PercLib.CriticalLRP.Orchestration.SmwywszgoM5.finite_cornerRadii_inter_Icc
#print axioms PercLib.CriticalLRP.Orchestration.SmwywszgoM5.integral_rhsScalarTwo_eq_sub_of_cornerRadii
#print axioms PercLib.CriticalLRP.Orchestration.SmwywszgoM5.ac_and_ae_hasDerivAt_toReal_two_of_cornerRadii
#print axioms PercLib.CriticalLRP.Orchestration.SmwywszgoM5.ac_and_ae_hasDerivAt_toReal_two_of_cornerRadii_tail
#print axioms PercLib.CriticalLRP.Orchestration.SmwywszgoM5.ac_and_ae_hasDerivAt_toReal_two_of_cornerRadii_tail_no_meas
