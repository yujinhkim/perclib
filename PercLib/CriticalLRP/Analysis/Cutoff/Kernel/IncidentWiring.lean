module

public import PercLib.CriticalLRP.Analysis.Cutoff.Incident.IncidentBall
public import PercLib.CriticalLRP.Analysis.Cutoff.Kernel.StrictDecrease

/-!
# Off-corner form of the finite incident-ball transport

Direction `d8` of swarm `smwtzmkep`, member `m5`.

`Kernel/StrictDecrease.lean` proves the strict difference `K r < K s` for `s < r` from positivity of
`|deriv K|` on `(s,r)`, hence strict positivity of the subtractive cutoff profile and of the kernel
of an in-range non-loop edge off the corner set.  This file wires that into the finite incident-ball
transport of `Incident/IncidentBall.lean`: the kernel-floor hypothesis `∀ e ∈ u, 0 < J_r(e)` is
replaced by the off-corner radius, the density hypothesis on `(0,r)`, and the per-edge statements
that the edges of `u` are non-loops of length at most `r`.
-/
set_option linter.style.longLine false
set_option linter.hashCommand false

@[expose] public section

noncomputable section

open MeasureTheory Filter
open scoped ENNReal NNReal Topology

namespace PercLib.CriticalLRP.Orchestration

namespace SourceModelData

variable (M : SourceModelData)

attribute [local instance] Classical.propDecidable

/-- **Open-edge probability positivity off the corner set.** -/
theorem openProb_pos_of_offCorner {r : ℝ} (hβ : 0 < (M.betaCrit : ℝ))
    (hoff : r ∉ M.cornerRadii) {x y : M.V} (hxy : x ≠ y) (hd : M.S.dist x y ≤ r)
    (hdens : ∀ t ∈ Set.Ioo 0 r, 0 < |deriv M.K t|) :
    0 < M.openProb r s(x, y) :=
  M.openProb_pos_of_kernel_pos s(x, y) hβ (M.cutKernel_pos_of_offCorner hoff hxy hd hdens)

/-- **The finite incident-ball transport with the kernel positivity discharged off the corner set.** -/
theorem sum_stdEdgeWeight_mixed_le_offCorner {r : ℝ} (y : M.V) (u : Finset (Sym2 M.V))
    (hu : u.Nonempty) {B : ℝ} (hK' : 0 ≤ -(deriv M.K r))
    (hoff : r ∉ M.cornerRadii) (hdens : ∀ t ∈ Set.Ioo 0 r, 0 < |deriv M.K t|)
    (hnl : ∀ e ∈ u, ∀ x y : M.V, e = s(x, y) → x ≠ y)
    (hact : ∀ e ∈ u, ∀ x y : M.V, e = s(x, y) → M.S.dist x y ≤ r)
    (hcard : ∀ x : M.V, ((u.filter (fun e => x ∈ e)).card : ℝ) ≤ B)
    (hfin : ∫⁻ ω, clusterVol ω (0 : M.V)
      * (if y ∈ cluster ω (0 : M.V) then (1 : ℝ≥0∞) else 0) ∂(M.cutLaw r) ≠ ⊤) :
    ∑ e ∈ u, M.stdEdgeWeight r e * (M.cutLaw r).real (evEdge (o := (0 : M.V)) (y := y) e)
      ≤ B * ((-(deriv M.K r)) / M.kernelFloor r u hu) * M.mixedFluxDensity r y := by
  classical
  refine M.sum_stdEdgeWeight_mixed_le_kernelFloor y u hu hK' (fun e he => ?_) hcard hfin
  induction e using Sym2.ind with
  | h x y =>
    exact M.cutKernel_pos_of_offCorner hoff (hnl s(x, y) he x y rfl) (hact s(x, y) he x y rfl) hdens

/-- **The finite-window flux bound with the kernel positivity discharged off the corner set.** -/
theorem sum_abs_flux_le_offCorner {r : ℝ} (y : M.V) (u : Finset (Sym2 M.V))
    (hu : u.Nonempty) {B : ℝ} (hβ : 0 < (M.betaCrit : ℝ)) (hK' : 0 ≤ -(deriv M.K r))
    (hoff : r ∉ M.cornerRadii) (hdens : ∀ t ∈ Set.Ioo 0 r, 0 < |deriv M.K t|)
    (hnl : ∀ e ∈ u, ∀ x y : M.V, e = s(x, y) → x ≠ y)
    (hact : ∀ e ∈ u, ∀ x y : M.V, e = s(x, y) → M.S.dist x y ≤ r)
    (hcard : ∀ x : M.V, ((u.filter (fun e => x ∈ e)).card : ℝ) ≤ B)
    (hfin : ∫⁻ ω, clusterVol ω (0 : M.V)
      * (if y ∈ cluster ω (0 : M.V) then (1 : ℝ≥0∞) else 0) ∂(M.cutLaw r) ≠ ⊤) :
    ∑ e ∈ u, |M.cutEdgeDeriv r e * pivotalFlux (M.cutLaw r)
        (sMomentTrunc (fun _ => (1 : ℝ)) (0 : M.V) ({y} : Finset M.V)) e|
      ≤ B * ((-(deriv M.K r)) / M.kernelFloor r u hu) * M.mixedFluxDensity r y := by
  classical
  refine M.sum_abs_flux_le_kernelFloor y u hu hβ hK' (fun e he => ?_) hcard hfin
  induction e using Sym2.ind with
  | h x y =>
    exact M.cutKernel_pos_of_offCorner hoff (hnl s(x, y) he x y rfl) (hact s(x, y) he x y rfl) hdens

/-- **The finite incident-ball transport above the density radius.**  Same as
`sum_stdEdgeWeight_mixed_le_offCorner`, but the density hypothesis is replaced by the model-level
tail radius `R` (`∃ t > R, 0 < |deriv K t|`) and the per-edge hypothesis that every edge of `u` is
longer than `R`. -/
theorem sum_stdEdgeWeight_mixed_le_offCorner_large {r R : ℝ}
    (hdensR : ∀ t : ℝ, R < t → 0 < |deriv M.K t|)
    (hoff : r ∉ M.cornerRadii) (y : M.V) (u : Finset (Sym2 M.V)) (hu : u.Nonempty) {B : ℝ}
    (hK' : 0 ≤ -(deriv M.K r))
    (hnl : ∀ e ∈ u, ∀ x y : M.V, e = s(x, y) → x ≠ y)
    (hmid : ∀ e ∈ u, ∀ x y : M.V, e = s(x, y) → R < M.S.dist x y)
    (hact : ∀ e ∈ u, ∀ x y : M.V, e = s(x, y) → M.S.dist x y ≤ r)
    (hcard : ∀ x : M.V, ((u.filter (fun e => x ∈ e)).card : ℝ) ≤ B)
    (hfin : ∫⁻ ω, clusterVol ω (0 : M.V)
      * (if y ∈ cluster ω (0 : M.V) then (1 : ℝ≥0∞) else 0) ∂(M.cutLaw r) ≠ ⊤) :
    ∑ e ∈ u, M.stdEdgeWeight r e * (M.cutLaw r).real (evEdge (o := (0 : M.V)) (y := y) e)
      ≤ B * ((-(deriv M.K r)) / M.kernelFloor r u hu) * M.mixedFluxDensity r y := by
  classical
  refine M.sum_stdEdgeWeight_mixed_le_kernelFloor y u hu hK' (fun e he => ?_) hcard hfin
  induction e using Sym2.ind with
  | h x y =>
    have hxy : x ≠ y := hnl s(x, y) he x y rfl
    have hdR : R < M.S.dist x y := hmid s(x, y) he x y rfl
    have hd := hact s(x, y) he x y rfl
    have hlt : M.S.dist x y < r := by
      rcases lt_or_eq_of_le hd with h | h
      · exact h
      · exact absurd (show r ∈ M.cornerRadii from ⟨x, y, hxy, h⟩) hoff
    exact M.cutKernel_pos_of_lt hxy hlt (fun t ht => hdensR t (lt_trans hdR ht.1))

end SourceModelData

end PercLib.CriticalLRP.Orchestration

/-! ## Axiom audit -/

#print axioms PercLib.CriticalLRP.Orchestration.SourceModelData.openProb_pos_of_offCorner
#print axioms PercLib.CriticalLRP.Orchestration.SourceModelData.sum_stdEdgeWeight_mixed_le_offCorner
#print axioms PercLib.CriticalLRP.Orchestration.SourceModelData.sum_abs_flux_le_offCorner
#print axioms PercLib.CriticalLRP.Orchestration.SourceModelData.sum_stdEdgeWeight_mixed_le_offCorner_large
