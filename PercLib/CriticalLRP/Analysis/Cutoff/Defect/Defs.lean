/-
Copyright (c) 2026 PercLib contributors. Released under Apache 2.0.

# Connected and excluded window moments for the cutoff defect

This is the actual normalized source cutoff law, not the uncut critical law.
Defect-sign and upper-bound proofs live in `Analysis/Cutoff/Defect.lean`.

Reviewed from Ultramath `smwtqkdul`, member `m6`, `E1Sign.lean`.
-/
module

public import PercLib.CriticalLRP.Correlation.I411.Basic
public import PercLib.CriticalLRP.Analysis.Cutoff.Translation
public import PercLib.CriticalLRP.Analysis.BallRatioLogError
public import PercLib.CriticalLRP.VolumeMoments.ErrorTerms

set_option autoImplicit false

/-! # Cutoff connected, excluded, and joint window moments -/

open MeasureTheory Filter Topology
open scoped ENNReal NNReal

@[expose] public section



namespace PercLib.CriticalLRP
namespace E1Sign

open Orchestration

variable (M : SourceModelData)

/-- The truncated ball `B_r` as a `Finset`. -/
noncomputable def ballF (r : ℝ) : Finset M.V := (M.finite_ball r).toFinset

theorem mem_ballF {r : ℝ} {y : M.V} : y ∈ ballF M r ↔ y ∈ M.ball r :=
  Set.Finite.mem_toFinset (M.finite_ball r)

theorem card_ballF (r : ℝ) : (ballF M r).card = (M.ball r).ncard := by
  rw [ballF, Set.ncard_eq_toFinset_card (M.ball r) (M.finite_ball r)]

/-- The truncated law is the product law of the truncated edge probabilities. -/
theorem cutLaw_eq (r : ℝ) : M.cutLaw r = edgeMeasure (M.cutProb r) := rfl

theorem cutProb_lt_one (r : ℝ) (e : Sym2 M.V) : M.cutProb r e < 1 := by
  have hcoe : ((M.cutProb r e : unitInterval) : ℝ)
      = 1 - Real.exp (-((M.betaCrit : ℝ) * M.cutKernel r e)) :=
    bernoulliEdgeProb_coe (M.cutKernel r) (M.cutKernel_nonneg r) M.betaCrit e
  have hpos : 0 < Real.exp (-((M.betaCrit : ℝ) * M.cutKernel r e)) := Real.exp_pos _
  rw [← Subtype.coe_lt_coe]
  rw [hcoe]
  have : ((1 : unitInterval) : ℝ) = 1 := rfl
  rw [this]
  linarith

/-- The source's `E_{β_c,r}[|K| ∑_{y∈B_r} |K_y|]`. -/
noncomputable def pairMass (r : ℝ) : ℝ≥0∞ :=
  ∫⁻ ω, clusterVol ω (0 : M.V) * ∑ y ∈ ballF M r, clusterVol ω y ∂(M.cutLaw r)

/-- The source's `E_{β_c,r}[|K|² |K ∩ B_r|]`. -/
noncomputable def connMass (r : ℝ) : ℝ≥0∞ :=
  ∫⁻ ω, clusterVol ω (0 : M.V) ^ 2
    * ∑ y ∈ ballF M r, (cluster ω (0 : M.V)).indicator (fun _ => (1 : ℝ≥0∞)) y
      ∂(M.cutLaw r)

/-- The source's `E_{β_c,r}[|K| ∑_{y∈B_r} 1(y ∉ K)|K_y|]` (the excluded expectation). -/
noncomputable def exclMass (r : ℝ) : ℝ≥0∞ :=
  ∫⁻ ω, clusterVol ω (0 : M.V)
    * ∑ y ∈ ballF M r,
        ((cluster ω (0 : M.V))ᶜ).indicator (fun _ => (1 : ℝ≥0∞)) y * clusterVol ω y
      ∂(M.cutLaw r)

theorem exclMass_eq_exclMoment (r : ℝ) :
    exclMass M r = I411.exclMoment (M.cutProb r) (0 : M.V) (ballF M r) := rfl

namespace PercLib.CriticalLRP
namespace E1Sign

end E1Sign
end PercLib.CriticalLRP
