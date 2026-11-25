module
public import PercLib.CriticalLRP.Analysis.Cutoff.OffCorner.PairMassRegularity.Main
public import PercLib.CriticalLRP.Analysis.Cutoff.OffCorner.RadiusSummedFlux
public import PercLib.CriticalLRP.Analysis.Cutoff.OffCorner.RadiusTailDeriv

/-!
# Applications of excluded-mass continuity to summed-flux regularity
-/

@[expose] public section

set_option autoImplicit false
set_option linter.style.longLine false
set_option linter.hashCommand false

noncomputable section
open MeasureTheory Filter Topology Set
open scoped ENNReal NNReal Topology

namespace PercLib.CriticalLRP.Orchestration.SourceModelData

variable (M : SourceModelData)

/-- An off-corner positive radius carries no lattice point on its norm sphere. -/
theorem noSphere_of_cornerRadii {r : ℝ} (hr : 0 < r) (hoff : r ∉ M.cornerRadii)
    (y : M.V) : M.S.ρ (toVec y) ≠ r := by
  intro hy
  by_cases h0 : y = 0
  · subst y
    have hz : toVec (0 : M.V) = (0 : Fin M.d → ℝ) := by
      funext i
      simp [toVec]
    rw [hz, M.S.ρ_zero] at hy
    exact (ne_of_gt hr) hy.symm
  · apply hoff
    rw [← M.attainedRadii_eq_cornerRadii]
    exact M.mem_attainedRadii.mpr ⟨y, h0, by rw [M.S.dist_zero_right, hy]⟩

/-- The summed singleton flux is continuous on an off-corner window from continuity of `K'`
and finite second and third cutoff moments at its upper endpoint. -/
theorem hGcont_of_excludedMoments {α β : ℝ} (hα0 : 0 < α)
    (h2β : M.cutMoment 2 β ≠ ⊤) (h3β : M.cutMoment 3 β ≠ ⊤)
    (hoff : ∀ r ∈ Set.Ioo α β, r ∉ M.cornerRadii)
    (hK : ∀ r ∈ Set.Ioo α β, ContinuousAt (fun r' => deriv M.K r') r) :
    ∀ r ∈ Set.Ioo α β, ContinuousAt (fun r' => ∑' y : M.V,
      sMomentInfFlux (0 : M.V) {y} (fun _ => (1 : ℝ)) M.cutProb M.cutEdgeDeriv r') r :=
  M.hGcont_of_scalar_continuity hα0 h2β hoff hK fun r hr =>
    M.continuousAt_exclScalar (r0 := r) (r1 := β) (hα0.trans hr.1)
      (M.noSphere_of_cornerRadii (hα0.trans hr.1) (hoff r hr)) hr.2 h2β h3β

/-- The envelope endpoint derivative with `hGcont` discharged by the newly proved excluded-mass
regularity. The third endpoint moment is an explicit new input; per-vertex flux continuity
and derivative continuity are unchanged. -/
theorem hasDerivAt_cutMassReal_rhsScalar_of_endpoint_of_envelope_of_moments
    (T : ℕ → Finset M.V) (hTmono : Monotone T) (hT : ∀ y : M.V, ∃ n, y ∈ T n)
    (S : ℕ → Finset (Sym2 M.V)) (hSmono : Monotone S) (hS : ∀ e : Sym2 M.V, ∃ n, e ∈ S n)
    {α β r0 C : ℝ} (hα0 : 0 < α) (hαr0 : α < r0) (hr0β : r0 < β)
    (hoff : ∀ r ∈ Set.Ioo α β, r ∉ M.cornerRadii)
    (hKd : ∀ r ∈ Set.Ioo α β, DifferentiableAt ℝ M.K r)
    (h2β : M.cutMoment 2 β ≠ ⊤) (h3β : M.cutMoment 3 β ≠ ⊤)
    (hC0 : 0 ≤ C) (hCb : ∀ r ∈ Set.Ioo α β, -(deriv M.K r) ≤ C)
    (hKβ : deriv M.K β < 0)
    (hcontinf : ∀ y : M.V, ∀ r ∈ Set.Ioo α β, ContinuousAt
      (sMomentInfFlux (0 : M.V) {y} (fun _ => (1 : ℝ)) M.cutProb M.cutEdgeDeriv) r)
    (hK : ∀ r ∈ Set.Ioo α β, ContinuousAt (fun r' => deriv M.K r') r) :
    HasDerivAt M.cutMassReal (M.rhsScalar r0) r0 := by
  exact M.hasDerivAt_cutMassReal_rhsScalar_of_endpoint_of_envelope T hTmono hT S hSmono hS
    hα0 hαr0 hr0β hoff hKd h2β hC0 hCb hKβ hcontinf
    (M.hGcont_of_excludedMoments hα0 h2β h3β hoff hK)

/-- The tail endpoint derivative with the total summed-flux continuity discharged by the pair
and excluded-mass regularity theorems. -/
theorem hasDerivAt_cutMassReal_rhsScalar_of_endpoint_of_tail_of_moments
    (T : ℕ → Finset M.V) (hTmono : Monotone T) (hT : ∀ y : M.V, ∃ n, y ∈ T n)
    (S : ℕ → Finset (Sym2 M.V)) (hSmono : Monotone S) (hS : ∀ e : Sym2 M.V, ∃ n, e ∈ S n)
    {R α β r0 : ℝ} (hRpos : 0 < R) (hRα : R < α)
    (hlow : ∀ s : ℝ, R < s → (1 / 2) * s ^ (-(M.d : ℝ) - M.α - 1) ≤ |deriv M.K s|)
    (hupp : ∀ s : ℝ, R < s → |deriv M.K s| ≤ 2 * s ^ (-(M.d : ℝ) - M.α - 1))
    (hαr0 : α < r0) (hr0β : r0 < β)
    (hoff : ∀ r ∈ Set.Ioo α β, r ∉ M.cornerRadii)
    (h2β : M.cutMoment 2 β ≠ ⊤) (h3β : M.cutMoment 3 β ≠ ⊤)
    (hcontinf : ∀ y : M.V, ∀ r ∈ Set.Ioo α β, ContinuousAt
      (sMomentInfFlux (0 : M.V) {y} (fun _ => (1 : ℝ)) M.cutProb M.cutEdgeDeriv) r)
    (hK : ∀ r ∈ Set.Ioo α β, ContinuousAt (fun r' => deriv M.K r') r) :
    HasDerivAt M.cutMassReal (M.rhsScalar r0) r0 := by
  exact M.hasDerivAt_cutMassReal_rhsScalar_of_endpoint_of_tail T hTmono hT S hSmono hS
    hRpos hRα hlow hupp hαr0 hr0β hoff h2β hcontinf
    (M.hGcont_of_excludedMoments (hRpos.trans hRα) h2β h3β hoff hK)

end PercLib.CriticalLRP.Orchestration.SourceModelData

open PercLib.CriticalLRP.Orchestration.SourceModelData

#print axioms noSphere_of_cornerRadii
#print axioms hGcont_of_excludedMoments
#print axioms hasDerivAt_cutMassReal_rhsScalar_of_endpoint_of_envelope_of_moments
#print axioms hasDerivAt_cutMassReal_rhsScalar_of_endpoint_of_tail_of_moments
