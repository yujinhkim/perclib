/-
Copyright (c) 2026 PercLib contributors. Released under Apache 2.0.
-/
module

public import PercLib.CriticalLRP.Analysis.Cutoff.OffCorner.RightExcludedMass.Bridge

/-!
# Corner non-differentiability with no off-corner derivative-family input

Swarm `smwv8416l`, member `m1`.  Drop-in companion of `RightExcludedMass.Bridge`.

`Bridge.not_hasDerivAt_of_two_sided_interval_deriv_of_shell` still takes the off-corner derivative
families on a left window `(a, r₀)` and a right window `(r₀, r₁)` as inputs.  Both can be produced:

* on the right, `RightExcludedMass.Corner.exists_tail_hasDerivWithinAt_cutMassReal_rhsScalar_Ici`
  already gives the right one-sided derivative `rhsScalar r₀` past the source tail threshold, with
  no derivative-family hypothesis;
* on the left, the corner set is locally finite (`finite_cornerRadii_inter_Ioo`), so
  `exists_left_corner_gap` produces a corner-free left window, on which
  `hasDerivAt_cutMassReal_rhsScalar_of_endpoint_of_tail_of_moments` supplies the derivatives, and
  `LeftExcludedMass.Scalar.hasDerivWithinAt_cutMassReal_Iic_strict_of_interval_deriv` upgrades them
  to the left one-sided derivative `rhsScalarLt r₀`.

What remains is only model-level regularity: finite second and third cutoff moments at a larger
radius `r₂`, continuity of `r ↦ K'(r)` and of the per-vertex
singleton flux on the fixed window `(r₀ - 1, r₂)`, a nonzero shell mass, and
`0 < coeffRHS r₀`.  No separate moment at `r₀` is needed.
-/

@[expose] public section

set_option autoImplicit false
set_option linter.hashCommand false
set_option linter.style.longLine false

noncomputable section

open MeasureTheory Filter Topology Set
open scoped ENNReal NNReal Topology

namespace PercLib.CriticalLRP.Orchestration

namespace SourceModelData

variable (M : SourceModelData)

/-- **There is always a left window free of attained radii.** -/
theorem exists_left_corner_gap (r0 : ℝ) :
    ∃ a : ℝ, a < r0 ∧ ∀ r ∈ Set.Ioo a r0, r ∉ M.cornerRadii := by
  obtain ⟨ε, hε, hiso⟩ := M.exists_gap_at_attainedRadii r0
  refine ⟨r0 - ε / 2, by linarith, fun r hr hrc => ?_⟩
  have hratt : r ∈ M.attainedRadii := by
    rw [M.attainedRadii_eq_cornerRadii]
    exact hrc
  have hne : r ≠ r0 := ne_of_lt hr.2
  have hle := hiso r hratt hne
  rw [abs_of_neg (by linarith [hr.2])] at hle
  linarith [hr.1]

/-- **The left one-sided derivative at every radius past the tail threshold, with the strict-window
value `rhsScalarLt r₀`**, with no derivative-family input. -/
theorem exists_left_hasDerivWithinAt_cutMassReal_rhsScalarLt_Iic :
    ∃ R : ℝ, 0 < R ∧ ∀ {r0 r2 : ℝ}, R < r0 → 0 < r0 → r0 < r2 →
      M.cutMoment 2 r2 ≠ ⊤ → M.cutMoment 3 r2 ≠ ⊤ →
      (∀ r ∈ Set.Icc (r0 - 1) r2, ContinuousAt (fun r' => deriv M.K r') r) →
      (∀ y : M.V, ∀ r ∈ Set.Ioo (r0 - 1) r2, ContinuousAt
        (sMomentInfFlux (0 : M.V) ({y} : Finset M.V) (fun _ => (1 : ℝ))
          M.cutProb M.cutEdgeDeriv) r) →
      HasDerivWithinAt M.cutMassReal (M.rhsScalarLt r0) (Set.Iic r0) r0 := by
  obtain ⟨R, hRpos, -, hlow, hupp⟩ := M.exists_deriv_bounds
  refine ⟨R, hRpos, ?_⟩
  intro r0 r2 hRr0 hr0 hr0r2 h2 h3 hK' hcontinf
  obtain ⟨a, har0, hoffa⟩ := M.exists_left_corner_gap r0
  set α : ℝ := max ((R + r0) / 2) (max a (r0 - 1)) with hαdef
  have hRα : R < α :=
    lt_of_lt_of_le (by linarith) (le_max_left _ _)
  have hαr0 : α < r0 := max_lt (by linarith) (max_lt har0 (by linarith))
  have haα : a ≤ α := le_trans (le_max_left _ _) (le_max_right _ _)
  have hm1α : r0 - 1 ≤ α := le_trans (le_max_right _ _) (le_max_right _ _)
  have hoff : ∀ r ∈ Set.Ioo α r0, r ∉ M.cornerRadii :=
    fun r hr => hoffa r ⟨lt_of_le_of_lt haα hr.1, hr.2⟩
  have h2r0 : M.cutMoment 2 r0 ≠ ⊤ := M.cutMoment_ne_top_of_le hr0r2.le 2 h2
  have h3r0 : M.cutMoment 3 r0 ≠ ⊤ := M.cutMoment_ne_top_of_le hr0r2.le 3 h3
  have hdiff : ∀ r ∈ Set.Ioo α r0, HasDerivAt M.cutMassReal (M.rhsScalar r) r := by
    intro r hr
    exact M.hasDerivAt_cutMassReal_rhsScalar_of_endpoint_of_tail_of_moments
      (α := α) (β := r0) (r0 := r)
      M.vertexExhaustion M.monotone_vertexExhaustion M.exists_mem_vertexExhaustion
      M.edgeExhaustion M.monotone_edgeExhaustion M.exists_mem_edgeExhaustion
      hRpos hRα hlow hupp hr.1 hr.2 (fun s hs => hoff s hs) h2r0 h3r0
      (fun y s hs => hcontinf y s ⟨lt_of_le_of_lt hm1α hs.1, lt_trans hs.2 hr0r2⟩)
      (fun s hs => hK' s ⟨le_of_lt (lt_of_le_of_lt hm1α hs.1), le_of_lt (lt_trans hs.2 hr0r2)⟩)
  exact M.hasDerivWithinAt_cutMassReal_Iic_strict_of_interval_deriv hαr0 hr0 hr0r2 h2 h3
    (hK' r0 ⟨by linarith, le_of_lt hr0r2⟩) hdiff

/-- **Non-differentiability at a corner, with no derivative-family and no left-hand inputs.**

Past the source tail threshold, at any `r₀` with a nonzero shell mass and positive coefficient, the
cutoff mass has no two-sided derivative at `r₀`.  The right one-sided value is `rhsScalar r₀`
(closed window, shell included), the left one is `rhsScalarLt r₀` (strict window), and they differ
by `coeffRHS r₀ · (exclMassShell r₀).toReal`. -/
theorem exists_not_hasDerivAt_of_shell :
    ∃ R : ℝ, 0 < R ∧ ∀ {r0 r2 : ℝ}, R < r0 → 0 < r0 → r0 < r2 →
      M.cutMoment 2 r2 ≠ ⊤ → M.cutMoment 3 r2 ≠ ⊤ →
      (∀ r ∈ Set.Icc (r0 - 1) r2, ContinuousAt (fun r' => deriv M.K r') r) →
      (∀ y : M.V, ∀ r ∈ Set.Ioo (r0 - 1) r2, ContinuousAt
        (sMomentInfFlux (0 : M.V) ({y} : Finset M.V) (fun _ => (1 : ℝ))
          M.cutProb M.cutEdgeDeriv) r) →
      M.exclMassShell r0 ≠ 0 → 0 < M.coeffRHS r0 → ¬ ∃ L', HasDerivAt M.cutMassReal L' r0 := by
  obtain ⟨R1, hR1pos, hR1⟩ := M.exists_tail_hasDerivWithinAt_cutMassReal_rhsScalar_Ici
  obtain ⟨R2, hR2pos, hR2⟩ := M.exists_left_hasDerivWithinAt_cutMassReal_rhsScalarLt_Iic
  refine ⟨max (max R1 R2) 2,
    lt_of_lt_of_le (lt_of_lt_of_le hR1pos (le_max_left _ _)) (le_max_left _ _), ?_⟩
  intro r0 r2 hRr0 hr0 hr0r2 h2 h3 hK' hcontinf hshell hcoeffpos
  have hright : HasDerivWithinAt M.cutMassReal (M.rhsScalar r0) (Set.Ici r0) r0 :=
    hR1 (lt_of_le_of_lt (le_trans (le_max_left _ _) (le_max_left _ _)) hRr0) hr0 hr0r2 h2 h3
      (fun r hr => hK' r ⟨by linarith [hr.1], hr.2⟩)
      (fun y r hr => hcontinf y r ⟨by linarith [hr.1], hr.2⟩)
  have hleft : HasDerivWithinAt M.cutMassReal (M.rhsScalarLt r0) (Set.Iic r0) r0 :=
    hR2 (lt_of_le_of_lt (le_trans (le_max_right _ _) (le_max_left _ _)) hRr0) hr0 hr0r2 h2 h3 hK' hcontinf
  intro hdiff
  obtain ⟨L', hL'⟩ := hdiff
  have e1 : derivWithin M.cutMassReal (Set.Ici r0) r0 = M.rhsScalar r0 :=
    hright.derivWithin (uniqueDiffWithinAt_Ici r0)
  have e2 : derivWithin M.cutMassReal (Set.Ici r0) r0 = L' :=
    hL'.hasDerivWithinAt.derivWithin (uniqueDiffWithinAt_Ici r0)
  have e3 : derivWithin M.cutMassReal (Set.Iic r0) r0 = M.rhsScalarLt r0 :=
    hleft.derivWithin (uniqueDiffWithinAt_Iic r0)
  have e4 : derivWithin M.cutMassReal (Set.Iic r0) r0 = L' :=
    hL'.hasDerivWithinAt.derivWithin (uniqueDiffWithinAt_Iic r0)
  have hval : M.rhsScalar r0 = M.rhsScalarLt r0 := by rw [← e1, ← e3, e2, e4]
  have h2r0 : M.cutMoment 2 r0 ≠ ⊤ := M.cutMoment_ne_top_of_le hr0r2.le 2 h2
  have hclosed : E1Sign.exclMass M r0 ≠ ⊤ := M.exclMass_ne_top_of_le le_rfl h2r0
  have hshelltop : M.exclMassShell r0 ≠ ⊤ := by
    rw [M.exclMassShell_eq_exclMass_sub_strict r0 h2r0]
    exact ENNReal.sub_ne_top hclosed
  have hpos : 0 < (M.exclMassShell r0).toReal := ENNReal.toReal_pos hshell hshelltop
  have hdiffeq := M.rhsScalar_sub_coeffRHS_mul_exclScalarStrict r0 h2r0
  have hgap : M.coeffRHS r0 * M.exclScalarStrict r0 < M.rhsScalar r0 := by
    have : 0 < M.coeffRHS r0 * (M.exclMassShell r0).toReal := mul_pos hcoeffpos hpos
    linarith
  have hstrict := M.rhsScalarLt_eq_coeffRHS_mul_exclScalarStrict r0
  linarith

end SourceModelData

end PercLib.CriticalLRP.Orchestration

/-! ## 4. The attained-radius capstone -/

namespace PercLib.CriticalLRP.Orchestration

namespace SourceModelData

variable (M : SourceModelData)

/-- **At an attained radius past the tail threshold the cutoff mass is not differentiable.**

This is `exists_not_hasDerivAt_of_shell` with the shell hypothesis discharged by
`Bridge.exclMassShell_ne_zero_of_attained`.  It therefore also records whether that lemma is
genuinely proved: the axiom audit below reports `sorryAx` if it is not. -/
theorem exists_not_hasDerivAt_of_attained :
    ∃ R : ℝ, 0 < R ∧ ∀ {r0 r2 : ℝ}, R < r0 → 0 < r0 → r0 < r2 →
      r0 ∈ M.attainedRadii → M.cutMoment 2 r2 ≠ ⊤ → M.cutMoment 3 r2 ≠ ⊤ →
      (∀ r ∈ Set.Icc (r0 - 1) r2, ContinuousAt (fun r' => deriv M.K r') r) →
      (∀ y : M.V, ∀ r ∈ Set.Ioo (r0 - 1) r2, ContinuousAt
        (sMomentInfFlux (0 : M.V) ({y} : Finset M.V) (fun _ => (1 : ℝ))
          M.cutProb M.cutEdgeDeriv) r) →
      0 < M.coeffRHS r0 → ¬ ∃ L', HasDerivAt M.cutMassReal L' r0 := by
  obtain ⟨R, hRpos, hR⟩ := M.exists_not_hasDerivAt_of_shell
  refine ⟨R, hRpos, fun hRr0 hr0 hr0r2 hratt h2 h3 hK hcontinf hcoeff => ?_⟩
  exact hR hRr0 hr0 hr0r2 h2 h3 hK hcontinf
    (M.exclMassShell_ne_zero_of_attained hratt) hcoeff

end SourceModelData

end PercLib.CriticalLRP.Orchestration

/-! ## Axiom audit -/

#print axioms PercLib.CriticalLRP.Orchestration.SourceModelData.exists_left_corner_gap
#print axioms
  PercLib.CriticalLRP.Orchestration.SourceModelData.exists_left_hasDerivWithinAt_cutMassReal_rhsScalarLt_Iic
#print axioms PercLib.CriticalLRP.Orchestration.SourceModelData.exists_not_hasDerivAt_of_shell
#print axioms PercLib.CriticalLRP.Orchestration.SourceModelData.exists_not_hasDerivAt_of_attained
