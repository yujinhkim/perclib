module

public import PercLib.CriticalLRP.Analysis.Cutoff.OffCorner.PairMassRegularity.Main
public import PercLib.CriticalLRP.Analysis.Cutoff.ConnMassRegularity.Main
public import PercLib.CriticalLRP.Analysis.Cutoff.CutoffDefect.LogIntegrable

/-! # Tail measurability of the two window-mass statistics -/

@[expose] public section

noncomputable section

open MeasureTheory Measure Filter Set
open scoped ENNReal

set_option linter.hashCommand false

namespace PercLib.CriticalLRP.CutoffDefect

open Orchestration

/-- The real pair mass is monotone on the tail where the second cutoff moment is finite. -/
theorem monotoneOn_pairMassReal (M : SourceModelData)
    (h2 : ∀ r : ℝ, 1 ≤ r → M.cutMoment 2 r ≠ ⊤) :
    MonotoneOn (fun r : ℝ => (E1Sign.pairMass M r).toReal) (Ioi 1) := by
  intro r hr r' hr' hrr'
  exact ENNReal.toReal_mono (E1Sign.pairMass_ne_top M r' (h2 r' hr'.le))
    (E1Sign.pairMass_mono M (by linarith [show (1 : ℝ) < r from hr]) hrr')

/-- The real connected mass is monotone on the same second-moment tail. -/
theorem monotoneOn_connMassReal (M : SourceModelData)
    (h2 : ∀ r : ℝ, 1 ≤ r → M.cutMoment 2 r ≠ ⊤) :
    MonotoneOn (fun r : ℝ => (E1Sign.connMass M r).toReal) (Ioi 1) := by
  intro r hr r' hr' hrr'
  exact ENNReal.toReal_mono (E1Sign.connMass_ne_top M r' (h2 r' hr'.le))
    (E1Sign.connMass_mono M (by linarith [show (1 : ℝ) < r from hr]) hrr')

/-- Pair mass is almost-everywhere measurable on the finite-second-moment tail. -/
theorem aemeasurable_pairMassReal (M : SourceModelData)
    (h2 : ∀ r : ℝ, 1 ≤ r → M.cutMoment 2 r ≠ ⊤) :
    AEMeasurable (fun r : ℝ => (E1Sign.pairMass M r).toReal) (volume.restrict (Ioi 1)) :=
  aemeasurable_restrict_of_monotoneOn measurableSet_Ioi (monotoneOn_pairMassReal M h2)

/-- Connected mass is almost-everywhere measurable on the finite-second-moment tail. -/
theorem aemeasurable_connMassReal (M : SourceModelData)
    (h2 : ∀ r : ℝ, 1 ≤ r → M.cutMoment 2 r ≠ ⊤) :
    AEMeasurable (fun r : ℝ => (E1Sign.connMass M r).toReal) (volume.restrict (Ioi 1)) :=
  aemeasurable_restrict_of_monotoneOn measurableSet_Ioi (monotoneOn_connMassReal M h2)

/-- The cluster defect is tail-a.e. measurable from finite second moments alone. -/
theorem aemeasurable_cutE1_of_secondMoment (M : SourceModelData)
    (h2 : ∀ r : ℝ, 1 ≤ r → M.cutMoment 2 r ≠ ⊤) :
    AEMeasurable (fun r : ℝ => cutE1 M r) (volume.restrict (Ioi 1)) := by
  refine aemeasurable_cutE1_of_aemeasurable_stats M ?_
    (aemeasurable_pairMassReal M h2) (aemeasurable_connMassReal M h2)
  intro r hr
  exact ne_top_of_le_ne_top (h2 r hr) (E1Sign.cutMassAt_le_cutMoment_two M r)

#print axioms monotoneOn_pairMassReal
#print axioms monotoneOn_connMassReal
#print axioms aemeasurable_pairMassReal
#print axioms aemeasurable_connMassReal
#print axioms aemeasurable_cutE1_of_secondMoment

end PercLib.CriticalLRP.CutoffDefect
