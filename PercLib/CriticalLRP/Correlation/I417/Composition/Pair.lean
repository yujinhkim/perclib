/-
The composed moment gap in pair-depth form, reusing the independently reviewed
summed fresh profile rather than reproving it.
-/
module

public import PercLib.CriticalLRP.Correlation.I417.Composition.Defs
public import PercLib.CriticalLRP.Correlation.I417.SummedFresh.Compose

/-! ## The pair-depth moment bound
-/

open MeasureTheory Measure ProbabilityTheory unitInterval
open scoped ENNReal NNReal BigOperators

set_option linter.unusedSectionVars false
set_option linter.style.longLine false

@[expose] public section

namespace PercLib.CriticalLRP.I417SummedClose

open PercLib.CriticalLRP

variable {V : Type*} [Countable V] [DecidableEq V]

/-- The pair-depth form of Lemma I.4.17's upper moment-gap bound, with the ordinary
first-moment row sum used by the paper. -/
theorem moment_gap_le_markedPairSum (π : Sym2 V → unitInterval) (hπ : ∀ e, π e < 1) (x y : V)
    {p q : ℕ} (hp : 1 ≤ p) (hq : 1 ≤ q)
    (hχ : ∀ v : V, I417.meanVol π v = I417.meanVol π x) :
    I417A.momentProd π x y p q - I417A.rawDiff π x y p q ≤
      markedPairSum π p q (I417.meanVol π x) x y := by
  exact I417SummedFresh.moment_gap_le_pairPoly π hπ x y hp hq (fun v => hχ v)

end PercLib.CriticalLRP.I417SummedClose
