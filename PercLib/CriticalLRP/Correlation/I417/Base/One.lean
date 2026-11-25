/- Integration at the `p = q = 1` instance, built from the verified
canonical branch-three proof in `MarkedOne.lean`. -/

module

public import PercLib.CriticalLRP.Correlation.I417.Base.MarkedOne
public import PercLib.CriticalLRP.Correlation.I417.Base.QOne

/-!
# The one-arm-by-one-arm instance of Lemma I.4.17

The general polygon assembly needs a marked-tree input. At `p = 1`, the proved
three-way branch cover provides it directly: `MarkedP1.jointPow_one_le_polygon`
gives the marked moment at most `χ · T²(x,w)`. The fresh BK factor adds the
final matrix step. Therefore the moment gap is at most `χ² · T³(x,y)`, with the
source's endpoints `3 ≤ 3 ≤ p + q + 1 = 3`.
-/

open MeasureTheory Measure ProbabilityTheory unitInterval
open scoped ENNReal NNReal

@[expose] public section

namespace PercLib.CriticalLRP.I417Base

open PercLib.CriticalLRP.TreeExpansion
open PercLib.CriticalLRP.I417Gen

variable {V : Type*} [Countable V]

attribute [local instance] Classical.propDecidable

/-- The source-form marked diagram premise for `q_one_polygon`, discharged at `p = 1`. -/
theorem jointPow_one_le_q_one_diagram (π : Sym2 V → unitInterval)
    (hπ : ∀ e, π e < 1) (x w : V)
    (hχ : ∀ v : V, I417.meanVol π v = I417.meanVol π x) :
    I417Gen.jointPow π x 1 w ≤
      ∑ ℓ ∈ Finset.Icc 2 (1 + 1),
        (((if ℓ = 2 then 1 else 0 : ℕ) : ℝ≥0∞) *
          ((I417.meanVol π x) ^ (2 * 1 + 1 - ℓ) *
            iterPow (fun a b => (edgeMeasure π) (connSet a b)) ℓ x w)) := by
  simpa using MarkedP1.jointPow_one_le_polygon π hπ x w (I417.meanVol π x) hχ

/-- **Lemma I.4.17 at `p = q = 1`, with no remaining marked-tree premise.**
With a constant expected cluster volume `χ`, the moment gap is at most `χ² T³`. -/
theorem moment_gap_one_one_le (π : Sym2 V → unitInterval) (hπ : ∀ e, π e < 1)
    (x y : V) (hχ : ∀ v : V, I417.meanVol π v = I417.meanVol π x) :
    I417A.momentProd π x y 1 1 - I417A.rawDiff π x y 1 1 ≤
      (I417.meanVol π x) ^ 2 *
        iterPow (fun a b => (edgeMeasure π) (connSet a b)) 3 x y := by
  have hmain := q_one_polygon π hπ x y hχ 1 (fun ℓ => if ℓ = 2 then 1 else 0)
    (fun w => jointPow_one_le_q_one_diagram π hπ x w hχ)
  simpa using hmain

end PercLib.CriticalLRP.I417Base
