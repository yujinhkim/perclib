/- Integrated from independently rebuilt Ultramath work, base revision 4140ac56119d2cd80995f91886669efe004839d5.
Scratch source: ../../.ultramath/smwqozn0q/m2/Defs.lean ; imports migrated;
auxiliary definitions and probability instances are collected in `Defs.lean`.
-/

/-
Cutoff-law vocabulary for Lemma I.4.18 (Hutchcroft, Critical long-range percolation I).

The source writes `T = T_{β_c,r}`, the two-point matrix of the *range-truncated* law, and
`χ = E_{β_c,r}|K|`.  Production (`Orchestration/Defs.lean`) provides `cutLaw r` and
`cutMoment p r` but not the truncated two-point function itself; these are its definitions.

Nothing is asserted here: this is a definition layer only.
-/
module

public import PercLib.CriticalLRP.Orchestration.Defs

@[expose] public section

noncomputable section

open MeasureTheory
open scoped ENNReal NNReal

namespace PercLib.CriticalLRP.Orchestration

namespace SourceModelData

variable (M : SourceModelData)

/-- The two-point function `T_{β_c,r}(x,y) = P_{β_c,r}(x ↔ y)` of the range-truncated law
that Lemma I.4.18 calls `T`. -/
def cutTwoPoint (r : ℝ) (x y : M.V) : ℝ :=
  (M.cutLaw r).real {ω : Config M.V | Connects ω x y}

/-- The same quantity in `ℝ≥0∞`, the form in which row sums are taken. -/
def cutTwoPointE (r : ℝ) (x y : M.V) : ℝ≥0∞ :=
  (M.cutLaw r) {ω : Config M.V | Connects ω x y}

/-- `E_{β_c,r}|K_x|`: the cluster mass of `x` under the truncated law.  At `x = 0` this is
the source's `χ = E_{β_c,r}|K|`, definitionally `M.cutMoment 1 r`. -/
def cutMassAt (r : ℝ) (x : M.V) : ℝ≥0∞ :=
  ∫⁻ ω, clusterVol ω x ∂(M.cutLaw r)

/-- The uncut two-point function in `ℝ≥0∞`, at any parameter `β`. -/
def twoPointE (β : ℝ≥0) (x y : M.V) : ℝ≥0∞ :=
  (M.law β) {ω : Config M.V | Connects ω x y}

/-- The uncut threefold convolution of the two-point function at the diagonal. -/
def uncutThreefold (β : ℝ≥0) : ℝ≥0∞ :=
  ∑' y, ∑' z, M.twoPointE β 0 y * M.twoPointE β y z * M.twoPointE β z 0


/-- The range-truncated law is a probability measure (the instance is not found by
unification through the definition, so it is restated). -/
instance instIsProbabilityMeasureCutLaw (M : SourceModelData) (r : ℝ) :
    IsProbabilityMeasure (M.cutLaw r) := by
  rw [SourceModelData.cutLaw]
  infer_instance

/-- The uncut long-range law is a probability measure. -/
instance instIsProbabilityMeasureLaw (M : SourceModelData) (β : ℝ≥0) :
    IsProbabilityMeasure (M.law β) := by
  rw [SourceModelData.law]
  infer_instance

/-- The edge-open profile of the truncated law. -/
abbrev cutProb (r : ℝ) : Sym2 M.V → unitInterval :=
  bernoulliEdgeProb (M.cutKernel r) (M.cutKernel_nonneg r) M.betaCrit

/-- The `ℓ = 3` convolution of the truncated two-point matrix at the origin. -/
def cutThreefold (M : SourceModelData) (r : ℝ) : ℝ≥0∞ :=
  ∑' y, ∑' z, M.cutTwoPointE r 0 y * M.cutTwoPointE r y z * M.cutTwoPointE r z 0

end SourceModelData

end PercLib.CriticalLRP.Orchestration
