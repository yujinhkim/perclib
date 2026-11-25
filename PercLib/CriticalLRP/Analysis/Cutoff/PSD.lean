/- Integrated from independently rebuilt Ultramath work, base revision 4140ac56119d2cd80995f91886669efe004839d5.
Scratch source: ../../.ultramath/smwqozn0q/m2/PSD.lean ; imports migrated;
auxiliary definitions and probability instances are collected in `Defs.lean`.
-/

/-
Positive semidefiniteness of the truncated two-point matrix, at the actual truncated law.

Lemma I.4.18's first step needs two properties of `T = T_{β_c,r}`: translation invariance
(`Translation.lean`, `cutTwoPoint_eq_sub`) and positive-definiteness.  The positive-definite
half is production mathematics (`PercLib/Percolation/Bond/ConnectionKernel.lean`,
`posSemidef_tau`, from the cluster Gram decomposition); this module only identifies
`tau (bernoulliEdgeProb (M.cutKernel r) … M.betaCrit)` with `M.cutTwoPoint r` and transfers the
statement, so the diagonal-maximality argument can be run on the *truncated* matrix rather
than on an abstract kernel.  Nothing is assumed.
-/
module

public import PercLib.CriticalLRP.Analysis.Cutoff.Translation
public import PercLib.Percolation.Bond.ConnectionKernel

@[expose] public section

noncomputable section

open MeasureTheory
open scoped ENNReal NNReal

namespace PercLib.CriticalLRP.Orchestration

namespace SourceModelData

variable (M : SourceModelData)

/-- Production `tau` at the truncated profile is the truncated two-point function. -/
theorem tau_cutProb (r : ℝ) (x y : M.V) :
    PercLib.Percolation.Bond.tau (M.cutProb r) x y = M.cutTwoPointE r x y := rfl

/-- Production `chi` at the truncated profile is the truncated cluster mass. -/
theorem chi_cutProb (r : ℝ) (x : M.V) :
    PercLib.Percolation.Bond.chi (M.cutProb r) x = M.cutMassAt r x := rfl

/-- **The truncated two-point matrix is positive semidefinite** (70KD at the cutoff). -/
theorem cutTwoPoint_posSemidef (r : ℝ) {ι : Type*} [Fintype ι] (f : ι → M.V) :
    (Matrix.of fun i j => M.cutTwoPoint r (f i) (f j)).PosSemidef := by
  have h := PercLib.Percolation.Bond.posSemidef_tau (q := M.cutProb r) f
  convert h using 2
  funext i j
  rw [M.tau_cutProb r (f i) (f j), M.cutTwoPointE_eq_ofReal,
    ENNReal.toReal_ofReal (M.cutTwoPoint_nonneg r (f i) (f j))]

end SourceModelData

end PercLib.CriticalLRP.Orchestration
