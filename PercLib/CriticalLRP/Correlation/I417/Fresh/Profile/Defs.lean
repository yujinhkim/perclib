/-
Definitions for direction `FREE-ARM-PROFILE-ASSEMBLY` (swarm `smwxh86dl`, member `m2`).

Read-only against production `repo/.scratch/critical-lrp-orchestration` (HEAD `159f6ac`); the
reviewed history-fibre package of `smwxfstjy/m1` is present here under the names
`FibreDefs`/`FibreMain`/`FibreMarkDepth`/`FibreFinal` with the import lines rewritten only.
Nothing outside this directory is written.

# What is defined

`branchVal` is the printed normal-form monomial of one branch of the iterated first-hit cover,
`χ ^ (2q - ℓ) · T ^ ℓ`, with `ℓ = markDepthK n k` the pin--mark depth; `depthFiber` is the finite
set of branches of depth `ℓ`, whose cardinality is production's coefficient `genCoeff q ℓ`;
`genProfileSum` is the resulting coefficient-weighted polynomial in the *assembly* variable
order, i.e. `genFreshProfile` with `q = n + 1`; `pinnedArm` is the arm-pinning predicate of
production's `I417GenIter.genShape` written out, so that the actual fresh event can be compared
with the unrestricted history fibre.

Theorems are in `Main.lean`, `Profile.lean`; the axiom audit is `Check.lean`.
-/
module

public import PercLib.CriticalLRP.Correlation.I417.Fresh.HistFibre.Final

/-!
# Assembly of the actual pinned-history cover into `genFreshProfile`

Uses the real split-choice/fibre decomposition; the bound is not a general marked-moment theorem.
-/


open MeasureTheory Measure ProbabilityTheory unitInterval
open scoped ENNReal NNReal BigOperators

set_option linter.unusedSectionVars false
set_option linter.unusedDecidableInType false
set_option linter.style.longLine false

@[expose] public section

namespace PercLib.CriticalLRP.I417FreshProfile

open PercLib.CriticalLRP

variable {V : Type*} [Countable V] [DecidableEq V]

attribute [local instance] Classical.propDecidable

/-! ## The branch monomial and the depth fibres -/

/-- **The printed normal-form monomial of one branch**: `χ ^ (2(n+1) - ℓ) · T ^ ℓ(v,w)` with
`ℓ = markDepthK n k` the number of legs of the pin--mark path of the branch `k` and `2(n+1)` the
total number of legs of the `2q`-leg fresh diagram (`q = n + 1`).  The remaining `2(n+1) - ℓ`
legs are the fully summed ones and contribute the `χ`-power. -/
noncomputable def branchVal (τ : V → V → ℝ≥0∞) (χ : ℝ≥0∞) (n : ℕ)
    (k : (t : Fin n) → I417GenIter.Idx t) (v w : V) : ℝ≥0∞ :=
  χ ^ (2 * (n + 1) - I417FreshDepth.markDepthK n k) *
    I417Base.iterPow τ (I417FreshDepth.markDepthK n k) v w

/-- **The branches of pin--mark depth `ℓ`**, as a finite set of split-choice tuples.  Its
cardinality is production's coefficient `I417FreshDepth.genCoeff q ℓ` with `q = n + 1`
(`card_depthFiber`). -/
noncomputable def depthFiber (n ℓ : ℕ) : Finset ((t : Fin n) → I417GenIter.Idx t) :=
  Finset.univ.filter fun k => I417FreshDepth.markDepthK n k = ℓ

/-- **The coefficient-weighted fresh polynomial over the branches of length `n`**, in the
orientation of production's `I417GenIter.GenFreshEval`: the mark `w` is the *first* argument of
the kernel power.  With `q = n + 1` this is `genFreshProfile τ χ q w y` (`genProfileSum_eq`). -/
noncomputable def genProfileSum (τ : V → V → ℝ≥0∞) (χ : ℝ≥0∞) (n : ℕ) (v w : V) : ℝ≥0∞ :=
  ∑ ℓ ∈ Finset.Icc 1 (n + 1),
    (I417FreshDepth.depthCount n ℓ : ℝ≥0∞) * (χ ^ (2 * (n + 1) - ℓ) * I417Base.iterPow τ ℓ v w)

/-- **The arm-pinning predicate of production's `I417GenIter.genShape`**: the `t`-th attached arm
of the history is the `t`-th label of the enumeration `e` of the arms other than `j`.  The fresh
family is the union of `ShapeOfI (Hist.legs H y w (g j))` over exactly the histories satisfying
this predicate, so this is the restriction that separates the *actual* event from the
unrestricted history fibre `I417HistToSpine.histFibre`, which sums the attached arms over all
of `V`. -/
def pinnedArm {q : ℕ} (g : Fin q → V) (j : Fin q)
    (e : Fin (q - 1) ≃ {i : Fin q // i ≠ j}) (H : I417GenIter.Hist V (q - 1)) : Prop :=
  ∀ t : Fin (q - 1), H.arm t = g (e t).1

end PercLib.CriticalLRP.I417FreshProfile
