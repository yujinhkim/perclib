/-
The event-level assembly for direction `FREE-ARM-PROFILE-ASSEMBLY` (swarm `smwxh86dl`, member
`m2`).  Proofs only; every definition is in `Defs.lean`, the axiom audit is `Check.lean`.

# What this file proves

* `genProfileSum_eq` — the assembly polynomial over `n` branches is production's
  `I417FreshDepth.genFreshProfile` at `q = n + 1`, i.e. the printed normal form
  `∑_{ℓ∈[1,q]} C_ℓ χ^(2q-ℓ) T^ℓ(w,y)` with the cover's own coefficients.
* `genShape_measure_le_genFreshProfile` — **the diagram evaluation for the actual fresh cover**:
  production's `I417GenIter.genShape` at every `q ≥ 1`, arm tuple, selected arm and arm ordering
  is bounded by that printed normal form, using only the constant row sums of `τ`, the symmetry
  of `τ`, and `hπ : ∀ e, π e < 1` (the hypothesis of the BK step `genShape_measure_le`).
* `genFreshEval_genCoeff` — production's named remaining goal `GenFreshEval π q (genCoeff q)`,
  closed under the same `hπ`.
* `freshMark_measure_le_genFreshProfile` — the same bound for the fresh marked event
  `I417Gen.freshMark`, through production's `freshMark_measure_le_poly`.
-/
module

public import PercLib.CriticalLRP.Correlation.I417.Fresh.Profile.Main
public import PercLib.CriticalLRP.Correlation.I417Example.Excess

/-!
# Assembly of the actual pinned-history cover into `genFreshProfile`

Uses the real split-choice/fibre decomposition; the bound is not a general marked-moment theorem.
-/


open MeasureTheory Measure ProbabilityTheory unitInterval
open scoped ENNReal NNReal BigOperators

set_option linter.unusedSectionVars false
set_option linter.unusedDecidableInType false
set_option linter.style.longLine false
set_option linter.unusedSimpArgs false

@[expose] public section

namespace PercLib.CriticalLRP.I417FreshProfile

open PercLib.CriticalLRP

variable {V : Type*} [Countable V] [DecidableEq V]

attribute [local instance] Classical.propDecidable

/-! ## 1. The assembly polynomial is `genFreshProfile` -/

/-- **The branch polynomial over `n` attachment rounds is the fresh profile at `q = n + 1`.**
This is the comparison that the fibre package left open: the coefficient of `T ^ ℓ(w,y)` is the
number of branches of pin--mark depth `ℓ`, which is production's `genCoeff`. -/
theorem genProfileSum_eq {q : ℕ} (hq : 1 ≤ q) (τ : V → V → ℝ≥0∞) (χ : ℝ≥0∞) (v w : V) :
    genProfileSum τ χ (q - 1) v w = I417FreshDepth.genFreshProfile τ χ q v w := by
  simp only [genProfileSum, I417FreshDepth.genFreshProfile, I417FreshDepth.genCoeff,
    Nat.sub_add_cancel hq]

/-! ## 2. The event-level bound -/

/-- **The diagram evaluation of the general-`q` fresh cover.**  The fresh family `genShape` of
`q` labelled arms is bounded by the printed normalisation
`∑_{ℓ∈[1,q]} C_ℓ χ^(2q-ℓ) T^ℓ(w,y)` with the cover's own coefficients `C_ℓ = genCoeff q ℓ`.

The route: production's union/BK bound `genShape_measure_le` costs at most the sum over the
*pinned* attachment histories of the leg-weight products; the pinned-arm sum is a sub-sum of the
unrestricted history sum (`tsum_pinned_le_tsum`); the unrestricted sum is the sum of the branch
fibres (`tsum_histW_eq_tsum_histFibre`); each branch fibre, **with the selected arm pinned at
`g j`**, is at most its printed monomial (`histFibre_le_branchVal`); and grouping the branches by
their pin--mark depth produces the coefficients (`sum_markDepthK_mul`, `card_depthFiber`).

No independence, no local finiteness and no factorisation of `τ` is used, and the pinned arms are
*not* replaced by summed ones: the single hypothesis that `genShape`'s selected arm `g j` is
pinned costs only the single-term bound on the arm chain. -/
theorem genShape_measure_le_genFreshProfile (π : Sym2 V → unitInterval)
    (hπ : ∀ e, π e < 1) {q : ℕ} (hq : 1 ≤ q) (y w : V) (g : Fin q → V) (j : Fin q)
    (e : Fin (q - 1) ≃ {i : Fin q // i ≠ j}) (χ : ℝ≥0∞)
    (hχ : ∀ v : V, ∑' z : V, (edgeMeasure π) (connSet v z) = χ) :
    (edgeMeasure π) (I417GenIter.genShape y w g j e) ≤
      I417FreshDepth.genFreshProfile (fun a b => (edgeMeasure π) (connSet a b)) χ q w y := by
  have hτ : ∀ a b : V, (fun a b => (edgeMeasure π) (connSet a b)) a b
      = (fun a b => (edgeMeasure π) (connSet a b)) b a := by
    intro a b
    exact congrArg (edgeMeasure π) (I417Example.connSet_comm a b)
  refine (I417GenIter.genShape_measure_le π hπ y w g j e).trans ?_
  refine (tsum_pinned_histW_le_genProfileSum hχ hτ (pinnedArm g j e) y w (g j)).trans ?_
  rw [genProfileSum_eq hq]

/-- **Production's named remaining goal `GenFreshEval`, closed.**  The constant is the cover's own
coefficient `genCoeff q`; the only extra hypothesis is `hπ : ∀ e, π e < 1`, which is the
hypothesis of the BK/union step (`shapeOfI_measure_le`) and is not removable from that step. -/
theorem genFreshEval_genCoeff (π : Sym2 V → unitInterval) (hπ : ∀ e, π e < 1) (q : ℕ) :
    I417GenIter.GenFreshEval π q (I417FreshDepth.genCoeff q) := by
  rintro χ hχ y w g j e
  rcases q with _ | n
  · exact j.elim0
  · exact genShape_measure_le_genFreshProfile π hπ (Nat.le_add_left 1 n) y w g j e χ hχ

/-- **The fresh marked event of Lemma I.4.17**, in the printed normalisation: the same bound for
`I417Gen.freshMark`, through production's `freshMark_measure_le_freshPoly` and
`Subdivision.freshPoly`. -/
theorem freshMark_measure_le_genFreshProfile (π : Sym2 V → unitInterval)
    (hπ : ∀ e, π e < 1) {q : ℕ} (hq : 2 ≤ q) (y w : V) (g : Fin q → V) (j : Fin q)
    (χ : ℝ≥0∞) (hχ : ∀ v : V, ∑' z : V, (edgeMeasure π) (connSet v z) = χ) :
    (edgeMeasure π) (I417Gen.freshMark y g j w) ≤
      I417FreshDepth.genFreshProfile (fun a b => (edgeMeasure π) (connSet a b)) χ q w y := by
  refine (I417GenIter.freshMark_measure_le_poly π hπ hq (I417FreshDepth.genCoeff q)
    (genFreshEval_genCoeff π hπ q) χ hχ y w g j).trans ?_
  exact le_of_eq rfl

/-- **The same bound in production's `Subdivision.freshPoly` normalisation**, which is the form
consumed by the marked-side composition `Subdivision.composed_family_le` /
`I417Base.marked_fresh_le`.  This is the handoff of the diagram-evaluation step to the existing
marked side of Lemma I.4.17. -/
theorem freshMark_measure_le_freshPoly_genCoeff (π : Sym2 V → unitInterval)
    (hπ : ∀ e, π e < 1) {q : ℕ} (hq : 2 ≤ q) (y w : V) (g : Fin q → V) (j : Fin q)
    (χ : ℝ≥0∞) (hχ : ∀ v : V, ∑' z : V, (edgeMeasure π) (connSet v z) = χ) :
    (edgeMeasure π) (I417Gen.freshMark y g j w) ≤
      I417Fresh.Subdivision.freshPoly (fun a b => (edgeMeasure π) (connSet a b)) χ q
        (I417FreshDepth.genCoeff q) w y :=
  I417GenIter.freshMark_measure_le_freshPoly π hπ hq (I417FreshDepth.genCoeff q)
    (genFreshEval_genCoeff π hπ q) χ hχ y w g j

end PercLib.CriticalLRP.I417FreshProfile
