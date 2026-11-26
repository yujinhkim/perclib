/-
Independently built for swarm `smwxcafk7`, member `m1`, direction
`GENERAL-Q-WEIGHTED-EVALUATION`.  Read-only against production
`repo/.scratch/critical-lrp-orchestration` at HEAD `8d1c9eb`.  Proofs only.
-/
module

public import PercLib.CriticalLRP.Correlation.I417.Fresh.Spine.Main
public import PercLib.CriticalLRP.Correlation.I417.Fresh.Five.Defs

/-!
# Aggregating spine branches into the printed fresh profile

The generic evaluation `spineVal_eq_normal` gives, for one branch with pin--mark path length `ℓ`,
the value `χ ^ (2q - ℓ) · T^ℓ`.  This file performs the aggregation over the branches, i.e. the last
step of the general-`q` fresh evaluation once every branch is known to be a spine:

* `spineVal_congr_size` --- **shape independence**: two spine diagrams with the same path length `ℓ`
  and the same number of hanging vertices have the *same* value.  So no per-branch computation is
  needed beyond counting `ℓ`; this is what fails for the hand-ordered evaluation of
  `Fresh/Eval/Branch.lean`, where each of the 48 members needed its own peel order.
* `spine_aggregate` --- the `genCoeff q`-weighted sum of the branches is the printed fresh profile.
* `genFreshProfile_four` --- production's accepted `I417FreshDepth.genFreshProfile` at `q = 4` is
  *exactly* the accepted `I417FreshFour.Eval.freshFourProfile`, so the spine normalisation is the
  same object as the accepted `q = 4` fresh factor.
* `genFreshProfile_five` --- the same at `q = 5`: `genFreshProfile` is
  `24 χ⁵T⁵ + 60 χ⁶T⁴ + 90 χ⁷T³ + 105 χ⁸T² + 105 χ⁹T(w,y)`, the `q = 5` fresh polynomial of the
  reviewed candidate, derived here from production's accepted `I417FreshDepth.genCoeff_five` only.

The remaining gap is combinatorial: identify the actual `Hist.legs` families
with `spineVal`, including all free-vertex joins and the path-depth count.
This module proves the analytic spine evaluation and profile aggregation only.
It does not prove the general fresh event cover or the weighted `GenFreshEval`.
-/

set_option linter.unusedSectionVars false
set_option linter.unusedDecidableInType false
set_option linter.style.longLine false
set_option linter.style.show false





open MeasureTheory Measure ProbabilityTheory unitInterval
open scoped ENNReal NNReal


@[expose] public section

namespace PercLib.CriticalLRP.I417FreshGenSpine

open PercLib.CriticalLRP
open PercLib.CriticalLRP.I417Base

variable {V : Type*} [Countable V] [DecidableEq V]

/-- **Shape independence of the spine value.**  Two tree diagrams with the same pin--mark path
length and the same number of hanging vertices evaluate identically, whatever their shapes. -/
theorem spineVal_congr_size (tau : V → V → ℝ≥0∞) (chi : ℝ≥0∞)
    (hchi : ∀ a : V, ∑' b : V, tau a b = chi) (ℓ : ℕ) {Fs Fs' : Fin (ℓ + 1) → Hang} (y w : V)
    (h : (∑ i : Fin (ℓ + 1), (Fs i).size) = ∑ i : Fin (ℓ + 1), (Fs' i).size) :
    spineVal tau ℓ Fs y w = spineVal tau ℓ Fs' y w := by
  rw [spineVal_eq tau chi hchi, spineVal_eq tau chi hchi, h]

/-- **Aggregation over the branches of the cover.**  If branch `ℓ` is a spine diagram with
`2q - ℓ` hanging vertices, then the `C ℓ`-weighted sum of the branches is the printed fresh profile
`∑_{ℓ∈[1,q]} C ℓ · χ^(2q-ℓ) · T^ℓ(v,w)`. -/
theorem spine_aggregate (tau : V → V → ℝ≥0∞) (chi : ℝ≥0∞)
    (hchi : ∀ a : V, ∑' b : V, tau a b = chi) (q : ℕ) (C : ℕ → ℕ)
    (br : (ℓ : ℕ) → Fin (ℓ + 1) → Hang)
    (hlen : ∀ ℓ : ℕ, ℓ ∈ Finset.Icc 1 q → (∑ i : Fin (ℓ + 1), (br ℓ i).size) = 2 * q - ℓ)
    (v w : V) :
    (∑ ℓ ∈ Finset.Icc 1 q, (C ℓ : ℝ≥0∞) * spineVal tau ℓ (br ℓ) v w) =
      ∑ ℓ ∈ Finset.Icc 1 q, (C ℓ : ℝ≥0∞) * (chi ^ (2 * q - ℓ) * iterPow tau ℓ v w) :=
  Finset.sum_congr rfl fun ℓ hℓ =>
    congrArg ((C ℓ : ℝ≥0∞) * ·) (spineVal_eq_normal tau chi hchi ℓ q (br ℓ) v w (hlen ℓ hℓ))

/-- **The aggregation is `genFreshProfile`.**  With the cover's own coefficients `genCoeff q` (the
accepted `I417FreshDepth` cardinalities) the aggregated spine value is precisely the fresh profile
consumed by `I417Fresh.Subdivision.composed_family_le`/`marked_fresh_le`. -/
theorem spine_aggregate_genFreshProfile (tau : V → V → ℝ≥0∞) (chi : ℝ≥0∞)
    (hchi : ∀ a : V, ∑' b : V, tau a b = chi) (q : ℕ)
    (br : (ℓ : ℕ) → Fin (ℓ + 1) → Hang)
    (hlen : ∀ ℓ : ℕ, ℓ ∈ Finset.Icc 1 q → (∑ i : Fin (ℓ + 1), (br ℓ i).size) = 2 * q - ℓ)
    (v w : V) :
    (∑ ℓ ∈ Finset.Icc 1 q, (I417FreshDepth.genCoeff q ℓ : ℝ≥0∞) * spineVal tau ℓ (br ℓ) v w) =
      I417FreshDepth.genFreshProfile tau chi q v w := by
  rw [spine_aggregate tau chi hchi q (I417FreshDepth.genCoeff q) br hlen v w]
  rfl

/-! ## The accepted `q = 4` profile and the `q = 5` profile -/

/-- Production's accepted `I417FreshDepth.genFreshProfile` at `q = 4` is exactly the accepted
`q = 4` fresh factor `6 χ⁴T⁴ + 12 χ⁵T³ + 15 χ⁶T² + 15 χ⁷T`.  The coefficients `15, 15, 12, 6` of
`T^1, T^2, T^3, T^4` are `genCoeff_four`. -/
theorem genFreshProfile_four (pi : Sym2 V → unitInterval) (chi : ℝ≥0∞) (y w : V) :
    I417FreshDepth.genFreshProfile (I417FreshTwo.kernel pi) chi 4 w y =
      I417FreshFour.Eval.freshFourProfile pi chi y w := by
  obtain ⟨c1, c2, c3, c4⟩ := I417FreshDepth.genCoeff_four
  simp only [I417FreshDepth.genFreshProfile, I417FreshFour.Eval.freshFourProfile]
  rw [show Finset.Icc 1 4 = ({1, 2, 3, 4} : Finset ℕ) from by decide]
  simp [c1, c2, c3, c4]
  ring

/-- Production's accepted `I417FreshDepth.genFreshProfile` at `q = 5` is
`24 χ⁵T⁵ + 60 χ⁶T⁴ + 90 χ⁷T³ + 105 χ⁸T² + 105 χ⁹T(w,y)`, the `q = 5` fresh polynomial.  The
coefficients `105, 105, 90, 60, 24` of `T^1, …, T^5` are the accepted `genCoeff_five`. -/
theorem genFreshProfile_five (pi : Sym2 V → unitInterval) (chi : ℝ≥0∞) (y w : V) :
    I417FreshDepth.genFreshProfile (I417FreshTwo.kernel pi) chi 5 w y =
      I417FreshFive.freshFiveProfile pi chi y w := by
  obtain ⟨c1, c2, c3, c4, c5⟩ := I417FreshDepth.genCoeff_five
  simp only [I417FreshDepth.genFreshProfile, I417FreshFive.freshFiveProfile]
  rw [show Finset.Icc 1 5 = ({1, 2, 3, 4, 5} : Finset ℕ) from by decide]
  have hk : (fun a b : V => (edgeMeasure pi) (connSet a b)) = I417FreshTwo.kernel pi := by
    funext a b
    exact (I417FreshTwo.kernel_def pi a b).symm
  rw [hk]
  simp [c1, c2, c3, c4, c5]
  ring

end PercLib.CriticalLRP.I417FreshGenSpine

namespace PercLib.CriticalLRP.I417FreshGenSpine

open PercLib.CriticalLRP
open PercLib.CriticalLRP.I417Base

variable {V : Type*} [Countable V] [DecidableEq V]

/-- **A `q = 5` branch**: ten legs, pin--mark path of length `ℓ ∈ [1,5]`, `10 - ℓ` hanging
vertices, value `χ^(10-ℓ) · T^ℓ(w,y)`.  This is what each of the 384 branches of the `q = 5` cover
must reduce to; by `spineVal_congr_size` no branch-specific peel order is needed. -/
theorem spineVal_q5 (pi : Sym2 V → unitInterval) (chi : ℝ≥0∞)
    (hchi : ∀ a : V, ∑' b : V, I417FreshTwo.kernel pi a b = chi) (ℓ : ℕ) (Fs : Fin (ℓ + 1) → Hang)
    (y w : V) (hlen : (∑ i : Fin (ℓ + 1), (Fs i).size) = 2 * 5 - ℓ) :
    spineVal (I417FreshTwo.kernel pi) ℓ Fs y w =
      chi ^ (2 * 5 - ℓ) * iterPow (I417FreshTwo.kernel pi) ℓ w y :=
  spineVal_eq_kernel pi chi hchi ℓ 5 Fs y w hlen

/-- **A `q = 4` branch**: eight legs, pin--mark path of length `ℓ ∈ [1,4]`, `8 - ℓ` hanging
vertices, value `χ^(8-ℓ) · T^ℓ(w,y)` — the value the accepted `Fresh/Eval/Branch.lean` obtains for
each of its 48 members individually. -/
theorem spineVal_q4 (pi : Sym2 V → unitInterval) (chi : ℝ≥0∞)
    (hchi : ∀ a : V, ∑' b : V, I417FreshTwo.kernel pi a b = chi) (ℓ : ℕ) (Fs : Fin (ℓ + 1) → Hang)
    (y w : V) (hlen : (∑ i : Fin (ℓ + 1), (Fs i).size) = 2 * 4 - ℓ) :
    spineVal (I417FreshTwo.kernel pi) ℓ Fs y w =
      chi ^ (2 * 4 - ℓ) * iterPow (I417FreshTwo.kernel pi) ℓ w y :=
  spineVal_eq_kernel pi chi hchi ℓ 4 Fs y w hlen

end PercLib.CriticalLRP.I417FreshGenSpine
