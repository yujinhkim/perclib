/-
Definitions for direction `(B) UNRESTRICTED-FIBRE EVALUATION`, swarm `smwxtabcx`, member `m2`.

Read-only against production `repo/.scratch/critical-lrp-orchestration`
(HEAD `1cf119aa54facb618600bb09077747b6a3b891f3`, Lean 4.35.0).  Nothing outside
`.ultramath/smwxtabcx/m2/` is written.

# What is defined, and why

Lemma I.4.17 (Hutchcroft, *Critical long-range percolation I*, arXiv:2508.18807v1, pp. 45--46)
needs the fresh-copy factor of the two-copy marked expansion in the **summed** form

  `∑_{g : Fin q → V} P(freshMark y g j w) ≤ ∑_{ℓ∈[1,q]} C_ℓ · χ^(2q-ℓ) · T^ℓ(w,y)`.

Production's `I417GenIter.GenFreshEval` states the same polynomial bound for a *single* arm
tuple `g`; such a bound cannot be summed over the infinite type `Fin q → V` (its right-hand side
does not depend on `g`).  The objects below are those of the genuinely summed evaluation:

* `freshProfileSum π χ q w y` — the printed fresh polynomial with production's own coefficients
  `I417FreshDepth.genCoeff q ℓ` (the number of branches of the iterated first-hit cover whose
  pin--mark path has `ℓ` legs), in the orientation `T^ℓ(w,y)` of the printed normal form;
* `SummedFreshProfile π q` — the summed bound itself, as a single named `Prop` with no analytic
  wrapper: exactly `I417Comp.FreshProfileBound` of the accepted composition package
  (`../../.ultramath/smwxii2d9/m2/Defs.lean`) with `tauK` written out as
  `edgeMeasure π (connSet · ·)`;
* `armFibreEquiv` — **the reindexing that makes the summed evaluation possible**.  For a fixed
  attachment history `H` of stage `q - 1` and a fixed enumeration `e` of the `q - 1` arms other
  than the selected label `j`, the arm tuples `g : Fin q → V` that *pin* the arms of `H`
  (`∀ t, H.arm t = g (e t).1`) are exactly the graph of a function of `a = g j`: giving the
  selected arm's target determines `g` uniquely.  The stage is written as `q - 1` at type
  `Fin q` so that no `Fin` cast is ever needed.

Theorem `tsum_armFibre_le_freshProfileSum` (in `Main.lean`) evaluates the *sum* of the cover:
the `g`-sum and the history sum are exchanged, the selected arm target is then summed out by the
constant row sum, and the result is the polynomial above.  No step sums a `g`-independent bound.

Theorems are in `Main.lean`; the axiom audit is `Audit.lean`.
-/
module

public import PercLib.CriticalLRP.Correlation.I417.Fresh.Profile.Main
public import PercLib.CriticalLRP.Correlation.I417.Fresh.Iter.Bound

/-! The summed fresh-profile objects and the arm-pinning equivalence. -/

open MeasureTheory Measure ProbabilityTheory unitInterval
open scoped ENNReal NNReal BigOperators

set_option linter.unusedSectionVars false
set_option linter.unusedDecidableInType false
set_option linter.style.longLine false
set_option linter.style.show false

@[expose] public section

namespace PercLib.CriticalLRP.I417SummedFresh

open PercLib.CriticalLRP

variable {V : Type*} [Countable V] [DecidableEq V]

/-! ## The printed fresh polynomial and the summed bound -/

/-- **The fresh polynomial of Lemma I.4.17** at `q` arms, with production's coefficients.

`freshProfileSum π χ q w y = ∑_{ℓ∈[1,q]} C_ℓ · χ^(2q-ℓ) · T^ℓ(w,y)` where `C_ℓ` is
`I417FreshDepth.genCoeff q ℓ`, the number of branches of the iterated first-hit cover with
pin--mark depth `ℓ`, and `T a b = edgeMeasure π (connSet a b)`.  Every monomial has exactly `2q`
kernel factors: `2q - ℓ` free (summed) legs and `ℓ` legs of the pin--mark path. -/
noncomputable def freshProfileSum (π : Sym2 V → unitInterval) (χ : ℝ≥0∞) (q : ℕ) (w y : V) :
    ℝ≥0∞ :=
  ∑ ℓ ∈ Finset.Icc 1 q,
    (I417FreshDepth.genCoeff q ℓ : ℝ≥0∞) *
      (χ ^ (2 * q - ℓ) * I417Base.iterPow (I417Fresh.tau π) ℓ w y)

/-- **The genuinely summed fresh-side input of Lemma I.4.17 at general `q`.**

For every constant row sum `χ` of the two-point kernel, every pin `y`, every mark `w` and every
selected arm `j : Fin q`, the `q`-tuple sum of the marked fresh event is at most the printed fresh
polynomial.  This is the form the two-copy marked expansion `I417Gen.moment_gap_tsub_le_marked`
consumes: the sum over the arm tuple `g` is *inside* the inequality. -/
def SummedFreshProfile (π : Sym2 V → unitInterval) (q : ℕ) : Prop :=
  ∀ (χ : ℝ≥0∞), (∀ v : V, ∑' z : V, I417Fresh.tau π v z = χ) →
    ∀ (y w : V) (j : Fin q),
      (∑' g : Fin q → V, (edgeMeasure π) (I417Gen.freshMark y g j w)) ≤
        freshProfileSum π χ q w y

/-! ## The arm-pinning reindexing

Fix an attachment history `H` of stage `q - 1` and an enumeration `e` of the `q - 1` labels other
than `j`.  The history's attached arms are `H.arm t`, and production's `genShape` uses `H` only
through the pinning `∀ t, H.arm t = g (e t).1`.  For a **fixed** `H` this pinning is satisfiable
by exactly one `g` per value of the selected arm's target `g j`:  the label `j` is not in the
range of `e`, so the other `q - 1` entries are forced, and `g j` is free. -/

/-- The inverse of the arm pinning:  the arm tuple that carries `a` on the selected label `j`
and the arms of `H` on the labels enumerated by `e`. -/
noncomputable def pinnedArmTuple {q : ℕ} (H : I417GenIter.Hist V (q - 1)) {j : Fin q}
    (e : Fin (q - 1) ≃ {i : Fin q // i ≠ j}) (a : V) : Fin q → V :=
  fun i => if h : i = j then a else H.arm (e.symm ⟨i, h⟩)

theorem pinnedArmTuple_apply_self {q : ℕ} (H : I417GenIter.Hist V (q - 1)) {j : Fin q}
    (e : Fin (q - 1) ≃ {i : Fin q // i ≠ j}) (a : V) :
    pinnedArmTuple H e a j = a := by
  rw [pinnedArmTuple, dite_eq_left rfl]

theorem pinnedArmTuple_apply_arm {q : ℕ} (H : I417GenIter.Hist V (q - 1)) {j : Fin q}
    (e : Fin (q - 1) ≃ {i : Fin q // i ≠ j}) (a : V) (t : Fin (q - 1)) :
    pinnedArmTuple H e a (e t).1 = H.arm t := by
  have hne : ¬ ((e t).1 = j) := (e t).2
  rw [pinnedArmTuple, dite_eq_right hne]
  have hsub : (⟨(e t).1, hne⟩ : {i : Fin q // i ≠ j}) = e t := Subtype.ext rfl
  rw [hsub, Equiv.symm_apply_apply]

/-- **The arm-pinning reindexing.**  For a fixed attachment history `H` and a fixed enumeration
`e` of the non-selected labels, the arm tuples that pin the arms of `H` are in bijection with the
values of the selected arm's target: `g ↦ g j`.  This is what lets the `g`-sum of the summed cover
be exchanged with the history sum and then evaluated by the constant row sum. -/
noncomputable def armFibreEquiv {q : ℕ} (H : I417GenIter.Hist V (q - 1)) {j : Fin q}
    (e : Fin (q - 1) ≃ {i : Fin q // i ≠ j}) :
    {g : Fin q → V // ∀ t : Fin (q - 1), H.arm t = g (e t).1} ≃ V where
  toFun g := g.1 j
  invFun a :=
    ⟨pinnedArmTuple H e a, fun t => (pinnedArmTuple_apply_arm H e a t).symm⟩
  left_inv g := by
    refine Subtype.ext ?_
    funext i
    show pinnedArmTuple H e (g.1 j) i = g.1 i
    by_cases h : i = j
    · rw [h, pinnedArmTuple_apply_self]
    · rw [pinnedArmTuple, dite_eq_right h]
      have hg := g.2 (e.symm ⟨i, h⟩)
      rw [hg]
      have h2 : (e (e.symm ⟨i, h⟩)).1 = i := by rw [Equiv.apply_symm_apply]
      rw [h2]
  right_inv a := pinnedArmTuple_apply_self H e a

end PercLib.CriticalLRP.I417SummedFresh
