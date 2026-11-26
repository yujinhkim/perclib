/-
Counterexample data for the `p = 5`, `k = 2` two-hub slot bound of
`PercLib.CriticalLRP.TreeExpansion.HubK2`.

The vertex type is `ZMod 6`; the profile is translation invariant: it opens exactly the six
"unit difference" pairs `s(x, x + 1)` with probability `θ = 1/64` and every other pair with
probability `0`.  Everything in this file is data.
-/
module

public import PercLib.CriticalLRP.Correlation.SixPoint.MixedK2.Assembly
public import PercLib.Probability.Cylinder

/-!
# The translation-invariant six-cycle profile on `ZMod 6`
-/

@[expose] public section

noncomputable section

namespace PercLib.CriticalLRP.Counterexample.Cycle6

open Set MeasureTheory
open scoped ENNReal NNReal BigOperators
open PercLib.Percolation.Bond
open PercLib.Probability

/-- `(if c then a else b) = a` when `c` holds. -/
theorem ite_pos_eq {α : Sort*} {c : Prop} [Decidable c] (h : c) {a b : α} :
    (if c then a else b) = a := by split_ifs; rfl

/-- `(if c then a else b) = b` when `c` fails. -/
theorem ite_neg_eq {α : Sort*} {c : Prop} [Decidable c] (h : ¬c) {a b : α} :
    (if c then a else b) = b := by split_ifs; rfl

/-- The symmetric weight function on pairs. -/
def stepFun (θ : unitInterval) (x y : ZMod 6) : unitInterval :=
  if y - x = 1 ∨ x - y = 1 then θ else 0

theorem stepFun_symm (θ : unitInterval) (a b : ZMod 6) : stepFun θ a b = stepFun θ b a := by
  rw [stepFun, stepFun]
  by_cases h : b - a = 1 ∨ a - b = 1
  · rw [ite_pos_eq h, ite_pos_eq (h.elim Or.inr Or.inl)]
  · rw [ite_neg_eq h, ite_neg_eq (fun h2 => h (h2.elim Or.inr Or.inl))]

/-- The translation-invariant profile: probability `θ` on unit differences, `0` elsewhere. -/
def stepProfile (θ : unitInterval) : Sym2 (ZMod 6) → unitInterval :=
  Sym2.lift ⟨stepFun θ, stepFun_symm θ⟩

/-- The opening probability `1/64`. -/
def theta : unitInterval := ⟨1 / 64, by norm_num⟩

/-- `eps = 1/64` as an extended nonnegative real. -/
def eps : ℝ≥0∞ := ((unitInterval.toNNReal theta : ℝ≥0) : ℝ≥0∞)

/-- The cyclic distance on `ZMod 6`. -/
def cdist (x y : ZMod 6) : ℕ := min (y - x).val (6 - (y - x).val)

/-- The vertex `x + t`. -/
def vtx (x : ZMod 6) (t : ℕ) : ZMod 6 := x + (t : ZMod 6)

/-- The cycle edge from `x + t` in the positive direction. -/
def eAt (x : ZMod 6) (t : ℕ) : Sym2 (ZMod 6) := s(vtx x t, vtx x (t + 1))

/-- The set of unit-difference pairs: the edges of the cycle. -/
def stepSet : Set (Sym2 (ZMod 6)) := {e | ∃ z : ZMod 6, e = s(z, z + 1)}

/-- The forward arc of `k` edges from `x`. -/
def fwdArc (x : ZMod 6) (k : ℕ) : Finset (Sym2 (ZMod 6)) := (Finset.range k).image (eAt x)

/-- The backward arc from `x + k` back to `x`, of `6 - k` edges. -/
def bwdArc (x : ZMod 6) (k : ℕ) : Finset (Sym2 (ZMod 6)) :=
  (Finset.range (6 - k)).image fun i => eAt x (k + i)

/-- The vertex set `{x, …, x + i} ∪ {x + j + 1, …, x + 5}`; its step edges leaving it are
exactly `eAt x i` and `eAt x j`. -/
def cutSet (x : ZMod 6) (i j : ℕ) : Set (ZMod 6) :=
  {z | (z - x).val ≤ i ∨ j < (z - x).val}

/-- The leaf vector of the counterexample tuple `(0, 3, 3, 3, 3)`. -/
def leaves : Fin 5 → ZMod 6 := ![0, 3, 3, 3, 3]

/-! ## Values of the profile -/

theorem stepProfile_mk (θ : unitInterval) (x y : ZMod 6) :
    stepProfile θ s(x, y) = stepFun θ x y :=
  Sym2.lift_mk ⟨stepFun θ, stepFun_symm θ⟩ x y

theorem vtx_succ (x : ZMod 6) (t : ℕ) : vtx x (t + 1) = vtx x t + 1 := by
  simp only [vtx]
  push_cast
  ring

theorem stepFun_eAt (θ : unitInterval) (x : ZMod 6) (t : ℕ) :
    stepFun θ (vtx x t) (vtx x (t + 1)) = θ := by
  rw [stepFun, vtx_succ]
  refine ite_pos_eq (Or.inl ?_)
  ring

theorem stepProfile_eAt (θ : unitInterval) (x : ZMod 6) (t : ℕ) :
    stepProfile θ (eAt x t) = θ := by
  rw [eAt, stepProfile_mk, stepFun_eAt]

theorem stepProfile_eq_zero {θ : unitInterval} {e : Sym2 (ZMod 6)} (he : e ∉ stepSet) :
    stepProfile θ e = 0 := by
  induction e using Sym2.ind with
  | _ a b =>
    rw [stepProfile_mk, stepFun, ite_neg_eq]
    rintro (h | h)
    · refine he ⟨a, ?_⟩
      have hb : b = a + 1 := by rw [← h]; ring
      rw [hb]
    · refine he ⟨b, ?_⟩
      have ha : a = b + 1 := by rw [← h]; ring
      rw [ha]
      exact Sym2.eq_swap

theorem eAt_mem_stepSet (x : ZMod 6) (t : ℕ) : eAt x t ∈ stepSet :=
  ⟨vtx x t, by rw [eAt, vtx_succ]⟩

/-! ## The leaf vector -/

theorem leaves_eq (i : Fin 5) : leaves i = if i = 0 then (0 : ZMod 6) else 3 := by
  fin_cases i <;> rfl

end PercLib.CriticalLRP.Counterexample.Cycle6
