/-
Swarm `smwprafq1`, member `m2` (direction B: event/BK side of `p = 5`, `k = 1`).

# The `p = 5`, `k = 1` fork-shape bound

Assembly of the two halves: the fork event is bounded by sevenfold BK with **one joint pair**
and six two-point groups (`forkEvent_le_diagram`), and the resulting diagram evaluates to

  `E|K_0|^2 * (E|K|)^6`

using only the full translation invariance `hq` of the profile (`forkDiagram_tsum`).  The joint
pair is summed by `tsum_jointP_centre` into the native second moment — it is never split into
`tau * tau` — and each of the six remaining arms contributes one susceptibility factor.  No
moment finiteness is used anywhere.

The deterministic cover of all connected six-terminal configurations by the `105` shapes is
*not* proved here and is not claimed.
-/
module

public import PercLib.CriticalLRP.Correlation.SixPoint.Fork.Eval

set_option autoImplicit false

open Set MeasureTheory
open scoped ENNReal BigOperators
open PercLib.Percolation.Bond
open PercLib.Probability

@[expose] public section

namespace PercLib.CriticalLRP.TreeExpansion.FivePoint

variable {V : Type*}

/-! ### The three hub sums -/

/-- Summing the lower hub `w` of the fork: only the spine arm `v — w` depends on `w`. -/
theorem tsum_hub_w [Countable V] [AddCommGroup V] (π : Sym2 V → unitInterval)
    (hq : ∀ x y g : V, π s(x + g, y + g) = π s(x, y)) (a v : V) (K : ℝ≥0∞) :
    (∑' w, (tau π a v * tau π v w) * K) = tau π a v * ((∑' x, tau π 0 x) * K) := by
  rw [show (∑' w, (tau π a v * tau π v w) * K) = ∑' w, tau π a v * (tau π v w * K) from
    tsum_congr fun w => by ring]
  rw [ENNReal.tsum_mul_left,
    show (∑' w, tau π v w * K) = (∑' w, tau π v w) * K from ENNReal.tsum_mul_right,
    tau_row π hq v]

/-- Summing the middle hub `v`: only the spine arm `a — v` depends on `v`. -/
theorem tsum_hub_v [Countable V] [AddCommGroup V] (π : Sym2 V → unitInterval)
    (hq : ∀ x y g : V, π s(x + g, y + g) = π s(x, y)) (a : V) (K : ℝ≥0∞) :
    (∑' v, tau π a v * K) = (∑' x, tau π 0 x) * K := by
  rw [ENNReal.tsum_mul_right, tau_row π hq a]

/-- Summing the pair centre `a`: the **joint pair** becomes the native second moment. -/
theorem tsum_hub_a [Countable V] [AddCommGroup V] (π : Sym2 V → unitInterval)
    (hq : ∀ x y g : V, π s(x + g, y + g) = π s(x, y)) (b0 : V) (K : ℝ≥0∞) :
    (∑' a, (∑' x1, jointP π b0 x1 a) * K) = secondMoment π 0 * K := by
  rw [ENNReal.tsum_mul_right, tsum_jointP_centre π hq b0]

/-! ### The diagram summed over the five free leaves -/

/-- **The fork diagram summed over its five free leaves.**  One joint pair (native second
moment at the root) times six susceptibility factors. -/
theorem forkDiagram_tsum [Countable V] [AddCommGroup V] (π : Sym2 V → unitInterval)
    (hq : ∀ x y g : V, π s(x + g, y + g) = π s(x, y)) (b0 : V) :
    (∑' x1, ∑' x2, ∑' x3, ∑' x4, ∑' x5, forkDiagram π b0 x1 x2 x3 x4 x5)
      = secondMoment π 0 * (∑' x, tau π 0 x) ^ 6 := by
  have h1 : (∑' x1, ∑' x2, ∑' x3, ∑' x4, ∑' x5, forkDiagram π b0 x1 x2 x3 x4 x5)
      = (∑' x1, ∑' x2, ∑' x3, ∑' x4, ∑' x5, ∑' a, ∑' v, ∑' w,
          forkSummand π b0 x1 x2 x3 x4 x5 a v w) := by
    simp only [forkDiagram_eq_flat, forkDiagramFlat]
  have h2 : (∑' x1, ∑' x2, ∑' x3, ∑' x4, ∑' x5, ∑' a, ∑' v, ∑' w,
        forkSummand π b0 x1 x2 x3 x4 x5 a v w)
      = (∑' a, ∑' v, ∑' w, ∑' x1, ∑' x2, ∑' x3, ∑' x4, ∑' x5,
          forkSummand π b0 x1 x2 x3 x4 x5 a v w) := by
    refine (tsum_move_last_eight (F := fun x1 x2 x3 x4 x5 a v w =>
      forkSummand π b0 x1 x2 x3 x4 x5 a v w)).trans ?_
    refine (tsum_congr fun w => tsum_move_last_seven (F := fun x1 x2 x3 x4 x5 a v =>
      forkSummand π b0 x1 x2 x3 x4 x5 a v w)).trans ?_
    refine (tsum_congr fun w => tsum_congr fun v => tsum_move_last_six
      (F := fun x1 x2 x3 x4 x5 a => forkSummand π b0 x1 x2 x3 x4 x5 a v w)).trans ?_
    refine (tsum_congr fun w => ENNReal.tsum_comm).trans ?_
    refine (ENNReal.tsum_comm).trans ?_
    exact tsum_congr fun a => ENNReal.tsum_comm
  have h3 : ∀ a v w : V, (∑' x1, ∑' x2, ∑' x3, ∑' x4, ∑' x5,
        forkSummand π b0 x1 x2 x3 x4 x5 a v w)
      = (tau π a v * tau π v w) *
          ((∑' x1, jointP π b0 x1 a) *
            ((∑' x, tau π 0 x) * ((∑' x, tau π 0 x) *
              ((∑' x, tau π 0 x) * (∑' x, tau π 0 x))))) := by
    intro a v w
    rw [show (∑' x1, ∑' x2, ∑' x3, ∑' x4, ∑' x5,
          forkSummand π b0 x1 x2 x3 x4 x5 a v w)
        = ∑' x1, ∑' x2, ∑' x3, ∑' x4, ∑' x5,
            (tau π a v * tau π v w) * (jointP π b0 x1 a) * (tau π x2 v) *
              (tau π x3 w) * (tau π x4 w) * (tau π x5 a) from
      tsum_congr fun x1 => tsum_congr fun x2 => tsum_congr fun x3 => tsum_congr fun x4 =>
        tsum_congr fun x5 => by simp only [forkSummand]]
    rw [tsum_leaf_five (J := fun x => jointP π b0 x a) (A := tau π a v) (C := tau π v w)
      (B := fun x => tau π x v) (D := fun x => tau π x w) (E := fun x => tau π x w)
      (G := fun x => tau π x a)]
    rw [tau_col π hq v, tau_col π hq w, tau_col π hq a]
  rw [h1, h2,
    show (∑' a, ∑' v, ∑' w, ∑' x1, ∑' x2, ∑' x3, ∑' x4, ∑' x5,
        forkSummand π b0 x1 x2 x3 x4 x5 a v w)
      = ∑' a, ∑' v, ∑' w, (tau π a v * tau π v w) *
          ((∑' x1, jointP π b0 x1 a) *
            ((∑' x, tau π 0 x) * ((∑' x, tau π 0 x) *
              ((∑' x, tau π 0 x) * (∑' x, tau π 0 x))))) from
      tsum_congr fun a => tsum_congr fun v => tsum_congr fun w => h3 a v w]
  -- sum the three hubs, outermost `a` last
  rw [show (∑' a, ∑' v, ∑' w, (tau π a v * tau π v w) *
        ((∑' x1, jointP π b0 x1 a) *
          ((∑' x, tau π 0 x) * ((∑' x, tau π 0 x) *
            ((∑' x, tau π 0 x) * (∑' x, tau π 0 x))))))
      = ∑' a, ∑' v, (tau π a v) *
          ((∑' x, tau π 0 x) * ((∑' x1, jointP π b0 x1 a) *
            ((∑' x, tau π 0 x) * ((∑' x, tau π 0 x) *
              ((∑' x, tau π 0 x) * (∑' x, tau π 0 x)))))) from
    tsum_congr fun a => tsum_congr fun v =>
      tsum_hub_w (π := π) hq a v
        ((∑' x1, jointP π b0 x1 a) *
          ((∑' x, tau π 0 x) * ((∑' x, tau π 0 x) *
            ((∑' x, tau π 0 x) * (∑' x, tau π 0 x)))))]
  rw [show (∑' a, ∑' v, (tau π a v) *
        ((∑' x, tau π 0 x) * ((∑' x1, jointP π b0 x1 a) *
          ((∑' x, tau π 0 x) * ((∑' x, tau π 0 x) *
            ((∑' x, tau π 0 x) * (∑' x, tau π 0 x)))))))
      = ∑' a, ((∑' x, tau π 0 x)) *
          (((∑' x, tau π 0 x)) * ((∑' x1, jointP π b0 x1 a) *
            ((∑' x, tau π 0 x) * ((∑' x, tau π 0 x) *
              ((∑' x, tau π 0 x) * (∑' x, tau π 0 x)))))) from
    tsum_congr fun a => tsum_hub_v (π := π) hq a
      ((∑' x, tau π 0 x) * ((∑' x1, jointP π b0 x1 a) *
        ((∑' x, tau π 0 x) * ((∑' x, tau π 0 x) *
          ((∑' x, tau π 0 x) * (∑' x, tau π 0 x))))))]
  rw [show (∑' a, ((∑' x, tau π 0 x)) *
        (((∑' x, tau π 0 x)) * ((∑' x1, jointP π b0 x1 a) *
          ((∑' x, tau π 0 x) * ((∑' x, tau π 0 x) *
            ((∑' x, tau π 0 x) * (∑' x, tau π 0 x)))))))
      = ∑' a, ((∑' x1, jointP π b0 x1 a)) *
          (((∑' x, tau π 0 x)) * ((∑' x, tau π 0 x) *
            ((∑' x, tau π 0 x) * ((∑' x, tau π 0 x) *
              ((∑' x, tau π 0 x) * (∑' x, tau π 0 x)))))) from
    tsum_congr fun a => by ring]
  rw [tsum_hub_a (π := π) hq b0
    (((∑' x, tau π 0 x)) * ((∑' x, tau π 0 x) *
      ((∑' x, tau π 0 x) * ((∑' x, tau π 0 x) *
        ((∑' x, tau π 0 x) * (∑' x, tau π 0 x))))))]
  ring

/-- **The `p = 5`, `k = 1` fork-shape theorem.**  For any countable abelian group `V` and any
profile with full translation invariance, the fivefold sum over the free leaves of the fork
shape event is at most `E|K_0|^2 * (E|K|)^6`. -/
theorem fork_shape_bound [Countable V] [AddCommGroup V] (π : Sym2 V → unitInterval)
    (hq : ∀ x y g : V, π s(x + g, y + g) = π s(x, y)) (b0 : V) :
    (∑' x1, ∑' x2, ∑' x3, ∑' x4, ∑' x5, law π (ForkEvent b0 x1 x2 x3 x4 x5))
      ≤ secondMoment π 0 * (∑' x, tau π 0 x) ^ 6 :=
  (ENNReal.tsum_le_tsum fun x1 => ENNReal.tsum_le_tsum fun x2 =>
    ENNReal.tsum_le_tsum fun x3 => ENNReal.tsum_le_tsum fun x4 =>
    ENNReal.tsum_le_tsum fun x5 => forkEvent_le_diagram π b0 x1 x2 x3 x4 x5).trans_eq
    (forkDiagram_tsum π hq b0)

end PercLib.CriticalLRP.TreeExpansion.FivePoint
