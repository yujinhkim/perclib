/-
Swarm `smwprafq1`, member `m2` (direction B: event/BK side of `p = 5`, `k = 1`).

# Evaluation of the fork slot diagram

`forkDiagram` sums the sevenfold BK product over the pair centre `a` and the two lower hubs
`v`, `w`, with the five free leaves `b1 … b4, y` still free.  This file evaluates its sum over
the five free leaves and finds exactly

  `E|K_0|^2 * (E|K|)^6`,

using only full translation invariance of the profile: no moment finiteness, and no separate
hypothesis on `tau`.  The single joint pair is summed by `tsum_jointP_centre` (it becomes the
native second moment, never a product of two `tau`s), and every one of the six remaining arms
becomes one factor `Σ_x tau π · x = E|K|`.
-/
module

public import PercLib.CriticalLRP.Correlation.SixPoint.Fork.Regroup

set_option autoImplicit false

open Set MeasureTheory
open scoped ENNReal BigOperators
open PercLib.Percolation.Bond
open PercLib.Probability

@[expose] public section

namespace PercLib.CriticalLRP.TreeExpansion.FivePoint

variable {V : Type*}

/-! ### Moving the innermost index of seven- and eight-fold sums to the front -/

theorem tsum_move_last_seven [Countable V] (F : V → V → V → V → V → V → V → ℝ≥0∞) :
    (∑' a, ∑' b, ∑' c, ∑' d, ∑' x, ∑' y, ∑' z, F a b c d x y z)
      = ∑' z, ∑' a, ∑' b, ∑' c, ∑' d, ∑' x, ∑' y, F a b c d x y z := by
  calc (∑' a, ∑' b, ∑' c, ∑' d, ∑' x, ∑' y, ∑' z, F a b c d x y z)
      = ∑' a, ∑' b, ∑' c, ∑' d, ∑' x, ∑' z, ∑' y, F a b c d x y z :=
        tsum_congr fun a => tsum_congr fun b => tsum_congr fun c => tsum_congr fun d =>
          tsum_congr fun x => ENNReal.tsum_comm
    _ = ∑' a, ∑' b, ∑' c, ∑' d, ∑' z, ∑' x, ∑' y, F a b c d x y z :=
        tsum_congr fun a => tsum_congr fun b => tsum_congr fun c => tsum_congr fun d =>
          ENNReal.tsum_comm
    _ = ∑' a, ∑' b, ∑' c, ∑' z, ∑' d, ∑' x, ∑' y, F a b c d x y z :=
        tsum_congr fun a => tsum_congr fun b => tsum_congr fun c => ENNReal.tsum_comm
    _ = ∑' a, ∑' b, ∑' z, ∑' c, ∑' d, ∑' x, ∑' y, F a b c d x y z :=
        tsum_congr fun a => tsum_congr fun b => ENNReal.tsum_comm
    _ = ∑' a, ∑' z, ∑' b, ∑' c, ∑' d, ∑' x, ∑' y, F a b c d x y z :=
        tsum_congr fun a => ENNReal.tsum_comm
    _ = ∑' z, ∑' a, ∑' b, ∑' c, ∑' d, ∑' x, ∑' y, F a b c d x y z := ENNReal.tsum_comm

theorem tsum_move_last_eight [Countable V]
    (F : V → V → V → V → V → V → V → V → ℝ≥0∞) :
    (∑' a, ∑' b, ∑' c, ∑' d, ∑' x, ∑' y, ∑' z, ∑' u, F a b c d x y z u)
      = ∑' u, ∑' a, ∑' b, ∑' c, ∑' d, ∑' x, ∑' y, ∑' z, F a b c d x y z u := by
  calc (∑' a, ∑' b, ∑' c, ∑' d, ∑' x, ∑' y, ∑' z, ∑' u, F a b c d x y z u)
      = ∑' a, ∑' b, ∑' c, ∑' d, ∑' x, ∑' y, ∑' u, ∑' z, F a b c d x y z u :=
        tsum_congr fun a => tsum_congr fun b => tsum_congr fun c => tsum_congr fun d =>
          tsum_congr fun x => tsum_congr fun y => ENNReal.tsum_comm
    _ = ∑' a, ∑' b, ∑' c, ∑' d, ∑' x, ∑' u, ∑' y, ∑' z, F a b c d x y z u :=
        tsum_congr fun a => tsum_congr fun b => tsum_congr fun c => tsum_congr fun d =>
          tsum_congr fun x => ENNReal.tsum_comm
    _ = ∑' a, ∑' b, ∑' c, ∑' d, ∑' u, ∑' x, ∑' y, ∑' z, F a b c d x y z u :=
        tsum_congr fun a => tsum_congr fun b => tsum_congr fun c => tsum_congr fun d =>
          ENNReal.tsum_comm
    _ = ∑' a, ∑' b, ∑' c, ∑' u, ∑' d, ∑' x, ∑' y, ∑' z, F a b c d x y z u :=
        tsum_congr fun a => tsum_congr fun b => tsum_congr fun c => ENNReal.tsum_comm
    _ = ∑' a, ∑' b, ∑' u, ∑' c, ∑' d, ∑' x, ∑' y, ∑' z, F a b c d x y z u :=
        tsum_congr fun a => tsum_congr fun b => ENNReal.tsum_comm
    _ = ∑' a, ∑' u, ∑' b, ∑' c, ∑' d, ∑' x, ∑' y, ∑' z, F a b c d x y z u :=
        tsum_congr fun a => ENNReal.tsum_comm
    _ = ∑' u, ∑' a, ∑' b, ∑' c, ∑' d, ∑' x, ∑' y, ∑' z, F a b c d x y z u := ENNReal.tsum_comm

/-! ### The flat form of the fork diagram -/

/-- The fork summand in flat (left-associated) factor order, chosen so that the five free-leaf
sums peel off one factor at a time. -/
noncomputable def forkSummand (π : Sym2 V → unitInterval) (b0 x1 x2 x3 x4 x5 a v w : V) : ℝ≥0∞ :=
  tau π a v * tau π v w * jointP π b0 x1 a * tau π x2 v * tau π x3 w * tau π x4 w *
    tau π x5 a

/-- The fork diagram in flat factor order. -/
noncomputable def forkDiagramFlat [Countable V] (π : Sym2 V → unitInterval)
    (b0 b1 b2 b3 b4 y : V) : ℝ≥0∞ :=
  ∑' a, ∑' v, ∑' w, forkSummand π b0 b1 b2 b3 b4 y a v w

theorem forkDiagram_eq_flat [Countable V] (π : Sym2 V → unitInterval) (b0 b1 b2 b3 b4 y : V) :
    forkDiagram π b0 b1 b2 b3 b4 y = forkDiagramFlat π b0 b1 b2 b3 b4 y := by
  simp only [forkDiagram, forkDiagramFlat, forkSummand]
  exact tsum_congr fun a => tsum_congr fun v => tsum_congr fun w => by ring

/-! ### The five free-leaf sums factor into one second moment and four susceptibilities -/

/-- **Five-leaf factorisation.**  A flat product in which the five leaves occur one factor each
(summed in the reverse order of the factors) factorises into the product of the five sums. -/
theorem tsum_leaf_five [Countable V] (J : V → ℝ≥0∞) (A C : ℝ≥0∞) (B D E G : V → ℝ≥0∞) :
    (∑' x1, ∑' x2, ∑' x3, ∑' x4, ∑' x5, A * C * J x1 * B x2 * D x3 * E x4 * G x5)
      = (A * C) * ((∑' x1, J x1) * ((∑' x2, B x2) * ((∑' x3, D x3) *
          ((∑' x4, E x4) * (∑' x5, G x5))))) := by
  have h5 : ∀ x1 x2 x3 x4,
      (∑' x5, A * C * J x1 * B x2 * D x3 * E x4 * G x5)
        = (A * C * J x1 * B x2 * D x3 * E x4) * (∑' x5, G x5) :=
    fun x1 x2 x3 x4 => ENNReal.tsum_mul_left
  have h4 : ∀ x1 x2 x3,
      (∑' x4, (A * C * J x1 * B x2 * D x3 * E x4) * (∑' x5, G x5))
        = (A * C * J x1 * B x2 * D x3) *
            ((∑' x4, E x4) * (∑' x5, G x5)) := by
    intro x1 x2 x3
    rw [show (∑' x4, (A * C * J x1 * B x2 * D x3 * E x4) * (∑' x5, G x5))
        = ∑' x4, (A * C * J x1 * B x2 * D x3) * (E x4 * (∑' x5, G x5)) from
      tsum_congr fun x4 => by ring]
    rw [ENNReal.tsum_mul_left, ENNReal.tsum_mul_right]
  have h3 : ∀ x1 x2,
      (∑' x3, (A * C * J x1 * B x2 * D x3) * ((∑' x4, E x4) * (∑' x5, G x5)))
        = (A * C * J x1 * B x2) *
            ((∑' x3, D x3) * ((∑' x4, E x4) * (∑' x5, G x5))) := by
    intro x1 x2
    rw [show (∑' x3, (A * C * J x1 * B x2 * D x3) * ((∑' x4, E x4) * (∑' x5, G x5)))
        = ∑' x3, (A * C * J x1 * B x2) * (D x3 * ((∑' x4, E x4) * (∑' x5, G x5))) from
      tsum_congr fun x3 => by ring]
    rw [ENNReal.tsum_mul_left, ENNReal.tsum_mul_right]
  have h2 : ∀ x1,
      (∑' x2, (A * C * J x1 * B x2) * ((∑' x3, D x3) * ((∑' x4, E x4) * (∑' x5, G x5))))
        = (A * C * J x1) *
            ((∑' x2, B x2) * ((∑' x3, D x3) * ((∑' x4, E x4) * (∑' x5, G x5)))) := by
    intro x1
    rw [show (∑' x2, (A * C * J x1 * B x2) * ((∑' x3, D x3) * ((∑' x4, E x4) * (∑' x5, G x5))))
        = ∑' x2, (A * C * J x1) *
            (B x2 * ((∑' x3, D x3) * ((∑' x4, E x4) * (∑' x5, G x5)))) from
      tsum_congr fun x2 => by ring]
    rw [ENNReal.tsum_mul_left, ENNReal.tsum_mul_right]
  have h1 :
      (∑' x1, (A * C * J x1) *
          ((∑' x2, B x2) * ((∑' x3, D x3) * ((∑' x4, E x4) * (∑' x5, G x5)))))
        = (A * C) *
            ((∑' x1, J x1) * ((∑' x2, B x2) * ((∑' x3, D x3) *
              ((∑' x4, E x4) * (∑' x5, G x5))))) := by
    rw [show (∑' x1, (A * C * J x1) *
          ((∑' x2, B x2) * ((∑' x3, D x3) * ((∑' x4, E x4) * (∑' x5, G x5)))))
        = ∑' x1, (A * C) * (J x1 *
            ((∑' x2, B x2) * ((∑' x3, D x3) * ((∑' x4, E x4) * (∑' x5, G x5))))) from
      tsum_congr fun x1 => by ring]
    rw [ENNReal.tsum_mul_left, ENNReal.tsum_mul_right]
  calc (∑' x1, ∑' x2, ∑' x3, ∑' x4, ∑' x5, A * C * J x1 * B x2 * D x3 * E x4 * G x5)
      = ∑' x1, ∑' x2, ∑' x3, ∑' x4,
          (A * C * J x1 * B x2 * D x3 * E x4) * (∑' x5, G x5) :=
        tsum_congr fun x1 => tsum_congr fun x2 => tsum_congr fun x3 => tsum_congr fun x4 =>
          h5 x1 x2 x3 x4
    _ = ∑' x1, ∑' x2, ∑' x3,
          (A * C * J x1 * B x2 * D x3) * ((∑' x4, E x4) * (∑' x5, G x5)) :=
        tsum_congr fun x1 => tsum_congr fun x2 => tsum_congr fun x3 => h4 x1 x2 x3
    _ = ∑' x1, ∑' x2,
          (A * C * J x1 * B x2) *
            ((∑' x3, D x3) * ((∑' x4, E x4) * (∑' x5, G x5))) :=
        tsum_congr fun x1 => tsum_congr fun x2 => h3 x1 x2
    _ = ∑' x1, (A * C * J x1) *
          ((∑' x2, B x2) * ((∑' x3, D x3) * ((∑' x4, E x4) * (∑' x5, G x5)))) :=
        tsum_congr fun x1 => h2 x1
    _ = _ := h1

end PercLib.CriticalLRP.TreeExpansion.FivePoint
