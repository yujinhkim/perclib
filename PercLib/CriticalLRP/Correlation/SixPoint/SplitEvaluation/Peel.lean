/-
Free-vertex evaluations of the three remaining `k = 2` slots, `j = 0, 5, 6`.

Swarm `smwxfstjy`, member `m2`, direction d3 (`REMAINING-SPLIT-EVALUATIONS`).

Each slot is the product of two joint connection probabilities and three two-point
probabilities produced by the event-level regroupings of `SixPoint.SplitPattern`, with the free
vertices summed.  The evaluation is a pure peel of the seven nested sums; every factor is closed
by exactly one of three identities:

* `tau_row` / `tau_col` (two-point row and column sums, `E|K|`), used for the three residual
  two-point factors;
* `secondMoment_eq` (both ears of a joint pair summed, centre free, `E|K|²`), used for the joint
  pairs whose two ears are summed terminals;
* `tsum_jointP_centre` (centre and one ear summed, the other ear pinned, `E|K|²`), used for the
  one joint pair that is left over at the end.

Only translation invariance `hq` is used; no independence, no moment finiteness and no
factorisation of `tau` is assumed.  The pinned ear of the last peel is the **root** and it is a
terminal of the six-terminal system:

* `j = 0`: root `b₁` (an ear of the star at `u`);
* `j = 5`: root `b₂` (an ear of the star at `v`);
* `j = 6`: root `t`, the terminal of the *sixth* arm (an ear of the star at `c`).

The root placement is not free: it is forced by which vertex is shared between a joint pair and a
residual factor (see `Bridge.lean` for the event-level consequence).
-/
module

public import PercLib.CriticalLRP.Correlation.SixPoint.SplitEvaluation.Defs

/-!
# Split evaluation and event bridges (`j = 0,5,6`)

The specified root placement is part of each evaluation. Other splits and the final moment assembly
remain open.-/


/-!
# The peels at split positions `0`, `5`, `6`

Each value is the `p = 5`, `k = 2` monomial `(E|K|²)²(E|K|)³`.
-/

open Set MeasureTheory
open scoped ENNReal BigOperators
open PercLib.Percolation.Bond
open PercLib.CriticalLRP.TreeExpansion.FivePoint

@[expose] public section

namespace PercLib.CriticalLRP.SixPoint.SplitEval

variable {V : Type*}

/-! ## Split position `j = 0`, root `b₁` -/

/-- **Free-vertex evaluation of the `j = 0` slot, root on the ear `b₁`.**  In the peel order
`t, b₀, (b₃, b₄), b₂, (v, c)` the five factors are closed as `E|K|, E|K|, E|K|², E|K|, E|K|²`,
so the slot is `(E|K|²)² (E|K|)³`.  The two sums at `c` (`t — c` and `b₀ — c`) are taken before
`c` is consumed by the joint pair `b₁, c` about `v`, and the centre `v` is consumed together with
the ear `c` in the pinning step. -/
theorem peelZero [Countable V] [AddCommGroup V] (π : Sym2 V → unitInterval)
    (hq : ∀ x y g : V, π s(x + g, y + g) = π s(x, y)) (b1 : V) :
    (∑' v, ∑' c, ∑' b2, ∑' b3, ∑' b4, ∑' b0, ∑' t,
        prodZero π b0 b1 b2 b3 b4 t v c) =
      (secondMoment π 0) ^ 2 * (∑' x, tau π 0 x) ^ 3 := by
  classical
  have ht : ∀ (v c b2 b3 b4 b0 : V),
      (∑' t, prodZero π b0 b1 b2 b3 b4 t v c) =
        jointP π b1 c v * (jointP π b3 b4 v *
          (tau π b2 v * (tau π b0 c * (∑' x, tau π 0 x)))) := by
    intro v c b2 b3 b4 b0
    rw [show (∑' t, prodZero π b0 b1 b2 b3 b4 t v c) =
        ∑' t, (jointP π b1 c v * (jointP π b3 b4 v * (tau π b2 v * tau π b0 c))) *
          tau π t c from
      tsum_congr fun t => by simp only [prodZero]; ring]
    rw [ENNReal.tsum_mul_left, tau_col π hq c]
    ring
  have hb0 : ∀ (v c b2 b3 b4 : V),
      (∑' b0, jointP π b1 c v * (jointP π b3 b4 v *
          (tau π b2 v * (tau π b0 c * (∑' x, tau π 0 x))))) =
        jointP π b1 c v * (jointP π b3 b4 v *
          (tau π b2 v * ((∑' x, tau π 0 x) * (∑' x, tau π 0 x)))) := by
    intro v c b2 b3 b4
    rw [show (∑' b0, jointP π b1 c v * (jointP π b3 b4 v *
        (tau π b2 v * (tau π b0 c * (∑' x, tau π 0 x))))) =
        ∑' b0, (jointP π b1 c v * (jointP π b3 b4 v *
          (tau π b2 v * (∑' x, tau π 0 x)))) * tau π b0 c from
      tsum_congr fun b0 => by ring]
    rw [ENNReal.tsum_mul_left, tau_col π hq c]
    ring
  have hb34 : ∀ (v c b2 : V),
      (∑' b3, ∑' b4, jointP π b1 c v * (jointP π b3 b4 v *
          (tau π b2 v * ((∑' x, tau π 0 x) * (∑' x, tau π 0 x))))) =
        jointP π b1 c v * (secondMoment π 0 *
          (tau π b2 v * ((∑' x, tau π 0 x) * (∑' x, tau π 0 x)))) := by
    intro v c b2
    rw [show (∑' b3, ∑' b4, jointP π b1 c v * (jointP π b3 b4 v *
        (tau π b2 v * ((∑' x, tau π 0 x) * (∑' x, tau π 0 x))))) =
        ∑' b3, ∑' b4, (jointP π b1 c v *
          (tau π b2 v * ((∑' x, tau π 0 x) * (∑' x, tau π 0 x)))) *
          jointP π b3 b4 v from
      tsum_congr fun b3 => tsum_congr fun b4 => by ring]
    simp only [ENNReal.tsum_mul_left]
    rw [show (∑' b3, ∑' b4, jointP π b3 b4 v) = secondMoment π v from
      (secondMoment_eq π v).symm]
    rw [secondMoment_root_independent π hq v]
    ring
  have hb2 : ∀ (v c : V),
      (∑' b2, jointP π b1 c v * (secondMoment π 0 *
          (tau π b2 v * ((∑' x, tau π 0 x) * (∑' x, tau π 0 x))))) =
        jointP π b1 c v * (secondMoment π 0 *
          ((∑' x, tau π 0 x) * ((∑' x, tau π 0 x) * (∑' x, tau π 0 x)))) := by
    intro v c
    rw [show (∑' b2, jointP π b1 c v * (secondMoment π 0 *
        (tau π b2 v * ((∑' x, tau π 0 x) * (∑' x, tau π 0 x))))) =
        ∑' b2, (jointP π b1 c v * (secondMoment π 0 *
          ((∑' x, tau π 0 x) * (∑' x, tau π 0 x)))) * tau π b2 v from
      tsum_congr fun b2 => by ring]
    rw [ENNReal.tsum_mul_left, tau_col π hq v]
    ring
  have hvc :
      (∑' v, ∑' c, jointP π b1 c v * (secondMoment π 0 *
          ((∑' x, tau π 0 x) * ((∑' x, tau π 0 x) * (∑' x, tau π 0 x))))) =
        secondMoment π 0 * (secondMoment π 0 *
          ((∑' x, tau π 0 x) * ((∑' x, tau π 0 x) * (∑' x, tau π 0 x)))) := by
    rw [show (∑' v, ∑' c, jointP π b1 c v * (secondMoment π 0 *
        ((∑' x, tau π 0 x) * ((∑' x, tau π 0 x) * (∑' x, tau π 0 x))))) =
        ∑' v, ∑' c, (secondMoment π 0 *
          ((∑' x, tau π 0 x) * ((∑' x, tau π 0 x) * (∑' x, tau π 0 x)))) *
          jointP π b1 c v from
      tsum_congr fun v => tsum_congr fun c => by ring]
    simp only [ENNReal.tsum_mul_left]
    rw [tsum_jointP_centre π hq b1]
    ring
  rw [tsum_congr fun v => tsum_congr fun c => tsum_congr fun b2 => tsum_congr fun b3 =>
      tsum_congr fun b4 => tsum_congr fun b0 => ht v c b2 b3 b4 b0]
  rw [tsum_congr fun v => tsum_congr fun c => tsum_congr fun b2 => tsum_congr fun b3 =>
      tsum_congr fun b4 => hb0 v c b2 b3 b4]
  rw [tsum_congr fun v => tsum_congr fun c => tsum_congr fun b2 => hb34 v c b2]
  rw [tsum_congr fun v => tsum_congr fun c => hb2 v c]
  rw [hvc]
  ring

/-! ## Split position `j = 5`, root `b₂` -/

/-- **Free-vertex evaluation of the `j = 5` slot, root on the ear `b₂`.**  In the peel order
`(b₀, b₁), t, b₄, b₃, (c, w)` the factors are closed as `E|K|², E|K|, E|K|, E|K|, E|K|²`.
The star at `u` is closed first, keeping `c` free; the two residuals `b₃ — w`, `b₄ — w` and the
ear `t — c` are closed next; the star at `v` is closed last, consuming the centre `w` and the ear
`c` around the pinned ear `b₂`. -/
theorem peelFive [Countable V] [AddCommGroup V] (π : Sym2 V → unitInterval)
    (hq : ∀ x y g : V, π s(x + g, y + g) = π s(x, y)) (b2 : V) :
    (∑' c, ∑' w, ∑' b3, ∑' b4, ∑' t, ∑' b0, ∑' b1,
        prodFive π b0 b1 b2 b3 b4 t c w) =
      (secondMoment π 0) ^ 2 * (∑' x, tau π 0 x) ^ 3 := by
  classical
  have hb01 : ∀ (c w b3 b4 t : V),
      (∑' b0, ∑' b1, prodFive π b0 b1 b2 b3 b4 t c w) =
        secondMoment π 0 *
          (jointP π b2 c w * (tau π b3 w * (tau π b4 w * tau π t c))) := by
    intro c w b3 b4 t
    rw [show (∑' b0, ∑' b1, prodFive π b0 b1 b2 b3 b4 t c w) =
        ∑' b0, ∑' b1, (jointP π b2 c w *
          (tau π b3 w * (tau π b4 w * tau π t c))) * jointP π b0 b1 c from
      tsum_congr fun b0 => tsum_congr fun b1 => by simp only [prodFive]; ring]
    simp only [ENNReal.tsum_mul_left]
    rw [show (∑' b0, ∑' b1, jointP π b0 b1 c) = secondMoment π c from
      (secondMoment_eq π c).symm]
    rw [secondMoment_root_independent π hq c]
    ring
  have ht : ∀ (c w b3 b4 : V),
      (∑' t, secondMoment π 0 *
          (jointP π b2 c w * (tau π b3 w * (tau π b4 w * tau π t c)))) =
        secondMoment π 0 * (jointP π b2 c w *
          (tau π b3 w * (tau π b4 w * (∑' x, tau π 0 x)))) := by
    intro c w b3 b4
    rw [show (∑' t, secondMoment π 0 *
        (jointP π b2 c w * (tau π b3 w * (tau π b4 w * tau π t c)))) =
        ∑' t, (secondMoment π 0 *
          (jointP π b2 c w * (tau π b3 w * tau π b4 w))) * tau π t c from
      tsum_congr fun t => by ring]
    rw [ENNReal.tsum_mul_left, tau_col π hq c]
    ring
  have hb4 : ∀ (c w b3 : V),
      (∑' b4, secondMoment π 0 * (jointP π b2 c w *
          (tau π b3 w * (tau π b4 w * (∑' x, tau π 0 x))))) =
        secondMoment π 0 * (jointP π b2 c w *
          (tau π b3 w * ((∑' x, tau π 0 x) * (∑' x, tau π 0 x)))) := by
    intro c w b3
    rw [show (∑' b4, secondMoment π 0 * (jointP π b2 c w *
        (tau π b3 w * (tau π b4 w * (∑' x, tau π 0 x))))) =
        ∑' b4, (secondMoment π 0 * (jointP π b2 c w *
          (tau π b3 w * (∑' x, tau π 0 x)))) * tau π b4 w from
      tsum_congr fun b4 => by ring]
    rw [ENNReal.tsum_mul_left, tau_col π hq w]
    ring
  have hb3 : ∀ (c w : V),
      (∑' b3, secondMoment π 0 * (jointP π b2 c w *
          (tau π b3 w * ((∑' x, tau π 0 x) * (∑' x, tau π 0 x))))) =
        secondMoment π 0 * (jointP π b2 c w *
          ((∑' x, tau π 0 x) * ((∑' x, tau π 0 x) * (∑' x, tau π 0 x)))) := by
    intro c w
    rw [show (∑' b3, secondMoment π 0 * (jointP π b2 c w *
        (tau π b3 w * ((∑' x, tau π 0 x) * (∑' x, tau π 0 x))))) =
        ∑' b3, (secondMoment π 0 * (jointP π b2 c w *
          ((∑' x, tau π 0 x) * (∑' x, tau π 0 x)))) * tau π b3 w from
      tsum_congr fun b3 => by ring]
    rw [ENNReal.tsum_mul_left, tau_col π hq w]
    ring
  have hcw :
      (∑' c, ∑' w, secondMoment π 0 * (jointP π b2 c w *
          ((∑' x, tau π 0 x) * ((∑' x, tau π 0 x) * (∑' x, tau π 0 x))))) =
        secondMoment π 0 * (secondMoment π 0 *
          ((∑' x, tau π 0 x) * ((∑' x, tau π 0 x) * (∑' x, tau π 0 x)))) := by
    rw [show (∑' c, ∑' w, secondMoment π 0 * (jointP π b2 c w *
        ((∑' x, tau π 0 x) * ((∑' x, tau π 0 x) * (∑' x, tau π 0 x))))) =
        ∑' c, ∑' w, (secondMoment π 0 *
          ((∑' x, tau π 0 x) * ((∑' x, tau π 0 x) * (∑' x, tau π 0 x)))) *
          jointP π b2 c w from
      tsum_congr fun c => tsum_congr fun w => by ring]
    simp only [ENNReal.tsum_mul_left]
    rw [ENNReal.tsum_comm, tsum_jointP_centre π hq b2]
    ring
  simp only [hb01, ht, hb4, hb3]
  rw [hcw]
  ring

/-! ## Split position `j = 6`, root `t` -/

/-- **Free-vertex evaluation of the `j = 6` slot, root on the *sixth* terminal `t`.**  In the
peel order `(b₀, b₁), b₂, b₄, b₃, (v, w)` the factors are closed as
`E|K|², E|K|, E|K|, E|K|, E|K|²`: the pinning step consumes the centre `w` and the ear `v` of the
joint pair `v, t` about `w`, so the root has to be `t` — the terminal of the sixth arm. -/
theorem peelSix [Countable V] [AddCommGroup V] (π : Sym2 V → unitInterval)
    (hq : ∀ x y g : V, π s(x + g, y + g) = π s(x, y)) (t : V) :
    (∑' v, ∑' w, ∑' b3, ∑' b4, ∑' b2, ∑' b0, ∑' b1,
        prodSix π b0 b1 b2 b3 b4 t v w) =
      (secondMoment π 0) ^ 2 * (∑' x, tau π 0 x) ^ 3 := by
  classical
  have hb01 : ∀ (v w b3 b4 b2 : V),
      (∑' b0, ∑' b1, prodSix π b0 b1 b2 b3 b4 t v w) =
        secondMoment π 0 *
          (jointP π v t w * (tau π b2 v * (tau π b3 w * tau π b4 w))) := by
    intro v w b3 b4 b2
    rw [show (∑' b0, ∑' b1, prodSix π b0 b1 b2 b3 b4 t v w) =
        ∑' b0, ∑' b1, (jointP π v t w *
          (tau π b2 v * (tau π b3 w * tau π b4 w))) * jointP π b0 b1 v from
      tsum_congr fun b0 => tsum_congr fun b1 => by simp only [prodSix]; ring]
    simp only [ENNReal.tsum_mul_left]
    rw [show (∑' b0, ∑' b1, jointP π b0 b1 v) = secondMoment π v from
      (secondMoment_eq π v).symm]
    rw [secondMoment_root_independent π hq v]
    ring
  have hb2 : ∀ (v w b3 b4 : V),
      (∑' b2, secondMoment π 0 *
          (jointP π v t w * (tau π b2 v * (tau π b3 w * tau π b4 w)))) =
        secondMoment π 0 *
          (jointP π v t w * ((∑' x, tau π 0 x) * (tau π b3 w * tau π b4 w))) := by
    intro v w b3 b4
    rw [show (∑' b2, secondMoment π 0 *
        (jointP π v t w * (tau π b2 v * (tau π b3 w * tau π b4 w)))) =
        ∑' b2, (secondMoment π 0 *
          (jointP π v t w * (tau π b3 w * tau π b4 w))) * tau π b2 v from
      tsum_congr fun b2 => by ring]
    rw [ENNReal.tsum_mul_left, tau_col π hq v]
    ring
  have hb4 : ∀ (v w b3 : V),
      (∑' b4, secondMoment π 0 *
          (jointP π v t w * ((∑' x, tau π 0 x) * (tau π b3 w * tau π b4 w)))) =
        secondMoment π 0 * (jointP π v t w *
          ((∑' x, tau π 0 x) * (tau π b3 w * (∑' x, tau π 0 x)))) := by
    intro v w b3
    rw [show (∑' b4, secondMoment π 0 *
        (jointP π v t w * ((∑' x, tau π 0 x) * (tau π b3 w * tau π b4 w)))) =
        ∑' b4, (secondMoment π 0 *
          (jointP π v t w * ((∑' x, tau π 0 x) * tau π b3 w))) * tau π b4 w from
      tsum_congr fun b4 => by ring]
    rw [ENNReal.tsum_mul_left, tau_col π hq w]
    ring
  have hb3 : ∀ (v w : V),
      (∑' b3, secondMoment π 0 * (jointP π v t w *
          ((∑' x, tau π 0 x) * (tau π b3 w * (∑' x, tau π 0 x))))) =
        secondMoment π 0 * (jointP π v t w *
          ((∑' x, tau π 0 x) * ((∑' x, tau π 0 x) * (∑' x, tau π 0 x)))) := by
    intro v w
    rw [show (∑' b3, secondMoment π 0 * (jointP π v t w *
        ((∑' x, tau π 0 x) * (tau π b3 w * (∑' x, tau π 0 x))))) =
        ∑' b3, (secondMoment π 0 * (jointP π v t w *
          ((∑' x, tau π 0 x) * (∑' x, tau π 0 x)))) * tau π b3 w from
      tsum_congr fun b3 => by ring]
    rw [ENNReal.tsum_mul_left, tau_col π hq w]
    ring
  have hvw :
      (∑' v, ∑' w, secondMoment π 0 * (jointP π v t w *
          ((∑' x, tau π 0 x) * ((∑' x, tau π 0 x) * (∑' x, tau π 0 x))))) =
        secondMoment π 0 * (secondMoment π 0 *
          ((∑' x, tau π 0 x) * ((∑' x, tau π 0 x) * (∑' x, tau π 0 x)))) := by
    rw [show (∑' v, ∑' w, secondMoment π 0 * (jointP π v t w *
        ((∑' x, tau π 0 x) * ((∑' x, tau π 0 x) * (∑' x, tau π 0 x))))) =
        ∑' v, ∑' w, (secondMoment π 0 *
          ((∑' x, tau π 0 x) * ((∑' x, tau π 0 x) * (∑' x, tau π 0 x)))) *
          jointP π t v w from
      tsum_congr fun v => tsum_congr fun w => by
        rw [jointP_comm π v t w]; ring]
    simp only [ENNReal.tsum_mul_left]
    rw [ENNReal.tsum_comm, tsum_jointP_centre π hq t]
    ring
  simp only [hb01, hb2, hb4, hb3]
  rw [hvw]
  ring

/-- **Nesting reindexing at `j = 0`.**  The assembly order `b₀, b₂, b₃, b₄, t, c, v` and the
peel order `v, c, b₂, b₃, b₄, b₀, t` carry the same sevenfold sum.  Purely bookkeeping: it
permutes the seven indices of the extended sum, nothing else. -/
theorem reindexZero (F : V → V → V → V → V → V → V → ℝ≥0∞) :
    (∑' b0, ∑' b2, ∑' b3, ∑' b4, ∑' t, ∑' c, ∑' v, F b0 b2 b3 b4 t c v)
      = ∑' v, ∑' c, ∑' b2, ∑' b3, ∑' b4, ∑' b0, ∑' t, F b0 b2 b3 b4 t c v := by
  rw [tsum_congr fun b0 => tsum_congr fun b2 => tsum_congr fun b3 => tsum_congr fun b4 =>
    tsum_congr fun t => ENNReal.tsum_comm]
  rw [tsum_congr fun b0 => tsum_congr fun b2 => tsum_congr fun b3 => tsum_congr fun b4 =>
    ENNReal.tsum_comm]
  rw [tsum_congr fun b0 => tsum_congr fun b2 => tsum_congr fun b3 => ENNReal.tsum_comm]
  rw [tsum_congr fun b0 => tsum_congr fun b2 => ENNReal.tsum_comm]
  rw [tsum_congr fun b0 => ENNReal.tsum_comm]
  rw [ENNReal.tsum_comm]
  rw [tsum_congr fun v => tsum_congr fun b0 => tsum_congr fun b2 => tsum_congr fun b3 =>
    tsum_congr fun b4 => ENNReal.tsum_comm]
  rw [tsum_congr fun v => tsum_congr fun b0 => tsum_congr fun b2 => tsum_congr fun b3 =>
    ENNReal.tsum_comm]
  rw [tsum_congr fun v => tsum_congr fun b0 => tsum_congr fun b2 => ENNReal.tsum_comm]
  rw [tsum_congr fun v => tsum_congr fun b0 => ENNReal.tsum_comm]
  rw [tsum_congr fun v => ENNReal.tsum_comm]
  rw [tsum_congr fun v => tsum_congr fun c => ENNReal.tsum_comm]
  rw [tsum_congr fun v => tsum_congr fun c => tsum_congr fun b2 => ENNReal.tsum_comm]
  rw [tsum_congr fun v => tsum_congr fun c => tsum_congr fun b2 => tsum_congr fun b3 =>
    ENNReal.tsum_comm]

/-- **Nesting reindexing at `j = 5`.**  Assembly order `b₀, b₁, b₃, b₄, t, c, w`, peel order
`c, w, b₃, b₄, t, b₀, b₁`. -/
theorem reindexFive (F : V → V → V → V → V → V → V → ℝ≥0∞) :
    (∑' b0, ∑' b1, ∑' b3, ∑' b4, ∑' t, ∑' c, ∑' w, F b0 b1 b3 b4 t c w)
      = ∑' c, ∑' w, ∑' b3, ∑' b4, ∑' t, ∑' b0, ∑' b1, F b0 b1 b3 b4 t c w := by
  rw [tsum_congr fun b0 => tsum_congr fun b1 => tsum_congr fun b3 => tsum_congr fun b4 =>
    ENNReal.tsum_comm]
  rw [tsum_congr fun b0 => tsum_congr fun b1 => tsum_congr fun b3 => ENNReal.tsum_comm]
  rw [tsum_congr fun b0 => tsum_congr fun b1 => ENNReal.tsum_comm]
  rw [tsum_congr fun b0 => ENNReal.tsum_comm]
  rw [ENNReal.tsum_comm]
  rw [tsum_congr fun c => tsum_congr fun b0 => tsum_congr fun b1 => tsum_congr fun b3 =>
    tsum_congr fun b4 => ENNReal.tsum_comm]
  rw [tsum_congr fun c => tsum_congr fun b0 => tsum_congr fun b1 => tsum_congr fun b3 =>
    ENNReal.tsum_comm]
  rw [tsum_congr fun c => tsum_congr fun b0 => tsum_congr fun b1 => ENNReal.tsum_comm]
  rw [tsum_congr fun c => tsum_congr fun b0 => ENNReal.tsum_comm]
  rw [tsum_congr fun c => ENNReal.tsum_comm]
  rw [tsum_congr fun c => tsum_congr fun w => tsum_congr fun b0 => ENNReal.tsum_comm]
  rw [tsum_congr fun c => tsum_congr fun w => ENNReal.tsum_comm]
  rw [tsum_congr fun c => tsum_congr fun w => tsum_congr fun b3 => tsum_congr fun b0 =>
    ENNReal.tsum_comm]
  rw [tsum_congr fun c => tsum_congr fun w => tsum_congr fun b3 => ENNReal.tsum_comm]
  rw [tsum_congr fun c => tsum_congr fun w => tsum_congr fun b3 => tsum_congr fun b4 =>
    tsum_congr fun b0 => ENNReal.tsum_comm]
  rw [tsum_congr fun c => tsum_congr fun w => tsum_congr fun b3 => tsum_congr fun b4 =>
    ENNReal.tsum_comm]

/-- **Nesting reindexing at `j = 6`.**  Assembly order `b₀, b₁, b₂, b₃, b₄, v, w`, peel order
`v, w, b₃, b₄, b₂, b₀, b₁`. -/
theorem reindexSix (F : V → V → V → V → V → V → V → ℝ≥0∞) :
    (∑' b0, ∑' b1, ∑' b2, ∑' b3, ∑' b4, ∑' v, ∑' w, F b0 b1 b2 b3 b4 v w)
      = ∑' v, ∑' w, ∑' b3, ∑' b4, ∑' b2, ∑' b0, ∑' b1, F b0 b1 b2 b3 b4 v w := by
  rw [tsum_congr fun b0 => tsum_congr fun b1 => tsum_congr fun b2 => tsum_congr fun b3 =>
    ENNReal.tsum_comm]
  rw [tsum_congr fun b0 => tsum_congr fun b1 => tsum_congr fun b2 => ENNReal.tsum_comm]
  rw [tsum_congr fun b0 => tsum_congr fun b1 => ENNReal.tsum_comm]
  rw [tsum_congr fun b0 => ENNReal.tsum_comm]
  rw [ENNReal.tsum_comm]
  rw [tsum_congr fun v => tsum_congr fun b0 => tsum_congr fun b1 => tsum_congr fun b2 =>
    tsum_congr fun b3 => ENNReal.tsum_comm]
  rw [tsum_congr fun v => tsum_congr fun b0 => tsum_congr fun b1 => tsum_congr fun b2 =>
    ENNReal.tsum_comm]
  rw [tsum_congr fun v => tsum_congr fun b0 => tsum_congr fun b1 => ENNReal.tsum_comm]
  rw [tsum_congr fun v => tsum_congr fun b0 => ENNReal.tsum_comm]
  rw [tsum_congr fun v => ENNReal.tsum_comm]
  rw [tsum_congr fun v => tsum_congr fun w => tsum_congr fun b0 => tsum_congr fun b1 =>
    ENNReal.tsum_comm]
  rw [tsum_congr fun v => tsum_congr fun w => tsum_congr fun b0 => ENNReal.tsum_comm]
  rw [tsum_congr fun v => tsum_congr fun w => ENNReal.tsum_comm]
  rw [tsum_congr fun v => tsum_congr fun w => tsum_congr fun b3 => tsum_congr fun b0 =>
    tsum_congr fun b1 => ENNReal.tsum_comm]
  rw [tsum_congr fun v => tsum_congr fun w => tsum_congr fun b3 => tsum_congr fun b0 =>
    ENNReal.tsum_comm]
  rw [tsum_congr fun v => tsum_congr fun w => tsum_congr fun b3 => ENNReal.tsum_comm]
  rw [tsum_congr fun v => tsum_congr fun w => tsum_congr fun b3 => tsum_congr fun b4 =>
    tsum_congr fun b0 => ENNReal.tsum_comm]
  rw [tsum_congr fun v => tsum_congr fun w => tsum_congr fun b3 => tsum_congr fun b4 =>
    ENNReal.tsum_comm]

/-- **The `j = 0` slot in the order of the assembly**, i.e. with the five non-root terminals
summed outside the two free-vertex sums, equals `(E|K|²)² (E|K|)³`.  The terminal `b₁` is the
root and is not summed. -/
theorem slotZero_tsum [Countable V] [AddCommGroup V] (π : Sym2 V → unitInterval)
    (hq : ∀ x y g : V, π s(x + g, y + g) = π s(x, y)) (b1 : V) :
    (∑' b0, ∑' b2, ∑' b3, ∑' b4, ∑' t, slotZero π b0 b1 b2 b3 b4 t) =
      (secondMoment π 0) ^ 2 * (∑' x, tau π 0 x) ^ 3 := by
  simp only [slotZero]
  rw [reindexZero (F := fun b0 b2 b3 b4 t c v => prodZero π b0 b1 b2 b3 b4 t v c)]
  exact peelZero π hq b1

/-- **The `j = 5` slot in the order of the assembly**, root `b₂`. -/
theorem slotFive_tsum [Countable V] [AddCommGroup V] (π : Sym2 V → unitInterval)
    (hq : ∀ x y g : V, π s(x + g, y + g) = π s(x, y)) (b2 : V) :
    (∑' b0, ∑' b1, ∑' b3, ∑' b4, ∑' t, slotFive π b0 b1 b2 b3 b4 t) =
      (secondMoment π 0) ^ 2 * (∑' x, tau π 0 x) ^ 3 := by
  simp only [slotFive]
  rw [reindexFive (F := fun b0 b1 b3 b4 t c w => prodFive π b0 b1 b2 b3 b4 t c w)]
  exact peelFive π hq b2

/-- **The `j = 6` slot in the order of the assembly**, root `t`. -/
theorem slotSix_tsum [Countable V] [AddCommGroup V] (π : Sym2 V → unitInterval)
    (hq : ∀ x y g : V, π s(x + g, y + g) = π s(x, y)) (t : V) :
    (∑' b0, ∑' b1, ∑' b2, ∑' b3, ∑' b4, slotSix π b0 b1 b2 b3 b4 t) =
      (secondMoment π 0) ^ 2 * (∑' x, tau π 0 x) ^ 3 := by
  simp only [slotSix]
  rw [reindexSix (F := fun b0 b1 b2 b3 b4 v w => prodSix π b0 b1 b2 b3 b4 t v w)]
  exact peelSix π hq t

/-! ## The five non-root terminals in an arbitrary order

The labelled patterns of the fifth-moment assembly deliver the five non-root terminals in the
order fixed by `pat k`, so each evaluated slot is recorded here with the five terminal sums read
through an arbitrary permutation `σ` of the five free labels.  The root (`b₁` at `j = 0`, `b₂` at
`j = 5`, `t` at `j = 6`) is not summed. -/

/-- **The `j = 0` slot at an arbitrary order of the five non-root terminals.** -/
theorem slotZero_tsum_of_perm [Countable V] [AddCommGroup V] (π : Sym2 V → unitInterval)
    (hq : ∀ x y g : V, π s(x + g, y + g) = π s(x, y)) (b1 : V) (σ : Equiv.Perm (Fin 5)) :
    (∑' T : Fin 5 → V, slotZero π (T (σ 0)) b1 (T (σ 1)) (T (σ 2)) (T (σ 3)) (T (σ 4))) =
      (secondMoment π 0) ^ 2 * (∑' x, tau π 0 x) ^ 3 := by
  have hbase : (∑' T : Fin 5 → V, slotZero π (T 0) b1 (T 1) (T 2) (T 3) (T 4)) =
      (secondMoment π 0) ^ 2 * (∑' x, tau π 0 x) ^ 3 := by
    rw [PercLib.CriticalLRP.SixPoint.TwoJointEval.tsum_fin5
      (G := fun T : Fin 5 → V => slotZero π (T 0) b1 (T 1) (T 2) (T 3) (T 4))]
    simpa only [Matrix.cons_val] using slotZero_tsum π hq b1
  rw [show (∑' T : Fin 5 → V,
      slotZero π (T (σ 0)) b1 (T (σ 1)) (T (σ 2)) (T (σ 3)) (T (σ 4))) =
      ∑' T : Fin 5 → V, slotZero π (T 0) b1 (T 1) (T 2) (T 3) (T 4) from
    PercLib.CriticalLRP.SixPoint.TwoJointEval.tsum_fin5_perm σ
      (G := fun T : Fin 5 → V => slotZero π (T 0) b1 (T 1) (T 2) (T 3) (T 4))]
  exact hbase

/-- **The `j = 5` slot at an arbitrary order of the five non-root terminals.** -/
theorem slotFive_tsum_of_perm [Countable V] [AddCommGroup V] (π : Sym2 V → unitInterval)
    (hq : ∀ x y g : V, π s(x + g, y + g) = π s(x, y)) (b2 : V) (σ : Equiv.Perm (Fin 5)) :
    (∑' T : Fin 5 → V, slotFive π (T (σ 0)) (T (σ 1)) b2 (T (σ 2)) (T (σ 3)) (T (σ 4))) =
      (secondMoment π 0) ^ 2 * (∑' x, tau π 0 x) ^ 3 := by
  have hbase : (∑' T : Fin 5 → V, slotFive π (T 0) (T 1) b2 (T 2) (T 3) (T 4)) =
      (secondMoment π 0) ^ 2 * (∑' x, tau π 0 x) ^ 3 := by
    rw [PercLib.CriticalLRP.SixPoint.TwoJointEval.tsum_fin5
      (G := fun T : Fin 5 → V => slotFive π (T 0) (T 1) b2 (T 2) (T 3) (T 4))]
    simpa only [Matrix.cons_val] using slotFive_tsum π hq b2
  rw [show (∑' T : Fin 5 → V,
      slotFive π (T (σ 0)) (T (σ 1)) b2 (T (σ 2)) (T (σ 3)) (T (σ 4))) =
      ∑' T : Fin 5 → V, slotFive π (T 0) (T 1) b2 (T 2) (T 3) (T 4) from
    PercLib.CriticalLRP.SixPoint.TwoJointEval.tsum_fin5_perm σ
      (G := fun T : Fin 5 → V => slotFive π (T 0) (T 1) b2 (T 2) (T 3) (T 4))]
  exact hbase

/-- **The `j = 6` slot at an arbitrary order of the five comb terminals.** -/
theorem slotSix_tsum_of_perm [Countable V] [AddCommGroup V] (π : Sym2 V → unitInterval)
    (hq : ∀ x y g : V, π s(x + g, y + g) = π s(x, y)) (t : V) (σ : Equiv.Perm (Fin 5)) :
    (∑' T : Fin 5 → V, slotSix π (T (σ 0)) (T (σ 1)) (T (σ 2)) (T (σ 3)) (T (σ 4)) t) =
      (secondMoment π 0) ^ 2 * (∑' x, tau π 0 x) ^ 3 := by
  have hbase : (∑' T : Fin 5 → V, slotSix π (T 0) (T 1) (T 2) (T 3) (T 4) t) =
      (secondMoment π 0) ^ 2 * (∑' x, tau π 0 x) ^ 3 := by
    rw [PercLib.CriticalLRP.SixPoint.TwoJointEval.tsum_fin5
      (G := fun T : Fin 5 → V => slotSix π (T 0) (T 1) (T 2) (T 3) (T 4) t)]
    simpa only [Matrix.cons_val] using slotSix_tsum π hq t
  rw [show (∑' T : Fin 5 → V,
      slotSix π (T (σ 0)) (T (σ 1)) (T (σ 2)) (T (σ 3)) (T (σ 4)) t) =
      ∑' T : Fin 5 → V, slotSix π (T 0) (T 1) (T 2) (T 3) (T 4) t from
    PercLib.CriticalLRP.SixPoint.TwoJointEval.tsum_fin5_perm σ
      (G := fun T : Fin 5 → V => slotSix π (T 0) (T 1) (T 2) (T 3) (T 4) t)]
  exact hbase

end PercLib.CriticalLRP.SixPoint.SplitEval
