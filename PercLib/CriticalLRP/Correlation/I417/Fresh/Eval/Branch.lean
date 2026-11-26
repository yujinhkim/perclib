/-
Independently rebuilt and integrated from `smwx9itnu/m1`. Production
integration revision `3163cff3d90175d69f2612903830a27bdf5c0ab6`.
The coordinator supplies the fully applied 48-term aggregation and its
moment composition; only the strict build and global axiom audit determine acceptance.
-/
/-
Independently built for swarm `smwx9itnu`, member `m1`, direction Q4-SUMMED-EVALUATION.
No production files are modified; this module is read-only against production.
-/
module

public import PercLib.CriticalLRP.Correlation.I417.Fresh.Eval.Engine

/-!
# The `48` members of the accepted `q = 4` fresh cover, summed

Source: T. Hutchcroft, *Critical long-range percolation I: High effective dimension*,
arXiv:2508.18807v1, Lemma I.4.17 and its proof (supplied paper text pp. 45--46).

Each of the `2 · 4 · 6 = 48` branches `q4Legs k1 k2 k3` of the accepted cover
(`PercLib.CriticalLRP.I417FreshFour.Refined.q4Legs`) is an eight-leg diagram.  Four of its legs form
the **skeleton**, a tree on the five syntactic vertices `{y, w, z1, z2, z3}` containing the pin `y`
as a leaf and the mark `w` on the path from `y`; the remaining four legs are the labelled arms, one
free end each, whose other endpoint is a skeleton vertex.  The theorem `ev_<n>` below evaluates the
member exactly:

* the four arms sum out to `χ⁴` (`tsum_arm_four`), one `χ` per free arm end;
* every skeleton vertex outside the `y`--`w` path is summed out and contributes exactly one `χ`
  (`hχ`), in the peel order recorded in the proof;
* the `ℓ` skeleton legs on the `y`--`w` path compose into `T^ℓ` (`chain_L<ℓ>`).

The result is `χ^(8-ℓ) T^ℓ`: `2q = 8` two-point factors, split as `(8 - ℓ) + ℓ`.  The `ℓ` of each
member, its path order and its peel order were read off the composition of `splitAt` for that
member.  The counts are `ℓ = 4 : 6`, `ℓ = 3 : 12`, `ℓ = 2 : 15`, `ℓ = 1 : 15`, 48 in total.
-/

open MeasureTheory Measure ProbabilityTheory unitInterval
open scoped ENNReal NNReal

set_option linter.unusedSectionVars false
set_option linter.unusedDecidableInType false
set_option linter.style.longLine false
set_option linter.style.show false
set_option linter.unusedSimpArgs false

@[expose] public section

namespace PercLib.CriticalLRP.I417FreshFour.Eval

open PercLib.CriticalLRP
open PercLib.CriticalLRP.I417FreshFour.Refined
open PercLib.CriticalLRP.I417Fresh
open PercLib.CriticalLRP.I417FreshTwo
open PercLib.CriticalLRP.I417Base

variable {V : Type*} [Countable V] [DecidableEq V]

/-- Member `1` of the `q = 4` family: `k1 = (0 : Fin 2)`, `k2 = Sum.inl ((0 : Fin 2))`,
`k3 = Sum.inl (Sum.inl ((0 : Fin 2)))`.  Skeleton path `y – z3 – z2 – z1 – w` (so `ℓ = 4`),
summed-out skeleton vertices `none` in peel order
`none`. -/
theorem ev_0 (π : Sym2 V → unitInterval) (y w : V) (χ : ℝ≥0∞)
    (hχ : ∀ v : V, ∑' z : V, tau π v z = χ) :
    (∑' z1 : V, ∑' z2 : V, ∑' z3 : V, ∑' pa : V × V × V × V,
        ∏ i, tau π
          (q4Legs ((0 : Fin 2)) (Sum.inl ((0 : Fin 2))) (Sum.inl (Sum.inl ((0 : Fin 2)))) z1 z2 z3 y w pa.1 pa.2.1 pa.2.2.1 pa.2.2.2 i).1
          (q4Legs ((0 : Fin 2)) (Sum.inl ((0 : Fin 2))) (Sum.inl (Sum.inl ((0 : Fin 2)))) z1 z2 z3 y w pa.1 pa.2.1 pa.2.2.1 pa.2.2.2 i).2) =
      χ ^ 4 * iterPow (kernel π) 4 w y := by
  have hNF : ∀ z1 z2 z3 (pa : V × V × V × V),
      (∏ i, tau π (q4Legs ((0 : Fin 2)) (Sum.inl ((0 : Fin 2))) (Sum.inl (Sum.inl ((0 : Fin 2)))) z1 z2 z3 y w pa.1 pa.2.1 pa.2.2.1 pa.2.2.2 i).1 (q4Legs ((0 : Fin 2)) (Sum.inl ((0 : Fin 2))) (Sum.inl (Sum.inl ((0 : Fin 2)))) z1 z2 z3 y w pa.1 pa.2.1 pa.2.2.1 pa.2.2.2 i).2) = tau π y z3 * tau π z3 z2 * tau π z2 z1 * tau π z1 w * (tau π w pa.1 * tau π z1 pa.2.1 * tau π z2 pa.2.2.1 * tau π z3 pa.2.2.2) := by
    intro z1 z2 z3 pa
    simp [q4Legs, splitAt, baseLegs, Fintype.prod_sum_type, Fin.prod_univ_two]
    all_goals ring
  simp only [hNF]
  have harm : (∑' z1 : V, ∑' z2 : V, ∑' z3 : V,
        (∑' pa : V × V × V × V, tau π y z3 * tau π z3 z2 * tau π z2 z1 * tau π z1 w * (tau π w pa.1 * tau π z1 pa.2.1 * tau π z2 pa.2.2.1 * tau π z3 pa.2.2.2))) =
      ∑' z1 : V, ∑' z2 : V, ∑' z3 : V, tau π y z3 * tau π z3 z2 * tau π z2 z1 * tau π z1 w * χ ^ 4 := by
    refine tsum_congr fun z1 => tsum_congr fun z2 => tsum_congr fun z3 => ?_
    exact tsum_arm_four_tuple π χ hχ w z1 z2 z3 _
  rw [harm]
  have hpull : (∑' z1 : V, ∑' z2 : V, ∑' z3 : V, tau π y z3 * tau π z3 z2 * tau π z2 z1 * tau π z1 w * χ ^ 4) =
      (∑' z1 : V, ∑' z2 : V, ∑' z3 : V, tau π y z3 * tau π z3 z2 * tau π z2 z1 * tau π z1 w) * χ ^ 4 := by
    simp only [ENNReal.tsum_mul_right]
  rw [hpull]
  have hchain : (∑' z1 : V, ∑' z2 : V, ∑' z3 : V, tau π y z3 * tau π z3 z2 * tau π z2 z1 * tau π z1 w) =
      χ ^ 0 * iterPow (kernel π) 4 y w := by
    refine Eq.trans (perm13 (fun a b c => tau π y c * tau π c b * tau π b a * tau π a w)) ?_
    simp only [ENNReal.tsum_mul_left, ENNReal.tsum_mul_right, hχ, ← iterPow_four_eq π y w]
    ring
  rw [hchain, iterPow_kernel_comm π 4 y w]
  ring

/-- Member `2` of the `q = 4` family: `k1 = (0 : Fin 2)`, `k2 = Sum.inl ((0 : Fin 2))`,
`k3 = Sum.inl (Sum.inl ((1 : Fin 2)))`.  Skeleton path `y – z2 – z1 – w` (so `ℓ = 3`),
summed-out skeleton vertices `z3` in peel order
`z3`. -/
theorem ev_1 (π : Sym2 V → unitInterval) (y w : V) (χ : ℝ≥0∞)
    (hχ : ∀ v : V, ∑' z : V, tau π v z = χ) :
    (∑' z1 : V, ∑' z2 : V, ∑' z3 : V, ∑' pa : V × V × V × V,
        ∏ i, tau π
          (q4Legs ((0 : Fin 2)) (Sum.inl ((0 : Fin 2))) (Sum.inl (Sum.inl ((1 : Fin 2)))) z1 z2 z3 y w pa.1 pa.2.1 pa.2.2.1 pa.2.2.2 i).1
          (q4Legs ((0 : Fin 2)) (Sum.inl ((0 : Fin 2))) (Sum.inl (Sum.inl ((1 : Fin 2)))) z1 z2 z3 y w pa.1 pa.2.1 pa.2.2.1 pa.2.2.2 i).2) =
      χ ^ 5 * iterPow (kernel π) 3 w y := by
  have hNF : ∀ z1 z2 z3 (pa : V × V × V × V),
      (∏ i, tau π (q4Legs ((0 : Fin 2)) (Sum.inl ((0 : Fin 2))) (Sum.inl (Sum.inl ((1 : Fin 2)))) z1 z2 z3 y w pa.1 pa.2.1 pa.2.2.1 pa.2.2.2 i).1 (q4Legs ((0 : Fin 2)) (Sum.inl ((0 : Fin 2))) (Sum.inl (Sum.inl ((1 : Fin 2)))) z1 z2 z3 y w pa.1 pa.2.1 pa.2.2.1 pa.2.2.2 i).2) = tau π y z2 * tau π z2 z1 * tau π z1 w * tau π w z3 * (tau π z3 pa.1 * tau π z1 pa.2.1 * tau π z2 pa.2.2.1 * tau π z3 pa.2.2.2) := by
    intro z1 z2 z3 pa
    simp [q4Legs, splitAt, baseLegs, Fintype.prod_sum_type, Fin.prod_univ_two]
    all_goals ring
  simp only [hNF]
  have harm : (∑' z1 : V, ∑' z2 : V, ∑' z3 : V,
        (∑' pa : V × V × V × V, tau π y z2 * tau π z2 z1 * tau π z1 w * tau π w z3 * (tau π z3 pa.1 * tau π z1 pa.2.1 * tau π z2 pa.2.2.1 * tau π z3 pa.2.2.2))) =
      ∑' z1 : V, ∑' z2 : V, ∑' z3 : V, tau π y z2 * tau π z2 z1 * tau π z1 w * tau π w z3 * χ ^ 4 := by
    refine tsum_congr fun z1 => tsum_congr fun z2 => tsum_congr fun z3 => ?_
    exact tsum_arm_four_tuple π χ hχ z3 z1 z2 z3 _
  rw [harm]
  have hpull : (∑' z1 : V, ∑' z2 : V, ∑' z3 : V, tau π y z2 * tau π z2 z1 * tau π z1 w * tau π w z3 * χ ^ 4) =
      (∑' z1 : V, ∑' z2 : V, ∑' z3 : V, tau π y z2 * tau π z2 z1 * tau π z1 w * tau π w z3) * χ ^ 4 := by
    simp only [ENNReal.tsum_mul_right]
  rw [hpull]
  have hchain : (∑' z1 : V, ∑' z2 : V, ∑' z3 : V, tau π y z2 * tau π z2 z1 * tau π z1 w * tau π w z3) =
      χ ^ 1 * iterPow (kernel π) 3 y w := by
    refine Eq.trans (perm12 (fun a b c => tau π y b * tau π b a * tau π a w * tau π w c)) ?_
    simp only [ENNReal.tsum_mul_left, ENNReal.tsum_mul_right, hχ, ← I417FreshTwo.iterPow_three_eq]
    ring
  rw [hchain, iterPow_kernel_comm π 3 y w]
  ring

/-- Member `3` of the `q = 4` family: `k1 = (0 : Fin 2)`, `k2 = Sum.inl ((0 : Fin 2))`,
`k3 = Sum.inl (Sum.inr false)`.  Skeleton path `y – z2 – z1 – z3 – w` (so `ℓ = 4`),
summed-out skeleton vertices `none` in peel order
`none`. -/
theorem ev_2 (π : Sym2 V → unitInterval) (y w : V) (χ : ℝ≥0∞)
    (hχ : ∀ v : V, ∑' z : V, tau π v z = χ) :
    (∑' z1 : V, ∑' z2 : V, ∑' z3 : V, ∑' pa : V × V × V × V,
        ∏ i, tau π
          (q4Legs ((0 : Fin 2)) (Sum.inl ((0 : Fin 2))) (Sum.inl (Sum.inr false)) z1 z2 z3 y w pa.1 pa.2.1 pa.2.2.1 pa.2.2.2 i).1
          (q4Legs ((0 : Fin 2)) (Sum.inl ((0 : Fin 2))) (Sum.inl (Sum.inr false)) z1 z2 z3 y w pa.1 pa.2.1 pa.2.2.1 pa.2.2.2 i).2) =
      χ ^ 4 * iterPow (kernel π) 4 w y := by
  have hNF : ∀ z1 z2 z3 (pa : V × V × V × V),
      (∏ i, tau π (q4Legs ((0 : Fin 2)) (Sum.inl ((0 : Fin 2))) (Sum.inl (Sum.inr false)) z1 z2 z3 y w pa.1 pa.2.1 pa.2.2.1 pa.2.2.2 i).1 (q4Legs ((0 : Fin 2)) (Sum.inl ((0 : Fin 2))) (Sum.inl (Sum.inr false)) z1 z2 z3 y w pa.1 pa.2.1 pa.2.2.1 pa.2.2.2 i).2) = tau π y z2 * tau π z2 z1 * tau π z1 z3 * tau π z3 w * (tau π w pa.1 * tau π z1 pa.2.1 * tau π z2 pa.2.2.1 * tau π z3 pa.2.2.2) := by
    intro z1 z2 z3 pa
    simp [q4Legs, splitAt, baseLegs, Fintype.prod_sum_type, Fin.prod_univ_two]
    all_goals ring
  simp only [hNF]
  have harm : (∑' z1 : V, ∑' z2 : V, ∑' z3 : V,
        (∑' pa : V × V × V × V, tau π y z2 * tau π z2 z1 * tau π z1 z3 * tau π z3 w * (tau π w pa.1 * tau π z1 pa.2.1 * tau π z2 pa.2.2.1 * tau π z3 pa.2.2.2))) =
      ∑' z1 : V, ∑' z2 : V, ∑' z3 : V, tau π y z2 * tau π z2 z1 * tau π z1 z3 * tau π z3 w * χ ^ 4 := by
    refine tsum_congr fun z1 => tsum_congr fun z2 => tsum_congr fun z3 => ?_
    exact tsum_arm_four_tuple π χ hχ w z1 z2 z3 _
  rw [harm]
  have hpull : (∑' z1 : V, ∑' z2 : V, ∑' z3 : V, tau π y z2 * tau π z2 z1 * tau π z1 z3 * tau π z3 w * χ ^ 4) =
      (∑' z1 : V, ∑' z2 : V, ∑' z3 : V, tau π y z2 * tau π z2 z1 * tau π z1 z3 * tau π z3 w) * χ ^ 4 := by
    simp only [ENNReal.tsum_mul_right]
  rw [hpull]
  have hchain : (∑' z1 : V, ∑' z2 : V, ∑' z3 : V, tau π y z2 * tau π z2 z1 * tau π z1 z3 * tau π z3 w) =
      χ ^ 0 * iterPow (kernel π) 4 y w := by
    refine Eq.trans (perm12 (fun a b c => tau π y b * tau π b a * tau π a c * tau π c w)) ?_
    simp only [ENNReal.tsum_mul_left, ENNReal.tsum_mul_right, hχ, ← iterPow_four_eq π y w]
    ring
  rw [hchain, iterPow_kernel_comm π 4 y w]
  ring

/-- Member `4` of the `q = 4` family: `k1 = (0 : Fin 2)`, `k2 = Sum.inl ((0 : Fin 2))`,
`k3 = Sum.inl (Sum.inr true)`.  Skeleton path `y – z2 – z1 – w` (so `ℓ = 3`),
summed-out skeleton vertices `z3` in peel order
`z3`. -/
theorem ev_3 (π : Sym2 V → unitInterval) (y w : V) (χ : ℝ≥0∞)
    (hχ : ∀ v : V, ∑' z : V, tau π v z = χ) :
    (∑' z1 : V, ∑' z2 : V, ∑' z3 : V, ∑' pa : V × V × V × V,
        ∏ i, tau π
          (q4Legs ((0 : Fin 2)) (Sum.inl ((0 : Fin 2))) (Sum.inl (Sum.inr true)) z1 z2 z3 y w pa.1 pa.2.1 pa.2.2.1 pa.2.2.2 i).1
          (q4Legs ((0 : Fin 2)) (Sum.inl ((0 : Fin 2))) (Sum.inl (Sum.inr true)) z1 z2 z3 y w pa.1 pa.2.1 pa.2.2.1 pa.2.2.2 i).2) =
      χ ^ 5 * iterPow (kernel π) 3 w y := by
  have hNF : ∀ z1 z2 z3 (pa : V × V × V × V),
      (∏ i, tau π (q4Legs ((0 : Fin 2)) (Sum.inl ((0 : Fin 2))) (Sum.inl (Sum.inr true)) z1 z2 z3 y w pa.1 pa.2.1 pa.2.2.1 pa.2.2.2 i).1 (q4Legs ((0 : Fin 2)) (Sum.inl ((0 : Fin 2))) (Sum.inl (Sum.inr true)) z1 z2 z3 y w pa.1 pa.2.1 pa.2.2.1 pa.2.2.2 i).2) = tau π y z2 * tau π z2 z1 * tau π z1 w * tau π z1 z3 * (tau π w pa.1 * tau π z3 pa.2.1 * tau π z2 pa.2.2.1 * tau π z3 pa.2.2.2) := by
    intro z1 z2 z3 pa
    simp [q4Legs, splitAt, baseLegs, Fintype.prod_sum_type, Fin.prod_univ_two]
    all_goals ring
  simp only [hNF]
  have harm : (∑' z1 : V, ∑' z2 : V, ∑' z3 : V,
        (∑' pa : V × V × V × V, tau π y z2 * tau π z2 z1 * tau π z1 w * tau π z1 z3 * (tau π w pa.1 * tau π z3 pa.2.1 * tau π z2 pa.2.2.1 * tau π z3 pa.2.2.2))) =
      ∑' z1 : V, ∑' z2 : V, ∑' z3 : V, tau π y z2 * tau π z2 z1 * tau π z1 w * tau π z1 z3 * χ ^ 4 := by
    refine tsum_congr fun z1 => tsum_congr fun z2 => tsum_congr fun z3 => ?_
    exact tsum_arm_four_tuple π χ hχ w z3 z2 z3 _
  rw [harm]
  have hpull : (∑' z1 : V, ∑' z2 : V, ∑' z3 : V, tau π y z2 * tau π z2 z1 * tau π z1 w * tau π z1 z3 * χ ^ 4) =
      (∑' z1 : V, ∑' z2 : V, ∑' z3 : V, tau π y z2 * tau π z2 z1 * tau π z1 w * tau π z1 z3) * χ ^ 4 := by
    simp only [ENNReal.tsum_mul_right]
  rw [hpull]
  have hchain : (∑' z1 : V, ∑' z2 : V, ∑' z3 : V, tau π y z2 * tau π z2 z1 * tau π z1 w * tau π z1 z3) =
      χ ^ 1 * iterPow (kernel π) 3 y w := by
    refine Eq.trans (perm12 (fun a b c => tau π y b * tau π b a * tau π a w * tau π a c)) ?_
    simp only [ENNReal.tsum_mul_left, ENNReal.tsum_mul_right, hχ, ← I417FreshTwo.iterPow_three_eq]
    ring
  rw [hchain, iterPow_kernel_comm π 3 y w]
  ring

/-- Member `5` of the `q = 4` family: `k1 = (0 : Fin 2)`, `k2 = Sum.inl ((0 : Fin 2))`,
`k3 = Sum.inr false`.  Skeleton path `y – z2 – z3 – z1 – w` (so `ℓ = 4`),
summed-out skeleton vertices `none` in peel order
`none`. -/
theorem ev_4 (π : Sym2 V → unitInterval) (y w : V) (χ : ℝ≥0∞)
    (hχ : ∀ v : V, ∑' z : V, tau π v z = χ) :
    (∑' z1 : V, ∑' z2 : V, ∑' z3 : V, ∑' pa : V × V × V × V,
        ∏ i, tau π
          (q4Legs ((0 : Fin 2)) (Sum.inl ((0 : Fin 2))) (Sum.inr false) z1 z2 z3 y w pa.1 pa.2.1 pa.2.2.1 pa.2.2.2 i).1
          (q4Legs ((0 : Fin 2)) (Sum.inl ((0 : Fin 2))) (Sum.inr false) z1 z2 z3 y w pa.1 pa.2.1 pa.2.2.1 pa.2.2.2 i).2) =
      χ ^ 4 * iterPow (kernel π) 4 w y := by
  have hNF : ∀ z1 z2 z3 (pa : V × V × V × V),
      (∏ i, tau π (q4Legs ((0 : Fin 2)) (Sum.inl ((0 : Fin 2))) (Sum.inr false) z1 z2 z3 y w pa.1 pa.2.1 pa.2.2.1 pa.2.2.2 i).1 (q4Legs ((0 : Fin 2)) (Sum.inl ((0 : Fin 2))) (Sum.inr false) z1 z2 z3 y w pa.1 pa.2.1 pa.2.2.1 pa.2.2.2 i).2) = tau π y z2 * tau π z2 z3 * tau π z3 z1 * tau π z1 w * (tau π w pa.1 * tau π z1 pa.2.1 * tau π z2 pa.2.2.1 * tau π z3 pa.2.2.2) := by
    intro z1 z2 z3 pa
    simp [q4Legs, splitAt, baseLegs, Fintype.prod_sum_type, Fin.prod_univ_two]
    all_goals ring
  simp only [hNF]
  have harm : (∑' z1 : V, ∑' z2 : V, ∑' z3 : V,
        (∑' pa : V × V × V × V, tau π y z2 * tau π z2 z3 * tau π z3 z1 * tau π z1 w * (tau π w pa.1 * tau π z1 pa.2.1 * tau π z2 pa.2.2.1 * tau π z3 pa.2.2.2))) =
      ∑' z1 : V, ∑' z2 : V, ∑' z3 : V, tau π y z2 * tau π z2 z3 * tau π z3 z1 * tau π z1 w * χ ^ 4 := by
    refine tsum_congr fun z1 => tsum_congr fun z2 => tsum_congr fun z3 => ?_
    exact tsum_arm_four_tuple π χ hχ w z1 z2 z3 _
  rw [harm]
  have hpull : (∑' z1 : V, ∑' z2 : V, ∑' z3 : V, tau π y z2 * tau π z2 z3 * tau π z3 z1 * tau π z1 w * χ ^ 4) =
      (∑' z1 : V, ∑' z2 : V, ∑' z3 : V, tau π y z2 * tau π z2 z3 * tau π z3 z1 * tau π z1 w) * χ ^ 4 := by
    simp only [ENNReal.tsum_mul_right]
  rw [hpull]
  have hchain : (∑' z1 : V, ∑' z2 : V, ∑' z3 : V, tau π y z2 * tau π z2 z3 * tau π z3 z1 * tau π z1 w) =
      χ ^ 0 * iterPow (kernel π) 4 y w := by
    refine Eq.trans (perm231 (fun a b c => tau π y b * tau π b c * tau π c a * tau π a w)) ?_
    simp only [ENNReal.tsum_mul_left, ENNReal.tsum_mul_right, hχ, ← iterPow_four_eq π y w]
    ring
  rw [hchain, iterPow_kernel_comm π 4 y w]
  ring

/-- Member `6` of the `q = 4` family: `k1 = (0 : Fin 2)`, `k2 = Sum.inl ((0 : Fin 2))`,
`k3 = Sum.inr true`.  Skeleton path `y – z2 – z1 – w` (so `ℓ = 3`),
summed-out skeleton vertices `z3` in peel order
`z3`. -/
theorem ev_5 (π : Sym2 V → unitInterval) (y w : V) (χ : ℝ≥0∞)
    (hχ : ∀ v : V, ∑' z : V, tau π v z = χ) :
    (∑' z1 : V, ∑' z2 : V, ∑' z3 : V, ∑' pa : V × V × V × V,
        ∏ i, tau π
          (q4Legs ((0 : Fin 2)) (Sum.inl ((0 : Fin 2))) (Sum.inr true) z1 z2 z3 y w pa.1 pa.2.1 pa.2.2.1 pa.2.2.2 i).1
          (q4Legs ((0 : Fin 2)) (Sum.inl ((0 : Fin 2))) (Sum.inr true) z1 z2 z3 y w pa.1 pa.2.1 pa.2.2.1 pa.2.2.2 i).2) =
      χ ^ 5 * iterPow (kernel π) 3 w y := by
  have hNF : ∀ z1 z2 z3 (pa : V × V × V × V),
      (∏ i, tau π (q4Legs ((0 : Fin 2)) (Sum.inl ((0 : Fin 2))) (Sum.inr true) z1 z2 z3 y w pa.1 pa.2.1 pa.2.2.1 pa.2.2.2 i).1 (q4Legs ((0 : Fin 2)) (Sum.inl ((0 : Fin 2))) (Sum.inr true) z1 z2 z3 y w pa.1 pa.2.1 pa.2.2.1 pa.2.2.2 i).2) = tau π y z2 * tau π z2 z1 * tau π z1 w * tau π z2 z3 * (tau π w pa.1 * tau π z1 pa.2.1 * tau π z3 pa.2.2.1 * tau π z3 pa.2.2.2) := by
    intro z1 z2 z3 pa
    simp [q4Legs, splitAt, baseLegs, Fintype.prod_sum_type, Fin.prod_univ_two]
    all_goals ring
  simp only [hNF]
  have harm : (∑' z1 : V, ∑' z2 : V, ∑' z3 : V,
        (∑' pa : V × V × V × V, tau π y z2 * tau π z2 z1 * tau π z1 w * tau π z2 z3 * (tau π w pa.1 * tau π z1 pa.2.1 * tau π z3 pa.2.2.1 * tau π z3 pa.2.2.2))) =
      ∑' z1 : V, ∑' z2 : V, ∑' z3 : V, tau π y z2 * tau π z2 z1 * tau π z1 w * tau π z2 z3 * χ ^ 4 := by
    refine tsum_congr fun z1 => tsum_congr fun z2 => tsum_congr fun z3 => ?_
    exact tsum_arm_four_tuple π χ hχ w z1 z3 z3 _
  rw [harm]
  have hpull : (∑' z1 : V, ∑' z2 : V, ∑' z3 : V, tau π y z2 * tau π z2 z1 * tau π z1 w * tau π z2 z3 * χ ^ 4) =
      (∑' z1 : V, ∑' z2 : V, ∑' z3 : V, tau π y z2 * tau π z2 z1 * tau π z1 w * tau π z2 z3) * χ ^ 4 := by
    simp only [ENNReal.tsum_mul_right]
  rw [hpull]
  have hchain : (∑' z1 : V, ∑' z2 : V, ∑' z3 : V, tau π y z2 * tau π z2 z1 * tau π z1 w * tau π z2 z3) =
      χ ^ 1 * iterPow (kernel π) 3 y w := by
    refine Eq.trans (perm12 (fun a b c => tau π y b * tau π b a * tau π a w * tau π b c)) ?_
    simp only [ENNReal.tsum_mul_left, ENNReal.tsum_mul_right, hχ, ← I417FreshTwo.iterPow_three_eq]
    ring
  rw [hchain, iterPow_kernel_comm π 3 y w]
  ring

/-- Member `7` of the `q = 4` family: `k1 = (0 : Fin 2)`, `k2 = Sum.inl ((1 : Fin 2))`,
`k3 = Sum.inl (Sum.inl ((0 : Fin 2)))`.  Skeleton path `y – z3 – z1 – w` (so `ℓ = 3`),
summed-out skeleton vertices `z2` in peel order
`z2`. -/
theorem ev_6 (π : Sym2 V → unitInterval) (y w : V) (χ : ℝ≥0∞)
    (hχ : ∀ v : V, ∑' z : V, tau π v z = χ) :
    (∑' z1 : V, ∑' z2 : V, ∑' z3 : V, ∑' pa : V × V × V × V,
        ∏ i, tau π
          (q4Legs ((0 : Fin 2)) (Sum.inl ((1 : Fin 2))) (Sum.inl (Sum.inl ((0 : Fin 2)))) z1 z2 z3 y w pa.1 pa.2.1 pa.2.2.1 pa.2.2.2 i).1
          (q4Legs ((0 : Fin 2)) (Sum.inl ((1 : Fin 2))) (Sum.inl (Sum.inl ((0 : Fin 2)))) z1 z2 z3 y w pa.1 pa.2.1 pa.2.2.1 pa.2.2.2 i).2) =
      χ ^ 5 * iterPow (kernel π) 3 w y := by
  have hNF : ∀ z1 z2 z3 (pa : V × V × V × V),
      (∏ i, tau π (q4Legs ((0 : Fin 2)) (Sum.inl ((1 : Fin 2))) (Sum.inl (Sum.inl ((0 : Fin 2)))) z1 z2 z3 y w pa.1 pa.2.1 pa.2.2.1 pa.2.2.2 i).1 (q4Legs ((0 : Fin 2)) (Sum.inl ((1 : Fin 2))) (Sum.inl (Sum.inl ((0 : Fin 2)))) z1 z2 z3 y w pa.1 pa.2.1 pa.2.2.1 pa.2.2.2 i).2) = tau π y z3 * tau π z3 z1 * tau π z1 w * tau π w z2 * (tau π z2 pa.1 * tau π z1 pa.2.1 * tau π z2 pa.2.2.1 * tau π z3 pa.2.2.2) := by
    intro z1 z2 z3 pa
    simp [q4Legs, splitAt, baseLegs, Fintype.prod_sum_type, Fin.prod_univ_two]
    all_goals ring
  simp only [hNF]
  have harm : (∑' z1 : V, ∑' z2 : V, ∑' z3 : V,
        (∑' pa : V × V × V × V, tau π y z3 * tau π z3 z1 * tau π z1 w * tau π w z2 * (tau π z2 pa.1 * tau π z1 pa.2.1 * tau π z2 pa.2.2.1 * tau π z3 pa.2.2.2))) =
      ∑' z1 : V, ∑' z2 : V, ∑' z3 : V, tau π y z3 * tau π z3 z1 * tau π z1 w * tau π w z2 * χ ^ 4 := by
    refine tsum_congr fun z1 => tsum_congr fun z2 => tsum_congr fun z3 => ?_
    exact tsum_arm_four_tuple π χ hχ z2 z1 z2 z3 _
  rw [harm]
  have hpull : (∑' z1 : V, ∑' z2 : V, ∑' z3 : V, tau π y z3 * tau π z3 z1 * tau π z1 w * tau π w z2 * χ ^ 4) =
      (∑' z1 : V, ∑' z2 : V, ∑' z3 : V, tau π y z3 * tau π z3 z1 * tau π z1 w * tau π w z2) * χ ^ 4 := by
    simp only [ENNReal.tsum_mul_right]
  rw [hpull]
  have hchain : (∑' z1 : V, ∑' z2 : V, ∑' z3 : V, tau π y z3 * tau π z3 z1 * tau π z1 w * tau π w z2) =
      χ ^ 1 * iterPow (kernel π) 3 y w := by
    refine Eq.trans (perm312 (fun a b c => tau π y c * tau π c a * tau π a w * tau π w b)) ?_
    simp only [ENNReal.tsum_mul_left, ENNReal.tsum_mul_right, hχ, ← I417FreshTwo.iterPow_three_eq]
    ring
  rw [hchain, iterPow_kernel_comm π 3 y w]
  ring

/-- Member `8` of the `q = 4` family: `k1 = (0 : Fin 2)`, `k2 = Sum.inl ((1 : Fin 2))`,
`k3 = Sum.inl (Sum.inl ((1 : Fin 2)))`.  Skeleton path `y – z1 – w` (so `ℓ = 2`),
summed-out skeleton vertices `z2, z3` in peel order
`z2, z3`. -/
theorem ev_7 (π : Sym2 V → unitInterval) (y w : V) (χ : ℝ≥0∞)
    (hχ : ∀ v : V, ∑' z : V, tau π v z = χ) :
    (∑' z1 : V, ∑' z2 : V, ∑' z3 : V, ∑' pa : V × V × V × V,
        ∏ i, tau π
          (q4Legs ((0 : Fin 2)) (Sum.inl ((1 : Fin 2))) (Sum.inl (Sum.inl ((1 : Fin 2)))) z1 z2 z3 y w pa.1 pa.2.1 pa.2.2.1 pa.2.2.2 i).1
          (q4Legs ((0 : Fin 2)) (Sum.inl ((1 : Fin 2))) (Sum.inl (Sum.inl ((1 : Fin 2)))) z1 z2 z3 y w pa.1 pa.2.1 pa.2.2.1 pa.2.2.2 i).2) =
      χ ^ 6 * iterPow (kernel π) 2 w y := by
  have hNF : ∀ z1 z2 z3 (pa : V × V × V × V),
      (∏ i, tau π (q4Legs ((0 : Fin 2)) (Sum.inl ((1 : Fin 2))) (Sum.inl (Sum.inl ((1 : Fin 2)))) z1 z2 z3 y w pa.1 pa.2.1 pa.2.2.1 pa.2.2.2 i).1 (q4Legs ((0 : Fin 2)) (Sum.inl ((1 : Fin 2))) (Sum.inl (Sum.inl ((1 : Fin 2)))) z1 z2 z3 y w pa.1 pa.2.1 pa.2.2.1 pa.2.2.2 i).2) = tau π y z1 * tau π z1 w * tau π w z3 * tau π z3 z2 * (tau π z2 pa.1 * tau π z1 pa.2.1 * tau π z2 pa.2.2.1 * tau π z3 pa.2.2.2) := by
    intro z1 z2 z3 pa
    simp [q4Legs, splitAt, baseLegs, Fintype.prod_sum_type, Fin.prod_univ_two]
    all_goals ring
  simp only [hNF]
  have harm : (∑' z1 : V, ∑' z2 : V, ∑' z3 : V,
        (∑' pa : V × V × V × V, tau π y z1 * tau π z1 w * tau π w z3 * tau π z3 z2 * (tau π z2 pa.1 * tau π z1 pa.2.1 * tau π z2 pa.2.2.1 * tau π z3 pa.2.2.2))) =
      ∑' z1 : V, ∑' z2 : V, ∑' z3 : V, tau π y z1 * tau π z1 w * tau π w z3 * tau π z3 z2 * χ ^ 4 := by
    refine tsum_congr fun z1 => tsum_congr fun z2 => tsum_congr fun z3 => ?_
    exact tsum_arm_four_tuple π χ hχ z2 z1 z2 z3 _
  rw [harm]
  have hpull : (∑' z1 : V, ∑' z2 : V, ∑' z3 : V, tau π y z1 * tau π z1 w * tau π w z3 * tau π z3 z2 * χ ^ 4) =
      (∑' z1 : V, ∑' z2 : V, ∑' z3 : V, tau π y z1 * tau π z1 w * tau π w z3 * tau π z3 z2) * χ ^ 4 := by
    simp only [ENNReal.tsum_mul_right]
  rw [hpull]
  have hchain : (∑' z1 : V, ∑' z2 : V, ∑' z3 : V, tau π y z1 * tau π z1 w * tau π w z3 * tau π z3 z2) =
      χ ^ 2 * iterPow (kernel π) 2 y w := by
    refine Eq.trans (perm23 (fun a b c => tau π y a * tau π a w * tau π w c * tau π c b)) ?_
    simp only [ENNReal.tsum_mul_left, ENNReal.tsum_mul_right, hχ, ← I417FreshTwo.iterPow_two_eq]
    ring
  rw [hchain, iterPow_kernel_comm π 2 y w]
  ring

/-- Member `9` of the `q = 4` family: `k1 = (0 : Fin 2)`, `k2 = Sum.inl ((1 : Fin 2))`,
`k3 = Sum.inl (Sum.inr false)`.  Skeleton path `y – z1 – z3 – w` (so `ℓ = 3`),
summed-out skeleton vertices `z2` in peel order
`z2`. -/
theorem ev_8 (π : Sym2 V → unitInterval) (y w : V) (χ : ℝ≥0∞)
    (hχ : ∀ v : V, ∑' z : V, tau π v z = χ) :
    (∑' z1 : V, ∑' z2 : V, ∑' z3 : V, ∑' pa : V × V × V × V,
        ∏ i, tau π
          (q4Legs ((0 : Fin 2)) (Sum.inl ((1 : Fin 2))) (Sum.inl (Sum.inr false)) z1 z2 z3 y w pa.1 pa.2.1 pa.2.2.1 pa.2.2.2 i).1
          (q4Legs ((0 : Fin 2)) (Sum.inl ((1 : Fin 2))) (Sum.inl (Sum.inr false)) z1 z2 z3 y w pa.1 pa.2.1 pa.2.2.1 pa.2.2.2 i).2) =
      χ ^ 5 * iterPow (kernel π) 3 w y := by
  have hNF : ∀ z1 z2 z3 (pa : V × V × V × V),
      (∏ i, tau π (q4Legs ((0 : Fin 2)) (Sum.inl ((1 : Fin 2))) (Sum.inl (Sum.inr false)) z1 z2 z3 y w pa.1 pa.2.1 pa.2.2.1 pa.2.2.2 i).1 (q4Legs ((0 : Fin 2)) (Sum.inl ((1 : Fin 2))) (Sum.inl (Sum.inr false)) z1 z2 z3 y w pa.1 pa.2.1 pa.2.2.1 pa.2.2.2 i).2) = tau π y z1 * tau π z1 z3 * tau π z3 w * tau π w z2 * (tau π z2 pa.1 * tau π z1 pa.2.1 * tau π z2 pa.2.2.1 * tau π z3 pa.2.2.2) := by
    intro z1 z2 z3 pa
    simp [q4Legs, splitAt, baseLegs, Fintype.prod_sum_type, Fin.prod_univ_two]
    all_goals ring
  simp only [hNF]
  have harm : (∑' z1 : V, ∑' z2 : V, ∑' z3 : V,
        (∑' pa : V × V × V × V, tau π y z1 * tau π z1 z3 * tau π z3 w * tau π w z2 * (tau π z2 pa.1 * tau π z1 pa.2.1 * tau π z2 pa.2.2.1 * tau π z3 pa.2.2.2))) =
      ∑' z1 : V, ∑' z2 : V, ∑' z3 : V, tau π y z1 * tau π z1 z3 * tau π z3 w * tau π w z2 * χ ^ 4 := by
    refine tsum_congr fun z1 => tsum_congr fun z2 => tsum_congr fun z3 => ?_
    exact tsum_arm_four_tuple π χ hχ z2 z1 z2 z3 _
  rw [harm]
  have hpull : (∑' z1 : V, ∑' z2 : V, ∑' z3 : V, tau π y z1 * tau π z1 z3 * tau π z3 w * tau π w z2 * χ ^ 4) =
      (∑' z1 : V, ∑' z2 : V, ∑' z3 : V, tau π y z1 * tau π z1 z3 * tau π z3 w * tau π w z2) * χ ^ 4 := by
    simp only [ENNReal.tsum_mul_right]
  rw [hpull]
  have hchain : (∑' z1 : V, ∑' z2 : V, ∑' z3 : V, tau π y z1 * tau π z1 z3 * tau π z3 w * tau π w z2) =
      χ ^ 1 * iterPow (kernel π) 3 y w := by
    refine Eq.trans (perm23 (fun a b c => tau π y a * tau π a c * tau π c w * tau π w b)) ?_
    simp only [ENNReal.tsum_mul_left, ENNReal.tsum_mul_right, hχ, ← I417FreshTwo.iterPow_three_eq]
    ring
  rw [hchain, iterPow_kernel_comm π 3 y w]
  ring

/-- Member `10` of the `q = 4` family: `k1 = (0 : Fin 2)`, `k2 = Sum.inl ((1 : Fin 2))`,
`k3 = Sum.inl (Sum.inr true)`.  Skeleton path `y – z1 – w` (so `ℓ = 2`),
summed-out skeleton vertices `z2, z3` in peel order
`z2, z3`. -/
theorem ev_9 (π : Sym2 V → unitInterval) (y w : V) (χ : ℝ≥0∞)
    (hχ : ∀ v : V, ∑' z : V, tau π v z = χ) :
    (∑' z1 : V, ∑' z2 : V, ∑' z3 : V, ∑' pa : V × V × V × V,
        ∏ i, tau π
          (q4Legs ((0 : Fin 2)) (Sum.inl ((1 : Fin 2))) (Sum.inl (Sum.inr true)) z1 z2 z3 y w pa.1 pa.2.1 pa.2.2.1 pa.2.2.2 i).1
          (q4Legs ((0 : Fin 2)) (Sum.inl ((1 : Fin 2))) (Sum.inl (Sum.inr true)) z1 z2 z3 y w pa.1 pa.2.1 pa.2.2.1 pa.2.2.2 i).2) =
      χ ^ 6 * iterPow (kernel π) 2 w y := by
  have hNF : ∀ z1 z2 z3 (pa : V × V × V × V),
      (∏ i, tau π (q4Legs ((0 : Fin 2)) (Sum.inl ((1 : Fin 2))) (Sum.inl (Sum.inr true)) z1 z2 z3 y w pa.1 pa.2.1 pa.2.2.1 pa.2.2.2 i).1 (q4Legs ((0 : Fin 2)) (Sum.inl ((1 : Fin 2))) (Sum.inl (Sum.inr true)) z1 z2 z3 y w pa.1 pa.2.1 pa.2.2.1 pa.2.2.2 i).2) = tau π y z1 * tau π z1 w * tau π z1 z3 * tau π w z2 * (tau π z2 pa.1 * tau π z3 pa.2.1 * tau π z2 pa.2.2.1 * tau π z3 pa.2.2.2) := by
    intro z1 z2 z3 pa
    simp [q4Legs, splitAt, baseLegs, Fintype.prod_sum_type, Fin.prod_univ_two]
    all_goals ring
  simp only [hNF]
  have harm : (∑' z1 : V, ∑' z2 : V, ∑' z3 : V,
        (∑' pa : V × V × V × V, tau π y z1 * tau π z1 w * tau π z1 z3 * tau π w z2 * (tau π z2 pa.1 * tau π z3 pa.2.1 * tau π z2 pa.2.2.1 * tau π z3 pa.2.2.2))) =
      ∑' z1 : V, ∑' z2 : V, ∑' z3 : V, tau π y z1 * tau π z1 w * tau π z1 z3 * tau π w z2 * χ ^ 4 := by
    refine tsum_congr fun z1 => tsum_congr fun z2 => tsum_congr fun z3 => ?_
    exact tsum_arm_four_tuple π χ hχ z2 z3 z2 z3 _
  rw [harm]
  have hpull : (∑' z1 : V, ∑' z2 : V, ∑' z3 : V, tau π y z1 * tau π z1 w * tau π z1 z3 * tau π w z2 * χ ^ 4) =
      (∑' z1 : V, ∑' z2 : V, ∑' z3 : V, tau π y z1 * tau π z1 w * tau π z1 z3 * tau π w z2) * χ ^ 4 := by
    simp only [ENNReal.tsum_mul_right]
  rw [hpull]
  have hchain : (∑' z1 : V, ∑' z2 : V, ∑' z3 : V, tau π y z1 * tau π z1 w * tau π z1 z3 * tau π w z2) =
      χ ^ 2 * iterPow (kernel π) 2 y w := by
    refine Eq.trans (perm23 (fun a b c => tau π y a * tau π a w * tau π a c * tau π w b)) ?_
    simp only [ENNReal.tsum_mul_left, ENNReal.tsum_mul_right, hχ, ← I417FreshTwo.iterPow_two_eq]
    ring
  rw [hchain, iterPow_kernel_comm π 2 y w]
  ring

/-- Member `11` of the `q = 4` family: `k1 = (0 : Fin 2)`, `k2 = Sum.inl ((1 : Fin 2))`,
`k3 = Sum.inr false`.  Skeleton path `y – z1 – w` (so `ℓ = 2`),
summed-out skeleton vertices `z2, z3` in peel order
`z3, z2`. -/
theorem ev_10 (π : Sym2 V → unitInterval) (y w : V) (χ : ℝ≥0∞)
    (hχ : ∀ v : V, ∑' z : V, tau π v z = χ) :
    (∑' z1 : V, ∑' z2 : V, ∑' z3 : V, ∑' pa : V × V × V × V,
        ∏ i, tau π
          (q4Legs ((0 : Fin 2)) (Sum.inl ((1 : Fin 2))) (Sum.inr false) z1 z2 z3 y w pa.1 pa.2.1 pa.2.2.1 pa.2.2.2 i).1
          (q4Legs ((0 : Fin 2)) (Sum.inl ((1 : Fin 2))) (Sum.inr false) z1 z2 z3 y w pa.1 pa.2.1 pa.2.2.1 pa.2.2.2 i).2) =
      χ ^ 6 * iterPow (kernel π) 2 w y := by
  have hNF : ∀ z1 z2 z3 (pa : V × V × V × V),
      (∏ i, tau π (q4Legs ((0 : Fin 2)) (Sum.inl ((1 : Fin 2))) (Sum.inr false) z1 z2 z3 y w pa.1 pa.2.1 pa.2.2.1 pa.2.2.2 i).1 (q4Legs ((0 : Fin 2)) (Sum.inl ((1 : Fin 2))) (Sum.inr false) z1 z2 z3 y w pa.1 pa.2.1 pa.2.2.1 pa.2.2.2 i).2) = tau π y z1 * tau π z1 w * tau π w z2 * tau π z2 z3 * (tau π z3 pa.1 * tau π z1 pa.2.1 * tau π z2 pa.2.2.1 * tau π z3 pa.2.2.2) := by
    intro z1 z2 z3 pa
    simp [q4Legs, splitAt, baseLegs, Fintype.prod_sum_type, Fin.prod_univ_two]
    all_goals ring
  simp only [hNF]
  have harm : (∑' z1 : V, ∑' z2 : V, ∑' z3 : V,
        (∑' pa : V × V × V × V, tau π y z1 * tau π z1 w * tau π w z2 * tau π z2 z3 * (tau π z3 pa.1 * tau π z1 pa.2.1 * tau π z2 pa.2.2.1 * tau π z3 pa.2.2.2))) =
      ∑' z1 : V, ∑' z2 : V, ∑' z3 : V, tau π y z1 * tau π z1 w * tau π w z2 * tau π z2 z3 * χ ^ 4 := by
    refine tsum_congr fun z1 => tsum_congr fun z2 => tsum_congr fun z3 => ?_
    exact tsum_arm_four_tuple π χ hχ z3 z1 z2 z3 _
  rw [harm]
  have hpull : (∑' z1 : V, ∑' z2 : V, ∑' z3 : V, tau π y z1 * tau π z1 w * tau π w z2 * tau π z2 z3 * χ ^ 4) =
      (∑' z1 : V, ∑' z2 : V, ∑' z3 : V, tau π y z1 * tau π z1 w * tau π w z2 * tau π z2 z3) * χ ^ 4 := by
    simp only [ENNReal.tsum_mul_right]
  rw [hpull]
  have hchain : (∑' z1 : V, ∑' z2 : V, ∑' z3 : V, tau π y z1 * tau π z1 w * tau π w z2 * tau π z2 z3) =
      χ ^ 2 * iterPow (kernel π) 2 y w := by
    simp only [ENNReal.tsum_mul_left, ENNReal.tsum_mul_right, hχ, ← I417FreshTwo.iterPow_two_eq]
    ring
  rw [hchain, iterPow_kernel_comm π 2 y w]
  ring

/-- Member `12` of the `q = 4` family: `k1 = (0 : Fin 2)`, `k2 = Sum.inl ((1 : Fin 2))`,
`k3 = Sum.inr true`.  Skeleton path `y – z1 – w` (so `ℓ = 2`),
summed-out skeleton vertices `z2, z3` in peel order
`z3, z2`. -/
theorem ev_11 (π : Sym2 V → unitInterval) (y w : V) (χ : ℝ≥0∞)
    (hχ : ∀ v : V, ∑' z : V, tau π v z = χ) :
    (∑' z1 : V, ∑' z2 : V, ∑' z3 : V, ∑' pa : V × V × V × V,
        ∏ i, tau π
          (q4Legs ((0 : Fin 2)) (Sum.inl ((1 : Fin 2))) (Sum.inr true) z1 z2 z3 y w pa.1 pa.2.1 pa.2.2.1 pa.2.2.2 i).1
          (q4Legs ((0 : Fin 2)) (Sum.inl ((1 : Fin 2))) (Sum.inr true) z1 z2 z3 y w pa.1 pa.2.1 pa.2.2.1 pa.2.2.2 i).2) =
      χ ^ 6 * iterPow (kernel π) 2 w y := by
  have hNF : ∀ z1 z2 z3 (pa : V × V × V × V),
      (∏ i, tau π (q4Legs ((0 : Fin 2)) (Sum.inl ((1 : Fin 2))) (Sum.inr true) z1 z2 z3 y w pa.1 pa.2.1 pa.2.2.1 pa.2.2.2 i).1 (q4Legs ((0 : Fin 2)) (Sum.inl ((1 : Fin 2))) (Sum.inr true) z1 z2 z3 y w pa.1 pa.2.1 pa.2.2.1 pa.2.2.2 i).2) = tau π y z1 * tau π z1 w * tau π w z2 * tau π z2 z3 * (tau π z2 pa.1 * tau π z1 pa.2.1 * tau π z3 pa.2.2.1 * tau π z3 pa.2.2.2) := by
    intro z1 z2 z3 pa
    simp [q4Legs, splitAt, baseLegs, Fintype.prod_sum_type, Fin.prod_univ_two]
    all_goals ring
  simp only [hNF]
  have harm : (∑' z1 : V, ∑' z2 : V, ∑' z3 : V,
        (∑' pa : V × V × V × V, tau π y z1 * tau π z1 w * tau π w z2 * tau π z2 z3 * (tau π z2 pa.1 * tau π z1 pa.2.1 * tau π z3 pa.2.2.1 * tau π z3 pa.2.2.2))) =
      ∑' z1 : V, ∑' z2 : V, ∑' z3 : V, tau π y z1 * tau π z1 w * tau π w z2 * tau π z2 z3 * χ ^ 4 := by
    refine tsum_congr fun z1 => tsum_congr fun z2 => tsum_congr fun z3 => ?_
    exact tsum_arm_four_tuple π χ hχ z2 z1 z3 z3 _
  rw [harm]
  have hpull : (∑' z1 : V, ∑' z2 : V, ∑' z3 : V, tau π y z1 * tau π z1 w * tau π w z2 * tau π z2 z3 * χ ^ 4) =
      (∑' z1 : V, ∑' z2 : V, ∑' z3 : V, tau π y z1 * tau π z1 w * tau π w z2 * tau π z2 z3) * χ ^ 4 := by
    simp only [ENNReal.tsum_mul_right]
  rw [hpull]
  have hchain : (∑' z1 : V, ∑' z2 : V, ∑' z3 : V, tau π y z1 * tau π z1 w * tau π w z2 * tau π z2 z3) =
      χ ^ 2 * iterPow (kernel π) 2 y w := by
    simp only [ENNReal.tsum_mul_left, ENNReal.tsum_mul_right, hχ, ← I417FreshTwo.iterPow_two_eq]
    ring
  rw [hchain, iterPow_kernel_comm π 2 y w]
  ring

/-- Member `13` of the `q = 4` family: `k1 = (0 : Fin 2)`, `k2 = Sum.inr false`,
`k3 = Sum.inl (Sum.inl ((0 : Fin 2)))`.  Skeleton path `y – z3 – z1 – z2 – w` (so `ℓ = 4`),
summed-out skeleton vertices `none` in peel order
`none`. -/
theorem ev_12 (π : Sym2 V → unitInterval) (y w : V) (χ : ℝ≥0∞)
    (hχ : ∀ v : V, ∑' z : V, tau π v z = χ) :
    (∑' z1 : V, ∑' z2 : V, ∑' z3 : V, ∑' pa : V × V × V × V,
        ∏ i, tau π
          (q4Legs ((0 : Fin 2)) (Sum.inr false) (Sum.inl (Sum.inl ((0 : Fin 2)))) z1 z2 z3 y w pa.1 pa.2.1 pa.2.2.1 pa.2.2.2 i).1
          (q4Legs ((0 : Fin 2)) (Sum.inr false) (Sum.inl (Sum.inl ((0 : Fin 2)))) z1 z2 z3 y w pa.1 pa.2.1 pa.2.2.1 pa.2.2.2 i).2) =
      χ ^ 4 * iterPow (kernel π) 4 w y := by
  have hNF : ∀ z1 z2 z3 (pa : V × V × V × V),
      (∏ i, tau π (q4Legs ((0 : Fin 2)) (Sum.inr false) (Sum.inl (Sum.inl ((0 : Fin 2)))) z1 z2 z3 y w pa.1 pa.2.1 pa.2.2.1 pa.2.2.2 i).1 (q4Legs ((0 : Fin 2)) (Sum.inr false) (Sum.inl (Sum.inl ((0 : Fin 2)))) z1 z2 z3 y w pa.1 pa.2.1 pa.2.2.1 pa.2.2.2 i).2) = tau π y z3 * tau π z3 z1 * tau π z1 z2 * tau π z2 w * (tau π w pa.1 * tau π z1 pa.2.1 * tau π z2 pa.2.2.1 * tau π z3 pa.2.2.2) := by
    intro z1 z2 z3 pa
    simp [q4Legs, splitAt, baseLegs, Fintype.prod_sum_type, Fin.prod_univ_two]
    all_goals ring
  simp only [hNF]
  have harm : (∑' z1 : V, ∑' z2 : V, ∑' z3 : V,
        (∑' pa : V × V × V × V, tau π y z3 * tau π z3 z1 * tau π z1 z2 * tau π z2 w * (tau π w pa.1 * tau π z1 pa.2.1 * tau π z2 pa.2.2.1 * tau π z3 pa.2.2.2))) =
      ∑' z1 : V, ∑' z2 : V, ∑' z3 : V, tau π y z3 * tau π z3 z1 * tau π z1 z2 * tau π z2 w * χ ^ 4 := by
    refine tsum_congr fun z1 => tsum_congr fun z2 => tsum_congr fun z3 => ?_
    exact tsum_arm_four_tuple π χ hχ w z1 z2 z3 _
  rw [harm]
  have hpull : (∑' z1 : V, ∑' z2 : V, ∑' z3 : V, tau π y z3 * tau π z3 z1 * tau π z1 z2 * tau π z2 w * χ ^ 4) =
      (∑' z1 : V, ∑' z2 : V, ∑' z3 : V, tau π y z3 * tau π z3 z1 * tau π z1 z2 * tau π z2 w) * χ ^ 4 := by
    simp only [ENNReal.tsum_mul_right]
  rw [hpull]
  have hchain : (∑' z1 : V, ∑' z2 : V, ∑' z3 : V, tau π y z3 * tau π z3 z1 * tau π z1 z2 * tau π z2 w) =
      χ ^ 0 * iterPow (kernel π) 4 y w := by
    refine Eq.trans (perm312 (fun a b c => tau π y c * tau π c a * tau π a b * tau π b w)) ?_
    simp only [ENNReal.tsum_mul_left, ENNReal.tsum_mul_right, hχ, ← iterPow_four_eq π y w]
    ring
  rw [hchain, iterPow_kernel_comm π 4 y w]
  ring

/-- Member `14` of the `q = 4` family: `k1 = (0 : Fin 2)`, `k2 = Sum.inr false`,
`k3 = Sum.inl (Sum.inl ((1 : Fin 2)))`.  Skeleton path `y – z1 – z2 – w` (so `ℓ = 3`),
summed-out skeleton vertices `z3` in peel order
`z3`. -/
theorem ev_13 (π : Sym2 V → unitInterval) (y w : V) (χ : ℝ≥0∞)
    (hχ : ∀ v : V, ∑' z : V, tau π v z = χ) :
    (∑' z1 : V, ∑' z2 : V, ∑' z3 : V, ∑' pa : V × V × V × V,
        ∏ i, tau π
          (q4Legs ((0 : Fin 2)) (Sum.inr false) (Sum.inl (Sum.inl ((1 : Fin 2)))) z1 z2 z3 y w pa.1 pa.2.1 pa.2.2.1 pa.2.2.2 i).1
          (q4Legs ((0 : Fin 2)) (Sum.inr false) (Sum.inl (Sum.inl ((1 : Fin 2)))) z1 z2 z3 y w pa.1 pa.2.1 pa.2.2.1 pa.2.2.2 i).2) =
      χ ^ 5 * iterPow (kernel π) 3 w y := by
  have hNF : ∀ z1 z2 z3 (pa : V × V × V × V),
      (∏ i, tau π (q4Legs ((0 : Fin 2)) (Sum.inr false) (Sum.inl (Sum.inl ((1 : Fin 2)))) z1 z2 z3 y w pa.1 pa.2.1 pa.2.2.1 pa.2.2.2 i).1 (q4Legs ((0 : Fin 2)) (Sum.inr false) (Sum.inl (Sum.inl ((1 : Fin 2)))) z1 z2 z3 y w pa.1 pa.2.1 pa.2.2.1 pa.2.2.2 i).2) = tau π y z1 * tau π z1 z2 * tau π z2 w * tau π w z3 * (tau π z3 pa.1 * tau π z1 pa.2.1 * tau π z2 pa.2.2.1 * tau π z3 pa.2.2.2) := by
    intro z1 z2 z3 pa
    simp [q4Legs, splitAt, baseLegs, Fintype.prod_sum_type, Fin.prod_univ_two]
    all_goals ring
  simp only [hNF]
  have harm : (∑' z1 : V, ∑' z2 : V, ∑' z3 : V,
        (∑' pa : V × V × V × V, tau π y z1 * tau π z1 z2 * tau π z2 w * tau π w z3 * (tau π z3 pa.1 * tau π z1 pa.2.1 * tau π z2 pa.2.2.1 * tau π z3 pa.2.2.2))) =
      ∑' z1 : V, ∑' z2 : V, ∑' z3 : V, tau π y z1 * tau π z1 z2 * tau π z2 w * tau π w z3 * χ ^ 4 := by
    refine tsum_congr fun z1 => tsum_congr fun z2 => tsum_congr fun z3 => ?_
    exact tsum_arm_four_tuple π χ hχ z3 z1 z2 z3 _
  rw [harm]
  have hpull : (∑' z1 : V, ∑' z2 : V, ∑' z3 : V, tau π y z1 * tau π z1 z2 * tau π z2 w * tau π w z3 * χ ^ 4) =
      (∑' z1 : V, ∑' z2 : V, ∑' z3 : V, tau π y z1 * tau π z1 z2 * tau π z2 w * tau π w z3) * χ ^ 4 := by
    simp only [ENNReal.tsum_mul_right]
  rw [hpull]
  have hchain : (∑' z1 : V, ∑' z2 : V, ∑' z3 : V, tau π y z1 * tau π z1 z2 * tau π z2 w * tau π w z3) =
      χ ^ 1 * iterPow (kernel π) 3 y w := by
    simp only [ENNReal.tsum_mul_left, ENNReal.tsum_mul_right, hχ, ← I417FreshTwo.iterPow_three_eq]
    ring
  rw [hchain, iterPow_kernel_comm π 3 y w]
  ring

/-- Member `15` of the `q = 4` family: `k1 = (0 : Fin 2)`, `k2 = Sum.inr false`,
`k3 = Sum.inl (Sum.inr false)`.  Skeleton path `y – z1 – z3 – z2 – w` (so `ℓ = 4`),
summed-out skeleton vertices `none` in peel order
`none`. -/
theorem ev_14 (π : Sym2 V → unitInterval) (y w : V) (χ : ℝ≥0∞)
    (hχ : ∀ v : V, ∑' z : V, tau π v z = χ) :
    (∑' z1 : V, ∑' z2 : V, ∑' z3 : V, ∑' pa : V × V × V × V,
        ∏ i, tau π
          (q4Legs ((0 : Fin 2)) (Sum.inr false) (Sum.inl (Sum.inr false)) z1 z2 z3 y w pa.1 pa.2.1 pa.2.2.1 pa.2.2.2 i).1
          (q4Legs ((0 : Fin 2)) (Sum.inr false) (Sum.inl (Sum.inr false)) z1 z2 z3 y w pa.1 pa.2.1 pa.2.2.1 pa.2.2.2 i).2) =
      χ ^ 4 * iterPow (kernel π) 4 w y := by
  have hNF : ∀ z1 z2 z3 (pa : V × V × V × V),
      (∏ i, tau π (q4Legs ((0 : Fin 2)) (Sum.inr false) (Sum.inl (Sum.inr false)) z1 z2 z3 y w pa.1 pa.2.1 pa.2.2.1 pa.2.2.2 i).1 (q4Legs ((0 : Fin 2)) (Sum.inr false) (Sum.inl (Sum.inr false)) z1 z2 z3 y w pa.1 pa.2.1 pa.2.2.1 pa.2.2.2 i).2) = tau π y z1 * tau π z1 z3 * tau π z3 z2 * tau π z2 w * (tau π w pa.1 * tau π z1 pa.2.1 * tau π z2 pa.2.2.1 * tau π z3 pa.2.2.2) := by
    intro z1 z2 z3 pa
    simp [q4Legs, splitAt, baseLegs, Fintype.prod_sum_type, Fin.prod_univ_two]
    all_goals ring
  simp only [hNF]
  have harm : (∑' z1 : V, ∑' z2 : V, ∑' z3 : V,
        (∑' pa : V × V × V × V, tau π y z1 * tau π z1 z3 * tau π z3 z2 * tau π z2 w * (tau π w pa.1 * tau π z1 pa.2.1 * tau π z2 pa.2.2.1 * tau π z3 pa.2.2.2))) =
      ∑' z1 : V, ∑' z2 : V, ∑' z3 : V, tau π y z1 * tau π z1 z3 * tau π z3 z2 * tau π z2 w * χ ^ 4 := by
    refine tsum_congr fun z1 => tsum_congr fun z2 => tsum_congr fun z3 => ?_
    exact tsum_arm_four_tuple π χ hχ w z1 z2 z3 _
  rw [harm]
  have hpull : (∑' z1 : V, ∑' z2 : V, ∑' z3 : V, tau π y z1 * tau π z1 z3 * tau π z3 z2 * tau π z2 w * χ ^ 4) =
      (∑' z1 : V, ∑' z2 : V, ∑' z3 : V, tau π y z1 * tau π z1 z3 * tau π z3 z2 * tau π z2 w) * χ ^ 4 := by
    simp only [ENNReal.tsum_mul_right]
  rw [hpull]
  have hchain : (∑' z1 : V, ∑' z2 : V, ∑' z3 : V, tau π y z1 * tau π z1 z3 * tau π z3 z2 * tau π z2 w) =
      χ ^ 0 * iterPow (kernel π) 4 y w := by
    refine Eq.trans (perm23 (fun a b c => tau π y a * tau π a c * tau π c b * tau π b w)) ?_
    simp only [ENNReal.tsum_mul_left, ENNReal.tsum_mul_right, hχ, ← iterPow_four_eq π y w]
    ring
  rw [hchain, iterPow_kernel_comm π 4 y w]
  ring

/-- Member `16` of the `q = 4` family: `k1 = (0 : Fin 2)`, `k2 = Sum.inr false`,
`k3 = Sum.inl (Sum.inr true)`.  Skeleton path `y – z1 – z2 – w` (so `ℓ = 3`),
summed-out skeleton vertices `z3` in peel order
`z3`. -/
theorem ev_15 (π : Sym2 V → unitInterval) (y w : V) (χ : ℝ≥0∞)
    (hχ : ∀ v : V, ∑' z : V, tau π v z = χ) :
    (∑' z1 : V, ∑' z2 : V, ∑' z3 : V, ∑' pa : V × V × V × V,
        ∏ i, tau π
          (q4Legs ((0 : Fin 2)) (Sum.inr false) (Sum.inl (Sum.inr true)) z1 z2 z3 y w pa.1 pa.2.1 pa.2.2.1 pa.2.2.2 i).1
          (q4Legs ((0 : Fin 2)) (Sum.inr false) (Sum.inl (Sum.inr true)) z1 z2 z3 y w pa.1 pa.2.1 pa.2.2.1 pa.2.2.2 i).2) =
      χ ^ 5 * iterPow (kernel π) 3 w y := by
  have hNF : ∀ z1 z2 z3 (pa : V × V × V × V),
      (∏ i, tau π (q4Legs ((0 : Fin 2)) (Sum.inr false) (Sum.inl (Sum.inr true)) z1 z2 z3 y w pa.1 pa.2.1 pa.2.2.1 pa.2.2.2 i).1 (q4Legs ((0 : Fin 2)) (Sum.inr false) (Sum.inl (Sum.inr true)) z1 z2 z3 y w pa.1 pa.2.1 pa.2.2.1 pa.2.2.2 i).2) = tau π y z1 * tau π z1 z2 * tau π z2 w * tau π z1 z3 * (tau π w pa.1 * tau π z3 pa.2.1 * tau π z2 pa.2.2.1 * tau π z3 pa.2.2.2) := by
    intro z1 z2 z3 pa
    simp [q4Legs, splitAt, baseLegs, Fintype.prod_sum_type, Fin.prod_univ_two]
    all_goals ring
  simp only [hNF]
  have harm : (∑' z1 : V, ∑' z2 : V, ∑' z3 : V,
        (∑' pa : V × V × V × V, tau π y z1 * tau π z1 z2 * tau π z2 w * tau π z1 z3 * (tau π w pa.1 * tau π z3 pa.2.1 * tau π z2 pa.2.2.1 * tau π z3 pa.2.2.2))) =
      ∑' z1 : V, ∑' z2 : V, ∑' z3 : V, tau π y z1 * tau π z1 z2 * tau π z2 w * tau π z1 z3 * χ ^ 4 := by
    refine tsum_congr fun z1 => tsum_congr fun z2 => tsum_congr fun z3 => ?_
    exact tsum_arm_four_tuple π χ hχ w z3 z2 z3 _
  rw [harm]
  have hpull : (∑' z1 : V, ∑' z2 : V, ∑' z3 : V, tau π y z1 * tau π z1 z2 * tau π z2 w * tau π z1 z3 * χ ^ 4) =
      (∑' z1 : V, ∑' z2 : V, ∑' z3 : V, tau π y z1 * tau π z1 z2 * tau π z2 w * tau π z1 z3) * χ ^ 4 := by
    simp only [ENNReal.tsum_mul_right]
  rw [hpull]
  have hchain : (∑' z1 : V, ∑' z2 : V, ∑' z3 : V, tau π y z1 * tau π z1 z2 * tau π z2 w * tau π z1 z3) =
      χ ^ 1 * iterPow (kernel π) 3 y w := by
    simp only [ENNReal.tsum_mul_left, ENNReal.tsum_mul_right, hχ, ← I417FreshTwo.iterPow_three_eq]
    ring
  rw [hchain, iterPow_kernel_comm π 3 y w]
  ring

/-- Member `17` of the `q = 4` family: `k1 = (0 : Fin 2)`, `k2 = Sum.inr false`,
`k3 = Sum.inr false`.  Skeleton path `y – z1 – z2 – z3 – w` (so `ℓ = 4`),
summed-out skeleton vertices `none` in peel order
`none`. -/
theorem ev_16 (π : Sym2 V → unitInterval) (y w : V) (χ : ℝ≥0∞)
    (hχ : ∀ v : V, ∑' z : V, tau π v z = χ) :
    (∑' z1 : V, ∑' z2 : V, ∑' z3 : V, ∑' pa : V × V × V × V,
        ∏ i, tau π
          (q4Legs ((0 : Fin 2)) (Sum.inr false) (Sum.inr false) z1 z2 z3 y w pa.1 pa.2.1 pa.2.2.1 pa.2.2.2 i).1
          (q4Legs ((0 : Fin 2)) (Sum.inr false) (Sum.inr false) z1 z2 z3 y w pa.1 pa.2.1 pa.2.2.1 pa.2.2.2 i).2) =
      χ ^ 4 * iterPow (kernel π) 4 w y := by
  have hNF : ∀ z1 z2 z3 (pa : V × V × V × V),
      (∏ i, tau π (q4Legs ((0 : Fin 2)) (Sum.inr false) (Sum.inr false) z1 z2 z3 y w pa.1 pa.2.1 pa.2.2.1 pa.2.2.2 i).1 (q4Legs ((0 : Fin 2)) (Sum.inr false) (Sum.inr false) z1 z2 z3 y w pa.1 pa.2.1 pa.2.2.1 pa.2.2.2 i).2) = tau π y z1 * tau π z1 z2 * tau π z2 z3 * tau π z3 w * (tau π w pa.1 * tau π z1 pa.2.1 * tau π z2 pa.2.2.1 * tau π z3 pa.2.2.2) := by
    intro z1 z2 z3 pa
    simp [q4Legs, splitAt, baseLegs, Fintype.prod_sum_type, Fin.prod_univ_two]
    all_goals ring
  simp only [hNF]
  have harm : (∑' z1 : V, ∑' z2 : V, ∑' z3 : V,
        (∑' pa : V × V × V × V, tau π y z1 * tau π z1 z2 * tau π z2 z3 * tau π z3 w * (tau π w pa.1 * tau π z1 pa.2.1 * tau π z2 pa.2.2.1 * tau π z3 pa.2.2.2))) =
      ∑' z1 : V, ∑' z2 : V, ∑' z3 : V, tau π y z1 * tau π z1 z2 * tau π z2 z3 * tau π z3 w * χ ^ 4 := by
    refine tsum_congr fun z1 => tsum_congr fun z2 => tsum_congr fun z3 => ?_
    exact tsum_arm_four_tuple π χ hχ w z1 z2 z3 _
  rw [harm]
  have hpull : (∑' z1 : V, ∑' z2 : V, ∑' z3 : V, tau π y z1 * tau π z1 z2 * tau π z2 z3 * tau π z3 w * χ ^ 4) =
      (∑' z1 : V, ∑' z2 : V, ∑' z3 : V, tau π y z1 * tau π z1 z2 * tau π z2 z3 * tau π z3 w) * χ ^ 4 := by
    simp only [ENNReal.tsum_mul_right]
  rw [hpull]
  have hchain : (∑' z1 : V, ∑' z2 : V, ∑' z3 : V, tau π y z1 * tau π z1 z2 * tau π z2 z3 * tau π z3 w) =
      χ ^ 0 * iterPow (kernel π) 4 y w := by
    simp only [ENNReal.tsum_mul_left, ENNReal.tsum_mul_right, hχ, ← iterPow_four_eq π y w]
    ring
  rw [hchain, iterPow_kernel_comm π 4 y w]
  ring

/-- Member `18` of the `q = 4` family: `k1 = (0 : Fin 2)`, `k2 = Sum.inr false`,
`k3 = Sum.inr true`.  Skeleton path `y – z1 – z2 – w` (so `ℓ = 3`),
summed-out skeleton vertices `z3` in peel order
`z3`. -/
theorem ev_17 (π : Sym2 V → unitInterval) (y w : V) (χ : ℝ≥0∞)
    (hχ : ∀ v : V, ∑' z : V, tau π v z = χ) :
    (∑' z1 : V, ∑' z2 : V, ∑' z3 : V, ∑' pa : V × V × V × V,
        ∏ i, tau π
          (q4Legs ((0 : Fin 2)) (Sum.inr false) (Sum.inr true) z1 z2 z3 y w pa.1 pa.2.1 pa.2.2.1 pa.2.2.2 i).1
          (q4Legs ((0 : Fin 2)) (Sum.inr false) (Sum.inr true) z1 z2 z3 y w pa.1 pa.2.1 pa.2.2.1 pa.2.2.2 i).2) =
      χ ^ 5 * iterPow (kernel π) 3 w y := by
  have hNF : ∀ z1 z2 z3 (pa : V × V × V × V),
      (∏ i, tau π (q4Legs ((0 : Fin 2)) (Sum.inr false) (Sum.inr true) z1 z2 z3 y w pa.1 pa.2.1 pa.2.2.1 pa.2.2.2 i).1 (q4Legs ((0 : Fin 2)) (Sum.inr false) (Sum.inr true) z1 z2 z3 y w pa.1 pa.2.1 pa.2.2.1 pa.2.2.2 i).2) = tau π y z1 * tau π z1 z2 * tau π z2 w * tau π z2 z3 * (tau π w pa.1 * tau π z1 pa.2.1 * tau π z3 pa.2.2.1 * tau π z3 pa.2.2.2) := by
    intro z1 z2 z3 pa
    simp [q4Legs, splitAt, baseLegs, Fintype.prod_sum_type, Fin.prod_univ_two]
    all_goals ring
  simp only [hNF]
  have harm : (∑' z1 : V, ∑' z2 : V, ∑' z3 : V,
        (∑' pa : V × V × V × V, tau π y z1 * tau π z1 z2 * tau π z2 w * tau π z2 z3 * (tau π w pa.1 * tau π z1 pa.2.1 * tau π z3 pa.2.2.1 * tau π z3 pa.2.2.2))) =
      ∑' z1 : V, ∑' z2 : V, ∑' z3 : V, tau π y z1 * tau π z1 z2 * tau π z2 w * tau π z2 z3 * χ ^ 4 := by
    refine tsum_congr fun z1 => tsum_congr fun z2 => tsum_congr fun z3 => ?_
    exact tsum_arm_four_tuple π χ hχ w z1 z3 z3 _
  rw [harm]
  have hpull : (∑' z1 : V, ∑' z2 : V, ∑' z3 : V, tau π y z1 * tau π z1 z2 * tau π z2 w * tau π z2 z3 * χ ^ 4) =
      (∑' z1 : V, ∑' z2 : V, ∑' z3 : V, tau π y z1 * tau π z1 z2 * tau π z2 w * tau π z2 z3) * χ ^ 4 := by
    simp only [ENNReal.tsum_mul_right]
  rw [hpull]
  have hchain : (∑' z1 : V, ∑' z2 : V, ∑' z3 : V, tau π y z1 * tau π z1 z2 * tau π z2 w * tau π z2 z3) =
      χ ^ 1 * iterPow (kernel π) 3 y w := by
    simp only [ENNReal.tsum_mul_left, ENNReal.tsum_mul_right, hχ, ← I417FreshTwo.iterPow_three_eq]
    ring
  rw [hchain, iterPow_kernel_comm π 3 y w]
  ring

/-- Member `19` of the `q = 4` family: `k1 = (0 : Fin 2)`, `k2 = Sum.inr true`,
`k3 = Sum.inl (Sum.inl ((0 : Fin 2)))`.  Skeleton path `y – z3 – z1 – w` (so `ℓ = 3`),
summed-out skeleton vertices `z2` in peel order
`z2`. -/
theorem ev_18 (π : Sym2 V → unitInterval) (y w : V) (χ : ℝ≥0∞)
    (hχ : ∀ v : V, ∑' z : V, tau π v z = χ) :
    (∑' z1 : V, ∑' z2 : V, ∑' z3 : V, ∑' pa : V × V × V × V,
        ∏ i, tau π
          (q4Legs ((0 : Fin 2)) (Sum.inr true) (Sum.inl (Sum.inl ((0 : Fin 2)))) z1 z2 z3 y w pa.1 pa.2.1 pa.2.2.1 pa.2.2.2 i).1
          (q4Legs ((0 : Fin 2)) (Sum.inr true) (Sum.inl (Sum.inl ((0 : Fin 2)))) z1 z2 z3 y w pa.1 pa.2.1 pa.2.2.1 pa.2.2.2 i).2) =
      χ ^ 5 * iterPow (kernel π) 3 w y := by
  have hNF : ∀ z1 z2 z3 (pa : V × V × V × V),
      (∏ i, tau π (q4Legs ((0 : Fin 2)) (Sum.inr true) (Sum.inl (Sum.inl ((0 : Fin 2)))) z1 z2 z3 y w pa.1 pa.2.1 pa.2.2.1 pa.2.2.2 i).1 (q4Legs ((0 : Fin 2)) (Sum.inr true) (Sum.inl (Sum.inl ((0 : Fin 2)))) z1 z2 z3 y w pa.1 pa.2.1 pa.2.2.1 pa.2.2.2 i).2) = tau π y z3 * tau π z3 z1 * tau π z1 w * tau π z1 z2 * (tau π w pa.1 * tau π z2 pa.2.1 * tau π z2 pa.2.2.1 * tau π z3 pa.2.2.2) := by
    intro z1 z2 z3 pa
    simp [q4Legs, splitAt, baseLegs, Fintype.prod_sum_type, Fin.prod_univ_two]
    all_goals ring
  simp only [hNF]
  have harm : (∑' z1 : V, ∑' z2 : V, ∑' z3 : V,
        (∑' pa : V × V × V × V, tau π y z3 * tau π z3 z1 * tau π z1 w * tau π z1 z2 * (tau π w pa.1 * tau π z2 pa.2.1 * tau π z2 pa.2.2.1 * tau π z3 pa.2.2.2))) =
      ∑' z1 : V, ∑' z2 : V, ∑' z3 : V, tau π y z3 * tau π z3 z1 * tau π z1 w * tau π z1 z2 * χ ^ 4 := by
    refine tsum_congr fun z1 => tsum_congr fun z2 => tsum_congr fun z3 => ?_
    exact tsum_arm_four_tuple π χ hχ w z2 z2 z3 _
  rw [harm]
  have hpull : (∑' z1 : V, ∑' z2 : V, ∑' z3 : V, tau π y z3 * tau π z3 z1 * tau π z1 w * tau π z1 z2 * χ ^ 4) =
      (∑' z1 : V, ∑' z2 : V, ∑' z3 : V, tau π y z3 * tau π z3 z1 * tau π z1 w * tau π z1 z2) * χ ^ 4 := by
    simp only [ENNReal.tsum_mul_right]
  rw [hpull]
  have hchain : (∑' z1 : V, ∑' z2 : V, ∑' z3 : V, tau π y z3 * tau π z3 z1 * tau π z1 w * tau π z1 z2) =
      χ ^ 1 * iterPow (kernel π) 3 y w := by
    refine Eq.trans (perm312 (fun a b c => tau π y c * tau π c a * tau π a w * tau π a b)) ?_
    simp only [ENNReal.tsum_mul_left, ENNReal.tsum_mul_right, hχ, ← I417FreshTwo.iterPow_three_eq]
    ring
  rw [hchain, iterPow_kernel_comm π 3 y w]
  ring

/-- Member `20` of the `q = 4` family: `k1 = (0 : Fin 2)`, `k2 = Sum.inr true`,
`k3 = Sum.inl (Sum.inl ((1 : Fin 2)))`.  Skeleton path `y – z1 – w` (so `ℓ = 2`),
summed-out skeleton vertices `z2, z3` in peel order
`z2, z3`. -/
theorem ev_19 (π : Sym2 V → unitInterval) (y w : V) (χ : ℝ≥0∞)
    (hχ : ∀ v : V, ∑' z : V, tau π v z = χ) :
    (∑' z1 : V, ∑' z2 : V, ∑' z3 : V, ∑' pa : V × V × V × V,
        ∏ i, tau π
          (q4Legs ((0 : Fin 2)) (Sum.inr true) (Sum.inl (Sum.inl ((1 : Fin 2)))) z1 z2 z3 y w pa.1 pa.2.1 pa.2.2.1 pa.2.2.2 i).1
          (q4Legs ((0 : Fin 2)) (Sum.inr true) (Sum.inl (Sum.inl ((1 : Fin 2)))) z1 z2 z3 y w pa.1 pa.2.1 pa.2.2.1 pa.2.2.2 i).2) =
      χ ^ 6 * iterPow (kernel π) 2 w y := by
  have hNF : ∀ z1 z2 z3 (pa : V × V × V × V),
      (∏ i, tau π (q4Legs ((0 : Fin 2)) (Sum.inr true) (Sum.inl (Sum.inl ((1 : Fin 2)))) z1 z2 z3 y w pa.1 pa.2.1 pa.2.2.1 pa.2.2.2 i).1 (q4Legs ((0 : Fin 2)) (Sum.inr true) (Sum.inl (Sum.inl ((1 : Fin 2)))) z1 z2 z3 y w pa.1 pa.2.1 pa.2.2.1 pa.2.2.2 i).2) = tau π y z1 * tau π z1 w * tau π w z3 * tau π z1 z2 * (tau π z3 pa.1 * tau π z2 pa.2.1 * tau π z2 pa.2.2.1 * tau π z3 pa.2.2.2) := by
    intro z1 z2 z3 pa
    simp [q4Legs, splitAt, baseLegs, Fintype.prod_sum_type, Fin.prod_univ_two]
    all_goals ring
  simp only [hNF]
  have harm : (∑' z1 : V, ∑' z2 : V, ∑' z3 : V,
        (∑' pa : V × V × V × V, tau π y z1 * tau π z1 w * tau π w z3 * tau π z1 z2 * (tau π z3 pa.1 * tau π z2 pa.2.1 * tau π z2 pa.2.2.1 * tau π z3 pa.2.2.2))) =
      ∑' z1 : V, ∑' z2 : V, ∑' z3 : V, tau π y z1 * tau π z1 w * tau π w z3 * tau π z1 z2 * χ ^ 4 := by
    refine tsum_congr fun z1 => tsum_congr fun z2 => tsum_congr fun z3 => ?_
    exact tsum_arm_four_tuple π χ hχ z3 z2 z2 z3 _
  rw [harm]
  have hpull : (∑' z1 : V, ∑' z2 : V, ∑' z3 : V, tau π y z1 * tau π z1 w * tau π w z3 * tau π z1 z2 * χ ^ 4) =
      (∑' z1 : V, ∑' z2 : V, ∑' z3 : V, tau π y z1 * tau π z1 w * tau π w z3 * tau π z1 z2) * χ ^ 4 := by
    simp only [ENNReal.tsum_mul_right]
  rw [hpull]
  have hchain : (∑' z1 : V, ∑' z2 : V, ∑' z3 : V, tau π y z1 * tau π z1 w * tau π w z3 * tau π z1 z2) =
      χ ^ 2 * iterPow (kernel π) 2 y w := by
    refine Eq.trans (perm23 (fun a b c => tau π y a * tau π a w * tau π w c * tau π a b)) ?_
    simp only [ENNReal.tsum_mul_left, ENNReal.tsum_mul_right, hχ, ← I417FreshTwo.iterPow_two_eq]
    ring
  rw [hchain, iterPow_kernel_comm π 2 y w]
  ring

/-- Member `21` of the `q = 4` family: `k1 = (0 : Fin 2)`, `k2 = Sum.inr true`,
`k3 = Sum.inl (Sum.inr false)`.  Skeleton path `y – z1 – z3 – w` (so `ℓ = 3`),
summed-out skeleton vertices `z2` in peel order
`z2`. -/
theorem ev_20 (π : Sym2 V → unitInterval) (y w : V) (χ : ℝ≥0∞)
    (hχ : ∀ v : V, ∑' z : V, tau π v z = χ) :
    (∑' z1 : V, ∑' z2 : V, ∑' z3 : V, ∑' pa : V × V × V × V,
        ∏ i, tau π
          (q4Legs ((0 : Fin 2)) (Sum.inr true) (Sum.inl (Sum.inr false)) z1 z2 z3 y w pa.1 pa.2.1 pa.2.2.1 pa.2.2.2 i).1
          (q4Legs ((0 : Fin 2)) (Sum.inr true) (Sum.inl (Sum.inr false)) z1 z2 z3 y w pa.1 pa.2.1 pa.2.2.1 pa.2.2.2 i).2) =
      χ ^ 5 * iterPow (kernel π) 3 w y := by
  have hNF : ∀ z1 z2 z3 (pa : V × V × V × V),
      (∏ i, tau π (q4Legs ((0 : Fin 2)) (Sum.inr true) (Sum.inl (Sum.inr false)) z1 z2 z3 y w pa.1 pa.2.1 pa.2.2.1 pa.2.2.2 i).1 (q4Legs ((0 : Fin 2)) (Sum.inr true) (Sum.inl (Sum.inr false)) z1 z2 z3 y w pa.1 pa.2.1 pa.2.2.1 pa.2.2.2 i).2) = tau π y z1 * tau π z1 z3 * tau π z3 w * tau π z1 z2 * (tau π w pa.1 * tau π z2 pa.2.1 * tau π z2 pa.2.2.1 * tau π z3 pa.2.2.2) := by
    intro z1 z2 z3 pa
    simp [q4Legs, splitAt, baseLegs, Fintype.prod_sum_type, Fin.prod_univ_two]
    all_goals ring
  simp only [hNF]
  have harm : (∑' z1 : V, ∑' z2 : V, ∑' z3 : V,
        (∑' pa : V × V × V × V, tau π y z1 * tau π z1 z3 * tau π z3 w * tau π z1 z2 * (tau π w pa.1 * tau π z2 pa.2.1 * tau π z2 pa.2.2.1 * tau π z3 pa.2.2.2))) =
      ∑' z1 : V, ∑' z2 : V, ∑' z3 : V, tau π y z1 * tau π z1 z3 * tau π z3 w * tau π z1 z2 * χ ^ 4 := by
    refine tsum_congr fun z1 => tsum_congr fun z2 => tsum_congr fun z3 => ?_
    exact tsum_arm_four_tuple π χ hχ w z2 z2 z3 _
  rw [harm]
  have hpull : (∑' z1 : V, ∑' z2 : V, ∑' z3 : V, tau π y z1 * tau π z1 z3 * tau π z3 w * tau π z1 z2 * χ ^ 4) =
      (∑' z1 : V, ∑' z2 : V, ∑' z3 : V, tau π y z1 * tau π z1 z3 * tau π z3 w * tau π z1 z2) * χ ^ 4 := by
    simp only [ENNReal.tsum_mul_right]
  rw [hpull]
  have hchain : (∑' z1 : V, ∑' z2 : V, ∑' z3 : V, tau π y z1 * tau π z1 z3 * tau π z3 w * tau π z1 z2) =
      χ ^ 1 * iterPow (kernel π) 3 y w := by
    refine Eq.trans (perm23 (fun a b c => tau π y a * tau π a c * tau π c w * tau π a b)) ?_
    simp only [ENNReal.tsum_mul_left, ENNReal.tsum_mul_right, hχ, ← I417FreshTwo.iterPow_three_eq]
    ring
  rw [hchain, iterPow_kernel_comm π 3 y w]
  ring

/-- Member `22` of the `q = 4` family: `k1 = (0 : Fin 2)`, `k2 = Sum.inr true`,
`k3 = Sum.inl (Sum.inr true)`.  Skeleton path `y – z1 – w` (so `ℓ = 2`),
summed-out skeleton vertices `z2, z3` in peel order
`z2, z3`. -/
theorem ev_21 (π : Sym2 V → unitInterval) (y w : V) (χ : ℝ≥0∞)
    (hχ : ∀ v : V, ∑' z : V, tau π v z = χ) :
    (∑' z1 : V, ∑' z2 : V, ∑' z3 : V, ∑' pa : V × V × V × V,
        ∏ i, tau π
          (q4Legs ((0 : Fin 2)) (Sum.inr true) (Sum.inl (Sum.inr true)) z1 z2 z3 y w pa.1 pa.2.1 pa.2.2.1 pa.2.2.2 i).1
          (q4Legs ((0 : Fin 2)) (Sum.inr true) (Sum.inl (Sum.inr true)) z1 z2 z3 y w pa.1 pa.2.1 pa.2.2.1 pa.2.2.2 i).2) =
      χ ^ 6 * iterPow (kernel π) 2 w y := by
  have hNF : ∀ z1 z2 z3 (pa : V × V × V × V),
      (∏ i, tau π (q4Legs ((0 : Fin 2)) (Sum.inr true) (Sum.inl (Sum.inr true)) z1 z2 z3 y w pa.1 pa.2.1 pa.2.2.1 pa.2.2.2 i).1 (q4Legs ((0 : Fin 2)) (Sum.inr true) (Sum.inl (Sum.inr true)) z1 z2 z3 y w pa.1 pa.2.1 pa.2.2.1 pa.2.2.2 i).2) = tau π y z1 * tau π z1 w * tau π z1 z3 * tau π z3 z2 * (tau π w pa.1 * tau π z2 pa.2.1 * tau π z2 pa.2.2.1 * tau π z3 pa.2.2.2) := by
    intro z1 z2 z3 pa
    simp [q4Legs, splitAt, baseLegs, Fintype.prod_sum_type, Fin.prod_univ_two]
    all_goals ring
  simp only [hNF]
  have harm : (∑' z1 : V, ∑' z2 : V, ∑' z3 : V,
        (∑' pa : V × V × V × V, tau π y z1 * tau π z1 w * tau π z1 z3 * tau π z3 z2 * (tau π w pa.1 * tau π z2 pa.2.1 * tau π z2 pa.2.2.1 * tau π z3 pa.2.2.2))) =
      ∑' z1 : V, ∑' z2 : V, ∑' z3 : V, tau π y z1 * tau π z1 w * tau π z1 z3 * tau π z3 z2 * χ ^ 4 := by
    refine tsum_congr fun z1 => tsum_congr fun z2 => tsum_congr fun z3 => ?_
    exact tsum_arm_four_tuple π χ hχ w z2 z2 z3 _
  rw [harm]
  have hpull : (∑' z1 : V, ∑' z2 : V, ∑' z3 : V, tau π y z1 * tau π z1 w * tau π z1 z3 * tau π z3 z2 * χ ^ 4) =
      (∑' z1 : V, ∑' z2 : V, ∑' z3 : V, tau π y z1 * tau π z1 w * tau π z1 z3 * tau π z3 z2) * χ ^ 4 := by
    simp only [ENNReal.tsum_mul_right]
  rw [hpull]
  have hchain : (∑' z1 : V, ∑' z2 : V, ∑' z3 : V, tau π y z1 * tau π z1 w * tau π z1 z3 * tau π z3 z2) =
      χ ^ 2 * iterPow (kernel π) 2 y w := by
    refine Eq.trans (perm23 (fun a b c => tau π y a * tau π a w * tau π a c * tau π c b)) ?_
    simp only [ENNReal.tsum_mul_left, ENNReal.tsum_mul_right, hχ, ← I417FreshTwo.iterPow_two_eq]
    ring
  rw [hchain, iterPow_kernel_comm π 2 y w]
  ring

/-- Member `23` of the `q = 4` family: `k1 = (0 : Fin 2)`, `k2 = Sum.inr true`,
`k3 = Sum.inr false`.  Skeleton path `y – z1 – w` (so `ℓ = 2`),
summed-out skeleton vertices `z2, z3` in peel order
`z3, z2`. -/
theorem ev_22 (π : Sym2 V → unitInterval) (y w : V) (χ : ℝ≥0∞)
    (hχ : ∀ v : V, ∑' z : V, tau π v z = χ) :
    (∑' z1 : V, ∑' z2 : V, ∑' z3 : V, ∑' pa : V × V × V × V,
        ∏ i, tau π
          (q4Legs ((0 : Fin 2)) (Sum.inr true) (Sum.inr false) z1 z2 z3 y w pa.1 pa.2.1 pa.2.2.1 pa.2.2.2 i).1
          (q4Legs ((0 : Fin 2)) (Sum.inr true) (Sum.inr false) z1 z2 z3 y w pa.1 pa.2.1 pa.2.2.1 pa.2.2.2 i).2) =
      χ ^ 6 * iterPow (kernel π) 2 w y := by
  have hNF : ∀ z1 z2 z3 (pa : V × V × V × V),
      (∏ i, tau π (q4Legs ((0 : Fin 2)) (Sum.inr true) (Sum.inr false) z1 z2 z3 y w pa.1 pa.2.1 pa.2.2.1 pa.2.2.2 i).1 (q4Legs ((0 : Fin 2)) (Sum.inr true) (Sum.inr false) z1 z2 z3 y w pa.1 pa.2.1 pa.2.2.1 pa.2.2.2 i).2) = tau π y z1 * tau π z1 w * tau π z1 z2 * tau π z2 z3 * (tau π w pa.1 * tau π z3 pa.2.1 * tau π z2 pa.2.2.1 * tau π z3 pa.2.2.2) := by
    intro z1 z2 z3 pa
    simp [q4Legs, splitAt, baseLegs, Fintype.prod_sum_type, Fin.prod_univ_two]
    all_goals ring
  simp only [hNF]
  have harm : (∑' z1 : V, ∑' z2 : V, ∑' z3 : V,
        (∑' pa : V × V × V × V, tau π y z1 * tau π z1 w * tau π z1 z2 * tau π z2 z3 * (tau π w pa.1 * tau π z3 pa.2.1 * tau π z2 pa.2.2.1 * tau π z3 pa.2.2.2))) =
      ∑' z1 : V, ∑' z2 : V, ∑' z3 : V, tau π y z1 * tau π z1 w * tau π z1 z2 * tau π z2 z3 * χ ^ 4 := by
    refine tsum_congr fun z1 => tsum_congr fun z2 => tsum_congr fun z3 => ?_
    exact tsum_arm_four_tuple π χ hχ w z3 z2 z3 _
  rw [harm]
  have hpull : (∑' z1 : V, ∑' z2 : V, ∑' z3 : V, tau π y z1 * tau π z1 w * tau π z1 z2 * tau π z2 z3 * χ ^ 4) =
      (∑' z1 : V, ∑' z2 : V, ∑' z3 : V, tau π y z1 * tau π z1 w * tau π z1 z2 * tau π z2 z3) * χ ^ 4 := by
    simp only [ENNReal.tsum_mul_right]
  rw [hpull]
  have hchain : (∑' z1 : V, ∑' z2 : V, ∑' z3 : V, tau π y z1 * tau π z1 w * tau π z1 z2 * tau π z2 z3) =
      χ ^ 2 * iterPow (kernel π) 2 y w := by
    simp only [ENNReal.tsum_mul_left, ENNReal.tsum_mul_right, hχ, ← I417FreshTwo.iterPow_two_eq]
    ring
  rw [hchain, iterPow_kernel_comm π 2 y w]
  ring

/-- Member `24` of the `q = 4` family: `k1 = (0 : Fin 2)`, `k2 = Sum.inr true`,
`k3 = Sum.inr true`.  Skeleton path `y – z1 – w` (so `ℓ = 2`),
summed-out skeleton vertices `z2, z3` in peel order
`z3, z2`. -/
theorem ev_23 (π : Sym2 V → unitInterval) (y w : V) (χ : ℝ≥0∞)
    (hχ : ∀ v : V, ∑' z : V, tau π v z = χ) :
    (∑' z1 : V, ∑' z2 : V, ∑' z3 : V, ∑' pa : V × V × V × V,
        ∏ i, tau π
          (q4Legs ((0 : Fin 2)) (Sum.inr true) (Sum.inr true) z1 z2 z3 y w pa.1 pa.2.1 pa.2.2.1 pa.2.2.2 i).1
          (q4Legs ((0 : Fin 2)) (Sum.inr true) (Sum.inr true) z1 z2 z3 y w pa.1 pa.2.1 pa.2.2.1 pa.2.2.2 i).2) =
      χ ^ 6 * iterPow (kernel π) 2 w y := by
  have hNF : ∀ z1 z2 z3 (pa : V × V × V × V),
      (∏ i, tau π (q4Legs ((0 : Fin 2)) (Sum.inr true) (Sum.inr true) z1 z2 z3 y w pa.1 pa.2.1 pa.2.2.1 pa.2.2.2 i).1 (q4Legs ((0 : Fin 2)) (Sum.inr true) (Sum.inr true) z1 z2 z3 y w pa.1 pa.2.1 pa.2.2.1 pa.2.2.2 i).2) = tau π y z1 * tau π z1 w * tau π z1 z2 * tau π z2 z3 * (tau π w pa.1 * tau π z2 pa.2.1 * tau π z3 pa.2.2.1 * tau π z3 pa.2.2.2) := by
    intro z1 z2 z3 pa
    simp [q4Legs, splitAt, baseLegs, Fintype.prod_sum_type, Fin.prod_univ_two]
    all_goals ring
  simp only [hNF]
  have harm : (∑' z1 : V, ∑' z2 : V, ∑' z3 : V,
        (∑' pa : V × V × V × V, tau π y z1 * tau π z1 w * tau π z1 z2 * tau π z2 z3 * (tau π w pa.1 * tau π z2 pa.2.1 * tau π z3 pa.2.2.1 * tau π z3 pa.2.2.2))) =
      ∑' z1 : V, ∑' z2 : V, ∑' z3 : V, tau π y z1 * tau π z1 w * tau π z1 z2 * tau π z2 z3 * χ ^ 4 := by
    refine tsum_congr fun z1 => tsum_congr fun z2 => tsum_congr fun z3 => ?_
    exact tsum_arm_four_tuple π χ hχ w z2 z3 z3 _
  rw [harm]
  have hpull : (∑' z1 : V, ∑' z2 : V, ∑' z3 : V, tau π y z1 * tau π z1 w * tau π z1 z2 * tau π z2 z3 * χ ^ 4) =
      (∑' z1 : V, ∑' z2 : V, ∑' z3 : V, tau π y z1 * tau π z1 w * tau π z1 z2 * tau π z2 z3) * χ ^ 4 := by
    simp only [ENNReal.tsum_mul_right]
  rw [hpull]
  have hchain : (∑' z1 : V, ∑' z2 : V, ∑' z3 : V, tau π y z1 * tau π z1 w * tau π z1 z2 * tau π z2 z3) =
      χ ^ 2 * iterPow (kernel π) 2 y w := by
    simp only [ENNReal.tsum_mul_left, ENNReal.tsum_mul_right, hχ, ← I417FreshTwo.iterPow_two_eq]
    ring
  rw [hchain, iterPow_kernel_comm π 2 y w]
  ring

/-- Member `25` of the `q = 4` family: `k1 = (1 : Fin 2)`, `k2 = Sum.inl ((0 : Fin 2))`,
`k3 = Sum.inl (Sum.inl ((0 : Fin 2)))`.  Skeleton path `y – z3 – z2 – w` (so `ℓ = 3`),
summed-out skeleton vertices `z1` in peel order
`z1`. -/
theorem ev_24 (π : Sym2 V → unitInterval) (y w : V) (χ : ℝ≥0∞)
    (hχ : ∀ v : V, ∑' z : V, tau π v z = χ) :
    (∑' z1 : V, ∑' z2 : V, ∑' z3 : V, ∑' pa : V × V × V × V,
        ∏ i, tau π
          (q4Legs ((1 : Fin 2)) (Sum.inl ((0 : Fin 2))) (Sum.inl (Sum.inl ((0 : Fin 2)))) z1 z2 z3 y w pa.1 pa.2.1 pa.2.2.1 pa.2.2.2 i).1
          (q4Legs ((1 : Fin 2)) (Sum.inl ((0 : Fin 2))) (Sum.inl (Sum.inl ((0 : Fin 2)))) z1 z2 z3 y w pa.1 pa.2.1 pa.2.2.1 pa.2.2.2 i).2) =
      χ ^ 5 * iterPow (kernel π) 3 w y := by
  have hNF : ∀ z1 z2 z3 (pa : V × V × V × V),
      (∏ i, tau π (q4Legs ((1 : Fin 2)) (Sum.inl ((0 : Fin 2))) (Sum.inl (Sum.inl ((0 : Fin 2)))) z1 z2 z3 y w pa.1 pa.2.1 pa.2.2.1 pa.2.2.2 i).1 (q4Legs ((1 : Fin 2)) (Sum.inl ((0 : Fin 2))) (Sum.inl (Sum.inl ((0 : Fin 2)))) z1 z2 z3 y w pa.1 pa.2.1 pa.2.2.1 pa.2.2.2 i).2) = tau π y z3 * tau π z3 z2 * tau π z2 w * tau π w z1 * (tau π z1 pa.1 * tau π z1 pa.2.1 * tau π z2 pa.2.2.1 * tau π z3 pa.2.2.2) := by
    intro z1 z2 z3 pa
    simp [q4Legs, splitAt, baseLegs, Fintype.prod_sum_type, Fin.prod_univ_two]
    all_goals ring
  simp only [hNF]
  have harm : (∑' z1 : V, ∑' z2 : V, ∑' z3 : V,
        (∑' pa : V × V × V × V, tau π y z3 * tau π z3 z2 * tau π z2 w * tau π w z1 * (tau π z1 pa.1 * tau π z1 pa.2.1 * tau π z2 pa.2.2.1 * tau π z3 pa.2.2.2))) =
      ∑' z1 : V, ∑' z2 : V, ∑' z3 : V, tau π y z3 * tau π z3 z2 * tau π z2 w * tau π w z1 * χ ^ 4 := by
    refine tsum_congr fun z1 => tsum_congr fun z2 => tsum_congr fun z3 => ?_
    exact tsum_arm_four_tuple π χ hχ z1 z1 z2 z3 _
  rw [harm]
  have hpull : (∑' z1 : V, ∑' z2 : V, ∑' z3 : V, tau π y z3 * tau π z3 z2 * tau π z2 w * tau π w z1 * χ ^ 4) =
      (∑' z1 : V, ∑' z2 : V, ∑' z3 : V, tau π y z3 * tau π z3 z2 * tau π z2 w * tau π w z1) * χ ^ 4 := by
    simp only [ENNReal.tsum_mul_right]
  rw [hpull]
  have hchain : (∑' z1 : V, ∑' z2 : V, ∑' z3 : V, tau π y z3 * tau π z3 z2 * tau π z2 w * tau π w z1) =
      χ ^ 1 * iterPow (kernel π) 3 y w := by
    refine Eq.trans (perm13 (fun a b c => tau π y c * tau π c b * tau π b w * tau π w a)) ?_
    simp only [ENNReal.tsum_mul_left, ENNReal.tsum_mul_right, hχ, ← I417FreshTwo.iterPow_three_eq]
    ring
  rw [hchain, iterPow_kernel_comm π 3 y w]
  ring

/-- Member `26` of the `q = 4` family: `k1 = (1 : Fin 2)`, `k2 = Sum.inl ((0 : Fin 2))`,
`k3 = Sum.inl (Sum.inl ((1 : Fin 2)))`.  Skeleton path `y – z2 – w` (so `ℓ = 2`),
summed-out skeleton vertices `z1, z3` in peel order
`z1, z3`. -/
theorem ev_25 (π : Sym2 V → unitInterval) (y w : V) (χ : ℝ≥0∞)
    (hχ : ∀ v : V, ∑' z : V, tau π v z = χ) :
    (∑' z1 : V, ∑' z2 : V, ∑' z3 : V, ∑' pa : V × V × V × V,
        ∏ i, tau π
          (q4Legs ((1 : Fin 2)) (Sum.inl ((0 : Fin 2))) (Sum.inl (Sum.inl ((1 : Fin 2)))) z1 z2 z3 y w pa.1 pa.2.1 pa.2.2.1 pa.2.2.2 i).1
          (q4Legs ((1 : Fin 2)) (Sum.inl ((0 : Fin 2))) (Sum.inl (Sum.inl ((1 : Fin 2)))) z1 z2 z3 y w pa.1 pa.2.1 pa.2.2.1 pa.2.2.2 i).2) =
      χ ^ 6 * iterPow (kernel π) 2 w y := by
  have hNF : ∀ z1 z2 z3 (pa : V × V × V × V),
      (∏ i, tau π (q4Legs ((1 : Fin 2)) (Sum.inl ((0 : Fin 2))) (Sum.inl (Sum.inl ((1 : Fin 2)))) z1 z2 z3 y w pa.1 pa.2.1 pa.2.2.1 pa.2.2.2 i).1 (q4Legs ((1 : Fin 2)) (Sum.inl ((0 : Fin 2))) (Sum.inl (Sum.inl ((1 : Fin 2)))) z1 z2 z3 y w pa.1 pa.2.1 pa.2.2.1 pa.2.2.2 i).2) = tau π y z2 * tau π z2 w * tau π w z3 * tau π z3 z1 * (tau π z1 pa.1 * tau π z1 pa.2.1 * tau π z2 pa.2.2.1 * tau π z3 pa.2.2.2) := by
    intro z1 z2 z3 pa
    simp [q4Legs, splitAt, baseLegs, Fintype.prod_sum_type, Fin.prod_univ_two]
    all_goals ring
  simp only [hNF]
  have harm : (∑' z1 : V, ∑' z2 : V, ∑' z3 : V,
        (∑' pa : V × V × V × V, tau π y z2 * tau π z2 w * tau π w z3 * tau π z3 z1 * (tau π z1 pa.1 * tau π z1 pa.2.1 * tau π z2 pa.2.2.1 * tau π z3 pa.2.2.2))) =
      ∑' z1 : V, ∑' z2 : V, ∑' z3 : V, tau π y z2 * tau π z2 w * tau π w z3 * tau π z3 z1 * χ ^ 4 := by
    refine tsum_congr fun z1 => tsum_congr fun z2 => tsum_congr fun z3 => ?_
    exact tsum_arm_four_tuple π χ hχ z1 z1 z2 z3 _
  rw [harm]
  have hpull : (∑' z1 : V, ∑' z2 : V, ∑' z3 : V, tau π y z2 * tau π z2 w * tau π w z3 * tau π z3 z1 * χ ^ 4) =
      (∑' z1 : V, ∑' z2 : V, ∑' z3 : V, tau π y z2 * tau π z2 w * tau π w z3 * tau π z3 z1) * χ ^ 4 := by
    simp only [ENNReal.tsum_mul_right]
  rw [hpull]
  have hchain : (∑' z1 : V, ∑' z2 : V, ∑' z3 : V, tau π y z2 * tau π z2 w * tau π w z3 * tau π z3 z1) =
      χ ^ 2 * iterPow (kernel π) 2 y w := by
    refine Eq.trans (perm231 (fun a b c => tau π y b * tau π b w * tau π w c * tau π c a)) ?_
    simp only [ENNReal.tsum_mul_left, ENNReal.tsum_mul_right, hχ, ← I417FreshTwo.iterPow_two_eq]
    ring
  rw [hchain, iterPow_kernel_comm π 2 y w]
  ring

/-- Member `27` of the `q = 4` family: `k1 = (1 : Fin 2)`, `k2 = Sum.inl ((0 : Fin 2))`,
`k3 = Sum.inl (Sum.inr false)`.  Skeleton path `y – z2 – w` (so `ℓ = 2`),
summed-out skeleton vertices `z1, z3` in peel order
`z3, z1`. -/
theorem ev_26 (π : Sym2 V → unitInterval) (y w : V) (χ : ℝ≥0∞)
    (hχ : ∀ v : V, ∑' z : V, tau π v z = χ) :
    (∑' z1 : V, ∑' z2 : V, ∑' z3 : V, ∑' pa : V × V × V × V,
        ∏ i, tau π
          (q4Legs ((1 : Fin 2)) (Sum.inl ((0 : Fin 2))) (Sum.inl (Sum.inr false)) z1 z2 z3 y w pa.1 pa.2.1 pa.2.2.1 pa.2.2.2 i).1
          (q4Legs ((1 : Fin 2)) (Sum.inl ((0 : Fin 2))) (Sum.inl (Sum.inr false)) z1 z2 z3 y w pa.1 pa.2.1 pa.2.2.1 pa.2.2.2 i).2) =
      χ ^ 6 * iterPow (kernel π) 2 w y := by
  have hNF : ∀ z1 z2 z3 (pa : V × V × V × V),
      (∏ i, tau π (q4Legs ((1 : Fin 2)) (Sum.inl ((0 : Fin 2))) (Sum.inl (Sum.inr false)) z1 z2 z3 y w pa.1 pa.2.1 pa.2.2.1 pa.2.2.2 i).1 (q4Legs ((1 : Fin 2)) (Sum.inl ((0 : Fin 2))) (Sum.inl (Sum.inr false)) z1 z2 z3 y w pa.1 pa.2.1 pa.2.2.1 pa.2.2.2 i).2) = tau π y z2 * tau π z2 w * tau π w z1 * tau π z1 z3 * (tau π z3 pa.1 * tau π z1 pa.2.1 * tau π z2 pa.2.2.1 * tau π z3 pa.2.2.2) := by
    intro z1 z2 z3 pa
    simp [q4Legs, splitAt, baseLegs, Fintype.prod_sum_type, Fin.prod_univ_two]
    all_goals ring
  simp only [hNF]
  have harm : (∑' z1 : V, ∑' z2 : V, ∑' z3 : V,
        (∑' pa : V × V × V × V, tau π y z2 * tau π z2 w * tau π w z1 * tau π z1 z3 * (tau π z3 pa.1 * tau π z1 pa.2.1 * tau π z2 pa.2.2.1 * tau π z3 pa.2.2.2))) =
      ∑' z1 : V, ∑' z2 : V, ∑' z3 : V, tau π y z2 * tau π z2 w * tau π w z1 * tau π z1 z3 * χ ^ 4 := by
    refine tsum_congr fun z1 => tsum_congr fun z2 => tsum_congr fun z3 => ?_
    exact tsum_arm_four_tuple π χ hχ z3 z1 z2 z3 _
  rw [harm]
  have hpull : (∑' z1 : V, ∑' z2 : V, ∑' z3 : V, tau π y z2 * tau π z2 w * tau π w z1 * tau π z1 z3 * χ ^ 4) =
      (∑' z1 : V, ∑' z2 : V, ∑' z3 : V, tau π y z2 * tau π z2 w * tau π w z1 * tau π z1 z3) * χ ^ 4 := by
    simp only [ENNReal.tsum_mul_right]
  rw [hpull]
  have hchain : (∑' z1 : V, ∑' z2 : V, ∑' z3 : V, tau π y z2 * tau π z2 w * tau π w z1 * tau π z1 z3) =
      χ ^ 2 * iterPow (kernel π) 2 y w := by
    refine Eq.trans (perm12 (fun a b c => tau π y b * tau π b w * tau π w a * tau π a c)) ?_
    simp only [ENNReal.tsum_mul_left, ENNReal.tsum_mul_right, hχ, ← I417FreshTwo.iterPow_two_eq]
    ring
  rw [hchain, iterPow_kernel_comm π 2 y w]
  ring

/-- Member `28` of the `q = 4` family: `k1 = (1 : Fin 2)`, `k2 = Sum.inl ((0 : Fin 2))`,
`k3 = Sum.inl (Sum.inr true)`.  Skeleton path `y – z2 – w` (so `ℓ = 2`),
summed-out skeleton vertices `z1, z3` in peel order
`z3, z1`. -/
theorem ev_27 (π : Sym2 V → unitInterval) (y w : V) (χ : ℝ≥0∞)
    (hχ : ∀ v : V, ∑' z : V, tau π v z = χ) :
    (∑' z1 : V, ∑' z2 : V, ∑' z3 : V, ∑' pa : V × V × V × V,
        ∏ i, tau π
          (q4Legs ((1 : Fin 2)) (Sum.inl ((0 : Fin 2))) (Sum.inl (Sum.inr true)) z1 z2 z3 y w pa.1 pa.2.1 pa.2.2.1 pa.2.2.2 i).1
          (q4Legs ((1 : Fin 2)) (Sum.inl ((0 : Fin 2))) (Sum.inl (Sum.inr true)) z1 z2 z3 y w pa.1 pa.2.1 pa.2.2.1 pa.2.2.2 i).2) =
      χ ^ 6 * iterPow (kernel π) 2 w y := by
  have hNF : ∀ z1 z2 z3 (pa : V × V × V × V),
      (∏ i, tau π (q4Legs ((1 : Fin 2)) (Sum.inl ((0 : Fin 2))) (Sum.inl (Sum.inr true)) z1 z2 z3 y w pa.1 pa.2.1 pa.2.2.1 pa.2.2.2 i).1 (q4Legs ((1 : Fin 2)) (Sum.inl ((0 : Fin 2))) (Sum.inl (Sum.inr true)) z1 z2 z3 y w pa.1 pa.2.1 pa.2.2.1 pa.2.2.2 i).2) = tau π y z2 * tau π z2 w * tau π w z1 * tau π z1 z3 * (tau π z1 pa.1 * tau π z3 pa.2.1 * tau π z2 pa.2.2.1 * tau π z3 pa.2.2.2) := by
    intro z1 z2 z3 pa
    simp [q4Legs, splitAt, baseLegs, Fintype.prod_sum_type, Fin.prod_univ_two]
    all_goals ring
  simp only [hNF]
  have harm : (∑' z1 : V, ∑' z2 : V, ∑' z3 : V,
        (∑' pa : V × V × V × V, tau π y z2 * tau π z2 w * tau π w z1 * tau π z1 z3 * (tau π z1 pa.1 * tau π z3 pa.2.1 * tau π z2 pa.2.2.1 * tau π z3 pa.2.2.2))) =
      ∑' z1 : V, ∑' z2 : V, ∑' z3 : V, tau π y z2 * tau π z2 w * tau π w z1 * tau π z1 z3 * χ ^ 4 := by
    refine tsum_congr fun z1 => tsum_congr fun z2 => tsum_congr fun z3 => ?_
    exact tsum_arm_four_tuple π χ hχ z1 z3 z2 z3 _
  rw [harm]
  have hpull : (∑' z1 : V, ∑' z2 : V, ∑' z3 : V, tau π y z2 * tau π z2 w * tau π w z1 * tau π z1 z3 * χ ^ 4) =
      (∑' z1 : V, ∑' z2 : V, ∑' z3 : V, tau π y z2 * tau π z2 w * tau π w z1 * tau π z1 z3) * χ ^ 4 := by
    simp only [ENNReal.tsum_mul_right]
  rw [hpull]
  have hchain : (∑' z1 : V, ∑' z2 : V, ∑' z3 : V, tau π y z2 * tau π z2 w * tau π w z1 * tau π z1 z3) =
      χ ^ 2 * iterPow (kernel π) 2 y w := by
    refine Eq.trans (perm12 (fun a b c => tau π y b * tau π b w * tau π w a * tau π a c)) ?_
    simp only [ENNReal.tsum_mul_left, ENNReal.tsum_mul_right, hχ, ← I417FreshTwo.iterPow_two_eq]
    ring
  rw [hchain, iterPow_kernel_comm π 2 y w]
  ring

/-- Member `29` of the `q = 4` family: `k1 = (1 : Fin 2)`, `k2 = Sum.inl ((0 : Fin 2))`,
`k3 = Sum.inr false`.  Skeleton path `y – z2 – z3 – w` (so `ℓ = 3`),
summed-out skeleton vertices `z1` in peel order
`z1`. -/
theorem ev_28 (π : Sym2 V → unitInterval) (y w : V) (χ : ℝ≥0∞)
    (hχ : ∀ v : V, ∑' z : V, tau π v z = χ) :
    (∑' z1 : V, ∑' z2 : V, ∑' z3 : V, ∑' pa : V × V × V × V,
        ∏ i, tau π
          (q4Legs ((1 : Fin 2)) (Sum.inl ((0 : Fin 2))) (Sum.inr false) z1 z2 z3 y w pa.1 pa.2.1 pa.2.2.1 pa.2.2.2 i).1
          (q4Legs ((1 : Fin 2)) (Sum.inl ((0 : Fin 2))) (Sum.inr false) z1 z2 z3 y w pa.1 pa.2.1 pa.2.2.1 pa.2.2.2 i).2) =
      χ ^ 5 * iterPow (kernel π) 3 w y := by
  have hNF : ∀ z1 z2 z3 (pa : V × V × V × V),
      (∏ i, tau π (q4Legs ((1 : Fin 2)) (Sum.inl ((0 : Fin 2))) (Sum.inr false) z1 z2 z3 y w pa.1 pa.2.1 pa.2.2.1 pa.2.2.2 i).1 (q4Legs ((1 : Fin 2)) (Sum.inl ((0 : Fin 2))) (Sum.inr false) z1 z2 z3 y w pa.1 pa.2.1 pa.2.2.1 pa.2.2.2 i).2) = tau π y z2 * tau π z2 z3 * tau π z3 w * tau π w z1 * (tau π z1 pa.1 * tau π z1 pa.2.1 * tau π z2 pa.2.2.1 * tau π z3 pa.2.2.2) := by
    intro z1 z2 z3 pa
    simp [q4Legs, splitAt, baseLegs, Fintype.prod_sum_type, Fin.prod_univ_two]
    all_goals ring
  simp only [hNF]
  have harm : (∑' z1 : V, ∑' z2 : V, ∑' z3 : V,
        (∑' pa : V × V × V × V, tau π y z2 * tau π z2 z3 * tau π z3 w * tau π w z1 * (tau π z1 pa.1 * tau π z1 pa.2.1 * tau π z2 pa.2.2.1 * tau π z3 pa.2.2.2))) =
      ∑' z1 : V, ∑' z2 : V, ∑' z3 : V, tau π y z2 * tau π z2 z3 * tau π z3 w * tau π w z1 * χ ^ 4 := by
    refine tsum_congr fun z1 => tsum_congr fun z2 => tsum_congr fun z3 => ?_
    exact tsum_arm_four_tuple π χ hχ z1 z1 z2 z3 _
  rw [harm]
  have hpull : (∑' z1 : V, ∑' z2 : V, ∑' z3 : V, tau π y z2 * tau π z2 z3 * tau π z3 w * tau π w z1 * χ ^ 4) =
      (∑' z1 : V, ∑' z2 : V, ∑' z3 : V, tau π y z2 * tau π z2 z3 * tau π z3 w * tau π w z1) * χ ^ 4 := by
    simp only [ENNReal.tsum_mul_right]
  rw [hpull]
  have hchain : (∑' z1 : V, ∑' z2 : V, ∑' z3 : V, tau π y z2 * tau π z2 z3 * tau π z3 w * tau π w z1) =
      χ ^ 1 * iterPow (kernel π) 3 y w := by
    refine Eq.trans (perm231 (fun a b c => tau π y b * tau π b c * tau π c w * tau π w a)) ?_
    simp only [ENNReal.tsum_mul_left, ENNReal.tsum_mul_right, hχ, ← I417FreshTwo.iterPow_three_eq]
    ring
  rw [hchain, iterPow_kernel_comm π 3 y w]
  ring

/-- Member `30` of the `q = 4` family: `k1 = (1 : Fin 2)`, `k2 = Sum.inl ((0 : Fin 2))`,
`k3 = Sum.inr true`.  Skeleton path `y – z2 – w` (so `ℓ = 2`),
summed-out skeleton vertices `z1, z3` in peel order
`z1, z3`. -/
theorem ev_29 (π : Sym2 V → unitInterval) (y w : V) (χ : ℝ≥0∞)
    (hχ : ∀ v : V, ∑' z : V, tau π v z = χ) :
    (∑' z1 : V, ∑' z2 : V, ∑' z3 : V, ∑' pa : V × V × V × V,
        ∏ i, tau π
          (q4Legs ((1 : Fin 2)) (Sum.inl ((0 : Fin 2))) (Sum.inr true) z1 z2 z3 y w pa.1 pa.2.1 pa.2.2.1 pa.2.2.2 i).1
          (q4Legs ((1 : Fin 2)) (Sum.inl ((0 : Fin 2))) (Sum.inr true) z1 z2 z3 y w pa.1 pa.2.1 pa.2.2.1 pa.2.2.2 i).2) =
      χ ^ 6 * iterPow (kernel π) 2 w y := by
  have hNF : ∀ z1 z2 z3 (pa : V × V × V × V),
      (∏ i, tau π (q4Legs ((1 : Fin 2)) (Sum.inl ((0 : Fin 2))) (Sum.inr true) z1 z2 z3 y w pa.1 pa.2.1 pa.2.2.1 pa.2.2.2 i).1 (q4Legs ((1 : Fin 2)) (Sum.inl ((0 : Fin 2))) (Sum.inr true) z1 z2 z3 y w pa.1 pa.2.1 pa.2.2.1 pa.2.2.2 i).2) = tau π y z2 * tau π z2 w * tau π z2 z3 * tau π w z1 * (tau π z1 pa.1 * tau π z1 pa.2.1 * tau π z3 pa.2.2.1 * tau π z3 pa.2.2.2) := by
    intro z1 z2 z3 pa
    simp [q4Legs, splitAt, baseLegs, Fintype.prod_sum_type, Fin.prod_univ_two]
    all_goals ring
  simp only [hNF]
  have harm : (∑' z1 : V, ∑' z2 : V, ∑' z3 : V,
        (∑' pa : V × V × V × V, tau π y z2 * tau π z2 w * tau π z2 z3 * tau π w z1 * (tau π z1 pa.1 * tau π z1 pa.2.1 * tau π z3 pa.2.2.1 * tau π z3 pa.2.2.2))) =
      ∑' z1 : V, ∑' z2 : V, ∑' z3 : V, tau π y z2 * tau π z2 w * tau π z2 z3 * tau π w z1 * χ ^ 4 := by
    refine tsum_congr fun z1 => tsum_congr fun z2 => tsum_congr fun z3 => ?_
    exact tsum_arm_four_tuple π χ hχ z1 z1 z3 z3 _
  rw [harm]
  have hpull : (∑' z1 : V, ∑' z2 : V, ∑' z3 : V, tau π y z2 * tau π z2 w * tau π z2 z3 * tau π w z1 * χ ^ 4) =
      (∑' z1 : V, ∑' z2 : V, ∑' z3 : V, tau π y z2 * tau π z2 w * tau π z2 z3 * tau π w z1) * χ ^ 4 := by
    simp only [ENNReal.tsum_mul_right]
  rw [hpull]
  have hchain : (∑' z1 : V, ∑' z2 : V, ∑' z3 : V, tau π y z2 * tau π z2 w * tau π z2 z3 * tau π w z1) =
      χ ^ 2 * iterPow (kernel π) 2 y w := by
    refine Eq.trans (perm231 (fun a b c => tau π y b * tau π b w * tau π b c * tau π w a)) ?_
    simp only [ENNReal.tsum_mul_left, ENNReal.tsum_mul_right, hχ, ← I417FreshTwo.iterPow_two_eq]
    ring
  rw [hchain, iterPow_kernel_comm π 2 y w]
  ring

/-- Member `31` of the `q = 4` family: `k1 = (1 : Fin 2)`, `k2 = Sum.inl ((1 : Fin 2))`,
`k3 = Sum.inl (Sum.inl ((0 : Fin 2)))`.  Skeleton path `y – z3 – w` (so `ℓ = 2`),
summed-out skeleton vertices `z1, z2` in peel order
`z1, z2`. -/
theorem ev_30 (π : Sym2 V → unitInterval) (y w : V) (χ : ℝ≥0∞)
    (hχ : ∀ v : V, ∑' z : V, tau π v z = χ) :
    (∑' z1 : V, ∑' z2 : V, ∑' z3 : V, ∑' pa : V × V × V × V,
        ∏ i, tau π
          (q4Legs ((1 : Fin 2)) (Sum.inl ((1 : Fin 2))) (Sum.inl (Sum.inl ((0 : Fin 2)))) z1 z2 z3 y w pa.1 pa.2.1 pa.2.2.1 pa.2.2.2 i).1
          (q4Legs ((1 : Fin 2)) (Sum.inl ((1 : Fin 2))) (Sum.inl (Sum.inl ((0 : Fin 2)))) z1 z2 z3 y w pa.1 pa.2.1 pa.2.2.1 pa.2.2.2 i).2) =
      χ ^ 6 * iterPow (kernel π) 2 w y := by
  have hNF : ∀ z1 z2 z3 (pa : V × V × V × V),
      (∏ i, tau π (q4Legs ((1 : Fin 2)) (Sum.inl ((1 : Fin 2))) (Sum.inl (Sum.inl ((0 : Fin 2)))) z1 z2 z3 y w pa.1 pa.2.1 pa.2.2.1 pa.2.2.2 i).1 (q4Legs ((1 : Fin 2)) (Sum.inl ((1 : Fin 2))) (Sum.inl (Sum.inl ((0 : Fin 2)))) z1 z2 z3 y w pa.1 pa.2.1 pa.2.2.1 pa.2.2.2 i).2) = tau π y z3 * tau π z3 w * tau π w z2 * tau π z2 z1 * (tau π z1 pa.1 * tau π z1 pa.2.1 * tau π z2 pa.2.2.1 * tau π z3 pa.2.2.2) := by
    intro z1 z2 z3 pa
    simp [q4Legs, splitAt, baseLegs, Fintype.prod_sum_type, Fin.prod_univ_two]
    all_goals ring
  simp only [hNF]
  have harm : (∑' z1 : V, ∑' z2 : V, ∑' z3 : V,
        (∑' pa : V × V × V × V, tau π y z3 * tau π z3 w * tau π w z2 * tau π z2 z1 * (tau π z1 pa.1 * tau π z1 pa.2.1 * tau π z2 pa.2.2.1 * tau π z3 pa.2.2.2))) =
      ∑' z1 : V, ∑' z2 : V, ∑' z3 : V, tau π y z3 * tau π z3 w * tau π w z2 * tau π z2 z1 * χ ^ 4 := by
    refine tsum_congr fun z1 => tsum_congr fun z2 => tsum_congr fun z3 => ?_
    exact tsum_arm_four_tuple π χ hχ z1 z1 z2 z3 _
  rw [harm]
  have hpull : (∑' z1 : V, ∑' z2 : V, ∑' z3 : V, tau π y z3 * tau π z3 w * tau π w z2 * tau π z2 z1 * χ ^ 4) =
      (∑' z1 : V, ∑' z2 : V, ∑' z3 : V, tau π y z3 * tau π z3 w * tau π w z2 * tau π z2 z1) * χ ^ 4 := by
    simp only [ENNReal.tsum_mul_right]
  rw [hpull]
  have hchain : (∑' z1 : V, ∑' z2 : V, ∑' z3 : V, tau π y z3 * tau π z3 w * tau π w z2 * tau π z2 z1) =
      χ ^ 2 * iterPow (kernel π) 2 y w := by
    refine Eq.trans (perm13 (fun a b c => tau π y c * tau π c w * tau π w b * tau π b a)) ?_
    simp only [ENNReal.tsum_mul_left, ENNReal.tsum_mul_right, hχ, ← I417FreshTwo.iterPow_two_eq]
    ring
  rw [hchain, iterPow_kernel_comm π 2 y w]
  ring

/-- Member `32` of the `q = 4` family: `k1 = (1 : Fin 2)`, `k2 = Sum.inl ((1 : Fin 2))`,
`k3 = Sum.inl (Sum.inl ((1 : Fin 2)))`.  Skeleton path `y – w` (so `ℓ = 1`),
summed-out skeleton vertices `z1, z2, z3` in peel order
`z1, z2, z3`. -/
theorem ev_31 (π : Sym2 V → unitInterval) (y w : V) (χ : ℝ≥0∞)
    (hχ : ∀ v : V, ∑' z : V, tau π v z = χ) :
    (∑' z1 : V, ∑' z2 : V, ∑' z3 : V, ∑' pa : V × V × V × V,
        ∏ i, tau π
          (q4Legs ((1 : Fin 2)) (Sum.inl ((1 : Fin 2))) (Sum.inl (Sum.inl ((1 : Fin 2)))) z1 z2 z3 y w pa.1 pa.2.1 pa.2.2.1 pa.2.2.2 i).1
          (q4Legs ((1 : Fin 2)) (Sum.inl ((1 : Fin 2))) (Sum.inl (Sum.inl ((1 : Fin 2)))) z1 z2 z3 y w pa.1 pa.2.1 pa.2.2.1 pa.2.2.2 i).2) =
      χ ^ 7 * iterPow (kernel π) 1 w y := by
  have hNF : ∀ z1 z2 z3 (pa : V × V × V × V),
      (∏ i, tau π (q4Legs ((1 : Fin 2)) (Sum.inl ((1 : Fin 2))) (Sum.inl (Sum.inl ((1 : Fin 2)))) z1 z2 z3 y w pa.1 pa.2.1 pa.2.2.1 pa.2.2.2 i).1 (q4Legs ((1 : Fin 2)) (Sum.inl ((1 : Fin 2))) (Sum.inl (Sum.inl ((1 : Fin 2)))) z1 z2 z3 y w pa.1 pa.2.1 pa.2.2.1 pa.2.2.2 i).2) = tau π y w * tau π w z3 * tau π z3 z2 * tau π z2 z1 * (tau π z1 pa.1 * tau π z1 pa.2.1 * tau π z2 pa.2.2.1 * tau π z3 pa.2.2.2) := by
    intro z1 z2 z3 pa
    simp [q4Legs, splitAt, baseLegs, Fintype.prod_sum_type, Fin.prod_univ_two]
    all_goals ring
  simp only [hNF]
  have harm : (∑' z1 : V, ∑' z2 : V, ∑' z3 : V,
        (∑' pa : V × V × V × V, tau π y w * tau π w z3 * tau π z3 z2 * tau π z2 z1 * (tau π z1 pa.1 * tau π z1 pa.2.1 * tau π z2 pa.2.2.1 * tau π z3 pa.2.2.2))) =
      ∑' z1 : V, ∑' z2 : V, ∑' z3 : V, tau π y w * tau π w z3 * tau π z3 z2 * tau π z2 z1 * χ ^ 4 := by
    refine tsum_congr fun z1 => tsum_congr fun z2 => tsum_congr fun z3 => ?_
    exact tsum_arm_four_tuple π χ hχ z1 z1 z2 z3 _
  rw [harm]
  have hpull : (∑' z1 : V, ∑' z2 : V, ∑' z3 : V, tau π y w * tau π w z3 * tau π z3 z2 * tau π z2 z1 * χ ^ 4) =
      (∑' z1 : V, ∑' z2 : V, ∑' z3 : V, tau π y w * tau π w z3 * tau π z3 z2 * tau π z2 z1) * χ ^ 4 := by
    simp only [ENNReal.tsum_mul_right]
  rw [hpull]
  have hchain : (∑' z1 : V, ∑' z2 : V, ∑' z3 : V, tau π y w * tau π w z3 * tau π z3 z2 * tau π z2 z1) =
      χ ^ 3 * iterPow (kernel π) 1 y w := by
    refine Eq.trans (perm13 (fun a b c => tau π y w * tau π w c * tau π c b * tau π b a)) ?_
    simp only [ENNReal.tsum_mul_left, ENNReal.tsum_mul_right, hχ]
    rw [I417FreshTwo.iterPow_one, ← kernel_def]
    ring
  rw [hchain, iterPow_kernel_comm π 1 y w]
  ring

/-- Member `33` of the `q = 4` family: `k1 = (1 : Fin 2)`, `k2 = Sum.inl ((1 : Fin 2))`,
`k3 = Sum.inl (Sum.inr false)`.  Skeleton path `y – w` (so `ℓ = 1`),
summed-out skeleton vertices `z1, z2, z3` in peel order
`z3, z1, z2`. -/
theorem ev_32 (π : Sym2 V → unitInterval) (y w : V) (χ : ℝ≥0∞)
    (hχ : ∀ v : V, ∑' z : V, tau π v z = χ) :
    (∑' z1 : V, ∑' z2 : V, ∑' z3 : V, ∑' pa : V × V × V × V,
        ∏ i, tau π
          (q4Legs ((1 : Fin 2)) (Sum.inl ((1 : Fin 2))) (Sum.inl (Sum.inr false)) z1 z2 z3 y w pa.1 pa.2.1 pa.2.2.1 pa.2.2.2 i).1
          (q4Legs ((1 : Fin 2)) (Sum.inl ((1 : Fin 2))) (Sum.inl (Sum.inr false)) z1 z2 z3 y w pa.1 pa.2.1 pa.2.2.1 pa.2.2.2 i).2) =
      χ ^ 7 * iterPow (kernel π) 1 w y := by
  have hNF : ∀ z1 z2 z3 (pa : V × V × V × V),
      (∏ i, tau π (q4Legs ((1 : Fin 2)) (Sum.inl ((1 : Fin 2))) (Sum.inl (Sum.inr false)) z1 z2 z3 y w pa.1 pa.2.1 pa.2.2.1 pa.2.2.2 i).1 (q4Legs ((1 : Fin 2)) (Sum.inl ((1 : Fin 2))) (Sum.inl (Sum.inr false)) z1 z2 z3 y w pa.1 pa.2.1 pa.2.2.1 pa.2.2.2 i).2) = tau π y w * tau π w z2 * tau π z2 z1 * tau π z1 z3 * (tau π z3 pa.1 * tau π z1 pa.2.1 * tau π z2 pa.2.2.1 * tau π z3 pa.2.2.2) := by
    intro z1 z2 z3 pa
    simp [q4Legs, splitAt, baseLegs, Fintype.prod_sum_type, Fin.prod_univ_two]
    all_goals ring
  simp only [hNF]
  have harm : (∑' z1 : V, ∑' z2 : V, ∑' z3 : V,
        (∑' pa : V × V × V × V, tau π y w * tau π w z2 * tau π z2 z1 * tau π z1 z3 * (tau π z3 pa.1 * tau π z1 pa.2.1 * tau π z2 pa.2.2.1 * tau π z3 pa.2.2.2))) =
      ∑' z1 : V, ∑' z2 : V, ∑' z3 : V, tau π y w * tau π w z2 * tau π z2 z1 * tau π z1 z3 * χ ^ 4 := by
    refine tsum_congr fun z1 => tsum_congr fun z2 => tsum_congr fun z3 => ?_
    exact tsum_arm_four_tuple π χ hχ z3 z1 z2 z3 _
  rw [harm]
  have hpull : (∑' z1 : V, ∑' z2 : V, ∑' z3 : V, tau π y w * tau π w z2 * tau π z2 z1 * tau π z1 z3 * χ ^ 4) =
      (∑' z1 : V, ∑' z2 : V, ∑' z3 : V, tau π y w * tau π w z2 * tau π z2 z1 * tau π z1 z3) * χ ^ 4 := by
    simp only [ENNReal.tsum_mul_right]
  rw [hpull]
  have hchain : (∑' z1 : V, ∑' z2 : V, ∑' z3 : V, tau π y w * tau π w z2 * tau π z2 z1 * tau π z1 z3) =
      χ ^ 3 * iterPow (kernel π) 1 y w := by
    refine Eq.trans (perm12 (fun a b c => tau π y w * tau π w b * tau π b a * tau π a c)) ?_
    simp only [ENNReal.tsum_mul_left, ENNReal.tsum_mul_right, hχ]
    rw [I417FreshTwo.iterPow_one, ← kernel_def]
    ring
  rw [hchain, iterPow_kernel_comm π 1 y w]
  ring

/-- Member `34` of the `q = 4` family: `k1 = (1 : Fin 2)`, `k2 = Sum.inl ((1 : Fin 2))`,
`k3 = Sum.inl (Sum.inr true)`.  Skeleton path `y – w` (so `ℓ = 1`),
summed-out skeleton vertices `z1, z2, z3` in peel order
`z3, z1, z2`. -/
theorem ev_33 (π : Sym2 V → unitInterval) (y w : V) (χ : ℝ≥0∞)
    (hχ : ∀ v : V, ∑' z : V, tau π v z = χ) :
    (∑' z1 : V, ∑' z2 : V, ∑' z3 : V, ∑' pa : V × V × V × V,
        ∏ i, tau π
          (q4Legs ((1 : Fin 2)) (Sum.inl ((1 : Fin 2))) (Sum.inl (Sum.inr true)) z1 z2 z3 y w pa.1 pa.2.1 pa.2.2.1 pa.2.2.2 i).1
          (q4Legs ((1 : Fin 2)) (Sum.inl ((1 : Fin 2))) (Sum.inl (Sum.inr true)) z1 z2 z3 y w pa.1 pa.2.1 pa.2.2.1 pa.2.2.2 i).2) =
      χ ^ 7 * iterPow (kernel π) 1 w y := by
  have hNF : ∀ z1 z2 z3 (pa : V × V × V × V),
      (∏ i, tau π (q4Legs ((1 : Fin 2)) (Sum.inl ((1 : Fin 2))) (Sum.inl (Sum.inr true)) z1 z2 z3 y w pa.1 pa.2.1 pa.2.2.1 pa.2.2.2 i).1 (q4Legs ((1 : Fin 2)) (Sum.inl ((1 : Fin 2))) (Sum.inl (Sum.inr true)) z1 z2 z3 y w pa.1 pa.2.1 pa.2.2.1 pa.2.2.2 i).2) = tau π y w * tau π w z2 * tau π z2 z1 * tau π z1 z3 * (tau π z1 pa.1 * tau π z3 pa.2.1 * tau π z2 pa.2.2.1 * tau π z3 pa.2.2.2) := by
    intro z1 z2 z3 pa
    simp [q4Legs, splitAt, baseLegs, Fintype.prod_sum_type, Fin.prod_univ_two]
    all_goals ring
  simp only [hNF]
  have harm : (∑' z1 : V, ∑' z2 : V, ∑' z3 : V,
        (∑' pa : V × V × V × V, tau π y w * tau π w z2 * tau π z2 z1 * tau π z1 z3 * (tau π z1 pa.1 * tau π z3 pa.2.1 * tau π z2 pa.2.2.1 * tau π z3 pa.2.2.2))) =
      ∑' z1 : V, ∑' z2 : V, ∑' z3 : V, tau π y w * tau π w z2 * tau π z2 z1 * tau π z1 z3 * χ ^ 4 := by
    refine tsum_congr fun z1 => tsum_congr fun z2 => tsum_congr fun z3 => ?_
    exact tsum_arm_four_tuple π χ hχ z1 z3 z2 z3 _
  rw [harm]
  have hpull : (∑' z1 : V, ∑' z2 : V, ∑' z3 : V, tau π y w * tau π w z2 * tau π z2 z1 * tau π z1 z3 * χ ^ 4) =
      (∑' z1 : V, ∑' z2 : V, ∑' z3 : V, tau π y w * tau π w z2 * tau π z2 z1 * tau π z1 z3) * χ ^ 4 := by
    simp only [ENNReal.tsum_mul_right]
  rw [hpull]
  have hchain : (∑' z1 : V, ∑' z2 : V, ∑' z3 : V, tau π y w * tau π w z2 * tau π z2 z1 * tau π z1 z3) =
      χ ^ 3 * iterPow (kernel π) 1 y w := by
    refine Eq.trans (perm12 (fun a b c => tau π y w * tau π w b * tau π b a * tau π a c)) ?_
    simp only [ENNReal.tsum_mul_left, ENNReal.tsum_mul_right, hχ]
    rw [I417FreshTwo.iterPow_one, ← kernel_def]
    ring
  rw [hchain, iterPow_kernel_comm π 1 y w]
  ring

/-- Member `35` of the `q = 4` family: `k1 = (1 : Fin 2)`, `k2 = Sum.inl ((1 : Fin 2))`,
`k3 = Sum.inr false`.  Skeleton path `y – w` (so `ℓ = 1`),
summed-out skeleton vertices `z1, z2, z3` in peel order
`z1, z3, z2`. -/
theorem ev_34 (π : Sym2 V → unitInterval) (y w : V) (χ : ℝ≥0∞)
    (hχ : ∀ v : V, ∑' z : V, tau π v z = χ) :
    (∑' z1 : V, ∑' z2 : V, ∑' z3 : V, ∑' pa : V × V × V × V,
        ∏ i, tau π
          (q4Legs ((1 : Fin 2)) (Sum.inl ((1 : Fin 2))) (Sum.inr false) z1 z2 z3 y w pa.1 pa.2.1 pa.2.2.1 pa.2.2.2 i).1
          (q4Legs ((1 : Fin 2)) (Sum.inl ((1 : Fin 2))) (Sum.inr false) z1 z2 z3 y w pa.1 pa.2.1 pa.2.2.1 pa.2.2.2 i).2) =
      χ ^ 7 * iterPow (kernel π) 1 w y := by
  have hNF : ∀ z1 z2 z3 (pa : V × V × V × V),
      (∏ i, tau π (q4Legs ((1 : Fin 2)) (Sum.inl ((1 : Fin 2))) (Sum.inr false) z1 z2 z3 y w pa.1 pa.2.1 pa.2.2.1 pa.2.2.2 i).1 (q4Legs ((1 : Fin 2)) (Sum.inl ((1 : Fin 2))) (Sum.inr false) z1 z2 z3 y w pa.1 pa.2.1 pa.2.2.1 pa.2.2.2 i).2) = tau π y w * tau π w z2 * tau π z2 z3 * tau π z3 z1 * (tau π z1 pa.1 * tau π z1 pa.2.1 * tau π z2 pa.2.2.1 * tau π z3 pa.2.2.2) := by
    intro z1 z2 z3 pa
    simp [q4Legs, splitAt, baseLegs, Fintype.prod_sum_type, Fin.prod_univ_two]
    all_goals ring
  simp only [hNF]
  have harm : (∑' z1 : V, ∑' z2 : V, ∑' z3 : V,
        (∑' pa : V × V × V × V, tau π y w * tau π w z2 * tau π z2 z3 * tau π z3 z1 * (tau π z1 pa.1 * tau π z1 pa.2.1 * tau π z2 pa.2.2.1 * tau π z3 pa.2.2.2))) =
      ∑' z1 : V, ∑' z2 : V, ∑' z3 : V, tau π y w * tau π w z2 * tau π z2 z3 * tau π z3 z1 * χ ^ 4 := by
    refine tsum_congr fun z1 => tsum_congr fun z2 => tsum_congr fun z3 => ?_
    exact tsum_arm_four_tuple π χ hχ z1 z1 z2 z3 _
  rw [harm]
  have hpull : (∑' z1 : V, ∑' z2 : V, ∑' z3 : V, tau π y w * tau π w z2 * tau π z2 z3 * tau π z3 z1 * χ ^ 4) =
      (∑' z1 : V, ∑' z2 : V, ∑' z3 : V, tau π y w * tau π w z2 * tau π z2 z3 * tau π z3 z1) * χ ^ 4 := by
    simp only [ENNReal.tsum_mul_right]
  rw [hpull]
  have hchain : (∑' z1 : V, ∑' z2 : V, ∑' z3 : V, tau π y w * tau π w z2 * tau π z2 z3 * tau π z3 z1) =
      χ ^ 3 * iterPow (kernel π) 1 y w := by
    refine Eq.trans (perm231 (fun a b c => tau π y w * tau π w b * tau π b c * tau π c a)) ?_
    simp only [ENNReal.tsum_mul_left, ENNReal.tsum_mul_right, hχ]
    rw [I417FreshTwo.iterPow_one, ← kernel_def]
    ring
  rw [hchain, iterPow_kernel_comm π 1 y w]
  ring

/-- Member `36` of the `q = 4` family: `k1 = (1 : Fin 2)`, `k2 = Sum.inl ((1 : Fin 2))`,
`k3 = Sum.inr true`.  Skeleton path `y – w` (so `ℓ = 1`),
summed-out skeleton vertices `z1, z2, z3` in peel order
`z1, z3, z2`. -/
theorem ev_35 (π : Sym2 V → unitInterval) (y w : V) (χ : ℝ≥0∞)
    (hχ : ∀ v : V, ∑' z : V, tau π v z = χ) :
    (∑' z1 : V, ∑' z2 : V, ∑' z3 : V, ∑' pa : V × V × V × V,
        ∏ i, tau π
          (q4Legs ((1 : Fin 2)) (Sum.inl ((1 : Fin 2))) (Sum.inr true) z1 z2 z3 y w pa.1 pa.2.1 pa.2.2.1 pa.2.2.2 i).1
          (q4Legs ((1 : Fin 2)) (Sum.inl ((1 : Fin 2))) (Sum.inr true) z1 z2 z3 y w pa.1 pa.2.1 pa.2.2.1 pa.2.2.2 i).2) =
      χ ^ 7 * iterPow (kernel π) 1 w y := by
  have hNF : ∀ z1 z2 z3 (pa : V × V × V × V),
      (∏ i, tau π (q4Legs ((1 : Fin 2)) (Sum.inl ((1 : Fin 2))) (Sum.inr true) z1 z2 z3 y w pa.1 pa.2.1 pa.2.2.1 pa.2.2.2 i).1 (q4Legs ((1 : Fin 2)) (Sum.inl ((1 : Fin 2))) (Sum.inr true) z1 z2 z3 y w pa.1 pa.2.1 pa.2.2.1 pa.2.2.2 i).2) = tau π y w * tau π w z2 * tau π z2 z3 * tau π z2 z1 * (tau π z1 pa.1 * tau π z1 pa.2.1 * tau π z3 pa.2.2.1 * tau π z3 pa.2.2.2) := by
    intro z1 z2 z3 pa
    simp [q4Legs, splitAt, baseLegs, Fintype.prod_sum_type, Fin.prod_univ_two]
    all_goals ring
  simp only [hNF]
  have harm : (∑' z1 : V, ∑' z2 : V, ∑' z3 : V,
        (∑' pa : V × V × V × V, tau π y w * tau π w z2 * tau π z2 z3 * tau π z2 z1 * (tau π z1 pa.1 * tau π z1 pa.2.1 * tau π z3 pa.2.2.1 * tau π z3 pa.2.2.2))) =
      ∑' z1 : V, ∑' z2 : V, ∑' z3 : V, tau π y w * tau π w z2 * tau π z2 z3 * tau π z2 z1 * χ ^ 4 := by
    refine tsum_congr fun z1 => tsum_congr fun z2 => tsum_congr fun z3 => ?_
    exact tsum_arm_four_tuple π χ hχ z1 z1 z3 z3 _
  rw [harm]
  have hpull : (∑' z1 : V, ∑' z2 : V, ∑' z3 : V, tau π y w * tau π w z2 * tau π z2 z3 * tau π z2 z1 * χ ^ 4) =
      (∑' z1 : V, ∑' z2 : V, ∑' z3 : V, tau π y w * tau π w z2 * tau π z2 z3 * tau π z2 z1) * χ ^ 4 := by
    simp only [ENNReal.tsum_mul_right]
  rw [hpull]
  have hchain : (∑' z1 : V, ∑' z2 : V, ∑' z3 : V, tau π y w * tau π w z2 * tau π z2 z3 * tau π z2 z1) =
      χ ^ 3 * iterPow (kernel π) 1 y w := by
    refine Eq.trans (perm231 (fun a b c => tau π y w * tau π w b * tau π b c * tau π b a)) ?_
    simp only [ENNReal.tsum_mul_left, ENNReal.tsum_mul_right, hχ]
    rw [I417FreshTwo.iterPow_one, ← kernel_def]
    ring
  rw [hchain, iterPow_kernel_comm π 1 y w]
  ring

/-- Member `37` of the `q = 4` family: `k1 = (1 : Fin 2)`, `k2 = Sum.inr false`,
`k3 = Sum.inl (Sum.inl ((0 : Fin 2)))`.  Skeleton path `y – z3 – w` (so `ℓ = 2`),
summed-out skeleton vertices `z1, z2` in peel order
`z2, z1`. -/
theorem ev_36 (π : Sym2 V → unitInterval) (y w : V) (χ : ℝ≥0∞)
    (hχ : ∀ v : V, ∑' z : V, tau π v z = χ) :
    (∑' z1 : V, ∑' z2 : V, ∑' z3 : V, ∑' pa : V × V × V × V,
        ∏ i, tau π
          (q4Legs ((1 : Fin 2)) (Sum.inr false) (Sum.inl (Sum.inl ((0 : Fin 2)))) z1 z2 z3 y w pa.1 pa.2.1 pa.2.2.1 pa.2.2.2 i).1
          (q4Legs ((1 : Fin 2)) (Sum.inr false) (Sum.inl (Sum.inl ((0 : Fin 2)))) z1 z2 z3 y w pa.1 pa.2.1 pa.2.2.1 pa.2.2.2 i).2) =
      χ ^ 6 * iterPow (kernel π) 2 w y := by
  have hNF : ∀ z1 z2 z3 (pa : V × V × V × V),
      (∏ i, tau π (q4Legs ((1 : Fin 2)) (Sum.inr false) (Sum.inl (Sum.inl ((0 : Fin 2)))) z1 z2 z3 y w pa.1 pa.2.1 pa.2.2.1 pa.2.2.2 i).1 (q4Legs ((1 : Fin 2)) (Sum.inr false) (Sum.inl (Sum.inl ((0 : Fin 2)))) z1 z2 z3 y w pa.1 pa.2.1 pa.2.2.1 pa.2.2.2 i).2) = tau π y z3 * tau π z3 w * tau π w z1 * tau π z1 z2 * (tau π z2 pa.1 * tau π z1 pa.2.1 * tau π z2 pa.2.2.1 * tau π z3 pa.2.2.2) := by
    intro z1 z2 z3 pa
    simp [q4Legs, splitAt, baseLegs, Fintype.prod_sum_type, Fin.prod_univ_two]
    all_goals ring
  simp only [hNF]
  have harm : (∑' z1 : V, ∑' z2 : V, ∑' z3 : V,
        (∑' pa : V × V × V × V, tau π y z3 * tau π z3 w * tau π w z1 * tau π z1 z2 * (tau π z2 pa.1 * tau π z1 pa.2.1 * tau π z2 pa.2.2.1 * tau π z3 pa.2.2.2))) =
      ∑' z1 : V, ∑' z2 : V, ∑' z3 : V, tau π y z3 * tau π z3 w * tau π w z1 * tau π z1 z2 * χ ^ 4 := by
    refine tsum_congr fun z1 => tsum_congr fun z2 => tsum_congr fun z3 => ?_
    exact tsum_arm_four_tuple π χ hχ z2 z1 z2 z3 _
  rw [harm]
  have hpull : (∑' z1 : V, ∑' z2 : V, ∑' z3 : V, tau π y z3 * tau π z3 w * tau π w z1 * tau π z1 z2 * χ ^ 4) =
      (∑' z1 : V, ∑' z2 : V, ∑' z3 : V, tau π y z3 * tau π z3 w * tau π w z1 * tau π z1 z2) * χ ^ 4 := by
    simp only [ENNReal.tsum_mul_right]
  rw [hpull]
  have hchain : (∑' z1 : V, ∑' z2 : V, ∑' z3 : V, tau π y z3 * tau π z3 w * tau π w z1 * tau π z1 z2) =
      χ ^ 2 * iterPow (kernel π) 2 y w := by
    refine Eq.trans (perm312 (fun a b c => tau π y c * tau π c w * tau π w a * tau π a b)) ?_
    simp only [ENNReal.tsum_mul_left, ENNReal.tsum_mul_right, hχ, ← I417FreshTwo.iterPow_two_eq]
    ring
  rw [hchain, iterPow_kernel_comm π 2 y w]
  ring

/-- Member `38` of the `q = 4` family: `k1 = (1 : Fin 2)`, `k2 = Sum.inr false`,
`k3 = Sum.inl (Sum.inl ((1 : Fin 2)))`.  Skeleton path `y – w` (so `ℓ = 1`),
summed-out skeleton vertices `z1, z2, z3` in peel order
`z2, z1, z3`. -/
theorem ev_37 (π : Sym2 V → unitInterval) (y w : V) (χ : ℝ≥0∞)
    (hχ : ∀ v : V, ∑' z : V, tau π v z = χ) :
    (∑' z1 : V, ∑' z2 : V, ∑' z3 : V, ∑' pa : V × V × V × V,
        ∏ i, tau π
          (q4Legs ((1 : Fin 2)) (Sum.inr false) (Sum.inl (Sum.inl ((1 : Fin 2)))) z1 z2 z3 y w pa.1 pa.2.1 pa.2.2.1 pa.2.2.2 i).1
          (q4Legs ((1 : Fin 2)) (Sum.inr false) (Sum.inl (Sum.inl ((1 : Fin 2)))) z1 z2 z3 y w pa.1 pa.2.1 pa.2.2.1 pa.2.2.2 i).2) =
      χ ^ 7 * iterPow (kernel π) 1 w y := by
  have hNF : ∀ z1 z2 z3 (pa : V × V × V × V),
      (∏ i, tau π (q4Legs ((1 : Fin 2)) (Sum.inr false) (Sum.inl (Sum.inl ((1 : Fin 2)))) z1 z2 z3 y w pa.1 pa.2.1 pa.2.2.1 pa.2.2.2 i).1 (q4Legs ((1 : Fin 2)) (Sum.inr false) (Sum.inl (Sum.inl ((1 : Fin 2)))) z1 z2 z3 y w pa.1 pa.2.1 pa.2.2.1 pa.2.2.2 i).2) = tau π y w * tau π w z3 * tau π z3 z1 * tau π z1 z2 * (tau π z2 pa.1 * tau π z1 pa.2.1 * tau π z2 pa.2.2.1 * tau π z3 pa.2.2.2) := by
    intro z1 z2 z3 pa
    simp [q4Legs, splitAt, baseLegs, Fintype.prod_sum_type, Fin.prod_univ_two]
    all_goals ring
  simp only [hNF]
  have harm : (∑' z1 : V, ∑' z2 : V, ∑' z3 : V,
        (∑' pa : V × V × V × V, tau π y w * tau π w z3 * tau π z3 z1 * tau π z1 z2 * (tau π z2 pa.1 * tau π z1 pa.2.1 * tau π z2 pa.2.2.1 * tau π z3 pa.2.2.2))) =
      ∑' z1 : V, ∑' z2 : V, ∑' z3 : V, tau π y w * tau π w z3 * tau π z3 z1 * tau π z1 z2 * χ ^ 4 := by
    refine tsum_congr fun z1 => tsum_congr fun z2 => tsum_congr fun z3 => ?_
    exact tsum_arm_four_tuple π χ hχ z2 z1 z2 z3 _
  rw [harm]
  have hpull : (∑' z1 : V, ∑' z2 : V, ∑' z3 : V, tau π y w * tau π w z3 * tau π z3 z1 * tau π z1 z2 * χ ^ 4) =
      (∑' z1 : V, ∑' z2 : V, ∑' z3 : V, tau π y w * tau π w z3 * tau π z3 z1 * tau π z1 z2) * χ ^ 4 := by
    simp only [ENNReal.tsum_mul_right]
  rw [hpull]
  have hchain : (∑' z1 : V, ∑' z2 : V, ∑' z3 : V, tau π y w * tau π w z3 * tau π z3 z1 * tau π z1 z2) =
      χ ^ 3 * iterPow (kernel π) 1 y w := by
    refine Eq.trans (perm312 (fun a b c => tau π y w * tau π w c * tau π c a * tau π a b)) ?_
    simp only [ENNReal.tsum_mul_left, ENNReal.tsum_mul_right, hχ]
    rw [I417FreshTwo.iterPow_one, ← kernel_def]
    ring
  rw [hchain, iterPow_kernel_comm π 1 y w]
  ring

/-- Member `39` of the `q = 4` family: `k1 = (1 : Fin 2)`, `k2 = Sum.inr false`,
`k3 = Sum.inl (Sum.inr false)`.  Skeleton path `y – w` (so `ℓ = 1`),
summed-out skeleton vertices `z1, z2, z3` in peel order
`z2, z3, z1`. -/
theorem ev_38 (π : Sym2 V → unitInterval) (y w : V) (χ : ℝ≥0∞)
    (hχ : ∀ v : V, ∑' z : V, tau π v z = χ) :
    (∑' z1 : V, ∑' z2 : V, ∑' z3 : V, ∑' pa : V × V × V × V,
        ∏ i, tau π
          (q4Legs ((1 : Fin 2)) (Sum.inr false) (Sum.inl (Sum.inr false)) z1 z2 z3 y w pa.1 pa.2.1 pa.2.2.1 pa.2.2.2 i).1
          (q4Legs ((1 : Fin 2)) (Sum.inr false) (Sum.inl (Sum.inr false)) z1 z2 z3 y w pa.1 pa.2.1 pa.2.2.1 pa.2.2.2 i).2) =
      χ ^ 7 * iterPow (kernel π) 1 w y := by
  have hNF : ∀ z1 z2 z3 (pa : V × V × V × V),
      (∏ i, tau π (q4Legs ((1 : Fin 2)) (Sum.inr false) (Sum.inl (Sum.inr false)) z1 z2 z3 y w pa.1 pa.2.1 pa.2.2.1 pa.2.2.2 i).1 (q4Legs ((1 : Fin 2)) (Sum.inr false) (Sum.inl (Sum.inr false)) z1 z2 z3 y w pa.1 pa.2.1 pa.2.2.1 pa.2.2.2 i).2) = tau π y w * tau π w z1 * tau π z1 z3 * tau π z3 z2 * (tau π z2 pa.1 * tau π z1 pa.2.1 * tau π z2 pa.2.2.1 * tau π z3 pa.2.2.2) := by
    intro z1 z2 z3 pa
    simp [q4Legs, splitAt, baseLegs, Fintype.prod_sum_type, Fin.prod_univ_two]
    all_goals ring
  simp only [hNF]
  have harm : (∑' z1 : V, ∑' z2 : V, ∑' z3 : V,
        (∑' pa : V × V × V × V, tau π y w * tau π w z1 * tau π z1 z3 * tau π z3 z2 * (tau π z2 pa.1 * tau π z1 pa.2.1 * tau π z2 pa.2.2.1 * tau π z3 pa.2.2.2))) =
      ∑' z1 : V, ∑' z2 : V, ∑' z3 : V, tau π y w * tau π w z1 * tau π z1 z3 * tau π z3 z2 * χ ^ 4 := by
    refine tsum_congr fun z1 => tsum_congr fun z2 => tsum_congr fun z3 => ?_
    exact tsum_arm_four_tuple π χ hχ z2 z1 z2 z3 _
  rw [harm]
  have hpull : (∑' z1 : V, ∑' z2 : V, ∑' z3 : V, tau π y w * tau π w z1 * tau π z1 z3 * tau π z3 z2 * χ ^ 4) =
      (∑' z1 : V, ∑' z2 : V, ∑' z3 : V, tau π y w * tau π w z1 * tau π z1 z3 * tau π z3 z2) * χ ^ 4 := by
    simp only [ENNReal.tsum_mul_right]
  rw [hpull]
  have hchain : (∑' z1 : V, ∑' z2 : V, ∑' z3 : V, tau π y w * tau π w z1 * tau π z1 z3 * tau π z3 z2) =
      χ ^ 3 * iterPow (kernel π) 1 y w := by
    refine Eq.trans (perm23 (fun a b c => tau π y w * tau π w a * tau π a c * tau π c b)) ?_
    simp only [ENNReal.tsum_mul_left, ENNReal.tsum_mul_right, hχ]
    rw [I417FreshTwo.iterPow_one, ← kernel_def]
    ring
  rw [hchain, iterPow_kernel_comm π 1 y w]
  ring

/-- Member `40` of the `q = 4` family: `k1 = (1 : Fin 2)`, `k2 = Sum.inr false`,
`k3 = Sum.inl (Sum.inr true)`.  Skeleton path `y – w` (so `ℓ = 1`),
summed-out skeleton vertices `z1, z2, z3` in peel order
`z2, z3, z1`. -/
theorem ev_39 (π : Sym2 V → unitInterval) (y w : V) (χ : ℝ≥0∞)
    (hχ : ∀ v : V, ∑' z : V, tau π v z = χ) :
    (∑' z1 : V, ∑' z2 : V, ∑' z3 : V, ∑' pa : V × V × V × V,
        ∏ i, tau π
          (q4Legs ((1 : Fin 2)) (Sum.inr false) (Sum.inl (Sum.inr true)) z1 z2 z3 y w pa.1 pa.2.1 pa.2.2.1 pa.2.2.2 i).1
          (q4Legs ((1 : Fin 2)) (Sum.inr false) (Sum.inl (Sum.inr true)) z1 z2 z3 y w pa.1 pa.2.1 pa.2.2.1 pa.2.2.2 i).2) =
      χ ^ 7 * iterPow (kernel π) 1 w y := by
  have hNF : ∀ z1 z2 z3 (pa : V × V × V × V),
      (∏ i, tau π (q4Legs ((1 : Fin 2)) (Sum.inr false) (Sum.inl (Sum.inr true)) z1 z2 z3 y w pa.1 pa.2.1 pa.2.2.1 pa.2.2.2 i).1 (q4Legs ((1 : Fin 2)) (Sum.inr false) (Sum.inl (Sum.inr true)) z1 z2 z3 y w pa.1 pa.2.1 pa.2.2.1 pa.2.2.2 i).2) = tau π y w * tau π w z1 * tau π z1 z3 * tau π z1 z2 * (tau π z2 pa.1 * tau π z3 pa.2.1 * tau π z2 pa.2.2.1 * tau π z3 pa.2.2.2) := by
    intro z1 z2 z3 pa
    simp [q4Legs, splitAt, baseLegs, Fintype.prod_sum_type, Fin.prod_univ_two]
    all_goals ring
  simp only [hNF]
  have harm : (∑' z1 : V, ∑' z2 : V, ∑' z3 : V,
        (∑' pa : V × V × V × V, tau π y w * tau π w z1 * tau π z1 z3 * tau π z1 z2 * (tau π z2 pa.1 * tau π z3 pa.2.1 * tau π z2 pa.2.2.1 * tau π z3 pa.2.2.2))) =
      ∑' z1 : V, ∑' z2 : V, ∑' z3 : V, tau π y w * tau π w z1 * tau π z1 z3 * tau π z1 z2 * χ ^ 4 := by
    refine tsum_congr fun z1 => tsum_congr fun z2 => tsum_congr fun z3 => ?_
    exact tsum_arm_four_tuple π χ hχ z2 z3 z2 z3 _
  rw [harm]
  have hpull : (∑' z1 : V, ∑' z2 : V, ∑' z3 : V, tau π y w * tau π w z1 * tau π z1 z3 * tau π z1 z2 * χ ^ 4) =
      (∑' z1 : V, ∑' z2 : V, ∑' z3 : V, tau π y w * tau π w z1 * tau π z1 z3 * tau π z1 z2) * χ ^ 4 := by
    simp only [ENNReal.tsum_mul_right]
  rw [hpull]
  have hchain : (∑' z1 : V, ∑' z2 : V, ∑' z3 : V, tau π y w * tau π w z1 * tau π z1 z3 * tau π z1 z2) =
      χ ^ 3 * iterPow (kernel π) 1 y w := by
    refine Eq.trans (perm23 (fun a b c => tau π y w * tau π w a * tau π a c * tau π a b)) ?_
    simp only [ENNReal.tsum_mul_left, ENNReal.tsum_mul_right, hχ]
    rw [I417FreshTwo.iterPow_one, ← kernel_def]
    ring
  rw [hchain, iterPow_kernel_comm π 1 y w]
  ring

/-- Member `41` of the `q = 4` family: `k1 = (1 : Fin 2)`, `k2 = Sum.inr false`,
`k3 = Sum.inr false`.  Skeleton path `y – w` (so `ℓ = 1`),
summed-out skeleton vertices `z1, z2, z3` in peel order
`z3, z2, z1`. -/
theorem ev_40 (π : Sym2 V → unitInterval) (y w : V) (χ : ℝ≥0∞)
    (hχ : ∀ v : V, ∑' z : V, tau π v z = χ) :
    (∑' z1 : V, ∑' z2 : V, ∑' z3 : V, ∑' pa : V × V × V × V,
        ∏ i, tau π
          (q4Legs ((1 : Fin 2)) (Sum.inr false) (Sum.inr false) z1 z2 z3 y w pa.1 pa.2.1 pa.2.2.1 pa.2.2.2 i).1
          (q4Legs ((1 : Fin 2)) (Sum.inr false) (Sum.inr false) z1 z2 z3 y w pa.1 pa.2.1 pa.2.2.1 pa.2.2.2 i).2) =
      χ ^ 7 * iterPow (kernel π) 1 w y := by
  have hNF : ∀ z1 z2 z3 (pa : V × V × V × V),
      (∏ i, tau π (q4Legs ((1 : Fin 2)) (Sum.inr false) (Sum.inr false) z1 z2 z3 y w pa.1 pa.2.1 pa.2.2.1 pa.2.2.2 i).1 (q4Legs ((1 : Fin 2)) (Sum.inr false) (Sum.inr false) z1 z2 z3 y w pa.1 pa.2.1 pa.2.2.1 pa.2.2.2 i).2) = tau π y w * tau π w z1 * tau π z1 z2 * tau π z2 z3 * (tau π z3 pa.1 * tau π z1 pa.2.1 * tau π z2 pa.2.2.1 * tau π z3 pa.2.2.2) := by
    intro z1 z2 z3 pa
    simp [q4Legs, splitAt, baseLegs, Fintype.prod_sum_type, Fin.prod_univ_two]
    all_goals ring
  simp only [hNF]
  have harm : (∑' z1 : V, ∑' z2 : V, ∑' z3 : V,
        (∑' pa : V × V × V × V, tau π y w * tau π w z1 * tau π z1 z2 * tau π z2 z3 * (tau π z3 pa.1 * tau π z1 pa.2.1 * tau π z2 pa.2.2.1 * tau π z3 pa.2.2.2))) =
      ∑' z1 : V, ∑' z2 : V, ∑' z3 : V, tau π y w * tau π w z1 * tau π z1 z2 * tau π z2 z3 * χ ^ 4 := by
    refine tsum_congr fun z1 => tsum_congr fun z2 => tsum_congr fun z3 => ?_
    exact tsum_arm_four_tuple π χ hχ z3 z1 z2 z3 _
  rw [harm]
  have hpull : (∑' z1 : V, ∑' z2 : V, ∑' z3 : V, tau π y w * tau π w z1 * tau π z1 z2 * tau π z2 z3 * χ ^ 4) =
      (∑' z1 : V, ∑' z2 : V, ∑' z3 : V, tau π y w * tau π w z1 * tau π z1 z2 * tau π z2 z3) * χ ^ 4 := by
    simp only [ENNReal.tsum_mul_right]
  rw [hpull]
  have hchain : (∑' z1 : V, ∑' z2 : V, ∑' z3 : V, tau π y w * tau π w z1 * tau π z1 z2 * tau π z2 z3) =
      χ ^ 3 * iterPow (kernel π) 1 y w := by
    simp only [ENNReal.tsum_mul_left, ENNReal.tsum_mul_right, hχ]
    rw [I417FreshTwo.iterPow_one, ← kernel_def]
    ring
  rw [hchain, iterPow_kernel_comm π 1 y w]
  ring

/-- Member `42` of the `q = 4` family: `k1 = (1 : Fin 2)`, `k2 = Sum.inr false`,
`k3 = Sum.inr true`.  Skeleton path `y – w` (so `ℓ = 1`),
summed-out skeleton vertices `z1, z2, z3` in peel order
`z3, z2, z1`. -/
theorem ev_41 (π : Sym2 V → unitInterval) (y w : V) (χ : ℝ≥0∞)
    (hχ : ∀ v : V, ∑' z : V, tau π v z = χ) :
    (∑' z1 : V, ∑' z2 : V, ∑' z3 : V, ∑' pa : V × V × V × V,
        ∏ i, tau π
          (q4Legs ((1 : Fin 2)) (Sum.inr false) (Sum.inr true) z1 z2 z3 y w pa.1 pa.2.1 pa.2.2.1 pa.2.2.2 i).1
          (q4Legs ((1 : Fin 2)) (Sum.inr false) (Sum.inr true) z1 z2 z3 y w pa.1 pa.2.1 pa.2.2.1 pa.2.2.2 i).2) =
      χ ^ 7 * iterPow (kernel π) 1 w y := by
  have hNF : ∀ z1 z2 z3 (pa : V × V × V × V),
      (∏ i, tau π (q4Legs ((1 : Fin 2)) (Sum.inr false) (Sum.inr true) z1 z2 z3 y w pa.1 pa.2.1 pa.2.2.1 pa.2.2.2 i).1 (q4Legs ((1 : Fin 2)) (Sum.inr false) (Sum.inr true) z1 z2 z3 y w pa.1 pa.2.1 pa.2.2.1 pa.2.2.2 i).2) = tau π y w * tau π w z1 * tau π z1 z2 * tau π z2 z3 * (tau π z2 pa.1 * tau π z1 pa.2.1 * tau π z3 pa.2.2.1 * tau π z3 pa.2.2.2) := by
    intro z1 z2 z3 pa
    simp [q4Legs, splitAt, baseLegs, Fintype.prod_sum_type, Fin.prod_univ_two]
    all_goals ring
  simp only [hNF]
  have harm : (∑' z1 : V, ∑' z2 : V, ∑' z3 : V,
        (∑' pa : V × V × V × V, tau π y w * tau π w z1 * tau π z1 z2 * tau π z2 z3 * (tau π z2 pa.1 * tau π z1 pa.2.1 * tau π z3 pa.2.2.1 * tau π z3 pa.2.2.2))) =
      ∑' z1 : V, ∑' z2 : V, ∑' z3 : V, tau π y w * tau π w z1 * tau π z1 z2 * tau π z2 z3 * χ ^ 4 := by
    refine tsum_congr fun z1 => tsum_congr fun z2 => tsum_congr fun z3 => ?_
    exact tsum_arm_four_tuple π χ hχ z2 z1 z3 z3 _
  rw [harm]
  have hpull : (∑' z1 : V, ∑' z2 : V, ∑' z3 : V, tau π y w * tau π w z1 * tau π z1 z2 * tau π z2 z3 * χ ^ 4) =
      (∑' z1 : V, ∑' z2 : V, ∑' z3 : V, tau π y w * tau π w z1 * tau π z1 z2 * tau π z2 z3) * χ ^ 4 := by
    simp only [ENNReal.tsum_mul_right]
  rw [hpull]
  have hchain : (∑' z1 : V, ∑' z2 : V, ∑' z3 : V, tau π y w * tau π w z1 * tau π z1 z2 * tau π z2 z3) =
      χ ^ 3 * iterPow (kernel π) 1 y w := by
    simp only [ENNReal.tsum_mul_left, ENNReal.tsum_mul_right, hχ]
    rw [I417FreshTwo.iterPow_one, ← kernel_def]
    ring
  rw [hchain, iterPow_kernel_comm π 1 y w]
  ring

/-- Member `43` of the `q = 4` family: `k1 = (1 : Fin 2)`, `k2 = Sum.inr true`,
`k3 = Sum.inl (Sum.inl ((0 : Fin 2)))`.  Skeleton path `y – z3 – w` (so `ℓ = 2`),
summed-out skeleton vertices `z1, z2` in peel order
`z2, z1`. -/
theorem ev_42 (π : Sym2 V → unitInterval) (y w : V) (χ : ℝ≥0∞)
    (hχ : ∀ v : V, ∑' z : V, tau π v z = χ) :
    (∑' z1 : V, ∑' z2 : V, ∑' z3 : V, ∑' pa : V × V × V × V,
        ∏ i, tau π
          (q4Legs ((1 : Fin 2)) (Sum.inr true) (Sum.inl (Sum.inl ((0 : Fin 2)))) z1 z2 z3 y w pa.1 pa.2.1 pa.2.2.1 pa.2.2.2 i).1
          (q4Legs ((1 : Fin 2)) (Sum.inr true) (Sum.inl (Sum.inl ((0 : Fin 2)))) z1 z2 z3 y w pa.1 pa.2.1 pa.2.2.1 pa.2.2.2 i).2) =
      χ ^ 6 * iterPow (kernel π) 2 w y := by
  have hNF : ∀ z1 z2 z3 (pa : V × V × V × V),
      (∏ i, tau π (q4Legs ((1 : Fin 2)) (Sum.inr true) (Sum.inl (Sum.inl ((0 : Fin 2)))) z1 z2 z3 y w pa.1 pa.2.1 pa.2.2.1 pa.2.2.2 i).1 (q4Legs ((1 : Fin 2)) (Sum.inr true) (Sum.inl (Sum.inl ((0 : Fin 2)))) z1 z2 z3 y w pa.1 pa.2.1 pa.2.2.1 pa.2.2.2 i).2) = tau π y z3 * tau π z3 w * tau π w z1 * tau π z1 z2 * (tau π z1 pa.1 * tau π z2 pa.2.1 * tau π z2 pa.2.2.1 * tau π z3 pa.2.2.2) := by
    intro z1 z2 z3 pa
    simp [q4Legs, splitAt, baseLegs, Fintype.prod_sum_type, Fin.prod_univ_two]
    all_goals ring
  simp only [hNF]
  have harm : (∑' z1 : V, ∑' z2 : V, ∑' z3 : V,
        (∑' pa : V × V × V × V, tau π y z3 * tau π z3 w * tau π w z1 * tau π z1 z2 * (tau π z1 pa.1 * tau π z2 pa.2.1 * tau π z2 pa.2.2.1 * tau π z3 pa.2.2.2))) =
      ∑' z1 : V, ∑' z2 : V, ∑' z3 : V, tau π y z3 * tau π z3 w * tau π w z1 * tau π z1 z2 * χ ^ 4 := by
    refine tsum_congr fun z1 => tsum_congr fun z2 => tsum_congr fun z3 => ?_
    exact tsum_arm_four_tuple π χ hχ z1 z2 z2 z3 _
  rw [harm]
  have hpull : (∑' z1 : V, ∑' z2 : V, ∑' z3 : V, tau π y z3 * tau π z3 w * tau π w z1 * tau π z1 z2 * χ ^ 4) =
      (∑' z1 : V, ∑' z2 : V, ∑' z3 : V, tau π y z3 * tau π z3 w * tau π w z1 * tau π z1 z2) * χ ^ 4 := by
    simp only [ENNReal.tsum_mul_right]
  rw [hpull]
  have hchain : (∑' z1 : V, ∑' z2 : V, ∑' z3 : V, tau π y z3 * tau π z3 w * tau π w z1 * tau π z1 z2) =
      χ ^ 2 * iterPow (kernel π) 2 y w := by
    refine Eq.trans (perm312 (fun a b c => tau π y c * tau π c w * tau π w a * tau π a b)) ?_
    simp only [ENNReal.tsum_mul_left, ENNReal.tsum_mul_right, hχ, ← I417FreshTwo.iterPow_two_eq]
    ring
  rw [hchain, iterPow_kernel_comm π 2 y w]
  ring

/-- Member `44` of the `q = 4` family: `k1 = (1 : Fin 2)`, `k2 = Sum.inr true`,
`k3 = Sum.inl (Sum.inl ((1 : Fin 2)))`.  Skeleton path `y – w` (so `ℓ = 1`),
summed-out skeleton vertices `z1, z2, z3` in peel order
`z2, z1, z3`. -/
theorem ev_43 (π : Sym2 V → unitInterval) (y w : V) (χ : ℝ≥0∞)
    (hχ : ∀ v : V, ∑' z : V, tau π v z = χ) :
    (∑' z1 : V, ∑' z2 : V, ∑' z3 : V, ∑' pa : V × V × V × V,
        ∏ i, tau π
          (q4Legs ((1 : Fin 2)) (Sum.inr true) (Sum.inl (Sum.inl ((1 : Fin 2)))) z1 z2 z3 y w pa.1 pa.2.1 pa.2.2.1 pa.2.2.2 i).1
          (q4Legs ((1 : Fin 2)) (Sum.inr true) (Sum.inl (Sum.inl ((1 : Fin 2)))) z1 z2 z3 y w pa.1 pa.2.1 pa.2.2.1 pa.2.2.2 i).2) =
      χ ^ 7 * iterPow (kernel π) 1 w y := by
  have hNF : ∀ z1 z2 z3 (pa : V × V × V × V),
      (∏ i, tau π (q4Legs ((1 : Fin 2)) (Sum.inr true) (Sum.inl (Sum.inl ((1 : Fin 2)))) z1 z2 z3 y w pa.1 pa.2.1 pa.2.2.1 pa.2.2.2 i).1 (q4Legs ((1 : Fin 2)) (Sum.inr true) (Sum.inl (Sum.inl ((1 : Fin 2)))) z1 z2 z3 y w pa.1 pa.2.1 pa.2.2.1 pa.2.2.2 i).2) = tau π y w * tau π w z3 * tau π z3 z1 * tau π z1 z2 * (tau π z1 pa.1 * tau π z2 pa.2.1 * tau π z2 pa.2.2.1 * tau π z3 pa.2.2.2) := by
    intro z1 z2 z3 pa
    simp [q4Legs, splitAt, baseLegs, Fintype.prod_sum_type, Fin.prod_univ_two]
    all_goals ring
  simp only [hNF]
  have harm : (∑' z1 : V, ∑' z2 : V, ∑' z3 : V,
        (∑' pa : V × V × V × V, tau π y w * tau π w z3 * tau π z3 z1 * tau π z1 z2 * (tau π z1 pa.1 * tau π z2 pa.2.1 * tau π z2 pa.2.2.1 * tau π z3 pa.2.2.2))) =
      ∑' z1 : V, ∑' z2 : V, ∑' z3 : V, tau π y w * tau π w z3 * tau π z3 z1 * tau π z1 z2 * χ ^ 4 := by
    refine tsum_congr fun z1 => tsum_congr fun z2 => tsum_congr fun z3 => ?_
    exact tsum_arm_four_tuple π χ hχ z1 z2 z2 z3 _
  rw [harm]
  have hpull : (∑' z1 : V, ∑' z2 : V, ∑' z3 : V, tau π y w * tau π w z3 * tau π z3 z1 * tau π z1 z2 * χ ^ 4) =
      (∑' z1 : V, ∑' z2 : V, ∑' z3 : V, tau π y w * tau π w z3 * tau π z3 z1 * tau π z1 z2) * χ ^ 4 := by
    simp only [ENNReal.tsum_mul_right]
  rw [hpull]
  have hchain : (∑' z1 : V, ∑' z2 : V, ∑' z3 : V, tau π y w * tau π w z3 * tau π z3 z1 * tau π z1 z2) =
      χ ^ 3 * iterPow (kernel π) 1 y w := by
    refine Eq.trans (perm312 (fun a b c => tau π y w * tau π w c * tau π c a * tau π a b)) ?_
    simp only [ENNReal.tsum_mul_left, ENNReal.tsum_mul_right, hχ]
    rw [I417FreshTwo.iterPow_one, ← kernel_def]
    ring
  rw [hchain, iterPow_kernel_comm π 1 y w]
  ring

/-- Member `45` of the `q = 4` family: `k1 = (1 : Fin 2)`, `k2 = Sum.inr true`,
`k3 = Sum.inl (Sum.inr false)`.  Skeleton path `y – w` (so `ℓ = 1`),
summed-out skeleton vertices `z1, z2, z3` in peel order
`z2, z3, z1`. -/
theorem ev_44 (π : Sym2 V → unitInterval) (y w : V) (χ : ℝ≥0∞)
    (hχ : ∀ v : V, ∑' z : V, tau π v z = χ) :
    (∑' z1 : V, ∑' z2 : V, ∑' z3 : V, ∑' pa : V × V × V × V,
        ∏ i, tau π
          (q4Legs ((1 : Fin 2)) (Sum.inr true) (Sum.inl (Sum.inr false)) z1 z2 z3 y w pa.1 pa.2.1 pa.2.2.1 pa.2.2.2 i).1
          (q4Legs ((1 : Fin 2)) (Sum.inr true) (Sum.inl (Sum.inr false)) z1 z2 z3 y w pa.1 pa.2.1 pa.2.2.1 pa.2.2.2 i).2) =
      χ ^ 7 * iterPow (kernel π) 1 w y := by
  have hNF : ∀ z1 z2 z3 (pa : V × V × V × V),
      (∏ i, tau π (q4Legs ((1 : Fin 2)) (Sum.inr true) (Sum.inl (Sum.inr false)) z1 z2 z3 y w pa.1 pa.2.1 pa.2.2.1 pa.2.2.2 i).1 (q4Legs ((1 : Fin 2)) (Sum.inr true) (Sum.inl (Sum.inr false)) z1 z2 z3 y w pa.1 pa.2.1 pa.2.2.1 pa.2.2.2 i).2) = tau π y w * tau π w z1 * tau π z1 z3 * tau π z1 z2 * (tau π z3 pa.1 * tau π z2 pa.2.1 * tau π z2 pa.2.2.1 * tau π z3 pa.2.2.2) := by
    intro z1 z2 z3 pa
    simp [q4Legs, splitAt, baseLegs, Fintype.prod_sum_type, Fin.prod_univ_two]
    all_goals ring
  simp only [hNF]
  have harm : (∑' z1 : V, ∑' z2 : V, ∑' z3 : V,
        (∑' pa : V × V × V × V, tau π y w * tau π w z1 * tau π z1 z3 * tau π z1 z2 * (tau π z3 pa.1 * tau π z2 pa.2.1 * tau π z2 pa.2.2.1 * tau π z3 pa.2.2.2))) =
      ∑' z1 : V, ∑' z2 : V, ∑' z3 : V, tau π y w * tau π w z1 * tau π z1 z3 * tau π z1 z2 * χ ^ 4 := by
    refine tsum_congr fun z1 => tsum_congr fun z2 => tsum_congr fun z3 => ?_
    exact tsum_arm_four_tuple π χ hχ z3 z2 z2 z3 _
  rw [harm]
  have hpull : (∑' z1 : V, ∑' z2 : V, ∑' z3 : V, tau π y w * tau π w z1 * tau π z1 z3 * tau π z1 z2 * χ ^ 4) =
      (∑' z1 : V, ∑' z2 : V, ∑' z3 : V, tau π y w * tau π w z1 * tau π z1 z3 * tau π z1 z2) * χ ^ 4 := by
    simp only [ENNReal.tsum_mul_right]
  rw [hpull]
  have hchain : (∑' z1 : V, ∑' z2 : V, ∑' z3 : V, tau π y w * tau π w z1 * tau π z1 z3 * tau π z1 z2) =
      χ ^ 3 * iterPow (kernel π) 1 y w := by
    refine Eq.trans (perm23 (fun a b c => tau π y w * tau π w a * tau π a c * tau π a b)) ?_
    simp only [ENNReal.tsum_mul_left, ENNReal.tsum_mul_right, hχ]
    rw [I417FreshTwo.iterPow_one, ← kernel_def]
    ring
  rw [hchain, iterPow_kernel_comm π 1 y w]
  ring

/-- Member `46` of the `q = 4` family: `k1 = (1 : Fin 2)`, `k2 = Sum.inr true`,
`k3 = Sum.inl (Sum.inr true)`.  Skeleton path `y – w` (so `ℓ = 1`),
summed-out skeleton vertices `z1, z2, z3` in peel order
`z2, z3, z1`. -/
theorem ev_45 (π : Sym2 V → unitInterval) (y w : V) (χ : ℝ≥0∞)
    (hχ : ∀ v : V, ∑' z : V, tau π v z = χ) :
    (∑' z1 : V, ∑' z2 : V, ∑' z3 : V, ∑' pa : V × V × V × V,
        ∏ i, tau π
          (q4Legs ((1 : Fin 2)) (Sum.inr true) (Sum.inl (Sum.inr true)) z1 z2 z3 y w pa.1 pa.2.1 pa.2.2.1 pa.2.2.2 i).1
          (q4Legs ((1 : Fin 2)) (Sum.inr true) (Sum.inl (Sum.inr true)) z1 z2 z3 y w pa.1 pa.2.1 pa.2.2.1 pa.2.2.2 i).2) =
      χ ^ 7 * iterPow (kernel π) 1 w y := by
  have hNF : ∀ z1 z2 z3 (pa : V × V × V × V),
      (∏ i, tau π (q4Legs ((1 : Fin 2)) (Sum.inr true) (Sum.inl (Sum.inr true)) z1 z2 z3 y w pa.1 pa.2.1 pa.2.2.1 pa.2.2.2 i).1 (q4Legs ((1 : Fin 2)) (Sum.inr true) (Sum.inl (Sum.inr true)) z1 z2 z3 y w pa.1 pa.2.1 pa.2.2.1 pa.2.2.2 i).2) = tau π y w * tau π w z1 * tau π z1 z3 * tau π z3 z2 * (tau π z1 pa.1 * tau π z2 pa.2.1 * tau π z2 pa.2.2.1 * tau π z3 pa.2.2.2) := by
    intro z1 z2 z3 pa
    simp [q4Legs, splitAt, baseLegs, Fintype.prod_sum_type, Fin.prod_univ_two]
    all_goals ring
  simp only [hNF]
  have harm : (∑' z1 : V, ∑' z2 : V, ∑' z3 : V,
        (∑' pa : V × V × V × V, tau π y w * tau π w z1 * tau π z1 z3 * tau π z3 z2 * (tau π z1 pa.1 * tau π z2 pa.2.1 * tau π z2 pa.2.2.1 * tau π z3 pa.2.2.2))) =
      ∑' z1 : V, ∑' z2 : V, ∑' z3 : V, tau π y w * tau π w z1 * tau π z1 z3 * tau π z3 z2 * χ ^ 4 := by
    refine tsum_congr fun z1 => tsum_congr fun z2 => tsum_congr fun z3 => ?_
    exact tsum_arm_four_tuple π χ hχ z1 z2 z2 z3 _
  rw [harm]
  have hpull : (∑' z1 : V, ∑' z2 : V, ∑' z3 : V, tau π y w * tau π w z1 * tau π z1 z3 * tau π z3 z2 * χ ^ 4) =
      (∑' z1 : V, ∑' z2 : V, ∑' z3 : V, tau π y w * tau π w z1 * tau π z1 z3 * tau π z3 z2) * χ ^ 4 := by
    simp only [ENNReal.tsum_mul_right]
  rw [hpull]
  have hchain : (∑' z1 : V, ∑' z2 : V, ∑' z3 : V, tau π y w * tau π w z1 * tau π z1 z3 * tau π z3 z2) =
      χ ^ 3 * iterPow (kernel π) 1 y w := by
    refine Eq.trans (perm23 (fun a b c => tau π y w * tau π w a * tau π a c * tau π c b)) ?_
    simp only [ENNReal.tsum_mul_left, ENNReal.tsum_mul_right, hχ]
    rw [I417FreshTwo.iterPow_one, ← kernel_def]
    ring
  rw [hchain, iterPow_kernel_comm π 1 y w]
  ring

/-- Member `47` of the `q = 4` family: `k1 = (1 : Fin 2)`, `k2 = Sum.inr true`,
`k3 = Sum.inr false`.  Skeleton path `y – w` (so `ℓ = 1`),
summed-out skeleton vertices `z1, z2, z3` in peel order
`z3, z2, z1`. -/
theorem ev_46 (π : Sym2 V → unitInterval) (y w : V) (χ : ℝ≥0∞)
    (hχ : ∀ v : V, ∑' z : V, tau π v z = χ) :
    (∑' z1 : V, ∑' z2 : V, ∑' z3 : V, ∑' pa : V × V × V × V,
        ∏ i, tau π
          (q4Legs ((1 : Fin 2)) (Sum.inr true) (Sum.inr false) z1 z2 z3 y w pa.1 pa.2.1 pa.2.2.1 pa.2.2.2 i).1
          (q4Legs ((1 : Fin 2)) (Sum.inr true) (Sum.inr false) z1 z2 z3 y w pa.1 pa.2.1 pa.2.2.1 pa.2.2.2 i).2) =
      χ ^ 7 * iterPow (kernel π) 1 w y := by
  have hNF : ∀ z1 z2 z3 (pa : V × V × V × V),
      (∏ i, tau π (q4Legs ((1 : Fin 2)) (Sum.inr true) (Sum.inr false) z1 z2 z3 y w pa.1 pa.2.1 pa.2.2.1 pa.2.2.2 i).1 (q4Legs ((1 : Fin 2)) (Sum.inr true) (Sum.inr false) z1 z2 z3 y w pa.1 pa.2.1 pa.2.2.1 pa.2.2.2 i).2) = tau π y w * tau π w z1 * tau π z1 z2 * tau π z2 z3 * (tau π z1 pa.1 * tau π z3 pa.2.1 * tau π z2 pa.2.2.1 * tau π z3 pa.2.2.2) := by
    intro z1 z2 z3 pa
    simp [q4Legs, splitAt, baseLegs, Fintype.prod_sum_type, Fin.prod_univ_two]
    all_goals ring
  simp only [hNF]
  have harm : (∑' z1 : V, ∑' z2 : V, ∑' z3 : V,
        (∑' pa : V × V × V × V, tau π y w * tau π w z1 * tau π z1 z2 * tau π z2 z3 * (tau π z1 pa.1 * tau π z3 pa.2.1 * tau π z2 pa.2.2.1 * tau π z3 pa.2.2.2))) =
      ∑' z1 : V, ∑' z2 : V, ∑' z3 : V, tau π y w * tau π w z1 * tau π z1 z2 * tau π z2 z3 * χ ^ 4 := by
    refine tsum_congr fun z1 => tsum_congr fun z2 => tsum_congr fun z3 => ?_
    exact tsum_arm_four_tuple π χ hχ z1 z3 z2 z3 _
  rw [harm]
  have hpull : (∑' z1 : V, ∑' z2 : V, ∑' z3 : V, tau π y w * tau π w z1 * tau π z1 z2 * tau π z2 z3 * χ ^ 4) =
      (∑' z1 : V, ∑' z2 : V, ∑' z3 : V, tau π y w * tau π w z1 * tau π z1 z2 * tau π z2 z3) * χ ^ 4 := by
    simp only [ENNReal.tsum_mul_right]
  rw [hpull]
  have hchain : (∑' z1 : V, ∑' z2 : V, ∑' z3 : V, tau π y w * tau π w z1 * tau π z1 z2 * tau π z2 z3) =
      χ ^ 3 * iterPow (kernel π) 1 y w := by
    simp only [ENNReal.tsum_mul_left, ENNReal.tsum_mul_right, hχ]
    rw [I417FreshTwo.iterPow_one, ← kernel_def]
    ring
  rw [hchain, iterPow_kernel_comm π 1 y w]
  ring

/-- Member `48` of the `q = 4` family: `k1 = (1 : Fin 2)`, `k2 = Sum.inr true`,
`k3 = Sum.inr true`.  Skeleton path `y – w` (so `ℓ = 1`),
summed-out skeleton vertices `z1, z2, z3` in peel order
`z3, z2, z1`. -/
theorem ev_47 (π : Sym2 V → unitInterval) (y w : V) (χ : ℝ≥0∞)
    (hχ : ∀ v : V, ∑' z : V, tau π v z = χ) :
    (∑' z1 : V, ∑' z2 : V, ∑' z3 : V, ∑' pa : V × V × V × V,
        ∏ i, tau π
          (q4Legs ((1 : Fin 2)) (Sum.inr true) (Sum.inr true) z1 z2 z3 y w pa.1 pa.2.1 pa.2.2.1 pa.2.2.2 i).1
          (q4Legs ((1 : Fin 2)) (Sum.inr true) (Sum.inr true) z1 z2 z3 y w pa.1 pa.2.1 pa.2.2.1 pa.2.2.2 i).2) =
      χ ^ 7 * iterPow (kernel π) 1 w y := by
  have hNF : ∀ z1 z2 z3 (pa : V × V × V × V),
      (∏ i, tau π (q4Legs ((1 : Fin 2)) (Sum.inr true) (Sum.inr true) z1 z2 z3 y w pa.1 pa.2.1 pa.2.2.1 pa.2.2.2 i).1 (q4Legs ((1 : Fin 2)) (Sum.inr true) (Sum.inr true) z1 z2 z3 y w pa.1 pa.2.1 pa.2.2.1 pa.2.2.2 i).2) = tau π y w * tau π w z1 * tau π z1 z2 * tau π z2 z3 * (tau π z1 pa.1 * tau π z2 pa.2.1 * tau π z3 pa.2.2.1 * tau π z3 pa.2.2.2) := by
    intro z1 z2 z3 pa
    simp [q4Legs, splitAt, baseLegs, Fintype.prod_sum_type, Fin.prod_univ_two]
    all_goals ring
  simp only [hNF]
  have harm : (∑' z1 : V, ∑' z2 : V, ∑' z3 : V,
        (∑' pa : V × V × V × V, tau π y w * tau π w z1 * tau π z1 z2 * tau π z2 z3 * (tau π z1 pa.1 * tau π z2 pa.2.1 * tau π z3 pa.2.2.1 * tau π z3 pa.2.2.2))) =
      ∑' z1 : V, ∑' z2 : V, ∑' z3 : V, tau π y w * tau π w z1 * tau π z1 z2 * tau π z2 z3 * χ ^ 4 := by
    refine tsum_congr fun z1 => tsum_congr fun z2 => tsum_congr fun z3 => ?_
    exact tsum_arm_four_tuple π χ hχ z1 z2 z3 z3 _
  rw [harm]
  have hpull : (∑' z1 : V, ∑' z2 : V, ∑' z3 : V, tau π y w * tau π w z1 * tau π z1 z2 * tau π z2 z3 * χ ^ 4) =
      (∑' z1 : V, ∑' z2 : V, ∑' z3 : V, tau π y w * tau π w z1 * tau π z1 z2 * tau π z2 z3) * χ ^ 4 := by
    simp only [ENNReal.tsum_mul_right]
  rw [hpull]
  have hchain : (∑' z1 : V, ∑' z2 : V, ∑' z3 : V, tau π y w * tau π w z1 * tau π z1 z2 * tau π z2 z3) =
      χ ^ 3 * iterPow (kernel π) 1 y w := by
    simp only [ENNReal.tsum_mul_left, ENNReal.tsum_mul_right, hχ]
    rw [I417FreshTwo.iterPow_one, ← kernel_def]
    ring
  rw [hchain, iterPow_kernel_comm π 1 y w]
  ring

end PercLib.CriticalLRP.I417FreshFour.Eval
