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

public import PercLib.CriticalLRP.Correlation.I417.Fresh.Four.Refined.Bound
public import PercLib.CriticalLRP.Correlation.I417.Fresh.Two.Poly.Main

/-!
# Engine lemmas for the summed `q = 4` fresh-diagram evaluation

Source: T. Hutchcroft, *Critical long-range percolation I: High effective dimension*,
arXiv:2508.18807v1, Lemma I.4.17 and its proof (supplied paper text pp. 45--46): the two-copy
expansion produces tree diagrams with `2p + 2q + 1` edges in total, some number
`3 ≤ ℓ ≤ p+q+1` of them on the path connecting `x` and `y`.

This file contains the **diagram-evaluation engine** used by `Q4Eval.Branch` and
`Q4Eval.Summed`: every `q = 4` member of the accepted fresh cover `q4Shape` is a rooted tree with
nine syntactic vertices `{y, w, g j, g i1, g i2, g i3, z1, z2, z3}` and eight legs, whose skeleton
(the four legs not incident to an arm) is a path through `y` and `w`.  Summing the
four arms out gives `χ⁴` (the **constant row sum**, one free end per arm), leaving a chain of
four legs through the three summed attachment vertices, with `w` in position `ℓ ∈ {1,2,3,4}`:

* the `ℓ` legs from `y` to `w` compose into `T^ℓ = iterPow (kernel π) ℓ`,
* each of the remaining `4 - ℓ` legs past `w` ends in a free summed vertex, giving `χ`,

so each member is worth `χ^(8-ℓ) T^ℓ`: the count `(2q - ℓ) + ℓ = 2q = 8` of Lemma I.4.17 at `q = 4`.
Each non-path vertex supplies exactly one `χ`; the path legs compose into `iterPow`.

Nothing here uses probability, BK, moment hypotheses or subcriticality: only the constant row sum
`∑_z τ(v,z) = χ`.
-/

open MeasureTheory Measure ProbabilityTheory unitInterval
open scoped ENNReal NNReal

set_option linter.unusedSectionVars false
set_option linter.unusedDecidableInType false
set_option linter.style.longLine false
set_option linter.style.show false

@[expose] public section

namespace PercLib.CriticalLRP.I417FreshFour.Eval

open PercLib.CriticalLRP
open PercLib.CriticalLRP.I417Fresh
open PercLib.CriticalLRP.I417FreshTwo
open PercLib.CriticalLRP.I417Base

variable {V : Type*} [Countable V] [DecidableEq V]

/-! ## The two-point function is symmetric -/

/-- `τ` is symmetric (it is the `connSet` measure of an unordered pair). -/
theorem tau_symm (π : Sym2 V → unitInterval) (a b : V) : tau π a b = tau π b a := by
  rw [tau, tau, I417Fresh.connSet_swap]

/-! ## Composition of kernel powers is symmetric in the arguments -/

/-- The transpose of a kernel has the transposed `n`-fold power.  Proved with the "peel the last
step" recursion `iterPow_add_right` so that the induction hypothesis applies pointwise. -/
theorem iterPow_transpose (k : V → V → ℝ≥0∞) (n : ℕ) (a b : V) :
    iterPow (fun x y => k y x) n a b = iterPow k n b a := by
  induction n generalizing a b with
  | zero =>
      by_cases h : a = b
      · subst h; simp [iterPow]
      · have h' : ¬ b = a := fun hh => h hh.symm
        simp [iterPow, h, h']
  | succ n ih =>
      rw [show iterPow (fun x y => k y x) (n + 1) a b
            = ∑' u, k u a * iterPow (fun x y => k y x) n u b from rfl]
      rw [← I417FreshTwo.iterPow_add_right k n 1 b a]
      refine tsum_congr fun u => ?_
      rw [ih u b, I417FreshTwo.iterPow_one, mul_comm]

/-- **`T^n` is symmetric in its two arguments** for a symmetric kernel. -/
theorem iterPow_comm (k : V → V → ℝ≥0∞) (hk : ∀ a b, k a b = k b a) (n : ℕ) (a b : V) :
    iterPow k n a b = iterPow k n b a := by
  have hfun : (fun x y => k y x) = k := funext fun x => funext fun y => (hk x y).symm
  rw [← iterPow_transpose k n a b, hfun]

/-- The `q = 4` instance: `T^ℓ(w,y) = T^ℓ(y,w)`. -/
theorem iterPow_kernel_comm (π : Sym2 V → unitInterval) (n : ℕ) (a b : V) :
    iterPow (kernel π) n a b = iterPow (kernel π) n b a :=
  iterPow_comm (kernel π) (fun a b => tau_symm π a b) n a b

/-! ## The four-leg chain in the `y`-direction -/

/-- `T⁴(v,w) = ∑_{a,b,c} τ(v,a)τ(a,b)τ(b,c)τ(c,w)`. -/
theorem iterPow_four_eq (π : Sym2 V → unitInterval) (v w : V) :
    iterPow (kernel π) 4 v w =
      ∑' a : V, ∑' b : V, ∑' c : V, tau π v a * tau π a b * tau π b c * tau π c w := by
  have h4 : iterPow (kernel π) 4 v w =
      ∑' a : V, tau π v a *
        (∑' b : V, ∑' c : V, tau π a b * tau π b c * tau π c w) := by
    show (∑' a : V, kernel π v a * iterPow (kernel π) 3 a w) = _
    refine tsum_congr fun a => ?_
    rw [I417FreshTwo.iterPow_three_eq, kernel_def]
  rw [h4]
  refine Eq.trans (tsum_congr fun a => (ENNReal.tsum_mul_left).symm.trans
    (tsum_congr fun b => (ENNReal.tsum_mul_left).symm)) ?_
  exact tsum_congr fun a => tsum_congr fun b => tsum_congr fun c => by ring

/-- `y–a–b–c–w`: the four-leg chain contributes `T⁴`. -/
theorem chain_L4 (π : Sym2 V → unitInterval) (y w : V) :
    (∑' a : V, ∑' b : V, ∑' c : V,
        tau π y a * tau π a b * tau π b c * tau π c w) =
      iterPow (kernel π) 4 y w :=
  (iterPow_four_eq π y w).symm

/-- `y–a–b–w` with one leg past `w`: `χ·T³`. -/
theorem chain_L3 (π : Sym2 V → unitInterval) (χ : ℝ≥0∞)
    (hχ : ∀ v : V, ∑' z : V, tau π v z = χ) (y w : V) :
    (∑' a : V, ∑' b : V, ∑' c : V,
        tau π y a * tau π a b * tau π b w * tau π w c) =
      χ * iterPow (kernel π) 3 y w := by
  have hsimp : (∑' a : V, ∑' b : V, ∑' c : V,
        tau π y a * tau π a b * tau π b w * tau π w c) =
      (∑' a : V, ∑' b : V, tau π y a * tau π a b * tau π b w) * χ := by
    simp only [ENNReal.tsum_mul_left, ENNReal.tsum_mul_right, hχ]
  rw [hsimp, ← I417FreshTwo.iterPow_three_eq, mul_comm]

/-- `y–a–w` with two legs past `w`: `χ²·T²`. -/
theorem chain_L2 (π : Sym2 V → unitInterval) (χ : ℝ≥0∞)
    (hχ : ∀ v : V, ∑' z : V, tau π v z = χ) (y w : V) :
    (∑' a : V, ∑' b : V, ∑' c : V,
        tau π y a * tau π a w * tau π w b * tau π b c) =
      χ ^ 2 * iterPow (kernel π) 2 y w := by
  have hsimp : (∑' a : V, ∑' b : V, ∑' c : V,
        tau π y a * tau π a w * tau π w b * tau π b c) =
      (∑' a : V, tau π y a * tau π a w) * χ * χ := by
    simp only [ENNReal.tsum_mul_left, ENNReal.tsum_mul_right, hχ]
  rw [hsimp, ← I417FreshTwo.iterPow_two_eq, pow_two]
  ring

/-- `y–w` with three legs past `w`: `χ³·T`. -/
theorem chain_L1 (π : Sym2 V → unitInterval) (χ : ℝ≥0∞)
    (hχ : ∀ v : V, ∑' z : V, tau π v z = χ) (y w : V) :
    (∑' a : V, ∑' b : V, ∑' c : V,
        tau π y w * tau π w a * tau π a b * tau π b c) =
      χ ^ 3 * iterPow (kernel π) 1 y w := by
  have hsimp : (∑' a : V, ∑' b : V, ∑' c : V,
        tau π y w * tau π w a * tau π a b * tau π b c) =
      tau π y w * χ * χ * χ := by
    simp only [ENNReal.tsum_mul_left, ENNReal.tsum_mul_right, hχ]
  rw [hsimp, I417FreshTwo.iterPow_one, ← kernel_def]
  ring

/-! ## The four labelled arms sum out to `χ⁴` -/

/-- **Summing the four labelled arms out.**  Each arm sits in exactly one leg, so the four arm legs
are independent one-variable sums; the constant row sum gives `χ⁴` whatever the attachment points
`p1, …, p4` are, and whatever else the diagram carries (`C` does not involve the arm values). -/
theorem tsum_arm_four (π : Sym2 V → unitInterval) (χ : ℝ≥0∞)
    (hχ : ∀ v : V, ∑' z : V, tau π v z = χ) (p1 p2 p3 p4 : V) (C : ℝ≥0∞) :
    (∑' a : V, ∑' b : V, ∑' c : V, ∑' d : V,
        C * (tau π p1 a * tau π p2 b * tau π p3 c * tau π p4 d)) = C * χ ^ 4 := by
  have h1 : (∑' a : V, ∑' b : V, ∑' c : V, ∑' d : V,
        C * (tau π p1 a * tau π p2 b * tau π p3 c * tau π p4 d)) =
      C * (∑' a : V, ∑' b : V, ∑' c : V, ∑' d : V,
        tau π p1 a * tau π p2 b * tau π p3 c * tau π p4 d) := by
    simp only [ENNReal.tsum_mul_left]
  have h2 : (∑' a : V, ∑' b : V, ∑' c : V, ∑' d : V,
        tau π p1 a * tau π p2 b * tau π p3 c * tau π p4 d) = χ ^ 4 := by
    rw [show (∑' a : V, ∑' b : V, ∑' c : V, ∑' d : V,
        tau π p1 a * tau π p2 b * tau π p3 c * tau π p4 d) =
        χ * χ * χ * χ from by
      simp only [ENNReal.tsum_mul_left, ENNReal.tsum_mul_right, hχ]]
    ring
  rw [h1, h2]

/-! ## Reordering three nested sums -/

/-- Swap the first two of three nested sums. -/
theorem perm12 (F : V → V → V → ℝ≥0∞) :
    (∑' a : V, ∑' b : V, ∑' c : V, F a b c) = ∑' b : V, ∑' a : V, ∑' c : V, F a b c :=
  ENNReal.tsum_comm

/-- Swap the last two of three nested sums. -/
theorem perm23 (F : V → V → V → ℝ≥0∞) :
    (∑' a : V, ∑' b : V, ∑' c : V, F a b c) = ∑' a : V, ∑' c : V, ∑' b : V, F a b c :=
  tsum_congr fun _ => ENNReal.tsum_comm

/-- Reverse the order of three nested sums. -/
theorem perm13 (F : V → V → V → ℝ≥0∞) :
    (∑' a : V, ∑' b : V, ∑' c : V, F a b c) = ∑' c : V, ∑' b : V, ∑' a : V, F a b c := by
  rw [perm12]
  rw [show (∑' b : V, ∑' a : V, ∑' c : V, F a b c)
        = ∑' b : V, ∑' c : V, ∑' a : V, F a b c from tsum_congr fun _ => ENNReal.tsum_comm]
  rw [ENNReal.tsum_comm]

/-- The cyclic order `(b, c, a)` of three nested sums. -/
theorem perm231 (F : V → V → V → ℝ≥0∞) :
    (∑' a : V, ∑' b : V, ∑' c : V, F a b c) = ∑' b : V, ∑' c : V, ∑' a : V, F a b c := by
  rw [perm12]
  exact tsum_congr fun _ => ENNReal.tsum_comm

/-- The cyclic order `(c, a, b)` of three nested sums. -/
theorem perm312 (F : V → V → V → ℝ≥0∞) :
    (∑' a : V, ∑' b : V, ∑' c : V, F a b c) = ∑' c : V, ∑' a : V, ∑' b : V, F a b c := by
  rw [perm23]
  exact ENNReal.tsum_comm

/-! ## The four labelled arms as one tuple of vertex values -/

/-- **Summing the four labelled arms out**, with the arm values carried as a single tuple (the form
the `Fin 4 → V`-sum of the fresh event is reindexed to). -/
theorem tsum_arm_four_tuple (π : Sym2 V → unitInterval) (χ : ℝ≥0∞)
    (hχ : ∀ v : V, ∑' z : V, tau π v z = χ) (p1 p2 p3 p4 : V) (C : ℝ≥0∞) :
    (∑' pa : V × V × V × V,
        C * (tau π p1 pa.1 * tau π p2 pa.2.1 * tau π p3 pa.2.2.1 * tau π p4 pa.2.2.2)) =
      C * χ ^ 4 := by
  simp only [ENNReal.tsum_prod']
  exact tsum_arm_four π χ hχ p1 p2 p3 p4 C

/-- The arm tuple `pa` sits in the innermost position of the family sum. -/
theorem arms_inner (F : V × V × V × V → Fin 2 → (Fin 2 ⊕ Bool) → ((Fin 2 ⊕ Bool) ⊕ Bool) →
    V → V → V → ℝ≥0∞) :
    (∑' p : V × V × V × V, ∑' (k1 : Fin 2), ∑' (k2 : Fin 2 ⊕ Bool),
        ∑' (k3 : (Fin 2 ⊕ Bool) ⊕ Bool), ∑' (z1 : V), ∑' (z2 : V), ∑' (z3 : V),
        F p k1 k2 k3 z1 z2 z3) =
      ∑' (k1 : Fin 2), ∑' (k2 : Fin 2 ⊕ Bool), ∑' (k3 : (Fin 2 ⊕ Bool) ⊕ Bool),
        ∑' (z1 : V), ∑' (z2 : V), ∑' (z3 : V), ∑' p : V × V × V × V,
        F p k1 k2 k3 z1 z2 z3 := by
  rw [ENNReal.tsum_comm]
  refine Eq.trans (tsum_congr fun k1 => ENNReal.tsum_comm) ?_
  refine Eq.trans (tsum_congr fun k1 => tsum_congr fun k2 => ENNReal.tsum_comm) ?_
  refine Eq.trans (tsum_congr fun k1 => tsum_congr fun k2 => tsum_congr fun k3 =>
    ENNReal.tsum_comm) ?_
  refine Eq.trans (tsum_congr fun k1 => tsum_congr fun k2 => tsum_congr fun k3 =>
    tsum_congr fun z1 => ENNReal.tsum_comm) ?_
  refine Eq.trans (tsum_congr fun k1 => tsum_congr fun k2 => tsum_congr fun k3 =>
    tsum_congr fun z1 => tsum_congr fun z2 => ENNReal.tsum_comm) ?_
  rfl

/-! ## Expanding the three finite index sums of the `q = 4` family -/

/-- `Fin 2` sum expansion. -/
theorem tsum_fin2 (H : Fin 2 → ℝ≥0∞) : (∑' k : Fin 2, H k) = H 0 + H 1 := by
  rw [tsum_fintype, Fin.sum_univ_two]

/-- `Fin 2 ⊕ Bool` sum expansion, in the order of the accepted family. -/
theorem tsum_fin2_bool (H : Fin 2 ⊕ Bool → ℝ≥0∞) :
    (∑' k : Fin 2 ⊕ Bool, H k) =
      H (Sum.inl 0) + H (Sum.inl 1) + H (Sum.inr false) + H (Sum.inr true) := by
  rw [tsum_fintype, Fintype.sum_sum_type, Fin.sum_univ_two, Fintype.sum_bool]
  ring

/-- `(Fin 2 ⊕ Bool) ⊕ Bool` sum expansion, in the order of the accepted family. -/
theorem tsum_fin2_bool_bool (H : (Fin 2 ⊕ Bool) ⊕ Bool → ℝ≥0∞) :
    (∑' k : (Fin 2 ⊕ Bool) ⊕ Bool, H k) =
      H (Sum.inl (Sum.inl 0)) + H (Sum.inl (Sum.inl 1)) +
        H (Sum.inl (Sum.inr false)) + H (Sum.inl (Sum.inr true)) +
        H (Sum.inr false) + H (Sum.inr true) := by
  rw [tsum_fintype, Fintype.sum_sum_type]
  rw [show (∑ a : Fin 2 ⊕ Bool, H (Sum.inl a)) =
      H (Sum.inl (Sum.inl 0)) + H (Sum.inl (Sum.inl 1)) +
        H (Sum.inl (Sum.inr false)) + H (Sum.inl (Sum.inr true)) from by
    rw [Fintype.sum_sum_type, Fin.sum_univ_two, Fintype.sum_bool]
    ring]
  rw [Fintype.sum_bool]
  ring

end PercLib.CriticalLRP.I417FreshFour.Eval
