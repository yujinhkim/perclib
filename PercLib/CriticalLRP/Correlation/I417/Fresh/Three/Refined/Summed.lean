/-
Independently reviewed and integrated from the completed artifact `smwx6p0op/m1`
at `.ultramath/smwx6p0op/m1/M3Q`. Production integration revision:
`3cd318e5a37d0dc889f23bd3baf1b8884e651a27`. The coordinator uses the production
namespace and fully qualified imports; the proof covers `q = 3`, not arbitrary `q`.
-/
module

public import PercLib.CriticalLRP.Correlation.I417.Fresh.Three.Refined.Bound

/-!
Independently built for swarm `smwx6p0op`, member `m1`, direction Q3-MARK-ON-PATH-COVER.

# The `q = 3` fresh-copy factor, summed

This file sums the eight six-edge diagram families of `freshShapeSum` over the three labelled
arms and the two branch points, and evaluates them in the printed normalisation:

  `∑_g P(freshMark y g j w) ≤ 2 χ³ T³(w,y) + 3 χ⁴ T²(w,y) + 3 χ⁵ T(w,y)`.

Each of the eight monomials has exactly `2q = 6` two-point factors: three arm factors summed out to
`χ³` and a structure part with `y`-leg length `1`, `2` or `3`
(`2` of the eight have `y`-leg `3`, `3` have `y`-leg `2`, `3` have `y`-leg `1`).  Composed with the
`2p + 1`-edge marked side this gives the printed `2p + 2q + 1 = 2p + 7` total and `T`-powers
`ℓ + m` with `2 ≤ ℓ ≤ p + 1` and `1 ≤ m ≤ 3`, i.e. `3 ≤ ℓ + m ≤ p + 4 = p + q + 1`.

Inputs: `π e < 1` (BK) and the constant row sum `∑_z τ(v,z) = χ` (constant mean cluster volume).
-/

open MeasureTheory Measure ProbabilityTheory unitInterval
open scoped ENNReal NNReal

set_option linter.unusedSectionVars false
set_option linter.unusedDecidableInType false
set_option linter.unusedSimpArgs false
-- the eight six-leg products are written out in full and exceed the line limit
set_option linter.style.longLine false

@[expose] public section

namespace PercLib.CriticalLRP.I417FreshThree.Refined

open PercLib.CriticalLRP
open PercLib.CriticalLRP.I417Fresh
open PercLib.CriticalLRP.I417FreshTwo
open PercLib.CriticalLRP.I417Base

variable {V : Type*} [Countable V] [DecidableEq V]

attribute [local instance] Classical.propDecidable

/-! ## Symmetry of the two-point function -/

/-- The free arm sum is the sum of `τ` over the free end. -/
theorem tsum_tau (π : Sym2 V → unitInterval) (v : V) :
    (∑' z : V, tau π v z) = hubArmSum π v := rfl

/-- `τ` is symmetric. -/
theorem tau_comm (π : Sym2 V → unitInterval) (a b : V) :
    tau π a b = tau π b a := by
  rw [tau, tau, I417Fresh.connSet_swap]

/-- `T²` is symmetric. -/
theorem iterPow_two_comm (π : Sym2 V → unitInterval) (a b : V) :
    iterPow (kernel π) 2 a b = iterPow (kernel π) 2 b a := by
  rw [iterPow_two_eq, iterPow_two_eq]
  refine tsum_congr fun z => ?_
  rw [tau_comm π a z, tau_comm π z b, mul_comm]

/-! ## Summing the three labelled arms out -/

/-- **The three labelled arms sum out independently.** -/
theorem tsum_three (a b c : Fin 3) (hab : a ≠ b) (hac : a ≠ c) (hbc : b ≠ c)
    (f k l : V → ℝ≥0∞) :
    (∑' g : Fin 3 → V, f (g a) * k (g b) * l (g c)) =
      (∑' z : V, f z) * (∑' z : V, k z) * (∑' z : V, l z) := by
  have h := Equiv.tsum_eq (armEquiv a b c hab hac hbc).symm
    (fun g : Fin 3 → V => f (g a) * k (g b) * l (g c))
  rw [← h]
  have hbody : ∀ p : V × V × V,
      f ((armEquiv a b c hab hac hbc).symm p a) *
        k ((armEquiv a b c hab hac hbc).symm p b) *
        l ((armEquiv a b c hab hac hbc).symm p c) = f p.1 * k p.2.1 * l p.2.2 := by
    intro p
    simp [armEquiv, hab.symm, hac.symm, hbc.symm]
  rw [tsum_congr hbody]
  rw [ENNReal.tsum_prod']
  have h1 : ∀ x : V, (∑' yz : V × V, f x * k yz.1 * l yz.2) =
      ∑' y : V, ∑' z : V, f x * k y * l z := by
    intro x
    rw [ENNReal.tsum_prod']
  rw [tsum_congr h1]
  simp only [ENNReal.tsum_mul_left, ENNReal.tsum_mul_right]

/-! ## The seven structure sums -/

/-- `y–q–p–w`: `∑_{p,q} τ(y,q)τ(q,p)τ(p,w) = T³(w,y)`. -/
theorem structA (π : Sym2 V → unitInterval) (y w : V) :
    (∑' p : V, ∑' q : V, tau π y q * tau π q p * tau π p w) =
      iterPow (kernel π) 3 w y := by
  rw [iterPow_three_eq]
  refine tsum_congr fun p => tsum_congr fun q => ?_
  rw [tau_comm π y q, tau_comm π q p, tau_comm π p w]
  ring

/-- `y–p–q–w`: `∑_{p,q} τ(p,q)τ(q,w)τ(y,p) = T³(w,y)`. -/
theorem structA' (π : Sym2 V → unitInterval) (y w : V) :
    (∑' p : V, ∑' q : V, tau π p q * tau π q w * tau π y p) =
      iterPow (kernel π) 3 w y := by
  rw [← structA π y w]
  rw [ENNReal.tsum_comm]
  refine tsum_congr fun q => tsum_congr fun p => ?_
  ring

/-- `y–p–w` with the free end `q` at `w`. -/
theorem structB1 (π : Sym2 V → unitInterval) (y w : V) (χ : ℝ≥0∞)
    (hχ : ∀ v : V, hubArmSum π v = χ) :
    (∑' p : V, ∑' q : V, tau π w q * tau π y p * tau π p w) =
      χ * iterPow (kernel π) 2 w y := by
  have hstep : ∀ p : V, (∑' q : V, tau π w q * tau π y p * tau π p w) =
      χ * (tau π y p * tau π p w) := by
    intro p
    rw [show (∑' q : V, tau π w q * tau π y p * tau π p w) =
      ∑' q : V, tau π w q * (tau π y p * tau π p w) from
      tsum_congr fun q => by ring]
    rw [ENNReal.tsum_mul_right, show (∑' q : V, tau π w q) = χ from hχ w]
  rw [tsum_congr hstep, ENNReal.tsum_mul_left,
    show (∑' p : V, tau π y p * tau π p w) = iterPow (kernel π) 2 y w from
      (iterPow_two_eq π y w).symm,
    iterPow_two_comm π y w]

/-- `y–p–w` with the free end `q` at `p`. -/
theorem structB2 (π : Sym2 V → unitInterval) (y w : V) (χ : ℝ≥0∞)
    (hχ : ∀ v : V, hubArmSum π v = χ) :
    (∑' p : V, ∑' q : V, tau π p q * tau π y p * tau π p w) =
      χ * iterPow (kernel π) 2 w y := by
  have hstep : ∀ p : V, (∑' q : V, tau π p q * tau π y p * tau π p w) =
      χ * (tau π y p * tau π p w) := by
    intro p
    rw [show (∑' q : V, tau π p q * tau π y p * tau π p w) =
      ∑' q : V, tau π p q * (tau π y p * tau π p w) from
      tsum_congr fun q => by ring]
    rw [ENNReal.tsum_mul_right, show (∑' q : V, tau π p q) = χ from hχ p]
  rw [tsum_congr hstep, ENNReal.tsum_mul_left,
    show (∑' p : V, tau π y p * tau π p w) = iterPow (kernel π) 2 y w from
      (iterPow_two_eq π y w).symm,
    iterPow_two_comm π y w]

/-- `y–q–w` with the free end `p` at `w`. -/
theorem structB3 (π : Sym2 V → unitInterval) (y w : V) (χ : ℝ≥0∞)
    (hχ : ∀ v : V, hubArmSum π v = χ) :
    (∑' p : V, ∑' q : V, tau π y q * tau π q w * tau π w p) =
      χ * iterPow (kernel π) 2 w y := by
  have hstep : ∀ p : V, (∑' q : V, tau π y q * tau π q w * tau π w p) =
      iterPow (kernel π) 2 y w * tau π w p := by
    intro p
    rw [show (∑' q : V, tau π y q * tau π q w * tau π w p) =
      ∑' q : V, (tau π y q * tau π q w) * tau π w p from
      tsum_congr fun q => by ring]
    rw [ENNReal.tsum_mul_right,
      show (∑' q : V, tau π y q * tau π q w) = iterPow (kernel π) 2 y w from
        (iterPow_two_eq π y w).symm]
  rw [tsum_congr hstep, ENNReal.tsum_mul_left, show (∑' p : V, tau π w p) = χ from hχ w,
    iterPow_two_comm π y w]
  ring

/-- The edge `y–w` with the chain `w–q–p`. -/
theorem structC1 (π : Sym2 V → unitInterval) (y w : V) (χ : ℝ≥0∞)
    (hχ : ∀ v : V, hubArmSum π v = χ) :
    (∑' p : V, ∑' q : V, tau π w q * tau π q p * tau π y w) =
      χ ^ 2 * iterPow (kernel π) 1 w y := by
  rw [ENNReal.tsum_comm]
  have hstep : ∀ q : V, (∑' p : V, tau π w q * tau π q p * tau π y w) =
      (tau π w q * tau π y w) * χ := by
    intro q
    rw [show (∑' p : V, tau π w q * tau π q p * tau π y w) =
      ∑' p : V, (tau π w q * tau π y w) * tau π q p from
      tsum_congr fun p => by ring]
    rw [ENNReal.tsum_mul_left, show (∑' p : V, tau π q p) = χ from hχ q]
  rw [tsum_congr hstep, ENNReal.tsum_mul_right, ENNReal.tsum_mul_right,
    show (∑' q : V, tau π w q) = χ from hχ w, iterPow_one, kernel_def, tau_comm π y w]
  ring

/-- The edge `y–w` with the chain `w–p–q`. -/
theorem structC2 (π : Sym2 V → unitInterval) (y w : V) (χ : ℝ≥0∞)
    (hχ : ∀ v : V, hubArmSum π v = χ) :
    (∑' p : V, ∑' q : V, tau π p q * tau π y w * tau π w p) =
      χ ^ 2 * iterPow (kernel π) 1 w y := by
  have hstep : ∀ p : V, (∑' q : V, tau π p q * tau π y w * tau π w p) =
      χ * (tau π y w * tau π w p) := by
    intro p
    rw [show (∑' q : V, tau π p q * tau π y w * tau π w p) =
      ∑' q : V, tau π p q * (tau π y w * tau π w p) from
      tsum_congr fun q => by ring]
    rw [ENNReal.tsum_mul_right, show (∑' q : V, tau π p q) = χ from hχ p]
  rw [tsum_congr hstep, ENNReal.tsum_mul_left, ENNReal.tsum_mul_left,
    show (∑' p : V, tau π w p) = χ from hχ w, iterPow_one, kernel_def, tau_comm π y w]
  ring


/-- The `evalA0` product sums to its six-factor value. -/
theorem evalA0 (π : Sym2 V → unitInterval) (y w : V) (a b c : Fin 3)
    (hab : a ≠ b) (hac : a ≠ c) (hbc : b ≠ c) (χ : ℝ≥0∞)
    (hχ : ∀ v : V, hubArmSum π v = χ) :
    (∑' p : V, ∑' q : V, ∑' g : Fin 3 → V, tau π y q * tau π q p * tau π p w * tau π w (g a) * tau π p (g b) *
          tau π q (g c)) = χ ^ 3 * iterPow (kernel π) 3 w y := by
  have hstep : ∀ p q : V, (∑' g : Fin 3 → V, tau π y q * tau π q p * tau π p w * tau π w (g a) * tau π p (g b) *
          tau π q (g c)) =
      (tau π y q * tau π q p * tau π p w) * χ ^ 3 := by
    intro p q
    rw [show (∑' g : Fin 3 → V, tau π y q * tau π q p * tau π p w * tau π w (g a) * tau π p (g b) *
          tau π q (g c)) =
        ∑' g : Fin 3 → V, (tau π y q * tau π q p * tau π p w) * (tau π w (g a) * tau π p (g b) * tau π q (g c)) from
      tsum_congr fun g => by ring]
    rw [ENNReal.tsum_mul_left, tsum_three a b c hab hac hbc (tau π w) (tau π p) (tau π q)]
    simp only [tsum_tau, hχ]
    ring
  rw [tsum_congr fun p => tsum_congr fun q => hstep p q]
  rw [show (∑' p : V, ∑' q : V, (tau π y q * tau π q p * tau π p w) * χ ^ 3) =
      (∑' p : V, ∑' q : V, tau π y q * tau π q p * tau π p w) * χ ^ 3 from by
    rw [show (∑' p : V, ∑' q : V, (tau π y q * tau π q p * tau π p w) * χ ^ 3) =
      ∑' p : V, (∑' q : V, tau π y q * tau π q p * tau π p w) * χ ^ 3 from
      tsum_congr fun p => ENNReal.tsum_mul_right]
    exact ENNReal.tsum_mul_right]
  rw [structA π y w]
  ring

/-- The `evalA1` product sums to its six-factor value. -/
theorem evalA1 (π : Sym2 V → unitInterval) (y w : V) (a b c : Fin 3)
    (hab : a ≠ b) (hac : a ≠ c) (hbc : b ≠ c) (χ : ℝ≥0∞)
    (hχ : ∀ v : V, hubArmSum π v = χ) :
    (∑' p : V, ∑' q : V, ∑' g : Fin 3 → V, tau π p q * tau π q w * tau π y p * tau π w (g a) * tau π p (g b) *
          tau π q (g c)) = χ ^ 3 * iterPow (kernel π) 3 w y := by
  have hstep : ∀ p q : V, (∑' g : Fin 3 → V, tau π p q * tau π q w * tau π y p * tau π w (g a) * tau π p (g b) *
          tau π q (g c)) =
      (tau π p q * tau π q w * tau π y p) * χ ^ 3 := by
    intro p q
    rw [show (∑' g : Fin 3 → V, tau π p q * tau π q w * tau π y p * tau π w (g a) * tau π p (g b) *
          tau π q (g c)) =
        ∑' g : Fin 3 → V, (tau π p q * tau π q w * tau π y p) * (tau π w (g a) * tau π p (g b) * tau π q (g c)) from
      tsum_congr fun g => by ring]
    rw [ENNReal.tsum_mul_left, tsum_three a b c hab hac hbc (tau π w) (tau π p) (tau π q)]
    simp only [tsum_tau, hχ]
    ring
  rw [tsum_congr fun p => tsum_congr fun q => hstep p q]
  rw [show (∑' p : V, ∑' q : V, (tau π p q * tau π q w * tau π y p) * χ ^ 3) =
      (∑' p : V, ∑' q : V, tau π p q * tau π q w * tau π y p) * χ ^ 3 from by
    rw [show (∑' p : V, ∑' q : V, (tau π p q * tau π q w * tau π y p) * χ ^ 3) =
      ∑' p : V, (∑' q : V, tau π p q * tau π q w * tau π y p) * χ ^ 3 from
      tsum_congr fun p => ENNReal.tsum_mul_right]
    exact ENNReal.tsum_mul_right]
  rw [structA' π y w]
  ring

/-- The `evalA2` product sums to its six-factor value. -/
theorem evalA2 (π : Sym2 V → unitInterval) (y w : V) (a b c : Fin 3)
    (hab : a ≠ b) (hac : a ≠ c) (hbc : b ≠ c) (χ : ℝ≥0∞)
    (hχ : ∀ v : V, hubArmSum π v = χ) :
    (∑' p : V, ∑' q : V, ∑' g : Fin 3 → V, tau π w q * tau π q (g a) * tau π y p * tau π p w * tau π p (g b) *
          tau π q (g c)) = χ ^ 4 * iterPow (kernel π) 2 w y := by
  have hstep : ∀ p q : V, (∑' g : Fin 3 → V, tau π w q * tau π q (g a) * tau π y p * tau π p w * tau π p (g b) *
          tau π q (g c)) =
      (tau π w q * tau π y p * tau π p w) * χ ^ 3 := by
    intro p q
    rw [show (∑' g : Fin 3 → V, tau π w q * tau π q (g a) * tau π y p * tau π p w * tau π p (g b) *
          tau π q (g c)) =
        ∑' g : Fin 3 → V, (tau π w q * tau π y p * tau π p w) * (tau π q (g a) * tau π p (g b) * tau π q (g c)) from
      tsum_congr fun g => by ring]
    rw [ENNReal.tsum_mul_left, tsum_three a b c hab hac hbc (tau π q) (tau π p) (tau π q)]
    simp only [tsum_tau, hχ]
    ring
  rw [tsum_congr fun p => tsum_congr fun q => hstep p q]
  rw [show (∑' p : V, ∑' q : V, (tau π w q * tau π y p * tau π p w) * χ ^ 3) =
      (∑' p : V, ∑' q : V, tau π w q * tau π y p * tau π p w) * χ ^ 3 from by
    rw [show (∑' p : V, ∑' q : V, (tau π w q * tau π y p * tau π p w) * χ ^ 3) =
      ∑' p : V, (∑' q : V, tau π w q * tau π y p * tau π p w) * χ ^ 3 from
      tsum_congr fun p => ENNReal.tsum_mul_right]
    exact ENNReal.tsum_mul_right]
  rw [structB1 π y w χ hχ]
  ring

/-- The `evalA3` product sums to its six-factor value. -/
theorem evalA3 (π : Sym2 V → unitInterval) (y w : V) (a b c : Fin 3)
    (hab : a ≠ b) (hac : a ≠ c) (hbc : b ≠ c) (χ : ℝ≥0∞)
    (hχ : ∀ v : V, hubArmSum π v = χ) :
    (∑' p : V, ∑' q : V, ∑' g : Fin 3 → V, tau π p q * tau π q (g b) * tau π y p * tau π p w * tau π w (g a) *
          tau π q (g c)) = χ ^ 4 * iterPow (kernel π) 2 w y := by
  have hstep : ∀ p q : V, (∑' g : Fin 3 → V, tau π p q * tau π q (g b) * tau π y p * tau π p w * tau π w (g a) *
          tau π q (g c)) =
      (tau π p q * tau π y p * tau π p w) * χ ^ 3 := by
    intro p q
    rw [show (∑' g : Fin 3 → V, tau π p q * tau π q (g b) * tau π y p * tau π p w * tau π w (g a) *
          tau π q (g c)) =
        ∑' g : Fin 3 → V, (tau π p q * tau π y p * tau π p w) * (tau π w (g a) * tau π q (g b) * tau π q (g c)) from
      tsum_congr fun g => by ring]
    rw [ENNReal.tsum_mul_left, tsum_three a b c hab hac hbc (tau π w) (tau π q) (tau π q)]
    simp only [tsum_tau, hχ]
    ring
  rw [tsum_congr fun p => tsum_congr fun q => hstep p q]
  rw [show (∑' p : V, ∑' q : V, (tau π p q * tau π y p * tau π p w) * χ ^ 3) =
      (∑' p : V, ∑' q : V, tau π p q * tau π y p * tau π p w) * χ ^ 3 from by
    rw [show (∑' p : V, ∑' q : V, (tau π p q * tau π y p * tau π p w) * χ ^ 3) =
      ∑' p : V, (∑' q : V, tau π p q * tau π y p * tau π p w) * χ ^ 3 from
      tsum_congr fun p => ENNReal.tsum_mul_right]
    exact ENNReal.tsum_mul_right]
  rw [structB2 π y w χ hχ]
  ring

/-- The `evalB0` product sums to its six-factor value. -/
theorem evalB0 (π : Sym2 V → unitInterval) (y w : V) (a b c : Fin 3)
    (hab : a ≠ b) (hac : a ≠ c) (hbc : b ≠ c) (χ : ℝ≥0∞)
    (hχ : ∀ v : V, hubArmSum π v = χ) :
    (∑' p : V, ∑' q : V, ∑' g : Fin 3 → V, tau π y q * tau π q w * tau π w p * tau π p (g a) * tau π p (g b) *
          tau π q (g c)) = χ ^ 4 * iterPow (kernel π) 2 w y := by
  have hstep : ∀ p q : V, (∑' g : Fin 3 → V, tau π y q * tau π q w * tau π w p * tau π p (g a) * tau π p (g b) *
          tau π q (g c)) =
      (tau π y q * tau π q w * tau π w p) * χ ^ 3 := by
    intro p q
    rw [show (∑' g : Fin 3 → V, tau π y q * tau π q w * tau π w p * tau π p (g a) * tau π p (g b) *
          tau π q (g c)) =
        ∑' g : Fin 3 → V, (tau π y q * tau π q w * tau π w p) * (tau π p (g a) * tau π p (g b) * tau π q (g c)) from
      tsum_congr fun g => by ring]
    rw [ENNReal.tsum_mul_left, tsum_three a b c hab hac hbc (tau π p) (tau π p) (tau π q)]
    simp only [tsum_tau, hχ]
    ring
  rw [tsum_congr fun p => tsum_congr fun q => hstep p q]
  rw [show (∑' p : V, ∑' q : V, (tau π y q * tau π q w * tau π w p) * χ ^ 3) =
      (∑' p : V, ∑' q : V, tau π y q * tau π q w * tau π w p) * χ ^ 3 from by
    rw [show (∑' p : V, ∑' q : V, (tau π y q * tau π q w * tau π w p) * χ ^ 3) =
      ∑' p : V, (∑' q : V, tau π y q * tau π q w * tau π w p) * χ ^ 3 from
      tsum_congr fun p => ENNReal.tsum_mul_right]
    exact ENNReal.tsum_mul_right]
  rw [structB3 π y w χ hχ]
  ring

/-- The `evalB1` product sums to its six-factor value. -/
theorem evalB1 (π : Sym2 V → unitInterval) (y w : V) (a b c : Fin 3)
    (hab : a ≠ b) (hac : a ≠ c) (hbc : b ≠ c) (χ : ℝ≥0∞)
    (hχ : ∀ v : V, hubArmSum π v = χ) :
    (∑' p : V, ∑' q : V, ∑' g : Fin 3 → V, tau π w q * tau π q p * tau π y w * tau π p (g a) * tau π p (g b) *
          tau π q (g c)) = χ ^ 5 * iterPow (kernel π) 1 w y := by
  have hstep : ∀ p q : V, (∑' g : Fin 3 → V, tau π w q * tau π q p * tau π y w * tau π p (g a) * tau π p (g b) *
          tau π q (g c)) =
      (tau π w q * tau π q p * tau π y w) * χ ^ 3 := by
    intro p q
    rw [show (∑' g : Fin 3 → V, tau π w q * tau π q p * tau π y w * tau π p (g a) * tau π p (g b) *
          tau π q (g c)) =
        ∑' g : Fin 3 → V, (tau π w q * tau π q p * tau π y w) * (tau π p (g a) * tau π p (g b) * tau π q (g c)) from
      tsum_congr fun g => by ring]
    rw [ENNReal.tsum_mul_left, tsum_three a b c hab hac hbc (tau π p) (tau π p) (tau π q)]
    simp only [tsum_tau, hχ]
    ring
  rw [tsum_congr fun p => tsum_congr fun q => hstep p q]
  rw [show (∑' p : V, ∑' q : V, (tau π w q * tau π q p * tau π y w) * χ ^ 3) =
      (∑' p : V, ∑' q : V, tau π w q * tau π q p * tau π y w) * χ ^ 3 from by
    rw [show (∑' p : V, ∑' q : V, (tau π w q * tau π q p * tau π y w) * χ ^ 3) =
      ∑' p : V, (∑' q : V, tau π w q * tau π q p * tau π y w) * χ ^ 3 from
      tsum_congr fun p => ENNReal.tsum_mul_right]
    exact ENNReal.tsum_mul_right]
  rw [structC1 π y w χ hχ]
  ring

/-- The `evalB2` product sums to its six-factor value. -/
theorem evalB2 (π : Sym2 V → unitInterval) (y w : V) (a b c : Fin 3)
    (hab : a ≠ b) (hac : a ≠ c) (hbc : b ≠ c) (χ : ℝ≥0∞)
    (hχ : ∀ v : V, hubArmSum π v = χ) :
    (∑' p : V, ∑' q : V, ∑' g : Fin 3 → V, tau π p q * tau π q (g a) * tau π y w * tau π w p * tau π p (g b) *
          tau π q (g c)) = χ ^ 5 * iterPow (kernel π) 1 w y := by
  have hstep : ∀ p q : V, (∑' g : Fin 3 → V, tau π p q * tau π q (g a) * tau π y w * tau π w p * tau π p (g b) *
          tau π q (g c)) =
      (tau π p q * tau π y w * tau π w p) * χ ^ 3 := by
    intro p q
    rw [show (∑' g : Fin 3 → V, tau π p q * tau π q (g a) * tau π y w * tau π w p * tau π p (g b) *
          tau π q (g c)) =
        ∑' g : Fin 3 → V, (tau π p q * tau π y w * tau π w p) * (tau π q (g a) * tau π p (g b) * tau π q (g c)) from
      tsum_congr fun g => by ring]
    rw [ENNReal.tsum_mul_left, tsum_three a b c hab hac hbc (tau π q) (tau π p) (tau π q)]
    simp only [tsum_tau, hχ]
    ring
  rw [tsum_congr fun p => tsum_congr fun q => hstep p q]
  rw [show (∑' p : V, ∑' q : V, (tau π p q * tau π y w * tau π w p) * χ ^ 3) =
      (∑' p : V, ∑' q : V, tau π p q * tau π y w * tau π w p) * χ ^ 3 from by
    rw [show (∑' p : V, ∑' q : V, (tau π p q * tau π y w * tau π w p) * χ ^ 3) =
      ∑' p : V, (∑' q : V, tau π p q * tau π y w * tau π w p) * χ ^ 3 from
      tsum_congr fun p => ENNReal.tsum_mul_right]
    exact ENNReal.tsum_mul_right]
  rw [structC2 π y w χ hχ]
  ring

/-- The `evalB3` product sums to its six-factor value. -/
theorem evalB3 (π : Sym2 V → unitInterval) (y w : V) (a b c : Fin 3)
    (hab : a ≠ b) (hac : a ≠ c) (hbc : b ≠ c) (χ : ℝ≥0∞)
    (hχ : ∀ v : V, hubArmSum π v = χ) :
    (∑' p : V, ∑' q : V, ∑' g : Fin 3 → V, tau π p q * tau π q (g b) * tau π y w * tau π w p * tau π p (g a) *
          tau π q (g c)) = χ ^ 5 * iterPow (kernel π) 1 w y := by
  have hstep : ∀ p q : V, (∑' g : Fin 3 → V, tau π p q * tau π q (g b) * tau π y w * tau π w p * tau π p (g a) *
          tau π q (g c)) =
      (tau π p q * tau π y w * tau π w p) * χ ^ 3 := by
    intro p q
    rw [show (∑' g : Fin 3 → V, tau π p q * tau π q (g b) * tau π y w * tau π w p * tau π p (g a) *
          tau π q (g c)) =
        ∑' g : Fin 3 → V, (tau π p q * tau π y w * tau π w p) * (tau π p (g a) * tau π q (g b) * tau π q (g c)) from
      tsum_congr fun g => by ring]
    rw [ENNReal.tsum_mul_left, tsum_three a b c hab hac hbc (tau π p) (tau π q) (tau π q)]
    simp only [tsum_tau, hχ]
    ring
  rw [tsum_congr fun p => tsum_congr fun q => hstep p q]
  rw [show (∑' p : V, ∑' q : V, (tau π p q * tau π y w * tau π w p) * χ ^ 3) =
      (∑' p : V, ∑' q : V, tau π p q * tau π y w * tau π w p) * χ ^ 3 from by
    rw [show (∑' p : V, ∑' q : V, (tau π p q * tau π y w * tau π w p) * χ ^ 3) =
      ∑' p : V, (∑' q : V, tau π p q * tau π y w * tau π w p) * χ ^ 3 from
      tsum_congr fun p => ENNReal.tsum_mul_right]
    exact ENNReal.tsum_mul_right]
  rw [structC2 π y w χ hχ]
  ring

/-- **The `q = 3` fresh-copy factor, summed**: six two-point factors per monomial. -/
theorem tsum_freshMark_le_refined_gen (π : Sym2 V → unitInterval) (hπ : ∀ e, π e < 1)
    (y w : V) (χ : ℝ≥0∞) (hχ : ∀ v : V, hubArmSum π v = χ) (a b c : Fin 3)
    (hab : a ≠ b) (hac : a ≠ c) (hbc : b ≠ c) :
    (∑' g : Fin 3 → V, (edgeMeasure π) (I417Gen.freshMark y g a w)) ≤
      freshThreeRefined π χ y w := by
  have hcomm : ∀ F : (Fin 3 → V) → V → V → ℝ≥0∞,
      (∑' g : Fin 3 → V, ∑' p : V, ∑' q : V, F g p q) =
        ∑' p : V, ∑' q : V, ∑' g : Fin 3 → V, F g p q := by
    intro F
    rw [ENNReal.tsum_comm]
    exact tsum_congr fun p => ENNReal.tsum_comm
  refine le_trans (ENNReal.tsum_le_tsum fun g => freshMark_measure_le_shapes π hπ y w g a b c) ?_
  refine le_trans (le_of_eq (hcomm (fun g p q =>
    freshShapeSum π y w (g a) (g b) (g c) p q))) ?_
  simp only [freshShapeSum, ENNReal.tsum_add]
  rw [evalA0 π y w a b c hab hac hbc χ hχ, evalA1 π y w a b c hab hac hbc χ hχ,
    evalA2 π y w a b c hab hac hbc χ hχ, evalA3 π y w a b c hab hac hbc χ hχ,
    evalB0 π y w a b c hab hac hbc χ hχ, evalB1 π y w a b c hab hac hbc χ hχ,
    evalB2 π y w a b c hab hac hbc χ hχ, evalB3 π y w a b c hab hac hbc χ hχ]
  rw [freshThreeRefined]
  exact le_of_eq (by ring)

/-- **The `q = 3` fresh-copy factor for every selected arm `j : Fin 3`.** -/
theorem tsum_freshMark_le_refined (π : Sym2 V → unitInterval) (hπ : ∀ e, π e < 1)
    (y w : V) (χ : ℝ≥0∞) (hχ : ∀ v : V, hubArmSum π v = χ) (j : Fin 3) :
    (∑' g : Fin 3 → V, (edgeMeasure π) (I417Gen.freshMark y g j w)) ≤
      freshThreeRefined π χ y w := by
  fin_cases j
  · exact tsum_freshMark_le_refined_gen π hπ y w χ hχ 0 1 2 (by decide) (by decide) (by decide)
  · exact tsum_freshMark_le_refined_gen π hπ y w χ hχ 1 2 0 (by decide) (by decide) (by decide)
  · exact tsum_freshMark_le_refined_gen π hπ y w χ hχ 2 0 1 (by decide) (by decide) (by decide)

end PercLib.CriticalLRP.I417FreshThree.Refined
