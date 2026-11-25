/- Integrated from independently rebuilt Ultramath work, base revision 4140ac56119d2cd80995f91886669efe004839d5.
Scratch source: ../../.ultramath/smwqozn0q/m1/Defs.lean ; imports migrated only.
-/

module

/-
Copyright (c) 2026 PercLib contributors. Released under Apache 2.0.
Matrix powers of the native connection kernel, and the finite truncations used to pass
from finite submatrices to the infinite lattice.  No theorem conclusion is asserted here.
-/
public import Mathlib

/-!
# Matrix powers of the connection kernel

For a vertex type `V` and a kernel `K : V → V → ℝ` we write `KpowF K S n x y` for the
`n`-fold iterated sum of `K` in which every intermediate vertex is restricted to the finite
set `S`, and `Kpow K n x y` for the unrestricted (`ℝ≥0∞`-valued) `n`-fold matrix power.

`KpowF K S n x y` is, for `x, y ∈ S`, exactly the `(x,y)` entry of the `n`-th power of the
principal submatrix of `K` on `S` (`KpowF_eq_matpow` below); the set `S` is kept as an
explicit parameter so that the truncation is visible and never confused with `Kpow`.
-/

@[expose] public section

noncomputable section

open scoped ENNReal

namespace PercLib.CriticalLRP.KernelPower

variable {V : Type*}

/-- The Kronecker delta, as a real number. -/
def delta (x y : V) : ℝ := by classical exact if x = y then 1 else 0

theorem delta_self (x : V) : delta x x = 1 := by classical simp [delta]

theorem delta_of_ne {x y : V} (h : x ≠ y) : delta x y = 0 := by classical simp [delta, h]

theorem delta_nonneg (x y : V) : 0 ≤ delta x y := by
  classical rw [delta]; split_ifs <;> norm_num

/-- The Kronecker delta, as an `ℝ≥0∞`-valued kernel. -/
def deltaE (x y : V) : ℝ≥0∞ := by classical exact if x = y then 1 else 0

theorem deltaE_self (x : V) : deltaE x x = 1 := by classical simp [deltaE]

theorem ofReal_delta (x y : V) : ENNReal.ofReal (delta x y) = deltaE x y := by
  classical rw [delta, deltaE]; split_ifs <;> simp

/-- `KpowF K S n x y` is the `n`-fold iterated sum `∑ u₁ ∈ S, …, ∑ uₙ₋₁ ∈ S,`
`K x u₁ * ⋯ * K uₙ₋₁ y` of the kernel `K`, with all intermediate vertices restricted to the
finite set `S`.  Equivalently (see `KpowF_eq_matpow`) it is the `(x,y)` entry of the `n`-th
power of the principal submatrix of `K` on `S`. -/
def KpowF (K : V → V → ℝ) (S : Finset V) : ℕ → V → V → ℝ
  | 0, x, y => delta x y
  | (n + 1), x, y => ∑ u ∈ S, KpowF K S n x u * K u y

@[simp]
theorem KpowF_zero (K : V → V → ℝ) (S : Finset V) (x y : V) :
    KpowF K S 0 x y = delta x y := rfl

theorem KpowF_succ (K : V → V → ℝ) (S : Finset V) (n : ℕ) (x y : V) :
    KpowF K S (n + 1) x y = ∑ u ∈ S, KpowF K S n x u * K u y := rfl

/-- `Kpow K n x y` is the unrestricted `n`-fold matrix power of the `ℝ≥0∞`-valued kernel
`K`.  It is defined by iterated `tsum`, which is the only available notion for a countably
infinite index type: `Matrix` multiplication requires a `Fintype`. -/
def Kpow (K : V → V → ℝ≥0∞) : ℕ → V → V → ℝ≥0∞
  | 0, x, y => deltaE x y
  | (n + 1), x, y => ∑' u, Kpow K n x u * K u y

@[simp]
theorem Kpow_zero (K : V → V → ℝ≥0∞) (x y : V) : Kpow K 0 x y = deltaE x y := rfl

theorem Kpow_succ (K : V → V → ℝ≥0∞) (n : ℕ) (x y : V) :
    Kpow K (n + 1) x y = ∑' u, Kpow K n x u * K u y := rfl

/-- **Definitional anchor**: the one-fold matrix power is the kernel itself.  This pins down the
exponent convention (the paper's `T^ℓ` is `Kpow K ℓ`). -/
theorem Kpow_one {K : V → V → ℝ≥0∞} (x y : V) : Kpow K 1 x y = K x y := by
  classical
  rw [show (1 : ℕ) = 0 + 1 from rfl, Kpow_succ]
  rw [tsum_eq_single x]
  · simp [deltaE]
  · intro b hb
    have hxb : ¬ (x = b) := fun h => hb h.symm
    simp [Kpow_zero, deltaE, hxb]

/-- The `ℝ≥0∞`-valued value of the truncated power. -/
def KpowS (K : V → V → ℝ) (S : Finset V) (n : ℕ) (x y : V) : ℝ≥0∞ :=
  ENNReal.ofReal (KpowF K S n x y)

theorem KpowS_def (K : V → V → ℝ) (S : Finset V) (n : ℕ) (x y : V) :
    KpowS K S n x y = ENNReal.ofReal (KpowF K S n x y) := rfl

/-! ### Nonnegativity and monotonicity in the truncation set -/

theorem KpowF_nonneg {K : V → V → ℝ} (hK : ∀ a b, 0 ≤ K a b) (S : Finset V) (n : ℕ)
    (x y : V) : 0 ≤ KpowF K S n x y := by
  induction n generalizing x y with
  | zero => simpa using delta_nonneg x y
  | succ n ih =>
    rw [KpowF_succ]
    exact Finset.sum_nonneg fun u _ => mul_nonneg (ih x u) (hK u y)

theorem KpowF_mono {K : V → V → ℝ} (hK : ∀ a b, 0 ≤ K a b) {S S' : Finset V} (h : S ⊆ S')
    (n : ℕ) (x y : V) : KpowF K S n x y ≤ KpowF K S' n x y := by
  induction n generalizing x y with
  | zero => simp
  | succ n ih =>
    rw [KpowF_succ, KpowF_succ]
    calc ∑ u ∈ S, KpowF K S n x u * K u y
        ≤ ∑ u ∈ S, KpowF K S' n x u * K u y :=
          Finset.sum_le_sum fun u _ => mul_le_mul_of_nonneg_right (ih x u) (hK u y)
      _ ≤ ∑ u ∈ S', KpowF K S' n x u * K u y :=
          Finset.sum_le_sum_of_subset_of_nonneg h fun u _ _ =>
            mul_nonneg (KpowF_nonneg hK _ _ _ _) (hK u y)

end PercLib.CriticalLRP.KernelPower
