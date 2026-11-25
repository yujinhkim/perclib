/- Integrated from independently rebuilt Ultramath work, base revision 4140ac56119d2cd80995f91886669efe004839d5.
Scratch source: ../../.ultramath/smwqozn0q/m1/Main.lean ; imports migrated only.
-/

module

/-
Copyright (c) 2026 PercLib contributors. Released under Apache 2.0.
Diagonal maximality of the matrix powers of the native connection kernel.
-/
public import PercLib.CriticalLRP.Analysis.KernelPower.Infinite
public import PercLib.Percolation.Bond.ConnectionKernel

/-!
# Diagonal maximality for the connection kernel

`T^ℓ` is maximized on the diagonal: under translation invariance of the two-point function,
`T^ℓ(x,y) ≤ T^ℓ(x,x)` for every `ℓ` and every `y`, and hence `sup_x T^ℓ(0,x) = T^ℓ(0,0)`.

This is the step "by translation-invariance and positive-definiteness of `T` that `T^ℓ` is
maximized on the diagonal" in the proof of Lemma I.4.18.
-/

@[expose] public section

noncomputable section

open scoped ENNReal

attribute [local instance] Classical.propDecidable

namespace PercLib.CriticalLRP.KernelPower

variable {V : Type*}

/-- `Kpow` depends only on the kernel, pointwise. -/
theorem Kpow_congr {K K' : V → V → ℝ≥0∞} (h : ∀ a b, K a b = K' a b) (n : ℕ) (x y : V) :
    Kpow K n x y = Kpow K' n x y := by
  induction n generalizing x y with
  | zero => simp
  | succ n ih =>
    rw [Kpow_succ, Kpow_succ]
    exact tsum_congr fun u => by rw [ih, h]

/-- A kernel with values in `[0,1]` may be recovered from its real version. -/
theorem Kpow_ofReal_toReal {K : V → V → ℝ≥0∞} (h : ∀ a b, K a b ≠ ⊤) (n : ℕ) (x y : V) :
    Kpow (fun a b => ENNReal.ofReal ((K a b).toReal)) n x y = Kpow K n x y :=
  Kpow_congr (fun a b => ENNReal.ofReal_toReal (h a b)) n x y

/-! ### Translation invariance of matrix powers -/

/-- The Kronecker delta is invariant under a bijection. -/
theorem deltaE_equiv (e : V ≃ V) (x y : V) : deltaE (e x) (e y) = deltaE x y := by
  classical
  unfold deltaE
  simp only [e.injective.eq_iff]

/-- **Translation invariance of matrix powers.**  If the kernel is invariant under a
translation, then so is every matrix power. -/
theorem Kpow_add_invariant [AddCommGroup V] {K : V → V → ℝ}
    (hshift : ∀ (v a b : V), K (a + v) (b + v) = K a b) (n : ℕ) (x y v : V) :
    Kpow (fun a b => ENNReal.ofReal (K a b)) n (x + v) (y + v)
      = Kpow (fun a b => ENNReal.ofReal (K a b)) n x y := by
  induction n generalizing x y v with
  | zero => simpa using deltaE_equiv (Equiv.addRight v) x y
  | succ n ih =>
    rw [Kpow_succ, Kpow_succ]
    have hre : (∑' u : V, Kpow (fun a b => ENNReal.ofReal (K a b)) n (x + v) u *
          ENNReal.ofReal (K u (y + v)))
        = ∑' w : V, Kpow (fun a b => ENNReal.ofReal (K a b)) n (x + v) (w + v) *
            ENNReal.ofReal (K (w + v) (y + v)) :=
      (Equiv.addRight v).tsum_eq
        (fun u => Kpow (fun a b => ENNReal.ofReal (K a b)) n (x + v) u *
          ENNReal.ofReal (K u (y + v))) |>.symm
    rw [hre]
    exact tsum_congr fun w => by rw [ih x w v, hshift v w y]

/-- **The diagonal of a matrix power is constant under translation invariance.** -/
theorem Kpow_diag_eq [AddCommGroup V] {K : V → V → ℝ}
    (hshift : ∀ (v a b : V), K (a + v) (b + v) = K a b) (n : ℕ) (x y : V) :
    Kpow (fun a b => ENNReal.ofReal (K a b)) n y y
      = Kpow (fun a b => ENNReal.ofReal (K a b)) n x x := by
  have h := Kpow_add_invariant hshift n x x (y - x)
  simpa using h

/-- **Diagonal maximality from translation invariance.**  Combining `Kpow_diag_eq` with
`Kpow_le_diag`: if the kernel is invariant under translations and its finite principal
submatrices are positive semidefinite, then every entry of every matrix power is bounded by the
diagonal entry. -/
theorem Kpow_le_diag_of_shift [AddCommGroup V] {K : V → V → ℝ} (hK : ∀ a b, 0 ≤ K a b)
    (hPSD : ∀ S : Finset V, (Matrix.of fun i j : S => K (i : V) (j : V)).PosSemidef)
    (hshift : ∀ (v a b : V), K (a + v) (b + v) = K a b) (n : ℕ) (x y : V) :
    Kpow (fun a b => ENNReal.ofReal (K a b)) n x y ≤
      Kpow (fun a b => ENNReal.ofReal (K a b)) n x x :=
  Kpow_le_diag hK hPSD n x (fun z => Kpow_diag_eq hshift n x z) y

/-! ### The connection kernel -/

open PercLib.Percolation.Bond in
/-- **Diagonal maximality for the native connection kernel.**  For a `Sym2`-valued edge weight
`q` on a countable vertex group whose two-point function is translation invariant, every entry
of every matrix power of the connection kernel is bounded by the corresponding diagonal entry.

`Kpow (fun a b => tau q a b) n x y` is the `n`-th matrix power `T^n_{β,r}(x,y)` of the two-point
function; `n` is the `ℓ` of Lemma I.4.18. -/
theorem tau_Kpow_le_diag [AddCommGroup V] [Countable V] (q : Sym2 V → unitInterval)
    (hshift : ∀ (v a b : V), PercLib.Percolation.Bond.tau q (a + v) (b + v)
      = PercLib.Percolation.Bond.tau q a b) (n : ℕ) (x y : V) :
    Kpow (fun a b => PercLib.Percolation.Bond.tau q a b) n x y ≤
      Kpow (fun a b => PercLib.Percolation.Bond.tau q a b) n x x := by
  classical
  have hKnn : ∀ a b : V, 0 ≤ (PercLib.Percolation.Bond.tau q a b).toReal := fun a b =>
    ENNReal.toReal_nonneg
  have hPSD : ∀ S : Finset V,
      (Matrix.of fun i j : S => (PercLib.Percolation.Bond.tau q (i : V) (j : V)).toReal).PosSemidef :=
    fun S => PercLib.Percolation.Bond.posSemidef_tau q (fun i : S => (i : V))
  have hKshift : ∀ (v a b : V),
      (PercLib.Percolation.Bond.tau q (a + v) (b + v)).toReal
        = (PercLib.Percolation.Bond.tau q a b).toReal := by
    intro v a b
    rw [hshift v a b]
  have hdiag : ∀ y : V,
      Kpow (fun a b => ENNReal.ofReal ((PercLib.Percolation.Bond.tau q a b).toReal)) n y y
        = Kpow (fun a b => ENNReal.ofReal ((PercLib.Percolation.Bond.tau q a b).toReal)) n x x :=
    fun y => Kpow_diag_eq hKshift n x y
  have hmain := Kpow_le_diag hKnn hPSD n x hdiag y
  have hnt : ∀ a b : V, PercLib.Percolation.Bond.tau q a b ≠ ⊤ := fun a b =>
    ne_top_of_le_ne_top ENNReal.one_ne_top (PercLib.Percolation.Bond.tau_le_one q a b)
  rwa [Kpow_ofReal_toReal hnt n x y, Kpow_ofReal_toReal hnt n x x] at hmain

/-- **`sup_x T^ℓ(0,x) = T^ℓ(0,0)`.**  The diagonal of a matrix power of the connection kernel
dominates every entry of the row, so the supremum over `x` is attained at the origin. -/
theorem tau_Kpow_iSup_diag [AddCommGroup V] [Countable V] (q : Sym2 V → unitInterval)
    (hshift : ∀ (v a b : V), PercLib.Percolation.Bond.tau q (a + v) (b + v)
      = PercLib.Percolation.Bond.tau q a b) (n : ℕ) (x : V) :
    (⨆ y : V, Kpow (fun a b => PercLib.Percolation.Bond.tau q a b) n x y) =
      Kpow (fun a b => PercLib.Percolation.Bond.tau q a b) n x x :=
  le_antisymm (iSup_le fun y => tau_Kpow_le_diag q hshift n x y)
    (le_iSup (fun y => Kpow (fun a b => PercLib.Percolation.Bond.tau q a b) n x y) x)

end PercLib.CriticalLRP.KernelPower
