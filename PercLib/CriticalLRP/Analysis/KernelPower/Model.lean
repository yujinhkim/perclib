/- Integrated from independently rebuilt Ultramath work, base revision 4140ac56119d2cd80995f91886669efe004839d5.
Scratch source: ../../.ultramath/smwqozn0q/m1/Model.lean ; imports migrated only.
-/

module

/-
Copyright (c) 2026 PercLib contributors. Released under Apache 2.0.
Diagonal maximality for the two-point function of the long-range model on `Fin d → ℤ`,
including the source's cutoff law `T_{β_c,r}`.
-/
public import PercLib.CriticalLRP.Analysis.KernelPower.Main
public import PercLib.CriticalLRP.CountableProduct.Lattice
public import PercLib.CriticalLRP.Orchestration.Defs

/-!
# Diagonal maximality for `T_{β,r}`

`twoPointFunction J hJ β x y` (the paper's `τ_β(x,y) = P_β(x ↔ y)`) equals the native
connection kernel `tau (bernoulliEdgeProb J hJ β) x y` (`twoPointFunction_eq_tau`), so every
finite principal submatrix of it is positive semidefinite (`posSemidef_tau`).  Its translation
invariance is `twoPointFunction_shift` from the library.  Feeding these two inputs into
`Kpow_le_diag_of_shift` gives

`T^ℓ_{β,r}(x,y) ≤ T^ℓ_{β,r}(x,x)`  and  `sup_x T^ℓ_{β,r}(0,x) = T^ℓ_{β,r}(0,0)`,

the step used at the start of the proof of Lemma I.4.18.
-/

@[expose] public section

noncomputable section

open scoped ENNReal NNReal

attribute [local instance] Classical.propDecidable

open PercLib.CriticalLRP PercLib.CriticalLRP.Orchestration

namespace PercLib.CriticalLRP.KernelPower

/-! ### The two-point function is the native connection kernel -/

/-- The two-point function is the native connection kernel of the corresponding edge
probability. -/
theorem twoPointFunction_eq_tau {V : Type*} [Countable V] (J : Sym2 V → ℝ)
    (hJ : ∀ e, 0 ≤ J e) (β : NNReal) (x y : V) :
    twoPointFunction J hJ β x y
      = PercLib.Percolation.Bond.tau (bernoulliEdgeProb J hJ β) x y := rfl

/-- Every finite principal submatrix of the two-point function is positive semidefinite. -/
theorem posSemidef_twoPointFunction {V : Type*} [Countable V] (J : Sym2 V → ℝ)
    (hJ : ∀ e, 0 ≤ J e) (β : NNReal) :
    ∀ S : Finset V, (Matrix.of fun i j : S =>
      (twoPointFunction J hJ β (i : V) (j : V)).toReal).PosSemidef := by
  intro S
  have h := PercLib.Percolation.Bond.posSemidef_tau (bernoulliEdgeProb J hJ β)
    (fun i : S => (i : V))
  simpa only [twoPointFunction_eq_tau] using h

/-! ### Translation invariance of radial kernels on `Fin d → ℤ` -/

theorem toVec_sub_add {d : ℕ} (x y a : Fin d → ℤ) : toVec ((x + a) - (y + a)) = toVec (x - y) := by
  have h : (x + a) - (y + a) = x - y := by
    funext i
    simp only [Pi.sub_apply, Pi.add_apply]
    ring
  rw [h]

/-- A radial kernel on `Fin d → ℤ` is translation invariant. -/
theorem radialSym_shift {d : ℕ} (S : SourceNormData d) (K : ℝ → ℝ) (a : Fin d → ℤ)
    (e : Sym2 (Fin d → ℤ)) :
    radialSym S K (Sym2.map (fun x => x + a) e) = radialSym S K e := by
  induction e using Sym2.ind with
  | h x y =>
    rw [Sym2.map_mk, radialSym_mk, radialSym_mk]
    have hxy : (x + a = y + a) ↔ (x = y) := by
      constructor
      · intro h
        funext i
        have := congrFun h i
        simpa using this
      · rintro rfl; rfl
    simp only [hxy]
    split_ifs with h
    · rfl
    · simp only [SourceNormData.dist]
      rw [toVec_sub_add]

/-- The cutoff kernel of `SourceModelData` is translation invariant. -/
theorem cutKernel_shift (M : SourceModelData) (r : ℝ) (a : M.V) (e : Sym2 M.V) :
    M.cutKernel r (Sym2.map (fun x => x + a) e) = M.cutKernel r e :=
  radialSym_shift M.S (FiniteVolume.cutoffProfile M.K r) a e

/-- The (uncut) kernel of `SourceModelData` is translation invariant. -/
theorem kernel_shift (M : SourceModelData) (a : M.V) (e : Sym2 M.V) :
    M.kernel (Sym2.map (fun x => x + a) e) = M.kernel e :=
  radialSym_shift M.S M.K a e

/-! ### Diagonal maximality for the two-point function on `Fin d → ℤ` -/

/-- **Diagonal maximality for the two-point function.**  For a translation-invariant edge
weight on `Fin d → ℤ`, every entry of every matrix power of the two-point function is bounded
by the corresponding diagonal entry. -/
theorem twoPointFunction_Kpow_le_diag {d : ℕ} {J : Sym2 (Fin d → ℤ) → ℝ}
    (hJinv : ∀ (a : Fin d → ℤ) (e : Sym2 (Fin d → ℤ)),
      J (Sym2.map (fun x => x + a) e) = J e)
    (hJ : ∀ e, 0 ≤ J e) (β : NNReal) (n : ℕ) (x y : Fin d → ℤ) :
    Kpow (fun a b => twoPointFunction J hJ β a b) n x y
      ≤ Kpow (fun a b => twoPointFunction J hJ β a b) n x x := by
  have hKnn : ∀ a b : Fin d → ℤ, 0 ≤ (twoPointFunction J hJ β a b).toReal :=
    fun a b => ENNReal.toReal_nonneg
  have hPSD := posSemidef_twoPointFunction J hJ β
  have hshift : ∀ (v a b : Fin d → ℤ),
      (twoPointFunction J hJ β (a + v) (b + v)).toReal = (twoPointFunction J hJ β a b).toReal := by
    intro v a b
    rw [twoPointFunction_shift hJinv hJ β v a b]
  have hmain := Kpow_le_diag_of_shift hKnn hPSD hshift n x y
  have hnt : ∀ a b : Fin d → ℤ, twoPointFunction J hJ β a b ≠ ⊤ := fun a b =>
    ne_top_of_le_ne_top ENNReal.one_ne_top (twoPointFunction_le_one J hJ β a b)
  rwa [Kpow_ofReal_toReal hnt n x y, Kpow_ofReal_toReal hnt n x x] at hmain

/-- **`sup_x T^ℓ(0,x) = T^ℓ(0,0)`** for the two-point function of a translation-invariant edge
weight on `Fin d → ℤ`. -/
theorem twoPointFunction_Kpow_iSup_diag {d : ℕ} {J : Sym2 (Fin d → ℤ) → ℝ}
    (hJinv : ∀ (a : Fin d → ℤ) (e : Sym2 (Fin d → ℤ)),
      J (Sym2.map (fun x => x + a) e) = J e)
    (hJ : ∀ e, 0 ≤ J e) (β : NNReal) (n : ℕ) (x : Fin d → ℤ) :
    (⨆ y : Fin d → ℤ, Kpow (fun a b => twoPointFunction J hJ β a b) n x y)
      = Kpow (fun a b => twoPointFunction J hJ β a b) n x x :=
  le_antisymm (iSup_le fun y => twoPointFunction_Kpow_le_diag hJinv hJ β n x y)
    (le_iSup (fun y => Kpow (fun a b => twoPointFunction J hJ β a b) n x y) x)

/-! ### The source's cutoff two-point function `T_{β_c,r}` -/

/-- **Diagonal maximality for the source's cutoff polygon diagram.**  `T^ℓ_{β_c,r}` is the
`ℓ`-fold matrix power of the two-point function of the cutoff law `cutLaw r` at `β_c`; its
diagonal dominates every entry. -/
theorem SourceModelData.cutTwoPoint_Kpow_le_diag (M : SourceModelData) (r : ℝ) (n : ℕ)
    (x y : M.V) :
    Kpow (fun a b : M.V =>
        twoPointFunction (M.cutKernel r) (M.cutKernel_nonneg r) M.betaCrit a b) n x y
      ≤ Kpow (fun a b : M.V =>
          twoPointFunction (M.cutKernel r) (M.cutKernel_nonneg r) M.betaCrit a b) n x x :=
  twoPointFunction_Kpow_le_diag (cutKernel_shift M r) (M.cutKernel_nonneg r) M.betaCrit n x y

/-- **`sup_x T^ℓ_{β_c,r}(0,x) = T^ℓ_{β_c,r}(0,0)`**: the displayed equality in the proof of
Lemma I.4.18, for the source's cutoff law. -/
theorem SourceModelData.cutTwoPoint_Kpow_iSup_diag (M : SourceModelData) (r : ℝ) (n : ℕ) :
    (⨆ y : M.V,
        Kpow (fun a b : M.V =>
          twoPointFunction (M.cutKernel r) (M.cutKernel_nonneg r) M.betaCrit a b) n (0 : M.V) y)
      = Kpow (fun a b : M.V =>
          twoPointFunction (M.cutKernel r) (M.cutKernel_nonneg r) M.betaCrit a b) n (0 : M.V)
          (0 : M.V) :=
  twoPointFunction_Kpow_iSup_diag (cutKernel_shift M r) (M.cutKernel_nonneg r) M.betaCrit n
    (0 : M.V)

/-- **Diagonal maximality for the uncut two-point function** `τ_{β_c}` of the source model. -/
theorem SourceModelData.twoPoint_Kpow_le_diag (M : SourceModelData) (β : ℝ≥0) (n : ℕ)
    (x y : M.V) :
    Kpow (fun a b : M.V => twoPointFunction M.kernel M.kernel_nonneg β a b) n x y
      ≤ Kpow (fun a b : M.V => twoPointFunction M.kernel M.kernel_nonneg β a b) n x x :=
  twoPointFunction_Kpow_le_diag (kernel_shift M) M.kernel_nonneg β n x y

end PercLib.CriticalLRP.KernelPower
