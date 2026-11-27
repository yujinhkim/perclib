/-
Accepted from Ultramath `smwzg77c3`, member `m4`, independently rebuilt.
Production integration based on commit `81c6038182e9a883ffcd3d870aed7cd4829649d4`.
Original direction `d4`.

Copyright (c) 2026 PercLib contributors. Released under Apache 2.0.

# The `q = 0`, `p = 3` per-vertex tree gap: conversion, absorption and invariance

Hutchcroft, *Critical long-range percolation I*, arXiv:2508.18807v1, Lemma I.4.17 at
`p = 3`, `q = 0`.  The left-hand side of that lemma is the connected star moment
`E_{β_c,r}[|K_0|³ 1(y ∈ K_0)]` (`I417Gen.starMoment`, identified with the Case-3 per-vertex
numerator `M.connCubeVertexMass r y` by
`Orchestration.SourceModelData.connCubeVertexMass_eq_starMoment`), and the two surviving terms
are `ℓ = 3` and `ℓ = 4`:

`E[|K_0|³ 1(y ∈ K_0)] ≤ C₃ T³(0,y) χ⁴ + C₄ T⁴(0,y) χ³`.

## What this file proves

* `one_le_chi`, `chi_nonneg` — the honest real-valued susceptibility, `χ ≥ 1` (every cluster
  contains its basepoint), under the finiteness `χ ≠ ⊤`;
* `Kpow_le_succ`, `Kpow_mono_exponent`, `polyK_mono_exponent` — the source's `T^ℓ` is monotone in
  `ℓ`, so `T² ≤ T³ ≤ T⁴`;
* `tau_le_Tpow_three` — `τ(0,y) = T(0,y) ≤ T³(0,y)` (insert the diagonal `T(0,0) = 1` twice);
* `hgap_of_treeFour` — **the absorption**: the labelled-tree residual `FourTermTreeBound` with the
  four classes `ℓ = 1,2,3,4` at degrees `τ χ³`, `T² χ²`, `T³ χ`, `T⁴` implies the source's
  two-term estimate with `C₃ = A + C`, `C₄ = B + D`.  Only `τ ≤ T³`, `T² ≤ T⁴` and `χ ≥ 1` are
  used, so the source's restriction to `ℓ ≥ 3` is not the binding constraint at `q = 0`;
* `hgap_of_tauChi` — the single-term residual `E[|K_0|³1(y ∈ K_0)] ≤ A τ(0,y) χ⁴` implies the
  target with `C₃ = A`, `C₄ = 0`;
* `hgap_of_KpowTwoTerm` — the honest `ℝ≥0∞ → ℝ` conversion: the natural parent statement
  `KpowTwoTerm` (extended-real matrix powers `Kpow (M.cutTwoPointE r)`, `ℝ≥0∞` mass
  `M.cutMassAt r 0`, coefficients `ofReal C₃`) yields the real per-vertex target, with the
  finiteness of every factor carried explicitly (`χ ≠ ⊤`); no `⊤ ↦ 0` conversion is made;
* `polyK_shift`, `polyK_root_indep`, `chi_root_indep` — the translation invariance and root
  independence guards: `T^ℓ(x,y)` depends only on `y − x` and `χ` does not depend on the vertex.

## What is *not* proved here

`FourTermTreeBound` and `TauChiBound` are recorded as named residuals (`Defs.lean`), not derived.
The module notes explain exactly which labelled-tree class is the obstruction.
-/
module

public import PercLib.CriticalLRP.Correlation.I417.General.QZeroReduction.Defs
public import PercLib.CriticalLRP.Analysis.Cutoff.Translation
public import PercLib.CriticalLRP.Analysis.KernelPower.Main

/-! # `q = 0`, `p = 3`: conversion, absorption and invariance -/

noncomputable section

open MeasureTheory Measure ProbabilityTheory unitInterval
open scoped ENNReal NNReal

set_option linter.unusedSectionVars false

@[expose] public section

namespace PercLib.CriticalLRP.M4QZero

open PercLib.CriticalLRP Orchestration
open PercLib.CriticalLRP.KernelPower

attribute [local instance] Classical.propDecidable

variable (M : SourceModelData)

/-! ## The susceptibility: `χ ≥ 1` -/

/-- Every cluster contains its basepoint, so its volume is at least one. -/
theorem one_le_clusterVol (ω : Config M.V) (v : M.V) : 1 ≤ clusterVol ω v := by
  rw [clusterVol_eq_encard, ← Percolation.cardFun_eq_encard]
  exact I417Gen.one_le_cardFun_cluster ω v

/-- The cutoff cluster mass at the origin is at least one. -/
theorem one_le_cutMassAt_zero (r : ℝ) : 1 ≤ M.cutMassAt r 0 := by
  have h := M.one_le_cutMoment_one r
  simpa only [SourceModelData.cutMoment, SourceModelData.cutMassAt, pow_one] using h

/-- `χ = (E_{β_c,r}|K|)` is at least one, in real form. -/
theorem one_le_chi (r : ℝ) (hχ : M.cutMassAt r 0 ≠ ⊤) : 1 ≤ chi M r := by
  have h := ENNReal.toReal_mono hχ (one_le_cutMassAt_zero M r)
  simpa using h

theorem chi_nonneg (r : ℝ) : 0 ≤ chi M r := ENNReal.toReal_nonneg

/-! ## `T^ℓ` is monotone in `ℓ` -/

/-- `T^n ≤ T^{n+1}`: the diagonal entry `T(y,y) = 1` inserts a dummy step. -/
theorem Kpow_le_succ (r : ℝ) (n : ℕ) (x y : M.V) :
    Kpow (M.cutTwoPointE r) n x y ≤ Kpow (M.cutTwoPointE r) (n + 1) x y := by
  rw [Kpow_succ]
  calc Kpow (M.cutTwoPointE r) n x y
      = Kpow (M.cutTwoPointE r) n x y * 1 := (mul_one _).symm
    _ = Kpow (M.cutTwoPointE r) n x y * M.cutTwoPointE r y y := by
        rw [M.cutTwoPointE_self_eq_one]
    _ ≤ ∑' u, Kpow (M.cutTwoPointE r) n x u * M.cutTwoPointE r u y :=
        ENNReal.le_tsum (f := fun u : M.V =>
          Kpow (M.cutTwoPointE r) n x u * M.cutTwoPointE r u y) y

/-- `T^n` is monotone in the exponent. -/
theorem Kpow_mono_exponent (r : ℝ) (x y : M.V) :
    Monotone fun n : ℕ => Kpow (M.cutTwoPointE r) n x y :=
  monotone_nat_of_le_succ fun n => Kpow_le_succ M r n x y

/-- The real polygon power `T^ℓ(0,y)` is monotone in `ℓ`, under `χ ≠ ⊤`. -/
theorem polyK_mono_exponent (r : ℝ) (hχ : M.cutMassAt r 0 ≠ ⊤) {m n : ℕ} (hmn : m ≤ n)
    (y : M.V) : Tpow M r m y ≤ Tpow M r n y := by
  simp only [Tpow_def]
  rw [← M.cutKpow_toReal_eq_polyK r hχ m 0 y,
    ← M.cutKpow_toReal_eq_polyK r hχ n 0 y]
  exact ENNReal.toReal_mono (M.cutKpow_ne_top_of_chi_ne_top r hχ n 0 y)
    (Kpow_mono_exponent M r 0 y hmn)

/-- **`τ(0,y) ≤ T³(0,y)`**: the path `0 → 0 → 0 → y` inside the threefold power. -/
theorem tau_le_Tpow_three (r : ℝ) (hχ : M.cutMassAt r 0 ≠ ⊤) (y : M.V) :
    M.cutTwoPoint r 0 y ≤ Tpow M r 3 y := by
  have h13 : (1 : ℕ) ≤ 3 := by norm_num
  calc M.cutTwoPoint r 0 y
      = (M.cutTwoPointE r 0 y).toReal := by
          rw [M.cutTwoPointE_eq_ofReal, ENNReal.toReal_ofReal (M.cutTwoPoint_nonneg r 0 y)]
    _ = (Kpow (M.cutTwoPointE r) 1 0 y).toReal := by rw [Kpow_one]
    _ ≤ (Kpow (M.cutTwoPointE r) 3 0 y).toReal :=
        ENNReal.toReal_mono (M.cutKpow_ne_top_of_chi_ne_top r hχ 3 0 y)
          (Kpow_mono_exponent M r 0 y h13)
    _ = Tpow M r 3 y := by rw [Tpow_def, M.cutKpow_toReal_eq_polyK r hχ 3 0 y]

/-! ## The absorption: four labelled-tree classes give the source's two terms -/

/-- **The target follows from the labelled-tree residual.**

`FourTermTreeBound M r y A B C D` records the four `ℓ = 1,2,3,4` classes of the tree-graph bound
for the labels `y, x₁, x₂, x₃` at their exact degrees `τ χ³`, `T² χ²`, `T³ χ`, `T⁴`.  Each class
absorbs into the source's `ℓ = 3` or `ℓ = 4` term using only `τ ≤ T³`, `T² ≤ T⁴ ≤ T³` and
`χ ≥ 1`:
`A τ χ³ ≤ A T³ χ⁴`, `B T² χ² ≤ B T⁴ χ³`, `C T³ χ ≤ C T³ χ⁴`, `D T⁴ ≤ D T⁴ χ³`. -/
theorem hgap_of_treeFour (r : ℝ) (hχ : M.cutMassAt r 0 ≠ ⊤) (y : M.V)
    {A B C D : ℝ} (hA : 0 ≤ A) (hB : 0 ≤ B) (hC : 0 ≤ C) (hD : 0 ≤ D)
    (h : FourTermTreeBound M r y A B C D) :
    TwoTermTarget M r y (A + C) (B + D) := by
  have hχ1 : 1 ≤ chi M r := one_le_chi M r hχ
  have hχ0 : 0 ≤ chi M r := chi_nonneg M r
  have hτ0 : 0 ≤ M.cutTwoPoint r 0 y := M.cutTwoPoint_nonneg r 0 y
  have hT2 : 0 ≤ Tpow M r 2 y :=
    I418C.polyK_nonneg _ (fun a b => M.cutTwoPoint_nonneg r a b) 2 0 y
  have hT3 : 0 ≤ Tpow M r 3 y :=
    I418C.polyK_nonneg _ (fun a b => M.cutTwoPoint_nonneg r a b) 3 0 y
  have hT4 : 0 ≤ Tpow M r 4 y :=
    I418C.polyK_nonneg _ (fun a b => M.cutTwoPoint_nonneg r a b) 4 0 y
  have hτ3 : M.cutTwoPoint r 0 y ≤ Tpow M r 3 y := tau_le_Tpow_three M r hχ y
  have h23 : Tpow M r 2 y ≤ Tpow M r 3 y :=
    polyK_mono_exponent M r hχ (m := 2) (n := 3) (by norm_num) y
  have h34 : Tpow M r 3 y ≤ Tpow M r 4 y :=
    polyK_mono_exponent M r hχ (m := 3) (n := 4) (by norm_num) y
  have h24 : Tpow M r 2 y ≤ Tpow M r 4 y := le_trans h23 h34
  -- the four real classes, and their absorption
  have hterm1 : A * M.cutTwoPoint r 0 y * chi M r ^ 3 ≤ A * Tpow M r 3 y * chi M r ^ 4 := by
    have hstep : A * M.cutTwoPoint r 0 y * chi M r ^ 3 ≤ A * Tpow M r 3 y * chi M r ^ 3 := by
      have := mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hτ3 hA) (pow_nonneg hχ0 3)
      simpa [mul_assoc] using this
    have hpow : chi M r ^ 3 ≤ chi M r ^ 4 := pow_le_pow_right₀ hχ1 (by norm_num)
    have hstep2 : A * Tpow M r 3 y * chi M r ^ 3 ≤ A * Tpow M r 3 y * chi M r ^ 4 := by
      have := mul_le_mul_of_nonneg_left hpow (mul_nonneg hA hT3)
      simpa [mul_assoc] using this
    linarith
  have hterm2 : B * Tpow M r 2 y * chi M r ^ 2 ≤ B * Tpow M r 4 y * chi M r ^ 3 := by
    have hstep : B * Tpow M r 2 y * chi M r ^ 2 ≤ B * Tpow M r 4 y * chi M r ^ 2 := by
      have := mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left h24 hB) (pow_nonneg hχ0 2)
      simpa [mul_assoc] using this
    have hpow : chi M r ^ 2 ≤ chi M r ^ 3 := pow_le_pow_right₀ hχ1 (by norm_num)
    have hstep2 : B * Tpow M r 4 y * chi M r ^ 2 ≤ B * Tpow M r 4 y * chi M r ^ 3 := by
      have := mul_le_mul_of_nonneg_left hpow (mul_nonneg hB hT4)
      simpa [mul_assoc] using this
    linarith
  have hterm3 : C * Tpow M r 3 y * chi M r ≤ C * Tpow M r 3 y * chi M r ^ 4 := by
    have hpow : chi M r ^ 1 ≤ chi M r ^ 4 := pow_le_pow_right₀ hχ1 (by norm_num)
    have := mul_le_mul_of_nonneg_left hpow (mul_nonneg hC hT3)
    simpa [pow_one, mul_assoc] using this
  have hterm4 : D * Tpow M r 4 y ≤ D * Tpow M r 4 y * chi M r ^ 3 := by
    have hpow : (1 : ℝ) ≤ chi M r ^ 3 := one_le_pow₀ hχ1
    calc D * Tpow M r 4 y = D * Tpow M r 4 y * 1 := (mul_one _).symm
      _ ≤ D * Tpow M r 4 y * chi M r ^ 3 :=
          mul_le_mul_of_nonneg_left hpow (mul_nonneg hD hT4)
  have hR0 : 0 ≤ A * M.cutTwoPoint r 0 y * chi M r ^ 3 + B * Tpow M r 2 y * chi M r ^ 2
      + C * Tpow M r 3 y * chi M r + D * Tpow M r 4 y := by
    have h1 : 0 ≤ A * M.cutTwoPoint r 0 y * chi M r ^ 3 :=
      mul_nonneg (mul_nonneg hA hτ0) (pow_nonneg hχ0 3)
    have h2 : 0 ≤ B * Tpow M r 2 y * chi M r ^ 2 :=
      mul_nonneg (mul_nonneg hB hT2) (pow_nonneg hχ0 2)
    have h3 : 0 ≤ C * Tpow M r 3 y * chi M r := mul_nonneg (mul_nonneg hC hT3) hχ0
    have h4 : 0 ≤ D * Tpow M r 4 y := mul_nonneg hD hT4
    linarith
  have key : A * M.cutTwoPoint r 0 y * chi M r ^ 3 + B * Tpow M r 2 y * chi M r ^ 2
      + C * Tpow M r 3 y * chi M r + D * Tpow M r 4 y
      ≤ (A + C) * Tpow M r 3 y * chi M r ^ 4 + (B + D) * Tpow M r 4 y * chi M r ^ 3 := by
    calc A * M.cutTwoPoint r 0 y * chi M r ^ 3 + B * Tpow M r 2 y * chi M r ^ 2
          + C * Tpow M r 3 y * chi M r + D * Tpow M r 4 y
        ≤ A * Tpow M r 3 y * chi M r ^ 4 + B * Tpow M r 4 y * chi M r ^ 3
          + C * Tpow M r 3 y * chi M r ^ 4 + D * Tpow M r 4 y * chi M r ^ 3 :=
          add_le_add (add_le_add (add_le_add hterm1 hterm2) hterm3) hterm4
      _ = (A + C) * Tpow M r 3 y * chi M r ^ 4 + (B + D) * Tpow M r 4 y * chi M r ^ 3 := by
          ring
  rw [TwoTermTarget, M.connCubeVertexMass_eq_starMoment]
  refine le_trans (ENNReal.toReal_mono ENNReal.ofReal_ne_top h) ?_
  rw [ENNReal.toReal_ofReal hR0]
  exact key

/-- **The target follows from the single-term residual** `E[|K_0|³1(y∈K_0)] ≤ A τ(0,y) χ⁴`. -/
theorem hgap_of_tauChi (r : ℝ) (hχ : M.cutMassAt r 0 ≠ ⊤) (y : M.V)
    {A : ℝ} (hA : 0 ≤ A) (h : TauChiBound M r y A) : TwoTermTarget M r y A 0 := by
  have hχ1 : 1 ≤ chi M r := one_le_chi M r hχ
  have hχ0 : 0 ≤ chi M r := chi_nonneg M r
  have hτ0 : 0 ≤ M.cutTwoPoint r 0 y := M.cutTwoPoint_nonneg r 0 y
  have hT3 : 0 ≤ Tpow M r 3 y :=
    I418C.polyK_nonneg _ (fun a b => M.cutTwoPoint_nonneg r a b) 3 0 y
  have hτ3 : M.cutTwoPoint r 0 y ≤ Tpow M r 3 y := tau_le_Tpow_three M r hχ y
  have hR0 : 0 ≤ A * M.cutTwoPoint r 0 y * chi M r ^ 4 :=
    mul_nonneg (mul_nonneg hA hτ0) (pow_nonneg hχ0 4)
  rw [TwoTermTarget, M.connCubeVertexMass_eq_starMoment]
  refine le_trans (ENNReal.toReal_mono ENNReal.ofReal_ne_top h) ?_
  rw [ENNReal.toReal_ofReal hR0]
  have hstep : A * M.cutTwoPoint r 0 y * chi M r ^ 4 ≤ A * Tpow M r 3 y * chi M r ^ 4 := by
    have := mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hτ3 hA) (pow_nonneg hχ0 4)
    simpa [mul_assoc] using this
  have hz : (0 : ℝ) * Tpow M r 4 y * chi M r ^ 3 = 0 := by ring
  linarith

/-- **The target follows from the tree-graph classes other than the degree-five one.**

`TreeClassesBound M r y A B C D E` is the tree-graph bound with the five absorbable classes kept
individually; the three non-absorbable classes `T χ⁵`, `T χ⁶`, `T² χ⁵` are excluded (see
`deep_class_not_absorbable`).  Each retained class absorbs into the source's `ℓ = 3` term using
only `τ ≤ T³`, `T² ≤ T³` and `χ ≥ 1`. -/
theorem hgap_of_treeClasses (r : ℝ) (hχ : M.cutMassAt r 0 ≠ ⊤) (y : M.V)
    {A B C D E : ℝ} (hA : 0 ≤ A) (hB : 0 ≤ B) (hC : 0 ≤ C) (hD : 0 ≤ D) (hE : 0 ≤ E)
    (h : TreeClassesBound M r y A B C D E) :
    TwoTermTarget M r y (A + B + C + D) E := by
  have hχ1 : 1 ≤ chi M r := one_le_chi M r hχ
  have hχ0 : 0 ≤ chi M r := chi_nonneg M r
  have hτ0 : 0 ≤ M.cutTwoPoint r 0 y := M.cutTwoPoint_nonneg r 0 y
  have hT2 : 0 ≤ Tpow M r 2 y :=
    I418C.polyK_nonneg _ (fun a b => M.cutTwoPoint_nonneg r a b) 2 0 y
  have hT3 : 0 ≤ Tpow M r 3 y :=
    I418C.polyK_nonneg _ (fun a b => M.cutTwoPoint_nonneg r a b) 3 0 y
  have hT4 : 0 ≤ Tpow M r 4 y :=
    I418C.polyK_nonneg _ (fun a b => M.cutTwoPoint_nonneg r a b) 4 0 y
  have hτ3 : M.cutTwoPoint r 0 y ≤ Tpow M r 3 y := tau_le_Tpow_three M r hχ y
  have h23 : Tpow M r 2 y ≤ Tpow M r 3 y :=
    polyK_mono_exponent M r hχ (m := 2) (n := 3) (by norm_num) y
  have hp3 : chi M r ^ 3 ≤ chi M r ^ 4 := pow_le_pow_right₀ hχ1 (by norm_num)
  have hR0 : 0 ≤ A * M.cutTwoPoint r 0 y * chi M r ^ 3 + B * Tpow M r 2 y * chi M r ^ 4
      + C * Tpow M r 3 y * chi M r ^ 3 + D * Tpow M r 3 y * chi M r ^ 4
      + E * Tpow M r 4 y * chi M r ^ 3 := by
    have h1 : 0 ≤ A * M.cutTwoPoint r 0 y * chi M r ^ 3 :=
      mul_nonneg (mul_nonneg hA hτ0) (pow_nonneg hχ0 3)
    have h2 : 0 ≤ B * Tpow M r 2 y * chi M r ^ 4 :=
      mul_nonneg (mul_nonneg hB hT2) (pow_nonneg hχ0 4)
    have h3 : 0 ≤ C * Tpow M r 3 y * chi M r ^ 3 :=
      mul_nonneg (mul_nonneg hC hT3) (pow_nonneg hχ0 3)
    have h4 : 0 ≤ D * Tpow M r 3 y * chi M r ^ 4 :=
      mul_nonneg (mul_nonneg hD hT3) (pow_nonneg hχ0 4)
    have h5 : 0 ≤ E * Tpow M r 4 y * chi M r ^ 3 :=
      mul_nonneg (mul_nonneg hE hT4) (pow_nonneg hχ0 3)
    linarith
  have k1 : A * M.cutTwoPoint r 0 y * chi M r ^ 3 ≤ A * Tpow M r 3 y * chi M r ^ 4 := by
    have hs : A * M.cutTwoPoint r 0 y * chi M r ^ 3 ≤ A * Tpow M r 3 y * chi M r ^ 3 := by
      have := mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hτ3 hA) (pow_nonneg hχ0 3)
      simpa [mul_assoc] using this
    have hs2 : A * Tpow M r 3 y * chi M r ^ 3 ≤ A * Tpow M r 3 y * chi M r ^ 4 := by
      have := mul_le_mul_of_nonneg_left hp3 (mul_nonneg hA hT3)
      simpa [mul_assoc] using this
    linarith
  have k2 : B * Tpow M r 2 y * chi M r ^ 4 ≤ B * Tpow M r 3 y * chi M r ^ 4 := by
    have := mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left h23 hB) (pow_nonneg hχ0 4)
    simpa [mul_assoc] using this
  have k3 : C * Tpow M r 3 y * chi M r ^ 3 ≤ C * Tpow M r 3 y * chi M r ^ 4 := by
    have := mul_le_mul_of_nonneg_left hp3 (mul_nonneg hC hT3)
    simpa [mul_assoc] using this
  have key : A * M.cutTwoPoint r 0 y * chi M r ^ 3 + B * Tpow M r 2 y * chi M r ^ 4
      + C * Tpow M r 3 y * chi M r ^ 3 + D * Tpow M r 3 y * chi M r ^ 4
      + E * Tpow M r 4 y * chi M r ^ 3
      ≤ (A + B + C + D) * Tpow M r 3 y * chi M r ^ 4 + E * Tpow M r 4 y * chi M r ^ 3 := by
    calc A * M.cutTwoPoint r 0 y * chi M r ^ 3 + B * Tpow M r 2 y * chi M r ^ 4
          + C * Tpow M r 3 y * chi M r ^ 3 + D * Tpow M r 3 y * chi M r ^ 4
          + E * Tpow M r 4 y * chi M r ^ 3
        ≤ A * Tpow M r 3 y * chi M r ^ 4 + B * Tpow M r 3 y * chi M r ^ 4
          + C * Tpow M r 3 y * chi M r ^ 4 + D * Tpow M r 3 y * chi M r ^ 4
          + E * Tpow M r 4 y * chi M r ^ 3 := by
          linarith [k1, k2, k3]
      _ = (A + B + C + D) * Tpow M r 3 y * chi M r ^ 4 + E * Tpow M r 4 y * chi M r ^ 3 := by
          ring
  rw [TwoTermTarget, M.connCubeVertexMass_eq_starMoment]
  refine le_trans (ENNReal.toReal_mono ENNReal.ofReal_ne_top h) ?_
  rw [ENNReal.toReal_ofReal hR0]
  exact key

/-- **The degree-five class `T² χ⁵` is not absorbable.**

The tree-graph bound for the five leaves `0, y, x₁, x₂, x₃` produces, in addition to the
absorbable classes, the class `T²(0,y) χ⁵` (a reduced tree with `p = 3` branch vertices whose
`0`–`y` path has length `ℓ = 2`, so that five off-path free vertices are charged).  No absorption
of that class into the source's `T³ χ⁴ + T⁴ χ³` follows from the structural facts used for all the
others (`0 ≤ T² ≤ T³ ≤ T⁴`, `χ ≥ 1`): for every candidate constant `K` there is a tuple with
`T² = 1`, `T³ = 3`, `T⁴ = 8` and `χ` large where the class exceeds `K` times the right-hand
side.  (The tuple `(1, 3, 8)` with `χ = 1 + m` is realised by the explicit
nonnegative symmetric kernel on `{0, y} ∪ {a_1,…,a_{m²}}` with `τ(0,a_i) = τ(y,a_i) = 1/m` and
`τ(0,y) = 0`, whose row sums are at most `χ`; see `derivation.md`.) -/
theorem degree_five_class_not_absorbable (K : ℝ) :
    ∃ T2 T3 T4 χ : ℝ, 0 ≤ T2 ∧ T2 ≤ T3 ∧ T3 ≤ T4 ∧ 1 ≤ χ ∧
      K * (T3 * χ ^ 4 + T4 * χ ^ 3) < T2 * χ ^ 5 := by
  refine ⟨1, 3, 8, 3 * |K| + 10, by norm_num, by norm_num, by norm_num, ?_, ?_⟩
  · have h := abs_nonneg K
    linarith
  set χ : ℝ := 3 * |K| + 10 with hχdef
  have hχ : 0 < χ := by positivity
  have key : K * (3 * χ + 8) < χ ^ 2 := by
    have h1 : K * (3 * χ + 8) ≤ |K| * (3 * χ + 8) :=
      mul_le_mul_of_nonneg_right (le_abs_self K) (by positivity)
    have h2 : |K| * (3 * χ + 8) < χ ^ 2 := by
      have hK : (0 : ℝ) ≤ |K| := abs_nonneg K
      rw [hχdef]
      nlinarith [mul_nonneg hK hK]
    linarith
  have hfinal : (K * (3 * χ + 8)) * χ ^ 3 < χ ^ 5 := by
    have := mul_lt_mul_of_pos_right key (pow_pos hχ 3)
    calc (K * (3 * χ + 8)) * χ ^ 3 < χ ^ 2 * χ ^ 3 := this
      _ = χ ^ 5 := by ring
  have heq : K * (3 * χ ^ 4 + 8 * χ ^ 3) = (K * (3 * χ + 8)) * χ ^ 3 := by ring
  rw [heq]
  simpa using hfinal

/-- **Every deep class `T χ^m`, `m ≥ 5`, is not absorbable.**

For `m ≥ 5` the class `T χ^m` (produced by the tree-graph bound with `T = T^ℓ`, `ℓ ≤ 2`, for the
shapes whose off-path subtree is deep and whose `0`–`y` path is short) exceeds `K` times
`T³ χ⁴ + T⁴ χ³` for every `K`, in the same one-parameter family.  Together with
`degree_five_class_not_absorbable` this pins down exactly the three classes `T χ⁵`, `T χ⁶`,
`T² χ⁵` that a proof must produce by other means. -/
theorem deep_class_not_absorbable (K : ℝ) (m : ℕ) (hm : 5 ≤ m) :
    ∃ T T3 T4 χ : ℝ, 0 ≤ T ∧ T ≤ T3 ∧ T3 ≤ T4 ∧ 1 ≤ χ ∧
      K * (T3 * χ ^ 4 + T4 * χ ^ 3) < T * χ ^ m := by
  refine ⟨1, 3, 8, 3 * |K| + 10, by norm_num, by norm_num, by norm_num, ?_, ?_⟩
  · have h := abs_nonneg K
    linarith
  set χ : ℝ := 3 * |K| + 10 with hχdef
  have hχ : 0 < χ := by positivity
  have key : K * (3 * χ + 8) < χ ^ 2 := by
    have h1 : K * (3 * χ + 8) ≤ |K| * (3 * χ + 8) :=
      mul_le_mul_of_nonneg_right (le_abs_self K) (by positivity)
    have h2 : |K| * (3 * χ + 8) < χ ^ 2 := by
      have hK : (0 : ℝ) ≤ |K| := abs_nonneg K
      rw [hχdef]
      nlinarith [mul_nonneg hK hK]
    linarith
  have hχ1 : 1 ≤ χ := by
    have h := abs_nonneg K
    rw [hχdef]
    linarith
  calc K * (3 * χ ^ 4 + 8 * χ ^ 3)
      = (K * (3 * χ + 8)) * χ ^ 3 := by ring
    _ < (χ ^ 2) * χ ^ 3 := mul_lt_mul_of_pos_right key (pow_pos hχ 3)
    _ = χ ^ 5 := by ring
    _ ≤ χ ^ m := pow_le_pow_right₀ hχ1 hm
    _ = 1 * χ ^ m := by ring

/-! ## The honest `ℝ≥0∞ → ℝ` conversion -/

/-- **The natural `ℝ≥0∞` parent implies the real target, with no loss.**

The only analytic input is the finiteness of the cutoff susceptibility `χ = M.cutMassAt r 0 ≠ ⊤`,
which makes every extended-real matrix power finite (`cutKpow_ne_top_of_chi_ne_top`) and hence every
product in the parent statement finite.  All `toReal` steps are applied to finite quantities, so no
`⊤ ↦ 0` convention is used. -/
theorem hgap_of_KpowTwoTerm (r : ℝ) (hχ : M.cutMassAt r 0 ≠ ⊤) (y : M.V)
    {C3 C4 : ℝ} (h3 : 0 ≤ C3) (h4 : 0 ≤ C4) (h : KpowTwoTerm M r y C3 C4) :
    TwoTermTarget M r y C3 C4 := by
  have hk3 : Kpow (M.cutTwoPointE r) 3 (0 : M.V) y ≠ ⊤ :=
    M.cutKpow_ne_top_of_chi_ne_top r hχ 3 0 y
  have hk4 : Kpow (M.cutTwoPointE r) 4 (0 : M.V) y ≠ ⊤ :=
    M.cutKpow_ne_top_of_chi_ne_top r hχ 4 0 y
  have hp4 : (M.cutMassAt r 0) ^ 4 ≠ ⊤ := ENNReal.pow_ne_top hχ
  have hp3 : (M.cutMassAt r 0) ^ 3 ≠ ⊤ := ENNReal.pow_ne_top hχ
  have hfin1 : ENNReal.ofReal C3 * Kpow (M.cutTwoPointE r) 3 0 y * (M.cutMassAt r 0) ^ 4
      ≠ ⊤ := ENNReal.mul_ne_top (ENNReal.mul_ne_top ENNReal.ofReal_ne_top hk3) hp4
  have hfin2 : ENNReal.ofReal C4 * Kpow (M.cutTwoPointE r) 4 0 y * (M.cutMassAt r 0) ^ 3
      ≠ ⊤ := ENNReal.mul_ne_top (ENNReal.mul_ne_top ENNReal.ofReal_ne_top hk4) hp3
  have hfin : ENNReal.ofReal C3 * Kpow (M.cutTwoPointE r) 3 0 y * (M.cutMassAt r 0) ^ 4
      + ENNReal.ofReal C4 * Kpow (M.cutTwoPointE r) 4 0 y * (M.cutMassAt r 0) ^ 3 ≠ ⊤ :=
    ENNReal.add_ne_top.2 ⟨hfin1, hfin2⟩
  rw [TwoTermTarget, M.connCubeVertexMass_eq_starMoment]
  refine le_trans (ENNReal.toReal_mono hfin h) ?_
  rw [ENNReal.toReal_add hfin1 hfin2, ENNReal.toReal_mul, ENNReal.toReal_mul,
    ENNReal.toReal_mul, ENNReal.toReal_mul, ENNReal.toReal_ofReal h3, ENNReal.toReal_ofReal h4,
    ENNReal.toReal_pow, ENNReal.toReal_pow,
    M.cutKpow_toReal_eq_polyK r hχ 3 0 y, M.cutKpow_toReal_eq_polyK r hχ 4 0 y]
  simp only [Tpow_def, chi_def]
  exact le_rfl

/-- **The same conversion for the `cutPoly` parent.**  `I420Case3.cutPoly M r y j` is by
definition `ofReal (polyK (cutTwoPoint r) j 0 y)`, so the only finiteness needed here is `χ ≠ ⊤`
(the polygon entries are automatically finite, being `ofReal` of a real number). -/
theorem hgap_of_cutPolyTwoTerm (r : ℝ) (hχ : M.cutMassAt r 0 ≠ ⊤) (y : M.V)
    {C3 C4 : ℝ} (h3 : 0 ≤ C3) (h4 : 0 ≤ C4) (h : CutPolyTwoTerm M r y C3 C4) :
    TwoTermTarget M r y C3 C4 := by
  have hp4 : (M.cutMassAt r 0) ^ 4 ≠ ⊤ := ENNReal.pow_ne_top hχ
  have hp3 : (M.cutMassAt r 0) ^ 3 ≠ ⊤ := ENNReal.pow_ne_top hχ
  have hfin1 : ENNReal.ofReal C3 * I420Case3.cutPoly M r y 3 * (M.cutMassAt r 0) ^ 4 ≠ ⊤ :=
    ENNReal.mul_ne_top
      (ENNReal.mul_ne_top ENNReal.ofReal_ne_top ENNReal.ofReal_ne_top) hp4
  have hfin2 : ENNReal.ofReal C4 * I420Case3.cutPoly M r y 4 * (M.cutMassAt r 0) ^ 3 ≠ ⊤ :=
    ENNReal.mul_ne_top
      (ENNReal.mul_ne_top ENNReal.ofReal_ne_top ENNReal.ofReal_ne_top) hp3
  have hfin : ENNReal.ofReal C3 * I420Case3.cutPoly M r y 3 * (M.cutMassAt r 0) ^ 4
      + ENNReal.ofReal C4 * I420Case3.cutPoly M r y 4 * (M.cutMassAt r 0) ^ 3 ≠ ⊤ :=
    ENNReal.add_ne_top.2 ⟨hfin1, hfin2⟩
  have hp3nn : 0 ≤ I418C.polyK (M.cutTwoPoint r) 3 (0 : M.V) y :=
    I418C.polyK_nonneg _ (fun a b => M.cutTwoPoint_nonneg r a b) 3 0 y
  have hp4nn : 0 ≤ I418C.polyK (M.cutTwoPoint r) 4 (0 : M.V) y :=
    I418C.polyK_nonneg _ (fun a b => M.cutTwoPoint_nonneg r a b) 4 0 y
  rw [TwoTermTarget, M.connCubeVertexMass_eq_starMoment]
  refine le_trans (ENNReal.toReal_mono hfin h) ?_
  simp only [I420Case3.cutPoly] at hfin1 hfin2 hfin ⊢
  rw [ENNReal.toReal_add hfin1 hfin2, ENNReal.toReal_mul, ENNReal.toReal_mul,
    ENNReal.toReal_mul, ENNReal.toReal_mul, ENNReal.toReal_ofReal h3, ENNReal.toReal_ofReal h4,
    ENNReal.toReal_ofReal hp3nn, ENNReal.toReal_ofReal hp4nn, ENNReal.toReal_pow,
    ENNReal.toReal_pow]
  simp only [Tpow_def, chi_def]
  exact le_rfl

/-- **The target in the literal `polyK` shape** used by
`SecondMomentCase3.connCubeMass_toReal_le_of_perVertex_gap`. -/
theorem twoTermTarget_polyK (r : ℝ) (y : M.V) {C3 C4 : ℝ}
    (h : TwoTermTarget M r y C3 C4) :
    (M.connCubeVertexMass r y).toReal
      ≤ C3 * I418C.polyK (M.cutTwoPoint r) 3 (0 : M.V) y * (M.cutMassAt r 0).toReal ^ 4
        + C4 * I418C.polyK (M.cutTwoPoint r) 4 (0 : M.V) y * (M.cutMassAt r 0).toReal ^ 3 :=
  h

/-! ## Translation invariance and root independence -/

/-- **Translation invariance of the polygon powers.**  `T^ℓ` is a function of `y − x` only. -/
theorem polyK_shift (r : ℝ) (hχ : M.cutMassAt r 0 ≠ ⊤) (n : ℕ) (v x y : M.V) :
    I418C.polyK (M.cutTwoPoint r) n (x + v) (y + v) = I418C.polyK (M.cutTwoPoint r) n x y := by
  rw [← M.cutKpow_toReal_eq_polyK r hχ n (x + v) (y + v),
    ← M.cutKpow_toReal_eq_polyK r hχ n x y]
  rw [Kpow_congr (K := M.cutTwoPointE r)
      (K' := fun a b => ENNReal.ofReal (M.cutTwoPoint r a b))
      (fun a b => M.cutTwoPointE_eq_ofReal r a b) n (x + v) (y + v),
    Kpow_congr (K := M.cutTwoPointE r)
      (K' := fun a b => ENNReal.ofReal (M.cutTwoPoint r a b))
      (fun a b => M.cutTwoPointE_eq_ofReal r a b) n x y,
    Kpow_add_invariant (K := M.cutTwoPoint r)
      (fun v a b => M.cutTwoPoint_translate r v a b) n x y v]

/-- **Root independence of the polygon powers**: the entry depends only on the difference. -/
theorem polyK_root_indep (r : ℝ) (hχ : M.cutMassAt r 0 ≠ ⊤) (n : ℕ) (x y : M.V) :
    I418C.polyK (M.cutTwoPoint r) n x y = Tpow M r n (y - x) := by
  rw [Tpow_def, sub_eq_add_neg]
  simpa using (polyK_shift M r hχ n (-x) x y).symm

/-- **Translation invariance of the connected star moment.**

`E|K_x|^p 1(x ↔ y)` depends only on `y - x`: shifting the configuration by `a` carries the cluster
of `x + a` onto the translate of the cluster of `x` and the connection event accordingly, and the
cutoff law is translation invariant (`SourceModelData.cutLaw_map_shiftConfig`). -/
theorem starMoment_shift (r : ℝ) (p : ℕ) (a x y : M.V) :
    I417Gen.starMoment (M.cutProb r) (x + a) (y + a) p
      = I417Gen.starMoment (M.cutProb r) x y p := by
  -- the integrand, written with `clusterVol` instead of `cardFun`
  set F : M.V → M.V → Config M.V → ℝ≥0∞ := fun u v ω =>
    (connSet u v).indicator (fun _ => (1 : ℝ≥0∞)) ω * (clusterVol ω u) ^ p with hF
  have hFmeas : ∀ u v : M.V, Measurable (F u v) := by
    intro u v
    exact (measurable_const.indicator (measurableSet_connSet u v)).mul
      ((measurable_clusterVol u).pow_const p)
  have hstar : ∀ u v : M.V, I417Gen.starMoment (M.cutProb r) u v p
      = ∫⁻ ω, F u v ω ∂(M.cutLaw r) := by
    intro u v
    rw [I417Gen.starMoment, M.cutLaw_eq_edgeMeasure]
    refine lintegral_congr fun ω => ?_
    simp only [hF]
    rw [Percolation.cardFun_eq_encard]
  have hpt : ∀ ω : Config M.V, F (x + a) (y + a) (shiftConfig a ω) = F x y ω := by
    intro ω
    have hconn : (shiftConfig a ω ∈ connSet (x + a) (y + a)) ↔ (ω ∈ connSet x y) :=
      connects_shiftConfig_iff a ω x y
    have hvol : clusterVol (shiftConfig a ω) (x + a) = clusterVol ω x :=
      M.clusterVol_shiftConfig a ω x
    simp only [hF, Set.indicator_apply, hconn, hvol]
  have hlin : ∫⁻ ω, F (x + a) (y + a) ω ∂((M.cutLaw r).map (shiftConfig a))
      = ∫⁻ ω, F (x + a) (y + a) (shiftConfig a ω) ∂(M.cutLaw r) :=
    lintegral_map (hFmeas (x + a) (y + a)) (measurable_shiftConfig a)
  calc I417Gen.starMoment (M.cutProb r) (x + a) (y + a) p
      = ∫⁻ ω, F (x + a) (y + a) ω ∂(M.cutLaw r) := hstar (x + a) (y + a)
    _ = ∫⁻ ω, F (x + a) (y + a) ω ∂((M.cutLaw r).map (shiftConfig a)) := by
          rw [M.cutLaw_map_shiftConfig r a]
    _ = ∫⁻ ω, F (x + a) (y + a) (shiftConfig a ω) ∂(M.cutLaw r) := hlin
    _ = ∫⁻ ω, F x y ω ∂(M.cutLaw r) := lintegral_congr hpt
    _ = I417Gen.starMoment (M.cutProb r) x y p := (hstar x y).symm

/-- **Root independence of the connected star moment**: the star moment at any root is the one at
the origin for the difference. -/
theorem starMoment_root_indep (r : ℝ) (p : ℕ) (x y : M.V) :
    I417Gen.starMoment (M.cutProb r) x y p
      = I417Gen.starMoment (M.cutProb r) (0 : M.V) (y - x) p := by
  have h := starMoment_shift M r p (-x) x y
  simpa [sub_eq_add_neg] using h.symm

/-- **The per-vertex two-term estimate is root independent.**  Proving it at the origin for every
vertex `y` is exactly the same statement as proving it at every root `x` for every `y`. -/
theorem twoTermTargetAt_iff (r : ℝ) (hχ : M.cutMassAt r 0 ≠ ⊤) (x y : M.V) {C3 C4 : ℝ} :
    TwoTermTargetAt M r x y C3 C4 ↔ TwoTermTarget M r (y - x) C3 C4 := by
  have h3 := polyK_root_indep M r hχ 3 x y
  have h4 := polyK_root_indep M r hχ 4 x y
  rw [TwoTermTargetAt, TwoTermTarget, M.connCubeVertexMass_eq_starMoment,
    starMoment_root_indep M r 3 x y, h3, h4]

/-- **Root independence of the susceptibility**: `E_{β_c,r}|K_x| = χ` for every vertex `x`. -/
theorem chi_root_indep (r : ℝ) (x : M.V) : (M.cutMassAt r x).toReal = chi M r := by
  rw [chi_def, M.cutMassAt_eq_zero r x]

end PercLib.CriticalLRP.M4QZero
