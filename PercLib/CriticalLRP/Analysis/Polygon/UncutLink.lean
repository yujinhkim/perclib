/-
Copyright (c) 2026 PercLib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: PercLib contributors

Proof-only result for Lemma I.4.18. The following constructor eliminates three uncut
analytic hypotheses from a strengthened form of the landed consumer.

The landed handoff `Polygon.Consumer.source_polygon_bound_of_cutoff_data` carries three
unproved analytic inputs about the *uncut* two-point function:

  hB2  : ∀ u, Summable (v ↦ τ(0,v) τ(v,u))
  hB3  : ∀ y, Summable (u ↦ (∑' v, τ(0,v) τ(v,u)) τ(u,y))
  hlink: ∀ y, polyK τ 3 0 y ≤ ∇(0,y)

(`τ = M.twoPoint β_c` real-valued, `∇(0,y) = M.triPoint 0 y`.)

This file removes all three, without assuming them, by keeping the threefold comparison in
`ℝ≥0∞`.  The mechanism is exactly the source's monotone-convergence step
`T_{β_c,r} ≤ τ_{β_c} ⟹ T^3_{β_c,r} ≤ τ^3_{β_c} = ∇_{β_c}(0,·)`:

* `Kpow_mono` : monotonicity of the `ℝ≥0∞` matrix power in the kernel;
* `Kpow_twoPointE_three_eq_openTriangle` : the threefold `ℝ≥0∞` power of `τ` *is* the
  configured open triangle `∇_{β_c}(0,·)` (pure `tsum` algebra, no summability input);
* `cutTriPoint_le_triPoint` : `T^3_{β_c,r}(0,y) ≤ ∇_{β_c}(0,y)` from `χ < ∞` only;
* `source_triSup'` / `source_triTail'` : the `PowerInputs.triSup` field and its tail form
  with no `hB2/hB3/hlink`;
* `source_polygon_bound'`, `source_polygon_bound_of_cutoff_data'` : exact drop-in replacements
  for the landed consumer with those three hypotheses deleted.

Remaining honest inputs of the replacement: the triangle condition `∇ < ∞` (`hTri`), finite
cutoff mass `M.cutMassAt r 0 ≠ ⊤` (`hχfin`, needed to read `Kpow` back in `ℝ`), and the
ball/tail/first-moment data already present in the landed statement.
-/
module

public import PercLib.CriticalLRP.Analysis.Polygon.Consumer
public import PercLib.CriticalLRP.Analysis.TriTail

open MeasureTheory Measure
open scoped ENNReal NNReal BigOperators

@[expose] public section

namespace PercLib.CriticalLRP.KernelPower

variable {V : Type*}

/-- The `ℝ≥0∞` matrix power is monotone in the kernel, for every order.  No summability
hypothesis is needed: `ℝ≥0∞`-valued `tsum` is the supremum over finite partial sums. -/
theorem Kpow_mono {K K' : V → V → ℝ≥0∞} (h : ∀ a b, K a b ≤ K' a b) (n : ℕ) (x y : V) :
    Kpow K n x y ≤ Kpow K' n x y := by
  induction n generalizing x y with
  | zero => simp only [Kpow_zero]; exact le_rfl
  | succ n ih =>
    rw [Kpow_succ, Kpow_succ]
    exact ENNReal.tsum_le_tsum fun u => by
      have h1 : Kpow K n x u ≤ Kpow K' n x u := ih x u
      exact mul_le_mul h1 (h u y) bot_le bot_le

end PercLib.CriticalLRP.KernelPower

namespace PercLib.CriticalLRP.Orchestration.SourceModelData

open PercLib.CriticalLRP Orchestration
open PercLib.CriticalLRP.I418C
open PercLib.CriticalLRP.KernelPower
open PercLib.CriticalLRP.TriTail

variable (M : SourceModelData)

/-! ### The threefold `ℝ≥0∞` power of `τ` is the open triangle -/

theorem Kpow_twoPointE_two (β : ℝ≥0) (x y : M.V) :
    Kpow (M.twoPointE β) 2 x y = ∑' v, M.twoPointE β x v * M.twoPointE β v y := by
  rw [show (2 : ℕ) = 1 + 1 from rfl, Kpow_succ]
  simp only [Kpow_one]

theorem Kpow_twoPointE_three (β : ℝ≥0) (x y : M.V) :
    Kpow (M.twoPointE β) 3 x y
      = ∑' u, ∑' v, M.twoPointE β x u * M.twoPointE β u v * M.twoPointE β v y := by
  rw [show (3 : ℕ) = 2 + 1 from rfl, Kpow_succ]
  simp only [M.Kpow_twoPointE_two]
  rw [show (∑' u, (∑' v, M.twoPointE β x v * M.twoPointE β v u) * M.twoPointE β u y)
      = ∑' u, ∑' v, (M.twoPointE β x v * M.twoPointE β v u) * M.twoPointE β u y from
    tsum_congr fun u => ENNReal.tsum_mul_right.symm]
  rw [ENNReal.tsum_comm]

/-- The threefold `ℝ≥0∞` power of the model two-point function is the configured open
triangle `∇_{β}(0,y)` of `TriTail`. -/
theorem Kpow_twoPointE_three_eq_openTriangle (β : ℝ≥0) (y : M.V) :
    Kpow (M.twoPointE β) 3 0 y = openTriangle M.kernel M.kernel_nonneg β 0 y := by
  rw [M.Kpow_twoPointE_three]
  rfl

/-! ### The cutoff triple versus the uncut triangle -/

theorem twoPointE_ne_top (β : ℝ≥0) (x y : M.V) : M.twoPointE β x y ≠ ⊤ :=
  ne_top_of_le_ne_top ENNReal.one_ne_top
    (twoPointFunction_le_one M.kernel M.kernel_nonneg β x y)

/-- **Monotone domination of the cutoff threefold power by the open triangle.**
No summability or conjugation hypothesis: the comparison is carried out in `ℝ≥0∞` and the
only real-valued input is finiteness of the cutoff first moment, needed to read `Kpow` of the
cutoff kernel back as the real `polyK`. -/
theorem cutTriPoint_le_triPoint (r : ℝ) (hχ : M.cutMassAt r 0 ≠ ⊤)
    (hTri : openTriangleSelf M.kernel M.kernel_nonneg M.betaCrit 0 < ⊤) (y : M.V) :
    M.cutTriPoint r y ≤ M.triPoint 0 y := by
  have hmono : Kpow (M.cutTwoPointE r) 3 0 y ≤ Kpow (M.twoPointE M.betaCrit) 3 0 y :=
    Kpow_mono (fun a b => M.cutTwoPointE_le_twoPointE r a b) 3 0 y
  have hne : Kpow (M.twoPointE M.betaCrit) 3 0 y ≠ ⊤ := by
    rw [M.Kpow_twoPointE_three_eq_openTriangle]
    exact ne_top_of_le_ne_top hTri.ne
      (openTriangle_le_diagonal M.kernel_shift M.kernel_nonneg M.betaCrit y)
  calc M.cutTriPoint r y
      = (Kpow (M.cutTwoPointE r) 3 0 y).toReal :=
        (M.cutKpow_toReal_eq_polyK r hχ 3 0 y).symm
    _ ≤ (Kpow (M.twoPointE M.betaCrit) 3 0 y).toReal := ENNReal.toReal_mono hne hmono
    _ = M.triPoint 0 y := by rw [M.Kpow_twoPointE_three_eq_openTriangle]; rfl


/-! ### The landed `hB2`, `hB3`, `hlink` are derivable, not extra inputs

The three uncut hypotheses of the landed consumer are all consequences of `∇ < ∞`
together with positive definiteness and translation invariance of `τ_{β_c}`
(`twoPoint_Kpow_le_diag`) and the identity `τ(x,x) = 1`.  So the landed interface was
consistent; this section closes the question raised in the work list. -/

theorem twoPoint_eq_toReal (β : ℝ≥0) (x y : M.V) :
    M.twoPoint β x y = (M.twoPointE β x y).toReal := rfl

theorem twoPointE_self (β : ℝ≥0) (x : M.V) : M.twoPointE β x x = 1 :=
  twoPointFunction_self M.kernel M.kernel_nonneg β x

theorem twoPointE_comm (β : ℝ≥0) (x y : M.V) :
    M.twoPointE β x y = M.twoPointE β y x :=
  twoPointFunction_comm M.kernel M.kernel_nonneg β x y

/-- `∑_v τ(0,v)² ≤ ∇`, the `n = 2` case of the diagonal bound.  The `u = v` term of the
twofold convolution is `τ(0,v) τ(v,v) = τ(0,v)`. -/
theorem Kpow_two_le_three_self (β : ℝ≥0) :
    Kpow (M.twoPointE β) 2 0 0 ≤ Kpow (M.twoPointE β) 3 0 0 := by
  calc Kpow (M.twoPointE β) 2 0 0
      = ∑' v, M.twoPointE β 0 v * M.twoPointE β v 0 := M.Kpow_twoPointE_two β 0 0
    _ ≤ ∑' v, Kpow (M.twoPointE β) 2 0 v * M.twoPointE β v 0 := by
        refine ENNReal.tsum_le_tsum fun v => ?_
        have h1 : M.twoPointE β 0 v ≤ Kpow (M.twoPointE β) 2 0 v := by
          calc M.twoPointE β 0 v
              = M.twoPointE β 0 v * M.twoPointE β v v := by rw [M.twoPointE_self, mul_one]
            _ ≤ ∑' u, M.twoPointE β 0 u * M.twoPointE β u v :=
                ENNReal.le_tsum (f := fun u => M.twoPointE β 0 u * M.twoPointE β u v) v
            _ = Kpow (M.twoPointE β) 2 0 v := (M.Kpow_twoPointE_two β 0 v).symm
        exact mul_le_mul h1 le_rfl bot_le bot_le
    _ = Kpow (M.twoPointE β) 3 0 0 := by
        rw [show (3 : ℕ) = 2 + 1 from rfl, Kpow_succ]

/-- Finiteness of the twofold convolution of `τ` at every point, from `∇ < ∞`. -/
theorem Kpow_two_ne_top (β : ℝ≥0)
    (hTri : openTriangleSelf M.kernel M.kernel_nonneg β 0 < ⊤) (u : M.V) :
    Kpow (M.twoPointE β) 2 0 u ≠ ⊤ := by
  have h1 : Kpow (M.twoPointE β) 2 0 u ≤ Kpow (M.twoPointE β) 2 0 0 :=
    PercLib.CriticalLRP.KernelPower.SourceModelData.twoPoint_Kpow_le_diag M β 2 0 u
  have h2 : Kpow (M.twoPointE β) 2 0 0 ≤ Kpow (M.twoPointE β) 3 0 0 :=
    M.Kpow_two_le_three_self β
  have h3 : Kpow (M.twoPointE β) 3 0 0 = openTriangleSelf M.kernel M.kernel_nonneg β 0 := by
    rw [M.Kpow_twoPointE_three_eq_openTriangle]
    rfl
  exact ne_top_of_le_ne_top (by rw [h3]; exact hTri.ne) (h1.trans h2)

/-- The landed `hB2`: the twofold convolution of `τ` is summable in `ℝ` at every point. -/
theorem summable_twoPoint_mul (β : ℝ≥0)
    (hTri : openTriangleSelf M.kernel M.kernel_nonneg β 0 < ⊤) (u : M.V) :
    Summable (fun v => M.twoPoint β 0 v * M.twoPoint β v u) := by
  have hne : (∑' v, M.twoPointE β 0 v * M.twoPointE β v u) ≠ ⊤ := by
    rw [← M.Kpow_twoPointE_two β 0 u]
    exact M.Kpow_two_ne_top β hTri u
  have h := ENNReal.summable_toReal hne
  simpa only [SourceModelData.twoPoint, SourceModelData.twoPointE, Measure.real_def,
    ENNReal.toReal_mul] using h

/-- The landed `hB3`: the twofold convolution of `τ` is summable against the last row. -/
theorem summable_twoPoint_conv_mul (β : ℝ≥0)
    (hTri : openTriangleSelf M.kernel M.kernel_nonneg β 0 < ⊤) (y : M.V) :
    Summable (fun u => (∑' v, M.twoPoint β 0 v * M.twoPoint β v u)
      * M.twoPoint β u y) := by
  have hne : (∑' u, Kpow (M.twoPointE β) 2 0 u * M.twoPointE β u y) ≠ ⊤ := by
    rw [show (∑' u, Kpow (M.twoPointE β) 2 0 u * M.twoPointE β u y)
        = Kpow (M.twoPointE β) 3 0 y from by
      rw [show (3 : ℕ) = 2 + 1 from rfl, Kpow_succ]]
    rw [M.Kpow_twoPointE_three_eq_openTriangle]
    exact ne_top_of_le_ne_top hTri.ne
      (openTriangle_le_diagonal M.kernel_shift M.kernel_nonneg β y)
  have h := ENNReal.summable_toReal hne
  have hcongr : ∀ u,
      (Kpow (M.twoPointE β) 2 0 u * M.twoPointE β u y).toReal
        = (∑' v, M.twoPoint β 0 v * M.twoPoint β v u) * M.twoPoint β u y := by
    intro u
    rw [ENNReal.toReal_mul, M.Kpow_twoPointE_two β 0 u,
      ENNReal.tsum_toReal_eq (fun v =>
        ENNReal.mul_ne_top (M.twoPointE_ne_top β 0 v) (M.twoPointE_ne_top β v u))]
    simp only [SourceModelData.twoPoint, SourceModelData.twoPointE, Measure.real_def,
      ENNReal.toReal_mul]
  simpa only [hcongr] using h

/-- `polyK` in `ℝ` is the `toReal` of `Kpow` in `ℝ≥0∞`, `n = 2`. -/
theorem polyK_twoPoint_eq_toReal_two (β : ℝ≥0) (x y : M.V) :
    polyK (M.twoPoint β) 2 x y = (Kpow (M.twoPointE β) 2 x y).toReal := by
  rw [M.Kpow_twoPointE_two β x y, polyK_two,
    ENNReal.tsum_toReal_eq (fun v =>
      ENNReal.mul_ne_top (M.twoPointE_ne_top β x v) (M.twoPointE_ne_top β v y))]
  simp only [SourceModelData.twoPoint, SourceModelData.twoPointE, Measure.real_def,
    ENNReal.toReal_mul]

/-- The real threefold convolution of `τ` is below the open triangle. -/
theorem hlink_derived (β : ℝ≥0)
    (hTri : openTriangleSelf M.kernel M.kernel_nonneg β 0 < ⊤) (y : M.V) :
    polyK (M.twoPoint β) 3 0 y ≤
      (openTriangle M.kernel M.kernel_nonneg β 0 y).toReal := by
  have h2 : ∀ u, polyK (M.twoPoint β) 2 0 u * M.twoPoint β u y
      = (Kpow (M.twoPointE β) 2 0 u * M.twoPointE β u y).toReal := by
    intro u
    rw [M.polyK_twoPoint_eq_toReal_two β 0 u]
    simp only [SourceModelData.twoPoint, SourceModelData.twoPointE, Measure.real_def]
    exact (ENNReal.toReal_mul ..).symm
  calc polyK (M.twoPoint β) 3 0 y
      = ∑' u, (Kpow (M.twoPointE β) 2 0 u * M.twoPointE β u y).toReal := by
        rw [show (3 : ℕ) = 2 + 1 from rfl, polyK_succ]
        exact tsum_congr h2
    _ = (∑' u, Kpow (M.twoPointE β) 2 0 u * M.twoPointE β u y).toReal :=
        (ENNReal.tsum_toReal_eq (fun u =>
          ENNReal.mul_ne_top (M.Kpow_two_ne_top β hTri u)
            (M.twoPointE_ne_top β u y))).symm
    _ = (Kpow (M.twoPointE β) 3 0 y).toReal := by
        rw [show (3 : ℕ) = 2 + 1 from rfl, Kpow_succ]
    _ ≤ (openTriangle M.kernel M.kernel_nonneg β 0 y).toReal := by
        rw [M.Kpow_twoPointE_three_eq_openTriangle]

/-- **The landed `hlink`**, exactly as `Polygon.Consumer` states it. -/
theorem hlink_betaCrit (hTri : openTriangleSelf M.kernel M.kernel_nonneg M.betaCrit 0 < ⊤)
    (y : M.V) : polyK (M.twoPoint M.betaCrit) 3 0 y ≤ M.triPoint 0 y :=
  M.hlink_derived M.betaCrit hTri y

/-- The landed triple `hB2/hB3/hlink`, derived, in exactly the shapes of
`Polygon.Consumer.source_polygon_bound_of_cutoff_data`. -/
theorem hB2_hB3_hlink_derived
    (hTri : openTriangleSelf M.kernel M.kernel_nonneg M.betaCrit 0 < ⊤) :
    (∀ u : M.V, Summable (fun v => M.twoPoint M.betaCrit 0 v * M.twoPoint M.betaCrit v u)) ∧
      (∀ y : M.V, Summable (fun u => (∑' v, M.twoPoint M.betaCrit 0 v
        * M.twoPoint M.betaCrit v u) * M.twoPoint M.betaCrit u y)) ∧
      (∀ y : M.V, polyK (M.twoPoint M.betaCrit) 3 0 y ≤ M.triPoint 0 y) :=
  ⟨M.summable_twoPoint_mul M.betaCrit hTri, M.summable_twoPoint_conv_mul M.betaCrit hTri,
    M.hlink_betaCrit hTri⟩

/-- **`triSup` of `PowerInputs`, with `hB2/hB3/hlink` removed.** -/
theorem source_triSup' (r : ℝ) (hχ : M.cutMassAt r 0 ≠ ⊤)
    (hTri : openTriangleSelf M.kernel M.kernel_nonneg M.betaCrit 0 < ⊤) (y : M.V) :
    M.cutTriPoint r y ≤ M.triSelf :=
  (M.cutTriPoint_le_triPoint r hχ hTri y).trans (M.triPoint_le_self hTri y)

/-- The same comparison on the source's tail `∇_{r^c}`. -/
theorem source_triTail' (r cc trc : ℝ) (hχ : M.cutMassAt r 0 ≠ ⊤)
    (hTri : openTriangleSelf M.kernel M.kernel_nonneg M.betaCrit 0 < ⊤)
    (htailc : ∀ y : M.V, r ^ cc ≤ M.S.dist 0 y → M.triPoint 0 y ≤ trc) (y : M.V)
    (hy : r ^ cc ≤ M.S.dist 0 y) : M.cutTriPoint r y ≤ trc :=
  (M.cutTriPoint_le_triPoint r hχ hTri y).trans (htailc y hy)

/-- **The honest `ℓ = 3` case**, with diagonal maximality: `sup_x T^3(0,x) = T^3(0,0) ≤ ∇_{β_c}`.
The printed `C(∇_{r^c} + r^{-c})(E|K|)^0` cannot hold at `ℓ = 3` (see
`I418C.one_le_polyK_three`); this is the bound the applications use. -/
theorem source_ell_three_le (r : ℝ) (hχ : M.cutMassAt r 0 ≠ ⊤)
    (hTri : openTriangleSelf M.kernel M.kernel_nonneg M.betaCrit 0 < ⊤) (x : M.V) :
    polyK (M.cutTwoPoint r) 3 0 x ≤ M.triSelf :=
  (M.source_polyK_le_diag r hχ 3 x).trans (M.source_triSup' r hχ hTri 0)


/-! ### `PowerInputs` with the triSup field supplied -/

theorem source_powerInputs_of_triSup (r : ℝ) (hχ : M.cutMassAt r 0 ≠ ⊤)
    (htriSup : ∀ y : M.V, polyK (M.cutTwoPoint r) 3 0 y ≤ M.triSelf) :
    PowerInputs (polyK (M.cutTwoPoint r)) M.triSelf (M.cutMassAt r 0).toReal := by
  refine ⟨?_, ?_, M.cutPolyK_comp_toReal r hχ, ?_, ?_, ?_, ?_, ?_, htriSup⟩
  · exact fun n x y => polyK_nonneg _ (fun a b => M.cutTwoPoint_nonneg r a b) n x y
  · exact fun x y => polyK_zero (M.cutTwoPoint r) x y
  · intro n
    have hsum : (∑' y : M.V, Kpow (M.cutTwoPointE r) 3 0 y *
        Kpow (M.cutTwoPointE r) n y 0) ≠ ⊤ := by
      rw [← M.cutKpow_comp r n]
      exact M.cutKpow_ne_top_of_chi_ne_top r hχ (n + 3) 0 0
    have hreal := ENNReal.summable_toReal hsum
    simpa only [ENNReal.toReal_mul, M.cutKpow_toReal_eq_polyK r hχ] using hreal
  · intro n
    simpa only [M.cutKpow_toReal_eq_polyK r hχ] using M.cutKpow_colSum_toReal r hχ n 0
  · intro n
    have hsum : (∑' x : M.V, Kpow (M.cutTwoPointE r) n x 0) ≠ ⊤ := by
      rw [M.cutKpow_colSum r n 0]
      exact ENNReal.pow_ne_top hχ
    have hreal := ENNReal.summable_toReal hsum
    simpa only [M.cutKpow_toReal_eq_polyK r hχ] using hreal
  · intro n hn y
    obtain ⟨m, rfl⟩ := Nat.exists_eq_succ_of_ne_zero (Nat.ne_of_gt hn)
    have h := M.cutKpow_entry r m y 0
    have hreal := ENNReal.toReal_mono (ENNReal.pow_ne_top hχ) h
    simpa only [M.cutKpow_toReal_eq_polyK r hχ, ENNReal.toReal_pow,
      Nat.succ_sub_one, Nat.add_sub_cancel] using hreal
  · rw [polyK_one]
    exact M.cutTwoPoint_self_eq_one r 0

/-- `PowerInputs` for the cutoff powers, from `χ < ∞` and `∇ < ∞` alone. -/
theorem source_powerInputs' (r : ℝ) (hχ : M.cutMassAt r 0 ≠ ⊤)
    (hTri : openTriangleSelf M.kernel M.kernel_nonneg M.betaCrit 0 < ⊤) :
    PowerInputs (polyK (M.cutTwoPoint r)) M.triSelf (M.cutMassAt r 0).toReal :=
  M.source_powerInputs_of_triSup r hχ (fun y => M.source_triSup' r hχ hTri y)

end PercLib.CriticalLRP.Orchestration.SourceModelData

namespace PercLib.CriticalLRP.I418C

open PercLib.CriticalLRP Orchestration
open PercLib.CriticalLRP.TriTail

/-- **The model-level Lemma I.4.18 assembly without `hB2/hB3/hlink`.**  Same conclusion and
same ball/tail/first-moment data as `SourceModelData.source_polygon_bound`, but the uncut
threefold input is derived. -/
theorem source_polygon_bound' (M : SourceModelData)
    (r R trc χ : ℝ) (s : Finset M.V) {c₀ K cc : ℝ}
    (hr : 1 ≤ r) (hc₀ : 0 < c₀) (hK : 0 ≤ K)
    (hχfin : M.cutMassAt r 0 ≠ ⊤)
    (hTri : openTriangleSelf M.kernel M.kernel_nonneg M.betaCrit 0 < ⊤)
    (H : PowerInputs (polyK (M.cutTwoPoint r)) M.triSelf χ)
    {ell : ℕ} (hell : 4 ≤ ell)
    (hct : cc = M.α / (4 * (M.d : ℝ)))
    (hfar : ∀ y : M.V, y ∉ s → R ≤ M.S.dist 0 y)
    (htailc : ∀ y : M.V, r ^ cc ≤ M.S.dist 0 y → M.triPoint 0 y ≤ trc)
    (htrc : 0 ≤ trc)
    (hcard : (s.card : ℝ) ≤ K * R ^ (M.d : ℝ))
    (hR : R = r ^ (M.α / (2 * (M.d : ℝ))))
    (hχ : c₀ * r ^ M.α ≤ χ)
    (hdiag : ∀ x : M.V, polyK (M.cutTwoPoint r) ell 0 x ≤ polyK (M.cutTwoPoint r) ell 0 0) :
    ∀ x : M.V, polyK (M.cutTwoPoint r) ell 0 x
      ≤ max 1 (M.triSelf * K / c₀) * (trc + r ^ (-cc)) * χ ^ (ell - 3) := by
  have htail : ∀ y : M.V, r ^ cc ≤ M.S.dist 0 y → polyK (M.cutTwoPoint r) 3 0 y ≤ trc :=
    fun y hy => M.source_triTail' r cc trc hχfin hTri htailc y hy
  exact polygon_bound_sup H s (fun y => M.S.dist 0 y) r R trc M.hα M.hd hc₀ hK hr hell
    hct hfar htail htrc hcard hR hχ hdiag

/-- Drop-in replacement for `source_polygon_bound_of_cutoff_data` with `hB2`, `hB3` and
`hlink` deleted. -/
theorem source_polygon_bound_of_cutoff_data' (M : SourceModelData)
    (r R trc : ℝ) (s : Finset M.V) {c₀ K cc : ℝ}
    (hr : 1 ≤ r) (hc₀ : 0 < c₀) (hK : 0 ≤ K)
    (hχfin : M.cutMassAt r 0 ≠ ⊤)
    (hTri : openTriangleSelf M.kernel M.kernel_nonneg M.betaCrit 0 < ⊤)
    {ell : ℕ} (hell : 4 ≤ ell)
    (hct : cc = M.α / (4 * (M.d : ℝ)))
    (hfar : ∀ y : M.V, y ∉ s → R ≤ M.S.dist 0 y)
    (htailc : ∀ y : M.V, r ^ cc ≤ M.S.dist 0 y → M.triPoint 0 y ≤ trc)
    (htrc : 0 ≤ trc)
    (hcard : (s.card : ℝ) ≤ K * R ^ (M.d : ℝ))
    (hR : R = r ^ (M.α / (2 * (M.d : ℝ))))
    (hχ : c₀ * r ^ M.α ≤ (M.cutMassAt r 0).toReal) :
    ∀ x : M.V, polyK (M.cutTwoPoint r) ell 0 x
      ≤ max 1 (M.triSelf * K / c₀) * (trc + r ^ (-cc)) *
        ((M.cutMassAt r 0).toReal) ^ (ell - 3) :=
  source_polygon_bound' M r R trc (M.cutMassAt r 0).toReal s hr hc₀ hK hχfin hTri
    (M.source_powerInputs' r hχfin hTri) hell hct hfar htailc htrc hcard hR hχ
    (fun x => M.source_polyK_le_diag r hχfin ell x)

end PercLib.CriticalLRP.I418C
