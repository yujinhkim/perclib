/-
Independent Ultramath work for Case 3 of Proposition I.4.20 (the `(∇)`-triangle case).

Direction (B): the *polygon interface*.  This file records the genuine range-truncated
matrix powers `T^j_{β_c,r}(0,y)` of the source (Lemma I.4.18) in the `ℝ≥0∞` shape that
`PercLib.CriticalLRP.I420Case3.HasPolygonBound` expects, together with the two bridges
that are needed to speak about them in the Case 3 interface:

* `cutPoly M r y j = ofReal (polyK (M.cutTwoPoint r) j 0 y)` is `Kpow (M.cutTwoPointE r) j 0 y`,
  i.e. the extended-real matrix power of the cutoff two-point kernel
  (`cutPoly_eq_Kpow`, conditional on the finite-cutoff susceptibility `hfin`, which is
  *derived* in `Main.lean` from the first-moment asymptotic rather than assumed);
* the first cluster moment of the canonical law of the cutoff profile `M.cutProb r` is
  the source's `χ = E_{β_c,r}|K| = M.cutMassAt r 0` (`powMomentAt_cutProb_one`).

Source: Tom Hutchcroft, *Critical long-range percolation I: High effective dimension*,
arXiv:2508.18807v1; Lemma I.4.18 is the polygon estimate
`sup_x T^ℓ_{β_c,r}(0,x) = T^ℓ_{β_c,r}(0,0) ≤ C (∇_{r^c} + r^{-c}) (E_{β_c,r}|K|)^{ℓ-3}`.
No new axioms, no `sorry`.
-/
module

public import PercLib.CriticalLRP.Analysis.Polygon.Assembly
public import PercLib.CriticalLRP.Analysis.Polygon.TailConstant
public import PercLib.CriticalLRP.VolumeMoments.HigherMoments.I420Case3.Defs

/-! # Genuine cutoff polygon powers and their threefold lower bound -/

@[expose] public section

noncomputable section

open MeasureTheory Measure ProbabilityTheory unitInterval
open scoped ENNReal

set_option linter.unusedSectionVars false

namespace PercLib.CriticalLRP

namespace I420Case3

open PercLib.CriticalLRP Orchestration
open PercLib.CriticalLRP.KernelPower

/-- **The polygon powers of Lemma I.4.18 as genuine cutoff matrix entries.**

`cutPoly M r y j = T^j_{β_c,r}(0,y)`, the `j`-fold matrix power of the range-truncated
two-point function `M.cutTwoPoint r`, in the `ℝ≥0∞` form used by `HasPolygonBound`.

This is the `poly` argument of the Case 3 interface, with `o = 0`, `π = M.cutProb r` and
the source's `χ = E_{β_c,r}|K| = M.cutMassAt r 0`; see `Main.lean`. -/
noncomputable def cutPoly (M : SourceModelData) (r : ℝ) : M.V → ℕ → ℝ≥0∞ :=
  fun y j => ENNReal.ofReal (I418C.polyK (M.cutTwoPoint r) j 0 y)

/-- **The first cluster moment of the cutoff profile is the source's `χ`.**

`I420Case1.powMomentAt (M.cutProb r) 1 0 = M.cutMassAt r 0`: `M.cutLaw r` *is* the
canonical independent-edge law of the profile `M.cutProb r` (`SourceModelData.cutLaw`,
`SourceModelData.cutProb`, `PercLib.CriticalLRP.CountableProduct.Marks.longRangeMeasure`),
so the two integrals agree up to `clusterVol ^ 1 = clusterVol`. -/
theorem powMomentAt_cutProb_one (M : SourceModelData) (r : ℝ) :
    I420Case1.powMomentAt (M.cutProb r) 1 (0 : M.V) = M.cutMassAt r 0 := by
  have h : M.cutMassAt r 0
      = ∫⁻ ω, clusterVol ω (0 : M.V) ∂(edgeMeasure (M.cutProb r)) := rfl
  simp only [I420Case1.powMomentAt, pow_one, h]

/-- `cutPoly` is the extended-real cutoff matrix power `Kpow (cutTwoPointE r) j 0 y`.

The only input is the finite-cutoff susceptibility `M.cutMassAt r 0 ≠ ⊤`, which makes
every entry of every cutoff power finite (`cutKpow_ne_top_of_chi_ne_top`) and therefore
identifies `ofReal` of the real matrix power with the `ℝ≥0∞` one. -/
theorem cutPoly_eq_Kpow (M : SourceModelData) (r : ℝ) (hχ : M.cutMassAt r 0 ≠ ⊤)
    (y : M.V) (j : ℕ) :
    cutPoly M r y j = Kpow (M.cutTwoPointE r) j 0 y := by
  rw [cutPoly, ← M.cutKpow_toReal_eq_polyK r hχ j 0 y,
    ENNReal.ofReal_toReal (M.cutKpow_ne_top_of_chi_ne_top r hχ j 0 y)]

/-- Sanity check: at `j = 1` `cutPoly` is the cutoff two-point function itself. -/
theorem cutPoly_one (M : SourceModelData) (r : ℝ) (y : M.V) :
    cutPoly M r y 1 = ENNReal.ofReal (M.cutTwoPoint r 0 y) := by
  simp only [cutPoly, I418C.polyK_one]

/-- Sanity check: at `j = 0` `cutPoly` is the identity kernel `δ_{0,y}`. -/
theorem cutPoly_zero (M : SourceModelData) (r : ℝ) (y : M.V) :
    cutPoly M r y 0 = if y = 0 then 1 else 0 := by
  rw [cutPoly, I418C.polyK_zero]
  by_cases h : y = 0
  · subst h
    simp
  · have h' : ¬ (0 : M.V) = y := fun hh => h hh.symm
    simp [h, h']

/-- `cutPoly` is a non-negative real matrix power (it is an `ofReal`). -/
theorem cutPoly_nonneg (M : SourceModelData) (r : ℝ) (y : M.V) (j : ℕ) :
    0 ≤ I418C.polyK (M.cutTwoPoint r) j 0 y := by
  by_cases h : j = 0
  · subst h
    rw [I418C.polyK_zero]
    split_ifs <;> norm_num
  · obtain ⟨n, rfl⟩ := Nat.exists_eq_succ_of_ne_zero h
    exact I418C.polyK_nonneg _ (fun a b => M.cutTwoPoint_nonneg r a b) _ _ _

/-- **The cutoff threefold power is at least one at the origin.**

`T^3_{β_c,r}(0,0) ≥ T(0,0)^3 = 1`, so the diagonal entry of the `j = 3` polygon power is
never small.  This is the exact obstruction recorded in `Main.lean`: a `HasPolygonBound`
whose ball contains `0` cannot have a factor below `1`.  (The lower bound is proved for
the `ℝ≥0∞` power `Kpow`, which needs no summability, and then transported to `ℝ` by
`cutKpow_toReal_eq_polyK`; the real iterated sum is *not* automatically bounded below by a
single one of its terms when it is non-summable, which is exactly why `hχ` is needed.) -/
theorem one_le_polyK_three_of_chi_ne_top (M : SourceModelData) (r : ℝ)
    (hχ : M.cutMassAt r 0 ≠ ⊤) :
    1 ≤ I418C.polyK (M.cutTwoPoint r) 3 (0 : M.V) 0 := by
  have hK : M.cutTwoPointE r 0 0 = 1 := by
    rw [M.cutTwoPointE_eq_ofReal, M.cutTwoPoint_self_eq_one, ENNReal.ofReal_one]
  have hstep : ∀ n : ℕ, Kpow (M.cutTwoPointE r) n 0 0
      ≤ Kpow (M.cutTwoPointE r) (n + 1) 0 0 := by
    intro n
    rw [Kpow_succ]
    have h := ENNReal.le_tsum
      (f := fun z : M.V => Kpow (M.cutTwoPointE r) n 0 z * M.cutTwoPointE r z 0) 0
    rwa [hK, mul_one] at h
  have h0 : Kpow (M.cutTwoPointE r) 0 0 0 = 1 := by
    rw [Kpow_zero, deltaE]
    simp
  have h1 : (1 : ℝ≥0∞) ≤ Kpow (M.cutTwoPointE r) 3 0 0 := by
    calc (1 : ℝ≥0∞) = Kpow (M.cutTwoPointE r) 0 0 0 := h0.symm
      _ ≤ Kpow (M.cutTwoPointE r) 3 0 0 :=
        le_trans (hstep 0) (le_trans (hstep 1) (hstep 2))
  have h2 := ENNReal.toReal_mono (M.cutKpow_ne_top_of_chi_ne_top r hχ 3 0 0) h1
  rw [M.cutKpow_toReal_eq_polyK r hχ 3 0 0] at h2
  simpa using h2

end I420Case3

end PercLib.CriticalLRP
