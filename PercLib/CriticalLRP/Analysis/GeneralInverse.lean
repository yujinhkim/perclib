/-
Migration source: https://github.com/yujinhkim/Critical-Long-range-percolation
Integration revision: 3b3d1d0e43ef940bfaa2292ee5c2ee094ac4edbf
Licence: Apache-2.0 for the PercLib Lean sources and tooling; see third_party/critical-lrp/.
External provenance and modifications are recorded in the file-specific notices below.
-/

/-
# Generalized inverse of a measurable regularly varying function, I

The source (T. Hutchcroft, *Critical long-range percolation I*, Prop. I.3.2)
assumes only that `f` is a **measurable** regularly varying function of positive
index -- no monotonicity, no continuity.  This file constructs a generalized
inverse that works for such an `f`, and proves the composition and regular
variation laws it satisfies.

Main contents:

* `eventually_pos_of_tendsto_div` -- eventual positivity of `f` follows from
  `ψ r / (A₂ * f r) → 1`, `ψ ≥ 0`, `A₂ > 0` (so the paper's hypotheses give
  positivity; it is not an extra assumption).
* `RVPosData` -- the bundle "`f` is measurable, regularly varying of index
  `ρ > 0`, and above a threshold `x₀ ≥ 1` it is positive and satisfies Potter's
  bounds" (BGT 1.5.6), built from the paper's hypotheses by `RVPosData.of` and
  from the moment asymptotics by `RVPosData.of_moment`.
* `RVPosData.tendsto_atTop_self` -- `f → ∞` (no monotonicity used).
* `genInv` / `RVPosData.genInv` -- the level-set inverse `inf {x ≥ x₀ | y ≤ f x}`,
  with `x₀ ≤ genInv y` and `genInv y ≤ x` whenever `f x ≥ y`, `x ≥ x₀`; every
  level set is nonempty and `genInv` is nondecreasing.
* `RVPosData.tendsto_genInv_atTop` -- the inverse diverges.
* `RVPosData.uniform_ratio` -- the uniform convergence theorem (BGT 1.2.1) for
  `f`, in the two-sided form used below.
* `RVPosData.tendsto_comp_genInv` -- the asymptotic composition law
  `f (genInv y) / y → 1` (no exact inverse is asserted or fabricated).
-/
module

public import PercLib.CriticalLRP.Analysis.UniformConvergence

set_option linter.unusedSectionVars false
set_option linter.unusedSimpArgs false
set_option linter.unnecessarySimpa false
set_option linter.unusedTactic false
set_option linter.unusedVariables false

set_option autoImplicit true

@[expose] public section

open Filter Set MeasureTheory
open scoped Topology

namespace PercLib.CriticalLRP.Analysis

/-! ## Eventual positivity from the moment comparison -/

/-- **Eventual positivity of `f` from the moment asymptotics.**  If `ψ ≥ 0`,
`A₂ > 0` and `ψ r / (A₂ * f r) → 1`, then `f` is eventually positive.
Hypothesis 2 of Proposition I.3.2 reads `Ê_r |K| ∼ A₂ f r` with `Ê_r|K| ≥ 0`, so
it provides this positivity; it never has to be assumed separately. -/
theorem eventually_pos_of_tendsto_div {ψ f : ℝ → ℝ} {A₂ : ℝ} (hA₂ : 0 < A₂)
    (hψ : ∀ᶠ r in atTop, 0 ≤ ψ r)
    (h : Tendsto (fun r => ψ r / (A₂ * f r)) atTop (𝓝 1)) : ∀ᶠ r in atTop, 0 < f r := by
  have h1 : ∀ᶠ r in atTop, 0 < ψ r / (A₂ * f r) :=
    h.eventually (eventually_gt_nhds zero_lt_one)
  filter_upwards [h1, hψ] with r hr hψr
  rcases div_pos_iff.1 hr with ⟨-, h2⟩ | ⟨h1', -⟩
  · by_contra hcon
    push Not at hcon
    exact absurd h2 (not_lt.mpr (mul_nonpos_of_nonneg_of_nonpos hA₂.le hcon))
  · exact absurd h1' (not_lt.mpr hψr)

/-! ## Potter data -/

/-- **Regular variation data of positive index.**  `f` is measurable, regularly
varying at `∞` of index `ρ > 0`, and above the threshold `threshold ≥ 1` it is
positive and satisfies Potter's bounds with that same threshold (for all
`ε ∈ (0, 1/2]`; weaker bounds for larger `ε` follow from these). -/
structure RVPosData (f : ℝ → ℝ) (ρ : ℝ) where
  /-- the index is positive -/
  pos_index : 0 < ρ
  /-- `f` is measurable -/
  measurable_f : Measurable f
  /-- `f` is regularly varying of index `ρ` at `∞` -/
  rv : RegularlyVaryingAtTop f ρ
  /-- a threshold above which the Potter bounds and positivity hold -/
  threshold : ℝ
  /-- the threshold is at least `1` -/
  one_le_threshold : 1 ≤ threshold
  /-- `f` is positive above the threshold -/
  pos_above : ∀ x : ℝ, threshold ≤ x → 0 < f x
  /-- the exponent used in Potter's bounds -/
  eps : ℝ
  /-- the Potter exponent is positive -/
  eps_pos : 0 < eps
  /-- the Potter exponent is below the index -/
  eps_lt : eps < ρ
  /-- the Potter exponent is at most `1/2` -/
  eps_le_half : eps ≤ 1 / 2
  /-- Potter's bounds above the threshold -/
  potter : ∀ x y : ℝ, threshold ≤ y → y ≤ x →
    (1 - eps) * (x / y) ^ (ρ - eps) * |f y| ≤ |f x| ∧
      |f x| ≤ (1 + eps) * (x / y) ^ (ρ + eps) * |f y|

/-- **Existence of the regular variation data** from the paper's hypotheses:
measurability, regular variation of positive index and eventual positivity. -/
theorem RVPosData.nonempty {f : ℝ → ℝ} {ρ : ℝ} (hρ : 0 < ρ) (hmeas : Measurable f)
    (hrv : RegularlyVaryingAtTop f ρ) (hpos : ∀ᶠ x in atTop, 0 < f x) :
    Nonempty (RVPosData f ρ) := by
  obtain ⟨e, he, heρ, heh⟩ : ∃ e : ℝ, 0 < e ∧ e < ρ ∧ e ≤ 1 / 2 :=
    ⟨min (ρ / 2) (1 / 2), lt_min (by linarith) (by norm_num),
      lt_of_le_of_lt (min_le_left _ _) (by linarith), min_le_right _ _⟩
  obtain ⟨Xp, hXp1, hpot⟩ := hasPotterBounds_of_regularlyVarying hmeas hrv e he
  obtain ⟨Xq, hXq⟩ := eventually_atTop.1 hpos
  refine ⟨⟨hρ, hmeas, hrv, max Xp Xq, le_trans hXp1 (le_max_left _ _), ?_, e, he, heρ, heh, ?_⟩⟩
  · intro x hx
    exact hXq x (le_trans (le_max_right _ _) hx)
  · intro x y hy hyx
    exact hpot x y (le_trans (le_max_left _ _) hy) hyx

/-- **Construction of the regular variation data** from the paper's hypotheses:
measurability, regular variation of positive index and eventual positivity. -/
noncomputable def RVPosData.of {f : ℝ → ℝ} {ρ : ℝ} (hρ : 0 < ρ) (hmeas : Measurable f)
    (hrv : RegularlyVaryingAtTop f ρ) (hpos : ∀ᶠ x in atTop, 0 < f x) : RVPosData f ρ :=
  Classical.choice (RVPosData.nonempty hρ hmeas hrv hpos)

/-- **Construction of the regular variation data from the moment asymptotics**
(hypothesis 2 of Proposition I.3.2 and its positivity part). -/
noncomputable def RVPosData.of_moment {f ψ : ℝ → ℝ} {ρ A₂ : ℝ} (hρ : 0 < ρ)
    (hmeas : Measurable f) (hrv : RegularlyVaryingAtTop f ρ) (hA₂ : 0 < A₂)
    (hψ : ∀ᶠ r in atTop, 0 ≤ ψ r)
    (hmom : Tendsto (fun r => ψ r / (A₂ * f r)) atTop (𝓝 1)) : RVPosData f ρ :=
  RVPosData.of hρ hmeas hrv (eventually_pos_of_tendsto_div hA₂ hψ hmom)

/-! ## A regularly varying function of positive index diverges -/

/-- **A measurable regularly varying function of positive index tends to `∞`.**
No monotonicity is used: the lower Potter bound at the threshold gives
`f x ≥ c x ^ (ρ - ε)` with `ρ - ε > 0`, which diverges. -/
theorem RVPosData.tendsto_atTop_self (D : RVPosData f ρ) : Tendsto f atTop atTop := by
  have he := D.eps_pos
  have hlt := D.eps_lt
  have hthr : 0 < D.threshold := lt_of_lt_of_le one_pos D.one_le_threshold
  have hcoef : 0 < (1 - D.eps) * f D.threshold := by
    have h1 : 0 < 1 - D.eps := by linarith [D.eps_le_half]
    exact mul_pos h1 (D.pos_above _ le_rfl)
  have hlow : ∀ᶠ x : ℝ in atTop,
      (1 - D.eps) * f D.threshold * (x / D.threshold) ^ (ρ - D.eps) ≤ f x := by
    filter_upwards [eventually_ge_atTop D.threshold] with x hx
    have hpot := (D.potter x D.threshold le_rfl hx).1
    rw [abs_of_pos (D.pos_above _ le_rfl), abs_of_pos (D.pos_above x hx)] at hpot
    calc (1 - D.eps) * f D.threshold * (x / D.threshold) ^ (ρ - D.eps)
        = (1 - D.eps) * (x / D.threshold) ^ (ρ - D.eps) * f D.threshold := by ring
      _ ≤ f x := hpot
  have hbase : Tendsto (fun x : ℝ => x / D.threshold) atTop atTop :=
    tendsto_id.atTop_div_const hthr
  have hrpow : Tendsto (fun x : ℝ => (x / D.threshold) ^ (ρ - D.eps)) atTop atTop :=
    (tendsto_rpow_atTop (by linarith : 0 < ρ - D.eps)).comp hbase
  have hcmp : Tendsto (fun x : ℝ => (1 - D.eps) * f D.threshold *
      (x / D.threshold) ^ (ρ - D.eps)) atTop atTop :=
    hrpow.const_mul_atTop hcoef
  exact tendsto_atTop_mono' atTop hlow hcmp

/-- **A uniform bound above the threshold.**  On `[x₀, M]` a regularly varying
`f` of positive index is bounded (Potter's upper bound). -/
theorem RVPosData.bddAbove_Icc (D : RVPosData f ρ) (M : ℝ) :
    ∃ C : ℝ, ∀ x : ℝ, D.threshold ≤ x → x ≤ M → f x ≤ C := by
  refine ⟨(1 + D.eps) * (max M D.threshold / D.threshold) ^ (ρ + D.eps) * f D.threshold,
    fun x hx1 hx2 => ?_⟩
  have hthr : 0 < D.threshold := lt_of_lt_of_le one_pos D.one_le_threshold
  have hpot := (D.potter x D.threshold le_rfl hx1).2
  rw [abs_of_pos (D.pos_above x hx1), abs_of_pos (D.pos_above _ le_rfl)] at hpot
  have hxM : x ≤ max M D.threshold := le_trans hx2 (le_max_left _ _)
  have hxpos : 0 < x := lt_of_lt_of_le hthr hx1
  have hmono : (x / D.threshold) ^ (ρ + D.eps) ≤ (max M D.threshold / D.threshold) ^ (ρ + D.eps) :=
    Real.rpow_le_rpow (le_of_lt (div_pos hxpos hthr))
      (by rw [div_le_div_iff_of_pos_right hthr]; exact hxM) (by linarith [D.pos_index, D.eps_pos])
  calc f x ≤ (1 + D.eps) * (x / D.threshold) ^ (ρ + D.eps) * f D.threshold := hpot
    _ ≤ (1 + D.eps) * (max M D.threshold / D.threshold) ^ (ρ + D.eps) * f D.threshold := by
        apply mul_le_mul_of_nonneg_right _ (D.pos_above _ le_rfl).le
        exact mul_le_mul_of_nonneg_left hmono (by linarith [D.eps_pos])

/-- The level set of `f` at level `y` above the threshold `x₀`. -/
def levelSet (f : ℝ → ℝ) (x0 y : ℝ) : Set ℝ := {x : ℝ | x0 ≤ x ∧ y ≤ f x}

/-- **The generalized inverse** of `f` above the threshold `x₀`: the infimum of
the level set `{x ≥ x₀ | y ≤ f x}`.  On the level sets it is exact up to the
infimum: `genInv y ≤ x` whenever `y ≤ f x` and `x₀ ≤ x`. -/
noncomputable def genInv (f : ℝ → ℝ) (x0 : ℝ) (y : ℝ) : ℝ := sInf (levelSet f x0 y)

theorem genInv_def (f : ℝ → ℝ) (x0 y : ℝ) :
    genInv f x0 y = sInf {x : ℝ | x0 ≤ x ∧ y ≤ f x} := rfl

/-- **The generalized inverse of the regular variation data.** -/
noncomputable def RVPosData.genInv (D : RVPosData f ρ) (y : ℝ) : ℝ :=
  sInf (levelSet f D.threshold y)

theorem RVPosData.genInv_def (D : RVPosData f ρ) (y : ℝ) :
    D.genInv y = sInf {x : ℝ | D.threshold ≤ x ∧ y ≤ f x} := rfl

theorem bddBelow_levelSet (f : ℝ → ℝ) (x0 y : ℝ) :
    BddBelow (levelSet f x0 y) := ⟨x0, fun _ hx => hx.1⟩

/-- **Every level set is nonempty**: `f` diverges. -/
theorem RVPosData.levelSet_nonempty (D : RVPosData f ρ) (y : ℝ) :
    (levelSet f D.threshold y).Nonempty := by
  have h : ∀ᶠ x : ℝ in atTop, y ≤ f x :=
    D.tendsto_atTop_self.eventually (eventually_ge_atTop y)
  obtain ⟨X, hX⟩ := eventually_atTop.1 h
  exact ⟨max X D.threshold, le_max_right _ _, hX _ (le_max_left _ _)⟩

/-- **The inverse is above the threshold.** -/
theorem RVPosData.le_genInv (D : RVPosData f ρ) (y : ℝ) : D.threshold ≤ D.genInv y :=
  le_csInf (D.levelSet_nonempty y) (fun _ hx => hx.1)

/-- **The inverse is at most any point of the level set.** -/
theorem RVPosData.genInv_le (D : RVPosData f ρ) {y x : ℝ} (hx : D.threshold ≤ x)
    (hy : y ≤ f x) : D.genInv y ≤ x :=
  csInf_le (bddBelow_levelSet f D.threshold y) ⟨hx, hy⟩

/-- **Infimum approximation**: points of the level set come arbitrarily close to
the inverse from above. -/
theorem RVPosData.lt_genInv_add (D : RVPosData f ρ) {y ε : ℝ} (hε : 0 < ε) :
    ∃ x : ℝ, D.threshold ≤ x ∧ y ≤ f x ∧ x < D.genInv y + ε := by
  have hlt : sInf (levelSet f D.threshold y) < sInf (levelSet f D.threshold y) + ε := by
    linarith
  obtain ⟨x, hx⟩ := exists_lt_of_csInf_lt (D.levelSet_nonempty y) hlt
  exact ⟨x, hx.1.1, hx.1.2, hx.2⟩

/-- **The inverse is nondecreasing.** -/
theorem RVPosData.genInv_mono (D : RVPosData f ρ) {y y' : ℝ} (h : y ≤ y') :
    D.genInv y ≤ D.genInv y' := by
  have hsub : levelSet f D.threshold y' ⊆ levelSet f D.threshold y :=
    fun x hx => ⟨hx.1, le_trans h hx.2⟩
  exact csInf_le_csInf (bddBelow_levelSet f D.threshold y) (D.levelSet_nonempty y') hsub

/-- **The inverse diverges.**  Above a level exceeding the bound of `f` on
`[x₀, M]` every point of the level set is larger than `M`. -/
theorem RVPosData.tendsto_genInv_atTop (D : RVPosData f ρ) : Tendsto D.genInv atTop atTop := by
  refine Filter.tendsto_atTop.mpr fun M => ?_
  rcases le_or_gt M D.threshold with hM | hM
  · exact Eventually.of_forall fun y => le_trans hM (D.le_genInv y)
  obtain ⟨C, hC⟩ := D.bddAbove_Icc M
  filter_upwards [eventually_gt_atTop C] with y hy
  refine le_csInf (D.levelSet_nonempty y) ?_
  intro x hx
  by_contra hcon
  push Not at hcon
  exact absurd (hC x hx.1 (le_of_lt hcon)) (not_le.mpr (lt_of_lt_of_le hy hx.2))

/-! ## The uniform ratio bound for `f` -/

/-- **The uniform convergence theorem** (BGT 1.2.1) for `f`, in the two-sided
form used below: on a compact ratio range `[a,b] ⊂ (0,∞)`, `f (l x) / f x` is
uniformly close to `l ^ ρ`. -/
theorem RVPosData.uniform_ratio (D : RVPosData f ρ) {a b η : ℝ} (ha : 0 < a) (hab : a ≤ b)
    (hη : 0 < η) :
    ∃ Y : ℝ, D.threshold ≤ Y ∧ ∀ x : ℝ, Y ≤ x → ∀ l ∈ Icc a b,
      |f (l * x)| ≤ (l ^ ρ + η) * |f x| ∧ (l ^ ρ - η) * |f x| ≤ |f (l * x)| := by
  obtain ⟨Y₀, -, hY₀⟩ :=
    tendsto_uniformly_abs_ratio_of_regularlyVarying D.measurable_f D.rv ha hab hη
  refine ⟨max Y₀ D.threshold, le_max_right _ _, fun x hx l hl => ?_⟩
  have hxY : Y₀ ≤ x := le_trans (le_max_left _ _) hx
  have hxthr : D.threshold ≤ x := le_trans (le_max_right _ _) hx
  have hfx : 0 < f x := D.pos_above x hxthr
  have h := hY₀ x hxY l hl
  rw [abs_of_pos hfx] at h
  have h2 := abs_le.1 h
  have hfx' : |f x| = f x := abs_of_pos hfx
  constructor
  · have h3 : |f (l * x)| / f x ≤ l ^ ρ + η := by linarith [h2.2]
    have h4 : |f (l * x)| ≤ (l ^ ρ + η) * f x := (div_le_iff₀ hfx).1 h3
    calc |f (l * x)| ≤ (l ^ ρ + η) * f x := h4
      _ = (l ^ ρ + η) * |f x| := by rw [hfx']
  · have h3 : l ^ ρ - η ≤ |f (l * x)| / f x := by linarith [h2.1]
    have h4 : (l ^ ρ - η) * f x ≤ |f (l * x)| := (le_div_iff₀ hfx).1 h3
    calc (l ^ ρ - η) * |f x| = (l ^ ρ - η) * f x := by rw [hfx']
      _ ≤ |f (l * x)| := h4

/-! ## The asymptotic composition law `f (genInv y) ∼ y` -/

/-- **Upper half of the composition law**: `f (genInv y) ≤ (1 + η) y` eventually.
The infimum of the level set lies strictly below `genInv y`, so `f` is below the
level there; the ratio to the level is controlled by regular variation. -/
theorem RVPosData.eventually_comp_le (D : RVPosData f ρ) {η : ℝ} (hη : 0 < η) :
    ∀ᶠ y in atTop, f (D.genInv y) ≤ (1 + η) * y := by
  have hρ := D.pos_index
  -- a small `δ ∈ (0,1)` with `(1 - δ) ^ (-ρ) < 1 + η`
  obtain ⟨δ, hδ0, hδ1, hδratio⟩ : ∃ δ : ℝ, 0 < δ ∧ δ < 1 ∧ (1 - δ) ^ (-ρ) < 1 + η := by
    have hB : 0 < (1 + η / 2) ^ (1 / ρ) := Real.rpow_pos_of_pos (by linarith) _
    have hB1 : 1 < (1 + η / 2) ^ (1 / ρ) := Real.one_lt_rpow (by linarith) (by positivity)
    have hinv1 : ((1 + η / 2) ^ (1 / ρ))⁻¹ < 1 := inv_lt_one_of_one_lt₀ hB1
    have hinv0 : 0 < ((1 + η / 2) ^ (1 / ρ))⁻¹ := inv_pos.2 hB
    refine ⟨1 - ((1 + η / 2) ^ (1 / ρ))⁻¹, by linarith, by linarith, ?_⟩
    have h1 : (1 : ℝ) - (1 - ((1 + η / 2) ^ (1 / ρ))⁻¹) = ((1 + η / 2) ^ (1 / ρ))⁻¹ := by ring
    rw [h1, Real.inv_rpow hB.le, Real.rpow_neg hB.le, inv_inv,
      ← Real.rpow_mul (by linarith : (0:ℝ) ≤ 1 + η / 2), one_div_mul_cancel hρ.ne', Real.rpow_one]
    linarith
  set L := (1 - δ) ^ (-ρ) with hL
  have hLlt : L < 1 + η := hδratio
  -- eventually `(1 - δ) * genInv y` is above the threshold and `f` there is below the level
  have hbig : ∀ᶠ y in atTop, D.threshold ≤ (1 - δ) * D.genInv y := by
    have hg : ∀ᶠ y in atTop, D.threshold / (1 - δ) ≤ D.genInv y :=
      D.tendsto_genInv_atTop.eventually (eventually_ge_atTop (D.threshold / (1 - δ)))
    filter_upwards [hg] with y hy
    rw [div_le_iff₀ (by linarith : (0:ℝ) < 1 - δ)] at hy
    linarith
  have hbelow : ∀ᶠ y in atTop, f ((1 - δ) * D.genInv y) < y := by
    filter_upwards [hbig] with y hy
    by_contra hcon
    push Not at hcon
    have hmem : (1 - δ) * D.genInv y ∈ levelSet f D.threshold y := ⟨hy, hcon⟩
    have h1 : D.genInv y ≤ (1 - δ) * D.genInv y :=
      csInf_le (bddBelow_levelSet f D.threshold y) hmem
    have h2 : 0 < D.genInv y :=
      lt_of_lt_of_le (lt_of_lt_of_le one_pos D.one_le_threshold) (D.le_genInv y)
    nlinarith [mul_pos hδ0 h2]
  -- the ratio `f (genInv y) / f ((1 - δ) * genInv y)` tends to `L`
  have hratio : Tendsto (fun y => f (D.genInv y) / f ((1 - δ) * D.genInv y)) atTop (𝓝 L) := by
    have hscale : Tendsto (fun y : ℝ => (1 - δ) * D.genInv y) atTop atTop :=
      Filter.Tendsto.const_mul_atTop (show (0:ℝ) < 1 - δ by linarith) D.tendsto_genInv_atTop
    have hinvpos : (0:ℝ) < (1 - δ)⁻¹ := by rw [inv_pos]; linarith
    have hcomp := (D.rv.2 (1 - δ)⁻¹ hinvpos).comp hscale
    have hval : ((1 - δ)⁻¹) ^ ρ = L := by
      rw [hL, Real.inv_rpow (by linarith : (0:ℝ) ≤ 1 - δ), Real.rpow_neg (by linarith : (0:ℝ) ≤ 1 - δ)]
    rw [hval] at hcomp
    refine hcomp.congr' ?_
    filter_upwards with y
    show f ((1 - δ)⁻¹ * ((1 - δ) * D.genInv y)) / f ((1 - δ) * D.genInv y)
      = f (D.genInv y) / f ((1 - δ) * D.genInv y)
    rw [show (1 - δ)⁻¹ * ((1 - δ) * D.genInv y) = D.genInv y by field_simp]
  filter_upwards [hbelow, hratio.eventually (eventually_lt_nhds hLlt), hbig,
    eventually_gt_atTop (0 : ℝ)] with y hbelow_y hratio_y hbig_y hypos
  have hfpos : 0 < f ((1 - δ) * D.genInv y) := D.pos_above _ hbig_y
  have h3 : f (D.genInv y) / f ((1 - δ) * D.genInv y) * f ((1 - δ) * D.genInv y)
      = f (D.genInv y) := by field_simp
  rw [← h3]
  exact mul_le_mul (le_of_lt hratio_y) (le_of_lt hbelow_y) hfpos.le (by linarith)


/-- **The inverse is positive.** -/
theorem RVPosData.genInv_pos (D : RVPosData f ρ) (y : ℝ) : 0 < D.genInv y :=
  lt_of_lt_of_le (lt_of_lt_of_le one_pos D.one_le_threshold) (D.le_genInv y)

/-- **Lower half of the composition law**: `(1 - η) y ≤ f (genInv y)` eventually.
A point `x` of the level set just above `genInv y` has `f x ≥ y`, and `f` grows at
most like the `ρ`-th power between `genInv y` and `x` (uniform convergence
theorem), so `f (genInv y)` cannot be much smaller than `y`. -/
theorem RVPosData.eventually_le_comp (D : RVPosData f ρ) {η : ℝ} (hη : 0 < η) (hη1 : η < 1) :
    ∀ᶠ y in atTop, (1 - η) * y ≤ f (D.genInv y) := by
  have hρ := D.pos_index
  set ζ := η / (2 * (1 - η)) with hζ
  have hζ0 : 0 < ζ := by rw [hζ]; positivity
  have hkey : 1 + 2 * ζ = 1 / (1 - η) := by
    rw [hζ]; field_simp; ring
  -- `δ > 0` with `(1 + δ) ^ ρ = 1 + ζ`
  obtain ⟨δ, hδ0, hδρ⟩ : ∃ δ : ℝ, 0 < δ ∧ (1 + δ) ^ ρ = 1 + ζ := by
    refine ⟨(1 + ζ) ^ (1 / ρ) - 1, ?_, ?_⟩
    · have h1 : 1 < (1 + ζ) ^ (1 / ρ) := Real.one_lt_rpow (by linarith) (by positivity)
      linarith
    · have h1 : (1 : ℝ) + ((1 + ζ) ^ (1 / ρ) - 1) = (1 + ζ) ^ (1 / ρ) := by ring
      rw [h1, ← Real.rpow_mul (by linarith : (0:ℝ) ≤ 1 + ζ), one_div_mul_cancel hρ.ne',
        Real.rpow_one]
  obtain ⟨Y, -, hY⟩ := D.uniform_ratio (a := 1) (b := 1 + δ) one_pos (by linarith) hζ0
  filter_upwards [D.tendsto_genInv_atTop.eventually (eventually_ge_atTop Y),
    eventually_gt_atTop (0 : ℝ)] with y hYle hypos
  have hthrle : D.threshold ≤ D.genInv y := D.le_genInv y
  have hgpos : 0 < D.genInv y := D.genInv_pos y
  -- a point of the level set just above the inverse
  obtain ⟨x, hxthr, hxf, hxlt⟩ :=
    D.lt_genInv_add (y := y) (ε := δ * D.genInv y) (by positivity)
  have hxge : D.genInv y ≤ x := D.genInv_le hxthr hxf
  have hl1 : 1 ≤ x / D.genInv y := (le_div_iff₀ hgpos).2 (by linarith)
  have hl2 : x / D.genInv y ≤ 1 + δ := by
    rw [div_le_iff₀ hgpos]
    linarith
  have hxeq : x = (x / D.genInv y) * D.genInv y := by field_simp
  have hbound := (hY (D.genInv y) hYle (x / D.genInv y) ⟨hl1, hl2⟩).1
  have hlr : (x / D.genInv y) ^ ρ ≤ 1 + ζ := by
    calc (x / D.genInv y) ^ ρ ≤ (1 + δ) ^ ρ :=
          Real.rpow_le_rpow (by linarith) hl2 (le_of_lt hρ)
      _ = 1 + ζ := hδρ
  have hxpos : 0 < f x := D.pos_above x hxthr
  have hfx : f x ≤ (1 + 2 * ζ) * f (D.genInv y) := by
    rw [← hxeq, abs_of_pos hxpos, abs_of_pos (D.pos_above _ hthrle)] at hbound
    refine le_trans hbound ?_
    apply mul_le_mul_of_nonneg_right _ (D.pos_above _ hthrle).le
    linarith
  rw [hkey] at hfx
  have h1 : y ≤ (1 / (1 - η)) * f (D.genInv y) := le_trans hxf hfx
  have h2 : (1 - η) * (1 / (1 - η)) = 1 := by field_simp
  calc (1 - η) * y ≤ (1 - η) * ((1 / (1 - η)) * f (D.genInv y)) :=
        mul_le_mul_of_nonneg_left h1 (by linarith)
    _ = ((1 - η) * (1 / (1 - η))) * f (D.genInv y) := by ring
    _ = f (D.genInv y) := by rw [h2, one_mul]

/-- **The composition law `f (genInv y) ∼ y`.**  No exact inverse is asserted:
`genInv` is an *asymptotic* inverse, which is what Proposition I.3.2 uses. -/
theorem RVPosData.tendsto_comp_genInv (D : RVPosData f ρ) :
    Tendsto (fun y => f (D.genInv y) / y) atTop (𝓝 1) := by
  refine tendsto_order.2 ⟨fun b hb => ?_, fun b hb => ?_⟩
  · have hη : 0 < min ((1 - b) / 2) (1 / 2) := lt_min (by linarith) (by norm_num)
    have hη1 : min ((1 - b) / 2) (1 / 2) < 1 := lt_of_le_of_lt (min_le_right _ _) one_half_lt_one
    have hb2 : b < 1 - min ((1 - b) / 2) (1 / 2) := by
      rcases le_or_gt ((1 - b) / 2) (1 / 2) with hle | hgt
      · rw [min_eq_left hle]; linarith
      · rw [min_eq_right (le_of_lt hgt)]; linarith
    filter_upwards [D.eventually_le_comp hη hη1, eventually_gt_atTop (0 : ℝ)] with y h1 h2
    rw [lt_div_iff₀ h2]
    have h3 : b * y < (1 - min ((1 - b) / 2) (1 / 2)) * y :=
      mul_lt_mul_of_pos_right hb2 h2
    exact lt_of_lt_of_le h3 h1
  · have hη : 0 < (b - 1) / 2 := by linarith
    filter_upwards [D.eventually_comp_le hη, eventually_gt_atTop (0 : ℝ)] with y h1 h2
    rw [div_lt_iff₀ h2]
    have h3 : (1 + (b - 1) / 2) * y < b * y := by
      apply mul_lt_mul_of_pos_right _ h2
      linarith
    exact lt_of_le_of_lt h1 h3

/-! ## Upper and lower comparability of the inverse at two levels -/

/-- **Upper comparability**: if `lam < M ^ ρ` then eventually
`genInv (lam * y) ≤ M * genInv y`.  The level `M * genInv y` is above `lam * y`
because `f` grows like the `ρ`-th power (pointwise regular variation along the
diverging argument `genInv y`). -/
theorem RVPosData.eventually_genInv_mul_le (D : RVPosData f ρ) {lam M : ℝ} (hlam : 0 < lam)
    (hM : 0 < M) (hMlam : lam < M ^ ρ) :
    ∀ᶠ y in atTop, D.genInv (lam * y) ≤ M * D.genInv y := by
  have hρ := D.pos_index
  obtain ⟨L, hL1, hL2⟩ : ∃ L : ℝ, lam < L ∧ L < M ^ ρ :=
    ⟨(lam + M ^ ρ) / 2, by linarith, by linarith⟩
  have hLpos : 0 < L := lt_trans hlam hL1
  -- `f (genInv y) ≥ (1 - θ) y` with `L * (1 - θ) > lam`
  have hθ : 0 < (L - lam) / (2 * L) := by positivity
  have hθ1 : (L - lam) / (2 * L) < 1 := by
    rw [div_lt_one (by positivity)]
    linarith
  have hθkey : lam < L * (1 - (L - lam) / (2 * L)) := by
    have h4 : L * (1 - (L - lam) / (2 * L)) = (L + lam) / 2 := by
      field_simp; ring
    rw [h4]; linarith
  have hfy : ∀ᶠ y in atTop, lam * y < L * f (D.genInv y) := by
    filter_upwards [D.eventually_le_comp hθ hθ1, eventually_gt_atTop (0 : ℝ)] with y hy hypos
    have h1 : lam * y < (L * (1 - (L - lam) / (2 * L))) * y :=
      mul_lt_mul_of_pos_right hθkey hypos
    have h2 : L * ((1 - (L - lam) / (2 * L)) * y) ≤ L * f (D.genInv y) :=
      mul_le_mul_of_nonneg_left hy hLpos.le
    nlinarith
  have hratio : ∀ᶠ y in atTop, L < f (M * D.genInv y) / f (D.genInv y) := by
    have hlim : Tendsto (fun y => f (M * D.genInv y) / f (D.genInv y)) atTop (𝓝 (M ^ ρ)) :=
      (D.rv.2 M hM).comp D.tendsto_genInv_atTop
    exact hlim.eventually (eventually_gt_nhds hL2)
  have hthr : ∀ᶠ y in atTop, D.threshold ≤ M * D.genInv y := by
    have hg : ∀ᶠ y in atTop, D.threshold / M ≤ D.genInv y :=
      D.tendsto_genInv_atTop.eventually (eventually_ge_atTop (D.threshold / M))
    filter_upwards [hg] with y hy
    rw [div_le_iff₀ hM] at hy
    linarith
  filter_upwards [hfy, hratio, hthr] with y hfy' hratio' hthr'
  refine D.genInv_le hthr' ?_
  have hfpos : 0 < f (D.genInv y) := D.pos_above _ (D.le_genInv y)
  have h2 : L * f (D.genInv y) < f (M * D.genInv y) := by
    rw [lt_div_iff₀ hfpos] at hratio'
    linarith
  linarith

/-- **Lower comparability**: if `m ^ ρ < lam` then eventually
`m * genInv y ≤ genInv (lam * y)`.  This is the upper comparability applied to the
reciprocal level ratio `1 / lam` (at the point `lam * y`). -/
theorem RVPosData.eventually_mul_genInv_le (D : RVPosData f ρ) {lam m : ℝ} (hlam : 0 < lam)
    (hm : 0 < m) (hmlam : m ^ ρ < lam) :
    ∀ᶠ y in atTop, m * D.genInv y ≤ D.genInv (lam * y) := by
  have h1 : (0:ℝ) < 1 / lam := by positivity
  have h2 : (0:ℝ) < 1 / m := by positivity
  have h3 : 1 / lam < (1 / m) ^ ρ := by
    rw [one_div, one_div, Real.inv_rpow (le_of_lt hm), inv_lt_inv₀ hlam (Real.rpow_pos_of_pos hm ρ)]
    exact hmlam
  have h := D.eventually_genInv_mul_le (lam := 1 / lam) (M := 1 / m) h1 h2 h3
  have hscale : Tendsto (fun y : ℝ => lam * y) atTop atTop :=
    (tendsto_const_mul_atTop_of_pos hlam).2 tendsto_id
  have hcomp : ∀ᶠ y in atTop, D.genInv (1 / lam * (lam * y)) ≤ 1 / m * D.genInv (lam * y) :=
    hscale.eventually h
  filter_upwards [hcomp] with y hy
  rw [show 1 / lam * (lam * y) = y by field_simp] at hy
  calc m * D.genInv y ≤ m * (1 / m * D.genInv (lam * y)) := mul_le_mul_of_nonneg_left hy hm.le
    _ = D.genInv (lam * y) := by field_simp

/-! ## `genInv` is regularly varying of index `1 / ρ` -/

/-- **The inverse ratio law**: `genInv (lam * y) / genInv y → lam ^ (1 / ρ)`.  The
two comparability estimates above give a lower and an upper bound for every test
value below, respectively above, the limit. -/
theorem RVPosData.tendsto_genInv_ratio (D : RVPosData f ρ) {lam : ℝ} (hlam : 0 < lam) :
    Tendsto (fun y => D.genInv (lam * y) / D.genInv y) atTop (𝓝 (lam ^ (1 / ρ))) := by
  have hρ := D.pos_index
  set c := lam ^ (1 / ρ) with hc
  have hcpos : 0 < c := Real.rpow_pos_of_pos hlam _
  have hcpow : c ^ ρ = lam := by
    rw [hc, ← Real.rpow_mul hlam.le, one_div_mul_cancel hρ.ne', Real.rpow_one]
  refine tendsto_order.2 ⟨fun b hb => ?_, fun b hb => ?_⟩
  · -- `b < c`: use a comparison value `m ∈ (b, c)`
    set m := max ((b + c) / 2) (c / 2) with hm
    have hmpos : 0 < m := lt_of_lt_of_le (by linarith) (le_max_right _ _)
    have hbm : b < m := lt_of_lt_of_le (by linarith) (le_max_left _ _)
    have hmc : m < c := max_lt (by linarith) (by linarith)
    have hmpow : m ^ ρ < lam := by
      rw [← hcpow]
      exact Real.rpow_lt_rpow (le_of_lt hmpos) hmc hρ
    filter_upwards [D.eventually_mul_genInv_le hlam hmpos hmpow] with y h1
    rw [lt_div_iff₀ (D.genInv_pos y)]
    have h3 : b * D.genInv y < m * D.genInv y := mul_lt_mul_of_pos_right hbm (D.genInv_pos y)
    linarith
  · -- `c < b`: use a comparison value `M ∈ (c, b)`
    obtain ⟨M, hcM, hMb⟩ : ∃ M : ℝ, c < M ∧ M < b := ⟨(c + b) / 2, by linarith, by linarith⟩
    have hMpos : 0 < M := lt_trans hcpos hcM
    have hMpow : lam < M ^ ρ := by
      rw [← hcpow]
      exact Real.rpow_lt_rpow (le_of_lt hcpos) hcM hρ
    filter_upwards [D.eventually_genInv_mul_le hlam hMpos hMpow] with y h1
    rw [div_lt_iff₀ (D.genInv_pos y)]
    have h3 : M * D.genInv y < b * D.genInv y := mul_lt_mul_of_pos_right hMb (D.genInv_pos y)
    linarith

/-- **The inverse is monotone** (all level sets are nonempty, so this holds
globally). -/
theorem RVPosData.monotone_genInv (D : RVPosData f ρ) : Monotone D.genInv :=
  fun _ _ h => D.genInv_mono h

/-- **The inverse is measurable** (as a monotone function). -/
theorem RVPosData.measurable_genInv (D : RVPosData f ρ) : Measurable D.genInv :=
  D.monotone_genInv.measurable

/-- **The generalized inverse is regularly varying of index `1 / ρ`** (BGT
Theorem 1.5.12, for arbitrary measurable `f` of positive index; no monotonicity or
continuity is used). -/
theorem RVPosData.regularlyVaryingAtTop_genInv (D : RVPosData f ρ) :
    RegularlyVaryingAtTop D.genInv (1 / ρ) :=
  ⟨Eventually.of_forall fun y => ne_of_gt (D.genInv_pos y),
    fun l hl => D.tendsto_genInv_ratio hl⟩

/-- **Assembly interface for the volume-tail step** (`Analysis/VolumeTail.lean`):
the generalized inverse is measurable, eventually positive, and regularly varying of
index `1 / (a α)` when the index of `f` is `ρ = a α`. -/
theorem RVPosData.genInv_volumeTail_data (D : RVPosData f ρ) {a α : ℝ} (ha : 0 < a)
    (hα : 0 < α) (hρα : ρ = a * α) :
    Measurable D.genInv ∧ (∀ᶠ x in atTop, 0 < D.genInv x) ∧
      RegularlyVaryingAtTop D.genInv (1 / (a * α)) := by
  refine ⟨D.measurable_genInv, Eventually.of_forall fun x => D.genInv_pos x, ?_⟩
  have h : 1 / (a * α) = 1 / ρ := by rw [hρα]
  rw [h]
  exact D.regularlyVaryingAtTop_genInv

/-! ## The level laws in the intensity variable `h ↓ 0⁺` -/

/-- **Level ratio law in the intensity variable**: `genInv (λ / h) / genInv (1 / h)
→ λ ^ (1 / ρ)` as `h ↓ 0⁺`. -/
theorem RVPosData.tendsto_genInv_levelRatio (D : RVPosData f ρ) {lam : ℝ} (hlam : 0 < lam) :
    Tendsto (fun h : ℝ => D.genInv (lam / h) / D.genInv (1 / h)) (𝓝[>] 0)
      (𝓝 (lam ^ (1 / ρ))) := by
  have hinv : Tendsto (fun h : ℝ => h⁻¹) (𝓝[>] (0:ℝ)) atTop := tendsto_inv_nhdsGT_zero
  have hcomp := (D.tendsto_genInv_ratio hlam).comp hinv
  refine hcomp.congr' ?_
  filter_upwards with h
  show D.genInv (lam * h⁻¹) / D.genInv h⁻¹ = D.genInv (lam / h) / D.genInv (1 / h)
  have h1 : lam * h⁻¹ = lam / h := by rw [div_eq_mul_inv]
  have h2 : h⁻¹ = 1 / h := by rw [one_div]
  rw [h1, h2]

/-- The level argument `λ / (A₂ h)` tends to `∞` as `h ↓ 0⁺`. -/
theorem tendsto_level_arg {A₂ lam : ℝ} (hA₂ : 0 < A₂) (hlam : 0 < lam) :
    Tendsto (fun h : ℝ => lam / (A₂ * h)) (𝓝[>] 0) atTop := by
  have hA : 0 < lam / A₂ := div_pos hlam hA₂
  have h1 : Tendsto (fun h : ℝ => (lam / A₂) * h⁻¹) (𝓝[>] (0:ℝ)) atTop :=
    (tendsto_const_mul_atTop_of_pos hA).2 tendsto_inv_nhdsGT_zero
  refine h1.congr' ?_
  filter_upwards [self_mem_nhdsWithin] with h hh
  have hh0 : h ≠ 0 := ne_of_gt hh
  have hA₂0 : A₂ ≠ 0 := hA₂.ne'
  have h2 : (lam / A₂) * h⁻¹ = lam / (A₂ * h) := by field_simp
  rw [h2]

/-- **The level is filled**: with the cutoff `r h = genInv (λ / (A₂ h))`,
`h · (A₂ · f (r h)) → λ`.  This is the asymptotic content of the paper's
`h Ê_{r(h)}|K| → λ`. -/
theorem RVPosData.tendsto_level_filled (D : RVPosData f ρ) {A₂ lam : ℝ} (hA₂ : 0 < A₂)
    (hlam : 0 < lam) :
    Tendsto (fun h : ℝ => h * (A₂ * f (D.genInv (lam / (A₂ * h))))) (𝓝[>] 0) (𝓝 lam) := by
  have hy := tendsto_level_arg hA₂ hlam
  have hcomp := D.tendsto_comp_genInv.comp hy
  have h2 : Tendsto (fun h : ℝ =>
      lam * (f (D.genInv (lam / (A₂ * h))) / (lam / (A₂ * h)))) (𝓝[>] (0:ℝ)) (𝓝 (lam * 1)) :=
    hcomp.const_mul lam
  rw [mul_one] at h2
  refine h2.congr' ?_
  filter_upwards [self_mem_nhdsWithin] with h hh
  have hh0 : h ≠ 0 := ne_of_gt hh
  have hA₂0 : A₂ ≠ 0 := hA₂.ne'
  field_simp

/-- **The level is filled for the moment function itself**: if `ψ r / f r → A₂`
(the paper's `Ê_r |K| ∼ A₂ f r`) then with the cutoff `r h = genInv (λ / (A₂ h))`,

  `h · ψ (r h) → λ`,

which is the paper's `h Ê_{r(h)}|K| → λ` at the top of p. 31. -/
theorem RVPosData.tendsto_level_filled_of_tendsto_div (D : RVPosData f ρ) {ψ : ℝ → ℝ}
    {A₂ lam : ℝ} (hA₂ : 0 < A₂) (hlam : 0 < lam)
    (hψ : Tendsto (fun r => ψ r / f r) atTop (𝓝 A₂)) :
    Tendsto (fun h : ℝ => h * ψ (D.genInv (lam / (A₂ * h)))) (𝓝[>] 0) (𝓝 lam) := by
  have hy := tendsto_level_arg hA₂ hlam
  have hfilled := D.tendsto_level_filled (f := f) hA₂ hlam
  have hratio : Tendsto (fun h : ℝ =>
      ψ (D.genInv (lam / (A₂ * h))) / (A₂ * f (D.genInv (lam / (A₂ * h)))))
      (𝓝[>] 0) (𝓝 1) := by
    have harg : Tendsto (fun h : ℝ => D.genInv (lam / (A₂ * h))) (𝓝[>] 0) atTop :=
      D.tendsto_genInv_atTop.comp hy
    have h1 : Tendsto (fun h : ℝ =>
        ψ (D.genInv (lam / (A₂ * h))) / f (D.genInv (lam / (A₂ * h)))) (𝓝[>] 0) (𝓝 A₂) :=
      hψ.comp harg
    have h2 : Tendsto (fun h : ℝ =>
        ψ (D.genInv (lam / (A₂ * h))) / f (D.genInv (lam / (A₂ * h))) / A₂)
        (𝓝[>] 0) (𝓝 (A₂ / A₂)) := h1.div_const A₂
    rw [div_self hA₂.ne'] at h2
    refine h2.congr' ?_
    filter_upwards with h
    show ψ (D.genInv (lam / (A₂ * h))) / f (D.genInv (lam / (A₂ * h))) / A₂
      = ψ (D.genInv (lam / (A₂ * h))) / (A₂ * f (D.genInv (lam / (A₂ * h))))
    have hfne : f (D.genInv (lam / (A₂ * h))) ≠ 0 :=
      ne_of_gt (D.pos_above _ (D.le_genInv _))
    field_simp
  have hprod : Tendsto (fun h : ℝ =>
      (h * (A₂ * f (D.genInv (lam / (A₂ * h))))) *
        (ψ (D.genInv (lam / (A₂ * h))) / (A₂ * f (D.genInv (lam / (A₂ * h))))))
      (𝓝[>] 0) (𝓝 (lam * 1)) := hfilled.mul hratio
  rw [mul_one] at hprod
  refine hprod.congr' ?_
  filter_upwards with h
  have hfne : f (D.genInv (lam / (A₂ * h))) ≠ 0 :=
    ne_of_gt (D.pos_above _ (D.le_genInv _))
  have hzero : A₂ * f (D.genInv (lam / (A₂ * h))) ≠ 0 :=
    mul_ne_zero hA₂.ne' (ne_of_gt (D.pos_above _ (D.le_genInv _)))
  have key : (A₂ * f (D.genInv (lam / (A₂ * h)))) *
      (ψ (D.genInv (lam / (A₂ * h))) / (A₂ * f (D.genInv (lam / (A₂ * h)))))
      = ψ (D.genInv (lam / (A₂ * h))) := mul_div_cancel₀ _ hzero
  show (h * (A₂ * f (D.genInv (lam / (A₂ * h))))) *
        (ψ (D.genInv (lam / (A₂ * h))) / (A₂ * f (D.genInv (lam / (A₂ * h)))))
      = h * ψ (D.genInv (lam / (A₂ * h)))
  rw [mul_assoc, key]

/-- **The Proposition I.3.2 normalising ratio**: with the cutoff
`r h = genInv (λ / (A₂ h))` and `τ h = genInv (1 / h)`, and with the regularly
varying index `ρ = a α` of the hypothesis,

  `(r h) ^ α / (τ h) ^ α → (λ / A₂) ^ (1 / a)`   as `h ↓ 0⁺`.

This is exactly the step from `f⁻¹ (λ / (A₂ h))` to `f⁻¹ (1 / h)` in (I.3.7). -/
theorem RVPosData.tendsto_level_normalization (D : RVPosData f ρ) {a α A₂ lam : ℝ}
    (ha : 0 < a) (hα : 0 < α) (hρα : ρ = a * α) (hA₂ : 0 < A₂) (hlam : 0 < lam) :
    Tendsto (fun h : ℝ => (D.genInv (lam / (A₂ * h))) ^ α / (D.genInv (1 / h)) ^ α)
      (𝓝[>] 0) (𝓝 ((lam / A₂) ^ (1 / a))) := by
  have hA : 0 < lam / A₂ := div_pos hlam hA₂
  have hbase : Tendsto (fun h : ℝ => D.genInv (lam / (A₂ * h)) / D.genInv (1 / h))
      (𝓝[>] 0) (𝓝 ((lam / A₂) ^ (1 / ρ))) := by
    refine (D.tendsto_genInv_levelRatio hA).congr' ?_
    filter_upwards [self_mem_nhdsWithin] with h hh
    show D.genInv (lam / A₂ / h) / D.genInv (1 / h)
      = D.genInv (lam / (A₂ * h)) / D.genInv (1 / h)
    rw [show lam / A₂ / h = lam / (A₂ * h) by field_simp]
  have hcont : Tendsto (fun t : ℝ => t ^ α) (𝓝 ((lam / A₂) ^ (1 / ρ)))
      (𝓝 (((lam / A₂) ^ (1 / ρ)) ^ α)) :=
    (Real.continuousAt_rpow_const _ α
      (Or.inr hα.le)).tendsto
  have hexp : (1 / ρ) * α = 1 / a := by
    have hρne : ρ ≠ 0 := D.pos_index.ne'
    have hane : a ≠ 0 := ha.ne'
    have hαne : α ≠ 0 := hα.ne'
    field_simp
    linarith
  have hval : ((lam / A₂) ^ (1 / ρ)) ^ α = (lam / A₂) ^ (1 / a) := by
    rw [← Real.rpow_mul (le_of_lt hA), hexp]
  rw [hval] at hcont
  refine (hcont.comp hbase).congr' ?_
  filter_upwards with h
  show (D.genInv (lam / (A₂ * h)) / D.genInv (1 / h)) ^ α
    = (D.genInv (lam / (A₂ * h))) ^ α / (D.genInv (1 / h)) ^ α
  rw [Real.div_rpow (le_of_lt (D.genInv_pos _)) (le_of_lt (D.genInv_pos _))]


/-- **The power form of the level ratio law**: `(genInv (λ y)) ^ α / (genInv y) ^ α →
λ ^ (α / ρ)`.  With `ρ = a α` this is `λ ^ (1 / a)`, the exponent appearing in
(I.3.7). -/
theorem RVPosData.tendsto_genInv_rpow_ratio (D : RVPosData f ρ) {lam α : ℝ} (hlam : 0 < lam)
    (hα : 0 < α) :
    Tendsto (fun y => (D.genInv (lam * y)) ^ α / (D.genInv y) ^ α) atTop
      (𝓝 (lam ^ (α / ρ))) := by
  have hbase := D.tendsto_genInv_ratio hlam
  have hval : (lam ^ (1 / ρ)) ^ α = lam ^ (α / ρ) := by
    rw [← Real.rpow_mul hlam.le]
    ring_nf
  have hcont : Tendsto (fun t : ℝ => t ^ α) (𝓝 (lam ^ (1 / ρ))) (𝓝 (lam ^ (α / ρ))) := by
    have h := (Real.continuousAt_rpow_const (lam ^ (1 / ρ)) α (Or.inr hα.le)).tendsto
    rwa [hval] at h
  have hcomp := hcont.comp hbase
  refine hcomp.congr' ?_
  filter_upwards with y
  show (D.genInv (lam * y) / D.genInv y) ^ α
    = (D.genInv (lam * y)) ^ α / (D.genInv y) ^ α
  rw [Real.div_rpow (le_of_lt (D.genInv_pos _)) (le_of_lt (D.genInv_pos _))]

/-- **Level selections with a bounded ratio obey the same law.**  If `v → ∞` and
`u h / v h` is eventually in a compact `[a,b] ⊂ (0,∞)` and
`f (u h) / f (v h) → c > 0`, then `u h / v h → c ^ (1/ρ)`.

This is the form in which an *arbitrary* level selection (not necessarily
`genInv`) can be compared: the uniform convergence theorem (BGT 1.2.1) identifies
`f (u h) / f (v h)` with `(u h / v h) ^ ρ` on the compact ratio range. -/
theorem RVPosData.tendsto_div_of_bounded_ratio (D : RVPosData f ρ) {α : Type*}
    {l : Filter α} {u v : α → ℝ} {c a b : ℝ} (ha : 0 < a) (hab : a ≤ b)
    (hmem : ∀ᶠ h in l, u h / v h ∈ Icc a b) (hv : Tendsto v l atTop)
    (hratio : Tendsto (fun h => f (u h) / f (v h)) l (𝓝 c)) (hc : 0 < c) :
    Tendsto (fun h => u h / v h) l (𝓝 (c ^ (1 / ρ))) := by
  have hρ := D.pos_index
  have hpow : Tendsto (fun h => (u h / v h) ^ ρ) l (𝓝 c) := by
    rw [Metric.tendsto_nhds]
    intro ε hε
    obtain ⟨Y, -, hY⟩ := D.uniform_ratio (a := a) (b := b) ha hab (by linarith : 0 < ε / 2)
    have hev1 : ∀ᶠ h in l, Y ≤ v h := hv.eventually (eventually_ge_atTop Y)
    have hev2 : ∀ᶠ h in l, D.threshold ≤ v h := hv.eventually (eventually_ge_atTop D.threshold)
    have hev3 : ∀ᶠ h in l, f (u h) / f (v h) ∈ Ioo (c - ε / 2) (c + ε / 2) :=
      hratio.eventually (Ioo_mem_nhds (by linarith) (by linarith))
    have hev4 : ∀ᶠ h in l, 0 < f (u h) / f (v h) :=
      hratio.eventually (eventually_gt_nhds hc)
    filter_upwards [hmem, hev1, hev2, hev3, hev4] with h hmem' hYle hthr hrat hratpos
    have hvpos : 0 < f (v h) := D.pos_above _ hthr
    have huval : (u h / v h) * v h = u h := by
      have hv0 : v h ≠ 0 := by linarith [lt_of_lt_of_le one_pos D.one_le_threshold]
      field_simp
    have hfu : 0 < f (u h) := by
      have := mul_pos hratpos hvpos
      rwa [div_mul_cancel₀] at this
      linarith [lt_of_lt_of_le one_pos D.one_le_threshold]
    obtain ⟨hb1, hb2⟩ := hY (v h) hYle (u h / v h) hmem'
    rw [huval, abs_of_pos hfu, abs_of_pos hvpos] at hb1 hb2
    have hi1 : f (u h) / f (v h) ≤ (u h / v h) ^ ρ + ε / 2 := by
      rw [div_le_iff₀ hvpos]; linarith
    have hi2 : (u h / v h) ^ ρ - ε / 2 ≤ f (u h) / f (v h) := by
      rw [le_div_iff₀ hvpos]; linarith
    rw [Real.dist_eq, abs_lt]
    constructor <;> linarith [hrat.1, hrat.2]
  have hcont : Tendsto (fun t : ℝ => t ^ (1 / ρ)) (𝓝 c) (𝓝 (c ^ (1 / ρ))) :=
    (Real.continuousAt_rpow_const c (1 / ρ) (Or.inl hc.ne')).tendsto
  have h2 := hcont.comp hpow
  refine h2.congr' ?_
  filter_upwards [hmem] with h hhmem
  have hlpos : 0 < u h / v h := lt_of_lt_of_le ha hhmem.1
  show ((u h / v h) ^ ρ) ^ (1 / ρ) = u h / v h
  rw [← Real.rpow_mul (le_of_lt hlpos), mul_one_div_cancel hρ.ne', Real.rpow_one]

/-- **Proposition I.3.2, inverse/scale layer, end to end (paper's hypotheses).**
Let `f` be measurable and regularly varying of index `a α` (`a, α > 0`) — no
monotonicity, no continuity — and let the moment function `ψ = Ê_·|K|` satisfy
`ψ r / f r → A₂` with `A₂ > 0` and `ψ ≥ 0`.  Then the generalized inverse `g` of `f`
provides the cutoff `r h = g (λ / (A₂ h))` with

* `h · ψ (r h) → λ` (the level is filled), and
* `(r h) ^ α / (g (1 / h)) ^ α → (λ / A₂) ^ (1 / a)` (the (I.3.7) normalisation),

and `g` is measurable, eventually positive and regularly varying of index `1/(a α)`.
-/
theorem prop_I_3_2_inverse_layer {f ψ : ℝ → ℝ} {a α A₂ lam : ℝ}
    (ha : 0 < a) (hα : 0 < α) (hmeas : Measurable f)
    (hrv : RegularlyVaryingAtTop f (a * α)) (hA₂ : 0 < A₂)
    (hψ : ∀ᶠ r in atTop, 0 ≤ ψ r)
    (hψ2 : Tendsto (fun r => ψ r / (A₂ * f r)) atTop (𝓝 1)) (hlam : 0 < lam) :
    let D : RVPosData f (a * α) := RVPosData.of_moment (by positivity) hmeas hrv hA₂ hψ hψ2
    (Measurable D.genInv ∧ (∀ᶠ x in atTop, 0 < D.genInv x) ∧
        RegularlyVaryingAtTop D.genInv (1 / (a * α))) ∧
      Tendsto (fun h : ℝ => h * ψ (D.genInv (lam / (A₂ * h)))) (𝓝[>] 0) (𝓝 lam) ∧
      Tendsto (fun h : ℝ => (D.genInv (lam / (A₂ * h))) ^ α / (D.genInv (1 / h)) ^ α)
        (𝓝[>] 0) (𝓝 ((lam / A₂) ^ (1 / a))) := by
  dsimp only
  have hψdiv : Tendsto (fun r => ψ r / f r) atTop (𝓝 A₂) := by
    have h := hψ2.const_mul A₂
    rw [mul_one] at h
    refine h.congr' ?_
    filter_upwards [hrv.1] with r hfr
    field_simp
  refine ⟨RVPosData.genInv_volumeTail_data _ ha hα rfl, ?_, ?_⟩
  · exact RVPosData.tendsto_level_filled_of_tendsto_div _ hA₂ hlam hψdiv
  · exact RVPosData.tendsto_level_normalization _ ha hα rfl hA₂ hlam

end PercLib.CriticalLRP.Analysis

/-! ### Axiom audit -/

#print axioms PercLib.CriticalLRP.Analysis.eventually_pos_of_tendsto_div
#print axioms PercLib.CriticalLRP.Analysis.RVPosData.nonempty
#print axioms PercLib.CriticalLRP.Analysis.RVPosData.of_moment
#print axioms PercLib.CriticalLRP.Analysis.RVPosData.tendsto_atTop_self
#print axioms PercLib.CriticalLRP.Analysis.RVPosData.levelSet_nonempty
#print axioms PercLib.CriticalLRP.Analysis.RVPosData.le_genInv
#print axioms PercLib.CriticalLRP.Analysis.RVPosData.genInv_le
#print axioms PercLib.CriticalLRP.Analysis.RVPosData.lt_genInv_add
#print axioms PercLib.CriticalLRP.Analysis.RVPosData.genInv_mono
#print axioms PercLib.CriticalLRP.Analysis.RVPosData.tendsto_genInv_atTop
#print axioms PercLib.CriticalLRP.Analysis.RVPosData.uniform_ratio
#print axioms PercLib.CriticalLRP.Analysis.RVPosData.eventually_comp_le
#print axioms PercLib.CriticalLRP.Analysis.RVPosData.eventually_le_comp
#print axioms PercLib.CriticalLRP.Analysis.RVPosData.tendsto_comp_genInv
#print axioms PercLib.CriticalLRP.Analysis.RVPosData.eventually_genInv_mul_le
#print axioms PercLib.CriticalLRP.Analysis.RVPosData.eventually_mul_genInv_le
#print axioms PercLib.CriticalLRP.Analysis.RVPosData.monotone_genInv
#print axioms PercLib.CriticalLRP.Analysis.RVPosData.measurable_genInv
#print axioms PercLib.CriticalLRP.Analysis.RVPosData.genInv_volumeTail_data
#print axioms PercLib.CriticalLRP.Analysis.RVPosData.tendsto_genInv_ratio
#print axioms PercLib.CriticalLRP.Analysis.RVPosData.regularlyVaryingAtTop_genInv
#print axioms PercLib.CriticalLRP.Analysis.RVPosData.tendsto_genInv_rpow_ratio
#print axioms PercLib.CriticalLRP.Analysis.RVPosData.tendsto_div_of_bounded_ratio
#print axioms PercLib.CriticalLRP.Analysis.RVPosData.tendsto_genInv_levelRatio
#print axioms PercLib.CriticalLRP.Analysis.tendsto_level_arg
#print axioms PercLib.CriticalLRP.Analysis.RVPosData.tendsto_level_filled
#print axioms PercLib.CriticalLRP.Analysis.RVPosData.tendsto_level_filled_of_tendsto_div
#print axioms PercLib.CriticalLRP.Analysis.RVPosData.tendsto_level_normalization
#print axioms PercLib.CriticalLRP.Analysis.prop_I_3_2_inverse_layer
