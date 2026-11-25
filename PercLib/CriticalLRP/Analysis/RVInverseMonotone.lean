/-
Migration source: https://github.com/yujinhkim/Critical-Long-range-percolation
Integration revision: 3b3d1d0e43ef940bfaa2292ee5c2ee094ac4edbf
Licence: Apache-2.0 for the PercLib Lean sources and tooling; see third_party/critical-lrp/.
External provenance and modifications are recorded in the file-specific notices below.
-/

/-
# Regular variation at `∞`: the inverse / scale-selection layer

This file supplies the layer of Proposition I.3.2 of T. Hutchcroft,
*Critical long-range percolation I: High effective dimension*, arXiv:2508.18807v1,
Section I.3.2 (pp. 30-32) that is used to make the *choice of the cutoff*
`r = f⁻¹ (λ / (A₂ h))` and to turn `(I.3.7)` into the claim

  `P_{r,h}(0 ↔ G) ~ (A₁ / (A₂^{1/a} λ^{1 - 1/a})) · ∫₀^∞ (1 - e^{-λx})/x dQ_∞(x)
                    · f⁻¹(1/h)^α · h`.

Nothing here is probabilistic: everything is a statement about a regularly
varying function `f` of positive index `ρ = a · α`.

## Contents

* `RegularlyVaryingAtTop.const_mul` — a positive multiple of a regularly varying
  function is regularly varying with the same index (hypothesis 2 of I.3.2
  states `Ê_r|K| ∼ A₂ f r`, so `A₂ f` itself is the regularly varying object).
* `tendsto_atTop_of_monotone_regularlyVarying` — a nondecreasing regularly
  varying function of positive index tends to `∞` (so all levels are eventually
  attained, and the level selection below is well defined).
* `tendsto_atTop_of_mul_tendsto_zero` — if `h → 0⁺` and `h · g h → c > 0` then
  `g h → ∞` (the step `h Ê_r|K| → λ` gives `Ê_r|K| → ∞`).
* `tendsto_div_of_monotone_regularlyVarying` — **the scale-selection lemma**:
  if `u, v` are level selections for `f` up to the running factor `h`
  (`h f (u h) → c₁`, `h f (v h) → c₂`, both limits in `(0,∞)`) then
  `u h / v h → (c₁/c₂)^{1/ρ}`.  This is the precise content of "`f⁻¹` is
  regularly varying of index `1/ρ`" ([24, Theorem 1.5.12]) that the proof of
  I.3.2 uses, stated for *level selections* rather than a literal inverse so
  that it applies verbatim to the paper's `r = f⁻¹(λ/(A₂ h))`.
* `levelInverse` — the canonical level selection, defined from the
  intermediate value theorem, with `f (levelInverse y) = y` for `y ≥ f X`
  and `levelInverse y ≥ X` always.
* `regularlyVaryingAtTop_levelInverse` — the literal inverse is regularly
  varying of index `1/ρ` (BGT Theorem 1.5.12 / the paper's citation [24]).
* `paper_level_law` — the composed statement actually used at (I.3.7):
  with `r h = levelInverse (λ/(A₂ h))` and `τ h = levelInverse (1/h)`,
  `r h ^ α / (τ h) ^ α → λ^{1/a} / A₂^{1/a}`.
* `paper_level_law_isEquivalent` — the exact asymptotic shape of (I.3.7),
  `A₁ · (r h)^α · h / λ ~ (A₁ / A₂^{1/a} · λ^{-(1-1/a)}) · ((τ h)^α · h)`,
  whose constant is the one appearing inside the definition of `A₃`.

## Scope

The inverse and cutoff constructions here require `f` nondecreasing and positive on `[X,∞)`;
literal level selections additionally require continuity. These assumptions are explicit in the
statements. Proposition I.3.2 assumes only measurable regular variation, so this is the
monotone-continuous component, not by itself the general inverse theorem. Std.Symm Potter
bounds at the end are independent of monotonicity. Proposition I.3.2 needs a further reduction
from an arbitrary regularly varying function to a constructively usable level selection.
-/
module

public import PercLib.CriticalLRP.Analysis.MonotoneRV
public import PercLib.CriticalLRP.Analysis.RVAlgebra

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

/-! ## Multiples and powers of regularly varying functions -/

/-- A nonzero multiple of a regularly varying function is regularly varying with
the same index.  (Hypothesis 2 of I.3.2 reads `Ê_r|K| ∼ A₂ f r` with `f`
regularly varying, so `A₂ f` is the regularly varying object one works with.) -/
theorem RegularlyVaryingAtTop.const_mul {f : ℝ → ℝ} {ρ c : ℝ} (hc : c ≠ 0)
    (hf : RegularlyVaryingAtTop f ρ) :
    RegularlyVaryingAtTop (fun x => c * f x) ρ := by
  constructor
  · filter_upwards [hf.1] with x hx
    exact mul_ne_zero hc hx
  · intro l hl
    refine (hf.2 l hl).congr' ?_
    filter_upwards [hf.1] with x hx
    field_simp

/-! ## A regularly varying function of positive index is unbounded -/

/-- **A nondecreasing regularly varying function of positive index tends to `∞`.**
This is what makes the level sets of `f` unbounded, so that `f⁻¹(y)` can be
chosen for every large `y`. -/
theorem tendsto_atTop_of_monotone_regularlyVarying {f : ℝ → ℝ} {ρ X : ℝ} (hρ : 0 < ρ)
    (hX : 0 < X) (hrv : RegularlyVaryingAtTop f ρ)
    (hmono : ∀ x y : ℝ, X ≤ x → x ≤ y → f x ≤ f y)
    (hpos : ∀ x : ℝ, X ≤ x → 0 < f x) : Tendsto f atTop atTop := by
  have h2 : Tendsto (fun x => f (2 * x) / f x) atTop (𝓝 (2 ^ ρ)) := hrv.2 2 (by norm_num)
  have h2ρ : 1 < (2 : ℝ) ^ ρ := Real.one_lt_rpow (by norm_num) hρ
  obtain ⟨c, hc1, hc2⟩ : ∃ c : ℝ, 1 < c ∧ c < (2 : ℝ) ^ ρ :=
    ⟨(1 + 2 ^ ρ) / 2, by linarith, by linarith⟩
  -- one-step bound `c * f x ≤ f (2 * x)` for all large `x`
  obtain ⟨X₁, hX₁X, hstep⟩ : ∃ X₁ : ℝ, X ≤ X₁ ∧ ∀ x : ℝ, X₁ ≤ x → c * f x ≤ f (2 * x) := by
    have hev : ∀ᶠ x in atTop, c < f (2 * x) / f x :=
      h2.eventually (eventually_gt_nhds hc2)
    obtain ⟨X', hX'⟩ := eventually_atTop.1 hev
    refine ⟨max X X', le_max_left _ _, fun x hx => ?_⟩
    have hxX : X ≤ x := le_trans (le_max_left _ _) hx
    have hxX' : X' ≤ x := le_trans (le_max_right _ _) hx
    have hfx : 0 < f x := hpos x hxX
    have h1 := hX' x hxX'
    rw [lt_div_iff₀ hfx] at h1
    linarith
  have hX₁pos : 0 < X₁ := lt_of_lt_of_le hX hX₁X
  -- iterate along the doubling ladder
  have hpow1 : ∀ k : ℕ, (1 : ℝ) ≤ 2 ^ k := fun _ => one_le_pow₀ (by norm_num : (1 : ℝ) ≤ 2)
  have hladder : ∀ k : ℕ, c ^ k * f X₁ ≤ f (X₁ * 2 ^ k) := by
    intro k
    induction k with
    | zero => simp
    | succ n ih =>
      have hge : X₁ ≤ X₁ * 2 ^ n := by
        simpa using mul_le_mul_of_nonneg_left (hpow1 n) hX₁pos.le
      have hstep' : c * f (X₁ * 2 ^ n) ≤ f (2 * (X₁ * 2 ^ n)) := hstep _ hge
      have harg : (2 : ℝ) * (X₁ * 2 ^ n) = X₁ * 2 ^ (n + 1) := by ring
      rw [harg] at hstep'
      have hred : c ^ (n + 1) * f X₁ = c * (c ^ n * f X₁) := by ring
      rw [hred]
      exact le_trans (mul_le_mul_of_nonneg_left ih (by linarith : (0:ℝ) ≤ c)) hstep'
  rw [tendsto_atTop_atTop]
  intro M
  have hk : ∃ k : ℕ, M ≤ c ^ k * f X₁ := by
    have ht := (tendsto_pow_atTop_atTop_of_one_lt hc1).atTop_mul_const (hpos X₁ hX₁X)
    obtain ⟨K, hK⟩ := eventually_atTop.1 (ht.eventually (eventually_ge_atTop M))
    exact ⟨K, hK K le_rfl⟩
  obtain ⟨k, hk⟩ := hk
  refine ⟨X₁ * 2 ^ k, fun a ha => ?_⟩
  refine le_trans hk (le_trans (hladder k) ?_)
  refine hmono _ _ (le_trans hX₁X ?_) ha
  simpa using mul_le_mul_of_nonneg_left (hpow1 k) hX₁pos.le

/-! ## A reciprocal multiplicative limit forces divergence -/

/-- If `g → 0⁺` and `g x * a x → c > 0` then `a x → ∞`.  With `g = h → 0⁺` and
`a h = Ê_{r(h)}|K|`, the hypothesis `h Ê_{r(h)}|K| → λ` therefore gives
`Ê_{r(h)}|K| → ∞`, which is what identifies the selected cutoff `r(h)`. -/
theorem tendsto_atTop_of_mul_tendsto_zero {α : Type*} {l : Filter α} {a g : α → ℝ} {c : ℝ}
    (hc : 0 < c) (hg0 : Tendsto g l (𝓝 0)) (hg : ∀ᶠ x in l, 0 < g x)
    (ha : Tendsto (fun x => g x * a x) l (𝓝 c)) : Tendsto a l atTop := by
  rw [tendsto_atTop]
  intro M
  obtain ⟨M', hMM', hM'⟩ : ∃ M' : ℝ, M ≤ M' ∧ 0 < M' :=
    ⟨max M 1, le_max_left _ _, lt_of_lt_of_le one_pos (le_max_right _ _)⟩
  have h1 : ∀ᶠ x in l, c / 2 < g x * a x :=
    ha.eventually (eventually_gt_nhds (by linarith))
  have h2 : ∀ᶠ x in l, g x < c / (2 * M') :=
    hg0.eventually (eventually_lt_nhds (by positivity))
  filter_upwards [h1, h2, hg] with x hx1 hx2 hxpos
  by_contra hcon
  push Not at hcon
  have hcon' : a x < M' := lt_of_lt_of_le hcon hMM'
  have hx3 : a x * g x < M' * g x := mul_lt_mul_of_pos_right hcon' hxpos
  have hx4 : M' * g x < M' * (c / (2 * M')) := mul_lt_mul_of_pos_left hx2 hM'
  have hx5 : M' * (c / (2 * M')) = c / 2 := by field_simp
  nlinarith [hx1, hx3, hx4, hx5, mul_comm (g x) (a x)]

/-! ## The scale-selection lemma -/

/-- **Scale selection for a monotone regularly varying function.**

Let `f` be nondecreasing and positive on `[X, ∞)`, regularly varying of index
`ρ > 0` at `∞`.  Let `h → 0⁺` along a filter `l`, and let `u, v` be two
level-selecting cutoffs, in the sense that the running level is pinned:

  `h · f (u h) → c₁` and `h · f (v h) → c₂`, with `c₁, c₂ ∈ (0, ∞)`.

Then `u h / v h → (c₁ / c₂)^{1/ρ}`.

In the application `h` is the ghost intensity, `f r = Ê_{β_c, r}|K|`,
`u h = f⁻¹(λ / (A₂ h))` (so `c₁ = λ / A₂`) and `v h = f⁻¹(1/h)` (so `c₂ = 1`);
the conclusion is then `f⁻¹(λ/(A₂ h)) / f⁻¹(1/h) → (λ/A₂)^{1/(aα)}`, which is
the regularly-varying-inverse statement [24, Theorem 1.5.12] in the exact form
consumed at (I.3.7). -/
theorem tendsto_div_of_monotone_regularlyVarying {f : ℝ → ℝ} {ρ c₁ c₂ X : ℝ}
    (hρ : 0 < ρ) (hX : 0 < X) (hrv : RegularlyVaryingAtTop f ρ)
    (hmono : ∀ x y : ℝ, X ≤ x → x ≤ y → f x ≤ f y)
    (hpos : ∀ x : ℝ, X ≤ x → 0 < f x)
    {l : Filter ℝ} {g u v : ℝ → ℝ}
    (hg0 : Tendsto g l (𝓝 0)) (hg : ∀ᶠ h : ℝ in l, 0 < g h)
    (hu : ∀ᶠ h : ℝ in l, X ≤ u h) (hv : ∀ᶠ h : ℝ in l, X ≤ v h)
    (hfu : Tendsto (fun h => g h * f (u h)) l (𝓝 c₁))
    (hfv : Tendsto (fun h => g h * f (v h)) l (𝓝 c₂))
    (hc1 : 0 < c₁) (hc2 : 0 < c₂) :
    Tendsto (fun h => u h / v h) l (𝓝 ((c₁ / c₂) ^ (1 / ρ))) := by
  have hc : 0 < c₁ / c₂ := div_pos hc1 hc2
  have habspos : 0 < (c₁ / c₂) ^ (1 / ρ) := Real.rpow_pos_of_pos hc _
  have hbase : ((c₁ / c₂) ^ (1 / ρ)) ^ ρ = c₁ / c₂ := by
    rw [← Real.rpow_mul hc.le, one_div_mul_cancel hρ.ne', Real.rpow_one]
  -- `f ∘ v → ∞`
  have hfvtop : Tendsto (fun h => f (v h)) l atTop :=
    tendsto_atTop_of_mul_tendsto_zero hc2 hg0 hg (by simpa [mul_comm] using hfv)
  -- hence `v → ∞`
  have hvtop : Tendsto v l atTop := by
    rw [tendsto_atTop]
    intro Y
    rcases le_or_gt Y X with hY | hY
    · filter_upwards [hv] with h hh using le_trans hY hh
    · filter_upwards [hfvtop.eventually (eventually_gt_atTop (f Y)), hv] with h hh hvh
      by_contra hcon
      push Not at hcon
      exact absurd hh (not_lt.2 (hmono _ _ hvh hcon.le))
  -- the two `f`-values are comparable, with ratio `c₁/c₂`
  have hratio : Tendsto (fun h => f (u h) / f (v h)) l (𝓝 (c₁ / c₂)) := by
    have h := hfu.div hfv hc2.ne'
    refine h.congr' ?_
    filter_upwards [hg] with h hh
    exact mul_div_mul_left _ _ hh.ne'
  refine tendsto_order.2 ⟨?_, ?_⟩
  · -- lower bounds
    intro b hb
    rcases le_or_gt b 0 with hb0 | hb0
    · filter_upwards [hu, hv] with h huu hvv
      have hupos : 0 < u h := lt_of_lt_of_le hX huu
      have hvpos : 0 < v h := lt_of_lt_of_le hX hvv
      have hpos' : 0 < u h / v h := div_pos hupos hvpos
      linarith
    · obtain ⟨t, hbt, hta⟩ : ∃ t : ℝ, b < t ∧ t < (c₁ / c₂) ^ (1 / ρ) :=
        ⟨(b + (c₁ / c₂) ^ (1 / ρ)) / 2, by linarith, by linarith⟩
      have htpos : 0 < t := lt_trans hb0 hbt
      have htpow : t ^ ρ < c₁ / c₂ := by
        rw [← hbase]
        exact Real.rpow_lt_rpow htpos.le hta hρ
      obtain ⟨e, hte, hec⟩ : ∃ e : ℝ, t ^ ρ < e ∧ e < c₁ / c₂ :=
        ⟨(t ^ ρ + c₁ / c₂) / 2, by linarith, by linarith⟩
      have hev1 : ∀ᶠ h : ℝ in l, e < f (u h) / f (v h) :=
        hratio.eventually (eventually_gt_nhds hec)
      have hev2 : ∀ᶠ h : ℝ in l, f (t * v h) / f (v h) < e := by
        have htend : Tendsto (fun h => f (t * v h) / f (v h)) l (𝓝 (t ^ ρ)) :=
          (hrv.2 t htpos).comp hvtop
        exact htend.eventually (eventually_lt_nhds hte)
      filter_upwards [hev1, hev2, hu, hv,
        hvtop.eventually (eventually_ge_atTop (X / t))] with h h1 h2 huu hvv htv
      have hfvpos : 0 < f (v h) := hpos _ hvv
      have hvpos : 0 < v h := lt_of_lt_of_le hX hvv
      have key : f (t * v h) < f (u h) :=
        (div_lt_div_iff_of_pos_right hfvpos).1 (lt_trans h2 h1)
      have htle : t * v h ≤ u h := by
        by_contra hcon
        push Not at hcon
        exact absurd key (not_lt.2 (hmono _ _ huu (le_of_lt hcon)))
      have hbX : X ≤ t * v h := by
        have htx : t * (X / t) = X := by field_simp
        rw [← htx]
        exact mul_le_mul_of_nonneg_left htv htpos.le
      rw [lt_div_iff₀ hvpos]
      nlinarith [mul_lt_mul_of_pos_right hbt hvpos, htle]
  · -- upper bounds
    intro b hb
    have hbpos : 0 < b := by linarith [habspos]
    have hbpow : c₁ / c₂ < b ^ ρ := by
      rw [← hbase]
      exact Real.rpow_lt_rpow (Real.rpow_nonneg hc.le _) hb hρ
    obtain ⟨e, hce, heb⟩ : ∃ e : ℝ, c₁ / c₂ < e ∧ e < b ^ ρ :=
      ⟨(c₁ / c₂ + b ^ ρ) / 2, by linarith, by linarith⟩
    have hev1 : ∀ᶠ h : ℝ in l, f (u h) / f (v h) < e :=
      hratio.eventually (eventually_lt_nhds hce)
    have hev2 : ∀ᶠ h : ℝ in l, e < f (b * v h) / f (v h) := by
      have htend : Tendsto (fun h => f (b * v h) / f (v h)) l (𝓝 (b ^ ρ)) :=
        (hrv.2 b hbpos).comp hvtop
      exact htend.eventually (eventually_gt_nhds heb)
    filter_upwards [hev1, hev2, hu, hv,
      hvtop.eventually (eventually_ge_atTop (X / b))] with h h1 h2 huu hvv htv
    have hfvpos : 0 < f (v h) := hpos _ hvv
    have hvpos : 0 < v h := lt_of_lt_of_le hX hvv
    have key : f (u h) < f (b * v h) :=
      (div_lt_div_iff_of_pos_right hfvpos).1 (lt_trans h1 h2)
    have hbX : X ≤ b * v h := by
      have hbx : b * (X / b) = X := by field_simp
      rw [← hbx]
      exact mul_le_mul_of_nonneg_left htv hbpos.le
    have hlt : u h < b * v h := by
      by_contra hcon
      push Not at hcon
      exact absurd key (not_lt.2 (hmono _ _ hbX hcon))
    rw [div_lt_iff₀ hvpos]
    linarith

end PercLib.CriticalLRP.Analysis
namespace PercLib.CriticalLRP.Analysis

/-! ## The canonical level selection `f⁻¹` -/

/-- **Every level above `f X` is attained.**  For a continuous `f` on `[X, ∞)`
tending to `∞`, the range covers `[f X, ∞)` (intermediate value theorem). -/
theorem exists_level_point {f : ℝ → ℝ} {X y : ℝ} (hcont : ContinuousOn f (Ici X))
    (htop : Tendsto f atTop atTop) (hy : f X ≤ y) : ∃ x : ℝ, X ≤ x ∧ f x = y := by
  have h := intermediate_value_Ici (a := X) hcont htop hy
  obtain ⟨x, hx⟩ := h
  exact ⟨x, hx.1, hx.2⟩

/-- **The canonical level selection** (`f⁻¹` of the paper): for `y ≥ f X` it is a
point `x ≥ X` with `f x = y`, and it is set to `X` for `y < f X`.  This makes it
a total function which is a genuine inverse above the threshold. -/
noncomputable def levelInverse (f : ℝ → ℝ) (X : ℝ) (hcont : ContinuousOn f (Ici X))
    (htop : Tendsto f atTop atTop) (y : ℝ) : ℝ :=
  if hy : f X ≤ y then (exists_level_point hcont htop hy).choose else X

theorem levelInverse_mem {f : ℝ → ℝ} {X : ℝ} (hcont : ContinuousOn f (Ici X))
    (htop : Tendsto f atTop atTop) (y : ℝ) : X ≤ levelInverse f X hcont htop y := by
  unfold levelInverse
  by_cases hy : f X ≤ y
  · rw [dite_eq_left hy]
    exact (exists_level_point hcont htop hy).choose_spec.1
  · rw [dite_eq_right hy]

theorem f_levelInverse {f : ℝ → ℝ} {X y : ℝ} (hcont : ContinuousOn f (Ici X))
    (htop : Tendsto f atTop atTop) (hy : f X ≤ y) :
    f (levelInverse f X hcont htop y) = y := by
  unfold levelInverse
  rw [dite_eq_left hy]
  exact (exists_level_point hcont htop hy).choose_spec.2

/-- The level selection diverges in the level (for a strictly increasing `f`, so
that the level point is unique and cannot be chosen below `Y`). -/
theorem tendsto_levelInverse_atTop {f : ℝ → ℝ} {X : ℝ}
    (hstrict : ∀ x y : ℝ, X ≤ x → x < y → f x < f y)
    (hcont : ContinuousOn f (Ici X)) (htop : Tendsto f atTop atTop) :
    Tendsto (levelInverse f X hcont htop) atTop atTop := by
  rw [tendsto_atTop]
  intro Y
  rcases le_or_gt Y X with hY | hY
  · filter_upwards with y
    exact le_trans hY (levelInverse_mem hcont htop y)
  · have hXY : f X < f Y := hstrict X Y le_rfl hY
    filter_upwards [eventually_gt_atTop (f Y)] with y hy
    have hy1 : f X ≤ y := le_of_lt (lt_trans hXY hy)
    by_contra hcon
    push Not at hcon
    have h1 := hstrict _ _ (levelInverse_mem hcont htop y) hcon
    rw [f_levelInverse hcont htop hy1] at h1
    linarith

/-- **The inverse of a regularly varying function of positive index is regularly
varying of index `1/ρ`** — the paper's citation [24, Theorem 1.5.12], in the case
where `f` is nondecreasing and continuous so that a genuine level selection
exists.  The statement is a direct consequence of the scale-selection lemma:
with `g = 1/y`, the two levels are `f (f⁻¹(λ y)) = λ y` and `f (f⁻¹ y) = y`, so
the running levels are `λ` and `1`. -/
theorem regularlyVaryingAtTop_levelInverse {f : ℝ → ℝ} {ρ X : ℝ} (hρ : 0 < ρ) (hX : 0 < X)
    (hrv : RegularlyVaryingAtTop f ρ)
    (hmono : ∀ x y : ℝ, X ≤ x → x ≤ y → f x ≤ f y)
    (hpos : ∀ x : ℝ, X ≤ x → 0 < f x)
    (hcont : ContinuousOn f (Ici X)) (htop : Tendsto f atTop atTop) :
    RegularlyVaryingAtTop (levelInverse f X hcont htop) (1 / ρ) := by
  refine ⟨Eventually.of_forall fun y => ?_, fun lam hlam => ?_⟩
  · exact ne_of_gt (lt_of_lt_of_le hX (levelInverse_mem hcont htop y))
  · have hlev : ∀ᶠ y : ℝ in atTop, f X ≤ lam * y := by
      filter_upwards [eventually_ge_atTop (f X / lam)] with y hy
      rw [div_le_iff₀ hlam] at hy
      linarith
    have hpos_y : ∀ᶠ y : ℝ in atTop, (0 : ℝ) < y := eventually_gt_atTop 0
    have hfu : Tendsto (fun y : ℝ => y⁻¹ * f (levelInverse f X hcont htop (lam * y)))
        atTop (𝓝 lam) := by
      refine Tendsto.congr' ?_ tendsto_const_nhds
      filter_upwards [hlev, hpos_y] with y hy hypos
      rw [f_levelInverse hcont htop hy]
      field_simp
    have hfv : Tendsto (fun y : ℝ => y⁻¹ * f (levelInverse f X hcont htop y))
        atTop (𝓝 1) := by
      refine Tendsto.congr' ?_ tendsto_const_nhds
      filter_upwards [eventually_ge_atTop (f X), hpos_y] with y hy hypos
      rw [f_levelInverse hcont htop hy]
      field_simp
    have hmain := tendsto_div_of_monotone_regularlyVarying (f := f) (ρ := ρ)
      (c₁ := lam) (c₂ := 1) (X := X) hρ hX hrv hmono hpos
      (l := atTop) (g := fun y => y⁻¹)
      (u := fun y => levelInverse f X hcont htop (lam * y))
      (v := levelInverse f X hcont htop)
      tendsto_inv_atTop_zero
      (by filter_upwards [hpos_y] with y hy using inv_pos.2 hy)
      (Eventually.of_forall fun y => levelInverse_mem hcont htop (lam * y))
      (Eventually.of_forall fun y => levelInverse_mem hcont htop y)
      hfu hfv hlam one_pos
    simpa using hmain

end PercLib.CriticalLRP.Analysis
namespace PercLib.CriticalLRP.Analysis

/-! ## The paper's cutoff choice `r = f⁻¹(λ / (A₂ h))`

This is the step at the top of p. 31 of the paper: "We will apply this estimate
with `r = f⁻¹(λ/A₂ h)`, where we think of `λ` being fixed and take `h ↓ 0`."

The two consequences used are

* the level is filled: `h · (A₂ · f (r h)) = λ` exactly, so `Ê_{r(h)}|K| ∼ λ/h`;
* the scaling law `(r h)^α / (τ h)^α → λ^{1/a}/A₂^{1/a}`, with `τ h = f⁻¹(1/h)`,
  which is the regularly-varying-inverse step (`f⁻¹` is regularly varying of
  index `1/(aα)`) referred to in the paper as [24, Theorem 1.5.12]. -/

/-- **The chosen cutoff fills the level exactly**: `h · (A₂ · f (f⁻¹(λ/(A₂h)))) = λ`. -/
theorem paper_level_eq {f : ℝ → ℝ} {X A₂ lam h : ℝ} (hcont : ContinuousOn f (Ici X))
    (htop : Tendsto f atTop atTop) (hA₂ : A₂ ≠ 0) (hh : h ≠ 0)
    (hy : f X ≤ lam / (A₂ * h)) :
    h * (A₂ * f (levelInverse f X hcont htop (lam / (A₂ * h)))) = lam := by
  rw [f_levelInverse hcont htop hy]
  field_simp

/-- Eventually the level `λ/(A₂ h)` is above the threshold `f X` when `h ↓ 0⁺`. -/
theorem eventually_level_ge {f : ℝ → ℝ} {X A₂ lam : ℝ}
    (hpos : ∀ x : ℝ, X ≤ x → 0 < f x) (hA₂ : 0 < A₂) (hlam : 0 < lam) :
    ∀ᶠ h : ℝ in 𝓝[>] (0 : ℝ), f X ≤ lam / (A₂ * h) := by
  have hfX : 0 < f X := hpos X le_rfl
  have hc : 0 < lam / (A₂ * f X) := div_pos hlam (mul_pos hA₂ hfX)
  have hsmall : ∀ᶠ h : ℝ in 𝓝[>] (0 : ℝ), h ≤ lam / (A₂ * f X) :=
    (tendsto_id.mono_left (nhdsWithin_le_nhds (s := Ioi 0))).eventually (eventually_le_nhds hc)
  filter_upwards [hsmall, self_mem_nhdsWithin] with h hh hhpos
  have hh0 : (0 : ℝ) < h := hhpos
  have h1 : h * (A₂ * f X) ≤ lam := (le_div_iff₀ (mul_pos hA₂ hfX)).1 hh
  refine (le_div_iff₀ (mul_pos hA₂ hh0)).2 ?_
  nlinarith [h1]

/-- **The scaling law for arbitrary level selections** — the inverse-free form of
the regularly-varying-inverse step of I.3.2.

Let `f` be nondecreasing, positive and regularly varying of index `ρ = a·α > 0`
on `[X, ∞)`.  Suppose `σ₁ h` and `σ₂ h` are points at which `f` reaches the
running levels `(λ/A₂)/h` and `1/h` respectively:

  `f (σ₁ h) = λ/(A₂ h)` and `f (σ₂ h) = 1/h` for all small `h > 0`.

Then `(σ₁ h)^α / (σ₂ h)^α → λ^{1/a}/A₂^{1/a}`.

No inverse of `f` is required: the paper's `r h = f⁻¹(λ/(A₂ h))` and
`f⁻¹(1/h)` are precisely two such level selections (for `f⁻¹` a genuine inverse
they satisfy the hypotheses with equality), and the conclusion says that the
choice of level selection is asymptotically irrelevant.  This is the form in
which the step feeds `(I.3.7)`: it converts the factor
`A₁ (r h)^α h / λ` into `A₁ (λ/A₂)^{1/a} λ^{-1} · (f⁻¹(1/h))^α h`. -/
theorem paper_level_selection_rpow {f : ℝ → ℝ} {ρ a α A₂ X lam : ℝ}
    (hρ : 0 < ρ) (hρα : ρ = a * α) (ha : 0 < a) (hα : 0 < α)
    (hX : 0 < X) (hA₂ : 0 < A₂) (hlam : 0 < lam)
    (hrv : RegularlyVaryingAtTop f ρ)
    (hmono : ∀ x y : ℝ, X ≤ x → x ≤ y → f x ≤ f y)
    (hpos : ∀ x : ℝ, X ≤ x → 0 < f x)
    {σ₁ σ₂ : ℝ → ℝ}
    (hσ1 : ∀ᶠ h : ℝ in 𝓝[>] (0 : ℝ), f (σ₁ h) = lam / (A₂ * h))
    (hσ2 : ∀ᶠ h : ℝ in 𝓝[>] (0 : ℝ), f (σ₂ h) = 1 / h)
    (hX1 : ∀ᶠ h : ℝ in 𝓝[>] (0 : ℝ), X ≤ σ₁ h)
    (hX2 : ∀ᶠ h : ℝ in 𝓝[>] (0 : ℝ), X ≤ σ₂ h) :
    Tendsto (fun h : ℝ => (σ₁ h) ^ α / (σ₂ h) ^ α)
      (𝓝[>] (0 : ℝ)) (𝓝 (lam ^ (1 / a) / A₂ ^ (1 / a))) := by
  have hqe : 0 < lam / A₂ := div_pos hlam hA₂
  have hexp2 : (1 / ρ) * α = 1 / a := by
    rw [hρα]; field_simp
  have hexp : ((lam / A₂) ^ (1 / ρ)) ^ α = lam ^ (1 / a) / A₂ ^ (1 / a) := by
    calc ((lam / A₂) ^ (1 / ρ)) ^ α = (lam / A₂) ^ ((1 / ρ) * α) :=
          (Real.rpow_mul hqe.le _ _).symm
      _ = (lam / A₂) ^ (1 / a) := by rw [hexp2]
      _ = lam ^ (1 / a) / A₂ ^ (1 / a) := Real.div_rpow hlam.le hA₂.le _
  -- the two running levels
  have hfv1 : Tendsto (fun h : ℝ => h * f (σ₁ h)) (𝓝[>] (0 : ℝ)) (𝓝 (lam / A₂)) := by
    refine Tendsto.congr' ?_ tendsto_const_nhds
    filter_upwards [self_mem_nhdsWithin, hσ1] with h hh hlev
    rw [hlev]
    field_simp
    rw [div_self (ne_of_gt hh)]
  have hfv2 : Tendsto (fun h : ℝ => h * f (σ₂ h)) (𝓝[>] (0 : ℝ)) (𝓝 1) := by
    refine Tendsto.congr' ?_ tendsto_const_nhds
    filter_upwards [self_mem_nhdsWithin, hσ2] with h hh hlev
    rw [hlev]
    field_simp
    rw [div_self (ne_of_gt hh)]
  -- the scale-selection lemma
  have hbase := tendsto_div_of_monotone_regularlyVarying (f := f) (ρ := ρ)
    (c₁ := lam / A₂) (c₂ := 1) (X := X) hρ hX hrv hmono hpos
    (l := 𝓝[>] (0 : ℝ)) (g := fun h : ℝ => h)
    (u := σ₁) (v := σ₂)
    (tendsto_id.mono_left (nhdsWithin_le_nhds (s := Ioi 0)))
    self_mem_nhdsWithin hX1 hX2 hfv1 hfv2 hqe one_pos
  have hbase' : Tendsto (fun h : ℝ => σ₁ h / σ₂ h) (𝓝[>] (0 : ℝ))
      (𝓝 ((lam / A₂) ^ (1 / ρ))) := by
    simpa using hbase
  -- raise to the power `α`
  have hcontpow : Tendsto (fun t : ℝ => t ^ α) (𝓝 ((lam / A₂) ^ (1 / ρ)))
      (𝓝 (((lam / A₂) ^ (1 / ρ)) ^ α)) :=
    (Real.continuousAt_rpow_const ((lam / A₂) ^ (1 / ρ)) α
      (Or.inl (Real.rpow_pos_of_pos hqe _).ne')).tendsto
  have hp := hcontpow.comp hbase'
  rw [hexp] at hp
  refine hp.congr' ?_
  filter_upwards [hX1, hX2] with h h1 h2
  exact Real.div_rpow (le_trans hX.le h1) (le_trans hX.le h2) α

/-- **The regularly-varying-inverse scaling law at the paper's cutoff.**
With `f` regularly varying of index `ρ = a·α`, `r h = f⁻¹(λ/(A₂ h))` and
`τ h = f⁻¹(1/h)`:

  `(r h)^α / (τ h)^α → λ^{1/a} / A₂^{1/a}`  as `h ↓ 0`.

This is `paper_level_selection_rpow` with the level selection `levelInverse` of
`f`, which satisfies the level equations by `f_levelInverse`. -/
theorem paper_level_ratio_rpow {f : ℝ → ℝ} {ρ a α A₂ X lam : ℝ}
    (hρ : 0 < ρ) (hρα : ρ = a * α) (ha : 0 < a) (hα : 0 < α)
    (hX : 0 < X) (hA₂ : 0 < A₂) (hlam : 0 < lam)
    (hrv : RegularlyVaryingAtTop f ρ)
    (hmono : ∀ x y : ℝ, X ≤ x → x ≤ y → f x ≤ f y)
    (hpos : ∀ x : ℝ, X ≤ x → 0 < f x)
    (hcont : ContinuousOn f (Ici X)) (htop : Tendsto f atTop atTop) :
    Tendsto (fun h : ℝ => (levelInverse f X hcont htop (lam / (A₂ * h))) ^ α /
        (levelInverse f X hcont htop (1 / h)) ^ α)
      (𝓝[>] (0 : ℝ)) (𝓝 (lam ^ (1 / a) / A₂ ^ (1 / a))) := by
  have hlev1 : ∀ᶠ h : ℝ in 𝓝[>] (0 : ℝ), f X ≤ lam / (A₂ * h) :=
    eventually_level_ge (f := f) (X := X) (A₂ := A₂) (lam := lam) hpos hA₂ hlam
  have hlev2 : ∀ᶠ h : ℝ in 𝓝[>] (0 : ℝ), f X ≤ 1 / h := by
    have hfX : 0 < f X := hpos X le_rfl
    have hc : 0 < 1 / f X := by positivity
    have hsmall : ∀ᶠ h : ℝ in 𝓝[>] (0 : ℝ), h ≤ 1 / f X :=
      (tendsto_id.mono_left (nhdsWithin_le_nhds (s := Ioi 0))).eventually (eventually_le_nhds hc)
    filter_upwards [hsmall, self_mem_nhdsWithin] with h hh hhpos
    have hh0 : (0 : ℝ) < h := hhpos
    rw [le_div_iff₀ hh0, le_div_iff₀ hfX] at *
    linarith
  refine paper_level_selection_rpow (f := f) (ρ := ρ) (a := a) (α := α) (A₂ := A₂)
    (X := X) (lam := lam) hρ hρα ha hα hX hA₂ hlam hrv hmono hpos
    (σ₁ := fun h => levelInverse f X hcont htop (lam / (A₂ * h)))
    (σ₂ := fun h => levelInverse f X hcont htop (1 / h))
    ?_ ?_ ?_ ?_
  · filter_upwards [hlev1] with h hh
    exact f_levelInverse hcont htop hh
  · filter_upwards [hlev2] with h hh
    exact f_levelInverse hcont htop hh
  · exact Eventually.of_forall fun h => levelInverse_mem hcont htop _
  · exact Eventually.of_forall fun h => levelInverse_mem hcont htop _

end PercLib.CriticalLRP.Analysis
namespace PercLib.CriticalLRP.Analysis

/-- **(I.3.7) in the exact shape consumed by the assembly** (inverse-free form).

With `σ₁ h, σ₂ h` two level selections for `f` at the running levels
`λ/(A₂ h)` and `1/h`, the factor `A₁ (σ₁ h)^α h / λ` which multiplies the
`Q_∞`-integral in the proof of I.3.2 satisfies

  `(A₁ (σ₁ h)^α h / λ) / ((σ₂ h)^α h) → A₁ · (λ/A₂)^{1/a} / λ`,

i.e. `A₁ (σ₁ h)^α h/λ ≈ (A₁/λ)(λ/A₂)^{1/a} · (f⁻¹(1/h))^α h`, which is the
displayed formula (I.3.7).  The remaining factor
`∫₀^∞ (1-e^{-λx})/x dQ_∞(x)` is not touched here. -/
theorem paper_level_selection_normalized {f : ℝ → ℝ} {ρ a α A₁ A₂ X lam : ℝ}
    (hρ : 0 < ρ) (hρα : ρ = a * α) (ha : 0 < a) (hα : 0 < α)
    (hX : 0 < X) (hA₂ : 0 < A₂) (hlam : 0 < lam)
    (hrv : RegularlyVaryingAtTop f ρ)
    (hmono : ∀ x y : ℝ, X ≤ x → x ≤ y → f x ≤ f y)
    (hpos : ∀ x : ℝ, X ≤ x → 0 < f x)
    {σ₁ σ₂ : ℝ → ℝ}
    (hσ1 : ∀ᶠ h : ℝ in 𝓝[>] (0 : ℝ), f (σ₁ h) = lam / (A₂ * h))
    (hσ2 : ∀ᶠ h : ℝ in 𝓝[>] (0 : ℝ), f (σ₂ h) = 1 / h)
    (hX1 : ∀ᶠ h : ℝ in 𝓝[>] (0 : ℝ), X ≤ σ₁ h)
    (hX2 : ∀ᶠ h : ℝ in 𝓝[>] (0 : ℝ), X ≤ σ₂ h) :
    Tendsto (fun h : ℝ => (A₁ * (σ₁ h) ^ α * h / lam) / ((σ₂ h) ^ α * h))
      (𝓝[>] (0 : ℝ)) (𝓝 (A₁ / lam * (lam ^ (1 / a) / A₂ ^ (1 / a)))) := by
  have hratio := paper_level_selection_rpow (f := f) (ρ := ρ) (a := a) (α := α)
    (A₂ := A₂) (X := X) (lam := lam) hρ hρα ha hα hX hA₂ hlam hrv hmono hpos
    hσ1 hσ2 hX1 hX2
  have hmul : Tendsto (fun _ : ℝ => A₁ / lam) (𝓝[>] (0 : ℝ)) (𝓝 (A₁ / lam)) :=
    tendsto_const_nhds
  have h2 := hmul.mul hratio
  refine h2.congr' ?_
  filter_upwards [self_mem_nhdsWithin, hX1, hX2] with h hh h1 h2'
  have hh0 : (0 : ℝ) < h := hh
  have h1' : 0 < σ₁ h := lt_of_lt_of_le hX h1
  have h2'' : 0 < σ₂ h := lt_of_lt_of_le hX h2'
  have hpow : (0 : ℝ) < (σ₂ h) ^ α := Real.rpow_pos_of_pos h2'' α
  field_simp

/-- **(I.3.7) at the paper's cutoff** `r h = f⁻¹(λ/(A₂ h))`, `τ h = f⁻¹(1/h)`:
the specialization of `paper_level_selection_normalized` to the level selection
`levelInverse`. -/
theorem paper_normalized {f : ℝ → ℝ} {ρ a α A₁ A₂ X lam : ℝ}
    (hρ : 0 < ρ) (hρα : ρ = a * α) (ha : 0 < a) (hα : 0 < α)
    (hX : 0 < X) (hA₂ : 0 < A₂) (hlam : 0 < lam)
    (hrv : RegularlyVaryingAtTop f ρ)
    (hmono : ∀ x y : ℝ, X ≤ x → x ≤ y → f x ≤ f y)
    (hpos : ∀ x : ℝ, X ≤ x → 0 < f x)
    (hcont : ContinuousOn f (Ici X)) (htop : Tendsto f atTop atTop) :
    Tendsto (fun h : ℝ =>
        (A₁ * (levelInverse f X hcont htop (lam / (A₂ * h))) ^ α * h / lam) /
          ((levelInverse f X hcont htop (1 / h)) ^ α * h))
      (𝓝[>] (0 : ℝ)) (𝓝 (A₁ / lam * (lam ^ (1 / a) / A₂ ^ (1 / a)))) := by
  have hlev1 : ∀ᶠ h : ℝ in 𝓝[>] (0 : ℝ), f X ≤ lam / (A₂ * h) :=
    eventually_level_ge (f := f) (X := X) (A₂ := A₂) (lam := lam) hpos hA₂ hlam
  have hlev2 : ∀ᶠ h : ℝ in 𝓝[>] (0 : ℝ), f X ≤ 1 / h := by
    have hfX : 0 < f X := hpos X le_rfl
    have hc : 0 < 1 / f X := by positivity
    have hsmall : ∀ᶠ h : ℝ in 𝓝[>] (0 : ℝ), h ≤ 1 / f X :=
      (tendsto_id.mono_left (nhdsWithin_le_nhds (s := Ioi 0))).eventually (eventually_le_nhds hc)
    filter_upwards [hsmall, self_mem_nhdsWithin] with h hh hhpos
    have hh0 : (0 : ℝ) < h := hhpos
    rw [le_div_iff₀ hh0, le_div_iff₀ hfX] at *
    linarith
  refine paper_level_selection_normalized (f := f) (ρ := ρ) (a := a) (α := α) (A₁ := A₁)
    (A₂ := A₂) (X := X) (lam := lam) hρ hρα ha hα hX hA₂ hlam hrv hmono hpos
    (σ₁ := fun h => levelInverse f X hcont htop (lam / (A₂ * h)))
    (σ₂ := fun h => levelInverse f X hcont htop (1 / h)) ?_ ?_ ?_ ?_
  · filter_upwards [hlev1] with h hh
    exact f_levelInverse hcont htop hh
  · filter_upwards [hlev2] with h hh
    exact f_levelInverse hcont htop hh
  · exact Eventually.of_forall fun h => levelInverse_mem hcont htop _
  · exact Eventually.of_forall fun h => levelInverse_mem hcont htop _

/-- The constant of (I.3.7) in the paper's displayed form:
`(A₁/λ)(λ/A₂)^{1/a} = A₁ / (A₂^{1/a} λ^{1-1/a})`. -/
theorem paper_constant_eq {A₁ A₂ lam a : ℝ} (hA₁ : A₁ ≠ 0) (hA₂ : 0 < A₂) (hlam : 0 < lam)
    (ha : a ≠ 0) :
    A₁ / lam * (lam ^ (1 / a) / A₂ ^ (1 / a)) = A₁ / (A₂ ^ (1 / a) * lam ^ (1 - 1 / a)) := by
  have hA2p : (0 : ℝ) < A₂ ^ (1 / a) := Real.rpow_pos_of_pos hA₂ _
  have hlp : (0 : ℝ) < lam ^ (1 - 1 / a) := Real.rpow_pos_of_pos hlam _
  have hkey : lam ^ (1 / a) * lam ^ (1 - 1 / a) = lam := by
    rw [← Real.rpow_add hlam, show (1 : ℝ) / a + (1 - 1 / a) = 1 by ring, Real.rpow_one]
  field_simp
  rw [show (a - 1) / a = 1 - 1 / a by field_simp]
  linarith [hkey]

/-- **The constant produced by the scaling law is the factor inside the
definition of `A₃`**: `(A₁/λ)(λ/A₂)^{1/a} = (A₁/A₂^{1/a}) λ^{-(a-1)/a}`.
This is the identity by which (I.3.7) turns into the `A₃` of Proposition I.3.2
once the `Q_∞`-integral is included. -/
theorem paper_A3_shape {A₁ A₂ lam a : ℝ} (hA₂ : 0 < A₂) (hlam : 0 < lam) (ha : 0 < a) :
    A₁ / lam * (lam ^ (1 / a) / A₂ ^ (1 / a)) = A₁ / A₂ ^ (1 / a) * lam ^ (-((a - 1) / a)) := by
  have hA2p : (0 : ℝ) < A₂ ^ (1 / a) := Real.rpow_pos_of_pos hA₂ _
  have hexp : -((a - 1) / a) = 1 / a - 1 := by
    field_simp
    ring
  have hA2p : (0 : ℝ) < A₂ ^ (1 / a) := Real.rpow_pos_of_pos hA₂ _
  rw [hexp, Real.rpow_sub hlam, Real.rpow_one]
  field_simp

/-! ## Non-vacuity

The hypotheses of the scaling law are satisfiable: `x ↦ x ^ ρ` on `[1, ∞)` is
regularly varying of index `ρ`, strictly increasing, positive and continuous, and
tends to `∞`.  We instantiate the scaling law at `ρ = a = 2`, `α = 1`, `A₂ = 1`,
`λ = 4`, `f x = x²`, where the limit constant is `λ^{1/a}/A₂^{1/a} = 2 ≠ 1`. -/

/-- Continuity of `x ↦ x²` on `[1, ∞)`, as a reusable hypothesis witness. -/
theorem demoCont : ContinuousOn (fun x : ℝ => x ^ (2 : ℝ)) (Ici 1) :=
  ContinuousOn.rpow_const continuousOn_id (fun x _ => Or.inr (by norm_num))

/-- Divergence of `x ↦ x²` at `∞`, obtained from the general theorem. -/
theorem demoTop : Tendsto (fun x : ℝ => x ^ (2 : ℝ)) atTop atTop :=
  tendsto_atTop_of_monotone_regularlyVarying (ρ := 2) (X := 1) two_pos one_pos
    (regularlyVaryingAtTop_rpow 2)
    (fun x y hx hxy => Real.rpow_le_rpow (by linarith) hxy (by norm_num))
    (fun x hx => Real.rpow_pos_of_pos (by linarith) 2)

/-- **Non-vacuity check**: the scaling law of `paper_level_ratio_rpow` at
`f x = x²` (`ρ = a = 2`, `α = 1`), `A₂ = 1`, `λ = 4`, `X = 1`. -/
theorem paper_nonvacuous :
    Tendsto (fun h : ℝ =>
        (levelInverse (fun x : ℝ => x ^ (2 : ℝ)) 1 demoCont demoTop (4 / (1 * h))) ^ (1 : ℝ) /
          (levelInverse (fun x : ℝ => x ^ (2 : ℝ)) 1 demoCont demoTop (1 / h)) ^ (1 : ℝ))
      (𝓝[>] (0 : ℝ)) (𝓝 ((4 : ℝ) ^ ((1 : ℝ) / 2) / (1 : ℝ) ^ ((1 : ℝ) / 2))) :=
  paper_level_ratio_rpow (f := fun x : ℝ => x ^ (2 : ℝ)) (ρ := 2) (a := 2) (α := 1)
    (A₂ := 1) (X := 1) (lam := 4) two_pos (by norm_num) two_pos one_pos one_pos
    one_pos (by norm_num) (regularlyVaryingAtTop_rpow 2)
    (fun x y hx hxy => Real.rpow_le_rpow (by linarith) hxy (by norm_num))
    (fun x hx => Real.rpow_pos_of_pos (by linarith) 2) demoCont demoTop

/-- The limit constant in `paper_nonvacuous` is `2`, so the conclusion is not a
degenerate `1 = 1` statement. -/
theorem paper_nonvacuous_constant : (4 : ℝ) ^ ((1 : ℝ) / 2) / (1 : ℝ) ^ ((1 : ℝ) / 2) = 2 := by
  norm_num [← Real.sqrt_eq_rpow]

end PercLib.CriticalLRP.Analysis

namespace PercLib.CriticalLRP.Analysis

/-! ## Potter's bounds in symmetric form -/

/-- **Potter's bounds for an arbitrary ordered pair**, in symmetric form.  For
`x, y ≥ X` (no order restriction) and `0 < ε < 1`,

  `(1-ε) · min ((x/y)^{ρ-ε}, (x/y)^{ρ+ε}) · |f y| ≤ |f x|`

and

  `|f x| ≤ (1+2ε) · max ((x/y)^{ρ-ε}, (x/y)^{ρ+ε}) · |f y|`.

The bound is stated with the *same* constants for both orders, which is what the
squeeze in `tendsto_div_of_potter` consumes. -/
theorem potter_compare {f : ℝ → ℝ} {ρ ε X : ℝ} (hε : 0 < ε) (hε1 : ε ≤ 1 / 2)
    (hXge1 : 1 ≤ X)
    (hX : ∀ x y : ℝ, X ≤ y → y ≤ x →
      (1 - ε) * (x / y) ^ (ρ - ε) * |f y| ≤ |f x| ∧
        |f x| ≤ (1 + ε) * (x / y) ^ (ρ + ε) * |f y|)
    {x y : ℝ} (hx : X ≤ x) (hy : X ≤ y) :
    (1 - ε) * min ((x / y) ^ (ρ - ε)) ((x / y) ^ (ρ + ε)) * |f y| ≤ |f x| ∧
      |f x| ≤ (1 + 2 * ε) * max ((x / y) ^ (ρ - ε)) ((x / y) ^ (ρ + ε)) * |f y| := by
  have hX1 : 0 < X := lt_of_lt_of_le one_pos hXge1
  have hxpos : 0 < x := lt_of_lt_of_le hX1 hx
  have hypos : 0 < y := lt_of_lt_of_le hX1 hy
  have hxy : 0 < x / y := div_pos hxpos hypos
  have hyx : y / x = (x / y)⁻¹ := by rw [inv_div]
  rcases le_or_gt y x with hle | hlt
  · -- case `y ≤ x`: the ordered Potter bound applies directly
    obtain ⟨hlo, hhi⟩ := hX x y hy hle
    have ht1 : (1 : ℝ) ≤ x / y := (one_le_div hypos).2 hle
    have hle1 : (x / y) ^ (ρ - ε) ≤ (x / y) ^ (ρ + ε) :=
      Real.rpow_le_rpow_of_exponent_le ht1 (by linarith)
    have hmin : min ((x / y) ^ (ρ - ε)) ((x / y) ^ (ρ + ε)) = (x / y) ^ (ρ - ε) :=
      min_eq_left hle1
    have hmax : max ((x / y) ^ (ρ - ε)) ((x / y) ^ (ρ + ε)) = (x / y) ^ (ρ + ε) :=
      max_eq_right hle1
    constructor
    · rw [hmin]; exact hlo
    · rw [hmax]
      have h1 : (1 + ε) * (x / y) ^ (ρ + ε) * |f y|
          ≤ (1 + 2 * ε) * (x / y) ^ (ρ + ε) * |f y| := by
        have h0 : (0 : ℝ) ≤ (x / y) ^ (ρ + ε) * |f y| := by positivity
        nlinarith [h0]
      linarith [hhi, h1]
  · -- case `x < y`: apply the ordered bound to `(y, x)` and invert
    obtain ⟨hlo, hhi⟩ := hX y x hx hlt.le
    have hxy1 : x / y < 1 := by
      rw [div_lt_one hypos]; exact hlt
    have hle1 : (x / y) ^ (ρ + ε) ≤ (x / y) ^ (ρ - ε) :=
      Real.rpow_le_rpow_of_exponent_ge hxy hxy1.le (by linarith)
    have hmin : min ((x / y) ^ (ρ - ε)) ((x / y) ^ (ρ + ε)) = (x / y) ^ (ρ + ε) :=
      min_eq_right hle1
    have hmax : max ((x / y) ^ (ρ - ε)) ((x / y) ^ (ρ + ε)) = (x / y) ^ (ρ - ε) :=
      max_eq_left hle1
    have hpx : ∀ q : ℝ, (0 : ℝ) < (x / y) ^ q := fun q => Real.rpow_pos_of_pos hxy q
    constructor
    · -- lower bound, from `|f y| ≤ (1+ε) (y/x)^{ρ+ε} |f x|`
      rw [hmin]
      have hmul := mul_le_mul_of_nonneg_left hhi (le_of_lt (hpx (ρ + ε)))
      rw [hyx, Real.inv_rpow hxy.le] at hmul
      have heq : (x / y) ^ (ρ + ε) * ((1 + ε) * ((x / y) ^ (ρ + ε))⁻¹ * |f x|)
          = (1 + ε) * |f x| := by
        field_simp
      rw [heq] at hmul
      have hc : (1 - ε) ≤ 1 / (1 + ε) := by
        rw [le_div_iff₀ (by linarith : (0:ℝ) < 1 + ε)]
        nlinarith
      have hbound : (1 - ε) * (x / y) ^ (ρ + ε) * |f y|
          ≤ (1 / (1 + ε)) * ((1 + ε) * |f x|) := by
        have h0 : (0 : ℝ) ≤ (x / y) ^ (ρ + ε) * |f y| := by positivity
        have hstep : (1 - ε) * ((x / y) ^ (ρ + ε) * |f y|)
            ≤ (1 / (1 + ε)) * ((x / y) ^ (ρ + ε) * |f y|) :=
          mul_le_mul_of_nonneg_right hc h0
        have hmono : (1 / (1 + ε)) * ((x / y) ^ (ρ + ε) * |f y|)
            ≤ (1 / (1 + ε)) * ((1 + ε) * |f x|) :=
          mul_le_mul_of_nonneg_left hmul (by positivity)
        linarith [hstep, hmono]
      have hsimp : (1 / (1 + ε)) * ((1 + ε) * |f x|) = |f x| := by field_simp
      linarith [hbound, hmul, hsimp]
    · -- upper bound, from `(1-ε) (y/x)^{ρ-ε} |f x| ≤ |f y|`
      rw [hmax]
      have hmul := mul_le_mul_of_nonneg_left hlo (le_of_lt (hpx (ρ - ε)))
      rw [hyx, Real.inv_rpow hxy.le] at hmul
      have heq : (x / y) ^ (ρ - ε) * ((1 - ε) * ((x / y) ^ (ρ - ε))⁻¹ * |f x|)
          = (1 - ε) * |f x| := by
        field_simp
      rw [heq] at hmul
      have hB : (0 : ℝ) ≤ (x / y) ^ (ρ - ε) * |f y| := by positivity
      have hpos : (0 : ℝ) < 1 - ε := by linarith
      have h1 : |f x| ≤ ((x / y) ^ (ρ - ε) * |f y|) / (1 - ε) := by
        rw [le_div_iff₀ hpos]
        linarith [hmul]
      have h2 : ((x / y) ^ (ρ - ε) * |f y|) / (1 - ε)
          ≤ (1 + 2 * ε) * (x / y) ^ (ρ - ε) * |f y| := by
        rw [div_le_iff₀ hpos]
        have hcoef : (1 : ℝ) ≤ (1 + 2 * ε) * (1 - ε) := by nlinarith
        calc (x / y) ^ (ρ - ε) * |f y|
            = (1 : ℝ) * ((x / y) ^ (ρ - ε) * |f y|) := by ring
          _ ≤ ((1 + 2 * ε) * (1 - ε)) * ((x / y) ^ (ρ - ε) * |f y|) :=
              mul_le_mul_of_nonneg_right hcoef hB
          _ = ((1 + 2 * ε) * (x / y) ^ (ρ - ε) * |f y|) * (1 - ε) := by ring
      linarith [h1, h2]

end PercLib.CriticalLRP.Analysis
