/-
Integrated and independently rebuilt from accepted Ultramath `smwywszgo`, member `m8`.

Copyright (c) 2026 PercLib contributors. Released under Apache 2.0.

Swarm `smwywszgo`, member `m8`, direction `d3`.

# Corner elimination for the `p = 2` radius picture, at the level of *almost-everywhere*
  statements on off-corner windows

`Analysis/SecondMomentTail.lean` derives, for an **off-corner** window `[a,b]`
(`M.IsOffCornerWindow a b`: `0 < a`, `a ≤ b`, and no radius of `[a,b]` attained by the norm),

* `AbsolutelyContinuousOnInterval (fun r => M.cutMomentReal 2 r) a b`,
* `∀ᵐ r ∈ Ioo a b, HasDerivAt (fun r => M.cutMomentReal 2 r) (M.rhsScalarTwo r) r`,
* and the integrated identity `∫ t in a..x, M.rhsScalarTwo t = M.cutMomentReal 2 x - M.cutMomentReal 2 a`

from flux-side convergence only.  §9 of that file lists the two pure real-analysis bridges that
were open at that point; the second of them is

> Almost every radius of `(r₀,∞)` is off-corner, and each off-corner radius lies in an off-corner
> window.  Covering `(r₀,∞) \ M.cornerRadii` by countably many off-corner windows with rational
> endpoints and taking a countable union of the a.e. statements gives the consumer's `hae`.

This file proves exactly that bridge, and nothing about absolute continuity: no AC statement, no
integrated identity and no derivative at an attained radius is claimed.  The corner set is finite
on every compact window (`finite_cornerRadii_inter_Ioo`), hence Lebesgue-null
(`volume_cornerRadii`), and every off-corner radius is surrounded by an open ball of off-corner
radii (`exists_nhds_notMem_attainedRadii`); those are the only geometric inputs.

Contents:

* `ae_hasDerivAt_of_offCorner_window_ae_Ioo` — the generic countable-union lemma: if a formula
  `HasDerivAt f (g x) x` holds a.e. on *every* rational-ended subwindow of `(r₀,b)` that avoids a
  closed exceptional set `C`, then it holds a.e. on `(r₀,b)` minus `C`;
* `ae_hasDerivAt_of_offCorner_window_ae_Ioo_of_measure_zero` — the same with `C` dropped from the
  conclusion when `volume C = 0`;
* `exists_neighbourhood_notMem_cornerRadii` — off-corner radii have off-corner neighbourhoods;
* `measurable_rhsScalarTwo_of_windowFlux_tendsto`,
  `intervalIntegrable_rhsScalarTwo_of_windowFlux_tendsto` — `M.rhsScalarTwo` is measurable and
  interval integrable on **every** window `[a,b]` with `a ≤ b`, without any off-corner hypothesis
  (the corner exception is irrelevant to `L¹`-data);
* `ae_hasDerivAt_cutMomentReal_two_Ioo` — **corner elimination for `hae`**: on any window
  `(r₀,b)` of the positive tail the moment has derivative `M.rhsScalarTwo` a.e., from the landed
  a.e. statement on off-corner windows only;
* `deriv_ae_eq_rhsScalarTwo_Ioo` — the same as an a.e. equality of `deriv`;
* `ae_hasDerivAt_toReal_two_tail` — the consumer shape on the whole tail `[r₀,∞)`;
* `intervalIntegrable_rhsScalarTwo_tail` — the `hint`-input of
  `ac_and_ae_hasDerivAt_cutMomentReal_two_of_identity` on the whole tail.

No `sorry`, no `admit`, no `native_decide`, no custom axiom.
-/
module

public import PercLib.CriticalLRP.Analysis.SecondMomentTail
public import PercLib.CriticalLRP.Analysis.Cutoff.CornerRadii
public import PercLib.CriticalLRP.Analysis.Cutoff.SecondMoment.RadiusMoments

/-!
# Almost-everywhere corner elimination on radius windows
-/

set_option autoImplicit false
set_option linter.hashCommand false
set_option linter.style.longLine false
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false

@[expose] public section

noncomputable section

open MeasureTheory Filter Topology Set
open scoped ENNReal NNReal Topology

namespace PercLib.CriticalLRP.Orchestration.SmwywszgoM8

/-! ## 1. The generic countable-union lemma

The hypothesis is stated over *real*-ended windows, which is the form the landed model-level
theorems have; the countable family used in the proof is the subset of `ℚ × ℚ` of pairs whose
closed window avoids `C`, so no choice and no enumeration of the exceptional set is needed. -/

/-- **Countable transfer from off-exception windows to the whole window.**

Let `C` have the local separation property that every point outside `C` has a neighbourhood
outside `C` (true for a closed `C`, in particular for the finite `M.cornerRadii ∩ [a,b]`).  If
`HasDerivAt f (g x) x` holds for almost every `x` of every window `(u,v) ⊂ (r₀,b)` whose closed
window avoids `C`, then it holds for almost every `x ∈ (r₀,b) \ C`.

The proof covers `(r₀,b) \ C` by the rational-ended windows that avoid `C` and uses
`MeasureTheory.ae_all_iff` for the countable union; the only point that needs the separation
property is that a rational window fits inside the off-`C` ball around `x`. -/
theorem ae_hasDerivAt_of_offCorner_window_ae_Ioo {f g : ℝ → ℝ} {C : Set ℝ} {r₀ b : ℝ}
    (hC : ∀ t, t ∉ C → ∃ ε > 0, ∀ s : ℝ, |s - t| < ε → s ∉ C)
    (H : ∀ u v : ℝ, r₀ < u → u < v → v < b → (∀ r ∈ Set.Icc u v, r ∉ C) →
      ∀ᵐ x ∂volume, x ∈ Set.Ioo u v → HasDerivAt f (g x) x) :
    ∀ᵐ x ∂volume, x ∈ Set.Ioo r₀ b → x ∉ C → HasDerivAt f (g x) x := by
  classical
  set T : Set (ℚ × ℚ) :=
    {p | r₀ < (p.1 : ℝ) ∧ (p.1 : ℝ) < (p.2 : ℝ) ∧ (p.2 : ℝ) < b ∧
      ∀ r ∈ Set.Icc (p.1 : ℝ) (p.2 : ℝ), r ∉ C} with hT
  have hTw : ∀ p : T, ∀ᵐ x ∂volume,
      x ∈ Set.Ioo ((p : ℚ × ℚ).1 : ℝ) ((p : ℚ × ℚ).2 : ℝ) → HasDerivAt f (g x) x :=
    fun p => H _ _ p.2.1 p.2.2.1 p.2.2.2.1 p.2.2.2.2
  have hall : ∀ᵐ x ∂volume, ∀ p : T,
      x ∈ Set.Ioo ((p : ℚ × ℚ).1 : ℝ) ((p : ℚ × ℚ).2 : ℝ) → HasDerivAt f (g x) x :=
    MeasureTheory.ae_all_iff.mpr hTw
  filter_upwards [hall] with x hx hxI hxC
  obtain ⟨ε, hε, hball⟩ := hC x hxC
  have hlt : max r₀ (x - ε) < x := max_lt hxI.1 (by linarith)
  obtain ⟨p, hp1, hp2⟩ := exists_rat_btwn hlt
  have hgt : x < min b (x + ε) := lt_min hxI.2 (by linarith)
  obtain ⟨q, hq1, hq2⟩ := exists_rat_btwn hgt
  have hpq : (p : ℝ) < (q : ℝ) := lt_trans hp2 hq1
  have hmem : ((p, q) : ℚ × ℚ) ∈ T := by
    refine ⟨lt_of_le_of_lt (le_max_left _ _) hp1, hpq,
      lt_of_lt_of_le hq2 (min_le_left _ _), ?_⟩
    intro r hr
    refine hball r ?_
    have hpx : x - ε < (p : ℝ) := lt_of_le_of_lt (le_max_right _ _) hp1
    have hqx : (q : ℝ) < x + ε := lt_of_lt_of_le hq2 (min_le_right _ _)
    rw [abs_lt]
    constructor <;> linarith [hr.1, hr.2, hpx, hqx]
  exact hx ⟨(p, q), hmem⟩ ⟨hp2, hq1⟩

/-- **The same, with the exceptional set dropped from the conclusion when it is null.** -/
theorem ae_hasDerivAt_of_offCorner_window_ae_Ioo_of_measure_zero {f g : ℝ → ℝ} {C : Set ℝ}
    {r₀ b : ℝ} (hCmeas : volume C = 0)
    (hC : ∀ t, t ∉ C → ∃ ε > 0, ∀ s : ℝ, |s - t| < ε → s ∉ C)
    (H : ∀ u v : ℝ, r₀ < u → u < v → v < b → (∀ r ∈ Set.Icc u v, r ∉ C) →
      ∀ᵐ x ∂volume, x ∈ Set.Ioo u v → HasDerivAt f (g x) x) :
    ∀ᵐ x ∂volume, x ∈ Set.Ioo r₀ b → HasDerivAt f (g x) x := by
  have hae : ∀ᵐ x ∂(volume : Measure ℝ), x ∉ C := by
    rw [ae_iff]
    simpa using hCmeas
  filter_upwards [ae_hasDerivAt_of_offCorner_window_ae_Ioo hC H, hae] with x hx1 hx2 hx3
  exact hx1 hx3 hx2

/-! ## 2. The model-level corner set: separation and nullity -/

variable (M : SourceModelData)

/-- **Every off-corner radius has an off-corner neighbourhood**, in the `cornerRadii` vocabulary
used by `M.IsOffCornerWindow`. -/
theorem exists_neighbourhood_notMem_cornerRadii {t : ℝ} (ht : t ∉ M.cornerRadii) :
    ∃ ε > 0, ∀ s : ℝ, |s - t| < ε → s ∉ M.cornerRadii := by
  have ht' : t ∉ M.attainedRadii := by
    rwa [← M.attainedRadii_eq_cornerRadii] at ht
  obtain ⟨ε, hε, hsub⟩ := M.exists_nhds_notMem_attainedRadii ht'
  exact ⟨ε, hε, fun s hs => by
    have h := hsub s hs
    rwa [M.attainedRadii_eq_cornerRadii] at h⟩

/-! ## 3. `rhsScalarTwo` on windows that contain corner radii

The measurability and `L¹` inputs of the radius picture never used the off-corner condition: they
only used the window-flux convergence and the coefficient bound.  Making that explicit gives the
`hint`-input of `ac_and_ae_hasDerivAt_cutMomentReal_two_of_identity` on *every* window of the
positive tail, which is what a corner-containing window needs. -/

/-- **Measurability of `M.rhsScalarTwo` from the window-flux convergence alone.**  No off-corner
hypothesis is involved: `M.rhsScalarTwo` is a pointwise limit of the measurable window fluxes. -/
theorem measurable_rhsScalarTwo_of_windowFlux_tendsto (S : ℕ → Finset (Sym2 M.V))
    (hfluxConv : ∀ t, Tendsto (fun n => M.windowFlux (S n) t) atTop (𝓝 (M.rhsScalarTwo t))) :
    Measurable fun t => M.rhsScalarTwo t := by
  have hlim : (fun t => M.rhsScalarTwo t)
      = fun t => liminf (fun n => M.windowFlux (S n) t) atTop := by
    funext t
    exact (hfluxConv t).liminf_eq.symm
  rw [hlim]
  exact Measurable.liminf fun n => M.measurable_windowFlux (S n)

/-- **`M.rhsScalarTwo` is interval integrable on every window**, corner radii or not. -/
theorem intervalIntegrable_rhsScalarTwo_of_windowFlux_tendsto {a b : ℝ} (hab : a ≤ b)
    (S : ℕ → Finset (Sym2 M.V))
    (hfluxConv : ∀ t, Tendsto (fun n => M.windowFlux (S n) t) atTop (𝓝 (M.rhsScalarTwo t)))
    {C : ℝ} (hC0 : 0 ≤ C) (hC : ∀ r ∈ Set.Icc a b, |M.coeffRHS r| ≤ C)
    (h2b : M.cutMoment 2 b ≠ ⊤) :
    IntervalIntegrable (fun t => M.rhsScalarTwo t) volume a b :=
  M.intervalIntegrable_rhsScalarTwo_of_coeffBound hab
    (measurable_rhsScalarTwo_of_windowFlux_tendsto M S hfluxConv) hC0 hC
    (PercLib.CriticalLRP.CaseOne.cutMoment_four_ne_top_of_two M h2b)

/-! ## 4. Corner elimination for the a.e. radius derivative

This is the `hae` half of the `p = 2` radius picture on a window that *contains* corner radii:
the landed `ac_and_ae_hasDerivAt_cutMomentReal_two_assembled` is applied on each rational-ended
off-corner subwindow, and §1 glues the countably many a.e. statements.  Nothing is claimed about
absolute continuity, the integrated identity, or the derivative at an attained radius. -/

/-- **The a.e. radius derivative on any positive window, corners allowed.**

Inputs are those of the landed off-corner theorem, evaluated on the *single* window `[r₀,b]`:
a monotone edge-exhausting family `S`, finiteness of the second cutoff moment at `b`, a bound on
`|M.coeffRHS|` on `[r₀,b]`, and the fixed-radius window-flux convergence.  The conclusion is the
a.e. derivative statement on the whole of `(r₀,b)`, with no off-corner assumption on `[r₀,b]`. -/
theorem ae_hasDerivAt_cutMomentReal_two_Ioo {r₀ b : ℝ} (hr₀ : 0 < r₀) (hrb : r₀ < b)
    (S : ℕ → Finset (Sym2 M.V)) (hSmono : Monotone S) (hS : ∀ e : Sym2 M.V, ∃ k, e ∈ S k)
    (h2b : M.cutMoment 2 b ≠ ⊤)
    {C : ℝ} (hC0 : 0 ≤ C) (hC : ∀ r ∈ Set.Icc r₀ b, |M.coeffRHS r| ≤ C)
    (hfluxConv : ∀ t, Tendsto (fun n => M.windowFlux (S n) t) atTop (𝓝 (M.rhsScalarTwo t))) :
    ∀ᵐ r ∂volume, r ∈ Set.Ioo r₀ b →
      HasDerivAt (fun r => M.cutMomentReal 2 r) (M.rhsScalarTwo r) r := by
  have hsep : ∀ t : ℝ, t ∉ M.cornerRadii →
      ∃ ε > 0, ∀ s : ℝ, |s - t| < ε → s ∉ M.cornerRadii :=
    fun t ht => exists_neighbourhood_notMem_cornerRadii M ht
  refine ae_hasDerivAt_of_offCorner_window_ae_Ioo_of_measure_zero M.volume_cornerRadii hsep ?_
  intro u v hru huv hvb hoff
  have hcr : r₀ ≤ u := hru.le
  have hsub : Set.Icc u v ⊆ Set.Icc r₀ b := fun r hr => ⟨hcr.trans hr.1, hr.2.trans hvb.le⟩
  exact (PercLib.CriticalLRP.Orchestration.Smwyvlg99M1.ac_and_ae_hasDerivAt_cutMomentReal_two_assembled
    M ⟨lt_trans hr₀ hru, le_of_lt huv, hoff⟩ S hSmono hS
    (M.cutMoment_ne_top_of_le hvb.le 2 h2b) hC0 (fun r hr => hC r (hsub hr))
    hfluxConv).2.1

/-- **Corner elimination as an a.e. equality of `deriv`.** -/
theorem deriv_ae_eq_rhsScalarTwo_Ioo {r₀ b : ℝ} (hr₀ : 0 < r₀) (hrb : r₀ < b)
    (S : ℕ → Finset (Sym2 M.V)) (hSmono : Monotone S) (hS : ∀ e : Sym2 M.V, ∃ k, e ∈ S k)
    (h2b : M.cutMoment 2 b ≠ ⊤)
    {C : ℝ} (hC0 : 0 ≤ C) (hC : ∀ r ∈ Set.Icc r₀ b, |M.coeffRHS r| ≤ C)
    (hfluxConv : ∀ t, Tendsto (fun n => M.windowFlux (S n) t) atTop (𝓝 (M.rhsScalarTwo t))) :
    deriv (fun r => M.cutMomentReal 2 r) =ᵐ[volume.restrict (Set.Ioo r₀ b)]
      fun t => M.rhsScalarTwo t :=
  PercLib.CriticalLRP.Orchestration.Smwyvlg99M1.deriv_ae_eq_of_ae_hasDerivAt
    (ae_hasDerivAt_cutMomentReal_two_Ioo M hr₀ hrb S hSmono hS h2b hC0 hC hfluxConv)

/-! ## 5. The consumer shape on the whole tail `[r₀,∞)`

The consumer (`SourceModelData.regularlyVarying_two` and its Case-1/Case-3 companions) wants the
a.e. derivative on `volume.restrict (Set.Ici r₀)`.  The passage from the per-window statements to
the tail is the countable union over the windows `(r₀, r₀ + n + 1)`.  The only extra input is
finiteness of the second cutoff moment on the tail, which is stated explicitly: it is not landed
in production. -/

/-- **`hae` for the consumer, with `IsOffCornerWindow` removed.** -/
theorem ae_hasDerivAt_toReal_two_tail {r₀ : ℝ} (hr₀ : 0 < r₀)
    (S : ℕ → Finset (Sym2 M.V)) (hSmono : Monotone S) (hS : ∀ e : Sym2 M.V, ∃ k, e ∈ S k)
    (hfin : ∀ b : ℝ, r₀ ≤ b → M.cutMoment 2 b ≠ ⊤)
    {C : ℝ} (hC0 : 0 ≤ C) (hC : ∀ r : ℝ, r₀ ≤ r → |M.coeffRHS r| ≤ C)
    (hfluxConv : ∀ t, Tendsto (fun n => M.windowFlux (S n) t) atTop (𝓝 (M.rhsScalarTwo t))) :
    ∀ᵐ t ∂(volume.restrict (Set.Ici r₀)),
      HasDerivAt (fun r : ℝ => (M.cutMoment 2 r).toReal) (M.rhsScalarTwo t) t := by
  have hall : ∀ n : ℕ, ∀ᵐ t ∂volume,
      t ∈ Set.Ioo r₀ (r₀ + (n : ℝ) + 1) →
        HasDerivAt (fun r : ℝ => (M.cutMoment 2 r).toReal) (M.rhsScalarTwo t) t := by
    intro n
    have hn : (0 : ℝ) ≤ (n : ℝ) := Nat.cast_nonneg n
    have hlt : r₀ < r₀ + (n : ℝ) + 1 := by linarith
    have hb : r₀ ≤ r₀ + (n : ℝ) + 1 := hlt.le
    exact ae_hasDerivAt_cutMomentReal_two_Ioo M hr₀ hlt S hSmono hS
      (hfin _ hb) hC0 (fun r hr => hC r hr.1) hfluxConv
  have hu : ∀ᵐ t ∂volume, ∀ n : ℕ, t ∈ Set.Ioo r₀ (r₀ + (n : ℝ) + 1) →
      HasDerivAt (fun r : ℝ => (M.cutMoment 2 r).toReal) (M.rhsScalarTwo t) t :=
    MeasureTheory.ae_all_iff.mpr hall
  rw [ae_restrict_iff' measurableSet_Ici]
  have hne : ∀ᵐ t ∂(volume : Measure ℝ), t ≠ r₀ := by
    rw [ae_iff]
    simp
  filter_upwards [hu, hne] with t ht htr hmem
  have hlt : r₀ < t := lt_of_le_of_ne hmem (Ne.symm htr)
  obtain ⟨n, hn⟩ := exists_nat_gt (t - r₀)
  exact ht n ⟨hlt, by linarith⟩

/-- **The `hint`-input of the identity route on the whole tail**, with no off-corner condition:
on `[r₀, R]` for every `R ≥ r₀`, `M.rhsScalarTwo` is interval integrable. -/
theorem intervalIntegrable_rhsScalarTwo_tail {r₀ : ℝ}
    (S : ℕ → Finset (Sym2 M.V))
    (hfluxConv : ∀ t, Tendsto (fun n => M.windowFlux (S n) t) atTop (𝓝 (M.rhsScalarTwo t)))
    {C : ℝ} (hC0 : 0 ≤ C) (hC : ∀ r : ℝ, r₀ ≤ r → |M.coeffRHS r| ≤ C)
    (hfin : ∀ b : ℝ, r₀ ≤ b → M.cutMoment 2 b ≠ ⊤) :
    ∀ R : ℝ, r₀ ≤ R → IntervalIntegrable (fun t => M.rhsScalarTwo t) volume r₀ R :=
  fun R hR => intervalIntegrable_rhsScalarTwo_of_windowFlux_tendsto M hR S hfluxConv hC0
    (fun r hr => hC r hr.1) (hfin R hR)

end PercLib.CriticalLRP.Orchestration.SmwywszgoM8

/-! ## Axiom audit -/

namespace PercLib.CriticalLRP.Orchestration.SmwywszgoM8

#print axioms ae_hasDerivAt_of_offCorner_window_ae_Ioo
#print axioms ae_hasDerivAt_of_offCorner_window_ae_Ioo_of_measure_zero
#print axioms exists_neighbourhood_notMem_cornerRadii
#print axioms measurable_rhsScalarTwo_of_windowFlux_tendsto
#print axioms intervalIntegrable_rhsScalarTwo_of_windowFlux_tendsto
#print axioms ae_hasDerivAt_cutMomentReal_two_Ioo
#print axioms deriv_ae_eq_rhsScalarTwo_Ioo
#print axioms ae_hasDerivAt_toReal_two_tail
#print axioms intervalIntegrable_rhsScalarTwo_tail

end PercLib.CriticalLRP.Orchestration.SmwywszgoM8

namespace PercLib.CriticalLRP.Orchestration.SmwywszgoM8

variable (M : SourceModelData)

/-! ## 6. Capstone: `hae` on the tail with the coefficient bound discharged

`ac_and_ae_hasDerivAt_cutMomentReal_two_tail` of `Analysis/SecondMomentTail.lean` produces
`hac ∧ hae` but only under `M.IsOffCornerWindow a b`.  Composing §4/§5 with the sharpness-derived
coefficient bound gives the `hae` half for *every* tail window, with the coefficient bound no
longer a hypothesis.  The remaining inputs are exactly those of the consumer
`SourceModelData.regularlyVarying_two`: `0 < r₀`, an exhaustive monotone window family, tail
finiteness of the second cutoff moment (its `h2`), and the fixed-radius convergence of the window
fluxes.  `hac` is *not* claimed. -/

/-- **A uniform-in-`r` coefficient bound on the positive tail**, from the model's own sharpness
field.  Unlike `exists_coeffRHS_bound_of_deriv_decay` the constant is uniform on the whole halfline
`[r₀,∞)`, which is what a tail-wide statement needs. -/
theorem exists_uniform_coeffRHS_bound_tail :
    ∃ R : ℝ, ∀ r₀ : ℝ, R ≤ r₀ → 0 < r₀ →
      ∃ C, 0 ≤ C ∧ ∀ r : ℝ, r₀ ≤ r → |M.coeffRHS r| ≤ C := by
  obtain ⟨δ, hδ, hlog⟩ := M.exists_error
  have hδtend : Tendsto δ atTop (𝓝 0) := hlog.2
  have hev : ∀ᶠ r in atTop, |δ r| < 1 := by
    have h := hδtend.eventually (Metric.ball_mem_nhds (0 : ℝ) one_pos)
    simpa [Real.dist_eq, abs_sub_comm] using h
  obtain ⟨R₀, hR₀⟩ := eventually_atTop.mp hev
  refine ⟨max R₀ 0, fun r₀ hR₀' hr₀ => ?_⟩
  have hR₀le : R₀ ≤ r₀ := le_trans (le_max_left _ _) hR₀'
  have he : -(M.d : ℝ) - M.α - 1 ≤ 0 := by
    have hd1 : (1 : ℝ) ≤ (M.d : ℝ) := by exact_mod_cast M.hd
    have := M.hα
    linarith
  refine ⟨(M.betaCrit : ℝ) * (2 * r₀ ^ (-(M.d : ℝ) - M.α - 1)),
    mul_nonneg M.betaCrit.coe_nonneg (by positivity), fun r hr => ?_⟩
  have hr0 : 0 < r := lt_of_lt_of_le hr₀ hr
  have hδr : |δ r| ≤ 1 := le_of_lt (hR₀ r (le_trans hR₀le hr))
  have hδub : δ r ≤ 1 := (abs_le.mp hδr).2
  have h1 : 1 + δ r ≤ 2 := by linarith
  have hKr : |deriv M.K r| = (1 + δ r) * r ^ (-(M.d : ℝ) - M.α - 1) := hδ r hr0
  have hpow : r ^ (-(M.d : ℝ) - M.α - 1) ≤ r₀ ^ (-(M.d : ℝ) - M.α - 1) :=
    Real.rpow_le_rpow_of_nonpos hr₀ hr he
  have hpow0 : 0 ≤ r ^ (-(M.d : ℝ) - M.α - 1) :=
    le_of_lt (Real.rpow_pos_of_pos hr0 _)
  calc |M.coeffRHS r| = (M.betaCrit : ℝ) * |deriv M.K r| := by
        rw [SourceModelData.coeffRHS, abs_mul, abs_of_nonneg M.betaCrit.coe_nonneg, abs_neg]
    _ = (M.betaCrit : ℝ) * ((1 + δ r) * r ^ (-(M.d : ℝ) - M.α - 1)) := by rw [hKr]
    _ ≤ (M.betaCrit : ℝ) * (2 * r₀ ^ (-(M.d : ℝ) - M.α - 1)) :=
        mul_le_mul_of_nonneg_left
          (mul_le_mul h1 hpow hpow0 (by norm_num : (0 : ℝ) ≤ 2))
          M.betaCrit.coe_nonneg

/-- **The `hae` hypothesis of the consumer, without `IsOffCornerWindow` and without the
coefficient bound.**

There is a radius `R` such that for every `r₀ ≥ R`, every monotone edge-exhausting window family,
every tail-finite second cutoff moment and every fixed-radius window-flux convergence, the actual
second cutoff moment `r ↦ (M.cutMoment 2 r).toReal` has derivative `M.rhsScalarTwo` at almost every
radius of the whole tail `[r₀,∞)`.

Compared with `ac_and_ae_hasDerivAt_cutMoment_toReal_two_tail` the off-corner hypothesis on the
window is gone and the window is the whole halfline `[r₀,∞)` rather than a compact `[a,b]`; the
price is the explicit tail finiteness `∀ t ≥ r₀, M.cutMoment 2 t ≠ ⊤`, which is already the
consumer's input `h2`. -/
theorem ae_hasDerivAt_toReal_two_tail_of_hfluxConv :
    ∃ R : ℝ, ∀ ⦃r₀ : ℝ⦄, R ≤ r₀ → 0 < r₀ →
      ∀ (S : ℕ → Finset (Sym2 M.V)), Monotone S → (∀ e : Sym2 M.V, ∃ k, e ∈ S k) →
      (∀ t : ℝ, r₀ ≤ t → M.cutMoment 2 t ≠ ⊤) →
      (∀ t, Tendsto (fun n => M.windowFlux (S n) t) atTop (𝓝 (M.rhsScalarTwo t))) →
      ∀ᵐ t ∂(volume.restrict (Set.Ici r₀)),
        HasDerivAt (fun r : ℝ => (M.cutMoment 2 r).toReal) (M.rhsScalarTwo t) t := by
  obtain ⟨R, hR⟩ := exists_uniform_coeffRHS_bound_tail M
  refine ⟨R, fun {r₀} hRr hr₀ S hSmono hS hfin hfluxConv => ?_⟩
  obtain ⟨C, hC0, hC⟩ := hR r₀ hRr hr₀
  exact ae_hasDerivAt_toReal_two_tail M hr₀ S hSmono hS hfin hC0 hC hfluxConv

end PercLib.CriticalLRP.Orchestration.SmwywszgoM8

/-! ## Axiom audit (continued) -/

namespace PercLib.CriticalLRP.Orchestration.SmwywszgoM8

#print axioms exists_uniform_coeffRHS_bound_tail
#print axioms ae_hasDerivAt_toReal_two_tail_of_hfluxConv

end PercLib.CriticalLRP.Orchestration.SmwywszgoM8

namespace PercLib.CriticalLRP.Orchestration.SmwywszgoM8

variable (M : SourceModelData)

/-! ## 7. Corner elimination from the *integrated identity* on off-corner windows

The route of §4 goes through the flux-side inputs.  The landed
`SourceModelData.integral_rhsScalarTwo_eq_sub_of_offCornerWindow` (`OffCornerIdentity.lean`,
swarm member `m2`) produces the off-corner integrated identity with **no** flux hypothesis, so the
right interface for corner elimination is the identity itself: the only per-window inputs needed
below are interval integrability of `M.rhsScalarTwo` and the identity on that window.  This keeps
the two halves of the argument separate: the identity on corner-free windows is flux-side work
(`m2`), the passage to corner-containing windows is the countable union below. -/

/-- **Corner elimination from the integrated identity on off-exception windows.**

If every off-`C` subwindow of `(r₀,b)` carries the primitive identity
`∫ t in u..x, g = f x - f u` together with interval integrability of `g`, and `C` is null with
off-`C` neighbourhoods, then `f` has derivative `g` at almost every point of `(r₀,b)`. -/
theorem ae_hasDerivAt_of_offCorner_window_integral {f g : ℝ → ℝ} {C : Set ℝ} {r₀ b : ℝ}
    (hCmeas : volume C = 0)
    (hC : ∀ t, t ∉ C → ∃ ε > 0, ∀ s : ℝ, |s - t| < ε → s ∉ C)
    (H : ∀ u v : ℝ, r₀ < u → u < v → v < b → (∀ r ∈ Set.Icc u v, r ∉ C) →
      IntervalIntegrable g volume u v ∧ ∀ x ∈ Set.Icc u v, ∫ t in u..x, g t = f x - f u) :
    ∀ᵐ x ∂volume, x ∈ Set.Ioo r₀ b → HasDerivAt f (g x) x := by
  refine ae_hasDerivAt_of_offCorner_window_ae_Ioo_of_measure_zero hCmeas hC ?_
  intro u v hru huv hvb hoff
  obtain ⟨hint, hid⟩ := H u v hru huv hvb hoff
  refine PercLib.CriticalLRP.Orchestration.Smwyvlg99M1.ae_hasDerivAt_of_eq_add_integral
    hint ?_
  intro x hx
  rw [Set.uIcc_of_le huv.le] at hx
  rw [hid x hx]
  ring

/-- **`hae` on a corner-containing window, from the off-corner integrated identity.** -/
theorem ae_hasDerivAt_cutMomentReal_two_Ioo_of_offCorner_identity {r₀ b : ℝ} (hr₀ : 0 < r₀)
    (hrb : r₀ < b)
    (H : ∀ u v : ℝ, r₀ < u → u < v → v < b → (∀ r ∈ Set.Icc u v, r ∉ M.cornerRadii) →
      IntervalIntegrable (fun t => M.rhsScalarTwo t) volume u v ∧
        ∀ x ∈ Set.Icc u v,
          ∫ t in u..x, M.rhsScalarTwo t = M.cutMomentReal 2 x - M.cutMomentReal 2 u) :
    ∀ᵐ r ∂volume, r ∈ Set.Ioo r₀ b →
      HasDerivAt (fun r => M.cutMomentReal 2 r) (M.rhsScalarTwo r) r := by
  have hsep : ∀ t : ℝ, t ∉ M.cornerRadii →
      ∃ ε > 0, ∀ s : ℝ, |s - t| < ε → s ∉ M.cornerRadii :=
    fun t ht => exists_neighbourhood_notMem_cornerRadii M ht
  exact ae_hasDerivAt_of_offCorner_window_integral M.volume_cornerRadii hsep H

/-- **`hae` for the consumer on the whole tail, from the off-corner integrated identity.**

No flux hypothesis and no off-corner condition on the tail: the only per-window inputs are the
off-corner identity and interval integrability of `M.rhsScalarTwo` there, both of which are
supplied on each off-corner window by
`SourceModelData.integral_rhsScalarTwo_eq_sub_of_offCornerWindow` together with the tail
finiteness of the second moment. -/
theorem ae_hasDerivAt_toReal_two_tail_of_offCorner_identity {r₀ : ℝ} (hr₀ : 0 < r₀)
    (H : ∀ u v : ℝ, r₀ < u → u < v → (∀ r ∈ Set.Icc u v, r ∉ M.cornerRadii) →
      IntervalIntegrable (fun t => M.rhsScalarTwo t) volume u v ∧
        ∀ x ∈ Set.Icc u v,
          ∫ t in u..x, M.rhsScalarTwo t = M.cutMomentReal 2 x - M.cutMomentReal 2 u) :
    ∀ᵐ t ∂(volume.restrict (Set.Ici r₀)),
      HasDerivAt (fun r : ℝ => (M.cutMoment 2 r).toReal) (M.rhsScalarTwo t) t := by
  have hall : ∀ n : ℕ, ∀ᵐ t ∂volume,
      t ∈ Set.Ioo r₀ (r₀ + (n : ℝ) + 1) →
        HasDerivAt (fun r : ℝ => (M.cutMoment 2 r).toReal) (M.rhsScalarTwo t) t := by
    intro n
    have hn : (0 : ℝ) ≤ (n : ℝ) := Nat.cast_nonneg n
    have hlt : r₀ < r₀ + (n : ℝ) + 1 := by linarith
    refine ae_hasDerivAt_cutMomentReal_two_Ioo_of_offCorner_identity M hr₀ hlt ?_
    intro u v hru huv _ hoff
    exact H u v hru huv hoff
  have hu : ∀ᵐ t ∂volume, ∀ n : ℕ, t ∈ Set.Ioo r₀ (r₀ + (n : ℝ) + 1) →
      HasDerivAt (fun r : ℝ => (M.cutMoment 2 r).toReal) (M.rhsScalarTwo t) t :=
    MeasureTheory.ae_all_iff.mpr hall
  rw [ae_restrict_iff' measurableSet_Ici]
  have hne : ∀ᵐ t ∂(volume : Measure ℝ), t ≠ r₀ := by
    rw [ae_iff]
    simp
  filter_upwards [hu, hne] with t ht htr hmem
  have hlt : r₀ < t := lt_of_le_of_ne hmem (Ne.symm htr)
  obtain ⟨n, hn⟩ := exists_nat_gt (t - r₀)
  exact ht n ⟨hlt, by linarith⟩

end PercLib.CriticalLRP.Orchestration.SmwywszgoM8

/-! ## Axiom audit (continued) -/

namespace PercLib.CriticalLRP.Orchestration.SmwywszgoM8

#print axioms ae_hasDerivAt_of_offCorner_window_integral
#print axioms ae_hasDerivAt_cutMomentReal_two_Ioo_of_offCorner_identity
#print axioms ae_hasDerivAt_toReal_two_tail_of_offCorner_identity

end PercLib.CriticalLRP.Orchestration.SmwywszgoM8
