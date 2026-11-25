/-
Copyright (c) 2026 PercLib contributors. Released under Apache 2.0 license.

# `β ↑ β_c` transfer of the a priori first-moment bound (direction D1)

Source: T. Hutchcroft, *Critical long-range percolation I: High effective
dimension*, arXiv:2508.18807v1, Lemma I.4.9 (last line) and the passage to
`β ↑ β_c`.

`PercLib.CriticalLRP.SharpnessInput` supplies the left continuity `hmeet` of the
cut-off first moment in the intensity parameter (for the raw `sup`-norm kernel
`cutoffSymKernel`), but it stops there: it keeps the a priori ("sharpness")
bound

  `E_{β,r}|K_x| ≤ (2α/β) r^α`   for `β ∈ [β_c/2, β_c)` and `r ≥ R`

as a black-box hypothesis `hbdd` attached to each *individual* `β < β_c`, and it
does not pass the bound to `β = β_c`.  This file does that passage, at the
actual source model (`SourceModelData`, arbitrary normalized norm `M.S`,
loop-safe cut-off `M.cutKernel`).

The step is not a formality.  Monotonicity of `β ↦ E_{β,r}|K_x|` alone gives
`E_{β,r} ≤ E_{β_c,r}`; it cannot pass a bound to `β_c`, and the right-hand side
`2α r^α / β` is *increasing* as `β` decreases, so substituting `β = β_c` in the
bound would be invalid without a continuity statement.  What is actually used is
(i) monotonicity in `β`, (ii) left continuity at `β_c`, and (iii) the fact that
the a priori bound is available on a whole left-neighbourhood of `β_c`, so the
limit of the *bound* may be taken with it.

## Main results

* `SourceModelData.cutMassAtBeta`: the intensity-dependent range-truncated
  cluster mass `E_{β,r}|K_x|`, definitionally `M.cutMassAt r x` at
  `β = M.betaCrit`.
* `SourceModelData.tendsto_cutMassAtBeta_Iio`: left continuity of
  `β ↦ E_{β,r}|K_x|` at `β_c > 0`, at every fixed `r` and vertex `x`, with `⊤`
  allowed on both sides and no kernel-regularity hypothesis.
* `SourceModelData.iSup_cutMassAtBeta_eq`: `M.cutMassAt r x` is the supremum of
  `E_{β,r}|K_x|` over the subcritical intensities.
* `le_of_tendsto_le_of_tendsto_le`: the abstract transfer engine, and
  `exists_monotone_le_of_not_le_at`, a Lean-checked witness that its continuity
  hypothesis is not removable.
* `SourceModelData.cutMassAtBeta_le_at_betaCrit_of_Ioo`: a bound
  `E_{β,r}|K_x| ≤ C/β` on *one* interval `(β₁, β_c)` transfers to `β_c` with
  the constant `C/β_c` — no uniformity in `β → 0` is needed.
* `SourceModelData.cutMassAt_le_two_alpha_rpow`: the a priori bound at `β_c`
  with the *same* constant `2α/β_c` that the source uses.
* `SourceModelData.cutMassAt_ne_top` / `cutMoment_one_ne_top`: for every
  `r ≥ R`, `M.cutMassAt r 0 ≠ ⊤` (and `M.cutMoment 1 r ≠ ⊤`).  This is the
  eventual finiteness input of `ChiLower`, obtained without the lower
  comparison, the cut-off ODE, or `χ r → ∞`.

## What is *not* proved

The a priori bound on `[β_c/2, β_c)` itself is the source's sharpness input
`P_{(1-ε)β_c}`; it remains an explicit hypothesis here.  In particular the
finiteness of the *uncut* mean at `β < β_c` is not derived, and no use is made
of `θ = 0`, of percolation probabilities, or of finite boxes.

No `sorry`, no `admit`, no `native_decide`, no custom axioms.
-/
module

public import PercLib.CriticalLRP.MomentMonotonicity.Temperature.Defs
public import PercLib.CriticalLRP.Analysis.Cutoff.Defs
public import PercLib.CriticalLRP.SharpnessInput

/-! # Left continuity and endpoint transfer for subcritical cutoff means -/

set_option autoImplicit false
set_option linter.unusedSectionVars false
set_option linter.style.haveILetI false

open MeasureTheory Measure Filter Topology
open scoped ENNReal NNReal Topology

@[expose] public section

namespace PercLib.CriticalLRP.Orchestration

open PercLib.CriticalLRP FiniteVolume CutoffMomentTransfer

/-! ## The abstract transfer engine -/

/-- **Transfer of a pointwise bound to an endpoint from the left.**

If `f` is left continuous at `βc`, `g` has the left limit `g βc`, and `f β ≤ g β`
eventually for `β ↑ βc`, then `f βc ≤ g βc`.

The bound is required only on a left-neighbourhood of `βc`.  This is what lets
the a priori bound of Lemma I.4.9, stated on an interval `[β_c/2, β_c)`, be
passed to `β_c` with the constant at `β_c`.  Requiring the bound for all
`β < βc` also suffices, while requiring it at a single `β < βc` does not (see
`exists_monotone_le_of_not_le_at`). -/
theorem le_of_tendsto_le_of_tendsto_le {βc : ℝ≥0} [NeBot (𝓝[<] βc)]
    {f g : ℝ≥0 → ℝ≥0∞}
    (hf : Tendsto f (𝓝[<] βc) (𝓝 (f βc)))
    (hg : Tendsto g (𝓝[<] βc) (𝓝 (g βc)))
    (h : ∀ᶠ β : ℝ≥0 in 𝓝[<] βc, f β ≤ g β) : f βc ≤ g βc := by
  refine ENNReal.le_of_forall_pos_le_add fun ε hε hεtop => ?_
  have hlt : g βc < g βc + (ε : ℝ≥0∞) :=
    ENNReal.lt_add_right (ne_of_lt hεtop) (by exact_mod_cast hε.ne')
  refine le_of_tendsto hf ?_
  filter_upwards [h, hg (isOpen_Iio.mem_nhds hlt)] with β hfg hgβ
  exact hfg.trans hgβ.le

/-- The engine needs its continuity hypothesis: a monotone family satisfying
`f β ≤ g β` for *every* `β < βc` may still violate the bound at `βc`.  Here `f`
jumps by `⊤` at `βc`.  Consequently the `Tendsto` hypothesis of
`le_of_tendsto_le_of_tendsto_le` cannot be replaced by monotonicity of `f`,
which is why the left continuity `hmeet` is a genuine input of the passage to
`β_c` (for the actual model it is a theorem:
`SourceModelData.tendsto_cutMassAtBeta_Iio`). -/
theorem exists_monotone_le_of_not_le_at (βc : ℝ≥0) :
    ∃ f g : ℝ≥0 → ℝ≥0∞, (∀ β, β < βc → f β ≤ g β) ∧ ¬ f βc ≤ g βc ∧ Monotone f := by
  classical
  refine ⟨fun β => if β < βc then (0 : ℝ≥0∞) else ⊤, fun _ => 0, ?_, ?_, ?_⟩
  · intro β hβ
    change (if β < βc then (0 : ℝ≥0∞) else ⊤) ≤ (0 : ℝ≥0∞)
    rw [ite_eq_left hβ]
  · change ¬ (if βc < βc then (0 : ℝ≥0∞) else ⊤) ≤ (0 : ℝ≥0∞)
    rw [ite_eq_right (lt_irrefl βc)]
    exact not_le.mpr (by simp)
  · intro β γ hβγ
    change (if β < βc then (0 : ℝ≥0∞) else ⊤) ≤ (if γ < βc then (0 : ℝ≥0∞) else ⊤)
    by_cases hγ : γ < βc
    · rw [ite_eq_left (lt_of_le_of_lt hβγ hγ), ite_eq_left hγ]
    · rw [ite_eq_right hγ]
      split_ifs with h
      · exact zero_le
      · exact le_rfl

/-- A non-vacuous, sharp instance of the transfer engine: with `βc = 2`,
`f β = β` and `g β = 4/β` the hypothesis `f β ≤ g β` holds for every `β < 2`, and
the conclusion holds with **equality**.  So the engine's hypotheses are
satisfiable and its conclusion is not lossy in the rate. -/
theorem le_of_tendsto_le_of_tendsto_le_sharp_instance :
    (fun β : ℝ≥0 => ENNReal.ofReal (β : ℝ)) 2
      ≤ (fun β : ℝ≥0 => ENNReal.ofReal (4 / (β : ℝ))) 2 := by
  haveI : NeBot (𝓝[<] (2 : ℝ≥0)) := nhdsLT_neBot_of_exists_lt ⟨0, by norm_num⟩
  refine le_of_tendsto_le_of_tendsto_le (βc := 2) (f := fun β : ℝ≥0 => ENNReal.ofReal (β : ℝ))
    (g := fun β : ℝ≥0 => ENNReal.ofReal (4 / (β : ℝ))) ?_ ?_ ?_
  · exact ENNReal.continuous_ofReal.continuousAt.tendsto.comp
      (NNReal.continuous_coe.continuousAt.mono_left nhdsWithin_le_nhds)
  · exact ENNReal.continuous_ofReal.continuousAt.tendsto.comp
      (tendsto_const_nhds.div
        (NNReal.continuous_coe.continuousAt.mono_left nhdsWithin_le_nhds) (by norm_num))
  · filter_upwards [self_mem_nhdsWithin] with β hβ
    apply ENNReal.ofReal_le_ofReal
    have hβ2 : (β : ℝ) < 2 := by exact_mod_cast hβ
    rcases eq_or_lt_of_le β.coe_nonneg with h | h
    · rw [← h]
      simp
    · rw [le_div_iff₀ h]
      nlinarith

/-- The `ℝ≥0∞` a priori bound with a real constant is exactly the source's real
inequality *together with* finiteness of the quantity being bounded.  So in a
hypothesis of the form `E ≤ ofReal C` nothing about finiteness at `β_c` is
hidden: only finiteness at the subcritical intensities themselves. -/
theorem le_ofReal_iff_toReal {a : ℝ≥0∞} {C : ℝ} (hC : 0 ≤ C) :
    a ≤ ENNReal.ofReal C ↔ a ≠ ⊤ ∧ a.toReal ≤ C := by
  constructor
  · intro ha
    exact ⟨ne_top_of_le_ne_top ENNReal.ofReal_ne_top ha,
      (ENNReal.le_ofReal_iff_toReal_le (ne_top_of_le_ne_top ENNReal.ofReal_ne_top ha) hC).mp ha⟩
  · rintro ⟨htop, hle⟩
    calc a = ENNReal.ofReal a.toReal := (ENNReal.ofReal_toReal htop).symm
      _ ≤ ENNReal.ofReal C := ENNReal.ofReal_le_ofReal hle

/-! ## The intensity-dependent range-truncated cluster mass -/

namespace SourceModelData

noncomputable section

variable (M : SourceModelData)


/-! ### Left continuity in the intensity -/

/-- At nonnegative real parameters the `ℝ≥0`-parametrized family agrees with the
`ℝ`-parametrized one used by `longRangeMeasure`. -/
theorem cutMassAtBeta_mk (t : ℝ) (ht : 0 ≤ t) (r : ℝ) (x : M.V) :
    (∫⁻ ω, clusterVol ω x ∂(longRangeMeasure (M.cutKernel r) (M.cutKernel_nonneg r)
        (NNReal.mk (max t 0) (le_max_right t 0))))
      = M.cutMassAtBeta (NNReal.mk t ht) r x := by
  have h : NNReal.mk (max t 0) (le_max_right t 0) = NNReal.mk t ht := by
    apply NNReal.eq
    simp [max_eq_left ht]
  rw [h]
  rfl

/-- **Left continuity of the range-truncated cluster mass in the intensity**, at
every fixed cut-off radius and every vertex, for an arbitrary normalized source
norm and the loop-safe cut-off kernel.  Both sides may be `⊤`. -/
theorem tendsto_cutMassAtBeta_Iio {βc : ℝ≥0} (hβc : 0 < βc) (r : ℝ) (x : M.V) :
    Tendsto (fun β : ℝ≥0 => M.cutMassAtBeta β r x) (𝓝[<] βc)
      (𝓝 (M.cutMassAtBeta βc r x)) := by
  have hpos : (0 : ℝ) < (βc : ℝ) := by exact_mod_cast hβc
  have hbase := PercLib.CriticalLRP.tendsto_lintegral_clusterVol_longRangeMeasure
    (J := M.cutKernel r) (M.cutKernel_nonneg r) (βc := (βc : ℝ)) hpos x
  have hcoe : Tendsto (fun β : ℝ≥0 => (β : ℝ)) (𝓝[<] βc) (𝓝[<] (βc : ℝ)) := by
    refine tendsto_nhdsWithin_iff.mpr ⟨?_, ?_⟩
    · exact NNReal.continuous_coe.continuousAt.mono_left nhdsWithin_le_nhds
    · filter_upwards [self_mem_nhdsWithin] with β hβ
      exact_mod_cast hβ
  have hcomp := hbase.comp hcoe
  have hfun : ∀ β : ℝ≥0, (∫⁻ ω, clusterVol ω x ∂(longRangeMeasure (M.cutKernel r)
        (M.cutKernel_nonneg r) (NNReal.mk (max (β : ℝ) 0) (le_max_right (β : ℝ) 0))))
      = M.cutMassAtBeta β r x := fun β =>
    M.cutMassAtBeta_mk (β : ℝ) β.coe_nonneg r x
  have hval : (∫⁻ ω, clusterVol ω x ∂(longRangeMeasure (M.cutKernel r)
        (M.cutKernel_nonneg r) (NNReal.mk (max (βc : ℝ) 0) (le_max_right (βc : ℝ) 0))))
      = M.cutMassAtBeta βc r x :=
    M.cutMassAtBeta_mk (βc : ℝ) βc.coe_nonneg r x
  rw [hval] at hcomp
  exact (tendsto_congr hfun).mp hcomp

/-- **`M.cutMassAt r x` is the supremum of the subcritical range-truncated cluster
masses.**  The `iSup` form of `hmeet` at the actual source model, at every fixed
radius and vertex. -/
theorem iSup_cutMassAtBeta_eq {βc : ℝ≥0} (hβc : 0 < βc) (r : ℝ) (x : M.V) :
    (⨆ β : ℝ≥0, ⨆ (_ : β < βc), M.cutMassAtBeta β r x) = M.cutMassAtBeta βc r x := by
  haveI : NeBot (𝓝[<] βc) := nhdsLT_neBot_of_exists_lt ⟨0, hβc⟩
  refine le_antisymm ?_ ?_
  · refine iSup_le fun β => iSup_le fun hβ => ?_
    exact M.cutMassAtBeta_mono (le_of_lt hβ) r x
  · refine le_of_tendsto_le_of_tendsto_le (M.tendsto_cutMassAtBeta_Iio hβc r x)
      tendsto_const_nhds ?_
    filter_upwards [self_mem_nhdsWithin] with β hβ
    exact le_iSup₂ (f := fun β (_ : β < βc) => M.cutMassAtBeta β r x) β hβ

/-! ### The a priori bound at `β_c` -/

/-- The bound function `β ↦ C/β` is left continuous at `βc > 0`. -/
theorem tendsto_ofReal_div {C : ℝ} {βc : ℝ≥0} (hβc : 0 < βc) :
    Tendsto (fun β : ℝ≥0 => ENNReal.ofReal (C / (β : ℝ))) (𝓝[<] βc)
      (𝓝 (ENNReal.ofReal (C / (βc : ℝ)))) := by
  have hreal : Tendsto (fun β : ℝ≥0 => C / (β : ℝ)) (𝓝[<] βc) (𝓝 (C / (βc : ℝ))) :=
    tendsto_const_nhds.div
      (NNReal.continuous_coe.continuousAt.mono_left nhdsWithin_le_nhds)
      (by exact_mod_cast hβc.ne')
  exact ENNReal.continuous_ofReal.continuousAt.tendsto.comp hreal

/-- **`β ↑ β_c` transfer, general rate.**  A bound `E_{β,r}|K_x| ≤ C/β` valid on
one left-neighbourhood of `β_c` transfers to `β_c` with the constant `C/β_c` and
no loss. -/
theorem cutMassAtBeta_le_at_betaCrit_of_eventually {βc : ℝ≥0} (hβc : 0 < βc) {C : ℝ}
    {r : ℝ} {x : M.V}
    (h : ∀ᶠ β : ℝ≥0 in 𝓝[<] βc,
      M.cutMassAtBeta β r x ≤ ENNReal.ofReal (C / (β : ℝ))) :
    M.cutMassAtBeta βc r x ≤ ENNReal.ofReal (C / (βc : ℝ)) := by
  haveI : NeBot (𝓝[<] βc) := nhdsLT_neBot_of_exists_lt ⟨0, hβc⟩
  exact le_of_tendsto_le_of_tendsto_le (M.tendsto_cutMassAtBeta_Iio hβc r x)
    (tendsto_ofReal_div (C := C) hβc) h

/-- The rate function `β ↦ (2α/β) r^α` of the bound is left continuous at
`βc > 0`. -/
theorem tendsto_ofReal_two_alpha {r : ℝ} {βc : ℝ≥0} (hβc : 0 < βc) :
    Tendsto (fun β : ℝ≥0 => ENNReal.ofReal ((2 * M.α / (β : ℝ)) * r ^ M.α)) (𝓝[<] βc)
      (𝓝 (ENNReal.ofReal ((2 * M.α / (βc : ℝ)) * r ^ M.α))) := by
  have hcoe : Tendsto (fun β : ℝ≥0 => (β : ℝ)) (𝓝[<] βc) (𝓝 (βc : ℝ)) :=
    NNReal.continuous_coe.continuousAt.mono_left nhdsWithin_le_nhds
  have hdiv : Tendsto (fun β : ℝ≥0 => 2 * M.α / (β : ℝ)) (𝓝[<] βc)
      (𝓝 (2 * M.α / (βc : ℝ))) :=
    tendsto_const_nhds.div hcoe (NNReal.coe_ne_zero.mpr hβc.ne')
  have hreal : Tendsto (fun β : ℝ≥0 => (2 * M.α / (β : ℝ)) * r ^ M.α) (𝓝[<] βc)
      (𝓝 ((2 * M.α / (βc : ℝ)) * r ^ M.α)) :=
    hdiv.mul tendsto_const_nhds
  exact ENNReal.continuous_ofReal.continuousAt.tendsto.comp hreal

/-- **The a priori bound at one fixed radius, with no uniformity in `β` or in `r`.**

For a single radius `r`, only the bound at that radius and only for `β` in a
left-neighbourhood of `β_c` is needed: this is the weakest hypothesis shape that
the passage to `β_c` supports. -/
theorem cutMassAtBeta_le_two_alpha_of_eventually {βc : ℝ≥0} (hβc : 0 < βc) {r : ℝ}
    {x : M.V}
    (h : ∀ᶠ β : ℝ≥0 in 𝓝[<] βc,
      M.cutMassAtBeta β r x ≤ ENNReal.ofReal ((2 * M.α / (β : ℝ)) * r ^ M.α)) :
    M.cutMassAtBeta βc r x ≤ ENNReal.ofReal ((2 * M.α / (βc : ℝ)) * r ^ M.α) := by
  haveI : NeBot (𝓝[<] βc) := nhdsLT_neBot_of_exists_lt ⟨0, hβc⟩
  exact le_of_tendsto_le_of_tendsto_le (M.tendsto_cutMassAtBeta_Iio hβc r x)
    (M.tendsto_ofReal_two_alpha hβc) h

/-- **`β ↑ β_c` transfer of an arbitrary left-continuous rate.**  The a priori
bound `E_{β,r}|K_x| ≤ g β` need only hold on one interval `(β₁, β_c)`, and it
transfers to `β_c` with the constant `g β_c` and no loss. -/
theorem cutMassAtBeta_le_at_betaCrit_of_Ioo {β₁ βc : ℝ≥0} (h1 : β₁ < βc)
    {r : ℝ} {x : M.V} {g : ℝ≥0 → ℝ≥0∞}
    (hg : Tendsto g (𝓝[<] βc) (𝓝 (g βc)))
    (h : ∀ β : ℝ≥0, β₁ < β → β < βc → M.cutMassAtBeta β r x ≤ g β) :
    M.cutMassAtBeta βc r x ≤ g βc := by
  have hβc : 0 < βc := lt_of_le_of_lt (zero_le : (0 : ℝ≥0) ≤ β₁) h1
  haveI : NeBot (𝓝[<] βc) := nhdsLT_neBot_of_exists_lt ⟨0, hβc⟩
  have hmem : Set.Ioi β₁ ∈ 𝓝[<] βc := nhdsWithin_le_nhds (isOpen_Ioi.mem_nhds h1)
  exact le_of_tendsto_le_of_tendsto_le (M.tendsto_cutMassAtBeta_Iio hβc r x) hg
    (by filter_upwards [hmem, self_mem_nhdsWithin] with β hβ hlt; exact h β hβ hlt)

/-- The source's rate `(2α/β) r^α` as the rate function of
`cutMassAtBeta_le_at_betaCrit_of_Ioo`. -/
theorem cutMassAtBeta_le_at_betaCrit_of_Ioo_two_alpha {β₁ βc : ℝ≥0} (h1 : β₁ < βc)
    {r : ℝ} {x : M.V}
    (h : ∀ β : ℝ≥0, β₁ < β → β < βc →
      M.cutMassAtBeta β r x ≤ ENNReal.ofReal ((2 * M.α / (β : ℝ)) * r ^ M.α)) :
    M.cutMassAtBeta βc r x ≤ ENNReal.ofReal ((2 * M.α / (βc : ℝ)) * r ^ M.α) :=
  M.cutMassAtBeta_le_at_betaCrit_of_Ioo h1
    (M.tendsto_ofReal_two_alpha (lt_of_le_of_lt (zero_le : (0 : ℝ≥0) ≤ β₁) h1)) h

/-- **`β ↑ β_c` transfer of the a priori bound of Lemma I.4.9, at the actual
model.**  If `E_{β,r}|K_x| ≤ (2α/β) r^α` for every `β ∈ (0, β_c)` and every
`r ≥ R`, then the same bound holds at `β_c` for every `r ≥ R`. -/
theorem cutMassAt_le_two_alpha_rpow {R : ℝ} (hβc : 0 < M.betaCrit) {x : M.V}
    (h : ∀ β : ℝ≥0, 0 < β → β < M.betaCrit → ∀ r : ℝ, R ≤ r →
      M.cutMassAtBeta β r x ≤ ENNReal.ofReal ((2 * M.α / (β : ℝ)) * r ^ M.α))
    {r : ℝ} (hr : R ≤ r) :
    M.cutMassAt r x ≤ ENNReal.ofReal ((2 * M.α / (M.betaCrit : ℝ)) * r ^ M.α) := by
  rw [← M.cutMassAtBeta_betaCrit r x]
  refine M.cutMassAtBeta_le_at_betaCrit_of_Ioo_two_alpha (β₁ := 0) (βc := M.betaCrit)
    ?_ fun β hβ0 hβ => h β hβ0 hβ r hr
  exact hβc

/-- **The last line of the proof of Lemma I.4.9, in the source's own hypothesis
shape.**

The source proves the bound `E_{β,r}|K| ≤ (2α/β) r^α` for every
`β ∈ [β_c/2, β_c)` and every `r ≥ r₀`, with a threshold `r₀` that does *not*
depend on `β` (it obtains `r₀ ≤ (32C)^{1/(d-3α)}`).  Then it takes `β ↑ β_c`.
This theorem is exactly that step: from the uniform-in-`β` bound on the
half-interval one gets, at `β_c` and at the same radii, the bound with the
constant `2α/β_c`. -/
theorem cutMassAt_le_two_alpha_rpow_of_Ico {R : ℝ} (hβc : 0 < M.betaCrit) {x : M.V}
    (h : ∀ β : ℝ≥0, M.betaCrit / 2 ≤ β → β < M.betaCrit → ∀ r : ℝ, R ≤ r →
      M.cutMassAtBeta β r x ≤ ENNReal.ofReal ((2 * M.α / (β : ℝ)) * r ^ M.α))
    {r : ℝ} (hr : R ≤ r) :
    M.cutMassAt r x ≤ ENNReal.ofReal ((2 * M.α / (M.betaCrit : ℝ)) * r ^ M.α) := by
  rw [← M.cutMassAtBeta_betaCrit r x]
  refine M.cutMassAtBeta_le_at_betaCrit_of_Ioo_two_alpha (β₁ := M.betaCrit / 2)
    (βc := M.betaCrit) (half_lt_self hβc) fun β hβ hβlt => h β (le_of_lt hβ) hβlt r hr

/-- The finiteness consequence of `cutMassAt_le_two_alpha_rpow_of_Ico`: under the
source's uniform a priori bound on `[β_c/2, β_c)` the critical range-truncated
cluster mass is finite for every `r ≥ R`, at every vertex. -/
theorem cutMassAt_ne_top_of_Ico {R : ℝ} (hβc : 0 < M.betaCrit) {x : M.V}
    (h : ∀ β : ℝ≥0, M.betaCrit / 2 ≤ β → β < M.betaCrit → ∀ r : ℝ, R ≤ r →
      M.cutMassAtBeta β r x ≤ ENNReal.ofReal ((2 * M.α / (β : ℝ)) * r ^ M.α))
    {r : ℝ} (hr : R ≤ r) : M.cutMassAt r x ≠ ⊤ :=
  ne_top_of_le_ne_top ENNReal.ofReal_ne_top
    (M.cutMassAt_le_two_alpha_rpow_of_Ico hβc h hr)

/-- **Finiteness of the critical range-truncated cluster mass at a fixed radius.**
This is an eventual-finiteness input for `ChiLower` that does not go through the
cut-off ODE, the lower comparison, or `χ r → ∞`. -/
theorem cutMassAt_ne_top {R : ℝ} (hβc : 0 < M.betaCrit) {x : M.V}
    (h : ∀ β : ℝ≥0, 0 < β → β < M.betaCrit → ∀ r : ℝ, R ≤ r →
      M.cutMassAtBeta β r x ≤ ENNReal.ofReal ((2 * M.α / (β : ℝ)) * r ^ M.α))
    {r : ℝ} (hr : R ≤ r) : M.cutMassAt r x ≠ ⊤ :=
  ne_top_of_le_ne_top ENNReal.ofReal_ne_top (M.cutMassAt_le_two_alpha_rpow hβc h hr)

/-- The root mass at any intensity is the first moment. -/
theorem cutMassAt_zero_eq_cutMoment (r : ℝ) : M.cutMassAt r 0 = M.cutMoment 1 r := by
  simp [cutMassAt, cutMoment]

/-- The root form `M.cutMassAt r 0 = M.cutMoment 1 r ≠ ⊤`. -/
theorem cutMoment_one_ne_top {R : ℝ} (hβc : 0 < M.betaCrit)
    (h : ∀ β : ℝ≥0, 0 < β → β < M.betaCrit → ∀ r : ℝ, R ≤ r →
      M.cutMassAtBeta β r 0 ≤ ENNReal.ofReal ((2 * M.α / (β : ℝ)) * r ^ M.α))
    {r : ℝ} (hr : R ≤ r) : M.cutMoment 1 r ≠ ⊤ := by
  rw [← cutMassAt_zero_eq_cutMoment]
  exact M.cutMassAt_ne_top hβc h hr

/-! ## Reducing the a priori bound to a uniform bound on subcritical means -/

/-- At any nonnegative radius the range-truncated cluster mass is bounded by the
uncut first moment at the same intensity. -/
theorem cutMassAtBeta_le_law {β : ℝ≥0} {r : ℝ} (hr : 0 ≤ r) (x : M.V) :
    M.cutMassAtBeta β r x ≤ ∫⁻ ω, clusterVol ω x ∂(M.law β) := by
  have h := lintegral_clusterVol_pow_mono_of_le
    (π := bernoulliEdgeProb (M.cutKernel r) (M.cutKernel_nonneg r) β)
    (κ := bernoulliEdgeProb M.kernel M.kernel_nonneg β)
    (fun e => bernoulliEdgeProb_mono_kernel (M.cutKernel_le_kernel_of_nonneg hr)
      (M.cutKernel_nonneg r) M.kernel_nonneg β e) x 1
  simpa [cutMassAtBeta, law, longRangeMeasure, pow_one] using h

/-- **Finiteness of the critical range-truncated cluster mass from a uniform bound
on the subcritical uncut means.**

This is the weakest form of the source's sharpness input used by the passage to
`β_c`: it assumes only that the *uncut* mean at each `β < β_c` is bounded by one
constant `C ≠ ⊤` (no rate, no asymptotic, and nothing at `β_c` itself).  The
conclusion is `M.cutMassAt r x ≠ ⊤` for `r ≥ max 1 ((C / (2α/β_c))^(1/α))`.

The threshold is the one produced by `eventual_rpow_bound_of_le` at `β_c`; the
proof spends the factor `β ≤ β_c` on the monotonicity of `β ↦ 2α/β`. -/
theorem cutMassAt_ne_top_of_uncut_uniform {C : ℝ≥0∞} (hβc : 0 < M.betaCrit)
    (hC : C ≠ ⊤) {x : M.V}
    (huncut : ∀ β : ℝ≥0, β < M.betaCrit →
      (∫⁻ ω, clusterVol ω x ∂(M.law β)) ≤ C)
    {r : ℝ} (hr : max 1 ((C.toReal / (2 * M.α / (M.betaCrit : ℝ))) ^ (1 / M.α)) ≤ r) :
    M.cutMassAt r x ≠ ⊤ := by
  have hα : 0 < M.α := M.hα
  have hβcR : (0 : ℝ) < (M.betaCrit : ℝ) := by exact_mod_cast hβc
  have hr1 : 1 ≤ r := le_trans (le_max_left _ _) hr
  have hr0 : 0 ≤ r := le_trans zero_le_one hr1
  have hrpos : (0 : ℝ) < r := lt_of_lt_of_le one_pos hr1
  have hpowpos : (0 : ℝ) < r ^ M.α := Real.rpow_pos_of_pos hrpos M.α
  -- the constant is dominated by the rate at `β_c`
  have hCr : C.toReal ≤ (2 * M.α / (M.betaCrit : ℝ)) * r ^ M.α :=
    PercLib.CriticalLRP.eventual_rpow_bound_of_le (F := fun _ : ℝ => C) hα hβcR hC
      (fun _ => le_rfl) r hr
  -- the a priori bound at every subcritical intensity
  have hap : ∀ β : ℝ≥0, 0 < β → β < M.betaCrit →
      M.cutMassAtBeta β r x ≤ ENNReal.ofReal ((2 * M.α / (β : ℝ)) * r ^ M.α) := by
    intro β hβ0 hβlt
    have hle : M.cutMassAtBeta β r x ≤ C :=
      (M.cutMassAtBeta_le_law hr0 x).trans (huncut β hβlt)
    have hne : M.cutMassAtBeta β r x ≠ ⊤ := ne_top_of_le_ne_top hC hle
    refine (le_ofReal_iff_toReal (mul_nonneg (div_nonneg (by positivity) β.coe_nonneg)
      hpowpos.le)).mpr ⟨hne, ?_⟩
    calc (M.cutMassAtBeta β r x).toReal ≤ C.toReal := ENNReal.toReal_mono hC hle
      _ ≤ (2 * M.α / (M.betaCrit : ℝ)) * r ^ M.α := hCr
      _ ≤ (2 * M.α / (β : ℝ)) * r ^ M.α :=
          mul_le_mul_of_nonneg_right
            (div_le_div_of_nonneg_left (by positivity) (by exact_mod_cast hβ0)
              (by exact_mod_cast le_of_lt hβlt)) hpowpos.le
  rw [← M.cutMassAtBeta_betaCrit r x]
  exact ne_top_of_le_ne_top ENNReal.ofReal_ne_top
    (M.cutMassAtBeta_le_at_betaCrit_of_Ioo_two_alpha (β₁ := 0) (βc := M.betaCrit) hβc hap)

/-- The `∀ᶠ r in atTop` shape (the `hfin` of
`VolumeMoments/FirstMoment/Divergence.lean`) of critical finiteness, from the
uniform a priori bound on `[β_c/2, β_c)`. -/
theorem eventually_cutMassAt_ne_top_of_Ico {R : ℝ} (hβc : 0 < M.betaCrit)
    (h : ∀ β : ℝ≥0, M.betaCrit / 2 ≤ β → β < M.betaCrit → ∀ r : ℝ, R ≤ r →
      M.cutMassAtBeta β r 0 ≤ ENNReal.ofReal ((2 * M.α / (β : ℝ)) * r ^ M.α)) :
    ∀ᶠ r : ℝ in atTop, M.cutMassAt r 0 ≠ ⊤ :=
  eventually_atTop.mpr ⟨R, fun _ hr => M.cutMassAt_ne_top_of_Ico hβc h hr⟩

/-- The same eventual form, from a uniform bound on the subcritical uncut means. -/
theorem eventually_cutMassAt_ne_top_of_uncut_uniform {C : ℝ≥0∞} (hβc : 0 < M.betaCrit)
    (hC : C ≠ ⊤)
    (huncut : ∀ β : ℝ≥0, β < M.betaCrit →
      (∫⁻ ω, clusterVol ω 0 ∂(M.law β)) ≤ C) :
    ∀ᶠ r : ℝ in atTop, M.cutMassAt r 0 ≠ ⊤ :=
  eventually_atTop.mpr ⟨max 1 ((C.toReal / (2 * M.α / (M.betaCrit : ℝ))) ^ (1 / M.α)),
    fun _ hr => M.cutMassAt_ne_top_of_uncut_uniform hβc hC huncut hr⟩

/-- The `ChiLower` consumer form of `cutMassAt_ne_top_of_Ico`: the first cut-off
moment at the critical intensity is finite for every `r ≥ R`. -/
theorem cutMoment_one_ne_top_of_Ico {R : ℝ} (hβc : 0 < M.betaCrit)
    (h : ∀ β : ℝ≥0, M.betaCrit / 2 ≤ β → β < M.betaCrit → ∀ r : ℝ, R ≤ r →
      M.cutMassAtBeta β r 0 ≤ ENNReal.ofReal ((2 * M.α / (β : ℝ)) * r ^ M.α))
    {r : ℝ} (hr : R ≤ r) : M.cutMoment 1 r ≠ ⊤ := by
  rw [← cutMassAt_zero_eq_cutMoment]
  exact M.cutMassAt_ne_top_of_Ico hβc h hr

/-! ### Real-valued versus `ℝ≥0∞`-valued left continuity

The landed bootstrap `VolumeMoments.FirstMoment.first_moment_bound_all_beta` assumes
`hmeet : ∀ r, Tendsto (fun β => F β r) (𝓝[<] βc) (𝓝 (F βc r))` with `F` **real**-valued.  The two
theorems below show that, at the model (`F β r = (M.cutMassAtBeta β r x).toReal`), this hypothesis
is *equivalent* to finiteness of the critical mass (given finiteness of the subcritical ones).  It
therefore cannot be used to prove that finiteness, which is why the `ℝ≥0∞`-level statements above
are the ones that carry the content. -/

/-- The cluster of `x` contains `x`, so its volume is at least `1`. -/
theorem one_le_clusterVol {V : Type*} [Countable V] (ω : Config V) (x : V) :
    (1 : ℝ≥0∞) ≤ clusterVol ω x := by
  rw [clusterVol_eq_tsum]
  refine le_trans ?_ (ENNReal.le_tsum (f := fun y =>
    (cluster ω x).indicator (fun _ => (1 : ℝ≥0∞)) y) x)
  rw [Set.indicator_of_mem (PercLib.Percolation.Bond.mem_cluster_self ω x)]

/-- The range-truncated cluster mass is at least `1`. -/
theorem one_le_cutMassAtBeta (β : ℝ≥0) (r : ℝ) (x : M.V) :
    (1 : ℝ≥0∞) ≤ M.cutMassAtBeta β r x := by
  have hint : (1 : ℝ≥0∞) ≤ ∫⁻ ω, clusterVol ω x
      ∂(longRangeMeasure (M.cutKernel r) (M.cutKernel_nonneg r) β) := by
    calc (1 : ℝ≥0∞) = ∫⁻ _ω : Config M.V, (1 : ℝ≥0∞)
          ∂(longRangeMeasure (M.cutKernel r) (M.cutKernel_nonneg r) β) := by simp
      _ ≤ ∫⁻ ω, clusterVol ω x
          ∂(longRangeMeasure (M.cutKernel r) (M.cutKernel_nonneg r) β) :=
          lintegral_mono (fun ω => one_le_clusterVol ω x)
  exact hint

/-- **Real-valued left continuity forces finiteness at `βc`.**  If the subcritical
range-truncated masses are finite, the real-valued `Tendsto` hypothesis of
`first_moment_bound_all_beta` at `F β r = (M.cutMassAtBeta β r x).toReal` already
implies `M.cutMassAtBeta βc r x ≠ ⊤`. -/
theorem cutMassAtBeta_ne_top_of_tendsto_toReal {βc : ℝ≥0} (hβc : 0 < βc) {r : ℝ}
    {x : M.V} (hsub : ∀ β : ℝ≥0, β < βc → M.cutMassAtBeta β r x ≠ ⊤)
    (h : Tendsto (fun β : ℝ≥0 => (M.cutMassAtBeta β r x).toReal) (𝓝[<] βc)
      (𝓝 ((M.cutMassAtBeta βc r x).toReal))) :
    M.cutMassAtBeta βc r x ≠ ⊤ := by
  haveI : NeBot (𝓝[<] βc) := nhdsLT_neBot_of_exists_lt ⟨0, hβc⟩
  intro htop
  have h0 : (M.cutMassAtBeta βc r x).toReal = 0 := by rw [htop]; simp
  rw [h0] at h
  have hev : ∀ᶠ β : ℝ≥0 in 𝓝[<] βc, (M.cutMassAtBeta β r x).toReal < 1 :=
    h (isOpen_Iio.mem_nhds (by norm_num : (0 : ℝ) < 1))
  obtain ⟨β, hβ1, hβ2⟩ := (hev.and self_mem_nhdsWithin).exists
  have hge : (1 : ℝ) ≤ (M.cutMassAtBeta β r x).toReal := by
    calc (1 : ℝ) = (1 : ℝ≥0∞).toReal := by simp
      _ ≤ (M.cutMassAtBeta β r x).toReal :=
          ENNReal.toReal_mono (hsub β hβ2) (M.one_le_cutMassAtBeta β r x)
  linarith

/-- The converse direction: finiteness at `βc` gives the real-valued `Tendsto`
hypothesis `hmeet` of `first_moment_bound_all_beta`. -/
theorem tendsto_toReal_cutMassAtBeta {βc : ℝ≥0} (hβc : 0 < βc) (r : ℝ) (x : M.V)
    (hfin : M.cutMassAtBeta βc r x ≠ ⊤) :
    Tendsto (fun β : ℝ≥0 => (M.cutMassAtBeta β r x).toReal) (𝓝[<] βc)
      (𝓝 ((M.cutMassAtBeta βc r x).toReal)) :=
  (ENNReal.tendsto_toReal hfin).comp (M.tendsto_cutMassAtBeta_Iio hβc r x)

/-- The hypothesis of `cutMassAt_le_two_alpha_rpow` at a subcritical intensity is
the source's real inequality plus finiteness at that intensity. -/
theorem cutMassAtBeta_le_iff_toReal {β : ℝ≥0} {r : ℝ} {x : M.V}
    (h : 0 ≤ (2 * M.α / (β : ℝ)) * r ^ M.α) :
    M.cutMassAtBeta β r x ≤ ENNReal.ofReal ((2 * M.α / (β : ℝ)) * r ^ M.α) ↔
      M.cutMassAtBeta β r x ≠ ⊤ ∧
        (M.cutMassAtBeta β r x).toReal ≤ (2 * M.α / (β : ℝ)) * r ^ M.α :=
  le_ofReal_iff_toReal h

end

end SourceModelData

end PercLib.CriticalLRP.Orchestration

/-! ## Axiom audit (every new theorem) -/

set_option linter.hashCommand false
set_option linter.style.longLine false

#print axioms PercLib.CriticalLRP.Orchestration.le_of_tendsto_le_of_tendsto_le
#print axioms PercLib.CriticalLRP.Orchestration.exists_monotone_le_of_not_le_at
#print axioms PercLib.CriticalLRP.Orchestration.le_of_tendsto_le_of_tendsto_le_sharp_instance
#print axioms PercLib.CriticalLRP.Orchestration.le_ofReal_iff_toReal
#print axioms PercLib.CriticalLRP.Orchestration.SourceModelData.cutMassAtBeta_betaCrit
#print axioms PercLib.CriticalLRP.Orchestration.SourceModelData.cutMassAtBeta_mono
#print axioms PercLib.CriticalLRP.Orchestration.SourceModelData.cutMassAtBeta_mk
#print axioms PercLib.CriticalLRP.Orchestration.SourceModelData.tendsto_cutMassAtBeta_Iio
#print axioms PercLib.CriticalLRP.Orchestration.SourceModelData.iSup_cutMassAtBeta_eq
#print axioms PercLib.CriticalLRP.Orchestration.SourceModelData.tendsto_ofReal_div
#print axioms PercLib.CriticalLRP.Orchestration.SourceModelData.cutMassAtBeta_le_at_betaCrit_of_eventually
#print axioms PercLib.CriticalLRP.Orchestration.SourceModelData.tendsto_ofReal_two_alpha
#print axioms PercLib.CriticalLRP.Orchestration.SourceModelData.cutMassAtBeta_le_two_alpha_of_eventually
#print axioms PercLib.CriticalLRP.Orchestration.SourceModelData.cutMassAtBeta_le_at_betaCrit_of_Ioo
#print axioms PercLib.CriticalLRP.Orchestration.SourceModelData.cutMassAtBeta_le_at_betaCrit_of_Ioo_two_alpha
#print axioms PercLib.CriticalLRP.Orchestration.SourceModelData.cutMassAt_le_two_alpha_rpow
#print axioms PercLib.CriticalLRP.Orchestration.SourceModelData.cutMassAt_le_two_alpha_rpow_of_Ico
#print axioms PercLib.CriticalLRP.Orchestration.SourceModelData.cutMassAt_ne_top_of_Ico
#print axioms PercLib.CriticalLRP.Orchestration.SourceModelData.cutMassAt_ne_top
#print axioms PercLib.CriticalLRP.Orchestration.SourceModelData.cutMassAt_zero_eq_cutMoment
#print axioms PercLib.CriticalLRP.Orchestration.SourceModelData.cutMoment_one_ne_top
#print axioms PercLib.CriticalLRP.Orchestration.SourceModelData.cutMassAtBeta_le_law
#print axioms PercLib.CriticalLRP.Orchestration.SourceModelData.cutMassAt_ne_top_of_uncut_uniform
#print axioms PercLib.CriticalLRP.Orchestration.SourceModelData.eventually_cutMassAt_ne_top_of_Ico
#print axioms PercLib.CriticalLRP.Orchestration.SourceModelData.eventually_cutMassAt_ne_top_of_uncut_uniform
#print axioms PercLib.CriticalLRP.Orchestration.SourceModelData.cutMoment_one_ne_top_of_Ico
#print axioms PercLib.CriticalLRP.Orchestration.SourceModelData.one_le_clusterVol
#print axioms PercLib.CriticalLRP.Orchestration.SourceModelData.one_le_cutMassAtBeta
#print axioms PercLib.CriticalLRP.Orchestration.SourceModelData.cutMassAtBeta_ne_top_of_tendsto_toReal
#print axioms PercLib.CriticalLRP.Orchestration.SourceModelData.tendsto_toReal_cutMassAtBeta
#print axioms PercLib.CriticalLRP.Orchestration.SourceModelData.cutMassAtBeta_le_iff_toReal
