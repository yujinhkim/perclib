/-
Copyright (c) 2026 PercLib contributors. Released under Apache 2.0.

# Normalized reduced-parameter moment transfer

Reviewed and integrated from Ultramath `smwtqkdul` member `m4`,
`A2ReducedMomentTransfer.lean`, against revision
`9afe8a172733efb434a2944a2ed97cfca4ad9bcf`. The transfer is conditional on
finite subcritical moments of the uncut law; it does not derive them from
vanishing percolation probability.
-/

/-
# A2 — Normalized reduced-parameter moment transfer at the actual source model

Hutchcroft, *Critical long-range percolation I: High effective dimension*,
arXiv:2508.18807v1, Definition I.1.5 and p. 7: for every `r < ∞` there is
`ε = ε(r) > 0` with `J_r ≤ (1 − ε) J`, so that `P_{β_c,r} ⪯ P_{(1−ε)β_c}`.

`MomentMonotonicity/StrictCutoffEpsilon.lean` proves the *edgewise* statement at the
genuine source model, at an arbitrary admissible `SourceNormData`, for every `r > 0`:

  `SourceModelData.exists_epsilon_domination_attained`
  `SourceModelData.cutKernel_edgeProb_le_reduced`
  `SourceModelData.cutLaw_le_reduced`

`CountableProduct/MonotoneMoments.lean` / `MomentMonotonicity/MomentTransfer.lean`
supply the *all-order* monotone transport for an arbitrary countable vertex type
(`lintegral_clusterVol_pow_mono_of_le`, `lintegral_clusterVol_rpow_mono_of_le`), so that
side is already general and is only *instantiated* here.

What is missing, and what this file adds, is the ENNReal **moment** comparison at the
model level:

* `lintegral_clusterVol_pow_mono_of_le` is stated for `edgeMeasure π` / `edgeMeasure κ`;
  the model's laws are `longRangeMeasure` (`= edgeMeasure (bernoulliEdgeProb …)`), and
  the reduced parameter is `β_c * c` with `c = 1 − ε`.  The composition of the edgewise
  comparison with the transport is `SourceModelData.cutMoment_le_reduced_nnreal`, and it
  covers every natural order (`cutMoment p`) and every real order `p ≥ 0`.
* `CutoffMomentTransfer.cutoff_lintegral_clusterVol_pow_le` is the *raw sup-norm*
  interface (`kernelJ (K ∘ ‖·‖_∞)`, `r ≥ 1`); it is not used and does not apply to the
  actual `SourceNormData` kernel.
* The coefficient supplied by `exists_epsilon_domination` depends on `r`.  For an
  *interval* of cutoffs a single `c` suffices, because the profile is `K s − K r`, so the
  smallness that matters is `K r / K t₀ ≤ K R / K t₀` for `r ≤ R`:
  `SourceModelData.exists_uniform_reduced_coefficient`.  Hence one subcritical moment at
  the single parameter `β_c c_R` bounds every cutoff moment with `r ∈ (0, R]`
  (`cutMoment_le_reduced_uniform_window`).
* Finally `SourceModelData.cutMassAt_ne_top_of_subcritical`: if the *uncut* first moment
  is finite at every parameter strictly below `β_c`, then `M.cutMassAt r 0 ≠ ⊤` for
  **every** `r > 0`.  This discharges the `hfin` premise that
  `VolumeMoments/FirstMoment/Divergence.lean` explicitly leaves open, and combined with
  the landed `I42C.tendsto_cutMassAt_atTop_nhds_top` yields the paper's real-valued
  `E_{β_c,r}|K| → ∞` (`tendsto_cutMassAt_toReal_atTop_of_subcritical`).

## What is *not* claimed

* No subcritical moment finiteness is produced here.  `E_β|K| < ∞` for `β < β_c` is the
  explicit premise `hsub`; it is **not** implied by `θ_β = 0`
  (`RayRefutation.exists_subcritical_infinite_mean` is a Lean-checked counterexample in
  this very framework), and it is certainly not implied by finiteness of the critical
  mean — which is what the campaign is trying to *derive*, not assume.
* Nothing about large `r` uniformly: `c(r) = 1 − ε(r) ↑ 1` as `r → ∞` because
  `K r ↓ 0`, so the global statement genuinely needs *all* subcritical parameters.
* No claim about the actual model ODE, about AC, or about `E1 ≥ 0`.

No `sorry`, no `admit`, no `native_decide`, no custom axioms.
-/
module

public import PercLib.CriticalLRP.MomentMonotonicity.SourceModelMoments
public import PercLib.CriticalLRP.MomentMonotonicity.StrictCutoffEpsilon
public import PercLib.CriticalLRP.MomentMonotonicity.MomentTransfer
public import PercLib.CriticalLRP.VolumeMoments.FirstMoment.Divergence

set_option autoImplicit false
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false

open MeasureTheory Measure ProbabilityTheory unitInterval Filter Topology Set
open scoped ENNReal NNReal Topology

@[expose] public section

namespace PercLib.CriticalLRP.Orchestration

open PercLib.CriticalLRP FiniteVolume CutoffMomentTransfer

variable {d : ℕ}

/-! ## 1. The transfer at the level of the laws

The reduced parameter is written `β_c * c` with `c = (1 − ε : ℝ≥0)`, which avoids
carrying the side condition `0 ≤ 1 − ε` inside the statement of every theorem below. -/

/-- **Definition I.1.5, moment form, every natural order, at the actual source model.**

If the loop-safe cutoff kernel is dominated by `c • J` edge by edge, then the `p`-th
cluster moment of `P_{β_c,r}` is at most the `p`-th cluster moment of the *uncut* law at
the reduced parameter `β_c * c`.

Nothing is assumed finite: the inequality holds in `ℝ≥0∞`, so `⊤` is allowed on both
sides. -/
theorem SourceModelData.cutMoment_le_reduced_nnreal (M : SourceModelData) {r : ℝ}
    {c : NNReal} (hdom : ∀ e : Sym2 M.V, M.cutKernel r e ≤ (c : ℝ) * M.kernel e) (p : ℕ) :
    M.cutMoment p r ≤
      ∫⁻ ω, clusterVol ω (0 : M.V) ^ p ∂(M.law (M.betaCrit * c)) := by
  have hce : ∀ e : Sym2 M.V,
      bernoulliEdgeProb (M.cutKernel r) (M.cutKernel_nonneg r) M.betaCrit e ≤
        bernoulliEdgeProb M.kernel M.kernel_nonneg (M.betaCrit * c) e := by
    intro e
    refine CutoffDominated.bernoulliEdgeProb_le_of_mul_le (M.cutKernel_nonneg r)
      M.kernel_nonneg ?_
    have h1 : (M.betaCrit : ℝ) * M.cutKernel r e
        ≤ (M.betaCrit : ℝ) * ((c : ℝ) * M.kernel e) :=
      mul_le_mul_of_nonneg_left (hdom e) M.betaCrit.coe_nonneg
    have h2 : (M.betaCrit : ℝ) * ((c : ℝ) * M.kernel e)
        = ((M.betaCrit * c : NNReal) : ℝ) * M.kernel e := by
      rw [NNReal.coe_mul]; ring
    rw [h2] at h1
    exact h1
  simp only [SourceModelData.cutMoment, SourceModelData.cutLaw, SourceModelData.law,
    longRangeMeasure]
  exact lintegral_clusterVol_pow_mono_of_le hce 0 p

/-- The same transport for an arbitrary real order `p ≥ 0`, stated on the law itself
(`M.cutLaw r` rather than `M.cutMoment`). -/
theorem SourceModelData.lintegral_rpow_clusterVol_le_reduced_nnreal (M : SourceModelData)
    {r : ℝ} {c : NNReal} (hdom : ∀ e : Sym2 M.V, M.cutKernel r e ≤ (c : ℝ) * M.kernel e)
    {p : ℝ} (hp : 0 ≤ p) :
    (∫⁻ ω, clusterVol ω (0 : M.V) ^ p ∂(M.cutLaw r)) ≤
      ∫⁻ ω, clusterVol ω (0 : M.V) ^ p ∂(M.law (M.betaCrit * c)) := by
  have hce : ∀ e : Sym2 M.V,
      bernoulliEdgeProb (M.cutKernel r) (M.cutKernel_nonneg r) M.betaCrit e ≤
        bernoulliEdgeProb M.kernel M.kernel_nonneg (M.betaCrit * c) e := by
    intro e
    refine CutoffDominated.bernoulliEdgeProb_le_of_mul_le (M.cutKernel_nonneg r)
      M.kernel_nonneg ?_
    have h1 : (M.betaCrit : ℝ) * M.cutKernel r e
        ≤ (M.betaCrit : ℝ) * ((c : ℝ) * M.kernel e) :=
      mul_le_mul_of_nonneg_left (hdom e) M.betaCrit.coe_nonneg
    have h2 : (M.betaCrit : ℝ) * ((c : ℝ) * M.kernel e)
        = ((M.betaCrit * c : NNReal) : ℝ) * M.kernel e := by
      rw [NNReal.coe_mul]; ring
    rw [h2] at h1
    exact h1
  simp only [SourceModelData.cutLaw, SourceModelData.law, longRangeMeasure]
  exact lintegral_clusterVol_rpow_mono_of_le hce 0 hp

/-- The first-moment form in the `cutMassAt` vocabulary: `E_{β_c,r}|K_0|` is at most the
uncut first moment at the reduced parameter. -/
theorem SourceModelData.cutMassAt_le_reduced_nnreal (M : SourceModelData) {r : ℝ}
    {c : NNReal} (hdom : ∀ e : Sym2 M.V, M.cutKernel r e ≤ (c : ℝ) * M.kernel e) :
    M.cutMassAt r 0 ≤
      ∫⁻ ω, clusterVol ω (0 : M.V) ∂(M.law (M.betaCrit * c)) := by
  rw [M.cutMassAt_zero_eq_cutMoment]
  simpa only [pow_one] using M.cutMoment_le_reduced_nnreal hdom 1

/-- **Finiteness transfer at every natural order.**  A single finite moment of the uncut
law at the reduced parameter bounds the whole cutoff moment. -/
theorem SourceModelData.cutMoment_ne_top_of_reduced_nnreal (M : SourceModelData) {r : ℝ}
    {c : NNReal} (hdom : ∀ e : Sym2 M.V, M.cutKernel r e ≤ (c : ℝ) * M.kernel e) (p : ℕ)
    (hfin : (∫⁻ ω, clusterVol ω (0 : M.V) ^ p ∂(M.law (M.betaCrit * c))) ≠ ⊤) :
    M.cutMoment p r ≠ ⊤ :=
  ne_top_of_le_ne_top hfin (M.cutMoment_le_reduced_nnreal hdom p)

/-- The first-moment finiteness transfer, in the `cutMassAt` vocabulary. -/
theorem SourceModelData.cutMassAt_ne_top_of_reduced_nnreal (M : SourceModelData) {r : ℝ}
    {c : NNReal} (hdom : ∀ e : Sym2 M.V, M.cutKernel r e ≤ (c : ℝ) * M.kernel e)
    (hfin : (∫⁻ ω, clusterVol ω (0 : M.V) ∂(M.law (M.betaCrit * c))) ≠ ⊤) :
    M.cutMassAt r 0 ≠ ⊤ :=
  ne_top_of_le_ne_top hfin (M.cutMassAt_le_reduced_nnreal hdom)

/-! ## 2. The coefficient supplied by the attained lattice minimum

`exists_epsilon_domination` gives `ε = ε(r)`, hence `c = 1 − ε(r)`, for each `r > 0`.
This section restates that supply in the `c`-vocabulary used above; it is a repackaging
of the landed strict domination, not a new domination proof.

The single difference from `exists_epsilon_domination` is cosmetic: the side condition
`0 ≤ 1 − ε` is absorbed into the `ℝ≥0` coefficient. -/

/-- **Definition I.1.5 at the actual source model, coefficient form.**  For every `r > 0`
there is `c : ℝ≥0` with `0 < c < 1` and `J_r ≤ c · J` at every unordered pair, loops
included.  (`c = 1 − min (1/2) (K r / (2 K t₀))` with `t₀` the attained nonzero lattice
minimum.) -/
theorem SourceModelData.exists_reduced_coefficient (M : SourceModelData) {r : ℝ}
    (hr : 0 < r) :
    ∃ c : NNReal, 0 < (c : ℝ) ∧ (c : ℝ) < 1 ∧
      ∀ e : Sym2 M.V, M.cutKernel r e ≤ (c : ℝ) * M.kernel e := by
  obtain ⟨t0, ht0, _hat, hlat⟩ := M.exists_attained_lattice_min
  have hKr : 0 < M.K r := M.K_pos hr
  have hKt0 : 0 < M.K t0 := M.K_pos ht0
  have hε0 : 0 < min (1 / 2) (M.K r / (2 * M.K t0)) :=
    lt_min (by norm_num) (div_pos hKr (by linarith))
  have hε1 : min (1 / 2) (M.K r / (2 * M.K t0)) < 1 :=
    lt_of_le_of_lt (min_le_left _ _) (by norm_num)
  refine ⟨NNReal.mk (1 - min (1 / 2) (M.K r / (2 * M.K t0))) (by linarith), ?_, ?_, ?_⟩
  · rw [NNReal.coe_mk]; linarith
  · rw [NNReal.coe_mk]; linarith
  · intro e
    rw [NNReal.coe_mk]
    exact M.cutKernel_le_scaled ht0 hr hlat e

/-- **The `ε`-form of Definition I.1.5, moment shape.**  Same content as
`exists_reduced_coefficient`, with the reduced parameter displayed as `(1 − ε) β_c`. -/
theorem SourceModelData.cutMoment_le_reduced (M : SourceModelData) {r ε : ℝ}
    (hε0 : 0 ≤ ε) (hε1 : ε ≤ 1)
    (hdom : ∀ e : Sym2 M.V, M.cutKernel r e ≤ (1 - ε) * M.kernel e) (p : ℕ) :
    M.cutMoment p r ≤
      ∫⁻ ω, clusterVol ω (0 : M.V) ^ p
        ∂(M.law (M.betaCrit * NNReal.mk (1 - ε) (by linarith))) := by
  refine M.cutMoment_le_reduced_nnreal ?_ p
  intro e
  rw [NNReal.coe_mk]
  exact hdom e

/-! ## 2'. Loops

The `SourceNormData` kernel `radialSym` is loop-safe *by definition*: the diagonal
`Sym2.diag x = s(x,x)` is assigned `0` outright, so neither `M.kernel` nor `M.cutKernel`
needs a hypothesis `K 0 = 0` — unlike the raw sup-norm interface, whose
`kernelJ (K ∘ ‖·‖_∞)` must carry `hK0 : K 0 = 0` throughout `CutoffDominated.lean`.
The domination `J_r ≤ c · J` therefore holds at loops for free (`0 ≤ c · 0`), and the
coefficient theorems above spend no hypothesis on them. -/

/-- The loop-safe cutoff kernel vanishes on the diagonal, with no hypothesis on `K 0`. -/
theorem SourceModelData.cutKernel_diag (M : SourceModelData) (r : ℝ) (x : M.V) :
    M.cutKernel r s(x, x) = 0 := by
  rw [SourceModelData.cutKernel, cutRadialSym, radialSym_mk]
  simp

/-- The uncut kernel vanishes on the diagonal, with no hypothesis on `K 0`. -/
theorem SourceModelData.kernel_diag (M : SourceModelData) (x : M.V) :
    M.kernel s(x, x) = 0 := by
  rw [SourceModelData.kernel, radialSym_mk]
  simp

/-- Consequently the domination used in §1 holds at the diagonal for every coefficient,
so `exists_reduced_coefficient` and `exists_uniform_reduced_coefficient` only ever need
the off-diagonal pairs. -/
theorem SourceModelData.cutKernel_diag_le (M : SourceModelData) (r : ℝ) (c : NNReal)
    (x : M.V) : M.cutKernel r s(x, x) ≤ (c : ℝ) * M.kernel s(x, x) := by
  rw [M.cutKernel_diag r x, M.kernel_diag x, mul_zero]

/-! ## 3. One coefficient for a whole window of cutoffs

The pointwise profile is `cutoffProfile K r s = K s − K r` for `s ≤ r` and `0` beyond, so
the inequality `ε · K s ≤ K r` that makes the domination strict only needs `K s ≤ K t₀`
and `K r ≥ K R` for `r ≤ R`.  Both hold by antitonicity, uniformly in `r ∈ (0, R]`, so a
single coefficient — hence a single subcritical parameter — controls every cutoff in the
window. -/

/-- The analytic window lemma: `cutRadialSym_le_scaled` with `K r` replaced by the
*window lower bound* `K R`, valid for every `0 < r ≤ R` simultaneously. -/
theorem cutRadialSym_le_scaled_of_le {d : ℕ} (S : SourceNormData d) {K : ℝ → ℝ}
    (hK : AntitoneOn K (Set.Ioi 0)) (hKnn : ∀ s : ℝ, 0 < s → 0 ≤ K s)
    {t0 R r : ℝ} (ht0 : 0 < t0) (hR : 0 < R) (hr0 : 0 < r) (hrR : r ≤ R)
    (hKR : 0 < K R) (hKt0 : 0 < K t0)
    (hlat : ∀ v : Fin d → ℤ, v ≠ 0 → t0 ≤ S.ρ (toVec v)) (e : Sym2 (Fin d → ℤ)) :
    cutRadialSym S K r e ≤ (1 - min (1 / 2) (K R / (2 * K t0))) * radialSym S K e := by
  have hcoef : (0 : ℝ) ≤ 1 - min (1 / 2) (K R / (2 * K t0)) := by
    have h : min (1 / 2) (K R / (2 * K t0)) ≤ 1 / 2 := min_le_left _ _
    linarith
  induction e using Sym2.ind with
  | _ x y =>
    rw [cutRadialSym, radialSym_mk, radialSym_mk]
    by_cases hxy : x = y
    · rw [ite_eq_left hxy, ite_eq_left hxy]
      simp
    · rw [ite_eq_right hxy, ite_eq_right hxy]
      set s : ℝ := S.dist x y with hsdef
      have hspos : 0 < s := S.dist_pos hxy
      have hst0 : t0 ≤ s := by
        have h := hlat (x - y) (sub_ne_zero.mpr hxy)
        simpa [hsdef, SourceNormData.dist] using h
      rcases le_or_gt s r with hsr | hrs
      · rw [cutoffProfile_of_le hsr]
        have hKs : K s ≤ K t0 := hK (Set.mem_Ioi.mpr ht0) (Set.mem_Ioi.mpr hspos) hst0
        have hKsr : K R ≤ K r := hK (Set.mem_Ioi.mpr hr0) (Set.mem_Ioi.mpr hR) hrR
        have hle : min (1 / 2) (K R / (2 * K t0)) ≤ K R / (2 * K t0) := min_le_right _ _
        have hfrac : (0 : ℝ) ≤ K R / (2 * K t0) := div_nonneg hKR.le (by linarith)
        have hεK : min (1 / 2) (K R / (2 * K t0)) * K s ≤ K r := by
          have h1 : min (1 / 2) (K R / (2 * K t0)) * K s
              ≤ (K R / (2 * K t0)) * K t0 :=
            mul_le_mul hle hKs (hKnn s hspos) hfrac
          have h2 : (K R / (2 * K t0)) * K t0 = K R / 2 := by
            field_simp
          linarith
        nlinarith
      · rw [cutoffProfile_of_lt hrs]
        exact mul_nonneg hcoef (hKnn s hspos)

/-- The window lemma for the genuine source-model cutoff kernel. -/
theorem SourceModelData.cutKernel_le_scaled_of_le (M : SourceModelData) {t0 R r : ℝ}
    (ht0 : 0 < t0) (hR : 0 < R) (hr0 : 0 < r) (hrR : r ≤ R)
    (hlat : ∀ v : M.V, v ≠ 0 → t0 ≤ M.S.dist v 0) (e : Sym2 M.V) :
    M.cutKernel r e ≤ (1 - min (1 / 2) (M.K R / (2 * M.K t0))) * M.kernel e :=
  cutRadialSym_le_scaled_of_le M.S M.K_antitone M.K_nonneg ht0 hR hr0 hrR
    (M.K_pos hR) (M.K_pos ht0) (fun v hv => by
      have h := hlat v hv
      simpa [SourceNormData.dist, toVec] using h) e

/-- **A single reduced parameter for the window `(0, R]`.**  There is `c : ℝ≥0` with
`0 < c < 1` and `J_r ≤ c · J` at every pair, simultaneously for every cutoff
`0 < r ≤ R`. -/
theorem SourceModelData.exists_uniform_reduced_coefficient (M : SourceModelData) {R : ℝ}
    (hR : 0 < R) :
    ∃ c : NNReal, 0 < (c : ℝ) ∧ (c : ℝ) < 1 ∧
      ∀ r : ℝ, 0 < r → r ≤ R → ∀ e : Sym2 M.V, M.cutKernel r e ≤ (c : ℝ) * M.kernel e := by
  obtain ⟨t0, ht0, _hat, hlat⟩ := M.exists_attained_lattice_min
  have hKR : 0 < M.K R := M.K_pos hR
  have hKt0 : 0 < M.K t0 := M.K_pos ht0
  have hε0 : 0 < min (1 / 2) (M.K R / (2 * M.K t0)) :=
    lt_min (by norm_num) (div_pos hKR (by linarith))
  have hε1 : min (1 / 2) (M.K R / (2 * M.K t0)) < 1 :=
    lt_of_le_of_lt (min_le_left _ _) (by norm_num)
  refine ⟨NNReal.mk (1 - min (1 / 2) (M.K R / (2 * M.K t0))) (by linarith), ?_, ?_, ?_⟩
  · rw [NNReal.coe_mk]; linarith
  · rw [NNReal.coe_mk]; linarith
  · intro r hr0 hrR e
    rw [NNReal.coe_mk]
    exact M.cutKernel_le_scaled_of_le ht0 hR hr0 hrR hlat e

/-- **One subcritical moment bounds a whole window of cutoff moments.**  For every
natural order `p` and every `r ∈ (0, R]`, `E_{β_c,r}|K_0|^p` is at most the `p`-th uncut
moment at the single reduced parameter `β_c · c_R`. -/
theorem SourceModelData.cutMoment_le_reduced_uniform_window (M : SourceModelData) {R : ℝ}
    (hR : 0 < R) (p : ℕ) :
    ∃ c : NNReal, 0 < (c : ℝ) ∧ (c : ℝ) < 1 ∧
      ∀ r : ℝ, 0 < r → r ≤ R →
        M.cutMoment p r ≤ ∫⁻ ω, clusterVol ω (0 : M.V) ^ p ∂(M.law (M.betaCrit * c)) := by
  obtain ⟨c, hc0, hc1, hdom⟩ := M.exists_uniform_reduced_coefficient hR
  exact ⟨c, hc0, hc1, fun r hr0 hrR => M.cutMoment_le_reduced_nnreal (hdom r hr0 hrR) p⟩

/-- **Finiteness of every cutoff moment on a window, from one subcritical moment.**
This is the finite-window form of `hutchcroft.i.1.5.step.cutoffmoments`: for `r ∈ (0,R]`
the cutoff moment at order `p` is finite as soon as the *uncut* `p`-th moment at the
single parameter `β_c · c_R < β_c` is.  No critical moment is assumed. -/
theorem SourceModelData.cutMoment_ne_top_uniform_window (M : SourceModelData) {R : ℝ}
    (hR : 0 < R) (p : ℕ) :
    ∃ c : NNReal, 0 < (c : ℝ) ∧ (c : ℝ) < 1 ∧
      ((∫⁻ ω, clusterVol ω (0 : M.V) ^ p ∂(M.law (M.betaCrit * c))) ≠ ⊤ →
        ∀ r : ℝ, 0 < r → r ≤ R → M.cutMoment p r ≠ ⊤) := by
  obtain ⟨c, hc0, hc1, hle⟩ := M.cutMoment_le_reduced_uniform_window hR p
  exact ⟨c, hc0, hc1, fun hfin r hr0 hrR =>
    ne_top_of_le_ne_top hfin (hle r hr0 hrR)⟩

/-- The same for the first moment, in the `cutMassAt` vocabulary. -/
theorem SourceModelData.cutMassAt_ne_top_uniform_window (M : SourceModelData) {R : ℝ}
    (hR : 0 < R) :
    ∃ c : NNReal, 0 < (c : ℝ) ∧ (c : ℝ) < 1 ∧
      ((∫⁻ ω, clusterVol ω (0 : M.V) ∂(M.law (M.betaCrit * c))) ≠ ⊤ →
        ∀ r : ℝ, 0 < r → r ≤ R → M.cutMassAt r 0 ≠ ⊤) := by
  obtain ⟨c, hc0, hc1, hle⟩ := M.cutMoment_le_reduced_uniform_window hR 1
  exact ⟨c, hc0, hc1, fun hfin r hr0 hrR => by
    rw [M.cutMassAt_zero_eq_cutMoment]
    exact ne_top_of_le_ne_top hfin (by simpa only [pow_one] using hle r hr0 hrR)⟩

/-! ## 4. From subcritical first-moment finiteness to all cutoff masses

`c(r) = 1 − ε(r) < 1` for every `r > 0`, so the reduced parameter `β_c · c(r)` is
*strictly* below `β_c` for every `r`, not merely eventually.  Hence "the uncut mean is
finite at every subcritical parameter" gives finiteness of every cutoff mass at once. -/

/-- **The global finiteness statement.**  If the uncut first moment is finite at every
parameter strictly below `β_c` (and `β_c > 0`), then every cutoff mass at the critical
parameter is finite, for every `r > 0`.

`hsub` is a genuine premise: it is *not* a consequence of `θ_β = 0`
(`RayRefutation.exists_subcritical_infinite_mean`) and it is strictly weaker than
finiteness at `β_c`, which the campaign does not have. -/
theorem SourceModelData.cutMassAt_ne_top_of_subcritical (M : SourceModelData)
    (hβ : 0 < M.betaCrit)
    (hsub : ∀ β : NNReal, β < M.betaCrit →
      (∫⁻ ω, clusterVol ω (0 : M.V) ∂(M.law β)) ≠ ⊤)
    {r : ℝ} (hr : 0 < r) : M.cutMassAt r 0 ≠ ⊤ := by
  obtain ⟨c, hc0, hc1, hdom⟩ := M.exists_reduced_coefficient hr
  have hlt : M.betaCrit * c < M.betaCrit := by
    have h : M.betaCrit * c < M.betaCrit * 1 :=
      mul_lt_mul_of_pos_left (by rwa [← NNReal.coe_lt_coe, NNReal.coe_one]) hβ
    simpa using h
  exact M.cutMassAt_ne_top_of_reduced_nnreal hdom (hsub _ hlt)

/-- The same statement at every natural order: the cutoff `p`-th moment at
`β_c` is finite from subcritical `p`-th moment finiteness of the uncut law.

The reduction of the `p`-th cutoff moment to the *first* uncut moment is not attempted
here; it is stated for the `p`-th uncut moment, which is the exact premise consumed. -/
theorem SourceModelData.cutMoment_ne_top_of_subcritical (M : SourceModelData) (p : ℕ)
    (hβ : 0 < M.betaCrit)
    (hsub : ∀ β : NNReal, β < M.betaCrit →
      (∫⁻ ω, clusterVol ω (0 : M.V) ^ p ∂(M.law β)) ≠ ⊤)
    {r : ℝ} (hr : 0 < r) : M.cutMoment p r ≠ ⊤ := by
  obtain ⟨c, hc0, hc1, hdom⟩ := M.exists_reduced_coefficient hr
  have hlt : M.betaCrit * c < M.betaCrit := by
    have h : M.betaCrit * c < M.betaCrit * 1 :=
      mul_lt_mul_of_pos_left (by rwa [← NNReal.coe_lt_coe, NNReal.coe_one]) hβ
    simpa using h
  exact M.cutMoment_ne_top_of_reduced_nnreal hdom p (hsub _ hlt)

/-- The eventual form directly: the premise `hfin` left open by
`VolumeMoments/FirstMoment/Divergence.lean`. -/
theorem SourceModelData.eventually_cutMassAt_ne_top (M : SourceModelData)
    (hβ : 0 < M.betaCrit)
    (hsub : ∀ β : NNReal, β < M.betaCrit →
      (∫⁻ ω, clusterVol ω (0 : M.V) ∂(M.law β)) ≠ ⊤) :
    ∀ᶠ r : ℝ in atTop, M.cutMassAt r 0 ≠ ⊤ :=
  Filter.eventually_atTop.2
    ⟨1, fun r hr => M.cutMassAt_ne_top_of_subcritical hβ hsub (lt_of_lt_of_le zero_lt_one hr)⟩


/-! ## 5. Monotonicity in the reduced parameter, and hypothesis strength -/

/-- The reduced-parameter moment is at most the critical moment: the transport of
Definition I.1.5 lands at a *strictly* smaller parameter, so its premise is strictly
weaker than finiteness of the critical moment. -/
theorem SourceModelData.lintegral_clusterVol_pow_le_critical (M : SourceModelData)
    {c : NNReal} (hc : c ≤ 1) (p : ℕ) :
    (∫⁻ ω, clusterVol ω (0 : M.V) ^ p ∂(M.law (M.betaCrit * c))) ≤
      ∫⁻ ω, clusterVol ω (0 : M.V) ^ p ∂(M.criticalLaw) := by
  have hbc : M.betaCrit * c ≤ M.betaCrit := by
    simpa using mul_le_mul_of_nonneg_left hc (zero_le (a := M.betaCrit))
  have hce : ∀ e : Sym2 M.V,
      bernoulliEdgeProb M.kernel M.kernel_nonneg (M.betaCrit * c) e ≤
        bernoulliEdgeProb M.kernel M.kernel_nonneg M.betaCrit e :=
    fun e => bernoulliEdgeProb_mono M.kernel M.kernel_nonneg hbc e
  simp only [SourceModelData.law, SourceModelData.criticalLaw, longRangeMeasure]
  exact lintegral_clusterVol_pow_mono_of_le hce 0 p

/-- Hypothesis strength: finiteness of the *critical* first moment implies the premise
`hsub` used above, hence every cutoff mass is finite.  This is recorded only to locate
the premise — the critical mean is `⊤` for the source model
(`I42C.uncutFirstMoment_eq_top_of_rpow_lower`), so this is *not* the campaign's route. -/
theorem SourceModelData.cutMassAt_ne_top_of_critical (M : SourceModelData)
    (hcrit : (∫⁻ ω, clusterVol ω (0 : M.V) ∂(M.criticalLaw)) ≠ ⊤)
    {r : ℝ} (hr : 0 < r) : M.cutMassAt r 0 ≠ ⊤ := by
  obtain ⟨c, _hc0, hc1, hdom⟩ := M.exists_reduced_coefficient hr
  have hcle : c ≤ 1 := by
    rw [← NNReal.coe_le_coe, NNReal.coe_one]
    linarith
  have h1 : (∫⁻ ω, clusterVol ω (0 : M.V) ∂(M.law (M.betaCrit * c))) ≤
      ∫⁻ ω, clusterVol ω (0 : M.V) ∂(M.criticalLaw) := by
    simpa only [pow_one] using M.lintegral_clusterVol_pow_le_critical hcle 1
  exact M.cutMassAt_ne_top_of_reduced_nnreal hdom (ne_top_of_le_ne_top hcrit h1)

/-! ## 6. Closing the `hfin` gap of `VolumeMoments/FirstMoment/Divergence.lean`

The landed `I42C.tendsto_cutMassAt_toReal_atTop` carries an *eventual finiteness*
hypothesis that the file itself records as unproved.  Section 4 supplies it, so the
paper's real-valued `E_{β_c,r}|K| → ∞` (the `hinf` input of Lemma I.4.5(3)) follows from
subcritical first-moment finiteness and the critical-mean divergence
`I42C.uncutFirstMoment_eq_top_of_rpow_lower`. -/

/-- **`E_{β_c,r}|K_0| → ∞` in `ℝ`**, from subcritical first-moment finiteness together
with `E_{β_c}|K_0| = ⊤`. -/
theorem tendsto_cutMassAt_toReal_atTop_of_subcritical (M : SourceModelData)
    (hβ : 0 < M.betaCrit)
    (hsub : ∀ β : NNReal, β < M.betaCrit →
      (∫⁻ ω, clusterVol ω (0 : M.V) ∂(M.law β)) ≠ ⊤)
    (htop : (∫⁻ ω, clusterVol ω (0 : M.V) ∂(M.law M.betaCrit)) = ⊤) :
    Tendsto (fun r : ℝ => (M.cutMassAt r 0).toReal) atTop atTop :=
  PercLib.CriticalLRP.I42C.tendsto_cutMassAt_toReal_atTop M
    (PercLib.CriticalLRP.I42C.tendsto_cutMassAt_atTop_nhds_top M htop)
    (M.eventually_cutMassAt_ne_top hβ hsub)

/-! ## 7. No uniform strict coefficient: why the global statement needs a family

The window theorem of §3 is not an artefact of the proof: for `r → ∞` the coefficient
genuinely has to degenerate to `1`.  The reason is visible on the single edge realising
the attained lattice minimum `t₀`: there `J_r(e) = K t₀ − K r` and `J(e) = K t₀`, so any
uniform `c < 1` would force `K r ≥ (1 − c) K t₀` at every `r`, contradicting
`SourceModelData.tendsto_K_atTop_zero`.

Consequently the *global* finiteness statement `∀ r > 0, M.cutMassAt r 0 ≠ ⊤` cannot be
obtained from a single subcritical parameter, and §4's hypothesis genuinely quantifies
over all `β < β_c`. -/

/-- **No uniform strict reduced coefficient.**  There is no `c : ℝ≥0` with `c < 1` and
`J_r ≤ c · J` at every pair for *every* cutoff `r > 0`; the strict domination necessarily
degenerates as `r → ∞`.  (The non-strict `c = 1` is available but reduces the parameter to
`β_c` itself, which is what the campaign cannot use.) -/
theorem SourceModelData.not_exists_uniform_strict_coefficient (M : SourceModelData) :
    ¬ ∃ c : NNReal, (c : ℝ) < 1 ∧
      ∀ r : ℝ, 0 < r → ∀ e : Sym2 M.V, M.cutKernel r e ≤ (c : ℝ) * M.kernel e := by
  rintro ⟨c, hc, hdom⟩
  obtain ⟨t0, ht0, ⟨v0, hv0, hv0t⟩, _hlat⟩ := M.exists_attained_lattice_min
  have hKt0 : 0 < M.K t0 := M.K_pos ht0
  have hgap : 0 < (1 - (c : ℝ)) * M.K t0 := by
    have h1 : (0 : ℝ) < 1 - (c : ℝ) := by linarith
    exact mul_pos h1 hKt0
  have hev : ∀ᶠ r : ℝ in atTop, M.K r < (1 - (c : ℝ)) * M.K t0 :=
    (tendsto_order.1 M.tendsto_K_atTop_zero).2 _ hgap
  obtain ⟨r, hlt, hr⟩ := (hev.and (eventually_ge_atTop t0)).exists
  have hr0 : 0 < r := lt_of_lt_of_le ht0 hr
  have hck : M.cutKernel r s(v0, 0) = M.K t0 - M.K r := by
    rw [SourceModelData.cutKernel, cutRadialSym, radialSym_mk, ite_eq_right hv0, hv0t,
      cutoffProfile_of_le hr]
  have hker : M.kernel s(v0, 0) = M.K t0 := by
    rw [SourceModelData.kernel, radialSym_mk, ite_eq_right hv0, hv0t]
  have h := hdom r hr0 s(v0, 0)
  rw [hck, hker] at h
  have h2 : (1 - (c : ℝ)) * M.K t0 ≤ M.K r := by linarith
  linarith

/-! ## 8. Non-vacuity of the coefficient theorems

`Witness.sourceModelWitness` inhabits `SourceModelData`, so the coefficient theorems of
§2–§3 are not quantified over an empty type. -/

/-- The coefficient of §2 exists at the concrete witness model: `0 < c < 1` with
`J_1 ≤ c · J` edge by edge. -/
theorem exists_reduced_coefficient_nonvacuous :
    ∃ M : SourceModelData, ∃ c : NNReal, 0 < (c : ℝ) ∧ (c : ℝ) < 1 ∧
      ∀ e : Sym2 M.V, M.cutKernel 1 e ≤ (c : ℝ) * M.kernel e := by
  refine ⟨Witness.sourceModelWitness 1 le_rfl 1 zero_lt_one, ?_⟩
  exact (Witness.sourceModelWitness 1 le_rfl 1 zero_lt_one).exists_reduced_coefficient
    one_pos

end PercLib.CriticalLRP.Orchestration

/-! ## Axiom audit -/

set_option linter.hashCommand false
set_option linter.style.longLine false

#print axioms PercLib.CriticalLRP.Orchestration.SourceModelData.cutMoment_le_reduced_nnreal
#print axioms PercLib.CriticalLRP.Orchestration.SourceModelData.lintegral_rpow_clusterVol_le_reduced_nnreal
#print axioms PercLib.CriticalLRP.Orchestration.SourceModelData.cutMassAt_le_reduced_nnreal
#print axioms PercLib.CriticalLRP.Orchestration.SourceModelData.cutMoment_ne_top_of_reduced_nnreal
#print axioms PercLib.CriticalLRP.Orchestration.SourceModelData.cutMassAt_ne_top_of_reduced_nnreal
#print axioms PercLib.CriticalLRP.Orchestration.SourceModelData.exists_reduced_coefficient
#print axioms PercLib.CriticalLRP.Orchestration.SourceModelData.cutMoment_le_reduced
#print axioms PercLib.CriticalLRP.Orchestration.cutRadialSym_le_scaled_of_le
#print axioms PercLib.CriticalLRP.Orchestration.SourceModelData.cutKernel_le_scaled_of_le
#print axioms PercLib.CriticalLRP.Orchestration.SourceModelData.exists_uniform_reduced_coefficient
#print axioms PercLib.CriticalLRP.Orchestration.SourceModelData.cutMoment_le_reduced_uniform_window
#print axioms PercLib.CriticalLRP.Orchestration.SourceModelData.cutMoment_ne_top_uniform_window
#print axioms PercLib.CriticalLRP.Orchestration.SourceModelData.cutMassAt_ne_top_uniform_window
#print axioms PercLib.CriticalLRP.Orchestration.SourceModelData.cutMassAt_ne_top_of_subcritical
#print axioms PercLib.CriticalLRP.Orchestration.SourceModelData.cutMoment_ne_top_of_subcritical
#print axioms PercLib.CriticalLRP.Orchestration.SourceModelData.eventually_cutMassAt_ne_top
#print axioms PercLib.CriticalLRP.Orchestration.SourceModelData.lintegral_clusterVol_pow_le_critical
#print axioms PercLib.CriticalLRP.Orchestration.SourceModelData.cutMassAt_ne_top_of_critical
#print axioms PercLib.CriticalLRP.Orchestration.tendsto_cutMassAt_toReal_atTop_of_subcritical
#print axioms PercLib.CriticalLRP.Orchestration.SourceModelData.not_exists_uniform_strict_coefficient
#print axioms PercLib.CriticalLRP.Orchestration.exists_reduced_coefficient_nonvacuous
#print axioms PercLib.CriticalLRP.Orchestration.SourceModelData.cutKernel_diag
#print axioms PercLib.CriticalLRP.Orchestration.SourceModelData.kernel_diag
#print axioms PercLib.CriticalLRP.Orchestration.SourceModelData.cutKernel_diag_le
