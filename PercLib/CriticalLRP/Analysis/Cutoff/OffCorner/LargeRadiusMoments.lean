/-
Copyright (c) 2026 PercLib contributors. Released under Apache 2.0 license.

# A7 — the reality check on cutoff moments at large radius

Source: T. Hutchcroft, *Critical long-range percolation I: High effective
dimension*, arXiv:2508.18807v1, Definition I.1.5 and the proof of Lemma I.4.9.

Definition I.1.5 states the cut-off kernel `J_r` and observes: for every
`r < ∞` there is `ε = ε(r) > 0` with `J_r ≤ (1 − ε) J`, so that `P_{β_c,r}` is
stochastically dominated by the subcritical measure `P_{(1−ε)β_c}`.  The proof of
Lemma I.4.9 then uses *sharpness of the phase transition* to know that
`r₀(β) < ∞` for every `β_c/2 ≤ β < β_c`, i.e. that the subcritical mean is
finite at every subcritical parameter.

This file separates what the formalization actually has at large radius from
what it does not.
-/
module

public import PercLib.CriticalLRP.MomentMonotonicity.Temperature
public import PercLib.CriticalLRP.MomentMonotonicity.ReducedMomentTransfer
public import PercLib.CriticalLRP.MomentMonotonicity.SourceModelCutoffLimit
public import PercLib.CriticalLRP.Correlation.FourthMoment.Bridge
public import PercLib.CriticalLRP.Correlation.FourthMoment.MixedK2.Transport
public import PercLib.CriticalLRP.Analysis.KernelPower.Model
public import PercLib.CriticalLRP.Analysis.Cutoff.OffCorner.PowerLawContinuity
public import PercLib.CriticalLRP.SharpnessInput

/-!
# Large-radius cutoff moments at the actual source model

The landed `MomentMonotonicity/ReducedMomentTransfer.lean` transfers the
`p`-th cutoff moment at `β_c` to the `p`-th *uncut* moment at a strictly reduced
parameter `β_c · c(r)`, and `MomentMonotonicity/Temperature.lean` passes an a
priori bound on `[β_c/2, β_c)` to `β_c`.  Neither file reduces the order: the
`p`-th transfer consumes the `p`-th subcritical moment.

The contents below are the two pieces that are genuinely available at an
arbitrary (large) radius, and the precise shape of the input that is not.

* §1 the translation invariance of the source two-point function needed by the
  generic tree expansion;
* §2 finite susceptibility ⇒ finite fourth moment at the *uncut* source law,
  hence (because `|K_x| ≥ 1` so `|K_x|^p ≤ |K_x|^4` for `p ≤ 4`) every cutoff
  moment of order `p ≤ 4` is finite at **every** `r > 0`, from finiteness of the
  uncut first moment at every subcritical parameter;
* §3 the same subcritical first-moment hypothesis gives the per-`β` a priori
  bound `E_{β,r}|K| ≤ (2α/β) r^α` for `r ≥ r₀(β)` with the explicit threshold
  `r₀(β) = max 1 ((χ_β / (2α/β))^(1/α))` — this is exactly the consequence the
  source attributes to sharpness of the phase transition;
* §4 the moment bounds must degenerate: with `E_{β_c}|K|^p = ⊤` the cutoff
  moments converge to `⊤`, so there is no uniform finite bound in `r` — finiteness
  at each fixed `r` is not the content of the paper, the `r^{(2p−1)α}` rate is;
* §5 the sharpness-conditional derivative wrapper: at the literal power-law
  witness, subcritical first-moment finiteness alone supplies the finite first
  cutoff moment at a strictly larger radius that the landed off-corner
  derivative theorem consumes, so the paper's derivative holds at every
  off-corner radius with no moment hypothesis left.

## What is *not* claimed

No subcritical first-moment finiteness is produced: `θ_β = 0` does not imply it
(`RayRefutation.exists_subcritical_infinite_mean` is a Lean-checked
counterexample in this framework), and it is not implied by finiteness of the
critical mean.  No uniform-in-`β` threshold on `[β_c/2, β_c)` is derived from the
per-`β` thresholds of §3, so the passage to `β_c` of
`MomentMonotonicity/Temperature.lean` still needs the uniform a priori bound as
a hypothesis.  Nothing here proves the paper's asymptotic ODE or the moment
asymptotics of Theorem I.1.6.
-/

set_option autoImplicit false
set_option linter.unusedSectionVars false
set_option linter.style.longLine false

open MeasureTheory Measure Filter Topology Set
open scoped ENNReal NNReal Topology

@[expose] public section

namespace PercLib.CriticalLRP.Orchestration

open PercLib.CriticalLRP FiniteVolume

/-! ## 1. Translation invariance of the source two-point function

The generic fourth-moment tree expansion of
`Correlation/FourthMoment/Bridge.lean` is stated for an arbitrary edge parameter
`π` on an additive countable vertex type and consumes translation invariance of
`τ_π`.  For the source model this is `M.kernel ∘ (· + a) = M.kernel`, which is
`KernelPower/Model.lean`'s `kernel_shift`. -/

/-- **Simultaneous translation of both endpoints does not change the edge
probability of the source model.** -/
theorem SourceModelData.bernoulliEdgeProb_translate (M : SourceModelData) (β : ℝ≥0)
    (x y g : M.V) :
    bernoulliEdgeProb M.kernel M.kernel_nonneg β s(x + g, y + g) =
      bernoulliEdgeProb M.kernel M.kernel_nonneg β s(x, y) := by
  have h := bernoulliEdgeProb_shift (J := M.kernel) (fun a e => M.kernel_shift a e)
    M.kernel_nonneg β g s(x, y)
  simpa only [Sym2.map_mk] using h

/-- **Translation invariance of the source two-point function**, in the exact
form `∀ a b, τ a b = τ 0 (b - a)` consumed by the generic tree-moment bounds. -/
theorem SourceModelData.tau_hinv (M : SourceModelData) (β : ℝ≥0) :
    ∀ a b : M.V,
      PercLib.Percolation.Bond.tau (bernoulliEdgeProb M.kernel M.kernel_nonneg β) a b
        = PercLib.Percolation.Bond.tau (bernoulliEdgeProb M.kernel M.kernel_nonneg β) 0
            (b - a) :=
  TreeExpansion.FivePoint.tau_hinv (bernoulliEdgeProb M.kernel M.kernel_nonneg β)
    (fun x y g => M.bernoulliEdgeProb_translate β x y g)

/-! ## 2. Finite fourth moment at the uncut source law

The tree-graph inequality gives `E|K|^4 ≤ 15 (E|K|)^7` (the `15` comb shapes of
`Correlation/FourthMoment/Bridge.lean`).  Since the cluster of the origin always
contains the origin, `|K_x| ≥ 1`, so this one bound covers every order `p ≤ 4`. -/

/-- **Finite susceptibility gives a finite fourth cluster moment at the uncut
source law.**  This is the generic native fourth-moment bound applied to the
actual source kernel through `M.tau_hinv`; no cutoff is involved. -/
theorem SourceModelData.uncutMoment_four_ne_top_of_first (M : SourceModelData)
    {β : ℝ≥0} (h1 : (∫⁻ ω, clusterVol ω (0 : M.V) ∂(M.law β)) ≠ ⊤) :
    (∫⁻ ω, clusterVol ω (0 : M.V) ^ 4 ∂(M.law β)) ≠ ⊤ := by
  have hbridge := TreeExpansion.FivePoint.fourth_moment_le
    (π := bernoulliEdgeProb M.kernel M.kernel_nonneg β) (M.tau_hinv β)
  have hlaw : M.law β
      = PercLib.Percolation.Bond.law (bernoulliEdgeProb M.kernel M.kernel_nonneg β) := rfl
  rw [hlaw] at h1 ⊢
  simp only [Percolation.cardFun_eq_encard] at hbridge ⊢
  exact ne_top_of_le_ne_top
    (ENNReal.mul_ne_top (by norm_num) (ENNReal.pow_ne_top h1)) hbridge

/-- The comparison of orders: at every configuration `|K_x| ≥ 1`, so the `p`-th
moment of the cluster volume is at most its fourth moment for `p ≤ 4`. -/
theorem SourceModelData.lintegral_pow_le_four (M : SourceModelData) {β : ℝ≥0} {p : ℕ}
    (hp : p ≤ 4) :
    (∫⁻ ω, clusterVol ω (0 : M.V) ^ p ∂(M.law β)) ≤
      ∫⁻ ω, clusterVol ω (0 : M.V) ^ 4 ∂(M.law β) :=
  lintegral_mono fun ω => pow_le_pow_right₀ (SourceModelData.one_le_clusterVol ω 0) hp

/-- **Every cutoff moment of order `p ≤ 4` is finite at every fixed cutoff
radius, from subcritical first-moment finiteness alone.**

`hsub` is the formal counterpart of the sentence "noting that `r₀(β)` is finite
for every `β_c/2 ≤ β < β_c` by sharpness of the phase transition" in the proof
of Lemma I.4.9.  No uniformity in `β` and nothing at `β_c` is assumed. -/
theorem SourceModelData.cutMoment_ne_top_of_subcritical_first (M : SourceModelData)
    (hβ : 0 < M.betaCrit)
    (hsub : ∀ β : ℝ≥0, β < M.betaCrit →
      (∫⁻ ω, clusterVol ω (0 : M.V) ∂(M.law β)) ≠ ⊤)
    {p : ℕ} (hp : p ≤ 4) {r : ℝ} (hr : 0 < r) : M.cutMoment p r ≠ ⊤ := by
  refine M.cutMoment_ne_top_of_subcritical p hβ (fun β hβlt => ?_) hr
  exact ne_top_of_le_ne_top
    (M.uncutMoment_four_ne_top_of_first (hsub β hβlt)) (M.lintegral_pow_le_four hp)

/-- **Orders `p ≤ 4` at one cutoff radius, from one reduced intensity.**

This is the "reduced intensity" form of the target: the reduced coefficient `c`
is whatever Definition I.1.5 supplies at this radius (`exists_reduced_coefficient`
produces one with `c < 1`), and the only moment hypothesis is finiteness of the
*first* uncut moment at the reduced parameter `β_c · c`.  The fourth moment at
that same parameter comes from the tree-graph inequality, and `|K_x| ≥ 1` carries
it down to every order `p ≤ 4`. -/
theorem SourceModelData.cutMoment_ne_top_le_four_of_reduced_first (M : SourceModelData)
    {r : ℝ} {c : NNReal}
    (hdom : ∀ e : Sym2 M.V, M.cutKernel r e ≤ (c : ℝ) * M.kernel e)
    (hfin : (∫⁻ ω, clusterVol ω (0 : M.V) ∂(M.law (M.betaCrit * c))) ≠ ⊤)
    {p : ℕ} (hp : p ≤ 4) : M.cutMoment p r ≠ ⊤ := by
  have h4 := M.uncutMoment_four_ne_top_of_first hfin
  refine ne_top_of_le_ne_top ?_ (M.cutMoment_le_reduced_nnreal hdom p)
  exact ne_top_of_le_ne_top h4 (M.lintegral_pow_le_four hp)

/-- **The same statement with the reduced coefficient existentially quantified**:
for every cutoff radius at which some strict reduced coefficient is available (all
`r > 0`, by `exists_reduced_coefficient`), first-moment finiteness at the
corresponding reduced parameter bounds every cutoff moment of order `p ≤ 4`. -/
theorem SourceModelData.cutMoment_ne_top_le_four_of_exists_reduced (M : SourceModelData)
    {r : ℝ} {p : ℕ} (hp : p ≤ 4)
    (h : ∃ c : NNReal, (∀ e : Sym2 M.V, M.cutKernel r e ≤ (c : ℝ) * M.kernel e) ∧
      (∫⁻ ω, clusterVol ω (0 : M.V) ∂(M.law (M.betaCrit * c))) ≠ ⊤) :
    M.cutMoment p r ≠ ⊤ := by
  obtain ⟨c, hdom, hfin⟩ := h
  exact M.cutMoment_ne_top_le_four_of_reduced_first hdom hfin hp

/-! ## 3. The per-`β` a priori bound of Lemma I.4.9

At a fixed subcritical `β`, the cutoff mean is dominated by the uncut mean at the
*same* `β` (`cutMassAtBeta_le_law`), and the latter is a constant.  Hence the
threshold needed for `E_{β,r}|K| ≤ (2α/β) r^α` is explicit.  What the source's
bootstrap then needs is a *uniform* threshold on `[β_c/2, β_c)`, and that is not
derived here. -/

/-- **The sharpness consequence used by the proof of Lemma I.4.9, at one fixed
subcritical intensity.**  From a finite uncut mean at `β` one gets the a priori
bound at that `β` for every `r` beyond the explicit threshold
`max 1 ((χ_β / (2α/β))^(1/α))`. -/
theorem SourceModelData.exists_threshold_cutMassAtBeta_le_two_alpha (M : SourceModelData)
    {β : ℝ≥0} (hβ0 : 0 < β)
    (hχ : (∫⁻ ω, clusterVol ω (0 : M.V) ∂(M.law β)) ≠ ⊤) :
    ∀ r : ℝ, max 1
        (((∫⁻ ω, clusterVol ω (0 : M.V) ∂(M.law β)).toReal / (2 * M.α / (β : ℝ)))
          ^ (1 / M.α)) ≤ r →
      M.cutMassAtBeta β r 0 ≤ ENNReal.ofReal ((2 * M.α / (β : ℝ)) * r ^ M.α) := by
  intro r hr
  have hβr : (0 : ℝ) < (β : ℝ) := by exact_mod_cast hβ0
  have hαpos : 0 < M.α := M.hα
  have hc : 0 < 2 * M.α / (β : ℝ) := by positivity
  have hr1 : (1 : ℝ) ≤ r := le_trans (le_max_left _ _) hr
  have hr0 : (0 : ℝ) ≤ r := le_trans zero_le_one hr1
  have hle := M.cutMassAtBeta_le_law (β := β) hr0 0
  have hne : M.cutMassAtBeta β r 0 ≠ ⊤ := ne_top_of_le_ne_top hχ hle
  have hF : ∀ s : ℝ, M.cutMassAtBeta β (max s 1) 0
      ≤ ∫⁻ ω, clusterVol ω (0 : M.V) ∂(M.law β) := fun s =>
    M.cutMassAtBeta_le_law (β := β) (le_trans zero_le_one (le_max_right s 1)) 0
  have hbound := PercLib.CriticalLRP.eventual_rpow_bound_of_le
    (F := fun s : ℝ => M.cutMassAtBeta β (max s 1) 0)
    (χ := ∫⁻ ω, clusterVol ω (0 : M.V) ∂(M.law β)) M.hα hβr hχ hF r hr
  rw [max_eq_left hr1] at hbound
  refine (le_ofReal_iff_toReal (mul_nonneg hc.le (Real.rpow_nonneg hr0 _))).mpr
    ⟨hne, hbound⟩

/-! ## 4. Large `r` is where the bounds must degenerate

The cutoff moments increase to the uncut critical moment
(`SourceModelCutoffLimit.lean`).  So once the critical moment is infinite, the
cutoff moments are finite at every fixed `r` but tend to `⊤`: there is no uniform
finite bound, and no argument from finite boxes or from small radii can supply the
paper's rate. -/

/-- **Cutoff moments tend to `⊤` when the critical uncut moment is `⊤`.** -/
theorem SourceModelData.tendsto_cutMoment_atTop_top (M : SourceModelData) (p : ℕ)
    (h : (∫⁻ ω, clusterVol ω (0 : M.V) ^ p ∂(M.criticalLaw)) = ⊤) :
    Tendsto (fun r : ℝ => M.cutMoment p r) atTop (𝓝 ⊤) := by
  have hT := M.tendsto_cutMoment p
  have hcrit : (∫⁻ ω, clusterVol ω (0 : M.V) ^ p ∂(M.law M.betaCrit)) = ⊤ := by
    simpa only [SourceModelData.criticalLaw] using h
  rwa [hcrit] at hT

/-- **No uniform finite bound on the cutoff moments** when the critical uncut
moment is `⊤`.  (Equivalently, `E_{β_c,r}|K|^p` is finite for each `r` and
unbounded in `r`; cf. `cutMoment_ne_top_of_subcritical_first`.) -/
theorem SourceModelData.not_exists_uniform_cutMoment_bound (M : SourceModelData) (p : ℕ)
    (h : (∫⁻ ω, clusterVol ω (0 : M.V) ^ p ∂(M.criticalLaw)) = ⊤) :
    ¬ ∃ C : ℝ≥0∞, C ≠ ⊤ ∧ ∀ r : ℝ, M.cutMoment p r ≤ C := by
  rintro ⟨C, hC, hle⟩
  exact M.uncutMoment_ne_top_of_forall_cutMoment_le p C hC hle h

/-- The fourth moment is infinite whenever the first is: `|K_x| ≥ 1` makes the
first moment a lower bound for the fourth.  Consequently, from a divergent
critical mean, *every* order `p ≥ 1` cutoff moment diverges as `r → ∞`. -/
theorem SourceModelData.tendsto_cutMoment_atTop_top_of_first_eq_top (M : SourceModelData)
    {p : ℕ} (hp : 1 ≤ p)
    (h : (∫⁻ ω, clusterVol ω (0 : M.V) ∂(M.criticalLaw)) = ⊤) :
    Tendsto (fun r : ℝ => M.cutMoment p r) atTop (𝓝 ⊤) := by
  refine M.tendsto_cutMoment_atTop_top p ?_
  have hle : (∫⁻ ω, clusterVol ω (0 : M.V) ∂(M.criticalLaw))
      ≤ ∫⁻ ω, clusterVol ω (0 : M.V) ^ p ∂(M.criticalLaw) := by
    simpa only [pow_one] using
      (lintegral_mono (μ := M.criticalLaw) fun ω =>
        pow_le_pow_right₀ (SourceModelData.one_le_clusterVol ω 0) hp)
  exact (le_antisymm (h ▸ hle) le_top).symm

/-! ## 5. The sharpness-conditional derivative wrapper at the witness

`OffCorner/PowerLawContinuity.lean` proves, at the literal power-law witness, the
paper's off-corner derivative from a finite first cutoff moment at a strictly
larger radius.  §2 above supplies that finite moment at *every* radius from
subcritical first-moment finiteness, so the derivative at an arbitrary off-corner
radius carries no moment hypothesis any more.  What remains is exactly the
sharpness hypothesis `hsub` (and `β_c > 0`). -/

/-- **The paper's cutoff-mass derivative at every off-corner radius, conditional
only on sharpness.**

`hsub` is the pointwise subcritical first-moment finiteness of Definition I.1.5
(the input the source calls sharpness of the phase transition); `hβ` records that
the critical parameter is positive.  No cutoff-moment finiteness at any radius is
assumed: `cutMassAt_ne_top_of_subcritical` produces it. -/
theorem Witness.sourceModelWitness_hasDerivAt_cutMassReal_powerLaw_of_subcritical
    (d : ℕ) (hd : 1 ≤ d) (α : ℝ) (hα : 0 < α)
    (hβ : 0 < (sourceModelWitness d hd α hα).betaCrit)
    (hsub : ∀ β : ℝ≥0, β < (sourceModelWitness d hd α hα).betaCrit →
      (∫⁻ ω, clusterVol ω (0 : (sourceModelWitness d hd α hα).V)
        ∂((sourceModelWitness d hd α hα).law β)) ≠ ⊤)
    {r0 : ℝ} (hr0 : 0 < r0)
    (hoff : r0 ∉ (sourceModelWitness d hd α hα).cornerRadii) :
    HasDerivAt (sourceModelWitness d hd α hα).cutMassReal
      (((sourceModelWitness d hd α hα).betaCrit : ℝ) * r0 ^ (-(d : ℝ) - α - 1) *
        (sourceModelWitness d hd α hα).exclScalar r0) r0 := by
  have h1R : (sourceModelWitness d hd α hα).cutMoment 1 (r0 + 1) ≠ ⊤ := by
    rw [← SourceModelData.cutMassAt_zero_eq_cutMoment]
    exact SourceModelData.cutMassAt_ne_top_of_subcritical _ hβ hsub (by linarith)
  exact sourceModelWitness_hasDerivAt_cutMassReal_powerLaw_of_firstMoment d hd α hα
    hr0 (by linarith) hoff h1R

end PercLib.CriticalLRP.Orchestration

/-! ## Axiom audit (every new theorem) -/

set_option linter.hashCommand false
set_option linter.style.longLine false

#print axioms PercLib.CriticalLRP.Orchestration.SourceModelData.bernoulliEdgeProb_translate
#print axioms PercLib.CriticalLRP.Orchestration.SourceModelData.tau_hinv
#print axioms PercLib.CriticalLRP.Orchestration.SourceModelData.uncutMoment_four_ne_top_of_first
#print axioms PercLib.CriticalLRP.Orchestration.SourceModelData.lintegral_pow_le_four
#print axioms PercLib.CriticalLRP.Orchestration.SourceModelData.cutMoment_ne_top_of_subcritical_first
#print axioms PercLib.CriticalLRP.Orchestration.SourceModelData.cutMoment_ne_top_le_four_of_reduced_first
#print axioms PercLib.CriticalLRP.Orchestration.SourceModelData.cutMoment_ne_top_le_four_of_exists_reduced
#print axioms PercLib.CriticalLRP.Orchestration.SourceModelData.exists_threshold_cutMassAtBeta_le_two_alpha
#print axioms PercLib.CriticalLRP.Orchestration.SourceModelData.tendsto_cutMoment_atTop_top
#print axioms PercLib.CriticalLRP.Orchestration.SourceModelData.not_exists_uniform_cutMoment_bound
#print axioms PercLib.CriticalLRP.Orchestration.SourceModelData.tendsto_cutMoment_atTop_top_of_first_eq_top
#print axioms PercLib.CriticalLRP.Orchestration.Witness.sourceModelWitness_hasDerivAt_cutMassReal_powerLaw_of_subcritical
