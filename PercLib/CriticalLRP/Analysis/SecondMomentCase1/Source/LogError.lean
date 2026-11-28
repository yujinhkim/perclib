/-
Ultramath swarm `smwzt36y2`, member `m5`, direction `d3` (open area D).

# Case 1 of Proposition I.4.2: the normalised first-moment error is log-integrable

Hutchcroft, *Critical long-range percolation I*, arXiv:2508.18807v1, Proposition I.4.2
(second assertion), proof of Lemma I.4.9 (p. 37-38), and the fidelity audit note
`CRITICAL_LRP_FIDELITY_AUDIT.md` ("`hHlog` for Case 1 is still an explicit premise ... the
Case-1 producer is not supplied here").

The source's Case 1 (`d > 3α`) proves the polynomial decay

```text
  0 ≤ E_{1,r} ≤ (16 α³ / β_c³) r^{3α-d},
```

(`Lemma I.4.9`, second display) and concludes that `E_{1,r}` is a logarithmically integrable
error function. Since `E_{0,r}` already is one and
`1 - Ē_{1,r} = (1 - E_{0,r})(1 - E_{1,r})`, the composite defect `Ē_{1,r}` is a log-error
function, and the ODE identity `(I.4.7)` of Section I.4.1 then gives `H_r → 0` with
`∫^∞ |H_r| dr/r < ∞`.

This file formalises exactly that last step, on the paper's own Case-1 defect bound: it
supplies the `hHlog : LogarithmicallyIntegrable M.p2H` premise of
`SourceModelData.isLogErrorFunction_p2H` / `SourceModelData.logIntegrable_p2H` from the
polynomial bound, with no triangle condition and no Case-2/Case-3 input.

## What is proved

* `measurable_cutE1` — `r ↦ 𝓔_{1,r}` is measurable on all of `ℝ`, unconditionally (below `0`
  the defect vanishes, above `0` it is the landed mixed proxy
  `E1Sign.measurable_cutE1_exp_log`).  This removes the measurability input from the
  consumer.
* `isLogErrorFunction_cutE1_of_eventually_le_rpow` — polynomial decay of `𝓔_{1,r}` makes it a
  log-error function (the `In particular` clause of Lemma I.4.9).
* `isLogErrorFunction_p2H_of_caseOne` — **Case 1 of Proposition I.4.2, second assertion**: the
  normalised first-moment error `H_r = M.p2H r` is log-integrable and `→ 0`, from Lemma I.4.9's
  defect bound.
* `logIntegrable_p2H_of_caseOne` — the `hHlog` shape alone, as consumed by
  `SourceModelData.tendsto_div_two_of_caseOne_no_ac` and the Case-3 assembly.

## Remaining hypotheses

The only model-theoretic input beyond the standing `SourceModelData` fields and the radial
regularity bundle already carried by `SourceModelData.isLogErrorFunction_p2H` (`T`, `S`, `hlow`,
`hupp`, `hcontinf`, `hK`, `hex`, `hinf`, `h2`) is the paper's Lemma I.4.9 bound
`𝓔_{1,r} ≤ C r^{3α-d}`.  Measurability of the defect and eventual finiteness of the first
moment are derived.  No Case-2 or Case-3 assumption (triangle condition, hydrodynamic
condition, uncut critical tail) is used.
-/
module

public import PercLib.CriticalLRP.Analysis.SecondMomentCase3.FirstMomentLogError
public import PercLib.CriticalLRP.Analysis.Cutoff.CutoffDefect.LogIntegrable

/-! # Case 1: the first-moment error is logarithmically integrable -/

set_option autoImplicit false
set_option linter.style.longLine false
set_option linter.hashCommand false
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false

@[expose] public section

noncomputable section

open MeasureTheory Filter Topology Set
open scoped ENNReal NNReal Topology

namespace PercLib.CriticalLRP
namespace CaseOne

open Orchestration

/-! ## The Case-1 defect is a log-error function -/

/-- **`𝓔_{1,r}` is a measurable function of `r` on all of `ℝ`.**  Below `0` the ball is
empty and
the defect vanishes (`E1Sign.cutE1_eq_zero_of_neg`); above `0` it is the mixed proxy
`E1Sign.measurable_cutE1_exp_log`.  This discharges the measurability input used below. -/
theorem measurable_cutE1 (M : SourceModelData) :
    Measurable fun r : ℝ => PivotFlux.cutE1 M r := by
  refine MeasureTheory.measurable_of_measurable_inter_Ioi (c := 0) (g' := fun _ => (0 : ℝ))
    ?_ ?_ measurable_const
  · intro s hs
    have heq : (fun r : ℝ => PivotFlux.cutE1 M r) ⁻¹' s ∩ Ioi 0
        = (fun r : ℝ => PivotFlux.cutE1 M (Real.exp (Real.log r))) ⁻¹' s ∩ Ioi 0 := by
      ext r
      simp only [Set.mem_inter_iff, Set.mem_preimage, Set.mem_Ioi]
      constructor
      · rintro ⟨h1, h2⟩
        exact ⟨by rw [Real.exp_log h2]; exact h1, h2⟩
      · rintro ⟨h1, h2⟩
        exact ⟨by rwa [Real.exp_log h2] at h1, h2⟩
    rw [heq]
    exact (E1Sign.measurable_cutE1_exp_log M hs).inter measurableSet_Ioi
  · intro r hr
    exact E1Sign.cutE1_eq_zero_of_neg M hr

/-- **Lemma I.4.9, `In particular` clause.**  If the truncated-law defect satisfies the Case-1
polynomial bound `𝓔_{1,r} ≤ C r^{-e}` eventually for some `e > 0`, then it is a
logarithmically
integrable error function.  (In the paper `e = d - 3α`, and `C = 16 α³ / β_c³`.) -/
theorem isLogErrorFunction_cutE1_of_eventually_le_rpow (M : SourceModelData)
    (hmeas : Measurable fun r : ℝ => PivotFlux.cutE1 M r)
    (h1 : ∀ᶠ r : ℝ in atTop, M.cutMoment 1 r ≠ ⊤)
    {C e : ℝ} (he : 0 < e)
    (hb : ∀ᶠ r : ℝ in atTop, PivotFlux.cutE1 M r ≤ C * r ^ (-e)) :
    Analysis.IsLogErrorFunction (fun r : ℝ => PivotFlux.cutE1 M r) := by
  have hnonneg : ∀ᶠ r : ℝ in atTop, 0 ≤ PivotFlux.cutE1 M r := by
    have h := CutoffDefect.cutE1_nonneg_eventually M h1
    simpa only [PivotFlux.cutE1, CutoffDefect.cutE1] using h
  refine ⟨⟨hmeas,
    Analysis.integrableOn_abs_div_of_eventually_le_rpow_neg hmeas he hnonneg hb⟩,
    ?_⟩
  have hg : Tendsto (fun r : ℝ => C * r ^ (-e)) atTop (𝓝 0) := by
    simpa using (TriangleAverage.tendsto_rpow_neg_atTop_zero (a := -e) (by linarith)).const_mul C
  exact squeeze_zero' hnonneg hb hg

/-! ## Case 1 of Proposition I.4.2, second assertion -/

/-- **Case 1 of Proposition I.4.2, second assertion.**  For `d > 3α`, Lemma I.4.9's defect bound
`𝓔_{1,r} ≤ C r^{3α-d}` makes the normalised first-moment error
`H_r = (β_c/α) r^{-α} E_{β_c,r}|K| - 1` a logarithmically integrable error function.

This is `SourceModelData.isLogErrorFunction_p2H` with the Case-3 triangle-condition input `hE1`
replaced by the paper's Case-1 polynomial defect estimate; the composite defect bound `hC` and
its vanishing `h0` are *derived* here exactly as in the triangle-condition form. -/
theorem isLogErrorFunction_p2H_of_caseOne (M : SourceModelData)
    (hβ : (0 : ℝ) < M.betaCrit)
    (T : ℕ → Finset M.V) (hTmono : Monotone T) (hT : ∀ y : M.V, ∃ n, y ∈ T n)
    (S : ℕ → Finset (Sym2 M.V)) (hSmono : Monotone S) (hS : ∀ e : Sym2 M.V, ∃ n, e ∈ S n)
    {R a₀ r₀ : ℝ} (hRpos : 0 < R) (hRa₀ : R < a₀) (ha₀r₀ : a₀ < r₀)
    (hlow : ∀ s : ℝ, R < s → (1 / 2) * s ^ (-(M.d : ℝ) - M.α - 1) ≤ |deriv M.K s|)
    (hupp : ∀ s : ℝ, R < s → |deriv M.K s| ≤ 2 * s ^ (-(M.d : ℝ) - M.α - 1))
    (h2 : ∀ t : ℝ, a₀ ≤ t → M.cutMoment 2 t ≠ ⊤)
    (hcontinf : ∀ y : M.V, ∀ r : ℝ, a₀ ≤ r → ContinuousAt
      (sMomentInfFlux (0 : M.V) {y} (fun _ => (1 : ℝ)) M.cutProb M.cutEdgeDeriv) r)
    (hK : ∀ r : ℝ, a₀ ≤ r → ContinuousAt (fun r' => deriv M.K r') r)
    (hex : ∀ r : ℝ, a₀ ≤ r → ContinuousAt M.exclScalar r)
    (hinf : Tendsto M.cutMassReal atTop atTop)
    (h3α : 3 * M.α < (M.d : ℝ))
    {C : ℝ} (hE1bound : ∀ᶠ r : ℝ in atTop,
      PivotFlux.cutE1 M r ≤ C * r ^ (3 * M.α - M.d)) :
    Analysis.IsLogErrorFunction M.p2H := by
  have hmeasE1 : Measurable fun r : ℝ => PivotFlux.cutE1 M r := measurable_cutE1 M
  have h1fin : ∀ᶠ r : ℝ in atTop, M.cutMoment 1 r ≠ ⊤ := by
    filter_upwards [eventually_ge_atTop a₀] with r hr
    exact M.cutMoment_one_ne_top_of_two (h2 r hr)
  have he : 0 < (M.d : ℝ) - 3 * M.α := by linarith
  have hb : ∀ᶠ r : ℝ in atTop,
      PivotFlux.cutE1 M r ≤ C * r ^ (-((M.d : ℝ) - 3 * M.α)) := by
    filter_upwards [hE1bound] with r hr
    rwa [show -((M.d : ℝ) - 3 * M.α) = 3 * M.α - (M.d : ℝ) by ring]
  have hE1 : Analysis.IsLogErrorFunction (fun r : ℝ => PivotFlux.cutE1 M r) :=
    isLogErrorFunction_cutE1_of_eventually_le_rpow M hmeasE1 h1fin he hb
  have h0 : Tendsto (I420Case3.cutError M) atTop (𝓝 0) :=
    CornerSafe.tendsto_one_sub_mul (PivotFlux.tendsto_cutE0 M) hE1.2
  obtain ⟨N, hN⟩ := (Metric.tendsto_atTop.1 h0) 1 zero_lt_one
  have hNle : ∀ t : ℝ, max r₀ (max N 1) ≤ t → |I420Case3.cutError M t| ≤ 1 := by
    intro t ht
    have htN : N ≤ t := le_trans (le_trans (le_max_left N 1) (le_max_right r₀ (max N 1))) ht
    have h := hN t htN
    rw [Real.dist_eq, sub_zero] at h
    exact le_of_lt h
  have ha₀ : a₀ < max r₀ (max N 1) :=
    lt_of_lt_of_le ha₀r₀ (le_max_left r₀ (max N 1))
  exact M.isLogErrorFunction_p2H hβ T hTmono hT S hSmono hS hRpos hRa₀ ha₀ hlow hupp h2
    hcontinf hK hex hinf hE1 (C := 1) hNle h0

/-- The `hHlog` shape of the Case-1 producer: `H_r` is logarithmically integrable. -/
theorem logIntegrable_p2H_of_caseOne (M : SourceModelData)
    (hβ : (0 : ℝ) < M.betaCrit)
    (T : ℕ → Finset M.V) (hTmono : Monotone T) (hT : ∀ y : M.V, ∃ n, y ∈ T n)
    (S : ℕ → Finset (Sym2 M.V)) (hSmono : Monotone S) (hS : ∀ e : Sym2 M.V, ∃ n, e ∈ S n)
    {R a₀ r₀ : ℝ} (hRpos : 0 < R) (hRa₀ : R < a₀) (ha₀r₀ : a₀ < r₀)
    (hlow : ∀ s : ℝ, R < s → (1 / 2) * s ^ (-(M.d : ℝ) - M.α - 1) ≤ |deriv M.K s|)
    (hupp : ∀ s : ℝ, R < s → |deriv M.K s| ≤ 2 * s ^ (-(M.d : ℝ) - M.α - 1))
    (h2 : ∀ t : ℝ, a₀ ≤ t → M.cutMoment 2 t ≠ ⊤)
    (hcontinf : ∀ y : M.V, ∀ r : ℝ, a₀ ≤ r → ContinuousAt
      (sMomentInfFlux (0 : M.V) {y} (fun _ => (1 : ℝ)) M.cutProb M.cutEdgeDeriv) r)
    (hK : ∀ r : ℝ, a₀ ≤ r → ContinuousAt (fun r' => deriv M.K r') r)
    (hex : ∀ r : ℝ, a₀ ≤ r → ContinuousAt M.exclScalar r)
    (hinf : Tendsto M.cutMassReal atTop atTop)
    (h3α : 3 * M.α < (M.d : ℝ))
    {C : ℝ} (hE1bound : ∀ᶠ r : ℝ in atTop,
      PivotFlux.cutE1 M r ≤ C * r ^ (3 * M.α - M.d)) :
    Analysis.LogarithmicallyIntegrable M.p2H :=
  (isLogErrorFunction_p2H_of_caseOne M hβ T hTmono hT S hSmono hS hRpos hRa₀ ha₀r₀ hlow hupp
    h2 hcontinf hK hex hinf h3α hE1bound).1

end CaseOne
end PercLib.CriticalLRP

/-! ## Axiom audit -/

set_option linter.hashCommand false

#print axioms PercLib.CriticalLRP.CaseOne.measurable_cutE1
#print axioms PercLib.CriticalLRP.CaseOne.isLogErrorFunction_cutE1_of_eventually_le_rpow
#print axioms PercLib.CriticalLRP.CaseOne.isLogErrorFunction_p2H_of_caseOne
#print axioms PercLib.CriticalLRP.CaseOne.logIntegrable_p2H_of_caseOne
