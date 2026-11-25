/- Integrated from independently rebuilt Ultramath work.
Production base ed48eea0fa7697ac0e16db08e39b60ebb7c70e02.
Scratch source: ../../.ultramath/smwvlmbqa/m2/Assembly.lean; migrated to current namespaces.
-/

module

public import PercLib.CriticalLRP.VolumeMoments.HigherMoments.Induction

/-!
# The ODE comparison of Proposition I.4.20, and its application to the moments

Source: T. Hutchcroft, *Critical long-range percolation I: High effective
dimension*, arXiv:2508.18807v1, proof of Proposition I.4.20, p. 50.

`derivative_bound` turns the percolation inputs (the exact derivative identity of
Lemma I.4.1, the mass-transport equality of its two end terms, the
decorrelation bounds of Lemma I.2.1, the induction hypothesis and the
first-moment normalisation `β|J'(r)||B_r| E|K| ~ α/r`) into the hypothesis of
Lemma I.4.22.

`moment_upper_bound` applies `Analysis.lemma_I_4_22_of_hasDerivAt_bound` with
`a = (p+1)α` and `b = (2p-1)α`, and uses
`b - a = (p-2)α` to cancel the constant `α(p-2)(2p-3)!!` of the driving term,
yielding `E|K|^p ≤ (1+o(1))(2p-3)!!(E|K|²/E|K|)^(p-1)E|K|`.
-/

@[expose] public section

noncomputable section

open Filter Set MeasureTheory
open PercLib.CriticalLRP.Analysis
open scoped Topology

namespace PercLib.CriticalLRP.VolumeMoments.HigherMoments

/-- **The derivative comparison of the induction step.**  From the exact
derivative identity, mass transport, the decorrelation bounds, the induction
hypothesis and the normalisation `c(r) |B_r| E|K| r ≤ (1+o(1))α`, the derivative
of `E|K|^p` satisfies the one-sided ODE
`f'(r) ≤ (1+o(1)) ((p+1)α f(r) + h(r))/r` with `h` the paper's driving term. -/
theorem derivative_bound {p : ℕ} (hp : 3 ≤ p) {α : ℝ} (hα : 0 < α)
    {mom : ℕ → ℝ → ℝ} {c Bcard : ℝ → ℝ} {A : ℕ → ℝ → ℝ}
    (hmom : ∀ m x, 0 < x → 0 < mom m x)
    (hB : ∀ x, 0 < x → 0 ≤ Bcard x) (hc0 : ∀ x, 0 < x → 0 ≤ c x)
    (hmass : ∀ x, 0 < x → A 0 x = A (p - 1) x)
    (hA0 : ∀ x, 0 < x → A 0 x ≤ Bcard x * (mom 1 x * mom p x))
    (hAmid : ∀ x, 0 < x → ∀ ℓ, 1 ≤ ℓ → ℓ ≤ p - 2 →
      A ℓ x ≤ Bcard x * (mom (ℓ + 1) x * mom (p - ℓ) x))
    (hIH : ∀ ε > 0, ∀ᶠ x in atTop, ∀ m, 2 ≤ m → m ≤ p - 1 →
      mom m x ≤ (1 + ε) * dblFact (m - 1) * momentRatio mom x ^ ((m : ℝ) - 1) * mom 1 x)
    (hc : ∀ ε > 0, ∀ᶠ x in atTop, c x * Bcard x * mom 1 x * x ≤ (1 + ε) * α) :
    ∀ ε > 0, ∀ᶠ x in atTop,
      c x * (∑ ℓ ∈ Finset.range p, ((p.choose ℓ : ℕ) : ℝ) * A ℓ x)
        ≤ (1 + ε) * (((p : ℝ) + 1) * α * mom p x + drivingTerm p α mom x) / x := by
  intro ε hε
  obtain ⟨δ, hδpos, hδε⟩ := exists_one_add_pow_three_le hε
  have hδ : 0 ≤ δ := hδpos.le
  have hαnn : 0 ≤ α := hα.le
  have hp2pos : (0 : ℝ) < (p : ℝ) - 2 := by
    have h3 : (3 : ℝ) ≤ (p : ℝ) := by exact_mod_cast hp
    linarith
  filter_upwards [eventually_gt_atTop (0 : ℝ), hIH δ hδpos, hc δ hδpos] with x hx hIHx hcx
  have h1 : 0 < mom 1 x := hmom 1 x hx
  have h2 : 0 < mom 2 x := hmom 2 x hx
  have hP : 0 < mom p x := hmom p x hx
  have hnn : ∀ m, 0 ≤ mom m x := fun m => (hmom m x hx).le
  have hBx : 0 ≤ Bcard x := hB x hx
  have hc0x : 0 ≤ c x := hc0 x hx
  have hmm : 0 < mixedMoment p mom x := mixedMoment_pos (p := p) h1 h2
  have hsum := sum_bound (p := p) hp hδ hBx hnn h1 h2 (hmass x hx) (hA0 x hx) (hAmid x hx) hIHx
  have hmul := mul_le_mul_of_nonneg_left hsum hc0x
  -- first term
  have T1 : c x * (Bcard x * ((p : ℝ) + 1) * (mom 1 x * mom p x))
      ≤ (1 + δ) * (((p : ℝ) + 1) * α * mom p x / x) := by
    have hfac : c x * (Bcard x * ((p : ℝ) + 1) * (mom 1 x * mom p x))
        = (c x * Bcard x * mom 1 x * x) * (((p : ℝ) + 1) * mom p x / x) := by
      field_simp
    rw [hfac]
    have hnonneg : 0 ≤ ((p : ℝ) + 1) * mom p x / x := by positivity
    calc (c x * Bcard x * mom 1 x * x) * (((p : ℝ) + 1) * mom p x / x)
        ≤ ((1 + δ) * α) * (((p : ℝ) + 1) * mom p x / x) :=
          mul_le_mul_of_nonneg_right hcx hnonneg
      _ = (1 + δ) * (((p : ℝ) + 1) * α * mom p x / x) := by ring
  -- second term
  have T2 : c x * (Bcard x * (1 + δ) ^ 2 *
        (((p : ℝ) - 2) * mixedMoment p mom x * mom 1 x))
      ≤ (1 + δ) ^ 3 * (drivingTerm p α mom x / x) := by
    have hfac : c x * (Bcard x * (1 + δ) ^ 2 *
          (((p : ℝ) - 2) * mixedMoment p mom x * mom 1 x))
        = (c x * Bcard x * mom 1 x * x) *
            ((1 + δ) ^ 2 * (((p : ℝ) - 2) * mixedMoment p mom x) / x) := by
      field_simp
    rw [hfac]
    have hnonneg : 0 ≤ (1 + δ) ^ 2 * (((p : ℝ) - 2) * mixedMoment p mom x) / x := by
      have hd : 0 ≤ (1 + δ) ^ 2 := by positivity
      have hm : 0 < ((p : ℝ) - 2) * mixedMoment p mom x := by positivity
      positivity
    calc (c x * Bcard x * mom 1 x * x) *
          ((1 + δ) ^ 2 * (((p : ℝ) - 2) * mixedMoment p mom x) / x)
        ≤ ((1 + δ) * α) *
          ((1 + δ) ^ 2 * (((p : ℝ) - 2) * mixedMoment p mom x) / x) :=
          mul_le_mul_of_nonneg_right hcx hnonneg
      _ = (1 + δ) ^ 3 * (drivingTerm p α mom x / x) := by
          rw [drivingTerm_eq_smul]
          field_simp
  -- combine the pieces
  have hexp : c x * (Bcard x * ((p : ℝ) + 1) * (mom 1 x * mom p x)
        + Bcard x * (1 + δ) ^ 2 * (((p : ℝ) - 2) * mixedMoment p mom x * mom 1 x))
      = c x * (Bcard x * ((p : ℝ) + 1) * (mom 1 x * mom p x))
        + c x * (Bcard x * (1 + δ) ^ 2 *
            (((p : ℝ) - 2) * mixedMoment p mom x * mom 1 x)) := by ring
  rw [hexp] at hmul
  have hmain : c x * (∑ ℓ ∈ Finset.range p, ((p.choose ℓ : ℕ) : ℝ) * A ℓ x)
      ≤ (1 + δ) * (((p : ℝ) + 1) * α * mom p x / x)
        + (1 + δ) ^ 3 * (drivingTerm p α mom x / x) := by
    linarith [hmul, T1, T2]
  -- absorb the three `(1+δ)` factors
  have hmono : (1 + δ) ≤ (1 + δ) ^ 3 := by nlinarith [hδ, sq_nonneg δ]
  have hA1 : 0 ≤ ((p : ℝ) + 1) * α * mom p x / x := by positivity
  have hB1 : 0 ≤ drivingTerm p α mom x / x := by
    have := drivingTerm_pos hp hα h1 h2
    positivity
  have hstep1 : (1 + δ) * (((p : ℝ) + 1) * α * mom p x / x)
      ≤ (1 + δ) ^ 3 * (((p : ℝ) + 1) * α * mom p x / x) :=
    mul_le_mul_of_nonneg_right hmono hA1
  have hsum2 : (1 + δ) ^ 3 * (((p : ℝ) + 1) * α * mom p x / x)
        + (1 + δ) ^ 3 * (drivingTerm p α mom x / x)
      = (1 + δ) ^ 3 *
          ((((p : ℝ) + 1) * α * mom p x + drivingTerm p α mom x) / x) := by
    field_simp
  have hlast : (1 + δ) ^ 3 *
        ((((p : ℝ) + 1) * α * mom p x + drivingTerm p α mom x) / x)
      ≤ (1 + ε) *
        ((((p : ℝ) + 1) * α * mom p x + drivingTerm p α mom x) / x) := by
    apply mul_le_mul_of_nonneg_right hδε
    have hnum : 0 ≤ ((p : ℝ) + 1) * α * mom p x + drivingTerm p α mom x := by
      have hd : 0 < drivingTerm p α mom x := drivingTerm_pos hp hα h1 h2
      positivity
    exact div_nonneg hnum hx.le
  have htail : (1 + δ) * (((p : ℝ) + 1) * α * mom p x / x)
        + (1 + δ) ^ 3 * (drivingTerm p α mom x / x)
      ≤ (1 + ε) * (((p : ℝ) + 1) * α * mom p x + drivingTerm p α mom x) / x := by
    calc (1 + δ) * (((p : ℝ) + 1) * α * mom p x / x)
          + (1 + δ) ^ 3 * (drivingTerm p α mom x / x)
        ≤ (1 + δ) ^ 3 * (((p : ℝ) + 1) * α * mom p x / x)
          + (1 + δ) ^ 3 * (drivingTerm p α mom x / x) := by linarith [hstep1]
      _ = (1 + δ) ^ 3 *
            ((((p : ℝ) + 1) * α * mom p x + drivingTerm p α mom x) / x) := hsum2
      _ ≤ (1 + ε) *
            ((((p : ℝ) + 1) * α * mom p x + drivingTerm p α mom x) / x) := hlast
      _ = (1 + ε) * (((p : ℝ) + 1) * α * mom p x + drivingTerm p α mom x) / x := by
          rw [mul_div_assoc]
  exact hmain.trans htail

/-- **Lemma I.4.22 applied to the moment of order `p`.**  If the driving term is
regularly varying of index `(2p-1)α` (as it is, by
`drivingTerm_regularlyVarying`), the derivative satisfies the one-sided ODE of
`derivative_bound`, and `E|K|` has index `α` while `E|K|²` has index `3α`, then
`E|K|^p ≤ (1+o(1)) (2p-3)!! (E|K|²/E|K|)^(p-1) E|K|`. -/
theorem moment_upper_bound {p : ℕ} (hp : 3 ≤ p) {α : ℝ} (hα : 0 < α)
    {mom : ℕ → ℝ → ℝ} (hmom : ∀ m x, 0 < x → 0 < mom m x)
    (hmommeas1 : Measurable (mom 1)) (hmommeas2 : Measurable (mom 2))
    (h1 : RegularlyVaryingAtTop (mom 1) α)
    (h2 : RegularlyVaryingAtTop (mom 2) (3 * α))
    {f' : ℝ → ℝ} (hderiv : ∀ x, 0 < x → HasDerivAt (fun r => mom p r) (f' x) x)
    (hfbd : ∀ ε > 0, ∀ᶠ x in atTop,
      f' x ≤ (1 + ε) * (((p : ℝ) + 1) * α * mom p x + drivingTerm p α mom x) / x) :
    ∀ ε > 0, ∀ᶠ r in atTop, mom p r ≤ (1 + ε) * mixedMoment p mom r := by
  obtain ⟨D⟩ := drivingTerm_RVPosData hp hα hmom hmommeas1 hmommeas2 h1 h2
  have hlin : 0 < ((p : ℝ) + 1) * α := by positivity
  have hgap : (0 : ℝ) < ((p : ℝ) - 2) * α := by
    have h3 : (3 : ℝ) ≤ (p : ℝ) := by exact_mod_cast hp
    have : 0 < (p : ℝ) - 2 := by linarith
    positivity
  have hlt : ((p : ℝ) + 1) * α < (2 * (p : ℝ) - 1) * α := by
    have := drivingIndex_sub_linearIndex p α
    linarith
  have hhpos : ∀ x, 0 < x → 0 < drivingTerm p α mom x :=
    fun x hx => drivingTerm_pos hp hα (hmom 1 x hx) (hmom 2 x hx)
  have hfpos : ∀ x, 0 < x → 0 < mom p x := fun x hx => hmom p x hx
  intro ε hε
  have h := lemma_I_4_22_of_hasDerivAt_bound D hlin hlt hhpos hfpos hderiv hfbd ε hε
  refine h.mono (fun r hr => ?_)
  have hba : (2 * (p : ℝ) - 1) * α - ((p : ℝ) + 1) * α = ((p : ℝ) - 2) * α :=
    drivingIndex_sub_linearIndex p α
  have hp2 : (0 : ℝ) < (p : ℝ) - 2 := by
    have h3 : (3 : ℝ) ≤ (p : ℝ) := by exact_mod_cast hp
    linarith
  have hkey : drivingTerm p α mom r / ((2 * (p : ℝ) - 1) * α - ((p : ℝ) + 1) * α)
      = mixedMoment p mom r := by
    rw [hba, drivingTerm_eq_smul]
    field_simp
  rwa [hkey] at hr

end PercLib.CriticalLRP.VolumeMoments.HigherMoments
