/- Integrated from independently rebuilt Ultramath work.
Production base ed48eea0fa7697ac0e16db08e39b60ebb7c70e02.
Scratch source: ../../.ultramath/smwvlmbqa/m2/RVData.lean; migrated to current namespaces.
-/

module

public import PercLib.CriticalLRP.VolumeMoments.Convolution
public import PercLib.CriticalLRP.Analysis.Lemma_I_4_22
public import PercLib.CriticalLRP.Analysis.RVAlgebra
public import PercLib.CriticalLRP.VolumeMoments.HigherMoments.Defs

/-!
# Auxiliary lemmas for the Proposition I.4.20 induction step

Two groups of facts are collected here.

* Finite combinatorics: the middle binomial sum of the induction step,
  `∑_{ℓ=1}^{p-2} C(p,ℓ)(2ℓ-1)!!(2p-2ℓ-3)!! = (p-2)(2p-3)!!`, obtained from the
  production identity `PercLib.CriticalLRP.VolumeMoments.SA_middle` (the
  additive form of Lemma I.4.23 with the two end terms removed).

* Regular variation of the driving term
  `α(p-2)(2p-3)!! (E|K|²/E|K|)^(p-1) E|K|`: from regular variation of
  `E|K|` of index `α` and of `E|K|²` of index `3α`, its index is
  `2α(p-1)+α = (2p-1)α`.  This is the index bookkeeping of the paper's
  induction step; together with `drivingIndex_sub_linearIndex` it shows that
  the constant of the driving term is exactly cancelled by Lemma I.4.22.
-/

@[expose] public section

noncomputable section

open Filter Set MeasureTheory
open PercLib.CriticalLRP.Analysis
open scoped Topology

namespace PercLib.CriticalLRP.VolumeMoments.HigherMoments

/-! ### Finite combinatorics -/

theorem dblFact_eq_mul {p : ℕ} (hp : 2 ≤ p) :
    dblFact p = (2 * (p : ℝ) - 1) * dblFact (p - 1) := by
  have h := dblFact_succ (p - 1)
  have hp' : p - 1 + 1 = p := by omega
  rw [hp'] at h
  rw [h]
  have hc : ((p - 1 : ℕ) : ℝ) = (p : ℝ) - 1 := by
    rw [Nat.cast_sub (by omega)]
    norm_num
  rw [hc]
  ring

/-- The middle binomial sum of the induction step in Proposition I.4.20
(paper p. 49):
`∑_{ℓ=1}^{p-2} C(p,ℓ)(2ℓ-1)!!(2p-2ℓ-3)!! = (p-2)(2p-3)!!`,
written with the index shift `ℓ = m-1` matching `SA_middle`. -/
theorem middle_sum_eq {p : ℕ} (hp : 3 ≤ p) :
    (∑ ℓ ∈ Finset.range (p - 2),
        ((p.choose (ℓ + 1) : ℕ) : ℝ) * (dblFact (ℓ + 1) * dblFact (p - 2 - ℓ)))
      = ((p : ℝ) - 2) * dblFact (p - 1) := by
  have h := SA_middle p hp
  have hcast : (∑ ℓ ∈ Finset.range (p - 2),
        ((p.choose (ℓ + 1) : ℕ) : ℝ) * (dblFact (ℓ + 1) * dblFact (p - 2 - ℓ)))
        + ((p : ℝ) + 1) * dblFact (p - 1) = dblFact p := by
    have := congrArg (fun n : ℕ => (n : ℝ)) h
    push_cast at this
    simpa only [dblFact] using this
  have h2 : dblFact p = (2 * (p : ℝ) - 1) * dblFact (p - 1) := dblFact_eq_mul (by omega)
  rw [h2] at hcast
  linarith

/-- The middle sum written with the exponent bookkeeping of the induction step:
the coefficient `(2ℓ-1)!!(2p-2ℓ-3)!!` is the product of the two double
factorials `dblFact ℓ` and `dblFact (p-1-ℓ)`. -/
theorem middle_sum_eq' {p : ℕ} (hp : 3 ≤ p) :
    (∑ m ∈ Finset.range (p - 2), ((p.choose (m + 1) : ℕ) : ℝ) *
        (dblFact (m + 1) * dblFact (p - 2 - m))) = ((p : ℝ) - 2) * dblFact (p - 1) :=
  middle_sum_eq hp

/-! ### Regular variation of the ratio and of the driving term -/

/-- Multiplying by a nonzero constant preserves regular variation. -/
theorem regularlyVaryingAtTop_const_mul {f : ℝ → ℝ} {ρ c : ℝ} (hc : c ≠ 0)
    (h : RegularlyVaryingAtTop f ρ) :
    RegularlyVaryingAtTop (fun x => c * f x) ρ := by
  refine ⟨h.1.mono (fun x hx => mul_ne_zero hc hx), fun l hl => ?_⟩
  simpa only [mul_div_mul_left _ _ hc] using h.2 l hl

/-- The ratio `E|K|²/E|K|` is regularly varying of index `3α - α = 2α`. -/
theorem momentRatio_regularlyVarying {mom : ℕ → ℝ → ℝ} {α : ℝ}
    (h1 : RegularlyVaryingAtTop (mom 1) α)
    (h2 : RegularlyVaryingAtTop (mom 2) (3 * α)) :
    RegularlyVaryingAtTop (momentRatio mom) (2 * α) := by
  change RegularlyVaryingAtTop (fun x => momentRatio mom x) (2 * α)
  have h := h2.mul h1.inv
  have he : 3 * α + -α = 2 * α := by ring
  rw [he] at h
  have hfun : (fun x => momentRatio mom x) = fun x => mom 2 x * (mom 1 x)⁻¹ := by
    funext x
    unfold momentRatio
    rw [div_eq_mul_inv]
  rw [hfun]
  exact h

/-- A positive power of the ratio is regularly varying of index
`2α(p-1)`. -/
theorem momentRatio_rpow_regularlyVarying {mom : ℕ → ℝ → ℝ} {α : ℝ}
    (h1 : RegularlyVaryingAtTop (mom 1) α)
    (h2 : RegularlyVaryingAtTop (mom 2) (3 * α))
    (hpos1 : ∀ᶠ x in atTop, 0 < mom 1 x) (hpos2 : ∀ᶠ x in atTop, 0 < mom 2 x)
    (p : ℕ) :
    RegularlyVaryingAtTop (fun x => momentRatio mom x ^ ((p : ℝ) - 1))
      (2 * α * ((p : ℝ) - 1)) := by
  have hratio : RegularlyVaryingAtTop (momentRatio mom) (2 * α) :=
    momentRatio_regularlyVarying h1 h2
  have hposr : ∀ᶠ x in atTop, 0 < momentRatio mom x :=
    (hpos1.and hpos2).mono (fun x hx => div_pos hx.2 hx.1)
  exact hratio.rpow hposr

/-- **The driving term is regularly varying of index `(2p-1)α`.** -/
theorem drivingTerm_regularlyVarying {p : ℕ} {α : ℝ} {mom : ℕ → ℝ → ℝ}
    (hp : 3 ≤ p) (hα : 0 < α)
    (h1 : RegularlyVaryingAtTop (mom 1) α)
    (h2 : RegularlyVaryingAtTop (mom 2) (3 * α))
    (hpos1 : ∀ᶠ x in atTop, 0 < mom 1 x) (hpos2 : ∀ᶠ x in atTop, 0 < mom 2 x) :
    RegularlyVaryingAtTop (drivingTerm p α mom) ((2 * (p : ℝ) - 1) * α) := by
  have hprod := (momentRatio_rpow_regularlyVarying h1 h2 hpos1 hpos2 p).mul h1
  have hidx : 2 * α * ((p : ℝ) - 1) + α = (2 * (p : ℝ) - 1) * α := by ring
  have hrv : RegularlyVaryingAtTop
      (fun x => momentRatio mom x ^ ((p : ℝ) - 1) * mom 1 x) ((2 * (p : ℝ) - 1) * α) := by
    rw [← hidx]
    exact hprod
  have hc : α * ((p : ℝ) - 2) * dblFact (p - 1) ≠ 0 := by
    have hp2 : (p : ℝ) - 2 ≠ 0 := by
      have : (3 : ℝ) ≤ (p : ℝ) := by exact_mod_cast hp
      linarith
    exact mul_ne_zero (mul_ne_zero hα.ne' hp2) (dblFact_ne_zero _)
  have hconst := regularlyVaryingAtTop_const_mul hc hrv
  have hfun : (fun x => α * ((p : ℝ) - 2) * dblFact (p - 1) *
      (momentRatio mom x ^ ((p : ℝ) - 1) * mom 1 x)) = drivingTerm p α mom := by
    funext x
    unfold drivingTerm
    ring
  rwa [hfun] at hconst

/-- **The target `(2p-3)!!(E|K|²/E|K|)^(p-1)E|K|` is regularly varying of
index `(2p-1)α`**, which is the paper's "in particular, `E_{βc,r}|K|^p` is
regularly varying of index `(2p-1)α`". -/
theorem mixedMoment_regularlyVarying {p : ℕ} {α : ℝ} {mom : ℕ → ℝ → ℝ}
    (h1 : RegularlyVaryingAtTop (mom 1) α)
    (h2 : RegularlyVaryingAtTop (mom 2) (3 * α))
    (hpos1 : ∀ᶠ x in atTop, 0 < mom 1 x) (hpos2 : ∀ᶠ x in atTop, 0 < mom 2 x) :
    RegularlyVaryingAtTop (mixedMoment p mom) ((2 * (p : ℝ) - 1) * α) := by
  have hprod := (momentRatio_rpow_regularlyVarying h1 h2 hpos1 hpos2 p).mul h1
  have hidx : 2 * α * ((p : ℝ) - 1) + α = (2 * (p : ℝ) - 1) * α := by ring
  have hrv : RegularlyVaryingAtTop
      (fun x => momentRatio mom x ^ ((p : ℝ) - 1) * mom 1 x) ((2 * (p : ℝ) - 1) * α) := by
    rw [← hidx]
    exact hprod
  have hc : dblFact (p - 1) ≠ 0 := dblFact_ne_zero _
  have hconst := regularlyVaryingAtTop_const_mul hc hrv
  have hfun : (fun x => dblFact (p - 1) *
      (momentRatio mom x ^ ((p : ℝ) - 1) * mom 1 x)) = mixedMoment p mom := by
    funext x
    unfold mixedMoment
    ring
  rwa [hfun] at hconst

/-- Measurability of the driving term. -/
theorem measurable_drivingTerm {p : ℕ} {α : ℝ} {mom : ℕ → ℝ → ℝ}
    (hp : 1 ≤ p) (h1 : Measurable (mom 1)) (h2 : Measurable (mom 2)) :
    Measurable (drivingTerm p α mom) := by
  have hratio : Measurable (momentRatio mom) := by
    unfold momentRatio
    exact h2.div h1
  have hq : (0 : ℝ) ≤ (p : ℝ) - 1 := by
    have hp1 : (1 : ℝ) ≤ (p : ℝ) := by exact_mod_cast hp
    linarith
  have hrpow : Measurable (fun x => momentRatio mom x ^ ((p : ℝ) - 1)) :=
    (Real.continuous_rpow_const hq).measurable.comp hratio
  have hprod : Measurable (fun x => momentRatio mom x ^ ((p : ℝ) - 1) * mom 1 x) :=
    hrpow.mul h1
  have hconst : Measurable (fun x => α * ((p : ℝ) - 2) * dblFact (p - 1) *
      (momentRatio mom x ^ ((p : ℝ) - 1) * mom 1 x)) := hprod.const_mul _
  have hfun : (fun x => α * ((p : ℝ) - 2) * dblFact (p - 1) *
      (momentRatio mom x ^ ((p : ℝ) - 1) * mom 1 x)) = drivingTerm p α mom := by
    funext x
    unfold drivingTerm
    ring
  rwa [hfun] at hconst

/-- Eventual positivity of the driving term. -/
theorem drivingTerm_eventually_pos {p : ℕ} {α : ℝ} {mom : ℕ → ℝ → ℝ}
    (hp : 3 ≤ p) (hα : 0 < α) (hmom : ∀ m x, 0 < x → 0 < mom m x) :
    ∀ᶠ x in atTop, 0 < drivingTerm p α mom x :=
  (eventually_gt_atTop (0 : ℝ)).mono (fun x hx =>
    drivingTerm_pos hp hα (hmom 1 x hx) (hmom 2 x hx))

/-- **Regular-variation package of the driving term**: the data needed by
Lemma I.4.22, with index `(2p-1)α`. -/
theorem drivingTerm_RVPosData {p : ℕ} {α : ℝ} {mom : ℕ → ℝ → ℝ}
    (hp : 3 ≤ p) (hα : 0 < α)
    (hmom : ∀ m x, 0 < x → 0 < mom m x)
    (hmommeas1 : Measurable (mom 1)) (hmommeas2 : Measurable (mom 2))
    (h1 : RegularlyVaryingAtTop (mom 1) α)
    (h2 : RegularlyVaryingAtTop (mom 2) (3 * α)) :
    Nonempty (RVPosData (drivingTerm p α mom) ((2 * (p : ℝ) - 1) * α)) :=
  RVPosData.nonempty (drivingIndex_pos hp hα)
    (measurable_drivingTerm (by omega) hmommeas1 hmommeas2)
    (drivingTerm_regularlyVarying hp hα h1 h2
      ((eventually_gt_atTop (0 : ℝ)).mono (fun x hx => hmom 1 x hx))
      ((eventually_gt_atTop (0 : ℝ)).mono (fun x hx => hmom 2 x hx)))
    (drivingTerm_eventually_pos hp hα hmom)

end PercLib.CriticalLRP.VolumeMoments.HigherMoments
