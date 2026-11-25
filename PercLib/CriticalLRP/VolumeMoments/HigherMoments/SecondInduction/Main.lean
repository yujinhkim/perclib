/- Integrated from independently rebuilt Ultramath work.
Production base e756a603f08962e545c3c11bf9dd877b46c80d6f.
Scratch source: ../../.ultramath/smwvp122a/m2/M2/Main.lean.
-/

module

public import PercLib.CriticalLRP.VolumeMoments.HigherMoments.SecondInduction.TwoSided
public import PercLib.CriticalLRP.Analysis.Lemma_I_4_21

/-!
# The second induction step of Proposition I.4.20, assembled

`derivative_ratio_tendsto` converts the exact derivative identity of Lemma I.4.1
plus the decorrelation estimates (I.4.20) and the induction hypothesis for the
smaller moments into the hypothesis of Lemma I.4.21,
`(E|K|^p)' ~ ((p+1)α E|K|^p + h)/r`.

`moment_asymptotic_of_decorrelation` then applies Lemma I.4.21, concluding
`E|K|^p ~ (2p-3)!!(E|K|²/E|K|)^(p-1)E|K|` and the regular variation of index
`(2p-1)α`.  No step of the conclusion is assumed: the only probabilistic inputs
are the derivative identity, mass transport, the three decorrelation
asymptotics, the induction hypothesis and the first-moment normalisation
`r c_r |B_r| E|K| → α`, all of them the paper's own inputs at this point.
-/

@[expose] public section

noncomputable section

open Finset Filter
open scoped Topology

namespace PercLib.CriticalLRP.VolumeMoments.HigherMoments.SecondInduction

open PercLib.CriticalLRP.VolumeMoments
open PercLib.CriticalLRP.VolumeMoments.HigherMoments
open PercLib.CriticalLRP.Analysis

/-- The binomial sum of the decorrelators is `|B_r| E|K|` times its
normalisation. -/
theorem sum_A_eq_mul_normalizedSum (p : ℕ) {A : ℕ → ℝ → ℝ} {Bcard : ℝ → ℝ}
    {mom : ℕ → ℝ → ℝ} {r : ℝ} (hB : Bcard r ≠ 0) (h1 : mom 1 r ≠ 0) :
    (∑ ℓ ∈ Finset.range p, ((p.choose ℓ : ℕ) : ℝ) * A ℓ r)
      = (Bcard r * mom 1 r) * normalizedSum p A Bcard mom r := by
  unfold normalizedSum
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro ℓ hℓ
  field_simp

/-- **The derivative ratio of the second induction.**  With the exact derivative
identity of Lemma I.4.1, the decorrelation estimates (I.4.20), the induction
hypothesis and the first-moment normalisation `r c_r |B_r| E|K| → α`, the ratio
`(E|K|^p)' / (((p+1)α E|K|^p + h)/r)` tends to `1`; this is hypothesis `hasym`
of Lemma I.4.21 in the paper's notation. -/
theorem derivative_ratio_tendsto {p : ℕ} (hp : 3 ≤ p) {α : ℝ} (hα : 0 < α)
    {mom : ℕ → ℝ → ℝ} {A : ℕ → ℝ → ℝ} {Bcard c : ℝ → ℝ}
    (hmom : ∀ m r, 0 < r → 0 < mom m r)
    (hB : ∀ r, 0 < r → 0 < Bcard r)
    (hmass : ∀ r, 0 < r → A (p - 1) r = A 0 r)
    (hAend : Tendsto (fun r => A 0 r / (Bcard r * (mom 1 r * mom p r))) atTop (𝓝 1))
    (hAmid : ∀ ℓ, 1 ≤ ℓ → ℓ ≤ p - 2 →
      Tendsto (fun r => A ℓ r / (Bcard r * (mom (ℓ + 1) r * mom (p - ℓ) r))) atTop (𝓝 1))
    (hIH : ∀ m, 2 ≤ m → m ≤ p - 1 →
      Tendsto (fun r => mom m r / mixedMoment m mom r) atTop (𝓝 1))
    (hc : Tendsto (fun r => r * c r * Bcard r * mom 1 r) atTop (𝓝 α)) :
    Tendsto (fun r => (c r * ∑ ℓ ∈ Finset.range p, ((p.choose ℓ : ℕ) : ℝ) * A ℓ r)
      / ((((p : ℝ) + 1) * α * mom p r + drivingTerm p α mom r) / r)) atTop (𝓝 1) := by
  have hZ := normalizedSum_tendsto hp hmom hB hmass hAend hAmid hIH
  have hw : Tendsto (fun r => (r * c r * Bcard r * mom 1 r) / α) atTop (𝓝 1) := by
    have h := hc.div_const α
    rwa [div_self hα.ne'] at h
  have hprod : Tendsto (fun r => ((r * c r * Bcard r * mom 1 r) / α)
      * (normalizedSum p A Bcard mom r / targetSum p mom r)) atTop (𝓝 1) := by
    have := hw.mul hZ
    rwa [one_mul] at this
  refine hprod.congr' ?_
  filter_upwards [eventually_gt_atTop (0 : ℝ)] with r hr
  have hBne : Bcard r ≠ 0 := (hB r hr).ne'
  have h1ne : mom 1 r ≠ 0 := (hmom 1 r hr).ne'
  have hTne : targetSum p mom r ≠ 0 :=
    (targetSum_pos hp (hmom 1 r hr) (hmom 2 r hr) (hmom p r hr)).ne'
  rw [sum_A_eq_mul_normalizedSum p hBne h1ne, targetSum_eq_ratio (p := p) (α := α)]
  field_simp

/-- **Proposition I.4.20, second induction step.**  If the exact derivative
identity of Lemma I.4.1 holds for the `p`-th moment, the decorrelation estimates
(I.4.20) hold for every `ℓ ∈ [0,p-1]`, the induction hypothesis holds for the
smaller moments `2 ≤ m ≤ p-1`, and the first-moment normalisation
`r c_r |B_r| E|K| → α` holds, then

`E|K|^p ~ (2p-3)!! (E|K|²/E|K|)^(p-1) E|K|`

and `E|K|^p` is regularly varying of index `(2p-1)α`. -/
theorem moment_asymptotic_of_decorrelation {p : ℕ} (hp : 3 ≤ p) {α : ℝ} (hα : 0 < α)
    {mom : ℕ → ℝ → ℝ} {A : ℕ → ℝ → ℝ} {Bcard c : ℝ → ℝ}
    (hmom : ∀ m r, 0 < r → 0 < mom m r)
    (hmommeas1 : Measurable (mom 1)) (hmommeas2 : Measurable (mom 2))
    (h1 : RegularlyVaryingAtTop (mom 1) α)
    (h2 : RegularlyVaryingAtTop (mom 2) (3 * α))
    (hB : ∀ r, 0 < r → 0 < Bcard r)
    (hmass : ∀ r, 0 < r → A (p - 1) r = A 0 r)
    (hderivId : ∀ r, 0 < r → HasDerivAt (fun s => mom p s)
      (c r * ∑ ℓ ∈ Finset.range p, ((p.choose ℓ : ℕ) : ℝ) * A ℓ r) r)
    (hAend : Tendsto (fun r => A 0 r / (Bcard r * (mom 1 r * mom p r))) atTop (𝓝 1))
    (hAmid : ∀ ℓ, 1 ≤ ℓ → ℓ ≤ p - 2 →
      Tendsto (fun r => A ℓ r / (Bcard r * (mom (ℓ + 1) r * mom (p - ℓ) r))) atTop (𝓝 1))
    (hIH : ∀ m, 2 ≤ m → m ≤ p - 1 →
      Tendsto (fun r => mom m r / mixedMoment m mom r) atTop (𝓝 1))
    (hc : Tendsto (fun r => r * c r * Bcard r * mom 1 r) atTop (𝓝 α)) :
    Tendsto (fun r => mom p r / mixedMoment p mom r) atTop (𝓝 1) ∧
      RegularlyVaryingAtTop (mom p) ((2 * (p : ℝ) - 1) * α) := by
  obtain ⟨D⟩ := drivingTerm_RVPosData hp hα hmom hmommeas1 hmommeas2 h1 h2
  have hlin : 0 < ((p : ℝ) + 1) * α := by positivity
  have hlt : ((p : ℝ) + 1) * α < (2 * (p : ℝ) - 1) * α := by
    have := drivingIndex_sub_linearIndex p α
    have h3 : (3 : ℝ) ≤ (p : ℝ) := by exact_mod_cast hp
    nlinarith
  have hhpos : ∀ x, 0 < x → 0 < drivingTerm p α mom x :=
    fun x hx => drivingTerm_pos hp hα (hmom 1 x hx) (hmom 2 x hx)
  have hfpos : ∀ x, 0 < x → 0 < mom p x := fun x hx => hmom p x hx
  have hderiv : ∀ x, 0 < x → HasDerivAt (fun s => mom p s)
      (c x * ∑ ℓ ∈ Finset.range p, ((p.choose ℓ : ℕ) : ℝ) * A ℓ x) x := hderivId
  have hasym := derivative_ratio_tendsto hp hα hmom hB hmass hAend hAmid hIH hc
  refine ⟨?_, lemma_I_4_21_regularlyVarying_of_hasDerivAt D hlin hlt hhpos hfpos
    hderiv hasym⟩
  have hbase := lemma_I_4_21_tendsto_of_hasDerivAt D hlin hlt hhpos hfpos hderiv hasym
  refine hbase.congr' ?_
  filter_upwards [eventually_gt_atTop (0 : ℝ)] with r hr
  have hba : (2 * (p : ℝ) - 1) * α - ((p : ℝ) + 1) * α = ((p : ℝ) - 2) * α :=
    drivingIndex_sub_linearIndex p α
  have hp2 : (0 : ℝ) < (p : ℝ) - 2 := by
    have h3 : (3 : ℝ) ≤ (p : ℝ) := by exact_mod_cast hp
    linarith
  rw [hba, drivingTerm_eq_smul]
  field_simp

/-! ### The base case `p = 3` of the second induction -/

/-- At `p = 3` the induction hypothesis is vacuous: the only order below `p`
is `m = 2`, for which `mixedMoment 2 mom = mom 2` identically.  Hence the
second induction step needs no previously established asymptotic there. -/
theorem induction_hypothesis_three {mom : ℕ → ℝ → ℝ}
    (hmom : ∀ m r, 0 < r → 0 < mom m r) :
    ∀ m, 2 ≤ m → m ≤ 3 - 1 →
      Tendsto (fun r => mom m r / mixedMoment m mom r) atTop (𝓝 1) := by
  intro m hm2 hm3
  have hm : m = 2 := by omega
  subst hm
  refine tendsto_const_nhds.congr' ?_
  filter_upwards [eventually_gt_atTop (0 : ℝ)] with r hr
  have h1 : 0 < mom 1 r := hmom 1 r hr
  have hR : momentRatio mom r = mom 2 r / mom 1 r := rfl
  unfold mixedMoment
  rw [hR]
  have hcast : ((2 : ℕ) : ℝ) - 1 = 1 := by norm_num
  rw [hcast, Real.rpow_one]
  norm_num [dblFact]
  have h2 : mom 2 r ≠ 0 := (hmom 2 r hr).ne'
  field_simp

/-- **The second induction step of Proposition I.4.20 at `p = 3`**, with the
induction hypothesis discharged: this is the full second-induction step at
`p = 3` from the percolation inputs alone. -/
theorem moment_three_asymptotic_of_decorrelation {α : ℝ} (hα : 0 < α)
    {mom : ℕ → ℝ → ℝ} {A : ℕ → ℝ → ℝ} {Bcard c : ℝ → ℝ}
    (hmom : ∀ m r, 0 < r → 0 < mom m r)
    (hmommeas1 : Measurable (mom 1)) (hmommeas2 : Measurable (mom 2))
    (h1 : RegularlyVaryingAtTop (mom 1) α)
    (h2 : RegularlyVaryingAtTop (mom 2) (3 * α))
    (hB : ∀ r, 0 < r → 0 < Bcard r)
    (hmass : ∀ r, 0 < r → A (3 - 1) r = A 0 r)
    (hderivId : ∀ r, 0 < r → HasDerivAt (fun s => mom 3 s)
      (c r * ∑ ℓ ∈ Finset.range 3, ((Nat.choose 3 ℓ : ℕ) : ℝ) * A ℓ r) r)
    (hAend : Tendsto (fun r => A 0 r / (Bcard r * (mom 1 r * mom 3 r))) atTop (𝓝 1))
    (hAmid : ∀ ℓ, 1 ≤ ℓ → ℓ ≤ 3 - 2 →
      Tendsto (fun r => A ℓ r / (Bcard r * (mom (ℓ + 1) r * mom (3 - ℓ) r))) atTop (𝓝 1))
    (hc : Tendsto (fun r => r * c r * Bcard r * mom 1 r) atTop (𝓝 α)) :
    Tendsto (fun r => mom 3 r / mixedMoment 3 mom r) atTop (𝓝 1) ∧
      RegularlyVaryingAtTop (mom 3) ((2 * (3 : ℝ) - 1) * α) :=
  moment_asymptotic_of_decorrelation (p := 3) (by norm_num) hα hmom hmommeas1 hmommeas2
    h1 h2 hB hmass hderivId hAend hAmid (induction_hypothesis_three hmom) hc

/-! ### The base moments `p = 1, 2` and the induction closed -/

/-- `mixedMoment 1` is the first moment itself: `(2·1-3)!! = (-1)!! = 1` and
`(E|K|²/E|K|)^0 = 1`. -/
theorem mixedMoment_one (mom : ℕ → ℝ → ℝ) (r : ℝ) : mixedMoment 1 mom r = mom 1 r := by
  unfold mixedMoment momentRatio
  norm_num [dblFact]

/-- `mixedMoment 2` is the second moment itself. -/
theorem mixedMoment_two {mom : ℕ → ℝ → ℝ} {r : ℝ} (h1 : mom 1 r ≠ 0) :
    mixedMoment 2 mom r = mom 2 r := by
  unfold mixedMoment momentRatio
  have h : ((2 : ℕ) : ℝ) - 1 = 1 := by norm_num
  rw [h, Real.rpow_one]
  norm_num [dblFact]
  field_simp

/-- **The second induction of Proposition I.4.20, closed.**  Assume the
percolation inputs uniformly in `p`: the exact derivative identity of Lemma
I.4.1, the mass-transport identity `A_0 = A_{p-1}`, the decorrelation estimates
(I.4.20) at every `ℓ`, the first-moment normalisation `r c_r |B_r| E|K| → α`, and
the regular variation of `E|K|` (index `α`) and `E|K|²` (index `3α`).  Then for
every `p ≥ 1`,

`E|K|^p ~ (2p-3)!! (E|K|²/E|K|)^(p-1) E|K|`

and `E|K|^p` is regularly varying of index `(2p-1)α`.  The induction hypothesis
of `moment_asymptotic_of_decorrelation` is discharged internally by strong
induction on `p`; the cases `p = 1, 2` are the identities
`mixedMoment 1 = E|K|` and `mixedMoment 2 = E|K|²`. -/
theorem moment_asymptotic_all {α : ℝ} (hα : 0 < α)
    (mom : ℕ → ℝ → ℝ) (A : ℕ → ℕ → ℝ → ℝ) (Bcard : ℕ → ℝ → ℝ) (c : ℕ → ℝ → ℝ)
    (hmom : ∀ m r, 0 < r → 0 < mom m r)
    (hmommeas1 : Measurable (mom 1)) (hmommeas2 : Measurable (mom 2))
    (h1 : RegularlyVaryingAtTop (mom 1) α)
    (h2 : RegularlyVaryingAtTop (mom 2) (3 * α))
    (hB : ∀ p r, 0 < r → 0 < Bcard p r)
    (hmass : ∀ p r, 0 < r → A p (p - 1) r = A p 0 r)
    (hderivId : ∀ p r, 0 < r → HasDerivAt (fun s => mom p s)
      (c p r * ∑ ℓ ∈ Finset.range p, ((p.choose ℓ : ℕ) : ℝ) * A p ℓ r) r)
    (hAend : ∀ p, Tendsto (fun r => A p 0 r / (Bcard p r * (mom 1 r * mom p r)))
      atTop (𝓝 1))
    (hAmid : ∀ p ℓ, 1 ≤ ℓ → ℓ ≤ p - 2 →
      Tendsto (fun r => A p ℓ r / (Bcard p r * (mom (ℓ + 1) r * mom (p - ℓ) r)))
        atTop (𝓝 1))
    (hc : ∀ p, Tendsto (fun r => r * c p r * Bcard p r * mom 1 r) atTop (𝓝 α)) :
    ∀ p, 1 ≤ p →
      Tendsto (fun r => mom p r / mixedMoment p mom r) atTop (𝓝 1) ∧
        RegularlyVaryingAtTop (mom p) ((2 * (p : ℝ) - 1) * α) := by
  intro p
  induction p using Nat.strong_induction_on with
  | _ p ih =>
    intro hp1
    rcases lt_or_ge p 3 with hlt | hge
    · -- `p = 1` or `p = 2`: the target is the moment itself
      have hp : p = 1 ∨ p = 2 := by omega
      rcases hp with rfl | rfl
      · refine ⟨?_, ?_⟩
        · refine tendsto_const_nhds.congr' ?_
          filter_upwards [eventually_gt_atTop (0 : ℝ)] with r hr
          rw [mixedMoment_one, div_self]
          exact (hmom 1 r hr).ne'
        · have hidx : (2 * ((1 : ℕ) : ℝ) - 1) * α = α := by norm_num
          rwa [hidx]
      · refine ⟨?_, ?_⟩
        · refine tendsto_const_nhds.congr' ?_
          filter_upwards [eventually_gt_atTop (0 : ℝ)] with r hr
          rw [mixedMoment_two (hmom 1 r hr).ne', div_self]
          exact (hmom 2 r hr).ne'
        · have hidx : (2 * ((2 : ℕ) : ℝ) - 1) * α = 3 * α := by norm_num
          rwa [hidx]
    · -- `p ≥ 3`: the induction step, with the induction hypothesis for `m < p`
      have hIH : ∀ m, 2 ≤ m → m ≤ p - 1 →
          Tendsto (fun r => mom m r / mixedMoment m mom r) atTop (𝓝 1) := by
        intro m hm2 hm3
        exact (ih m (by omega) (by omega)).1
      exact moment_asymptotic_of_decorrelation (p := p) hge hα hmom hmommeas1 hmommeas2
        h1 h2 (fun r hr => hB p r hr) (fun r hr => hmass p r hr) (fun r hr => hderivId p r hr)
        (hAend p) (fun ℓ h1' h2' => hAmid p ℓ h1' h2') hIH (hc p)

end PercLib.CriticalLRP.VolumeMoments.HigherMoments.SecondInduction
