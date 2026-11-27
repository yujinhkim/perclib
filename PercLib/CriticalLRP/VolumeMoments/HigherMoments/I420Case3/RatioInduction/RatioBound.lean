/-
Integrated Ultramath work, swarm `smwyop3kc`, member `m2`.
Production worktree: `.scratch/critical-lrp-orchestration` (read only), HEAD
`2e544875fbae83810bd1aa1de1d8faddcdeacc05`.
-/

module

public import PercLib.CriticalLRP.VolumeMoments.HigherMoments.Main
public import PercLib.CriticalLRP.VolumeMoments.HigherMoments.I420Case3.RatioInduction.Defs

/-!
# The I.4.19 induction step from decorrelation *ratios* instead of pointwise bounds

`HigherMoments.derivative_bound_three`/`derivative_bound` consume the
decorrelation estimates of Lemma I.2.1 in the shape

`A_ℓ(r) ≤ |B_r| E|K|^{ℓ+1} E|K|^{p-ℓ}`   (pointwise, every `r > 0`),

with the two end terms identified by mass transport.  The Case-3 development of
`I420Case3` (and likewise Cases 1 and 2) produces the *normalized* limits

`A_ℓ(r) / (|B_r| E|K|^{ℓ+1} E|K|^{p-ℓ}) → 1`,

which only give the pointwise bound up to `1 + o(1)`.

This file records that the `1 + o(1)` form is enough: `derivative_bound_ratio`
proves the derivative comparison of Proposition I.4.20 with `hA0` and `hAmid`
replaced by those two limits, at the cost of a single extra power of `1 + δ`
which is absorbed by `exists_one_add_pow_four_le`.  `moment_upper_bound_three_ratio`
then instantiates the shipped `moment_upper_bound` at `p = 3` with no induction
hypothesis (as in `moment_upper_bound_three`), and
`moment_upper_bound_three_ratio_of_pos` weakens the positivity input `hmom` from
"every order `m`" to the orders `1, 2, 3` that are actually consumed, using the
padding `padMom`.

No step of the argument assumes a higher moment finite: `humom` is positive at
three concrete orders only, and no finiteness is derived from the first moment.
-/

@[expose] public section

noncomputable section

open Filter Set MeasureTheory
open PercLib.CriticalLRP.Analysis
open scoped Topology

namespace PercLib.CriticalLRP.VolumeMoments.HigherMoments

/-- A ratio tending to `1` gives, against a positive denominator, an eventual
multiplicative bound with any prescribed slack. -/
theorem eventually_le_mul_of_tendsto_div_one {f g : ℝ → ℝ}
    (hg : ∀ᶠ x in atTop, 0 < g x)
    (h : Tendsto (fun x => f x / g x) atTop (𝓝 1)) {δ : ℝ} (hδ : 0 < δ) :
    ∀ᶠ x in atTop, f x ≤ (1 + δ) * g x := by
  have hlt : ∀ᶠ x : ℝ in atTop, f x / g x < 1 + δ :=
    h.eventually (Iio_mem_nhds (by linarith))
  filter_upwards [hlt, hg] with x hx hgx
  have h' : f x < (1 + δ) * g x := (div_lt_iff₀ hgx).mp hx
  linarith

/-- For every `ε > 0` there is `δ > 0` with `(1 + δ)^4 ≤ 1 + ε`. -/
theorem exists_one_add_pow_four_le {ε : ℝ} (hε : 0 < ε) :
    ∃ δ : ℝ, 0 < δ ∧ (1 + δ) ^ 4 ≤ 1 + ε := by
  have h0 : (0 : ℝ) < min (ε / 16) 1 := lt_min (by positivity) one_pos
  refine ⟨min (ε / 16) 1, h0, ?_⟩
  have h1 : min (ε / 16) 1 ≤ 1 := min_le_right _ _
  have h2 : 16 * min (ε / 16) 1 ≤ ε := by
    have := min_le_left (ε / 16) 1
    linarith
  have hsq : min (ε / 16) 1 ^ 2 ≤ min (ε / 16) 1 := by nlinarith
  have hcb : min (ε / 16) 1 ^ 3 ≤ min (ε / 16) 1 := by nlinarith
  have hqd : min (ε / 16) 1 ^ 4 ≤ min (ε / 16) 1 := by nlinarith [sq_nonneg (min (ε / 16) 1)]
  have hexp : (1 + min (ε / 16) 1) ^ 4
      = 1 + 4 * min (ε / 16) 1 + 6 * min (ε / 16) 1 ^ 2 +
        4 * min (ε / 16) 1 ^ 3 + min (ε / 16) 1 ^ 4 := by ring
  rw [hexp]
  linarith

/-- **The derivative comparison of Proposition I.4.20 from decorrelation ratios.**

Identical in content to `derivative_bound`, except that the pointwise
decorrelation bounds `hA0` and `hAmid` are replaced by the normalized limits
that the three cases of Proposition I.4.20 produce, and `hB` is required to be
positive so that the limits can be converted into eventual inequalities. -/
theorem derivative_bound_ratio {p : ℕ} (hp : 3 ≤ p) {α : ℝ} (hα : 0 < α)
    {mom : ℕ → ℝ → ℝ} {c Bcard : ℝ → ℝ} {A : ℕ → ℝ → ℝ}
    (hmom : ∀ m x, 0 < x → 0 < mom m x)
    (hB : ∀ x, 0 < x → 0 < Bcard x) (hc0 : ∀ x, 0 < x → 0 ≤ c x)
    (hmass : ∀ x, 0 < x → A 0 x = A (p - 1) x)
    (hAend : Tendsto (fun x => A 0 x / (Bcard x * (mom 1 x * mom p x))) atTop (𝓝 1))
    (hAmid : ∀ ℓ, 1 ≤ ℓ → ℓ ≤ p - 2 →
      Tendsto (fun x => A ℓ x / (Bcard x * (mom (ℓ + 1) x * mom (p - ℓ) x))) atTop (𝓝 1))
    (hIH : ∀ ε > 0, ∀ᶠ x in atTop, ∀ m, 2 ≤ m → m ≤ p - 1 →
      mom m x ≤ (1 + ε) * dblFact (m - 1) * momentRatio mom x ^ ((m : ℝ) - 1) * mom 1 x)
    (hc : ∀ ε > 0, ∀ᶠ x in atTop, c x * Bcard x * mom 1 x * x ≤ (1 + ε) * α) :
    ∀ ε > 0, ∀ᶠ x in atTop,
      c x * (∑ ℓ ∈ Finset.range p, ((p.choose ℓ : ℕ) : ℝ) * A ℓ x)
        ≤ (1 + ε) * (((p : ℝ) + 1) * α * mom p x + drivingTerm p α mom x) / x := by
  intro ε hε
  obtain ⟨δ, hδpos, hδε⟩ := exists_one_add_pow_four_le hε
  have hδ : 0 ≤ δ := hδpos.le
  have h1δ : (0 : ℝ) < 1 + δ := by linarith
  -- the slack `1 + δ` is moved into the window cardinality
  have hgev : ∀ᶠ x : ℝ in atTop, 0 < Bcard x * (mom 1 x * mom p x) :=
    (eventually_gt_atTop (0 : ℝ)).mono fun x hx =>
      mul_pos (hB x hx) (mul_pos (hmom 1 x hx) (hmom p x hx))
  have hA0ev : ∀ᶠ x : ℝ in atTop,
      A 0 x ≤ ((1 + δ) * Bcard x) * (mom 1 x * mom p x) :=
    (eventually_le_mul_of_tendsto_div_one hgev hAend hδpos).mono fun x hx => by
      simpa only [mul_assoc] using hx
  have hAmidev : ∀ᶠ x : ℝ in atTop, ∀ ℓ, 1 ≤ ℓ → ℓ ≤ p - 2 →
      A ℓ x ≤ ((1 + δ) * Bcard x) * (mom (ℓ + 1) x * mom (p - ℓ) x) := by
    have key : ∀ ℓ ∈ Finset.range p, ∀ᶠ x : ℝ in atTop,
        (1 ≤ ℓ → ℓ ≤ p - 2 →
          A ℓ x ≤ ((1 + δ) * Bcard x) * (mom (ℓ + 1) x * mom (p - ℓ) x)) := by
      intro ℓ _
      by_cases h1 : 1 ≤ ℓ
      · by_cases h2 : ℓ ≤ p - 2
        · have hg : ∀ᶠ x : ℝ in atTop,
              0 < Bcard x * (mom (ℓ + 1) x * mom (p - ℓ) x) :=
            (eventually_gt_atTop (0 : ℝ)).mono fun x hx =>
              mul_pos (hB x hx) (mul_pos (hmom (ℓ + 1) x hx) (hmom (p - ℓ) x hx))
          exact (eventually_le_mul_of_tendsto_div_one hg (hAmid ℓ h1 h2) hδpos).mono
            fun x hx => fun _ _ => by simpa only [mul_assoc] using hx
        · exact Eventually.of_forall fun _ _ h2' => (h2 h2').elim
      · exact Eventually.of_forall fun _ h1' _ => (h1 h1').elim
    filter_upwards [(Filter.eventually_all_finset (Finset.range p)).mpr key] with x hx
    exact fun ℓ h1 h2 => hx ℓ (Finset.mem_range.mpr (by omega)) h1 h2
  filter_upwards [eventually_gt_atTop (0 : ℝ), hIH δ hδpos, hc δ hδpos, hA0ev, hAmidev]
    with x hx hIHx hcx hA0x hAmidx
  have h1x : 0 < mom 1 x := hmom 1 x hx
  have h2x : 0 < mom 2 x := hmom 2 x hx
  have hPx : 0 < mom p x := hmom p x hx
  have hBx : (0 : ℝ) ≤ (1 + δ) * Bcard x := by
    have := hB x hx
    nlinarith
  have hsum := sum_bound (p := p) hp (mom := mom) (Bcard := fun x => (1 + δ) * Bcard x)
    (A := A) (r := x) (δ := δ) hδ hBx (fun m => (hmom m x hx).le) h1x h2x
    (hmass x hx) hA0x hAmidx hIHx
  have hmul := mul_le_mul_of_nonneg_left hsum (hc0 x hx)
  -- the end terms
  have T1 : c x * ((1 + δ) * Bcard x * ((p : ℝ) + 1) * (mom 1 x * mom p x))
      ≤ (1 + δ) ^ 2 * (((p : ℝ) + 1) * α * mom p x / x) := by
    have hfac : c x * ((1 + δ) * Bcard x * ((p : ℝ) + 1) * (mom 1 x * mom p x))
        = (1 + δ) * (c x * Bcard x * mom 1 x * x) *
            (((p : ℝ) + 1) * mom p x / x) := by
      field_simp
    rw [hfac]
    have hnn : (0 : ℝ) ≤ ((p : ℝ) + 1) * mom p x / x := by positivity
    have hstep : (1 + δ) * (c x * Bcard x * mom 1 x * x) ≤ (1 + δ) * ((1 + δ) * α) :=
      mul_le_mul_of_nonneg_left hcx (by linarith)
    calc (1 + δ) * (c x * Bcard x * mom 1 x * x) * (((p : ℝ) + 1) * mom p x / x)
        ≤ ((1 + δ) * ((1 + δ) * α)) * (((p : ℝ) + 1) * mom p x / x) :=
          mul_le_mul_of_nonneg_right hstep hnn
      _ = (1 + δ) ^ 2 * (((p : ℝ) + 1) * α * mom p x / x) := by
          field_simp
  -- the middle terms
  have T2 : c x * ((1 + δ) * Bcard x * (1 + δ) ^ 2 *
        (((p : ℝ) - 2) * mixedMoment p mom x * mom 1 x))
      ≤ (1 + δ) ^ 4 * (drivingTerm p α mom x / x) := by
    have hfac : c x * ((1 + δ) * Bcard x * (1 + δ) ^ 2 *
          (((p : ℝ) - 2) * mixedMoment p mom x * mom 1 x))
        = (c x * Bcard x * mom 1 x * x) *
            ((1 + δ) ^ 3 * (((p : ℝ) - 2) * mixedMoment p mom x) / x) := by
      field_simp
    rw [hfac]
    have hnn : (0 : ℝ) ≤ (1 + δ) ^ 3 * (((p : ℝ) - 2) * mixedMoment p mom x) / x := by
      have hd : 0 ≤ (1 + δ) ^ 3 := by positivity
      have hm : 0 < ((p : ℝ) - 2) * mixedMoment p mom x := by
        have hp2 : (0 : ℝ) < (p : ℝ) - 2 := by
          have h3 : (3 : ℝ) ≤ (p : ℝ) := by exact_mod_cast hp
          linarith
        have := mixedMoment_pos (p := p) h1x h2x
        positivity
      positivity
    calc (c x * Bcard x * mom 1 x * x) *
          ((1 + δ) ^ 3 * (((p : ℝ) - 2) * mixedMoment p mom x) / x)
        ≤ ((1 + δ) * α) *
          ((1 + δ) ^ 3 * (((p : ℝ) - 2) * mixedMoment p mom x) / x) :=
          mul_le_mul_of_nonneg_right hcx hnn
      _ = (1 + δ) ^ 4 * (drivingTerm p α mom x / x) := by
          rw [drivingTerm_eq_smul]
          field_simp
  have hexp : c x * ((1 + δ) * Bcard x * ((p : ℝ) + 1) * (mom 1 x * mom p x)
        + (1 + δ) * Bcard x * (1 + δ) ^ 2 *
            (((p : ℝ) - 2) * mixedMoment p mom x * mom 1 x))
      = c x * ((1 + δ) * Bcard x * ((p : ℝ) + 1) * (mom 1 x * mom p x))
        + c x * ((1 + δ) * Bcard x * (1 + δ) ^ 2 *
            (((p : ℝ) - 2) * mixedMoment p mom x * mom 1 x)) := by ring
  rw [hexp] at hmul
  have hmain : c x * (∑ ℓ ∈ Finset.range p, ((p.choose ℓ : ℕ) : ℝ) * A ℓ x)
      ≤ (1 + δ) ^ 2 * (((p : ℝ) + 1) * α * mom p x / x)
        + (1 + δ) ^ 4 * (drivingTerm p α mom x / x) :=
    hmul.trans (add_le_add T1 T2)
  -- absorb the slack
  have hmono : (1 + δ) ^ 2 ≤ (1 + δ) ^ 4 :=
    pow_le_pow_right₀ (by linarith : (1 : ℝ) ≤ 1 + δ) (by norm_num : 2 ≤ 4)
  have hA1 : (0 : ℝ) ≤ ((p : ℝ) + 1) * α * mom p x / x := by positivity
  have hB1 : (0 : ℝ) ≤ drivingTerm p α mom x / x := by
    have := drivingTerm_pos (p := p) hp hα h1x h2x
    positivity
  have hstep1 : (1 + δ) ^ 2 * (((p : ℝ) + 1) * α * mom p x / x)
      ≤ (1 + δ) ^ 4 * (((p : ℝ) + 1) * α * mom p x / x) :=
    mul_le_mul_of_nonneg_right hmono hA1
  have hnum : (0 : ℝ) ≤ (((p : ℝ) + 1) * α * mom p x + drivingTerm p α mom x) / x := by
    have hd : 0 < drivingTerm p α mom x := drivingTerm_pos (p := p) hp hα h1x h2x
    positivity
  calc c x * (∑ ℓ ∈ Finset.range p, ((p.choose ℓ : ℕ) : ℝ) * A ℓ x)
      ≤ (1 + δ) ^ 2 * (((p : ℝ) + 1) * α * mom p x / x)
          + (1 + δ) ^ 4 * (drivingTerm p α mom x / x) := hmain
    _ ≤ (1 + δ) ^ 4 * (((p : ℝ) + 1) * α * mom p x / x)
          + (1 + δ) ^ 4 * (drivingTerm p α mom x / x) := by linarith [hstep1]
    _ = (1 + δ) ^ 4 *
          ((((p : ℝ) + 1) * α * mom p x + drivingTerm p α mom x) / x) := by
        field_simp
    _ ≤ (1 + ε) *
          ((((p : ℝ) + 1) * α * mom p x + drivingTerm p α mom x) / x) :=
        mul_le_mul_of_nonneg_right hδε hnum
    _ = (1 + ε) *
          (((p : ℝ) + 1) * α * mom p x + drivingTerm p α mom x) / x := by
        rw [mul_div_assoc]

/-- **Proposition I.4.20's step (I.4.19) from the decorrelation ratio limits**,
in general `p`. -/
theorem moment_upper_bound_of_percolation_ratio {p : ℕ} (hp : 3 ≤ p) {α : ℝ}
    (hα : 0 < α)
    {mom : ℕ → ℝ → ℝ} (hmom : ∀ m x, 0 < x → 0 < mom m x)
    (hmommeas1 : Measurable (mom 1)) (hmommeas2 : Measurable (mom 2))
    (h1 : RegularlyVaryingAtTop (mom 1) α)
    (h2 : RegularlyVaryingAtTop (mom 2) (3 * α))
    {c Bcard : ℝ → ℝ} {A : ℕ → ℝ → ℝ}
    (hB : ∀ x, 0 < x → 0 < Bcard x) (hc0 : ∀ x, 0 < x → 0 ≤ c x)
    (hderivId : ∀ x, 0 < x → HasDerivAt (fun r => mom p r)
      (c x * (∑ ℓ ∈ Finset.range p, ((p.choose ℓ : ℕ) : ℝ) * A ℓ x)) x)
    (hmass : ∀ x, 0 < x → A 0 x = A (p - 1) x)
    (hAend : Tendsto (fun x => A 0 x / (Bcard x * (mom 1 x * mom p x))) atTop (𝓝 1))
    (hAmid : ∀ ℓ, 1 ≤ ℓ → ℓ ≤ p - 2 →
      Tendsto (fun x => A ℓ x / (Bcard x * (mom (ℓ + 1) x * mom (p - ℓ) x))) atTop (𝓝 1))
    (hIH : ∀ ε > 0, ∀ᶠ x in atTop, ∀ m, 2 ≤ m → m ≤ p - 1 →
      mom m x ≤ (1 + ε) * dblFact (m - 1) * momentRatio mom x ^ ((m : ℝ) - 1) * mom 1 x)
    (hc : ∀ ε > 0, ∀ᶠ x in atTop, c x * Bcard x * mom 1 x * x ≤ (1 + ε) * α) :
    ∀ ε > 0, ∀ᶠ r in atTop, mom p r ≤ (1 + ε) * mixedMoment p mom r :=
  moment_upper_bound hp hα hmom hmommeas1 hmommeas2 h1 h2 hderivId
    (derivative_bound_ratio hp hα hmom hB hc0 hmass hAend hAmid hIH hc)

/-- **The `p = 3` instance with no induction hypothesis**, fed by ratio limits.

This is `moment_upper_bound_three` with `hA0`/`hAmid` replaced by the two
normalized limits `A_0 / (|B_r| E|K| · E|K|³) → 1` and
`A_1 / (|B_r| E|K|² · E|K|²) → 1` that the Case-3 (and Case-1/2) analyses
produce, and with the mass-transport identification of the two end terms kept
explicit. -/
theorem moment_upper_bound_three_ratio {α : ℝ} (hα : 0 < α)
    {mom : ℕ → ℝ → ℝ} (hmom : ∀ m x, 0 < x → 0 < mom m x)
    (hmommeas1 : Measurable (mom 1)) (hmommeas2 : Measurable (mom 2))
    (h1 : RegularlyVaryingAtTop (mom 1) α) (h2 : RegularlyVaryingAtTop (mom 2) (3 * α))
    {c Bcard : ℝ → ℝ} {A : ℕ → ℝ → ℝ}
    (hB : ∀ x, 0 < x → 0 < Bcard x) (hc0 : ∀ x, 0 < x → 0 ≤ c x)
    (hderivId : ∀ x, 0 < x → HasDerivAt (fun r => mom 3 r)
      (c x * (∑ ℓ ∈ Finset.range 3, ((Nat.choose 3 ℓ : ℕ) : ℝ) * A ℓ x)) x)
    (hmass : ∀ x, 0 < x → A 0 x = A (3 - 1) x)
    (hAend : Tendsto (fun x => A 0 x / (Bcard x * (mom 1 x * mom 3 x))) atTop (𝓝 1))
    (hAmid : ∀ ℓ, 1 ≤ ℓ → ℓ ≤ 3 - 2 →
      Tendsto (fun x => A ℓ x / (Bcard x * (mom (ℓ + 1) x * mom (3 - ℓ) x))) atTop (𝓝 1))
    (hc : ∀ ε > 0, ∀ᶠ x in atTop, c x * Bcard x * mom 1 x * x ≤ (1 + ε) * α) :
    ∀ ε > 0, ∀ᶠ r in atTop, mom 3 r ≤ (1 + ε) * mixedMoment 3 mom r := by
  have hIH : ∀ ε > 0, ∀ᶠ x in atTop, ∀ m, 2 ≤ m → m ≤ 3 - 1 →
      mom m x ≤ (1 + ε) * dblFact (m - 1) * momentRatio mom x ^ ((m : ℝ) - 1) * mom 1 x := by
    intro ε hε
    filter_upwards [eventually_gt_atTop (0 : ℝ)] with x hx
    exact induction_hypothesis_three (hmom 1 x hx) (hmom 2 x hx).le hε.le
  exact moment_upper_bound_of_percolation_ratio (p := 3) (by norm_num) hα hmom hmommeas1
    hmommeas2 h1 h2 hB hc0 hderivId hmass hAend hAmid hIH hc

/-- **The `p = 3` instance with positivity only at orders `1, 2, 3`.**

Identical to `moment_upper_bound_three_ratio`, but `hmom` is required only at
the three orders that the induction step consumes; the padding `padMom`
discharges every other order.  This is the form in which the canonical cutoff
model can supply the input: no all-order moment finiteness is assumed. -/
theorem moment_upper_bound_three_ratio_of_pos {α : ℝ} (hα : 0 < α)
    {mom : ℕ → ℝ → ℝ}
    (hmom : ∀ m, 1 ≤ m → m ≤ 3 → ∀ x, 0 < x → 0 < mom m x)
    (hmommeas1 : Measurable (mom 1)) (hmommeas2 : Measurable (mom 2))
    (h1 : RegularlyVaryingAtTop (mom 1) α) (h2 : RegularlyVaryingAtTop (mom 2) (3 * α))
    {c Bcard : ℝ → ℝ} {A : ℕ → ℝ → ℝ}
    (hB : ∀ x, 0 < x → 0 < Bcard x) (hc0 : ∀ x, 0 < x → 0 ≤ c x)
    (hderivId : ∀ x, 0 < x → HasDerivAt (fun r => mom 3 r)
      (c x * (∑ ℓ ∈ Finset.range 3, ((Nat.choose 3 ℓ : ℕ) : ℝ) * A ℓ x)) x)
    (hmass : ∀ x, 0 < x → A 0 x = A (3 - 1) x)
    (hAend : Tendsto (fun x => A 0 x / (Bcard x * (mom 1 x * mom 3 x))) atTop (𝓝 1))
    (hAmid : ∀ ℓ, 1 ≤ ℓ → ℓ ≤ 3 - 2 →
      Tendsto (fun x => A ℓ x / (Bcard x * (mom (ℓ + 1) x * mom (3 - ℓ) x))) atTop (𝓝 1))
    (hc : ∀ ε > 0, ∀ᶠ x in atTop, c x * Bcard x * mom 1 x * x ≤ (1 + ε) * α) :
    ∀ ε > 0, ∀ᶠ r in atTop, mom 3 r ≤ (1 + ε) * mixedMoment 3 mom r := by
  have hmem1 : padMom 3 mom 1 = mom 1 :=
    funext fun r => padMom_apply_of_mem mom r ⟨le_refl 1, by norm_num⟩
  have hmem2 : padMom 3 mom 2 = mom 2 :=
    funext fun r => padMom_apply_of_mem mom r ⟨by norm_num, by norm_num⟩
  have hmem3 : padMom 3 mom 3 = mom 3 :=
    funext fun r => padMom_apply_of_mem mom r ⟨by norm_num, by norm_num⟩
  have hmain := moment_upper_bound_three_ratio (mom := padMom 3 mom) hα
    (padMom_pos hmom) (by rw [hmem1]; exact hmommeas1)
    (by rw [hmem2]; exact hmommeas2)
    (by rw [hmem1]; exact h1) (by rw [hmem2]; exact h2) hB hc0
    (fun x hx => by rw [hmem3]; exact hderivId x hx) hmass
    (by rw [hmem1, hmem3]; exact hAend)
    (fun ℓ h1ℓ h2ℓ => by
      refine (hAmid ℓ h1ℓ h2ℓ).congr' (Eventually.of_forall fun x => ?_)
      have hA : padMom 3 mom (ℓ + 1) x = mom (ℓ + 1) x :=
        padMom_apply_of_mem mom x ⟨by omega, by omega⟩
      have hB : padMom 3 mom (3 - ℓ) x = mom (3 - ℓ) x :=
        padMom_apply_of_mem mom x ⟨by omega, by omega⟩
      simp only [hA, hB])
    hc
  refine fun ε hε => (hmain ε hε).mono fun r hr => ?_
  rwa [hmem3, mixedMoment_padMom 3 (by norm_num) mom r] at hr

end PercLib.CriticalLRP.VolumeMoments.HigherMoments
