/- Integrated from independently rebuilt Ultramath work.
Production base ed48eea0fa7697ac0e16db08e39b60ebb7c70e02.
Scratch source: ../../.ultramath/smwvlmbqa/m2/Main.lean; migrated to current namespaces.
-/

module

public import PercLib.CriticalLRP.VolumeMoments.HigherMoments.Assembly

/-!
# Proposition I.4.20: the general-`p` upper-bound induction step, assembled

Source: T. Hutchcroft, *Critical long-range percolation I: High effective
dimension*, arXiv:2508.18807v1, proof of Proposition I.4.20 (pp. 49--50).

`moment_upper_bound_of_percolation` below is the whole upper-bound induction
step (I.4.19) in general `p`, with every probabilistic input left visible:

* `hderivId` is the exact derivative identity of Lemma I.4.1, with
  `A ℓ x = E[|K|^{ℓ+1} ∑_{y∈B_x} 1(y∉K)|K_y|^{p-ℓ}]` and
  `c x = β|J'(x)|`;
* `hmass` is the mass-transport equality of the two end terms `ℓ = 0` and
  `ℓ = p-1`;
* `hA0`, `hAmid` are the decorrelation bounds of Lemma I.2.1;
* `hIH` is the induction hypothesis, i.e. (I.4.19) for all smaller moments;
* `hc` is the first-moment normalisation `β|J'(r)||B_r| E|K| ~ α/r` that
  Proposition I.4.2 supplies at criticality;
* `h1`, `h2` are the first- and second-moment regular variation of
  Propositions I.4.2 and I.4.15, which give the driving term index `(2p-1)α`.

The conclusion is exactly (I.4.19),
`E|K|^p ≤ (1+o(1))(2p-3)!!(E|K|²/E|K|)^(p-1)E|K|`, uniformly in a single
`ε`.  No step of the argument is hidden in a hypothesis that restates the
conclusion: the only assumptions about `mom` are its positivity, measurability
and the two regular-variation indices.
-/

@[expose] public section

noncomputable section

open Filter Set MeasureTheory
open PercLib.CriticalLRP.Analysis
open scoped Topology

namespace PercLib.CriticalLRP.VolumeMoments.HigherMoments

/-- **The upper-bound induction step (I.4.19) of Proposition I.4.20, in general
`p`.**  All probabilistic inputs are explicit percolation hypotheses; the
analytic content is the Lemma I.4.22 comparison with `a = (p+1)α`,
`b = (2p-1)α`, whose index gap `(p-2)α` cancels the constant of the driving
term. -/
theorem moment_upper_bound_of_percolation {p : ℕ} (hp : 3 ≤ p) {α : ℝ} (hα : 0 < α)
    {mom : ℕ → ℝ → ℝ} (hmom : ∀ m x, 0 < x → 0 < mom m x)
    (hmommeas1 : Measurable (mom 1)) (hmommeas2 : Measurable (mom 2))
    (h1 : RegularlyVaryingAtTop (mom 1) α)
    (h2 : RegularlyVaryingAtTop (mom 2) (3 * α))
    {c Bcard : ℝ → ℝ} {A : ℕ → ℝ → ℝ}
    (hB : ∀ x, 0 < x → 0 ≤ Bcard x) (hc0 : ∀ x, 0 < x → 0 ≤ c x)
    (hderivId : ∀ x, 0 < x → HasDerivAt (fun r => mom p r)
      (c x * (∑ ℓ ∈ Finset.range p, ((p.choose ℓ : ℕ) : ℝ) * A ℓ x)) x)
    (hmass : ∀ x, 0 < x → A 0 x = A (p - 1) x)
    (hA0 : ∀ x, 0 < x → A 0 x ≤ Bcard x * (mom 1 x * mom p x))
    (hAmid : ∀ x, 0 < x → ∀ ℓ, 1 ≤ ℓ → ℓ ≤ p - 2 →
      A ℓ x ≤ Bcard x * (mom (ℓ + 1) x * mom (p - ℓ) x))
    (hIH : ∀ ε > 0, ∀ᶠ x in atTop, ∀ m, 2 ≤ m → m ≤ p - 1 →
      mom m x ≤ (1 + ε) * dblFact (m - 1) * momentRatio mom x ^ ((m : ℝ) - 1) * mom 1 x)
    (hc : ∀ ε > 0, ∀ᶠ x in atTop, c x * Bcard x * mom 1 x * x ≤ (1 + ε) * α) :
    ∀ ε > 0, ∀ᶠ r in atTop, mom p r ≤ (1 + ε) * mixedMoment p mom r := by
  have hfbd : ∀ ε > 0, ∀ᶠ x in atTop,
      (c x * (∑ ℓ ∈ Finset.range p, ((p.choose ℓ : ℕ) : ℝ) * A ℓ x))
        ≤ (1 + ε) * (((p : ℝ) + 1) * α * mom p x + drivingTerm p α mom x) / x :=
    derivative_bound hp hα hmom hB hc0 hmass hA0 hAmid hIH hc
  exact moment_upper_bound hp hα hmom hmommeas1 hmommeas2 h1 h2 hderivId hfbd

/-- Unfolding the target: the conclusion of `moment_upper_bound_of_percolation`
is the paper's `E|K|^p ≤ (1+o(1))(2p-3)!!(E|K|²/E|K|)^(p-1)E|K|`. -/
theorem moment_upper_bound_of_percolation_unfolded {p : ℕ} (hp : 3 ≤ p) {α : ℝ}
    (hα : 0 < α)
    {mom : ℕ → ℝ → ℝ} (hmom : ∀ m x, 0 < x → 0 < mom m x)
    (hmommeas1 : Measurable (mom 1)) (hmommeas2 : Measurable (mom 2))
    (h1 : RegularlyVaryingAtTop (mom 1) α)
    (h2 : RegularlyVaryingAtTop (mom 2) (3 * α))
    {c Bcard : ℝ → ℝ} {A : ℕ → ℝ → ℝ}
    (hB : ∀ x, 0 < x → 0 ≤ Bcard x) (hc0 : ∀ x, 0 < x → 0 ≤ c x)
    (hderivId : ∀ x, 0 < x → HasDerivAt (fun r => mom p r)
      (c x * (∑ ℓ ∈ Finset.range p, ((p.choose ℓ : ℕ) : ℝ) * A ℓ x)) x)
    (hmass : ∀ x, 0 < x → A 0 x = A (p - 1) x)
    (hA0 : ∀ x, 0 < x → A 0 x ≤ Bcard x * (mom 1 x * mom p x))
    (hAmid : ∀ x, 0 < x → ∀ ℓ, 1 ≤ ℓ → ℓ ≤ p - 2 →
      A ℓ x ≤ Bcard x * (mom (ℓ + 1) x * mom (p - ℓ) x))
    (hIH : ∀ ε > 0, ∀ᶠ x in atTop, ∀ m, 2 ≤ m → m ≤ p - 1 →
      mom m x ≤ (1 + ε) * dblFact (m - 1) * momentRatio mom x ^ ((m : ℝ) - 1) * mom 1 x)
    (hc : ∀ ε > 0, ∀ᶠ x in atTop, c x * Bcard x * mom 1 x * x ≤ (1 + ε) * α) :
    ∀ ε > 0, ∀ᶠ r in atTop, mom p r ≤
      (1 + ε) * (dblFact (p - 1) * (mom 2 r / mom 1 r) ^ ((p : ℝ) - 1) * mom 1 r) := by
  simpa only [mixedMoment, momentRatio] using
    moment_upper_bound_of_percolation hp hα hmom hmommeas1 hmommeas2 h1 h2 hB hc0
      hderivId hmass hA0 hAmid hIH hc

/-! ### The base case of the induction hypothesis at `p = 3` -/

/-- At `p = 3` the induction hypothesis `hIH` of
`moment_upper_bound_of_percolation` is automatic: the only smaller moment with
`2 ≤ m ≤ p-1` is `m = 2`, for which the inequality is
`E|K|² ≤ (1+δ)(E|K|²/E|K|)E|K|`.  Thus the general theorem specialises to the
full step (I.4.19) at `p = 3` with no induction hypothesis to verify. -/
theorem induction_hypothesis_three {mom : ℕ → ℝ → ℝ} {x : ℝ}
    (h1 : 0 < mom 1 x) (h2 : 0 ≤ mom 2 x) {ε : ℝ} (hε : 0 ≤ ε) :
    ∀ m, 2 ≤ m → m ≤ 3 - 1 →
      mom m x ≤ (1 + ε) * dblFact (m - 1) * momentRatio mom x ^ ((m : ℝ) - 1) * mom 1 x := by
  intro m hm2 hm3
  have hm : m = 2 := by omega
  subst hm
  have hcast : ((2 : ℕ) : ℝ) - 1 = 1 := by norm_num
  rw [hcast, Real.rpow_one, dblFact_one]
  unfold momentRatio
  have hne : mom 1 x ≠ 0 := h1.ne'
  field_simp
  nlinarith

/-! ### The `p = 3` instance, with no induction hypothesis -/

/-- **Proposition I.4.20's step (I.4.19) at `p = 3`, with no induction
hypothesis.**  The `hIH` of `moment_upper_bound_of_percolation` is discharged by
`induction_hypothesis_three`, so this is the full upper-bound induction step at
`p = 3` from the percolation inputs alone. -/
theorem moment_upper_bound_three {α : ℝ} (hα : 0 < α)
    {mom : ℕ → ℝ → ℝ} (hmom : ∀ m x, 0 < x → 0 < mom m x)
    (hmommeas1 : Measurable (mom 1)) (hmommeas2 : Measurable (mom 2))
    (h1 : RegularlyVaryingAtTop (mom 1) α)
    (h2 : RegularlyVaryingAtTop (mom 2) (3 * α))
    {c Bcard : ℝ → ℝ} {A : ℕ → ℝ → ℝ}
    (hB : ∀ x, 0 < x → 0 ≤ Bcard x) (hc0 : ∀ x, 0 < x → 0 ≤ c x)
    (hderivId : ∀ x, 0 < x → HasDerivAt (fun r => mom 3 r)
      (c x * (∑ ℓ ∈ Finset.range 3, ((Nat.choose 3 ℓ : ℕ) : ℝ) * A ℓ x)) x)
    (hmass : ∀ x, 0 < x → A 0 x = A (3 - 1) x)
    (hA0 : ∀ x, 0 < x → A 0 x ≤ Bcard x * (mom 1 x * mom 3 x))
    (hAmid : ∀ x, 0 < x → ∀ ℓ, 1 ≤ ℓ → ℓ ≤ 3 - 2 →
      A ℓ x ≤ Bcard x * (mom (ℓ + 1) x * mom (3 - ℓ) x))
    (hc : ∀ ε > 0, ∀ᶠ x in atTop, c x * Bcard x * mom 1 x * x ≤ (1 + ε) * α) :
    ∀ ε > 0, ∀ᶠ r in atTop, mom 3 r ≤ (1 + ε) * mixedMoment 3 mom r := by
  have hIH : ∀ ε > 0, ∀ᶠ x in atTop, ∀ m, 2 ≤ m → m ≤ 3 - 1 →
      mom m x ≤ (1 + ε) * dblFact (m - 1) * momentRatio mom x ^ ((m : ℝ) - 1) * mom 1 x := by
    intro ε hε
    filter_upwards [eventually_gt_atTop (0 : ℝ)] with x hx
    exact induction_hypothesis_three (hmom 1 x hx) (hmom 2 x hx).le hε.le
  exact moment_upper_bound_of_percolation (p := 3) (by norm_num) hα hmom hmommeas1 hmommeas2
    h1 h2 hB hc0 hderivId hmass hA0 hAmid hIH hc

/-! ### Sanity checks of the constants at `p = 3` -/

example : dblFact 2 = 3 := by
  norm_num [dblFact, M]

example (α : ℝ) (mom : ℕ → ℝ → ℝ) (r : ℝ) :
    drivingTerm 3 α mom r = α * (3 * (mom 2 r / mom 1 r) ^ (2 : ℝ) * mom 1 r) := by
  unfold drivingTerm dblFact momentRatio
  norm_num
  ring

example (mom : ℕ → ℝ → ℝ) (r : ℝ) :
    mixedMoment 3 mom r = 3 * (mom 2 r / mom 1 r) ^ (2 : ℝ) * mom 1 r := by
  unfold mixedMoment dblFact momentRatio
  norm_num

/-- The base case `p = 1` of the target is `E|K|` itself. -/
example (mom : ℕ → ℝ → ℝ) (r : ℝ) : mixedMoment 1 mom r = mom 1 r := by
  unfold mixedMoment dblFact momentRatio
  norm_num

/-- The base case `p = 2` of the target is `E|K|²`. -/
example {mom : ℕ → ℝ → ℝ} {r : ℝ} (h : mom 1 r ≠ 0) :
    mixedMoment 2 mom r = mom 2 r := by
  unfold mixedMoment dblFact momentRatio
  norm_num
  field_simp

end PercLib.CriticalLRP.VolumeMoments.HigherMoments
