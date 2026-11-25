/-
Migration source: https://github.com/yujinhkim/Critical-Long-range-percolation
Integration revision: 3b3d1d0e43ef940bfaa2292ee5c2ee094ac4edbf
Licence: Apache-2.0 for the PercLib Lean sources and tooling; see third_party/critical-lrp/.
-/

module

public import PercLib.CriticalLRP.VolumeMoments.ErrorTerms
public import PercLib.CriticalLRP.VolumeMoments.ODELowerComparison
public import PercLib.CriticalLRP.LatticeGeometry.Cell.Asymptotic

/-
Hutchcroft, *Critical long-range percolation I: High effective dimension*,
arXiv:2508.18807v1, Section I.4.1, Corollary I.4.8.

This module proves the scalar lower-comparison argument and its two error-term
inputs: `E₁ ≥ 0` gives `1 - Ē₁ ≤ 1 - E₀`, and a power-law derivative together
with Lemma I.4.6 gives `1 - E₀ → 1`. The conclusions are eventual lower bounds,
equivalently the source liminf bound.

The cutoff-model identification of the differentiated first moment and its
divergence remain explicit hypotheses. This is an analytic component of
Corollary I.4.8, not a construction of those missing model inputs.
-/

noncomputable section

@[expose] public section

open Filter
open scoped Topology Asymptotics

namespace PercLib.CriticalLRP.VolumeMoments.FirstMoment

/-! ### A perturbed lower comparison -/

/-- **Corollary I.4.8, analytic core.**  If the multiplicative error `h` of the
first-moment ODE satisfies `h ≥ -o(1)` (in particular if `h` is nonnegative
eventually, or `h ≥ E0` with `E0 → 0`), then `lim inf_{r→∞} r^{-α} f r ≥ α/A`.

The conclusion is stated in the equivalent eventual form
`∀ c < α/A, ∀ᶠ r, c r^α ≤ f r`.  No measurability, boundedness or continuity of
`h` is required, and no dimensional hypothesis. -/
theorem first_moment_liminf_lower_bound {f f' h : ℝ → ℝ} {A α r₀ : ℝ}
    (hA : 0 < A) (hα : 0 < α) (hr₀ : 0 < r₀)
    (hderiv : ∀ t, r₀ ≤ t → HasDerivAt f (f' t) t)
    (hpos : ∀ t, r₀ ≤ t → 0 < f t)
    (hinf : Tendsto f atTop atTop)
    (hode : ∀ t, r₀ ≤ t → f' t = A * (1 - h t) * t ^ (-α - 1) * (f t) ^ 2)
    (hbelow : ∀ ε > 0, ∀ᶠ t : ℝ in atTop, -ε ≤ h t) :
    ∀ c, c < α / A → ∀ᶠ r : ℝ in atTop, c * r ^ α ≤ f r := by
  intro c hc
  rcases le_or_gt c 0 with hc0 | hc0
  · -- `c ≤ 0`: the bound is trivial since `f > 0` and `r^α ≥ 0`
    filter_upwards [eventually_ge_atTop (max r₀ 1)] with r hr
    have hr₀' : r₀ ≤ r := le_trans (le_max_left _ _) hr
    have hr1 : 1 ≤ r := le_trans (le_max_right _ _) hr
    have hrpos : 0 < r := lt_of_lt_of_le zero_lt_one hr1
    have hpow : 0 ≤ r ^ α := Real.rpow_nonneg hrpos.le α
    have hf : 0 < f r := hpos r hr₀'
    nlinarith
  · -- `c > 0`: compare with the ODE `f' ≤ A(1+ε) r^{-α-1} f²`
    set ε : ℝ := (α / (A * c) - 1) / 2 with hεdef
    have hAc : 0 < A * c := mul_pos hA hc0
    have hAne : A ≠ 0 := ne_of_gt hA
    have hlt : 1 < α / (A * c) := by
      have hcA : c * A < α := (lt_div_iff₀ hA).1 hc
      rw [lt_div_iff₀ hAc]
      linarith
    have hεpos : 0 < ε := by
      rw [hεdef]; linarith
    have hεc : (1 + ε) * c ≤ α / A := by
      have h1 : (1 + ε) * c = (c + α / A) / 2 := by
        rw [hεdef]; field_simp; ring
      rw [h1]; linarith
    obtain ⟨R, hR⟩ := eventually_atTop.1 (hbelow ε hεpos)
    set R' : ℝ := max r₀ R with hR'def
    have hR'pos : 0 < R' := lt_of_lt_of_le hr₀ (le_max_left _ _)
    have hcmp : ∀ x, R' ≤ x → f' x ≤ A * (1 + ε) * x ^ (-α - 1) * (f x) ^ 2 := by
      intro x hx
      have hxr : r₀ ≤ x := le_trans (le_max_left _ _) hx
      have hxR : R ≤ x := le_trans (le_max_right _ _) hx
      have hxpos : 0 < x := lt_of_lt_of_le hr₀ hxr
      have hle : -ε ≤ h x := hR x hxR
      have h1 : 1 - h x ≤ 1 + ε := by linarith
      have h0 : 0 ≤ A * x ^ (-α - 1) * (f x) ^ 2 := by
        have hp := Real.rpow_pos_of_pos hxpos (-α - 1)
        have hf := hpos x hxr
        positivity
      rw [hode x hxr]
      calc A * (1 - h x) * x ^ (-α - 1) * (f x) ^ 2
          = (1 - h x) * (A * x ^ (-α - 1) * (f x) ^ 2) := by ring
        _ ≤ (1 + ε) * (A * x ^ (-α - 1) * (f x) ^ 2) :=
            mul_le_mul_of_nonneg_right h1 h0
        _ = A * (1 + ε) * x ^ (-α - 1) * (f x) ^ 2 := by ring
    have hlb := lemma_I_4_5_two_nocont (f := f) (f' := f') (A := A * (1 + ε))
        (α := α) (r₀ := R') (by positivity) hα hR'pos
        (fun x hx => hderiv x (le_trans (le_max_left _ _) hx))
        (fun x hx => hpos x (le_trans (le_max_left _ _) hx)) hinf hcmp
    have hcle : c ≤ α / (A * (1 + ε)) := by
      have hA1 : 0 < A * (1 + ε) := by positivity
      rw [le_div_iff₀ hA1]
      calc c * (A * (1 + ε)) = ((1 + ε) * c) * A := by ring
        _ ≤ (α / A) * A := mul_le_mul_of_nonneg_right hεc hA.le
        _ = α := by field_simp
    filter_upwards [eventually_ge_atTop R'] with r hr
    have hrpos : 0 < r := lt_of_lt_of_le hR'pos hr
    have hpow : 0 ≤ r ^ α := Real.rpow_nonneg hrpos.le α
    exact le_trans (mul_le_mul_of_nonneg_right hcle hpow) (hlb r hr)

/-- **Corollary I.4.8, pointwise form.**  If the multiplicative error is
nonnegative on a tail then the pointwise lower bound `α/A · r^α ≤ f r` holds on
that tail.  This is the honest hypothesis behind the existing
`first_moment_lower_bound`; it is *not* implied by `E1 ≥ 0` and `E0 → 0` alone. -/
theorem first_moment_lower_bound_of_eventually_nonneg {f f' h : ℝ → ℝ} {A α r₀ : ℝ}
    (hA : 0 < A) (hα : 0 < α) (hr₀ : 0 < r₀)
    (hderiv : ∀ t, r₀ ≤ t → HasDerivAt f (f' t) t)
    (hpos : ∀ t, r₀ ≤ t → 0 < f t)
    (hinf : Tendsto f atTop atTop)
    (hode : ∀ t, r₀ ≤ t → f' t = A * (1 - h t) * t ^ (-α - 1) * (f t) ^ 2)
    (hnn : ∀ᶠ t : ℝ in atTop, 0 ≤ h t) :
    ∀ᶠ r : ℝ in atTop, α / A * r ^ α ≤ f r := by
  obtain ⟨R, hR⟩ := eventually_atTop.1 hnn
  set R' : ℝ := max r₀ R with hR'def
  have hR'pos : 0 < R' := lt_of_lt_of_le hr₀ (le_max_left _ _)
  have hcmp : ∀ x, R' ≤ x → f' x ≤ A * x ^ (-α - 1) * (f x) ^ 2 := by
    intro x hx
    have hxr : r₀ ≤ x := le_trans (le_max_left _ _) hx
    have hxR : R ≤ x := le_trans (le_max_right _ _) hx
    have hxpos : 0 < x := lt_of_lt_of_le hr₀ hxr
    have h1 : 1 - h x ≤ 1 := by linarith [hR x hxR]
    have h0 : 0 ≤ A * x ^ (-α - 1) * (f x) ^ 2 := by
      have hp := Real.rpow_pos_of_pos hxpos (-α - 1)
      have hf := hpos x hxr
      positivity
    rw [hode x hxr]
    calc A * (1 - h x) * x ^ (-α - 1) * (f x) ^ 2
        = (1 - h x) * (A * x ^ (-α - 1) * (f x) ^ 2) := by ring
      _ ≤ 1 * (A * x ^ (-α - 1) * (f x) ^ 2) := mul_le_mul_of_nonneg_right h1 h0
      _ = A * x ^ (-α - 1) * (f x) ^ 2 := by ring
  have hlb := lemma_I_4_5_two_nocont (f := f) (f' := f') (A := A) (α := α) (r₀ := R')
    hA hα hR'pos
    (fun x hx => hderiv x (le_trans (le_max_left _ _) hx))
    (fun x hx => hpos x (le_trans (le_max_left _ _) hx)) hinf hcmp
  filter_upwards [eventually_ge_atTop R'] with r hr
  exact hlb r hr

/-! ### The source sign argument -/

/-- The sign step of Corollary I.4.8, with the product made explicit:
if `0 ≤ E1` then `(1 - E1) ≤ 1`, and if `1 - E0 = oneSubE0 > 0` then
`1 - Ebar1 = (1 - E1)(1 - E0) ≤ (1 - E0) = oneSubE0`, i.e. `E0 ≤ 1 - Ebar1`. -/
theorem oneSubEbar1_le_oneSubE0 {E1 J b r α : ℝ}
    (hE1 : 0 ≤ E1) (h0 : 0 < oneSubE0 J b r α) :
    oneSubEbar1 E1 J b r α ≤ oneSubE0 J b r α := by
  unfold oneSubEbar1
  exact mul_le_of_le_one_left h0.le (by linarith)

/-- The sign step gives the vanishing lower bound on the multiplicative error
`e = 1 - Ebar1` used by `first_moment_liminf_lower_bound`. -/
theorem eventually_neg_le_one_sub_oneSubEbar1 {J b E1 : ℝ → ℝ} {α r₀ : ℝ}
    (hr₀ : 0 < r₀)
    (hJ : ∀ t, r₀ ≤ t → 0 < J t) (hb : ∀ t, r₀ ≤ t → 0 < b t)
    (hE1 : ∀ t, r₀ ≤ t → 0 ≤ E1 t)
    (hE0 : Tendsto (fun t => oneSubE0 (J t) (b t) t α) atTop (𝓝 1)) :
    ∀ ε > 0, ∀ᶠ t : ℝ in atTop, -ε ≤ 1 - oneSubEbar1 (E1 t) (J t) (b t) t α := by
  intro ε hε
  have hlim : Tendsto (fun t => 1 - oneSubE0 (J t) (b t) t α) atTop (𝓝 0) := by
    have hc1 : Tendsto (fun _ : ℝ => (1 : ℝ)) atTop (𝓝 1) := tendsto_const_nhds
    have h := hc1.sub hE0
    simpa using h
  have hsmall : ∀ᶠ t : ℝ in atTop, -(ε) ≤ 1 - oneSubE0 (J t) (b t) t α := by
    have h3 : ∀ᶠ t : ℝ in atTop, |1 - oneSubE0 (J t) (b t) t α| < ε := by
      have h4 : ∀ ε > 0, ∃ N, ∀ n ≥ N,
          dist (1 - oneSubE0 (J n) (b n) n α) 0 < ε := Metric.tendsto_atTop.1 hlim
      obtain ⟨N, hN⟩ := h4 ε hε
      exact eventually_atTop.2 ⟨N, fun t ht => by simpa using hN t ht⟩
    filter_upwards [h3] with t ht
    have := (abs_lt.1 ht).1
    linarith
  filter_upwards [hsmall, eventually_ge_atTop r₀] with t ht htr
  have h0 : 0 < oneSubE0 (J t) (b t) t α := by
    have ht0 : 0 < t := lt_of_lt_of_le hr₀ htr
    have hp : 0 < t ^ (α + 1) := Real.rpow_pos_of_pos ht0 _
    unfold oneSubE0
    exact mul_pos (mul_pos (hJ t htr) (hb t htr)) hp
  have hstep := oneSubEbar1_le_oneSubE0 (E1 := E1 t) (J := J t) (b := b t) (r := t) (α := α)
    (hE1 t htr) h0
  linarith

/-- **Corollary I.4.8 at the source interface (I.4.6).**

Let `F' = (1 - Ebar1) β_c r^{-α-1} F²` be the first-moment ODE (I.4.6) written with
`1 - Ebar1 = (1 - E1)(1 - E0) = oneSubEbar1`, where
`1 - E0 = |J'||B_r| r^{α+1} = oneSubE0 → 1`, `E1 ≥ 0`, and `|J'|, |B_r| > 0`.
Then `lim inf_{r→∞} r^{-α} F r ≥ α/β_c`.

The hypotheses are exactly the source ones: `E1 ≥ 0` (Lemma I.4.7), `E0 → 0`
(standing assumption (∗) + Lemma I.4.6), positivity of `|J'|` and `|B_r|`, and
`F → ∞`.  There is no hypothesis on `d`, on `α` other than `α > 0`, no bound on
`E1`, and no eventual vanishing of `E0`. -/
theorem first_moment_liminf_lower_bound_critical
    {F F' J b E1 : ℝ → ℝ} {α βc r₀ : ℝ}
    (hα : 0 < α) (hβc : 0 < βc) (hr₀ : 0 < r₀)
    (hderiv : ∀ t, r₀ ≤ t → HasDerivAt F (F' t) t)
    (hpos : ∀ t, r₀ ≤ t → 0 < F t)
    (hinf : Tendsto F atTop atTop)
    (hODE : ∀ t, r₀ ≤ t →
      F' t = oneSubEbar1 (E1 t) (J t) (b t) t α * βc * t ^ (-α - 1) * (F t) ^ 2)
    (hJ : ∀ t, r₀ ≤ t → 0 < J t)
    (hb : ∀ t, r₀ ≤ t → 0 < b t)
    (hE0 : Tendsto (fun t => oneSubE0 (J t) (b t) t α) atTop (𝓝 1))
    (hE1 : ∀ t, r₀ ≤ t → 0 ≤ E1 t) :
    ∀ c, c < α / βc → ∀ᶠ r : ℝ in atTop, c * r ^ α ≤ F r := by
  set e : ℝ → ℝ := fun t => 1 - oneSubEbar1 (E1 t) (J t) (b t) t α with hedef
  refine first_moment_liminf_lower_bound (f := F) (f' := F') (h := e)
    (A := βc) hβc hα hr₀ hderiv hpos hinf ?_ ?_
  · intro t ht
    rw [hODE t ht]
    simp only [hedef]
    ring
  · intro ε hε
    simpa only [hedef] using eventually_neg_le_one_sub_oneSubEbar1 hr₀ hJ hb hE1 hE0 ε hε

/-- **Corollary I.4.8**, literal form: `lim inf_{r→∞} r^{-α} F r ≥ α/β_c`
(equivalently `∀ c < α/β_c`, eventually `c ≤ r^{-α} F r`). -/
theorem first_moment_liminf_rpow_lower_bound_critical
    {F F' J b E1 : ℝ → ℝ} {α βc r₀ : ℝ}
    (hα : 0 < α) (hβc : 0 < βc) (hr₀ : 0 < r₀)
    (hderiv : ∀ t, r₀ ≤ t → HasDerivAt F (F' t) t)
    (hpos : ∀ t, r₀ ≤ t → 0 < F t)
    (hinf : Tendsto F atTop atTop)
    (hODE : ∀ t, r₀ ≤ t →
      F' t = oneSubEbar1 (E1 t) (J t) (b t) t α * βc * t ^ (-α - 1) * (F t) ^ 2)
    (hJ : ∀ t, r₀ ≤ t → 0 < J t)
    (hb : ∀ t, r₀ ≤ t → 0 < b t)
    (hE0 : Tendsto (fun t => oneSubE0 (J t) (b t) t α) atTop (𝓝 1))
    (hE1 : ∀ t, r₀ ≤ t → 0 ≤ E1 t) :
    ∀ c, c < α / βc → ∀ᶠ r : ℝ in atTop, c ≤ r ^ (-α) * F r := by
  intro c hc
  have hmain := first_moment_liminf_lower_bound_critical hα hβc hr₀ hderiv hpos hinf
    hODE hJ hb hE0 hE1 c hc
  filter_upwards [hmain, eventually_ge_atTop (max r₀ 1)] with r hr hr'
  have hr1 : 1 ≤ r := le_trans (le_max_right _ _) hr'
  have hrpos : 0 < r := lt_of_lt_of_le zero_lt_one hr1
  have hneg : 0 ≤ r ^ (-α) := Real.rpow_nonneg hrpos.le _
  have h2 : c * r ^ α * r ^ (-α) ≤ F r * r ^ (-α) :=
    mul_le_mul_of_nonneg_right hr hneg
  have h3 : r ^ α * r ^ (-α) = 1 := by
    rw [← Real.rpow_add hrpos]
    simp
  have h4 : c * r ^ α * r ^ (-α) = c := by rw [mul_assoc, h3, mul_one]
  rw [h4] at h2
  calc c ≤ F r * r ^ (-α) := h2
    _ = r ^ (-α) * F r := by ring

end PercLib.CriticalLRP.VolumeMoments.FirstMoment

namespace PercLib.CriticalLRP.VolumeMoments.FirstMoment

/-- **Corollary I.4.8 with the paper's `𝓔₁` in place.**  Same statement as
`first_moment_liminf_lower_bound_critical` with `E1 t := cE1 (A t) (S t) (T t) (b t)`
(the paper's `𝓔₁,r`, with `A = E|K|`, `S = E[|K|∑_{y∈B_r}|K_y|]`,
`T = E[|K|²|K∩B_r|]`, `b = |B_r|`), so that `𝓔₁ ≥ 0` can be supplied by
`Hvol.lemma_I_4_7_cutoff_of_secondMoment`. -/
theorem first_moment_liminf_lower_bound_critical_of_cE1
    {F F' J b A S T : ℝ → ℝ} {α βc r₀ : ℝ}
    (hα : 0 < α) (hβc : 0 < βc) (hr₀ : 0 < r₀)
    (hderiv : ∀ t, r₀ ≤ t → HasDerivAt F (F' t) t)
    (hpos : ∀ t, r₀ ≤ t → 0 < F t)
    (hinf : Tendsto F atTop atTop)
    (hODE : ∀ t, r₀ ≤ t →
      F' t = oneSubEbar1 (cE1 (A t) (S t) (T t) (b t)) (J t) (b t) t α
        * βc * t ^ (-α - 1) * (F t) ^ 2)
    (hJ : ∀ t, r₀ ≤ t → 0 < J t)
    (hb : ∀ t, r₀ ≤ t → 0 < b t)
    (hE0 : Tendsto (fun t => oneSubE0 (J t) (b t) t α) atTop (𝓝 1))
    (hE1 : ∀ t, r₀ ≤ t → 0 ≤ cE1 (A t) (S t) (T t) (b t)) :
    ∀ c, c < α / βc → ∀ᶠ r : ℝ in atTop, c * r ^ α ≤ F r :=
  first_moment_liminf_lower_bound_critical hα hβc hr₀ hderiv hpos hinf hODE hJ hb hE0 hE1

/-! ### The `𝓔₀ → 0` input from (∗) and Lemma I.4.6

The theorem below closes one of the model inputs listed above: if the kernel
derivative has the source form `|J'(r)| = (1 + δ_r) r^{−d−α−1}` with `δ_r → 0`
(the asymptotic reading of (∗), after the normalizations `C = 1` and `|B_1| = 1`),
then the error `𝓔₀,r = 1 − oneSubE0` of (I.4.6) tends to zero, by Lemma I.4.6
(`lemma_I_4_6_isEquivalent`: `|B_r| ~ r^d`). -/

/-- **`𝓔₀,r → 0`.**  With `|B_r| = #{z ∈ ℤ^d : ρ z ≤ r}` and
`|J'(r)| = (1 + δ_r) r^{−d−α−1}` with `δ_r → 0`,
`oneSubE0 (|J'| r) |B_r| r α = |J'(r)||B_r| r^{α+1} → 1`. -/
theorem oneSubE0_tendsto_one {d : ℕ} {ρ : (Fin d → ℝ) → ℝ} {α : ℝ} {J' δ : ℝ → ℝ}
    (hd : 1 ≤ d)
    (h_add : ∀ x y, ρ (x + y) ≤ ρ x + ρ y) (h_neg : ∀ x, ρ (-x) = ρ x)
    (h_cont : Continuous ρ)
    (h_hom : ∀ (c : ℝ) (x : Fin d → ℝ), ρ (c • x) = |c| * ρ x)
    (hunit : MeasureTheory.volume (PercLib.CriticalLRP.LatticeGeometry.rhoBall ρ 1) = 1)
    (hJ : ∀ r, 1 ≤ r → J' r = (1 + δ r) * r ^ (-(d : ℝ) - α - 1))
    (hδ : Tendsto δ atTop (𝓝 0)) :
    Tendsto (fun r : ℝ =>
      oneSubE0 (J' r) ((Set.ncard {z : Fin d → ℤ | ρ (fun j => (z j : ℝ)) ≤ r} : ℕ) : ℝ) r α)
      atTop (𝓝 1) := by
  set N : ℝ → ℝ := fun r =>
    ((Set.ncard {z : Fin d → ℤ | ρ (fun j => (z j : ℝ)) ≤ r} : ℕ) : ℝ) with hN
  have hEq : (fun r : ℝ => N r) ~[atTop] (fun r : ℝ => r ^ d) :=
    PercLib.CriticalLRP.LatticeGeometry.lemma_I_4_6_isEquivalent hd h_add h_neg h_cont h_hom hunit
  have hne : ∀ᶠ r : ℝ in atTop, (fun r : ℝ => r ^ d) r ≠ 0 := by
    filter_upwards [eventually_ge_atTop (1 : ℝ)] with r hr
    have hr0 : 0 < r := lt_of_lt_of_le zero_lt_one hr
    positivity
  have hdiv : Tendsto (fun r : ℝ => N r / r ^ d) atTop (𝓝 1) :=
    (Asymptotics.isEquivalent_iff_tendsto_one hne).1 hEq
  have hone : Tendsto (fun r : ℝ => 1 + δ r) atTop (𝓝 1) := by
    have hc1 : Tendsto (fun _ : ℝ => (1 : ℝ)) atTop (𝓝 1) := tendsto_const_nhds
    have h := hc1.add hδ
    simpa using h
  have hprod : Tendsto (fun r : ℝ => (1 + δ r) * (N r / r ^ d)) atTop (𝓝 (1 * 1)) :=
    hone.mul hdiv
  have hcongr : ∀ᶠ r : ℝ in atTop,
      oneSubE0 (J' r) (N r) r α = (1 + δ r) * (N r / r ^ d) := by
    filter_upwards [eventually_ge_atTop (1 : ℝ)] with r hr
    have hr0 : 0 < r := lt_of_lt_of_le zero_lt_one hr
    have hkey : r ^ (-(d : ℝ) - α - 1) * r ^ (α + 1) = (r ^ d)⁻¹ := by
      rw [← Real.rpow_add hr0,
        show -(d : ℝ) - α - 1 + (α + 1) = -(d : ℝ) by ring,
        Real.rpow_neg hr0.le, Real.rpow_natCast]
    rw [hJ r hr]
    unfold oneSubE0
    rw [show (1 + δ r) * r ^ (-(d : ℝ) - α - 1) * N r * r ^ (α + 1)
        = (1 + δ r) * (N r * (r ^ (-(d : ℝ) - α - 1) * r ^ (α + 1))) from by ring, hkey]
    rw [div_eq_mul_inv]
  simpa using Tendsto.congr' (Filter.EventuallyEq.symm hcongr) hprod

/-! ### Non-vacuity witnesses

These are evidence, not part of the proof: they show that the hypothesis sets of
the two main theorems are simultaneously satisfiable, and (second witness) that
`first_moment_liminf_lower_bound` covers cases where the error is *negative
everywhere*, so that the existing `first_moment_lower_bound` (`0 ≤ h`
pointwise) does not apply. -/

/-- Witness for the source interface: `α = β_c = 1`, `F r = r`,
`|J'(r)| = r^{-2}`, `|B_r| = 1`, `E1 ≡ 0`.  Then `oneSubE0 ≡ 1 → 1` and the ODE
(I.4.6) is `1 = 1 · 1 · r^{-2} · r²`. -/
theorem first_moment_liminf_lower_bound_critical_witness :
    ∀ c, c < (1 : ℝ) / 1 → ∀ᶠ r : ℝ in atTop, c * r ^ (1 : ℝ) ≤ (fun t : ℝ => t) r := by
  refine first_moment_liminf_lower_bound_critical
    (F := fun t : ℝ => t) (F' := fun _ => 1)
    (J := fun t : ℝ => t ^ (-2 : ℝ)) (b := fun _ => 1) (E1 := fun _ => 0)
    (α := 1) (βc := 1) (r₀ := 1) one_pos one_pos one_pos ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_
  · intro t ht
    exact hasDerivAt_id t
  · intro t ht
    exact lt_of_lt_of_le zero_lt_one ht
  · exact tendsto_id
  · intro t ht
    have ht0 : 0 < t := lt_of_lt_of_le zero_lt_one ht
    have e1 : t ^ (-2 : ℝ) = (t ^ 2)⁻¹ := by
      rw [show (-2 : ℝ) = -(2 : ℝ) by norm_num, Real.rpow_neg ht0.le, Real.rpow_two]
    have e2 : t ^ (1 + 1 : ℝ) = t ^ 2 := by
      rw [show (1 + 1 : ℝ) = (2 : ℝ) by norm_num, Real.rpow_two]
    have e3 : t ^ (-1 - 1 : ℝ) = (t ^ 2)⁻¹ := by
      rw [show (-1 - 1 : ℝ) = -(2 : ℝ) by norm_num, Real.rpow_neg ht0.le, Real.rpow_two]
    unfold oneSubEbar1 oneSubE0
    rw [e1, e2, e3]
    field_simp
    ring
  · intro t ht
    exact Real.rpow_pos_of_pos (lt_of_lt_of_le zero_lt_one ht) (-2)
  · intro t ht
    exact one_pos
  · -- `oneSubE0 (t^{-2}) 1 t 1 = 1` eventually
    refine Tendsto.congr' ?_ (tendsto_const_nhds : Tendsto (fun _ : ℝ => (1 : ℝ)) atTop (𝓝 1))
    filter_upwards [eventually_ge_atTop (1 : ℝ)] with t ht
    have ht0 : 0 < t := lt_of_lt_of_le zero_lt_one ht
    have e1 : t ^ (-2 : ℝ) = (t ^ 2)⁻¹ := by
      rw [show (-2 : ℝ) = -(2 : ℝ) by norm_num, Real.rpow_neg ht0.le, Real.rpow_two]
    have e2 : t ^ (1 + 1 : ℝ) = t ^ 2 := by
      rw [show (1 + 1 : ℝ) = (2 : ℝ) by norm_num, Real.rpow_two]
    unfold oneSubE0
    rw [e1, e2]
    field_simp
  · intro t ht
    exact le_refl 0

/-- Witness with a strictly negative error: `α = A = 1`, `r₀ = 1`,
`f r = r²/(r+1)`, `h r = -2/r`.  Then `h < 0` everywhere on `[1,∞)` yet
`f' = (1 - h) r^{-1-1} f²` and `f r / r → 1 = α/A`.  The existing
`first_moment_lower_bound` (hypothesis `0 ≤ h` on the tail) cannot be applied. -/
theorem first_moment_liminf_lower_bound_negative_error_witness :
    ∀ c, c < (1 : ℝ) / 1 → ∀ᶠ r : ℝ in atTop,
      c * r ^ (1 : ℝ) ≤ (fun t : ℝ => t ^ 2 / (t + 1)) r := by
  refine first_moment_liminf_lower_bound
    (f := fun t : ℝ => t ^ 2 / (t + 1))
    (f' := fun t : ℝ => t * (t + 2) / (t + 1) ^ 2)
    (h := fun t : ℝ => -2 / t) (A := 1) (α := 1) (r₀ := 1)
    one_pos one_pos one_pos ?_ ?_ ?_ ?_ ?_
  · intro t ht
    have ht0 : 0 < t := lt_of_lt_of_le zero_lt_one ht
    have h1 : t + 1 ≠ 0 := by positivity
    have hderiv := (((hasDerivAt_id t).pow 2).div ((hasDerivAt_id t).add_const 1) h1)
    have hderiv0 : HasDerivAt (fun s : ℝ => s ^ 2 / (s + 1))
        ((2 * t ^ (2 - 1) * (t + 1) - t ^ 2 * 1) / (t + 1) ^ 2) t := by
      convert hderiv using 1
      · funext s
        simp [Pi.pow_apply, Pi.div_apply]
      · norm_num
    have heq : (2 * t ^ (2 - 1) * (t + 1) - t ^ 2 * 1) / (t + 1) ^ 2
        = t * (t + 2) / (t + 1) ^ 2 := by
      rw [show (2 : ℕ) - 1 = 1 by norm_num]
      ring
    rw [heq] at hderiv0
    exact hderiv0
  · intro t ht
    have ht0 : 0 < t := lt_of_lt_of_le zero_lt_one ht
    positivity
  · -- `f r = r²/(r+1) → ∞`
    have hmono : ∀ᶠ t : ℝ in atTop, t / 2 ≤ t ^ 2 / (t + 1) := by
      filter_upwards [eventually_ge_atTop (1 : ℝ)] with t ht
      have ht0 : 0 < t := lt_of_lt_of_le zero_lt_one ht
      have hsplit : t ^ 2 / (t + 1) = t * (t / (t + 1)) := by field_simp
      have hratio : 1 / 2 ≤ t / (t + 1) := by
        rw [le_div_iff₀ (by positivity)]
        linarith
      calc t / 2 = t * (1 / 2) := by ring
        _ ≤ t * (t / (t + 1)) := mul_le_mul_of_nonneg_left hratio ht0.le
        _ = t ^ 2 / (t + 1) := hsplit.symm
    exact tendsto_atTop_mono' atTop hmono (tendsto_id.atTop_div_const (by norm_num))
  · -- the ODE
    intro t ht
    have ht0 : 0 < t := lt_of_lt_of_le zero_lt_one ht
    have ht1 : t + 1 ≠ 0 := by positivity
    have h1 : t ^ (-1 - 1 : ℝ) = (t ^ 2)⁻¹ := by
      rw [show (-1 - 1 : ℝ) = -(2 : ℝ) by norm_num, Real.rpow_neg ht0.le, Real.rpow_two]
    have h2 : 1 - -2 / t = (t + 2) / t := by
      field_simp
      ring
    rw [h1, h2]
    field_simp
  · -- `h = -2/t ≥ -ε` eventually
    intro ε hε
    have hpos : 0 < 2 / ε := by positivity
    filter_upwards [eventually_ge_atTop (max (2 / ε) 1)] with t ht
    have htge : 2 / ε ≤ t := le_trans (le_max_left _ _) ht
    have ht1 : 1 ≤ t := le_trans (le_max_right _ _) ht
    have ht0 : 0 < t := lt_of_lt_of_le zero_lt_one ht1
    have hbound : 2 / t ≤ ε := by
      rw [div_le_iff₀ ht0]
      have h2 : (2 / ε) * ε = 2 := by field_simp
      nlinarith [mul_le_mul_of_nonneg_right htge hε.le]
    have hneg : -ε ≤ -2 / t := by
      rw [neg_div]
      linarith
    exact hneg


end PercLib.CriticalLRP.VolumeMoments.FirstMoment
