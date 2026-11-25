/-
Migration source: https://github.com/yujinhkim/Critical-Long-range-percolation
Integration revision: 3b3d1d0e43ef940bfaa2292ee5c2ee094ac4edbf
Licence: Apache-2.0 for the PercLib Lean sources and tooling; see third_party/critical-lrp/.
External provenance and modifications are recorded in the file-specific notices below.
-/

/-
**The Tauberian converse at every point: `Phi α F f h u → u^{-α}` for every `u > 0`.**

This file strengthens the two required conclusions of the converse of Theorem I.2.11:

* the required conclusions concern the a.e. limit profile and the single point `u = 1`;
* here the normalised profile is shown to converge, along the *whole* filter `h ↓ 0` and for
  *every* `u > 0`, to `u ↦ u^{-α}`; consequently the limit profile equals `u ↦ u^{-α}` at every
  point of `(0,∞)`, not merely almost everywhere, and every subsequence (indeed every net tending
  to `0` through positive reals) gives the conclusion at `u = 1`.

Main results:

* `tendsto_Gamma_mul_div_of_tail`, `tendsto_Phi_at`: `∀ u > 0`,
  `Tendsto (fun h => Phi α F f h u) (𝓝[>] 0) (𝓝 (u ^ (-α)))`.
* `tendsto_Phi_subseq_at`: the same along any subsequence `hseq (ns ·) → 0`.
* `limitProfile_eq_rpow_all`: `∀ u > 0, limitProfile L u = u ^ (-α)`.
* `exists_limitProfile_eq_rpow_and_tendsto_one`: both required conclusions, with the a.e.
  identity upgraded to a pointwise identity.

The proof of the pointwise limit combines the tail asymptotic
`tendsto_tail_of_laplace` with regular variation. The everywhere identity
then follows from convergence almost everywhere, uniqueness of limits, and
the monotone squeeze.
-/
module

public import PercLib.CriticalLRP.Analysis.TauberianConverseComplete

set_option linter.unusedSectionVars false
set_option linter.unusedSimpArgs false
set_option linter.unnecessarySimpa false
set_option linter.unusedTactic false
set_option linter.unusedVariables false

set_option autoImplicit true

@[expose] public section

open MeasureTheory Set Filter
open scoped Topology ENNReal

namespace PercLib.CriticalLRP.Analysis

/-! ### The pointwise limit of the normalised profile -/

/-- The tail asymptotic in the multiplicative form `Γ(1-α) F x / f x → 1`. -/
theorem tendsto_Gamma_mul_div_of_tail
    {F f : ℝ → ℝ} {α : ℝ}
    (hα0 : 0 ≤ α) (hα1 : α < 1)
    (hFmeas : Measurable F) (hF0 : ∀ x, 0 ≤ F x) (hanti : Antitone F)
    (hfmeas : Measurable f) (hrv : RegularlyVaryingAtTop f (-α))
    (hmain : Tendsto (fun h : ℝ =>
      (∫ u in Ioi (0:ℝ), Real.exp (-u) * F (u/h)) / f (1/h)) (𝓝[>] (0:ℝ)) (𝓝 1)) :
    Tendsto (fun x : ℝ => Real.Gamma (1 - α) * (F x / f x)) atTop (𝓝 1) := by
  have hΓpos : (0:ℝ) < Real.Gamma (1 - α) := Real.Gamma_pos_of_pos (by linarith)
  have hΓne : Real.Gamma (1 - α) ≠ 0 := ne_of_gt hΓpos
  have htail := tendsto_tail_of_laplace hα0 hα1 hFmeas hF0 hanti hfmeas hrv hmain
  have h4 : Tendsto (fun x : ℝ => F x / f x) atTop (𝓝 ((Real.Gamma (1 - α))⁻¹)) := by
    have h := htail.const_mul ((Real.Gamma (1 - α))⁻¹)
    rw [mul_one] at h
    refine h.congr' ?_
    filter_upwards with x
    by_cases hfx : f x = 0
    · simp [hfx]
    · field_simp
  have h5 := h4.const_mul (Real.Gamma (1 - α))
  rw [mul_inv_cancel₀ hΓne] at h5
  exact h5

/-- **Pointwise convergence of the normalised profile.**  For every `u > 0`,
`Γ(1-α) F(u/h)/f(1/h) → u^{-α}` as `h ↓ 0` through positive reals. -/
theorem tendsto_Phi_at
    {F f : ℝ → ℝ} {α : ℝ}
    (hα0 : 0 ≤ α) (hα1 : α < 1)
    (hFmeas : Measurable F) (hF0 : ∀ x, 0 ≤ F x) (hanti : Antitone F)
    (hfmeas : Measurable f) (hrv : RegularlyVaryingAtTop f (-α))
    (hmain : Tendsto (fun h : ℝ =>
      (∫ u in Ioi (0:ℝ), Real.exp (-u) * F (u/h)) / f (1/h)) (𝓝[>] (0:ℝ)) (𝓝 1))
    {u : ℝ} (hu : 0 < u) :
    Tendsto (fun h : ℝ => Phi α F f h u) (𝓝[>] (0:ℝ)) (𝓝 (u ^ (-α))) := by
  have hA := tendsto_Gamma_mul_div_of_tail hα0 hα1 hFmeas hF0 hanti hfmeas hrv hmain
  have hinv : Tendsto (fun h : ℝ => 1/h) (𝓝[>] (0:ℝ)) atTop := by
    simpa [one_div] using tendsto_inv_nhdsGT_zero
  have htend : Tendsto (fun h : ℝ => u/h) (𝓝[>] (0:ℝ)) atTop := by
    have h := hinv.const_mul_atTop hu
    refine h.congr' ?_
    filter_upwards with h
    rw [mul_one_div]
  have h1 : Tendsto (fun h : ℝ => Real.Gamma (1 - α) * (F (u/h) / f (u/h)))
      (𝓝[>] (0:ℝ)) (𝓝 1) := hA.comp htend
  have h2 : Tendsto (fun h : ℝ => f (u/h) / f (1/h)) (𝓝[>] (0:ℝ)) (𝓝 (u ^ (-α))) := by
    have h := (hrv.2 u hu).comp hinv
    refine h.congr' ?_
    filter_upwards with h
    simp only [Function.comp_apply]
    rw [mul_one_div]
  have h3 := h1.mul h2
  rw [one_mul] at h3
  have hf1 : ∀ᶠ h : ℝ in 𝓝[>] (0:ℝ), f (u/h) ≠ 0 := htend.eventually hrv.1
  have hf2 : ∀ᶠ h : ℝ in 𝓝[>] (0:ℝ), f (1/h) ≠ 0 := hinv.eventually hrv.1
  refine h3.congr' ?_
  filter_upwards [hf1, hf2] with h hfne hfne2
  simp only [Phi]
  field_simp

/-- **Pointwise convergence along any subsequence.** -/
theorem tendsto_Phi_subseq_at
    {F f : ℝ → ℝ} {α : ℝ}
    (hα0 : 0 ≤ α) (hα1 : α < 1)
    (hFmeas : Measurable F) (hF0 : ∀ x, 0 ≤ F x) (hanti : Antitone F)
    (hfmeas : Measurable f) (hrv : RegularlyVaryingAtTop f (-α))
    (hmain : Tendsto (fun h : ℝ =>
      (∫ u in Ioi (0:ℝ), Real.exp (-u) * F (u/h)) / f (1/h)) (𝓝[>] (0:ℝ)) (𝓝 1))
    {hseq : ℕ → ℝ} (hpos : ∀ n, 0 < hseq n) (htend : Tendsto hseq atTop (𝓝 0))
    {ns : ℕ → ℕ} (hns : StrictMono ns) {u : ℝ} (hu : 0 < u) :
    Tendsto (fun n : ℕ => Phi α F f (hseq (ns n)) u) atTop (𝓝 (u ^ (-α))) := by
  have hseq_mem : Tendsto hseq atTop (𝓝[>] (0:ℝ)) := by
    rw [tendsto_nhdsWithin_iff]
    exact ⟨htend, Filter.Eventually.of_forall hpos⟩
  exact (tendsto_Phi_at hα0 hα1 hFmeas hF0 hanti hfmeas hrv hmain hu).comp
    (hseq_mem.comp hns.tendsto_atTop)

/-! ### Good points on either side of a base point -/

/-- There are good points just below any `u > 0`, with `a^{-α}` arbitrarily close to `u^{-α}`. -/
theorem exists_good_lt {α : ℝ} {P : ℝ → Prop}
    (hP : ∀ᵐ v ∂(volume.restrict (Ioi (0:ℝ))), P v) {u : ℝ} (hu : 0 < u) {ε : ℝ} (hε : 0 < ε) :
    ∃ a : ℝ, 0 < a ∧ a < u ∧ P a ∧ a ^ (-α) < u ^ (-α) + ε := by
  have hcont : Tendsto (fun v : ℝ => v ^ (-α)) (𝓝 u) (𝓝 (u ^ (-α))) :=
    Real.continuousAt_rpow_const u (-α) (Or.inl hu.ne')
  have hball : ∀ᶠ v : ℝ in 𝓝 u, dist (v ^ (-α)) (u ^ (-α)) < ε :=
    Metric.tendsto_nhds.mp hcont ε hε
  obtain ⟨η, hη, hηb⟩ := Metric.eventually_nhds_iff.mp hball
  set c := min (u/2) η with hc
  have hcpos : 0 < c := lt_min (by linarith) hη
  have hcη : c ≤ η := min_le_right _ _
  have hcu : c ≤ u/2 := min_le_left _ _
  obtain ⟨a, ha1, ha2, haP⟩ :=
    exists_mem_of_ae_restrict hP (a := u - c) (b := u) (by linarith) (by linarith)
  refine ⟨a, by linarith, ha2, haP, ?_⟩
  have hdist : dist a u < η := by
    rw [Real.dist_eq, abs_lt]
    constructor <;> linarith
  have hd := hηb hdist
  rw [Real.dist_eq] at hd
  linarith [(abs_lt.mp hd).2]

/-- There are good points just above any `u > 0`, with `b^{-α}` arbitrarily close to `u^{-α}`. -/
theorem exists_good_gt {α : ℝ} {P : ℝ → Prop}
    (hP : ∀ᵐ v ∂(volume.restrict (Ioi (0:ℝ))), P v) {u : ℝ} (hu : 0 < u) {ε : ℝ} (hε : 0 < ε) :
    ∃ b : ℝ, u < b ∧ P b ∧ u ^ (-α) < b ^ (-α) + ε := by
  have hcont : Tendsto (fun v : ℝ => v ^ (-α)) (𝓝 u) (𝓝 (u ^ (-α))) :=
    Real.continuousAt_rpow_const u (-α) (Or.inl hu.ne')
  have hball : ∀ᶠ v : ℝ in 𝓝 u, dist (v ^ (-α)) (u ^ (-α)) < ε :=
    Metric.tendsto_nhds.mp hcont ε hε
  obtain ⟨η, hη, hηb⟩ := Metric.eventually_nhds_iff.mp hball
  set c := min u η with hc
  have hcpos : 0 < c := lt_min hu hη
  have hcη : c ≤ η := min_le_right _ _
  obtain ⟨b, hb1, hb2, hbP⟩ :=
    exists_mem_of_ae_restrict hP (a := u) (b := u + c) hu (by linarith)
  refine ⟨b, hb1, hbP, ?_⟩
  have hdist : dist b u < η := by
    rw [Real.dist_eq, abs_lt]
    constructor <;> linarith
  have hd := hηb hdist
  rw [Real.dist_eq] at hd
  linarith [(abs_lt.mp hd).1]

/-! ### The limit profile is the power law at every point -/

/-- **The limit profile equals `u ↦ u^{-α}` at every point of `(0,∞)`.** -/
theorem limitProfile_eq_rpow_all
    {F f : ℝ → ℝ} {α : ℝ} {hseq : ℕ → ℝ} {L : {q : ℚ // 0 < q} → ℝ}
    (hα0 : 0 ≤ α) (hα1 : α < 1)
    (hFmeas : Measurable F) (hF0 : ∀ x, 0 ≤ F x) (hanti : Antitone F)
    (hfmeas : Measurable f) (hrv : RegularlyVaryingAtTop f (-α))
    (hmain : Tendsto (fun h : ℝ =>
      (∫ u in Ioi (0:ℝ), Real.exp (-u) * F (u/h)) / f (1/h)) (𝓝[>] (0:ℝ)) (𝓝 1))
    (hpos : ∀ n, 0 < hseq n) (htend : Tendsto hseq atTop (𝓝 0))
    (hantiPhi : ∀ k, Antitone fun u : ℝ => Phi α F f (hseq k) u)
    (hLb : ∀ q : {q : ℚ // 0 < q}, L q ≤ profileBound α (q:ℝ))
    (_hLnn : ∀ q : {q : ℚ // 0 < q}, 0 ≤ L q)
    (hconv : ∀ q : {q : ℚ // 0 < q},
      Tendsto (fun k => Phi α F f (hseq k) (q:ℝ)) atTop (𝓝 (L q))) :
    ∀ u : ℝ, 0 < u → limitProfile L u = u ^ (-α) := by
  have hae := ae_tendsto_limitProfile hα0 hα1 hantiPhi hLb hconv
  have hgood : ∀ᵐ v ∂(volume.restrict (Ioi (0:ℝ))), limitProfile L v = v ^ (-α) := by
    filter_upwards [hae, ae_restrict_mem measurableSet_Ioi] with v hv hv0
    refine tendsto_nhds_unique hv ?_
    exact tendsto_Phi_subseq_at hα0 hα1 hFmeas hF0 hanti hfmeas hrv hmain hpos htend
      strictMono_id hv0
  intro u hu
  refine le_antisymm ?_ ?_
  · refine le_of_forall_pos_le_add (fun ε hε => ?_)
    obtain ⟨a, ha0, hau, haP, haε⟩ := exists_good_lt (α := α) hgood hu hε
    have h1 : limitProfile L u ≤ limitProfile L a :=
      limitProfile_antitone hα0 hα1 hLb a u ha0 (le_of_lt hau)
    rw [haP] at h1
    linarith
  · refine le_of_forall_pos_le_add (fun ε hε => ?_)
    obtain ⟨b, hbu, hbP, hbε⟩ := exists_good_gt (α := α) hgood hu hε
    have h1 : limitProfile L b ≤ limitProfile L u :=
      limitProfile_antitone hα0 hα1 hLb u b hu (le_of_lt hbu)
    rw [hbP] at h1
    linarith

/-- The everywhere statement implies the a.e. statement in the form required. -/
theorem limitProfile_eq_rpow_ae_of_all
    {L : {q : ℚ // 0 < q} → ℝ} {α : ℝ}
    (h : ∀ u : ℝ, 0 < u → limitProfile L u = u ^ (-α)) :
    limitProfile L =ᵐ[volume.restrict (Ioi (0:ℝ))] fun u : ℝ => u ^ (-α) := by
  filter_upwards [ae_restrict_mem measurableSet_Ioi] with u hu
  exact h u hu

/-! ### Both required conclusions, with the identity holding everywhere -/

/-- **The Tauberian converse, complete.**  Under the exact hypotheses of Theorem I.2.11
(`0 ≤ α < 1`, `F` measurable, nonnegative and antitone, `f` measurable and regularly varying of
index `-α`, the kernel-form Laplace hypothesis, and any positive sequence `hseq → 0`), there are
subsequential rational limit values `L` and a renumbering `ns` such that

* the limit profile is `u ↦ u^{-α}` at *every* point of `(0,∞)` (hence a.e.), and
* `Γ(1-α) F(1/hseq (ns n))/f(1/hseq (ns n)) → 1`.

Since `tendsto_Phi_at` holds along the whole filter, the second conclusion in fact holds for
every strictly monotone renumbering (`tendsto_Phi_subseq_one`). -/
theorem exists_limitProfile_eq_rpow_and_tendsto_one
    {F f : ℝ → ℝ} {α : ℝ}
    (hα0 : 0 ≤ α) (hα1 : α < 1)
    (hFmeas : Measurable F) (hF0 : ∀ x, 0 ≤ F x) (hanti : Antitone F)
    (hfmeas : Measurable f) (hrv : RegularlyVaryingAtTop f (-α))
    (hmain : Tendsto (fun h : ℝ =>
      (∫ u in Ioi (0:ℝ), Real.exp (-u) * F (u/h)) / f (1/h)) (𝓝[>] (0:ℝ)) (𝓝 1))
    {hseq : ℕ → ℝ} (hpos : ∀ n, 0 < hseq n) (htend : Tendsto hseq atTop (𝓝 0)) :
    ∃ (L : {q : ℚ // 0 < q} → ℝ) (ns : ℕ → ℕ), StrictMono ns ∧
      (∀ q : {q : ℚ // 0 < q}, 0 ≤ L q ∧ L q ≤ profileBound α (q:ℝ)) ∧
      (∀ q : {q : ℚ // 0 < q},
        Tendsto (fun k => Phi α F f (hseq (ns k)) (q:ℝ)) atTop (𝓝 (L q))) ∧
      (∀ u : ℝ, 0 < u → limitProfile L u = u ^ (-α)) ∧
      (limitProfile L =ᵐ[volume.restrict (Ioi (0:ℝ))] fun u : ℝ => u ^ (-α)) ∧
      Tendsto (fun n => Phi α F f (hseq (ns n)) 1) atTop (𝓝 1) := by
  classical
  have hseq_mem : Tendsto hseq atTop (𝓝[>] (0:ℝ)) := by
    rw [tendsto_nhdsWithin_iff]
    exact ⟨htend, Filter.Eventually.of_forall hpos⟩
  have hinv_atTop : Tendsto (fun x : ℝ => 1/x) atTop (𝓝[>] (0:ℝ)) := by
    rw [tendsto_nhdsWithin_iff]
    refine ⟨by simpa [one_div] using tendsto_inv_atTop_zero, ?_⟩
    filter_upwards [eventually_gt_atTop (0:ℝ)] with x hx
    simp only [Set.mem_Ioi, one_div]
    positivity
  have hfpos_atTop : ∀ᶠ x : ℝ in atTop, 0 < f x :=
    (hinv_atTop.eventually (eventually_pos_f_inv hF0 hmain)).mono (fun x hx => by
      simpa [one_div] using hx)
  have hinvseq : Tendsto (fun n : ℕ => 1/(hseq n)) atTop atTop :=
    (by simpa [one_div] using tendsto_inv_nhdsGT_zero :
      Tendsto (fun h : ℝ => 1/h) (𝓝[>] (0:ℝ)) atTop).comp hseq_mem
  obtain ⟨K, hK⟩ := eventually_atTop.1 (hinvseq.eventually hfpos_atTop)
  set hseq' : ℕ → ℝ := fun n => hseq (n + K) with hseq'_def
  have hpos' : ∀ n, 0 < hseq' n := fun n => hpos (n + K)
  have htend' : Tendsto hseq' atTop (𝓝 0) := htend.comp (tendsto_add_atTop_nat K)
  have hfpos' : ∀ k, 0 < f (1/hseq' k) := fun k => hK (k + K) le_add_self
  obtain ⟨L, ns, hns, hL, hconv⟩ :=
    exists_rational_limit hα0 hα1 hFmeas hF0 hanti hfmeas hrv hmain hpos' htend'
  have hLb : ∀ q : {q : ℚ // 0 < q}, L q ≤ profileBound α (q:ℝ) := fun q => (hL q).2
  have hLnn : ∀ q : {q : ℚ // 0 < q}, 0 ≤ L q := fun q => (hL q).1
  have hpos'' : ∀ n, 0 < hseq' (ns n) := fun n => hpos' (ns n)
  have htend'' : Tendsto (fun n => hseq' (ns n)) atTop (𝓝 0) :=
    htend'.comp hns.tendsto_atTop
  have hantiPhi : ∀ k, Antitone fun u : ℝ => Phi α F f (hseq' (ns k)) u :=
    fun k => Phi_antitone hα1 hanti (hpos'' k) (hfpos' (ns k))
  have hall : ∀ u : ℝ, 0 < u → limitProfile L u = u ^ (-α) :=
    limitProfile_eq_rpow_all hα0 hα1 hFmeas hF0 hanti hfmeas hrv hmain
      hpos'' htend'' hantiPhi hLb hLnn hconv
  have hone : Tendsto (fun k => Phi α F f (hseq' (ns k)) 1) atTop (𝓝 1) := by
    have hmem : Tendsto (fun k : ℕ => hseq' (ns k)) atTop (𝓝[>] (0:ℝ)) := by
      rw [tendsto_nhdsWithin_iff]
      exact ⟨htend'', Filter.Eventually.of_forall hpos''⟩
    have h := (tendsto_Phi_at hα0 hα1 hFmeas hF0 hanti hfmeas hrv hmain one_pos).comp hmem
    simpa [Function.comp_def] using h
  refine ⟨L, fun n => ns n + K, fun a b hab => Nat.add_lt_add_right (hns hab) K,
    hL, hconv, hall, limitProfile_eq_rpow_ae_of_all hall, hone⟩


/-! ### Non-vacuity of the strengthened conclusion

The stronger conclusion `∀ u > 0, limitProfile L u = u^{-α}` is not vacuous: for the constant data
`α = 0`, `F ≡ 1`, `f ≡ 1` (which satisfy every hypothesis) it is attained. -/

/-- The strengthened converse is instantiated by the constant profile `F ≡ 1`, `f ≡ 1`, `α = 0`:
the limit profile is `u ↦ 1 = u^{-0}` at *every* point of `(0,∞)`, and the profile converges to
`1` at `u = 1`. -/
theorem nonvacuous_everywhere :
    ∃ (L : {q : ℚ // 0 < q} → ℝ) (ns : ℕ → ℕ),
      (∀ u : ℝ, 0 < u → limitProfile L u = u ^ (-(0:ℝ))) ∧
      Tendsto (fun n => Phi 0 (fun _ : ℝ => 1) (fun _ : ℝ => 1) (1/((ns n : ℝ)+1)) 1)
        atTop (𝓝 1) := by
  have hrv : RegularlyVaryingAtTop (fun _ : ℝ => (1:ℝ)) (-(0:ℝ)) := by
    constructor
    · filter_upwards with x
      simp
    · intro l hl
      have h0 : (-(0:ℝ)) = 0 := by norm_num
      rw [h0, Real.rpow_zero]
      simp
  have hint : (∫ u in Ioi (0:ℝ), Real.exp (-u) * (1:ℝ)) = 1 := by
    simpa using integral_exp_neg_Ioi_zero
  have hmain : Tendsto (fun h : ℝ =>
      (∫ u in Ioi (0:ℝ), Real.exp (-u) * (fun _ : ℝ => (1:ℝ)) (u/h))
        / (fun _ : ℝ => (1:ℝ)) (1/h)) (𝓝[>] (0:ℝ)) (𝓝 1) := by
    refine tendsto_const_nhds.congr' ?_
    filter_upwards with h
    show (1:ℝ) = (∫ u in Ioi (0:ℝ), Real.exp (-u) * (1:ℝ)) / 1
    rw [div_one, hint]
  obtain ⟨L, ns, -, -, -, hall, -, hlim⟩ :=
    exists_limitProfile_eq_rpow_and_tendsto_one (F := fun _ : ℝ => 1) (f := fun _ : ℝ => 1)
      (α := 0) le_rfl zero_lt_one measurable_const (fun _ => zero_le_one) antitone_const
      measurable_const hrv hmain (hseq := fun n : ℕ => 1/((n:ℝ)+1))
      (fun n => by positivity) tendsto_one_div_add_atTop_nhds_zero_nat
  exact ⟨L, ns, hall, hlim⟩


end PercLib.CriticalLRP.Analysis