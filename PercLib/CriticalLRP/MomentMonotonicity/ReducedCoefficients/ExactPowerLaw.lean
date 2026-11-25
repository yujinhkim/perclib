/-
Copyright (c) 2026 PercLib contributors. Released under Apache 2.0.
-/
module

public import PercLib.CriticalLRP.Analysis.Cutoff.SecondMoment.SourceWitness.Sharpness

/-!
# The exact reduced intensity a cutoff radius costs

Swarm `smwvj13j4`, member `m3`, direction `d8`.

Definition I.1.5 dominates the cutoff kernel `J_r` by `c · J` with `c < 1`, at the price of
replacing the intensity `β_c` by `β_c · c`.  This file computes the *sharp* coefficient for the
power-law witness `sourceModelWitness d hd α hα` (`K r = r ^ (-(d + α)) / (d + α)`,
norm `ρ v = 2‖v‖`): at radius `R ≥ 2`

  `∀ e, J_R e ≤ c · J e  ↔  1 − (2 / R) ^ (d + α) ≤ c`,

so the weakest finiteness hypothesis of this route at radius `R` is finiteness at the reduced
intensity

  `β_c · (1 − (2 / R) ^ (d + α))`:

any coefficient below the threshold fails to dominate at radius `R` at all, and the threshold
tends to `1` (the intensity to `β_c`) as `R → ∞`.

Consequences, all compiled below:

* `Witness.cutKernel_le_iff_coe` — the threshold identity above (both directions);
* `Witness.exists_cutKernel_not_le` — for every `c < 1` some radius `R ≥ 2` violates the
  domination, so *no single* subcritical intensity `β_c · c` reaches all radii; the point at
  `β_c` is genuinely needed in the limit;
* `SourceModelData.cutMoment_four_ne_top_uniform_window_of_domination` — the general window
  transfer with an explicit coefficient;
* `Witness.hasDerivAt_cutMomentReal_two_of_eps` and
  `Witness.sourceModelWitness_hasDerivAt_cutMassReal_powerLaw_of_eps` — the nondegenerate
  `p = 2` off-corner derivative and the paper's `cutMassReal` derivative from finiteness of the
  uncut mean at the single intensity `β_c · (1 − (2/R) ^ (d + α))`.

Together with `SharpnessResidual.lean` (one reduced intensity suffices for a fixed window, and
the ceiling here says which one), this pins the exact shape of the remaining sharpness input:
per radius `R` a single point `β_c (1 − (2/R) ^ (d+α))` of `[0, β_c)`, and the whole family
`β → β_c` when all radii are wanted.

Axiom audit at the end of the file: `propext`, `Classical.choice`, `Quot.sound` only.
-/

set_option autoImplicit false
set_option linter.hashCommand false
set_option linter.style.longLine false

@[expose] public section

noncomputable section

open MeasureTheory Filter Topology Set
open PercLib.CriticalLRP FiniteVolume
open scoped ENNReal NNReal Topology

namespace PercLib.CriticalLRP.Orchestration

/-! ## 1. The sharp cutoff domination for an arbitrary source model -/

/-- **Sharp-threshold form of the Definition I.1.5 domination.**  If `ε * K t₀ ≤ K R`, where
`t₀` is any lower bound for the nonzero lattice distances, then the cutoff kernel at every
`r ∈ (0, R]` is dominated by `(1 − ε) • J` edge by edge.  This is the sharp refinement of
`SourceModelData.exists_uniform_reduced_coefficient`, whose coefficient
`1 − min (1/2) (K R / (2 K t₀))` spends a factor two. -/
theorem SourceModelData.cutKernel_le_scaled_of_eps (M : SourceModelData) {t0 R r ε : ℝ}
    (ht0 : 0 < t0) (hR : 0 < R) (hr0 : 0 < r) (hrR : r ≤ R)
    (hlat : ∀ v : M.V, v ≠ 0 → t0 ≤ M.S.dist v 0)
    (hε0 : 0 ≤ ε) (hε1 : ε ≤ 1) (hε : ε * M.K t0 ≤ M.K R) (e : Sym2 M.V) :
    M.cutKernel r e ≤ (1 - ε) * M.kernel e := by
  have hcoef : (0 : ℝ) ≤ 1 - ε := by linarith
  induction e using Sym2.ind with
  | _ x y =>
    rw [SourceModelData.cutKernel, SourceModelData.kernel, cutRadialSym, radialSym_mk, radialSym_mk]
    by_cases hxy : x = y
    · rw [ite_eq_left hxy, ite_eq_left hxy]
      simp
    · rw [ite_eq_right hxy, ite_eq_right hxy]
      set s : ℝ := M.S.dist x y with hsdef
      have hspos : 0 < s := M.S.dist_pos hxy
      have hst0 : t0 ≤ s := by
        have h := hlat (x - y) (sub_ne_zero.mpr hxy)
        simpa [hsdef, SourceNormData.dist] using h
      rcases le_or_gt s r with hsr | hrs
      · rw [cutoffProfile_of_le hsr]
        have hKs : M.K s ≤ M.K t0 := M.K_antitone (Set.mem_Ioi.mpr ht0) (Set.mem_Ioi.mpr hspos) hst0
        have hKsr : M.K R ≤ M.K r := M.K_antitone (Set.mem_Ioi.mpr hr0) (Set.mem_Ioi.mpr hR) hrR
        have h1 : ε * M.K s ≤ ε * M.K t0 := by nlinarith
        nlinarith [M.K_nonneg s hspos, M.K_nonneg t0 ht0]
      · rw [cutoffProfile_of_lt hrs]
        exact mul_nonneg hcoef (M.K_nonneg s hspos)

/-! ## 2. The witness: exact kernel values on a minimal edge -/

namespace Witness

/-- The witness kernel is a pure power: `K R = K 2 * (2 / R) ^ (d + α)`. -/
theorem K_eq_K_two_mul (d : ℕ) (hd : 1 ≤ d) (α : ℝ) (hα : 0 < α) {R : ℝ} (hR : 0 < R) :
    (sourceModelWitness d hd α hα).K R
      = (sourceModelWitness d hd α hα).K 2 * (2 / R) ^ ((d : ℝ) + α) := by
  have hc : (0 : ℝ) < (d : ℝ) + α := by positivity
  have hp : (-(d : ℝ) - α) = -((d : ℝ) + α) := by ring
  change R ^ (-(d : ℝ) - α) / ((d : ℝ) + α)
      = (2 ^ (-(d : ℝ) - α) / ((d : ℝ) + α)) * (2 / R) ^ ((d : ℝ) + α)
  rw [hp, Real.rpow_neg hR.le, Real.div_rpow (by norm_num) hR.le,
    Real.rpow_neg (by norm_num : (0 : ℝ) ≤ 2)]
  field_simp

/-- On the minimal edge `(e_i, 0)` the uncut kernel equals `K 2`. -/
theorem kernel_single (d : ℕ) (hd : 1 ≤ d) (α : ℝ) (hα : 0 < α)
    (i : Fin (sourceModelWitness d hd α hα).d) :
    (sourceModelWitness d hd α hα).kernel (s(Pi.single i (1 : ℤ), 0))
      = (sourceModelWitness d hd α hα).K 2 := by
  rw [SourceModelData.kernel, radialSym_mk]
  have hne : (Pi.single i (1 : ℤ) : (sourceModelWitness d hd α hα).V) ≠ 0 := by
    intro h
    have hc := congrFun h i
    simp at hc
  rw [ite_eq_right hne]
  congr 1
  rw [SourceNormData.dist_zero_right]
  change 2 * ‖toVec (Pi.single i (1 : ℤ))‖ = 2
  have h1 : toVec (Pi.single i (1 : ℤ)) = Pi.single i (1 : ℝ) := by
    funext j
    by_cases hj : j = i
    · subst hj; simp [toVec]
    · simp [toVec, Pi.single_eq_of_ne hj]
  rw [h1, Pi.norm_single]
  norm_num

/-- On the minimal edge `(e_i, 0)` the cutoff kernel equals `K 2 - K R` for `R ≥ 2`. -/
theorem cutKernel_single (d : ℕ) (hd : 1 ≤ d) (α : ℝ) (hα : 0 < α) {R : ℝ} (hR : 2 ≤ R)
    (i : Fin (sourceModelWitness d hd α hα).d) :
    (sourceModelWitness d hd α hα).cutKernel R (s(Pi.single i (1 : ℤ), 0))
      = (sourceModelWitness d hd α hα).K 2 - (sourceModelWitness d hd α hα).K R := by
  rw [SourceModelData.cutKernel, cutRadialSym, radialSym_mk]
  have hne : (Pi.single i (1 : ℤ) : (sourceModelWitness d hd α hα).V) ≠ 0 := by
    intro h
    have hc := congrFun h i
    simp at hc
  have hdist : (sourceModelWitness d hd α hα).S.dist
      (Pi.single i (1 : ℤ) : (sourceModelWitness d hd α hα).V) 0 = 2 := by
    rw [SourceNormData.dist_zero_right]
    change 2 * ‖toVec (Pi.single i (1 : ℤ))‖ = 2
    have h1 : toVec (Pi.single i (1 : ℤ)) = Pi.single i (1 : ℝ) := by
      funext j
      by_cases hj : j = i
      · subst hj; simp [toVec]
      · simp [toVec, Pi.single_eq_of_ne hj]
    rw [h1, Pi.norm_single]
    norm_num
  rw [ite_eq_right hne, cutoffProfile_of_le (by rw [hdist]; exact hR), hdist]

/-- Every nonzero lattice distance of the witness is at least `2`, the lattice minimum. -/
theorem witness_two_le_dist (d : ℕ) (hd : 1 ≤ d) (α : ℝ) (hα : 0 < α)
    {v : (sourceModelWitness d hd α hα).V} (hv : v ≠ 0) :
    2 ≤ (sourceModelWitness d hd α hα).S.dist v 0 := by
  rw [SourceNormData.dist_zero_right]
  change 2 ≤ 2 * ‖toVec v‖
  have hex : ∃ j, v j ≠ 0 := by
    by_contra h
    exact hv (funext fun j => by
      have hj : ¬ (v j ≠ 0) := fun hj => h ⟨j, hj⟩
      simpa using hj)
  obtain ⟨j, hj⟩ := hex
  have h2 : (1 : ℝ) ≤ ‖toVec v‖ := by
    have h3 : (1 : ℝ) ≤ |(toVec v j)| := by
      have hcast : toVec v j = (v j : ℝ) := rfl
      rw [hcast]
      have h4 : (1 : ℤ) ≤ |v j| := Int.one_le_abs hj
      exact_mod_cast h4
    calc (1 : ℝ) ≤ |(toVec v j)| := h3
      _ = ‖toVec v j‖ := (Real.norm_eq_abs _).symm
      _ ≤ ‖toVec v‖ := norm_le_pi_norm (toVec v) j
  linarith

/-! ## 3. The exact coefficient threshold -/

/-- **The sharp threshold, positive side.**  For `R ≥ 2` the coefficient
`1 - (2 / R) ^ (d + α)` dominates the cutoff kernel at radius `R`. -/
theorem cutKernel_le_of_le_coe (d : ℕ) (hd : 1 ≤ d) (α : ℝ) (hα : 0 < α) {R r : ℝ}
    (hR : 2 ≤ R) (hr0 : 0 < r) (hrR : r ≤ R) {c : NNReal}
    (hc : 1 - (2 / R) ^ ((d : ℝ) + α) ≤ (c : ℝ)) :
    ∀ e : Sym2 (sourceModelWitness d hd α hα).V,
      (sourceModelWitness d hd α hα).cutKernel r e
        ≤ (c : ℝ) * (sourceModelWitness d hd α hα).kernel e := by
  have hR0 : (0 : ℝ) < R := lt_of_lt_of_le (by norm_num) hR
  have hK2 : 0 < (sourceModelWitness d hd α hα).K 2 :=
    (sourceModelWitness d hd α hα).K_pos (by norm_num)
  intro e
  rcases le_or_gt 1 (c : ℝ) with hc1 | hc1
  · have hzero := (sourceModelWitness d hd α hα).cutKernel_le_scaled_of_eps
      (t0 := 2) (R := R) (r := r) (ε := 0) (by norm_num) hR0 hr0 hrR
      (fun v hv => witness_two_le_dist d hd α hα hv) le_rfl (by norm_num)
      (by simpa using (sourceModelWitness d hd α hα).K_nonneg R hR0) e
    have hkn : 0 ≤ (sourceModelWitness d hd α hα).kernel e :=
      (sourceModelWitness d hd α hα).kernel_nonneg e
    have h1 : (sourceModelWitness d hd α hα).cutKernel r e
        ≤ (sourceModelWitness d hd α hα).kernel e := by
      simpa using hzero
    nlinarith
  · have hε0 : (0 : ℝ) ≤ 1 - (c : ℝ) := by linarith
    have hε1 : 1 - (c : ℝ) ≤ 1 := by linarith
    have hεle : 1 - (c : ℝ) ≤ (2 / R) ^ ((d : ℝ) + α) := by linarith
    have hε : (1 - (c : ℝ)) * (sourceModelWitness d hd α hα).K 2
        ≤ (sourceModelWitness d hd α hα).K R := by
      rw [K_eq_K_two_mul d hd α hα hR0]
      simpa [mul_comm] using mul_le_mul_of_nonneg_right hεle hK2.le
    have hmain := (sourceModelWitness d hd α hα).cutKernel_le_scaled_of_eps
      (t0 := 2) (R := R) (r := r) (ε := 1 - (c : ℝ)) (by norm_num) hR0 hr0 hrR
      (fun v hv => witness_two_le_dist d hd α hα hv) hε0 hε1 hε e
    have hsub : (1 : ℝ) - (1 - (c : ℝ)) = (c : ℝ) := by ring
    rwa [hsub] at hmain

/-- **The sharp threshold, ceiling side.**  Any coefficient that dominates the cutoff kernel
at radius `R ≥ 2` is at least `1 - (2 / R) ^ (d + α)`; the minimal edge `(e_i, 0)` forces it. -/
theorem le_coe_of_cutKernel_le (d : ℕ) (hd : 1 ≤ d) (α : ℝ) (hα : 0 < α) {R : ℝ}
    (hR : 2 ≤ R) {c : NNReal}
    (hdom : ∀ e : Sym2 (sourceModelWitness d hd α hα).V,
      (sourceModelWitness d hd α hα).cutKernel R e
        ≤ (c : ℝ) * (sourceModelWitness d hd α hα).kernel e) :
    1 - (2 / R) ^ ((d : ℝ) + α) ≤ (c : ℝ) := by
  have hR0 : (0 : ℝ) < R := lt_of_lt_of_le (by norm_num) hR
  have hK2 : 0 < (sourceModelWitness d hd α hα).K 2 :=
    (sourceModelWitness d hd α hα).K_pos (by norm_num)
  have hMd : (sourceModelWitness d hd α hα).d = d := rfl
  let i : Fin (sourceModelWitness d hd α hα).d := ⟨0, by omega⟩
  have h1 := hdom s(Pi.single i (1 : ℤ), 0)
  rw [cutKernel_single d hd α hα hR i, kernel_single d hd α hα i] at h1
  rw [K_eq_K_two_mul d hd α hα hR0] at h1
  nlinarith

/-- **The exact reduced-coefficient threshold at radius `R ≥ 2`.** -/
theorem cutKernel_le_iff_coe (d : ℕ) (hd : 1 ≤ d) (α : ℝ) (hα : 0 < α) {R : ℝ}
    (hR : 2 ≤ R) {c : NNReal} :
    (∀ e : Sym2 (sourceModelWitness d hd α hα).V,
        (sourceModelWitness d hd α hα).cutKernel R e
          ≤ (c : ℝ) * (sourceModelWitness d hd α hα).kernel e) ↔
      1 - (2 / R) ^ ((d : ℝ) + α) ≤ (c : ℝ) :=
  ⟨le_coe_of_cutKernel_le d hd α hα hR,
    fun hc e => cutKernel_le_of_le_coe d hd α hα hR
      (lt_of_lt_of_le (by norm_num) hR) le_rfl hc e⟩

/-- **No single reduced coefficient reaches every radius.**  For every `c < 1` there is a radius
at which the domination `J_R ≤ c · J` fails, so the sharpness family of the source cannot be
replaced by one subcritical intensity when unbounded radii are wanted. -/
theorem exists_cutKernel_not_le (d : ℕ) (hd : 1 ≤ d) (α : ℝ) (hα : 0 < α) {c : NNReal}
    (hc : (c : ℝ) < 1) :
    ∃ R : ℝ, 2 ≤ R ∧ ¬ ∀ e : Sym2 (sourceModelWitness d hd α hα).V,
      (sourceModelWitness d hd α hα).cutKernel R e
        ≤ (c : ℝ) * (sourceModelWitness d hd α hα).kernel e := by
  have hp : (0 : ℝ) < (d : ℝ) + α := by positivity
  have hδ : 0 < 1 - (c : ℝ) := by linarith
  have hlim : Tendsto (fun R : ℝ => (2 / R) ^ ((d : ℝ) + α)) atTop (𝓝 0) := by
    have h1 : Tendsto (fun R : ℝ => R ^ ((d : ℝ) + α)) atTop atTop := tendsto_rpow_atTop hp
    have h2 : Tendsto (fun R : ℝ => 2 ^ ((d : ℝ) + α) / R ^ ((d : ℝ) + α)) atTop (𝓝 0) :=
      h1.const_div_atTop _
    refine h2.congr' ?_
    filter_upwards [eventually_gt_atTop (0 : ℝ)] with R hR
    rw [Real.div_rpow (by norm_num) hR.le]
  obtain ⟨R, hRlt, hR2⟩ :=
    ((hlim.eventually (eventually_lt_nhds hδ)).and (eventually_ge_atTop (2 : ℝ))).exists
  exact ⟨R, hR2, fun hdom => by
    have hle := le_coe_of_cutKernel_le d hd α hα hR2 hdom
    linarith⟩

/-! ## 4. The window transfer with an explicit coefficient -/

end Witness

/-- **Every fourth cutoff moment on a window, from one uncut first moment.**  With an explicit
coefficient `c` dominating the cutoff kernel on `(0, R]`, finiteness of the uncut first moment at
`M.betaCrit * c` gives finiteness of `M.cutMoment 4 r` for every `r ∈ (0, R]`. -/
theorem SourceModelData.cutMoment_four_ne_top_uniform_window_of_domination
    (M : SourceModelData) {R : ℝ} {c : NNReal}
    (hdom : ∀ r : ℝ, 0 < r → r ≤ R → ∀ e : Sym2 M.V, M.cutKernel r e ≤ (c : ℝ) * M.kernel e)
    (hfin : (∫⁻ ω, clusterVol ω (0 : M.V) ∂(M.law (M.betaCrit * c))) ≠ ⊤) :
    ∀ r : ℝ, 0 < r → r ≤ R → M.cutMoment 4 r ≠ ⊤ := by
  have h4 := M.uncutMoment_four_ne_top_of_first hfin
  exact fun r hr0 hrR => ne_top_of_le_ne_top h4 (M.cutMoment_le_reduced_nnreal (hdom r hr0 hrR) 4)

namespace Witness

/-- **The `p = 2` off-corner derivative at the exact reduced intensity `β_c (1 - (2/R)^(d+α))`.**

The window `(a, b]` must lie below `R`, and the single finiteness supplied is the one for the
sharp coefficient.  In particular the whole subcritical family of the sharpness input is not
consumed: at a bounded window one point of `[0, β_c)` suffices, and §3 says no smaller one does. -/
theorem hasDerivAt_cutMomentReal_two_of_eps (d : ℕ) (hd : 1 ≤ d) (α : ℝ) (hα : 0 < α)
    {R : ℝ} (hR : 2 ≤ R) {c : NNReal}
    (hc : 1 - (2 / R) ^ ((d : ℝ) + α) ≤ (c : ℝ))
    (hfin : (∫⁻ ω, clusterVol ω (0 : (sourceModelWitness d hd α hα).V)
        ∂((sourceModelWitness d hd α hα).law ((sourceModelWitness d hd α hα).betaCrit * c)))
      ≠ ⊤)
    {a b r0 : ℝ} (hwin : (sourceModelWitness d hd α hα).IsOffCornerWindow a b)
    (har : a < r0) (hrb : r0 < b) (hbR : b ≤ R)
    (hsphere : ∀ y : (sourceModelWitness d hd α hα).V,
      (sourceModelWitness d hd α hα).S.ρ (toVec y) ≠ r0) :
    HasDerivAt (fun r => (sourceModelWitness d hd α hα).cutMomentReal 2 r)
      (powLawCoeff ((sourceModelWitness d hd α hα).betaCrit : ℝ) d α r0
        * ((sourceModelWitness d hd α hα).p2RHS r0).toReal) r0 :=
  hasDerivAt_cutMomentReal_two_sourceModelWitness_offCorner d hd α hα hwin har hrb
    (fun t ht => (sourceModelWitness d hd α hα).cutMoment_four_ne_top_uniform_window_of_domination
      (fun r hr0 hrR => cutKernel_le_of_le_coe (r := r) d hd α hα hR hr0 hrR hc) hfin t
      (lt_trans hwin.1 ht.1) (le_trans ht.2 hbR)) hsphere

/-- **The paper's cutoff-mass derivative at the exact reduced intensity.**

The same single finiteness `β_c * c` with `c ≥ 1 - (2/R)^(d+α)` (see
`hasDerivAt_cutMomentReal_two_of_eps`) yields the derivative of `cutMassReal` at every
off-corner point `r0` of a window `[a, b]` with `b ≤ R`, i.e. the object of Proposition I.4.2
localised to one subcritical intensity. -/
theorem sourceModelWitness_hasDerivAt_cutMassReal_powerLaw_of_eps
    (d : ℕ) (hd : 1 ≤ d) (α : ℝ) (hα : 0 < α)
    {R : ℝ} (hR : 2 ≤ R) {c : NNReal}
    (hc : 1 - (2 / R) ^ ((d : ℝ) + α) ≤ (c : ℝ))
    (hfin : (∫⁻ ω, clusterVol ω (0 : (sourceModelWitness d hd α hα).V)
        ∂((sourceModelWitness d hd α hα).law ((sourceModelWitness d hd α hα).betaCrit * c)))
      ≠ ⊤)
    {a b r0 : ℝ} (hwin : (sourceModelWitness d hd α hα).IsOffCornerWindow a b)
    (har : a < r0) (hrb : r0 < b) (hbR : b ≤ R) :
    HasDerivAt (sourceModelWitness d hd α hα).cutMassReal
      (((sourceModelWitness d hd α hα).betaCrit : ℝ) * r0 ^ (-(d : ℝ) - α - 1) *
        (sourceModelWitness d hd α hα).exclScalar r0) r0 := by
  have hr0 : 0 < r0 := lt_trans hwin.1 har
  have hb : 0 < b := lt_trans hr0 hrb
  have hoff : r0 ∉ (sourceModelWitness d hd α hα).cornerRadii :=
    hwin.2.2 r0 ⟨le_of_lt har, le_of_lt hrb⟩
  have h4b : (sourceModelWitness d hd α hα).cutMoment 4 b ≠ ⊤ :=
    (sourceModelWitness d hd α hα).cutMoment_four_ne_top_uniform_window_of_domination
      (fun r hr0' hrR => cutKernel_le_of_le_coe (r := r) d hd α hα hR hr0' hrR hc) hfin b hb
      hbR
  have h1b : (sourceModelWitness d hd α hα).cutMoment 1 b ≠ ⊤ :=
    ne_top_of_le_ne_top h4b
      (lintegral_mono fun ω => pow_le_pow_right₀
        (SourceModelData.one_le_clusterVol ω (0 : (sourceModelWitness d hd α hα).V))
        (by norm_num))
  exact sourceModelWitness_hasDerivAt_cutMassReal_powerLaw_of_firstMoment d hd α hα hr0 hrb hoff h1b

end Witness

end PercLib.CriticalLRP.Orchestration

/-! ## Axiom audit -/

#print axioms
  PercLib.CriticalLRP.Orchestration.SourceModelData.cutKernel_le_scaled_of_eps
#print axioms
  PercLib.CriticalLRP.Orchestration.Witness.K_eq_K_two_mul
#print axioms
  PercLib.CriticalLRP.Orchestration.Witness.kernel_single
#print axioms
  PercLib.CriticalLRP.Orchestration.Witness.cutKernel_single
#print axioms
  PercLib.CriticalLRP.Orchestration.Witness.cutKernel_le_of_le_coe
#print axioms
  PercLib.CriticalLRP.Orchestration.Witness.le_coe_of_cutKernel_le
#print axioms
  PercLib.CriticalLRP.Orchestration.Witness.cutKernel_le_iff_coe
#print axioms
  PercLib.CriticalLRP.Orchestration.Witness.exists_cutKernel_not_le
#print axioms
  PercLib.CriticalLRP.Orchestration.SourceModelData.cutMoment_four_ne_top_uniform_window_of_domination
#print axioms
  PercLib.CriticalLRP.Orchestration.Witness.hasDerivAt_cutMomentReal_two_of_eps
#print axioms
  PercLib.CriticalLRP.Orchestration.Witness.sourceModelWitness_hasDerivAt_cutMassReal_powerLaw_of_eps
