/-
Copyright (c) 2026 PercLib contributors. Released under Apache 2.0.

Accepted from independent swarm `smwp7ai5u` direction D2, then independently
recompiled by the integrator.  Proof-only: no new model definition, no altered
frozen declaration, and no finite-moment inference.
-/

/-
# The cutoff limit for the genuine `SourceModelData`

`SourceModelMoments.lean` proves the *comparison* `P_{β,r} ≤ P_{γ,r} ≤ P_γ` at an
arbitrary admissible source norm.  It does not prove that the cutoff moments
`M.cutMoment p r` converge as `r → ∞`.  The raw sup-norm modules obtain the limit from
the pointwise convergence of the cut profile, but they take `Tendsto K atTop (𝓝 0)` as a
hypothesis (`K` is the profile of the raw `cutoffSymKernel`).

This file closes both gaps for the source model:

* `SourceModelData.tendsto_K_atTop_zero` *derives* `K → 0` from the actual fields of
  `SourceModelData`: `K_eq_integral` writes `K` as the tail integral of `|K'|`, and
  `exists_error` bounds `|K' s| ≤ 2 s^{-d-α-1}` eventually, so
  `K r ≤ 2 r^{-(d+α)}/(d+α) → 0`.  No `K r / K 1` coefficient is used anywhere; that
  coefficient is genuinely false at a general norm (`Flat.flat_coefficient_bound_false`
  exhibits an admissible norm with a nonzero lattice point at distance `1/2`), so the
  general-norm route has to go through the pointwise profile bounds used here.
* `iSup_lintegral_clusterVol_pow_cutRadialSym` and
  `tendsto_lintegral_clusterVol_pow_cutRadialSym` are the general engine for an
  *arbitrary* `SourceNormData d` and any admissible radial profile, with `hKtop`
  explicit.  The only property of the norm that is used is `S.dist_pos`; in particular
  the engine applies to the flat norm of `FlatNorm/Defs.lean`, not only to `2‖·‖∞`.
* `SourceModelData.tendsto_cutMoment` and `SourceModelData.iSup_cutMoment_eq` are the
  source-model conclusions, with no `hKtop` hypothesis left.

All identities are in `ℝ≥0∞` and hold with value `⊤` on either side: nothing here
asserts that any moment is finite.
-/
module

public import PercLib.CriticalLRP.MomentMonotonicity.SourceModelMoments
public import PercLib.CriticalLRP.Orchestration.SourceModelNonvacuity

set_option autoImplicit false

open MeasureTheory Measure ProbabilityTheory unitInterval Filter Topology Set
open scoped ENNReal NNReal Topology

@[expose] public section

namespace PercLib.CriticalLRP.Orchestration

open PercLib.CriticalLRP FiniteVolume CutoffMomentTransfer CutoffLimit

variable {d : ℕ}

/-! ## The profile vanishes at infinity -/

/-- **The source profile vanishes at infinity.**  `K_eq_integral` writes `K` as the tail
integral of `|K'|`, and `exists_error` gives `|K' s| = (1 + δ s) s^{-d-α-1}` with
`δ → 0`, so `|K' s| ≤ 2 s^{-d-α-1}` eventually and `K r ≤ 2 r^{-(d+α)}/(d+α) → 0`.

This is the premise the raw sup-norm cutoff theorems assume and the source model supplies. -/
theorem SourceModelData.tendsto_K_atTop_zero (M : SourceModelData) :
    Tendsto M.K atTop (𝓝 0) := by
  obtain ⟨δ, hderiv, hlogerr⟩ := M.exists_error
  simp only [PercLib.CriticalLRP.Analysis.IsLogErrorFunction,
    PercLib.CriticalLRP.Analysis.LogarithmicallyIntegrable] at hlogerr
  obtain ⟨⟨-, -⟩, hδtend⟩ := hlogerr
  have hd0 : (0 : ℝ) ≤ (M.d : ℝ) := Nat.cast_nonneg M.d
  have hcpos : 0 < (M.d : ℝ) + M.α := by linarith [M.hα]
  have hev : ∀ᶠ s : ℝ in atTop, 1 + δ s < 2 := by
    have h1 : Tendsto (fun s : ℝ => (1 : ℝ) + δ s) atTop (𝓝 ((1 : ℝ) + 0)) :=
      tendsto_const_nhds.add hδtend
    have h2 : Tendsto (fun s : ℝ => 1 + δ s) atTop (𝓝 1) := by simpa using h1
    exact h2.eventually (isOpen_Iio.mem_nhds (by norm_num : (1 : ℝ) ∈ Set.Iio 2))
  obtain ⟨R₁, hR₁⟩ := eventually_atTop.mp hev
  set R : ℝ := max R₁ 1 with hRdef
  have hRpos : 0 < R := lt_of_lt_of_le one_pos (le_max_right _ _)
  have hR₁le : R₁ ≤ R := le_max_left _ _
  have hb : ∀ s : ℝ, R ≤ s → 1 + δ s ≤ 2 := fun s hs => le_of_lt (hR₁ s (le_trans hR₁le hs))
  have hpoint : ∀ s ∈ Set.Ioi R,
      |deriv M.K s| ≤ 2 * s ^ (-(M.d : ℝ) - M.α - 1) := by
    intro s hs
    have hs0 : 0 < s := lt_trans hRpos hs
    rw [hderiv s hs0]
    exact mul_le_mul_of_nonneg_right (hb s (le_of_lt hs)) (Real.rpow_nonneg hs0.le _)
  have hexp : -(M.d : ℝ) - M.α - 1 < -1 := by linarith [M.hα]
  have hbaseInt : ∀ x : ℝ, 0 < x →
      IntegrableOn (fun s : ℝ => s ^ (-(M.d : ℝ) - M.α - 1)) (Set.Ioi x) :=
    fun x hx => integrableOn_Ioi_rpow_of_lt hexp hx
  have hint : IntegrableOn (fun s : ℝ => |deriv M.K s|) (Set.Ioi R) := by
    have hg : IntegrableOn (fun s : ℝ => 2 * s ^ (-(M.d : ℝ) - M.α - 1))
        (Set.Ioi R) := (hbaseInt R hRpos).const_mul 2
    rw [IntegrableOn] at hg ⊢
    refine Integrable.mono hg ((measurable_deriv M.K).abs.aestronglyMeasurable) ?_
    filter_upwards [ae_restrict_mem measurableSet_Ioi] with s hs
    have hp : (0 : ℝ) ≤ s ^ (-(M.d : ℝ) - M.α - 1) :=
      (Real.rpow_pos_of_pos (lt_trans hRpos hs) _).le
    have hp2 : (0 : ℝ) ≤ 2 * s ^ (-(M.d : ℝ) - M.α - 1) := by linarith
    simpa [Real.norm_eq_abs, abs_of_nonneg hp, abs_of_nonneg hp2] using hpoint s hs
  have hKr : ∀ r : ℝ, R ≤ r →
      M.K r ≤ 2 * (r ^ (-(M.d : ℝ) - M.α) / ((M.d : ℝ) + M.α)) := by
    intro r hr
    have hrpos : 0 < r := lt_of_lt_of_le hRpos hr
    rw [M.K_eq_integral r hrpos]
    have hintr : IntegrableOn (fun s : ℝ => |deriv M.K s|) (Set.Ioi r) :=
      hint.mono_set (Set.Ioi_subset_Ioi hr)
    have hgr : IntegrableOn (fun s : ℝ => 2 * s ^ (-(M.d : ℝ) - M.α - 1)) (Set.Ioi r) :=
      (hbaseInt r hrpos).const_mul 2
    have hcmp : ∫ s in Set.Ioi r, |deriv M.K s| ≤
        ∫ s in Set.Ioi r, 2 * s ^ (-(M.d : ℝ) - M.α - 1) := by
      refine setIntegral_mono_on hintr hgr measurableSet_Ioi ?_
      intro s hs
      exact hpoint s (Set.mem_Ioi.mpr (lt_of_le_of_lt hr hs))
    have hval : ∫ s in Set.Ioi r, 2 * s ^ (-(M.d : ℝ) - M.α - 1)
        = 2 * (r ^ (-(M.d : ℝ) - M.α) / ((M.d : ℝ) + M.α)) := by
      rw [integral_const_mul, integral_Ioi_rpow_of_lt hexp hrpos]
      have hb1 : -(M.d : ℝ) - M.α - 1 + 1 = -((M.d : ℝ) + M.α) := by ring
      rw [hb1]
      rw [show -(M.d : ℝ) - M.α = -((M.d : ℝ) + M.α) from by ring]
      have hcne : (M.d : ℝ) + M.α ≠ 0 := ne_of_gt hcpos
      field_simp
    linarith [hcmp, hval]
  have hlim : Tendsto (fun r : ℝ => 2 * (r ^ (-(M.d : ℝ) - M.α) / ((M.d : ℝ) + M.α)))
      atTop (𝓝 0) := by
    have h1 : Tendsto (fun r : ℝ => r ^ (-((M.d : ℝ) + M.α))) atTop (𝓝 0) :=
      tendsto_rpow_neg_atTop hcpos
    have h2 : Tendsto (fun r : ℝ => r ^ (-((M.d : ℝ) + M.α)) / ((M.d : ℝ) + M.α))
        atTop (𝓝 0) := by
      simpa using h1.div_const ((M.d : ℝ) + M.α)
    have h3 : Tendsto (fun r : ℝ => 2 * (r ^ (-((M.d : ℝ) + M.α)) / ((M.d : ℝ) + M.α)))
        atTop (𝓝 0) := by
      simpa using h2.const_mul 2
    refine h3.congr' ?_
    filter_upwards with r
    rw [show -(M.d : ℝ) - M.α = -((M.d : ℝ) + M.α) from by ring]
  refine tendsto_of_tendsto_of_tendsto_of_le_of_le' tendsto_const_nhds hlim ?_ ?_
  · filter_upwards [eventually_gt_atTop (0 : ℝ)] with r hr using M.K_nonneg r hr
  · filter_upwards [eventually_ge_atTop R] with r hr using hKr r hr

/-! ## The general cutoff engine at an arbitrary admissible source norm -/

/-- Cutting off can only lower the radial profile: `J_r ≤ J_{r'}` at every edge, for
`r ≤ r'`.  Both signs of the cutoff are covered: a nonpositive cutoff gives the zero
profile off the diagonal. -/
theorem cutRadialSym_mono (S : SourceNormData d) {K : ℝ → ℝ}
    (hK : AntitoneOn K (Set.Ioi 0)) {r r' : ℝ} (h : r ≤ r')
    (e : Sym2 (Fin d → ℤ)) : cutRadialSym S K r e ≤ cutRadialSym S K r' e := by
  induction e using Sym2.ind with
  | _ x y =>
    rw [cutRadialSym, cutRadialSym, radialSym_mk, radialSym_mk]
    by_cases hxy : x = y
    · rw [ite_eq_left hxy, ite_eq_left hxy]
    · rw [ite_eq_right hxy, ite_eq_right hxy]
      by_cases hr : 0 < r
      · exact cutoffProfile_mono_r hK hr (lt_of_lt_of_le hr h) (S.dist_pos hxy) h
      · rw [cutoffProfile_of_lt (by linarith [S.dist_pos hxy] : r < S.dist x y)]
        exact cutoffProfile_nonneg_on hK (S.dist_pos hxy)

/-- The cut profile converges to the uncut profile at every edge, provided `K → 0`. -/
theorem cutRadialSym_tendsto (S : SourceNormData d) {K : ℝ → ℝ}
    (hKtop : Tendsto K atTop (𝓝 0)) (e : Sym2 (Fin d → ℤ)) :
    Tendsto (fun r : ℝ => cutRadialSym S K r e) atTop (𝓝 (radialSym S K e)) := by
  induction e using Sym2.ind with
  | _ x y =>
    simp only [cutRadialSym]
    by_cases hxy : x = y
    · simp only [radialSym_mk, ite_eq_left hxy]
      exact tendsto_const_nhds
    · simp only [radialSym_mk, ite_eq_right hxy]
      exact tendsto_cutoffProfile hKtop

/-- Edge-open probabilities converge as the cutoff grows, at any source norm. -/
theorem tendsto_bernoulliEdgeProb_cutRadialSym (S : SourceNormData d) {K : ℝ → ℝ}
    (hK : AntitoneOn K (Set.Ioi 0)) (hKnn : ∀ t, 0 < t → 0 ≤ K t)
    (hKtop : Tendsto K atTop (𝓝 0))
    (β : NNReal) (e : Sym2 (Fin d → ℤ)) :
    Tendsto (fun r : ℝ =>
        ((bernoulliEdgeProb (cutRadialSym S K r)
          (fun e => radialSym_nonneg S (fun _ hs => cutoffProfile_nonneg_on hK hs) e) β e :
            unitInterval) : ℝ)) atTop
      (𝓝 ((bernoulliEdgeProb (radialSym S K) (radialSym_nonneg S hKnn) β e :
        unitInterval) : ℝ)) := by
  have hk := cutRadialSym_tendsto S hKtop e
  have hcont : Continuous fun t : ℝ => (1 : ℝ) - Real.exp (-((β : ℝ) * t)) := by fun_prop
  have h1 : Tendsto (fun r : ℝ =>
      (1 : ℝ) - Real.exp (-((β : ℝ) * cutRadialSym S K r e))) atTop
      (𝓝 ((1 : ℝ) - Real.exp (-((β : ℝ) * radialSym S K e)))) :=
    (hcont.tendsto _).comp hk
  exact h1

/-- **The cutoff moments increase to the uncut moment at every natural order**, for an
arbitrary admissible source norm and any admissible radial profile with `K → 0` at
infinity.  Both sides are extended reals: no moment is asserted to be finite. -/
theorem iSup_lintegral_clusterVol_pow_cutRadialSym (S : SourceNormData d) {K : ℝ → ℝ}
    (hK : AntitoneOn K (Set.Ioi 0)) (hKnn : ∀ t, 0 < t → 0 ≤ K t)
    (hKtop : Tendsto K atTop (𝓝 0))
    (β : NNReal) (o : Fin d → ℤ) (k : ℕ) :
    (⨆ r : ℝ, ∫⁻ ω, clusterVol ω o ^ k
        ∂(longRangeMeasure (cutRadialSym S K r)
          (fun e => radialSym_nonneg S (fun _ hs => cutoffProfile_nonneg_on hK hs) e) β))
      = ∫⁻ ω, clusterVol ω o ^ k
        ∂(longRangeMeasure (radialSym S K) (radialSym_nonneg S hKnn) β) := by
  have hmono : ∀ (r r' : ℝ) (e : Sym2 (Fin d → ℤ)), r ≤ r' →
      bernoulliEdgeProb (cutRadialSym S K r)
        (fun e => radialSym_nonneg S (fun _ hs => cutoffProfile_nonneg_on hK hs) e) β e ≤
      bernoulliEdgeProb (cutRadialSym S K r')
        (fun e => radialSym_nonneg S (fun _ hs => cutoffProfile_nonneg_on hK hs) e) β e :=
    fun r r' e hrr' => bernoulliEdgeProb_mono_kernel
      (fun e => cutRadialSym_mono S hK hrr' e) _ _ β e
  have hlim : ∀ e : Sym2 (Fin d → ℤ),
      Tendsto (fun r : ℝ => ((bernoulliEdgeProb (cutRadialSym S K r)
        (fun e => radialSym_nonneg S (fun _ hs => cutoffProfile_nonneg_on hK hs) e) β e :
          unitInterval) : ℝ)) atTop
      (𝓝 ((bernoulliEdgeProb (radialSym S K) (radialSym_nonneg S hKnn) β e :
        unitInterval) : ℝ)) :=
    fun e => tendsto_bernoulliEdgeProb_cutRadialSym S hK hKnn hKtop β e
  exact iSup_lintegral_clusterVol_pow_real hmono hlim o k

/-- The cutoff moments are nondecreasing in the cutoff radius, at every order. -/
theorem monotone_lintegral_clusterVol_pow_cutRadialSym (S : SourceNormData d) {K : ℝ → ℝ}
    (hK : AntitoneOn K (Set.Ioi 0)) (β : NNReal) (o : Fin d → ℤ) (k : ℕ) :
    Monotone fun r : ℝ => ∫⁻ ω, clusterVol ω o ^ k
      ∂(longRangeMeasure (cutRadialSym S K r)
        (fun e => radialSym_nonneg S (fun _ hs => cutoffProfile_nonneg_on hK hs) e) β) :=
  fun _r _r' hrr' => lintegral_clusterVol_pow_mono_of_le
    (fun e => bernoulliEdgeProb_mono_kernel
      (fun e => cutRadialSym_mono S hK hrr' e) _ _ β e) o k

/-- Convergence form of the same statement. -/
theorem tendsto_lintegral_clusterVol_pow_cutRadialSym (S : SourceNormData d) {K : ℝ → ℝ}
    (hK : AntitoneOn K (Set.Ioi 0)) (hKnn : ∀ t, 0 < t → 0 ≤ K t)
    (hKtop : Tendsto K atTop (𝓝 0))
    (β : NNReal) (o : Fin d → ℤ) (k : ℕ) :
    Tendsto (fun r : ℝ => ∫⁻ ω, clusterVol ω o ^ k
        ∂(longRangeMeasure (cutRadialSym S K r)
          (fun e => radialSym_nonneg S (fun _ hs => cutoffProfile_nonneg_on hK hs) e) β)) atTop
      (𝓝 (∫⁻ ω, clusterVol ω o ^ k
        ∂(longRangeMeasure (radialSym S K) (radialSym_nonneg S hKnn) β))) := by
  rw [← iSup_lintegral_clusterVol_pow_cutRadialSym S hK hKnn hKtop β o k]
  exact tendsto_atTop_iSup (monotone_lintegral_clusterVol_pow_cutRadialSym S hK β o k)

/-- **Connectivity probabilities of the cutoff law increase to the uncut ones**, at any
admissible source norm.  This is the event-level form of the cutoff limit (it is not a
statement about the real-valued two-point function of the uncut law, whose finiteness is
not addressed here). -/
theorem iSup_edgeMeasure_connects_cutRadialSym (S : SourceNormData d) {K : ℝ → ℝ}
    (hK : AntitoneOn K (Set.Ioi 0)) (hKnn : ∀ t, 0 < t → 0 ≤ K t)
    (hKtop : Tendsto K atTop (𝓝 0)) (β : NNReal) (v w : Fin d → ℤ) :
    (⨆ r : ℝ, edgeMeasure (bernoulliEdgeProb (cutRadialSym S K r)
        (fun e => radialSym_nonneg S (fun _ hs => cutoffProfile_nonneg_on hK hs) e) β)
        {ω : Config (Fin d → ℤ) | Connects ω v w})
      = edgeMeasure (bernoulliEdgeProb (radialSym S K) (radialSym_nonneg S hKnn) β)
        {ω : Config (Fin d → ℤ) | Connects ω v w} := by
  have hnat := iSup_edgeMeasure_connects
    (p := fun (n : ℕ) (e : Sym2 (Fin d → ℤ)) => bernoulliEdgeProb (cutRadialSym S K (n : ℝ))
      (fun e => radialSym_nonneg S (fun _ hs => cutoffProfile_nonneg_on hK hs) e) β e)
    (q := bernoulliEdgeProb (radialSym S K) (radialSym_nonneg S hKnn) β)
    (fun n e => bernoulliEdgeProb_mono_kernel
      (fun e => cutRadialSym_mono S hK (by push_cast; linarith) e) _ _ β e)
    (fun e => (tendsto_bernoulliEdgeProb_cutRadialSym S hK hKnn hKtop β e).comp
      tendsto_natCast_atTop_atTop) v w
  have hmonoR : Monotone fun r : ℝ => edgeMeasure (bernoulliEdgeProb (cutRadialSym S K r)
      (fun e => radialSym_nonneg S (fun _ hs => cutoffProfile_nonneg_on hK hs) e) β)
      {ω : Config (Fin d → ℤ) | Connects ω v w} :=
    fun r r' hrr' => edgeMeasure_mono_of_le
      (fun e => bernoulliEdgeProb_mono_kernel (fun e => cutRadialSym_mono S hK hrr' e) _ _ β e)
      (measurableSet_connects v w) (isIncreasing_connects v w)
  rw [iSup_real_eq_iSup_nat hmonoR]
  exact hnat

/-! ## The source model: no `hKtop` hypothesis remains -/

/-- The source-model cutoff kernel is nondecreasing in the cutoff radius, at every edge
and for every admissible source norm. -/
theorem SourceModelData.cutKernel_mono (M : SourceModelData) {r r' : ℝ} (h : r ≤ r') :
    M.cutKernel r ≤ M.cutKernel r' :=
  fun e => cutRadialSym_mono M.S M.K_antitone h e

/-- The source-model cutoff kernel converges to the uncut kernel. -/
theorem SourceModelData.cutKernel_tendsto (M : SourceModelData) (e : Sym2 M.V) :
    Tendsto (fun r : ℝ => M.cutKernel r e) atTop (𝓝 (M.kernel e)) :=
  cutRadialSym_tendsto M.S M.tendsto_K_atTop_zero e

/-- Cutoff connection probabilities converge to the uncut ones. -/
theorem SourceModelData.iSup_connects_eq (M : SourceModelData) (x y : M.V) :
    (⨆ r : ℝ, M.cutLaw r {ω : Config M.V | Connects ω x y})
      = M.law M.betaCrit {ω : Config M.V | Connects ω x y} :=
  iSup_edgeMeasure_connects_cutRadialSym M.S M.K_antitone M.K_nonneg
    M.tendsto_K_atTop_zero M.betaCrit x y

/-- **Every natural cutoff moment of a genuine source model increases to its uncut
value.**  No finiteness is claimed on either side. -/
theorem SourceModelData.iSup_cutMoment_eq (M : SourceModelData) (p : ℕ) :
    (⨆ r : ℝ, M.cutMoment p r) =
      ∫⁻ ω, clusterVol ω (0 : M.V) ^ p ∂(M.law M.betaCrit) :=
  iSup_lintegral_clusterVol_pow_cutRadialSym M.S M.K_antitone M.K_nonneg
    M.tendsto_K_atTop_zero M.betaCrit 0 p

/-- The cutoff-moment limit at an arbitrary cluster root.  The engine is root-independent;
`M.cutMoment` is the special case `o = 0`. -/
theorem SourceModelData.iSup_lintegral_clusterVol_pow_cutLaw (M : SourceModelData)
    (p : ℕ) (o : M.V) :
    (⨆ r : ℝ, ∫⁻ ω, clusterVol ω o ^ p ∂(M.cutLaw r))
      = ∫⁻ ω, clusterVol ω o ^ p ∂(M.law M.betaCrit) :=
  iSup_lintegral_clusterVol_pow_cutRadialSym M.S M.K_antitone M.K_nonneg
    M.tendsto_K_atTop_zero M.betaCrit o p

/-- Convergence form at an arbitrary cluster root. -/
theorem SourceModelData.tendsto_lintegral_clusterVol_pow_cutLaw (M : SourceModelData)
    (p : ℕ) (o : M.V) :
    Tendsto (fun r : ℝ => ∫⁻ ω, clusterVol ω o ^ p ∂(M.cutLaw r)) atTop
      (𝓝 (∫⁻ ω, clusterVol ω o ^ p ∂(M.law M.betaCrit))) :=
  tendsto_lintegral_clusterVol_pow_cutRadialSym M.S M.K_antitone M.K_nonneg
    M.tendsto_K_atTop_zero M.betaCrit o p

/-- The cutoff moments are nondecreasing in the cutoff radius. -/
theorem SourceModelData.cutMoment_monotone (M : SourceModelData) (p : ℕ) :
    Monotone fun r : ℝ => M.cutMoment p r :=
  monotone_lintegral_clusterVol_pow_cutRadialSym M.S M.K_antitone M.betaCrit 0 p

/-- **Extended-real convergence `E_{β_c,r}|K_0|^p → E_{β_c}|K_0|^p` for every natural
`p`, including divergence to `⊤`.** -/
theorem SourceModelData.tendsto_cutMoment (M : SourceModelData) (p : ℕ) :
    Tendsto (fun r : ℝ => M.cutMoment p r) atTop
      (𝓝 (∫⁻ ω, clusterVol ω (0 : M.V) ^ p ∂(M.law M.betaCrit))) :=
  tendsto_lintegral_clusterVol_pow_cutRadialSym M.S M.K_antitone M.K_nonneg
    M.tendsto_K_atTop_zero M.betaCrit 0 p

/-- At every fixed cutoff the moment is dominated by the uncut moment. -/
theorem SourceModelData.cutMoment_le_uncut (M : SourceModelData) (p : ℕ) (r : ℝ) :
    M.cutMoment p r ≤ ∫⁻ ω, clusterVol ω (0 : M.V) ^ p ∂(M.law M.betaCrit) := by
  rw [← M.iSup_cutMoment_eq p]
  exact le_iSup (fun r : ℝ => M.cutMoment p r) r

/-- A bound uniform in the cutoff transfers to the uncut moment.  No such bound is
constructed here; the converse domination is `SourceModelData.cutMoment_le_uncut`. -/
theorem SourceModelData.uncutMoment_ne_top_of_forall_cutMoment_le (M : SourceModelData)
    (p : ℕ) (C : ℝ≥0∞) (hC : C ≠ ⊤) (h : ∀ r : ℝ, M.cutMoment p r ≤ C) :
    (∫⁻ ω, clusterVol ω (0 : M.V) ^ p ∂(M.law M.betaCrit)) ≠ ⊤ := by
  rw [← M.iSup_cutMoment_eq p]
  exact ne_top_of_le_ne_top hC (iSup_le h)

/-- Divergence propagates from any cutoff to the uncut moment.  The converse is not
proved here: finiteness at every individual cutoff does not by itself give finiteness of
the uncut moment without a bound uniform in the cutoff
(`SourceModelData.uncutMoment_ne_top_of_forall_cutMoment_le`). -/
theorem SourceModelData.uncutMoment_eq_top_of_cutMoment_eq_top (M : SourceModelData)
    (p : ℕ) (r : ℝ) (h : M.cutMoment p r = ⊤) :
    (∫⁻ ω, clusterVol ω (0 : M.V) ^ p ∂(M.law M.betaCrit)) = ⊤ := by
  have hle := M.cutMoment_le_uncut p r
  rw [h] at hle
  exact top_le_iff.mp hle

/-- The order-`0` moment is `1` at every cutoff: the statement is not vacuous at `p = 0`
and the limit is the constant `1`. -/
theorem SourceModelData.cutMoment_zero (M : SourceModelData) (r : ℝ) :
    M.cutMoment 0 r = 1 := by
  have hprob : IsProbabilityMeasure (M.cutLaw r) := by
    rw [SourceModelData.cutLaw]
    infer_instance
  have := hprob
  simp [SourceModelData.cutMoment]

/-- Non-vacuity: the explicit witness model of `ModelWitness/Defs.lean` satisfies the
source-model limit theorem, so none of the conclusions above is vacuous for want of a
model. -/
example : Nonempty SourceModelData :=
  ⟨Witness.sourceModelWitness 1 le_rfl 1 zero_lt_one⟩

example (p : ℕ) :
    Tendsto (fun r : ℝ => (Witness.sourceModelWitness 1 le_rfl 1 zero_lt_one).cutMoment p r)
      atTop
      (𝓝 (∫⁻ ω, clusterVol ω
          (0 : (Witness.sourceModelWitness 1 le_rfl 1 zero_lt_one).V) ^ p
        ∂((Witness.sourceModelWitness 1 le_rfl 1 zero_lt_one).law
          (Witness.sourceModelWitness 1 le_rfl 1 zero_lt_one).betaCrit))) :=
  (Witness.sourceModelWitness 1 le_rfl 1 zero_lt_one).tendsto_cutMoment p

/-- The engine is genuinely norm-independent, including norms that are not the normalized
sup norm.  At the flat norm of `FlatNorm/Defs.lean` a nonzero lattice edge has source
distance `1/2 < 1`, so no step may assume unit lattice spacing. -/
example : Flat.flatSourceNorm.dist 0 Flat.e1 = 1 / 2 := Flat.flat_dist_e1

/-- The general engine applies at the normalized flat norm with the source power-law
profile: a non-vacuous non-sup-norm instance of the cutoff limit. -/
example (β : NNReal) (o : Fin 2 → ℤ) (k : ℕ) :
    (⨆ r : ℝ, ∫⁻ ω, clusterVol ω o ^ k
        ∂(longRangeMeasure (cutRadialSym Flat.flatSourceNorm (modelProfile 2 1) r)
          (fun e => radialSym_nonneg Flat.flatSourceNorm (fun _ hs => cutoffProfile_nonneg_on
            (modelProfile_antitoneOn 2 (by norm_num)) hs) e) β))
      = ∫⁻ ω, clusterVol ω o ^ k
        ∂(longRangeMeasure (radialSym Flat.flatSourceNorm (modelProfile 2 1))
          (radialSym_nonneg Flat.flatSourceNorm (fun _ ht => (modelProfile_pos ht).le)) β) :=
  iSup_lintegral_clusterVol_pow_cutRadialSym Flat.flatSourceNorm
    (modelProfile_antitoneOn 2 (by norm_num)) (fun _ ht => (modelProfile_pos ht).le)
    (tendsto_modelProfile (by norm_num)) β o k

end PercLib.CriticalLRP.Orchestration

/-! ## Axiom audit -/

#print axioms PercLib.CriticalLRP.Orchestration.SourceModelData.tendsto_K_atTop_zero
#print axioms PercLib.CriticalLRP.Orchestration.cutRadialSym_mono
#print axioms PercLib.CriticalLRP.Orchestration.cutRadialSym_tendsto
#print axioms PercLib.CriticalLRP.Orchestration.tendsto_bernoulliEdgeProb_cutRadialSym
#print axioms PercLib.CriticalLRP.Orchestration.iSup_lintegral_clusterVol_pow_cutRadialSym
#print axioms PercLib.CriticalLRP.Orchestration.monotone_lintegral_clusterVol_pow_cutRadialSym
#print axioms PercLib.CriticalLRP.Orchestration.tendsto_lintegral_clusterVol_pow_cutRadialSym
#print axioms PercLib.CriticalLRP.Orchestration.iSup_edgeMeasure_connects_cutRadialSym
#print axioms PercLib.CriticalLRP.Orchestration.SourceModelData.cutKernel_mono
#print axioms PercLib.CriticalLRP.Orchestration.SourceModelData.cutKernel_tendsto
#print axioms PercLib.CriticalLRP.Orchestration.SourceModelData.iSup_connects_eq
#print axioms PercLib.CriticalLRP.Orchestration.SourceModelData.iSup_cutMoment_eq
#print axioms PercLib.CriticalLRP.Orchestration.SourceModelData.iSup_lintegral_clusterVol_pow_cutLaw
#print axioms PercLib.CriticalLRP.Orchestration.SourceModelData.tendsto_lintegral_clusterVol_pow_cutLaw
#print axioms PercLib.CriticalLRP.Orchestration.SourceModelData.cutMoment_monotone
#print axioms PercLib.CriticalLRP.Orchestration.SourceModelData.tendsto_cutMoment
#print axioms PercLib.CriticalLRP.Orchestration.SourceModelData.cutMoment_le_uncut
#print axioms PercLib.CriticalLRP.Orchestration.SourceModelData.uncutMoment_ne_top_of_forall_cutMoment_le
#print axioms PercLib.CriticalLRP.Orchestration.SourceModelData.uncutMoment_eq_top_of_cutMoment_eq_top
#print axioms PercLib.CriticalLRP.Orchestration.SourceModelData.cutMoment_zero
