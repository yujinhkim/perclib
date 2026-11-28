/-
Copyright (c) 2026 PercLib contributors. Released under Apache 2.0.

Accepted and independently rebuilt from Ultramath `smwzqts7r`, member m3.
Production review base `e2b5cf635f5a2ffb1c7f203271de1c0a7ef3ad2b`;
reviewed scratch source `.scratch/review-smwzqts7r/m3/SumLevel.lean`.
-/

module

/-
Direction (F), sum level: the corner jump of the first-moment flux.

The single-edge (summand) statements live in `Corner.lean`.  Here we assemble the **full
summed flux** `firstFlux y r = ∑'_e cutEdgeDeriv r e · pivotalFlux (cutLaw r) g e` of the
singleton observation `g = 1{y ∈ K}` and prove:

* `tendsto_m8FluxTerm_singleton_nhdsLT_corner`: for every edge, the flux summand has the
  left limit `cornerLimitTerm` at the attained radius (shorter edges keep their value,
  corner edges contribute `0`, longer edges contribute `0`);
* `tendsto_firstFlux_nhdsLT_cornerLimit`: **Tannery for the source flux** — the full flux
  has that left limit, from the landed radius-uniform summable envelope
  (`m1_exists_uniform_fluxEnvelope`), i.e. from a genuine kernel-summability estimate;
* `not_continuousAt_firstFlux_of_corner`: the corner summand is *not lost in the limit*, so
  the full flux is **discontinuous** at the attained radius whenever the corner pivotal flux
  is positive.  This is the sum-level coefficient discontinuity the direction asks for.

Retained inputs (all explicit): a positive corner pivotal flux at `‖y‖` (the measure-side
fact isolated in `Corner.lean`), continuity of `K'` at `‖y‖`, a bound on `-K'` on the window
`[‖y‖/2, ‖y‖]`, `K'(ρ) < 0` and finite first cutoff moment at some `ρ > ‖y‖`.
-/
public import PercLib.CriticalLRP.Analysis.SecondMomentCase3.RadialRegularity.CornerFlux.Defs
public import PercLib.CriticalLRP.Analysis.SecondMomentCase3.RadialRegularity.CornerFlux.Main

/-! ## Direct-pivotal mass and the summed singleton flux at attained radii -/

set_option autoImplicit false
set_option linter.style.longLine false
set_option linter.hashCommand false
set_option linter.unusedSectionVars false

@[expose] public section

noncomputable section

open MeasureTheory Filter Topology Set
open scoped ENNReal NNReal Topology

namespace PercLib.CriticalLRP.Orchestration

namespace SourceModelData

variable (M : SourceModelData)

/-! ## 0. Nonnegativity of the singleton flux summands -/

/-- The pivotal flux of any edge for the cluster indicator of `y` is nonnegative: forcing the
edge open only adds connections. -/
theorem pivotalFlux_singleton_nonneg (y : M.V) (r : ℝ) (e : Sym2 M.V) :
    0 ≤ pivotalFlux (M.cutLaw r) (sMomentTrunc (fun _ => (1 : ℝ)) (0 : M.V) ({y} : Finset M.V)) e := by
  have hE : MeasurableSet (M.connEvent y) := M.measurableSet_connEvent y
  have hfun : pivotalFlux (M.cutLaw r)
      (sMomentTrunc (fun _ => (1 : ℝ)) (0 : M.V) ({y} : Finset M.V)) e
      = (M.cutLaw r).real (M.rawOpenEvent e (M.connEvent y))
        - (M.cutLaw r).real (M.rawClosedEvent e (M.connEvent y)) := by
    unfold pivotalFlux
    rw [M.sMomentTrunc_singleton_as_indicator y, M.connEvent_eq_cluster]
    exact M.integral_flipDiff_indicator (M.cutLaw r) e hE
  have hsub : M.rawClosedEvent e (M.connEvent y) ⊆ M.rawOpenEvent e (M.connEvent y) := by
    intro ω hω
    simp only [SourceModelData.rawClosedEvent, SourceModelData.rawOpenEvent,
      SourceModelData.connEvent, mem_preimage, Set.mem_ofPred_eq] at hω ⊢
    refine connects_mono (fun f hf => ?_) hω
    rw [forceOn_empty_eq] at hf
    have hmem : f ∈ (ω \ ({e} : Set (Sym2 M.V))) ∪ ({e} ∩ ({e} : Set (Sym2 M.V))) := Or.inl hf
    simpa [forceOn] using hmem
  have hmono : (M.cutLaw r).real (M.rawClosedEvent e (M.connEvent y))
      ≤ (M.cutLaw r).real (M.rawOpenEvent e (M.connEvent y)) :=
    measureReal_mono hsub (measure_ne_top _ _)
  rw [hfun]
  linarith

/-- The singleton flux summand is nonnegative. -/
theorem m8FluxTerm_singleton_nonneg (y : M.V) {r : ℝ} (hr : 0 < r) (e : Sym2 M.V) :
    0 ≤ M.m8FluxTerm (sMomentTrunc (fun _ => (1 : ℝ)) (0 : M.V) ({y} : Finset M.V)) r e :=
  mul_nonneg (M.cutEdgeDeriv_nonneg (M.neg_deriv_K_nonneg hr) e)
    (M.pivotalFlux_singleton_nonneg y r e)

/-- The singleton flux summand of an edge vanishes strictly below the edge length. -/
theorem m8FluxTerm_singleton_eq_zero_of_lt {y : M.V} {x z : M.V} {r : ℝ}
    (h : r < M.S.dist x z) :
    M.m8FluxTerm (sMomentTrunc (fun _ => (1 : ℝ)) (0 : M.V) ({y} : Finset M.V)) r s(x, z) = 0 := by
  unfold m8FluxTerm
  rw [M.m8_cutEdgeDeriv_eq_zero_of_lt h, zero_mul]

/-! ## 1. Termwise left limits at an attained radius -/

/-- **The flux summand has a left limit at every radius**, equal to `cornerLimitTerm`:
shorter edges keep their value at the radius, while edges of length exactly the radius (and
longer ones) contribute `0`. -/
theorem tendsto_m8FluxTerm_singleton_nhdsLT_corner {y : M.V} {s : ℝ} (hs : 0 < s)
    (hK : ContinuousAt (fun r : ℝ => deriv M.K r) s)
    {r₁ : ℝ} (hr₁ : s < r₁) (hfin : M.cutMassAt r₁ 0 ≠ ⊤) (e : Sym2 M.V) :
    Tendsto (fun r => M.m8FluxTerm (sMomentTrunc (fun _ => (1 : ℝ)) (0 : M.V) ({y} : Finset M.V)) r e)
      (𝓝[<] s)
      (𝓝 (M.cornerLimitTerm (sMomentTrunc (fun _ => (1 : ℝ)) (0 : M.V) ({y} : Finset M.V)) s e)) := by
  classical
  induction e using Sym2.ind with
  | _ x z =>
    simp only [cornerLimitTerm, M.sourceEdgeLen_mk]
    rcases lt_trichotomy (M.S.dist x z) s with hlt | heq | hgt
    · rw [ite_eq_left hlt]
      exact (M.m8_continuousAt_m8FluxTerm_of_ne_dist hs hlt.ne hK
        (M.continuousAt_pivotalFlux_singleton hs hr₁ hfin y s(x, z))).tendsto.mono_left
          nhdsWithin_le_nhds
    · rw [← heq, ite_eq_right (lt_irrefl _)]
      refine (tendsto_const_nhds (x := (0 : ℝ))).congr' ?_
      filter_upwards [self_mem_nhdsWithin] with r hr
      exact (M.m8FluxTerm_singleton_eq_zero_of_lt (y := y) hr).symm
    · rw [ite_eq_right (not_lt.mpr hgt.le)]
      refine (tendsto_const_nhds (x := (0 : ℝ))).congr' ?_
      filter_upwards [self_mem_nhdsWithin] with r hr
      exact (M.m8FluxTerm_singleton_eq_zero_of_lt (y := y) (lt_trans hr hgt)).symm

/-! ## 2. Tannery for the full flux -/

/-- **The full first-moment flux has the corner left limit.**  The landed radius-uniform
summable envelope of `OffCorner/RadiusEnvelope` gives the dominator; Tannery's theorem then
identifies the limit of the flux series with the series of the termwise limits. -/
theorem tendsto_firstFlux_nhdsLT_cornerLimit {y : M.V} {s ρ C : ℝ} (hs : 0 < s) (hsρ : s < ρ)
    (hC0 : 0 ≤ C) (hCb : ∀ r ∈ Icc (s / 2) s, -(deriv M.K r) ≤ C)
    (hKρ : deriv M.K ρ < 0) (hvol : M.cutMoment 1 ρ ≠ ⊤)
    (hK : ContinuousAt (fun r : ℝ => deriv M.K r) s) :
    Tendsto (M.firstFlux y) (𝓝[<] s)
      (𝓝 (∑' e, M.cornerLimitTerm
        (sMomentTrunc (fun _ => (1 : ℝ)) (0 : M.V) ({y} : Finset M.V)) s e)) := by
  have hs0 : (0 : ℝ) < s / 2 := by linarith
  have hle : s / 2 ≤ s := by linarith
  have hρ0 : 0 < ρ := lt_trans hs hsρ
  have hfin : M.cutMassAt ρ 0 ≠ ⊤ := by
    rw [M.cutMassAt_zero_eq_cutMoment]; exact hvol
  obtain ⟨hu, henv⟩ :=
    M.m1_exists_uniform_fluxEnvelope (a' := s / 2) (b' := s) (ρ := ρ) (C := C)
      hs0 hle hsρ.le hCb hC0 hKρ hρ0 hvol y
  have hG : M.firstFlux y
      = fun r => ∑' e, M.m8FluxTerm
          (sMomentTrunc (fun _ => (1 : ℝ)) (0 : M.V) ({y} : Finset M.V)) r e := by
    funext r
    exact M.m8_sMomentInfFlux_eq_tsum (0 : M.V) ({y} : Finset M.V) (fun _ => (1 : ℝ)) r
  rw [hG]
  refine tendsto_tsum_of_dominated_convergence hu (fun e => ?_) ?_
  · exact M.tendsto_m8FluxTerm_singleton_nhdsLT_corner (y := y) hs hK hsρ hfin e
  · have h1 : ∀ᶠ r : ℝ in 𝓝 s, s / 2 < r := eventually_gt_nhds (by linarith)
    filter_upwards [h1.filter_mono nhdsWithin_le_nhds, self_mem_nhdsWithin] with r hr hr'
    exact fun e => by
      rw [Real.norm_eq_abs]
      exact henv r ⟨le_of_lt hr, le_of_lt hr'⟩ e

/-! ## 3. The corner summand survives the limit: the summed flux jumps -/

/-- **Quantitative corner inequality for the summed first-moment flux.**  At the attained
off-diagonal radius `s = ‖y‖` the flux exceeds the left limit `∑'_e cornerLimitTerm` by at
least the corner mass `β_c(-K'(s)) · directPivot y s`. -/
theorem firstFlux_jump_ge {y : M.V} (hy : y ≠ (0 : M.V)) {ρ C : ℝ}
    (hsρ : M.S.dist 0 y < ρ) (hC0 : 0 ≤ C)
    (hCb : ∀ r ∈ Icc (M.S.dist 0 y / 2) (M.S.dist 0 y), -(deriv M.K r) ≤ C)
    (hKρ : deriv M.K ρ < 0) (hvol : M.cutMoment 1 ρ ≠ ⊤) :
    (∑' e, M.cornerLimitTerm
        (sMomentTrunc (fun _ => (1 : ℝ)) (0 : M.V) ({y} : Finset M.V)) (M.S.dist 0 y) e)
      + (M.betaCrit : ℝ) * (-(deriv M.K (M.S.dist 0 y))) * M.directPivot y (M.S.dist 0 y)
      ≤ M.firstFlux y (M.S.dist 0 y) := by
  set s : ℝ := M.S.dist 0 y with hsdef
  set g : Config M.V → ℝ :=
    sMomentTrunc (fun _ => (1 : ℝ)) (0 : M.V) ({y} : Finset M.V) with hgdef
  set e₀ : Sym2 M.V := s(0, y) with he₀def
  have hs : 0 < s := M.S.dist_pos (fun h => hy h.symm)
  have hsρ' : s < ρ := hsρ
  have hs0 : (0 : ℝ) < s / 2 := by linarith
  have hle : s / 2 ≤ s := by linarith
  have hρ0 : 0 < ρ := lt_trans hs hsρ'
  set u : Sym2 M.V → ℝ := fun e => C / (-(deriv M.K ρ)) *
      Real.exp ((M.betaCrit : ℝ) * (M.K (s / 2) - M.K ρ)) *
        (|M.cutEdgeDeriv ρ e| * (2 * (M.cutLaw s).real {ω | e ∈ touchSet ω (0 : M.V)})) with hu_def
  obtain ⟨hu, henv⟩ :=
    M.m1_exists_uniform_fluxEnvelope (a' := s / 2) (b' := s) (ρ := ρ) (C := C)
      hs0 hle hsρ'.le hCb hC0 hKρ hρ0 hvol y
  have hu' : Summable u := hu
  have hterm_bound : ∀ e : Sym2 M.V, ‖M.m8FluxTerm g s e‖ ≤ u e := by
    intro e
    rw [Real.norm_eq_abs]
    exact henv s ⟨by linarith, le_rfl⟩ e
  have hFnn : ∀ e : Sym2 M.V, 0 ≤ M.m8FluxTerm g s e :=
    fun e => M.m8FluxTerm_singleton_nonneg y hs e
  have hsumF : Summable (fun e => M.m8FluxTerm g s e) :=
    Summable.of_nonneg_of_le hFnn (fun e => by
      simpa only [Real.norm_eq_abs, abs_of_nonneg (hFnn e)] using hterm_bound e) hu'
  have hFe₀ : M.m8FluxTerm g s e₀
      = (M.betaCrit : ℝ) * (-(deriv M.K s)) * M.directPivot y s := by
    rw [he₀def]
    exact M.m8FluxTerm_direct_at_self hy
  have hF'₀ : M.cornerLimitTerm g s e₀ = 0 := by
    simp only [cornerLimitTerm, he₀def, M.sourceEdgeLen_mk]
    rw [ite_eq_right (lt_irrefl s)]
  have hpt : ∀ e : Sym2 M.V, M.cornerLimitTerm g s e ≤ M.m8FluxTerm g s e := by
    intro e
    simp only [cornerLimitTerm]
    split_ifs with h
    · exact le_rfl
    · exact hFnn e
  have hF'nn : ∀ e : Sym2 M.V, 0 ≤ M.cornerLimitTerm g s e := by
    intro e
    simp only [cornerLimitTerm]
    split_ifs with h
    · exact hFnn e
    · exact le_rfl
  have hsumF' : Summable (fun e => M.cornerLimitTerm g s e) := by
    refine Summable.of_nonneg_of_le hF'nn (fun e => ?_) hu'
    calc M.cornerLimitTerm g s e ≤ M.m8FluxTerm g s e := hpt e
      _ = |M.m8FluxTerm g s e| := (abs_of_nonneg (hFnn e)).symm
      _ = ‖M.m8FluxTerm g s e‖ := (Real.norm_eq_abs _).symm
      _ ≤ u e := hterm_bound e
  have hsplit : (∑' e, M.m8FluxTerm g s e)
      = M.m8FluxTerm g s e₀ + ∑' e, (if e = e₀ then (0 : ℝ) else M.m8FluxTerm g s e) :=
    hsumF.tsum_eq_add_tsum_ite e₀
  have hsplit' : (∑' e, M.cornerLimitTerm g s e)
      = ∑' e, (if e = e₀ then (0 : ℝ) else M.cornerLimitTerm g s e) := by
    rw [← hF'₀]
    refine tsum_congr fun e => ?_
    by_cases he : e = e₀
    · subst he; simp
    · simp [he]
  have hcmp : (∑' e, (if e = e₀ then (0 : ℝ) else M.cornerLimitTerm g s e))
      ≤ ∑' e, (if e = e₀ then (0 : ℝ) else M.m8FluxTerm g s e) := by
    have hf : Summable (fun e => (if e = e₀ then (0 : ℝ) else M.cornerLimitTerm g s e)) := by
      refine Summable.of_nonneg_of_le (fun e => ?_) (fun e => ?_) hsumF'
      · by_cases he : e = e₀
        · subst he; simp
        · simp only [he, ite_false]; exact hF'nn e
      · by_cases he : e = e₀
        · subst he; simp [hF'₀]
        · simp only [he, ite_false]; exact le_rfl
    have hg : Summable (fun e => (if e = e₀ then (0 : ℝ) else M.m8FluxTerm g s e)) := by
      refine Summable.of_nonneg_of_le (fun e => ?_) (fun e => ?_) hsumF
      · by_cases he : e = e₀
        · subst he; simp
        · simp only [he, ite_false]; exact hFnn e
      · by_cases he : e = e₀
        · subst he; simp [hFnn]
        · simp only [he, ite_false]; exact le_rfl
    exact Summable.tsum_le_tsum (fun e => by
      by_cases he : e = e₀
      · subst he; simp
      · simp only [he, ite_false]; exact hpt e) hf hg
  have hgapSum : (∑' e, M.cornerLimitTerm g s e) + M.m8FluxTerm g s e₀
      ≤ ∑' e, M.m8FluxTerm g s e := by
    rw [hsplit', hsplit]
    linarith [hcmp]
  have hval : M.firstFlux y s = ∑' e, M.m8FluxTerm g s e :=
    M.m8_sMomentInfFlux_eq_tsum (0 : M.V) ({y} : Finset M.V) (fun _ => (1 : ℝ)) s
  rw [← hval, hFe₀] at hgapSum
  exact hgapSum

/-- **The summed first-moment flux is discontinuous at an attained off-diagonal radius**
whenever the corner pivotal flux of the direct edge is positive.  The jump is at least
`β_c(-K'(‖y‖)) · directPivot y ‖y‖ > 0`. -/
theorem not_continuousAt_firstFlux_of_corner {y : M.V} (hy : y ≠ (0 : M.V)) {ρ C : ℝ}
    (hsρ : M.S.dist 0 y < ρ) (hC0 : 0 ≤ C)
    (hCb : ∀ r ∈ Icc (M.S.dist 0 y / 2) (M.S.dist 0 y), -(deriv M.K r) ≤ C)
    (hKρ : deriv M.K ρ < 0) (hvol : M.cutMoment 1 ρ ≠ ⊤)
    (hK : ContinuousAt (fun r : ℝ => deriv M.K r) (M.S.dist 0 y))
    (hβ : (0 : ℝ) < (M.betaCrit : ℝ))
    (hK' : deriv M.K (M.S.dist 0 y) ≠ 0)
    (hgap : 0 < M.directPivot y (M.S.dist 0 y)) :
    ¬ ContinuousAt (M.firstFlux y) (M.S.dist 0 y) := by
  set s : ℝ := M.S.dist 0 y with hsdef
  have hs : 0 < s := M.S.dist_pos (fun h => hy h.symm)
  have hjump := M.firstFlux_jump_ge (y := y) hy hsρ hC0 hCb hKρ hvol
  rw [← hsdef] at hjump
  have hKneg : deriv M.K s < 0 := lt_of_le_of_ne (M.deriv_K_nonpos hs) hK'
  have hpos : 0 < (M.betaCrit : ℝ) * (-(deriv M.K s)) * M.directPivot y s :=
    mul_pos (mul_pos hβ (by linarith)) hgap
  intro hcont
  have hleft : Tendsto (M.firstFlux y) (𝓝[<] s) (𝓝 (M.firstFlux y s)) :=
    hcont.tendsto.mono_left nhdsWithin_le_nhds
  have hlim := M.tendsto_firstFlux_nhdsLT_cornerLimit (y := y) hs hsρ hC0 hCb hKρ hvol hK
  have heq : (∑' e, M.cornerLimitTerm
        (sMomentTrunc (fun _ => (1 : ℝ)) (0 : M.V) ({y} : Finset M.V)) s e)
      = M.firstFlux y s := tendsto_nhds_unique hlim hleft
  linarith

/-! ## 4. Confinement capstone -/

/-- **Confinement implies a corner in the summed flux.**  If with positive probability the
cutoff cluster of the origin stays inside a ball of radius `L < ‖y‖`, then the corner pivotal
mass of the direct edge is positive (`directPivot_pos_of_escape`), and consequently the full
first-moment flux is discontinuous at the attained radius. -/
theorem not_continuousAt_firstFlux_of_escape {y : M.V} (hy : y ≠ (0 : M.V)) {L ρ C : ℝ}
    (hLs : L < M.S.dist 0 y)
    (hesc : (M.cutLaw (M.S.dist 0 y)).real (M.escapeAt (0 : M.V) L) < 1)
    (hsρ : M.S.dist 0 y < ρ) (hC0 : 0 ≤ C)
    (hCb : ∀ r ∈ Icc (M.S.dist 0 y / 2) (M.S.dist 0 y), -(deriv M.K r) ≤ C)
    (hKρ : deriv M.K ρ < 0) (hvol : M.cutMoment 1 ρ ≠ ⊤)
    (hK : ContinuousAt (fun r : ℝ => deriv M.K r) (M.S.dist 0 y))
    (hβ : (0 : ℝ) < (M.betaCrit : ℝ))
    (hK' : deriv M.K (M.S.dist 0 y) ≠ 0) :
    ¬ ContinuousAt (M.firstFlux y) (M.S.dist 0 y) :=
  M.not_continuousAt_firstFlux_of_corner hy hsρ hC0 hCb hKρ hvol hK hβ hK'
    (M.directPivot_pos_of_escape hLs rfl hesc)

end SourceModelData

/-! ## Axiom audit -/

set_option linter.hashCommand false in
#print axioms SourceModelData.pivotalFlux_singleton_nonneg
#print axioms SourceModelData.m8FluxTerm_singleton_nonneg
#print axioms SourceModelData.m8FluxTerm_singleton_eq_zero_of_lt
#print axioms SourceModelData.m8FluxTerm_direct_at_self
#print axioms SourceModelData.tendsto_m8FluxTerm_singleton_nhdsLT_corner
#print axioms SourceModelData.tendsto_firstFlux_nhdsLT_cornerLimit
#print axioms SourceModelData.firstFlux_jump_ge
#print axioms SourceModelData.not_continuousAt_firstFlux_of_corner
#print axioms SourceModelData.not_continuousAt_firstFlux_of_escape

end PercLib.CriticalLRP.Orchestration
