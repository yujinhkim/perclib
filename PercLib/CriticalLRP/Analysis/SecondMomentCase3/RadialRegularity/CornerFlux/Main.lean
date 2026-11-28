/-
Copyright (c) 2026 PercLib contributors. Released under Apache 2.0.

Accepted and independently rebuilt from Ultramath `smwzqts7r`, member m3.
Production review base `e2b5cf635f5a2ffb1c7f203271de1c0a7ef3ad2b`;
reviewed scratch source `.scratch/review-smwzqts7r/m3/Corner.lean`.
-/

module

/-
Direction (F): the measure-side corner fact for the simple connecting pivotal event.

Main content:

* `rawOpenEvent_direct`: forcing the direct edge `s(0,y)` open makes the connection
  `0 ↔ y` certain, so the forced-open mass is `1`.
* `directPivot_eq_one_sub_cornerGap`: the pivotal flux of the direct edge at radius `r`
  is **exactly** `1 - cornerGap y r`, i.e. `P_r(0 ↔ y after the direct edge is deleted)`.
  Nothing is assumed: this is the measure-side identity behind the corner at `r = ‖y‖`.
* `cornerGap_le_twoPoint` / `one_sub_twoPoint_le_directPivot`: the corner contribution is
  at least the two-point non-degeneracy gap.
* `cornerGap_lt_one_of_escape`: a **positive probability of confinement** below the
  attained radius forces the corner gap to be `< 1`, hence the pivotal flux to be `> 0`.
  This is the precise measure-side input the corner needs.
* `m8FluxTerm_direct_eq_zero_of_lt` / `m8FluxTerm_direct_at_self`: the flux summand of
  the corner edge is `0` strictly below `‖y‖` and equals
  `β_c (-K'(‖y‖)) · directPivot` at `‖y‖`.
* `not_continuousAt_m8FluxTerm_direct_of_pos`: if the corner pivotal flux is nonzero (and
  the coefficient is), the *flux summand* has a genuine jump at the attained radius.
-/
public import PercLib.CriticalLRP.Analysis.SecondMomentCase3.RadialRegularity.CornerFlux.Defs

/-! ## Direct-pivotal mass and the summed singleton flux at attained radii -/

set_option autoImplicit false
set_option linter.style.longLine false
set_option linter.hashCommand false

@[expose] public section

noncomputable section

open MeasureTheory Filter Topology Set
open scoped ENNReal NNReal Topology

namespace PercLib.CriticalLRP.Orchestration

namespace SourceModelData

variable (M : SourceModelData)

/-! ## 1. The forced-open mass of the direct edge is one -/

/-- Forcing the direct edge `s(0,y)` open makes `0` and `y` connected, so the
forced-open event of the cluster indicator is the whole configuration space. -/
theorem rawOpenEvent_direct (y : M.V) :
    M.rawOpenEvent s(0, y) (M.connEvent y) = Set.univ := by
  ext ω
  constructor
  · intro _; exact trivial
  · intro _
    change Connects (forceOn ({s(0, y)} : Set (Sym2 M.V)) ({s(0, y)} : Config M.V) ω) (0 : M.V) y
    have hmem : s(0, y) ∈ forceOn ({s(0, y)} : Set (Sym2 M.V)) ({s(0, y)} : Config M.V) ω := by
      simp [forceOn]
    rcases eq_or_ne y 0 with rfl | hy
    · exact connects_refl _ _
    · exact (openGraph_adj.mpr ⟨fun h => hy h.symm, hmem⟩).reachable

/-- The corner gap is the forced-closed connection mass. -/
theorem cornerGap_eq_rawClosed (y : M.V) (s : ℝ) :
    M.cornerGap y s = (M.cutLaw s).real (M.rawClosedEvent s(0, y) (M.connEvent y)) := rfl

/-- **The pivotal flux of the direct edge is the non-degeneracy gap.** -/
theorem directPivot_eq_one_sub_cornerGap (y : M.V) (r : ℝ) :
    M.directPivot y r = 1 - M.cornerGap y r := by
  have hE : MeasurableSet (M.connEvent y) := M.measurableSet_connEvent y
  have hmain : M.directPivot y r
      = (M.cutLaw r).real (M.rawOpenEvent s(0, y) (M.connEvent y))
        - (M.cutLaw r).real (M.rawClosedEvent s(0, y) (M.connEvent y)) := by
    unfold directPivot pivotalFlux
    rw [M.sMomentTrunc_singleton_as_indicator y, M.connEvent_eq_cluster]
    exact M.integral_flipDiff_indicator (M.cutLaw r) s(0, y) hE
  rw [hmain, M.rawOpenEvent_direct, M.cornerGap_eq_rawClosed]
  have huniv : (M.cutLaw r).real (Set.univ : Set (Config M.V)) = 1 := by
    rw [Measure.real, measure_univ]
    norm_num
  rw [huniv]

/-- The pivotal flux of the direct edge is nonnegative: deleting the edge can only destroy
connections. -/
theorem directPivot_nonneg (y : M.V) (r : ℝ) : 0 ≤ M.directPivot y r := by
  have hE : MeasurableSet (M.connEvent y) := M.measurableSet_connEvent y
  have hclosed : MeasurableSet (M.rawClosedEvent s(0, y) (M.connEvent y)) :=
    M.measurableSet_rawClosedEvent s(0, y) hE
  have hopen : MeasurableSet (M.rawOpenEvent s(0, y) (M.connEvent y)) :=
    M.measurableSet_rawOpenEvent s(0, y) hE
  have hsub : M.rawClosedEvent s(0, y) (M.connEvent y) ⊆ M.rawOpenEvent s(0, y) (M.connEvent y) := by
    intro ω hω
    rw [M.rawOpenEvent_direct]
    exact trivial
  have hmono : (M.cutLaw r).real (M.rawClosedEvent s(0, y) (M.connEvent y))
      ≤ (M.cutLaw r).real (M.rawOpenEvent s(0, y) (M.connEvent y)) :=
    measureReal_mono hsub (measure_ne_top _ _)
  rw [M.rawOpenEvent_direct] at hmono
  have huniv : (M.cutLaw r).real (Set.univ : Set (Config M.V)) = 1 := by
    rw [Measure.real, measure_univ]; norm_num
  rw [M.directPivot_eq_one_sub_cornerGap, M.cornerGap_eq_rawClosed]
  linarith [hmono, huniv]

/-- The pivotal flux of the direct edge is at most one. -/
theorem directPivot_le_one (y : M.V) (r : ℝ) : M.directPivot y r ≤ 1 := by
  have hE : MeasurableSet (M.connEvent y) := M.measurableSet_connEvent y
  have hclosed : MeasurableSet (M.rawClosedEvent s(0, y) (M.connEvent y)) :=
    M.measurableSet_rawClosedEvent s(0, y) hE
  have hnn : 0 ≤ (M.cutLaw r).real (M.rawClosedEvent s(0, y) (M.connEvent y)) :=
    measureReal_nonneg
  rw [M.directPivot_eq_one_sub_cornerGap, M.cornerGap_eq_rawClosed]
  linarith

/-- **Strict positivity of the corner pivotal flux is exactly the corner gap.** -/
theorem directPivot_pos_iff (y : M.V) (r : ℝ) :
    0 < M.directPivot y r ↔ M.cornerGap y r < 1 := by
  rw [M.directPivot_eq_one_sub_cornerGap]
  constructor <;> intro h <;> linarith

/-! ## 2. The corner contribution dominates the two-point non-degeneracy gap -/

/-- Deleting the direct edge can only destroy the connection: the forced-closed mass is at
most the two-point mass. -/
theorem cornerGap_le_twoPoint (y : M.V) (s : ℝ) :
    M.cornerGap y s ≤ (M.cutLaw s).real (M.connEvent y) := by
  refine measureReal_mono ?_
  intro ω hω
  exact connects_mono (fun e he => by rw [forceOn_empty_eq] at he; exact he.1) hω

/-- The corner pivotal flux is at least the two-point non-degeneracy gap `1 - τ`. -/
theorem one_sub_twoPoint_le_directPivot (y : M.V) (s : ℝ) :
    1 - (M.cutLaw s).real (M.connEvent y) ≤ M.directPivot y s := by
  rw [M.directPivot_eq_one_sub_cornerGap]
  linarith [M.cornerGap_le_twoPoint y s]



/-! ## 2c. At the attained radius the corner mass is exactly the two-point gap -/

/-- The mass of a single open edge is its edge probability. -/
theorem real_openEvent_singleton (r : ℝ) (e : Sym2 M.V) :
    (M.cutLaw r).real {ω : Config M.V | e ∈ ω} = ((M.cutProb r e : unitInterval) : ℝ) := by
  have hset : {ω : Config M.V | e ∈ ω}
      = {ω : Config M.V | ∀ f ∈ ({e} : Finset (Sym2 M.V)), f ∈ ω} := by
    ext ω; simp
  rw [hset, M.cutLaw_eq_edgeMeasure r, measureReal_def,
    edgeMeasure_cylinder (M.cutProb r) ({e} : Finset (Sym2 M.V))]
  simp [Finset.prod_singleton]

/-- **The direct edge `s(0,y)` is a.s. closed at the attained radius `‖y‖`** (its kernel gap
vanishes there), hence deleting it does not change the cutoff law. -/
theorem cutProb_self_dist_eq_zero (y : M.V) :
    ((M.cutProb (M.S.dist 0 y) s(0, y) : unitInterval) : ℝ) = 0 := by
  rw [M.cutProb_coe_eq, M.cutKernel_mk]
  by_cases hy : y = (0 : M.V)
  · rw [ite_eq_left (show (0 : M.V) = y from hy.symm)]
    simp
  · rw [ite_eq_right (fun h => hy h.symm)]
    have hprof : FiniteVolume.cutoffProfile M.K (M.S.dist 0 y) (M.S.dist 0 y) = 0 := by
      rw [FiniteVolume.cutoffProfile_of_le le_rfl, sub_self]
    rw [hprof, mul_zero, neg_zero, Real.exp_zero]
    norm_num

/-- **Deleting the a.s.-closed direct edge does not change the connection probability.** -/
theorem cornerGap_eq_twoPoint_at_dist (y : M.V) :
    M.cornerGap y (M.S.dist 0 y) = (M.cutLaw (M.S.dist 0 y)).real (M.connEvent y) := by
  have hE : MeasurableSet (M.connEvent y) := M.measurableSet_connEvent y
  -- every forced-closed connection is a connection
  have hsub : M.rawClosedEvent s(0, y) (M.connEvent y) ⊆ M.connEvent y := by
    intro ω hω
    simp only [SourceModelData.rawClosedEvent, SourceModelData.connEvent, mem_preimage,
      Set.mem_ofPred_eq] at hω ⊢
    refine connects_mono (fun f hf => ?_) hω
    have hf' : f ∈ ω \ ({s(0, y)} : Set (Sym2 M.V)) := by
      simpa only [forceOn_empty_eq] using hf
    exact hf'.1
  -- a connection destroyed by deleting the direct edge requires that edge to be open
  have hsub2 : M.connEvent y ⊆
      M.rawClosedEvent s(0, y) (M.connEvent y) ∪ {ω : Config M.V | s(0, y) ∈ ω} := by
    intro ω hω
    by_contra hcon
    have hnotopen : s(0, y) ∉ ω := fun he => hcon (Or.inr he)
    have heq : forceOn ({s(0, y)} : Set (Sym2 M.V)) (∅ : Config M.V) ω = ω := by
      rw [forceOn_empty_eq]
      ext f
      simp only [Set.mem_sdiff, Set.mem_singleton_iff]
      exact ⟨fun h => h.1, fun hf => ⟨hf, fun hfe => hnotopen (hfe ▸ hf)⟩⟩
    have hmem : ω ∈ M.rawClosedEvent s(0, y) (M.connEvent y) := by
      simp only [SourceModelData.rawClosedEvent, SourceModelData.connEvent, mem_preimage,
        Set.mem_ofPred_eq, heq]
      simpa only [SourceModelData.connEvent, Set.mem_ofPred_eq] using hω
    exact hcon (Or.inl hmem)
  have hm1 : (M.cutLaw (M.S.dist 0 y)).real (M.rawClosedEvent s(0, y) (M.connEvent y))
      ≤ (M.cutLaw (M.S.dist 0 y)).real (M.connEvent y) :=
    measureReal_mono hsub (measure_ne_top _ _)
  have hm2 : (M.cutLaw (M.S.dist 0 y)).real (M.connEvent y)
      ≤ (M.cutLaw (M.S.dist 0 y)).real
          (M.rawClosedEvent s(0, y) (M.connEvent y) ∪ {ω : Config M.V | s(0, y) ∈ ω}) :=
    measureReal_mono hsub2 (measure_ne_top _ _)
  have hzero : (M.cutLaw (M.S.dist 0 y)).real {ω : Config M.V | s(0, y) ∈ ω} = 0 := by
    rw [M.real_openEvent_singleton, M.cutProb_self_dist_eq_zero]
  have hunion := measureReal_union_le (μ := M.cutLaw (M.S.dist 0 y))
    (M.rawClosedEvent s(0, y) (M.connEvent y)) {ω : Config M.V | s(0, y) ∈ ω}
  rw [hzero] at hunion
  have hfin : (M.cutLaw (M.S.dist 0 y)).real (M.rawClosedEvent s(0, y) (M.connEvent y))
      = (M.cutLaw (M.S.dist 0 y)).real (M.connEvent y) := by linarith
  rw [M.cornerGap_eq_rawClosed, hfin]

/-- **The corner pivotal mass at the attained radius is exactly the two-point gap**
`1 - τ_{β_c,‖y‖}(0,y)`. -/
theorem directPivot_eq_one_sub_twoPoint (y : M.V) :
    M.directPivot y (M.S.dist 0 y)
      = 1 - (M.cutLaw (M.S.dist 0 y)).real (M.connEvent y) := by
  rw [M.directPivot_eq_one_sub_cornerGap, M.cornerGap_eq_twoPoint_at_dist]


/-- **The corner pivotal mass vanishes exactly when the critical cutoff two-point function is
one at the attained radius.**  This is the exact residual of the measure-side corner fact: it
is not a statement about the coefficient `K'`, but a strict non-degeneracy statement about
`τ_{β_c,‖y‖}(0,y)`. -/
theorem directPivot_eq_zero_iff_twoPoint_eq_one (y : M.V) :
    M.directPivot y (M.S.dist 0 y) = 0 ↔ (M.cutLaw (M.S.dist 0 y)).real (M.connEvent y) = 1 := by
  rw [M.directPivot_eq_one_sub_twoPoint]
  constructor <;> intro h <;> linarith

/-! ## 2b. The pivot of the direct edge *is* its pivotal mass -/

/-- **The pivotal flux of the direct edge is the mass of its pivotal event.**  For the
increasing connection event, forcing the edge closed never adds a connection, so the pivot is
exactly the probability that forcing the edge open connects `0` to `y` while forcing it closed
does not.  Hence `0 < directPivot y s` is literally a statement of nonzero pivotal mass. -/
theorem directPivot_eq_pivotalMass (y : M.V) (r : ℝ) :
    M.directPivot y r
      = (M.cutLaw r).real
          (M.rawOpenEvent s(0, y) (M.connEvent y)
            \ M.rawClosedEvent s(0, y) (M.connEvent y)) := by
  have hE : MeasurableSet (M.connEvent y) := M.measurableSet_connEvent y
  have hclosed : MeasurableSet (M.rawClosedEvent s(0, y) (M.connEvent y)) :=
    M.measurableSet_rawClosedEvent s(0, y) hE
  have hsub : M.rawClosedEvent s(0, y) (M.connEvent y) ⊆ M.rawOpenEvent s(0, y) (M.connEvent y) := by
    intro ω _
    rw [M.rawOpenEvent_direct]
    exact trivial
  rw [measureReal_sdiff hsub hclosed, M.directPivot_eq_one_sub_cornerGap,
    M.cornerGap_eq_rawClosed, M.rawOpenEvent_direct]
  have huniv : (M.cutLaw r).real (Set.univ : Set (Config M.V)) = 1 := by
    rw [Measure.real, measure_univ]; norm_num
  rw [huniv]

/-- **Vanishing of the pivotal mass is exactly degeneracy of the deleted-edge connection.** -/
theorem directPivot_eq_zero_iff (y : M.V) (r : ℝ) :
    M.directPivot y r = 0 ↔ M.cornerGap y r = 1 := by
  rw [M.directPivot_eq_one_sub_cornerGap]
  constructor <;> intro h <;> linarith

/-! ## 3. A positive probability of confinement below the corner radius -/

/-- The complement of the escape event is the event that the cluster stays in the ball. -/
theorem compl_escapeAt (v : M.V) (R : ℝ) :
    (M.escapeAt v R)ᶜ
      = {ω : Config M.V | ∀ z : M.V, Connects ω v z → z ∈ M.ball R} := by
  ext ω
  simp only [SourceModelData.escapeAt, mem_compl_iff, Set.mem_ofPred_eq]
  constructor
  · intro h z hz
    exact Classical.byContradiction fun hz' => h ⟨z, hz', hz⟩
  · rintro h ⟨z, hz, hc⟩
    exact hz (h z hc)

/-- **Confinement below the corner radius forces a genuine corner.**  If with positive
probability the cluster of the origin stays inside a ball of radius `L < ‖y‖`, then the
origin is not connected to `y` after the direct edge is deleted, so the corner gap is
`< 1` and the pivotal flux is positive. -/
theorem cornerGap_lt_one_of_escape {y : M.V} {L s : ℝ} (hLs : L < s)
    (hdist : M.S.dist 0 y = s)
    (hesc : (M.cutLaw s).real (M.escapeAt (0 : M.V) L) < 1) :
    M.cornerGap y s < 1 := by
  have hE : MeasurableSet (M.connEvent y) := M.measurableSet_connEvent y
  have hclosed : MeasurableSet (M.rawClosedEvent s(0, y) (M.connEvent y)) :=
    M.measurableSet_rawClosedEvent s(0, y) hE
  have hescM : MeasurableSet (M.escapeAt (0 : M.V) L) := M.measurableSet_escapeAt (0 : M.V) L
  have huniv : (M.cutLaw s).real (Set.univ : Set (Config M.V)) = 1 := by
    rw [Measure.real, measure_univ]; norm_num
  -- confinement implies "not connected after deleting the direct edge"
  have hsub : (M.escapeAt (0 : M.V) L)ᶜ ⊆ (M.rawClosedEvent s(0, y) (M.connEvent y))ᶜ := by
    intro ω hω
    rw [M.compl_escapeAt] at hω
    simp only [SourceModelData.rawClosedEvent, SourceModelData.connEvent, mem_compl_iff,
      mem_preimage, Set.mem_ofPred_eq]
    intro hconn
    have hsube : forceOn ({s(0, y)} : Set (Sym2 M.V)) (∅ : Config M.V) ω ⊆ ω := by
      intro e he
      rw [forceOn_empty_eq] at he
      exact he.1
    have hconnω : Connects ω (0 : M.V) y := connects_mono hsube hconn
    have hmem : y ∈ M.ball L := hω y hconnω
    have hρ : M.S.ρ (toVec y) ≤ L := hmem
    have hρ' : M.S.ρ (toVec y) = s := by
      rw [← SourceNormData.dist_zero_right M.S y, ← SourceNormData.dist_comm M.S y 0]
      exact hdist
    linarith
  have hmono : (M.cutLaw s).real ((M.escapeAt (0 : M.V) L)ᶜ)
      ≤ (M.cutLaw s).real ((M.rawClosedEvent s(0, y) (M.connEvent y))ᶜ) :=
    measureReal_mono hsub (measure_ne_top _ _)
  have hA : (M.cutLaw s).real ((M.escapeAt (0 : M.V) L)ᶜ)
      = 1 - (M.cutLaw s).real (M.escapeAt (0 : M.V) L) := by
    rw [measureReal_compl hescM, huniv]
  have hD : (M.cutLaw s).real ((M.rawClosedEvent s(0, y) (M.connEvent y))ᶜ)
      = 1 - (M.cutLaw s).real (M.rawClosedEvent s(0, y) (M.connEvent y)) := by
    rw [measureReal_compl hclosed, huniv]
  rw [M.cornerGap_eq_rawClosed]
  linarith

/-- The same in pivotal-flux form. -/
theorem directPivot_pos_of_escape {y : M.V} {L s : ℝ} (hLs : L < s)
    (hdist : M.S.dist 0 y = s)
    (hesc : (M.cutLaw s).real (M.escapeAt (0 : M.V) L) < 1) :
    0 < M.directPivot y s :=
  (M.directPivot_pos_iff y s).mpr (M.cornerGap_lt_one_of_escape hLs hdist hesc)

/-! ## 4. The flux summand of the direct edge at the corner -/

/-- Strictly below the attained radius the flux summand of the direct edge vanishes. -/
theorem m8FluxTerm_direct_eq_zero_of_lt {y : M.V} {r : ℝ} (h : r < M.S.dist 0 y) :
    M.m8FluxTerm (sMomentTrunc (fun _ => (1 : ℝ)) (0 : M.V) ({y} : Finset M.V)) r s(0, y) = 0 := by
  unfold m8FluxTerm
  rw [M.m8_cutEdgeDeriv_eq_zero_of_lt h, zero_mul]

/-- At the attained radius the flux summand of the direct edge is the derivative coefficient
times the corner pivotal flux. -/
theorem m8FluxTerm_direct_at_self {y : M.V} (hy : y ≠ (0 : M.V)) :
    M.m8FluxTerm (sMomentTrunc (fun _ => (1 : ℝ)) (0 : M.V) ({y} : Finset M.V))
        (M.S.dist 0 y) s(0, y)
      = (M.betaCrit : ℝ) * (-(deriv M.K (M.S.dist 0 y))) * M.directPivot y (M.S.dist 0 y) := by
  unfold m8FluxTerm directPivot
  rw [M.m8_cutEdgeDeriv_at_dist (x := (0 : M.V)) (y := y) (fun h => hy h.symm)]

/-- **The flux summand of the direct edge has a genuine jump at the attained radius**
whenever the corner pivotal flux and the coefficient are nonzero. -/
theorem not_continuousAt_m8FluxTerm_direct_of_pos {y : M.V} (hy : y ≠ (0 : M.V))
    (hβ : (0 : ℝ) < (M.betaCrit : ℝ))
    (hK' : deriv M.K (M.S.dist 0 y) ≠ 0)
    (hgap : 0 < M.directPivot y (M.S.dist 0 y)) :
    ¬ ContinuousAt (fun r => M.m8FluxTerm
        (sMomentTrunc (fun _ => (1 : ℝ)) (0 : M.V) ({y} : Finset M.V)) r s(0, y))
      (M.S.dist 0 y) := by
  set s : ℝ := M.S.dist 0 y with hs
  set f : ℝ → ℝ := fun r => M.m8FluxTerm
    (sMomentTrunc (fun _ => (1 : ℝ)) (0 : M.V) ({y} : Finset M.V)) r s(0, y) with hf
  intro hcont
  have hleft : Tendsto f (𝓝[<] s) (𝓝 (f s)) := hcont.tendsto.mono_left nhdsWithin_le_nhds
  have hzero : Tendsto f (𝓝[<] s) (𝓝 0) := by
    refine (tendsto_const_nhds (x := (0 : ℝ))).congr' ?_
    filter_upwards [self_mem_nhdsWithin] with r hr
    exact (M.m8FluxTerm_direct_eq_zero_of_lt (y := y) (r := r) hr).symm
  have hfs : f s = 0 := tendsto_nhds_unique hleft hzero
  have hval : f s = (M.betaCrit : ℝ) * (-(deriv M.K s)) * M.directPivot y s :=
    M.m8FluxTerm_direct_at_self hy
  have hKneg : deriv M.K s < 0 := lt_of_le_of_ne (M.deriv_K_nonpos (by
    rw [hs]; exact M.S.dist_pos (fun h => hy h.symm))) hK'
  have hpos : 0 < (M.betaCrit : ℝ) * (-(deriv M.K s)) * M.directPivot y s := by
    have h1 : 0 < -(deriv M.K s) := by linarith
    exact mul_pos (mul_pos hβ h1) hgap
  rw [hval] at hfs
  linarith

end SourceModelData

/-! ## Axiom audit -/

set_option linter.hashCommand false in
#print axioms SourceModelData.rawOpenEvent_direct
#print axioms SourceModelData.cornerGap_eq_rawClosed
#print axioms SourceModelData.directPivot_eq_one_sub_cornerGap
#print axioms SourceModelData.real_openEvent_singleton
#print axioms SourceModelData.cutProb_self_dist_eq_zero
#print axioms SourceModelData.cornerGap_eq_twoPoint_at_dist
#print axioms SourceModelData.directPivot_eq_one_sub_twoPoint
#print axioms SourceModelData.directPivot_eq_zero_iff_twoPoint_eq_one
#print axioms SourceModelData.directPivot_eq_pivotalMass
#print axioms SourceModelData.directPivot_eq_zero_iff
#print axioms SourceModelData.directPivot_nonneg
#print axioms SourceModelData.directPivot_le_one
#print axioms SourceModelData.directPivot_pos_iff
#print axioms SourceModelData.cornerGap_le_twoPoint
#print axioms SourceModelData.one_sub_twoPoint_le_directPivot
#print axioms SourceModelData.compl_escapeAt
#print axioms SourceModelData.cornerGap_lt_one_of_escape
#print axioms SourceModelData.directPivot_pos_of_escape
#print axioms SourceModelData.m8FluxTerm_direct_eq_zero_of_lt
#print axioms SourceModelData.m8FluxTerm_direct_at_self
#print axioms SourceModelData.not_continuousAt_m8FluxTerm_direct_of_pos

end PercLib.CriticalLRP.Orchestration
