/-
Copyright (c) 2026 PercLib contributors. Released under Apache 2.0.
Continuity of the cutoff two-point function in the cutoff radius.
-/
module

public import PercLib.CriticalLRP.Analysis.Cutoff.OffCorner.TwoPoint.BoxReduction

/-!
# Continuity of the cutoff two-point function

For the genuine `SourceModelData`, and for any vertex `y`, the function

  `r ↦ (M.cutLaw r).real {ω | Connects ω 0 y}`

is continuous at every positive radius `r₀` at which the first cutoff moment is finite at
some larger radius.  This is a fixed-edge pair connectivity statement: it is a genuine
infinite-volume statement, obtained by combining

* the escape reduction `conn_sdiff_boxConn_subset_escapeConf`: a connection not carried by
  the edges of the ball of radius `R` must leave that ball, and the escape probability is
  small uniformly in a right-neighbourhood of `r₀` by `tendsto_escapeConf` and monotonicity
  of the cutoff law in the radius;
* the finite-range variation bound `edgeMeasure_abs_sub_le`, applied through
  `edgeMeasure_congr_of_eq_on` to the *finite* edge set of the ball, whose `ℓ¹` variation
  tends to zero by `tendsto_sum_abs_cutProb`.

Because the single-edge cutoff profile `K s - K r` is continuous in `r` (`K_diff`), no
off-corner hypothesis is needed for continuity of the two-point function; cornerness enters
the derivative formulae, not this statement.  The only moment input is finiteness of the
first cutoff moment at a strictly larger radius, which is what makes the escape probability
controllable; it is discharged from finiteness of the second cutoff moment at that radius in
`continuousAt_cutTwoPoint_of_cutMoment`.
-/

@[expose] public section

set_option autoImplicit false
set_option linter.style.longLine false
set_option linter.hashCommand false

noncomputable section

open MeasureTheory Filter Topology Set
open scoped ENNReal NNReal Topology

namespace PercLib.CriticalLRP.Orchestration

namespace SourceModelData

variable (M : SourceModelData)

/-- **Escape probabilities are eventually small.** -/
theorem exists_escapeConf_lt {r : ℝ} (hfin : M.cutMassAt r 0 ≠ ⊤) {ε : ℝ} (hε : 0 < ε) :
    ∃ N : ℕ, ∀ n : ℕ, N ≤ n → (M.cutLaw r).real (M.escapeConf (n : ℝ)) < ε := by
  have h := M.tendsto_escapeConf hfin
  rw [Metric.tendsto_atTop] at h
  obtain ⟨N, hN⟩ := h ε hε
  refine ⟨N, fun n hn => ?_⟩
  have h' := hN n hn
  have hnn : (0 : ℝ) ≤ ((M.cutLaw r) (M.escapeConf (n : ℝ))).toReal := ENNReal.toReal_nonneg
  rwa [Real.dist_eq, sub_zero, abs_of_nonneg hnn] at h'

/-- The two-point function of the cutoff law, as a real number. -/
theorem cutTwoPoint_eq_real (r : ℝ) (y : M.V) :
    M.cutTwoPoint r (0 : M.V) y
      = (M.cutLaw r).real {ω : Config M.V | Connects ω (0 : M.V) y} :=
  rfl

/-- **Comparison of the two-point function across two radii.**  The connection probability
at `r` and at `r₀` differ by at most the `ℓ¹` variation of the edge probabilities on the box
of radius `R`, plus the two escape probabilities. -/
theorem cutTwoPoint_abs_sub_le (r r0 R : ℝ) (y : M.V) :
    |M.cutTwoPoint r (0 : M.V) y - M.cutTwoPoint r0 (0 : M.V) y|
      ≤ (∑ e ∈ M.boxEdges R, |(M.cutProb r e : ℝ) - (M.cutProb r0 e : ℝ)|)
        + (M.cutLaw r).real (M.escapeConf R)
        + (M.cutLaw r0).real (M.escapeConf R) := by
  have hbox : MeasurableSet (M.boxConn (M.boxEdges R) y) := M.measurableSet_boxConn _ y
  have hsub : {ω : Config M.V | Connects ω (0 : M.V) y}
      ⊆ M.boxConn (M.boxEdges R) y ∪ M.escapeConf R := by
    intro ω hω
    by_cases hb : ω ∈ M.boxConn (M.boxEdges R) y
    · exact Or.inl hb
    · exact Or.inr (M.conn_sdiff_boxConn_subset_escapeConf R y ⟨hω, hb⟩)
  have hboxsub : M.boxConn (M.boxEdges R) y
      ⊆ {ω : Config M.V | Connects ω (0 : M.V) y} := M.boxConn_subset_conn _ y
  -- the hybrid profile: `cutProb r` on the box, `cutProb r0` outside
  set q : Sym2 M.V → unitInterval :=
    fun e => if e ∈ M.boxEdges R then M.cutProb r e else M.cutProb r0 e with hq
  have hqD : ∀ e ∈ M.boxEdges R, M.cutProb r e = q e := by
    intro e he
    change M.cutProb r e
      = (if e ∈ M.boxEdges R then M.cutProb r e else M.cutProb r0 e)
    rw [ite_eq_left he]
  have hq_out : ∀ e, q e ≠ M.cutProb r0 e → e ∈ M.boxEdges R := by
    intro e he
    by_contra hmem
    apply he
    change (if e ∈ M.boxEdges R then M.cutProb r e else M.cutProb r0 e) = M.cutProb r0 e
    rw [ite_eq_right hmem]
  have hdet : ∀ ω ω' : Config M.V, (∀ e ∈ M.boxEdges R, ω e = ω' e) →
      (ω ∈ M.boxConn (M.boxEdges R) y ↔ ω' ∈ M.boxConn (M.boxEdges R) y) :=
    fun _ _ h => M.boxConn_congr _ y h
  have hcongr₁ : (edgeMeasure (M.cutProb r)) (M.boxConn (M.boxEdges R) y)
      = (edgeMeasure q) (M.boxConn (M.boxEdges R) y) :=
    edgeMeasure_congr_of_eq_on (p := M.cutProb r) (q := q) (M.boxEdges R) hqD hbox hdet
  have hsum_eq : (∑ e ∈ M.boxEdges R, |(q e : ℝ) - (M.cutProb r0 e : ℝ)|)
      = ∑ e ∈ M.boxEdges R, |(M.cutProb r e : ℝ) - (M.cutProb r0 e : ℝ)| := by
    refine Finset.sum_congr rfl fun e he => ?_
    rw [hqD e he]
  have hTV : |(M.cutLaw r).real (M.boxConn (M.boxEdges R) y)
      - (M.cutLaw r0).real (M.boxConn (M.boxEdges R) y)|
      ≤ ∑ e ∈ M.boxEdges R, |(M.cutProb r e : ℝ) - (M.cutProb r0 e : ℝ)| := by
    rw [measureReal_def, measureReal_def,
      show M.cutLaw r = edgeMeasure (M.cutProb r) from rfl,
      show M.cutLaw r0 = edgeMeasure (M.cutProb r0) from rfl]
    have hraw := edgeMeasure_abs_sub_le q (M.cutProb r0) (M.boxEdges R) hq_out
      (M.boxConn (M.boxEdges R) y) hbox
    rw [hsum_eq] at hraw
    rw [← hcongr₁] at hraw
    exact hraw
  have h1 : M.cutTwoPoint r (0 : M.V) y
      ≤ (M.cutLaw r).real (M.boxConn (M.boxEdges R) y)
        + (M.cutLaw r).real (M.escapeConf R) := by
    rw [M.cutTwoPoint_eq_real]
    calc (M.cutLaw r).real {ω : Config M.V | Connects ω (0 : M.V) y}
        ≤ (M.cutLaw r).real (M.boxConn (M.boxEdges R) y ∪ M.escapeConf R) :=
          measureReal_mono hsub
      _ ≤ _ + _ := measureReal_union_le _ _
  have h2 : M.cutTwoPoint r0 (0 : M.V) y
      ≤ (M.cutLaw r0).real (M.boxConn (M.boxEdges R) y)
        + (M.cutLaw r0).real (M.escapeConf R) := by
    rw [M.cutTwoPoint_eq_real]
    calc (M.cutLaw r0).real {ω : Config M.V | Connects ω (0 : M.V) y}
        ≤ (M.cutLaw r0).real (M.boxConn (M.boxEdges R) y ∪ M.escapeConf R) :=
          measureReal_mono hsub
      _ ≤ _ + _ := measureReal_union_le _ _
  have hA : (M.cutLaw r).real (M.boxConn (M.boxEdges R) y)
      ≤ (M.cutLaw r0).real (M.boxConn (M.boxEdges R) y)
        + ∑ e ∈ M.boxEdges R, |(M.cutProb r e : ℝ) - (M.cutProb r0 e : ℝ)| := by
    have hle := (abs_le.mp hTV).2
    linarith
  have hB : (M.cutLaw r0).real (M.boxConn (M.boxEdges R) y)
      ≤ (M.cutLaw r).real (M.boxConn (M.boxEdges R) y)
        + ∑ e ∈ M.boxEdges R, |(M.cutProb r e : ℝ) - (M.cutProb r0 e : ℝ)| := by
    have hle := (abs_le.mp hTV).1
    linarith
  have hmono : (M.cutLaw r0).real (M.boxConn (M.boxEdges R) y)
      ≤ M.cutTwoPoint r0 (0 : M.V) y := by
    rw [M.cutTwoPoint_eq_real]
    exact measureReal_mono hboxsub
  have hmono_r : (M.cutLaw r).real (M.boxConn (M.boxEdges R) y)
      ≤ M.cutTwoPoint r (0 : M.V) y := by
    rw [M.cutTwoPoint_eq_real]
    exact measureReal_mono hboxsub
  rw [abs_le]
  constructor <;> linarith

/-- **Continuity of the cutoff two-point function in the cutoff radius.**  The hypothesis is
finiteness of the first cutoff moment at one radius strictly larger than `r₀`. -/
theorem continuousAt_cutTwoPoint {r0 r1 : ℝ} (hr0 : 0 < r0) (hr01 : r0 < r1)
    (hfin : M.cutMassAt r1 0 ≠ ⊤) (y : M.V) :
    ContinuousAt (fun r : ℝ => M.cutTwoPoint r (0 : M.V) y) r0 := by
  refine Metric.tendsto_nhds.mpr ?_
  intro ε hε
  obtain ⟨N, hN⟩ := M.exists_escapeConf_lt (r := r1) hfin (ε := ε / 4) (by linarith)
  have hevbox : ∀ᶠ r : ℝ in 𝓝 r0,
      (∑ e ∈ M.boxEdges (N : ℝ), |(M.cutProb r e : ℝ) - (M.cutProb r0 e : ℝ)|) < ε / 4 :=
    (M.tendsto_sum_abs_cutProb hr0 (M.boxEdges (N : ℝ))).eventually
      (Iio_mem_nhds (by linarith))
  have hevpos : ∀ᶠ r : ℝ in 𝓝 r0, 0 < r ∧ r ≤ r1 := by
    have h1 : ∀ᶠ r : ℝ in 𝓝 r0, 0 < r := isOpen_Ioi.eventually_mem hr0
    have h2 : ∀ᶠ r : ℝ in 𝓝 r0, r < r1 := isOpen_Iio.eventually_mem hr01
    exact h1.and (h2.mono fun r h => le_of_lt h)
  filter_upwards [hevbox, hevpos] with r hbox hpos
  have hesc1 : (M.cutLaw r).real (M.escapeConf (N : ℝ)) ≤ ε / 4 :=
    le_trans (M.escapeConf_real_mono hpos.1 (hr0.trans hr01) hpos.2) (le_of_lt (hN N le_rfl))
  have hesc0 : (M.cutLaw r0).real (M.escapeConf (N : ℝ)) ≤ ε / 4 :=
    le_trans (M.escapeConf_real_mono hr0 (hr0.trans hr01) hr01.le) (le_of_lt (hN N le_rfl))
  have hmain := M.cutTwoPoint_abs_sub_le r r0 (N : ℝ) y
  rw [Real.dist_eq]
  refine lt_of_le_of_lt hmain ?_
  linarith

/-- **Continuity of the cutoff two-point function from finiteness of the second cutoff
moment at a strictly larger radius.** -/
theorem continuousAt_cutTwoPoint_of_cutMoment {r0 : ℝ} (hr0 : 0 < r0) {β : ℝ} (hr0β : r0 < β)
    (h2 : M.cutMoment 2 β ≠ ⊤) (y : M.V) :
    ContinuousAt (fun r : ℝ => M.cutTwoPoint r (0 : M.V) y) r0 := by
  have h12 : M.cutMoment 1 β ≤ M.cutMoment 2 β := by
    refine lintegral_mono fun ω => ?_
    rw [pow_one, pow_two]
    calc PercLib.CriticalLRP.clusterVol ω (0 : M.V)
        = PercLib.CriticalLRP.clusterVol ω 0 * 1 := (mul_one _).symm
      _ ≤ PercLib.CriticalLRP.clusterVol ω 0 * PercLib.CriticalLRP.clusterVol ω 0 := by
        gcongr
        exact one_le_clusterVol ω (0 : M.V)
  have hfin : M.cutMassAt β 0 ≠ ⊤ := by
    rw [M.cutMassAt_zero_eq_cutMoment]
    exact ne_top_of_le_ne_top h2 h12
  exact M.continuousAt_cutTwoPoint hr0 hr0β hfin y

/-- **Continuity of the fixed-pair cutoff connectivity probability**, stated directly as the
`cutLaw`-probability of the connection event. -/
theorem continuousAt_cutLaw_conn {r0 r1 : ℝ} (hr0 : 0 < r0) (hr01 : r0 < r1)
    (hfin : M.cutMassAt r1 0 ≠ ⊤) (y : M.V) :
    ContinuousAt (fun r : ℝ => (M.cutLaw r).real {ω : Config M.V | Connects ω (0 : M.V) y}) r0 :=
  M.continuousAt_cutTwoPoint hr0 hr01 hfin y

/-- The same statement at an off-corner radius, in the vocabulary of the landed off-corner
interface.  No off-corner hypothesis is actually needed for continuity of the two-point
function; this form only records the compatibility. -/
theorem continuousAt_cutLaw_conn_offCorner {r0 r1 : ℝ} (hr0 : 0 < r0) (hr01 : r0 < r1)
    (_hcorn : r0 ∉ M.cornerRadii) (hfin : M.cutMassAt r1 0 ≠ ⊤) (y : M.V) :
    ContinuousAt (fun r : ℝ => (M.cutLaw r).real {ω : Config M.V | Connects ω (0 : M.V) y}) r0 :=
  M.continuousAt_cutLaw_conn hr0 hr01 hfin y

/-- The left limit of the cutoff connectivity probability at a positive radius. -/
theorem tendsto_cutLaw_conn_nhdsLT {r0 r1 : ℝ} (hr0 : 0 < r0) (hr01 : r0 < r1)
    (hfin : M.cutMassAt r1 0 ≠ ⊤) (y : M.V) :
    Tendsto (fun r : ℝ => (M.cutLaw r).real {ω : Config M.V | Connects ω (0 : M.V) y})
      (𝓝[<] r0) (𝓝 ((M.cutLaw r0).real {ω : Config M.V | Connects ω (0 : M.V) y})) :=
  (M.continuousAt_cutLaw_conn hr0 hr01 hfin y).tendsto.mono_left inf_le_left

/-- The right limit of the cutoff connectivity probability at a positive radius. -/
theorem tendsto_cutLaw_conn_nhdsGT {r0 r1 : ℝ} (hr0 : 0 < r0) (hr01 : r0 < r1)
    (hfin : M.cutMassAt r1 0 ≠ ⊤) (y : M.V) :
    Tendsto (fun r : ℝ => (M.cutLaw r).real {ω : Config M.V | Connects ω (0 : M.V) y})
      (𝓝[>] r0) (𝓝 ((M.cutLaw r0).real {ω : Config M.V | Connects ω (0 : M.V) y})) :=
  (M.continuousAt_cutLaw_conn hr0 hr01 hfin y).tendsto.mono_left inf_le_left

/-- The two-sided continuity in the `cutMoment 2` discharge form. -/
theorem continuousAt_cutLaw_conn_of_cutMoment {r0 : ℝ} (hr0 : 0 < r0) {β : ℝ} (hr0β : r0 < β)
    (h2 : M.cutMoment 2 β ≠ ⊤) (y : M.V) :
    ContinuousAt (fun r : ℝ => (M.cutLaw r).real {ω : Config M.V | Connects ω (0 : M.V) y}) r0 :=
  M.continuousAt_cutTwoPoint_of_cutMoment hr0 hr0β h2 y

end SourceModelData

end PercLib.CriticalLRP.Orchestration

open PercLib.CriticalLRP.Orchestration

#print axioms PercLib.CriticalLRP.edgeMeasure_abs_sub_le
#print axioms SourceModelData.measurableSet_boxConn
#print axioms SourceModelData.conn_sdiff_boxConn_subset_escapeConf
#print axioms SourceModelData.cutTwoPoint_abs_sub_le
#print axioms SourceModelData.continuousAt_cutTwoPoint
#print axioms SourceModelData.continuousAt_cutTwoPoint_of_cutMoment
#print axioms SourceModelData.continuousAt_cutLaw_conn
#print axioms SourceModelData.tendsto_cutLaw_conn_nhdsLT
#print axioms SourceModelData.tendsto_cutLaw_conn_nhdsGT
