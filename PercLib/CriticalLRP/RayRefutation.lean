/-
Copyright (c) 2026 PercLib contributors. Released under Apache 2.0.
-/
/-
Swarm smwpgngy4, member m2, direction d3 (the first-moment input of §I.4.1).

Hutchcroft, *Critical long-range percolation I: High effective dimension*,
arXiv:2508.18807v1, §I.4.1, source gap `I.4.g3`
(`.scratch/source/paper.html#S4.SS1.p6.1@L2219-L2219`):

  `𝔼_{β_c}|K| = ∞` and `𝔼_{β,r}|K| < ∞` for `β < β_c`.

This file contains three things.

1. **A refutation.**  The second half of that gap ("below `β_c` the first moment is
   finite") is not a consequence of subcriticality, i.e. of `θ_β = 0`, in the framework the
   library uses for `longRangeMeasure`.  The explicit intensity
   `J s(i,i+1) = log (i+2)`, `J = 0` on all other edges of `Sym2 ℕ`, has
   `infiniteClusterProb = 0` and `percolationFunction = 0` at every vertex at `β = 1`, while the
   expected cluster volume of the root is `⊤`; and the same model percolates a.s. at `β = 2`, so
   `1 ≤ criticalBeta J hJ`.  See `exists_subcritical_infinite_mean`.

   Since the example is deliberately *not* translation invariant, it does not contradict the
   paper; it shows that the missing input has to come from the translation-invariant power-law
   geometry and genuine sharpness of the phase transition, not from `β ≤ β_c`.

2. **The transfer that is valid.**  `θ > 0` forces an infinite first moment, and a finite first
   moment forces `θ = 0`; consequently the finite-mean set is contained in `[0, β_c]`
   (`le_criticalBeta_of_forall_lintegral_ne_top`).  This is the only half of the dichotomy that the
   framework supplies.

3. **A warning about the committed analytic cores.**  The `hinf` hypothesis of
   `VolumeMoments.FirstMoment.first_moment_liminf_lower_bound_critical` (the analytic core of
   Corollary I.4.8) is *equivalent* to the critical clause of `I.4.g3`
   (`tendsto_cutoffMean_nhds_top_iff_uncut_eq_top`), so that core consumes `I.4.g3` rather than
   supplying it.

No `sorry`, no `admit`, no `native_decide`, no custom axioms; `#print axioms` on every main
theorem below gives only `propext`, `Classical.choice`, `Quot.sound`.  This module is proof-only:
it introduces no meaning-carrying definition for the paper's model (the local `rayEdge`,
`rayProfile`, `rayCyl`, `rayShiftCyl` are the counterexample object itself).
-/
module

public import PercLib.CriticalLRP.CountableProduct.Marks
public import PercLib.CriticalLRP.CountableProduct.Critical
public import PercLib.CriticalLRP.CutoffLimit

set_option autoImplicit false

open MeasureTheory Measure Filter
open scoped ENNReal Topology

@[expose] public section

namespace PercLib.CriticalLRP.RayRefutation

attribute [local instance] Classical.propDecidable

/-- The `i`-th edge of the one-dimensional ray `0 — 1 — 2 — ⋯` on `ℕ`. -/
def rayEdge (i : ℕ) : Sym2 ℕ := s(i, i + 1)

theorem rayEdge_injective : Function.Injective rayEdge := by
  intro i j h
  rw [rayEdge, rayEdge, Sym2.eq_iff] at h
  rcases h with ⟨h1, h2⟩ | ⟨h1, h2⟩
  · exact h1
  · omega

/-- The intensity of the ray: `log (i+2)` on the `i`-th ray edge, `0` elsewhere. -/
noncomputable def rayProfile : Sym2 ℕ → ℝ :=
  fun e => if h : ∃ i, e = rayEdge i then Real.log ((Nat.find h : ℝ) + 2) else 0

theorem rayProfile_rayEdge (i : ℕ) : rayProfile (rayEdge i) = Real.log ((i : ℝ) + 2) := by
  rw [rayProfile]
  split
  · rename_i h
    rw [show Nat.find h = i from rayEdge_injective (Nat.find_spec h).symm]
  · rename_i h
    exact absurd ⟨i, rfl⟩ h

theorem rayProfile_of_notMem {e : Sym2 ℕ} (h : ∀ i, e ≠ rayEdge i) : rayProfile e = 0 := by
  rw [rayProfile]
  split
  · rename_i hh
    obtain ⟨i, hi⟩ := hh
    exact absurd hi (h i)
  · rfl

theorem rayProfile_nonneg (e : Sym2 ℕ) : 0 ≤ rayProfile e := by
  rw [rayProfile]
  split
  · rename_i h
    have : (0 : ℝ) ≤ (Nat.find h : ℝ) := Nat.cast_nonneg _
    have : (0 : ℝ) < (Nat.find h : ℝ) + 2 := by linarith
    exact Real.log_nonneg (by linarith)
  · exact le_refl 0

/-- The edge-open probability of the ray at `β = 1`: `(i+1)/(i+2)` on the `i`-th ray
edge. -/
theorem bernoulliEdgeProb_rayEdge (i : ℕ) :
    ((bernoulliEdgeProb rayProfile rayProfile_nonneg 1 (rayEdge i) : unitInterval) : ℝ)
      = ((i : ℝ) + 1) / ((i : ℝ) + 2) := by
  rw [bernoulliEdgeProb_coe, rayProfile_rayEdge]
  have hpos : (0 : ℝ) < (i : ℝ) + 2 := by positivity
  rw [show (1 : NNReal) * _ = Real.log ((i : ℝ) + 2) by
    rw [NNReal.coe_one, one_mul]]
  rw [Real.exp_neg, Real.exp_log hpos]
  have hne : ((i : ℝ) + 2) ≠ 0 := ne_of_gt hpos
  field_simp
  ring


/-! ## The edge law of the ray and its finite cylinders -/

/-- The edge probabilities of the ray intensity at `β = 1`. -/
noncomputable abbrev rayPi : Sym2 ℕ → unitInterval :=
  bernoulliEdgeProb rayProfile rayProfile_nonneg 1

/-- The law `P_1` of the ray intensity. -/
noncomputable abbrev rayMu : Measure (Config ℕ) :=
  longRangeMeasure rayProfile rayProfile_nonneg 1

theorem rayMu_eq_edgeMeasure : rayMu = edgeMeasure rayPi := rfl

/-- The event that the first `n` edges of the ray are open. -/
def rayCyl (n : ℕ) : Set (Config ℕ) := {ω | ∀ i ∈ Finset.range n, rayEdge i ∈ ω}

theorem rayCyl_eq_allOpen (n : ℕ) :
    rayCyl n = {ω : Config ℕ | ∀ e ∈ (Finset.range n).image rayEdge, e ∈ ω} := by
  ext ω
  constructor
  · rintro h e he
    obtain ⟨i, hi, rfl⟩ := Finset.mem_image.1 he
    exact h i hi
  · intro h i hi
    exact h (rayEdge i) (Finset.mem_image.2 ⟨i, hi, rfl⟩)

theorem measurableSet_rayCyl (n : ℕ) : MeasurableSet (rayCyl n) := by
  rw [rayCyl_eq_allOpen]
  exact measurableSet_allOpen _

theorem rayEdge_mem_range_inj {n : ℕ} : Set.InjOn rayEdge ↑(Finset.range n) :=
  fun _ _ _ _ h => rayEdge_injective h

theorem toNNReal_rayPi_rayEdge (i : ℕ) :
    (unitInterval.toNNReal (rayPi (rayEdge i)) : ℝ≥0∞)
      = ENNReal.ofReal (((i : ℝ) + 1) / ((i : ℝ) + 2)) := by
  rw [← ENNReal.ofReal_coe_nnreal]
  congr 1
  rw [unitInterval.coe_toNNReal, bernoulliEdgeProb_rayEdge]

theorem real_prod_rayRatios (n : ℕ) :
    ∏ i ∈ Finset.range n, (((i : ℝ) + 1) / ((i : ℝ) + 2)) = 1 / ((n : ℝ) + 1) := by
  induction n with
  | zero => simp
  | succ n ih =>
    rw [Finset.prod_range_succ, ih]
    have h1 : (0 : ℝ) < (n : ℝ) + 1 := by positivity
    have h2 : (0 : ℝ) < (n : ℝ) + 2 := by positivity
    field_simp
    push_cast
    ring

theorem measure_rayCyl (n : ℕ) : rayMu (rayCyl n) = ENNReal.ofReal (1 / ((n : ℝ) + 1)) := by
  rw [rayMu_eq_edgeMeasure, rayCyl_eq_allOpen, edgeMeasure_cylinder,
    Finset.prod_image rayEdge_mem_range_inj]
  have hprod : (∏ i ∈ Finset.range n, (unitInterval.toNNReal (rayPi (rayEdge i)) : ℝ≥0∞))
      = ∏ i ∈ Finset.range n, ENNReal.ofReal (((i : ℝ) + 1) / ((i : ℝ) + 2)) :=
    Finset.prod_congr rfl (fun i _ => toNNReal_rayPi_rayEdge i)
  rw [hprod, ← ENNReal.ofReal_prod_of_nonneg (fun i _ => by positivity), real_prod_rayRatios]

/-! ## The root's cluster blows up in mean -/

theorem connects_of_rayCyl {ω : Config ℕ} {n : ℕ} (h : ω ∈ rayCyl n) : Connects ω 0 n := by
  induction n with
  | zero => exact SimpleGraph.Reachable.refl 0
  | succ n ih =>
    have h1 : ω ∈ rayCyl n := fun i hi => h i (Finset.mem_range.2 (Nat.lt_succ_of_lt (Finset.mem_range.1 hi)))
    have hadj : (openGraph ω).Adj n (n + 1) := by
      rw [openGraph_adj]
      exact ⟨Nat.ne_of_lt (Nat.lt_succ_self n), h n (Finset.mem_range.2 (Nat.lt_succ_self n))⟩
    exact SimpleGraph.Reachable.trans (ih h1) (SimpleGraph.Adj.reachable hadj)

theorem tau_ge_rayCyl (n : ℕ) :
    ENNReal.ofReal (1 / ((n : ℝ) + 1)) ≤ PercLib.Percolation.Bond.tau rayPi 0 n := by
  have hsub : rayCyl n ⊆ PercLib.Percolation.Bond.conn (V := ℕ) 0 n := by
    intro ω hω
    exact connects_of_rayCyl hω
  calc ENNReal.ofReal (1 / ((n : ℝ) + 1))
      = rayMu (rayCyl n) := (measure_rayCyl n).symm
    _ ≤ rayMu (PercLib.Percolation.Bond.conn (V := ℕ) 0 n) := measure_mono hsub
    _ = PercLib.Percolation.Bond.tau rayPi 0 n := rfl

/-- `x = ⊤` as soon as `x` dominates every natural number. -/
theorem eq_top_of_forall_nat_le {x : ℝ≥0∞} (h : ∀ n : ℕ, (n : ℝ≥0∞) ≤ x) : x = ⊤ := by
  by_contra hx
  obtain ⟨n, hn⟩ := exists_nat_gt x.toReal
  have h1 : ((n : ℝ≥0∞)).toReal ≤ x.toReal := ENNReal.toReal_mono hx (h n)
  simp only [ENNReal.toReal_natCast] at h1
  linarith

/-- The harmonic series diverges in `ℝ≥0∞`. -/
theorem tsum_one_div_eq_top :
    (∑' n : ℕ, ENNReal.ofReal (1 / ((n : ℝ) + 1))) = ⊤ := by
  refine eq_top_of_forall_nat_le fun k => ?_
  -- a finite partial sum that dominates `k`
  obtain ⟨N, hN⟩ : ∃ N : ℕ, (k : ℝ) ≤ ∑ i ∈ Finset.range N, (1 / ((i : ℝ) + 1)) := by
    refine ⟨⌊Real.exp ((k : ℝ) + 1)⌋₊, ?_⟩
    have h1 : Real.log (Real.exp ((k : ℝ) + 1)) ≤ ((harmonic ⌊Real.exp ((k : ℝ) + 1)⌋₊ : ℚ) : ℝ) :=
      log_le_harmonic_floor _ (le_of_lt (Real.exp_pos _))
    rw [Real.log_exp] at h1
    have h2 : ((harmonic ⌊Real.exp ((k : ℝ) + 1)⌋₊ : ℚ) : ℝ)
        = ∑ i ∈ Finset.range ⌊Real.exp ((k : ℝ) + 1)⌋₊, (1 / ((i : ℝ) + 1)) := by
      rw [harmonic, Rat.cast_sum]
      simp [one_div]
    rw [h2] at h1
    linarith
  have hstep1 : (k : ℝ≥0∞) ≤ ENNReal.ofReal (∑ i ∈ Finset.range N, (1 / ((i : ℝ) + 1))) := by
    rw [← ENNReal.ofReal_natCast]
    exact ENNReal.ofReal_le_ofReal hN
  have hstep2 : ENNReal.ofReal (∑ i ∈ Finset.range N, (1 / ((i : ℝ) + 1)))
      = ∑ i ∈ Finset.range N, ENNReal.ofReal (1 / ((i : ℝ) + 1)) :=
    ENNReal.ofReal_sum_of_nonneg (fun i _ => by positivity)
  rw [hstep2] at hstep1
  exact le_trans hstep1 (ENNReal.sum_le_tsum (Finset.range N))

/-- **Infinite mean for the ray at `β = 1`.** -/
theorem ray_chi_eq_top : PercLib.Percolation.Bond.chi rayPi 0 = ⊤ := by
  rw [PercLib.Percolation.Bond.chi_eq_tsum_tau]
  refine eq_top_of_forall_nat_le fun k => ?_
  have h1 : (∑' n : ℕ, ENNReal.ofReal (1 / ((n : ℝ) + 1))) ≤
      ∑' n : ℕ, PercLib.Percolation.Bond.tau rayPi 0 n :=
    ENNReal.tsum_le_tsum fun n => tau_ge_rayCyl n
  rw [tsum_one_div_eq_top] at h1
  exact le_trans le_top h1

theorem ray_lintegral_clusterVol_eq_top :
    ∫⁻ ω, clusterVol ω 0 ∂(longRangeMeasure rayProfile rayProfile_nonneg 1) = ⊤ :=
  ray_chi_eq_top


/-! ## Almost every configuration has no infinite cluster at the root -/

theorem rayProfile_ne_zero_iff (e : Sym2 ℕ) : rayProfile e ≠ 0 ↔ ∃ i, e = rayEdge i := by
  constructor
  · intro h
    by_contra hc
    exact h (rayProfile_of_notMem fun i hi => hc ⟨i, hi⟩)
  · rintro ⟨i, rfl⟩ h
    have hpos : 0 < Real.log ((i : ℝ) + 2) := Real.log_pos (by
      have hi : (0 : ℝ) ≤ (i : ℝ) := Nat.cast_nonneg i
      linarith)
    rw [rayProfile_rayEdge] at h
    linarith

/-- A single edge of intensity zero is closed almost surely. -/
theorem ae_edge_closed_of_profile_zero {e : Sym2 ℕ} (he : rayProfile e = 0) :
    ∀ᵐ ω ∂rayMu, e ∉ ω := by
  have hsingle : ({ω : Config ℕ | e ∈ ω}) = {ω : Config ℕ | ∀ e' ∈ ({e} : Finset (Sym2 ℕ)), e' ∈ ω} := by
    ext ω; simp
  have hzero : rayPi e = 0 := by
    apply Subtype.ext
    rw [bernoulliEdgeProb_coe, he]
    simp
  have hmeasure : rayMu {ω : Config ℕ | e ∈ ω} = 0 := by
    rw [rayMu_eq_edgeMeasure, hsingle, edgeMeasure_cylinder]
    simp [hzero]
  exact (measure_eq_zero_iff_ae_notMem).1 hmeasure

/-- Almost every configuration is supported on the ray. -/
theorem ae_ray_only :
    ∀ᵐ ω ∂rayMu, ∀ e : Sym2 ℕ, rayProfile e = 0 → e ∉ ω := by
  rw [MeasureTheory.ae_all_iff]
  intro e
  by_cases he : rayProfile e = 0
  · simpa [he] using ae_edge_closed_of_profile_zero he
  · filter_upwards with ω
    exact fun h => absurd h he

/-! ## The ray has bounded degree

A reader could object that the ray intensity is not a power law.  The point of the next lemma is
that the counterexample is not "mean-field-like" in the only respect that could matter here: the
expected number of open edges at any vertex is at most `2`.  So even *bounded degree* (the strongest
regularity a finite-range model has) does not turn "no infinite cluster" into "finite first moment".
-/

theorem rayProfile_ne_zero_of_rayPi_ne_zero {e : Sym2 ℕ} (h : rayPi e ≠ 0) :
    rayProfile e ≠ 0 := by
  intro hJ
  exact h (Subtype.ext (by rw [bernoulliEdgeProb_coe, hJ]; simp))

theorem rayEdge_endpoints {v x i : ℕ} (h : s(v, x) = rayEdge i) :
    (v = i ∧ x = i + 1) ∨ (v = i + 1 ∧ x = i) := by
  rw [rayEdge, Sym2.eq_iff] at h
  exact h

theorem rayPi_ne_zero_imp {v x : ℕ} (h : rayPi (s(v, x)) ≠ 0) :
    x = v + 1 ∨ x = v - 1 := by
  obtain ⟨i, hi⟩ := (rayProfile_ne_zero_iff _).1 (rayProfile_ne_zero_of_rayPi_ne_zero h)
  rcases rayEdge_endpoints hi with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
  · exact Or.inl rfl
  · exact Or.inr (by omega)

/-- Every vertex has at most two potentially open incident edges, so the expected degree of the ray
is at most `2`. -/
theorem ray_expectedDegree_le_two (v : ℕ) :
    ∑' x : ℕ, (unitInterval.toNNReal (rayPi (s(v, x))) : ℝ≥0∞) ≤ 2 := by
  have hterm : ∀ x : ℕ, (unitInterval.toNNReal (rayPi (s(v, x))) : ℝ≥0∞)
      ≤ (if x = v + 1 then (1 : ℝ≥0∞) else 0) + (if x = v - 1 then (1 : ℝ≥0∞) else 0) := by
    intro x
    by_cases hx : rayPi (s(v, x)) = 0
    · have hzero : (unitInterval.toNNReal (rayPi (s(v, x))) : ℝ≥0∞) = 0 := by
        rw [hx]
        simp
      rw [hzero]
      exact zero_le
    · have hle : (unitInterval.toNNReal (rayPi (s(v, x))) : ℝ≥0∞) ≤ 1 := by
        rw [← ENNReal.ofReal_coe_nnreal, ENNReal.ofReal_le_one]
        rw [unitInterval.coe_toNNReal]
        exact (rayPi (s(v, x))).2.2
      rcases rayPi_ne_zero_imp hx with h | h
      · subst h
        have hne : ¬ (v + 1 = v - 1) := by omega
        simpa [hne] using hle
      · subst h
        have hne : ¬ (v - 1 = v + 1) := by omega
        simpa [hne] using hle
  calc ∑' x : ℕ, (unitInterval.toNNReal (rayPi (s(v, x))) : ℝ≥0∞)
      ≤ ∑' x : ℕ, ((if x = v + 1 then (1 : ℝ≥0∞) else 0)
          + (if x = v - 1 then (1 : ℝ≥0∞) else 0)) := ENNReal.tsum_le_tsum hterm
    _ = (∑' x : ℕ, (if x = v + 1 then (1 : ℝ≥0∞) else 0))
          + ∑' x : ℕ, (if x = v - 1 then (1 : ℝ≥0∞) else 0) := ENNReal.tsum_add
    _ = 2 := by
      have h1 : (∑' x : ℕ, (if x = v + 1 then (1 : ℝ≥0∞) else 0)) = 1 := by
        rw [tsum_eq_single (v + 1)] <;> simp
      have h2 : (∑' x : ℕ, (if x = v - 1 then (1 : ℝ≥0∞) else 0)) = 1 := by
        rw [tsum_eq_single (v - 1)] <;> simp
      rw [h1, h2]
      norm_num

/-! ## Missing ray edges arbitrarily far out -/

/-- The event that the ray edges with indices `M, M+1, …, M+N-1` are open. -/
def rayShiftCyl (M N : ℕ) : Set (Config ℕ) :=
  {ω | ∀ i ∈ Finset.range N, rayEdge (M + i) ∈ ω}

theorem rayShiftCyl_eq_allOpen (M N : ℕ) :
    rayShiftCyl M N
      = {ω : Config ℕ | ∀ e ∈ (Finset.range N).image (fun i => rayEdge (M + i)), e ∈ ω} := by
  ext ω
  constructor
  · rintro h e he
    obtain ⟨i, hi, rfl⟩ := Finset.mem_image.1 he
    exact h i hi
  · intro h i hi
    exact h (rayEdge (M + i)) (Finset.mem_image.2 ⟨i, hi, rfl⟩)

theorem measurableSet_rayShiftCyl (M N : ℕ) : MeasurableSet (rayShiftCyl M N) := by
  rw [rayShiftCyl_eq_allOpen]
  exact measurableSet_allOpen _

theorem real_prod_shift (M N : ℕ) :
    ∏ i ∈ Finset.range N, (((M : ℝ) + (i : ℝ) + 1) / ((M : ℝ) + (i : ℝ) + 2))
      = ((M : ℝ) + 1) / ((M : ℝ) + (N : ℝ) + 1) := by
  induction N with
  | zero =>
    have : (0 : ℝ) < (M : ℝ) + 1 := by positivity
    simp [this.ne']
  | succ N ih =>
    rw [Finset.prod_range_succ, ih]
    push_cast
    have h1 : (0 : ℝ) < (M : ℝ) + (N : ℝ) + 1 := by positivity
    have h2 : (0 : ℝ) < (M : ℝ) + (N : ℝ) + 2 := by positivity
    field_simp
    ring

theorem measure_rayShiftCyl (M N : ℕ) :
    rayMu (rayShiftCyl M N)
      = ENNReal.ofReal (((M : ℝ) + 1) / ((M : ℝ) + (N : ℝ) + 1)) := by
  have hinj : Set.InjOn (fun i => rayEdge (M + i)) ↑(Finset.range N) := by
    intro a _ b _ hab
    have := rayEdge_injective hab
    omega
  rw [rayShiftCyl_eq_allOpen, rayMu_eq_edgeMeasure, edgeMeasure_cylinder,
    Finset.prod_image hinj]
  have hprod : (∏ i ∈ Finset.range N,
        (unitInterval.toNNReal (rayPi (rayEdge (M + i))) : ℝ≥0∞))
      = ∏ i ∈ Finset.range N, ENNReal.ofReal (((M : ℝ) + (i : ℝ) + 1) / ((M : ℝ) + (i : ℝ) + 2)) := by
    refine Finset.prod_congr rfl fun i _ => ?_
    rw [toNNReal_rayPi_rayEdge]
    push_cast
    rfl
  rw [hprod, ← ENNReal.ofReal_prod_of_nonneg (fun i _ => by positivity), real_prod_shift]

theorem tendsto_measure_rayShiftCyl (M : ℕ) :
    Tendsto (fun N : ℕ => rayMu (rayShiftCyl M N)) atTop (𝓝 0) := by
  have hreal : Tendsto (fun N : ℕ => ((M : ℝ) + 1) / ((M : ℝ) + (N : ℝ) + 1)) atTop (𝓝 0) := by
    have hden : Tendsto (fun N : ℕ => (M : ℝ) + (N : ℝ) + 1) atTop atTop := by
      have h1 : Tendsto (fun N : ℕ => (N : ℝ) + ((M : ℝ) + 1)) atTop atTop :=
        tendsto_natCast_atTop_atTop.atTop_add tendsto_const_nhds
      refine h1.congr' ?_
      filter_upwards with N
      ring
    simpa using hden.const_div_atTop ((M : ℝ) + 1)
  have := ENNReal.tendsto_ofReal hreal
  simpa [measure_rayShiftCyl, ENNReal.ofReal_zero] using this

theorem mem_iInter_rayShiftCyl_iff (ω : Config ℕ) (M : ℕ) :
    ω ∈ (⋂ N : ℕ, rayShiftCyl M N) ↔ ∀ j : ℕ, rayEdge (M + j) ∈ ω := by
  rw [Set.mem_iInter]
  exact ⟨fun h j => h (j + 1) j (Finset.mem_range.2 (by omega)),
    fun h N j hj => h j⟩

/-- Almost every configuration has ray edges missing arbitrarily far out. -/
theorem ae_rayEdge_missing_cofinally :
    ∀ᵐ ω ∂rayMu, ∀ M : ℕ, ∃ i : ℕ, M ≤ i ∧ rayEdge i ∉ ω := by
  rw [MeasureTheory.ae_all_iff]
  intro M
  have hnull : rayMu (⋂ N : ℕ, rayShiftCyl M N) = 0 := by
    have hanti : Antitone (rayShiftCyl M) := by
      intro a b hab ω hω i hi
      exact hω i (Finset.mem_range.2 (lt_of_lt_of_le (Finset.mem_range.1 hi) hab))
    have h := tendsto_measure_iInter_atTop (μ := rayMu) (s := rayShiftCyl M)
      (fun N => (measurableSet_rayShiftCyl M N).nullMeasurableSet) hanti ⟨0, by simp⟩
    exact tendsto_nhds_unique h (tendsto_measure_rayShiftCyl M)
  have hset : (⋂ N : ℕ, rayShiftCyl M N)
      = {ω : Config ℕ | ¬ ∃ i : ℕ, M ≤ i ∧ rayEdge i ∉ ω} := by
    ext ω
    rw [mem_iInter_rayShiftCyl_iff]
    constructor
    · rintro h ⟨i, hi, hni⟩
      obtain ⟨j, rfl⟩ : ∃ j, i = M + j := ⟨i - M, by omega⟩
      exact hni (h j)
    · rintro h j
    -- `rayEdge (M + j) ∈ ω`, since otherwise `M + j` would be a missing index `≥ M`
      by_contra hc
      exact h ⟨M + j, le_add_right le_rfl, hc⟩
  have hzero : rayMu {ω : Config ℕ | ¬ ∃ i : ℕ, M ≤ i ∧ rayEdge i ∉ ω} = 0 := by
    rw [← hset]
    exact hnull
  have h := (measure_eq_zero_iff_ae_notMem).1 hzero
  simpa only [Set.mem_ofPred_eq, not_not] using h

/-! ## The barrier argument: a missing ray edge bounds every cluster below it -/

theorem le_of_adj_of_barrier {ω : Config ℕ} {i : ℕ}
    (hsub : ∀ e ∈ ω, ∃ j, e = rayEdge j) (hmiss : rayEdge i ∉ ω) {a b : ℕ}
    (ha : a ≤ i) (hab : (openGraph ω).Adj a b) : b ≤ i := by
  have hmem : s(a, b) ∈ ω := (openGraph_adj.1 hab).2
  obtain ⟨j, hj⟩ := hsub _ hmem
  simp only [rayEdge] at hj
  rw [Sym2.eq_iff] at hj
  rcases hj with ⟨haj, hbj⟩ | ⟨haj, hbj⟩
  · by_contra hb
    have hji : j = i := by omega
    have hray : rayEdge j ∈ ω := by
      rw [rayEdge, ← hbj, ← haj]
      exact hmem
    rw [hji] at hray
    exact hmiss hray
  · omega

theorem walk_endpoint_le_of_barrier {ω : Config ℕ} {i : ℕ}
    (hsub : ∀ e ∈ ω, ∃ j, e = rayEdge j) (hmiss : rayEdge i ∉ ω) :
    ∀ {a b : ℕ}, (openGraph ω).Walk a b → a ≤ i → b ≤ i := by
  intro a b w
  induction w with
  | nil => exact id
  | cons h p ih => exact fun ha => ih (le_of_adj_of_barrier hsub hmiss ha h)

theorem cluster_finite_of_barrier {ω : Config ℕ} {i v : ℕ}
    (hsub : ∀ e ∈ ω, ∃ j, e = rayEdge j) (hmiss : rayEdge i ∉ ω) (hv : v ≤ i) :
    (cluster ω v).Finite := by
  refine (Set.finite_le_nat i).subset ?_
  intro w hw
  rw [mem_cluster_iff] at hw
  exact SimpleGraph.Reachable.elim hw fun p => walk_endpoint_le_of_barrier hsub hmiss p hv

theorem ae_not_inInfiniteCluster (v : ℕ) :
    ∀ᵐ ω ∂rayMu, ¬ InInfiniteCluster ω v := by
  filter_upwards [ae_ray_only, ae_rayEdge_missing_cofinally] with ω hoff hmiss
  obtain ⟨i, hvi, hmi⟩ := hmiss v
  have hsub : ∀ e ∈ ω, ∃ j, e = rayEdge j := by
    intro e he
    by_contra hc
    exact hoff e (rayProfile_of_notMem fun j hj => hc ⟨j, hj⟩) he
  have hfin := cluster_finite_of_barrier hsub hmi hvi
  rw [InInfiniteCluster, clusterVol_eq_encard, hfin.encard_eq_coe_toFinset_card]
  simp

/-- **`θ_1(0) = 0` for the ray**: the cluster of the root is a.s. finite, although
`∫⁻ |K_0| dP_1 = ⊤` (`ray_lintegral_clusterVol_eq_top`). -/
theorem ray_percolationFunction_zero : percolationFunction rayProfile rayProfile_nonneg 1 0 = 0 := by
  rw [percolationFunction, measure_eq_zero_iff_ae_notMem]
  simpa using ae_not_inInfiniteCluster 0

/-- No vertex has an infinite cluster almost surely. -/
theorem ae_no_infinite_cluster :
    ∀ᵐ ω ∂rayMu, ∀ v : ℕ, ¬ InInfiniteCluster ω v := by
  rw [MeasureTheory.ae_all_iff]
  exact ae_not_inInfiniteCluster

/-- Every vertex's cluster is a.s. finite. -/
theorem ray_percolationFunction_eq_zero (v : ℕ) :
    percolationFunction rayProfile rayProfile_nonneg 1 v = 0 := by
  rw [percolationFunction, measure_eq_zero_iff_ae_notMem]
  simpa using ae_not_inInfiniteCluster v

theorem ray_infiniteClusterProb_zero : infiniteClusterProb rayProfile rayProfile_nonneg 1 = 0 := by
  rw [infiniteClusterProb, measure_eq_zero_iff_ae_notMem]
  filter_upwards [ae_no_infinite_cluster] with ω hω hmem
  obtain ⟨v, hv⟩ := mem_existsInfiniteClusterEvent.1 hmem
  exact hω v hv

/-- **The refutation, in one statement.**

There is an intensity `J` on the edges of the countable vertex set `ℕ` and a parameter `β = 1`
such that *no vertex lies in an infinite cluster almost surely* (`percolationFunction = 0` for
every vertex, `infiniteClusterProb = 0`) while the expected cluster volume of the root is
infinite.

Hence the second half of the source gap `I.4.g3` (`𝔼_{β,r}|K| < ∞` for `β < β_c`) cannot be
deduced from subcriticality alone: it needs the translation-invariant long-range geometry
together with genuine sharpness of the phase transition. -/
theorem exists_no_percolation_infinite_mean :
    ∃ (J : Sym2 ℕ → ℝ) (hJ : ∀ e, 0 ≤ J e) (β : NNReal),
      (∀ v : ℕ, percolationFunction J hJ β v = 0) ∧
      infiniteClusterProb J hJ β = 0 ∧
      (∫⁻ ω, clusterVol ω 0 ∂(longRangeMeasure J hJ β)) = ⊤ :=
  ⟨rayProfile, rayProfile_nonneg, 1, ray_percolationFunction_eq_zero,
    ray_infiniteClusterProb_zero, ray_lintegral_clusterVol_eq_top⟩


/-! ## The transfer that *is* valid

The converse of the refutation holds in complete generality: an infinite mean forces an infinite
cluster with positive probability, and a finite mean forces the cluster to be finite a.e.  These
two lemmas are the only direction in which "no infinite cluster" and "finite first moment" can be
transferred, and they are what make the example above a genuine obstruction rather than an
artefact.
-/

section General

variable {V : Type*} [Countable V] {J : Sym2 V → ℝ} (hJ : ∀ e, 0 ≤ J e) {β : NNReal}

/-- **`θ > 0` forces an infinite first moment.** -/
theorem lintegral_clusterVol_eq_top_of_percolationFunction_ne_zero (v : V)
    (h : percolationFunction J hJ β v ≠ 0) :
    ∫⁻ ω, clusterVol ω v ∂(longRangeMeasure J hJ β) = ⊤ := by
  have hne : (longRangeMeasure J hJ β) {ω : Config V | InInfiniteCluster ω v} ≠ 0 := h
  have hge : (∫⁻ ω, clusterVol ω v ∂(longRangeMeasure J hJ β))
      ≥ ∫⁻ ω, ({ω : Config V | InInfiniteCluster ω v}.indicator
          (fun _ => (⊤ : ℝ≥0∞))) ω ∂(longRangeMeasure J hJ β) := by
    refine lintegral_mono fun ω => ?_
    by_cases hω : InInfiniteCluster ω v
    · rw [Set.indicator_of_mem (show ω ∈ {ω : Config V | InInfiniteCluster ω v} from hω)]
      exact le_of_eq hω.symm
    · rw [Set.indicator_of_notMem (show ω ∉ {ω : Config V | InInfiniteCluster ω v} from hω)]
      exact zero_le
  have heq : (∫⁻ ω, ({ω : Config V | InInfiniteCluster ω v}.indicator
        (fun _ => (⊤ : ℝ≥0∞))) ω ∂(longRangeMeasure J hJ β)) = ⊤ := by
    rw [lintegral_indicator_const (measurableSet_inInfiniteCluster v) ⊤]
    exact ENNReal.top_mul hne
  rw [heq] at hge
  exact top_le_iff.1 hge

/-- **A finite first moment forces the cluster to be finite a.e.** (contrapositive of
`lintegral_clusterVol_eq_top_of_percolationFunction_ne_zero`). -/
theorem percolationFunction_eq_zero_of_lintegral_ne_top (v : V)
    (h : (∫⁻ ω, clusterVol ω v ∂(longRangeMeasure J hJ β)) ≠ ⊤) :
    percolationFunction J hJ β v = 0 := by
  by_contra hc
  exact h (lintegral_clusterVol_eq_top_of_percolationFunction_ne_zero hJ v hc)

/-- Finiteness of the first moment at every vertex forces a.s. absence of an infinite cluster. -/
theorem ae_no_infiniteCluster_of_forall_lintegral_ne_top
    (h : ∀ v : V, (∫⁻ ω, clusterVol ω v ∂(longRangeMeasure J hJ β)) ≠ ⊤) :
    ∀ᵐ ω ∂(longRangeMeasure J hJ β), ∀ v : V, ¬ InInfiniteCluster ω v := by
  rw [MeasureTheory.ae_all_iff]
  intro v
  exact (measure_eq_zero_iff_ae_notMem).1
    (percolationFunction_eq_zero_of_lintegral_ne_top hJ v (h v))

/-- Consequently the percolation probability vanishes. -/
theorem infiniteClusterProb_eq_zero_of_forall_lintegral_ne_top
    (h : ∀ v : V, (∫⁻ ω, clusterVol ω v ∂(longRangeMeasure J hJ β)) ≠ ⊤) :
    infiniteClusterProb J hJ β = 0 := by
  rw [infiniteClusterProb, measure_eq_zero_iff_ae_notMem]
  filter_upwards [ae_no_infiniteCluster_of_forall_lintegral_ne_top hJ h] with ω hω hmem
  obtain ⟨v, hv⟩ := mem_existsInfiniteClusterEvent.1 hmem
  exact hω v hv

/-- **The finite-mean set is contained in `[0, β_c]`**, whenever the percolating set is nonempty
(so that `β_c < ∞`).  This is the only half of the first-moment dichotomy of the source gap
`I.4.g3` that is available without sharpness of the phase transition. -/
theorem le_criticalBeta_of_forall_lintegral_ne_top
    (hne : (criticalBetaSet J hJ).Nonempty)
    (h : ∀ v : V, (∫⁻ ω, clusterVol ω v ∂(longRangeMeasure J hJ β)) ≠ ⊤) :
    β ≤ criticalBeta J hJ := by
  have hnot : β ∉ criticalBetaSet J hJ := by
    rw [mem_criticalBetaSet_iff]
    exact ne_of_eq_of_ne (infiniteClusterProb_eq_zero_of_forall_lintegral_ne_top hJ h) zero_ne_one
  refine le_csInf hne ?_
  rintro a ha
  by_contra hlt
  exact hnot (criticalBetaSet_isUpperSet (le_of_lt (not_le.1 hlt)) ha)

end General


/-! ## `β = 1` lies at or below the critical parameter of the ray

The example is not an artefact of an absurd parameter: at `β = 2` the ray percolates almost
surely, because the open probability of the `i`-th ray edge is `1 - (i+2)^{-2}` and
`∏_{i<n} (1 - (i+2)^{-2}) = (n+2)/(2(n+1)) ≥ 1/2`, so all ray edges are open with probability at
least `1/2`.  Since `β = 1` does not percolate (`ray_infiniteClusterProb_zero`), the critical
parameter of this intensity satisfies `1 ≤ β_c`, and the first moment is already infinite there.
-/

/-- The law of the ray at `β = 2`. -/
noncomputable abbrev rayMuTwo : Measure (Config ℕ) :=
  longRangeMeasure rayProfile rayProfile_nonneg 2

theorem bernoulliEdgeProb_rayEdge_two (i : ℕ) :
    ((bernoulliEdgeProb rayProfile rayProfile_nonneg 2 (rayEdge i) : unitInterval) : ℝ)
      = 1 - 1 / ((i : ℝ) + 2) ^ 2 := by
  rw [bernoulliEdgeProb_coe, rayProfile_rayEdge]
  have hb : ((2 : NNReal) : ℝ) = 2 := rfl
  rw [hb]
  have hlog : (2 : ℝ) * Real.log ((i : ℝ) + 2) = Real.log (((i : ℝ) + 2) ^ 2) := by
    rw [Real.log_pow]
    push_cast
    ring
  rw [hlog, Real.exp_neg, Real.exp_log (by positivity), one_div]

theorem toNNReal_rayPi_two (i : ℕ) :
    (unitInterval.toNNReal (bernoulliEdgeProb rayProfile rayProfile_nonneg 2 (rayEdge i)) : ℝ≥0∞)
      = ENNReal.ofReal (1 - 1 / ((i : ℝ) + 2) ^ 2) := by
  rw [← ENNReal.ofReal_coe_nnreal]
  congr 1
  rw [unitInterval.coe_toNNReal, bernoulliEdgeProb_rayEdge_two]

theorem measure_rayCyl_two (n : ℕ) :
    rayMuTwo (rayCyl n)
      = ENNReal.ofReal (∏ i ∈ Finset.range n, (1 - 1 / ((i : ℝ) + 2) ^ 2)) := by
  rw [show rayMuTwo = edgeMeasure (bernoulliEdgeProb rayProfile rayProfile_nonneg 2) from rfl,
    rayCyl_eq_allOpen, edgeMeasure_cylinder, Finset.prod_image rayEdge_mem_range_inj]
  have hprod : (∏ i ∈ Finset.range n,
        (unitInterval.toNNReal (bernoulliEdgeProb rayProfile rayProfile_nonneg 2 (rayEdge i)) : ℝ≥0∞))
      = ∏ i ∈ Finset.range n, ENNReal.ofReal (1 - 1 / ((i : ℝ) + 2) ^ 2) :=
    Finset.prod_congr rfl (fun i _ => toNNReal_rayPi_two i)
  rw [hprod, ← ENNReal.ofReal_prod_of_nonneg]
  intro i _
  have hx : (0 : ℝ) < (i : ℝ) + 2 := by positivity
  have hsq : (1 : ℝ) ≤ ((i : ℝ) + 2) ^ 2 := by nlinarith
  have : 1 / ((i : ℝ) + 2) ^ 2 ≤ 1 := by
    rw [div_le_one (by positivity)]
    exact hsq
  linarith

/-- The product of the ray edge probabilities at `β = 2` has the closed form
`(n+2)/(2(n+1))`. -/
theorem prod_rayTwo (n : ℕ) :
    ∏ i ∈ Finset.range n, (1 - 1 / ((i : ℝ) + 2) ^ 2)
      = ((n : ℝ) + 2) / (2 * ((n : ℝ) + 1)) := by
  induction n with
  | zero => norm_num
  | succ n ih =>
    rw [Finset.prod_range_succ, ih]
    have h1 : (0 : ℝ) < (n : ℝ) + 1 := by positivity
    have h2 : (0 : ℝ) < (n : ℝ) + 2 := by positivity
    field_simp
    push_cast
    ring

theorem measure_rayCyl_two_ge (n : ℕ) :
    ENNReal.ofReal (1 / 2) ≤ rayMuTwo (rayCyl n) := by
  rw [measure_rayCyl_two, prod_rayTwo]
  refine ENNReal.ofReal_le_ofReal ?_
  rw [le_div_iff₀ (by positivity)]
  have : (0 : ℝ) ≤ (n : ℝ) := Nat.cast_nonneg n
  linarith

theorem antitone_rayCyl : Antitone rayCyl := by
  intro a b hab ω hω i hi
  exact hω i (Finset.mem_range.2 (lt_of_lt_of_le (Finset.mem_range.1 hi) hab))

/-- All ray edges open with probability at least `1/2`. -/
theorem measure_iInter_rayCyl_two :
    ENNReal.ofReal (1 / 2) ≤ rayMuTwo (⋂ n : ℕ, rayCyl n) := by
  have hlim := tendsto_measure_iInter_atTop (μ := rayMuTwo) (s := rayCyl)
    (fun n => (measurableSet_rayCyl n).nullMeasurableSet) antitone_rayCyl ⟨0, by simp⟩
  exact le_of_tendsto_of_tendsto tendsto_const_nhds hlim
    (Eventually.of_forall fun n => measure_rayCyl_two_ge n)

theorem mem_iInter_rayCyl {ω : Config ℕ} (hω : ω ∈ ⋂ n : ℕ, rayCyl n) :
    ∀ n : ℕ, rayEdge n ∈ ω := by
  rw [Set.mem_iInter] at hω
  intro n
  exact hω (n + 1) n (Finset.mem_range.2 (Nat.lt_succ_self n))

/-- At `β = 2` the root lies in an infinite cluster with positive probability. -/
theorem ray_infiniteClusterProb_two_pos : 0 < infiniteClusterProb rayProfile rayProfile_nonneg 2 := by
  have hsub : (⋂ n : ℕ, rayCyl n) ⊆ existsInfiniteClusterEvent ℕ := by
    intro ω hω
    rw [mem_existsInfiniteClusterEvent]
    refine ⟨0, ?_⟩
    have huniv : (Set.univ : Set ℕ) ⊆ cluster ω 0 := by
      intro k _
      rw [mem_cluster_iff]
      exact connects_of_rayCyl (n := k) fun i _ => mem_iInter_rayCyl hω i
    have hinf : (cluster ω 0).Infinite := Set.Infinite.mono huniv Set.infinite_univ
    rw [InInfiniteCluster, clusterVol_eq_encard, Set.encard_eq_top_iff.mpr hinf]
    simp
  have hpos : (0 : ℝ≥0∞) < rayMuTwo (⋂ n : ℕ, rayCyl n) :=
    lt_of_lt_of_le (by simp) (measure_iInter_rayCyl_two)
  exact lt_of_lt_of_le hpos (measure_mono hsub)

theorem ray_infiniteClusterProb_two : infiniteClusterProb rayProfile rayProfile_nonneg 2 = 1 :=
  infiniteClusterProb_eq_one_of_pos rayProfile_nonneg ray_infiniteClusterProb_two_pos

theorem ray_criticalBetaSet_nonempty : (criticalBetaSet rayProfile rayProfile_nonneg).Nonempty :=
  ⟨2, ray_infiniteClusterProb_two⟩

theorem one_not_mem_criticalBetaSet_ray :
    (1 : NNReal) ∉ criticalBetaSet rayProfile rayProfile_nonneg := by
  rw [mem_criticalBetaSet_iff]
  exact ne_of_eq_of_ne ray_infiniteClusterProb_zero zero_ne_one

/-- **`1 ≤ β_c` for the ray**: the parameter `β = 1` at which the mean is infinite is subcritical
in the sense that no infinite cluster exists there. -/
theorem one_le_criticalBeta_ray : (1 : NNReal) ≤ criticalBeta rayProfile rayProfile_nonneg := by
  obtain ⟨a, ha⟩ := ray_criticalBetaSet_nonempty
  refine le_csInf ⟨a, ha⟩ ?_
  intro b hb
  by_contra hlt
  exact one_not_mem_criticalBetaSet_ray
    (criticalBetaSet_isUpperSet (le_of_lt (not_le.1 hlt)) hb)

/-- **The refutation, in its final form.**

There is an intensity `J` on `Sym2 ℕ` and a parameter `β = 1 ≤ β_c(J)` with

* bounded degree: the expected number of open edges at every vertex is at most `2`;
* `infiniteClusterProb J hJ β = 0` (indeed `percolationFunction = 0` at every vertex), and
* `∫⁻ |K_0| dP_β = ⊤`.

Hence "`β ≤ β_c` implies a finite first moment" — even in the presence of bounded degree, the
strongest regularity a finite-range model has — is false in the generality of the library's
`longRangeMeasure` framework.  The subcritical half of the source gap `I.4.g3` cannot be derived
from the position of `β` relative to `β_c` alone; it needs the translation-invariant power-law
geometry and genuine sharpness of the phase transition, exactly what the source asserts without
proof. -/
theorem exists_subcritical_infinite_mean :
    ∃ (J : Sym2 ℕ → ℝ) (hJ : ∀ e, 0 ≤ J e) (β : NNReal),
      (∀ v : ℕ, ∑' x : ℕ,
        (unitInterval.toNNReal (bernoulliEdgeProb J hJ β (s(v, x))) : ℝ≥0∞) ≤ 2) ∧
      β ≤ criticalBeta J hJ ∧ infiniteClusterProb J hJ β = 0 ∧
        (∫⁻ ω, clusterVol ω 0 ∂(longRangeMeasure J hJ β)) = ⊤ :=
  ⟨rayProfile, rayProfile_nonneg, 1,
    fun v => ray_expectedDegree_le_two v,
    one_le_criticalBeta_ray, ray_infiniteClusterProb_zero, ray_lintegral_clusterVol_eq_top⟩


/-! ## The `hinf` hypothesis of the Corollary I.4.8 core *is* the critical clause of `I.4.g3`

`VolumeMoments.FirstMoment.first_moment_liminf_lower_bound_critical` (the analytic core of
Corollary I.4.8) assumes `Tendsto F atTop atTop` for the cut-off first moment `F r = E_{β_c,r}|K|`.
By `iSup_lintegral_clusterVol_cutoff` that hypothesis is *equivalent* to the uncut first moment at
`β_c` being infinite, i.e. to the first clause of the source gap `I.4.g3`.  So the analytic core
consumes `I.4.g3`; it cannot be used to prove it.
-/

section Hinf

open PercLib.CriticalLRP.FiniteVolume CutoffKernel TreeExpansion PercLib.CriticalLRP.CutoffLimit

variable {d : ℕ} {K : ℝ → ℝ}

/-- **The divergence hypothesis of Corollary I.4.8's core is the critical clause of `I.4.g3`.**

`Tendsto (cutoff first moment) atTop (𝓝 ⊤)` is the `ℝ≥0∞` form of the hypothesis
`hinf : Tendsto F atTop atTop` of `first_moment_liminf_lower_bound_critical` (there `F` is the
real-valued cut-off first moment, which is finite for every finite `r`).  It holds exactly when the
*uncut* first moment at `β` is infinite. -/
theorem tendsto_cutoffMean_nhds_top_iff_uncut_eq_top
    (hK : AntitoneOn K (Set.Ioi 0)) (hKtop : Tendsto K atTop (𝓝 0)) (hK0 : K 0 = 0)
    (hKnn : ∀ t, 0 < t → 0 ≤ K t) (β : NNReal) (o : Fin d → ℤ) :
    Tendsto (fun r : ℝ => ∫⁻ ω, clusterVol ω o ∂(longRangeMeasure (cutoffSymKernel K d r)
        (fun e => cutoffSymKernel_nonneg' hK d r e) β)) atTop (𝓝 (⊤ : ℝ≥0∞)) ↔
      (∫⁻ ω, clusterVol ω o ∂(longRangeMeasure (kernelJ
        (fun y : Fin d → ℤ => K ((linfNorm y : ℕ) : ℝ)) (profile_even (d := d) K))
        (uncutKernel_nonneg hKnn hK0 d) β)) = ⊤ := by
  have hsup := iSup_lintegral_clusterVol_cutoff hK hKtop hK0 hKnn d β o
  constructor
  · intro htend
    refine le_antisymm le_top ?_
    rw [← hsup, ← ENNReal.iSup_natCast]
    refine iSup_le fun n => ?_
    have hev : ∀ᶠ r : ℝ in atTop, (n : ℝ≥0∞)
        < ∫⁻ ω, clusterVol ω o ∂(longRangeMeasure (cutoffSymKernel K d r)
            (fun e => cutoffSymKernel_nonneg' hK d r e) β) :=
      htend.eventually (eventually_gt_nhds (by simp))
    obtain ⟨R, hR⟩ := hev.exists
    exact le_trans (le_of_lt hR) (le_iSup (fun r : ℝ => ∫⁻ ω, clusterVol ω o
      ∂(longRangeMeasure (cutoffSymKernel K d r)
        (fun e => cutoffSymKernel_nonneg' hK d r e) β)) R)
  · intro h
    have hmono := monotone_lintegral_clusterVol_cutoff (K := K) hK d β o
    have h1 : Tendsto (fun r : ℝ => ∫⁻ ω, clusterVol ω o
        ∂(longRangeMeasure (cutoffSymKernel K d r)
          (fun e => cutoffSymKernel_nonneg' hK d r e) β)) atTop
        (𝓝 (⨆ r : ℝ, ∫⁻ ω, clusterVol ω o ∂(longRangeMeasure (cutoffSymKernel K d r)
          (fun e => cutoffSymKernel_nonneg' hK d r e) β))) := tendsto_atTop_iSup hmono
    rw [hsup, h] at h1
    exact h1

end Hinf

end PercLib.CriticalLRP.RayRefutation
