/-
Critical LRP I: measurability in the cutoff radius of the finite-window pivotal flux
(window-flux measurability `hmeasK`), via monotonicity of the cut edge probability.

Swarm smwuges40, member m5.  Self-contained packet: no production writes, no axioms.
-/
module

public import PercLib.CriticalLRP.Analysis.Cutoff.Resampling
public import PercLib.CriticalLRP.Analysis.Cutoff.OffCorner.RadiusMeasurability.Defs
public import PercLib.CriticalLRP.Analysis.Cutoff.OffCorner.StrictDecrease
public import PercLib.CriticalLRP.Analysis.Cutoff.Continuity
public import PercLib.CriticalLRP.Analysis.Cutoff.OffCorner.Degree
public import PercLib.CriticalLRP.Analysis.Cutoff.OffCorner.EdgeMajorant
public import PercLib.CriticalLRP.Analysis.Cutoff.OffCorner.ScalarFactor.Main

/-!
# Radius measurability of singleton window and infinite flux
-/

@[expose] public section

set_option autoImplicit false
set_option linter.unusedSectionVars false
set_option linter.dupNamespace false

open MeasureTheory Filter Topology Set
open scoped ENNReal NNReal Topology

namespace PercLib.CriticalLRP.Orchestration

/-! ## 1. The cut edge probability is monotone in the radius on all of `ℝ` -/

namespace SourceModelData

variable (M : SourceModelData)

/-- **The cut edge probability vanishes at nonpositive radii.**  Every non-loop edge has
positive length, so for `r ≤ 0` the cutoff profile is `0`; loops have zero kernel. -/
theorem cutProb_eq_zero_of_nonpos {r : ℝ} (hr : r ≤ 0) (e : Sym2 M.V) :
    ((M.cutProb r e : unitInterval) : ℝ) = 0 := by
  induction e using Sym2.ind with
  | h x y =>
    rw [M.cutProb_coe]
    by_cases hxy : x = y
    · subst hxy
      rw [M.cutKernel_diag]
      simp
    · rw [M.cutKernel_offdiag r hxy]
      have hlt : r < M.S.dist x y := lt_of_le_of_lt hr (M.S.dist_pos hxy)
      rw [PercLib.CriticalLRP.FiniteVolume.cutoffProfile_of_lt hlt]
      simp

/-- **The cut edge probability is monotone in the radius on all of `ℝ`.**  On `(0,∞)` this is
`cutProb_mono`; at nonpositive radii the probability is `0`. -/
theorem monotone_cutProb (e : Sym2 M.V) : Monotone fun r => M.cutProb r e := by
  intro r r' hrr'
  rcases le_or_gt r 0 with hr | hr
  · refine Subtype.coe_le_coe.mp ?_
    rw [M.cutProb_eq_zero_of_nonpos hr e]
    exact (M.cutProb r' e).2.1
  · have hr' : 0 < r' := lt_of_lt_of_le hr hrr'
    exact M.cutProb_mono hr hr' hrr' e

/-- The edge probability as a real number is monotone in the radius. -/
theorem monotone_cutProb_coe (e : Sym2 M.V) :
    Monotone fun r => ((M.cutProb r e : unitInterval) : ℝ) :=
  fun _ _ h => Subtype.coe_le_coe.mpr (M.monotone_cutProb e h)

end SourceModelData

/-! ## 2. Monotone maps and monotonicity of increasing-event probabilities -/

section Maps

variable {V : Type*} [Countable V]

/-- Forcing a set of coordinates from a fixed configuration is monotone in the configuration. -/
theorem monotone_forceOn (S : Set (Sym2 V)) (η : Config V) :
    Monotone (fun ω : Config V => forceOn S η ω) := by
  intro ω ω' h e he
  simp only [forceOn, Set.mem_union, Set.mem_inter_iff, Set.mem_sdiff] at he ⊢
  tauto

/-- Restriction of a configuration to a finite edge window is monotone. -/
theorem monotone_cutConfig (S : Finset (Sym2 V)) :
    Monotone (fun ω : Config V => cutConfig S ω) := by
  intro ω ω' h e he
  exact ⟨h he.1, he.2⟩

end Maps

namespace SourceModelData

variable (M : SourceModelData)

/-- **Monotonicity in the cutoff radius of the probability of an increasing event.** -/
theorem monotone_real_edgeMeasure {A : Set (Config M.V)} (hA : MeasurableSet A)
    (hinc : IsIncreasing A) :
    Monotone fun r => (edgeMeasure (M.cutProb r)).real A := by
  intro r r' hrr'
  have hp : edgeMeasure (M.cutProb r) A ≤ edgeMeasure (M.cutProb r') A :=
    edgeMeasure_mono_of_le (fun e => M.monotone_cutProb e hrr') hA hinc
  have hfin : edgeMeasure (M.cutProb r') A ≠ ⊤ := measure_ne_top _ _
  exact ENNReal.toReal_mono hfin hp

/-- Measurability in the radius of the probability of an increasing measurable event. -/
theorem measurable_real_edgeMeasure {A : Set (Config M.V)} (hA : MeasurableSet A)
    (hinc : IsIncreasing A) :
    Measurable fun r => (edgeMeasure (M.cutProb r)).real A :=
  (M.monotone_real_edgeMeasure hA hinc).measurable

end SourceModelData

/-! ## 3. The pivotal flux of a window cluster indicator as a difference of two monotone
probability functions of the radius -/

namespace SourceModelData

variable (M : SourceModelData)


theorem measurableSet_forcedOpenEvent (S : Finset (Sym2 M.V)) (e : Sym2 M.V)
    {E : Set (Config M.V)} (hE : MeasurableSet E) : MeasurableSet (M.forcedOpenEvent S e E) :=
  hE.preimage ((measurable_cutConfig S).comp (measurable_forceOn _ _))

theorem measurableSet_forcedClosedEvent (S : Finset (Sym2 M.V)) (e : Sym2 M.V)
    {E : Set (Config M.V)} (hE : MeasurableSet E) : MeasurableSet (M.forcedClosedEvent S e E) :=
  hE.preimage ((measurable_cutConfig S).comp (measurable_forceOn _ _))

theorem isIncreasing_forcedOpenEvent (S : Finset (Sym2 M.V)) (e : Sym2 M.V)
    {E : Set (Config M.V)} (hEinc : IsIncreasing E) : IsIncreasing (M.forcedOpenEvent S e E) :=
  hEinc.preimage ((monotone_cutConfig S).comp (monotone_forceOn _ _))

theorem isIncreasing_forcedClosedEvent (S : Finset (Sym2 M.V)) (e : Sym2 M.V)
    {E : Set (Config M.V)} (hEinc : IsIncreasing E) : IsIncreasing (M.forcedClosedEvent S e E) :=
  hEinc.preimage ((monotone_cutConfig S).comp (monotone_forceOn _ _))

/-- The singleton spatial-moment functional is the indicator of "`y` lies in the cluster of `0`". -/
theorem sMomentTrunc_singleton_as_indicator (y : M.V) :
    sMomentTrunc (fun _ => (1 : ℝ)) (0 : M.V) ({y} : Finset M.V)
      = {σ : Config M.V | y ∈ cluster σ (0 : M.V)}.indicator (fun _ => (1 : ℝ)) := by
  funext ω
  rw [sMomentTrunc_singleton_eq]
  by_cases h : y ∈ cluster ω (0 : M.V)
  · rw [Set.indicator_of_mem h,
      Set.indicator_of_mem (show ω ∈ {σ : Config M.V | y ∈ cluster σ (0 : M.V)} from h)]
  · rw [Set.indicator_of_notMem h,
      Set.indicator_of_notMem (show ω ∉ {σ : Config M.V | y ∈ cluster σ (0 : M.V)} from h)]

/-- The pivotal difference of a window cluster indicator, in closed form. -/
theorem flipDiff_cutFun_indicator (S : Finset (Sym2 M.V)) (e : Sym2 M.V)
    {E : Set (Config M.V)} (ω : Config M.V) :
    flipDiff (cutFun S (E.indicator (fun _ => (1 : ℝ)))) e ω
      = Set.indicator (M.forcedOpenEvent S e E) (fun _ => (1 : ℝ)) ω
        - Set.indicator (M.forcedClosedEvent S e E) (fun _ => (1 : ℝ)) ω := by
  by_cases h₁ : cutConfig S (forceOn ({e} : Set (Sym2 M.V)) ({e} : Config M.V) ω) ∈ E
  · by_cases h₂ : cutConfig S (forceOn ({e} : Set (Sym2 M.V)) (∅ : Config M.V) ω) ∈ E
    · simp [flipDiff, cutFun, forcedOpenEvent, forcedClosedEvent, Set.indicator_of_mem, h₁, h₂]
    · simp [flipDiff, cutFun, forcedOpenEvent, forcedClosedEvent, Set.indicator_of_mem,
        Set.indicator_of_notMem, h₁, h₂]
  · by_cases h₂ : cutConfig S (forceOn ({e} : Set (Sym2 M.V)) (∅ : Config M.V) ω) ∈ E
    · simp [flipDiff, cutFun, forcedOpenEvent, forcedClosedEvent, Set.indicator_of_mem,
        Set.indicator_of_notMem, h₁, h₂]
    · simp [flipDiff, cutFun, forcedOpenEvent, forcedClosedEvent,
          Set.indicator_of_notMem, h₁, h₂]

/-- **The pivotal flux of a window cluster indicator** is the difference of the probabilities of
the two forced configurations. -/
theorem integral_flipDiff_cutFun_indicator (μ : Measure (Config M.V)) [IsProbabilityMeasure μ]
    (S : Finset (Sym2 M.V)) (e : Sym2 M.V) {E : Set (Config M.V)} (hE : MeasurableSet E) :
    ∫ ω, flipDiff (cutFun S (E.indicator (fun _ => (1 : ℝ)))) e ω ∂μ
      = μ.real (M.forcedOpenEvent S e E) - μ.real (M.forcedClosedEvent S e E) := by
  have h₁ : MeasurableSet (M.forcedOpenEvent S e E) := M.measurableSet_forcedOpenEvent S e hE
  have h₂ : MeasurableSet (M.forcedClosedEvent S e E) := M.measurableSet_forcedClosedEvent S e hE
  rw [show (fun ω => flipDiff (cutFun S (E.indicator (fun _ => (1 : ℝ)))) e ω)
      = fun ω => Set.indicator (M.forcedOpenEvent S e E) (fun _ => (1 : ℝ)) ω
          - Set.indicator (M.forcedClosedEvent S e E) (fun _ => (1 : ℝ)) ω from
    funext fun ω => M.flipDiff_cutFun_indicator S e ω]
  have hInt₁ : ∫ ω, Set.indicator (M.forcedOpenEvent S e E) (fun _ => (1 : ℝ)) ω ∂μ
      = μ.real (M.forcedOpenEvent S e E) := integral_indicator_one h₁
  have hInt₂ : ∫ ω, Set.indicator (M.forcedClosedEvent S e E) (fun _ => (1 : ℝ)) ω ∂μ
      = μ.real (M.forcedClosedEvent S e E) := integral_indicator_one h₂
  rw [integral_sub (Integrable.indicator (integrable_const (1 : ℝ)) h₁)
    (Integrable.indicator (integrable_const (1 : ℝ)) h₂), hInt₁, hInt₂]

/-- **Measurability in the radius of the pivotal flux of a window cluster indicator.** -/
theorem measurable_pivotalFlux_cutFun_singleton (S : Finset (Sym2 M.V)) (y : M.V)
    (e : Sym2 M.V) :
    Measurable fun r => pivotalFlux (edgeMeasure (M.cutProb r))
      (cutFun S (sMomentTrunc (fun _ => (1 : ℝ)) (0 : M.V) ({y} : Finset M.V))) e := by
  classical
  set E : Set (Config M.V) := {σ : Config M.V | y ∈ cluster σ (0 : M.V)} with hEdef
  have hE : MeasurableSet E := measurableSet_cluster_mem (0 : M.V) y
  have hEinc : IsIncreasing E := isIncreasing_cluster_mem (0 : M.V) y
  have h₁ : MeasurableSet (M.forcedOpenEvent S e E) := M.measurableSet_forcedOpenEvent S e hE
  have h₂ : MeasurableSet (M.forcedClosedEvent S e E) := M.measurableSet_forcedClosedEvent S e hE
  have h₁inc : IsIncreasing (M.forcedOpenEvent S e E) := M.isIncreasing_forcedOpenEvent S e hEinc
  have h₂inc : IsIncreasing (M.forcedClosedEvent S e E) :=
    M.isIncreasing_forcedClosedEvent S e hEinc
  have hg : cutFun S (sMomentTrunc (fun _ => (1 : ℝ)) (0 : M.V) ({y} : Finset M.V))
      = cutFun S (E.indicator (fun _ => (1 : ℝ))) := by
    rw [M.sMomentTrunc_singleton_as_indicator y, hEdef]
  have hpt : ∀ r : ℝ, pivotalFlux (edgeMeasure (M.cutProb r))
      (cutFun S (sMomentTrunc (fun _ => (1 : ℝ)) (0 : M.V) ({y} : Finset M.V))) e
      = (edgeMeasure (M.cutProb r)).real (M.forcedOpenEvent S e E)
        - (edgeMeasure (M.cutProb r)).real (M.forcedClosedEvent S e E) := by
    intro r
    have : IsProbabilityMeasure (edgeMeasure (M.cutProb r)) := inferInstance
    rw [pivotalFlux, hg]
    exact M.integral_flipDiff_cutFun_indicator (edgeMeasure (M.cutProb r))
      S e hE
  rw [show (fun r => pivotalFlux (edgeMeasure (M.cutProb r))
      (cutFun S (sMomentTrunc (fun _ => (1 : ℝ)) (0 : M.V) ({y} : Finset M.V))) e)
      = fun r => (edgeMeasure (M.cutProb r)).real (M.forcedOpenEvent S e E)
          - (edgeMeasure (M.cutProb r)).real (M.forcedClosedEvent S e E) from funext hpt]
  exact (M.measurable_real_edgeMeasure h₁ h₁inc).sub
    (M.measurable_real_edgeMeasure h₂ h₂inc)

end SourceModelData

/-! ## 4. Measurability in the radius of the cutoff edge derivative -/

namespace SourceModelData

variable (M : SourceModelData)

/-- **The cutoff edge derivative, written without the cutoff profile.**  For a non-loop edge the
kernel gap is positive exactly on the open range, and `exp (-(β J_r e)) = 1 - q_e(r)`. -/
theorem cutEdgeDeriv_eq_beta_mul_one_sub_cutProb {x y : M.V} (hxy : x ≠ y) (r : ℝ) :
    M.cutEdgeDeriv r (Sym2.mk x y)
      = (M.betaCrit : ℝ) * (-(deriv M.K r))
        * (1 - ((M.cutProb r (Sym2.mk x y) : unitInterval) : ℝ))
        * (if M.S.dist x y ≤ r then (1 : ℝ) else 0) := by
  rw [M.cutEdgeDeriv_mk, ite_eq_right hxy]
  by_cases h : M.S.dist x y ≤ r
  · rw [ite_eq_left h, ite_eq_left h, M.cutProb_coe, M.cutKernel_offdiag r hxy]
    have : (1 : ℝ) - (1 - Real.exp (-((M.betaCrit : ℝ) *
        PercLib.CriticalLRP.FiniteVolume.cutoffProfile M.K r (M.S.dist x y))))
        = Real.exp (-((M.betaCrit : ℝ) *
            PercLib.CriticalLRP.FiniteVolume.cutoffProfile M.K r (M.S.dist x y))) := by ring
    rw [this, mul_one]
  · rw [ite_eq_right h, ite_eq_right h, mul_zero]

/-- **Measurability in the radius of the edge derivative weight.** -/
theorem measurable_cutEdgeDeriv (e : Sym2 M.V) : Measurable fun r => M.cutEdgeDeriv r e := by
  induction e using Sym2.ind with
  | h x y =>
    by_cases hxy : x = y
    · subst hxy
      have hzero : (fun r => M.cutEdgeDeriv r (Sym2.mk x x)) = fun _ => (0 : ℝ) := by
        funext r
        rw [M.cutEdgeDeriv_mk, ite_eq_left rfl]
      rw [hzero]
      exact measurable_const
    · have hpt : (fun r => M.cutEdgeDeriv r (Sym2.mk x y))
          = fun r => (M.betaCrit : ℝ) * (-(deriv M.K r))
              * (1 - ((M.cutProb r (Sym2.mk x y) : unitInterval) : ℝ))
              * (if M.S.dist x y ≤ r then (1 : ℝ) else 0) := by
        funext r
        exact M.cutEdgeDeriv_eq_beta_mul_one_sub_cutProb hxy r
      rw [hpt]
      refine Measurable.mul (Measurable.mul (Measurable.mul measurable_const
        (measurable_deriv M.K).neg) ?_) ?_
      · exact measurable_const.sub (M.monotone_cutProb_coe (Sym2.mk x y)).measurable
      · exact Measurable.indicator measurable_const measurableSet_Ici

end SourceModelData

/-! ## 6. The unrestricted (infinite-window) pivotal flux of the cluster indicator -/

namespace SourceModelData

variable (M : SourceModelData)


theorem measurableSet_rawOpenEvent (e : Sym2 M.V) {E : Set (Config M.V)} (hE : MeasurableSet E) :
    MeasurableSet (M.rawOpenEvent e E) :=
  hE.preimage (measurable_forceOn _ _)

theorem measurableSet_rawClosedEvent (e : Sym2 M.V) {E : Set (Config M.V)} (hE : MeasurableSet E) :
    MeasurableSet (M.rawClosedEvent e E) :=
  hE.preimage (measurable_forceOn _ _)

theorem isIncreasing_rawOpenEvent (e : Sym2 M.V) {E : Set (Config M.V)} (hinc : IsIncreasing E) :
    IsIncreasing (M.rawOpenEvent e E) :=
  hinc.preimage (monotone_forceOn _ _)

theorem isIncreasing_rawClosedEvent (e : Sym2 M.V) {E : Set (Config M.V)}
    (hinc : IsIncreasing E) : IsIncreasing (M.rawClosedEvent e E) :=
  hinc.preimage (monotone_forceOn _ _)

/-- The pivotal difference of the cluster indicator, in closed form. -/
theorem flipDiff_indicator (e : Sym2 M.V) {E : Set (Config M.V)} (ω : Config M.V) :
    flipDiff (E.indicator (fun _ => (1 : ℝ))) e ω
      = Set.indicator (M.rawOpenEvent e E) (fun _ => (1 : ℝ)) ω
        - Set.indicator (M.rawClosedEvent e E) (fun _ => (1 : ℝ)) ω := by
  by_cases h₁ : forceOn ({e} : Set (Sym2 M.V)) ({e} : Config M.V) ω ∈ E
  · by_cases h₂ : forceOn ({e} : Set (Sym2 M.V)) (∅ : Config M.V) ω ∈ E
    · simp [flipDiff, rawOpenEvent, rawClosedEvent, Set.indicator_of_mem, h₁, h₂]
    · simp [flipDiff, rawOpenEvent, rawClosedEvent, Set.indicator_of_mem,
        Set.indicator_of_notMem, h₁, h₂]
  · by_cases h₂ : forceOn ({e} : Set (Sym2 M.V)) (∅ : Config M.V) ω ∈ E
    · simp [flipDiff, rawOpenEvent, rawClosedEvent, Set.indicator_of_mem,
        Set.indicator_of_notMem, h₁, h₂]
    · simp [flipDiff, rawOpenEvent, rawClosedEvent, Set.indicator_of_notMem, h₁, h₂]

/-- **The pivotal flux of the cluster indicator** is a difference of two forced probabilities. -/
theorem integral_flipDiff_indicator (μ : Measure (Config M.V)) [IsProbabilityMeasure μ]
    (e : Sym2 M.V) {E : Set (Config M.V)} (hE : MeasurableSet E) :
    ∫ ω, flipDiff (E.indicator (fun _ => (1 : ℝ))) e ω ∂μ
      = μ.real (M.rawOpenEvent e E) - μ.real (M.rawClosedEvent e E) := by
  have h₁ : MeasurableSet (M.rawOpenEvent e E) := M.measurableSet_rawOpenEvent e hE
  have h₂ : MeasurableSet (M.rawClosedEvent e E) := M.measurableSet_rawClosedEvent e hE
  rw [show (fun ω => flipDiff (E.indicator (fun _ => (1 : ℝ))) e ω)
      = fun ω => Set.indicator (M.rawOpenEvent e E) (fun _ => (1 : ℝ)) ω
          - Set.indicator (M.rawClosedEvent e E) (fun _ => (1 : ℝ)) ω from
    funext fun ω => M.flipDiff_indicator e ω]
  have hInt₁ : ∫ ω, Set.indicator (M.rawOpenEvent e E) (fun _ => (1 : ℝ)) ω ∂μ
      = μ.real (M.rawOpenEvent e E) := integral_indicator_one h₁
  have hInt₂ : ∫ ω, Set.indicator (M.rawClosedEvent e E) (fun _ => (1 : ℝ)) ω ∂μ
      = μ.real (M.rawClosedEvent e E) := integral_indicator_one h₂
  rw [integral_sub (Integrable.indicator (integrable_const (1 : ℝ)) h₁)
    (Integrable.indicator (integrable_const (1 : ℝ)) h₂), hInt₁, hInt₂]

/-- **Measurability in the radius of the pivotal flux of the cluster indicator.** -/
theorem measurable_pivotalFlux_singleton (y : M.V) (e : Sym2 M.V) :
    Measurable fun r => pivotalFlux (edgeMeasure (M.cutProb r))
      (sMomentTrunc (fun _ => (1 : ℝ)) (0 : M.V) ({y} : Finset M.V)) e := by
  classical
  set E : Set (Config M.V) := {σ : Config M.V | y ∈ cluster σ (0 : M.V)} with hEdef
  have hE : MeasurableSet E := measurableSet_cluster_mem (0 : M.V) y
  have hEinc : IsIncreasing E := isIncreasing_cluster_mem (0 : M.V) y
  have h₁ : MeasurableSet (M.rawOpenEvent e E) := M.measurableSet_rawOpenEvent e hE
  have h₂ : MeasurableSet (M.rawClosedEvent e E) := M.measurableSet_rawClosedEvent e hE
  have h₁inc : IsIncreasing (M.rawOpenEvent e E) := M.isIncreasing_rawOpenEvent e hEinc
  have h₂inc : IsIncreasing (M.rawClosedEvent e E) := M.isIncreasing_rawClosedEvent e hEinc
  have hg : sMomentTrunc (fun _ => (1 : ℝ)) (0 : M.V) ({y} : Finset M.V)
      = E.indicator (fun _ => (1 : ℝ)) := by
    rw [M.sMomentTrunc_singleton_as_indicator y, hEdef]
  have hpt : ∀ r : ℝ, pivotalFlux (edgeMeasure (M.cutProb r))
      (sMomentTrunc (fun _ => (1 : ℝ)) (0 : M.V) ({y} : Finset M.V)) e
      = (edgeMeasure (M.cutProb r)).real (M.rawOpenEvent e E)
        - (edgeMeasure (M.cutProb r)).real (M.rawClosedEvent e E) := by
    intro r
    have : IsProbabilityMeasure (edgeMeasure (M.cutProb r)) := inferInstance
    rw [pivotalFlux, hg]
    exact M.integral_flipDiff_indicator (edgeMeasure (M.cutProb r))
      e hE
  rw [show (fun r => pivotalFlux (edgeMeasure (M.cutProb r))
      (sMomentTrunc (fun _ => (1 : ℝ)) (0 : M.V) ({y} : Finset M.V)) e)
      = fun r => (edgeMeasure (M.cutProb r)).real (M.rawOpenEvent e E)
          - (edgeMeasure (M.cutProb r)).real (M.rawClosedEvent e E) from funext hpt]
  exact (M.measurable_real_edgeMeasure h₁ h₁inc).sub
    (M.measurable_real_edgeMeasure h₂ h₂inc)

end SourceModelData

/-! ## 5. Window-flux measurability in the radius (the `hmeasK` input) -/

namespace SourceModelData

variable (M : SourceModelData)

/-- **Measurability in the cutoff radius of the finite-window pivotal flux** of the singleton
spatial moment functional `1{y ∈ K_0}`. -/
theorem measurable_windowFluxOf_singleton (y : M.V) (S : ℕ → Finset (Sym2 M.V)) (k : ℕ) :
    Measurable fun r => windowFluxOf (0 : M.V)
      (sMomentTrunc (fun _ => (1 : ℝ)) (0 : M.V) ({y} : Finset M.V))
      S M.cutProb M.cutEdgeDeriv k r := by
  have hterm : ∀ e ∈ S k, Measurable fun r =>
      M.cutEdgeDeriv r e * pivotalFlux (edgeMeasure (M.cutProb r))
        (cutFun (S k) (sMomentTrunc (fun _ => (1 : ℝ)) (0 : M.V) ({y} : Finset M.V))) e :=
    fun e _ => (M.measurable_cutEdgeDeriv e).mul
      (M.measurable_pivotalFlux_cutFun_singleton (S k) y e)
  have hsum := Finset.measurable_sum (S k) hterm
  exact hsum

/-- **Window-flux measurability `hmeasK`**, in the exact shape consumed by
`IntegralFluxInterchange`, `Deriv` and `RussoExcluded.Main`. -/
theorem aeStronglyMeasurable_windowFluxOf_singleton (y : M.V)
    (S : ℕ → Finset (Sym2 M.V)) :
    ∀ k : ℕ, AEStronglyMeasurable (windowFluxOf (0 : M.V)
      (sMomentTrunc (fun _ => (1 : ℝ)) (0 : M.V) ({y} : Finset M.V))
      S M.cutProb M.cutEdgeDeriv k) volume :=
  fun k => (M.measurable_windowFluxOf_singleton y S k).aestronglyMeasurable

/-- **No continuity in the radius at an attained edge length.**  The derivative weight of a fixed
edge jumps from `0` to `β_c (-K'(r))` when the radius reaches the edge length, so the window flux
`windowFluxOf` is not continuous at any attained radius at which the pivotal flux is nonzero.
This is why `hcontinf` cannot be obtained by dominated convergence of the window fluxes. -/
theorem cutEdgeDeriv_at_dist {x y : M.V} (hxy : x ≠ y) :
    M.cutEdgeDeriv (M.S.dist x y) (Sym2.mk x y)
      = (M.betaCrit : ℝ) * (-(deriv M.K (M.S.dist x y))) := by
  rw [M.cutEdgeDeriv_mk, ite_eq_right hxy, ite_eq_left le_rfl,
    PercLib.CriticalLRP.FiniteVolume.cutoffProfile_of_le le_rfl, sub_self, mul_zero, neg_zero,
    Real.exp_zero, mul_one]

end SourceModelData

/-! ## 7. Measurability in the radius of the infinite pivotal flux (`hmeasinf`) -/

namespace SourceModelData

variable (M : SourceModelData)

/-- **The infinite pivotal flux of the cluster indicator as an `ℝ≥0∞` series.**  All
summands are
nonnegative for `r > 0`, so the real `tsum` is the `toReal` of the `ℝ≥0∞` `tsum`, and this
`ℝ≥0∞` series is measurable in the radius. -/
theorem sMomentInfFlux_eq_toReal_tsum {r : ℝ} (hr : 0 < r) (hvol : M.cutMoment 1 r ≠ ⊤)
    (y : M.V) :
    sMomentInfFlux (0 : M.V) ({y} : Finset M.V) (fun _ => (1 : ℝ)) M.cutProb M.cutEdgeDeriv r
      = (∑' e : Sym2 M.V, ENNReal.ofReal (M.cutEdgeDeriv r e *
          pivotalFlux (edgeMeasure (M.cutProb r))
            (sMomentTrunc (fun _ => (1 : ℝ)) (0 : M.V) ({y} : Finset M.V)) e)).toReal := by
  classical
  set g := sMomentTrunc (fun _ => (1 : ℝ)) (0 : M.V) ({y} : Finset M.V) with hg
  have hcnonneg : ∀ e : Sym2 M.V, 0 ≤ M.cutEdgeDeriv r e :=
    fun e => M.cutEdgeDeriv_nonneg (M.neg_deriv_K_nonneg hr) e
  have hpivnonneg : ∀ e : Sym2 M.V, 0 ≤ pivotalFlux (edgeMeasure (M.cutProb r)) g e := by
    intro e
    rw [pivotalFlux]
    exact integral_nonneg fun ω => flipDiff_sMomentTrunc_singleton_nonneg (M := M) y e ω
  have hnonneg : ∀ e : Sym2 M.V,
      0 ≤ M.cutEdgeDeriv r e * pivotalFlux (edgeMeasure (M.cutProb r)) g e :=
    fun e => mul_nonneg (hcnonneg e) (hpivnonneg e)
  have hdom := M.summable_hdom_of_cutMoment hr hvol
  have hle : ∀ e : Sym2 M.V, M.cutEdgeDeriv r e * pivotalFlux (edgeMeasure (M.cutProb r)) g e
      ≤ |M.cutEdgeDeriv r e| * (2 * (M.cutLaw r).real {ω | e ∈ touchSet ω (0 : M.V)}) := by
    intro e
    have hpiv : pivotalFlux (edgeMeasure (M.cutProb r)) g e
        ≤ (M.cutLaw r).real {ω | e ∈ touchSet ω (0 : M.V)} := by
      rw [M.cutLaw_eq_edgeMeasure r]
      refine le_trans (pivotalFlux_sMomentTrunc_singleton_le_real (M := M) y e) ?_
      exact ENNReal.toReal_mono (measure_ne_top _ _) (measure_mono Set.inter_subset_right)
    have hP : 0 ≤ (M.cutLaw r).real {ω | e ∈ touchSet ω (0 : M.V)} := ENNReal.toReal_nonneg
    rw [abs_of_nonneg (hcnonneg e)]
    nlinarith [hcnonneg e, hpivnonneg e, hpiv, hP]
  have hsumm : Summable fun e : Sym2 M.V =>
      M.cutEdgeDeriv r e * pivotalFlux (edgeMeasure (M.cutProb r)) g e :=
    Summable.of_nonneg_of_le hnonneg hle hdom
  have hfun : sMomentInfFlux (0 : M.V) ({y} : Finset M.V) (fun _ => (1 : ℝ))
      M.cutProb M.cutEdgeDeriv r
      = ∑' e : Sym2 M.V,
          M.cutEdgeDeriv r e * pivotalFlux (edgeMeasure (M.cutProb r)) g e := by
    simp only [sMomentInfFlux, infFluxOf, hg]
  rw [hfun, ← ENNReal.ofReal_tsum_of_nonneg hnonneg hsumm,
    ENNReal.toReal_ofReal (tsum_nonneg hnonneg)]

/-- **Measurability in the radius of the infinite pivotal flux** of the cluster indicator, from a
finite first cutoff moment on the window (which supplies pointwise summability in the edge). -/
theorem stronglyMeasurableAtFilter_sMomentInfFlux (y : M.V) {α β : ℝ} (hα : 0 ≤ α)
    (hvol : ∀ r ∈ Set.Ioo α β, M.cutMoment 1 r ≠ ⊤) :
    ∀ r0 ∈ Set.Ioo α β, StronglyMeasurableAtFilter
      (sMomentInfFlux (0 : M.V) ({y} : Finset M.V) (fun _ => (1 : ℝ)) M.cutProb M.cutEdgeDeriv)
      (𝓝 r0) volume := by
  intro r0 hr0
  refine ⟨Set.Ioo α β, isOpen_Ioo.mem_nhds hr0, ?_⟩
  have hsummand : ∀ e : Sym2 M.V, Measurable fun r : ℝ => ENNReal.ofReal
      (M.cutEdgeDeriv r e * pivotalFlux (edgeMeasure (M.cutProb r))
        (sMomentTrunc (fun _ => (1 : ℝ)) (0 : M.V) ({y} : Finset M.V)) e) :=
    fun e => ((M.measurable_cutEdgeDeriv e).mul
      (M.measurable_pivotalFlux_singleton y e)).ennreal_ofReal
  have hgmeas : Measurable fun r : ℝ => (∑' e : Sym2 M.V, ENNReal.ofReal (M.cutEdgeDeriv r e *
      pivotalFlux (edgeMeasure (M.cutProb r))
        (sMomentTrunc (fun _ => (1 : ℝ)) (0 : M.V) ({y} : Finset M.V)) e)).toReal :=
    (Measurable.tsum hsummand).ennreal_toReal
  refine hgmeas.aestronglyMeasurable.congr ?_
  filter_upwards [ae_restrict_mem measurableSet_Ioo] with r hr
  exact (M.sMomentInfFlux_eq_toReal_tsum (lt_of_le_of_lt hα hr.1) (hvol r hr) y).symm

/-- The endpoint off-corner derivative with `hmeasK` discharged by the monotonicity package.
The remaining inputs `hboundint`, `hcontinf` and `hGcont` are unchanged. -/
theorem hasDerivAt_cutMassReal_rhsScalar_of_endpoint_of_measurability
    (M : SourceModelData)
    (T : ℕ → Finset M.V) (hTmono : Monotone T) (hT : ∀ y : M.V, ∃ n, y ∈ T n)
    (S : ℕ → Finset (Sym2 M.V)) (hSmono : Monotone S) (hS : ∀ e : Sym2 M.V, ∃ n, e ∈ S n)
    {α β r0 : ℝ} (hα0 : 0 < α) (hαr0 : α < r0) (hr0β : r0 < β)
    (hoff : ∀ r ∈ Set.Ioo α β, r ∉ M.cornerRadii)
    (hKd : ∀ r ∈ Set.Ioo α β, DifferentiableAt ℝ M.K r)
    (h2β : M.cutMoment 2 β ≠ ⊤)
    (hboundint : ∀ y : M.V, ∀ a' ∈ Set.Ioo α β, ∀ b' ∈ Set.Ioo α β, IntervalIntegrable
      (sMomentWeight (0 : M.V) {y} (fun _ => (1 : ℝ)) M.cutProb M.cutEdgeDeriv) volume a' b')
    (hcontinf : ∀ y : M.V, ∀ r ∈ Set.Ioo α β, ContinuousAt
      (sMomentInfFlux (0 : M.V) {y} (fun _ => (1 : ℝ)) M.cutProb M.cutEdgeDeriv) r)
    (hGcont : ∀ r ∈ Set.Ioo α β, ContinuousAt (fun r' => ∑' y : M.V,
      sMomentInfFlux (0 : M.V) {y} (fun _ => (1 : ℝ)) M.cutProb M.cutEdgeDeriv r') r) :
    HasDerivAt M.cutMassReal (M.rhsScalar r0) r0 :=
  M.hasDerivAt_cutMassReal_rhsScalar_of_endpoint T hTmono hT S hSmono hS hα0 hαr0 hr0β
    hoff hKd h2β hboundint (fun y k => M.aeStronglyMeasurable_windowFluxOf_singleton y S k)
    hcontinf hGcont

end SourceModelData

end PercLib.CriticalLRP.Orchestration

/-! ## Axiom audit -/

open PercLib.CriticalLRP.Orchestration.SourceModelData

#print axioms cutProb_eq_zero_of_nonpos
#print axioms monotone_cutProb
#print axioms monotone_real_edgeMeasure
#print axioms measurable_real_edgeMeasure
#print axioms flipDiff_cutFun_indicator
#print axioms integral_flipDiff_cutFun_indicator
#print axioms measurable_pivotalFlux_cutFun_singleton
#print axioms measurable_cutEdgeDeriv
#print axioms measurable_windowFluxOf_singleton
#print axioms aeStronglyMeasurable_windowFluxOf_singleton
#print axioms cutEdgeDeriv_at_dist
#print axioms flipDiff_indicator
#print axioms integral_flipDiff_indicator
#print axioms measurable_pivotalFlux_singleton
#print axioms sMomentInfFlux_eq_toReal_tsum
#print axioms stronglyMeasurableAtFilter_sMomentInfFlux
#print axioms hasDerivAt_cutMassReal_rhsScalar_of_endpoint_of_measurability
#print axioms PercLib.CriticalLRP.Orchestration.monotone_forceOn
#print axioms PercLib.CriticalLRP.Orchestration.monotone_cutConfig
