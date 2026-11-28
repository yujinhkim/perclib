/-
Accepted and independently rebuilt from Ultramath `smwzqts7r`, member m5.
Production review base `e2b5cf635f5a2ffb1c7f203271de1c0a7ef3ad2b`;
reviewed scratch source `.scratch/review-smwzqts7r/m5/Hydro.lean`.
-/

/-
M5 / swarm `smwzqts7r`, direction d7 (paper direction (D)):
Corollary I.4.14, Case 3 of (HD): the log-corrected critical two-point bound implies the
hydrodynamic condition.

Source: Hutchcroft, *Critical long-range percolation I*, arXiv:2508.18807v1,
(HD) Case 3 (p. 9), Lemma I.2.6 (p. 24), (I.4.13) and Corollary I.4.14 (p. 42).

  (HD)(3):  d = 6, alpha = 2, P_{beta_c}(x <-> y) <~ (log ||x-y||)^{-1} ||x-y||^{-d+2}.
  Hydro:    M_r = o(r^{(d+alpha)/2}).

The proof has three independent parts, all kernel checked here:

* (kernel step) the Case-3 pointwise bound summed over the ball of radius `2r`,
  using the production ball-shell estimate: `sum tau <= K r^2 / log r`;
* (median step) Lemma I.2.6 at the model's own normalized ball, i.e. the windowed
  moment version that the production box version does not give:
  `(M_r - 1)^2 <= e |B_r| E_{beta_c,r}|K cap B_{2r}|`;
* (assembly) the cutoff first moment as a sum of two-point values, the comparison with the
  uncut critical two-point function, and the elementary deduction `M_r = o(r^4)`.
-/
module

public import PercLib.CriticalLRP.Analysis.SecondMomentCase3.TriangleFromHD.LargeDistance.Main
public import PercLib.CriticalLRP.Analysis.LatticeConvolution.NormShell
public import PercLib.CriticalLRP.Analysis.SecondMomentCase2.Source.Defs
public import PercLib.CriticalLRP.Analysis.Cutoff.Translation
public import PercLib.CriticalLRP.Analysis.Cutoff.Basic
public import PercLib.CriticalLRP.Analysis.Cutoff.Monotone

/-! Conditional hydrodynamic estimates at the actual normalized cutoff law. -/

set_option autoImplicit false
set_option linter.style.longLine false
set_option linter.hashCommand false
set_option linter.unusedSectionVars false

@[expose] public section

open MeasureTheory Set Filter
open scoped ENNReal NNReal Topology BigOperators

open PercLib.CriticalLRP.Percolation

namespace M5

open PercLib.CriticalLRP PercLib.CriticalLRP.Orchestration

variable (M : SourceModelData)

/-! ## §1 The normalized source ball centred at `x` -/

/-- The closed source-norm ball of radius `s` centred at the lattice point `x`. -/
def ballAt (x : M.V) (s : ℝ) : Set M.V :=
  {y : M.V | M.S.ρ (toVec (y - x)) ≤ s}

theorem ballAt_zero (s : ℝ) : ballAt M 0 s = M.ball s := by
  ext y
  simp [ballAt, SourceModelData.ball]

theorem mem_ballAt_iff {x y : M.V} {s : ℝ} :
    y ∈ ballAt M x s ↔ M.S.ρ (toVec (y - x)) ≤ s := Iff.rfl

/-- A point of the window sees the whole window inside its own doubled window. -/
theorem ball_subset_ballAt_two_mul {r : ℝ} {x : M.V} (hx : x ∈ M.ball r) :
    M.ball r ⊆ ballAt M x (2 * r) := by
  intro y hy
  have hyr : M.S.ρ (toVec y) ≤ r := hy
  have hxr : M.S.ρ (toVec x) ≤ r := hx
  have hneg : M.S.ρ (toVec (0 - x)) = M.S.ρ (toVec x) := by
    have h : toVec (0 - x) = -toVec x := by
      funext i
      simp [toVec]
    rw [h, M.S.ρ_neg]
  have hsum : M.S.ρ (toVec (y - x)) ≤ M.S.ρ (toVec y) + M.S.ρ (toVec (0 - x)) := by
    have h : toVec (y - x) = toVec y + toVec (0 - x) := by
      funext i
      simp [toVec]
      ring
    rw [h]
    exact M.S.ρ_add_le _ _
  change M.S.ρ (toVec (y - x)) ≤ 2 * r
  rw [hneg] at hsum
  linarith

/-! ## §2 The kernel step: `∑_{x ∈ B_{2r}} τ(x) ⪯ r^α (log r)^{-1}` -/

/-- The shell constant of the `a = 2`, `c = 1` ball-shell estimate. -/
noncomputable def shellConst (M : SourceModelData) : ℝ :=
  (2 : ℝ) ^ (2 : ℝ) * (CriticalLRPConv.srcCountConst M.S *
    (1 + ((M.d : ℝ) - 2 + 2 * ((1 : ℝ) + 1)) * CriticalLRPConv.coreConst 2 1))

theorem shellConst_pos (M : SourceModelData) : 0 < shellConst M := by
  have hu : 0 < CriticalLRPConv.srcLowerUnit M.S :=
    CriticalLRPConv.srcLowerUnit_pos M.S M.hd
  have hbase : (0 : ℝ) < 3 / CriticalLRPConv.srcLowerUnit M.S + 3 := by positivity
  have hcount : 0 < CriticalLRPConv.srcCountConst M.S := by
    rw [CriticalLRPConv.srcCountConst]
    exact Real.rpow_pos_of_pos hbase _
  have hcore : 0 < CriticalLRPConv.coreConst 2 1 := CriticalLRPConv.coreConst_pos 2 1
  have h1 : (0 : ℝ) < 1 + ((M.d : ℝ) - 2 + 2 * ((1 : ℝ) + 1)) *
      CriticalLRPConv.coreConst 2 1 := by nlinarith
  have hpow : (0 : ℝ) < (2 : ℝ) ^ (2 : ℝ) := Real.rpow_pos_of_pos (by norm_num) _
  unfold shellConst
  positivity

/-- **The Case-3 lattice kernel sum.**  Under Case 3 of (HD), the critical two-point
function summed over the ball of source radius `2r` is `O(r^2 / log r)` — the marginal
`d = 6`, `α = 2` power law with the *gain* of one logarithm that makes the hydrodynamic
condition true.  (`r^2 = r^α` at `α = 2`.) -/
theorem sum_tau_ball_le_of_case3 (h : M.Case3HD) :
    ∃ K : ℝ, 0 < K ∧ ∀ r : ℝ, 2 ≤ r →
      ∑ x ∈ (M.finite_ball (2 * r)).toFinset, M.tau x
        ≤ K * r ^ 2 * (Real.log r)⁻¹ := by
  have hd6 : M.d = 6 := h.1
  obtain ⟨K₀, hK₀, hτ⟩ := M.exists_abs_tau_le_Wt h
  have hdR : (M.d : ℝ) = 6 := by exact_mod_cast hd6
  refine ⟨K₀ * shellConst M * 9, by have := shellConst_pos M; positivity, ?_⟩
  intro r hr
  have hr0 : (0 : ℝ) < r := by linarith
  have hlogr : (0 : ℝ) < Real.log r := Real.log_pos (by linarith)
  have hlog2r : (0 : ℝ) < CriticalLRPConv.LamR (2 * r) := by
    rw [CriticalLRPConv.LamR]
    exact Real.log_pos (by linarith)
  -- termwise domination by the positive-log majorant
  have hstep1 : ∑ x ∈ (M.finite_ball (2 * r)).toFinset, M.tau x
      ≤ K₀ * ∑ x ∈ (M.finite_ball (2 * r)).toFinset,
          CriticalLRPConv.Wt ((M.d : ℝ) - 2) 1 (M.S.ρ (toVec x)) := by
    rw [Finset.mul_sum]
    refine Finset.sum_le_sum fun x _ => ?_
    simpa only [abs_of_nonneg (M.tau_nonneg x)] using hτ x
  -- the production ball-shell estimate at `a = 2`, `c = 1`, `S₀ = 2r`
  have hshell : ∑ x ∈ (M.finite_ball (2 * r)).toFinset,
        CriticalLRPConv.Wt ((M.d : ℝ) - 2) 1 (M.S.ρ (toVec x))
      ≤ shellConst M * ((1 + 2 * r) ^ (2 : ℝ) * CriticalLRPConv.LamR (2 * r) ^ (-(1 : ℝ))) :=
    CriticalLRPConv.srcNorm_ball_shell_bound M.S M.hd
      (a := 2) (c := 1) (S₀ := 2 * r) (F := (M.finite_ball (2 * r)).toFinset)
      (by norm_num) (by rw [hdR]; norm_num) (by norm_num) (by linarith)
      (fun y hy => by
        have hmem : y ∈ M.ball (2 * r) := by
          rw [← (M.finite_ball (2 * r)).coe_toFinset]
          exact hy
        exact hmem)
  -- arithmetic: `(1 + 2r)^2 ≤ 9 r^2` and `LamR (2r)^{-1} ≤ (log r)^{-1}`
  have h9 : (1 + 2 * r) ^ (2 : ℝ) ≤ 9 * r ^ 2 := by
    have h2 : (1 + 2 * r : ℝ) ≤ 3 * r := by linarith
    have h3 : (0 : ℝ) < 1 + 2 * r := by linarith
    have h4 : (1 + 2 * r) ^ (2 : ℝ) ≤ (3 * r) ^ (2 : ℝ) :=
      Real.rpow_le_rpow h3.le h2 (by norm_num)
    have h5 : (3 * r) ^ (2 : ℝ) = 9 * r ^ 2 := by
      rw [Real.mul_rpow (by norm_num) hr0.le]
      norm_num
    rw [h5] at h4
    exact h4
  have hlog : CriticalLRPConv.LamR (2 * r) ^ (-(1 : ℝ)) ≤ (Real.log r)⁻¹ := by
    have hle : Real.log r ≤ CriticalLRPConv.LamR (2 * r) := by
      rw [CriticalLRPConv.LamR]
      exact Real.log_le_log hr0 (by linarith)
    have h := Real.rpow_le_rpow_of_nonpos hlogr hle (by norm_num : (-(1 : ℝ)) ≤ 0)
    simpa only [Real.rpow_neg_one] using h
  have hlog2rnn : (0 : ℝ) ≤ CriticalLRPConv.LamR (2 * r) ^ (-(1 : ℝ)) :=
    le_of_lt (by positivity)
  have hprod : (1 + 2 * r) ^ (2 : ℝ) * CriticalLRPConv.LamR (2 * r) ^ (-(1 : ℝ))
      ≤ (9 * r ^ 2) * (Real.log r)⁻¹ :=
    mul_le_mul h9 hlog hlog2rnn (by positivity)
  have hK : 0 < K₀ * shellConst M := by
    have := shellConst_pos M
    positivity
  calc ∑ x ∈ (M.finite_ball (2 * r)).toFinset, M.tau x
      ≤ K₀ * ∑ x ∈ (M.finite_ball (2 * r)).toFinset,
          CriticalLRPConv.Wt ((M.d : ℝ) - 2) 1 (M.S.ρ (toVec x)) := hstep1
    _ ≤ K₀ * (shellConst M *
          ((1 + 2 * r) ^ (2 : ℝ) * CriticalLRPConv.LamR (2 * r) ^ (-(1 : ℝ)))) := by
        exact mul_le_mul_of_nonneg_left hshell hK₀.le
    _ = K₀ * shellConst M *
          ((1 + 2 * r) ^ (2 : ℝ) * CriticalLRPConv.LamR (2 * r) ^ (-(1 : ℝ))) := by ring
    _ ≤ K₀ * shellConst M * ((9 * r ^ 2) * (Real.log r)⁻¹) := by
        exact mul_le_mul_of_nonneg_left hprod hK.le
    _ = K₀ * shellConst M * 9 * r ^ 2 * (Real.log r)⁻¹ := by ring


theorem clusterVolIn_eq_encard {V : Type*} [Countable V] (ω : Config V) (v : V) (W : Set V) :
    clusterVolIn ω v W = (((cluster ω v) ∩ W).encard : ℝ≥0∞) := rfl

/-- The source-norm ball is translation invariant. -/
theorem ballAt_add_image (a x : M.V) (s : ℝ) :
    ballAt M (x + a) s = (fun y : M.V => y + a) '' ballAt M x s := by
  ext y
  constructor
  · intro hy
    refine ⟨y - a, ?_, by abel⟩
    have h : toVec ((y - a) - x) = toVec (y - (x + a)) := by
      congr 1
      abel
    change M.S.ρ (toVec ((y - a) - x)) ≤ s
    rw [h]
    exact hy
  · rintro ⟨z, hz, rfl⟩
    have h : toVec ((z + a) - (x + a)) = toVec (z - x) := by
      congr 1
      abel
    change M.S.ρ (toVec ((z + a) - (x + a))) ≤ s
    rw [h]
    exact hz

/-! ## §2 The counting function -/

/-- The number of window vertices whose own cluster occupies at least `m` points of their
own doubled window. -/
noncomputable def winCount (m : ℕ) (r : ℝ) (ω : Config M.V) : ℝ≥0∞ :=
  ∑ x ∈ (M.finite_ball r).toFinset,
    if (m : ℝ≥0∞) ≤ clusterVolIn ω x (ballAt M x (2 * r)) then 1 else 0

theorem measurable_winCount (m : ℕ) (r : ℝ) : Measurable (winCount M m r) := by
  refine Finset.measurable_sum _ fun x _ => ?_
  refine Measurable.ite ?_ measurable_const measurable_const
  exact measurableSet_le measurable_const (measurable_clusterVolIn x _)

/-- **The deterministic counting step.**  If some cluster occupies at least `m` points of the
window `B_r`, then at least `m` window vertices `x` see `m` points of their own cluster in
their own doubled window `B_{2r}(x)`. -/
theorem le_winCount {m : ℕ} {r : ℝ} {ω : Config M.V}
    (h : ∃ w ∈ M.ball r, (m : ℝ≥0∞) ≤ clusterVolIn ω w (M.ball r)) :
    (m : ℝ≥0∞) ≤ winCount M m r ω := by
  classical
  obtain ⟨w, hw, hle⟩ := h
  set S : Set M.V := cluster ω w ∩ M.ball r with hS
  set T : Finset M.V := (M.finite_ball r).toFinset.filter
    (fun x => (m : ℝ≥0∞) ≤ clusterVolIn ω x (ballAt M x (2 * r))) with hT
  have hSfin : S.Finite := (M.finite_ball r).subset Set.inter_subset_right
  -- `m` is at most the number of points of `S`
  have hle' : (m : ℝ≥0∞) ≤ (S.encard : ℝ≥0∞) := by
    simpa only [clusterVolIn_eq_encard, hS] using hle
  have henc : (S.encard : ℝ≥0∞) = ((hSfin.toFinset.card : ℕ) : ℝ≥0∞) := by
    exact congrArg (fun x : ℕ∞ => (x : ℝ≥0∞)) hSfin.encard_eq_coe_toFinset_card
  have hmn : m ≤ hSfin.toFinset.card := by
    rw [henc] at hle'
    exact_mod_cast hle'
  -- every point of `S` is counted by `winCount`
  have hmem : ∀ x ∈ S, x ∈ M.ball r ∧ (m : ℝ≥0∞) ≤ clusterVolIn ω x (ballAt M x (2 * r)) := by
    intro x hx
    obtain ⟨hxc, hxb⟩ := hx
    refine ⟨hxb, le_trans hle' ?_⟩
    have hcl : cluster ω x = cluster ω w :=
      cluster_eq_iff.mpr (connects_symm (mem_cluster_iff.mp hxc))
    have hsub : cluster ω w ∩ M.ball r ⊆ cluster ω x ∩ ballAt M x (2 * r) := by
      intro y hy
      exact ⟨by rw [hcl]; exact hy.1, ball_subset_ballAt_two_mul M hxb hy.2⟩
    rw [clusterVolIn_eq_encard]
    rw [hS]
    exact_mod_cast Set.encard_mono hsub
  have hsubFT : hSfin.toFinset ⊆ T := by
    intro x hx
    have hxS : x ∈ S := hSfin.mem_toFinset.mp hx
    obtain ⟨hxb, hxm⟩ := hmem x hxS
    refine Finset.mem_filter.mpr ⟨?_, hxm⟩
    exact (M.finite_ball r).mem_toFinset.mpr hxb
  have hcard : hSfin.toFinset.card ≤ T.card := Finset.card_le_card hsubFT
  simp only [winCount]
  rw [Finset.sum_boole]
  change (m : ℝ≥0∞) ≤ (T.card : ℝ≥0∞)
  have h1 : (m : ℝ≥0∞) ≤ ((hSfin.toFinset.card : ℕ) : ℝ≥0∞) := by exact_mod_cast hmn
  have h2 : ((hSfin.toFinset.card : ℕ) : ℝ≥0∞) ≤ (T.card : ℝ≥0∞) := by exact_mod_cast hcard
  exact le_trans h1 h2



/-! ## §3 Translation invariance of the windowed event -/

/-- Shifting the configuration by `a` and the base point by `a` preserves the truncated
cluster volume in the translated window. -/
theorem clusterVolIn_shift_image {a v : M.V} {ω : Config M.V} {W : Set M.V} :
    clusterVolIn (shiftConfig a ω) (v + a) ((fun y : M.V => y + a) '' W)
      = clusterVolIn ω v W := by
  rw [clusterVolIn_eq_encard, clusterVolIn_eq_encard, cluster_shiftConfig]
  have hinj : Function.Injective (fun u : M.V => u + a) := fun u v huv => by simpa using huv
  rw [← Set.image_inter hinj]
  exact congrArg (fun z : ℕ∞ => (z : ℝ≥0∞))
    (Set.InjOn.encard_image (s := cluster ω v ∩ W) (fun u _ v _ huv => hinj huv))

/-- **Translation invariance of the windowed event** for the cutoff law. -/
theorem measure_clusterVolIn_ballAt_eq (m : ℕ) (r : ℝ) (x : M.V) :
    (M.cutLaw r) {ω : Config M.V | (m : ℝ≥0∞) ≤ clusterVolIn ω x (ballAt M x (2 * r))}
      = (M.cutLaw r) {ω : Config M.V | (m : ℝ≥0∞) ≤ clusterVolIn ω 0 (M.ball (2 * r))} := by
  have hmeas0 : MeasurableSet
      {ω : Config M.V | (m : ℝ≥0∞) ≤ clusterVolIn ω 0 (M.ball (2 * r))} :=
    measurableSet_le measurable_const (measurable_clusterVolIn 0 _)
  -- the point `x` of the configuration shifted by `-x` is the origin, and the window is `B_{2r}`
  have hid : ∀ ω : Config M.V,
      clusterVolIn (shiftConfig (-x) ω) (0 : M.V) (M.ball (2 * r))
        = clusterVolIn ω x (ballAt M x (2 * r)) := by
    intro ω
    have h4 := clusterVolIn_shift_image (M := M) (a := -x) (v := x) (ω := ω)
      (W := ballAt M x (2 * r))
    have h3 : x + (-x) = (0 : M.V) := by abel
    rw [h3] at h4
    have himg : (fun y : M.V => y + (-x)) '' ballAt M x (2 * r) = M.ball (2 * r) := by
      rw [← ballAt_add_image M (-x) x (2 * r), h3, ballAt_zero]
    rw [himg] at h4
    exact h4
  have hpre : shiftConfig (-x) ⁻¹'
      {ω : Config M.V | (m : ℝ≥0∞) ≤ clusterVolIn ω 0 (M.ball (2 * r))}
      = {ω : Config M.V | (m : ℝ≥0∞) ≤ clusterVolIn ω x (ballAt M x (2 * r))} := by
    ext ω
    change ((m : ℝ≥0∞) ≤ clusterVolIn (shiftConfig (-x) ω) 0 (M.ball (2 * r)))
      ↔ ((m : ℝ≥0∞) ≤ clusterVolIn ω x (ballAt M x (2 * r)))
    rw [hid ω]
  calc (M.cutLaw r) {ω : Config M.V | (m : ℝ≥0∞) ≤ clusterVolIn ω x (ballAt M x (2 * r))}
      = (M.cutLaw r) (shiftConfig (-x) ⁻¹'
          {ω : Config M.V | (m : ℝ≥0∞) ≤ clusterVolIn ω 0 (M.ball (2 * r))}) := by
        rw [hpre]
    _ = (M.cutLaw r).map (shiftConfig (-x))
          {ω : Config M.V | (m : ℝ≥0∞) ≤ clusterVolIn ω 0 (M.ball (2 * r))} := by
        rw [Measure.map_apply (measurable_shiftConfig _) hmeas0]
    _ = (M.cutLaw r) {ω : Config M.V | (m : ℝ≥0∞) ≤ clusterVolIn ω 0 (M.ball (2 * r))} := by
        rw [M.cutLaw_map_shiftConfig]

/-! ## §4 The lintegral of the counting function -/

theorem lintegral_winCount (m : ℕ) (r : ℝ) :
    ∫⁻ ω, winCount M m r ω ∂(M.cutLaw r)
      = ((M.ball r).ncard : ℝ≥0∞) *
          (M.cutLaw r) {ω : Config M.V | (m : ℝ≥0∞) ≤ clusterVolIn ω 0 (M.ball (2 * r))} := by
  classical
  simp only [winCount]
  rw [lintegral_finsetSum]
  · rw [Finset.sum_congr rfl (g := fun _ => (M.cutLaw r)
        {ω : Config M.V | (m : ℝ≥0∞) ≤ clusterVolIn ω 0 (M.ball (2 * r))})]
    · rw [Finset.sum_const, nsmul_eq_mul]
      congr 1
      rw [← Set.ncard_eq_toFinset_card (M.ball r) (M.finite_ball r)]
    · intro x _
      have hmeas : MeasurableSet
          {ω : Config M.V | (m : ℝ≥0∞) ≤ clusterVolIn ω x (ballAt M x (2 * r))} :=
        measurableSet_le measurable_const (measurable_clusterVolIn x _)
      have hfun : (fun ω => (if (m : ℝ≥0∞) ≤ clusterVolIn ω x (ballAt M x (2 * r)) then
            (1 : ℝ≥0∞) else 0))
          = {ω : Config M.V | (m : ℝ≥0∞) ≤ clusterVolIn ω x (ballAt M x (2 * r))}.indicator
              (fun _ => (1 : ℝ≥0∞)) := by
        funext ω
        by_cases h : (m : ℝ≥0∞) ≤ clusterVolIn ω x (ballAt M x (2 * r))
        · simp [h]
        · simp [h]
      rw [hfun]
      exact (lintegral_indicator_one hmeas).trans (measure_clusterVolIn_ballAt_eq M m r x)
  · intro b _
    exact Measurable.ite
      (measurableSet_le measurable_const (measurable_clusterVolIn b _))
      measurable_const measurable_const


/-! ## §5 The median gives the averaging hypothesis at the model's ball -/

theorem mr_measure_exists (r : ℝ) (hr : 0 ≤ r) :
    ENNReal.ofReal (Real.exp (-1)) ≤
      (M.cutLaw r) {ω : Config M.V | ∃ w ∈ M.ball r,
        (((M.Mr r) - 1 : ℕ) : ℝ≥0∞) ≤ clusterVolIn ω w (M.ball r)} := by
  classical
  set μ := M.cutLaw r
  set W := E1Sign.ballF M r
  have hW : (W : Set M.V) = M.ball r := PercLib.CriticalLRP.CaseTwo.coe_ballF M r
  have hMr1 : 1 ≤ M.Mr r := by
    rw [PercLib.CriticalLRP.CaseTwo.Mr_eq_edianMaxVol M r]
    exact one_le_edianMaxVol _ _
  have hMr : M.Mr r = edianMaxVol μ W (exists_edianMaxVol W) :=
    PercLib.CriticalLRP.CaseTwo.Mr_eq_edianMaxVol M r
  rcases Nat.lt_or_ge (M.Mr r) 2 with hsmall | hbig
  · have h1 : M.Mr r = 1 := by omega
    have huniv : {ω : Config M.V | ∃ w ∈ M.ball r,
        (((M.Mr r) - 1 : ℕ) : ℝ≥0∞) ≤ clusterVolIn ω w (M.ball r)} = univ := by
      ext ω
      refine iff_true_intro ⟨0, PercLib.CriticalLRP.CaseTwo.zero_mem_ball M hr, ?_⟩
      rw [h1]
      simp
    rw [huniv, measure_univ]
    exact le_of_lt (ENNReal.ofReal_lt_one.mpr (by
      rw [Real.exp_lt_one_iff]
      norm_num))
  · have hm : 1 ≤ M.Mr r - 1 := by omega
    have hlt : M.Mr r - 1 < edianMaxVol μ W (exists_edianMaxVol W) := by omega
    have hmin := edianOf_min (μ := μ) (X := fun ω => clusterMaxVol ω W)
      (hex := exists_edianMaxVol W) hlt
    refine le_trans (le_of_lt hmin) (measure_mono ?_)
    intro ω hω
    obtain ⟨w, hw, hle⟩ := (le_clusterMaxVol_iff hm W ω).mp hω
    refine ⟨w, ?_, ?_⟩
    · exact hW ▸ Finset.mem_coe.mpr hw
    · rw [hW] at hle
      exact hle

/-! ## §6 The averaging bound at the model's ball -/

theorem averaging_bound_ball (m : ℕ) (r : ℝ)
    (hA : ENNReal.ofReal (Real.exp (-1)) ≤
      (M.cutLaw r) {ω : Config M.V | ∃ w ∈ M.ball r, (m : ℝ≥0∞) ≤ clusterVolIn ω w (M.ball r)}) :
    ENNReal.ofReal (Real.exp (-1) * (m : ℝ)) ≤
      ENNReal.ofReal ((M.ball r).ncard : ℝ) *
        (M.cutLaw r) {ω : Config M.V | (m : ℝ≥0∞) ≤ clusterVolIn ω 0 (M.ball (2 * r))} := by
  classical
  set μ := M.cutLaw r
  set A : Set (Config M.V) :=
    {ω | ∃ w ∈ M.ball r, (m : ℝ≥0∞) ≤ clusterVolIn ω w (M.ball r)} with hAdef
  have hAmeas : MeasurableSet A := by
    have hset : A = ⋃ w ∈ (M.finite_ball r).toFinset,
        {ω : Config M.V | (m : ℝ≥0∞) ≤ clusterVolIn ω w (M.ball r)} := by
      ext ω
      simp only [hAdef, Set.mem_ofPred_eq, Set.mem_iUnion]
      constructor
      · rintro ⟨w, hw, hle⟩
        exact ⟨w, (M.finite_ball r).mem_toFinset.mpr hw, hle⟩
      · rintro ⟨w, hw, hle⟩
        exact ⟨w, (M.finite_ball r).mem_toFinset.mp hw, hle⟩
    rw [hset]
    exact Finset.measurableSet_biUnion _ fun w _ =>
      measurableSet_le measurable_const (measurable_clusterVolIn w _)
  have hpoint : ∀ ω : Config M.V,
      (m : ℝ≥0∞) * A.indicator (fun _ => (1 : ℝ≥0∞)) ω ≤ winCount M m r ω := by
    intro ω
    by_cases hω : ω ∈ A
    · rw [Set.indicator_of_mem hω, mul_one]
      exact le_winCount M hω
    · rw [Set.indicator_of_notMem hω, mul_zero]
      exact bot_le
  calc ENNReal.ofReal (Real.exp (-1) * (m : ℝ))
      = (m : ℝ≥0∞) * ENNReal.ofReal (Real.exp (-1)) := by
        rw [ENNReal.ofReal_mul (Real.exp_pos (-1)).le, ENNReal.ofReal_natCast]
        ring
    _ ≤ (m : ℝ≥0∞) * μ A := by
        rw [hAdef]
        gcongr
    _ = ∫⁻ ω, (m : ℝ≥0∞) * A.indicator (fun _ => (1 : ℝ≥0∞)) ω ∂μ := by
        rw [lintegral_const_mul _ (measurable_const.indicator hAmeas)]
        rw [show ∫⁻ a, A.indicator (fun _ => (1 : ℝ≥0∞)) a ∂μ = μ A from
          lintegral_indicator_one hAmeas]
    _ ≤ ∫⁻ ω, winCount M m r ω ∂μ := lintegral_mono hpoint
    _ = ENNReal.ofReal ((M.ball r).ncard : ℝ) *
          μ {ω : Config M.V | (m : ℝ≥0∞) ≤ clusterVolIn ω 0 (M.ball (2 * r))} := by
        rw [lintegral_winCount M m r, ENNReal.ofReal_natCast]

/-! ## §7 The windowed Lemma I.2.6 at the model's own ball -/

theorem mr_sq_le_inter (r : ℝ) (hr : 0 ≤ r) :
    ENNReal.ofReal (((M.Mr r : ℝ) - 1) ^ 2) ≤
      ENNReal.ofReal (Real.exp 1 * ((M.ball r).ncard : ℝ)) *
        ∫⁻ ω, clusterVolIn ω 0 (M.ball (2 * r)) ∂(M.cutLaw r) := by
  classical
  set μ := M.cutLaw r
  set m : ℕ := M.Mr r - 1 with hm
  set q : ℝ≥0∞ := μ {ω : Config M.V | (m : ℝ≥0∞) ≤ clusterVolIn ω 0 (M.ball (2 * r))} with hq
  set E : ℝ≥0∞ := ∫⁻ ω, clusterVolIn ω 0 (M.ball (2 * r)) ∂μ with hE
  have hMr1 : 1 ≤ M.Mr r := by
    rw [PercLib.CriticalLRP.CaseTwo.Mr_eq_edianMaxVol M r]
    exact one_le_edianMaxVol _ _
  have hmcast : (m : ℝ) + 1 = (M.Mr r : ℝ) := by
    have h : m + 1 = M.Mr r := by
      rw [hm]
      exact Nat.sub_add_cancel hMr1
    exact_mod_cast h
  have hmr : (m : ℝ) = (M.Mr r : ℝ) - 1 := by linarith
  -- `q` is at least `m/(e |B_r|)`, and `E` is at least `m q`
  have h1 : ENNReal.ofReal (Real.exp (-1) * (m : ℝ)) ≤
      ENNReal.ofReal ((M.ball r).ncard : ℝ) * q :=
    averaging_bound_ball M m r (mr_measure_exists M r hr)
  have h2 : (m : ℝ≥0∞) * q ≤ E := by
    have hmeas : MeasurableSet
        {ω : Config M.V | (m : ℝ≥0∞) ≤ clusterVolIn ω 0 (M.ball (2 * r))} :=
      measurableSet_le measurable_const (measurable_clusterVolIn 0 _)
    have hpoint : ∀ ω : Config M.V,
        (m : ℝ≥0∞) * {ω : Config M.V | (m : ℝ≥0∞) ≤ clusterVolIn ω 0 (M.ball (2 * r))}.indicator
          (fun _ => (1 : ℝ≥0∞)) ω ≤ clusterVolIn ω 0 (M.ball (2 * r)) := by
      intro ω
      by_cases hω : ω ∈ {ω : Config M.V | (m : ℝ≥0∞) ≤ clusterVolIn ω 0 (M.ball (2 * r))}
      · rw [Set.indicator_of_mem hω, mul_one]
        exact hω
      · rw [Set.indicator_of_notMem hω, mul_zero]
        exact bot_le
    calc (m : ℝ≥0∞) * q
        = ∫⁻ ω, (m : ℝ≥0∞) *
            {ω : Config M.V | (m : ℝ≥0∞) ≤ clusterVolIn ω 0 (M.ball (2 * r))}.indicator
              (fun _ => (1 : ℝ≥0∞)) ω ∂μ := by
          rw [hq, lintegral_const_mul _ (measurable_const.indicator hmeas)]
          rw [show ∫⁻ a, {ω : Config M.V | (m : ℝ≥0∞) ≤ clusterVolIn ω 0 (M.ball (2 * r))}.indicator
              (fun _ => (1 : ℝ≥0∞)) a ∂μ
              = μ {ω : Config M.V | (m : ℝ≥0∞) ≤ clusterVolIn ω 0 (M.ball (2 * r))} from
            lintegral_indicator_one hmeas]
      _ ≤ ∫⁻ ω, clusterVolIn ω 0 (M.ball (2 * r)) ∂μ := lintegral_mono hpoint
      _ = E := rfl
  -- multiply the two
  have h3 : ENNReal.ofReal (Real.exp (-1) * (m : ℝ) ^ 2) ≤
      ENNReal.ofReal ((M.ball r).ncard : ℝ) * E := by
    have hmul : ENNReal.ofReal (Real.exp (-1) * (m : ℝ)) * (m : ℝ≥0∞)
        = ENNReal.ofReal (Real.exp (-1) * (m : ℝ) ^ 2) := by
      rw [← ENNReal.ofReal_natCast m, ← ENNReal.ofReal_mul (by positivity)]
      ring_nf
    rw [← hmul]
    calc ENNReal.ofReal (Real.exp (-1) * (m : ℝ)) * (m : ℝ≥0∞)
        ≤ (ENNReal.ofReal ((M.ball r).ncard : ℝ) * q) * (m : ℝ≥0∞) := by
          gcongr
      _ = ENNReal.ofReal ((M.ball r).ncard : ℝ) * ((m : ℝ≥0∞) * q) := by ring
      _ ≤ ENNReal.ofReal ((M.ball r).ncard : ℝ) * E := by gcongr
  -- remove the `e^{-1}`
  have h4 : ENNReal.ofReal ((m : ℝ) ^ 2) ≤
      ENNReal.ofReal (Real.exp 1 * ((M.ball r).ncard : ℝ)) * E := by
    have he : (0 : ℝ) < Real.exp 1 := Real.exp_pos 1
    have hfac : Real.exp 1 * (Real.exp (-1) * (m : ℝ) ^ 2) = (m : ℝ) ^ 2 := by
      rw [← mul_assoc, Real.exp_neg]
      field_simp
    calc ENNReal.ofReal ((m : ℝ) ^ 2)
        = ENNReal.ofReal (Real.exp 1) * ENNReal.ofReal (Real.exp (-1) * (m : ℝ) ^ 2) := by
          rw [← ENNReal.ofReal_mul he.le, hfac]
      _ ≤ ENNReal.ofReal (Real.exp 1) *
            (ENNReal.ofReal ((M.ball r).ncard : ℝ) * E) := by gcongr
      _ = ENNReal.ofReal (Real.exp 1 * ((M.ball r).ncard : ℝ)) * E := by
          rw [ENNReal.ofReal_mul he.le]
          ring
  rwa [hmr] at h4



/-! ## §8 The windowed first moment of the cutoff law -/

theorem lintegral_clusterVolIn_ball_eq_sum (r : ℝ) :
    ∫⁻ ω, clusterVolIn ω (0 : M.V) (M.ball (2 * r)) ∂(M.cutLaw r)
      = ∑ x ∈ (M.finite_ball (2 * r)).toFinset, M.cutTwoPointE r 0 x := by
  classical
  set μ := M.cutLaw r
  set F := (M.finite_ball (2 * r)).toFinset with hF
  set W : Set M.V := M.ball (2 * r) with hW
  have hFcoe : (F : Set M.V) = W := by
    rw [hF, hW]
    exact (M.finite_ball (2 * r)).coe_toFinset
  have hind : ∀ ω : Config M.V, clusterVolIn ω (0 : M.V) W
      = ∑ x ∈ F, (cluster ω (0 : M.V) ∩ W).indicator (fun _ => (1 : ℝ≥0∞)) x := by
    intro ω
    rw [clusterVolIn_eq_tsum]
    refine tsum_eq_sum ?_
    intro x hx
    have hx' : x ∉ W := by
      rw [← hFcoe]
      exact fun hmem => hx (by rwa [hF] at hmem)
    exact Set.indicator_of_notMem (fun hh => hx' hh.2) _
  calc ∫⁻ ω, clusterVolIn ω (0 : M.V) W ∂μ
      = ∫⁻ ω, ∑ x ∈ F, (cluster ω (0 : M.V) ∩ W).indicator (fun _ => (1 : ℝ≥0∞)) x ∂μ := by
        exact lintegral_congr hind
    _ = ∑ x ∈ F, ∫⁻ ω, (cluster ω (0 : M.V) ∩ W).indicator (fun _ => (1 : ℝ≥0∞)) x ∂μ := by
        rw [lintegral_finsetSum]
        intro b _
        have hmeas : MeasurableSet {ω : Config M.V | (cluster ω (0 : M.V) ∩ W) b} := by
          by_cases hb : b ∈ W
          · have hset : {ω : Config M.V | (cluster ω (0 : M.V) ∩ W) b}
                = {ω : Config M.V | b ∈ cluster ω (0 : M.V)} := by
              ext ω
              exact ⟨fun h => h.1, fun h => ⟨h, hb⟩⟩
            rw [hset]
            exact measurableSet_cluster_mem 0 b
          · have hset : {ω : Config M.V | (cluster ω (0 : M.V) ∩ W) b}
                = (∅ : Set (Config M.V)) := by
              ext ω
              exact ⟨fun h => absurd h.2 hb, fun h => h.elim⟩
            rw [hset]
            exact MeasurableSet.empty
        exact measurable_const.indicator hmeas
    _ = ∑ x ∈ F, M.cutTwoPointE r 0 x := by
        refine Finset.sum_congr rfl fun x hx => ?_
        have hxW : x ∈ W := by
          rw [← hFcoe]
          exact hx
        have hmeas : MeasurableSet {ω : Config M.V | x ∈ cluster ω (0 : M.V)} :=
          measurableSet_cluster_mem 0 x
        have hfun : (fun ω => (cluster ω (0 : M.V) ∩ W).indicator (fun _ => (1 : ℝ≥0∞)) x)
            = {ω : Config M.V | x ∈ cluster ω (0 : M.V)}.indicator (fun _ => (1 : ℝ≥0∞)) := by
          funext ω
          by_cases h : x ∈ cluster ω (0 : M.V)
          · have hmem : ω ∈ {ω : Config M.V | x ∈ cluster ω (0 : M.V)} := h
            rw [Set.indicator_of_mem (Set.mem_inter h hxW), Set.indicator_of_mem hmem]
          · have hmem : ω ∉ {ω : Config M.V | x ∈ cluster ω (0 : M.V)} := h
            rw [Set.indicator_of_notMem (fun hh => h hh.1), Set.indicator_of_notMem hmem]
        rw [hfun]
        rw [show ∫⁻ a, {ω : Config M.V | x ∈ cluster ω (0 : M.V)}.indicator
              (fun _ => (1 : ℝ≥0∞)) a ∂μ
              = μ {ω : Config M.V | x ∈ cluster ω (0 : M.V)} from
            lintegral_indicator_one hmeas]
        simp only [SourceModelData.cutTwoPointE, mem_cluster_iff]
        rfl

theorem interVol_le_ofReal_sum_tau (r : ℝ) :
    ∫⁻ ω, clusterVolIn ω (0 : M.V) (M.ball (2 * r)) ∂(M.cutLaw r)
      ≤ ENNReal.ofReal (∑ x ∈ (M.finite_ball (2 * r)).toFinset, M.tau x) := by
  rw [lintegral_clusterVolIn_ball_eq_sum M r]
  rw [ENNReal.ofReal_sum_of_nonneg (fun x _ => M.tau_nonneg x)]
  refine Finset.sum_le_sum fun x _ => ?_
  rw [M.cutTwoPointE_eq_ofReal, ENNReal.ofReal_le_ofReal_iff (M.tau_nonneg x)]
  have h := M.cutTwoPoint_le_twoPoint r 0 x
  rwa [← M.tau_eq_twoPoint x] at h

theorem interVol_toReal_le_sum_tau (r : ℝ) :
    (∫⁻ ω, clusterVolIn ω (0 : M.V) (M.ball (2 * r)) ∂(M.cutLaw r)).toReal
      ≤ ∑ x ∈ (M.finite_ball (2 * r)).toFinset, M.tau x := by
  calc (∫⁻ ω, clusterVolIn ω (0 : M.V) (M.ball (2 * r)) ∂(M.cutLaw r)).toReal
      ≤ (ENNReal.ofReal (∑ x ∈ (M.finite_ball (2 * r)).toFinset, M.tau x)).toReal :=
        ENNReal.toReal_mono ENNReal.ofReal_ne_top (interVol_le_ofReal_sum_tau M r)
    _ = ∑ x ∈ (M.finite_ball (2 * r)).toFinset, M.tau x :=
        ENNReal.toReal_ofReal (Finset.sum_nonneg fun x _ => M.tau_nonneg x)

/-! ## §9 The median bound and the hydrodynamic condition -/

theorem ball_ncard_eventually_le (M : SourceModelData) :
    ∀ᶠ r : ℝ in atTop, ((M.ball r).ncard : ℝ) ≤ 2 * r ^ M.d := by
  have hne : ∀ᶠ r : ℝ in atTop, (fun r : ℝ => r ^ M.d) r ≠ 0 := by
    filter_upwards [eventually_ge_atTop (1 : ℝ)] with r hr
    exact ne_of_gt (by positivity)
  have ht : Tendsto (fun r : ℝ => ((M.ball r).ncard : ℝ) / r ^ M.d) atTop (𝓝 1) :=
    (Asymptotics.isEquivalent_iff_tendsto_one hne).mp M.ball_count
  filter_upwards [ht.eventually (eventually_lt_nhds (by norm_num : (1 : ℝ) < 2)),
    eventually_ge_atTop (1 : ℝ)] with r hr hr1
  have hpos : (0 : ℝ) < r ^ M.d := by positivity
  rw [div_lt_iff₀ hpos] at hr
  linarith

/-- **The median bound under Case 3 of (HD).**  `M_r` is at most a constant times
`r^{(d+α)/2} (log r)^{-1/2}`; the logarithm is exactly the gain supplied by the log
correction in (HD)(3). -/
theorem mr_le_log_sqrt (h : M.Case3HD) (Kτ : ℝ) (hKτ : 0 < Kτ)
    (hτsum : ∀ r : ℝ, 2 ≤ r →
      ∑ x ∈ (M.finite_ball (2 * r)).toFinset, M.tau x ≤ Kτ * r ^ 2 * (Real.log r)⁻¹) :
    ∃ C : ℝ, 0 < C ∧ ∀ᶠ r : ℝ in atTop,
      ((M.Mr r : ℝ) - 1) ^ 2 ≤ C * r ^ ((M.d : ℝ) + M.α) * (Real.log r)⁻¹ := by
  have hdR : (M.d : ℝ) = 6 := by exact_mod_cast h.1
  have hαR : M.α = 2 := h.2.1
  refine ⟨Real.exp 1 * 2 * Kτ, by positivity, ?_⟩
  filter_upwards [ball_ncard_eventually_le M, eventually_ge_atTop (2 : ℝ)] with r hcard hr
  have hr0 : (0 : ℝ) < r := by linarith
  have hlogr : (0 : ℝ) < Real.log r := Real.log_pos (by linarith)
  have hsum_nonneg : (0 : ℝ) ≤ ∑ x ∈ (M.finite_ball (2 * r)).toFinset, M.tau x :=
    Finset.sum_nonneg fun x _ => M.tau_nonneg x
  have hEne : (∫⁻ ω, clusterVolIn ω (0 : M.V) (M.ball (2 * r)) ∂(M.cutLaw r)) ≠ ⊤ :=
    ne_top_of_le_ne_top ENNReal.ofReal_ne_top (interVol_le_ofReal_sum_tau M r)
  have hEreal : (∫⁻ ω, clusterVolIn ω (0 : M.V) (M.ball (2 * r)) ∂(M.cutLaw r)).toReal
      ≤ Kτ * r ^ 2 * (Real.log r)⁻¹ := by
    refine (ENNReal.toReal_mono ENNReal.ofReal_ne_top (interVol_le_ofReal_sum_tau M r)).trans ?_
    rw [ENNReal.toReal_ofReal hsum_nonneg]
    exact hτsum r (by linarith)
  have h1 := mr_sq_le_inter M r hr0.le
  have hreal : ((M.Mr r : ℝ) - 1) ^ 2
      ≤ Real.exp 1 * ((M.ball r).ncard : ℝ) * (Kτ * r ^ 2 * (Real.log r)⁻¹) := by
    have hmono := ENNReal.toReal_mono
      (ENNReal.mul_ne_top ENNReal.ofReal_ne_top hEne) h1
    rw [ENNReal.toReal_mul, ENNReal.toReal_ofReal (by positivity),
      ENNReal.toReal_ofReal (by positivity)] at hmono
    exact hmono.trans (mul_le_mul_of_nonneg_left hEreal (by positivity))
  refine hreal.trans ?_
  have hrpow : r ^ ((M.d : ℝ) + M.α) = r ^ M.d * r ^ 2 := by
    rw [Real.rpow_add hr0, hαR]
    norm_num [Real.rpow_two]
  have h7 : Real.exp 1 * ((M.ball r).ncard : ℝ) * (Kτ * r ^ 2 * (Real.log r)⁻¹)
      ≤ Real.exp 1 * (2 * r ^ M.d) * (Kτ * r ^ 2 * (Real.log r)⁻¹) := by
    have hpos : (0 : ℝ) ≤ Kτ * r ^ 2 * (Real.log r)⁻¹ := by positivity
    have hle1 : Real.exp 1 * ((M.ball r).ncard : ℝ) ≤ Real.exp 1 * (2 * r ^ M.d) :=
      mul_le_mul_of_nonneg_left hcard (Real.exp_pos 1).le
    exact mul_le_mul_of_nonneg_right hle1 hpos
  refine h7.trans (le_of_eq ?_)
  rw [hrpow]
  ring

/-! ## §10 The hydrodynamic condition from Case 3 of (HD) -/

/-- **Corollary I.4.14 under Case 3 of (HD)** (Hutchcroft, arXiv:2508.18807v1, p. 42):
the log-corrected critical two-point bound implies the hydrodynamic condition
`M_r = o(r^{(d+α)/2})`.  The logarithm in (HD)(3) is what makes the estimate marginal:
without it one only obtains `M_r ⪯ r^{(d+α)/2}`, not `o`. -/
theorem hydro_of_case3HD (h : M.Case3HD) : Hydro M := by
  obtain ⟨Kτ, hKτ, hτsum⟩ := sum_tau_ball_le_of_case3 M h
  obtain ⟨C, hC, hCbound⟩ := mr_le_log_sqrt M h Kτ hKτ hτsum
  have hdR : (M.d : ℝ) = 6 := by exact_mod_cast h.1
  have hαR : M.α = 2 := h.2.1
  have hp : ((M.d : ℝ) + M.α) / 2 = 4 := by rw [hdR, hαR]; norm_num
  -- rewrite the target exponent to `4`
  have hexp : ∀ r : ℝ, r ^ (((M.d : ℝ) + M.α) / 2) = r ^ 4 := by
    intro r
    rw [hp]
    norm_num
  change Tendsto (fun r : ℝ => (M.Mr r : ℝ) / r ^ (((M.d : ℝ) + M.α) / 2)) atTop (𝓝 0)
  simp only [hexp]
  -- the ratio is squeezed between `0` and a vanishing upper bound
  have hupper : ∀ᶠ r : ℝ in atTop,
      (M.Mr r : ℝ) / r ^ 4 ≤ (r ^ 4)⁻¹ + Real.sqrt C * (Real.sqrt (Real.log r))⁻¹ := by
    filter_upwards [hCbound, eventually_ge_atTop (2 : ℝ)] with r hr hr2
    have hr0 : (0 : ℝ) < r := by linarith
    have hlog : (0 : ℝ) < Real.log r := Real.log_pos (by linarith)
    have hMr1 : (1 : ℝ) ≤ (M.Mr r : ℝ) := by
      have h1 : 1 ≤ M.Mr r := by
        rw [PercLib.CriticalLRP.CaseTwo.Mr_eq_edianMaxVol M r]
        exact PercLib.CriticalLRP.Percolation.one_le_edianMaxVol _ _
      exact_mod_cast h1
    have hpow8 : r ^ ((M.d : ℝ) + M.α) = r ^ 8 := by rw [hdR, hαR]; norm_num
    rw [hpow8] at hr
    have hr4 : (0 : ℝ) < r ^ 4 := by positivity
    -- the square root of the right-hand side
    have hroot : (M.Mr r : ℝ) - 1
        ≤ Real.sqrt C * (Real.sqrt (Real.log r))⁻¹ * r ^ 4 := by
      have hnn : (0 : ℝ) ≤ (M.Mr r : ℝ) - 1 := by linarith
      have hYnn : (0 : ℝ) ≤ Real.sqrt C * (Real.sqrt (Real.log r))⁻¹ * r ^ 4 := by positivity
      have hYsq : (Real.sqrt C * (Real.sqrt (Real.log r))⁻¹ * r ^ 4) ^ 2
          = C * r ^ 8 * (Real.log r)⁻¹ := by
        rw [mul_pow, mul_pow, inv_pow, Real.sq_sqrt hlog.le, Real.sq_sqrt hC.le]
        ring
      have hsq : ((M.Mr r : ℝ) - 1) ^ 2
          ≤ (Real.sqrt C * (Real.sqrt (Real.log r))⁻¹ * r ^ 4) ^ 2 := by
        rw [hYsq]
        exact hr
      have h := Real.sqrt_le_sqrt hsq
      rwa [Real.sqrt_sq hnn, Real.sqrt_sq hYnn] at h
    -- divide by `r ^ 4`
    rw [div_le_iff₀ hr4]
    have hkey : ((r ^ 4)⁻¹ + Real.sqrt C * (Real.sqrt (Real.log r))⁻¹) * r ^ 4
        = Real.sqrt C * (Real.sqrt (Real.log r))⁻¹ * r ^ 4 + 1 := by
      rw [add_mul, inv_mul_cancel₀ (ne_of_gt hr4)]
      ring
    rw [hkey]
    linarith
  -- the upper bound tends to zero
  have hlog : Tendsto (fun r : ℝ => Real.log r) atTop atTop := Real.tendsto_log_atTop
  have hsqrt : Tendsto (fun r : ℝ => Real.sqrt (Real.log r)) atTop atTop :=
    Real.tendsto_sqrt_atTop.comp hlog
  have hinv : Tendsto (fun r : ℝ => (Real.sqrt (Real.log r))⁻¹) atTop (𝓝 0) :=
    tendsto_inv_atTop_zero.comp hsqrt
  have hpow : Tendsto (fun r : ℝ => r ^ 4) atTop atTop :=
    tendsto_pow_atTop (by norm_num)
  have hinv4 : Tendsto (fun r : ℝ => (r ^ 4)⁻¹) atTop (𝓝 0) :=
    tendsto_inv_atTop_zero.comp hpow
  have hlim : Tendsto (fun r : ℝ => (r ^ 4)⁻¹ +
      Real.sqrt C * (Real.sqrt (Real.log r))⁻¹) atTop (𝓝 0) := by
    simpa using hinv4.add (hinv.const_mul (Real.sqrt C))
  refine tendsto_of_tendsto_of_tendsto_of_le_of_le' tendsto_const_nhds hlim ?_ ?_
  · filter_upwards with r
    exact div_nonneg (by positivity) (by positivity)
  · exact hupper

/-- **Quantitative form of the same chain.**  Under Case 3 of (HD) the edian satisfies
`M_r ≤ 1 + √C r^{(d+α)/2} (log r)^{-1/2}` eventually: the proof of Corollary I.4.14 gives
one half-power of logarithm, strictly more than the `o(r^{(d+α)/2})` of the source. -/
theorem mr_le_rpow_log (h : M.Case3HD) :
    ∃ C : ℝ, 0 < C ∧ ∀ᶠ r : ℝ in atTop,
      (M.Mr r : ℝ) ≤ 1 + Real.sqrt C * (Real.sqrt (Real.log r))⁻¹ * r ^ 4 := by
  obtain ⟨Kτ, hKτ, hτsum⟩ := sum_tau_ball_le_of_case3 M h
  obtain ⟨C, hC, hCbound⟩ := mr_le_log_sqrt M h Kτ hKτ hτsum
  have hdR : (M.d : ℝ) = 6 := by exact_mod_cast h.1
  have hαR : M.α = 2 := h.2.1
  refine ⟨C, hC, ?_⟩
  filter_upwards [hCbound, eventually_ge_atTop (2 : ℝ)] with r hr hr2
  have hr0 : (0 : ℝ) < r := by linarith
  have hlog : (0 : ℝ) < Real.log r := Real.log_pos (by linarith)
  have hpow8 : r ^ ((M.d : ℝ) + M.α) = r ^ 8 := by rw [hdR, hαR]; norm_num
  rw [hpow8] at hr
  have hMr1 : (1 : ℝ) ≤ (M.Mr r : ℝ) := by
    have h1 : 1 ≤ M.Mr r := by
      rw [PercLib.CriticalLRP.CaseTwo.Mr_eq_edianMaxVol M r]
      exact PercLib.CriticalLRP.Percolation.one_le_edianMaxVol _ _
    exact_mod_cast h1
  have hnn : (0 : ℝ) ≤ (M.Mr r : ℝ) - 1 := by linarith
  have hYnn : (0 : ℝ) ≤ Real.sqrt C * (Real.sqrt (Real.log r))⁻¹ * r ^ 4 := by positivity
  have hYsq : (Real.sqrt C * (Real.sqrt (Real.log r))⁻¹ * r ^ 4) ^ 2
      = C * r ^ 8 * (Real.log r)⁻¹ := by
    rw [mul_pow, mul_pow, inv_pow, Real.sq_sqrt hlog.le, Real.sq_sqrt hC.le]
    ring
  have hsq : ((M.Mr r : ℝ) - 1) ^ 2
      ≤ (Real.sqrt C * (Real.sqrt (Real.log r))⁻¹ * r ^ 4) ^ 2 := by
    rw [hYsq]
    exact hr
  have hroot : (M.Mr r : ℝ) - 1 ≤ Real.sqrt C * (Real.sqrt (Real.log r))⁻¹ * r ^ 4 := by
    have h := Real.sqrt_le_sqrt hsq
    rwa [Real.sqrt_sq hnn, Real.sqrt_sq hYnn] at h
  linarith


/-! ## §11 (HD) Case 2: the same route without the logarithmic correction -/

/-- `Wt e 0 r` is the pure power majorant `(1+r)^{-e}`. -/
theorem Wt_zero_log (e r : ℝ) :
    CriticalLRPConv.Wt e 0 r = (1 + r) ^ (-e) := by
  rw [CriticalLRPConv.Wt]
  have h0 : (-(0 : ℝ)) = 0 := by norm_num
  rw [h0, Real.rpow_zero, mul_one]

/-- **Case 2 pointwise majorant.**  If `d > 6` and `τ(x) ⪯ ‖x‖^{-d+2}` then `τ` is dominated
by the pure power profile `Wt (d-2) 0`. -/
theorem exists_abs_tau_le_Wt_of_case2 (hd : 6 < M.d) (C : ℝ) (hC : 0 < C)
    (hb : ∀ x y : M.V, x ≠ y → M.twoPoint M.betaCrit x y
      ≤ C * (M.S.ρ (toVec (x - y))) ^ (-(M.d : ℝ) + 2)) :
    ∃ K : ℝ, 0 < K ∧ ∀ z : M.V,
      |M.tau z| ≤ K * CriticalLRPConv.Wt ((M.d : ℝ) - 2) 0 (M.S.ρ (toVec z)) := by
  have he : (0 : ℝ) < (M.d : ℝ) - 2 := by
    have : (6 : ℝ) < (M.d : ℝ) := by exact_mod_cast hd
    linarith
  have hpow : (0 : ℝ) < (2 : ℝ) ^ ((M.d : ℝ) - 2) := Real.rpow_pos_of_pos (by norm_num) _
  have h5 : (0 : ℝ) < (5 : ℝ) ^ ((M.d : ℝ) - 2) := Real.rpow_pos_of_pos (by norm_num) _
  refine ⟨max ((5 : ℝ) ^ ((M.d : ℝ) - 2)) (C * (2 : ℝ) ^ ((M.d : ℝ) - 2)) + 1, ?_, ?_⟩
  · have := le_max_left ((5 : ℝ) ^ ((M.d : ℝ) - 2)) (C * (2 : ℝ) ^ ((M.d : ℝ) - 2))
    linarith
  · intro z
    have hr : (0 : ℝ) ≤ M.S.ρ (toVec z) := M.sρ_nonneg z
    have hK1 : (5 : ℝ) ^ ((M.d : ℝ) - 2) ≤
        max ((5 : ℝ) ^ ((M.d : ℝ) - 2)) (C * (2 : ℝ) ^ ((M.d : ℝ) - 2)) := le_max_left _ _
    have hK2 : C * (2 : ℝ) ^ ((M.d : ℝ) - 2) ≤
        max ((5 : ℝ) ^ ((M.d : ℝ) - 2)) (C * (2 : ℝ) ^ ((M.d : ℝ) - 2)) := le_max_right _ _
    rw [abs_of_nonneg (M.tau_nonneg z), Wt_zero_log]
    rcases le_or_gt (M.S.ρ (toVec z)) 4 with hle4 | hgt4
    · have h1 := M.tau_le_one z
      have h2 : (5 : ℝ) ^ (-((M.d : ℝ) - 2)) ≤ (1 + M.S.ρ (toVec z)) ^ (-((M.d : ℝ) - 2)) := by
        refine Real.rpow_le_rpow_of_nonpos (by linarith) ?_ (by linarith)
        linarith
      have h3 : (5 : ℝ) ^ (-((M.d : ℝ) - 2)) = ((5 : ℝ) ^ ((M.d : ℝ) - 2))⁻¹ :=
        Real.rpow_neg (by norm_num : (0 : ℝ) ≤ 5) _
      have h4 : (1 : ℝ) ≤ (5 : ℝ) ^ ((M.d : ℝ) - 2) * (5 : ℝ) ^ (-((M.d : ℝ) - 2)) := by
        rw [h3, mul_inv_cancel₀ (ne_of_gt h5)]
      calc M.tau z ≤ 1 := h1
        _ ≤ (5 : ℝ) ^ ((M.d : ℝ) - 2) * (5 : ℝ) ^ (-((M.d : ℝ) - 2)) := h4
        _ ≤ (5 : ℝ) ^ ((M.d : ℝ) - 2) * (1 + M.S.ρ (toVec z)) ^ (-((M.d : ℝ) - 2)) :=
            mul_le_mul_of_nonneg_left h2 (le_of_lt h5)
        _ ≤ (max ((5 : ℝ) ^ ((M.d : ℝ) - 2)) (C * (2 : ℝ) ^ ((M.d : ℝ) - 2)) + 1) *
              (1 + M.S.ρ (toVec z)) ^ (-((M.d : ℝ) - 2)) := by
            refine mul_le_mul_of_nonneg_right ?_ (by positivity)
            linarith
    · -- far region: `ρz > 4`
      have hpos : (0 : ℝ) < M.S.ρ (toVec z) := by linarith
      have hzne : z ≠ 0 := by
        intro h0
        rw [h0] at hgt4
        have hto : toVec (0 : M.V) = (0 : Fin M.d → ℝ) := by
          funext i
          simp [toVec]
        rw [hto, M.S.ρ_zero] at hgt4
        linarith
      have hb' := hb z 0 hzne
      simp only [sub_zero] at hb'
      have hmono : (1 + M.S.ρ (toVec z)) ≤ 2 * M.S.ρ (toVec z) := by linarith
      have hp : (2 * M.S.ρ (toVec z)) ^ (-((M.d : ℝ) - 2))
          ≤ (1 + M.S.ρ (toVec z)) ^ (-((M.d : ℝ) - 2)) :=
        Real.rpow_le_rpow_of_nonpos (by linarith) hmono (by linarith)
      have hsplit : (2 * M.S.ρ (toVec z)) ^ (-((M.d : ℝ) - 2))
          = (2 : ℝ) ^ (-((M.d : ℝ) - 2)) * (M.S.ρ (toVec z)) ^ (-((M.d : ℝ) - 2)) :=
        Real.mul_rpow (by norm_num) hpos.le
      have h2inv : (2 : ℝ) ^ (-((M.d : ℝ) - 2)) = ((2 : ℝ) ^ ((M.d : ℝ) - 2))⁻¹ :=
        Real.rpow_neg (by norm_num : (0 : ℝ) ≤ 2) _
      have hexp : -(M.d : ℝ) + 2 = -((M.d : ℝ) - 2) := by ring
      have hsym : M.tau z = M.twoPoint M.betaCrit z 0 := by
        rw [M.tau_eq_twoPoint z, M.twoPoint_symm M.betaCrit 0 z]
      calc M.tau z = M.twoPoint M.betaCrit z 0 := hsym
        _ ≤ C * (M.S.ρ (toVec z)) ^ (-(M.d : ℝ) + 2) := hb'
        _ = C * (2 : ℝ) ^ ((M.d : ℝ) - 2) * ((2 : ℝ) ^ (-((M.d : ℝ) - 2)) *
              (M.S.ρ (toVec z)) ^ (-((M.d : ℝ) - 2))) := by
            rw [hexp, h2inv]
            field_simp
        _ ≤ C * (2 : ℝ) ^ ((M.d : ℝ) - 2) * (1 + M.S.ρ (toVec z)) ^ (-((M.d : ℝ) - 2)) := by
            refine mul_le_mul_of_nonneg_left ?_ (by positivity)
            rw [← hsplit]
            exact hp
        _ ≤ (max ((5 : ℝ) ^ ((M.d : ℝ) - 2)) (C * (2 : ℝ) ^ ((M.d : ℝ) - 2)) + 1) *
              (1 + M.S.ρ (toVec z)) ^ (-((M.d : ℝ) - 2)) := by
            refine mul_le_mul_of_nonneg_right ?_ (by positivity)
            linarith

/-- The shell constant of the `a = 2`, `c = 0` (log-free) ball-shell estimate. -/
noncomputable def shellConst2 (M : SourceModelData) : ℝ :=
  (2 : ℝ) ^ (2 : ℝ) * (CriticalLRPConv.srcCountConst M.S *
    (1 + ((M.d : ℝ) - 2 + 2 * ((0 : ℝ) + 1)) * CriticalLRPConv.coreConst 2 0))

theorem shellConst2_pos (M : SourceModelData) : 0 < shellConst2 M := by
  have hu : 0 < CriticalLRPConv.srcLowerUnit M.S :=
    CriticalLRPConv.srcLowerUnit_pos M.S M.hd
  have hbase : (0 : ℝ) < 3 / CriticalLRPConv.srcLowerUnit M.S + 3 := by positivity
  have hcount : 0 < CriticalLRPConv.srcCountConst M.S := by
    rw [CriticalLRPConv.srcCountConst]
    exact Real.rpow_pos_of_pos hbase _
  have hcore : 0 < CriticalLRPConv.coreConst 2 0 := CriticalLRPConv.coreConst_pos 2 0
  have h1 : (0 : ℝ) < 1 + ((M.d : ℝ) - 2 + 2 * ((0 : ℝ) + 1)) *
      CriticalLRPConv.coreConst 2 0 := by nlinarith
  have hpow : (0 : ℝ) < (2 : ℝ) ^ (2 : ℝ) := Real.rpow_pos_of_pos (by norm_num) _
  unfold shellConst2
  positivity

/-- **The Case-2 lattice kernel sum.**  Under `d > 6` and the log-free pointwise bound
`τ(x) ⪯ ‖x‖^{-d+2}` the ball sum grows like `r^2` — no logarithm is lost, and none is gained. -/
theorem sum_tau_ball_le_of_case2 (hd : 6 < M.d) (C : ℝ) (hC : 0 < C)
    (hb : ∀ x y : M.V, x ≠ y → M.twoPoint M.betaCrit x y
      ≤ C * (M.S.ρ (toVec (x - y))) ^ (-(M.d : ℝ) + 2)) :
    ∃ K : ℝ, 0 < K ∧ ∀ r : ℝ, 2 ≤ r →
      ∑ x ∈ (M.finite_ball (2 * r)).toFinset, M.tau x ≤ K * r ^ 2 := by
  obtain ⟨K₀, hK₀, hτ⟩ := exists_abs_tau_le_Wt_of_case2 M hd C hC hb
  have hdR : (2 : ℝ) < (M.d : ℝ) := by
    have h : (2 : ℕ) < M.d := by omega
    exact_mod_cast h
  refine ⟨K₀ * shellConst2 M * 9, by have := shellConst2_pos M; positivity, ?_⟩
  intro r hr
  have hr0 : (0 : ℝ) < r := by linarith
  have hstep1 : ∑ x ∈ (M.finite_ball (2 * r)).toFinset, M.tau x
      ≤ K₀ * ∑ x ∈ (M.finite_ball (2 * r)).toFinset,
          CriticalLRPConv.Wt ((M.d : ℝ) - 2) 0 (M.S.ρ (toVec x)) := by
    rw [Finset.mul_sum]
    refine Finset.sum_le_sum fun x _ => ?_
    simpa only [abs_of_nonneg (M.tau_nonneg x)] using hτ x
  have hshell : ∑ x ∈ (M.finite_ball (2 * r)).toFinset,
        CriticalLRPConv.Wt ((M.d : ℝ) - 2) 0 (M.S.ρ (toVec x))
      ≤ shellConst2 M * ((1 + 2 * r) ^ (2 : ℝ) *
          CriticalLRPConv.LamR (2 * r) ^ (-(0 : ℝ))) :=
    CriticalLRPConv.srcNorm_ball_shell_bound M.S M.hd
      (a := 2) (c := 0) (S₀ := 2 * r) (F := (M.finite_ball (2 * r)).toFinset)
      (by norm_num) (by linarith) (by norm_num) (by linarith)
      (fun y hy => by
        have hmem : y ∈ M.ball (2 * r) := by
          rw [← (M.finite_ball (2 * r)).coe_toFinset]
          exact hy
        exact hmem)
  have hLam : CriticalLRPConv.LamR (2 * r) ^ (-(0 : ℝ)) = 1 := by
    rw [show (-(0 : ℝ)) = 0 from by norm_num, Real.rpow_zero]
  have h9 : (1 + 2 * r) ^ (2 : ℝ) ≤ 9 * r ^ 2 := by
    have h2 : (1 + 2 * r : ℝ) ≤ 3 * r := by linarith
    have h3 : (0 : ℝ) < 1 + 2 * r := by linarith
    have h4 : (1 + 2 * r) ^ (2 : ℝ) ≤ (3 * r) ^ (2 : ℝ) :=
      Real.rpow_le_rpow h3.le h2 (by norm_num)
    have h5 : (3 * r) ^ (2 : ℝ) = 9 * r ^ 2 := by
      rw [Real.mul_rpow (by norm_num) hr0.le]
      norm_num
    rw [h5] at h4
    exact h4
  have hK : 0 < K₀ * shellConst2 M := by
    have := shellConst2_pos M
    positivity
  calc ∑ x ∈ (M.finite_ball (2 * r)).toFinset, M.tau x
      ≤ K₀ * ∑ x ∈ (M.finite_ball (2 * r)).toFinset,
          CriticalLRPConv.Wt ((M.d : ℝ) - 2) 0 (M.S.ρ (toVec x)) := hstep1
    _ ≤ K₀ * (shellConst2 M * ((1 + 2 * r) ^ (2 : ℝ) *
          CriticalLRPConv.LamR (2 * r) ^ (-(0 : ℝ)))) := by
        exact mul_le_mul_of_nonneg_left hshell hK₀.le
    _ = K₀ * shellConst2 M * (1 + 2 * r) ^ (2 : ℝ) := by
        rw [hLam]; ring
    _ ≤ K₀ * shellConst2 M * (9 * r ^ 2) := by
        refine mul_le_mul_of_nonneg_left h9 hK.le
    _ = K₀ * shellConst2 M * 9 * r ^ 2 := by ring

/-- **The Case-2 median bound**: `(M_r - 1)^2 ⪯ r^{d+2}`. -/
theorem mr_sq_le_rpow_of_case2 (hd : 6 < M.d) (C : ℝ) (hC : 0 < C)
    (hb : ∀ x y : M.V, x ≠ y → M.twoPoint M.betaCrit x y
      ≤ C * (M.S.ρ (toVec (x - y))) ^ (-(M.d : ℝ) + 2)) :
    ∃ C' : ℝ, 0 < C' ∧ ∀ᶠ r : ℝ in atTop,
      ((M.Mr r : ℝ) - 1) ^ 2 ≤ C' * r ^ ((M.d : ℝ) + 2) := by
  obtain ⟨Kτ, hKτ, hτsum⟩ := sum_tau_ball_le_of_case2 M hd C hC hb
  refine ⟨Real.exp 1 * 2 * Kτ, by positivity, ?_⟩
  filter_upwards [ball_ncard_eventually_le M, eventually_ge_atTop (2 : ℝ)] with r hcard hr
  have hr0 : (0 : ℝ) < r := by linarith
  have hsum_nonneg : (0 : ℝ) ≤ ∑ x ∈ (M.finite_ball (2 * r)).toFinset, M.tau x :=
    Finset.sum_nonneg fun x _ => M.tau_nonneg x
  have hEne : (∫⁻ ω, clusterVolIn ω (0 : M.V) (M.ball (2 * r)) ∂(M.cutLaw r)) ≠ ⊤ :=
    ne_top_of_le_ne_top ENNReal.ofReal_ne_top (interVol_le_ofReal_sum_tau M r)
  have hEreal : (∫⁻ ω, clusterVolIn ω (0 : M.V) (M.ball (2 * r)) ∂(M.cutLaw r)).toReal
      ≤ Kτ * r ^ 2 := by
    refine (ENNReal.toReal_mono ENNReal.ofReal_ne_top (interVol_le_ofReal_sum_tau M r)).trans ?_
    rw [ENNReal.toReal_ofReal hsum_nonneg]
    exact hτsum r (by linarith)
  have h1 := mr_sq_le_inter M r hr0.le
  have hreal : ((M.Mr r : ℝ) - 1) ^ 2
      ≤ Real.exp 1 * ((M.ball r).ncard : ℝ) * (Kτ * r ^ 2) := by
    have hmono := ENNReal.toReal_mono
      (ENNReal.mul_ne_top ENNReal.ofReal_ne_top hEne) h1
    rw [ENNReal.toReal_mul, ENNReal.toReal_ofReal (by positivity),
      ENNReal.toReal_ofReal (by positivity)] at hmono
    exact hmono.trans (mul_le_mul_of_nonneg_left hEreal (by positivity))
  refine hreal.trans ?_
  have hrpow : r ^ ((M.d : ℝ) + 2) = r ^ M.d * r ^ 2 := by
    rw [Real.rpow_add hr0]
    norm_num
  have h7 : Real.exp 1 * ((M.ball r).ncard : ℝ) * (Kτ * r ^ 2)
      ≤ Real.exp 1 * (2 * r ^ M.d) * (Kτ * r ^ 2) := by
    have hpos : (0 : ℝ) ≤ Kτ * r ^ 2 := by positivity
    exact mul_le_mul_of_nonneg_right
      (mul_le_mul_of_nonneg_left hcard (Real.exp_pos 1).le) hpos
  refine h7.trans (le_of_eq ?_)
  rw [hrpow]
  ring

/-- A general power-law squeeze: `M_r ⪯ r^β` with `β < γ` gives `M_r / r^γ → 0`. -/
theorem tendsto_ratio_of_pow_bound {A β γ : ℝ} (hγ : 0 < γ) (hβγ : β < γ)
    (h : ∀ᶠ r : ℝ in atTop, (M.Mr r : ℝ) ≤ 1 + A * r ^ β) :
    Tendsto (fun r : ℝ => (M.Mr r : ℝ) / r ^ γ) atTop (𝓝 0) := by
  have hstep : ∀ᶠ r : ℝ in atTop,
      (M.Mr r : ℝ) / r ^ γ ≤ (r ^ γ)⁻¹ + A * r ^ (β - γ) := by
    filter_upwards [h, eventually_gt_atTop (0 : ℝ)] with r hr hr0
    have hpos : (0 : ℝ) < r ^ γ := Real.rpow_pos_of_pos hr0 γ
    rw [div_le_iff₀ hpos]
    have hkey : ((r ^ γ)⁻¹ + A * r ^ (β - γ)) * r ^ γ = 1 + A * r ^ β := by
      have hpow : r ^ (β - γ) * r ^ γ = r ^ β := by
        rw [← Real.rpow_add hr0 (β - γ) γ, sub_add_cancel]
      calc ((r ^ γ)⁻¹ + A * r ^ (β - γ)) * r ^ γ
          = (r ^ γ)⁻¹ * r ^ γ + A * (r ^ (β - γ) * r ^ γ) := by ring
        _ = 1 + A * r ^ β := by rw [inv_mul_cancel₀ (ne_of_gt hpos), hpow]
    rw [hkey]
    exact hr
  have h1 : Tendsto (fun r : ℝ => (r ^ γ)⁻¹) atTop (𝓝 0) :=
    tendsto_inv_atTop_zero.comp (tendsto_rpow_atTop hγ)
  have h2 : Tendsto (fun r : ℝ => A * r ^ (β - γ)) atTop (𝓝 0) := by
    have h0 : Tendsto (fun r : ℝ => r ^ (-(γ - β))) atTop (𝓝 0) :=
      tendsto_rpow_neg_atTop (by linarith)
    have := h0.const_mul A
    simpa only [neg_sub, mul_zero] using this
  refine tendsto_of_tendsto_of_tendsto_of_le_of_le' tendsto_const_nhds ?_ ?_ hstep
  · simpa using h1.add h2
  · filter_upwards [eventually_gt_atTop (0 : ℝ)] with r hr0
    exact div_nonneg (by exact_mod_cast Nat.zero_le (M.Mr r)) (Real.rpow_nonneg hr0.le γ)

/-- **Corollary I.4.14 under Case 2 of (HD) with `α > 2`**: the log-free critical two-point
bound in dimension `d > 6` implies the hydrodynamic condition. -/
theorem hydro_of_case2 (hd : 6 < M.d) (hα : 2 < M.α) (C : ℝ) (hC : 0 < C)
    (hb : ∀ x y : M.V, x ≠ y → M.twoPoint M.betaCrit x y
      ≤ C * (M.S.ρ (toVec (x - y))) ^ (-(M.d : ℝ) + 2)) :
    Hydro M := by
  obtain ⟨C', hC', hbound⟩ := mr_sq_le_rpow_of_case2 M hd C hC hb
  have hdR : (2 : ℝ) < (M.d : ℝ) := by
    have h : (2 : ℕ) < M.d := by omega
    exact_mod_cast h
  have hγ : (0 : ℝ) < ((M.d : ℝ) + M.α) / 2 := by linarith
  have hβγ : ((M.d : ℝ) + 2) / 2 < ((M.d : ℝ) + M.α) / 2 := by linarith
  -- square root of the median bound
  have hMr : ∀ᶠ r : ℝ in atTop,
      (M.Mr r : ℝ) ≤ 1 + Real.sqrt C' * r ^ (((M.d : ℝ) + 2) / 2) := by
    filter_upwards [hbound, eventually_gt_atTop (0 : ℝ)] with r hr hr0
    have hMr1 : (1 : ℝ) ≤ (M.Mr r : ℝ) := by
      have h1 : 1 ≤ M.Mr r := by
        rw [PercLib.CriticalLRP.CaseTwo.Mr_eq_edianMaxVol M r]
        exact PercLib.CriticalLRP.Percolation.one_le_edianMaxVol _ _
      exact_mod_cast h1
    have hnn : (0 : ℝ) ≤ (M.Mr r : ℝ) - 1 := by linarith
    have hYnn : (0 : ℝ) ≤ Real.sqrt C' * r ^ (((M.d : ℝ) + 2) / 2) := by positivity
    have hYsq : (Real.sqrt C' * r ^ (((M.d : ℝ) + 2) / 2)) ^ 2
        = C' * r ^ ((M.d : ℝ) + 2) := by
      rw [mul_pow, Real.sq_sqrt hC'.le, ← Real.rpow_natCast (r ^ (((M.d : ℝ) + 2) / 2)) 2,
        ← Real.rpow_mul hr0.le]
      ring_nf
    have hsq : ((M.Mr r : ℝ) - 1) ^ 2
        ≤ (Real.sqrt C' * r ^ (((M.d : ℝ) + 2) / 2)) ^ 2 := by
      rw [hYsq]
      exact hr
    have h := Real.sqrt_le_sqrt hsq
    rw [Real.sqrt_sq hnn, Real.sqrt_sq hYnn] at h
    linarith
  exact tendsto_ratio_of_pow_bound M hγ hβγ hMr

theorem mr_le_log_sqrt_of_exp (hd6 : M.d = 6) (hα2 : M.α = 2) (Kτ : ℝ) (hKτ : 0 < Kτ)
    (hτsum : ∀ r : ℝ, 2 ≤ r →
      ∑ x ∈ (M.finite_ball (2 * r)).toFinset, M.tau x ≤ Kτ * r ^ 2 * (Real.log r)⁻¹) :
    ∃ C : ℝ, 0 < C ∧ ∀ᶠ r : ℝ in atTop,
      ((M.Mr r : ℝ) - 1) ^ 2 ≤ C * r ^ ((M.d : ℝ) + M.α) * (Real.log r)⁻¹ := by
  have hdR : (M.d : ℝ) = 6 := by exact_mod_cast hd6
  have hαR : M.α = 2 := hα2
  refine ⟨Real.exp 1 * 2 * Kτ, by positivity, ?_⟩
  filter_upwards [ball_ncard_eventually_le M, eventually_ge_atTop (2 : ℝ)] with r hcard hr
  have hr0 : (0 : ℝ) < r := by linarith
  have hlogr : (0 : ℝ) < Real.log r := Real.log_pos (by linarith)
  have hsum_nonneg : (0 : ℝ) ≤ ∑ x ∈ (M.finite_ball (2 * r)).toFinset, M.tau x :=
    Finset.sum_nonneg fun x _ => M.tau_nonneg x
  have hEne : (∫⁻ ω, clusterVolIn ω (0 : M.V) (M.ball (2 * r)) ∂(M.cutLaw r)) ≠ ⊤ :=
    ne_top_of_le_ne_top ENNReal.ofReal_ne_top (interVol_le_ofReal_sum_tau M r)
  have hEreal : (∫⁻ ω, clusterVolIn ω (0 : M.V) (M.ball (2 * r)) ∂(M.cutLaw r)).toReal
      ≤ Kτ * r ^ 2 * (Real.log r)⁻¹ := by
    refine (ENNReal.toReal_mono ENNReal.ofReal_ne_top (interVol_le_ofReal_sum_tau M r)).trans ?_
    rw [ENNReal.toReal_ofReal hsum_nonneg]
    exact hτsum r (by linarith)
  have h1 := mr_sq_le_inter M r hr0.le
  have hreal : ((M.Mr r : ℝ) - 1) ^ 2
      ≤ Real.exp 1 * ((M.ball r).ncard : ℝ) * (Kτ * r ^ 2 * (Real.log r)⁻¹) := by
    have hmono := ENNReal.toReal_mono
      (ENNReal.mul_ne_top ENNReal.ofReal_ne_top hEne) h1
    rw [ENNReal.toReal_mul, ENNReal.toReal_ofReal (by positivity),
      ENNReal.toReal_ofReal (by positivity)] at hmono
    exact hmono.trans (mul_le_mul_of_nonneg_left hEreal (by positivity))
  refine hreal.trans ?_
  have hrpow : r ^ ((M.d : ℝ) + M.α) = r ^ M.d * r ^ 2 := by
    rw [Real.rpow_add hr0, hαR]
    norm_num [Real.rpow_two]
  have h7 : Real.exp 1 * ((M.ball r).ncard : ℝ) * (Kτ * r ^ 2 * (Real.log r)⁻¹)
      ≤ Real.exp 1 * (2 * r ^ M.d) * (Kτ * r ^ 2 * (Real.log r)⁻¹) := by
    have hpos : (0 : ℝ) ≤ Kτ * r ^ 2 * (Real.log r)⁻¹ := by positivity
    have hle1 : Real.exp 1 * ((M.ball r).ncard : ℝ) ≤ Real.exp 1 * (2 * r ^ M.d) :=
      mul_le_mul_of_nonneg_left hcard (Real.exp_pos 1).le
    exact mul_le_mul_of_nonneg_right hle1 hpos
  refine h7.trans (le_of_eq ?_)
  rw [hrpow]
  ring

/-! ## §10 The hydrodynamic condition from Case 3 of (HD) -/

theorem sum_tau_ball_le_of_majorant (hd6 : M.d = 6) (K₀ : ℝ) (hK₀ : 0 < K₀)
    (hτ : ∀ z : M.V,
      |M.tau z| ≤ K₀ * CriticalLRPConv.Wt ((M.d : ℝ) - 2) 1 (M.S.ρ (toVec z))) :
    ∃ K : ℝ, 0 < K ∧ ∀ r : ℝ, 2 ≤ r →
      ∑ x ∈ (M.finite_ball (2 * r)).toFinset, M.tau x
        ≤ K * r ^ 2 * (Real.log r)⁻¹ := by
  have hdR : (M.d : ℝ) = 6 := by exact_mod_cast hd6
  refine ⟨K₀ * shellConst M * 9, by have := shellConst_pos M; positivity, ?_⟩
  intro r hr
  have hr0 : (0 : ℝ) < r := by linarith
  have hlogr : (0 : ℝ) < Real.log r := Real.log_pos (by linarith)
  have hlog2r : (0 : ℝ) < CriticalLRPConv.LamR (2 * r) := by
    rw [CriticalLRPConv.LamR]
    exact Real.log_pos (by linarith)
  -- termwise domination by the positive-log majorant
  have hstep1 : ∑ x ∈ (M.finite_ball (2 * r)).toFinset, M.tau x
      ≤ K₀ * ∑ x ∈ (M.finite_ball (2 * r)).toFinset,
          CriticalLRPConv.Wt ((M.d : ℝ) - 2) 1 (M.S.ρ (toVec x)) := by
    rw [Finset.mul_sum]
    refine Finset.sum_le_sum fun x _ => ?_
    simpa only [abs_of_nonneg (M.tau_nonneg x)] using hτ x
  -- the production ball-shell estimate at `a = 2`, `c = 1`, `S₀ = 2r`
  have hshell : ∑ x ∈ (M.finite_ball (2 * r)).toFinset,
        CriticalLRPConv.Wt ((M.d : ℝ) - 2) 1 (M.S.ρ (toVec x))
      ≤ shellConst M * ((1 + 2 * r) ^ (2 : ℝ) * CriticalLRPConv.LamR (2 * r) ^ (-(1 : ℝ))) :=
    CriticalLRPConv.srcNorm_ball_shell_bound M.S M.hd
      (a := 2) (c := 1) (S₀ := 2 * r) (F := (M.finite_ball (2 * r)).toFinset)
      (by norm_num) (by rw [hdR]; norm_num) (by norm_num) (by linarith)
      (fun y hy => by
        have hmem : y ∈ M.ball (2 * r) := by
          rw [← (M.finite_ball (2 * r)).coe_toFinset]
          exact hy
        exact hmem)
  -- arithmetic: `(1 + 2r)^2 ≤ 9 r^2` and `LamR (2r)^{-1} ≤ (log r)^{-1}`
  have h9 : (1 + 2 * r) ^ (2 : ℝ) ≤ 9 * r ^ 2 := by
    have h2 : (1 + 2 * r : ℝ) ≤ 3 * r := by linarith
    have h3 : (0 : ℝ) < 1 + 2 * r := by linarith
    have h4 : (1 + 2 * r) ^ (2 : ℝ) ≤ (3 * r) ^ (2 : ℝ) :=
      Real.rpow_le_rpow h3.le h2 (by norm_num)
    have h5 : (3 * r) ^ (2 : ℝ) = 9 * r ^ 2 := by
      rw [Real.mul_rpow (by norm_num) hr0.le]
      norm_num
    rw [h5] at h4
    exact h4
  have hlog : CriticalLRPConv.LamR (2 * r) ^ (-(1 : ℝ)) ≤ (Real.log r)⁻¹ := by
    have hle : Real.log r ≤ CriticalLRPConv.LamR (2 * r) := by
      rw [CriticalLRPConv.LamR]
      exact Real.log_le_log hr0 (by linarith)
    have h := Real.rpow_le_rpow_of_nonpos hlogr hle (by norm_num : (-(1 : ℝ)) ≤ 0)
    simpa only [Real.rpow_neg_one] using h
  have hlog2rnn : (0 : ℝ) ≤ CriticalLRPConv.LamR (2 * r) ^ (-(1 : ℝ)) :=
    le_of_lt (by positivity)
  have hprod : (1 + 2 * r) ^ (2 : ℝ) * CriticalLRPConv.LamR (2 * r) ^ (-(1 : ℝ))
      ≤ (9 * r ^ 2) * (Real.log r)⁻¹ :=
    mul_le_mul h9 hlog hlog2rnn (by positivity)
  have hK : 0 < K₀ * shellConst M := by
    have := shellConst_pos M
    positivity
  calc ∑ x ∈ (M.finite_ball (2 * r)).toFinset, M.tau x
      ≤ K₀ * ∑ x ∈ (M.finite_ball (2 * r)).toFinset,
          CriticalLRPConv.Wt ((M.d : ℝ) - 2) 1 (M.S.ρ (toVec x)) := hstep1
    _ ≤ K₀ * (shellConst M *
          ((1 + 2 * r) ^ (2 : ℝ) * CriticalLRPConv.LamR (2 * r) ^ (-(1 : ℝ)))) := by
        exact mul_le_mul_of_nonneg_left hshell hK₀.le
    _ = K₀ * shellConst M *
          ((1 + 2 * r) ^ (2 : ℝ) * CriticalLRPConv.LamR (2 * r) ^ (-(1 : ℝ))) := by ring
    _ ≤ K₀ * shellConst M * ((9 * r ^ 2) * (Real.log r)⁻¹) := by
        exact mul_le_mul_of_nonneg_left hprod hK.le
    _ = K₀ * shellConst M * 9 * r ^ 2 * (Real.log r)⁻¹ := by ring


/-- **Corollary I.4.14 under Case 3 of (HD)** (Hutchcroft, arXiv:2508.18807v1, p. 42):
the log-corrected critical two-point bound implies the hydrodynamic condition
`M_r = o(r^{(d+α)/2})`.  The logarithm in (HD)(3) is what makes the estimate marginal:
without it one only obtains `M_r ⪯ r^{(d+α)/2}`, not `o`. -/
theorem hydro_of_case3_majorant (hd6 : M.d = 6) (hα2 : M.α = 2)
    (K₀ : ℝ) (hK₀ : 0 < K₀)
    (hτ : ∀ z : M.V,
      |M.tau z| ≤ K₀ * CriticalLRPConv.Wt ((M.d : ℝ) - 2) 1 (M.S.ρ (toVec z))) :
    Hydro M := by
  obtain ⟨Kτ, hKτ, hτsum⟩ := sum_tau_ball_le_of_majorant M hd6 K₀ hK₀ hτ
  obtain ⟨C, hC, hCbound⟩ := mr_le_log_sqrt_of_exp M hd6 hα2 Kτ hKτ hτsum
  have hdR : (M.d : ℝ) = 6 := by exact_mod_cast hd6
  have hαR : M.α = 2 := hα2
  have hp : ((M.d : ℝ) + M.α) / 2 = 4 := by rw [hdR, hαR]; norm_num
  -- rewrite the target exponent to `4`
  have hexp : ∀ r : ℝ, r ^ (((M.d : ℝ) + M.α) / 2) = r ^ 4 := by
    intro r
    rw [hp]
    norm_num
  change Tendsto (fun r : ℝ => (M.Mr r : ℝ) / r ^ (((M.d : ℝ) + M.α) / 2)) atTop (𝓝 0)
  simp only [hexp]
  -- the ratio is squeezed between `0` and a vanishing upper bound
  have hupper : ∀ᶠ r : ℝ in atTop,
      (M.Mr r : ℝ) / r ^ 4 ≤ (r ^ 4)⁻¹ + Real.sqrt C * (Real.sqrt (Real.log r))⁻¹ := by
    filter_upwards [hCbound, eventually_ge_atTop (2 : ℝ)] with r hr hr2
    have hr0 : (0 : ℝ) < r := by linarith
    have hlog : (0 : ℝ) < Real.log r := Real.log_pos (by linarith)
    have hMr1 : (1 : ℝ) ≤ (M.Mr r : ℝ) := by
      have h1 : 1 ≤ M.Mr r := by
        rw [PercLib.CriticalLRP.CaseTwo.Mr_eq_edianMaxVol M r]
        exact PercLib.CriticalLRP.Percolation.one_le_edianMaxVol _ _
      exact_mod_cast h1
    have hpow8 : r ^ ((M.d : ℝ) + M.α) = r ^ 8 := by rw [hdR, hαR]; norm_num
    rw [hpow8] at hr
    have hr4 : (0 : ℝ) < r ^ 4 := by positivity
    -- the square root of the right-hand side
    have hroot : (M.Mr r : ℝ) - 1
        ≤ Real.sqrt C * (Real.sqrt (Real.log r))⁻¹ * r ^ 4 := by
      have hnn : (0 : ℝ) ≤ (M.Mr r : ℝ) - 1 := by linarith
      have hYnn : (0 : ℝ) ≤ Real.sqrt C * (Real.sqrt (Real.log r))⁻¹ * r ^ 4 := by positivity
      have hYsq : (Real.sqrt C * (Real.sqrt (Real.log r))⁻¹ * r ^ 4) ^ 2
          = C * r ^ 8 * (Real.log r)⁻¹ := by
        rw [mul_pow, mul_pow, inv_pow, Real.sq_sqrt hlog.le, Real.sq_sqrt hC.le]
        ring
      have hsq : ((M.Mr r : ℝ) - 1) ^ 2
          ≤ (Real.sqrt C * (Real.sqrt (Real.log r))⁻¹ * r ^ 4) ^ 2 := by
        rw [hYsq]
        exact hr
      have h := Real.sqrt_le_sqrt hsq
      rwa [Real.sqrt_sq hnn, Real.sqrt_sq hYnn] at h
    -- divide by `r ^ 4`
    rw [div_le_iff₀ hr4]
    have hkey : ((r ^ 4)⁻¹ + Real.sqrt C * (Real.sqrt (Real.log r))⁻¹) * r ^ 4
        = Real.sqrt C * (Real.sqrt (Real.log r))⁻¹ * r ^ 4 + 1 := by
      rw [add_mul, inv_mul_cancel₀ (ne_of_gt hr4)]
      ring
    rw [hkey]
    linarith
  -- the upper bound tends to zero
  have hlog : Tendsto (fun r : ℝ => Real.log r) atTop atTop := Real.tendsto_log_atTop
  have hsqrt : Tendsto (fun r : ℝ => Real.sqrt (Real.log r)) atTop atTop :=
    Real.tendsto_sqrt_atTop.comp hlog
  have hinv : Tendsto (fun r : ℝ => (Real.sqrt (Real.log r))⁻¹) atTop (𝓝 0) :=
    tendsto_inv_atTop_zero.comp hsqrt
  have hpow : Tendsto (fun r : ℝ => r ^ 4) atTop atTop :=
    tendsto_pow_atTop (by norm_num)
  have hinv4 : Tendsto (fun r : ℝ => (r ^ 4)⁻¹) atTop (𝓝 0) :=
    tendsto_inv_atTop_zero.comp hpow
  have hlim : Tendsto (fun r : ℝ => (r ^ 4)⁻¹ +
      Real.sqrt C * (Real.sqrt (Real.log r))⁻¹) atTop (𝓝 0) := by
    simpa using hinv4.add (hinv.const_mul (Real.sqrt C))
  refine tendsto_of_tendsto_of_tendsto_of_le_of_le' tendsto_const_nhds hlim ?_ ?_
  · filter_upwards with r
    exact div_nonneg (by positivity) (by positivity)
  · exact hupper


/-! ## §12 Composing with the source's own hypothesis forms -/

/-- (HD) Case 3 is the third alternative of the source's hypothesis `(HD)`. -/
theorem HD_of_case3HD (h : M.Case3HD) : HD M := Or.inr (Or.inr h)

/-- Hence `(HD+)` holds under (HD) Case 3. -/
theorem HDplus_of_case3HD (h : M.Case3HD) : HDplus M := Or.inl (HD_of_case3HD M h)

/-- **Corollary I.4.14 under the repaired large-distance form `Case3HDLarge`.**  The proof of
`hydro_of_case3HD` uses the literal display only through the pointwise majorant, so the same
conclusion holds from production's distance-restricted hypothesis. -/
theorem hydro_of_case3HDLarge (h : M.Case3HDLarge) : Hydro M := by
  obtain ⟨hd6, hα2, C, hC, hb⟩ := h
  obtain ⟨K, hK, hτ⟩ := M.exists_abs_tau_le_Wt_of_case3HDLarge ⟨hd6, hα2, C, hC, hb⟩
  exact hydro_of_case3_majorant M hd6 hα2 K hK hτ

end M5

/-! ## Axiom audit -/

#print axioms M5.sum_tau_ball_le_of_case3
#print axioms M5.ball_subset_ballAt_two_mul
#print axioms M5.le_winCount
#print axioms M5.clusterVolIn_shift_image
#print axioms M5.measure_clusterVolIn_ballAt_eq
#print axioms M5.lintegral_winCount
#print axioms M5.mr_measure_exists
#print axioms M5.averaging_bound_ball
#print axioms M5.mr_sq_le_inter
#print axioms M5.lintegral_clusterVolIn_ball_eq_sum
#print axioms M5.interVol_le_ofReal_sum_tau
#print axioms M5.interVol_toReal_le_sum_tau
#print axioms M5.ball_ncard_eventually_le
#print axioms M5.mr_le_log_sqrt
#print axioms M5.mr_le_rpow_log
#print axioms M5.hydro_of_case3HD
#check @M5.hydro_of_case3HD
#check @M5.mr_sq_le_inter
#check @M5.mr_le_rpow_log

#print axioms M5.Wt_zero_log
#print axioms M5.exists_abs_tau_le_Wt_of_case2
#print axioms M5.sum_tau_ball_le_of_case2
#print axioms M5.mr_sq_le_rpow_of_case2
#print axioms M5.tendsto_ratio_of_pow_bound
#print axioms M5.hydro_of_case2
#check @M5.hydro_of_case2
#check @M5.mr_sq_le_rpow_of_case2

#print axioms M5.ballAt_zero
#print axioms M5.mem_ballAt_iff
#print axioms M5.measurable_winCount
#print axioms M5.shellConst_pos
#print axioms M5.shellConst2_pos
#print axioms M5.ballAt_add_image

#print axioms M5.mr_le_log_sqrt_of_exp
#print axioms M5.sum_tau_ball_le_of_majorant
#print axioms M5.hydro_of_case3_majorant
#print axioms M5.HD_of_case3HD
#print axioms M5.HDplus_of_case3HD
#print axioms M5.hydro_of_case3HDLarge
#check @M5.hydro_of_case3HDLarge
#check @M5.hydro_of_case3_majorant
