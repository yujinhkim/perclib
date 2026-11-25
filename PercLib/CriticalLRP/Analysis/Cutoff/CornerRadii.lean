/-
Copyright (c) 2026 PercLib contributors. Released under Apache 2.0.
-/
module

public import PercLib.CriticalLRP.Analysis.Cutoff.CornerRadii.Defs
public import PercLib.CriticalLRP.Analysis.BallRatioLogError

/-!
# Finiteness and counting of attained cutoff radii (normalized source norm)

This file proves, at the actual `SourceModelData` of the campaign, that the radii attained by
`M.S.dist · 0` on nonzero lattice points meet every bounded interval in a finite set, and that
the number of them is bounded by a polynomial in the upper endpoint of the window.

The mechanism is the finite bounded lattice ball that is already available
(`SourceModelData.finite_ball`): the radii attained below `b` are the image under
`x ↦ M.S.dist x 0` of the finite set of nonzero lattice points of `M.ball b`.  No separation
property of the norm (`M.S.dist x 0 ≥ 1` or similar) is used or claimed; only finiteness of
the ball and positivity of the norm off the origin.

The count estimate is obtained by feeding the landed ball-count asymptotics
(`SourceModelData.ball_ratio_error_bound`, Lemma I.4.6 in ratio form) into the cardinality
bound `ncard ≤ (M.ball b).ncard`.  It is the finite-degree input needed to select a uniform
finite exceptional set of corner radii in a bounded window.

Contents:
* `mem_ball_iff_dist_le` — the ball of radius `b` is the set of points at distance `≤ b`;
* `attainedRadii_inter_Iic_eq_image` — attained radii below `b` are a finite image;
* `finite_attainedRadii_inter_Iic`, `finite_attainedRadii_inter_Icc` — local finiteness;
* `ncard_attainedRadii_inter_Iic_le`, `ncard_attainedRadii_inter_Icc_le` — `ncard ≤ ball count`;
* `exists_ncard_attainedRadii_Icc_degree_bound` — degree-`d` bound, uniform in the left endpoint;
* `exists_ncard_attainedRadii_window_bound` — the same for the two-scale window `[t/2, 2t]`;
* `ncard_attainedRadii_isBigO` — the `O(b ^ d)` form of the same bound;
* `exists_offCorner_in_Icc` — every nondegenerate window contains an off-corner radius;
* `volume_attainedRadii_inter_Icc` — the corner set of a bounded window is Lebesgue-null;
* `attainedRadiiFinset` — the finite corner set of a window as a `Finset`;
* `exists_gap_at_attainedRadii` — attained radii are isolated: a uniform gap around each one;
* `exists_nhds_notMem_attainedRadii` — a non-attained radius has a corner-free neighbourhood;
* `attainedRadii_nonempty`, `attainedRadii_inter_Iic_eq_empty_of_nonpos` — non-vacuity and the
  degenerate `b ≤ 0` window.

Every theorem is audited with `#print axioms` at the end of the file.
-/

@[expose] public section

noncomputable section

open MeasureTheory Set Filter Asymptotics
open scoped ENNReal Topology

namespace PercLib.CriticalLRP.Orchestration

/-- The lattice ball of radius `b` is exactly the set of lattice points at distance at most
`b` from the origin. -/
theorem SourceModelData.mem_ball_iff_dist_le (M : SourceModelData) (x : M.V) (b : ℝ) :
    x ∈ M.ball b ↔ M.S.dist x 0 ≤ b := by
  simp only [SourceModelData.ball, Set.mem_ofPred_eq, M.S.dist_zero_right]

/-- Inside `(-∞, b]`, the attained radii are the image of the nonzero lattice points of the
ball of radius `b` under `x ↦ M.S.dist x 0`. -/
theorem SourceModelData.attainedRadii_inter_Iic_eq_image (M : SourceModelData) (b : ℝ) :
    M.attainedRadii ∩ Set.Iic b
      = (fun x : M.V => M.S.dist x 0) '' {x : M.V | x ≠ 0 ∧ M.S.dist x 0 ≤ b} := by
  ext r
  simp only [SourceModelData.attainedRadii, SourceNormData.mem_attainedRadii,
    Set.mem_inter_iff, Set.mem_Iic, Set.mem_image, Set.mem_ofPred_eq]
  constructor
  · rintro ⟨⟨x, hx, hd⟩, hb⟩
    exact ⟨x, ⟨hx, hd.trans_le hb⟩, hd⟩
  · rintro ⟨x, ⟨hx, hb⟩, hd⟩
    refine ⟨⟨x, hx, hd⟩, ?_⟩
    rw [← hd]
    exact hb

/-- The set of nonzero lattice points at distance at most `b` from the origin is finite. -/
theorem SourceModelData.finite_dist_ball (M : SourceModelData) (b : ℝ) :
    {x : M.V | x ≠ 0 ∧ M.S.dist x 0 ≤ b}.Finite :=
  (M.finite_ball b).subset (fun x hx => (M.mem_ball_iff_dist_le x b).mpr hx.2)

/-- **Local finiteness of attained radii.** Below any bound `b`, only finitely many radii are
attained. -/
theorem SourceModelData.finite_attainedRadii_inter_Iic (M : SourceModelData) (b : ℝ) :
    (M.attainedRadii ∩ Set.Iic b).Finite := by
  rw [M.attainedRadii_inter_Iic_eq_image]
  exact (M.finite_dist_ball b).image _

/-- **Corner finiteness in a bounded interval.** The radii attained by `M.S.dist · 0` on
nonzero lattice points meet every interval `[a, b]` in a finite set. -/
theorem SourceModelData.finite_attainedRadii_inter_Icc (M : SourceModelData) (a b : ℝ) :
    (M.attainedRadii ∩ Set.Icc a b).Finite :=
  (M.finite_attainedRadii_inter_Iic b).subset (fun _ hr => ⟨hr.1, hr.2.2⟩)

/-- The same window-corner finiteness in the original `cornerRadii` vocabulary. -/
theorem SourceModelData.finite_cornerRadii_inter_Ioo (M : SourceModelData) (a b : ℝ) :
    (M.cornerRadii ∩ Set.Ioo a b).Finite := by
  rw [← M.attainedRadii_eq_cornerRadii]
  exact (M.finite_attainedRadii_inter_Icc a b).subset
    (fun _ h => ⟨h.1, Set.Ioo_subset_Icc_self h.2⟩)

/-- The attained radius set of a bounded window is closed. -/
theorem SourceModelData.isClosed_attainedRadii_inter_Icc (M : SourceModelData) (a b : ℝ) :
    IsClosed (M.attainedRadii ∩ Set.Icc a b) :=
  (M.finite_attainedRadii_inter_Icc a b).isClosed

/-- **Cardinality bound.** The number of attained radii below `b` is at most the number of
lattice points of the ball of radius `b`. -/
theorem SourceModelData.ncard_attainedRadii_inter_Iic_le (M : SourceModelData) (b : ℝ) :
    (M.attainedRadii ∩ Set.Iic b).ncard ≤ (M.ball b).ncard := by
  rw [M.attainedRadii_inter_Iic_eq_image]
  refine le_trans (Set.ncard_image_le (M.finite_dist_ball b)) ?_
  exact Set.ncard_le_ncard (fun x hx => (M.mem_ball_iff_dist_le x b).mpr hx.2)
    (M.finite_ball b)

/-- The number of attained radii in `[a, b]` is at most the number of lattice points of the
ball of radius `b`. -/
theorem SourceModelData.ncard_attainedRadii_inter_Icc_le (M : SourceModelData) (a b : ℝ) :
    (M.attainedRadii ∩ Set.Icc a b).ncard ≤ (M.ball b).ncard :=
  le_trans
    (Set.ncard_le_ncard (s := M.attainedRadii ∩ Set.Icc a b)
      (t := M.attainedRadii ∩ Set.Iic b) (fun _ hr => ⟨hr.1, hr.2.2⟩)
      (M.finite_attainedRadii_inter_Iic b))
    (M.ncard_attainedRadii_inter_Iic_le b)

/-- **Degree bound for the corner set.** There are constants `c, R` with `0 ≤ c`, `0 < R` such
that every interval `[a, b]` with `b ≥ R` contains at most `(1 + c) * b ^ d` attained radii,
uniformly in the lower endpoint `a`. -/
theorem SourceModelData.exists_ncard_attainedRadii_Icc_degree_bound (M : SourceModelData) :
    ∃ c R : ℝ, 0 ≤ c ∧ 0 < R ∧ ∀ (a b : ℝ), R ≤ b →
      ((M.attainedRadii ∩ Set.Icc a b).ncard : ℝ) ≤ (1 + c) * b ^ M.d := by
  obtain ⟨c, R₀, hc, hR₀, hbound⟩ := M.ball_ratio_error_bound
  refine ⟨c, max R₀ 1, ?_⟩
  refine ⟨hc, lt_of_lt_of_le zero_lt_one (le_max_right R₀ 1), ?_⟩
  intro a b hb
  have hbR : R₀ ≤ b := (le_max_left R₀ 1).trans hb
  have hb1 : (1 : ℝ) ≤ b := (le_max_right R₀ 1).trans hb
  have hbpos : 0 < b := zero_lt_one.trans_le hb1
  have hpow : 0 < b ^ M.d := pow_pos hbpos M.d
  have hcard : ((M.attainedRadii ∩ Set.Icc a b).ncard : ℝ) ≤ ((M.ball b).ncard : ℝ) :=
    Nat.cast_le.mpr (M.ncard_attainedRadii_inter_Icc_le a b)
  have hone : ((M.ball b).ncard : ℝ) / b ^ M.d ≤ 1 + c := by
    have h₁ : |((M.ball b).ncard : ℝ) / b ^ M.d - 1| ≤ c * b⁻¹ := hbound b hbR
    have h₂ : c * b⁻¹ ≤ c :=
      mul_le_of_le_one_right hc (inv_le_one_of_one_le₀ hb1)
    have h₃ : ((M.ball b).ncard : ℝ) / b ^ M.d - 1 ≤ c :=
      (le_abs_self _).trans (h₁.trans h₂)
    linarith
  have hmain : ((M.ball b).ncard : ℝ) ≤ (1 + c) * b ^ M.d := (div_le_iff₀ hpow).mp hone
  exact hcard.trans hmain

/-- **Uniform degree bound on the two-scale window.** There are constants `C, R` with `0 ≤ C`,
`0 < R` such that every window `[t/2, 2t]` with `t ≥ R` contains at most `C * t ^ d` attained
radii.  This is the shape in which the corner set of an off-corner derivative argument is
selected. -/
theorem SourceModelData.exists_ncard_attainedRadii_window_bound (M : SourceModelData) :
    ∃ C R : ℝ, 0 ≤ C ∧ 0 < R ∧ ∀ t : ℝ, R ≤ t →
      ((M.attainedRadii ∩ Set.Icc (t / 2) (2 * t)).ncard : ℝ) ≤ C * t ^ M.d := by
  obtain ⟨c, R₀, hc, hR₀, hbound⟩ := M.exists_ncard_attainedRadii_Icc_degree_bound
  refine ⟨(1 + c) * 2 ^ M.d, max R₀ 1, ?_⟩
  refine ⟨?_, lt_of_lt_of_le zero_lt_one (le_max_right R₀ 1), ?_⟩
  · exact mul_nonneg (by linarith) (pow_nonneg (by norm_num) M.d)
  · intro t ht
    have htR : R₀ ≤ t := (le_max_left R₀ 1).trans ht
    have ht1 : (1 : ℝ) ≤ t := (le_max_right R₀ 1).trans ht
    have htpos : 0 < t := zero_lt_one.trans_le ht1
    have hR2 : R₀ ≤ 2 * t := htR.trans (le_of_lt (lt_two_mul_self htpos))
    have hpow : (2 * t) ^ M.d = 2 ^ M.d * t ^ M.d := mul_pow 2 t M.d
    refine (hbound (t / 2) (2 * t) hR2).trans (le_of_eq ?_)
    rw [hpow]
    ring

/-- **Asymptotic form of the count bound.** For a fixed lower endpoint the number of attained
radii in `[a, b]` grows at most like `b ^ d`. -/
theorem SourceModelData.ncard_attainedRadii_isBigO (M : SourceModelData) (a : ℝ) :
    (fun b : ℝ => ((M.attainedRadii ∩ Set.Icc a b).ncard : ℝ)) =O[atTop]
      (fun b : ℝ => b ^ M.d) := by
  obtain ⟨c, R, hc, hR, hbound⟩ := M.exists_ncard_attainedRadii_Icc_degree_bound
  refine IsBigO.of_bound (1 + c) ?_
  filter_upwards [eventually_ge_atTop R] with b hb
  have hbpos : 0 < b := hR.trans_le hb
  rw [Real.norm_eq_abs, Real.norm_eq_abs, abs_of_nonneg (Nat.cast_nonneg _),
    abs_of_nonneg (pow_nonneg hbpos.le M.d)]
  exact hbound a b hb

/-- The corner set of the window `[a, b]` as a `Finset`, for use as an explicit finite
exceptional set. -/
noncomputable def SourceModelData.attainedRadiiFinset (M : SourceModelData) (a b : ℝ) :
    Finset ℝ :=
  (M.finite_attainedRadii_inter_Icc a b).toFinset

/-- **An off-corner radius exists in every nondegenerate window.** The attained radii of a
bounded window are finite, so they cannot exhaust a nondegenerate interval.  This is the
selection step that makes "differentiate away from the corners" non-vacuous in a window. -/
theorem SourceModelData.exists_offCorner_in_Icc (M : SourceModelData) {a b : ℝ} (h : a < b) :
    ∃ r ∈ Set.Icc a b, r ∉ M.attainedRadii := by
  obtain ⟨r, hr, hnr⟩ :=
    (Set.Icc_infinite h).exists_notMem_finite (M.finite_attainedRadii_inter_Icc a b)
  exact ⟨r, hr, fun hrc => hnr ⟨hrc, hr⟩⟩

/-- **The corner set is Lebesgue-null.** The attained radii of a bounded window form a finite
set, hence a set of measure zero; a function may fail to be differentiable there without
affecting any integral over the window. -/
theorem SourceModelData.volume_attainedRadii_inter_Icc (M : SourceModelData) (a b : ℝ) :
    volume (M.attainedRadii ∩ Set.Icc a b) = 0 :=
  (M.finite_attainedRadii_inter_Icc a b).measure_zero volume

theorem SourceModelData.mem_attainedRadiiFinset {M : SourceModelData} {a b r : ℝ} :
    r ∈ M.attainedRadiiFinset a b ↔ r ∈ M.attainedRadii ∧ a ≤ r ∧ r ≤ b := by
  simp only [SourceModelData.attainedRadiiFinset]
  rw [Set.Finite.mem_toFinset, Set.mem_inter_iff, Set.mem_Icc]

theorem SourceModelData.card_attainedRadiiFinset (M : SourceModelData) (a b : ℝ) :
    (M.attainedRadiiFinset a b).card = (M.attainedRadii ∩ Set.Icc a b).ncard :=
  (Set.ncard_eq_toFinset_card _ _).symm

/-- The corner set of a window, as a set, is exactly the attained radii of that window. -/
theorem SourceModelData.coe_attainedRadiiFinset (M : SourceModelData) (a b : ℝ) :
    ((M.attainedRadiiFinset a b : Finset ℝ) : Set ℝ) = M.attainedRadii ∩ Set.Icc a b := by
  ext r
  rw [Finset.mem_coe, M.mem_attainedRadiiFinset, Set.mem_inter_iff, Set.mem_Icc]

/-- **Attained radii are isolated.** Around any real radius `r` there is a uniform gap such
that every *other* attained radius is at distance at least `ε` from `r`.  In particular the
attained radii have no accumulation point, and each of them is surrounded by an off-corner
interval. -/
theorem SourceModelData.exists_gap_at_attainedRadii (M : SourceModelData) (r : ℝ) :
    ∃ ε > 0, ∀ r' : ℝ, r' ∈ M.attainedRadii → r' ≠ r → ε ≤ |r' - r| := by
  classical
  set S : Set ℝ := M.attainedRadii ∩ Set.Icc (r - 1) (r + 1) with hS
  have hfin : S.Finite := M.finite_attainedRadii_inter_Icc (r - 1) (r + 1)
  have hclosed : IsClosed (S \ {r}) := (hfin.sdiff (t := {r})).isClosed
  have hmem : r ∈ (S \ {r})ᶜ := by simp
  obtain ⟨ε₀, hε₀, hsub⟩ := Metric.mem_nhds_iff.1 (hclosed.isOpen_compl.mem_nhds hmem)
  refine ⟨min ε₀ 1, lt_min hε₀ one_pos, ?_⟩
  intro r' hr' hne
  by_contra hcon
  rw [not_le] at hcon
  have hlt1 : |r' - r| < 1 := lt_of_lt_of_le hcon (min_le_right _ _)
  have hlt0 : |r' - r| < ε₀ := lt_of_lt_of_le hcon (min_le_left _ _)
  have hlt : r' ∈ S \ {r} := by
    refine ⟨⟨hr', ?_, ?_⟩, hne⟩
    · rw [abs_lt] at hlt1
      linarith [hlt1.1]
    · rw [abs_lt] at hlt1
      linarith [hlt1.2]
  have hball : r' ∈ Metric.ball r ε₀ := by
    rw [Metric.mem_ball, Real.dist_eq]
    exact hlt0
  exact hsub hball hlt

/-- **Off-corner neighbourhoods.** A radius that is not attained has a whole neighbourhood
consisting of non-attained radii. -/
theorem SourceModelData.exists_nhds_notMem_attainedRadii (M : SourceModelData) {r : ℝ}
    (hr : r ∉ M.attainedRadii) :
    ∃ ε > 0, ∀ r' : ℝ, |r' - r| < ε → r' ∉ M.attainedRadii := by
  classical
  set S : Set ℝ := M.attainedRadii ∩ Set.Icc (r - 1) (r + 1) with hS
  have hfin : S.Finite := M.finite_attainedRadii_inter_Icc (r - 1) (r + 1)
  have hclosed : IsClosed S := hfin.isClosed
  have hmem : r ∈ Sᶜ := by
    rw [Set.mem_compl_iff, hS]
    exact fun h => hr h.1
  obtain ⟨ε₀, hε₀, hsub⟩ :=
    Metric.mem_nhds_iff.1 (hclosed.isOpen_compl.mem_nhds hmem)
  refine ⟨min ε₀ 1, lt_min hε₀ one_pos, ?_⟩
  intro r' hlt hrmem
  have hlt1 : |r' - r| < 1 := lt_of_lt_of_le hlt (min_le_right _ _)
  have hlt0 : |r' - r| < ε₀ := lt_of_lt_of_le hlt (min_le_left _ _)
  have hmemS : r' ∈ S := by
    refine ⟨hrmem, ?_, ?_⟩
    · rw [abs_lt] at hlt1
      linarith [hlt1.1]
    · rw [abs_lt] at hlt1
      linarith [hlt1.2]
  have hball : r' ∈ Metric.ball r ε₀ := by
    rw [Metric.mem_ball, Real.dist_eq]
    exact hlt0
  exact hsub hball hmemS

/-- **Non-vacuity.** Some radius is attained: the unit vector in the first coordinate has a
strictly positive norm. -/
theorem SourceNormData.attainedRadii_nonempty {d : ℕ} (S : SourceNormData d) (hd : 1 ≤ d) :
    S.attainedRadii.Nonempty := by
  refine ⟨S.dist (fun i => if i = (⟨0, by omega⟩ : Fin d) then 1 else 0) 0, ?_⟩
  refine ⟨_, ?_, rfl⟩
  intro hc
  have hone := congrFun hc (⟨0, by omega⟩ : Fin d)
  simp at hone

/-- **Degenerate window.** Below the origin no radius is attained, so the corner set of a
window inside `(-∞, 0]` is empty. -/
theorem SourceModelData.attainedRadii_inter_Iic_eq_empty_of_nonpos (M : SourceModelData)
    {b : ℝ} (hb : b ≤ 0) : M.attainedRadii ∩ Set.Iic b = ∅ := by
  rw [Set.eq_empty_iff_forall_notMem]
  intro r hr
  exact absurd (M.attainedRadii_pos hr.1) (not_lt.mpr (hr.2.trans hb))

/-- **Empty window.** An interval whose endpoints are reversed contains no attained radius. -/
theorem SourceModelData.attainedRadii_inter_Icc_eq_empty_of_lt (M : SourceModelData)
    {a b : ℝ} (h : b < a) : M.attainedRadii ∩ Set.Icc a b = ∅ := by
  rw [Set.Icc_eq_empty_iff.mpr (not_le.mpr h), Set.inter_empty]

end PercLib.CriticalLRP.Orchestration
