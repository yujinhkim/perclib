module

public import PercLib.CriticalLRP.Analysis.LatticeConvolution.NormShell.Defs

/-!
# Arbitrary normalized-norm shell transfer
-/

set_option autoImplicit false
set_option linter.unusedSectionVars false

@[expose] public section

namespace CriticalLRPConv

open PercLib.CriticalLRP.Orchestration
open PercLib.CriticalLRP.FiniteVolume (linfNorm linfNorm_le_iff box mem_box_iff card_box)

variable {d : ℕ}

/-! ## §1 The lattice sup norm and the real sup norm of `toVec` -/

/-- The sup norm of a lattice point and of its real image agree:
`‖toVec y‖_∞ = linfNorm y`. -/
theorem norm_toVec_eq_linfNorm (y : Fin d → ℤ) : ‖toVec y‖ = (linfNorm y : ℝ) := by
  have hcast : ∀ i : Fin d, ‖(toVec y) i‖ = ((y i).natAbs : ℝ) := by
    intro i
    simp only [toVec, Real.norm_eq_abs]
    simp
  refine le_antisymm ?_ ?_
  · rw [pi_norm_le_iff_of_nonneg (by positivity : (0 : ℝ) ≤ (linfNorm y : ℝ))]
    intro i
    rw [hcast i]
    exact_mod_cast linfNorm_le_iff.mp (le_refl (linfNorm y)) i
  · have h : linfNorm y ≤ ⌊‖toVec y‖⌋₊ := by
      rw [linfNorm_le_iff]
      intro i
      refine Nat.le_floor ?_
      rw [← hcast i]
      exact norm_le_pi_norm (toVec y) i
    calc (linfNorm y : ℝ) ≤ ((⌊‖toVec y‖⌋₊ : ℕ) : ℝ) := by exact_mod_cast h
      _ ≤ ‖toVec y‖ := Nat.floor_le (norm_nonneg _)

/-! ## §2 Norm equivalence with the supremum norm -/

/-- `S.ρ` is nonnegative everywhere. -/
theorem src_nonneg (S : SourceNormData d) (v : Fin d → ℝ) : 0 ≤ S.ρ v := by
  have h := S.ρ_add_le v (-v)
  rw [add_neg_cancel, S.ρ_zero, S.ρ_neg] at h
  linarith

/-- `S.ρ` is subadditive over a finite sum. -/
theorem src_sum_le (S : SourceNormData d) {ι : Type*} (s : Finset ι)
    (f : ι → Fin d → ℝ) :
    S.ρ (∑ i ∈ s, f i) ≤ ∑ i ∈ s, S.ρ (f i) := by
  classical
  induction s using Finset.induction with
  | empty => simpa using le_of_eq S.ρ_zero
  | insert a s ha ih =>
      have h2 : (∑ i ∈ insert a s, S.ρ (f i))
          = S.ρ (f a) + ∑ i ∈ s, S.ρ (f i) := Finset.sum_insert ha
      calc S.ρ (∑ i ∈ insert a s, f i) = S.ρ (f a + ∑ i ∈ s, f i) := by
            congr 1
            exact Finset.sum_insert ha
        _ ≤ S.ρ (f a) + S.ρ (∑ i ∈ s, f i) := S.ρ_add_le _ _
        _ ≤ S.ρ (f a) + ∑ i ∈ s, S.ρ (f i) := add_le_add (le_refl _) ih
        _ = ∑ i ∈ insert a s, S.ρ (f i) := h2.symm

/-- Every real vector is the corresponding combination of the standard basis vectors. -/
theorem eq_sum_smul (v : Fin d → ℝ) :
    v = ∑ i : Fin d, (v i) • Pi.single i (1 : ℝ) := by
  funext j
  rw [Finset.sum_apply]
  rw [Finset.sum_eq_single j]
  · simp
  · intro b _ hb
    simp [Pi.smul_apply, hb]
  · intro h
    exact absurd (Finset.mem_univ j) h

/-- The real vector `toVec y` is the corresponding integer combination of the standard basis
vectors. -/
theorem toVec_eq_sum_smul (y : Fin d → ℤ) :
    toVec y = ∑ i : Fin d, (y i : ℝ) • Pi.single i (1 : ℝ) :=
  eq_sum_smul (toVec y)

/-- The upper norm-comparison constant is at least `1`. -/
theorem one_le_srcUpperConst (S : SourceNormData d) : 1 ≤ srcUpperConst S :=
  le_max_left _ _

/-- The upper norm-comparison constant is positive. -/
theorem srcUpperConst_pos (S : SourceNormData d) : 0 < srcUpperConst S :=
  lt_of_lt_of_le one_pos (one_le_srcUpperConst S)

/-- **The upper norm comparison.**  `S.ρ v ≤ srcUpperConst S * ‖v‖_∞` for every real
vector `v`, by the triangle inequality and absolute homogeneity through the standard basis. -/
theorem srcNorm_le_upper (S : SourceNormData d) (v : Fin d → ℝ) :
    S.ρ v ≤ srcUpperConst S * ‖v‖ := by
  have hsum : S.ρ v ≤ ∑ i : Fin d, S.ρ ((v i) • Pi.single i (1 : ℝ)) :=
    (congrArg S.ρ (eq_sum_smul v)).le.trans (src_sum_le S _ _)
  have hsmul : ∀ i : Fin d, S.ρ ((v i) • Pi.single i (1 : ℝ)) =
      |v i| * S.ρ (Pi.single i (1 : ℝ)) := fun i => S.ρ_smul _ _
  have hcoord : ∀ i : Fin d, |v i| ≤ ‖v‖ := fun i => by
    have h := norm_le_pi_norm v i
    rwa [Real.norm_eq_abs] at h
  calc S.ρ v ≤ ∑ i : Fin d, S.ρ ((v i) • Pi.single i (1 : ℝ)) := hsum
    _ = ∑ i : Fin d, |v i| * S.ρ (Pi.single i (1 : ℝ)) := by
        exact Finset.sum_congr rfl (fun i _ => hsmul i)
    _ ≤ ∑ i : Fin d, ‖v‖ * S.ρ (Pi.single i (1 : ℝ)) := by
        refine Finset.sum_le_sum fun i _ => ?_
        exact mul_le_mul_of_nonneg_right (hcoord i) (src_nonneg S _)
    _ = ‖v‖ * srcBasisConst S := by
        rw [srcBasisConst, Finset.mul_sum]
    _ ≤ srcUpperConst S * ‖v‖ := by
        rw [mul_comm ‖v‖]
        exact mul_le_mul_of_nonneg_right (le_max_right _ _) (norm_nonneg v)

/-- **The upper norm comparison on lattice points.** -/
theorem srcNorm_le_upper_linfNorm (S : SourceNormData d) (y : Fin d → ℤ) :
    S.ρ (toVec y) ≤ srcUpperConst S * (linfNorm y : ℝ) := by
  rw [← norm_toVec_eq_linfNorm]
  exact srcNorm_le_upper S _

/-- **Existence of the lower norm-comparison constant**: a positive `m` with
`m ‖v‖_∞ ≤ S.ρ v`.  This is the finite-dimensional norm equivalence, proved from
positive definiteness and continuity. -/
theorem exists_pos_mul_norm_le_src (S : SourceNormData d) (hd : 1 ≤ d) :
    ∃ m : ℝ, 0 < m ∧ ∀ v : Fin d → ℝ, m * ‖v‖ ≤ S.ρ v :=
  PercLib.CriticalLRP.LatticeGeometry.exists_pos_mul_norm_le_of_pos_def (d := d)
    S.ρ_add_le S.ρ_continuous S.ρ_smul
    (fun x hx => by
      by_contra hne
      exact absurd hx (ne_of_gt (S.ρ_pos x hne)))
    hd

/-- The lower norm-comparison constant is strictly positive in positive dimension. -/
theorem srcLowerConst_pos (S : SourceNormData d) (hd : 1 ≤ d) : 0 < srcLowerConst S := by
  classical
  obtain ⟨m, hm, hspec⟩ := exists_pos_mul_norm_le_src (d := d) S hd
  have hmem : m ∈ {r : ℝ | 0 < r ∧ ∀ v : Fin d → ℝ, r * ‖v‖ ≤ S.ρ v} :=
    ⟨hm, hspec⟩
  have hbdd : BddAbove {r : ℝ | 0 < r ∧ ∀ v : Fin d → ℝ, r * ‖v‖ ≤ S.ρ v} := by
    refine ⟨S.ρ (Pi.single (⟨0, hd⟩ : Fin d) (1 : ℝ) : Fin d → ℝ)
      / ‖(Pi.single (⟨0, hd⟩ : Fin d) (1 : ℝ) : Fin d → ℝ)‖, ?_⟩
    intro r hr
    have hpos : (0 : ℝ) < ‖(Pi.single (⟨0, hd⟩ : Fin d) (1 : ℝ) : Fin d → ℝ)‖ := by
      rw [Pi.norm_single]
      norm_num
    exact (le_div_iff₀ hpos).mpr (hr.2 _)
  exact lt_of_lt_of_le hm (le_csSup hbdd hmem)

/-- **The lower norm comparison.**  `srcLowerConst S * ‖v‖_∞ ≤ S.ρ v` for every real
vector `v`. -/
theorem srcLowerConst_spec (S : SourceNormData d) (hd : 1 ≤ d) (v : Fin d → ℝ) :
    srcLowerConst S * ‖v‖ ≤ S.ρ v := by
  obtain ⟨m, hm, hspec⟩ := exists_pos_mul_norm_le_src (d := d) S hd
  have hne : {r : ℝ | 0 < r ∧ ∀ v : Fin d → ℝ, r * ‖v‖ ≤ S.ρ v}.Nonempty :=
    ⟨m, hm, hspec⟩
  rcases eq_or_ne v 0 with rfl | hv
  · rw [norm_zero, mul_zero]
    exact src_nonneg S 0
  · have hv0 : (0 : ℝ) < ‖v‖ := norm_pos_iff.mpr hv
    have h : srcLowerConst S ≤ S.ρ v / ‖v‖ :=
      csSup_le hne (fun r hr => (le_div_iff₀ hv0).mpr (hr.2 v))
    exact (le_div_iff₀ hv0).mp h

/-- The clamped lower comparison constant is strictly positive. -/
theorem srcLowerUnit_pos (S : SourceNormData d) (hd : 1 ≤ d) : 0 < srcLowerUnit S :=
  lt_min (srcLowerConst_pos S hd) one_pos

/-- The clamped lower comparison constant is at most `1`. -/
theorem srcLowerUnit_le_one (S : SourceNormData d) : srcLowerUnit S ≤ 1 :=
  min_le_right _ _

/-- **The clamped lower norm comparison.** -/
theorem srcLowerUnit_spec (S : SourceNormData d) (hd : 1 ≤ d) (v : Fin d → ℝ) :
    srcLowerUnit S * ‖v‖ ≤ S.ρ v := by
  have h1 : srcLowerUnit S ≤ srcLowerConst S := min_le_left _ _
  have h2 : srcLowerUnit S * ‖v‖ ≤ srcLowerConst S * ‖v‖ :=
    mul_le_mul_of_nonneg_right h1 (norm_nonneg v)
  exact h2.trans (srcLowerConst_spec S hd v)

/-- **The lower norm comparison on lattice points.** -/
theorem srcLowerUnit_mul_linfNorm_le (S : SourceNormData d) (hd : 1 ≤ d)
    (y : Fin d → ℤ) : srcLowerUnit S * (linfNorm y : ℝ) ≤ S.ρ (toVec y) := by
  rw [← norm_toVec_eq_linfNorm]
  exact srcLowerUnit_spec S hd _



/-- The `S.ρ (toVec ·)` radius used by the shell estimates is the source's own distance from
the origin, `S.dist 0 ·`.  This is the bridge to the `SourceModelData` normalisation. -/
theorem dist_zero_eq_srcNorm (S : SourceNormData d) (y : Fin d → ℤ) :
    S.dist 0 y = S.ρ (toVec y) := by
  have hneg : toVec (-y) = -toVec y := by
    funext i
    simp [toVec]
  rw [SourceNormData.dist, zero_sub, hneg, S.ρ_neg]

/-! ## §3 The lattice ball count in the `S.ρ`-radius -/

/-- The counting constant is nonnegative. -/
theorem srcCountConst_nonneg (S : SourceNormData d) (hd : 1 ≤ d) : 0 ≤ srcCountConst S :=
  Real.rpow_nonneg
    (add_nonneg (div_nonneg (by norm_num) (srcLowerUnit_pos S hd).le) (by norm_num)) _

/-- **Directional comparison of the `S.ρ`-ball with a sup-norm ball.**  Every lattice point
of `S.ρ`-radius at most `r` has sup-norm at most `r / srcLowerUnit S`. -/
theorem srcNorm_ball_subset_linfBall (S : SourceNormData d) (hd : 1 ≤ d) {r : ℝ} :
    {y : Fin d → ℤ | S.ρ (toVec y) ≤ r} ⊆
      {y : Fin d → ℤ | (linfNorm y : ℝ) ≤ r / srcLowerUnit S} := by
  intro y hy
  have hc : 0 < srcLowerUnit S := srcLowerUnit_pos S hd
  have h1 : srcLowerUnit S * (linfNorm y : ℝ) ≤ S.ρ (toVec y) :=
    srcLowerUnit_mul_linfNorm_le S hd y
  refine (le_div_iff₀ hc).mpr ?_
  rw [mul_comm]
  exact le_trans h1 hy

/-- **The lattice ball count in the `S.ρ`-radius.**  For every finite set `F` of lattice
points and every `n : ℕ`, the number of `y ∈ F` with `⌊S.ρ (toVec y)⌋ ≤ n` is at most
`srcCountConst S * (1 + n)^d`.  This is the counting hypothesis of the generic ball-shell
bound, discharged for the source radius. -/
theorem srcNorm_ball_card_le (S : SourceNormData d) (hd : 1 ≤ d)
    (F : Finset (Fin d → ℤ)) (n : ℕ) :
    ((F.filter (fun y => ⌊S.ρ (toVec y)⌋₊ ≤ n)).card : ℝ) ≤
      srcCountConst S * (1 + (n : ℝ)) ^ (d : ℝ) := by
  classical
  have hc : 0 < srcLowerUnit S := srcLowerUnit_pos S hd
  set N : ℕ := ⌊((n : ℝ) + 1) / srcLowerUnit S⌋₊ + 1 with hNdef
  have hsub : F.filter (fun y => ⌊S.ρ (toVec y)⌋₊ ≤ n) ⊆ box d N := by
    intro y hy
    rw [Finset.mem_filter] at hy
    rw [mem_box_iff, linfNorm_le_iff]
    have hlt : S.ρ (toVec y) < (n : ℝ) + 1 := by
      have h1 : ⌊S.ρ (toVec y)⌋₊ < n + 1 := Nat.lt_succ_of_le hy.2
      have h2 := (Nat.floor_lt (n := n + 1) (src_nonneg S (toVec y))).mp h1
      simpa using h2
    have h2 : (linfNorm y : ℝ) < ((n : ℝ) + 1) / srcLowerUnit S := by
      refine (lt_div_iff₀ hc).mpr ?_
      rw [mul_comm]
      exact lt_of_le_of_lt (srcLowerUnit_mul_linfNorm_le S hd y) hlt
    have h3 : (linfNorm y : ℝ) < (N : ℝ) := by
      have hN : (N : ℝ) = ((⌊((n : ℝ) + 1) / srcLowerUnit S⌋₊ : ℕ) : ℝ) + 1 := by
        simp [hNdef]
      have hfloor := Nat.lt_floor_add_one (((n : ℝ) + 1) / srcLowerUnit S)
      rw [hN]
      linarith
    have h4 : linfNorm y ≤ N := le_of_lt (Nat.cast_lt.mp h3)
    exact linfNorm_le_iff.mp h4
  have hcard : (F.filter (fun y => ⌊S.ρ (toVec y)⌋₊ ≤ n)).card ≤ (2 * N + 1) ^ d := by
    have h := Finset.card_le_card hsub
    rwa [card_box] at h
  have hNbound : ((2 * N + 1 : ℕ) : ℝ) ≤ (3 / srcLowerUnit S + 3) * ((n : ℝ) + 1) := by
    have hNle : (N : ℝ) ≤ ((n : ℝ) + 1) / srcLowerUnit S + 1 := by
      have hN : (N : ℝ) = ((⌊((n : ℝ) + 1) / srcLowerUnit S⌋₊ : ℕ) : ℝ) + 1 := by
        simp [hNdef]
      rw [hN]
      have hx : (0 : ℝ) ≤ ((n : ℝ) + 1) / srcLowerUnit S := by positivity
      linarith [Nat.floor_le hx]
    have hcast : ((2 * N + 1 : ℕ) : ℝ) = 2 * (N : ℝ) + 1 := by push_cast; ring
    have hn1 : (0 : ℝ) < (n : ℝ) + 1 := by positivity
    have hinv : (0 : ℝ) < 1 / srcLowerUnit S := by positivity
    have hstep : 2 * (((n : ℝ) + 1) / srcLowerUnit S) + 3
        ≤ (3 / srcLowerUnit S + 3) * ((n : ℝ) + 1) := by
      have hdiv : 3 * (((n : ℝ) + 1) / srcLowerUnit S)
          = (3 / srcLowerUnit S) * ((n : ℝ) + 1) := by ring
      have h2 : 2 * (((n : ℝ) + 1) / srcLowerUnit S)
          ≤ 3 * (((n : ℝ) + 1) / srcLowerUnit S) := by
        have : (0 : ℝ) ≤ ((n : ℝ) + 1) / srcLowerUnit S := le_of_lt (by positivity)
        linarith
      have h3 : (3 : ℝ) ≤ 3 * ((n : ℝ) + 1) := by nlinarith
      nlinarith [hdiv, h2, h3]
    rw [hcast]
    nlinarith [hNle, hstep]
  calc ((F.filter (fun y => ⌊S.ρ (toVec y)⌋₊ ≤ n)).card : ℝ)
      ≤ (((2 * N + 1) ^ d : ℕ) : ℝ) := by exact_mod_cast hcard
    _ = ((2 * N + 1 : ℕ) : ℝ) ^ d := by push_cast; ring
    _ ≤ ((3 / srcLowerUnit S + 3) * ((n : ℝ) + 1)) ^ d :=
        pow_le_pow_left₀ (by positivity) hNbound d
    _ = (3 / srcLowerUnit S + 3) ^ d * ((n : ℝ) + 1) ^ d := mul_pow _ _ d
    _ = srcCountConst S * (1 + (n : ℝ)) ^ (d : ℝ) := by
        rw [srcCountConst, Real.rpow_natCast ((1 : ℝ) + (n : ℝ)) d,
          Real.rpow_natCast (3 / srcLowerUnit S + 3) d]
        ring_nf

/-! ## §4 The transferred weighted ball-shell bound (`A1`/`A2`) -/

/-- **Weighted ball-shell bound in the source norm.**  For a finite set `F` of lattice points
of `S.ρ`-radius at most `S₀`,

`∑_{y ∈ F} (1 + S.ρ (toVec y))^{-(d-a)} (log (2 + S.ρ (toVec y)))^{-c}
  ≤ K (1 + S₀)^a (log (2 + S₀))^{-c}`

with `K` depending on the dimension, on `a`, `c` and on the norm `S` only through
`srcCountConst S`.  This is the `A1`/`A2` estimate of (I.4.12) for the actual normalized
source radius. -/
theorem srcNorm_ball_shell_bound (S : SourceNormData d) (hd : 1 ≤ d)
    {a c S₀ : ℝ} (ha : 0 < a) (haD : a < (d : ℝ)) (hc : 0 ≤ c) (hS₀ : 0 ≤ S₀)
    {F : Finset (Fin d → ℤ)} (hrad : ∀ y ∈ F, S.ρ (toVec y) ≤ S₀) :
    ∑ y ∈ F, Wt ((d : ℝ) - a) c (S.ρ (toVec y)) ≤
      2 ^ a * (srcCountConst S * (1 + ((d : ℝ) - a + 2 * (c + 1)) * coreConst a c)) *
        ((1 + S₀) ^ a * LamR S₀ ^ (-c)) :=
  ball_shell_bound (ρ := fun y : Fin d → ℤ => S.ρ (toVec y))
    (fun y => src_nonneg S (toVec y)) ha haD hc hS₀ (srcCountConst_nonneg S hd) hrad
    (srcNorm_ball_card_le S hd F)

/-- Closed-ball form of the transferred `A1`/`A2` bound: the same estimate for a set of
lattice points of `S.ρ`-radius **strictly** below `S₀`. -/
theorem srcNorm_ball_shell_bound_lt (S : SourceNormData d) (hd : 1 ≤ d)
    {a c S₀ : ℝ} (ha : 0 < a) (haD : a < (d : ℝ)) (hc : 0 ≤ c) (hS₀ : 0 ≤ S₀)
    {F : Finset (Fin d → ℤ)} (hrad : ∀ y ∈ F, S.ρ (toVec y) < S₀) :
    ∑ y ∈ F, Wt ((d : ℝ) - a) c (S.ρ (toVec y)) ≤
      2 ^ a * (srcCountConst S * (1 + ((d : ℝ) - a + 2 * (c + 1)) * coreConst a c)) *
        ((1 + S₀) ^ a * LamR S₀ ^ (-c)) :=
  srcNorm_ball_shell_bound S hd ha haD hc hS₀ (fun y hy => (hrad y hy).le)


/-! ## §5 The weight comparison `Wt e c (S.ρ (toVec y)) ≤ K · Wt e c ‖y‖` -/

/-- **Logarithmic comparison.**  For `0 < c₀ ≤ 1` and `s ≥ 0`,
`log (2 + s) ≤ (1 + log (2 + 1/c₀)/log 2) · log (2 + c₀ s)`.  The two logarithms are
compared through `2 + s ≤ (2 + c₀ s)(2 + 1/c₀)`; no logarithm is dropped. -/
theorem LamR_le_logConst_mul {c0 s : ℝ} (hc0 : 0 < c0) (hs : 0 ≤ s) :
    LamR s ≤ (1 + Real.log (2 + 1 / c0) / Real.log 2) * LamR (c0 * s) := by
  have hlog2 : (0 : ℝ) < Real.log 2 := Real.log_pos (by norm_num)
  have hcs : (0 : ℝ) ≤ c0 * s := mul_nonneg hc0.le hs
  have h2s : (0 : ℝ) < 2 + s := by linarith
  have h2cs : (0 : ℝ) < 2 + c0 * s := by linarith
  have hinv : (0 : ℝ) < 2 + 1 / c0 := by positivity
  have hle : 2 + s ≤ (2 + c0 * s) * (2 + 1 / c0) := by
    have h2 : (0 : ℝ) ≤ 2 / c0 := by positivity
    have h3 : (0 : ℝ) ≤ 2 * (c0 * s) := by linarith
    have hexp : (2 + c0 * s) * (2 + 1 / c0) = 4 + 2 / c0 + 2 * (c0 * s) + s := by
      field_simp
      ring
    rw [hexp]
    linarith
  have hlog : Real.log (2 + s) ≤ Real.log ((2 + c0 * s) * (2 + 1 / c0)) :=
    Real.log_le_log h2s hle
  rw [Real.log_mul (ne_of_gt h2cs) (ne_of_gt hinv)] at hlog
  have hstep : Real.log (2 + 1 / c0) ≤ (Real.log (2 + 1 / c0) / Real.log 2) * LamR (c0 * s) := by
    rw [div_mul_eq_mul_div, le_div_iff₀ hlog2]
    have hmono : Real.log 2 ≤ LamR (c0 * s) := by
      rw [LamR_def]
      exact Real.log_le_log (by norm_num) (by linarith)
    have hinv1 : (0 : ℝ) < 1 / c0 := by positivity
    have hlog1 : (0 : ℝ) < Real.log (2 + 1 / c0) := Real.log_pos (by linarith)
    nlinarith [hlog1, hmono]
  simp only [LamR_def] at hstep ⊢
  linarith

/-- **The weight comparison.**  If `0 < c₀ ≤ 1` and `c₀ s ≤ r` with `r, s ≥ 0`, then

`(1+r)^{-e} (log (2+r))^{-c} ≤ c₀^{-e} (1 + log (2 + 1/c₀)/log 2)^{c} (1+s)^{-e} (log (2+s))^{-c}`.

The power factor is compared through `1 + r ≥ c₀ (1 + s)`, the logarithmic factor through
`LamR_le_logConst_mul`; both comparisons are exact and the exponents `e`, `c` are preserved. -/
theorem Wt_le_of_le_mul {e c r s c0 : ℝ} (he : 0 ≤ e) (hc : 0 ≤ c)
    (hc0 : 0 < c0) (hc01 : c0 ≤ 1) (hr : 0 ≤ r) (hs : 0 ≤ s) (h : c0 * s ≤ r) :
    Wt e c r ≤ c0 ^ (-e) * (1 + Real.log (2 + 1 / c0) / Real.log 2) ^ c * Wt e c s := by
  have hcs : (0 : ℝ) ≤ c0 * s := mul_nonneg hc0.le hs
  have hs' : (0 : ℝ) ≤ 1 + s := by linarith
  have hCl : (0 : ℝ) < 1 + Real.log (2 + 1 / c0) / Real.log 2 := by
    have hinv1 : (0 : ℝ) < 1 / c0 := by positivity
    have h1 : (0 : ℝ) < Real.log (2 + 1 / c0) := Real.log_pos (by linarith)
    have h2 : (0 : ℝ) < Real.log 2 := Real.log_pos (by norm_num)
    positivity
  have hpow : (1 + r) ^ (-e) ≤ c0 ^ (-e) * (1 + s) ^ (-e) := by
    have hbase : c0 * (1 + s) ≤ 1 + r := by nlinarith
    have hbpos : (0 : ℝ) < c0 * (1 + s) := by positivity
    calc (1 + r) ^ (-e) ≤ (c0 * (1 + s)) ^ (-e) :=
          Real.rpow_le_rpow_of_nonpos hbpos hbase (by linarith)
      _ = c0 ^ (-e) * (1 + s) ^ (-e) := Real.mul_rpow hc0.le hs'
  have hlog : LamR r ^ (-c) ≤
      (1 + Real.log (2 + 1 / c0) / Real.log 2) ^ c * LamR s ^ (-c) := by
    have hcs' : (0 : ℝ) ≤ c0 * s := hcs
    have hrlam : LamR (c0 * s) ≤ LamR r := LamR_mono hcs' h
    have hkey : LamR s ≤ (1 + Real.log (2 + 1 / c0) / Real.log 2) * LamR (c0 * s) :=
      LamR_le_logConst_mul hc0 hs
    have hbase : LamR s / (1 + Real.log (2 + 1 / c0) / Real.log 2) ≤ LamR r := by
      rw [div_le_iff₀ hCl, mul_comm (LamR r)]
      exact hkey.trans (mul_le_mul_of_nonneg_left hrlam hCl.le)
    have hbpos : (0 : ℝ) < LamR s / (1 + Real.log (2 + 1 / c0) / Real.log 2) := by
      have h1 : (0 : ℝ) < LamR s := LamR_pos hs
      positivity
    have step := Real.rpow_le_rpow_of_nonpos hbpos hbase (show -c ≤ 0 by linarith)
    rw [Real.div_rpow (LamR_pos hs).le hCl.le, Real.rpow_neg hCl.le] at step
    calc LamR r ^ (-c)
        ≤ LamR s ^ (-c) / ((1 + Real.log (2 + 1 / c0) / Real.log 2) ^ c)⁻¹ := step
      _ = (1 + Real.log (2 + 1 / c0) / Real.log 2) ^ c * LamR s ^ (-c) := by
          rw [div_inv_eq_mul, mul_comm]
  calc Wt e c r = (1 + r) ^ (-e) * LamR r ^ (-c) := rfl
    _ ≤ (c0 ^ (-e) * (1 + s) ^ (-e)) * ((1 + Real.log (2 + 1 / c0) / Real.log 2) ^ c
          * LamR s ^ (-c)) :=
        mul_le_mul hpow hlog (Real.rpow_nonneg (LamR_pos hr).le _)
          (mul_nonneg (Real.rpow_nonneg hc0.le _)
            (Real.rpow_nonneg (by linarith : (0:ℝ) ≤ 1 + s) _))
    _ = c0 ^ (-e) * (1 + Real.log (2 + 1 / c0) / Real.log 2) ^ c * Wt e c s := by
        rw [Wt]
        ring

/-- The lattice form of the weight comparison: the `S.ρ`-weight of `y` is bounded by the
sup-norm weight of `y`, with the norm-dependent constant `srcLowerUnit S^{-e} srcLogConst S^c`. -/
theorem Wt_srcNorm_le (S : SourceNormData d) (hd : 1 ≤ d) {e c : ℝ} (he : 0 ≤ e) (hc : 0 ≤ c)
    (y : Fin d → ℤ) :
    Wt e c (S.ρ (toVec y)) ≤
      srcLowerUnit S ^ (-e) * srcLogConst S ^ c * Wt e c (linfNorm y : ℝ) := by
  have h0 : srcLowerUnit S * (linfNorm y : ℝ) ≤ S.ρ (toVec y) :=
    srcLowerUnit_mul_linfNorm_le S hd y
  have h := Wt_le_of_le_mul (e := e) (c := c) (r := S.ρ (toVec y))
    (s := (linfNorm y : ℝ)) (c0 := srcLowerUnit S) he hc
    (srcLowerUnit_pos S hd) (srcLowerUnit_le_one S) (src_nonneg S (toVec y)) (by positivity) h0
  simpa only [srcLogConst] using h

/-- **Rescaling the outer radius.**  Dividing the radius by the upper comparison constant
`C = srcUpperConst S ≥ 1` costs the exact factor `C^e (1 + log (2+C)/log 2)^c`. -/
theorem Wt_div_srcUpper_le (S : SourceNormData d) {e c S₀ : ℝ} (he : 0 ≤ e) (hc : 0 ≤ c)
    (hS₀ : 0 ≤ S₀) :
    Wt e c (S₀ / srcUpperConst S) ≤
      srcUpperConst S ^ e * srcLogConstUpper S ^ c * Wt e c S₀ := by
  have hC : (0 : ℝ) < srcUpperConst S := srcUpperConst_pos S
  have hC1 : (1 : ℝ) ≤ srcUpperConst S := one_le_srcUpperConst S
  have hCpos : (0 : ℝ) < 1 / srcUpperConst S := by positivity
  have hC1' : (1 : ℝ) / srcUpperConst S ≤ 1 := by
    rw [div_le_one hC]; exact hC1
  have h := Wt_le_of_le_mul (e := e) (c := c) (r := S₀ / srcUpperConst S) (s := S₀)
    (c0 := 1 / srcUpperConst S) he hc hCpos hC1' (by positivity) hS₀
      (by rw [one_div, div_eq_inv_mul, mul_comm])
  have e1 : (1 / srcUpperConst S) ^ (-e) = srcUpperConst S ^ e := by
    rw [one_div, Real.inv_rpow (le_of_lt hC), Real.rpow_neg (le_of_lt hC), inv_inv]
  have e2 : (1 + Real.log (2 + 1 / (1 / srcUpperConst S)) / Real.log 2)
      = srcLogConstUpper S := by
    rw [one_div_one_div]
    rfl
  rw [e1, e2] at h
  exact h


/-- The logarithmic comparison constant is positive. -/
theorem srcLogConst_pos (S : SourceNormData d) (hd : 1 ≤ d) : 0 < srcLogConst S := by
  have h0 : (0 : ℝ) < srcLowerUnit S := srcLowerUnit_pos S hd
  have h1 : (0 : ℝ) < 1 / srcLowerUnit S := by rw [one_div]; exact inv_pos.mpr h0
  have h2 : (0 : ℝ) < Real.log (2 + 1 / srcLowerUnit S) := Real.log_pos (by linarith)
  have h3 : (0 : ℝ) < Real.log 2 := Real.log_pos (by norm_num)
  have h4 : (0 : ℝ) < Real.log (2 + 1 / srcLowerUnit S) / Real.log 2 := div_pos h2 h3
  simp only [srcLogConst]
  linarith

/-- **Weighted tail shell in the source norm (finite form).**  For `d ≥ 1`, `γ > 0`, `c ≥ 0`,
`S₀ ≥ 0` and a finite set `F` of lattice points of `S.ρ`-radius strictly exceeding `S₀`,

`∑_{y ∈ F} (1 + S.ρ (toVec y))^{-(d+γ)} (log (2 + S.ρ (toVec y)))^{-c}
  ≤ K · tailShellConst d γ · (1 + S₀/C)^{-γ} (log (2 + S₀/C))^{-c}`

where `C = srcUpperConst S` and `K = srcLowerUnit S^{-(d+γ)} srcLogConst S^c` depends on the
norm only. -/
theorem sum_Wt_tail_le_srcNorm (S : SourceNormData d) (hd : 1 ≤ d)
    {γ c S₀ : ℝ} (hγ : 0 < γ) (hc : 0 ≤ c) (hS₀ : 0 ≤ S₀)
    (F : Finset (Fin d → ℤ)) (hF : ∀ y ∈ F, S₀ < S.ρ (toVec y)) :
    ∑ y ∈ F, Wt ((d : ℝ) + γ) c (S.ρ (toVec y)) ≤
      srcLowerUnit S ^ (-((d : ℝ) + γ)) * srcLogConst S ^ c *
        (tailShellConst d γ * Wt γ c (S₀ / srcUpperConst S)) := by
  classical
  have htail : ∀ y ∈ F, S₀ / srcUpperConst S < (linfNorm y : ℝ) := by
    intro y hy
    have h1 : S₀ < S.ρ (toVec y) := hF y hy
    have h2 : S.ρ (toVec y) ≤ srcUpperConst S * (linfNorm y : ℝ) :=
      srcNorm_le_upper_linfNorm S y
    have hC : (0 : ℝ) < srcUpperConst S := srcUpperConst_pos S
    rw [div_lt_iff₀ hC]
    nlinarith [h1, h2]
  have hterm : ∀ y ∈ F, Wt ((d : ℝ) + γ) c (S.ρ (toVec y)) ≤
      (srcLowerUnit S ^ (-((d : ℝ) + γ)) * srcLogConst S ^ c) *
        Wt ((d : ℝ) + γ) c (linfNorm y : ℝ) := by
    intro y _
    exact Wt_srcNorm_le S hd (by positivity : (0:ℝ) ≤ (d:ℝ) + γ) hc y
  have hK : (0 : ℝ) ≤ srcLowerUnit S ^ (-((d : ℝ) + γ)) * srcLogConst S ^ c :=
    mul_nonneg (Real.rpow_nonneg (srcLowerUnit_pos S hd).le _)
      (Real.rpow_nonneg (srcLogConst_pos S hd).le _)
  calc ∑ y ∈ F, Wt ((d : ℝ) + γ) c (S.ρ (toVec y))
      ≤ ∑ y ∈ F, (srcLowerUnit S ^ (-((d : ℝ) + γ)) * srcLogConst S ^ c) *
          Wt ((d : ℝ) + γ) c (linfNorm y : ℝ) := Finset.sum_le_sum hterm
    _ = (srcLowerUnit S ^ (-((d : ℝ) + γ)) * srcLogConst S ^ c) *
          ∑ y ∈ F, Wt ((d : ℝ) + γ) c (linfNorm y : ℝ) := by rw [Finset.mul_sum]
    _ ≤ (srcLowerUnit S ^ (-((d : ℝ) + γ)) * srcLogConst S ^ c) *
          (tailShellConst d γ * Wt γ c (S₀ / srcUpperConst S)) := by
        refine mul_le_mul_of_nonneg_left ?_ hK
        exact sum_Wt_tail_le (d := d) hd hγ hc
          (div_nonneg hS₀ (srcUpperConst_pos S).le) F htail

/-- **Weighted tail shell in the source norm (unrestricted `tsum`).**  The whole far region
`{y | S₀ < S.ρ (toVec y)}` carries finite weighted mass, with the same norm-dependent
constant; summability is part of the conclusion. -/
theorem tsum_Wt_tail_le_srcNorm (S : SourceNormData d) (hd : 1 ≤ d)
    {γ c S₀ : ℝ} (hγ : 0 < γ) (hc : 0 ≤ c) (hS₀ : 0 ≤ S₀) :
    ∑' y : {y : Fin d → ℤ // S₀ < S.ρ (toVec y)},
        Wt ((d : ℝ) + γ) c (S.ρ (toVec (y : Fin d → ℤ))) ≤
      srcLowerUnit S ^ (-((d : ℝ) + γ)) * srcLogConst S ^ c *
        (tailShellConst d γ * Wt γ c (S₀ / srcUpperConst S)) := by
  classical
  have hnn : ∀ y : {y : Fin d → ℤ // S₀ < S.ρ (toVec y)},
      0 ≤ Wt ((d : ℝ) + γ) c (S.ρ (toVec (y : Fin d → ℤ))) :=
    fun y => Wt_nonneg (src_nonneg S _)
  have hbound : ∀ u : Finset {y : Fin d → ℤ // S₀ < S.ρ (toVec y)},
      ∑ y ∈ u, Wt ((d : ℝ) + γ) c (S.ρ (toVec (y : Fin d → ℤ))) ≤
        srcLowerUnit S ^ (-((d : ℝ) + γ)) * srcLogConst S ^ c *
          (tailShellConst d γ * Wt γ c (S₀ / srcUpperConst S)) := by
    intro u
    have hinj : Set.InjOn (fun y : {y : Fin d → ℤ // S₀ < S.ρ (toVec y)} =>
        (y : Fin d → ℤ)) ↑u := fun a _ b _ hab => Subtype.ext hab
    have himg : ∑ y ∈ u, Wt ((d : ℝ) + γ) c (S.ρ (toVec (y : Fin d → ℤ)))
        = ∑ z ∈ u.image (fun y : {y : Fin d → ℤ // S₀ < S.ρ (toVec y)} =>
            (y : Fin d → ℤ)), Wt ((d : ℝ) + γ) c (S.ρ (toVec z)) := by
      rw [Finset.sum_image
        (f := fun z : Fin d → ℤ => Wt ((d : ℝ) + γ) c (S.ρ (toVec z))) hinj]
    rw [himg]
    exact sum_Wt_tail_le_srcNorm S hd hγ hc hS₀ _ (fun z hz => by
      obtain ⟨y, _, rfl⟩ := Finset.mem_image.mp hz
      exact y.2)
  exact Summable.tsum_le_of_sum_le (summable_of_sum_le hnn hbound) hbound

/-- **Weighted tail shell in the source norm, pure-logarithmic case** (`γ = 0`, `c > 1`).
Summing the critical weight `(1+ρy)^{-d} (log (2+ρy))^{-c}` over the lattice costs exactly one
logarithm, so the far-region bound keeps the exponent `c - 1` and *not* `c`. -/
theorem sum_Wt_tail_le_pureLog_srcNorm (S : SourceNormData d) (hd : 1 ≤ d)
    {c S₀ : ℝ} (hc : 1 < c) (hS₀ : 0 ≤ S₀)
    (F : Finset (Fin d → ℤ)) (hF : ∀ y ∈ F, S₀ < S.ρ (toVec y)) :
    ∑ y ∈ F, Wt (d : ℝ) c (S.ρ (toVec y)) ≤
      srcLowerUnit S ^ (-(d : ℝ)) * srcLogConst S ^ c *
        (tailShellConstLog d c * Wt (0 : ℝ) (c - 1) (S₀ / srcUpperConst S)) := by
  classical
  have htail : ∀ y ∈ F, S₀ / srcUpperConst S < (linfNorm y : ℝ) := by
    intro y yF
    have h1 : S₀ < S.ρ (toVec y) := hF y yF
    have h2 : S.ρ (toVec y) ≤ srcUpperConst S * (linfNorm y : ℝ) :=
      srcNorm_le_upper_linfNorm S y
    have hC : (0 : ℝ) < srcUpperConst S := srcUpperConst_pos S
    rw [div_lt_iff₀ hC]
    nlinarith [h1, h2]
  have hterm : ∀ y ∈ F, Wt (d : ℝ) c (S.ρ (toVec y)) ≤
      (srcLowerUnit S ^ (-(d : ℝ)) * srcLogConst S ^ c) *
        Wt (d : ℝ) c (linfNorm y : ℝ) := by
    intro y _
    have hd0 : (0 : ℝ) ≤ (d : ℝ) := Nat.cast_nonneg d
    exact Wt_srcNorm_le S hd hd0 (le_of_lt (lt_trans one_pos hc)) y
  have hK : (0 : ℝ) ≤ srcLowerUnit S ^ (-(d : ℝ)) * srcLogConst S ^ c :=
    mul_nonneg (Real.rpow_nonneg (srcLowerUnit_pos S hd).le _)
      (Real.rpow_nonneg (srcLogConst_pos S hd).le _)
  calc ∑ y ∈ F, Wt (d : ℝ) c (S.ρ (toVec y))
      ≤ ∑ y ∈ F, (srcLowerUnit S ^ (-(d : ℝ)) * srcLogConst S ^ c) *
          Wt (d : ℝ) c (linfNorm y : ℝ) := Finset.sum_le_sum hterm
    _ = (srcLowerUnit S ^ (-(d : ℝ)) * srcLogConst S ^ c) *
          ∑ y ∈ F, Wt (d : ℝ) c (linfNorm y : ℝ) := by rw [Finset.mul_sum]
    _ ≤ (srcLowerUnit S ^ (-(d : ℝ)) * srcLogConst S ^ c) *
          (tailShellConstLog d c * Wt (0 : ℝ) (c - 1) (S₀ / srcUpperConst S)) := by
        refine mul_le_mul_of_nonneg_left ?_ hK
        exact sum_Wt_tail_le_pureLog (d := d) hd hc
          (div_nonneg hS₀ (srcUpperConst_pos S).le) F htail

/-- **Weighted tail shell in the source norm, pure-logarithmic `tsum` form.** -/
theorem tsum_Wt_tail_le_pureLog_srcNorm (S : SourceNormData d) (hd : 1 ≤ d)
    {c S₀ : ℝ} (hc : 1 < c) (hS₀ : 0 ≤ S₀) :
    ∑' y : {y : Fin d → ℤ // S₀ < S.ρ (toVec y)},
        Wt (d : ℝ) c (S.ρ (toVec (y : Fin d → ℤ))) ≤
      srcLowerUnit S ^ (-(d : ℝ)) * srcLogConst S ^ c *
        (tailShellConstLog d c * Wt (0 : ℝ) (c - 1) (S₀ / srcUpperConst S)) := by
  classical
  have hnn : ∀ y : {y : Fin d → ℤ // S₀ < S.ρ (toVec y)},
      0 ≤ Wt (d : ℝ) c (S.ρ (toVec (y : Fin d → ℤ))) :=
    fun y => Wt_nonneg (src_nonneg S _)
  have hbound : ∀ u : Finset {y : Fin d → ℤ // S₀ < S.ρ (toVec y)},
      ∑ y ∈ u, Wt (d : ℝ) c (S.ρ (toVec (y : Fin d → ℤ))) ≤
        srcLowerUnit S ^ (-(d : ℝ)) * srcLogConst S ^ c *
          (tailShellConstLog d c * Wt (0 : ℝ) (c - 1) (S₀ / srcUpperConst S)) := by
    intro u
    have hinj : Set.InjOn (fun y : {y : Fin d → ℤ // S₀ < S.ρ (toVec y)} =>
        (y : Fin d → ℤ)) ↑u := fun a _ b _ hab => Subtype.ext hab
    have himg : ∑ y ∈ u, Wt (d : ℝ) c (S.ρ (toVec (y : Fin d → ℤ)))
        = ∑ z ∈ u.image (fun y : {y : Fin d → ℤ // S₀ < S.ρ (toVec y)} =>
            (y : Fin d → ℤ)), Wt (d : ℝ) c (S.ρ (toVec z)) := by
      rw [Finset.sum_image
        (f := fun z : Fin d → ℤ => Wt (d : ℝ) c (S.ρ (toVec z))) hinj]
    rw [himg]
    exact sum_Wt_tail_le_pureLog_srcNorm S hd hc hS₀ _ (fun z hz => by
      obtain ⟨y, _, rfl⟩ := Finset.mem_image.mp hz
      exact y.2)
  exact Summable.tsum_le_of_sum_le (summable_of_sum_le hnn hbound) hbound

/-- **The transferred `A3` bound in the paper's outer normalisation** (`γ > 0`).  The
far-region sum over the actual source radius is bounded by the outer profile
`(1+S₀)^{-γ} (log (2+S₀))^{-c}`, with a constant depending on the norm only. -/
theorem tsum_Wt_tail_le_srcNorm_outer (S : SourceNormData d) (hd : 1 ≤ d)
    {γ c S₀ : ℝ} (hγ : 0 < γ) (hc : 0 ≤ c) (hS₀ : 0 ≤ S₀) :
    ∑' y : {y : Fin d → ℤ // S₀ < S.ρ (toVec y)},
        Wt ((d : ℝ) + γ) c (S.ρ (toVec (y : Fin d → ℤ))) ≤
      srcLowerUnit S ^ (-((d : ℝ) + γ)) * srcLogConst S ^ c * srcTailConst S γ c *
        tailShellConst d γ * Wt γ c S₀ := by
  have h0 := tsum_Wt_tail_le_srcNorm S hd hγ hc hS₀
  have h1 : Wt γ c (S₀ / srcUpperConst S) ≤
      srcUpperConst S ^ γ * srcLogConstUpper S ^ c * Wt γ c S₀ :=
    Wt_div_srcUpper_le S (le_of_lt hγ) hc hS₀
  have hK : (0 : ℝ) ≤ srcLowerUnit S ^ (-((d : ℝ) + γ)) * srcLogConst S ^ c :=
    mul_nonneg (Real.rpow_nonneg (srcLowerUnit_pos S hd).le _)
      (Real.rpow_nonneg (srcLogConst_pos S hd).le _)
  have hT : (0 : ℝ) ≤ tailShellConst d γ := (tailShellConst_pos hd hγ).le
  calc _ ≤ srcLowerUnit S ^ (-((d : ℝ) + γ)) * srcLogConst S ^ c *
        (tailShellConst d γ * Wt γ c (S₀ / srcUpperConst S)) := h0
    _ ≤ srcLowerUnit S ^ (-((d : ℝ) + γ)) * srcLogConst S ^ c *
        (tailShellConst d γ * (srcUpperConst S ^ γ * srcLogConstUpper S ^ c * Wt γ c S₀)) := by
        refine mul_le_mul_of_nonneg_left ?_ hK
        exact mul_le_mul_of_nonneg_left h1 hT
    _ = srcLowerUnit S ^ (-((d : ℝ) + γ)) * srcLogConst S ^ c * srcTailConst S γ c *
        tailShellConst d γ * Wt γ c S₀ := by
        rw [srcTailConst]
        ring_nf

/-- **The transferred `A3` bound in the paper's outer normalisation, pure-logarithmic case.**
The exponent of the logarithm is `c - 1`, exactly as in the raw sup-norm estimate. -/
theorem tsum_Wt_tail_le_pureLog_srcNorm_outer (S : SourceNormData d) (hd : 1 ≤ d)
    {c S₀ : ℝ} (hc : 1 < c) (hS₀ : 0 ≤ S₀) :
    ∑' y : {y : Fin d → ℤ // S₀ < S.ρ (toVec y)},
        Wt (d : ℝ) c (S.ρ (toVec (y : Fin d → ℤ))) ≤
      srcLowerUnit S ^ (-(d : ℝ)) * srcLogConst S ^ c * srcTailConstPureLog S c *
        tailShellConstLog d c * Wt (0 : ℝ) (c - 1) S₀ := by
  have h0 := tsum_Wt_tail_le_pureLog_srcNorm S hd hc hS₀
  have h1 : Wt (0 : ℝ) (c - 1) (S₀ / srcUpperConst S) ≤
      srcUpperConst S ^ (0 : ℝ) * srcLogConstUpper S ^ (c - 1) * Wt (0 : ℝ) (c - 1) S₀ :=
    Wt_div_srcUpper_le S (by norm_num) (by linarith) hS₀
  have hK : (0 : ℝ) ≤ srcLowerUnit S ^ (-(d : ℝ)) * srcLogConst S ^ c :=
    mul_nonneg (Real.rpow_nonneg (srcLowerUnit_pos S hd).le _)
      (Real.rpow_nonneg (srcLogConst_pos S hd).le _)
  have hT : (0 : ℝ) ≤ tailShellConstLog d c := by
    have h1 : (0 : ℝ) < c - 1 := by linarith
    unfold tailShellConstLog
    positivity
  calc _ ≤ srcLowerUnit S ^ (-(d : ℝ)) * srcLogConst S ^ c *
        (tailShellConstLog d c * Wt (0 : ℝ) (c - 1) (S₀ / srcUpperConst S)) := h0
    _ ≤ srcLowerUnit S ^ (-(d : ℝ)) * srcLogConst S ^ c *
        (tailShellConstLog d c *
          (srcUpperConst S ^ (0 : ℝ) * srcLogConstUpper S ^ (c - 1) *
            Wt (0 : ℝ) (c - 1) S₀)) := by
        refine mul_le_mul_of_nonneg_left ?_ hK
        exact mul_le_mul_of_nonneg_left h1 hT
    _ = srcLowerUnit S ^ (-(d : ℝ)) * srcLogConst S ^ c * srcTailConstPureLog S c *
        tailShellConstLog d c * Wt (0 : ℝ) (c - 1) S₀ := by
        rw [srcTailConstPureLog]
        simp only [Real.rpow_zero, one_mul]
        ring


/-- **The `A1`/`A2` contribution of (I.4.12) for the source radius.**  Multiplying the
transferred ball-shell bound by the outer factor `〈S₀〉^{-d+bh} (log〈S₀〉)^{-bh}` gives the
source's displayed contribution `〈S₀〉^{-d+a+bh} (log〈S₀〉)^{-(bh+c)}`, exactly as for the raw
sup-norm version; no further analytic content enters, only the `rpow` bookkeeping. -/
theorem A1_contribution_bound_srcNorm (S : SourceNormData d) (hd : 1 ≤ d) {a c bh S₀ : ℝ}
    (ha : 0 < a) (haD : a < (d : ℝ)) (hc : 0 ≤ c) (hbh : 0 ≤ bh) (hS₀ : 0 ≤ S₀)
    {F : Finset (Fin d → ℤ)} (hrad : ∀ y ∈ F, S.ρ (toVec y) ≤ S₀) :
    (1 + S₀) ^ (-(d : ℝ) + bh) * LamR S₀ ^ (-bh) *
        (∑ y ∈ F, Wt ((d : ℝ) - a) c (S.ρ (toVec y)))
      ≤ 2 ^ a * (srcCountConst S * (1 + ((d : ℝ) - a + 2 * (c + 1)) * coreConst a c)) *
          ((1 + S₀) ^ (-(d : ℝ) + a + bh) * LamR S₀ ^ (-(bh + c))) :=
  A1_contribution_bound (ρ := fun y : Fin d → ℤ => S.ρ (toVec y))
    (fun y => src_nonneg S (toVec y)) ha haD hc hbh hS₀ (srcCountConst_nonneg S hd) hrad
    (srcNorm_ball_card_le S hd F)

end CriticalLRPConv

set_option linter.hashCommand false

/-! ## §8 Axiom audit -/

#print axioms CriticalLRPConv.dist_zero_eq_srcNorm
#print axioms CriticalLRPConv.norm_toVec_eq_linfNorm
#print axioms CriticalLRPConv.src_nonneg
#print axioms CriticalLRPConv.src_sum_le
#print axioms CriticalLRPConv.eq_sum_smul
#print axioms CriticalLRPConv.toVec_eq_sum_smul
#print axioms CriticalLRPConv.one_le_srcUpperConst
#print axioms CriticalLRPConv.srcUpperConst_pos
#print axioms CriticalLRPConv.srcNorm_le_upper
#print axioms CriticalLRPConv.srcNorm_le_upper_linfNorm
#print axioms CriticalLRPConv.exists_pos_mul_norm_le_src
#print axioms CriticalLRPConv.srcLowerConst_pos
#print axioms CriticalLRPConv.srcLowerConst_spec
#print axioms CriticalLRPConv.srcLowerUnit_pos
#print axioms CriticalLRPConv.srcLowerUnit_le_one
#print axioms CriticalLRPConv.srcLowerUnit_spec
#print axioms CriticalLRPConv.srcLowerUnit_mul_linfNorm_le
#print axioms CriticalLRPConv.srcCountConst_nonneg
#print axioms CriticalLRPConv.srcNorm_ball_subset_linfBall
#print axioms CriticalLRPConv.srcNorm_ball_card_le
#print axioms CriticalLRPConv.srcNorm_ball_shell_bound
#print axioms CriticalLRPConv.srcNorm_ball_shell_bound_lt
#print axioms CriticalLRPConv.LamR_le_logConst_mul
#print axioms CriticalLRPConv.Wt_le_of_le_mul
#print axioms CriticalLRPConv.Wt_srcNorm_le
#print axioms CriticalLRPConv.Wt_div_srcUpper_le
#print axioms CriticalLRPConv.srcLogConst_pos
#print axioms CriticalLRPConv.sum_Wt_tail_le_srcNorm
#print axioms CriticalLRPConv.tsum_Wt_tail_le_srcNorm
#print axioms CriticalLRPConv.sum_Wt_tail_le_pureLog_srcNorm
#print axioms CriticalLRPConv.tsum_Wt_tail_le_pureLog_srcNorm
#print axioms CriticalLRPConv.tsum_Wt_tail_le_srcNorm_outer
#print axioms CriticalLRPConv.tsum_Wt_tail_le_pureLog_srcNorm_outer
#print axioms CriticalLRPConv.A1_contribution_bound_srcNorm
