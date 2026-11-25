/-
Copyright (c) 2026 PercLib contributors. Released under Apache 2.0.
-/
module

public import PercLib.CriticalLRP.Orchestration.Defs
public import PercLib.CriticalLRP.Analysis.Cutoff.CornerRadii
public import PercLib.CriticalLRP.Analysis.Cutoff.OffCorner.SourceCutoffMoments
public import PercLib.CriticalLRP.Analysis.Cutoff.OffCorner.PowerLawContinuity
public import PercLib.CriticalLRP.Analysis.Cutoff.OffCorner.TwoPoint.Capstone
public import PercLib.CriticalLRP.CountableProduct.Compatibility
public import PercLib.CriticalLRP.CountableProduct.GhostCutoffCounterexample

/-!
# Exact attained radii and the degenerate cut-off regime of the source witness

The explicit source model `sourceModelWitness d hd α hα` of
`Orchestration/ModelWitness/Defs.lean` carries the normalized sup norm `ρ v = 2 ‖v‖∞` and the
exact power-law kernel `K r = r ^ (-d - α) / (d + α)`.  This file computes, for that model, the
two inputs that every cut-off continuity or derivative statement of the campaign takes as
hypotheses at small radii.

* **Attained radii.**  `r` is an attained radius exactly when `r = 2 n` for an integer `n ≥ 1`
  (`sourceModelWitness_attainedRadii_eq_two_mul_nat`).  Consequently `2` is attained, every odd
  radius and every radius in `(0, 2)` is off corner
  (`sourceModelWitness_two_mul_add_one_notMem_attainedRadii`,
  `sourceModelWitness_notMem_attainedRadii_of_lt_two`), and the off-corner hypothesis of the
  capstone is free there.  The mechanism is a general statement about *any* norm that is a
  positive multiple of the `ℓ∞` norm on `ℤ ^ d`
  (`SourceNormData.attainedRadii_eq_mul_nat`), proved through the landed bridge
  `Witness.sourceModelWitness_dist_eq` (`ρ = c ‖·‖∞` with `c = 2`) rather than through a
  bespoke lattice-side definition.
* **Degenerate cut-off.**  Distinct lattice points are at distance at least `2`
  (`sourceModelWitness_two_le_dist`), so for every parameter `r ≤ 2` the cut-off kernel
  vanishes identically (`sourceModelWitness_cutKernel_eq_zero_of_le_two`), the cut-off law is
  the point mass at the empty configuration
  (`sourceModelWitness_cutLaw_eq_dirac_empty_of_le_two`) and *every* cut-off cluster moment
  equals `1` exactly (`sourceModelWitness_cutMoment_eq_one_of_le_two`).  Since the cut-off
  profile of a pair at distance `s ≤ r` is `K s - K r`, the endpoint `r = 2` is included: at
  `r = 2` the nearest-neighbour pairs get weight `K 2 - K 2 = 0`.  So the threshold is `r ≤ 2`,
  not `r < 2`.  This is the campaign's integrated form of Definition I.1.5
  (`FiniteVolume.cutoffProfile`); under a hard-truncation reading `J 1(|x| ≤ r)` the endpoint
  `r = 2` would carry weight `K 2 > 0` and the sharp bound would be `r < 2` instead.
* **Consequence.**  On `0 < r0 < 2` the first-moment hypothesis of the landed capstone
  `SourceModelData.continuousAt_normalizedPivotMass` is discharged with the exact value `1`,
  leaving a continuity statement for the normalized pivot mass with no moment input at all
  (`sourceModelWitness_continuousAt_normalizedPivotMass_of_lt_two`).

Loops are handled where they must be: the radial kernel is `0` on `s(x, x)` by construction of
`radialSym`, and the open graph `openGraph ω` discards open loops (`openGraph_adj_iff` requires
distinct endpoints), so the empty configuration has cluster volume exactly `1`.  Nothing here is
a statement about radii `> 2`, about a `p`-th moment at a large radius, or about derivative /
absolute-continuity claims: those keep their own hypotheses.
-/

@[expose] public section

noncomputable section

open MeasureTheory Set MeasureTheory.Measure

namespace PercLib.CriticalLRP.FiniteVolume

/-- The axis vector with value `n` in coordinate `i` and `0` elsewhere has `ℓ∞` radius `n`. -/
theorem linfNorm_axis {d : ℕ} (i : Fin d) (n : ℕ) :
    linfNorm (fun j : Fin d => if j = i then (n : ℤ) else 0) = n := by
  apply le_antisymm
  · rw [linfNorm_le_iff]
    intro j
    by_cases hj : j = i
    · simp [hj]
    · simp [hj]
  · have h := Finset.le_sup (s := Finset.univ)
      (f := fun j : Fin d => (if j = i then (n : ℤ) else 0).natAbs) (Finset.mem_univ i)
    simpa [linfNorm] using h

end PercLib.CriticalLRP.FiniteVolume

namespace PercLib.CriticalLRP.Orchestration

open PercLib.CriticalLRP.FiniteVolume

/-! ## 1. Attained radii of a norm that is a positive multiple of `ℓ∞` -/

/-- The distance of two lattice points for a norm that is a positive multiple of the `ℓ∞`
norm is that multiple times the `ℓ∞` radius of their difference. -/
theorem SourceNormData.dist_eq_mul_linfNorm {d : ℕ} (S : SourceNormData d) {c : ℝ}
    (hρ : ∀ z : Fin d → ℤ, S.ρ (toVec z) = c * (linfNorm z : ℝ)) (x y : Fin d → ℤ) :
    S.dist x y = c * (linfNorm (x - y) : ℝ) :=
  hρ (x - y)

/-- **Exact attained radii of a scaled `ℓ∞` norm.**  If the norm of a source model is
`c ‖·‖∞` with `c > 0`, then the radii attained on nonzero lattice vectors are exactly the
positive multiples `c n`, `n ≥ 1`.  A nonzero integer vector has `ℓ∞` radius at least `1`, and
the axis vector shows that every `n ≥ 1` occurs. -/
theorem SourceNormData.attainedRadii_eq_mul_nat {d : ℕ} (S : SourceNormData d) (hd : 1 ≤ d)
    {c : ℝ} (hρ : ∀ z : Fin d → ℤ, S.ρ (toVec z) = c * (linfNorm z : ℝ)) :
    S.attainedRadii = {r : ℝ | ∃ n : ℕ, 1 ≤ n ∧ r = c * (n : ℝ)} := by
  ext r
  constructor
  · rintro ⟨x, hx, rfl⟩
    refine ⟨linfNorm x, ?_, ?_⟩
    · have hne : linfNorm x ≠ 0 := fun h => hx (linfNorm_eq_zero_iff.mp h)
      omega
    · rw [SourceNormData.dist_zero_right]
      exact hρ x
  · rintro ⟨n, hn, rfl⟩
    have hd0 : 0 < d := by omega
    refine ⟨fun j : Fin d => if j = ⟨0, hd0⟩ then (n : ℤ) else 0, ?_, ?_⟩
    · intro hzero
      have h1 := congrFun hzero ⟨0, hd0⟩
      simp at h1
      omega
    · rw [SourceNormData.dist_zero_right, hρ, linfNorm_axis]

/-- The off-corner condition in membership form for a scaled `ℓ∞` norm. -/
theorem SourceNormData.mem_attainedRadii_iff_mul_nat {d : ℕ} (S : SourceNormData d)
    (hd : 1 ≤ d) {c : ℝ} (hρ : ∀ z : Fin d → ℤ, S.ρ (toVec z) = c * (linfNorm z : ℝ)) {r : ℝ} :
    r ∈ S.attainedRadii ↔ ∃ n : ℕ, 1 ≤ n ∧ r = c * (n : ℝ) := by
  rw [SourceNormData.attainedRadii_eq_mul_nat S hd hρ]
  exact Iff.rfl

namespace Witness

/-! ## 2. The source witness: attained radii are the even positive integers -/

/-- **The attained radii of the source witness are exactly `{2 n | n ≥ 1}`.** -/
theorem sourceModelWitness_attainedRadii_eq_two_mul_nat (d : ℕ) (hd : 1 ≤ d) (α : ℝ)
    (hα : 0 < α) :
    (sourceModelWitness d hd α hα).attainedRadii =
      {r : ℝ | ∃ n : ℕ, 1 ≤ n ∧ r = 2 * (n : ℝ)} :=
  SourceNormData.attainedRadii_eq_mul_nat (sourceModelWitness d hd α hα).S hd
    (sourceModelWitness_dist_eq d hd α hα)

/-- Membership form: `r` is an attained radius of the witness exactly when `r = 2 n` for an
integer `n ≥ 1`. -/
theorem sourceModelWitness_mem_attainedRadii_iff_two_mul (d : ℕ) (hd : 1 ≤ d) (α : ℝ)
    (hα : 0 < α) {r : ℝ} :
    r ∈ (sourceModelWitness d hd α hα).attainedRadii ↔ ∃ n : ℕ, 1 ≤ n ∧ r = 2 * (n : ℝ) :=
  SourceNormData.mem_attainedRadii_iff_mul_nat (sourceModelWitness d hd α hα).S hd
    (sourceModelWitness_dist_eq d hd α hα)

/-- The radius `2` is attained by the witness: the nearest-neighbour vector of the sup norm has
norm radius `1`.  So the lower bound `2` for attained radii is sharp. -/
theorem sourceModelWitness_two_mem_attainedRadii (d : ℕ) (hd : 1 ≤ d) (α : ℝ) (hα : 0 < α) :
    (2 : ℝ) ∈ (sourceModelWitness d hd α hα).attainedRadii := by
  rw [sourceModelWitness_mem_attainedRadii_iff_two_mul d hd α hα]
  exact ⟨1, le_rfl, by norm_num⟩

/-- Every radius strictly below `2` is off corner for the witness. -/
theorem sourceModelWitness_notMem_attainedRadii_of_lt_two (d : ℕ) (hd : 1 ≤ d) (α : ℝ)
    (hα : 0 < α) {r : ℝ} (hr : r < 2) : r ∉ (sourceModelWitness d hd α hα).attainedRadii := by
  rw [sourceModelWitness_mem_attainedRadii_iff_two_mul d hd α hα]
  rintro ⟨n, hn, rfl⟩
  have hn1 : (1 : ℝ) ≤ (n : ℝ) := by exact_mod_cast hn
  linarith

/-- Every odd radius `2 n + 1` is off corner for the witness. -/
theorem sourceModelWitness_two_mul_add_one_notMem_attainedRadii (d : ℕ) (hd : 1 ≤ d) (α : ℝ)
    (hα : 0 < α) (n : ℕ) :
    2 * (n : ℝ) + 1 ∉ (sourceModelWitness d hd α hα).attainedRadii := by
  rw [sourceModelWitness_mem_attainedRadii_iff_two_mul d hd α hα]
  rintro ⟨m, -, heq⟩
  have hcast : ((2 * m : ℕ) : ℝ) = ((2 * n + 1 : ℕ) : ℝ) := by
    push_cast
    linarith
  have hnat : 2 * m = 2 * n + 1 := Nat.cast_injective hcast
  omega

end Witness

/-! ## 3. A lattice separated by `c` has no cut-off edges below radius `c` -/

/-- **A lattice separated by `c` has no cut-off edges at any parameter `r ≤ c`.**  At a
parameter `r` below the separation the cut-off profile of a pair at distance `> r` is zero, at a
pair at distance `≤ r` it is `K s - K r` with `s = r = c`, and loops are killed by the radial
kernel. -/
theorem SourceModelData.cutKernel_eq_zero_of_separated (M : SourceModelData) {c r : ℝ}
    (hsep : ∀ x y : M.V, x ≠ y → c ≤ M.S.dist x y) (hr : r ≤ c) : M.cutKernel r = 0 := by
  funext e
  induction e using Sym2.ind with
  | h x y =>
    change M.cutKernel r s(x, y) = 0
    rw [SourceModelData.cutKernel, cutRadialSym, radialSym_mk]
    by_cases hxy : x = y
    · rw [ite_eq_left hxy]
    · rw [ite_eq_right hxy]
      have hcr : c ≤ M.S.dist x y := hsep x y hxy
      rcases lt_or_ge r (M.S.dist x y) with hlt | hge
      · exact FiniteVolume.cutoffProfile_of_lt hlt
      · rw [FiniteVolume.cutoffProfile_of_le hge]
        have hrc : r = c := le_antisymm hr (le_trans hcr hge)
        have hdc : M.S.dist x y = c := le_antisymm (le_trans hge hr) hcr
        rw [hdc, hrc]
        exact sub_self _

/-- **A vanishing cut-off kernel gives the empty configuration.**  If the cut-off kernel is
identically zero then no pair is open, so the cut-off law is the point mass at `∅`. -/
theorem SourceModelData.cutLaw_eq_dirac_empty_of_cutKernel_eq_zero (M : SourceModelData) {r : ℝ}
    (h : M.cutKernel r = 0) : M.cutLaw r = dirac (∅ : Config M.V) := by
  have hprob : PercLib.CriticalLRP.bernoulliEdgeProb (M.cutKernel r) (M.cutKernel_nonneg r)
      M.betaCrit = fun _ => (0 : unitInterval) := by
    funext e
    apply Subtype.ext
    rw [PercLib.CriticalLRP.bernoulliEdgeProb_coe]
    simp [h]
  rw [SourceModelData.cutLaw, PercLib.CriticalLRP.longRangeMeasure, hprob]
  exact PercLib.CriticalLRP.edgeMeasure_zero

/-- **A vanishing cut-off kernel gives unit moments.**  The cut-off cluster of the origin in the
empty configuration is the origin itself, of volume `1`. -/
theorem SourceModelData.cutMoment_eq_one_of_cutKernel_eq_zero (M : SourceModelData) {r : ℝ}
    (h : M.cutKernel r = 0) (p : ℕ) : M.cutMoment p r = 1 := by
  rw [SourceModelData.cutMoment, M.cutLaw_eq_dirac_empty_of_cutKernel_eq_zero h, lintegral_dirac,
    PercLib.CriticalLRP.clusterVol_empty]
  exact one_pow p

/-- Hence every cut-off moment is finite in the degenerate regime. -/
theorem SourceModelData.cutMoment_ne_top_of_cutKernel_eq_zero (M : SourceModelData) {r : ℝ}
    (h : M.cutKernel r = 0) (p : ℕ) : M.cutMoment p r ≠ ⊤ := by
  rw [M.cutMoment_eq_one_of_cutKernel_eq_zero h p]
  exact ENNReal.one_ne_top

namespace Witness

/-! ## 4. The source witness below radius `2`: the cut-off model has no edges -/

/-- **Distinct lattice points of the witness are at distance at least `2`.**  The distance of two
distinct points is an attained radius of the witness (`SourceNormData.mem_attainedRadii_of_dist`),
and the landed theorem `sourceModelWitness_two_le_of_mem_attainedRadii` bounds every attained
radius below by `2`; nothing is recomputed here. -/
theorem sourceModelWitness_two_le_dist (d : ℕ) (hd : 1 ≤ d) (α : ℝ) (hα : 0 < α)
    {x y : Fin d → ℤ} (hxy : x ≠ y) : 2 ≤ (sourceModelWitness d hd α hα).S.dist x y :=
  sourceModelWitness_two_le_of_mem_attainedRadii d hd α hα
    (SourceNormData.mem_attainedRadii_of_dist (sourceModelWitness d hd α hα).S hxy)

/-- **No cut-off edges at any parameter `r ≤ 2`.**  In particular the cut-off kernel vanishes
at every radius strictly below `2`. -/
theorem sourceModelWitness_cutKernel_eq_zero_of_le_two (d : ℕ) (hd : 1 ≤ d) (α : ℝ)
    (hα : 0 < α) {r : ℝ} (hr : r ≤ 2) :
    (sourceModelWitness d hd α hα).cutKernel r = 0 :=
  SourceModelData.cutKernel_eq_zero_of_separated (sourceModelWitness d hd α hα)
    (fun _ _ hxy => sourceModelWitness_two_le_dist d hd α hα hxy) hr

/-- **The cut-off law below radius `2` is the empty configuration.** -/
theorem sourceModelWitness_cutLaw_eq_dirac_empty_of_le_two (d : ℕ) (hd : 1 ≤ d) (α : ℝ)
    (hα : 0 < α) {r : ℝ} (hr : r ≤ 2) :
    (sourceModelWitness d hd α hα).cutLaw r = dirac (∅ : Config (Fin d → ℤ)) :=
  SourceModelData.cutLaw_eq_dirac_empty_of_cutKernel_eq_zero (sourceModelWitness d hd α hα)
    (sourceModelWitness_cutKernel_eq_zero_of_le_two d hd α hα hr)

/-- **Every cut-off moment equals `1` below radius `2`.** -/
theorem sourceModelWitness_cutMoment_eq_one_of_le_two (d : ℕ) (hd : 1 ≤ d) (α : ℝ) (hα : 0 < α)
    {r : ℝ} (hr : r ≤ 2) (p : ℕ) : (sourceModelWitness d hd α hα).cutMoment p r = 1 :=
  SourceModelData.cutMoment_eq_one_of_cutKernel_eq_zero (sourceModelWitness d hd α hα)
    (sourceModelWitness_cutKernel_eq_zero_of_le_two d hd α hα hr) p

/-- Consequently every cut-off moment of the witness is finite below radius `2`. -/
theorem sourceModelWitness_cutMoment_ne_top_of_le_two (d : ℕ) (hd : 1 ≤ d) (α : ℝ)
    (hα : 0 < α) {r : ℝ} (hr : r ≤ 2) (p : ℕ) :
    (sourceModelWitness d hd α hα).cutMoment p r ≠ ⊤ :=
  SourceModelData.cutMoment_ne_top_of_cutKernel_eq_zero (sourceModelWitness d hd α hα)
    (sourceModelWitness_cutKernel_eq_zero_of_le_two d hd α hα hr) p

/-- **Hypothesis-free small-radius continuity of the normalized pivot mass.**  For every
`0 < r0 < 2` the normalized pivot mass of the source witness is continuous at `r0`, with no
moment hypothesis: the capstone
`SourceModelData.continuousAt_normalizedPivotMass` is applied at the intermediate radius
`(r0 + 2) / 2 < 2`, where the first cut-off moment is exactly `1`.  This is the degenerate
regime where the cut-off model has no edges; it asserts nothing at any radius `≥ 2`. -/
theorem sourceModelWitness_continuousAt_normalizedPivotMass_of_lt_two (d : ℕ) (hd : 1 ≤ d)
    (α : ℝ) (hα : 0 < α) (y : Fin d → ℤ) {r0 : ℝ} (hr0 : 0 < r0) (hr2 : r0 < 2) :
    ContinuousAt ((sourceModelWitness d hd α hα).normalizedPivotMass y) r0 := by
  have hR : r0 < (r0 + 2) / 2 := by linarith
  have hR2 : (r0 + 2) / 2 ≤ 2 := by linarith
  refine SourceModelData.continuousAt_normalizedPivotMass
    (M := sourceModelWitness d hd α hα) (y := y) hr0 hR ?_ ?_
  · exact sourceModelWitness_notMem_attainedRadii_of_lt_two d hd α hα hr2
  · rw [sourceModelWitness_cutMoment_eq_one_of_le_two d hd α hα hR2 1]
    exact ENNReal.one_ne_top

end Witness

end PercLib.CriticalLRP.Orchestration
