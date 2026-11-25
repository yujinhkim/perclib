/-
Copyright (c) 2026 PercLib contributors. Released under Apache 2.0.

Integrated from Ultramath `smwv4hzkh`, member `m2`, direction C1, and independently
rebuilt before integration. The first-moment wrapper uses the separately rebuilt
moment transfer from swarm finding `smwv4hzkh/d3/f1`.
-/
module

public import PercLib.CriticalLRP.Analysis.Cutoff.OffCorner.TwoPoint.Capstone
public import PercLib.CriticalLRP.Analysis.Cutoff.OffCorner.PowerLawDeriv
public import PercLib.CriticalLRP.Analysis.Cutoff.OffCorner.RadiusExcludedMass
public import PercLib.CriticalLRP.Analysis.Cutoff.CornerRadii.Defs
public import PercLib.CriticalLRP.Analysis.Cutoff.RowMassSmall
public import PercLib.CriticalLRP.Analysis.Cutoff.Fibre.Expectation.Defs
public import PercLib.CriticalLRP.Analysis.LatticeConvolution.NormShell
public import PercLib.CriticalLRP.Orchestration.ModelWitness.Defs
public import PercLib.CriticalLRP.Analysis.Cutoff.OffCorner.SourceCutoffMoments

/-!
# Window integration of off-corner regularity at the explicit power-law model

`OffCorner/TwoPoint/Capstone.lean` proves continuity of the normalized pivotal mass at a single
off-corner radius from a finite *first* cutoff moment at a strictly larger radius.  The endpoint
derivative wrappers in `OffCorner/PowerLawDeriv.lean` consume, instead, the per-vertex flux
continuity `hcontinf` on a whole window, and the counted honest wrappers
(`sourceModelWitness_hasDerivAt_cutMassReal_powerLaw_of_moments`) still carry `hcontinf`.

This packet runs the three steps for the literal model `sourceModelWitness d hd α hα`:

* §1 the window statement `∀ y, ∀ r ∈ Ioo a b, ContinuousAt (normalizedPivotMass y) r` from the
  off-corner condition on the window and a finite **second** moment at the right endpoint `b`
  (the first moment at `b` follows from `cutMoment_one_le_cutMoment_two`);
* §2 its consequence `hcontinf` on the same window, with no flux hypothesis left;
* §3 the power-law `HasDerivAt` at an interior point with `hcontinf` eliminated: only the window,
  its off-corner condition, the `p = 2` and `p = 3` endpoint moments, and exhaustion data remain;
* §4 the last hypotheses are then removed at *small* radius: no attained radius of the witness is
  below `2` (`ρ = 2‖·‖∞` and nonzero integral vectors have sup norm at least `1`), and
  `exists_forall_cutMoment_ne_top_small_radius` supplies every moment at a small right endpoint,
  so the canonical `codeWindow` exhaustion makes the statement hypothesis-free:
  there is `b > 0` such that for every `0 < r0 < b` the cutoff mass has the paper's derivative
  `β_c r0 ^ (-d - α - 1) (exclMass r0)`.

What is *not* claimed: nothing at large radii.  The window at §1–§3 still has to be off-corner
and still has to carry the moments, and no statement here becomes uniform in the model.
-/

@[expose] public section

set_option autoImplicit false
set_option linter.style.longLine false
set_option linter.hashCommand false

noncomputable section

open MeasureTheory Filter Topology Set
open scoped ENNReal NNReal Topology

namespace PercLib.CriticalLRP.Orchestration.Witness

open PercLib.CriticalLRP.Orchestration
open PercLib.CriticalLRP.FiniteVolume (linfNorm linfNorm_eq_zero_iff)

/-! ## 1. Window continuity of the normalized pivotal mass at the explicit model -/

/-- **Window continuity of the normalized pivotal mass.**  For the literal power-law witness, the
normalized pivotal mass is continuous at every point of an off-corner window `(a, b)` as soon as
the *second* cutoff moment at `b` is finite.  The first moment at `b` that
`SourceModelData.continuousAt_normalizedPivotMass` asks for is derived here from the second. -/
theorem sourceModelWitness_continuousAt_normalizedPivotMass_of_window
    (d : ℕ) (hd : 1 ≤ d) (α : ℝ) (hα : 0 < α) {a b : ℝ} (ha : 0 < a)
    (hoff : ∀ r ∈ Set.Ioo a b, r ∉ (sourceModelWitness d hd α hα).cornerRadii)
    (h2b : (sourceModelWitness d hd α hα).cutMoment 2 b ≠ ⊤) :
    ∀ y : (sourceModelWitness d hd α hα).V, ∀ r ∈ Set.Ioo a b,
      ContinuousAt ((sourceModelWitness d hd α hα).normalizedPivotMass y) r := by
  intro y r hr
  have h1b : (sourceModelWitness d hd α hα).cutMoment 1 b ≠ ⊤ :=
    ne_top_of_le_ne_top h2b
      (SourceModelData.cutMoment_one_le_cutMoment_two (sourceModelWitness d hd α hα) b)
  refine SourceModelData.continuousAt_normalizedPivotMass (M := sourceModelWitness d hd α hα)
    (y := y) (ha.trans hr.1) hr.2 ?_ h1b
  rw [SourceModelData.attainedRadii_eq_cornerRadii]
  exact hoff r hr

/-! ## 2. Per-vertex flux continuity on a window, with no flux hypothesis -/

/-- **`hcontinf` from the second endpoint moment.**  The exact flux-continuity input consumed by
the endpoint derivative wrappers holds on an off-corner window from a finite second moment at the
right endpoint; no separate continuity of a per-vertex flux is assumed. -/
theorem sourceModelWitness_hcontinf_of_moment_two
    (d : ℕ) (hd : 1 ≤ d) (α : ℝ) (hα : 0 < α) {a b : ℝ} (ha : 0 < a)
    (hoff : ∀ r ∈ Set.Ioo a b, r ∉ (sourceModelWitness d hd α hα).cornerRadii)
    (h2b : (sourceModelWitness d hd α hα).cutMoment 2 b ≠ ⊤) :
    ∀ y : (sourceModelWitness d hd α hα).V, ∀ r ∈ Set.Ioo a b, ContinuousAt
      (sMomentInfFlux (0 : (sourceModelWitness d hd α hα).V)
        ({y} : Finset (sourceModelWitness d hd α hα).V) (fun _ => (1 : ℝ))
        (sourceModelWitness d hd α hα).cutProb
        (sourceModelWitness d hd α hα).cutEdgeDeriv) r :=
  sourceModelWitness_hcontinf d hd α hα ha
    (sourceModelWitness_continuousAt_normalizedPivotMass_of_window d hd α hα ha hoff h2b)


/-! ## 3. The power-law endpoint derivative with `hcontinf` eliminated -/

/-- **The envelope endpoint derivative at the explicit model with `hcontinf` discharged.**  This is
`sourceModelWitness_hasDerivAt_cutMassReal_rhsScalar_of_endpoint_of_moments` with its last
regularity input replaced by the window continuity of §1: the remaining data are the radius window
`a < r0 < b` off the corner set, the finite `p = 2` and `p = 3` cutoff moments *at the right
endpoint*, and the two exhaustions. -/
theorem sourceModelWitness_hasDerivAt_cutMassReal_rhsScalar_of_moments_of_window
    (d : ℕ) (hd : 1 ≤ d) (α : ℝ) (hα : 0 < α)
    (T : ℕ → Finset (sourceModelWitness d hd α hα).V) (hTmono : Monotone T)
    (hT : ∀ y : (sourceModelWitness d hd α hα).V, ∃ n, y ∈ T n)
    (S : ℕ → Finset (Sym2 (sourceModelWitness d hd α hα).V)) (hSmono : Monotone S)
    (hS : ∀ e : Sym2 (sourceModelWitness d hd α hα).V, ∃ n, e ∈ S n)
    {a b r0 : ℝ} (ha : 0 < a) (har0 : a < r0) (hr0b : r0 < b)
    (hoff : ∀ r ∈ Set.Ioo a b, r ∉ (sourceModelWitness d hd α hα).cornerRadii)
    (h2b : (sourceModelWitness d hd α hα).cutMoment 2 b ≠ ⊤)
    (h3b : (sourceModelWitness d hd α hα).cutMoment 3 b ≠ ⊤) :
    HasDerivAt (sourceModelWitness d hd α hα).cutMassReal
      ((sourceModelWitness d hd α hα).rhsScalar r0) r0 :=
  sourceModelWitness_hasDerivAt_cutMassReal_rhsScalar_of_endpoint_of_moments d hd α hα T hTmono hT
    S hSmono hS ha har0 hr0b hoff h2b h3b
    (sourceModelWitness_hcontinf_of_moment_two d hd α hα ha hoff h2b)

/-- **The power-law endpoint derivative at the explicit model with `hcontinf` eliminated**, in the
paper's scale `d/dr χ(r) = β_c r ^ (-d - α - 1) (exclMass r)`. -/
theorem sourceModelWitness_hasDerivAt_cutMassReal_powerLaw_of_moments_of_window
    (d : ℕ) (hd : 1 ≤ d) (α : ℝ) (hα : 0 < α)
    (T : ℕ → Finset (sourceModelWitness d hd α hα).V) (hTmono : Monotone T)
    (hT : ∀ y : (sourceModelWitness d hd α hα).V, ∃ n, y ∈ T n)
    (S : ℕ → Finset (Sym2 (sourceModelWitness d hd α hα).V)) (hSmono : Monotone S)
    (hS : ∀ e : Sym2 (sourceModelWitness d hd α hα).V, ∃ n, e ∈ S n)
    {a b r0 : ℝ} (ha : 0 < a) (har0 : a < r0) (hr0b : r0 < b)
    (hoff : ∀ r ∈ Set.Ioo a b, r ∉ (sourceModelWitness d hd α hα).cornerRadii)
    (h2b : (sourceModelWitness d hd α hα).cutMoment 2 b ≠ ⊤)
    (h3b : (sourceModelWitness d hd α hα).cutMoment 3 b ≠ ⊤) :
    HasDerivAt (sourceModelWitness d hd α hα).cutMassReal
      (((sourceModelWitness d hd α hα).betaCrit : ℝ) * r0 ^ (-(d : ℝ) - α - 1) *
        (sourceModelWitness d hd α hα).exclScalar r0) r0 :=
  sourceModelWitness_hasDerivAt_cutMassReal_powerLaw_of_moments d hd α hα T hTmono hT S hSmono hS
    ha har0 hr0b hoff h2b h3b (sourceModelWitness_hcontinf_of_moment_two d hd α hα ha hoff h2b)

/-! ## 4. No corner radius below `2`, and a hypothesis-free small-radius statement -/

/-- **Every attained radius of the explicit model is at least `2`.**  The model's norm is
`ρ v = 2 ‖v‖∞`, and a nonzero integral vector has sup norm at least `1`. -/
theorem sourceModelWitness_two_le_of_mem_attainedRadii
    (d : ℕ) (hd : 1 ≤ d) (α : ℝ) (hα : 0 < α) {r : ℝ}
    (hr : r ∈ (sourceModelWitness d hd α hα).attainedRadii) : 2 ≤ r := by
  obtain ⟨x, hx, hxr⟩ := SourceModelData.mem_attainedRadii.mp hr
  have hdist : (sourceModelWitness d hd α hα).S.dist x 0 = 2 * ‖toVec x‖ := by
    rw [SourceNormData.dist_zero_right]
    rfl
  have hlin : (1 : ℝ) ≤ (linfNorm x : ℝ) := by
    have hne : linfNorm x ≠ 0 := fun h =>
      hx (linfNorm_eq_zero_iff.mp h)
    exact_mod_cast Nat.one_le_iff_ne_zero.mpr hne
  rw [← hxr, hdist, CriticalLRPConv.norm_toVec_eq_linfNorm]
  linarith

/-- **The explicit model has no corner radius below `2`**, so every window inside `(0, 2)` is
automatically off corner. -/
theorem sourceModelWitness_notMem_cornerRadii_of_lt_two
    (d : ℕ) (hd : 1 ≤ d) (α : ℝ) (hα : 0 < α) {r : ℝ} (hr : r < 2) :
    r ∉ (sourceModelWitness d hd α hα).cornerRadii := by
  rw [← SourceModelData.attainedRadii_eq_cornerRadii]
  exact fun h => absurd (sourceModelWitness_two_le_of_mem_attainedRadii d hd α hα h)
    (not_le.mpr hr)

/-- **A hypothesis-free small-radius derivative for the explicit model.**  There is a positive
radius `b` — taken from the cutoff row-mass smallness theorem and capped below the first attained
radius `2` — such that for every `0 < r0 < b` the cutoff mass has the source's derivative
`β_c r0 ^ (-d - α - 1) (exclMass r0)`.  The window, its off-corner condition, the `p = 2` and
`p = 3` moments, and the two exhaustions are all discharged here (`codeWindow` is the canonical
exhaustion of the vertex set, and `Sym2` of it exhausts the edge set); `β_c` positivity is not
needed. -/
theorem sourceModelWitness_exists_small_radius_hasDerivAt_powerLaw
    (d : ℕ) (hd : 1 ≤ d) (α : ℝ) (hα : 0 < α) :
    ∃ b : ℝ, 0 < b ∧ ∀ r0 : ℝ, 0 < r0 → r0 < b →
      HasDerivAt (sourceModelWitness d hd α hα).cutMassReal
        (((sourceModelWitness d hd α hα).betaCrit : ℝ) * r0 ^ (-(d : ℝ) - α - 1) *
          (sourceModelWitness d hd α hα).exclScalar r0) r0 := by
  obtain ⟨t0, r₁, ht0, hr₁, hmom⟩ :=
    PercLib.CriticalLRP.SmallCutoffRowMass.exists_forall_cutMoment_ne_top_small_radius
      (sourceModelWitness d hd α hα)
  have hbpos : 0 < min (r₁ / 2) 1 := lt_min (by linarith) one_pos
  have hbr₁ : min (r₁ / 2) 1 < r₁ := lt_of_le_of_lt (min_le_left _ _) (by linarith)
  have hb2 : min (r₁ / 2) 1 ≤ 2 := le_trans (min_le_right _ _) (by norm_num)
  refine ⟨min (r₁ / 2) 1, hbpos, ?_⟩
  intro r0 _ hr0b
  have h2b : (sourceModelWitness d hd α hα).cutMoment 2 (min (r₁ / 2) 1) ≠ ⊤ :=
    (hmom _ hbpos hbr₁).1 2
  have h3b : (sourceModelWitness d hd α hα).cutMoment 3 (min (r₁ / 2) 1) ≠ ⊤ :=
    (hmom _ hbpos hbr₁).1 3
  have hoff : ∀ r ∈ Set.Ioo (r0 / 2) (min (r₁ / 2) 1),
      r ∉ (sourceModelWitness d hd α hα).cornerRadii := fun r hr =>
    sourceModelWitness_notMem_cornerRadii_of_lt_two d hd α hα (lt_of_lt_of_le hr.2 hb2)
  refine sourceModelWitness_hasDerivAt_cutMassReal_powerLaw_of_moments_of_window d hd α hα
    (codeWindow (sourceModelWitness d hd α hα).V) (monotone_codeWindow _)
    (fun y => ⟨code _ y, mem_codeWindow.mpr le_rfl⟩)
    (fun n => (codeWindow (sourceModelWitness d hd α hα).V n).sym2)
    (Finset.monotone_sym2.comp (monotone_codeWindow _)) ?_
    (a := r0 / 2) (b := min (r₁ / 2) 1) (r0 := r0) (by linarith) (by linarith) hr0b hoff h2b h3b
  intro e
  induction e using Sym2.ind with
  | _ x y =>
    exact ⟨max (code _ x) (code _ y), Finset.mk_mem_sym2_iff.mpr
      ⟨mem_codeWindow.mpr (le_max_left _ _), mem_codeWindow.mpr (le_max_right _ _)⟩⟩

end PercLib.CriticalLRP.Orchestration.Witness

/-! ## 5. From a single off-corner radius to a corner-free window

The wrappers above take an off-corner *window*.  Locally finiteness of the attained radii
(`SourceModelData.exists_nhds_notMem_attainedRadii`) turns a single off-corner radius into such a
window, and the endpoint of the window can be pushed below any prescribed larger radius so that
the moments only have to be finite at that larger radius. -/

namespace PercLib.CriticalLRP.Orchestration

/-- **An off-corner radius sits in a corner-free window that ends below any larger radius.**  For
`0 < r0 < R` with `r0` not an attained radius there are `a < r0 < b ≤ R`, `a > 0`, such that no
radius in `(a, b)` is attained.  This is the conversion from the single-radius hypotheses of the
capstone to the window hypotheses of the endpoint derivative wrappers. -/
theorem SourceModelData.exists_window_notMem_attainedRadii (M : SourceModelData) {r0 R : ℝ}
    (hr0 : 0 < r0) (hr0R : r0 < R) (hoff : r0 ∉ M.attainedRadii) :
    ∃ a b : ℝ, 0 < a ∧ a < r0 ∧ r0 < b ∧ b ≤ R ∧ ∀ r ∈ Set.Ioo a b, r ∉ M.attainedRadii := by
  obtain ⟨ε, hε, hball⟩ := M.exists_nhds_notMem_attainedRadii hoff
  refine ⟨max (r0 - ε / 2) (r0 / 2), min (r0 + ε / 2) R,
    lt_max_iff.mpr (Or.inr (by linarith)), max_lt (by linarith) (by linarith),
    lt_min (by linarith) hr0R, min_le_right _ _, ?_⟩
  intro r hr
  have hrlt : r < r0 + ε := by
    have h1 : r < min (r0 + ε / 2) R := hr.2
    have h2 : min (r0 + ε / 2) R ≤ r0 + ε / 2 := min_le_left _ _
    linarith
  have hrgt : r0 - ε < r := by
    have h1 : max (r0 - ε / 2) (r0 / 2) < r := hr.1
    have h2 : r0 - ε / 2 ≤ max (r0 - ε / 2) (r0 / 2) := le_max_left _ _
    linarith
  exact hball r (abs_sub_lt_iff.mpr ⟨by linarith, by linarith⟩)

end PercLib.CriticalLRP.Orchestration

namespace PercLib.CriticalLRP.Orchestration.Witness

/-- **The power-law endpoint derivative at a single off-corner radius, with a moment radius
above it.**  Only `0 < r0 < R`, `r0 ∉ cornerRadii`, finiteness of the `p = 2` and `p = 3` cutoff
moments at `R`, and the two exhaustions remain. -/
theorem sourceModelWitness_hasDerivAt_cutMassReal_powerLaw_of_moments_of_offCorner
    (d : ℕ) (hd : 1 ≤ d) (α : ℝ) (hα : 0 < α)
    (T : ℕ → Finset (sourceModelWitness d hd α hα).V) (hTmono : Monotone T)
    (hT : ∀ y : (sourceModelWitness d hd α hα).V, ∃ n, y ∈ T n)
    (S : ℕ → Finset (Sym2 (sourceModelWitness d hd α hα).V)) (hSmono : Monotone S)
    (hS : ∀ e : Sym2 (sourceModelWitness d hd α hα).V, ∃ n, e ∈ S n)
    {r0 R : ℝ} (hr0 : 0 < r0) (hr0R : r0 < R)
    (hoff : r0 ∉ (sourceModelWitness d hd α hα).cornerRadii)
    (h2R : (sourceModelWitness d hd α hα).cutMoment 2 R ≠ ⊤)
    (h3R : (sourceModelWitness d hd α hα).cutMoment 3 R ≠ ⊤) :
    HasDerivAt (sourceModelWitness d hd α hα).cutMassReal
      (((sourceModelWitness d hd α hα).betaCrit : ℝ) * r0 ^ (-(d : ℝ) - α - 1) *
        (sourceModelWitness d hd α hα).exclScalar r0) r0 := by
  obtain ⟨a, b, ha, har0, hr0b, hbR, hwin⟩ :=
    SourceModelData.exists_window_notMem_attainedRadii (sourceModelWitness d hd α hα) hr0 hr0R
      (by rwa [SourceModelData.attainedRadii_eq_cornerRadii])
  refine sourceModelWitness_hasDerivAt_cutMassReal_powerLaw_of_moments_of_window d hd α hα T hTmono
    hT S hSmono hS ha har0 hr0b ?_
    (SourceModelData.cutMoment_ne_top_of_le (sourceModelWitness d hd α hα) hbR 2 h2R)
    (SourceModelData.cutMoment_ne_top_of_le (sourceModelWitness d hd α hα) hbR 3 h3R)
  intro r hr
  rw [← SourceModelData.attainedRadii_eq_cornerRadii]
  exact hwin r hr

/-- **The same statement with the canonical `codeWindow` exhaustions**, so the exhaustions no
longer appear as inputs. -/
theorem sourceModelWitness_hasDerivAt_cutMassReal_powerLaw_of_offCorner
    (d : ℕ) (hd : 1 ≤ d) (α : ℝ) (hα : 0 < α) {r0 R : ℝ} (hr0 : 0 < r0) (hr0R : r0 < R)
    (hoff : r0 ∉ (sourceModelWitness d hd α hα).cornerRadii)
    (h2R : (sourceModelWitness d hd α hα).cutMoment 2 R ≠ ⊤)
    (h3R : (sourceModelWitness d hd α hα).cutMoment 3 R ≠ ⊤) :
    HasDerivAt (sourceModelWitness d hd α hα).cutMassReal
      (((sourceModelWitness d hd α hα).betaCrit : ℝ) * r0 ^ (-(d : ℝ) - α - 1) *
        (sourceModelWitness d hd α hα).exclScalar r0) r0 :=
  sourceModelWitness_hasDerivAt_cutMassReal_powerLaw_of_moments_of_offCorner d hd α hα
    (codeWindow (sourceModelWitness d hd α hα).V) (monotone_codeWindow _)
    (fun y => ⟨code _ y, mem_codeWindow.mpr le_rfl⟩)
    (fun n => (codeWindow (sourceModelWitness d hd α hα).V n).sym2)
    (Finset.monotone_sym2.comp (monotone_codeWindow _)) (fun e => by
      induction e using Sym2.ind with
      | _ x y =>
        exact ⟨max (code _ x) (code _ y), Finset.mk_mem_sym2_iff.mpr
          ⟨mem_codeWindow.mpr (le_max_left _ _), mem_codeWindow.mpr (le_max_right _ _)⟩⟩)
    hr0 hr0R hoff h2R h3R

/-- **Pointwise corollary of the capstone at the explicit model.**  Continuity of the normalized
pivotal mass at one off-corner radius `r0 > 0`, from a finite second moment at any larger radius:
the first moment at that radius is derived, and no window is needed. -/
theorem sourceModelWitness_continuousAt_normalizedPivotMass_of_offCorner
    (d : ℕ) (hd : 1 ≤ d) (α : ℝ) (hα : 0 < α) {r0 R : ℝ} (hr0 : 0 < r0) (hr0R : r0 < R)
    (hoff : r0 ∉ (sourceModelWitness d hd α hα).cornerRadii)
    (h2R : (sourceModelWitness d hd α hα).cutMoment 2 R ≠ ⊤)
    (y : (sourceModelWitness d hd α hα).V) :
    ContinuousAt ((sourceModelWitness d hd α hα).normalizedPivotMass y) r0 :=
  SourceModelData.continuousAt_normalizedPivotMass (M := sourceModelWitness d hd α hα) (y := y)
    hr0 hr0R (by rwa [SourceModelData.attainedRadii_eq_cornerRadii])
    (ne_top_of_le_ne_top h2R
      (SourceModelData.cutMoment_one_le_cutMoment_two (sourceModelWitness d hd α hα) R))

/-- **The `rhsScalar` form of the off-corner endpoint derivative**, for consumers that work with
`cutMassReal` and `rhsScalar` rather than the paper's explicit power. -/
theorem sourceModelWitness_hasDerivAt_cutMassReal_rhsScalar_of_offCorner
    (d : ℕ) (hd : 1 ≤ d) (α : ℝ) (hα : 0 < α) {r0 R : ℝ} (hr0 : 0 < r0) (hr0R : r0 < R)
    (hoff : r0 ∉ (sourceModelWitness d hd α hα).cornerRadii)
    (h2R : (sourceModelWitness d hd α hα).cutMoment 2 R ≠ ⊤)
    (h3R : (sourceModelWitness d hd α hα).cutMoment 3 R ≠ ⊤) :
    HasDerivAt (sourceModelWitness d hd α hα).cutMassReal
      ((sourceModelWitness d hd α hα).rhsScalar r0) r0 := by
  obtain ⟨a, b, ha, har0, hr0b, hbR, hwin⟩ :=
    SourceModelData.exists_window_notMem_attainedRadii (sourceModelWitness d hd α hα) hr0 hr0R
      (by rwa [SourceModelData.attainedRadii_eq_cornerRadii])
  refine sourceModelWitness_hasDerivAt_cutMassReal_rhsScalar_of_moments_of_window d hd α hα
    (codeWindow (sourceModelWitness d hd α hα).V) (monotone_codeWindow _)
    (fun y => ⟨code _ y, mem_codeWindow.mpr le_rfl⟩)
    (fun n => (codeWindow (sourceModelWitness d hd α hα).V n).sym2)
    (Finset.monotone_sym2.comp (monotone_codeWindow _)) (fun e => by
      induction e using Sym2.ind with
      | _ x y =>
        exact ⟨max (code _ x) (code _ y), Finset.mk_mem_sym2_iff.mpr
          ⟨mem_codeWindow.mpr (le_max_left _ _), mem_codeWindow.mpr (le_max_right _ _)⟩⟩)
    ha har0 hr0b ?_
    (SourceModelData.cutMoment_ne_top_of_le (sourceModelWitness d hd α hα) hbR 2 h2R)
    (SourceModelData.cutMoment_ne_top_of_le (sourceModelWitness d hd α hα) hbR 3 h3R)
  intro r hr
  rw [← SourceModelData.attainedRadii_eq_cornerRadii]
  exact hwin r hr

/-! ## 5. The derivative with only the first cutoff moment

For the literal power-law witness, norm rescaling identifies the source cutoff law with
the native cutoff law. The native third-moment bound therefore supplies both higher
moments from the first one. This discharges moment inputs only; it does not construct a
finite first moment at large radii or prove the paper's asymptotic ODE.
-/

/-- Off-corner derivative of the explicit model's cutoff mass from one finite first moment. -/
theorem sourceModelWitness_hasDerivAt_cutMassReal_powerLaw_of_firstMoment
    (d : ℕ) (hd : 1 ≤ d) (α : ℝ) (hα : 0 < α) {r0 R : ℝ} (hr0 : 0 < r0)
    (hr0R : r0 < R) (hoff : r0 ∉ (sourceModelWitness d hd α hα).cornerRadii)
    (h1R : (sourceModelWitness d hd α hα).cutMoment 1 R ≠ ⊤) :
    HasDerivAt (sourceModelWitness d hd α hα).cutMassReal
      (((sourceModelWitness d hd α hα).betaCrit : ℝ) * r0 ^ (-(d : ℝ) - α - 1) *
        (sourceModelWitness d hd α hα).exclScalar r0) r0 := by
  have hR : 0 < R := hr0.trans hr0R
  exact sourceModelWitness_hasDerivAt_cutMassReal_powerLaw_of_offCorner d hd α hα
    hr0 hr0R hoff (sourceModelWitness_cutMoment_two_ne_top d hd α hα hR h1R)
    (sourceModelWitness_cutMoment_three_ne_top d hd α hα hR h1R)

end PercLib.CriticalLRP.Orchestration.Witness

/-! ## 6. Axiom audit -/

#print axioms PercLib.CriticalLRP.Orchestration.Witness.sourceModelWitness_hasDerivAt_cutMassReal_powerLaw_of_firstMoment

#print axioms PercLib.CriticalLRP.Orchestration.Witness.sourceModelWitness_continuousAt_normalizedPivotMass_of_window
#print axioms PercLib.CriticalLRP.Orchestration.Witness.sourceModelWitness_hcontinf_of_moment_two
#print axioms PercLib.CriticalLRP.Orchestration.Witness.sourceModelWitness_hasDerivAt_cutMassReal_rhsScalar_of_moments_of_window
#print axioms PercLib.CriticalLRP.Orchestration.Witness.sourceModelWitness_hasDerivAt_cutMassReal_powerLaw_of_moments_of_window
#print axioms PercLib.CriticalLRP.Orchestration.Witness.sourceModelWitness_two_le_of_mem_attainedRadii
#print axioms PercLib.CriticalLRP.Orchestration.Witness.sourceModelWitness_notMem_cornerRadii_of_lt_two
#print axioms PercLib.CriticalLRP.Orchestration.Witness.sourceModelWitness_exists_small_radius_hasDerivAt_powerLaw
#print axioms PercLib.CriticalLRP.Orchestration.SourceModelData.exists_window_notMem_attainedRadii
#print axioms PercLib.CriticalLRP.Orchestration.Witness.sourceModelWitness_hasDerivAt_cutMassReal_powerLaw_of_moments_of_offCorner
#print axioms PercLib.CriticalLRP.Orchestration.Witness.sourceModelWitness_hasDerivAt_cutMassReal_powerLaw_of_offCorner
#print axioms PercLib.CriticalLRP.Orchestration.Witness.sourceModelWitness_continuousAt_normalizedPivotMass_of_offCorner
#print axioms PercLib.CriticalLRP.Orchestration.Witness.sourceModelWitness_hasDerivAt_cutMassReal_rhsScalar_of_offCorner
