/-
Finite-volume generalized-norm Russo handoff (swarm `smwtrtcqs`, member `m6`, direction D2).

The incremental Russo formula for the finite-volume `p`-th cluster moment over **one interval of
radii**, with

* the genuine normalized-norm cut-off profile `longRangeEdgeProbability β (cutoffProfile K r
  (S.dist x y))` as the only source of edge probabilities (general norm `ρ`, not `ℓ∞`);
* the explicit boundary convention: an edge of norm-length `‖e‖` contributes to the increment
  over `[r₁, r₂]` only when `‖e‖ < r₂` (its open probability is *identically zero* for
  `r ≤ ‖e‖`), so the lower endpoint never cuts and the upper endpoint does;
* the linearized flux majorant `β (J_{r₂} − J_{r₁})(‖e‖)`, i.e. the `β|J'|` weight of
  Lemma I.4.1 integrated over the interval;
* no claim at a corner radius and no infinite-volume interchange: all sums are finite.

Reference: Hutchcroft, *Critical long-range percolation I*, arXiv:2508.18807v1,
Definition I.1.5 and Lemma I.4.1.
-/
module

public import PercLib.CriticalLRP.Analysis.Cutoff.FiniteRusso.Binomial

set_option linter.unusedSectionVars false
set_option linter.unusedSimpArgs false
set_option linter.unnecessarySimpa false
set_option linter.unusedTactic false
set_option linter.unusedVariables false
set_option linter.unusedFintypeInType false
set_option linter.unusedDecidableInType false

@[expose] public section

open Finset MeasureTheory intervalIntegral

namespace PercLib.CriticalLRP.FiniteVolume.RussoHandoff

variable {E : Type*} [Fintype E] [DecidableEq E]
variable {V : Type*} [Fintype V] [DecidableEq V]

/-! ### Elementary facts about the cut-off edge probabilities -/

section EdgeFacts

variable {K : ℝ → ℝ} {β : ℝ} {len : E → ℝ}

theorem cutoffParam_nonneg (hβ : 0 ≤ β) (hK : AntitoneOn K (Set.Ioi 0))
    (hlen : ∀ e, 0 < len e) {r : ℝ} (hr : 0 < r) (e : E) :
    0 ≤ cutoffParam K β len r e := by
  refine longRangeEdgeProbability_nonneg hβ ?_
  exact Orchestration.cutoffProfile_nonneg_on hK (hlen e)

theorem cutoffParam_le_one (hβ : 0 ≤ β) (hK : AntitoneOn K (Set.Ioi 0))
    (hlen : ∀ e, 0 < len e) {r : ℝ} (hr : 0 < r) (e : E) :
    cutoffParam K β len r e ≤ 1 :=
  longRangeEdgeProbability_le_one hβ (Orchestration.cutoffProfile_nonneg_on hK (hlen e))

/-- **Boundary convention.**  An edge whose norm-length is at least the cut-off radius has open
probability exactly `0` under the cut-off law: it has not been switched on yet. -/
theorem cutoffParam_eq_zero_of_le (e : E) {r : ℝ} (h : r ≤ len e) :
    cutoffParam K β len r e = 0 := by
  unfold cutoffParam
  rcases lt_or_eq_of_le h with hlt | heq
  · rw [cutoffProfile_of_lt hlt, longRangeEdgeProbability_zero_right]
  · rw [heq, cutoffProfile_of_le le_rfl, sub_self, longRangeEdgeProbability_zero_right]

/-- The cut-off edge probabilities are nondecreasing in the cut-off radius. -/
theorem cutoffParam_mono_r (hβ : 0 ≤ β) (hK : AntitoneOn K (Set.Ioi 0))
    (hlen : ∀ e, 0 < len e) {r r' : ℝ} (hr : 0 < r) (hr' : 0 < r') (h : r ≤ r') (e : E) :
    cutoffParam K β len r e ≤ cutoffParam K β len r' e :=
  longRangeEdgeProbability_mono_J hβ (cutoffProfile_mono_r hK hr hr' (hlen e) h)

/-- **Linearized weight bound for one edge.**  Over an interval of radii, the rise of an edge's
open probability is at most `β` times the rise of the cut-off profile `J_r(‖e‖)`.  This is the
`β|J'(r)|` weight of Lemma I.4.1 seen from the integrated side. -/
theorem cutoffParam_sub_le (hβ : 0 ≤ β) (hK : AntitoneOn K (Set.Ioi 0))
    (hlen : ∀ e, 0 < len e) {r₁ r₂ : ℝ} (hr₁ : 0 < r₁) (h : r₁ ≤ r₂) (e : E) :
    cutoffParam K β len r₂ e - cutoffParam K β len r₁ e
      ≤ β * (cutoffProfile K r₂ (len e) - cutoffProfile K r₁ (len e)) := by
  have hr₂ : 0 < r₂ := lt_of_lt_of_le hr₁ h
  set J₁ : ℝ := cutoffProfile K r₁ (len e) with hJ₁
  set J₂ : ℝ := cutoffProfile K r₂ (len e) with hJ₂
  have hJ₁0 : 0 ≤ J₁ := Orchestration.cutoffProfile_nonneg_on hK (hlen e)
  have hmono : J₁ ≤ J₂ := cutoffProfile_mono_r hK hr₁ hr₂ (hlen e) h
  have hdiff : cutoffParam K β len r₂ e - cutoffParam K β len r₁ e
      = Real.exp (-(β * J₁)) * (1 - Real.exp (-(β * (J₂ - J₁)))) := by
    unfold cutoffParam longRangeEdgeProbability
    have hexp : -(β * J₂) = -(β * J₁) + -(β * (J₂ - J₁)) := by ring
    rw [hexp, Real.exp_add]
    ring
  have hexp_le : Real.exp (-(β * J₁)) ≤ 1 := by
    rw [Real.exp_le_one_iff]
    have : 0 ≤ β * J₁ := mul_nonneg hβ hJ₁0
    linarith
  have hu : 0 ≤ β * (J₂ - J₁) := mul_nonneg hβ (by linarith)
  have hone : 1 - Real.exp (-(β * (J₂ - J₁))) ≤ β * (J₂ - J₁) := by
    have h' := Real.add_one_le_exp (-(β * (J₂ - J₁)))
    linarith
  calc cutoffParam K β len r₂ e - cutoffParam K β len r₁ e
      = Real.exp (-(β * J₁)) * (1 - Real.exp (-(β * (J₂ - J₁)))) := hdiff
    _ ≤ 1 * (β * (J₂ - J₁)) := by
        have hnonneg : 0 ≤ 1 - Real.exp (-(β * (J₂ - J₁))) := by
          have hle : Real.exp (-(β * (J₂ - J₁))) ≤ 1 := by
            rw [Real.exp_le_one_iff]; linarith
          linarith
        exact mul_le_mul hexp_le hone hnonneg zero_le_one
    _ = β * (J₂ - J₁) := by ring

/-- **Boundary convention, summed form.**  Only the edges whose norm-length is *strictly* below
the upper endpoint `r₂` contribute to the total weight of the interval; edges of length `≥ r₂`
have zero weight at both endpoints. -/
theorem sum_cutoffParam_sub_eq_sum_filter (f : E → ℝ) {r₁ r₂ : ℝ} (h : r₁ ≤ r₂) :
    ∑ e, (cutoffParam K β len r₂ e - cutoffParam K β len r₁ e) * f e
      = ∑ e ∈ univ.filter (fun e => len e < r₂),
          (cutoffParam K β len r₂ e - cutoffParam K β len r₁ e) * f e := by
  refine (sum_subset (filter_subset _ _) ?_).symm
  intro e _ he
  simp only [mem_filter, mem_univ, true_and, not_lt] at he
  have h2 : cutoffParam K β len r₂ e = 0 := cutoffParam_eq_zero_of_le e he
  have h1 : cutoffParam K β len r₁ e = 0 := cutoffParam_eq_zero_of_le e (le_trans h he)
  rw [h1, h2, sub_self, zero_mul]

end EdgeFacts

/-! ### The interval increment for the cut-off cluster moment -/

section Interval

variable {K : ℝ → ℝ} {β : ℝ} {len : E → ℝ} {s t : E → V} {x : V} {p : ℕ}

/-- **Incremental Russo formula over one interval of radii** (finite volume, exact).  The change
of the `p`-th cut-off cluster moment between the radii `r₁ ≤ r₂` is the integral, along the affine
path of edge probabilities, of the pivotal flux of the flipped edges.  The path is the one that
moves every edge probability from its value at `r₁` to its value at `r₂` at once; `r₁` and `r₂`
themselves can be corners, because no derivative in `r` is taken. -/
theorem cutoffMoment_increment (r₁ r₂ : ℝ) :
    cutoffMoment K β len s t x p r₂ - cutoffMoment K β len s t x p r₁
      = ∫ θ in (0 : ℝ)..1,
          ∑ e, (cutoffParam K β len r₂ e - cutoffParam K β len r₁ e)
            * pivotalMass (pathParam (cutoffParam K β len r₁) (cutoffParam K β len r₂) θ) e
                (clusterMoment s t x p) :=
  expectation_sub_eq_integral_path _ _ _

/-- The interval increment with the sum restricted to the edges that are switched on by the
upper endpoint: the boundary convention in the form in which it is used. -/
theorem cutoffMoment_increment_filter (r₁ r₂ : ℝ) (h : r₁ ≤ r₂) :
    cutoffMoment K β len s t x p r₂ - cutoffMoment K β len s t x p r₁
      = ∫ θ in (0 : ℝ)..1,
          ∑ e ∈ univ.filter (fun e => len e < r₂),
            (cutoffParam K β len r₂ e - cutoffParam K β len r₁ e)
              * pivotalMass (pathParam (cutoffParam K β len r₁) (cutoffParam K β len r₂) θ) e
                  (clusterMoment s t x p) := by
  rw [cutoffMoment_increment]
  refine intervalIntegral.integral_congr fun θ _ => ?_
  exact sum_cutoffParam_sub_eq_sum_filter _ h

/-- **Monotonicity in the cut-off radius.**  The finite-volume cluster moment is nondecreasing
along the cut-off family: this is the finite-volume shadow of `∂_r E_{β,r}|K|^p ≥ 0`. -/
theorem cutoffMoment_mono_r (hβ : 0 ≤ β) (hK : AntitoneOn K (Set.Ioi 0))
    (hlen : ∀ e, 0 < len e) {r₁ r₂ : ℝ} (hr₁ : 0 < r₁) (h : r₁ ≤ r₂) :
    cutoffMoment K β len s t x p r₁ ≤ cutoffMoment K β len s t x p r₂ := by
  have hr₂ : 0 < r₂ := lt_of_lt_of_le hr₁ h
  refine expectation_mono_of_monotone (fun e => ?_) (fun e => ?_) (fun e => ?_)
    (clusterMoment_mono s t x p)
  · exact cutoffParam_nonneg hβ hK hlen hr₁ e
  · exact cutoffParam_mono_r hβ hK hlen hr₁ hr₂ h e
  · exact cutoffParam_le_one hβ hK hlen hr₂ e

/-- **Flux majorant over the interval.**  The increment of the cluster moment is bounded by the
integral of the pivotal flux weighted by the *linearized* cut-off weight
`β (J_{r₂} − J_{r₁})(‖e‖)`.  This is the form in which the `β|J'|` factor enters the source's
equation: on an infinitesimal interval the weight is `β|J'(r)|` and the flux is the pivotal mass
at `r`. -/
theorem cutoffMoment_increment_le (hβ : 0 ≤ β) (hK : AntitoneOn K (Set.Ioi 0))
    (hlen : ∀ e, 0 < len e) {r₁ r₂ : ℝ} (hr₁ : 0 < r₁) (h : r₁ ≤ r₂) :
    cutoffMoment K β len s t x p r₂ - cutoffMoment K β len s t x p r₁
      ≤ ∫ θ in (0 : ℝ)..1,
          ∑ e, (β * (cutoffProfile K r₂ (len e) - cutoffProfile K r₁ (len e)))
            * pivotalMass (pathParam (cutoffParam K β len r₁) (cutoffParam K β len r₂) θ) e
                (clusterMoment s t x p) := by
  rw [cutoffMoment_increment]
  refine intervalIntegral.integral_mono_on (a := 0) (b := 1) (by norm_num)
    ((continuous_flux _ _ _ _).intervalIntegrable _ _)
    ((continuous_flux _ _ _ _).intervalIntegrable _ _) ?_
  intro θ hθ
  refine sum_le_sum fun e _ => ?_
  have hpiv : 0 ≤ pivotalMass
      (pathParam (cutoffParam K β len r₁) (cutoffParam K β len r₂) θ) e
      (clusterMoment s t x p) := by
    refine pivotalMass_path_nonneg (fun e' => ?_) (fun e' => ?_) (fun e' => ?_)
      (clusterMoment_mono s t x p) hθ.1 hθ.2 e
    · exact cutoffParam_nonneg hβ hK hlen hr₁ e'
    · exact cutoffParam_mono_r hβ hK hlen hr₁ (lt_of_lt_of_le hr₁ h) h e'
    · exact cutoffParam_le_one hβ hK hlen (lt_of_lt_of_le hr₁ h) e'
  exact mul_le_mul_of_nonneg_right
    (cutoffParam_sub_le hβ hK hlen hr₁ h e) hpiv

end Interval

end PercLib.CriticalLRP.FiniteVolume.RussoHandoff
