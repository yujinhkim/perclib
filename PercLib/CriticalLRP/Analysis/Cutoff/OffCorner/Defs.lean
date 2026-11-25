module

public import PercLib.CriticalLRP.MomentMonotonicity.StrictCutoffEpsilon
public import PercLib.CriticalLRP.Analysis.Cutoff.Incident.IncidentBall
public import PercLib.CriticalLRP.Analysis.Cutoff.FluxSupport
public import PercLib.CriticalLRP.Analysis.Cutoff.CornerRadii.FlatSharpness
public import PercLib.CriticalLRP.Analysis.BallRatioLogError
public import PercLib.CriticalLRP.Analysis.Cutoff.MixedFluxDensityMonotone

/-!
# Off-corner standardised incident majorant: definitions

Swarm `smwu19308`, member `m1`.

The standardised incident majorant of a `SourceModelData` at a radius `r` is

  `D_std(r) = #(ball r) * (-K'(r)) / γ(r)`,

where

* `ball r` is the normalised lattice ball `{z | ρ z ≤ r}` (finite, `SourceModelData.finite_ball`);
  it counts the edges of the support at any vertex, uniformly in the vertex, because a support
  edge at `x` is `s(x, y)` with `y - x ∈ ball r`;
* `γ(r) = gapFloor r` is the minimum of `K s - K r` over those attained support radii `s < r`
  whose gap is **strictly positive** (default `1` if there is none); hence `γ(r) > 0` always;
* `(-K'(r)) ≥ 0` is the cutoff profile decrease (`deriv_K_nonpos`).

Two points of scope, forced by the structure of `SourceModelData`:

* The gap floor is taken over *positive* gaps only.  A support edge whose kernel gap
  `J_r(e) = K s - K r` vanishes has `openProb r e = 0`, hence standardised weight
  `0 / 0 = 0` in `ℝ`, so it needs no bound; this makes the degree bound valid at **every**
  `r > 0`, with no off-corner and no tail hypothesis (`vertexWeight_stdEdgeWeight_le_stdDegree`).
* The strict decrease `K r < K s` for `0 < s < r` is **not** derivable from the structure at
  small radii: `exists_error` only pins `|K'|` up to a log-error function `δ` with `δ → 0` at
  `+∞`, so `δ ≡ -1` on a bounded interval is admissible and `K` may be flat there.  The tail
  form is derivable (`K_lt_of_lt_of_tail`: `|K' t| ≥ (1/2) t^(-d-α-1)` on `(R, ∞)` and `R < r`
  imply `K r < K s` for every `0 < s < r`), but it turned out **not** to be needed: a vanishing
  gap below an off-corner radius forces `K` to be flat on `[s, r]`, hence `K'(r) = 0`
  (`deriv_eq_zero_of_flat_left`), hence the derivative weight itself vanishes.  That is what
  makes the flux majorant work at *every* positive off-corner radius.
-/

set_option linter.style.longLine false
set_option linter.hashCommand false

@[expose] public section

noncomputable section

open MeasureTheory Filter Topology Set
open scoped ENNReal NNReal Topology

namespace PercLib.CriticalLRP.Orchestration

namespace SourceModelData

variable (M : SourceModelData)

/-! ## 1. The attained support radii -/

/-- The radii attained by the source norm at a nonzero lattice displacement and strictly below
the cutoff radius.  These are exactly the lengths in `(0, r)` at which the cutoff kernel of a
non-loop edge of the support can be evaluated. -/
def supportRadii (r : ℝ) : Set ℝ := {s : ℝ | s ∈ M.attainedRadii ∧ s < r}

theorem mem_supportRadii {r s : ℝ} :
    s ∈ M.supportRadii r ↔ s ∈ M.attainedRadii ∧ s < r := Iff.rfl

/-- The attained support radii below `r` form a finite set. -/
theorem finite_supportRadii (r : ℝ) : (M.supportRadii r).Finite := by
  have himg : M.supportRadii r ⊆ (fun z : M.V => M.S.dist z 0) '' (M.ball r) := by
    rintro s ⟨⟨z, hz, hzs⟩, hsr⟩
    refine ⟨z, ?_, hzs⟩
    have h : M.S.ρ (toVec z) = M.S.dist z 0 := (SourceNormData.dist_zero_right M.S z).symm
    change M.S.ρ (toVec z) ≤ r
    rw [h, hzs]
    exact le_of_lt hsr
  exact ((M.finite_ball r).image (fun z : M.V => M.S.dist z 0)).subset himg

/-! ## 2. The positive gaps and the gap floor -/

/-- Those attained support radii below `r` whose cutoff kernel gap is strictly positive.  Only
these need to be bounded below: a vanishing gap gives standardised weight `0`. -/
def posGapRadii (r : ℝ) : Set ℝ :=
  {s : ℝ | s ∈ M.supportRadii r ∧ 0 < M.K s - M.K r}

theorem mem_posGapRadii {r s : ℝ} :
    s ∈ M.posGapRadii r ↔ s ∈ M.supportRadii r ∧ 0 < M.K s - M.K r := Iff.rfl

theorem finite_posGapRadii (r : ℝ) : (M.posGapRadii r).Finite :=
  (M.finite_supportRadii r).subset fun _ hs => hs.1

noncomputable def posGapRadiiFinset (r : ℝ) : Finset ℝ :=
  (M.finite_posGapRadii r).toFinset

theorem mem_posGapRadiiFinset {r s : ℝ} :
    s ∈ M.posGapRadiiFinset r ↔ s ∈ M.posGapRadii r :=
  Set.Finite.mem_toFinset _

/-- **The gap floor.**  The minimum of the strictly positive kernel gaps `K s - K r` over the
finite set of attained support radii `s < r` (default `1` when there is none).  It is strictly
positive at every radius. -/
noncomputable def gapFloor (r : ℝ) : ℝ :=
  if hne : (M.posGapRadiiFinset r).Nonempty then
    (M.posGapRadiiFinset r).inf' hne (fun s => M.K s - M.K r)
  else 1

/-! ## 3. The incident cardinality and the degree constant -/

/-- **The incident edge count.**  The number of points of the normalised ball `ball r`; every
support edge at a vertex `x` is `s(x, y)` with `y - x` a nonzero point of `ball r`, so this
bounds the number of incident support edges at every vertex, uniformly. -/
noncomputable def incidentCard (r : ℝ) : ℕ := (M.ball r).ncard

/-- **The standardised incident majorant.**  The incident edge count times `(-K'(r))` divided by
the gap floor. -/
noncomputable def stdDegree (r : ℝ) : ℝ :=
  ((M.ball r).ncard : ℝ) * (-(deriv M.K r)) / M.gapFloor r

end SourceModelData

end PercLib.CriticalLRP.Orchestration
