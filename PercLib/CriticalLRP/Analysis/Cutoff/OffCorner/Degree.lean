module

public import PercLib.CriticalLRP.Analysis.Cutoff.OffCorner.StrictDecrease

/-!
# The finite standardised incident degree bound

Swarm `smwu19308`, member `m1`.

The support of the cutoff derivative weight at radius `r` is the set of non-loop edges of
`ρ`-length `≤ r` (`inSupport`).  At a vertex `x`, such an edge is `s(x, y)` with `y - x` a
nonzero point of the normalised ball `M.ball r`, so there are at most `#(ball r)` of them,
**uniformly in `x`**.  Dividing the scalar bound `stdEdgeWeight r e ≤ (-K'(r))/J_r(e)`
by the gap floor gives,
for every finite edge set `u`,

  `vertexWeight (stdEdgeWeight r) x u ≤
    #(ball r) · (-K'(r)) / γ(r) = stdDegree r`.

The bound holds at **every** `r > 0`: an edge whose kernel gap vanishes carries standardised
weight `0` (Lean's `0 / 0 = 0`), so it only has to be excluded from the gap floor, not from the
support.  No off-corner hypothesis and no tail hypothesis are used here.
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

attribute [local instance] Classical.propDecidable

/-! ## 1. The individual support edges at a vertex -/

/-- The vertices reached from `x` by a support edge. -/
private def reachSet (r : ℝ) (x : M.V) : Set M.V := {y : M.V | y ≠ x ∧ M.S.dist x y ≤ r}

private theorem finite_reachSet (r : ℝ) (x : M.V) : (reachSet M r x).Finite := by
  refine ((M.finite_ball r).image (fun z : M.V => z + x)).subset ?_
  intro y hy
  obtain ⟨hyx, hyd⟩ := hy
  refine ⟨y - x, ?_, by abel⟩
  have hdist : M.S.dist x y = M.S.ρ (toVec (y - x)) := by
    rw [SourceNormData.dist, toVec_sub_eq_neg, M.S.ρ_neg]
  change M.S.ρ (toVec (y - x)) ≤ r
  rw [← hdist]
  exact hyd

/-- The support edges incident to `x` are the edges `s(x, y)` with `y` in the reach set. -/
private theorem incidentSupport_eq_image (r : ℝ) (x : M.V) :
    {e : Sym2 M.V | x ∈ e ∧ inSupport M r e}
      = (fun y : M.V => s(x, y)) '' reachSet M r x := by
  ext e
  constructor
  · rintro ⟨hxe, a, b, hab, heq, hd⟩
    subst heq
    rw [Sym2.mem_iff] at hxe
    rcases hxe with hxa | hxb
    · subst hxa
      exact ⟨b, ⟨Ne.symm hab, hd⟩, rfl⟩
    · subst hxb
      refine ⟨a, ⟨hab, ?_⟩, Sym2.eq_swap.symm⟩
      rw [SourceNormData.dist_comm]
      exact hd
  · rintro ⟨y, ⟨hyx, hyd⟩, rfl⟩
    exact ⟨Sym2.mem_mk_left x y, x, y, hyx.symm, rfl, hyd⟩

/-- The support edges incident to `x` form a finite set. -/
theorem finite_incidentSupport (r : ℝ) (x : M.V) :
    {e : Sym2 M.V | x ∈ e ∧ inSupport M r e}.Finite := by
  rw [incidentSupport_eq_image M r x]
  exact (finite_reachSet M r x).image _

/-- **The uniform incident count**: at any vertex there are at most `#(ball r)` support edges. -/
theorem ncard_incidentSupport_le (r : ℝ) (x : M.V) :
    {e : Sym2 M.V | x ∈ e ∧ inSupport M r e}.ncard ≤ (M.ball r).ncard := by
  rw [incidentSupport_eq_image M r x]
  calc ((fun y : M.V => s(x, y)) '' reachSet M r x).ncard
      ≤ (reachSet M r x).ncard := Set.ncard_image_le (finite_reachSet M r x)
    _ ≤ ((fun z : M.V => z + x) '' (M.ball r)).ncard := by
        refine Set.ncard_le_ncard ?_ ((M.finite_ball r).image _)
        intro y hy
        obtain ⟨hyx, hyd⟩ := hy
        refine ⟨y - x, ?_, by abel⟩
        have hdist : M.S.dist x y = M.S.ρ (toVec (y - x)) := by
          rw [SourceNormData.dist, toVec_sub_eq_neg, M.S.ρ_neg]
        change M.S.ρ (toVec (y - x)) ≤ r
        rw [← hdist]
        exact hyd
    _ ≤ (M.ball r).ncard := Set.ncard_image_le (M.finite_ball r)

/-- The same count on a finite edge set. -/
theorem card_filter_incidentSupport_le (r : ℝ) (x : M.V) (u : Finset (Sym2 M.V)) :
    ((u.filter (fun e => x ∈ e ∧ inSupport M r e)).card : ℝ) ≤ ((M.ball r).ncard : ℝ) := by
  have h1 : (u.filter (fun e => x ∈ e ∧ inSupport M r e)).card
      ≤ {e : Sym2 M.V | x ∈ e ∧ inSupport M r e}.ncard := by
    rw [← Set.ncard_coe_finset]
    exact Set.ncard_le_ncard (by
      intro e he
      rw [Finset.mem_coe, Finset.mem_filter] at he
      exact he.2) (finite_incidentSupport M r x)
  calc ((u.filter (fun e => x ∈ e ∧ inSupport M r e)).card : ℝ)
      ≤ ({e : Sym2 M.V | x ∈ e ∧ inSupport M r e}.ncard : ℝ) := by exact_mod_cast h1
    _ ≤ ((M.ball r).ncard : ℝ) := by exact_mod_cast ncard_incidentSupport_le M r x

/-! ## 2. The pointwise standardised weight bound -/

/-- **Per-edge standardised weight bound at the gap floor.**  For a support edge at radius `r`,
either the kernel gap vanishes — and then the standardised weight is `0` — or the gap is at
least the gap floor. -/
theorem stdEdgeWeight_le_neg_deriv_div_gapFloor {r : ℝ} (hr : 0 < r) {e : Sym2 M.V}
    (hsup : inSupport M r e) :
    M.stdEdgeWeight r e ≤ (-(deriv M.K r)) / M.gapFloor r := by
  classical
  have hK' : 0 ≤ -(deriv M.K r) := M.neg_deriv_K_nonneg hr
  have hγpos : 0 < M.gapFloor r := M.gapFloor_pos r
  obtain ⟨a, b, hab, heq, hd⟩ := hsup
  subst heq
  have hJeq : M.cutKernel r s(a, b) = M.K (M.S.dist a b) - M.K r := by
    rw [M.cutKernel_mk, ite_eq_right hab, FiniteVolume.cutoffProfile_of_le hd]
  by_cases hJ : M.cutKernel r s(a, b) = 0
  · have hq0 : M.openProb r s(a, b) = 0 := by
      rw [M.openProb_eq, hJ, mul_zero, neg_zero, Real.exp_zero, sub_self]
    rw [SourceModelData.stdEdgeWeight, hq0, div_zero]
    exact div_nonneg hK' hγpos.le
  · have hJpos : 0 < M.cutKernel r s(a, b) :=
      lt_of_le_of_ne (M.cutKernel_nonneg r _) (Ne.symm hJ)
    have hne : M.S.dist a b ≠ r := by
      intro h
      rw [h, sub_self] at hJeq
      rw [hJeq] at hJpos
      exact lt_irrefl 0 hJpos
    have hmem : M.S.dist a b ∈ M.posGapRadii r := by
      refine ⟨⟨M.S.mem_attainedRadii_of_dist hab, lt_of_le_of_ne hd hne⟩, ?_⟩
      rw [← hJeq]
      exact hJpos
    have hγJ : M.gapFloor r ≤ M.cutKernel r s(a, b) := by
      rw [hJeq]
      exact M.gapFloor_le_of_pos hmem
    exact (M.stdEdgeWeight_le_div_cutKernel s(a, b) hJpos hK').trans
      (div_le_div_of_nonneg_left hK' hγpos hγJ)

/-! ## 3. The vertex weight bound -/

/-- **The finite standardised incident degree bound.**  For every `r > 0`, every vertex `x` and
every finite edge set `u`, the total standardised weight of the edges of `u` incident to `x` is at
most the explicit finite constant `stdDegree r = #(ball r) · (-K'(r)) / γ(r)`. -/
theorem vertexWeight_stdEdgeWeight_le_stdDegree {r : ℝ} (hr : 0 < r) (x : M.V)
    (u : Finset (Sym2 M.V)) :
    PercLib.CriticalLRP.vertexWeight (M.stdEdgeWeight r) x u ≤ M.stdDegree r := by
  classical
  have hK' : 0 ≤ -(deriv M.K r) := M.neg_deriv_K_nonneg hr
  have hγpos : 0 < M.gapFloor r := M.gapFloor_pos r
  have hterm : ∀ e ∈ u, M.stdEdgeWeight r e * (if x ∈ e then (1 : ℝ) else 0)
      ≤ ((-(deriv M.K r)) / M.gapFloor r) * (if x ∈ e ∧ inSupport M r e then (1 : ℝ) else 0) := by
    intro e _
    by_cases hxe : x ∈ e
    · by_cases hsup : inSupport M r e
      · rw [ite_eq_left hxe, ite_eq_left ⟨hxe, hsup⟩, mul_one, mul_one]
        exact M.stdEdgeWeight_le_neg_deriv_div_gapFloor hr hsup
      · rw [SourceModelData.stdEdgeWeight, M.cutEdgeDeriv_eq_zero_of_not_support hsup, zero_div,
          ite_eq_left hxe]
        simp [hsup]
    · rw [ite_eq_right hxe]
      simp [hxe]
  calc PercLib.CriticalLRP.vertexWeight (M.stdEdgeWeight r) x u
      = ∑ e ∈ u, M.stdEdgeWeight r e * (if x ∈ e then (1 : ℝ) else 0) :=
        M.vertexWeight_congr_sum x u
    _ ≤ ∑ e ∈ u, ((-(deriv M.K r)) / M.gapFloor r)
          * (if x ∈ e ∧ inSupport M r e then (1 : ℝ) else 0) := Finset.sum_le_sum hterm
    _ = ((-(deriv M.K r)) / M.gapFloor r)
          * ∑ e ∈ u, (if x ∈ e ∧ inSupport M r e then (1 : ℝ) else 0) := by
        rw [Finset.mul_sum]
    _ = ((-(deriv M.K r)) / M.gapFloor r)
          * ((u.filter (fun e => x ∈ e ∧ inSupport M r e)).card : ℝ) := by
        rw [Finset.card_filter]
        push_cast
        rfl
    _ ≤ ((-(deriv M.K r)) / M.gapFloor r) * ((M.ball r).ncard : ℝ) :=
        mul_le_mul_of_nonneg_left (card_filter_incidentSupport_le M r x u)
          (div_nonneg hK' hγpos.le)
    _ = M.stdDegree r := by
        unfold stdDegree
        ring

/-! ## 4. The incident-series form -/

/-- A standardised incident term vanishes off the incident support. -/
theorem incidentTerm_eq_zero (r : ℝ) (x : M.V) {e : Sym2 M.V}
    (he : ¬(x ∈ e ∧ inSupport M r e)) :
    M.stdEdgeWeight r e * (if x ∈ e then (1 : ℝ) else 0) = 0 := by
  classical
  by_cases hxe : x ∈ e
  · have hns : ¬ inSupport M r e := fun h => he ⟨hxe, h⟩
    rw [SourceModelData.stdEdgeWeight, M.cutEdgeDeriv_eq_zero_of_not_support hns, zero_div,
      zero_mul]
  · rw [ite_eq_right hxe, mul_zero]

/-- **The incident series at a vertex is summable.**  It is supported on the finite set of support
edges incident to `x` (`finite_incidentSupport`). -/
theorem summable_incident_stdEdgeWeight (r : ℝ) (x : M.V) :
    Summable fun e : Sym2 M.V => M.stdEdgeWeight r e * (if x ∈ e then (1 : ℝ) else 0) := by
  classical
  refine summable_of_ne_finset_zero (s := (finite_incidentSupport M r x).toFinset) ?_
  intro e he
  exact M.incidentTerm_eq_zero r x (fun h => he ((finite_incidentSupport M r x).mem_toFinset.mpr h))

/-- **The incident series is bounded by the same constant.**  This is the form consumed by
`tsum_weight_mixed_touch_le_of_incident`: the full incident sum `incidentWeight` of the standardised
weight at any vertex is at most `stdDegree r`. -/
theorem incidentWeight_stdEdgeWeight_le_stdDegree {r : ℝ} (hr : 0 < r) (x : M.V) :
    PercLib.CriticalLRP.incidentWeight (M.stdEdgeWeight r) x ≤ M.stdDegree r := by
  classical
  have hzero : ∀ e ∉ (finite_incidentSupport M r x).toFinset,
      M.stdEdgeWeight r e * (if x ∈ e then (1 : ℝ) else 0) = 0 := fun e he =>
    M.incidentTerm_eq_zero r x (fun h => he ((finite_incidentSupport M r x).mem_toFinset.mpr h))
  calc PercLib.CriticalLRP.incidentWeight (M.stdEdgeWeight r) x
      = ∑' e : Sym2 M.V, M.stdEdgeWeight r e * (if x ∈ e then (1 : ℝ) else 0) := by
        unfold PercLib.CriticalLRP.incidentWeight
        apply tsum_congr
        intro e
        by_cases hx : x ∈ e <;> simp [hx]
    _ = ∑ e ∈ (finite_incidentSupport M r x).toFinset,
          M.stdEdgeWeight r e * (if x ∈ e then (1 : ℝ) else 0) := tsum_eq_sum hzero
    _ = PercLib.CriticalLRP.vertexWeight (M.stdEdgeWeight r) x
          (finite_incidentSupport M r x).toFinset := (M.vertexWeight_congr_sum x _).symm
    _ ≤ M.stdDegree r := M.vertexWeight_stdEdgeWeight_le_stdDegree hr x _

/-- **The degree bound, uniformly over finite edge sets.** -/
theorem exists_stdDegree_bound (r : ℝ) (hr : 0 < r) :
    0 ≤ M.stdDegree r ∧ ∀ x : M.V, ∀ u : Finset (Sym2 M.V),
      PercLib.CriticalLRP.vertexWeight (M.stdEdgeWeight r) x u ≤ M.stdDegree r :=
  ⟨M.stdDegree_nonneg hr, fun x u => M.vertexWeight_stdEdgeWeight_le_stdDegree hr x u⟩

end SourceModelData

end PercLib.CriticalLRP.Orchestration
