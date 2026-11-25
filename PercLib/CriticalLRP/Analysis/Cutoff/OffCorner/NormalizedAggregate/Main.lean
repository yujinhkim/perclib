/-
Critical LRP I: continuity of the normalized pivotal mass off corner, from fixed-edge pivotal
flux continuity and a finite first cutoff moment at a strictly larger radius.

Swarm `smwv2c2lw`, member `m3`, direction d3.  Self-contained packet: no production writes, no
axioms beyond the three standard ones.
-/
module

public import PercLib.CriticalLRP.Analysis.Cutoff.OffCorner.NormalizedAggregate.Defs
public import PercLib.CriticalLRP.Analysis.Cutoff.OffCorner.KernelFactor.Main
public import PercLib.CriticalLRP.Analysis.Cutoff.CornerRadii
public import PercLib.CriticalLRP.Analysis.Cutoff.Deriv
public import PercLib.CriticalLRP.Analysis.Cutoff.FluxSupport.Defs
public import PercLib.CriticalLRP.Analysis.Cutoff.Incident.Defs

/-!
# Radius continuity of the normalized pivotal mass off corner

The normalized pivotal mass

`normalizedPivotMass y r = ∑' e, cutPivotFactor r e * pivotalFlux (cutProb r) 1{y ∈ K_0} e`

is an infinite edge series.  Off an attained radius `r0` the cutoff factor
`cutPivotFactor r e` is *locally constant* in `r` (the corner-free neighbourhood of
`exists_nhds_notMem_attainedRadii`), so the only radius dependence of the series near `r0` is the
one of the single-edge pivotal fluxes.  This file proves:

* `pivotalFlux_singleton_le_edgeTouchMass` — the pivotal flux of one edge for `1{y ∈ K_0}` is at
  most the probability that the edge touches the cluster of the origin, which is at most the sum
  over its two endpoints of `cutTwoPoint r 0 x` (no two-arm or BK input is used);
* `summable_pivotMajorant` — the radius-uniform majorant `pivotMajorant r0 R` is summable as soon
  as the first cutoff moment `cutMoment 1 R` is finite at one radius `R ≥ r0`.  The proof is the
  fixed-radius incident count `#(ball r0)`: every edge is counted once per endpoint, and at each
  vertex only the edges of length at most `r0` carry a nonzero cutoff factor;
* `cutPivotFactor_eq_of_cornerFree` — local constancy of the cutoff factor off the corner set;
* `continuousAt_normalizedPivotMass_of_continuousAt_pivotalFlux` — **the reduction**: off-corner
  `r0 > 0`, a finite first cutoff moment at one strictly larger radius and continuity at `r0` of
  the single-edge pivotal flux, for the edges activated at `r0` only, give continuity of the
  normalized pivotal mass at `r0`.  The infinite edge sum is handled by Tannery's theorem
  (`tendsto_tsum_of_dominated_convergence`) with the moment majorant; no continuity of the total
  mass, and no uniformity in the edge beyond the moment bound, is assumed;
* `continuousAt_normalizedPivotMass_of_continuousAt_pivotalFlux_of_moment_two` — the same with
  a finite *second* cutoff moment at `R`, which implies the first
  (`cutMoment_one_le_cutMoment_two`);
* `continuousAt_sMomentInfFlux_of_continuousAt_deriv_of_continuousAt_pivotalFlux`,
  `hcontinf_of_continuousAt_deriv_of_continuousAt_pivotalFlux` and
  `hasDerivAt_cutMassReal_rhsScalar_of_envelope_of_pivotalFlux` — the corresponding replacements of
  the black-box `normalizedPivotMass` continuity in the landed kernel-factor sufficiency theorems
  (per-vertex flux, window, and the envelope endpoint derivative);
* `exists_finite_activated_distances` — the support of `cutPivotFactor r0` meets only finitely
  many distance scales, which is why the fixed-edge hypothesis is stated on `inSupport M r0`
  rather than on a finite edge set.

The remaining input is exactly the *fixed-edge* pivotal flux continuity that directions (A)/(B) of
the swarm target; nothing in this file proves it, and nothing here assumes continuity of the total
normalized mass, of the singleton flux, or of any two-point function.
-/

@[expose] public section

noncomputable section

open MeasureTheory Filter Topology Set
open scoped ENNReal NNReal Topology

namespace PercLib.CriticalLRP.Orchestration

namespace SourceModelData

variable (M : SourceModelData)

/-! ## 1. The single-edge pivotal flux is bounded by the edge touch mass -/

/-- The pivotal difference of the singleton cluster indicator is nonnegative and is at most the
indicator of the touching event. -/
theorem flipDiff_singleton_le_touchIndicator {y : M.V} (e : Sym2 M.V) (ω : Config M.V) :
    flipDiff (sMomentTrunc (fun _ => (1 : ℝ)) (0 : M.V) ({y} : Finset M.V)) e ω
      ≤ ({ω : Config M.V | e ∈ touchSet ω (0 : M.V)}).indicator (1 : Config M.V → ℝ) ω := by
  classical
  have hle := M.flipDiff_sMomentTrunc_singleton_le y e ω
  rw [Set.indicator_apply]
  split_ifs with ht
  · have hte : e ∈ touchSet ω (0 : M.V) := ht
    rw [Set.indicator_of_mem hte, mul_one] at hle
    refine hle.trans ?_
    rw [Set.indicator_apply]
    split_ifs <;> norm_num
  · have hte : e ∉ touchSet ω (0 : M.V) := ht
    rw [Set.indicator_of_notMem hte, mul_zero] at hle
    exact hle

/-- **The single-edge pivotal flux is at most the touching probability.**  Any configuration at
which opening `e` changes whether `y` lies in the cluster of the origin has `e` touching that
cluster. -/
theorem pivotalFlux_singleton_le_touchProb {r : ℝ} (y : M.V) (e : Sym2 M.V) :
    pivotalFlux (edgeMeasure (M.cutProb r))
        (sMomentTrunc (fun _ => (1 : ℝ)) (0 : M.V) ({y} : Finset M.V)) e
      ≤ (edgeMeasure (M.cutProb r)).real {ω : Config M.V | e ∈ touchSet ω (0 : M.V)} := by
  classical
  have hprob : IsProbabilityMeasure (edgeMeasure (M.cutProb r)) := inferInstance
  have hInt : Integrable
      ({ω : Config M.V | e ∈ touchSet ω (0 : M.V)}.indicator (fun _ => (1 : ℝ)))
      (edgeMeasure (M.cutProb r)) :=
    (integrable_const (1 : ℝ)).indicator (measurableSet_touchSet_mem (o := (0 : M.V)) e)
  rw [pivotalFlux, ← integral_indicator_one (measurableSet_touchSet_mem (o := (0 : M.V)) e)]
  refine integral_mono_of_nonneg
    (Eventually.of_forall fun ω => M.flipDiff_sMomentTrunc_singleton_nonneg y e ω) hInt
    (Eventually.of_forall fun ω => ?_)
  simpa using M.flipDiff_singleton_le_touchIndicator (y := y) e ω


/-- **The touching event of an edge is contained in the union of the two endpoint clusters.** -/
theorem touchSet_subset_endpoint_clusters {x y : M.V} (o : M.V) :
    {ω : Config M.V | s(x, y) ∈ touchSet ω o}
      ⊆ {ω : Config M.V | x ∈ cluster ω o} ∪ {ω : Config M.V | y ∈ cluster ω o} := by
  intro ω h
  rcases mem_touchSet.mp h with ⟨v, hv, hvc⟩
  rw [Sym2.mem_iff] at hv
  rcases hv with rfl | rfl
  · exact Or.inl hvc
  · exact Or.inr hvc

/-- **The endpoint connection probability is `cutTwoPoint`.** -/
theorem real_cluster_mem_eq_cutTwoPoint (r : ℝ) (o x : M.V) :
    (edgeMeasure (M.cutProb r)).real {ω : Config M.V | x ∈ cluster ω o}
      = M.cutTwoPoint r o x := by
  rw [cutTwoPoint, M.cutLaw_eq_edgeMeasure]
  exact congrArg (fun s => (edgeMeasure (M.cutProb r)).real s)
    (Set.ext fun ω => mem_cluster_iff)

/-- **The single-edge pivotal flux is bounded by the edge touch mass.**  This is the per-edge
majorant input of Tannery's theorem for the normalized pivotal mass; it uses only that a pivotal
edge touches the cluster of the origin, and then the union bound over its two endpoints. -/
theorem pivotalFlux_singleton_le_edgeTouchMass {r : ℝ} (y : M.V) (e : Sym2 M.V) :
    pivotalFlux (edgeMeasure (M.cutProb r))
        (sMomentTrunc (fun _ => (1 : ℝ)) (0 : M.V) ({y} : Finset M.V)) e
      ≤ M.edgeTouchMass r e := by
  classical
  induction e using Sym2.ind with
  | h a b =>
    rw [edgeTouchMass_mk]
    refine (M.pivotalFlux_singleton_le_touchProb y s(a, b)).trans ?_
    have hsub := touchSet_subset_endpoint_clusters (M := M) (x := a) (y := b) (0 : M.V)
    have h1 : (edgeMeasure (M.cutProb r)).real {ω : Config M.V | s(a, b) ∈ touchSet ω (0 : M.V)}
        ≤ (edgeMeasure (M.cutProb r)).real
            ({ω : Config M.V | a ∈ cluster ω (0 : M.V)}
              ∪ {ω : Config M.V | b ∈ cluster ω (0 : M.V)}) :=
      measureReal_mono hsub
    have h2 : (edgeMeasure (M.cutProb r)).real
        ({ω : Config M.V | a ∈ cluster ω (0 : M.V)}
          ∪ {ω : Config M.V | b ∈ cluster ω (0 : M.V)})
        ≤ (edgeMeasure (M.cutProb r)).real {ω : Config M.V | a ∈ cluster ω (0 : M.V)}
          + (edgeMeasure (M.cutProb r)).real {ω : Config M.V | b ∈ cluster ω (0 : M.V)} :=
      measureReal_union_le _ _
    have h3 : (edgeMeasure (M.cutProb r)).real {ω : Config M.V | a ∈ cluster ω (0 : M.V)}
        = M.cutTwoPoint r 0 a := M.real_cluster_mem_eq_cutTwoPoint r 0 a
    have h4 : (edgeMeasure (M.cutProb r)).real {ω : Config M.V | b ∈ cluster ω (0 : M.V)}
        = M.cutTwoPoint r 0 b := M.real_cluster_mem_eq_cutTwoPoint r 0 b
    linarith


/-! ## 2. Local constancy of the cutoff factor off the corner set -/

/-- **The cutoff factor is locally constant off the corner set.**  If no attained radius lies in
the open window `(r0 - ε, r0 + ε)`, then the cutoff factor of every edge is constant on that
window. -/
theorem cutPivotFactor_eq_of_cornerFree {r0 ε : ℝ}
    (hε : ∀ r' : ℝ, |r' - r0| < ε → r' ∉ M.attainedRadii)
    {r : ℝ} (hr : |r - r0| < ε) (e : Sym2 M.V) :
    M.cutPivotFactor r e = M.cutPivotFactor r0 e := by
  induction e using Sym2.ind with
  | h x y =>
    rw [cutPivotFactor, radialSym_mk, cutPivotFactor, radialSym_mk]
    by_cases hxy : x = y
    · rw [ite_eq_left hxy, ite_eq_left hxy]
    · rw [ite_eq_right hxy, ite_eq_right hxy]
      have hmem : M.S.dist x y ∈ M.attainedRadii := M.S.mem_attainedRadii_of_dist hxy
      have hrwin : r0 - ε < r ∧ r < r0 + ε := by
        rw [abs_lt] at hr
        exact ⟨by linarith [hr.1], by linarith [hr.2]⟩
      have hout : ¬ (r0 - ε < M.S.dist x y ∧ M.S.dist x y < r0 + ε) := by
        rintro ⟨h1, h2⟩
        refine hε (M.S.dist x y) ?_ hmem
        rw [abs_lt]
        exact ⟨by linarith, by linarith⟩
      by_cases hle : M.S.dist x y ≤ r0
      · have hle' : M.S.dist x y ≤ r := by
          by_contra hcon
          rw [not_le] at hcon
          exact hout ⟨by linarith [hrwin.1], by linarith⟩
        rw [ite_eq_left hle, ite_eq_left hle']
      · have hle' : ¬ M.S.dist x y ≤ r := by
          intro hcon
          exact hout ⟨by linarith, by linarith [hrwin.2]⟩
        rw [ite_eq_right hle, ite_eq_right hle']

/-- **The cutoff factor vanishes off the support.** -/
theorem cutPivotFactor_eq_zero_of_not_inSupport (r : ℝ) {e : Sym2 M.V}
    (he : ¬ inSupport M r e) : M.cutPivotFactor r e = 0 := by
  induction e using Sym2.ind with
  | h x y =>
    rw [cutPivotFactor, radialSym_mk]
    by_cases hxy : x = y
    · rw [ite_eq_left hxy]
    · rw [ite_eq_right hxy]
      have hd : ¬ M.S.dist x y ≤ r := fun h => he ⟨x, y, hxy, rfl, h⟩
      rw [ite_eq_right hd]

/-! ## 3. The edge majorant is summable at a finite first cutoff moment -/

theorem edgeTouchMass_le_two_mul_toFinset_sum {R : ℝ} (e : Sym2 M.V) :
    M.edgeTouchMass R e ≤ 2 * ∑ x ∈ e.toFinset, M.cutTwoPoint R 0 x := by
  classical
  induction e using Sym2.ind with
  | h a b =>
    rw [edgeTouchMass_mk, Sym2.toFinset_mk_eq]
    by_cases hab : a = b
    · subst hab
      have hpair : ({a, a} : Finset M.V) = {a} := by simp
      rw [hpair, Finset.sum_singleton]
      linarith [M.cutTwoPoint_nonneg R 0 a]
    · rw [Finset.sum_pair hab]
      linarith [M.cutTwoPoint_nonneg R 0 a, M.cutTwoPoint_nonneg R 0 b]

/-- **The per-vertex mass of the cutoff factor is bounded by the lattice ball.**  At a vertex `x`,
only the edges of length at most `r` can contribute, and there are at most `#(ball r)` of them. -/
theorem sum_cutPivotFactor_ite_le (r : ℝ) (x : M.V) (u : Finset (Sym2 M.V)) :
    ∑ e ∈ u, M.cutPivotFactor r e * (if x ∈ e then (1 : ℝ) else 0)
      ≤ ((M.ball r).ncard : ℝ) := by
  classical
  have h1 : ∑ e ∈ u, M.cutPivotFactor r e * (if x ∈ e then (1 : ℝ) else 0)
      ≤ ∑ e ∈ u, (if x ∈ e ∧ inSupport M r e then (1 : ℝ) else 0) := by
    refine Finset.sum_le_sum fun e _ => ?_
    by_cases hx : x ∈ e
    · by_cases hs : inSupport M r e
      · rw [ite_eq_left hx, ite_eq_left ⟨hx, hs⟩, mul_one]
        exact M.cutPivotFactor_le_one r e
      · rw [ite_eq_left hx, ite_eq_right (fun h => hs h.2),
          M.cutPivotFactor_eq_zero_of_not_inSupport r hs]
        simp
    · rw [ite_eq_right hx, ite_eq_right (fun h => hx h.1), mul_zero]
  refine h1.trans ?_
  have h2 : ((u.filter (fun e => x ∈ e ∧ inSupport M r e)).card : ℝ)
      = ∑ e ∈ u, (if x ∈ e ∧ inSupport M r e then (1 : ℝ) else 0) := by
    rw [Finset.card_filter]
    push_cast
    rfl
  rw [← h2]
  exact M.card_filter_incidentSupport_le r x u

/-- The pivotal majorant is nonnegative. -/
theorem pivotMajorant_nonneg (r0 R : ℝ) (e : Sym2 M.V) : 0 ≤ M.pivotMajorant r0 R e :=
  mul_nonneg (M.cutPivotFactor_nonneg r0 e) (M.edgeTouchMass_nonneg R e)

/-- **The pivotal majorant is summable at a finite first cutoff moment.**  The proof is the
fixed-radius incident count: each edge is counted once per endpoint, and at a vertex only the
edges of length at most `r0` carry a nonzero cutoff factor, so the whole edge series is bounded by
`2 * #(ball r0)` times the first cutoff moment `∑'_x cutTwoPoint R 0 x = cutMassReal R` at the
comparison radius. -/
theorem summable_pivotMajorant {r0 R : ℝ} (h1 : M.cutMoment 1 R ≠ ⊤) :
    Summable (M.pivotMajorant r0 R) := by
  classical
  set P : M.V → ℝ := fun x => M.cutTwoPoint R 0 x
  have hPnonneg : ∀ x : M.V, 0 ≤ P x := fun x => M.cutTwoPoint_nonneg R 0 x
  have hPsumm : Summable P := by
    refine M.summable_cutTwoPoint_of_finite ?_
    rwa [M.cutMassAt_zero_eq_cutMoment]
  have hDnonneg : (0 : ℝ) ≤ ((M.ball r0).ncard : ℝ) := Nat.cast_nonneg _
  refine summable_of_sum_le (c := 2 * ((M.ball r0).ncard : ℝ) * ∑' x : M.V, P x)
    (fun e => M.pivotMajorant_nonneg r0 R e) ?_
  intro u
  set W : Finset M.V := u.biUnion (fun e => e.toFinset)
  have hWmem : ∀ e ∈ u, e.toFinset ⊆ W := by
    intro e he x hx
    exact Finset.mem_biUnion.mpr ⟨e, he, hx⟩
  -- step 1: keep the cutoff factor inside the endpoint sum
  have hstep1 : ∑ e ∈ u, M.pivotMajorant r0 R e
      ≤ 2 * ∑ e ∈ u, ∑ x ∈ e.toFinset, M.cutPivotFactor r0 e * P x := by
    rw [Finset.mul_sum]
    refine Finset.sum_le_sum fun e _ => ?_
    rw [pivotMajorant]
    have h := mul_le_mul_of_nonneg_left (M.edgeTouchMass_le_two_mul_toFinset_sum (R := R) e)
      (M.cutPivotFactor_nonneg r0 e)
    have h' : M.cutPivotFactor r0 e * (2 * ∑ x ∈ e.toFinset, P x)
        = 2 * ∑ x ∈ e.toFinset, M.cutPivotFactor r0 e * P x := by
      calc M.cutPivotFactor r0 e * (2 * ∑ x ∈ e.toFinset, P x)
          = 2 * (M.cutPivotFactor r0 e * ∑ x ∈ e.toFinset, P x) := by ring
        _ = 2 * ∑ x ∈ e.toFinset, M.cutPivotFactor r0 e * P x := by rw [Finset.mul_sum]
    rw [h'] at h
    exact h
  -- step 2: extend the inner sum to the finite vertex set and exchange the two sums
  have hstep2 : ∑ e ∈ u, ∑ x ∈ e.toFinset, M.cutPivotFactor r0 e * P x
      ≤ ∑ x ∈ W, P x * ((M.ball r0).ncard : ℝ) := by
    have hswap : ∑ e ∈ u, ∑ x ∈ e.toFinset, M.cutPivotFactor r0 e * P x
        = ∑ e ∈ u, ∑ x ∈ W, (if x ∈ e then M.cutPivotFactor r0 e * P x else 0) := by
      refine Finset.sum_congr rfl fun e he => ?_
      have h1 : ∑ x ∈ e.toFinset, M.cutPivotFactor r0 e * P x
          = ∑ x ∈ e.toFinset, (if x ∈ e then M.cutPivotFactor r0 e * P x else 0) := by
        refine Finset.sum_congr rfl fun x hx => ?_
        rw [ite_eq_left (Sym2.mem_toFinset.mp hx)]
      rw [h1, Finset.sum_subset (hWmem e he)]
      intro x _ hx
      exact ite_eq_right (fun h => hx (Sym2.mem_toFinset.mpr h))
    rw [hswap, Finset.sum_comm]
    refine Finset.sum_le_sum fun x _ => ?_
    have hx1 : ∑ e ∈ u, (if x ∈ e then M.cutPivotFactor r0 e * P x else 0)
        = P x * ∑ e ∈ u, M.cutPivotFactor r0 e * (if x ∈ e then (1 : ℝ) else 0) := by
      rw [Finset.mul_sum]
      refine Finset.sum_congr rfl fun e _ => ?_
      by_cases hx : x ∈ e
      · rw [ite_eq_left hx, ite_eq_left hx]; ring
      · rw [ite_eq_right hx, ite_eq_right hx]; ring
    rw [hx1]
    exact mul_le_mul_of_nonneg_left (M.sum_cutPivotFactor_ite_le r0 x u) (hPnonneg x)
  calc ∑ e ∈ u, M.pivotMajorant r0 R e
      ≤ 2 * ∑ e ∈ u, ∑ x ∈ e.toFinset, M.cutPivotFactor r0 e * P x := hstep1
    _ ≤ 2 * ∑ x ∈ W, P x * ((M.ball r0).ncard : ℝ) := by
        exact mul_le_mul_of_nonneg_left hstep2 (by norm_num)
    _ = 2 * ((∑ x ∈ W, P x) * ((M.ball r0).ncard : ℝ)) := by
        rw [Finset.sum_mul]
    _ ≤ 2 * ((∑' x : M.V, P x) * ((M.ball r0).ncard : ℝ)) := by
        refine mul_le_mul_of_nonneg_left ?_ (by norm_num)
        exact mul_le_mul_of_nonneg_right (hPsumm.sum_le_tsum W (fun x _ => hPnonneg x)) hDnonneg
    _ = 2 * ((M.ball r0).ncard : ℝ) * ∑' x : M.V, P x := by ring



/-! ## 4. Continuity of the normalized pivotal mass from fixed-edge pivotal flux continuity -/

/-- The edge touch mass is monotone in the cutoff radius. -/
theorem edgeTouchMass_mono {r R : ℝ} (hr : 0 < r) (hR : 0 < R) (hrR : r ≤ R)
    (e : Sym2 M.V) : M.edgeTouchMass r e ≤ M.edgeTouchMass R e := by
  induction e using Sym2.ind with
  | h a b =>
    rw [edgeTouchMass_mk, edgeTouchMass_mk]
    have h1 := M.cutTwoPoint_mono_r (x := (0 : M.V)) (y := a) hr hR hrR
    have h2 := M.cutTwoPoint_mono_r (x := (0 : M.V)) (y := b) hr hR hrR
    linarith

/-- **Continuity of the normalized pivotal mass off corner, from the fixed-edge pivotal flux.**
Let `r0 > 0` be off the corner set and `R > r0` a radius with finite first cutoff moment.  Assume
that at `r0` the singleton pivotal flux of every edge *activated at `r0`* is continuous in the
radius.  Then the whole normalized pivotal mass is continuous at `r0`.

The infinite edge series is handled by Tannery's theorem with the radius-uniform majorant
`pivotMajorant r0 R`, whose summability is exactly `summable_pivotMajorant`.  No continuity of the
total mass, of the singleton flux, or uniformity beyond the first moment is assumed. -/
theorem continuousAt_normalizedPivotMass_of_continuousAt_pivotalFlux
    {y : M.V} {r0 R : ℝ} (hr0 : 0 < r0) (hr0R : r0 < R)
    (hoff : r0 ∉ M.attainedRadii)
    (h1 : M.cutMoment 1 R ≠ ⊤)
    (hpiv : ∀ e : Sym2 M.V, inSupport M r0 e →
      ContinuousAt (fun r => pivotalFlux (edgeMeasure (M.cutProb r))
        (sMomentTrunc (fun _ => (1 : ℝ)) (0 : M.V) ({y} : Finset M.V)) e) r0) :
    ContinuousAt (M.normalizedPivotMass y) r0 := by
  classical
  -- a corner-free window inside `(0, R)`
  obtain ⟨ε, hε0, hε⟩ := M.exists_nhds_notMem_attainedRadii hoff
  set δ : ℝ := min (min ε (R - r0)) (r0 / 2) with hδ
  have hδ0 : 0 < δ := lt_min (lt_min hε0 (sub_pos.mpr hr0R)) (by linarith)
  have hδε : δ ≤ ε := (min_le_left _ _).trans (min_le_left _ _)
  have hδR : δ ≤ R - r0 := (min_le_left _ _).trans (min_le_right _ _)
  have hδr : δ ≤ r0 / 2 := min_le_right _ _
  have hWindow : Metric.ball r0 δ ∈ 𝓝 r0 := Metric.ball_mem_nhds r0 hδ0
  -- on the window the cutoff factor is frozen
  have hfac : ∀ᶠ r in 𝓝 r0, ∀ e : Sym2 M.V, M.cutPivotFactor r e = M.cutPivotFactor r0 e := by
    filter_upwards [hWindow] with r hr
    intro e
    have hr' : |r - r0| < δ := by
      rw [← Real.dist_eq]; exact hr
    have hrε : |r - r0| < ε := lt_of_lt_of_le hr' hδε
    exact M.cutPivotFactor_eq_of_cornerFree (r0 := r0) (ε := ε) hε hrε e
  -- on the window the comparison radius dominates
  have hrlt : ∀ᶠ r in 𝓝 r0, r < R ∧ 0 < r := by
    filter_upwards [hWindow] with r hr
    have hr' : |r - r0| < δ := by
      rw [← Real.dist_eq]; exact hr
    have h1' : r0 - δ < r := by
      rw [abs_lt] at hr'
      linarith [hr'.1]
    have h2' : r < r0 + δ := by
      rw [abs_lt] at hr'
      linarith [hr'.2]
    refine ⟨by linarith, by linarith⟩
  -- Tannery's theorem with the frozen factor
  have hsumm : Summable (M.pivotMajorant r0 R) := M.summable_pivotMajorant h1
  have hbound : ∀ᶠ r in 𝓝 r0, ∀ e : Sym2 M.V,
      ‖M.cutPivotFactor r0 e * pivotalFlux (edgeMeasure (M.cutProb r))
        (sMomentTrunc (fun _ => (1 : ℝ)) (0 : M.V) ({y} : Finset M.V)) e‖
        ≤ M.pivotMajorant r0 R e := by
    filter_upwards [hrlt] with r hr
    intro e
    have hrpos : 0 < r := hr.2
    have hrR : r ≤ R := hr.1.le
    have hpivnonneg : 0 ≤ pivotalFlux (edgeMeasure (M.cutProb r))
        (sMomentTrunc (fun _ => (1 : ℝ)) (0 : M.V) ({y} : Finset M.V)) e := by
      rw [pivotalFlux]
      exact integral_nonneg fun ω => M.flipDiff_sMomentTrunc_singleton_nonneg y e ω
    have hnn : 0 ≤ M.cutPivotFactor r0 e * pivotalFlux (edgeMeasure (M.cutProb r))
        (sMomentTrunc (fun _ => (1 : ℝ)) (0 : M.V) ({y} : Finset M.V)) e :=
      mul_nonneg (M.cutPivotFactor_nonneg r0 e) hpivnonneg
    rw [Real.norm_eq_abs, abs_of_nonneg hnn]
    calc M.cutPivotFactor r0 e * pivotalFlux (edgeMeasure (M.cutProb r))
          (sMomentTrunc (fun _ => (1 : ℝ)) (0 : M.V) ({y} : Finset M.V)) e
        ≤ M.cutPivotFactor r0 e * M.edgeTouchMass r e :=
          mul_le_mul_of_nonneg_left (M.pivotalFlux_singleton_le_edgeTouchMass y e)
            (M.cutPivotFactor_nonneg r0 e)
      _ ≤ M.cutPivotFactor r0 e * M.edgeTouchMass R e :=
          mul_le_mul_of_nonneg_left (M.edgeTouchMass_mono hrpos (lt_trans hr0 hr0R) hrR e)
            (M.cutPivotFactor_nonneg r0 e)
      _ = M.pivotMajorant r0 R e := rfl
  have htend : Tendsto (fun r => ∑' e : Sym2 M.V, M.cutPivotFactor r0 e *
      pivotalFlux (edgeMeasure (M.cutProb r))
        (sMomentTrunc (fun _ => (1 : ℝ)) (0 : M.V) ({y} : Finset M.V)) e) (𝓝 r0)
      (𝓝 (∑' e : Sym2 M.V, M.cutPivotFactor r0 e *
        pivotalFlux (edgeMeasure (M.cutProb r0))
          (sMomentTrunc (fun _ => (1 : ℝ)) (0 : M.V) ({y} : Finset M.V)) e)) := by
    refine tendsto_tsum_of_dominated_convergence (bound := M.pivotMajorant r0 R) hsumm ?_ hbound
    intro e
    by_cases hs : inSupport M r0 e
    · exact (hpiv e hs).const_mul (M.cutPivotFactor r0 e)
    · have hzero : M.cutPivotFactor r0 e = 0 := M.cutPivotFactor_eq_zero_of_not_inSupport r0 hs
      simp only [hzero, zero_mul]
      exact tendsto_const_nhds
  -- transfer along the eventual identification with the frozen series
  refine htend.congr' ?_
  filter_upwards [hfac] with r hr
  rw [normalizedPivotMass]
  exact tsum_congr fun e => by rw [hr e]


/-! ## 5. Corollaries: second moment and the singleton flux -/

/-- The first cutoff moment is at most the second.  The cluster of the origin always contains the
origin, so `clusterVol ≥ 1` pointwise. -/
theorem cutMoment_one_le_cutMoment_two (r : ℝ) : M.cutMoment 1 r ≤ M.cutMoment 2 r := by
  rw [cutMoment]
  refine lintegral_mono fun ω => ?_
  have hone : (1 : ℝ≥0∞) ≤ clusterVol ω (0 : M.V) := by
    rw [clusterVol_eq_tsum]
    have hterm : ((cluster ω (0 : M.V)).indicator (fun _ => (1 : ℝ≥0∞)) 0) = 1 :=
      Set.indicator_of_mem (PercLib.Percolation.Bond.mem_cluster_self ω 0) _
    calc (1 : ℝ≥0∞) = ((cluster ω (0 : M.V)).indicator (fun _ => (1 : ℝ≥0∞)) 0) := hterm.symm
      _ ≤ ∑' w : M.V, ((cluster ω (0 : M.V)).indicator (fun _ => (1 : ℝ≥0∞)) w) :=
        ENNReal.le_tsum 0
  simpa only [pow_one] using le_self_pow₀ hone (by norm_num : (2 : ℕ) ≠ 0)

/-- The off-corner normalized-pivotal-mass reduction with a finite *second* cutoff moment at the
comparison radius instead of the first moment. -/
theorem continuousAt_normalizedPivotMass_of_continuousAt_pivotalFlux_of_moment_two
    {y : M.V} {r0 R : ℝ} (hr0 : 0 < r0) (hr0R : r0 < R)
    (hoff : r0 ∉ M.attainedRadii)
    (h2 : M.cutMoment 2 R ≠ ⊤)
    (hpiv : ∀ e : Sym2 M.V, inSupport M r0 e →
      ContinuousAt (fun r => pivotalFlux (edgeMeasure (M.cutProb r))
        (sMomentTrunc (fun _ => (1 : ℝ)) (0 : M.V) ({y} : Finset M.V)) e) r0) :
    ContinuousAt (M.normalizedPivotMass y) r0 :=
  M.continuousAt_normalizedPivotMass_of_continuousAt_pivotalFlux hr0 hr0R hoff
    (ne_top_of_le_ne_top h2 (M.cutMoment_one_le_cutMoment_two R)) hpiv

/-- **The singleton flux is continuous off corner** once the kernel derivative is, the normalized
pivotal mass reduction applies, and the first cutoff moment is finite at a strictly larger
radius.  This replaces the black-box `ContinuousAt (normalizedPivotMass y)` premise of the landed
kernel-factor sufficiency theorem by the fixed-edge pivotal flux continuity. -/
theorem continuousAt_sMomentInfFlux_of_continuousAt_deriv_of_continuousAt_pivotalFlux
    {y : M.V} {r0 R : ℝ} (hr0 : 0 < r0) (hr0R : r0 < R)
    (hoff : r0 ∉ M.attainedRadii)
    (h1 : M.cutMoment 1 R ≠ ⊤)
    (hK' : ContinuousAt (fun r => deriv M.K r) r0)
    (hpiv : ∀ e : Sym2 M.V, inSupport M r0 e →
      ContinuousAt (fun r => pivotalFlux (edgeMeasure (M.cutProb r))
        (sMomentTrunc (fun _ => (1 : ℝ)) (0 : M.V) ({y} : Finset M.V)) e) r0) :
    ContinuousAt (sMomentInfFlux (0 : M.V) ({y} : Finset M.V) (fun _ => (1 : ℝ))
      M.cutProb M.cutEdgeDeriv) r0 :=
  M.continuousAt_sMomentInfFlux_of_continuousAt_deriv hr0 hK'
    (M.continuousAt_normalizedPivotMass_of_continuousAt_pivotalFlux hr0 hr0R hoff h1 hpiv)

/-- **The per-vertex flux continuity `hcontinf` on an off-corner window**, from `K'` continuity,
fixed-edge pivotal flux continuity and a finite first cutoff moment at the right endpoint. -/
theorem hcontinf_of_continuousAt_deriv_of_continuousAt_pivotalFlux
    {α β : ℝ} (hα : 0 < α) (h1β : M.cutMoment 1 β ≠ ⊤)
    (hoff : ∀ r ∈ Set.Ioo α β, r ∉ M.attainedRadii)
    (hK' : ∀ r ∈ Set.Ioo α β, ContinuousAt (fun r => deriv M.K r) r)
    (hpiv : ∀ (y : M.V) (r : ℝ), r ∈ Set.Ioo α β → ∀ e : Sym2 M.V, inSupport M r e →
      ContinuousAt (fun r' => pivotalFlux (edgeMeasure (M.cutProb r'))
        (sMomentTrunc (fun _ => (1 : ℝ)) (0 : M.V) ({y} : Finset M.V)) e) r) :
    ∀ y : M.V, ∀ r ∈ Set.Ioo α β, ContinuousAt
      (sMomentInfFlux (0 : M.V) ({y} : Finset M.V) (fun _ => (1 : ℝ))
        M.cutProb M.cutEdgeDeriv) r :=
  fun y r hr =>
    M.continuousAt_sMomentInfFlux_of_continuousAt_deriv (lt_trans hα hr.1) (hK' r hr)
      (M.continuousAt_normalizedPivotMass_of_continuousAt_pivotalFlux (lt_trans hα hr.1) hr.2
        (hoff r hr) h1β (fun e he => hpiv y r hr e he))

/-! ## 6. Finite distance scales, and the envelope endpoint wrapper -/

/-- **The activated distance scales at `r0` are finite.**  Although the cutoff factor at `r0` has
infinitely many nonzero edge entries (all translates of an edge of length at most `r0`), its
support meets only finitely many distance scales: the attained radii below `r0`. -/
theorem exists_finite_activated_distances (r0 : ℝ) :
    ∃ D : Finset ℝ, ∀ x y : M.V, x ≠ y → M.cutPivotFactor r0 s(x, y) ≠ 0 → M.S.dist x y ∈ D := by
  classical
  refine ⟨(M.finite_attainedRadii_inter_Iic r0).toFinset, fun x y hxy hne => ?_⟩
  rw [Set.Finite.mem_toFinset]
  refine ⟨M.S.mem_attainedRadii_of_dist hxy, ?_⟩
  by_contra hgt
  have hgt' : r0 < M.S.dist x y := not_le.mp hgt
  rw [cutPivotFactor, radialSym_mk, ite_eq_right hxy, ite_eq_right (not_le.mpr hgt')] at hne
  exact hne rfl

/-- **The off-corner endpoint derivative with the normalized-mass continuity replaced by
fixed-edge pivotal flux continuity.**  This is
`hasDerivAt_cutMassReal_rhsScalar_of_envelope_of_kernelC1` with the black-box hypothesis
`ContinuousAt (normalizedPivotMass y)` discharged through
`continuousAt_normalizedPivotMass_of_continuousAt_pivotalFlux` from the second cutoff moment at
the right endpoint and fixed-edge pivotal flux continuity.  The envelope data, the off-corner
hypothesis, the kernel `C¹` regularity and the summed-mass continuity remain explicit. -/
theorem hasDerivAt_cutMassReal_rhsScalar_of_envelope_of_pivotalFlux
    (T : ℕ → Finset M.V) (hTmono : Monotone T) (hT : ∀ y : M.V, ∃ n, y ∈ T n)
    (S : ℕ → Finset (Sym2 M.V)) (hSmono : Monotone S) (hS : ∀ e : Sym2 M.V, ∃ n, e ∈ S n)
    {α β r0 C : ℝ} (hα0 : 0 < α) (hαr0 : α < r0) (hr0β : r0 < β)
    (hoff : ∀ r ∈ Set.Ioo α β, r ∉ M.cornerRadii)
    (hKd : ∀ r ∈ Set.Ioo α β, DifferentiableAt ℝ M.K r)
    (h2β : M.cutMoment 2 β ≠ ⊤)
    (hC0 : 0 ≤ C) (hCb : ∀ r ∈ Set.Ioo α β, -(deriv M.K r) ≤ C)
    (hKβ : deriv M.K β < 0)
    (hK' : ∀ r ∈ Set.Ioo α β, ContinuousAt (fun r => deriv M.K r) r)
    (hpiv : ∀ (y : M.V) (r : ℝ), r ∈ Set.Ioo α β → ∀ e : Sym2 M.V, inSupport M r e →
      ContinuousAt (fun r' => pivotalFlux (edgeMeasure (M.cutProb r'))
        (sMomentTrunc (fun _ => (1 : ℝ)) (0 : M.V) ({y} : Finset M.V)) e) r)
    (hBsum : ∀ r ∈ Set.Ioo α β,
      ContinuousAt (fun r' => ∑' y : M.V, M.normalizedPivotMass y r') r) :
    HasDerivAt M.cutMassReal (M.rhsScalar r0) r0 :=
  M.hasDerivAt_cutMassReal_rhsScalar_of_envelope_of_kernelC1 T hTmono hT S hSmono hS hα0 hαr0
    hr0β hoff hKd h2β hC0 hCb hKβ hK'
    (fun y r hr =>
      M.continuousAt_normalizedPivotMass_of_continuousAt_pivotalFlux (lt_trans hα0 hr.1) hr.2
        (by rw [M.attainedRadii_eq_cornerRadii]; exact hoff r hr)
        (ne_top_of_le_ne_top h2β (M.cutMoment_one_le_cutMoment_two β))
        (fun e he => hpiv y r hr e he))
    hBsum

end SourceModelData

end PercLib.CriticalLRP.Orchestration

/-! ## Axiom audit -/

set_option linter.hashCommand false

open PercLib.CriticalLRP.Orchestration.SourceModelData

#print axioms PercLib.CriticalLRP.Orchestration.SourceModelData.edgeTouchMass
#print axioms PercLib.CriticalLRP.Orchestration.SourceModelData.edgeTouchMass_mk
#print axioms PercLib.CriticalLRP.Orchestration.SourceModelData.edgeTouchMass_nonneg
#print axioms PercLib.CriticalLRP.Orchestration.SourceModelData.pivotMajorant
#print axioms flipDiff_singleton_le_touchIndicator
#print axioms pivotalFlux_singleton_le_touchProb
#print axioms touchSet_subset_endpoint_clusters
#print axioms real_cluster_mem_eq_cutTwoPoint
#print axioms pivotalFlux_singleton_le_edgeTouchMass
#print axioms cutPivotFactor_eq_of_cornerFree
#print axioms cutPivotFactor_eq_zero_of_not_inSupport
#print axioms edgeTouchMass_le_two_mul_toFinset_sum
#print axioms sum_cutPivotFactor_ite_le
#print axioms pivotMajorant_nonneg
#print axioms summable_pivotMajorant
#print axioms edgeTouchMass_mono
#print axioms continuousAt_normalizedPivotMass_of_continuousAt_pivotalFlux
#print axioms cutMoment_one_le_cutMoment_two
#print axioms continuousAt_normalizedPivotMass_of_continuousAt_pivotalFlux_of_moment_two
#print axioms continuousAt_sMomentInfFlux_of_continuousAt_deriv_of_continuousAt_pivotalFlux
#print axioms hcontinf_of_continuousAt_deriv_of_continuousAt_pivotalFlux
#print axioms exists_finite_activated_distances
#print axioms hasDerivAt_cutMassReal_rhsScalar_of_envelope_of_pivotalFlux
