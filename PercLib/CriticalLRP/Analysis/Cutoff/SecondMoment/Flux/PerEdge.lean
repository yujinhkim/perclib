/-
Copyright (c) 2026 PercLib contributors. Released under Apache 2.0.

# The real-valued `p = 2` per-edge flux identity for the *unbounded* square functional

Swarm `smwvctsvt`, member `m2`, direction `d1`.

Integration donor: `.ultramath/smwvctsvt/m2`; independently checked at `1c0e4b0dd9575c3ef811ef57e2669b0e8387a1fa`.

The landed `p = 1` theory obtains the per-edge flux identity by the closed-coordinate
factorization `ExcludedFlux.one_sub_mul_pivotalFlux_eq`, which requires the observation `g`
to be *bounded*.  The `p = 2` target is the observation `F ω = |K_0(ω)|²` (as a real number),
which is unbounded, so that theorem does not apply directly, and the donor packets stopped at
the finite-truncation statement.

This file closes that step, for the specific quadratic observation, with explicit moment
finiteness hypotheses and without any `⊤ ↦ 0` shortcut.  The mechanism is the exact *single-edge merge
identity* `clusterVol_sq_union_pair_eq_add_quadEdgeWeight`: opening the closed edge `{x,y}`
changes `|K_0|²` by exactly the quadratic edge weight `quadEdgeWeight`, and that identity is
stated at the *closed* configuration `ω \ {e}` rather than at `ω`.  Hence the flip difference
of the unbounded square is, almost surely,

  `flipDiff |K_0|² e ω = (quadEdgeWeight (ω \ {e})).toReal`,

an identity of *finite* real numbers as soon as every cluster volume of `ω` is finite.  The
`(1 - q_e)` factor is then absorbed by the landed closed-coordinate factorization applied to
the *nonnegative* function `ω ↦ quadEdgeWeight (ω \ {e})`, and the closed indicator can be
dropped because the edge weight vanishes on the open event `{e ∈ ω}`.

## What is claimed

* `quadEdgeWeight_eq_qEdgeIncrFull` — the unordered edge weight of `SecondMoment/EdgeFamily`
  is *pointwise* the untruncated excluded increment `qEdgeIncrFull` of `Fibre/QuadraticClosed`.
* `flipDiff_clusterVol_sq_eq_quadEdgeWeight_sdiff` — the exact almost-sure single-edge merge
  identity for the unbounded square, with the closed configuration.
* `one_sub_cutProb_mul_pivotalFlux_eq` — the real-valued per-edge flux identity at a genuine
  edge `{x,y}` (distinct endpoints, length `≤ r`).
* `cutEdgeClosedWeight_mul_pivotalFlux_eq` — the same identity for **every** edge, with the
  closed-edge weight `M.cutEdgeClosedWeight r e` of the derivative coefficient; loops and
  out-of-window edges give `0 = 0`.

## What is *not* claimed

No radius derivative, no continuity in `r`, no two-sided statement at attained radii, and no
summation over `e`.  The identity is per edge and holds at every real `r`.
-/
module

public import PercLib.CriticalLRP.Analysis.Cutoff.SecondMoment.EdgeFamily.Increment
public import PercLib.CriticalLRP.Analysis.Cutoff.SecondMoment.EdgeFamily.Main
public import PercLib.CriticalLRP.Analysis.Cutoff.Fibre.QuadraticClosed.Main
public import PercLib.CriticalLRP.Analysis.Cutoff.SecondMoment.Transport.ToReal
public import PercLib.CriticalLRP.Analysis.Cutoff.SecondMoment.Transport.Coeff

/-!
# The real per-edge `p = 2` flux identity for `|K_0|²`
-/

set_option autoImplicit false
set_option linter.style.longLine false
set_option linter.hashCommand false
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false

open MeasureTheory
open scoped ENNReal NNReal

@[expose] public section

namespace PercLib.CriticalLRP

attribute [local instance] Classical.propDecidable

variable {V : Type*} [Countable V]

/-! ## 1. Measurability and finiteness of the oriented weights -/

/-- The oriented `p = 2` pair weight is measurable in the configuration. -/
theorem measurable_quadPairWeight (dt : V → V → Prop) (o : V) (b c : V) :
    Measurable fun ω : Config V => quadPairWeight dt ω o b c := by
  have h1 : Measurable fun ω : Config V => (if Connects ω o b then (1 : ℝ≥0∞) else 0) :=
    Measurable.ite (measurableSet_connects o b) measurable_const measurable_const
  have h3 : Measurable fun ω : Config V => (if ¬ Connects ω b c then (1 : ℝ≥0∞) else 0) :=
    Measurable.ite (measurableSet_connects b c).compl measurable_const measurable_const
  have h4 : Measurable fun ω : Config V => clusterVol ω b := measurable_clusterVol b
  have h5 : Measurable fun ω : Config V => clusterVol ω c := measurable_clusterVol c
  have hinner : Measurable fun ω : Config V =>
      2 * clusterVol ω b * clusterVol ω c + clusterVol ω c ^ 2 :=
    ((h4.const_mul 2).mul h5).add (h5.pow_const 2)
  exact ((h1.mul measurable_const).mul h3).mul hinner

/-- The unordered `p = 2` edge weight is measurable in the configuration. -/
theorem measurable_quadEdgeWeight (dt : V → V → Prop) (o : V) (e : Sym2 V) :
    Measurable fun ω : Config V => quadEdgeWeight dt ω o e := by
  induction e using Sym2.ind with
  | h x y =>
    simp only [quadEdgeWeight_mk]
    exact (measurable_quadPairWeight dt o x y).add (measurable_quadPairWeight dt o y x)

/-- The oriented pair weight is bounded by the quadratic expression in the two endpoint cluster
volumes. -/
theorem quadPairWeight_le (dt : V → V → Prop) (ω : Config V) (o b c : V) :
    quadPairWeight dt ω o b c ≤ 2 * clusterVol ω b * clusterVol ω c + clusterVol ω c ^ 2 := by
  unfold quadPairWeight
  calc (if Connects ω o b then (1 : ℝ≥0∞) else 0) * (if dt c b then 1 else 0) *
        (if ¬ Connects ω b c then 1 else 0) *
          (2 * clusterVol ω b * clusterVol ω c + clusterVol ω c ^ 2)
      ≤ 1 * 1 * 1 * (2 * clusterVol ω b * clusterVol ω c + clusterVol ω c ^ 2) := by
        gcongr <;> split <;> simp
    _ = 2 * clusterVol ω b * clusterVol ω c + clusterVol ω c ^ 2 := by simp

/-- The oriented pair weight is finite on configurations with finite endpoint clusters. -/
theorem quadPairWeight_ne_top (dt : V → V → Prop) (ω : Config V) (o b c : V)
    (hb : clusterVol ω b ≠ ⊤) (hc : clusterVol ω c ≠ ⊤) :
    quadPairWeight dt ω o b c ≠ ⊤ := by
  refine ne_top_of_le_ne_top ?_ (quadPairWeight_le dt ω o b c)
  refine ENNReal.add_ne_top.mpr ⟨?_, ENNReal.pow_ne_top hc⟩
  exact ENNReal.mul_ne_top (ENNReal.mul_ne_top (by norm_num) hb) hc

/-- The unordered edge weight is finite on configurations with finite cluster volumes. -/
theorem quadEdgeWeight_ne_top (dt : V → V → Prop) (ω : Config V) (o x y : V)
    (h : ∀ v : V, clusterVol ω v ≠ ⊤) :
    quadEdgeWeight dt ω o s(x, y) ≠ ⊤ := by
  rw [quadEdgeWeight_mk]
  exact ENNReal.add_ne_top.mpr
    ⟨quadPairWeight_ne_top dt ω o x y (h x) (h y),
      quadPairWeight_ne_top dt ω o y x (h y) (h x)⟩

/-! ## 2. The unordered edge weight is the untruncated excluded increment -/

namespace Orchestration

/-- **The `EdgeFamily` unordered edge weight is the untruncated `qEdgeIncrFull`.**  On the
event that the base point is connected to the first endpoint, the two cluster volumes
`|K_o|` and `|K_b|` coincide; off that event both weights vanish.  This is the pointwise
identification of the `QuadraticClosed` excluded increment with the `EdgeFamily` edge family. -/
theorem quadEdgeWeight_eq_qEdgeIncrFull (M : SourceModelData) (r : ℝ) (ω : Config M.V)
    (e : Sym2 M.V) :
    quadEdgeWeight (fun c b : M.V => M.S.dist c b ≤ r) ω (0 : M.V) e
      = qEdgeIncrFull (cutDist M r) (cutDist_symm M r) ω (0 : M.V) e := by
  induction e using Sym2.ind with
  | h x y =>
    rw [quadEdgeWeight_mk, qEdgeIncrFull_mk]
    have hpair : ∀ b c : M.V,
        quadPairWeight (fun c b : M.V => M.S.dist c b ≤ r) ω (0 : M.V) b c
          = qPairIncrFull (cutDist M r) ω (0 : M.V) b c := by
      intro b c
      by_cases hb : Connects ω (0 : M.V) b
      · have hK : clusterVol ω b = clusterVol ω (0 : M.V) :=
          clusterVol_eq_of_mem_cluster (mem_cluster_iff.mpr hb)
        by_cases hd : M.S.dist c b ≤ r <;> by_cases hc : Connects ω b c <;>
          simp [quadPairWeight, qPairIncrFull, cutDist, hb, hd, hc, hK]
      · simp [quadPairWeight, qPairIncrFull, cutDist, hb]
    simp only [hpair x y, hpair y x]

end Orchestration

/-! ## 3. The derivative closed-edge weight of a genuine edge -/

namespace Orchestration

namespace SourceModelData

variable (M : SourceModelData)

/-- On a genuine edge (distinct endpoints of length `≤ r`) the closed-edge weight of the
derivative coefficient is exactly the closed-coordinate probability `1 - q_e`. -/
theorem cutEdgeClosedWeight_eq_one_sub_cutProb {r : ℝ} {x y : M.V} (hxy : x ≠ y)
    (hdist : M.S.dist x y ≤ r) :
    M.cutEdgeClosedWeight r s(x, y)
      = 1 - ((M.cutProb r s(x, y) : unitInterval) : ℝ) := by
  rw [M.cutEdgeClosedWeight_mk r x y, M.one_sub_cutProb_eq_exp r hxy hdist]
  simp only [ite_eq_right hxy, ite_eq_left hdist]

/-- The closed-edge weight vanishes on a loop. -/
theorem cutEdgeClosedWeight_loop (r : ℝ) (x : M.V) :
    M.cutEdgeClosedWeight r s(x, x) = 0 := by
  simp [SourceModelData.cutEdgeClosedWeight]

/-- The closed-edge weight vanishes outside the radius window. -/
theorem cutEdgeClosedWeight_eq_zero_of_dist_gt {r : ℝ} {x y : M.V}
    (h : r < M.S.dist x y) : M.cutEdgeClosedWeight r s(x, y) = 0 := by
  by_cases hxy : x = y
  · subst hxy
    exact M.cutEdgeClosedWeight_loop r x
  · rw [M.cutEdgeClosedWeight_mk r x y]
    simp only [ite_eq_right hxy, ite_eq_right (not_le.mpr h)]

end SourceModelData

end Orchestration

/-! ## 4. The almost-sure single-edge merge identity for the unbounded square

The exact increment `clusterVol_sq_union_pair_eq_add_quadEdgeWeight` is applied at the *closed*
configuration `ω \ {e}`, whose cluster volumes are dominated by those of `ω`.  This is why no
finiteness of the cluster at `ω ∪ {e}` is ever needed. -/

namespace Orchestration

namespace SourceModelData

variable (M : SourceModelData)

/-- **Almost-sure per-edge increment of the unbounded square.**  For a genuine edge and a
configuration with finite cluster volumes, the flip difference of `ω ↦ |K_0(ω)|²` is the real
edge weight evaluated at the *closed* configuration. -/
theorem flipDiff_clusterVol_sq_eq_quadEdgeWeight_sdiff (r : ℝ) {x y : M.V} (hxy : x ≠ y)
    (hdist : M.S.dist x y ≤ r) {ω : Config M.V}
    (hfin : ∀ v : M.V, clusterVol ω v ≠ ⊤) :
    flipDiff (fun η => (clusterVol η (0 : M.V)).toReal ^ 2) s(x, y) ω
      = (quadEdgeWeight (fun c b : M.V => M.S.dist c b ≤ r) (ω \ {s(x, y)}) (0 : M.V)
          s(x, y)).toReal := by
  classical
  set ω' : Config M.V := ω \ {s(x, y)} with hω'def
  have hsub : ∀ e ∈ ω', e ∈ ω := by
    intro e he
    rw [hω'def] at he
    exact Set.mem_of_mem_sdiff he
  have hfin' : ∀ v : M.V, clusterVol ω' v ≠ ⊤ := fun v =>
    ne_top_of_le_ne_top (hfin v) (clusterVol_mono hsub v)
  have hunion : ω' ∪ {s(x, y)} = ω ∪ {s(x, y)} := by
    rw [hω'def]
    exact sdiff_singleton_union s(x, y) ω
  have hmain := clusterVol_sq_union_pair_eq_add_quadEdgeWeight
    (dt := fun c b : M.V => M.S.dist c b ≤ r) (ω := ω') (o := (0 : M.V)) hxy
    (by rwa [M.S.dist_comm]) hdist
  have hQ : quadEdgeWeight (fun c b : M.V => M.S.dist c b ≤ r) ω' (0 : M.V) s(x, y) ≠ ⊤ :=
    quadEdgeWeight_ne_top _ _ _ _ _ hfin'
  have hto := congrArg ENNReal.toReal hmain
  rw [ENNReal.toReal_add (ENNReal.pow_ne_top (hfin' 0)) hQ, ENNReal.toReal_pow,
    ENNReal.toReal_pow] at hto
  rw [flipDiff, forceOn_singleton_open_eq, forceOn_singleton_closed_eq, ← hω'def, ← hunion]
  linarith [hto]

/-- **The pivotal flux of the unbounded square is the mean real edge weight at the closed
configuration.** -/
theorem pivotalFlux_clusterVol_sq_eq_integral_quadEdgeWeight_sdiff (r : ℝ) {x y : M.V}
    (hxy : x ≠ y) (hdist : M.S.dist x y ≤ r) (h1 : M.cutMassAt r (0 : M.V) ≠ ⊤) :
    pivotalFlux (M.cutLaw r) (fun ω => (clusterVol ω (0 : M.V)).toReal ^ 2) s(x, y)
      = ∫ ω, (quadEdgeWeight (fun c b : M.V => M.S.dist c b ≤ r) (ω \ {s(x, y)})
          (0 : M.V) s(x, y)).toReal ∂(M.cutLaw r) := by
  rw [pivotalFlux]
  refine integral_congr_ae ?_
  filter_upwards [PivotFlux.ae_clusterVol_ne_top M r h1] with ω hω
  exact flipDiff_clusterVol_sq_eq_quadEdgeWeight_sdiff M r hxy hdist hω

/-- **The real-valued `p = 2` per-edge flux identity at a genuine edge.**

The closed-coordinate factorization of `ExcludedFlux` is applied to the *nonnegative*
closed-configuration edge weight `ω ↦ (quadEdgeWeight (ω \ {e})).toReal`, which is determined
by the coordinates other than `e`; the `(1 - q_e)` factor it produces is exactly the factor
multiplying the pivotal flux.  Finally the closed indicator `1{e ∉ ω}` can be dropped because
the edge weight vanishes on `{e ∈ ω}`. -/
theorem one_sub_cutProb_mul_pivotalFlux_eq (r : ℝ) {x y : M.V} (hxy : x ≠ y)
    (hdist : M.S.dist x y ≤ r) (h1 : M.cutMassAt r (0 : M.V) ≠ ⊤) :
    (1 - ((M.cutProb r s(x, y) : unitInterval) : ℝ)) *
        pivotalFlux (M.cutLaw r) (fun ω => (clusterVol ω (0 : M.V)).toReal ^ 2) s(x, y)
      = ∫ ω, (quadEdgeWeight (fun c b : M.V => M.S.dist c b ≤ r) ω (0 : M.V)
          s(x, y)).toReal ∂(M.cutLaw r) := by
  classical
  have hlaw : M.cutLaw r = PercLib.Percolation.Bond.law (M.cutProb r) :=
    M.cutLaw_eq_edgeMeasure r
  set dt : M.V → M.V → Prop := fun c b => M.S.dist c b ≤ r with hdtdef
  set G : Config M.V → ℝ :=
    fun ω => (quadEdgeWeight dt (ω \ {s(x, y)}) (0 : M.V) s(x, y)).toReal with hGdef
  have hGmeas : Measurable G :=
    ENNReal.measurable_toReal.comp
      ((measurable_quadEdgeWeight dt (0 : M.V) s(x, y)).comp
        (PercLib.Probability.measurable_diff_singleton s(x, y)))
  have hGdet : ∀ ω : Config M.V, G ω = G (ω \ {s(x, y)}) := by
    intro ω
    simp only [hGdef]
    rw [sdiff_singleton_idem]
  have hGnn : ∀ ω : Config M.V, 0 ≤ G ω := fun ω => ENNReal.toReal_nonneg
  have hfac := integral_compl_indicator_mul_of_sdiff_determined (M.cutProb r) s(x, y)
    hGmeas hGdet hGnn
  have hfacM : (∫ ω, (if s(x, y) ∈ ω then 0 else G ω) ∂(M.cutLaw r))
      = (1 - ((M.cutProb r s(x, y) : unitInterval) : ℝ)) *
          ∫ ω, G ω ∂(M.cutLaw r) := by
    rw [hlaw]
    exact hfac
  have hflux := pivotalFlux_clusterVol_sq_eq_integral_quadEdgeWeight_sdiff M r hxy hdist h1
  have hdrop : (∫ ω, (if s(x, y) ∈ ω then 0 else G ω) ∂(M.cutLaw r))
      = ∫ ω, (quadEdgeWeight dt ω (0 : M.V) s(x, y)).toReal ∂(M.cutLaw r) := by
    refine integral_congr_ae (Filter.Eventually.of_forall fun ω => ?_)
    change (if s(x, y) ∈ ω then 0 else G ω)
      = (quadEdgeWeight dt ω (0 : M.V) s(x, y)).toReal
    by_cases h : s(x, y) ∈ ω
    · have hzero : quadEdgeWeight dt ω (0 : M.V) s(x, y) = 0 := by
        rw [quadEdgeWeight_mk]
        have hc : Connects ω x y :=
          SimpleGraph.Adj.reachable ((openGraph_adj (ω := ω)).2 ⟨hxy, h⟩)
        rw [quadPairWeight_eq_zero_of_connects dt ω (0 : M.V) hc,
          quadPairWeight_eq_zero_of_connects dt ω (0 : M.V) (connects_symm hc), add_zero]
      rw [ite_eq_left h, hzero, ENNReal.toReal_zero]
    · rw [ite_eq_right h]
      simp only [hGdef]
      rw [sdiff_singleton_of_notMem h]
  calc (1 - ((M.cutProb r s(x, y) : unitInterval) : ℝ)) *
        pivotalFlux (M.cutLaw r) (fun ω => (clusterVol ω (0 : M.V)).toReal ^ 2) s(x, y)
      = (1 - ((M.cutProb r s(x, y) : unitInterval) : ℝ)) *
          ∫ ω, G ω ∂(M.cutLaw r) := by rw [hflux]
    _ = ∫ ω, (if s(x, y) ∈ ω then 0 else G ω) ∂(M.cutLaw r) := hfacM.symm
    _ = ∫ ω, (quadEdgeWeight dt ω (0 : M.V) s(x, y)).toReal ∂(M.cutLaw r) := hdrop

/-- **The real-valued `p = 2` per-edge flux identity for every edge.**  Loops and edges outside
the radius window contribute `0` on both sides. -/
theorem cutEdgeClosedWeight_mul_pivotalFlux_eq (M : SourceModelData) (r : ℝ)
    (h1 : M.cutMassAt r (0 : M.V) ≠ ⊤) (e : Sym2 M.V) :
    M.cutEdgeClosedWeight r e *
        pivotalFlux (M.cutLaw r) (fun ω => (clusterVol ω (0 : M.V)).toReal ^ 2) e
      = ∫ ω, (quadEdgeWeight (fun c b : M.V => M.S.dist c b ≤ r) ω (0 : M.V) e).toReal
          ∂(M.cutLaw r) := by
  classical
  induction e using Sym2.ind with
  | h x y =>
    by_cases hxy : x = y
    · subst hxy
      rw [M.cutEdgeClosedWeight_loop, zero_mul]
      have hzero : (fun ω : Config M.V =>
          (quadEdgeWeight (fun c b : M.V => M.S.dist c b ≤ r) ω (0 : M.V) s(x, x)).toReal)
          = fun _ => 0 := by
        funext ω
        rw [quadEdgeWeight_diag, ENNReal.toReal_zero]
      rw [hzero]
      simp
    · by_cases hdist : M.S.dist x y ≤ r
      · rw [M.cutEdgeClosedWeight_eq_one_sub_cutProb hxy hdist]
        exact M.one_sub_cutProb_mul_pivotalFlux_eq r hxy hdist h1
      · have hgt : r < M.S.dist x y := not_le.mp hdist
        rw [M.cutEdgeClosedWeight_eq_zero_of_dist_gt hgt, zero_mul]
        have hzero : ∀ ω : Config M.V,
            quadEdgeWeight (fun c b : M.V => M.S.dist c b ≤ r) ω (0 : M.V) s(x, y) = 0 := by
          intro ω
          rw [quadEdgeWeight_mk]
          have h1' : ¬ (M.S.dist y x ≤ r) := by rwa [M.S.dist_comm]
          simp only [quadPairWeight, h1', hdist, ite_false, mul_zero, zero_mul, add_zero]
        simp only [hzero, ENNReal.toReal_zero]
        simp


/-! ## 5. Genuineness: the per-edge flux is a bona fide integral

The per-edge identity of §4 is an identity of real numbers, but a real-valued `integral` in Lean
is `0` on a non-integrable function, so the identity would be vacuous if the flip difference were
not integrable.  Here we prove that it *is*, for every genuine edge, from the finiteness of the
`p = 2` right-hand side.  The argument is the `ℝ≥0∞` companion of §4: the closed-coordinate
factorization gives

  `(1 - q_e) · ∫⁻ ω, quadEdgeWeight ((ω \ {e})) = ∫⁻ ω, quadEdgeWeight (ω)`

and the right-hand side is finite by the `EdgeFamily` exhaustion of `p2RHS`, so the left-hand
side is finite because `1 - q_e > 0` on a genuine edge. -/

/-- On a genuine edge the closed-coordinate probability `1 - q_e` is strictly positive. -/
theorem one_sub_cutProb_pos (r : ℝ) {x y : M.V} (hxy : x ≠ y) (hdist : M.S.dist x y ≤ r) :
    0 < 1 - ((M.cutProb r s(x, y) : unitInterval) : ℝ) := by
  rw [M.one_sub_cutProb_eq_exp r hxy hdist]
  exact Real.exp_pos _

set_option maxHeartbeats 1600000 in
-- The `Sym2`/`s(x,y)` elaboration of the edge weight makes the default budget too small; the
-- statement itself is elementary.
/-- The `ℝ≥0∞` closed-coordinate factorization at a genuine edge, for the edge weight evaluated
at the *closed* configuration. -/
theorem one_sub_mul_lintegral_quadEdgeWeight_sdiff (r : ℝ) {x y : M.V} (hxy : x ≠ y) :
    ((unitInterval.toNNReal (unitInterval.symm (M.cutProb r s(x, y))) : ℝ≥0) : ℝ≥0∞) *
        ∫⁻ ω, quadEdgeWeight (fun c b : M.V => M.S.dist c b ≤ r) (ω \ {s(x, y)})
          (0 : M.V) s(x, y) ∂(M.cutLaw r)
      = ∫⁻ ω, quadEdgeWeight (fun c b : M.V => M.S.dist c b ≤ r) ω (0 : M.V) s(x, y)
          ∂(M.cutLaw r) := by
  classical
  set dt : M.V → M.V → Prop := fun c b => M.S.dist c b ≤ r with hdtdef
  have hGmeas : Measurable fun ω : Config M.V =>
      quadEdgeWeight dt (ω \ {s(x, y)}) (0 : M.V) s(x, y) :=
    (measurable_quadEdgeWeight dt (0 : M.V) s(x, y)).comp
      (PercLib.Probability.measurable_diff_singleton s(x, y))
  have hGdet : ∀ ω : Config M.V,
      quadEdgeWeight dt (ω \ {s(x, y)}) (0 : M.V) s(x, y)
        = quadEdgeWeight dt ((ω \ {s(x, y)}) \ {s(x, y)}) (0 : M.V) s(x, y) := by
    intro ω
    rw [sdiff_singleton_idem]
  have hfac := lintegral_compl_indicator_mul_of_sdiff_determined (M.cutProb r) s(x, y)
    hGmeas hGdet
  have hfacM : (∫⁻ ω, (if s(x, y) ∈ ω then 0
        else quadEdgeWeight dt (ω \ {s(x, y)}) (0 : M.V) s(x, y)) ∂(M.cutLaw r))
      = ((unitInterval.toNNReal (unitInterval.symm (M.cutProb r s(x, y))) : ℝ≥0) : ℝ≥0∞) *
          ∫⁻ ω, quadEdgeWeight dt (ω \ {s(x, y)}) (0 : M.V) s(x, y) ∂(M.cutLaw r) := by
    rw [M.cutLaw_eq_edgeMeasure]
    exact hfac
  have hpt : ∀ᵐ ω ∂(M.cutLaw r), (if s(x, y) ∈ ω then 0
        else quadEdgeWeight dt (ω \ {s(x, y)}) (0 : M.V) s(x, y))
      = quadEdgeWeight dt ω (0 : M.V) s(x, y) := by
    filter_upwards with ω
    by_cases h : s(x, y) ∈ ω
    · have hzero : quadEdgeWeight dt ω (0 : M.V) s(x, y) = 0 := by
        rw [quadEdgeWeight_mk]
        have hc : Connects ω x y :=
          SimpleGraph.Adj.reachable ((openGraph_adj (ω := ω)).2 ⟨hxy, h⟩)
        rw [quadPairWeight_eq_zero_of_connects dt ω (0 : M.V) hc,
          quadPairWeight_eq_zero_of_connects dt ω (0 : M.V) (connects_symm hc), add_zero]
      rw [ite_eq_left h, hzero]
    · rw [ite_eq_right h, sdiff_singleton_of_notMem h]
  rw [← hfacM]
  exact lintegral_congr_ae hpt

/-- The closed-configuration edge weight has finite `ℝ≥0∞`-mean at a genuine edge, from the
finiteness of `p2RHS`. -/
theorem lintegral_quadEdgeWeight_sdiff_ne_top (r : ℝ) {x y : M.V} (hxy : x ≠ y)
    (hdist : M.S.dist x y ≤ r) (h1 : M.cutMassAt r (0 : M.V) ≠ ⊤) (hp2 : M.p2RHS r ≠ ⊤) :
    ∫⁻ ω, quadEdgeWeight (fun c b : M.V => M.S.dist c b ≤ r) (ω \ {s(x, y)})
        (0 : M.V) s(x, y) ∂(M.cutLaw r) ≠ ⊤ := by
  classical
  have hkey := M.one_sub_mul_lintegral_quadEdgeWeight_sdiff r hxy
  have hR : ∫⁻ ω, quadEdgeWeight (fun c b : M.V => M.S.dist c b ≤ r) ω (0 : M.V) s(x, y)
      ∂(M.cutLaw r) ≠ ⊤ := by
    refine ne_top_of_le_ne_top hp2 ?_
    rw [← lintegral_tsum_quadEdgeWeight_eq_p2RHS M r h1]
    exact lintegral_mono fun ω => ENNReal.le_tsum s(x, y)
  have hq : (0 : ℝ) < 1 - ((M.cutProb r s(x, y) : unitInterval) : ℝ) :=
    M.one_sub_cutProb_pos r hxy hdist
  have hcoe : ((unitInterval.toNNReal (unitInterval.symm (M.cutProb r s(x, y))) : ℝ≥0) : ℝ)
      = 1 - ((M.cutProb r s(x, y) : unitInterval) : ℝ) := by
    rw [← unitInterval.coe_symm_eq (M.cutProb r s(x, y))]
    simp
  have hpos : ((unitInterval.toNNReal (unitInterval.symm (M.cutProb r s(x, y))) : ℝ≥0) : ℝ≥0∞)
      ≠ 0 := by
    have hne : (unitInterval.toNNReal (unitInterval.symm (M.cutProb r s(x, y))) : ℝ≥0) ≠ 0 := by
      intro h0
      have hz : ((unitInterval.toNNReal (unitInterval.symm (M.cutProb r s(x, y))) : ℝ≥0) : ℝ) = 0 :=
        by rw [h0]; rfl
      rw [hcoe] at hz
      linarith
    exact fun h => hne (ENNReal.coe_inj.mp h)
  intro htop
  refine hR ?_
  rw [← hkey, htop]
  simp [hpos]

set_option maxHeartbeats 1600000 in
-- Same `Sym2` elaboration cost as `one_sub_mul_lintegral_quadEdgeWeight_sdiff` above.
/-- **The per-edge flip difference of the unbounded square is integrable.** -/
theorem integrable_flipDiff_clusterVol_sq (r : ℝ) {x y : M.V} (hxy : x ≠ y)
    (hdist : M.S.dist x y ≤ r) (h1 : M.cutMassAt r (0 : M.V) ≠ ⊤) (hp2 : M.p2RHS r ≠ ⊤) :
    Integrable (flipDiff (fun ω => (clusterVol ω (0 : M.V)).toReal ^ 2) s(x, y))
      (M.cutLaw r) := by
  classical
  have hae : ∀ᵐ ω ∂(M.cutLaw r),
      quadEdgeWeight (fun c b : M.V => M.S.dist c b ≤ r) (ω \ {s(x, y)}) (0 : M.V) s(x, y)
        ≠ ⊤ := by
    filter_upwards [PivotFlux.ae_clusterVol_ne_top M r h1] with ω hω
    exact quadEdgeWeight_ne_top _ (ω \ {s(x, y)}) (0 : M.V) x y
      (fun v => ne_top_of_le_ne_top (hω v)
        (clusterVol_mono (ω := ω \ {s(x, y)}) (ω' := ω)
          (fun a ha => Set.mem_of_mem_sdiff ha) v))
  have hbase : Integrable (fun ω =>
      (quadEdgeWeight (fun c b : M.V => M.S.dist c b ≤ r) (ω \ {s(x, y)}) (0 : M.V)
        s(x, y)).toReal) (M.cutLaw r) := by
    refine ⟨(ENNReal.measurable_toReal.comp
      ((measurable_quadEdgeWeight _ (0 : M.V) s(x, y)).comp
        (PercLib.Probability.measurable_diff_singleton s(x, y)))).aestronglyMeasurable, ?_⟩
    rw [MeasureTheory.hasFiniteIntegral_iff_ofReal
      (Filter.Eventually.of_forall fun ω => ENNReal.toReal_nonneg)]
    calc ∫⁻ ω, ENNReal.ofReal
          ((quadEdgeWeight (fun c b : M.V => M.S.dist c b ≤ r) (ω \ {s(x, y)}) (0 : M.V)
            s(x, y)).toReal) ∂(M.cutLaw r)
        = ∫⁻ ω, quadEdgeWeight (fun c b : M.V => M.S.dist c b ≤ r) (ω \ {s(x, y)})
            (0 : M.V) s(x, y) ∂(M.cutLaw r) :=
          lintegral_congr_ae (hae.mono fun ω hω => ENNReal.ofReal_toReal hω)
      _ < ⊤ := lt_top_iff_ne_top.mpr (M.lintegral_quadEdgeWeight_sdiff_ne_top r hxy hdist h1 hp2)
  refine hbase.congr ?_
  filter_upwards [PivotFlux.ae_clusterVol_ne_top M r h1] with ω hω
  exact (flipDiff_clusterVol_sq_eq_quadEdgeWeight_sdiff M r hxy hdist hω).symm

end SourceModelData

end Orchestration

end PercLib.CriticalLRP

/-! ## Axiom audit -/
namespace PercLib.CriticalLRP.Orchestration

#print axioms SourceModelData.one_sub_cutProb_pos
#print axioms SourceModelData.one_sub_mul_lintegral_quadEdgeWeight_sdiff
#print axioms SourceModelData.lintegral_quadEdgeWeight_sdiff_ne_top
#print axioms SourceModelData.integrable_flipDiff_clusterVol_sq

end PercLib.CriticalLRP.Orchestration

namespace PercLib.CriticalLRP

#print axioms measurable_quadPairWeight
#print axioms quadPairWeight_ne_top
#print axioms Orchestration.quadEdgeWeight_eq_qEdgeIncrFull
#print axioms Orchestration.SourceModelData.cutEdgeClosedWeight_eq_one_sub_cutProb
#print axioms Orchestration.SourceModelData.flipDiff_clusterVol_sq_eq_quadEdgeWeight_sdiff
#print axioms Orchestration.SourceModelData.one_sub_cutProb_mul_pivotalFlux_eq
#print axioms Orchestration.SourceModelData.cutEdgeClosedWeight_mul_pivotalFlux_eq

end PercLib.CriticalLRP
