/-
Copyright (c) 2026 PercLib contributors. Released under Apache 2.0.

Swarm `smwveg8a1`, member `m3`, direction (C).

Integration donor: `.ultramath/smwveg8a1/m3/FluxConv`; independently checked at `cfb27572ee02f0e8dbc751b822b50389b54f2df5`.

# The fixed-radius `p = 2` window flux: insertion split and closed ghost

The landed orchestration `SourceModelData.hasDerivAt_cutMomentReal_two` consumes at a fixed
radius `r` the pointwise-in-`r` convergence `hfluxConv` of the finite-window pivotal sums
`M.windowFlux (S k) r` to `M.rhsScalarTwo r`.  This file reduces that input to its two
genuinely different halves and discharges one of them.

## What is proved

* `flipDiff_cutFun_clusterVolSqReal_nonneg` / `pivotalFlux_cutFun_clusterVolSqReal_nonneg`:
  the windowed pivotal fluxes are nonnegative — *not* from any derivative sign, but because the
  windowed square `cutFun S |K₀|²` is monotone in the configuration and every cluster volume of a
  finite-window configuration is finite (`clusterVol_ne_top_of_subset_finset`), so the flip
  difference is a genuine difference of finite squares.
* `pivotalFlux_clusterVolSqReal_nonneg`: the *untruncated* pivotal flux of `|K₀|²` is
  nonnegative, from the source's first cutoff moment (`PivotFlux.ae_clusterVol_ne_top`) and
  monotonicity of `ENNReal.toReal` on finite values.  This is the input to the exhaustion half.
* `cutEdgeClosedWeight_mul_pivotalFlux_cutFun_eq`: **the finite-window per-edge closed-ghost
  identity**
  `M.cutEdgeClosedWeight r e · pivotalFlux (M.cutLaw r) (cutFun S |K₀|²) e
     = M.windowClosedGhost S r e`
  for every `e ∈ S`.  It is the windowed counterpart of the landed
  `cutEdgeClosedWeight_mul_pivotalFlux_eq`, and it needs *no* moment hypothesis: the windowed
  square is bounded by `|S|²`, so the exact merge identity
  `clusterVol_sq_union_pair_eq_add_quadEdgeWeight` holds at every closed windowed configuration,
  and the `(1 - q_e)` closed-coordinate factorization is applied to a genuinely bounded
  observable.
* `tendsto_partialLimitFlux`: the exhaustion half of `hfluxConv`, unconditionally: for a monotone
  exhausting window family the truncated infinite pivotal sums converge to `M.rhsScalarTwo r`
  (the landed fixed-radius FLUX identity plus monotone convergence of `ℝ≥0∞` `tsum` along
  finsets; no summability and no `⊤ ↦ 0` step).
* `tendsto_windowFlux_of_insertionError` and `tendsto_windowFlux_iff`: `hfluxConv` holds iff the
  insertion deficit vanishes; in particular it holds whenever the paper's insertion *error*
  (`SecondMomentExchange.insertionFlux`, with the windowed pivotal fluxes) vanishes.  The
  vanishing of that error is the one genuinely paper-level input this direction does not prove;
  see the module docstring of `Main.lean`'s final section for its exact shape.
-/
module

public import PercLib.CriticalLRP.Analysis.Cutoff.SecondMoment.FluxConv.Defs
public import Mathlib

/-!
# The fixed-radius `p = 2` window flux
-/

set_option autoImplicit false
set_option linter.hashCommand false
set_option linter.style.longLine false

@[expose] public section

noncomputable section

open MeasureTheory Filter Topology
open scoped ENNReal NNReal Topology

namespace PercLib.CriticalLRP

/-! ## 0. Finite windows have finite cluster volumes -/

variable {V : Type*} [Countable V]

/-- The cluster of a vertex inside a configuration that is contained in a finite edge set is
finite: every vertex of the cluster other than the root is an endpoint of an open edge of that
finite set. -/
theorem clusterVol_ne_top_of_subset_finset {S : Finset (Sym2 V)} {ω : Config V}
    (h : ∀ e : Sym2 V, e ∈ ω → e ∈ S) (v : V) : clusterVol ω v ≠ ⊤ := by
  classical
  have hsub : cluster ω v ⊆ ((insert v (edgeVertices S) : Finset V) : Set V) := by
    intro w hw
    have hwalk : Relation.ReflTransGen (openGraph ω).Adj v w :=
      mem_cluster_iff_reflTransGen.mp hw
    induction hwalk with
    | refl => exact Finset.mem_coe.mpr (Finset.mem_insert_self v (edgeVertices S))
    | @tail a b _ hab ih =>
      rw [openGraph_adj] at hab
      obtain ⟨hne, hedge⟩ := hab
      refine Finset.mem_coe.mpr (Finset.mem_insert_of_mem ?_)
      exact mem_edgeVertices (h _ hedge) (Sym2.mem_mk_right a b)
  have hfin : (cluster ω v).Finite := (Finset.finite_toSet _).subset hsub
  rw [clusterVol_eq_encard]
  simpa using hfin.encard_lt_top.ne

/-- A configuration contained in the finite edge set `S` has every cluster volume finite. -/
theorem clusterVol_cutConfig_ne_top (S : Finset (Sym2 V)) (ω : Config V) (v : V) :
    clusterVol (cutConfig S ω) v ≠ ⊤ :=
  clusterVol_ne_top_of_subset_finset (fun _ he => he.2) v

/-- Opening one edge can only merge two clusters: the volume of the cluster of `o` after opening
`s(x, y)` is at most the sum of the volumes of the clusters of `o`, `x` and `y` before. -/
theorem clusterVol_union_pair_le (ω : Config V) (o x y : V) :
    clusterVol (ω ∪ {s(x, y)}) o ≤ clusterVol ω o + clusterVol ω x + clusterVol ω y := by
  classical
  have hsub := cluster_union_singleton_subset_three (o := o) (x := x) (y := y) (ω := ω)
  have hpt : ∀ v : V,
      (cluster (ω ∪ {s(x, y)}) o).indicator (fun _ => (1 : ℝ≥0∞)) v
        ≤ (cluster ω o).indicator (fun _ => (1 : ℝ≥0∞)) v
          + (cluster ω x).indicator (fun _ => (1 : ℝ≥0∞)) v
          + (cluster ω y).indicator (fun _ => (1 : ℝ≥0∞)) v := by
    intro v
    by_cases hv : v ∈ cluster (ω ∪ {s(x, y)}) o
    · rw [Set.indicator_of_mem hv]
      rcases hsub hv with (h | h) | h
      · rw [Set.indicator_of_mem h]
        exact le_trans le_self_add le_self_add
      · rw [Set.indicator_of_mem h]
        exact le_trans le_add_self le_self_add
      · rw [Set.indicator_of_mem h]
        exact le_add_self
    · rw [Set.indicator_of_notMem hv]
      exact zero_le
  calc clusterVol (ω ∪ {s(x, y)}) o
      = ∑' v : V, (cluster (ω ∪ {s(x, y)}) o).indicator (fun _ => (1 : ℝ≥0∞)) v :=
        clusterVol_eq_tsum _ _
    _ ≤ ∑' v : V, ((cluster ω o).indicator (fun _ => (1 : ℝ≥0∞)) v
          + (cluster ω x).indicator (fun _ => (1 : ℝ≥0∞)) v
          + (cluster ω y).indicator (fun _ => (1 : ℝ≥0∞)) v) := ENNReal.tsum_le_tsum hpt
    _ = clusterVol ω o + clusterVol ω x + clusterVol ω y := by
        rw [ENNReal.tsum_add, ENNReal.tsum_add, clusterVol_eq_tsum, clusterVol_eq_tsum,
          clusterVol_eq_tsum]

end PercLib.CriticalLRP

namespace PercLib.CriticalLRP.Orchestration

namespace SourceModelData

variable (M : SourceModelData)

/-! ## 1. The windowed square: application, monotonicity, nonnegativity -/

/-- The windowed square, applied: it is the square of the cluster volume of the origin in the
windowed configuration. -/
theorem cutFun_clusterVolSqReal_apply (S : Finset (Sym2 M.V)) (ω : Config M.V) :
    cutFun S M.clusterVolSqReal ω = (clusterVol (cutConfig S ω) (0 : M.V)).toReal ^ 2 := rfl

/-- The windowed square is monotone in the configuration. -/
theorem cutFun_clusterVolSqReal_mono (S : Finset (Sym2 M.V)) {ω ω' : Config M.V}
    (h : ∀ e : Sym2 M.V, e ∈ ω → e ∈ ω') :
    cutFun S M.clusterVolSqReal ω ≤ cutFun S M.clusterVolSqReal ω' := by
  have hle : clusterVol (cutConfig S ω) (0 : M.V) ≤ clusterVol (cutConfig S ω') (0 : M.V) :=
    clusterVol_mono (fun e he => And.intro (h e he.1) he.2) (0 : M.V)
  rw [M.cutFun_clusterVolSqReal_apply, M.cutFun_clusterVolSqReal_apply]
  exact pow_le_pow_left₀ (ENNReal.toReal_nonneg)
    (ENNReal.toReal_mono (clusterVol_cutConfig_ne_top S ω' (0 : M.V)) hle) 2

/-- **The flip difference of the windowed square is nonnegative.** -/
theorem flipDiff_cutFun_clusterVolSqReal_nonneg (S : Finset (Sym2 M.V)) (e : Sym2 M.V)
    (ω : Config M.V) : 0 ≤ flipDiff (cutFun S M.clusterVolSqReal) e ω := by
  have hsub : ∀ a : Sym2 M.V, a ∈ forceOn {e} (∅ : Config M.V) ω →
      a ∈ forceOn {e} ({e} : Config M.V) ω := by
    rw [forceOn_singleton_closed_eq, forceOn_singleton_open_eq]
    exact Set.sdiff_subset.trans Set.subset_union_left
  have hmono := M.cutFun_clusterVolSqReal_mono S hsub
  rw [flipDiff]
  exact sub_nonneg.mpr hmono

/-- **The windowed pivotal flux is nonnegative**: it is the mean of the nonnegative flip
difference of the windowed square. -/
theorem pivotalFlux_cutFun_clusterVolSqReal_nonneg (S : Finset (Sym2 M.V)) (r : ℝ)
    (e : Sym2 M.V) : 0 ≤ pivotalFlux (M.cutLaw r) (cutFun S M.clusterVolSqReal) e := by
  rw [pivotalFlux]
  exact integral_nonneg fun ω => M.flipDiff_cutFun_clusterVolSqReal_nonneg S e ω

/-- **The untruncated pivotal flux of the square is nonnegative.**  On the almost-sure set where
every cluster volume is finite (`ae_clusterVol_ne_top`, from the source's first cutoff moment) the
flip difference of `|K₀|²` is a difference of two finite squares and hence nonnegative; nowhere
else is anything claimed. -/
theorem pivotalFlux_clusterVolSqReal_nonneg (r : ℝ) (h1 : M.cutMassAt r (0 : M.V) ≠ ⊤)
    (e : Sym2 M.V) : 0 ≤ pivotalFlux (M.cutLaw r) M.clusterVolSqReal e := by
  rw [pivotalFlux]
  refine integral_nonneg_of_ae ?_
  induction e using Sym2.ind with
  | h x y =>
    filter_upwards [PivotFlux.ae_clusterVol_ne_top M r h1] with ω hω
    have hK : ∀ v : M.V, clusterVol ω v ≠ ⊤ := hω
    have hfinA : clusterVol (forceOn {s(x, y)} ({s(x, y)} : Config M.V) ω) (0 : M.V) ≠ ⊤ := by
      rw [forceOn_singleton_open_eq]
      refine ne_top_of_le_ne_top ?_ (clusterVol_union_pair_le ω (0 : M.V) x y)
      exact ENNReal.add_ne_top.mpr
        ⟨ENNReal.add_ne_top.mpr ⟨hK 0, hK x⟩, hK y⟩
    have hmono : clusterVol (forceOn {s(x, y)} (∅ : Config M.V) ω) (0 : M.V)
        ≤ clusterVol (forceOn {s(x, y)} ({s(x, y)} : Config M.V) ω) (0 : M.V) := by
      rw [forceOn_singleton_closed_eq, forceOn_singleton_open_eq]
      exact clusterVol_mono (fun a ha => Set.mem_union_left _ (Set.mem_of_mem_sdiff ha)) 0
    have hkey := ENNReal.toReal_mono hfinA hmono
    change 0 ≤ (clusterVol (forceOn {s(x, y)} ({s(x, y)} : Config M.V) ω) (0 : M.V)).toReal ^ 2
      - (clusterVol (forceOn {s(x, y)} (∅ : Config M.V) ω) (0 : M.V)).toReal ^ 2
    exact sub_nonneg.mpr (pow_le_pow_left₀ (ENNReal.toReal_nonneg) hkey 2)

end SourceModelData

end PercLib.CriticalLRP.Orchestration

namespace PercLib.CriticalLRP

/-! ## 2. The fixed-radius exhaustion half -/

/-- A finite set is contained in some member of a monotone exhausting family of finite sets. -/
theorem exists_finset_subset_of_monotone_exhaust {ι : Type*} (S : ℕ → Finset ι)
    (hSmono : Monotone S) (hSexh : ∀ e : ι, ∃ n, e ∈ S n) (t : Finset ι) :
    ∃ n, t ⊆ S n := by
  classical
  choose N hN using hSexh
  exact ⟨t.sup N, fun e he => hSmono (Finset.le_sup (f := N) he) (hN e)⟩

/-- **Monotone exhaustive finset sums in `ℝ≥0∞` converge to the `tsum`.** -/
theorem tendsto_sum_finset_of_monotone_exhaust {ι : Type*} [Countable ι]
    (S : ℕ → Finset ι) (hSmono : Monotone S) (hSexh : ∀ e : ι, ∃ n, e ∈ S n)
    (F : ι → ℝ≥0∞) : Tendsto (fun n => ∑ e ∈ S n, F e) atTop (𝓝 (∑' e, F e)) := by
  have hmono : Monotone fun n => ∑ e ∈ S n, F e := fun m n hmn =>
    Finset.sum_le_sum_of_subset_of_nonneg (hSmono hmn) fun i _ _ => zero_le
  have hsup : (⨆ n, ∑ e ∈ S n, F e) = ∑' e, F e := by
    refine le_antisymm (iSup_le fun n => ENNReal.sum_le_tsum (S n)) ?_
    rw [ENNReal.tsum_eq_iSup_sum]
    refine iSup_le fun t => ?_
    obtain ⟨n, hn⟩ := exists_finset_subset_of_monotone_exhaust S hSmono hSexh t
    exact le_iSup_of_le n (Finset.sum_le_sum_of_subset_of_nonneg hn fun i _ _ => zero_le)
  rw [← hsup]
  exact tendsto_atTop_iSup hmono

end PercLib.CriticalLRP

namespace PercLib.CriticalLRP.Orchestration

namespace SourceModelData

variable (M : SourceModelData)

/-! ## 3. The finite-window per-edge closed ghost identity -/

/-- Inside the window, deleting an edge commutes with taking the windowed configuration. -/
theorem cutConfig_sdiff_singleton (S : Finset (Sym2 M.V)) (e : Sym2 M.V)
    (ω : Config M.V) : cutConfig S (ω \ {e}) = cutConfig S ω \ {e} := by
  ext a
  simp only [cutConfig, Set.mem_inter_iff, Set.mem_sdiff, Set.mem_singleton_iff]
  tauto

/-- The window closed ghost, with the range predicate written out. -/
theorem windowClosedGhost_apply (S : Finset (Sym2 M.V)) (r : ℝ) (e : Sym2 M.V) :
    M.windowClosedGhost S r e
      = ∫ ω, (quadEdgeWeight (fun c b : M.V => M.S.dist c b ≤ r) (cutConfig S ω)
          (0 : M.V) e).toReal ∂(M.cutLaw r) := rfl

/-- **The pointwise single-edge increment of the windowed square.**  For a genuine edge of the
window, the flip difference of the windowed square is the real closed ghost edge weight at the
closed windowed configuration.  No moment hypothesis: every cluster volume of a windowed
configuration is finite, so the landed untruncated identity
`flipDiff_clusterVol_sq_eq_quadEdgeWeight_sdiff` applies at the closed windowed configuration. -/
theorem flipDiff_cutFun_clusterVolSqReal_eq (S : Finset (Sym2 M.V)) (r : ℝ) {x y : M.V}
    (hxy : x ≠ y) (hdist : M.S.dist x y ≤ r) (he : s(x, y) ∈ S) (ω : Config M.V) :
    flipDiff (cutFun S M.clusterVolSqReal) s(x, y) ω
      = (quadEdgeWeight (fun c b : M.V => M.S.dist c b ≤ r)
          (cutConfig S (ω \ {s(x, y)})) (0 : M.V) s(x, y)).toReal := by
  classical
  have hnotmem : s(x, y) ∉ cutConfig S (ω \ {s(x, y)}) := fun hh => hh.1.2 rfl
  have hfin : ∀ v : M.V, clusterVol (cutConfig S (ω \ {s(x, y)})) v ≠ ⊤ :=
    fun v => clusterVol_ne_top_of_subset_finset (fun _ ha => ha.2) v
  have hcfg : cutConfig S (ω \ {s(x, y)}) ∪ {s(x, y)} = cutConfig S ω ∪ {s(x, y)} := by
    rw [M.cutConfig_sdiff_singleton S s(x, y) ω, sdiff_singleton_union]
  have hL : cutFun S M.clusterVolSqReal (forceOn {s(x, y)} ({s(x, y)} : Config M.V) ω)
      = (clusterVol (forceOn {s(x, y)} ({s(x, y)} : Config M.V)
          (cutConfig S (ω \ {s(x, y)}))) (0 : M.V)).toReal ^ 2 := by
    rw [cutFun, cutConfig_forceOn_of_mem S he, forceOn_singleton_open_eq,
      SourceModelData.clusterVolSqReal_apply, forceOn_singleton_open_eq, hcfg]
  have hR : cutFun S M.clusterVolSqReal (forceOn {s(x, y)} (∅ : Config M.V) ω)
      = (clusterVol (forceOn {s(x, y)} (∅ : Config M.V)
          (cutConfig S (ω \ {s(x, y)}))) (0 : M.V)).toReal ^ 2 := by
    rw [cutFun, cutConfig_forceOn_of_mem S he, forceOn_singleton_closed_eq,
      SourceModelData.clusterVolSqReal_apply, forceOn_singleton_closed_eq,
      M.cutConfig_sdiff_singleton S s(x, y) ω, sdiff_singleton_idem]
  have hlanded := flipDiff_clusterVol_sq_eq_quadEdgeWeight_sdiff M r hxy hdist hfin
  rw [flipDiff] at hlanded
  rw [flipDiff, hL, hR, hlanded, sdiff_singleton_of_notMem hnotmem]

/-- The closed-edge weight is nonnegative. -/
theorem cutEdgeClosedWeight_nonneg (r : ℝ) (e : Sym2 M.V) :
    0 ≤ M.cutEdgeClosedWeight r e := by
  induction e using Sym2.ind with
  | h x y =>
    rw [M.cutEdgeClosedWeight_mk r x y]
    split_ifs <;> positivity

/-- **The finite-window per-edge closed ghost identity.**  For every edge `e` of the window, the
source's closed-edge weight times the windowed pivotal flux is the mean of the exact nonnegative
`ℝ≥0∞` quadratic edge weight at the windowed configuration.  This is the windowed counterpart of
the landed `cutEdgeClosedWeight_mul_pivotalFlux_eq`, with the `(1 - q_e)` closed-coordinate
factorization applied to a genuinely bounded observable. -/
theorem cutEdgeClosedWeight_mul_pivotalFlux_cutFun_eq (S : Finset (Sym2 M.V)) (r : ℝ)
    (e : Sym2 M.V) (he : e ∈ S) :
    M.cutEdgeClosedWeight r e * pivotalFlux (M.cutLaw r) (cutFun S M.clusterVolSqReal) e
      = M.windowClosedGhost S r e := by
  classical
  induction e using Sym2.ind with
  | h x y =>
    by_cases hxy : x = y
    · subst hxy
      rw [M.cutEdgeClosedWeight_loop, zero_mul, M.windowClosedGhost_apply]
      have hzero : (fun ω : Config M.V => (quadEdgeWeight (fun c b : M.V => M.S.dist c b ≤ r)
          (cutConfig S ω) (0 : M.V) s(x, x)).toReal) = fun _ => (0 : ℝ) := by
        funext ω
        rw [quadEdgeWeight_diag, ENNReal.toReal_zero]
      rw [hzero]
      simp
    · by_cases hdist : M.S.dist x y ≤ r
      · have hpiv : pivotalFlux (M.cutLaw r) (cutFun S M.clusterVolSqReal) s(x, y)
            = ∫ ω, (quadEdgeWeight (fun c b : M.V => M.S.dist c b ≤ r)
                (cutConfig S (ω \ {s(x, y)})) (0 : M.V) s(x, y)).toReal ∂(M.cutLaw r) := by
          rw [pivotalFlux]
          exact integral_congr_ae (Filter.Eventually.of_forall fun ω =>
            M.flipDiff_cutFun_clusterVolSqReal_eq S r hxy hdist he ω)
        rw [M.cutEdgeClosedWeight_eq_one_sub_cutProb hxy hdist, hpiv,
          M.windowClosedGhost_apply]
        set G : Config M.V → ℝ := fun ω => (quadEdgeWeight (fun c b : M.V => M.S.dist c b ≤ r)
          (cutConfig S (ω \ {s(x, y)})) (0 : M.V) s(x, y)).toReal with hGdef
        have hGmeas : Measurable G := by
          rw [hGdef]
          exact ENNReal.measurable_toReal.comp
            ((measurable_quadEdgeWeight (fun c b : M.V => M.S.dist c b ≤ r) (0 : M.V)
                s(x, y)).comp ((measurable_cutConfig S).comp
                  (PercLib.Probability.measurable_diff_singleton s(x, y))))
        have hGdet : ∀ ω : Config M.V, G ω = G (ω \ {s(x, y)}) := by
          intro ω
          simp only [hGdef]
          rw [sdiff_singleton_idem]
        have hGnn : ∀ ω : Config M.V, 0 ≤ G ω := fun ω => ENNReal.toReal_nonneg
        have hfac := integral_compl_indicator_mul_of_sdiff_determined (M.cutProb r) s(x, y)
          hGmeas hGdet hGnn
        have hfacM : ∫ ω, (if s(x, y) ∈ ω then (0 : ℝ) else G ω) ∂(M.cutLaw r)
            = (1 - ((M.cutProb r s(x, y) : unitInterval) : ℝ)) * ∫ ω, G ω ∂(M.cutLaw r) := by
          rw [M.cutLaw_eq_edgeMeasure]
          exact hfac
        have hdrop : ∫ ω, (if s(x, y) ∈ ω then (0 : ℝ) else G ω) ∂(M.cutLaw r)
            = ∫ ω, (quadEdgeWeight (fun c b : M.V => M.S.dist c b ≤ r) (cutConfig S ω)
                (0 : M.V) s(x, y)).toReal ∂(M.cutLaw r) := by
          refine integral_congr_ae (Filter.Eventually.of_forall fun ω => ?_)
          change (if s(x, y) ∈ ω then (0 : ℝ) else G ω)
            = (quadEdgeWeight (fun c b : M.V => M.S.dist c b ≤ r) (cutConfig S ω)
                (0 : M.V) s(x, y)).toReal
          by_cases h : s(x, y) ∈ ω
          · have hconn : Connects (cutConfig S ω) x y :=
              SimpleGraph.Adj.reachable ((openGraph_adj (ω := cutConfig S ω)).2 ⟨hxy, ⟨h, he⟩⟩)
            have hz : quadEdgeWeight (fun c b : M.V => M.S.dist c b ≤ r) (cutConfig S ω)
                (0 : M.V) s(x, y) = 0 := by
              rw [quadEdgeWeight_mk, quadPairWeight_eq_zero_of_connects _ _ _ hconn,
                quadPairWeight_eq_zero_of_connects _ _ _ (connects_symm hconn), add_zero]
            rw [ite_eq_left h, hz, ENNReal.toReal_zero]
          · have hnot : s(x, y) ∉ cutConfig S ω := fun hc => h hc.1
            rw [ite_eq_right h]
            simp only [hGdef, M.cutConfig_sdiff_singleton S s(x, y) ω,
              sdiff_singleton_of_notMem hnot]
        rw [← hfacM, hdrop]
      · have hgt : r < M.S.dist x y := not_le.mp hdist
        rw [M.cutEdgeClosedWeight_eq_zero_of_dist_gt hgt, zero_mul, M.windowClosedGhost_apply]
        have hzero : (fun ω : Config M.V => (quadEdgeWeight (fun c b : M.V => M.S.dist c b ≤ r)
            (cutConfig S ω) (0 : M.V) s(x, y)).toReal) = fun _ => (0 : ℝ) := by
          funext ω
          rw [quadEdgeWeight_mk]
          have h1 : ¬ (fun c b : M.V => M.S.dist c b ≤ r) y x := by
            simp only
            rw [M.S.dist_comm]
            exact hdist
          have h2 : ¬ (fun c b : M.V => M.S.dist c b ≤ r) x y := hdist
          rw [quadPairWeight, quadPairWeight, ite_eq_right h1, ite_eq_right h2]
          simp
        rw [hzero]
        simp

/-- The radius-only coefficient `β_c (-K'(r))` is nonnegative at positive radius. -/
theorem coeffRHS_nonneg {r : ℝ} (hr : 0 < r) : 0 ≤ M.coeffRHS r := by
  change 0 ≤ (M.betaCrit : ℝ) * (-(deriv M.K r))
  exact mul_nonneg (NNReal.coe_nonneg _) (M.neg_deriv_K_nonneg hr)

/-- The accepted `p = 2` right-hand side is nonnegative at positive radius. -/
theorem rhsScalarTwo_nonneg {r : ℝ} (hr : 0 < r) : 0 ≤ M.rhsScalarTwo r :=
  mul_nonneg (M.coeffRHS_nonneg hr) ENNReal.toReal_nonneg

/-- The `ℝ≥0∞` total of the coefficient-weighted **untruncated** pivotal fluxes is finite: it is
the `coeffRHS`-multiple of the `p = 2` mass `M.p2RHS r`, through the landed per-edge closed ghost
identity. -/
theorem tsum_ofReal_cutEdgeDeriv_mul_pivotalFlux_ne_top {r : ℝ} (hr : 0 < r)
    (h1 : M.cutMassAt r (0 : M.V) ≠ ⊤) (hp2 : M.p2RHS r ≠ ⊤) :
    ∑' e : Sym2 M.V, ENNReal.ofReal (M.cutEdgeDeriv r e *
      pivotalFlux (M.cutLaw r) M.clusterVolSqReal e) ≠ ⊤ := by
  have hper : ∀ e : Sym2 M.V, ENNReal.ofReal (M.cutEdgeClosedWeight r e *
      pivotalFlux (M.cutLaw r) M.clusterVolSqReal e)
      = ∫⁻ ω, quadEdgeWeight (fun c b : M.V => M.S.dist c b ≤ r) ω (0 : M.V) e
          ∂(M.cutLaw r) := by
    intro e
    have hg : M.clusterVolSqReal = fun ω : Config M.V => (clusterVol ω (0 : M.V)).toReal ^ 2 :=
      funext fun ω => M.clusterVolSqReal_apply ω
    rw [hg, M.cutEdgeClosedWeight_mul_pivotalFlux_eq r h1 e,
      M.integral_toReal_quadEdgeWeight r h1 e,
      ENNReal.ofReal_toReal (M.lintegral_quadEdgeWeight_ne_top r h1 hp2 e)]
  have hsumClosed : ∑' e : Sym2 M.V, ENNReal.ofReal (M.cutEdgeClosedWeight r e *
      pivotalFlux (M.cutLaw r) M.clusterVolSqReal e) = M.p2RHS r := by
    rw [tsum_congr hper, ← MeasureTheory.lintegral_tsum
      (fun e => (measurable_quadEdgeWeight (fun c b : M.V => M.S.dist c b ≤ r)
        (0 : M.V) e).aemeasurable)]
    exact lintegral_tsum_quadEdgeWeight_eq_p2RHS M r h1
  have hpt : ∀ e : Sym2 M.V, ENNReal.ofReal (M.cutEdgeDeriv r e *
      pivotalFlux (M.cutLaw r) M.clusterVolSqReal e)
      = ENNReal.ofReal (M.coeffRHS r) * ENNReal.ofReal (M.cutEdgeClosedWeight r e *
          pivotalFlux (M.cutLaw r) M.clusterVolSqReal e) := by
    intro e
    rw [← ENNReal.ofReal_mul (M.coeffRHS_nonneg hr), ← mul_assoc,
      ← M.cutEdgeDeriv_eq_coeffRHS_mul r e]
  calc ∑' e : Sym2 M.V, ENNReal.ofReal (M.cutEdgeDeriv r e *
        pivotalFlux (M.cutLaw r) M.clusterVolSqReal e)
      = ∑' e : Sym2 M.V, ENNReal.ofReal (M.coeffRHS r) *
          ENNReal.ofReal (M.cutEdgeClosedWeight r e *
            pivotalFlux (M.cutLaw r) M.clusterVolSqReal e) := tsum_congr hpt
    _ = ENNReal.ofReal (M.coeffRHS r) * ∑' e : Sym2 M.V,
          ENNReal.ofReal (M.cutEdgeClosedWeight r e *
            pivotalFlux (M.cutLaw r) M.clusterVolSqReal e) := ENNReal.tsum_mul_left
    _ = ENNReal.ofReal (M.coeffRHS r) * M.p2RHS r := by rw [hsumClosed]
    _ ≠ ⊤ := ENNReal.mul_ne_top ENNReal.ofReal_ne_top hp2

/-- The closed-edge weights against the untruncated pivotal fluxes are summable, from the
finiteness of the `p = 2` mass. -/
theorem summable_cutEdgeClosedWeight_mul_pivotalFlux {r : ℝ}
    (h1 : M.cutMassAt r (0 : M.V) ≠ ⊤) (hp2 : M.p2RHS r ≠ ⊤) :
    Summable fun e : Sym2 M.V => M.cutEdgeClosedWeight r e *
      pivotalFlux (M.cutLaw r) M.clusterVolSqReal e := by
  have hnn : ∀ e : Sym2 M.V, 0 ≤ M.cutEdgeClosedWeight r e *
      pivotalFlux (M.cutLaw r) M.clusterVolSqReal e := fun e =>
    mul_nonneg (M.cutEdgeClosedWeight_nonneg r e)
      (M.pivotalFlux_clusterVolSqReal_nonneg r h1 e)
  refine summable_of_sum_le (c := (M.p2RHS r).toReal) hnn fun u => ?_
  have hper : ∀ e : Sym2 M.V, ENNReal.ofReal (M.cutEdgeClosedWeight r e *
      pivotalFlux (M.cutLaw r) M.clusterVolSqReal e)
      = ∫⁻ ω, quadEdgeWeight (fun c b : M.V => M.S.dist c b ≤ r) ω (0 : M.V) e
          ∂(M.cutLaw r) := by
    intro e
    have hg : M.clusterVolSqReal = fun ω : Config M.V => (clusterVol ω (0 : M.V)).toReal ^ 2 :=
      funext fun ω => M.clusterVolSqReal_apply ω
    rw [hg, M.cutEdgeClosedWeight_mul_pivotalFlux_eq r h1 e,
      M.integral_toReal_quadEdgeWeight r h1 e,
      ENNReal.ofReal_toReal (M.lintegral_quadEdgeWeight_ne_top r h1 hp2 e)]
  have hsumClosed : ∑' e : Sym2 M.V, ENNReal.ofReal (M.cutEdgeClosedWeight r e *
      pivotalFlux (M.cutLaw r) M.clusterVolSqReal e) = M.p2RHS r := by
    rw [tsum_congr hper, ← MeasureTheory.lintegral_tsum
      (fun e => (measurable_quadEdgeWeight (fun c b : M.V => M.S.dist c b ≤ r)
        (0 : M.V) e).aemeasurable)]
    exact lintegral_tsum_quadEdgeWeight_eq_p2RHS M r h1
  have hle : ∑ e ∈ u, ENNReal.ofReal (M.cutEdgeClosedWeight r e *
      pivotalFlux (M.cutLaw r) M.clusterVolSqReal e) ≤ M.p2RHS r := by
    rw [← hsumClosed]
    exact ENNReal.sum_le_tsum u
  have hto := ENNReal.toReal_mono hp2 hle
  rw [ENNReal.toReal_sum (fun e _ => ENNReal.ofReal_ne_top)] at hto
  rwa [Finset.sum_congr rfl fun e _ => ENNReal.toReal_ofReal (hnn e)] at hto

/-- The coefficient-weighted untruncated pivotal fluxes are summable at positive radius. -/
theorem summable_cutEdgeDeriv_mul_pivotalFlux {r : ℝ}
    (h1 : M.cutMassAt r (0 : M.V) ≠ ⊤) (hp2 : M.p2RHS r ≠ ⊤) :
    Summable fun e : Sym2 M.V => M.cutEdgeDeriv r e *
      pivotalFlux (M.cutLaw r) M.clusterVolSqReal e := by
  have h := (M.summable_cutEdgeClosedWeight_mul_pivotalFlux h1 hp2).mul_left (M.coeffRHS r)
  simpa only [M.cutEdgeDeriv_eq_coeffRHS_mul, mul_assoc] using h

/-- **The exhaustion half of the fixed-radius window convergence.**  Along a monotone exhausting
family of finite windows, the truncated infinite pivotal sums converge to the accepted right-hand
side, by monotone convergence of `ℝ≥0∞` finset sums and the landed fixed-radius FLUX identity
`tsum_cutEdgeDeriv_mul_pivotalFlux_eq_rhsScalarTwo`.  No `⊤ ↦ 0` step is used: the `ℝ≥0∞` total is
*proved* finite by the closed ghost factorization above. -/
theorem tendsto_partialLimitFlux (r : ℝ) (hr : 0 < r) (S : ℕ → Finset (Sym2 M.V))
    (hSmono : Monotone S) (hSexh : ∀ e : Sym2 M.V, ∃ n, e ∈ S n)
    (h1 : M.cutMassAt r (0 : M.V) ≠ ⊤) (hp2 : M.p2RHS r ≠ ⊤) :
    Tendsto (fun n => M.partialLimitFlux (S n) r) atTop (𝓝 (M.rhsScalarTwo r)) := by
  classical
  have hc : ∀ e : Sym2 M.V, 0 ≤ M.cutEdgeDeriv r e :=
    fun e => M.cutEdgeDeriv_nonneg (M.neg_deriv_K_nonneg hr) e
  have hp : ∀ e : Sym2 M.V, 0 ≤ pivotalFlux (M.cutLaw r) M.clusterVolSqReal e :=
    fun e => M.pivotalFlux_clusterVolSqReal_nonneg r h1 e
  have hnn : ∀ e : Sym2 M.V, 0 ≤ M.cutEdgeDeriv r e *
      pivotalFlux (M.cutLaw r) M.clusterVolSqReal e := fun e => mul_nonneg (hc e) (hp e)
  have hTot := M.tsum_ofReal_cutEdgeDeriv_mul_pivotalFlux_ne_top hr h1 hp2
  have hsumm := M.summable_cutEdgeDeriv_mul_pivotalFlux h1 hp2
  have hg : M.clusterVolSqReal
      = fun ω : Config M.V => (clusterVol ω (0 : M.V)).toReal ^ 2 :=
    funext fun ω => M.clusterVolSqReal_apply ω
  have hident : (∑' e : Sym2 M.V, ENNReal.ofReal (M.cutEdgeDeriv r e *
      pivotalFlux (M.cutLaw r) M.clusterVolSqReal e)).toReal = M.rhsScalarTwo r := by
    have hnn' : ∀ e : Sym2 M.V, 0 ≤ M.cutEdgeDeriv r e *
        pivotalFlux (M.cutLaw r) (fun ω => (clusterVol ω (0 : M.V)).toReal ^ 2) e :=
      fun e => mul_nonneg (hc e) (hp e)
    have hsumm' : Summable fun e : Sym2 M.V => M.cutEdgeDeriv r e *
        pivotalFlux (M.cutLaw r) (fun ω => (clusterVol ω (0 : M.V)).toReal ^ 2) e := by
      simpa only [hg] using hsumm
    have hkey : (∑' e : Sym2 M.V, ENNReal.ofReal (M.cutEdgeDeriv r e *
        pivotalFlux (M.cutLaw r) (fun ω => (clusterVol ω (0 : M.V)).toReal ^ 2) e)).toReal
        = M.rhsScalarTwo r := by
      rw [← ENNReal.ofReal_tsum_of_nonneg hnn' hsumm',
        M.tsum_cutEdgeDeriv_mul_pivotalFlux_eq_rhsScalarTwo r h1 hp2,
        ENNReal.toReal_ofReal (M.rhsScalarTwo_nonneg hr)]
    simpa only [hg] using hkey
  have hexh := tendsto_sum_finset_of_monotone_exhaust S hSmono hSexh
    (fun e => ENNReal.ofReal (M.cutEdgeDeriv r e *
      pivotalFlux (M.cutLaw r) M.clusterVolSqReal e))
  have hreal : Tendsto (fun n => (∑ e ∈ S n, ENNReal.ofReal (M.cutEdgeDeriv r e *
      pivotalFlux (M.cutLaw r) M.clusterVolSqReal e)).toReal) atTop
      (𝓝 ((∑' e : Sym2 M.V, ENNReal.ofReal (M.cutEdgeDeriv r e *
        pivotalFlux (M.cutLaw r) M.clusterVolSqReal e)).toReal)) :=
    (ENNReal.tendsto_toReal hTot).comp hexh
  have hgoal : Tendsto (fun n => (∑ e ∈ S n, ENNReal.ofReal (M.cutEdgeDeriv r e *
      pivotalFlux (M.cutLaw r) M.clusterVolSqReal e)).toReal) atTop (𝓝 (M.rhsScalarTwo r)) := by
    simpa only [hident] using hreal
  have hpt : ∀ n : ℕ, (∑ e ∈ S n, ENNReal.ofReal (M.cutEdgeDeriv r e *
      pivotalFlux (M.cutLaw r) M.clusterVolSqReal e)).toReal
      = M.partialLimitFlux (S n) r := by
    intro n
    rw [ENNReal.toReal_sum (fun e _ => ENNReal.ofReal_ne_top), SourceModelData.partialLimitFlux]
    exact Finset.sum_congr rfl fun e _ => ENNReal.toReal_ofReal (hnn e)
  simpa only [hpt] using hgoal

/-! ## 4. The insertion split of the window flux -/

/-- **The exact split of the window flux** into the truncated infinite pivotal sum and the
insertion deficit. -/
theorem windowFlux_eq_partialLimitFlux_sub_insertionDeficit (S : Finset (Sym2 M.V)) (r : ℝ) :
    M.windowFlux S r = M.partialLimitFlux S r - M.insertionDeficit S r := by
  rw [SourceModelData.windowFlux, SourceModelData.partialLimitFlux,
    SourceModelData.insertionDeficit, ← Finset.sum_sub_distrib]
  exact Finset.sum_congr rfl fun e _ => by ring

/-- The insertion error dominates the absolute value of the insertion deficit. -/
theorem abs_insertionDeficit_le_insertionError (S : Finset (Sym2 M.V)) (r : ℝ) :
    |M.insertionDeficit S r| ≤ M.insertionError S r := by
  rw [SourceModelData.insertionDeficit, SourceModelData.insertionError]
  refine (Finset.abs_sum_le_sum_abs _ _).trans (Finset.sum_le_sum fun e _ => ?_)
  rw [abs_mul]
  exact le_of_eq (by rw [abs_sub_comm])

/-- **`hfluxConv` from the vanishing insertion deficit.** -/
theorem tendsto_windowFlux_of_insertionDeficit (r : ℝ) (hr : 0 < r)
    (S : ℕ → Finset (Sym2 M.V)) (hSmono : Monotone S)
    (hSexh : ∀ e : Sym2 M.V, ∃ n, e ∈ S n)
    (h1 : M.cutMassAt r (0 : M.V) ≠ ⊤) (hp2 : M.p2RHS r ≠ ⊤)
    (hIns : Tendsto (fun n => M.insertionDeficit (S n) r) atTop (𝓝 0)) :
    Tendsto (fun n => M.windowFlux (S n) r) atTop (𝓝 (M.rhsScalarTwo r)) := by
  have h := (M.tendsto_partialLimitFlux r hr S hSmono hSexh h1 hp2).sub hIns
  have h' : Tendsto (fun n => M.partialLimitFlux (S n) r - M.insertionDeficit (S n) r)
      atTop (𝓝 (M.rhsScalarTwo r - 0)) := h
  simpa only [sub_zero, M.windowFlux_eq_partialLimitFlux_sub_insertionDeficit] using h'

/-- **`hfluxConv` from the vanishing insertion error.**  This is the form in which the paper's
insertion tolerance (`SecondMomentExchange.insertionFlux`) is consumed. -/
theorem tendsto_windowFlux_of_insertionError (r : ℝ) (hr : 0 < r)
    (S : ℕ → Finset (Sym2 M.V)) (hSmono : Monotone S)
    (hSexh : ∀ e : Sym2 M.V, ∃ n, e ∈ S n)
    (h1 : M.cutMassAt r (0 : M.V) ≠ ⊤) (hp2 : M.p2RHS r ≠ ⊤)
    (hErr : Tendsto (fun n => M.insertionError (S n) r) atTop (𝓝 0)) :
    Tendsto (fun n => M.windowFlux (S n) r) atTop (𝓝 (M.rhsScalarTwo r)) := by
  refine M.tendsto_windowFlux_of_insertionDeficit r hr S hSmono hSexh h1 hp2 ?_
  exact squeeze_zero_norm (fun n => M.abs_insertionDeficit_le_insertionError (S n) r) hErr

/-- **`hfluxConv` is exactly the vanishing of the insertion deficit**, given the exhaustion half
(which is unconditional).  Nothing is hidden: the right-hand side is a statement about the
*differences* of the windowed and untruncated per-edge pivotal fluxes, summed against the source's
coefficients, not a restatement of the convergence of the window flux. -/
theorem tendsto_windowFlux_iff (r : ℝ) (hr : 0 < r) (S : ℕ → Finset (Sym2 M.V))
    (hSmono : Monotone S) (hSexh : ∀ e : Sym2 M.V, ∃ n, e ∈ S n)
    (h1 : M.cutMassAt r (0 : M.V) ≠ ⊤) (hp2 : M.p2RHS r ≠ ⊤) :
    Tendsto (fun n => M.windowFlux (S n) r) atTop (𝓝 (M.rhsScalarTwo r)) ↔
      Tendsto (fun n => M.insertionDeficit (S n) r) atTop (𝓝 0) := by
  constructor
  · intro hW
    have hfun : (fun n => M.insertionDeficit (S n) r)
        = fun n => M.partialLimitFlux (S n) r - M.windowFlux (S n) r := by
      funext n
      have h := M.windowFlux_eq_partialLimitFlux_sub_insertionDeficit (S n) r
      linarith
    rw [hfun]
    simpa only [sub_self] using (M.tendsto_partialLimitFlux r hr S hSmono hSexh h1 hp2).sub hW
  · exact M.tendsto_windowFlux_of_insertionDeficit r hr S hSmono hSexh h1 hp2

end SourceModelData

end PercLib.CriticalLRP.Orchestration

end

/-! ## Axiom audit -/

namespace PercLib.CriticalLRP

#print axioms clusterVol_ne_top_of_subset_finset
#print axioms clusterVol_cutConfig_ne_top
#print axioms clusterVol_union_pair_le
#print axioms exists_finset_subset_of_monotone_exhaust
#print axioms tendsto_sum_finset_of_monotone_exhaust

end PercLib.CriticalLRP

namespace PercLib.CriticalLRP.Orchestration.SourceModelData

#print axioms cutFun_clusterVolSqReal_apply
#print axioms cutFun_clusterVolSqReal_mono
#print axioms flipDiff_cutFun_clusterVolSqReal_nonneg
#print axioms pivotalFlux_cutFun_clusterVolSqReal_nonneg
#print axioms pivotalFlux_clusterVolSqReal_nonneg
#print axioms cutConfig_sdiff_singleton
#print axioms windowClosedGhost_apply
#print axioms flipDiff_cutFun_clusterVolSqReal_eq
#print axioms cutEdgeClosedWeight_nonneg
#print axioms cutEdgeClosedWeight_mul_pivotalFlux_cutFun_eq
#print axioms coeffRHS_nonneg
#print axioms rhsScalarTwo_nonneg
#print axioms tsum_ofReal_cutEdgeDeriv_mul_pivotalFlux_ne_top
#print axioms summable_cutEdgeClosedWeight_mul_pivotalFlux
#print axioms summable_cutEdgeDeriv_mul_pivotalFlux
#print axioms tendsto_partialLimitFlux
#print axioms windowFlux_eq_partialLimitFlux_sub_insertionDeficit
#print axioms abs_insertionDeficit_le_insertionError
#print axioms tendsto_windowFlux_of_insertionDeficit
#print axioms tendsto_windowFlux_of_insertionError
#print axioms tendsto_windowFlux_iff

end PercLib.CriticalLRP.Orchestration.SourceModelData
