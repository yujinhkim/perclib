/-
Copyright (c) 2026 PercLib contributors. Released under Apache 2.0.

Swarm `smwvfwkks`, member `m1`, direction `d2`.

# The windowed closed ghost is eventually the untruncated one, configuration by configuration

This file proves the pointwise half of the insertion estimate for the fixed-radius `p = 2`
window flux.  The landed `FluxConv.Main` reduces `hfluxConv` (the convergence of the
finite-window pivotal sums `M.windowFlux (S k) r` to `M.rhsScalarTwo r`) to the vanishing of
the insertion deficit `M.insertionDeficit (S k) r`, i.e. to the per-edge difference between

* `pivotalFlux (M.cutLaw r) (cutFun S |K₀|²) e`, the pivotal flux of the **windowed** square,
  whose flip difference is the closed ghost `quadEdgeWeight (cutRange r)` at the windowed
  configuration `cutConfig S (ω \ {e})`, and
* `pivotalFlux (M.cutLaw r) |K₀|² e`, whose flip difference is the same closed ghost at
  `ω \ {e}`.

The main theorem `eventually_flipDiff_cutFun_eq` says: **at every configuration `ω` whose
cluster volumes are finite, and for every edge `e`, the two flip differences are equal as soon
as the window `S` contains `e` and contains a set of edges realising every connection used by
the untruncated flip difference.**  The threshold is configuration dependent, finite, and
explicit: it is the maximum of the finitely many finite edge sets realising the connections of
the finitely many vertices of `cluster (ω \ {e}) 0` and of `cluster (ω ∪ {e}) 0`.  Nothing here
is monotone in `S`: the closed ghost of the window can *drop*, and the statement is an
eventual equality, not a monotonicity.

Consequences recorded here:

* `eventually_quadEdgeWeight_eq`: the `ℝ≥0∞` closed ghost itself is eventually equal, which is
  the same statement one level down;
* `ae_eventually_flipDiff_cutFun_eq`: combined with the source's first cutoff moment
  (`ae_clusterVol_ne_top`) the threshold exists almost surely, simultaneously for all edges.

The remaining step to `hfluxConv` is *not* pointwise; it is the exchange of the limit with the
mean, i.e. a domination of the windowed closed ghosts along the exhausting family.  See
`Insertion.lean`.
-/
module

public import PercLib.CriticalLRP.Analysis.Cutoff.SecondMoment.FluxConv.Main
public import PercLib.CriticalLRP.Analysis.Cutoff.SecondMoment.Binomial

/-!
# Eventual agreement of windowed and untruncated closed ghosts
-/

set_option autoImplicit false
set_option linter.hashCommand false
set_option linter.style.longLine false

@[expose] public section

noncomputable section

open MeasureTheory Filter
open scoped ENNReal NNReal Topology

namespace PercLib.CriticalLRP

/-! ## 1. Connection is finitely determined -/

variable {V : Type*} [Countable V]

/-- **A connection is realised on a finite set of open edges.**  If `v` and `w` are connected
in `ω`, there is a finite edge set `s ⊆ ω` in which they are already connected (the edges of a
walk).  This is the form of `PathConnects` on which every eventual-agreement statement below
rests. -/
theorem exists_finset_subset_connects {ω : Config V} {v w : V} (h : Connects ω v w) :
    ∃ s : Finset (Sym2 V), (s : Set (Sym2 V)) ⊆ ω ∧ Connects (s : Config V) v w := by
  classical
  have h' : PathConnects ω v w := pathConnects_iff.mpr h
  obtain ⟨p, hp⟩ := h'
  exact ⟨p.edges.toFinset, fun e he => hp e (List.mem_toFinset.mp (Finset.mem_coe.mp he)),
    pathConnects_iff.mp ⟨p, fun e he => Finset.mem_coe.mpr (List.mem_toFinset.mpr he)⟩⟩

/-- Along a monotone exhausting family of finite windows, the connection of two vertices in
`cutConfig (S n) ω` eventually agrees with the connection in `ω`. -/
theorem eventually_connects_cutConfig (S : ℕ → Finset (Sym2 V)) (hSmono : Monotone S)
    (hSexh : ∀ e : Sym2 V, ∃ n, e ∈ S n) (ω : Config V) (v w : V) :
    ∀ᶠ n in atTop, (Connects (cutConfig (S n) ω) v w ↔ Connects ω v w) := by
  classical
  by_cases h : Connects ω v w
  · obtain ⟨s, hsω, hsc⟩ := exists_finset_subset_connects h
    obtain ⟨n₀, hn₀⟩ := exists_finset_subset_of_monotone_exhaust S hSmono hSexh s
    filter_upwards [eventually_ge_atTop n₀] with n hn
    refine ⟨fun _ => h, fun _ => ?_⟩
    refine connects_mono (fun e he => ?_) hsc
    exact ⟨hsω he, hn₀ (by simpa using he) |> fun hh => hSmono hn hh⟩
  · filter_upwards with n
    exact ⟨fun hc => (h (connects_mono (fun e he => he.1) hc)).elim,
      fun hc => (h hc).elim⟩

end PercLib.CriticalLRP

namespace PercLib.CriticalLRP

/-! ## 2. Cluster volumes of a windowed configuration are eventually the untruncated ones -/

variable {V : Type*} [Countable V]

/-- **The cluster volume of a vertex in the windowed configuration is eventually the
untruncated one**, at a configuration whose cluster of `v` is finite.

Finiteness of `cluster ω v` is what makes the statement pointwise: each of the finitely many
vertices of the cluster is connected to `v` through a finite set of open edges, and once the
window contains the union of those finite sets, the whole untruncated cluster is already
present in the window.  The threshold is `Finset.sup` of the finitely many thresholds of
`exists_finset_subset_of_monotone_exhaust`. -/
theorem eventually_clusterVol_cutConfig_eq (S : ℕ → Finset (Sym2 V)) (hSmono : Monotone S)
    (hSexh : ∀ e : Sym2 V, ∃ n, e ∈ S n) (ω : Config V) (v : V)
    (hfin : clusterVol ω v ≠ ⊤) :
    ∀ᶠ n in atTop, clusterVol (cutConfig (S n) ω) v = clusterVol ω v := by
  classical
  have hfinite : (cluster ω v).Finite := by
    by_contra hc
    exact hfin ((inInfiniteCluster_iff_infinite ω v).mpr hc)
  obtain ⟨t, ht⟩ := hfinite.exists_finset_coe
  have hmem : ∀ w : t, (w : V) ∈ cluster ω v := by
    intro w
    rw [← ht]
    exact Finset.mem_coe.mpr w.2
  have hwit : ∀ w : t, ∃ s : Finset (Sym2 V), (s : Set (Sym2 V)) ⊆ ω ∧
      (w : V) ∈ cluster (s : Config V) v := by
    intro w
    obtain ⟨s, hs1, hs2⟩ := exists_finset_subset_connects (mem_cluster_iff.mp (hmem w))
    exact ⟨s, hs1, mem_cluster_iff.mpr hs2⟩
  choose sw hsw1 hsw2 using hwit
  choose N hN using fun w : t =>
    exists_finset_subset_of_monotone_exhaust S hSmono hSexh (sw w)
  refine (eventually_ge_atTop (t.attach.sup N)).mono fun n hn => ?_
  have hEq : cluster (cutConfig (S n) ω) v = cluster ω v := by
    refine Set.Subset.antisymm (cluster_mono (fun e he => he.1) v) ?_
    intro w hw
    rw [← ht] at hw
    have hwt : w ∈ t := Finset.mem_coe.mp hw
    have hle : N ⟨w, hwt⟩ ≤ t.attach.sup N :=
      Finset.le_sup (f := N) (Finset.mem_attach t ⟨w, hwt⟩)
    have hsub : (sw ⟨w, hwt⟩ : Set (Sym2 V)) ⊆ cutConfig (S n) ω := by
      intro e he
      exact ⟨hsw1 ⟨w, hwt⟩ he, hSmono (hle.trans hn) (hN ⟨w, hwt⟩ he)⟩
    exact cluster_mono hsub v (hsw2 ⟨w, hwt⟩)
  rw [clusterVol_eq_encard, clusterVol_eq_encard, hEq]

end PercLib.CriticalLRP

namespace PercLib.CriticalLRP.Orchestration

/-! ## 3. The windowed flip difference is eventually the untruncated flip difference -/

variable {V : Type*} [Countable V]

omit [Countable V] in
/-- Deleting the edges outside `S` and then deleting `e` is the same as deleting `e` first. -/
theorem cutConfig_sdiff_singleton' (S : Finset (Sym2 V)) (e : Sym2 V) (ω : Config V) :
    cutConfig S (ω \ {e}) = cutConfig S ω \ {e} := by
  ext a
  simp only [cutConfig, Set.mem_inter_iff, Set.mem_sdiff, Set.mem_singleton_iff]
  tauto

omit [Countable V] in
/-- Deleting the edges outside `S` from `ω ∪ {e}`, with `e ∈ S`, keeps `e`: the windowed
configuration of `ω ∪ {e}` is the windowed configuration of `ω` together with `e`. -/
theorem cutConfig_union_singleton_of_mem (S : Finset (Sym2 V)) {e : Sym2 V} (he : e ∈ S)
    (ω : Config V) : cutConfig S (ω ∪ {e}) = cutConfig S ω ∪ {e} := by
  ext a
  simp only [cutConfig, Set.mem_inter_iff, Set.mem_union, Set.mem_singleton_iff]
  constructor
  · rintro ⟨ha | rfl, hs⟩
    · exact Or.inl ⟨ha, hs⟩
    · exact Or.inr rfl
  · rintro (⟨ha, hs⟩ | rfl)
    · exact ⟨Or.inl ha, hs⟩
    · exact ⟨Or.inr rfl, he⟩

omit [Countable V] in
/-- Reading the windowed configuration of `ω \ {e}` with `e` put back recovers the windowed
configuration of `ω ∪ {e}`, as soon as `e` is in the window. -/
theorem cutConfig_sdiff_singleton_union (S : Finset (Sym2 V)) {e : Sym2 V} (he : e ∈ S)
    (ω : Config V) : cutConfig S (ω \ {e}) ∪ {e} = cutConfig S (ω ∪ {e}) := by
  rw [cutConfig_sdiff_singleton', cutConfig_union_singleton_of_mem S he, Set.sdiff_union_self]

/-- **The windowed flip difference of the squared cluster volume, in closed form.**  For an
edge `e` of the window it is the difference of the squared cluster volume of the root at the
two windowed configurations `cutConfig S (ω \ {e}) ∪ {e}` (open) and `cutConfig S (ω \ {e})`
(closed) — no moment hypothesis, just unwinding the definitions. -/
theorem flipDiff_cutFun_clusterVolSq_eq (S : Finset (Sym2 V)) {e : Sym2 V} (he : e ∈ S)
    (o : V) (ω : Config V) :
    flipDiff (cutFun S (fun ω => (clusterVol ω o).toReal ^ 2)) e ω
      = (clusterVol (cutConfig S (ω \ {e}) ∪ {e}) o).toReal ^ 2
        - (clusterVol (cutConfig S (ω \ {e})) o).toReal ^ 2 := by
  rw [flipDiff, cutFun, cutFun, cutConfig_forceOn_of_mem S he, cutConfig_forceOn_of_mem S he,
    forceOn_singleton_open_eq, forceOn_singleton_closed_eq,
    cutConfig_sdiff_singleton', Set.sdiff_union_self]

/-- **The untruncated flip difference of the squared cluster volume, in closed form.** -/
theorem flipDiff_clusterVolSq_eq (e : Sym2 V) (o : V) (ω : Config V) :
    flipDiff (fun ω => (clusterVol ω o).toReal ^ 2) e ω
      = (clusterVol (ω ∪ {e}) o).toReal ^ 2 - (clusterVol (ω \ {e}) o).toReal ^ 2 := by
  rw [flipDiff, forceOn_singleton_open_eq, forceOn_singleton_closed_eq]

/-- **Eventual agreement of the windowed and untruncated flip differences of `|K_o|²`.**

At a configuration all of whose cluster volumes are finite, and for every edge `e`, the flip
difference of the windowed square `cutFun S |K_o|²` agrees with the flip difference of `|K_o|²`
as soon as the window contains `e` and the whole clusters of `ω \ {e}` and `ω ∪ {e}` at the
root.  This is an *eventual equality*, not a monotonicity: the closed ghost of the window can
drop when the window grows and alternate paths bridge `e`. -/
theorem eventually_flipDiff_cutFun_clusterVolSq_eq (S : ℕ → Finset (Sym2 V))
    (hSmono : Monotone S) (hSexh : ∀ e : Sym2 V, ∃ n, e ∈ S n) (o : V) (ω : Config V)
    (hfin : ∀ v : V, clusterVol ω v ≠ ⊤) (e : Sym2 V) :
    ∀ᶠ n in atTop,
      flipDiff (cutFun (S n) (fun ω => (clusterVol ω o).toReal ^ 2)) e ω
        = flipDiff (fun ω => (clusterVol ω o).toReal ^ 2) e ω := by
  classical
  have hmem : ∀ᶠ n in atTop, e ∈ S n := by
    obtain ⟨n₀, hn₀⟩ := hSexh e
    exact (eventually_ge_atTop n₀).mono fun n hn => hSmono hn hn₀
  have hfinA : clusterVol (ω \ {e}) o ≠ ⊤ :=
    ne_top_of_le_ne_top (hfin o) (clusterVol_mono (fun a ha => ha.1) o)
  have hfinB : clusterVol (ω ∪ {e}) o ≠ ⊤ := by
    induction e using Sym2.ind with
    | h x y =>
      have hle : clusterVol (ω ∪ {s(x, y)}) o ≤ clusterVol ω o + clusterVol ω x
          + clusterVol ω y := clusterVol_union_pair_le ω o x y
      exact ne_top_of_le_ne_top
        (ENNReal.add_ne_top.mpr ⟨ENNReal.add_ne_top.mpr ⟨hfin o, hfin x⟩, hfin y⟩) hle
  filter_upwards [hmem,
    eventually_clusterVol_cutConfig_eq S hSmono hSexh (ω \ {e}) o hfinA,
    eventually_clusterVol_cutConfig_eq S hSmono hSexh (ω ∪ {e}) o hfinB] with n hne hA hB
  rw [flipDiff_cutFun_clusterVolSq_eq (S n) hne o ω, flipDiff_clusterVolSq_eq e o ω,
    cutConfig_sdiff_singleton_union (S n) hne ω, hA, hB]

end PercLib.CriticalLRP.Orchestration
namespace PercLib.CriticalLRP.Orchestration

namespace SourceModelData

variable (M : SourceModelData)

/-! ## 4. Almost-sure simultaneous eventual agreement for the source model -/

/-- **Almost surely, the windowed flip difference of `|K₀|²` is eventually the untruncated one,
simultaneously for every edge.**

The almost-sure set is the one on which every cluster volume of the configuration is finite,
which the source's first cutoff moment provides (`ae_clusterVol_ne_top`).  This is the
configuration-by-configuration content of the insertion estimate: for every edge, the pivotal
flux of the windowed square has, eventually, exactly the integrand of the pivotal flux of the
untruncated square.  What it does *not* give is the exchange of the limit with the mean; that is
a domination, and it is the sole remaining input in `Insertion.lean`. -/
theorem ae_eventually_flipDiff_cutFun_eq (r : ℝ) (h1 : M.cutMassAt r (0 : M.V) ≠ ⊤)
    (S : ℕ → Finset (Sym2 M.V)) (hSmono : Monotone S)
    (hSexh : ∀ e : Sym2 M.V, ∃ n, e ∈ S n) :
    ∀ᵐ ω ∂(M.cutLaw r), ∀ e : Sym2 M.V, ∀ᶠ n in atTop,
      flipDiff (cutFun (S n) M.clusterVolSqReal) e ω = flipDiff M.clusterVolSqReal e ω := by
  filter_upwards [PivotFlux.ae_clusterVol_ne_top M r h1] with ω hω e
  have hf : M.clusterVolSqReal
      = fun ω : Config M.V => (clusterVol ω (0 : M.V)).toReal ^ 2 :=
    funext M.clusterVolSqReal_apply
  simp only [hf]
  exact eventually_flipDiff_cutFun_clusterVolSq_eq S hSmono hSexh (0 : M.V) ω hω e

end SourceModelData

end PercLib.CriticalLRP.Orchestration

/-! ## Axiom audit -/

namespace PercLib.CriticalLRP

#print axioms exists_finset_subset_connects
#print axioms eventually_connects_cutConfig
#print axioms eventually_clusterVol_cutConfig_eq

end PercLib.CriticalLRP

namespace PercLib.CriticalLRP.Orchestration

#print axioms cutConfig_sdiff_singleton'
#print axioms cutConfig_union_singleton_of_mem
#print axioms cutConfig_sdiff_singleton_union
#print axioms flipDiff_cutFun_clusterVolSq_eq
#print axioms flipDiff_clusterVolSq_eq
#print axioms eventually_flipDiff_cutFun_clusterVolSq_eq

end PercLib.CriticalLRP.Orchestration

namespace PercLib.CriticalLRP.Orchestration.SourceModelData

#print axioms ae_eventually_flipDiff_cutFun_eq

end PercLib.CriticalLRP.Orchestration.SourceModelData
