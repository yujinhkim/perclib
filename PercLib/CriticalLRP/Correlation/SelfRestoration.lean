/-
Migration source: https://github.com/yujinhkim/Critical-Long-range-percolation
Integration revision: 3b3d1d0e43ef940bfaa2292ee5c2ee094ac4edbf
Licence: Apache-2.0 for the PercLib Lean sources and tooling; see third_party/critical-lrp/.
External provenance and modifications are recorded in the file-specific notices below.
-/

/-
# Deterministic theory of the two restorations at the touch set of `K_0`

Source: Tom Hutchcroft, *Critical long-range percolation I: High effective dimension*,
arXiv:2508.18807v1, proof of Lemma I.4.12 (p. 39).

The paper defines, from two configurations `ω` and `ω'`,

  `ω̃(e) = ω(e)` for every edge `e` touching the cluster `K_0` of `0` in `ω`,
  `ω̃(e) = ω'(e)` for every other edge.

In the notation of `forceOn S η ω = (ω \ S) ∪ (η ∩ S)` (keep `ω` off `S`, take `η` on `S`), the
printed map is `forceOn (touchSet ω 0)ᶜ ω' ω` (the **complementary** map), while the map whose
*prose* the paper's subsequent argument describes is its transpose in the fresh/base pair,

  `forceOn (touchSet ω 0) ω' ω`     (the **self-resampling** map: fresh on the touch set).

Both maps preserve the product law: `edgeMeasure_map_forceOn_touchSet_compl` (printed map) and
`edgeMeasure_map_forceOn_touchSet'` (self-resampling map).  This file settles the **deterministic**
comparison of clusters for the self-resampling map, which is the one for which the paper's
inclusion `K_y ⊆ K̃_y` (`y ∉ K_0`) is *true*:

* `cluster_subset_forceOn_touchSet` : for `y ∉ K_0(ω)` the old cluster of `y` is contained in the
  restored cluster of `y` — the paper's inclusion, which fails for the printed map
  (`not_cluster_subset_forceOn_compl` in `CountableProduct/RestorationCompl.lean`).
* `mem_of_forceOn_touchSet_of_avoid` : a restored-open walk from `y` whose vertices avoid the old
  `K_0` consists of **base** edges.  Hence "avoiding the old `K_0`" is exactly the base regime.
* `exists_fresh_crossing` : a restored-open walk from `y ∉ K_0` that reaches `K_0` must cross into
  `K_0` along an edge that is **fresh**-open.  So the new part of the restored cluster is reached
  only after such a fresh crossing.
* `not_fresh_disjoint_connections` : the paper's next assertion — that on `z ∈ K̃_y \ K_y` there is
  `b ∈ K_0` joined to `y` and to `z` by disjoint paths *in the fresh configuration* — is **false**
  for the self-resampling map as well (explicit four-vertex counterexample).  This is the exact
  obstruction to the printed proof, and it is why the repaired chain in `TwoClusterGap.lean` reads
  `K_y` as the *fresh* copy's cluster instead.

No `sorry`, no custom axioms.
-/
module

public import PercLib.CriticalLRP.CountableProduct.RestorationCompl

set_option autoImplicit true

set_option linter.unusedSectionVars false
set_option maxHeartbeats 1000000

@[expose] public section

open MeasureTheory Measure ProbabilityTheory unitInterval
open scoped ENNReal NNReal

namespace PercLib.CriticalLRP

attribute [local instance] Classical.propDecidable

variable {V : Type*} [Countable V]

/-! ## Membership in `forceOn` -/

/-- Membership form of `forceOn_apply_of_mem`. -/
theorem mem_forceOn_of_mem {S : Set (Sym2 V)} {e : Sym2 V} (he : e ∈ S) (η ω : Config V) :
    (e ∈ forceOn S η ω ↔ e ∈ η) :=
  iff_of_eq (forceOn_apply_of_mem he η ω)

/-! ## Base walks avoid the touch set of `K_0`

That a walk of `K_0`-free vertices cannot use an edge touching `K_0` is proved by transporting the
repository's `walk_edges_not_mem_cluster` (stated for the complementary map) along
`forceOn (touchSet ω o)ᶜ ω ω = ω`.  No coupling is involved: this is a statement about a single
configuration. -/

/-- **A base-open walk from a vertex outside `K_0` meets no edge of the touch set, and never
enters `K_0`.** -/
theorem walk_edges_notMem_touchSet {ω : Config V} {o y : V} (hy : y ∉ cluster ω o) {z : V}
    (p : (⊤ : SimpleGraph V).Walk y z) (hp : ∀ e ∈ p.edges, e ∈ ω) :
    (∀ e ∈ p.edges, e ∉ touchSet ω o) ∧ z ∉ cluster ω o := by
  have hforce : ∀ e ∈ p.edges, e ∈ forceOn (touchSet ω o)ᶜ ω ω := by
    intro e he
    by_cases hT : e ∈ touchSet ω o
    · exact (mem_forceOn_of_notMem (S := (touchSet ω o)ᶜ) (by simpa using hT) ω ω).mpr
        (hp e he)
    · exact (iff_of_eq (forceOn_apply_of_mem (S := (touchSet ω o)ᶜ)
        (by simpa using hT) ω ω)).mpr (hp e he)
  obtain ⟨hav, hz⟩ := walk_edges_not_mem_cluster (ω := ω) (ω' := ω) (o := o) hy p hforce
  refine ⟨?_, hz⟩
  intro e he hmem
  obtain ⟨x, hx, hxc⟩ := mem_touchSet.mp hmem
  exact hav e he x hx hxc

/-! ## The self-resampling map: `K_y ⊆ K̃_y` for `y ∉ K_0` -/

/-- **The paper's inclusion holds for the self-resampling map.**  If `ω̃ = forceOn (touchSet ω o) η ω`
replaces the state of every edge touching `K_0(ω)` by its state in the independent configuration
`η`, then for `y ∉ K_0(ω)` the cluster of `y` only grows. -/
theorem cluster_subset_forceOn_touchSet (η ω : Config V) (o y : V)
    (hy : y ∉ cluster ω o) :
    cluster ω y ⊆ cluster (forceOn (touchSet ω o) η ω) y := by
  intro z hz
  obtain ⟨p, hp⟩ := pathConnects_iff.mpr (mem_cluster_iff.mp hz)
  have hT := (walk_edges_notMem_touchSet hy p hp).1
  exact mem_cluster_iff.mpr (pathConnects_iff.mp ⟨p, fun e he => by
    rw [mem_forceOn_of_notMem (hT e he) η ω]
    exact hp e he⟩)

/-- **A restored-open walk avoiding the old `K_0` is a base walk.**  In the self-resampling map the
edges off the touch set carry the base values, so every connection that stays clear of the old
`K_0` is a connection of the base configuration. -/
theorem mem_of_forceOn_touchSet_of_avoid {ω η : Config V} {o y z : V}
    (p : (⊤ : SimpleGraph V).Walk y z)
    (hp : ∀ e ∈ p.edges, e ∈ forceOn (touchSet ω o) η ω)
    (hav : ∀ v ∈ p.support, v ∉ cluster ω o) :
    ∀ e ∈ p.edges, e ∈ ω := by
  intro e he
  have hoff : e ∉ touchSet ω o := by
    intro hmem
    obtain ⟨w, hw, hwc⟩ := mem_touchSet.mp hmem
    exact hav w (SimpleGraph.Walk.mem_support_iff_exists_mem_edges.mpr (Or.inr ⟨e, he, hw⟩)) hwc
  exact (mem_forceOn_of_notMem hoff η ω).mp (hp e he)

/-- **Entering the old `K_0` in the self-resampled configuration costs a fresh edge.**  A
restored-open walk starting outside `K_0(ω)` and ending inside it must cross the boundary of `K_0`
along an edge open in the fresh configuration `η`.  (Everything the walk does before that crossing
may be a base connection.) -/
theorem exists_fresh_crossing {ω η : Config V} {o : V} {y : V} (hy : y ∉ cluster ω o) :
    ∀ {b : V} (p : (⊤ : SimpleGraph V).Walk y b), b ∈ cluster ω o →
      (∀ e ∈ p.edges, e ∈ forceOn (touchSet ω o) η ω) →
      ∃ e ∈ p.edges, e ∈ η ∧ ∃ u v : V, e = s(u, v) ∧ u ∈ cluster ω o ∧ v ∉ cluster ω o
  | _, .nil, hb, _ => absurd hb hy
  | _, .cons h p', hb, hp => by
      rename_i z m
      by_cases hm : m ∈ cluster ω o
      · have hmem : s(y, m) ∈ forceOn (touchSet ω o) η ω :=
          hp _ (by rw [SimpleGraph.Walk.edges_cons]; exact List.mem_cons_self ..)
        have hT : s(y, m) ∈ touchSet ω o :=
          mem_touchSet.mpr ⟨m, Sym2.mem_mk_right y m, hm⟩
        exact ⟨s(y, m), by rw [SimpleGraph.Walk.edges_cons]; exact List.mem_cons_self ..,
          (mem_forceOn_of_mem hT η ω).mp hmem, m, y, Sym2.eq_swap, hm, hy⟩
      · obtain ⟨e, he, hfresh, u, w, hev, hu, hw⟩ :=
          exists_fresh_crossing hm p' hb (fun e he => hp e (by
            rw [SimpleGraph.Walk.edges_cons]; exact List.mem_cons_of_mem _ he))
        exact ⟨e, by rw [SimpleGraph.Walk.edges_cons]; exact List.mem_cons_of_mem _ he,
          hfresh, u, w, hev, hu, hw⟩

/-! ## The paper's fresh-copy assertion fails for the self-resampling map

The paper continues: "if `z ∈ K̃_y \ K_y` then there must exist `b ∈ K_0` such that `b` is
connected to `y` and `z` by disjoint paths in `ω'`".  For the self-resampling map the new part of
the restored cluster is produced by fresh edges *crossing into* the old `K_0`, and the part beyond
the crossing may again be a base connection, so no such `b` with fresh connections to both `y` and
`z` need exist.  Four vertices suffice. -/

/-- The base configuration of the counterexample: the single open edge `{2,3}`. -/
def baseConfig4 : Config (Fin 4) := {s(2, 3)}

/-- The fresh configuration of the counterexample: the two open edges `{0,1}`, `{0,2}`. -/
def freshConfig4 : Config (Fin 4) := {s(0, 1), s(0, 2)}

theorem cluster_baseConfig4_zero : cluster baseConfig4 (0 : Fin 4) = {0} := by
  refine cluster_eq_singleton_of_isolated fun u => ?_
  fin_cases u <;> simp [baseConfig4]

theorem cluster_baseConfig4_one : cluster baseConfig4 (1 : Fin 4) = {1} := by
  refine cluster_eq_singleton_of_isolated fun u => ?_
  fin_cases u <;> simp [baseConfig4]

/-- Vertex `3` is *not* in the base cluster of `1`. -/
theorem not_mem_cluster_base_three : (3 : Fin 4) ∉ cluster baseConfig4 1 := by
  rw [cluster_baseConfig4_one]
  simp

/-- Vertex `3` *is* in the restored cluster of `1`. -/
theorem mem_cluster_forceOn_touchSet_three :
    (3 : Fin 4) ∈
      cluster (forceOn (touchSet baseConfig4 (0 : Fin 4)) freshConfig4 baseConfig4) 1 := by
  have h01 : s(1, 0) ∈ forceOn (touchSet baseConfig4 (0 : Fin 4)) freshConfig4 baseConfig4 :=
    (mem_forceOn_of_mem (mem_touchSet.mpr ⟨(0 : Fin 4), Sym2.mem_mk_right 1 0, by
      rw [cluster_baseConfig4_zero]; simp⟩) freshConfig4 baseConfig4).mpr (by simp [freshConfig4])
  have h02 : s(0, 2) ∈ forceOn (touchSet baseConfig4 (0 : Fin 4)) freshConfig4 baseConfig4 :=
    (mem_forceOn_of_mem (mem_touchSet.mpr ⟨(0 : Fin 4), Sym2.mem_mk_left 0 2, by
      rw [cluster_baseConfig4_zero]; simp⟩) freshConfig4 baseConfig4).mpr (by simp [freshConfig4])
  have h23 : s(2, 3) ∈ forceOn (touchSet baseConfig4 (0 : Fin 4)) freshConfig4 baseConfig4 := by
    refine (mem_forceOn_of_notMem ?_ freshConfig4 baseConfig4).mpr (by simp [baseConfig4])
    intro hmem
    obtain ⟨x, hx, hxc⟩ := mem_touchSet.mp hmem
    rw [cluster_baseConfig4_zero] at hxc
    have hx0 : x = 0 := by simpa using hxc
    subst hx0
    rw [Sym2.mem_iff] at hx
    rcases hx with h | h <;> exact absurd h (by decide)
  have hconn : Connects (forceOn (touchSet baseConfig4 (0 : Fin 4)) freshConfig4 baseConfig4) 1 3 := by
    rw [Connects, SimpleGraph.reachable_iff_reflTransGen]
    have e1 : (openGraph (forceOn (touchSet baseConfig4 (0 : Fin 4)) freshConfig4
        baseConfig4)).Adj 1 0 := by
      rw [openGraph_adj]; exact ⟨by decide, h01⟩
    have e2 : (openGraph (forceOn (touchSet baseConfig4 (0 : Fin 4)) freshConfig4
        baseConfig4)).Adj 0 2 := by
      rw [openGraph_adj]; exact ⟨by decide, h02⟩
    have e3 : (openGraph (forceOn (touchSet baseConfig4 (0 : Fin 4)) freshConfig4
        baseConfig4)).Adj 2 3 := by
      rw [openGraph_adj]; exact ⟨by decide, h23⟩
    exact Relation.ReflTransGen.head e1 (Relation.ReflTransGen.head e2
      (Relation.ReflTransGen.single e3))
  rwa [mem_cluster_iff]

/-- **The paper's fresh-copy assertion fails for the self-resampling map.**  With the base
configuration `{2,3}` and the fresh configuration `{0,1}, {0,2}`: `1 ∉ K_0` and `3 ∈ K̃_1 \ K_1`,
but no vertex `b ∈ K_0 = {0}` is connected in the *fresh* configuration to both `1` and `3`. -/
theorem not_fresh_disjoint_connections :
    ¬ ∃ b ∈ cluster baseConfig4 (0 : Fin 4),
        Connects freshConfig4 b 1 ∧ Connects freshConfig4 b 3 := by
  rintro ⟨b, hb, -, hb3⟩
  rw [cluster_baseConfig4_zero] at hb
  have hb0 : b = 0 := by simpa using hb
  subst hb0
  have hiso : ∀ u : Fin 4, s(3, u) ∉ freshConfig4 := by
    intro u
    fin_cases u <;> simp [freshConfig4]
  have hempty : cluster freshConfig4 (3 : Fin 4) = {3} := cluster_eq_singleton_of_isolated hiso
  have heq : cluster freshConfig4 (0 : Fin 4) = cluster freshConfig4 (3 : Fin 4) :=
    cluster_eq_iff.mpr hb3
  have hzero : (0 : Fin 4) ∈ cluster freshConfig4 (0 : Fin 4) := cluster_mem_self _ 0
  rw [heq, hempty] at hzero
  simp at hzero

/-- The three deterministic facts together: `1 ∉ K_0`, the restored cluster of `1` gains `3`,
`3` is not in the base cluster of `1`, and no `b ∈ K_0` is fresh-connected to both `1` and `3`. -/
theorem selfRestoration_mechanism :
    (1 : Fin 4) ∉ cluster baseConfig4 (0 : Fin 4) ∧
      (3 : Fin 4) ∈ cluster (forceOn (touchSet baseConfig4 (0 : Fin 4)) freshConfig4
        baseConfig4) 1 ∧
      (3 : Fin 4) ∉ cluster baseConfig4 1 ∧
      ¬ ∃ b ∈ cluster baseConfig4 (0 : Fin 4),
          Connects freshConfig4 b 1 ∧ Connects freshConfig4 b 3 := by
  refine ⟨by rw [cluster_baseConfig4_zero]; simp, mem_cluster_forceOn_touchSet_three,
    not_mem_cluster_base_three, not_fresh_disjoint_connections⟩

end PercLib.CriticalLRP
