/-
Copyright (c) 2026 PercLib contributors. Released under Apache 2.0.

# The exact single-edge cluster merge identity

Swarm `smwvakyb4`, member `m2`, direction `d1`.

`RussoInf/MergeSubset.lean` proves one half of the merge identity: for a distinct pair
`x ≠ y` and an edge `e = s(x,y)`,

  `cluster ω o ∪ cluster ω y ⊆ cluster (ω ∪ {e}) o`   (`cluster_union_edge_subset`),

*unconditionally*, i.e. no hypothesis on the position of `x` is needed.  The other half,
the one that makes the identity exact and yields the *cardinality* increment, needs a
path argument, and it is proved here:

  `cluster (ω ∪ {s(x,y)}) o ⊆ cluster ω o ∪ cluster ω x ∪ cluster ω y`   (no hypotheses)

and hence, as soon as `x` is already in the cluster of `o` (so that the cluster of `x`
*is* the cluster of `o`),

  `cluster (ω ∪ {s(x,y)}) o = cluster ω o ∪ cluster ω y`   (`x ≠ y`, `x ∈ cluster ω o`).

The first inclusion is proved by a walk induction: a walk from `o` in `ω ∪ {e}` that ends
at `v` stays inside the three clusters of `o`, `x`, `y`, because

* any step on an edge of `ω` keeps the walk inside the cluster it was already in, and
* any step on `e` puts the walk exactly at `x` or at `y`.

No path-shortening, no `SimpleGraph.Walk` surgery and no choice of representative is
needed; the induction is `Relation.ReflTransGen` induction on the *last* step, mirroring
the existing `reflTransGen_union_singleton_or_endpoint`, and it handles repetitions of the
new edge (a walk may cross `e` back and forth) by keeping all three clusters in the
statement.

Consequences proved here, all with explicit hypotheses:

* `cluster_forceOn_pair_eq` — the same identity with `ω` free and the flip written as
  `forceOn {e} {e} ω`; the two cases `e ∈ ω` and `e ∉ ω` are both handled, so no
  `e ∉ ω` side condition is smuggled in;
* `notMem_pair_of_mem_cluster_of_notMem` — if `x` is in the cluster of `o` and `y` is not,
  then the edge `s(x,y)` is *closed* in `ω` (the off-region is the genuine off-region);
* `disjoint_cluster_of_notMem` — clusters of `o` and of `y ∉ cluster ω o` are disjoint;
* `clusterVol_union_pair_eq`, `clusterVol_forceOn_pair_eq` — the exact volume identity
  `|K_o after opening e| = |K_o| + |K_y|` in `ℝ≥0∞`, with no finiteness hypothesis and no
  finite box: it is an identity of extended cardinalities of genuine infinite clusters;
* `clusterVol_union_pair_sq_eq` — the `p = 2` increment of the merged cluster volume is
  `2|K_o||K_y| + |K_y|²`, in `ℝ≥0∞`, again without finiteness hypotheses;
* `flipDiff_clusterVol_eq`, `flipDiff_clusterVol_sq_eq` — the same two statements in the
  exact `flipDiff` shape of `RussoInf/QuadraticFlux`, i.e. the source's
  `2|K||K_y| + |K_y|²` as a *pointwise* identity on the off-graph region (finiteness of
  the two volumes is required for `toReal`, and is stated);
* `flipDiff_clusterVol_sq_eq_cases` — the **complete** pointwise value of the `p = 2` flip
  difference at a closed edge: `0` if both endpoints are in the cluster, `2|K_o||K_y| +
  |K_y|²` if only `x` is, `2|K_o||K_x| + |K_x|²` if only `y` is, `0` if neither is;
* `clusterVol_forceOn_flip_eq`, `flipDiff_clusterVol_eq_free`,
  `flipDiff_clusterVol_sq_eq_free`, `setIntegral_flipDiff_clusterVol_sq_eq_free` — the same
  statements with `ω` free and the closed configuration `forceOn {s(x,y)} ∅ ω` written out,
  which is the shape in which `flipDiff`/`pivotalFlux` use them;
* `not_cluster_union_pair_eq_of_notMem_cluster` — a checked counterexample showing that the
  hypothesis `x ∈ cluster ω o` is not removable: the identity fails for `ω = ∅`,
  `o = 0`, `x = 1`, `y = 2`.

**What is not claimed.**  Nothing here differentiates a moment in the radius, and nothing
here bounds the increment by a finite-box quantity: `clusterVol` is the extended
cardinality of the genuine cluster.  The `p = 2` statements are pointwise identities (or
integrals over the off-region of a pointwise identity); no interchange of an edge sum with a
derivative, no majorant and no radius differentiability is asserted.  In particular the
integral of the flip difference over the *complement* of the off-region is not evaluated:
`flipDiff_clusterVol_sq_eq_cases` shows explicitly that the increment there is a different
value, not zero.

No `sorry`, no `admit`, no `native_decide`, no custom axioms.
-/
module

public import PercLib.CriticalLRP.RussoInf.MergeSubset
public import PercLib.CriticalLRP.RussoInf.QuadraticFlux

/-!
# The single-edge cluster merge and its quadratic increment

A last-step reachability induction proves the reverse merge inclusion.  On the
off-region the clusters are disjoint, giving exact extended-cardinality volume
identities and the real quadratic flip increment.
-/

set_option autoImplicit false
set_option linter.hashCommand false
set_option linter.style.longLine false
set_option linter.unusedSectionVars false
set_option linter.unusedSimpArgs false
set_option linter.unnecessarySimpa false
set_option linter.unusedTactic false
set_option linter.unusedVariables false

@[expose] public section

noncomputable section

open MeasureTheory Measure Filter Finset
open scoped ENNReal ENat NNReal Topology

namespace PercLib.CriticalLRP

attribute [local instance] Classical.propDecidable

variable {V : Type*} [Countable V]

/-! ## 1. Membership, reachability and the cluster of a member -/

/-- Cluster membership is `Relation.ReflTransGen` reachability along open edges. -/
theorem mem_cluster_iff_reflTransGen {ω : Config V} {v w : V} :
    w ∈ cluster ω v ↔ Relation.ReflTransGen (openGraph ω).Adj v w :=
  mem_cluster_iff.trans (SimpleGraph.reachable_iff_reflTransGen v w)

/-- A vertex of the cluster of `o` has the cluster of `o` as its own cluster. -/
theorem cluster_eq_of_mem_cluster {ω : Config V} {o y : V} (hy : y ∈ cluster ω o) :
    cluster ω y = cluster ω o :=
  cluster_eq_iff.mpr (connects_symm (mem_cluster_iff.mp hy))

/-! ## 2. A walk in `ω ∪ {s(x,y)}` stays in the three clusters of `o`, `x`, `y` -/

/-- **The walk lemma.**  If `v` is reachable from `o` in the graph with the single edge
`s(x,y)` added, then `v` is reachable from `o`, from `x` or from `y` in the original
graph.

The induction is on the last step, so it keeps the full strength at intermediate vertices:
this is what makes repeated crossings of the new edge harmless. -/
theorem reflTransGen_union_singleton_or_cluster {o x y v : V} {ω : Config V}
    (h : Relation.ReflTransGen (openGraph (ω ∪ {s(x, y)})).Adj o v) :
    Relation.ReflTransGen (openGraph ω).Adj o v ∨
      Relation.ReflTransGen (openGraph ω).Adj x v ∨
      Relation.ReflTransGen (openGraph ω).Adj y v := by
  induction h with
  | refl => exact Or.inl Relation.ReflTransGen.refl
  | @tail a b hab hstep ih =>
    have hne : a ≠ b := (openGraph_adj.mp hstep).1
    have hmem : s(a, b) ∈ ω ∪ {s(x, y)} := (openGraph_adj.mp hstep).2
    by_cases he : s(a, b) = s(x, y)
    · -- the step uses the added edge: `b` is one of its endpoints
      have hb : b = x ∨ b = y := by
        have hmem' : b ∈ s(x, y) := he ▸ Sym2.mem_mk_right a b
        rwa [Sym2.mem_iff] at hmem'
      rcases hb with hb | hb
      · rw [hb]; exact Or.inr (Or.inl Relation.ReflTransGen.refl)
      · rw [hb]; exact Or.inr (Or.inr Relation.ReflTransGen.refl)
    · -- the step is an edge of `ω`: extend the reachability of the same cluster
      have hmemω : s(a, b) ∈ ω := by
        rw [Set.mem_union, Set.mem_singleton_iff] at hmem
        exact hmem.resolve_right he
      have hstepω : (openGraph ω).Adj a b := by
        rw [openGraph_adj]
        exact ⟨hne, hmemω⟩
      rcases ih with ih | ih | ih
      · exact Or.inl (ih.tail hstepω)
      · exact Or.inr (Or.inl (ih.tail hstepω))
      · exact Or.inr (Or.inr (ih.tail hstepω))

/-- **The reverse inclusion of the merge identity, with the two extra clusters kept.** -/
theorem cluster_union_singleton_subset_three {o x y : V} {ω : Config V} :
    cluster (ω ∪ {s(x, y)}) o ⊆ cluster ω o ∪ cluster ω x ∪ cluster ω y := by
  intro v hv
  rcases reflTransGen_union_singleton_or_cluster (x := x) (y := y)
    (mem_cluster_iff_reflTransGen.mp hv) with h | h | h
  · exact Or.inl (Or.inl (mem_cluster_iff_reflTransGen.mpr h))
  · exact Or.inl (Or.inr (mem_cluster_iff_reflTransGen.mpr h))
  · exact Or.inr (mem_cluster_iff_reflTransGen.mpr h)

/-! ## 3. The exact merge identity -/

/-- **The exact single-edge cluster merge identity.**  If `x ≠ y` and `x` lies in the cluster
of `o`, then opening the edge `s(x,y)` merges the cluster of `y` into the cluster of `o` and
does nothing else:

  `cluster (ω ∪ {s(x,y)}) o = cluster ω o ∪ cluster ω y`.

Note that there is *no* hypothesis `s(x,y) ∉ ω`: when the edge is already open, `y` is already
in the cluster of `o` and both sides equal `cluster ω o`. -/
theorem cluster_union_pair_eq {o x y : V} {ω : Config V} (hxy : x ≠ y)
    (hx : x ∈ cluster ω o) :
    cluster (ω ∪ {s(x, y)}) o = cluster ω o ∪ cluster ω y := by
  refine Set.Subset.antisymm ?_ (cluster_union_edge_subset hxy hx)
  intro v hv
  have hsub := cluster_union_singleton_subset_three (x := x) (y := y) (o := o) hv
  have hxK : cluster ω x = cluster ω o := cluster_eq_of_mem_cluster hx
  simpa [hxK] using hsub

/-- The identity with the roles of the two endpoints exchanged. -/
theorem cluster_union_pair_eq_symm {o x y : V} {ω : Config V} (hxy : x ≠ y)
    (hy : y ∈ cluster ω o) :
    cluster (ω ∪ {s(x, y)}) o = cluster ω o ∪ cluster ω x := by
  have h := cluster_union_pair_eq (ω := ω) (o := o) hxy.symm hy
  simpa [Sym2.eq_swap] using h

/-- When both endpoints are already in the cluster of `o`, opening the edge changes nothing. -/
theorem cluster_union_pair_eq_of_mem_cluster {o x y : V} {ω : Config V} (hxy : x ≠ y)
    (hx : x ∈ cluster ω o) (hy : y ∈ cluster ω o) :
    cluster (ω ∪ {s(x, y)}) o = cluster ω o := by
  rw [cluster_union_pair_eq hxy hx, cluster_eq_of_mem_cluster hy, Set.union_self]

/-- **The loop case `x = y`.**  `s(x,x)` is the diagonal element of `Sym2 V`; `openGraph` is
`SimpleGraph.fromEdgeSet`, which discards diagonal pairs, so the edge contributes no adjacency at
all.  Consistently with that, the merge identity holds with `y = x` as well, and the two sides are
both `cluster ω o`: the three-cluster inclusion collapses `cluster ω x` into `cluster ω o` twice.
Hence the hypothesis `x ≠ y` in `cluster_union_pair_eq` is a convenience, not a necessity. -/
theorem cluster_union_loop_eq {o x : V} {ω : Config V} (hx : x ∈ cluster ω o) :
    cluster (ω ∪ {s(x, x)}) o = cluster ω o := by
  refine Set.Subset.antisymm ?_ (cluster_mono (fun _ he => Set.mem_union_left _ he) o)
  intro v hv
  have hsub := cluster_union_singleton_subset_three (x := x) (y := x) (o := o) hv
  simpa [cluster_eq_of_mem_cluster hx] using hsub

/-- Consequently the volume is unchanged when both endpoints are already in the cluster. -/
theorem clusterVol_union_pair_eq_of_mem_cluster {o x y : V} {ω : Config V} (hxy : x ≠ y)
    (hx : x ∈ cluster ω o) (hy : y ∈ cluster ω o) :
    clusterVol (ω ∪ {s(x, y)}) o = clusterVol ω o := by
  rw [clusterVol_eq_encard, clusterVol_eq_encard, cluster_union_pair_eq_of_mem_cluster hxy hx hy]

/-! ## 4. The `forceOn` form, with `ω` free -/

/-- `forceOn {e} {e}` with `e` absent is opening `e`. -/
theorem forceOn_singleton_self_eq_union {e : Sym2 V} {ω : Config V} (he : e ∉ ω) :
    forceOn {e} {e} ω = ω ∪ {e} := by
  ext e'
  by_cases hne : e' = e
  · subst hne; simp [forceOn, he]
  · simp [forceOn, hne]

/-- `forceOn {e} {e}` with `e` present is the identity. -/
theorem forceOn_singleton_self_eq_of_mem {e : Sym2 V} {ω : Config V} (he : e ∈ ω) :
    forceOn {e} {e} ω = ω := by
  ext e'
  by_cases hne : e' = e
  · subst hne; simp [forceOn, he]
  · simp [forceOn, hne]

/-- `forceOn {e} ∅` with `e` absent is the identity. -/
theorem forceOn_singleton_empty_eq_of_notMem {e : Sym2 V} {ω : Config V} (he : e ∉ ω) :
    forceOn {e} ∅ ω = ω := by
  ext e'
  by_cases hne : e' = e
  · subst hne; simp [forceOn, he]
  · simp [forceOn, hne]

/-- **The merge identity in `forceOn` form.**  For any configuration `ω`, distinct `x ≠ y` and
`x` in the cluster of `o`, replacing the state of `s(x,y)` by *open* gives

  `cluster (forceOn {s(x,y)} {s(x,y)} ω) o = cluster ω o ∪ cluster ω y`.

Both cases are handled: if `s(x,y)` is already open in `ω` then `forceOn` is the identity and
`y` is already in the cluster of `o`; if not, `forceOn` is `ω ∪ {s(x,y)}` and the identity
above applies.  No hypothesis on the state of `s(x,y)` in `ω` is left implicit. -/
theorem cluster_forceOn_pair_eq {o x y : V} {ω : Config V} (hxy : x ≠ y)
    (hx : x ∈ cluster ω o) :
    cluster (forceOn {s(x, y)} {s(x, y)} ω) o = cluster ω o ∪ cluster ω y := by
  by_cases he : s(x, y) ∈ ω
  · rw [forceOn_singleton_self_eq_of_mem he]
    have hadj : (openGraph ω).Adj x y := by
      rw [openGraph_adj]
      exact ⟨hxy, he⟩
    have hy : y ∈ cluster ω o :=
      mem_cluster_iff.mpr (connects_trans (mem_cluster_iff.mp hx) hadj.reachable)
    rw [cluster_eq_of_mem_cluster hy, Set.union_self]
  · rw [forceOn_singleton_self_eq_union he]
    exact cluster_union_pair_eq hxy hx

/-! ## 5. The off-region: `y` outside the cluster of `o` -/

/-- **On the off-region the edge is closed.**  If `x` is in the cluster of `o` but `y` is not,
then `s(x,y)` is not open in `ω`.  (In particular the hypotheses `x ∈ K_o`, `y ∉ K_o` are
consistent with an "open the edge" picture only when the edge is currently closed.) -/
theorem notMem_pair_of_mem_cluster_of_notMem {ω : Config V} {o x y : V}
    (hx : x ∈ cluster ω o) (hy : y ∉ cluster ω o) : s(x, y) ∉ ω := by
  have hne : x ≠ y := by
    rintro rfl
    exact hy hx
  intro he
  have hadj : (openGraph ω).Adj x y := by
    rw [openGraph_adj]
    exact ⟨hne, he⟩
  exact hy (mem_cluster_iff.mpr (connects_trans (mem_cluster_iff.mp hx) hadj.reachable))

/-- Clusters of `o` and of a vertex `y` outside it are disjoint. -/
theorem disjoint_cluster_of_notMem {ω : Config V} {o y : V} (hy : y ∉ cluster ω o) :
    Disjoint (cluster ω o) (cluster ω y) := by
  rw [Set.disjoint_left]
  intro z hz hz'
  have h1 : cluster ω z = cluster ω o := cluster_eq_of_mem_cluster (o := o) hz
  have h2 : cluster ω z = cluster ω y := cluster_eq_of_mem_cluster (o := y) hz'
  have hy' : cluster ω y = cluster ω o := h2.symm.trans h1
  refine hy ?_
  rw [← hy']
  exact cluster_mem_self ω y

/-! ## 6. The exact volume identity -/

/-- Monotonicity of the extended cluster volume in a cluster inclusion. -/
theorem clusterVol_le_of_cluster_subset {ω ω' : Config V} {v v' : V}
    (h : cluster ω v ⊆ cluster ω' v') : clusterVol ω v ≤ clusterVol ω' v' := by
  rw [clusterVol_eq_encard, clusterVol_eq_encard]
  exact_mod_cast Set.encard_le_encard h

/-- **The exact volume identity of the merge.**  On the off-region `y ∉ cluster ω o`, opening
the pivotal edge `s(x,y)` increases the volume of the cluster of `o` by exactly the volume of
the cluster of `y`:

  `|K_o (ω ∪ {s(x,y)})| = |K_o| + |K_y|`.

This is an identity of extended cardinalities: no finiteness of either cluster, no finite box
and no measurable quantity is involved. -/
theorem clusterVol_union_pair_eq {o x y : V} {ω : Config V} (hxy : x ≠ y)
    (hx : x ∈ cluster ω o) (hy : y ∉ cluster ω o) :
    clusterVol (ω ∪ {s(x, y)}) o = clusterVol ω o + clusterVol ω y := by
  rw [clusterVol_eq_encard, cluster_union_pair_eq hxy hx,
    Set.encard_union_eq (disjoint_cluster_of_notMem hy), clusterVol_eq_encard,
    clusterVol_eq_encard]
  push_cast
  ring

/-- The same volume identity in `forceOn` form; on the off-region the edge is closed, so
`forceOn {s(x,y)} {s(x,y)}` really is "open the edge". -/
theorem clusterVol_forceOn_pair_eq {o x y : V} {ω : Config V} (hxy : x ≠ y)
    (hx : x ∈ cluster ω o) (hy : y ∉ cluster ω o) :
    clusterVol (forceOn {s(x, y)} {s(x, y)} ω) o = clusterVol ω o + clusterVol ω y := by
  rw [forceOn_singleton_self_eq_union (notMem_pair_of_mem_cluster_of_notMem hx hy)]
  exact clusterVol_union_pair_eq hxy hx hy

/-- The volume only grows: opening `s(x,y)` never shrinks the cluster of `o`, with no hypothesis
at all. -/
theorem clusterVol_le_clusterVol_union_pair {o x y : V} {ω : Config V} :
    clusterVol ω o ≤ clusterVol (ω ∪ {s(x, y)}) o :=
  clusterVol_mono (fun _ he => Set.mem_union_left _ he) o

/-- The volume of the cluster of `y` is charged to the merged cluster: this is the *lower*
bound on the increment that holds with no hypothesis on `y`. -/
theorem clusterVol_y_le_clusterVol_union_pair {o x y : V} {ω : Config V} (hxy : x ≠ y)
    (hx : x ∈ cluster ω o) :
    clusterVol ω y ≤ clusterVol (ω ∪ {s(x, y)}) o :=
  clusterVol_le_of_cluster_subset
    (Set.subset_union_right.trans (cluster_union_edge_subset hxy hx))

/-- **Merging preserves the disjointness of the other clusters.**  If `z` is in neither the
cluster of `o` nor the cluster of `y`, then opening `s(x,y)` does not join it to the cluster of
`o` either, so the partition of the remaining clusters is untouched. -/
theorem disjoint_cluster_union_pair {o x y z : V} {ω : Config V} (hxy : x ≠ y)
    (hx : x ∈ cluster ω o) (hz : z ∉ cluster ω o) (hzy : z ∉ cluster ω y) :
    Disjoint (cluster (ω ∪ {s(x, y)}) o) (cluster (ω ∪ {s(x, y)}) z) := by
  have hz' : z ∉ cluster (ω ∪ {s(x, y)}) o := by
    rw [cluster_union_pair_eq hxy hx]
    rintro (h | h)
    · exact hz h
    · exact hzy h
  exact disjoint_cluster_of_notMem hz'

/-! ## 7. The `p = 2` increment: `2|K_o||K_y| + |K_y|²` -/

/-- **The `p = 2` increment of the merged cluster volume**, in `ℝ≥0∞` and with no finiteness
hypothesis: the square of the merged volume is the square of the old volume plus exactly
`2|K_o||K_y| + |K_y|²`.  The second summand is `flipDiff` of `|K_o|²` on the off-region. -/
theorem clusterVol_union_pair_sq_eq {o x y : V} {ω : Config V} (hxy : x ≠ y)
    (hx : x ∈ cluster ω o) (hy : y ∉ cluster ω o) :
    (clusterVol (ω ∪ {s(x, y)}) o) ^ 2
      = (clusterVol ω o) ^ 2
        + (2 * clusterVol ω o * clusterVol ω y + (clusterVol ω y) ^ 2) := by
  rw [clusterVol_union_pair_eq hxy hx hy, add_sq_ennreal]
  ring

/-- The same identity in `forceOn` form. -/
theorem clusterVol_forceOn_pair_sq_eq {o x y : V} {ω : Config V} (hxy : x ≠ y)
    (hx : x ∈ cluster ω o) (hy : y ∉ cluster ω o) :
    (clusterVol (forceOn {s(x, y)} {s(x, y)} ω) o) ^ 2
      = (clusterVol ω o) ^ 2
        + (2 * clusterVol ω o * clusterVol ω y + (clusterVol ω y) ^ 2) := by
  rw [clusterVol_forceOn_pair_eq hxy hx hy, add_sq_ennreal]
  ring

/-! ## 8. The same increment in the `flipDiff` shape of `QuadraticFlux` -/

/-- **The first-order flip difference of the cluster volume on the off-region.**  With `x` in
the cluster of `o`, `y` outside it and both volumes finite, flipping `s(x,y)` open changes the
real-valued cluster volume by exactly `|K_y|`.  This is the exact statement `Δ|K_o| = |K_y|`
for the pivotal edge. -/
theorem flipDiff_clusterVol_eq {o x y : V} {ω : Config V} (hxy : x ≠ y)
    (hx : x ∈ cluster ω o) (hy : y ∉ cluster ω o) (hK : clusterVol ω o ≠ ⊤)
    (hKy : clusterVol ω y ≠ ⊤) :
    flipDiff (fun η => (clusterVol η o).toReal) (s(x, y)) ω = (clusterVol ω y).toReal := by
  have he : s(x, y) ∉ ω := notMem_pair_of_mem_cluster_of_notMem hx hy
  unfold flipDiff
  rw [forceOn_singleton_self_eq_union he, forceOn_singleton_empty_eq_of_notMem he]
  change (clusterVol (ω ∪ {s(x, y)}) o).toReal - (clusterVol ω o).toReal
    = (clusterVol ω y).toReal
  rw [clusterVol_union_pair_eq hxy hx hy, ENNReal.toReal_add hK hKy]
  ring

/-- **The `p = 2` source increment on the off-region.**  Flipping the pivotal edge `s(x,y)` open
changes `|K_o|²` by exactly the source's `2|K||K_y| + |K_y|²`:

  `flipDiff (|K_o|²) e ω = 2|K_o||K_y| + |K_y|²`

with all volumes evaluated at the *closed* configuration `ω` (on the off-region the edge is
closed, so `ω` is that configuration).  Both the coefficient `2` and the squared term come from
`flipDiff_sq`; the merge identity supplies `Δ|K_o| = |K_y|`. -/
theorem flipDiff_clusterVol_sq_eq {o x y : V} {ω : Config V} (hxy : x ≠ y)
    (hx : x ∈ cluster ω o) (hy : y ∉ cluster ω o) (hK : clusterVol ω o ≠ ⊤)
    (hKy : clusterVol ω y ≠ ⊤) :
    flipDiff (fun η => (clusterVol η o).toReal ^ 2) (s(x, y)) ω
      = 2 * (clusterVol ω o).toReal * (clusterVol ω y).toReal
        + (clusterVol ω y).toReal ^ 2 := by
  have he : s(x, y) ∉ ω := notMem_pair_of_mem_cluster_of_notMem hx hy
  rw [flipDiff_sq (fun η => (clusterVol η o).toReal) (s(x, y)) ω,
    flipDiff_clusterVol_eq hxy hx hy hK hKy,
    forceOn_singleton_empty_eq_of_notMem he]

/-! ## 9. `ω` free: the same statements at the closed configuration

`flipDiff g e ω` compares `forceOn {e} {e} ω` with `forceOn {e} ∅ ω`, so the "closed"
configuration at which the merge happens is `forceOn {e} ∅ ω`, not `ω` itself.  The results of
this section are stated with `ω` free and the closed configuration written out, so that they can
be substituted into the `QuadraticFlux` identities verbatim. -/

/-- `forceOn {e} ∅` is idempotent. -/
theorem forceOn_singleton_empty_idem {e : Sym2 V} {ω : Config V} :
    forceOn {e} ∅ (forceOn {e} ∅ ω) = forceOn {e} ∅ ω := by
  ext e'
  by_cases hne : e' = e
  · subst hne; simp [forceOn]
  · simp [forceOn, hne]

/-- Closing and then opening `e` is opening `e`. -/
theorem forceOn_singleton_self_forceOn_empty {e : Sym2 V} {ω : Config V} :
    forceOn {e} {e} (forceOn {e} ∅ ω) = forceOn {e} {e} ω := by
  ext e'
  by_cases hne : e' = e
  · subst hne; simp [forceOn]
  · simp [forceOn, hne]

/-- The event "`x` lies in the cluster of `o`" is measurable after closing a fixed set of
edges. -/
theorem measurableSet_mem_cluster_forceOn (o x : V) (S : Set (Sym2 V)) :
    MeasurableSet {ω : Config V | x ∈ cluster (forceOn S ∅ ω) o} :=
  (measurableSet_cluster_mem o x).preimage (measurable_forceOn S ∅)

/-- **The volume identity at the closed configuration, `ω` free.** -/
theorem clusterVol_forceOn_flip_eq {o x y : V} {ω : Config V} (hxy : x ≠ y)
    (hx : x ∈ cluster (forceOn {s(x, y)} ∅ ω) o)
    (hy : y ∉ cluster (forceOn {s(x, y)} ∅ ω) o) :
    clusterVol (forceOn {s(x, y)} {s(x, y)} ω) o
      = clusterVol (forceOn {s(x, y)} ∅ ω) o
        + clusterVol (forceOn {s(x, y)} ∅ ω) y := by
  have h := clusterVol_forceOn_pair_eq (ω := forceOn {s(x, y)} ∅ ω) hxy hx hy
  rwa [forceOn_singleton_self_forceOn_empty] at h

/-- **`Δ|K_o| = |K_y|` on the off-region, `ω` free.** -/
theorem flipDiff_clusterVol_eq_free {o x y : V} {ω : Config V} (hxy : x ≠ y)
    (hx : x ∈ cluster (forceOn {s(x, y)} ∅ ω) o)
    (hy : y ∉ cluster (forceOn {s(x, y)} ∅ ω) o)
    (hK : clusterVol (forceOn {s(x, y)} ∅ ω) o ≠ ⊤)
    (hKy : clusterVol (forceOn {s(x, y)} ∅ ω) y ≠ ⊤) :
    flipDiff (fun η => (clusterVol η o).toReal) (s(x, y)) ω
      = (clusterVol (forceOn {s(x, y)} ∅ ω) y).toReal := by
  have hflip : flipDiff (fun η => (clusterVol η o).toReal) (s(x, y)) ω
      = flipDiff (fun η => (clusterVol η o).toReal) (s(x, y)) (forceOn {s(x, y)} ∅ ω) := by
    simp only [flipDiff, forceOn_singleton_self_forceOn_empty, forceOn_singleton_empty_idem]
  rw [hflip]
  exact flipDiff_clusterVol_eq hxy hx hy hK hKy

/-- **The `p = 2` source increment on the off-region, `ω` free.** -/
theorem flipDiff_clusterVol_sq_eq_free {o x y : V} {ω : Config V} (hxy : x ≠ y)
    (hx : x ∈ cluster (forceOn {s(x, y)} ∅ ω) o)
    (hy : y ∉ cluster (forceOn {s(x, y)} ∅ ω) o)
    (hK : clusterVol (forceOn {s(x, y)} ∅ ω) o ≠ ⊤)
    (hKy : clusterVol (forceOn {s(x, y)} ∅ ω) y ≠ ⊤) :
    flipDiff (fun η => (clusterVol η o).toReal ^ 2) (s(x, y)) ω
      = 2 * (clusterVol (forceOn {s(x, y)} ∅ ω) o).toReal
          * (clusterVol (forceOn {s(x, y)} ∅ ω) y).toReal
        + (clusterVol (forceOn {s(x, y)} ∅ ω) y).toReal ^ 2 := by
  have hflip : flipDiff (fun η => (clusterVol η o).toReal ^ 2) (s(x, y)) ω
      = flipDiff (fun η => (clusterVol η o).toReal ^ 2) (s(x, y)) (forceOn {s(x, y)} ∅ ω) := by
    simp only [flipDiff, forceOn_singleton_self_forceOn_empty, forceOn_singleton_empty_idem]
  rw [hflip]
  exact flipDiff_clusterVol_sq_eq hxy hx hy hK hKy

/-- **The `p = 2` increment on the off-region, as an integral over that region, `ω` free.**
The region is defined at the closed configuration `forceOn {s(x,y)} ∅ ω`, which is where the
pivot is evaluated. -/
theorem setIntegral_flipDiff_clusterVol_sq_eq_free (μ : Measure (Config V)) {o x y : V}
    (hxy : x ≠ y)
    (hK : ∀ ξ : Config V, x ∈ cluster ξ o → y ∉ cluster ξ o → clusterVol ξ o ≠ ⊤)
    (hKy : ∀ ξ : Config V, x ∈ cluster ξ o → y ∉ cluster ξ o → clusterVol ξ y ≠ ⊤) :
    ∫ ω in {ω : Config V | x ∈ cluster (forceOn {s(x, y)} ∅ ω) o ∧
              y ∉ cluster (forceOn {s(x, y)} ∅ ω) o},
        flipDiff (fun η => (clusterVol η o).toReal ^ 2) (s(x, y)) ω ∂μ
      = ∫ ω in {ω : Config V | x ∈ cluster (forceOn {s(x, y)} ∅ ω) o ∧
              y ∉ cluster (forceOn {s(x, y)} ∅ ω) o},
          (2 * (clusterVol (forceOn {s(x, y)} ∅ ω) o).toReal
              * (clusterVol (forceOn {s(x, y)} ∅ ω) y).toReal
            + (clusterVol (forceOn {s(x, y)} ∅ ω) y).toReal ^ 2) ∂μ := by
  refine setIntegral_congr_fun ?_ ?_
  · exact (measurableSet_mem_cluster_forceOn o x {s(x, y)}).inter
      (measurableSet_mem_cluster_forceOn o y {s(x, y)}).compl
  · intro ω hω
    exact flipDiff_clusterVol_sq_eq_free hxy hω.1 hω.2 (hK _ hω.1 hω.2) (hKy _ hω.1 hω.2)

/-! ## 10. The complete pointwise diagnosis of the single-edge `p = 2` increment -/

/-- If `x` and `y` are both outside the cluster of `o`, the edge `s(x,y)` does not touch that
cluster, so flipping it changes nothing. -/
theorem notMem_touchSet_pair {o x y : V} {ξ : Config V}
    (hx : x ∉ cluster ξ o) (hy : y ∉ cluster ξ o) : s(x, y) ∉ touchSet ξ o := by
  rw [mem_touchSet]
  rintro ⟨v, hv, hvc⟩
  rw [Sym2.mem_iff] at hv
  rcases hv with rfl | rfl
  · exact hx hvc
  · exact hy hvc

/-- The `p = 2` flip difference vanishes when the edge misses the cluster. -/
theorem flipDiff_clusterVol_sq_eq_zero_of_notMem_touchSet {o : V} {e : Sym2 V} {ξ : Config V}
    (h : e ∉ touchSet ξ o) :
    flipDiff (fun η => (clusterVol η o).toReal ^ 2) e ξ = 0 :=
  flipDiff_eq_zero (fun ω η hc => by rw [clusterVol_eq_encard, clusterVol_eq_encard, hc]) h

/-- The `p = 2` flip difference vanishes when both endpoints are already in the cluster (and the
edge is closed, so that flipping it is opening it). -/
theorem flipDiff_clusterVol_sq_eq_zero_of_mem_both {o x y : V} {ξ : Config V} (hxy : x ≠ y)
    (he : s(x, y) ∉ ξ) (hx : x ∈ cluster ξ o) (hy : y ∈ cluster ξ o) :
    flipDiff (fun η => (clusterVol η o).toReal ^ 2) (s(x, y)) ξ = 0 := by
  unfold flipDiff
  rw [forceOn_singleton_self_eq_union he, forceOn_singleton_empty_eq_of_notMem he]
  change (clusterVol (ξ ∪ {s(x, y)}) o).toReal ^ 2 - (clusterVol ξ o).toReal ^ 2 = 0
  rw [clusterVol_union_pair_eq_of_mem_cluster hxy hx hy]
  ring

/-- The `p = 2` flip difference vanishes when neither endpoint is in the cluster. -/
theorem flipDiff_clusterVol_sq_eq_zero_of_notMem_both {o x y : V} {ξ : Config V}
    (hx : x ∉ cluster ξ o) (hy : y ∉ cluster ξ o) :
    flipDiff (fun η => (clusterVol η o).toReal ^ 2) (s(x, y)) ξ = 0 :=
  flipDiff_clusterVol_sq_eq_zero_of_notMem_touchSet (notMem_touchSet_pair hx hy)

/-- The `p = 2` increment with the roles exchanged: only `y` is in the cluster of `o`. -/
theorem flipDiff_clusterVol_sq_eq_symm {o x y : V} {ξ : Config V} (hxy : x ≠ y)
    (hy : y ∈ cluster ξ o) (hx : x ∉ cluster ξ o) (hK : clusterVol ξ o ≠ ⊤)
    (hKx : clusterVol ξ x ≠ ⊤) :
    flipDiff (fun η => (clusterVol η o).toReal ^ 2) (s(x, y)) ξ
      = 2 * (clusterVol ξ o).toReal * (clusterVol ξ x).toReal
        + (clusterVol ξ x).toReal ^ 2 := by
  have h := flipDiff_clusterVol_sq_eq (x := y) (y := x) (ω := ξ) (o := o)
    hxy.symm hy hx hK hKx
  simpa [Sym2.eq_swap] using h

/-- **The complete pointwise `p = 2` increment of the cluster volume at a closed edge.**  For a
configuration `ξ` in which `s(x,y)` is closed and `x ≠ y`, the flip difference of `|K_o|²` is
exactly

* `0` if both endpoints are in the cluster of `o`;
* `2|K_o||K_y| + |K_y|²` if only `x` is;
* `2|K_o||K_x| + |K_x|²` if only `y` is;
* `0` if neither is.

This is the source's increment, as a pointwise identity, with no radius, no majorant and no
truncation.  It also shows that the off-region hypothesis is not removable: the value differs in
the other three cases. -/
theorem flipDiff_clusterVol_sq_eq_cases {o x y : V} {ξ : Config V} (hxy : x ≠ y)
    (he : s(x, y) ∉ ξ) (hK : clusterVol ξ o ≠ ⊤) (hKx : clusterVol ξ x ≠ ⊤)
    (hKy : clusterVol ξ y ≠ ⊤) :
    flipDiff (fun η => (clusterVol η o).toReal ^ 2) (s(x, y)) ξ
      = if x ∈ cluster ξ o then
          (if y ∈ cluster ξ o then 0 else
            2 * (clusterVol ξ o).toReal * (clusterVol ξ y).toReal
              + (clusterVol ξ y).toReal ^ 2)
        else if y ∈ cluster ξ o then
          2 * (clusterVol ξ o).toReal * (clusterVol ξ x).toReal
            + (clusterVol ξ x).toReal ^ 2
        else 0 := by
  by_cases hx : x ∈ cluster ξ o <;> by_cases hy : y ∈ cluster ξ o
  · simp only [hx, hy, ite_true]
    exact flipDiff_clusterVol_sq_eq_zero_of_mem_both hxy he hx hy
  · simp only [hx, hy, ite_true]
    exact flipDiff_clusterVol_sq_eq hxy hx hy hK hKy
  · simp only [hx, hy, ite_true, ite_false]
    exact flipDiff_clusterVol_sq_eq_symm hxy hy hx hK hKx
  · simp only [hx, hy, ite_true, ite_false]
    exact flipDiff_clusterVol_sq_eq_zero_of_notMem_both hx hy

/-- **The source increment on the off-region, at the level of the integral over that region.**
On the event `{x ∈ K_o, y ∉ K_o}` the `p = 2` flip difference *is* `2|K|K_y + |K_y|²`, so the
integral of the flip difference over that event is the integral of the source's increment.

Nothing is claimed about the complementary event (where the increment is one of the other three
values in `flipDiff_clusterVol_sq_eq_cases`), and no radius differentiation enters. -/
theorem setIntegral_flipDiff_clusterVol_sq_eq (μ : Measure (Config V)) {o x y : V}
    (hxy : x ≠ y)
    (hK : ∀ ξ : Config V, x ∈ cluster ξ o → y ∉ cluster ξ o → clusterVol ξ o ≠ ⊤)
    (hKy : ∀ ξ : Config V, x ∈ cluster ξ o → y ∉ cluster ξ o → clusterVol ξ y ≠ ⊤) :
    ∫ ξ in {ξ : Config V | x ∈ cluster ξ o ∧ y ∉ cluster ξ o},
        flipDiff (fun η => (clusterVol η o).toReal ^ 2) (s(x, y)) ξ ∂μ
      = ∫ ξ in {ξ : Config V | x ∈ cluster ξ o ∧ y ∉ cluster ξ o},
          (2 * (clusterVol ξ o).toReal * (clusterVol ξ y).toReal
            + (clusterVol ξ y).toReal ^ 2) ∂μ := by
  refine setIntegral_congr_fun ?_ ?_
  · exact (measurableSet_cluster_mem o x).inter (measurableSet_cluster_mem o y).compl
  · intro ξ hξ
    exact flipDiff_clusterVol_sq_eq hxy hξ.1 hξ.2 (hK ξ hξ.1 hξ.2) (hKy ξ hξ.1 hξ.2)

/-! ## 11. The hypothesis is not removable -/

/-- **Counterexample.**  Without the hypothesis `x ∈ cluster ω o` the merge identity is false.
Take `ω = ∅` on `ℕ`, `o = 0`, `x = 1`, `y = 2`: the edge `s(1,2)` does not touch the cluster
`{0}` of `0`, so opening it changes nothing, while the right-hand side of the merge identity
would add the cluster `{2}` of `y`.  (Checked, so that no unconditional version of the identity
can be quoted by accident.) -/
theorem not_cluster_union_pair_eq_of_notMem_cluster :
    ¬ (cluster ((∅ : Config ℕ) ∪ {s((1 : ℕ), 2)}) 0
        = cluster (∅ : Config ℕ) 0 ∪ cluster (∅ : Config ℕ) 2) := by
  intro h
  have hmem : (2 : ℕ) ∈ cluster ((∅ : Config ℕ) ∪ {s((1 : ℕ), 2)}) 0 := by
    rw [h]
    exact Or.inr (cluster_mem_self _ _)
  have htouch : s((1 : ℕ), 2) ∉ touchSet (∅ : Config ℕ) 0 := by
    rw [mem_touchSet]
    rintro ⟨v, hv, hvc⟩
    rw [cluster_empty] at hvc
    rw [Sym2.mem_iff] at hv
    rcases hv with rfl | rfl
    · simp at hvc
    · simp at hvc
  rw [cluster_union_singleton_eq htouch, cluster_empty] at hmem
  simp at hmem

end PercLib.CriticalLRP
