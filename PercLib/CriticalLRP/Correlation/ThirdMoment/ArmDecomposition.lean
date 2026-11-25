/-
Migration source: https://github.com/yujinhkim/Critical-Long-range-percolation
Integration revision: 3b3d1d0e43ef940bfaa2292ee5c2ee094ac4edbf
Licence: Apache-2.0 for the PercLib Lean sources and tooling; see third_party/critical-lrp/.
-/

module

/-
Swarm `smwj645my`, member `m1` (direction d2).

The remaining deterministic hypothesis of the infinite-native third-moment reduction
(`four_point_of_arm_decomposition` / `third_moment_le_of_arm_decomposition` in
`PercLib.CriticalLRP.Correlation.ThirdMoment`) is discharged here:

> four vertices in one component of a graph admit one of the three labelled binary trees on
> those four leaves with five pairwise edge-disjoint walks (`ShapeWitness`).

The route is *not* Steiner-tree minimality.  We take the three-arm branch-point decomposition of
the triangle `(y,z,w)` (`exists_three_arms`, restated for an arbitrary `SimpleGraph` and
strengthened to yield path arms with pairwise vertex-disjoint supports), and then attach the
fourth vertex `root` by a **shortest walk into the union of the three arms**.  The endvertex `t`
of that shortest walk is the new first branch vertex `u`: the arm whose support contains `t` is
split into `t → terminal` and `t → v`, and the remaining two arms stay whole.  Whichever of the
three arms contains `t` determines which of the three labellings of the binary tree is realised.

No finiteness hypothesis on the graph is used anywhere: only that walks are finite objects.
-/
public import PercLib.CriticalLRP.Correlation.ThirdMoment
public import PercLib.CriticalLRP.TreeGraph.Connectivity

open Set MeasureTheory
open scoped ENNReal
open PercLib.Percolation.Bond PercLib.CriticalLRP.TreeExpansion

@[expose] public section

namespace PercLib.CriticalLRP.TreeExpansion

variable {V : Type*}

/-! ### Walks whose supports meet in a single vertex have disjoint edge lists -/

/-- If the supports of two walks meet only in the vertex `x`, then their edge lists are disjoint.
(An edge shared by both walks would have both endpoints in the intersection, hence would be a
loop, which no walk edge is.) -/
theorem edges_disjoint_of_support_inter {G : SimpleGraph V} {a b c d x : V}
    (P : G.Walk a b) (Q : G.Walk c d)
    (h : ∀ u, u ∈ P.support → u ∈ Q.support → u = x) : P.edges.Disjoint Q.edges := by
  rw [List.disjoint_left]
  intro e heP heQ
  induction e using Sym2.ind with
  | h m n =>
    have hne : m ≠ n := (P.adj_of_mem_edges heP).ne
    have hm : m = x :=
      h m (P.mem_support_of_mem_edges heP (Sym2.mem_mk_left m n))
        (Q.mem_support_of_mem_edges heQ (Sym2.mem_mk_left m n))
    have hn : n = x :=
      h n (P.mem_support_of_mem_edges heP (Sym2.mem_mk_right m n))
        (Q.mem_support_of_mem_edges heQ (Sym2.mem_mk_right m n))
    exact hne (hm.trans hn.symm)

/-- Edge lists of a prefix and the complementary suffix of a *path* are disjoint. -/
theorem edges_takeUntil_disjoint_dropUntil {G : SimpleGraph V} [DecidableEq V] {a b : V}
    (p : G.Walk a b) (hpn : p.support.Nodup) {t : V} (ht : t ∈ p.support) :
    (p.takeUntil t ht).edges.Disjoint (p.dropUntil t ht).edges := by
  have hspec : (p.takeUntil t ht).edges ++ (p.dropUntil t ht).edges = p.edges := by
    rw [← SimpleGraph.Walk.edges_append, SimpleGraph.Walk.take_spec]
  have hnodup : p.edges.Nodup := SimpleGraph.Walk.edges_nodup_of_support_nodup hpn
  rw [← hspec] at hnodup
  exact List.Nodup.disjoint hnodup

/-! ### Three-arm decomposition in an arbitrary simple graph -/

/-- **Three-arm (branch-point) decomposition, general form.**  If `x`, `y` and `z` lie in a
common component of an arbitrary simple graph `G`, there are a vertex `c` and three arms
`x → c`, `y → c`, `z → c` that are paths, have pairwise disjoint edge lists, and whose supports
meet only in `c`.

This is the statement of `PercLib.CriticalLRP.TreeGraph.exists_three_arms` (the minimality
argument is that of that file, applied to an arbitrary `SimpleGraph` rather than to the open
graph of a finite configuration) with two strengthenings: the vertex-disjointness of the
supports, and the reduction of each arm to a path by `SimpleGraph.Walk.bypass`. -/
theorem exists_three_arms_general {G : SimpleGraph V} {x y z : V}
    (hxy : G.Reachable x y) (hxz : G.Reachable x z) :
    ∃ (c : V) (p : G.Walk x c) (q : G.Walk y c) (r : G.Walk z c),
      p.edges.Disjoint q.edges ∧ p.edges.Disjoint r.edges ∧ q.edges.Disjoint r.edges ∧
      p.support.Nodup ∧ q.support.Nodup ∧ r.support.Nodup ∧
      (∀ u, u ∈ p.support → u ∈ q.support → u = c) ∧
      (∀ u, u ∈ p.support → u ∈ r.support → u = c) ∧
      (∀ u, u ∈ q.support → u ∈ r.support → u = c) := by
  classical
  obtain ⟨pxy⟩ := hxy
  obtain ⟨pxz⟩ := hxz
  have hex : ∃ n : ℕ, ∃ (c : V) (p : G.Walk x c) (q : G.Walk y c) (r : G.Walk z c),
      p.length + q.length + r.length ≤ n :=
    ⟨pxy.length + pxz.length, x, SimpleGraph.Walk.nil, pxy.reverse, pxz.reverse, by simp⟩
  obtain ⟨c, p, q, r, hle⟩ := Nat.find_spec hex
  have hmin : ∀ (c' : V) (p' : G.Walk x c') (q' : G.Walk y c') (r' : G.Walk z c'),
      Nat.find hex ≤ p'.length + q'.length + r'.length :=
    fun c' p' q' r' => Nat.find_min' hex ⟨c', p', q', r', Nat.le_refl _⟩
  have hpq : ∀ {u : V}, u ∈ p.support → u ∈ q.support → u = c := by
    intro u huP huQ
    by_contra hne
    have hlt := PercLib.CriticalLRP.TreeGraph.shorten_total p q r huP huQ hne
    have hge := hmin u (p.takeUntil u huP) (q.takeUntil u huQ)
      (r.append (p.dropUntil u huP).reverse)
    omega
  have hpr : ∀ {u : V}, u ∈ p.support → u ∈ r.support → u = c := by
    intro u huP huR
    by_contra hne
    have hlt := PercLib.CriticalLRP.TreeGraph.shorten_total p r q huP huR hne
    have hge := hmin u (p.takeUntil u huP) (q.append (p.dropUntil u huP).reverse)
      (r.takeUntil u huR)
    omega
  have hqr : ∀ {u : V}, u ∈ q.support → u ∈ r.support → u = c := by
    intro u huQ huR
    by_contra hne
    have hlt := PercLib.CriticalLRP.TreeGraph.shorten_total q r p huQ huR hne
    have hge := hmin u (p.append (q.dropUntil u huQ).reverse) (q.takeUntil u huQ)
      (r.takeUntil u huR)
    omega
  have hd_pq : p.edges.Disjoint q.edges :=
    edges_disjoint_of_support_inter p q fun u hu hu' => hpq hu hu'
  have hd_pr : p.edges.Disjoint r.edges :=
    edges_disjoint_of_support_inter p r fun u hu hu' => hpr hu hu'
  have hd_qr : q.edges.Disjoint r.edges :=
    edges_disjoint_of_support_inter q r fun u hu hu' => hqr hu hu'
  refine ⟨c, p.bypass, q.bypass, r.bypass, ?_, ?_, ?_,
    (SimpleGraph.Walk.isPath_def _).mp (SimpleGraph.Walk.bypass_isPath p),
    (SimpleGraph.Walk.isPath_def _).mp (SimpleGraph.Walk.bypass_isPath q),
    (SimpleGraph.Walk.isPath_def _).mp (SimpleGraph.Walk.bypass_isPath r), ?_, ?_, ?_⟩
  · exact fun a ha ha' => hd_pq (p.edges_bypass_subset_edges ha) (q.edges_bypass_subset_edges ha')
  · exact fun a ha ha' => hd_pr (p.edges_bypass_subset_edges ha) (r.edges_bypass_subset_edges ha')
  · exact fun a ha ha' => hd_qr (q.edges_bypass_subset_edges ha) (r.edges_bypass_subset_edges ha')
  · exact fun u hu hu' => hpq (p.support_bypass_subset_support hu) (q.support_bypass_subset_support hu')
  · exact fun u hu hu' => hpr (p.support_bypass_subset_support hu) (r.support_bypass_subset_support hu')
  · exact fun u hu hu' => hqr (q.support_bypass_subset_support hu) (r.support_bypass_subset_support hu')


/-! ### Monotonicity helpers for `List.Disjoint` -/

theorem disjoint_of_subset_left {α : Type*} {l₁ l₁' l₂ : List α}
    (hsub : ∀ a ∈ l₁, a ∈ l₁') (h : l₁'.Disjoint l₂) : l₁.Disjoint l₂ :=
  fun a ha ha' => h (hsub a ha) ha'

theorem disjoint_of_subset_right {α : Type*} {l₁ l₂ l₂' : List α}
    (hsub : ∀ a ∈ l₂, a ∈ l₂') (h : l₁.Disjoint l₂') : l₁.Disjoint l₂ :=
  fun _a ha ha' => h ha (hsub _a ha')

theorem disjoint_symm' {α : Type*} (l₁ l₂ : List α) (h : l₁.Disjoint l₂) : l₂.Disjoint l₁ :=
  fun _a ha ha' => h ha' ha

theorem edges_takeUntil_subset {G : SimpleGraph V} [DecidableEq V] {a b : V}
    (p : G.Walk a b) {t : V} (ht : t ∈ p.support) :
    ∀ e ∈ (p.takeUntil t ht).edges, e ∈ p.edges := by
  intro e he
  have hspec : (p.takeUntil t ht).edges ++ (p.dropUntil t ht).edges = p.edges := by
    rw [← SimpleGraph.Walk.edges_append, SimpleGraph.Walk.take_spec]
  rw [← hspec]
  exact List.mem_append_left _ he

theorem edges_dropUntil_subset {G : SimpleGraph V} [DecidableEq V] {a b : V}
    (p : G.Walk a b) {t : V} (ht : t ∈ p.support) :
    ∀ e ∈ (p.dropUntil t ht).edges, e ∈ p.edges := by
  intro e he
  have hspec : (p.takeUntil t ht).edges ++ (p.dropUntil t ht).edges = p.edges := by
    rw [← SimpleGraph.Walk.edges_append, SimpleGraph.Walk.take_spec]
  rw [← hspec]
  exact List.mem_append_right _ he

/-! ### The binary-tree arm decomposition for four vertices in one component -/

/-- **`ShapeWitness` for four vertices in one component of an arbitrary simple graph.**

If `root`, `y`, `z`, `w` lie in one component of `G`, then one of the three labelled binary trees
on those four leaves is realised by five pairwise edge-disjoint walks: `root` and one of
`y, z, w` meet at a branch vertex `u`, and the remaining two meet at a branch vertex `v`, with a
spine `u → v`.  The degenerate case `u = v` (a star with four arms, empty spine) is included.

Which of the three labellings occurs is determined by which of the three arms of the branch-point
decomposition of `(y, z, w)` the shortest path from `root` enters first. -/
theorem shapeWitness_or {G : SimpleGraph V} {root y z w : V}
    (h0y : G.Reachable root y) (h0z : G.Reachable root z) (h0w : G.Reachable root w) :
    (∃ u v, ShapeWitness G root y z w u v) ∨
    (∃ u v, ShapeWitness G root z y w u v) ∨
    (∃ u v, ShapeWitness G root w y z u v) := by
  classical
  -- Three edge-disjoint path arms from the three terminals to a common branch point `c`.
  obtain ⟨c, p, q, s, hpq, hps, hqs, hpn, hqn, hsn, hpqS, hpsS, hqsS⟩ :=
    exists_three_arms_general (G := G) (x := y) (y := z) (z := w)
      (h0y.symm.trans h0z) (h0y.symm.trans h0w)
  -- The fourth terminal joins the union of the three arms by a shortest walk `Q`.
  obtain ⟨Qy⟩ := h0y
  have hex : ∃ n : ℕ, ∃ (t : V) (Q : G.Walk root t),
      (t ∈ p.support ∨ t ∈ q.support ∨ t ∈ s.support) ∧ Q.length ≤ n :=
    ⟨Qy.length, y, Qy, Or.inl p.start_mem_support, Nat.le_refl _⟩
  obtain ⟨t, Q, htS, hQle⟩ := Nat.find_spec hex
  have hmin : ∀ (t' : V) (Q' : G.Walk root t'),
      (t' ∈ p.support ∨ t' ∈ q.support ∨ t' ∈ s.support) → Nat.find hex ≤ Q'.length :=
    fun t' Q' h => Nat.find_min' hex ⟨t', Q', h, Nat.le_refl _⟩
  -- Hence `Q` meets the arms only in its final vertex `t`.
  have hQmeet : ∀ u, u ∈ Q.support →
      (u ∈ p.support ∨ u ∈ q.support ∨ u ∈ s.support) → u = t := by
    intro u hu huS
    by_contra hne
    have hspec := congrArg SimpleGraph.Walk.length (SimpleGraph.Walk.take_spec (p := Q) hu)
    rw [SimpleGraph.Walk.length_append] at hspec
    have hpos : 0 < (Q.dropUntil u hu).length :=
      PercLib.CriticalLRP.TreeGraph.length_pos_of_ne (Q.dropUntil u hu) hne
    have hge := hmin u (Q.takeUntil u hu) huS
    omega
  have hQp : Q.edges.Disjoint p.edges :=
    edges_disjoint_of_support_inter Q p fun u hu hu' => hQmeet u hu (Or.inl hu')
  have hQq : Q.edges.Disjoint q.edges :=
    edges_disjoint_of_support_inter Q q fun u hu hu' => hQmeet u hu (Or.inr (Or.inl hu'))
  have hQs : Q.edges.Disjoint s.edges :=
    edges_disjoint_of_support_inter Q s fun u hu hu' => hQmeet u hu (Or.inr (Or.inr hu'))
  rcases htS with ht | ht | ht
  · -- `t` lies on the arm to `y`: `root` and `y` branch at `u = t`.
    refine Or.inl ⟨t, c, Q, p.takeUntil t ht, q, s, p.dropUntil t ht,
      ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
    · exact disjoint_of_subset_right (edges_takeUntil_subset p ht) hQp
    · exact hQq
    · exact hQs
    · exact disjoint_of_subset_right (edges_dropUntil_subset p ht) hQp
    · exact disjoint_of_subset_left (edges_takeUntil_subset p ht) hpq
    · exact disjoint_of_subset_left (edges_takeUntil_subset p ht) hps
    · exact edges_takeUntil_disjoint_dropUntil p hpn ht
    · exact hqs
    · exact disjoint_of_subset_right (edges_dropUntil_subset p ht)
        (disjoint_symm' p.edges q.edges hpq)
    · exact disjoint_of_subset_right (edges_dropUntil_subset p ht)
        (disjoint_symm' p.edges s.edges hps)
  · -- `t` lies on the arm to `z`: the labelling `(root, z, y, w)` is realised.
    refine Or.inr (Or.inl ⟨t, c, Q, q.takeUntil t ht, p, s, q.dropUntil t ht,
      ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩)
    · exact disjoint_of_subset_right (edges_takeUntil_subset q ht) hQq
    · exact hQp
    · exact hQs
    · exact disjoint_of_subset_right (edges_dropUntil_subset q ht) hQq
    · exact disjoint_of_subset_left (edges_takeUntil_subset q ht) (disjoint_symm' _ _ hpq)
    · exact disjoint_of_subset_left (edges_takeUntil_subset q ht) hqs
    · exact edges_takeUntil_disjoint_dropUntil q hqn ht
    · exact hps
    · exact disjoint_of_subset_right (edges_dropUntil_subset q ht) hpq
    · exact disjoint_of_subset_right (edges_dropUntil_subset q ht)
        (disjoint_symm' q.edges s.edges hqs)
  · -- `t` lies on the arm to `w`: the labelling `(root, w, y, z)` is realised.
    refine Or.inr (Or.inr ⟨t, c, Q, s.takeUntil t ht, p, q, s.dropUntil t ht,
      ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩)
    · exact disjoint_of_subset_right (edges_takeUntil_subset s ht) hQs
    · exact hQp
    · exact hQq
    · exact disjoint_of_subset_right (edges_dropUntil_subset s ht) hQs
    · exact disjoint_of_subset_left (edges_takeUntil_subset s ht) (disjoint_symm' _ _ hps)
    · exact disjoint_of_subset_left (edges_takeUntil_subset s ht)
        (disjoint_symm' q.edges s.edges hqs)
    · exact edges_takeUntil_disjoint_dropUntil s hsn ht
    · exact hpq
    · exact disjoint_of_subset_right (edges_dropUntil_subset s ht) hps
    · exact disjoint_of_subset_right (edges_dropUntil_subset s ht) hqs


/-! ### The native statements: the arm hypothesis discharged, unconditionally -/

namespace Native

set_option linter.unusedSectionVars false

variable {V : Type*} [Countable V]

/-- **The deterministic binary-arm hypothesis, proved.**  In every configuration `ω` in which
`root, y, z, w` are connected, one of the three labelled binary trees on those four leaves is
realised by five pairwise edge-disjoint walks of the open graph.  (This is the `harm` hypothesis
of `four_point_of_arm_decomposition`, with no remaining hypothesis.) -/
theorem arm_decomposition_native (root y z w : V) (ω : PercLib.CriticalLRP.Config V)
    (h0y : PercLib.CriticalLRP.Connects ω root y)
    (h0z : PercLib.CriticalLRP.Connects ω root z)
    (h0w : PercLib.CriticalLRP.Connects ω root w) :
    (∃ u v, ShapeWitness (PercLib.CriticalLRP.openGraph ω) root y z w u v) ∨
    (∃ u v, ShapeWitness (PercLib.CriticalLRP.openGraph ω) root z y w u v) ∨
    (∃ u v, ShapeWitness (PercLib.CriticalLRP.openGraph ω) root w y z u v) :=
  shapeWitness_or h0y h0z h0w

/-- The pointwise four-point tree-graph inequality (I.2.2) at `k = 3`, with no hypothesis beyond
the four vertices being labelled. -/
theorem four_point_native (π : Sym2 V → unitInterval) (root y z w : V) :
    law π (conn root y ∩ conn root z ∩ conn root w)
      ≤ ∑' u, ∑' v,
          (tau π root u * tau π u v * (tau π u y * tau π z v * tau π v w)
            + tau π root u * tau π u v * (tau π u z * tau π y v * tau π v w)
            + tau π root u * tau π u v * (tau π u w * tau π y v * tau π v z)) :=
  four_point_of_arm_decomposition π root y z w
    fun ω h1 h2 h3 => arm_decomposition_native root y z w ω h1 h2 h3

/-- **The infinite-native third cluster moment, unconditionally.**

For Bernoulli bond percolation with edge law `law π` on a countable abelian group whose
two-point function is translation invariant, `E|K_0|³ ≤ 3 (E|K_0|)⁵`.  No finiteness of
`E|K_0|` is needed and no deterministic hypothesis remains: the binary-arm decomposition is
proved in `shapeWitness_or`. -/
theorem third_moment_native [AddCommGroup V] (π : Sym2 V → unitInterval)
    (hinv : ∀ a b : V, tau π a b = tau π 0 (b - a)) :
    ∫⁻ ω, (PercLib.CriticalLRP.Percolation.cardFun (cluster ω 0)) ^ 3 ∂(law π)
      ≤ 3 * (∫⁻ ω, PercLib.CriticalLRP.Percolation.cardFun (cluster ω 0) ∂(law π)) ^ 5 :=
  third_moment_le_of_arm_decomposition π hinv fun y z w ω h1 h2 h3 =>
    arm_decomposition_native 0 y z w ω h1 h2 h3

end Native

end PercLib.CriticalLRP.TreeExpansion
