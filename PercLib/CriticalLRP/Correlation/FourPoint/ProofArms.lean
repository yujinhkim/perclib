/- Integrated from independently rebuilt Ultramath work.
Production base 3b6ff818cd3ac1a9cee99dcfff154a2ff4f85095.
Scratch source: ../../.ultramath/smwvp122a/m3/ProofArms.lean.
-/

module

public import PercLib.CriticalLRP.Correlation.FourPoint.Defs

/-!
The branch-point (three-arm) decomposition with geodesic arms.

If `x`, `y` and `z` lie in a common component of a graph then there are walks from `x`, `y`, `z` to
a common vertex whose edge lists are pairwise disjoint and whose lengths are the three distances
to that vertex.  The proof is the minimality argument of the first tree-graph inequality: among all
triples of walks to a common vertex choose one of minimal total length; if two arms met at a vertex
`u ≠ w` then moving the centre to `u` and concatenating one arm with (a reverse of) the tail of
another gives a strictly shorter triple.  Minimality also forces each arm to be a shortest walk,
hence a path.

This is the deterministic input to the four-point cover: in a tree, the arms are the unique simple
paths from the centre to the three terminals.
-/

@[expose] public section

namespace PercLib.CriticalLRP.FourPoint

variable {V : Type*}

theorem length_pos_of_ne {G : SimpleGraph V} {u v : V} (p : G.Walk u v) (h : u ≠ v) :
    0 < p.length := by
  rcases Nat.eq_zero_or_pos p.length with h0 | h0
  · exact absurd (p.eq_of_length_eq_zero h0) h
  · exact h0

theorem mem_support_of_mem_edges {G : SimpleGraph V} {u v : V} {p : G.Walk u v} {e : Sym2 V}
    (he : e ∈ p.edges) {a : V} (ha : a ∈ e) : a ∈ p.support := by
  rw [SimpleGraph.Walk.mem_support_iff_exists_mem_edges]
  exact Or.inr ⟨e, he, ha⟩

section
variable [DecidableEq V]

/-- Length bookkeeping for the "move the centre" step: if the arms `P` (from `a`) and `Q` (from
`b`) meet at a vertex `u ≠ w`, then the triple consisting of `P` truncated at `u`, `Q` truncated at
`u` and the arm `R` extended along the tail of `P` has strictly smaller total length. -/
theorem shorten_total {G : SimpleGraph V} {a b c w : V}
    (P : G.Walk a w) (Q : G.Walk b w) (R : G.Walk c w) {u : V}
    (huP : u ∈ P.support) (huQ : u ∈ Q.support) (huw : u ≠ w) :
    (R.append (P.dropUntil u huP).reverse).length + (P.takeUntil u huP).length
        + (Q.takeUntil u huQ).length < P.length + Q.length + R.length := by
  have hR : (R.append (P.dropUntil u huP).reverse).length
      = R.length + (P.dropUntil u huP).length := by
    rw [SimpleGraph.Walk.length_append, SimpleGraph.Walk.length_reverse]
  have hP : (P.takeUntil u huP).length + (P.dropUntil u huP).length = P.length := by
    have h := congrArg SimpleGraph.Walk.length (SimpleGraph.Walk.take_spec (p := P) huP)
    rwa [SimpleGraph.Walk.length_append] at h
  have hQ : (Q.takeUntil u huQ).length + (Q.dropUntil u huQ).length = Q.length := by
    have h := congrArg SimpleGraph.Walk.length (SimpleGraph.Walk.take_spec (p := Q) huQ)
    rwa [SimpleGraph.Walk.length_append] at h
  have hpos : 0 < (Q.dropUntil u huQ).length := length_pos_of_ne _ huw
  omega

end

/-- **Branch-point decomposition with geodesic arms.**  If `x`, `y`, `z` lie in a common component,
there are a vertex `w` and shortest paths from `x`, `y`, `z` to `w` whose edge lists are pairwise
disjoint. -/
theorem exists_three_arm_data {G : SimpleGraph V} {x y z : V}
    (hxy : G.Reachable x y) (hxz : G.Reachable x z) : ThreeArmData G x y z := by
  classical
  obtain ⟨pxy⟩ := hxy
  obtain ⟨pxz⟩ := hxz
  have hex : ∃ n, ArmsGood G x y z n :=
    ⟨pxy.length + pxz.length, x, SimpleGraph.Walk.nil, pxy.reverse, pxz.reverse, by
      simp [SimpleGraph.Walk.length_reverse]⟩
  obtain ⟨w, p, q, r, hlen⟩ := Nat.find_spec hex
  have hmin : ∀ (w' : V) (p' : G.Walk x w') (q' : G.Walk y w') (r' : G.Walk z w'),
      Nat.find hex ≤ p'.length + q'.length + r'.length :=
    fun w' p' q' r' => Nat.find_min' hex ⟨w', p', q', r', rfl⟩
  have hpq : ∀ {u : V}, u ∈ p.support → u ∈ q.support → u = w := by
    intro u huP huQ
    by_contra hne
    have hlt := shorten_total p q r huP huQ hne
    have hge := hmin u (p.takeUntil u huP) (q.takeUntil u huQ)
      (r.append (p.dropUntil u huP).reverse)
    omega
  have hpr : ∀ {u : V}, u ∈ p.support → u ∈ r.support → u = w := by
    intro u huP huR
    by_contra hne
    have hlt := shorten_total p r q huP huR hne
    have hge := hmin u (p.takeUntil u huP) (q.append (p.dropUntil u huP).reverse)
      (r.takeUntil u huR)
    omega
  have hqr : ∀ {u : V}, u ∈ q.support → u ∈ r.support → u = w := by
    intro u huQ huR
    by_contra hne
    have hlt := shorten_total q r p huQ huR hne
    have hge := hmin u (p.append (q.dropUntil u huQ).reverse) (q.takeUntil u huQ)
      (r.takeUntil u huR)
    omega
  have hdisj : ∀ {a b : V} {p₁ : G.Walk a w} {p₂ : G.Walk b w},
      (∀ {u : V}, u ∈ p₁.support → u ∈ p₂.support → u = w) → p₁.edges.Disjoint p₂.edges := by
    intro a b p₁ p₂ hvw
    rw [List.disjoint_left]
    intro e he₁ he₂
    induction e using Sym2.ind with
    | h s t =>
      have hne : s ≠ t := (SimpleGraph.Walk.adj_of_mem_edges p₁ he₁).ne
      have h1 := hvw (mem_support_of_mem_edges he₁ (Sym2.mem_mk_left s t))
        (mem_support_of_mem_edges he₂ (Sym2.mem_mk_left s t))
      have h2 := hvw (mem_support_of_mem_edges he₁ (Sym2.mem_mk_right s t))
        (mem_support_of_mem_edges he₂ (Sym2.mem_mk_right s t))
      exact hne (h1.trans h2.symm)
  have hpg : p.length = G.dist x w := by
    obtain ⟨p', hp'⟩ := p.reachable.exists_walk_length_eq_dist
    by_contra hne
    have hlt : G.dist x w < p.length := lt_of_le_of_ne (SimpleGraph.dist_le p) (Ne.symm hne)
    have := hmin w p' q r
    omega
  have hqg : q.length = G.dist y w := by
    obtain ⟨q', hq'⟩ := q.reachable.exists_walk_length_eq_dist
    by_contra hne
    have hlt : G.dist y w < q.length := lt_of_le_of_ne (SimpleGraph.dist_le q) (Ne.symm hne)
    have := hmin w p q' r
    omega
  have hrg : r.length = G.dist z w := by
    obtain ⟨r', hr'⟩ := r.reachable.exists_walk_length_eq_dist
    by_contra hne
    have hlt : G.dist z w < r.length := lt_of_le_of_ne (SimpleGraph.dist_le r) (Ne.symm hne)
    have := hmin w p q r'
    omega
  exact ⟨w, p, q, r, SimpleGraph.Walk.isPath_of_length_eq_dist p hpg,
    SimpleGraph.Walk.isPath_of_length_eq_dist q hqg,
    SimpleGraph.Walk.isPath_of_length_eq_dist r hrg,
    hpg, hqg, hrg, hdisj hpq, hdisj hpr, hdisj hqr⟩

end PercLib.CriticalLRP.FourPoint
