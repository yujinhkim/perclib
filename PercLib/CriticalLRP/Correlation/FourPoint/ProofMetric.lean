/- Integrated from independently rebuilt Ultramath work.
Production base 3b6ff818cd3ac1a9cee99dcfff154a2ff4f85095.
Scratch source: ../../.ultramath/smwvp122a/m3/ProofMetric.lean.
-/

module

public import PercLib.CriticalLRP.Correlation.FourPoint.Defs

/-!
The metric edge-disjointness criterion.

If four walks `P : o → w`, `Q : t → w`, `R : u → w`, `S : v → w` are geodesics (their lengths are
the graph distances) and the pair distances among the endpoints are the sums of the distances to
`w` (`u` and `v` "see `w` between them and `o`", etc.), then the concatenated walk
`u → w → v` has length `dist u v`, hence is a path, hence has no repeated edge; so the edge lists
of `R` and `S` are disjoint, and the same argument with `u → w → o`, `u → w → t`, `v → w → o`,
`v → w → t` breaks the edge lists of both `P` and `Q` away from `R` and from `S`.

This is the only place where distances are used: the cover is then reduced to finding a centre
`w` and a partition for which these five betweenness identities hold.
-/

@[expose] public section

namespace PercLib.CriticalLRP.FourPoint

variable {V : Type*}

theorem disjoint_of_dist_add {G : SimpleGraph V} {o t u v w : V}
    (P : G.Walk o w) (hP : P.length = G.dist o w)
    (Q : G.Walk t w) (hQ : Q.length = G.dist t w)
    (R : G.Walk u w) (hR : R.length = G.dist u w)
    (S : G.Walk v w) (hS : S.length = G.dist v w)
    (h1 : G.dist u v = G.dist u w + G.dist w v)
    (h2 : G.dist u o = G.dist u w + G.dist w o)
    (h3 : G.dist u t = G.dist u w + G.dist w t)
    (h4 : G.dist v o = G.dist v w + G.dist w o)
    (h5 : G.dist v t = G.dist v w + G.dist w t) :
    (P.edges ++ Q.edges).Disjoint R.edges ∧ (P.edges ++ Q.edges).Disjoint S.edges ∧
      R.edges.Disjoint S.edges := by
  have key : ∀ ⦃a b : V⦄ (A : G.Walk a w) (B : G.Walk b w), A.length = G.dist a w →
      B.length = G.dist b w → G.dist a b = G.dist a w + G.dist w b →
      A.edges.Disjoint B.edges := by
    intro a b A B hA hB hd
    have hlen : (A.append B.reverse).length = G.dist a b := by
      rw [SimpleGraph.Walk.length_append, SimpleGraph.Walk.length_reverse, hA, hB, hd,
        SimpleGraph.dist_comm (u := b) (v := w)]
    have hpath : (A.append B.reverse).IsPath :=
      SimpleGraph.Walk.isPath_of_length_eq_dist _ hlen
    have htr : (A.append B.reverse).IsTrail := hpath.isTrail
    have hdisj := ((SimpleGraph.Walk.isTrail_append A B.reverse).mp htr).2.2
    rw [List.disjoint_left] at hdisj
    rw [List.disjoint_left]
    intro e heA heB
    exact hdisj heA (by simpa using heB)
  refine ⟨?_, ?_, key R S hR hS h1⟩
  · rw [List.disjoint_append_left]
    exact ⟨(key R P hR hP h2).symm, (key R Q hR hQ h3).symm⟩
  · rw [List.disjoint_append_left]
    exact ⟨(key S P hS hP h4).symm, (key S Q hS hQ h5).symm⟩

end PercLib.CriticalLRP.FourPoint
