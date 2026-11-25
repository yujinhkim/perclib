/- Integrated from independently rebuilt Ultramath work.
Production base 3b6ff818cd3ac1a9cee99dcfff154a2ff4f85095.
Scratch source: ../../.ultramath/smwvp122a/m3/ProofTree.lean.
-/

module

public import PercLib.CriticalLRP.Correlation.FourPoint.ProofMetric
public import PercLib.CriticalLRP.Correlation.FourPoint.ProofArms
public import Mathlib.Combinatorics.SimpleGraph.Acyclic

/-!
The four-point cover in a tree.

Given four vertices `o, x, y, z` of a tree, the branch-point decomposition
(`exists_three_arm_data`) produces a centre `w` and three pairwise edge-disjoint geodesics
`Aₓ, A_y, A_z` from `w` to the terminals.  Since the graph is a tree, those arms are the unique
simple paths from `w`, so two of them may meet outside `w` only if they share an edge.

The one remaining input is where the root `o` attaches.  Two geodesics ending at `w` share an edge
only if they share their last edge; consequently at most one terminal can be "bad", meaning that
the arm to it shares an edge with the path to `o` (two bad terminals would share the last edge of
the path to `o`, contradicting the edge-disjointness of the arms).  Choosing the bad terminal, if
it exists, as the joint terminal `t` and the other two as `u, v`, every distance identity required
by `disjoint_of_dist_add` holds:

* `dist u v = dist u w + dist w v` and the identities with `t` in place of `v`, because the arms
  are pairwise edge-disjoint;
* `dist u o = dist u w + dist w o` (and the same for `v`) because `u` and `v` are not bad.

The bad case is genuinely needed: on a path `o — x — y — z` the centre is `y` and the joint
terminal is `x`, the "arm" to `y` itself being empty.
-/

@[expose] public section

set_option linter.unusedSectionVars false
set_option linter.unusedDecidableInType false

namespace PercLib.CriticalLRP.FourPoint

variable {V : Type*}

/-- In a tree, every path is a shortest walk. -/
theorem path_length_eq_dist {T : SimpleGraph V} (hT : T.IsTree) {a b : V}
    {p : T.Walk a b} (hp : p.IsPath) : p.length = T.dist a b := by
  obtain ⟨q, hq, hql⟩ := (hT.connected a b).exists_path_of_dist
  rw [← hql, (hT.existsUnique_path a b).unique hp hq]

/-- The last vertex of the vertex list of a walk is its endpoint. -/
theorem getLast?_support {G : SimpleGraph V} {u v : V} (p : G.Walk u v) :
    p.support.getLast? = some v := by
  induction p with
  | nil => rfl
  | @cons u v w h p ih =>
    rw [SimpleGraph.Walk.support_cons, List.getLast?_cons, ih]
    rfl

/-- A vertex of `l.dropLast` is not the last vertex of the nodup list `l`. -/
theorem ne_of_mem_dropLast {l : List V} {v z : V} (hlast : l.getLast? = some z)
    (hnd : l.Nodup) (hv : v ∈ l.dropLast) : v ≠ z := by
  obtain ⟨l', hl'⟩ := List.getLast?_eq_some_iff.mp hlast
  rw [hl', List.dropLast_concat] at hv
  rw [hl', List.nodup_append] at hnd
  rintro rfl
  exact hnd.2.2 v hv v (by simp) rfl

section
variable [DecidableEq V]

/-- **Two paths from a common vertex that meet again share their first edge.** -/
theorem head?_eq_of_meet {T : SimpleGraph V} (hT : T.IsTree) {w a b : V}
    {p : T.Walk w a} {q : T.Walk w b} (hp : p.IsPath) (hq : q.IsPath)
    {v : V} (hvp : v ∈ p.support) (hvq : v ∈ q.support) (hvw : v ≠ w) :
    p.edges.head? = q.edges.head? := by
  have hp1 : (p.takeUntil v hvp).IsPath :=
    SimpleGraph.Walk.isPath_of_isSubwalk (SimpleGraph.Walk.isSubwalk_takeUntil p hvp) hp
  have hq1 : (q.takeUntil v hvq).IsPath :=
    SimpleGraph.Walk.isPath_of_isSubwalk (SimpleGraph.Walk.isSubwalk_takeUntil q hvq) hq
  have heq : p.takeUntil v hvp = q.takeUntil v hvq :=
    (hT.existsUnique_path w v).unique hp1 hq1
  have hne : (p.takeUntil v hvp).edges ≠ [] := by
    intro hnil
    have h0 : (p.takeUntil v hvp).length = 0 := by
      rw [← SimpleGraph.Walk.length_edges, hnil]
      rfl
    exact hvw (SimpleGraph.Walk.eq_of_length_eq_zero h0).symm
  have hne' : (q.takeUntil v hvq).edges ≠ [] := by
    rw [← heq]; exact hne
  have h1 : p.edges.head? = (p.takeUntil v hvp).edges.head? := by
    obtain ⟨t, ht⟩ := SimpleGraph.Walk.edges_takeUntil_prefix_edges p hvp
    rw [← ht, List.head?_append]
    cases h : (p.takeUntil v hvp).edges with
    | nil => exact False.elim (absurd h hne)
    | cons x xs => rfl
  have h2 : q.edges.head? = (q.takeUntil v hvq).edges.head? := by
    obtain ⟨t, ht⟩ := SimpleGraph.Walk.edges_takeUntil_prefix_edges q hvq
    rw [← ht, List.head?_append]
    cases h : (q.takeUntil v hvq).edges with
    | nil => exact False.elim (absurd h hne')
    | cons x xs => rfl
  rw [h1, h2, heq]

/-- **Two paths ending at a common vertex that meet elsewhere share their last edge.** -/
theorem getLast?_eq_of_meet {T : SimpleGraph V} (hT : T.IsTree) {w a b : V}
    {p : T.Walk a w} {q : T.Walk b w} (hp : p.IsPath) (hq : q.IsPath)
    {v : V} (hvp : v ∈ p.support) (hvq : v ∈ q.support) (hvw : v ≠ w) :
    p.edges.getLast? = q.edges.getLast? := by
  have h := head?_eq_of_meet hT hp.reverse hq.reverse (by simpa using hvp)
    (by simpa using hvq) hvw
  simpa [SimpleGraph.Walk.edges_reverse, List.head?_reverse] using h

/-- Edge-disjoint paths from `w` in a tree meet only at `w`. -/
theorem supp_eq_of_edges_disjoint {T : SimpleGraph V} (hT : T.IsTree) {w a b : V}
    {p : T.Walk w a} {q : T.Walk w b} (hp : p.IsPath) (hq : q.IsPath)
    (hd : p.edges.Disjoint q.edges) {v : V} (hvp : v ∈ p.support) (hvq : v ∈ q.support) :
    v = w := by
  by_contra hne
  have hhead := head?_eq_of_meet hT hp hq hvp hvq hne
  have hne_p : (p.takeUntil v hvp).edges ≠ [] := by
    intro hnil
    have h0 : (p.takeUntil v hvp).length = 0 := by
      rw [← SimpleGraph.Walk.length_edges, hnil]
      rfl
    exact hne (SimpleGraph.Walk.eq_of_length_eq_zero h0).symm
  obtain ⟨e, hes⟩ : ∃ e, (p.takeUntil v hvp).edges.head? = some e := by
    cases h : (p.takeUntil v hvp).edges with
    | nil => exact False.elim (absurd h hne_p)
    | cons x xs => exact ⟨x, rfl⟩
  have h1 : p.edges.head? = (p.takeUntil v hvp).edges.head? := by
    obtain ⟨t, ht⟩ := SimpleGraph.Walk.edges_takeUntil_prefix_edges p hvp
    rw [← ht, List.head?_append]
    cases h : (p.takeUntil v hvp).edges with
    | nil => exact False.elim (absurd h hne_p)
    | cons x xs => rfl
  have hpe : e ∈ p.edges := by
    have hheadp : p.edges.head? = some e := by rw [h1, hes]
    obtain ⟨ys, hys⟩ := List.head?_eq_some_iff.mp hheadp
    rw [hys]
    exact List.mem_cons_self ..
  have hqe : e ∈ q.edges := by
    have hqhead : q.edges.head? = some e := by
      rw [← hhead]
      rw [h1, hes]
    obtain ⟨ys, hys⟩ := List.head?_eq_some_iff.mp hqhead
    rw [hys]
    exact List.mem_cons_self ..
  exact (List.disjoint_left.mp hd hpe) hqe

/-- Edge-disjoint geodesics from a common vertex in a tree put the centre between their
endpoints. -/
theorem between_of_edges_disjoint {T : SimpleGraph V} (hT : T.IsTree) {w a b : V}
    {p : T.Walk a w} {q : T.Walk b w} (hp : p.IsPath) (hq : q.IsPath)
    (hd : p.edges.Disjoint q.edges) :
    T.dist a b = T.dist a w + T.dist w b := by
  have hpa : p.length = T.dist a w := path_length_eq_dist hT hp
  have hqb : q.length = T.dist b w := path_length_eq_dist hT hq
  have hdq : p.reverse.edges.Disjoint q.reverse.edges := by
    rw [SimpleGraph.Walk.edges_reverse, SimpleGraph.Walk.edges_reverse, List.disjoint_left]
    intro e he he'
    exact (List.disjoint_left.mp hd) (by simpa using he) (by simpa using he')
  have hpath : (p.append q.reverse).IsPath := by
    rw [SimpleGraph.Walk.isPath_append']
    refine ⟨hp.dropLast, hq.reverse, ?_⟩
    rw [List.disjoint_left]
    intro v hv hvq
    have hv' : v ∈ p.support := List.mem_of_mem_dropLast hv
    have hvw : v = w := supp_eq_of_edges_disjoint hT hp.reverse hq.reverse hdq
      (by simpa using hv') (by simpa using hvq)
    exact ne_of_mem_dropLast (getLast?_support p) hp.support_nodup hv hvw
  have hlen := path_length_eq_dist hT hpath
  rw [SimpleGraph.Walk.length_append, SimpleGraph.Walk.length_reverse, hpa, hqb] at hlen
  rw [← hlen, SimpleGraph.dist_comm (u := b) (v := w)]

/-- **The root attaches to at most one arm.**  If the arm to `s` shares an edge with the path to
`o`, then the two share their last edge at `w`. -/
theorem getLast?_eq_of_fail {T : SimpleGraph V} (hT : T.IsTree) {o s w : V}
    {A : T.Walk s w} {Po : T.Walk o w} (hA : A.IsPath) (hPo : Po.IsPath)
    (hAl : A.length = T.dist s w) (hPol : Po.length = T.dist o w)
    (hfail : T.dist o s < T.dist o w + T.dist w s) :
    A.edges.getLast? = Po.edges.getLast? := by
  have hlen : (A.append Po.reverse).length = T.dist s w + T.dist o w := by
    rw [SimpleGraph.Walk.length_append, SimpleGraph.Walk.length_reverse, hAl, hPol]
  have hnp : ¬ (A.append Po.reverse).IsPath := by
    intro hp
    have h2 := path_length_eq_dist hT hp
    rw [hlen] at h2
    have hso : T.dist s o = T.dist o s := SimpleGraph.dist_comm
    have hsw : T.dist s w = T.dist w s := SimpleGraph.dist_comm
    omega
  rw [SimpleGraph.Walk.isPath_append'] at hnp
  have hdisj : ¬ A.support.dropLast.Disjoint Po.reverse.support :=
    fun h => hnp ⟨hA.dropLast, hPo.reverse, h⟩
  rw [List.disjoint_left] at hdisj
  push Not at hdisj
  obtain ⟨v, hvA, hvP⟩ := hdisj
  have hvw : v ≠ w := ne_of_mem_dropLast (getLast?_support A) hA.support_nodup hvA
  exact getLast?_eq_of_meet hT hA hPo (List.mem_of_mem_dropLast hvA) (by simpa using hvP) hvw

/-- Assembly step: given the centre `w`, the root arm `Po`, the three arms and the two terminals
`u`, `v` that are not "bad", the five betweenness identities hold and the cover data follows. -/
theorem cover_of_choice {T : SimpleGraph V} (hT : T.IsTree) {o w t u v : V}
    {Po : T.Walk o w} {At : T.Walk t w} {Au : T.Walk u w} {Av : T.Walk v w}
    (hPol : Po.length = T.dist o w)
    (hAtl : At.length = T.dist t w) (hAul : Au.length = T.dist u w)
    (hAvl : Av.length = T.dist v w)
    (hAtp : At.IsPath) (hAup : Au.IsPath) (hAvp : Av.IsPath)
    (hAtu : At.edges.Disjoint Au.edges) (hAtv : At.edges.Disjoint Av.edges)
    (hAuv : Au.edges.Disjoint Av.edges)
    (hu : ¬ (T.dist o u < T.dist o w + T.dist w u))
    (hv : ¬ (T.dist o v < T.dist o w + T.dist w v)) :
    (Po.edges ++ At.edges).Disjoint Au.edges ∧
      (Po.edges ++ At.edges).Disjoint Av.edges ∧ Au.edges.Disjoint Av.edges := by
  have hwu : T.dist w u = T.dist u w := SimpleGraph.dist_comm
  have hwv : T.dist w v = T.dist v w := SimpleGraph.dist_comm
  have hwo : T.dist w o = T.dist o w := SimpleGraph.dist_comm
  have h1 : T.dist u v = T.dist u w + T.dist w v :=
    between_of_edges_disjoint hT hAup hAvp hAuv
  have h3 : T.dist u t = T.dist u w + T.dist w t :=
    between_of_edges_disjoint hT hAup hAtp hAtu.symm
  have h5 : T.dist v t = T.dist v w + T.dist w t :=
    between_of_edges_disjoint hT hAvp hAtp hAtv.symm
  have htri_u := (hT.connected o w).dist_triangle_left u
  have htri_v := (hT.connected o w).dist_triangle_left v
  have h2 : T.dist u o = T.dist u w + T.dist w o := by
    rw [SimpleGraph.dist_comm (u := u) (v := o)]
    omega
  have h4 : T.dist v o = T.dist v w + T.dist w o := by
    rw [SimpleGraph.dist_comm (u := v) (v := o)]
    omega
  exact disjoint_of_dist_add Po hPol At hAtl Au hAul Av hAvl h1 h2 h3 h4 h5

/-- **The four-point cover in a tree.** -/
theorem tree_cover {T : SimpleGraph V} (hT : T.IsTree) (o x y z : V) : HasCover T o x y z := by
  classical
  obtain ⟨w, Ax, Ay, Az, hAxp, hAyp, hAzp, hAxl, hAyl, hAzl, hAxe, hAye, hAze⟩ :=
    exists_three_arm_data (G := T) (hT.connected x y) (hT.connected x z)
  obtain ⟨Po, hPop, hPol⟩ := (hT.connected o w).exists_path_of_dist
  have notboth : ∀ {s₁ s₂ : V} {A₁ : T.Walk s₁ w} {A₂ : T.Walk s₂ w},
      A₁.IsPath → A₂.IsPath → A₁.length = T.dist s₁ w → A₂.length = T.dist s₂ w →
      A₁.edges.Disjoint A₂.edges →
      ¬ (T.dist o s₁ < T.dist o w + T.dist w s₁ ∧
        T.dist o s₂ < T.dist o w + T.dist w s₂) := by
    intro s₁ s₂ A₁ A₂ hp₁ hp₂ hl₁ hl₂ hd hboth
    obtain ⟨hf₁, hf₂⟩ := hboth
    have h₁ := getLast?_eq_of_fail hT hp₁ hPop hl₁ hPol hf₁
    have h₂ := getLast?_eq_of_fail hT hp₂ hPop hl₂ hPol hf₂
    have hne : Po.edges ≠ [] := by
      intro hnil
      have hlen0 : Po.length = 0 := by
        rw [← SimpleGraph.Walk.length_edges, hnil]
        rfl
      have how : o = w := SimpleGraph.Walk.eq_of_length_eq_zero hlen0
      rw [← how, SimpleGraph.dist_self] at hf₁
      omega
    obtain ⟨e, he⟩ : ∃ e, Po.edges.getLast? = some e :=
      ⟨Po.edges.getLast hne, List.getLast?_eq_some_getLast hne⟩
    have hmem : ∀ {s : V} {A : T.Walk s w}, A.edges.getLast? = Po.edges.getLast? → e ∈ A.edges := by
      intro s A hA
      obtain ⟨ys, hys⟩ := List.getLast?_eq_some_iff.mp (by rw [hA, he])
      rw [hys]
      exact List.mem_append_right _ (List.mem_singleton_self e)
    exact (List.disjoint_left.mp hd (hmem h₁)) (hmem h₂)
  by_cases hfx : T.dist o x < T.dist o w + T.dist w x
  · have hny : ¬ (T.dist o y < T.dist o w + T.dist w y) :=
      fun h => notboth hAyp hAxp hAyl hAxl hAxe.symm ⟨h, hfx⟩
    have hnz : ¬ (T.dist o z < T.dist o w + T.dist w z) :=
      fun h => notboth hAzp hAxp hAzl hAxl hAye.symm ⟨h, hfx⟩
    exact ⟨w, x, y, z, Po, Ax, Ay, Az, rfl,
      cover_of_choice hT hPol hAxl hAyl hAzl hAxp hAyp hAzp hAxe hAye hAze hny hnz⟩
  · by_cases hfy : T.dist o y < T.dist o w + T.dist w y
    · have hnx : ¬ (T.dist o x < T.dist o w + T.dist w x) := hfx
      have hnz : ¬ (T.dist o z < T.dist o w + T.dist w z) :=
        fun h => notboth hAzp hAyp hAzl hAyl hAze.symm ⟨h, hfy⟩
      refine ⟨w, y, x, z, Po, Ay, Ax, Az, ?_,
        cover_of_choice hT hPol hAyl hAxl hAzl hAyp hAxp hAzp hAxe.symm hAze hAye hnx hnz⟩
      ext a
      simp only [Finset.mem_insert, Finset.mem_singleton]
      tauto
    · by_cases hfz : T.dist o z < T.dist o w + T.dist w z
      · have hnx : ¬ (T.dist o x < T.dist o w + T.dist w x) := hfx
        have hny : ¬ (T.dist o y < T.dist o w + T.dist w y) := hfy
        refine ⟨w, z, x, y, Po, Az, Ax, Ay, ?_,
          cover_of_choice hT hPol hAzl hAxl hAyl hAzp hAxp hAyp hAye.symm hAze.symm hAxe
            hnx hny⟩
        ext a
        simp only [Finset.mem_insert, Finset.mem_singleton]
        tauto
      · exact ⟨w, x, y, z, Po, Ax, Ay, Az, rfl,
          cover_of_choice hT hPol hAxl hAyl hAzl hAxp hAyp hAzp hAxe hAye hAze hfy hfz⟩

end

end PercLib.CriticalLRP.FourPoint
