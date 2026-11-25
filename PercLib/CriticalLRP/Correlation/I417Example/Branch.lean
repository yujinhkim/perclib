/- Integrated from independently rebuilt Ultramath work, base revision 75f8858d8e30ea17b20f9ff1d216bc1508c01ce2.
Scratch source: ../../.ultramath/smwpxw774/m1/S474A/Branch.lean ; module path rewritten only.
-/

/-
# The two-level branch decomposition behind the three-terminal tree-graph bound

Deterministic content of direction A.  Given a configuration `ω` in which `x` is connected to
`w`, to `x₁` and to `x₂`, we produce one of the three five-edge tree structures of
`I417Example/Defs.lean`, each as a *five-fold disjoint occurrence*:

* `D2 u v`  — `x→u`, `u→w`, `u→v`, `v→x₁`, `v→x₂`  (the case `v = u` is included: then the
  `u→v` arm is trivial),
* `D3a u v` — `x→v`, `v→u`, `u→w`, `u→x₁`, `v→x₂`,
* `D3b u v` — `x→u`, `u→v`, `v→w`, `u→x₁`, `v→x₂`.

Construction.  Take a simple open path `P : x → w` and let `S` be its vertex set.  A first hit
(`exists_first_hit`) of a walk `x₁ → x` against `S` produces `u ∈ S` with a walk `u → x₁` whose
vertices other than `u` avoid `S`.  A first hit of a walk `x₂ → u` against
`S ∪ supp (u → x₁)` produces `b` with a walk `b → x₂` avoiding `S ∪ supp (u → x₁)` except at
`b`.  The three cases are: `b` on the arm `u → x₁` (`D2`), `u` after `b` on `P` (`D3a`), and
`u` before `b` on `P` (`D3b`).

Disjointness of the five witnesses is by endpoint regions: edges of `P` have both endpoints in
`S`; edges of the `u → x₁` arm have both endpoints in `{u} ∪ Sᶜ` (hence in `S ∪ supp(u → x₁)`);
edges of the `b → x₂` arm have both endpoints in `{b} ∪ (S ∪ supp(u → x₁))ᶜ`.  Two edge sets
whose endpoint regions meet in at most one vertex are disjoint, since an edge of a walk has two
distinct endpoints.

No `sorry`, no custom axioms; no definitions.
-/
module

public import PercLib.CriticalLRP.Correlation.I417Example.Defs

open MeasureTheory Measure ProbabilityTheory unitInterval
open scoped ENNReal NNReal

set_option linter.unusedSectionVars false

@[expose] public section

namespace PercLib.CriticalLRP.I417Example

variable {V : Type*} [Countable V] [DecidableEq V]

/-! ## Edge-set disjointness tools -/

/-- A `List.Disjoint` pair of edge lists has disjoint edge finsets. -/
theorem edgeFinset_disjoint_of_list_disjoint {V : Type*} {l₁ l₂ : List (Sym2 V)}
    (h : l₁.Disjoint l₂) : Disjoint (edgeFinset l₁) (edgeFinset l₂) := by
  classical
  rw [Finset.disjoint_left]
  intro a ha hb
  exact List.disjoint_left.mp h (mem_edgeFinset.mp ha) (mem_edgeFinset.mp hb)

/-- If every edge of `p` has both endpoints in `W`, every edge of `q` has both endpoints in
`W'`, and `W ∩ W'` has at most one point, then the edge sets of `p` and `q` are disjoint. -/
theorem edges_disjoint_of_regions {a b c d : V} {p : (⊤ : SimpleGraph V).Walk a b}
    {q : (⊤ : SimpleGraph V).Walk c d} {W W' : Set V} {z : V}
    (hp : ∀ e ∈ p.edges, ∀ v ∈ e, v ∈ W) (hq : ∀ e ∈ q.edges, ∀ v ∈ e, v ∈ W')
    (hz : ∀ v ∈ W, v ∈ W' → v = z) :
    Disjoint (edgeFinset p.edges) (edgeFinset q.edges) := by
  classical
  rw [Finset.disjoint_left]
  intro e he he'
  rw [mem_edgeFinset] at he he'
  induction e using Sym2.ind with
  | _ r s =>
      have hrW : r ∈ W := hp _ he r (Sym2.mem_mk_left r s)
      have hsW : s ∈ W := hp _ he s (Sym2.mem_mk_right r s)
      have hrW' : r ∈ W' := hq _ he' r (Sym2.mem_mk_left r s)
      have hsW' : s ∈ W' := hq _ he' s (Sym2.mem_mk_right r s)
      have h1 : r = z := hz r hrW hrW'
      have h2 : s = z := hz s hsW hsW'
      have hadj : (⊤ : SimpleGraph V).Adj r s := SimpleGraph.Walk.adj_of_mem_edges p he
      exact (SimpleGraph.top_adj r s).1 hadj (by rw [h1, h2])

/-- Three walks whose edge lists concatenate to a nodup list have pairwise disjoint edge
sets. -/
theorem edges_disjoint_three {a b c d : V} {p : (⊤ : SimpleGraph V).Walk a b}
    {q : (⊤ : SimpleGraph V).Walk b c} {r : (⊤ : SimpleGraph V).Walk c d}
    (h : ((p.edges ++ q.edges) ++ r.edges).Nodup) :
    Disjoint (edgeFinset p.edges) (edgeFinset q.edges) ∧
      Disjoint (edgeFinset p.edges) (edgeFinset r.edges) ∧
      Disjoint (edgeFinset q.edges) (edgeFinset r.edges) := by
  classical
  obtain ⟨hn1, -, hd1⟩ := List.nodup_append'.mp h
  obtain ⟨-, -, hd2⟩ := List.nodup_append'.mp hn1
  have hd1' : p.edges.Disjoint r.edges := fun {_} ha => hd1 (List.mem_append_left q.edges ha)
  have hd1'' : q.edges.Disjoint r.edges := fun {_} ha => hd1 (List.mem_append_right p.edges ha)
  exact ⟨edgeFinset_disjoint_of_list_disjoint hd2, edgeFinset_disjoint_of_list_disjoint hd1',
    edgeFinset_disjoint_of_list_disjoint hd1''⟩

/-- Support splitting: a vertex of `p` not on the initial segment up to `z` lies on the final
segment from `z`. -/
theorem mem_dropUntil_of_notMem_takeUntil {a b : V} {p : (⊤ : SimpleGraph V).Walk a b} {z v : V}
    (hz : z ∈ p.support) (hv : v ∈ p.support) (hv' : v ∉ (p.takeUntil z hz).support) :
    v ∈ (p.dropUntil z hz).support := by
  classical
  have hsupp : (p.takeUntil z hz).support ++ (p.dropUntil z hz).support.tail = p.support := by
    rw [← SimpleGraph.Walk.support_append, SimpleGraph.Walk.take_spec]
  rw [← hsupp] at hv
  rcases List.mem_append.mp hv with h | h
  · exact absurd h hv'
  · exact List.mem_of_mem_tail h

/-- Support splitting, mirror form: a vertex of `p` not on the final segment from `z` lies on
the initial segment up to `z`. -/
theorem mem_takeUntil_of_notMem_dropUntil {a b : V} {p : (⊤ : SimpleGraph V).Walk a b} {z v : V}
    (hz : z ∈ p.support) (hv : v ∈ p.support) (hv' : v ∉ (p.dropUntil z hz).support) :
    v ∈ (p.takeUntil z hz).support := by
  classical
  have hsupp : (p.takeUntil z hz).support ++ (p.dropUntil z hz).support.tail = p.support := by
    rw [← SimpleGraph.Walk.support_append, SimpleGraph.Walk.take_spec]
  rw [← hsupp] at hv
  rcases List.mem_append.mp hv with h | h
  · exact h
  · exact absurd (List.mem_of_mem_tail h) hv'

/-! ## Assembling a five-edge diagram from five walks -/

/-- Five walks that all consist of open edges and whose edge sets are pairwise disjoint realise
the five-fold disjoint occurrence of the five connection events. -/
theorem tree5_mem_of_walks {ω : Config V} {a b c d e f g h i j : V}
    {p₁ : (⊤ : SimpleGraph V).Walk a b} {p₂ : (⊤ : SimpleGraph V).Walk c d}
    {p₃ : (⊤ : SimpleGraph V).Walk e f} {p₄ : (⊤ : SimpleGraph V).Walk g h}
    {p₅ : (⊤ : SimpleGraph V).Walk i j}
    (m₁ : ∀ x ∈ p₁.edges, x ∈ ω) (m₂ : ∀ x ∈ p₂.edges, x ∈ ω)
    (m₃ : ∀ x ∈ p₃.edges, x ∈ ω) (m₄ : ∀ x ∈ p₄.edges, x ∈ ω)
    (m₅ : ∀ x ∈ p₅.edges, x ∈ ω)
    (d₁₂ : Disjoint (edgeFinset p₁.edges) (edgeFinset p₂.edges))
    (d₁₃ : Disjoint (edgeFinset p₁.edges) (edgeFinset p₃.edges))
    (d₁₄ : Disjoint (edgeFinset p₁.edges) (edgeFinset p₄.edges))
    (d₁₅ : Disjoint (edgeFinset p₁.edges) (edgeFinset p₅.edges))
    (d₂₃ : Disjoint (edgeFinset p₂.edges) (edgeFinset p₃.edges))
    (d₂₄ : Disjoint (edgeFinset p₂.edges) (edgeFinset p₄.edges))
    (d₂₅ : Disjoint (edgeFinset p₂.edges) (edgeFinset p₅.edges))
    (d₃₄ : Disjoint (edgeFinset p₃.edges) (edgeFinset p₄.edges))
    (d₃₅ : Disjoint (edgeFinset p₃.edges) (edgeFinset p₅.edges))
    (d₄₅ : Disjoint (edgeFinset p₄.edges) (edgeFinset p₅.edges)) :
    Tree5 (connSet a b) (connSet c d) (connSet e f) (connSet g h) (connSet i j) ω := by
  classical
  refine ⟨![(edgeFinset p₁.edges), (edgeFinset p₂.edges), (edgeFinset p₃.edges), (edgeFinset p₄.edges),
    (edgeFinset p₅.edges)], ?_, ?_, ?_⟩
  · intro k
    fin_cases k
    · intro x hx; exact m₁ x (mem_edgeFinset.mp hx)
    · intro x hx; exact m₂ x (mem_edgeFinset.mp hx)
    · intro x hx; exact m₃ x (mem_edgeFinset.mp hx)
    · intro x hx; exact m₄ x (mem_edgeFinset.mp hx)
    · intro x hx; exact m₅ x (mem_edgeFinset.mp hx)
  · intro k
    fin_cases k
    · exact pathConnects_iff.mp ⟨p₁, fun x hx => mem_edgeFinset.mpr hx⟩
    · exact pathConnects_iff.mp ⟨p₂, fun x hx => mem_edgeFinset.mpr hx⟩
    · exact pathConnects_iff.mp ⟨p₃, fun x hx => mem_edgeFinset.mpr hx⟩
    · exact pathConnects_iff.mp ⟨p₄, fun x hx => mem_edgeFinset.mpr hx⟩
    · exact pathConnects_iff.mp ⟨p₅, fun x hx => mem_edgeFinset.mpr hx⟩
  · intro k l hkl
    fin_cases k <;> fin_cases l <;> simp_all [disjoint_comm]

/-! ## The decomposition -/

/-- **Two-level branch decomposition.**  If `x` is connected to `w`, `x₁` and `x₂`, then one of
the three five-edge tree structures occurs, with all five edge events occurring *disjointly*. -/
theorem exists_two_level_branch {ω : Config V} {x w x₁ x₂ : V}
    (hw : Connects ω x w) (h1 : Connects ω x x₁) (h2 : Connects ω x x₂) :
    (∃ u v : V, D2 x w x₁ x₂ u v ω) ∨ (∃ u v : V, D3a x w x₁ x₂ u v ω) ∨
      (∃ u v : V, D3b x w x₁ x₂ u v ω) := by
  classical
  obtain ⟨p0, hp0⟩ := pathConnects_iff.mpr hw
  set P : (⊤ : SimpleGraph V).Walk x w := p0.bypass with hPdef
  have hPpath : P.IsPath := SimpleGraph.Walk.bypass_isPath p0
  have hPedges : ∀ e ∈ P.edges, e ∈ ω :=
    fun e he => hp0 e (SimpleGraph.Walk.edges_bypass_subset_edges p0 he)
  set S : Set V := {v | v ∈ P.support} with hSdef
  have hxS : x ∈ S := SimpleGraph.Walk.start_mem_support P
  have hPinS : ∀ e ∈ P.edges, ∀ v ∈ e, v ∈ S :=
    fun e he v hv =>
      SimpleGraph.Walk.mem_support_iff_exists_mem_edges.mpr (Or.inr ⟨e, he, hv⟩)
  -- first hit of `x₁ → x` against `S`
  obtain ⟨R1, hR1⟩ := pathConnects_iff.mpr (connects_symm h1)
  obtain ⟨u, Q1₀, huS, hQ1₀edges, hQ1₀supp⟩ := exists_first_hit R1 hR1 S hxS
  set Q1 : (⊤ : SimpleGraph V).Walk u x₁ := Q1₀.bypass with hQ1def
  have hQ1path : Q1.IsPath := SimpleGraph.Walk.bypass_isPath Q1₀
  have hQ1edges : ∀ e ∈ Q1.edges, e ∈ ω :=
    fun e he => hQ1₀edges e (SimpleGraph.Walk.edges_bypass_subset_edges Q1₀ he)
  have hQ1supp : ∀ v ∈ Q1.support, v = u ∨ v ∉ S :=
    fun v hv => hQ1₀supp v (SimpleGraph.Walk.support_bypass_subset_support Q1₀ hv)
  have huP : u ∈ P.support := huS
  have hxu : Connects ω x u :=
    pathConnects_iff.mp ⟨P.takeUntil u huP,
      fun e he => hPedges e (SimpleGraph.Walk.edges_takeUntil_subset_edges P huP he)⟩
  set S₂ : Set V := {v | v ∈ S ∨ v ∈ Q1.support} with hS₂def
  have huS₂ : u ∈ S₂ := Or.inl huS
  have hx₂u : Connects ω x₂ u := connects_trans (connects_symm h2) hxu
  obtain ⟨R2, hR2⟩ := pathConnects_iff.mpr hx₂u
  obtain ⟨b, Q2₀, hbS₂, hQ2₀edges, hQ2₀supp⟩ := exists_first_hit R2 hR2 S₂ huS₂
  set Q2 : (⊤ : SimpleGraph V).Walk b x₂ := Q2₀.bypass with hQ2def
  have hQ2edges : ∀ e ∈ Q2.edges, e ∈ ω :=
    fun e he => hQ2₀edges e (SimpleGraph.Walk.edges_bypass_subset_edges Q2₀ he)
  have hQ2supp : ∀ v ∈ Q2.support, v = b ∨ v ∉ S₂ :=
    fun v hv => hQ2₀supp v (SimpleGraph.Walk.support_bypass_subset_support Q2₀ hv)
  -- endpoint regions of the `u → x₁` and `b → x₂` arms
  have hQ1inU : ∀ e ∈ Q1.edges, ∀ v ∈ e, v ∈ ({u} : Set V) ∪ Sᶜ := by
    intro e he v hv
    rcases hQ1supp v (SimpleGraph.Walk.mem_support_iff_exists_mem_edges.mpr
      (Or.inr ⟨e, he, hv⟩)) with h | h
    · subst h
      exact Or.inl (by simp)
    · exact Or.inr h
  have hQ1inS₂ : ∀ e ∈ Q1.edges, ∀ v ∈ e, v ∈ S₂ := by
    intro e he v hv
    rcases hQ1inU e he v hv with h | h
    · rw [Set.mem_singleton_iff] at h
      exact Or.inl (h.symm ▸ huS)
    · exact Or.inr (SimpleGraph.Walk.mem_support_iff_exists_mem_edges.mpr
        (Or.inr ⟨e, he, hv⟩))
  have hQ2inB : ∀ e ∈ Q2.edges, ∀ v ∈ e, v ∈ ({b} : Set V) ∪ S₂ᶜ := by
    intro e he v hv
    rcases hQ2supp v (SimpleGraph.Walk.mem_support_iff_exists_mem_edges.mpr
      (Or.inr ⟨e, he, hv⟩)) with h | h
    · subst h
      exact Or.inl (by simp)
    · exact Or.inr h
  -- region cross-facts, shared by all three cases
  have hSU : ∀ v ∈ S, v ∈ ({u} : Set V) ∪ Sᶜ → v = u := by
    rintro v hv (h | h)
    · simpa using h
    · exact absurd hv h
  have hSB : ∀ v ∈ S, v ∈ ({b} : Set V) ∪ S₂ᶜ → v = b := by
    rintro v hv (h | h)
    · simpa using h
    · exact absurd (Or.inl hv) h
  have hS₂B : ∀ v ∈ S₂, v ∈ ({b} : Set V) ∪ S₂ᶜ → v = b := by
    rintro v hv (h | h)
    · simpa using h
    · exact absurd hv h
  rcases hbS₂ with hbS | hbQ1
  · -- ============ `b` lies on the path `P` ============
    have hbP : b ∈ P.support := hbS
    by_cases hbdrop : u ∈ (P.dropUntil b hbP).support
    · -- ---- D3a: `u` comes after `b` on `P` ----
      have hsplit : (P.takeUntil b hbP).append (P.dropUntil b hbP) = P :=
        SimpleGraph.Walk.take_spec _ _
      have hsplit' : ((P.dropUntil b hbP).takeUntil u hbdrop).append
          ((P.dropUntil b hbP).dropUntil u hbdrop) = P.dropUntil b hbP :=
        SimpleGraph.Walk.take_spec _ _
      have hconcat : (P.takeUntil b hbP).edges ++
          ((P.dropUntil b hbP).takeUntil u hbdrop).edges ++
          ((P.dropUntil b hbP).dropUntil u hbdrop).edges = P.edges := by
        rw [List.append_assoc, ← SimpleGraph.Walk.edges_append,
          ← SimpleGraph.Walk.edges_append, hsplit', hsplit]
      obtain ⟨d₁₂, d₁₃, d₂₃⟩ :=
        edges_disjoint_three (by rw [hconcat]; exact hPpath.isTrail.edges_nodup)
      -- the three `P`-segments lie in `S`
      have hR1 : ∀ e ∈ (P.takeUntil b hbP).edges, ∀ v ∈ e, v ∈ S :=
        fun e he v hv => hPinS e (SimpleGraph.Walk.edges_takeUntil_subset_edges P hbP he) v hv
      have hR2 : ∀ e ∈ ((P.dropUntil b hbP).takeUntil u hbdrop).edges, ∀ v ∈ e, v ∈ S :=
        fun e he v hv => hPinS e (SimpleGraph.Walk.edges_dropUntil_subset_edges P hbP
          (SimpleGraph.Walk.edges_takeUntil_subset_edges (P.dropUntil b hbP) hbdrop he)) v hv
      have hR3 : ∀ e ∈ ((P.dropUntil b hbP).dropUntil u hbdrop).edges, ∀ v ∈ e, v ∈ S :=
        fun e he v hv => hPinS e (SimpleGraph.Walk.edges_dropUntil_subset_edges P hbP
          (SimpleGraph.Walk.edges_dropUntil_subset_edges (P.dropUntil b hbP) hbdrop he)) v hv
      refine Or.inr (Or.inl ⟨u, b, ?_⟩)
      exact tree5_mem_of_walks (p₁ := P.takeUntil b hbP)
        (p₂ := (P.dropUntil b hbP).takeUntil u hbdrop)
        (p₃ := (P.dropUntil b hbP).dropUntil u hbdrop) (p₄ := Q1) (p₅ := Q2)
        (fun e he => hPedges e (SimpleGraph.Walk.edges_takeUntil_subset_edges P hbP he))
        (fun e he => hPedges e (SimpleGraph.Walk.edges_dropUntil_subset_edges P hbP
          (SimpleGraph.Walk.edges_takeUntil_subset_edges (P.dropUntil b hbP) hbdrop he)))
        (fun e he => hPedges e (SimpleGraph.Walk.edges_dropUntil_subset_edges P hbP
          (SimpleGraph.Walk.edges_dropUntil_subset_edges (P.dropUntil b hbP) hbdrop he)))
        hQ1edges hQ2edges d₁₂ d₁₃
        (edges_disjoint_of_regions hR1 hQ1inU hSU)
        (edges_disjoint_of_regions hR1 hQ2inB hSB) d₂₃
        (edges_disjoint_of_regions hR2 hQ1inU hSU)
        (edges_disjoint_of_regions hR2 hQ2inB hSB)
        (edges_disjoint_of_regions hR3 hQ1inU hSU)
        (edges_disjoint_of_regions hR3 hQ2inB hSB)
        (edges_disjoint_of_regions hQ1inS₂ hQ2inB hS₂B)
    · -- ---- D3b: `u` comes before `b` on `P` ----
      have hutake : u ∈ (P.takeUntil b hbP).support :=
        mem_takeUntil_of_notMem_dropUntil hbP huP hbdrop
      have hsplit : (P.takeUntil b hbP).append (P.dropUntil b hbP) = P :=
        SimpleGraph.Walk.take_spec _ _
      have hsplit' : ((P.takeUntil b hbP).takeUntil u hutake).append
          ((P.takeUntil b hbP).dropUntil u hutake) = P.takeUntil b hbP :=
        SimpleGraph.Walk.take_spec _ _
      have hconcat : ((P.takeUntil b hbP).takeUntil u hutake).edges ++
          ((P.takeUntil b hbP).dropUntil u hutake).edges ++ (P.dropUntil b hbP).edges =
          P.edges := by
        rw [← SimpleGraph.Walk.edges_append, ← SimpleGraph.Walk.edges_append, hsplit', hsplit]
      obtain ⟨d₁₂, d₁₃, d₂₃⟩ :=
        edges_disjoint_three (by rw [hconcat]; exact hPpath.isTrail.edges_nodup)
      have hR1 : ∀ e ∈ ((P.takeUntil b hbP).takeUntil u hutake).edges, ∀ v ∈ e, v ∈ S :=
        fun e he v hv => hPinS e (SimpleGraph.Walk.edges_takeUntil_subset_edges P hbP
          (SimpleGraph.Walk.edges_takeUntil_subset_edges (P.takeUntil b hbP) hutake he)) v hv
      have hR2 : ∀ e ∈ ((P.takeUntil b hbP).dropUntil u hutake).edges, ∀ v ∈ e, v ∈ S :=
        fun e he v hv => hPinS e (SimpleGraph.Walk.edges_takeUntil_subset_edges P hbP
          (SimpleGraph.Walk.edges_dropUntil_subset_edges (P.takeUntil b hbP) hutake he)) v hv
      have hR3 : ∀ e ∈ (P.dropUntil b hbP).edges, ∀ v ∈ e, v ∈ S :=
        fun e he v hv => hPinS e (SimpleGraph.Walk.edges_dropUntil_subset_edges P hbP he) v hv
      refine Or.inr (Or.inr ⟨u, b, ?_⟩)
      exact tree5_mem_of_walks (p₁ := (P.takeUntil b hbP).takeUntil u hutake)
        (p₂ := (P.takeUntil b hbP).dropUntil u hutake)
        (p₃ := P.dropUntil b hbP) (p₄ := Q1) (p₅ := Q2)
        (fun e he => hPedges e (SimpleGraph.Walk.edges_takeUntil_subset_edges P hbP
          (SimpleGraph.Walk.edges_takeUntil_subset_edges (P.takeUntil b hbP) hutake he)))
        (fun e he => hPedges e (SimpleGraph.Walk.edges_takeUntil_subset_edges P hbP
          (SimpleGraph.Walk.edges_dropUntil_subset_edges (P.takeUntil b hbP) hutake he)))
        (fun e he => hPedges e (SimpleGraph.Walk.edges_dropUntil_subset_edges P hbP he))
        hQ1edges hQ2edges d₁₂ d₁₃
        (edges_disjoint_of_regions hR1 hQ1inU hSU)
        (edges_disjoint_of_regions hR1 hQ2inB hSB) d₂₃
        (edges_disjoint_of_regions hR2 hQ1inU hSU)
        (edges_disjoint_of_regions hR2 hQ2inB hSB)
        (edges_disjoint_of_regions hR3 hQ1inU hSU)
        (edges_disjoint_of_regions hR3 hQ2inB hSB)
        (edges_disjoint_of_regions hQ1inS₂ hQ2inB hS₂B)
  · -- ============ `b` lies on the arm `u → x₁` ============
    have hR1 : ∀ e ∈ (P.takeUntil u huP).edges, ∀ v ∈ e, v ∈ S :=
      fun e he v hv => hPinS e (SimpleGraph.Walk.edges_takeUntil_subset_edges P huP he) v hv
    have hR2 : ∀ e ∈ (P.dropUntil u huP).edges, ∀ v ∈ e, v ∈ S :=
      fun e he v hv => hPinS e (SimpleGraph.Walk.edges_dropUntil_subset_edges P huP he) v hv
    have hU1 : ∀ e ∈ (Q1.takeUntil b hbQ1).edges, ∀ v ∈ e, v ∈ ({u} : Set V) ∪ Sᶜ :=
      fun e he v hv => hQ1inU e (SimpleGraph.Walk.edges_takeUntil_subset_edges Q1 hbQ1 he) v hv
    have hU2 : ∀ e ∈ (Q1.dropUntil b hbQ1).edges, ∀ v ∈ e, v ∈ ({u} : Set V) ∪ Sᶜ :=
      fun e he v hv => hQ1inU e (SimpleGraph.Walk.edges_dropUntil_subset_edges Q1 hbQ1 he) v hv
    have hT1 : ∀ e ∈ (Q1.takeUntil b hbQ1).edges, ∀ v ∈ e, v ∈ S₂ :=
      fun e he v hv => hQ1inS₂ e (SimpleGraph.Walk.edges_takeUntil_subset_edges Q1 hbQ1 he) v hv
    have hT2 : ∀ e ∈ (Q1.dropUntil b hbQ1).edges, ∀ v ∈ e, v ∈ S₂ :=
      fun e he v hv => hQ1inS₂ e (SimpleGraph.Walk.edges_dropUntil_subset_edges Q1 hbQ1 he) v hv
    refine Or.inl ⟨u, b, ?_⟩
    exact tree5_mem_of_walks (p₁ := P.takeUntil u huP) (p₂ := P.dropUntil u huP)
      (p₃ := Q1.takeUntil b hbQ1) (p₄ := Q1.dropUntil b hbQ1) (p₅ := Q2)
      (fun e he => hPedges e (SimpleGraph.Walk.edges_takeUntil_subset_edges P huP he))
      (fun e he => hPedges e (SimpleGraph.Walk.edges_dropUntil_subset_edges P huP he))
      (fun e he => hQ1edges e (SimpleGraph.Walk.edges_takeUntil_subset_edges Q1 hbQ1 he))
      (fun e he => hQ1edges e (SimpleGraph.Walk.edges_dropUntil_subset_edges Q1 hbQ1 he))
      hQ2edges
      (edgeFinset_disjoint_of_list_disjoint
        (hPpath.isTrail.disjoint_edges_takeUntil_dropUntil huP))
      (edges_disjoint_of_regions hR1 hU1 hSU)
      (edges_disjoint_of_regions hR1 hU2 hSU)
      (edges_disjoint_of_regions hR1 hQ2inB hSB)
      (edges_disjoint_of_regions hR2 hU1 hSU)
      (edges_disjoint_of_regions hR2 hU2 hSU)
      (edges_disjoint_of_regions hR2 hQ2inB hSB)
      (edgeFinset_disjoint_of_list_disjoint
        (hQ1path.isTrail.disjoint_edges_takeUntil_dropUntil hbQ1))
      (edges_disjoint_of_regions hT1 hQ2inB hS₂B)
      (edges_disjoint_of_regions hT2 hQ2inB hS₂B)

end PercLib.CriticalLRP.I417Example
