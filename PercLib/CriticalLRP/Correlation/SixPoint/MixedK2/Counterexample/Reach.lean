/-
Coordinator-integrated from the independently rebuilt `smwxb4a1l/m3` Line6 artifact
at production base `8d1c9eb3738a26cc63afc07f525ba4af357bd905`.
-/
/-
Connectivity in the open subgraph of the six-vertex line.

Ultramath swarm `smwxb4a1l`, member `m3`, direction `HUB-LINK-COUNTEREXAMPLE`.

If the only possible open pairs are the five line edges `i—(i+1)`, the open graph is a
subgraph of the line `0—1—2—3—4—5`, and two vertices are connected exactly when every
line edge between them is open.
-/
module

public import PercLib.CriticalLRP.Correlation.SixPoint.MixedK2.Counterexample.Support

/-!
# Reachability on the line
-/

@[expose] public section

namespace PercLib.CriticalLRP.Counterexample.Line6

open Set MeasureTheory
open scoped ENNReal NNReal BigOperators
open PercLib.Percolation.Bond
open PercLib.Probability

/-! ## The five line edges -/

@[simp] theorem vt_val_eq (i : ℕ) (h : i < 6) : (vt i h).val = i := rfl

theorem peAt_val {i : ℕ} (hi : i < 5) : (vt i (by omega) : Fin 6).val = i := rfl

/-- The edge `i—(i+1)` is the unordered pair of the two vertices at positions `i`, `i+1`. -/
theorem peAt_eq {i : ℕ} (hi : i < 5) :
    peAt i hi = s(vt i (by omega), vt (i + 1) (by omega)) := rfl

/-- Distinct line indices give distinct line edges. -/
theorem peAt_inj {i j : ℕ} (hi : i < 5) (hj : j < 5) (h : peAt i hi = peAt j hj) : i = j := by
  have h' : s(vt i (by omega), vt (i + 1) (by omega))
      = s(vt j (by omega), vt (j + 1) (by omega)) := h
  rcases Sym2.eq_iff.mp h' with ⟨h1, h2⟩ | ⟨h1, h2⟩
  · exact Fin.ext_iff.mp h1
  · have h1' : i = j + 1 := Fin.ext_iff.mp h1
    have h2' : i + 1 = j := Fin.ext_iff.mp h2
    omega

/-- Membership in the line edge set. -/
theorem mem_lineEdges {e : Sym2 (Fin 6)} :
    e ∈ lineEdges ↔ ∃ (i : ℕ) (hi : i < 5), peAt i hi = e := by
  constructor
  · intro h
    simp only [lineEdges, Finset.mem_image] at h
    obtain ⟨p, _, hp⟩ := h
    exact ⟨p.val, by have := p.prop; simp only [Finset.mem_range] at this; omega, hp⟩
  · rintro ⟨i, hi, rfl⟩
    simp only [lineEdges, Finset.mem_image]
    exact ⟨⟨i, by simp only [Finset.mem_range]; omega⟩, by simp, rfl⟩

/-- A pair of vertices is a line edge exactly when the two positions differ by one. -/
theorem s_mem_lineEdges_iff {u v : Fin 6} :
    s(u, v) ∈ lineEdges ↔ v.val = u.val + 1 ∨ u.val = v.val + 1 := by
  constructor
  · intro h
    obtain ⟨i, hi, hpe⟩ := mem_lineEdges.mp h
    have h' : s(vt i (by omega), vt (i + 1) (by omega)) = s(u, v) := hpe
    rcases Sym2.eq_iff.mp h' with ⟨h1, h2⟩ | ⟨h1, h2⟩
    · left
      have h1' : i = u.val := Fin.ext_iff.mp h1
      have h2' : i + 1 = v.val := Fin.ext_iff.mp h2
      omega
    · right
      have h1' : i = v.val := Fin.ext_iff.mp h1
      have h2' : i + 1 = u.val := Fin.ext_iff.mp h2
      omega
  · rintro (h | h)
    · refine mem_lineEdges.mpr ⟨u.val, by omega, ?_⟩
      have h1 : vt u.val (by omega) = u := Fin.ext rfl
      have h2 : vt (u.val + 1) (by omega) = v := Fin.ext (by simp only [vt_val_eq]; omega)
      rw [peAt_eq, h1, h2]
    · refine mem_lineEdges.mpr ⟨v.val, by omega, ?_⟩
      have h1 : vt v.val (by omega) = v := Fin.ext rfl
      have h2 : vt (v.val + 1) (by omega) = u := Fin.ext (by simp only [vt_val_eq]; omega)
      rw [peAt_eq, h1, h2, Sym2.eq_swap]

/-! ## The spanned segment -/

/-- The line edge `i—(i+1)` lies in the segment spanned by `x` and `y` exactly when `i` is
between the two positions. -/
theorem mem_seg {x y : Fin 6} {i : ℕ} (hi : i < 5) :
    peAt i hi ∈ seg x y ↔ min x.val y.val ≤ i ∧ i < max x.val y.val := by
  constructor
  · intro h
    simp only [seg, Finset.mem_image] at h
    obtain ⟨p, _, hp⟩ := h
    have hp5 : p.val < 5 := by have := p.prop; simp only [Finset.mem_Ico] at this; omega
    have hval : p.val = i := peAt_inj hp5 hi hp
    have hprop := p.prop
    simp only [Finset.mem_Ico] at hprop
    omega
  · rintro ⟨h1, h2⟩
    simp only [seg, Finset.mem_image]
    refine ⟨⟨i, ?_⟩, by simp, ?_⟩
    · simp only [Finset.mem_Ico]; omega
    · rfl

/-- Every segment is a set of line edges. -/
theorem seg_subset_lineEdges (x y : Fin 6) : seg x y ⊆ lineEdges := by
  intro e he
  simp only [seg, Finset.mem_image] at he
  obtain ⟨p, _, hp⟩ := he
  have hp5 : p.val < 5 := by have := p.prop; simp only [Finset.mem_Ico] at this; omega
  exact hp ▸ mem_lineEdges.mpr ⟨p.val, hp5, rfl⟩

/-- The segment spanned by `x` and `y` has exactly `pdist x y` edges. -/
theorem seg_card (x y : Fin 6) : (seg x y).card = pdist x y := by
  rw [seg, Finset.card_image_of_injOn]
  · rw [Finset.card_attach, Nat.card_Ico]
    rfl
  · intro p _ q _ hpq
    have hp5 : p.val < 5 := by have := p.prop; simp only [Finset.mem_Ico] at this; omega
    have hq5 : q.val < 5 := by have := q.prop; simp only [Finset.mem_Ico] at this; omega
    exact Subtype.ext (peAt_inj hp5 hq5 hpq)

/-! ## Reachability -/

/-- A single open step moves by one position. -/
theorem adj_pos {ω : Set (Sym2 (Fin 6))} (hω : ω ⊆ (lineEdges : Set (Sym2 (Fin 6))))
    {u v : Fin 6} (h : (openGraph ω).Adj u v) :
    v.val = u.val + 1 ∨ u.val = v.val + 1 := by
  have hmem : s(u, v) ∈ ω := ((openGraph_adj_iff ω u v).mp h).1
  exact s_mem_lineEdges_iff.mp (hω hmem)

/-- Every line edge crossed by a connection is open. -/
theorem reach_forward {ω : Set (Sym2 (Fin 6))} (hω : ω ⊆ (lineEdges : Set (Sym2 (Fin 6))))
    {x y : Fin 6} (h : (openGraph ω).Reachable x y) :
    ∀ (i : ℕ) (hi : i < 5), x.val ≤ i → i < y.val → peAt i hi ∈ ω := by
  rw [SimpleGraph.reachable_iff_reflTransGen] at h
  refine Relation.ReflTransGen.trans_induction_on
    (motive := fun {a b : Fin 6} (_ : Relation.ReflTransGen (openGraph ω).Adj a b) =>
      ∀ (i : ℕ) (hi : i < 5), a.val ≤ i → i < b.val → peAt i hi ∈ ω) h ?_ ?_ ?_
  · intro a i hi h1 h2
    omega
  · intro a b hab i hi h1 h2
    have hmem : s(a, b) ∈ ω := ((openGraph_adj_iff ω a b).mp hab).1
    have hpos : b.val = a.val + 1 ∨ a.val = b.val + 1 := adj_pos hω hab
    have hba : b.val = a.val + 1 := by omega
    have hia : i = a.val := by omega
    have hav : vt i (by omega) = a := Fin.ext (by simp only [vt_val_eq]; omega)
    have hbv : vt (i + 1) (by omega) = b := Fin.ext (by simp only [vt_val_eq]; omega)
    have hpe : peAt i hi = s(a, b) := by rw [peAt_eq, hav, hbv]
    rw [hpe]
    exact hmem
  · intro a b c _ _ ih1 ih2 i hi h1 h2
    by_cases hb : i < b.val
    · exact ih1 i hi h1 hb
    · exact ih2 i hi (by omega) h2

/-- If every line edge between `x` and `y` is open then `x` and `y` are connected. -/
theorem reach_of_seg {ω : Set (Sym2 (Fin 6))}
    {x y : Fin 6}
    (h : ∀ (i : ℕ) (hi : i < 5), min x.val y.val ≤ i → i < max x.val y.val →
      peAt i hi ∈ ω) :
    (openGraph ω).Reachable x y := by
  suffices H : ∀ (k : ℕ) (x y : Fin 6), y.val = x.val + k →
      (∀ (i : ℕ) (hi : i < 5), x.val ≤ i → i < y.val → peAt i hi ∈ ω) →
      (openGraph ω).Reachable x y by
    rcases le_total x.val y.val with hxy | hxy
    · exact H (y.val - x.val) x y (by omega) (by
        intro i hi h1 h2
        exact h i hi (by omega) (by omega))
    · have := H (x.val - y.val) y x (by omega) (by
        intro i hi h1 h2
        exact h i hi (by omega) (by omega))
      exact this.symm
  intro k
  induction k with
  | zero =>
    intro x y hy _
    have hxy : x = y := Fin.ext (by omega)
    rw [hxy]
  | succ k ih =>
    intro x y hy hseg
    have hx5 : x.val < 5 := by omega
    have hnxt : (nxt x hx5).val = x.val + 1 := rfl
    have hpe : s(x, nxt x hx5) = peAt x.val hx5 := rfl
    have hmem : s(x, nxt x hx5) ∈ ω := by
      rw [hpe]
      exact hseg x.val hx5 (by omega) (by omega)
    have hne : x ≠ nxt x hx5 := by
      intro hc
      have hv : x.val = (nxt x hx5).val := Fin.ext_iff.mp hc
      omega
    have hadj : (openGraph ω).Adj x (nxt x hx5) :=
      (openGraph_adj_iff ω x (nxt x hx5)).mpr ⟨hmem, hne⟩
    have hreach : (openGraph ω).Reachable (nxt x hx5) y := by
      refine ih (nxt x hx5) y ?_ ?_
      · omega
      · intro i hi h1 h2
        exact hseg i hi (by omega) h2
    exact (SimpleGraph.Adj.reachable hadj).trans hreach

/-- **Reachability on the line.**  On configurations whose open pairs are line edges, two
vertices are connected exactly when every line edge between them is open. -/
theorem reach_iff_seg {ω : Set (Sym2 (Fin 6))} (hω : ω ⊆ (lineEdges : Set (Sym2 (Fin 6))))
    (x y : Fin 6) :
    (openGraph ω).Reachable x y ↔
      ∀ (i : ℕ) (hi : i < 5), min x.val y.val ≤ i → i < max x.val y.val → peAt i hi ∈ ω := by
  constructor
  · intro h i hi h1 h2
    rcases le_total x.val y.val with hxy | hxy
    · exact reach_forward hω h i hi (by omega) (by omega)
    · exact reach_forward hω h.symm i hi (by omega) (by omega)
  · exact reach_of_seg

end PercLib.CriticalLRP.Counterexample.Line6
