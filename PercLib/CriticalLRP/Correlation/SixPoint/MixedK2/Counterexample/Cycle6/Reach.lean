/-
The arc dichotomy on the six-cycle: a connection between two distinct vertices forces one of
the two arcs to be entirely open.  Consequence: the two-point function is bounded by
`eps ^ cdist`.
-/
module

public import PercLib.CriticalLRP.Correlation.SixPoint.MixedK2.Counterexample.Cycle6.Arcs

/-!
# The cut lemma and the arc dichotomy on `ZMod 6`
-/

@[expose] public section

noncomputable section

namespace PercLib.CriticalLRP.Counterexample.Cycle6

open Set MeasureTheory
open scoped ENNReal NNReal BigOperators
open PercLib.Percolation.Bond
open PercLib.Probability

/-! ## The cut lemma -/

/-- A walk from `x` to `y` with `x ∈ S` and `y ∉ S` uses an edge leaving `S`. -/
theorem walk_crossing {ω : Config (ZMod 6)} {x y : ZMod 6} (p : (openGraph ω).Walk x y)
    (S : Set (ZMod 6)) (hx : x ∈ S) (hy : y ∉ S) : ∃ u ∈ S, ∃ v ∉ S, s(u, v) ∈ ω := by
  induction p with
  | nil => exact absurd hx hy
  | cons hadj p ih =>
    rename_i u v w
    by_cases hv : v ∈ S
    · exact ih hv hy
    · exact ⟨u, hx, v, hv, (openGraph_adj_iff ω u v).1 hadj |>.1⟩

/-- Reachability across a cut uses an edge leaving the cut. -/
theorem reachable_crossing {ω : Config (ZMod 6)} {x y : ZMod 6} {S : Set (ZMod 6)}
    (hx : x ∈ S) (hy : y ∉ S) (h : (openGraph ω).Reachable x y) :
    ∃ u ∈ S, ∃ v ∉ S, s(u, v) ∈ ω := by
  obtain ⟨p⟩ := h
  exact walk_crossing p S hx hy

/-! ## The separating cut of the two arcs -/

theorem mem_cutSet (x z : ZMod 6) (i j : ℕ) :
    z ∈ cutSet x i j ↔ ((z - x).val ≤ i ∨ j < (z - x).val) := Iff.rfl

theorem cut_mem_start (x : ZMod 6) (i j : ℕ) : x ∈ cutSet x i j := by
  rw [mem_cutSet, sub_self, ZMod.val_zero]
  omega

theorem cut_not_mem_vtx {x : ZMod 6} {k i j : ℕ} (hk : k < 6) (hi : i < k) (hj : k ≤ j) :
    vtx x k ∉ cutSet x i j := by
  rw [mem_cutSet, vtx, show x + (k : ZMod 6) - x = (k : ZMod 6) from by ring,
    val_natCast_of_lt hk]
  omega

/-! ## Which step edges leave the cut -/

theorem cross_left_dec : ∀ (i j : Fin 6) (w : ZMod 6), w.val ≤ i.val ∨ j.val < w.val →
    ¬((w + 1).val ≤ i.val ∨ j.val < (w + 1).val) → i.val < j.val →
    w = ((i.val : ℕ) : ZMod 6) := by
  decide

theorem cross_right_dec : ∀ (i j : Fin 6) (w : ZMod 6), ¬(w.val ≤ i.val ∨ j.val < w.val) →
    ((w + 1).val ≤ i.val ∨ j.val < (w + 1).val) → i.val < j.val →
    w = ((j.val : ℕ) : ZMod 6) := by
  decide

/-- If the step edge from `z` to `z + 1` leaves the cut in the forward direction, it is the
`i`-th edge of the arc. -/
theorem cut_cross_fst {x : ZMod 6} {i j : ℕ} (hij : i < j) (hi : i < 6) (hj : j < 6)
    {z : ZMod 6} (hz : z ∈ cutSet x i j) (hz1 : z + 1 ∉ cutSet x i j) : z = vtx x i := by
  have hz' : (z - x).val ≤ i ∨ j < (z - x).val := mem_cutSet x z i j |>.1 hz
  have hz1' : ¬((z + 1 - x).val ≤ i ∨ j < (z + 1 - x).val) := fun h =>
    hz1 (mem_cutSet x (z + 1) i j |>.2 h)
  have hshift : z + 1 - x = (z - x) + 1 := by ring
  rw [hshift] at hz1'
  have key := cross_left_dec ⟨i, hi⟩ ⟨j, hj⟩ (z - x) hz' hz1' hij
  have h2 : z = x + (z - x) := by abel
  rw [key] at h2
  simpa [vtx] using h2

/-- If the step edge from `z` to `z + 1` leaves the cut in the backward direction, it is the
`j`-th edge of the arc. -/
theorem cut_cross_snd {x : ZMod 6} {i j : ℕ} (hij : i < j) (hi : i < 6) (hj : j < 6)
    {z : ZMod 6} (hz : z ∉ cutSet x i j) (hz1 : z + 1 ∈ cutSet x i j) : z = vtx x j := by
  have hz' : ¬((z - x).val ≤ i ∨ j < (z - x).val) := fun h =>
    hz (mem_cutSet x z i j |>.2 h)
  have hz1' : (z + 1 - x).val ≤ i ∨ j < (z + 1 - x).val := mem_cutSet x (z + 1) i j |>.1 hz1
  have hshift : z + 1 - x = (z - x) + 1 := by ring
  rw [hshift] at hz1'
  have key := cross_right_dec ⟨i, hi⟩ ⟨j, hj⟩ (z - x) hz' hz1' hij
  have h2 : z = x + (z - x) := by abel
  rw [key] at h2
  simpa [vtx] using h2

end PercLib.CriticalLRP.Counterexample.Cycle6

namespace PercLib.CriticalLRP.Counterexample.Cycle6

open Set MeasureTheory
open scoped ENNReal NNReal BigOperators
open PercLib.Percolation.Bond
open PercLib.Probability

/-! ## The dichotomy: a connection forces one arc to be open -/

theorem conn_subset_arcs {x y : ZMod 6} {k : ℕ} (_hxy : x ≠ y) (hk : k = (y - x).val) :
    conn x y ⊆ {ω : Config (ZMod 6) | (fwdArc x k : Set (Sym2 (ZMod 6))) ⊆ ω} ∪
      ({ω : Config (ZMod 6) | (bwdArc x k : Set (Sym2 (ZMod 6))) ⊆ ω} ∪
        ⋃ (e : {e : Sym2 (ZMod 6) // e ∉ stepSet}),
          {ω : Config (ZMod 6) | (e.1 : Sym2 (ZMod 6)) ∈ ω}) := by
  intro ω hconn
  have hk6 : k < 6 := by rw [hk]; exact ZMod.val_lt _
  have hreach : (openGraph ω).Reachable x y := mem_conn_iff ω x y |>.1 hconn
  by_cases hstep : ∀ e : Sym2 (ZMod 6), e ∈ ω → e ∈ stepSet
  · by_cases hf : ∀ t, t < k → eAt x t ∈ ω
    · refine Or.inl ?_
      intro e he
      obtain ⟨t, ht, rfl⟩ := mem_fwdArc_iff.1 he
      exact hf t ht
    · push Not at hf
      obtain ⟨i, hik, hiω⟩ := hf
      refine Or.inr (Or.inl ?_)
      intro e he
      obtain ⟨m, hm, rfl⟩ := mem_bwdArc_iff.1 he
      have hj6 : k + m < 6 := by omega
      have hi6 : i < 6 := by omega
      by_contra hcon
      have hy : y ∉ cutSet x i (k + m) := by
        rw [mem_cutSet]
        omega
      have hc := reachable_crossing (cut_mem_start x i (k + m)) hy hreach
      obtain ⟨u, huS, v, hvS, huv⟩ := hc
      obtain ⟨z, hz⟩ := hstep (s(u, v)) huv
      rcases (Sym2.mk_eq_mk_iff (p := (u, v)) (q := (z, z + 1))).1 hz with hcase | hcase
      · have huz : u = z := congrArg Prod.fst hcase
        have hvz : v = z + 1 := congrArg Prod.snd hcase
        have hzS : z ∈ cutSet x i (k + m) := by rw [← huz]; exact huS
        have hzS' : z + 1 ∉ cutSet x i (k + m) := by rw [← hvz]; exact hvS
        have hzi : z = vtx x i := cut_cross_fst (by omega) hi6 hj6 hzS hzS'
        rw [hzi] at hz
        have hei : eAt x i = s(u, v) := by rw [eAt, vtx_succ]; exact hz.symm
        exact hiω (by rw [hei]; exact huv)
      · have huz : u = z + 1 := congrArg Prod.fst hcase
        have hvz : v = z := congrArg Prod.snd hcase
        have hzS' : z + 1 ∈ cutSet x i (k + m) := by rw [← huz]; exact huS
        have hzS : z ∉ cutSet x i (k + m) := by rw [← hvz]; exact hvS
        have hzj : z = vtx x (k + m) := cut_cross_snd (by omega) hi6 hj6 hzS hzS'
        rw [hzj] at hz
        have hej : eAt x (k + m) = s(u, v) := by rw [eAt, vtx_succ]; exact hz.symm
        exact hcon (by rw [hej]; exact huv)
  · push Not at hstep
    obtain ⟨e, heω, hest⟩ := hstep
    exact Or.inr (Or.inr (Set.mem_iUnion.2 ⟨⟨e, hest⟩, heω⟩))

/-! ## The two-point bound -/

theorem toNNReal_theta : unitInterval.toNNReal theta = 1 / 64 := rfl

theorem eps_eq : eps = ((1 / 64 : ℝ≥0) : ℝ≥0∞) := rfl

theorem eps_le_one : eps ≤ 1 := by
  rw [eps_eq]
  norm_num

theorem law_not_step (θ : unitInterval) :
    law (stepProfile θ) (⋃ (e : {e : Sym2 (ZMod 6) // e ∉ stepSet}),
      {ω : Config (ZMod 6) | (e.1 : Sym2 (ZMod 6)) ∈ ω}) = 0 := by
  refine measure_iUnion_null fun e => ?_
  rw [law, prodBernoulli_setOf_mem, stepProfile_eq_zero e.2]
  simp

theorem law_conn_le {x y : ZMod 6} (hxy : x ≠ y) :
    law (stepProfile theta) (conn x y) ≤ eps ^ (y - x).val + eps ^ (6 - (y - x).val) := by
  have hk6 : (y - x).val ≤ 6 := le_of_lt (ZMod.val_lt _)
  set k := (y - x).val with hkdef
  have hk6' : k ≤ 6 := by rw [hkdef]; exact hk6
  set A : Set (Config (ZMod 6)) := {ω | (fwdArc x k : Set (Sym2 (ZMod 6))) ⊆ ω} with hA
  set B : Set (Config (ZMod 6)) := {ω | (bwdArc x k : Set (Sym2 (ZMod 6))) ⊆ ω} with hB
  set C : Set (Config (ZMod 6)) := ⋃ (e : {e : Sym2 (ZMod 6) // e ∉ stepSet}),
    {ω : Config (ZMod 6) | (e.1 : Sym2 (ZMod 6)) ∈ ω} with hC
  have hsub : conn x y ⊆ A ∪ (B ∪ C) := by
    have h := conn_subset_arcs hxy hkdef.symm
    simpa [A, B, C] using h
  calc law (stepProfile theta) (conn x y)
      ≤ law (stepProfile theta) (A ∪ (B ∪ C)) := measure_mono hsub
    _ = law (stepProfile theta) ((A ∪ B) ∪ C) := by rw [Set.union_assoc]
    _ ≤ law (stepProfile theta) (A ∪ B) + law (stepProfile theta) C := measure_union_le _ _
    _ ≤ (law (stepProfile theta) A + law (stepProfile theta) B) + law (stepProfile theta) C :=
        add_le_add (measure_union_le A B) (le_refl _)
    _ = eps ^ k + eps ^ (6 - k) := by
        rw [show law (stepProfile theta) A = eps ^ k from by
              rw [hA]; exact law_fwdArc x hk6',
            show law (stepProfile theta) B = eps ^ (6 - k) from by
              rw [hB]; exact law_bwdArc x hk6',
            show law (stepProfile theta) C = 0 from by rw [hC]; exact law_not_step theta,
            add_zero]
    _ = eps ^ (y - x).val + eps ^ (6 - (y - x).val) := by rw [hkdef]

/-- The two-point function of the six-cycle profile at `1/64`. -/
theorem tau_le (x y : ZMod 6) : tau (stepProfile theta) x y ≤ 2 * eps ^ cdist x y := by
  by_cases hxy : x = y
  · subst hxy
    rw [tau, conn_self, measure_univ, cdist_self, pow_zero]
    norm_num
  · have h := law_conn_le hxy
    have h1 : eps ^ (y - x).val ≤ eps ^ cdist x y := by
      refine pow_le_pow_right_of_le_one' eps_le_one ?_
      rw [cdist]
      exact min_le_left _ _
    have h2 : eps ^ (6 - (y - x).val) ≤ eps ^ cdist x y := by
      refine pow_le_pow_right_of_le_one' eps_le_one ?_
      rw [cdist]
      exact min_le_right _ _
    calc tau (stepProfile theta) x y
        = law (stepProfile theta) (conn x y) := rfl
      _ ≤ eps ^ (y - x).val + eps ^ (6 - (y - x).val) := h
      _ ≤ eps ^ cdist x y + eps ^ cdist x y := add_le_add h1 h2
      _ = 2 * eps ^ cdist x y := by rw [two_mul]

end PercLib.CriticalLRP.Counterexample.Cycle6
