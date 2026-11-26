/-
Arc edges of the six-cycle on `ZMod 6`, the injectivity of the edge parametrisation, cylinder
probabilities for the translation-invariant profile and the elementary reachability direction.
-/
module

public import PercLib.CriticalLRP.Correlation.SixPoint.MixedK2.Counterexample.Cycle6.Defs

/-!
# Arcs, cylinder probabilities and reachability along an arc
-/

@[expose] public section

noncomputable section

namespace PercLib.CriticalLRP.Counterexample.Cycle6

open Set MeasureTheory
open scoped ENNReal NNReal BigOperators
open PercLib.Percolation.Bond
open PercLib.Probability

/-! ## Elementary `ZMod 6` arithmetic -/

theorem val_natCast_of_lt {t : ℕ} (ht : t < 6) : ((t : ZMod 6)).val = t := by
  rw [ZMod.val_natCast, Nat.mod_eq_of_lt ht]

theorem val_succ (w : ZMod 6) : (w + 1).val = if w.val = 5 then 0 else w.val + 1 := by
  revert w
  decide

theorem val_lt_six (w : ZMod 6) : w.val < 6 := ZMod.val_lt w

theorem one_ne_zero_zmod : (1 : ZMod 6) ≠ 0 := by decide

theorem two_ne_zero_zmod : (2 : ZMod 6) ≠ 0 := by decide

theorem cdist_zero_three (c : ZMod 6) : cdist 0 c + cdist 3 c = 3 := by
  revert c
  decide

theorem cdist_le_three (x y : ZMod 6) : cdist x y ≤ 3 := by
  revert x y
  decide

theorem cdist_self (x : ZMod 6) : cdist x x = 0 := by
  simp only [cdist, sub_self, ZMod.val_zero, min_eq_left (Nat.zero_le 6)]

theorem cdist_pos {x y : ZMod 6} (h : x ≠ y) : 1 ≤ cdist x y := by
  revert h
  revert x y
  decide

/-! ## Injectivity of the edge parametrisation -/

theorem mk_succ_inj {t t' : ℕ} (ht : t < 6) (ht' : t' < 6)
    (h : s((t : ZMod 6), ((t + 1 : ℕ) : ZMod 6)) =
      s((t' : ZMod 6), ((t' + 1 : ℕ) : ZMod 6))) : t = t' := by
  have h2 := (Sym2.mk_eq_mk_iff (p := ((t : ZMod 6), ((t + 1 : ℕ) : ZMod 6)))
    (q := ((t' : ZMod 6), ((t' + 1 : ℕ) : ZMod 6)))).1 h
  rcases h2 with h | h
  · have h1 : (t : ZMod 6) = (t' : ZMod 6) := congrArg Prod.fst h
    exact Nat.ModEq.eq_of_lt_of_lt (ZMod.natCast_eq_natCast_iff t t' 6 |>.1 h1) ht ht'
  · have h1 : (t : ZMod 6) = ((t' + 1 : ℕ) : ZMod 6) := congrArg Prod.fst h
    have h2 : ((t + 1 : ℕ) : ZMod 6) = (t' : ZMod 6) := congrArg Prod.snd h
    simp only [Nat.cast_add, Nat.cast_one] at h1 h2
    have h3 : (1 : ZMod 6) + 1 = 0 := by
      have key : (t : ZMod 6) + (1 + 1) = (t : ZMod 6) + 0 := by
        rw [← add_assoc, h2, ← h1, add_zero]
      exact add_left_cancel key
    exact absurd h3 (by decide)

theorem eAt_eq_iff {x : ZMod 6} {t t' : ℕ} (ht : t < 6) (ht' : t' < 6) :
    eAt x t = eAt x t' ↔ t = t' := by
  constructor
  · intro h
    have hmap := congrArg (Sym2.map (fun w : ZMod 6 => w - x)) h
    simp only [eAt, vtx, Sym2.map_mk] at hmap
    have e1 : x + (t : ZMod 6) - x = (t : ZMod 6) := by ring
    have e2 : x + ((t + 1 : ℕ) : ZMod 6) - x = ((t + 1 : ℕ) : ZMod 6) := by ring
    have e3 : x + (t' : ZMod 6) - x = (t' : ZMod 6) := by ring
    have e4 : x + ((t' + 1 : ℕ) : ZMod 6) - x = ((t' + 1 : ℕ) : ZMod 6) := by ring
    rw [e1, e2, e3, e4] at hmap
    exact mk_succ_inj ht ht' hmap
  · rintro rfl
    rfl

theorem eAt_injOn (x : ZMod 6) : Set.InjOn (eAt x) {t : ℕ | t < 6} := by
  intro a ha b hb h
  exact (eAt_eq_iff (by simpa using ha) (by simpa using hb)).1 h

/-! ## Membership in the arcs -/

theorem mem_fwdArc {x : ZMod 6} {k t : ℕ} (ht : t < k) : eAt x t ∈ fwdArc x k := by
  rw [fwdArc]
  exact Finset.mem_image.2 ⟨t, Finset.mem_range.2 ht, rfl⟩

theorem mem_fwdArc_iff {x : ZMod 6} {k : ℕ} {e : Sym2 (ZMod 6)} :
    e ∈ fwdArc x k ↔ ∃ t, t < k ∧ eAt x t = e := by
  rw [fwdArc, Finset.mem_image]
  constructor
  · rintro ⟨t, ht, rfl⟩
    exact ⟨t, Finset.mem_range.1 ht, rfl⟩
  · rintro ⟨t, ht, rfl⟩
    exact ⟨t, Finset.mem_range.2 ht, rfl⟩

theorem mem_bwdArc_iff {x : ZMod 6} {k : ℕ} {e : Sym2 (ZMod 6)} :
    e ∈ bwdArc x k ↔ ∃ i, i < 6 - k ∧ eAt x (k + i) = e := by
  rw [bwdArc, Finset.mem_image]
  constructor
  · rintro ⟨i, hi, rfl⟩
    exact ⟨i, Finset.mem_range.1 hi, rfl⟩
  · rintro ⟨i, hi, rfl⟩
    exact ⟨i, Finset.mem_range.2 hi, rfl⟩

theorem card_fwdArc (x : ZMod 6) {k : ℕ} (hk : k ≤ 6) : (fwdArc x k).card = k := by
  rw [fwdArc, Finset.card_image_of_injOn ?_, Finset.card_range]
  intro a ha b hb h
  have ha6 : a < 6 := by have := Finset.mem_range.1 ha; omega
  have hb6 : b < 6 := by have := Finset.mem_range.1 hb; omega
  exact eAt_injOn (x := x) (by simpa using ha6) (by simpa using hb6) h

theorem card_bwdArc (x : ZMod 6) {k : ℕ} (hk : k ≤ 6) : (bwdArc x k).card = 6 - k := by
  rw [bwdArc, Finset.card_image_of_injOn ?_, Finset.card_range]
  intro a ha b hb h
  have ha6 : k + a < 6 := by have := Finset.mem_range.1 ha; omega
  have hb6 : k + b < 6 := by have := Finset.mem_range.1 hb; omega
  have hinj := (eAt_eq_iff ha6 hb6).1 h
  omega

/-! ## Cylinder probabilities -/

theorem stepProfile_step {θ : unitInterval} {z : ZMod 6} : stepProfile θ s(z, z + 1) = θ := by
  rw [stepProfile_mk, stepFun]
  refine ite_pos_eq (Or.inl ?_)
  ring

theorem toNNReal_stepProfile_of_step {θ : unitInterval} {z : ZMod 6} :
    (unitInterval.toNNReal (stepProfile θ s(z, z + 1)) : ℝ≥0∞) =
      (unitInterval.toNNReal θ : ℝ≥0∞) := by
  rw [stepProfile_step]

theorem law_subset_of_step {θ : unitInterval} {F : Finset (Sym2 (ZMod 6))}
    (hF : ∀ e ∈ F, e ∈ stepSet) :
    law (stepProfile θ) {ω : Config (ZMod 6) | (F : Set (Sym2 (ZMod 6))) ⊆ ω}
      = (unitInterval.toNNReal θ : ℝ≥0∞) ^ F.card := by
  rw [law, prodBernoulli_subset]
  rw [Finset.prod_congr rfl (fun e he => ?_), Finset.prod_const]
  obtain ⟨z, hz⟩ := hF e he
  rw [hz, toNNReal_stepProfile_of_step]

theorem law_fwdArc (x : ZMod 6) {k : ℕ} (hk : k ≤ 6) :
    law (stepProfile theta) {ω : Config (ZMod 6) | (fwdArc x k : Set (Sym2 (ZMod 6))) ⊆ ω}
      = eps ^ k := by
  rw [law_subset_of_step (F := fwdArc x k) ?_, card_fwdArc x hk]
  · rfl
  · intro e he
    obtain ⟨t, -, rfl⟩ := mem_fwdArc_iff.1 he
    exact eAt_mem_stepSet x t

theorem law_bwdArc (x : ZMod 6) {k : ℕ} (hk : k ≤ 6) :
    law (stepProfile theta) {ω : Config (ZMod 6) | (bwdArc x k : Set (Sym2 (ZMod 6))) ⊆ ω}
      = eps ^ (6 - k) := by
  rw [law_subset_of_step (F := bwdArc x k) ?_, card_bwdArc x hk]
  · rfl
  · intro e he
    obtain ⟨i, -, rfl⟩ := mem_bwdArc_iff.1 he
    exact eAt_mem_stepSet x _

/-! ## Reachability along an arc -/

theorem vtx_ne_succ (x : ZMod 6) (t : ℕ) : vtx x t ≠ vtx x t + 1 := by
  intro h
  have h' : (0 : ZMod 6) = 1 := by
    have hh := congrArg (fun w => w - vtx x t) h
    simpa using hh
  exact absurd h' (by decide)

theorem reach_of_arc {ω : Config (ZMod 6)} {x : ZMod 6} {k : ℕ}
    (h : ∀ t, t < k → eAt x t ∈ ω) : (openGraph ω).Reachable x (vtx x k) := by
  induction k with
  | zero => simp [vtx]
  | succ n ih =>
    have ih' := ih fun t ht => h t (by omega)
    have hadj : (openGraph ω).Adj (vtx x n) (vtx x (n + 1)) := by
      rw [openGraph_adj_iff]
      exact ⟨by rw [← eAt]; exact h n (by omega), by rw [vtx_succ]; exact vtx_ne_succ x n⟩
    exact ih'.trans hadj.reachable

theorem subset_fwdArc_imp_reach {ω : Config (ZMod 6)} {x : ZMod 6} {k : ℕ}
    (h : (fwdArc x k : Set (Sym2 (ZMod 6))) ⊆ ω) :
    (openGraph ω).Reachable x (vtx x k) := by
  refine reach_of_arc fun t ht => h ?_
  exact mem_fwdArc ht

/-- The lower bound `eps ^ 3 ≤ law (conn 0 3)` behind the counterexample. -/
theorem eps_cube_le_law_conn_three :
    eps ^ 3 ≤ law (stepProfile theta) (conn (0 : ZMod 6) 3) := by
  have hcyl : law (stepProfile theta)
      {ω : Config (ZMod 6) | (fwdArc (0 : ZMod 6) 3 : Set (Sym2 (ZMod 6))) ⊆ ω} = eps ^ 3 :=
    law_fwdArc 0 (by norm_num : 3 ≤ 6)
  rw [← hcyl]
  refine measure_mono ?_
  intro ω hω
  rw [mem_conn_iff]
  have := subset_fwdArc_imp_reach (x := 0) (k := 3) hω
  simpa [vtx] using this

end PercLib.CriticalLRP.Counterexample.Cycle6
