/-
Migration source: https://github.com/yujinhkim/Critical-Long-range-percolation
Integration revision: 3b3d1d0e43ef940bfaa2292ee5c2ee094ac4edbf
Licence: Apache-2.0 for the PercLib Lean sources and tooling; see third_party/critical-lrp/.
External provenance and modifications are recorded in the file-specific notices below.
-/

/-
# Root-spine completion and exact-threshold trimming of rooted pieces

The integer tree-piece partition does not guarantee that its common root belongs to a piece. For
the pointed disjoint-occurrence inclusion (2.11), `exists_root_spine_piece_of_root` selects a piece
whose root has minimal depth and adjoins its ancestor chain. The enlarged piece is rooted at the
common root, retains its marked vertices, and has parent edges disjoint from every other piece.

The source arXiv:2008.11197v2 uses an all-edge partition here. This file proves the weaker property
actually needed for that probability step rather than asserting the absent partition property.
It also proves exact marked-count trimming by removing a deepest non-root member of a piece.
-/
module

public import PercLib.CriticalLRP.Tightness.TreePieces

set_option linter.unusedSectionVars false
set_option linter.unusedSimpArgs false
set_option linter.unnecessarySimpa false
set_option linter.unusedTactic false
set_option linter.unusedVariables false

set_option autoImplicit true

@[expose] public section

namespace Hutchcroft

open Finset

variable {V : Type*} [Fintype V] [DecidableEq V]

/-! ### Depth in a rooted `pp`-tree -/

section Depth

variable {pp : V → V} {r : V}

/-- `pdepth pp r hroot x` is the number of `pp`-steps from `x` to the common root `r`; it is the
graph distance from `x` to `r` in the tree of parent edges. -/
noncomputable def pdepth (pp : V → V) (r : V) (hroot : ∀ x : V, ∃ n : ℕ, pp^[n] x = r)
    (x : V) : ℕ :=
  Nat.find (hroot x)

lemma pdepth_spec (hroot : ∀ x : V, ∃ n : ℕ, pp^[n] x = r) (x : V) :
    pp^[pdepth pp r hroot x] x = r :=
  Nat.find_spec (hroot x)

lemma pdepth_le (hroot : ∀ x : V, ∃ n : ℕ, pp^[n] x = r) {x : V} {n : ℕ}
    (h : pp^[n] x = r) : pdepth pp r hroot x ≤ n :=
  Nat.find_min' (hroot x) h

lemma pdepth_root (hroot : ∀ x : V, ∃ n : ℕ, pp^[n] x = r) :
    pdepth pp r hroot r = 0 :=
  Nat.eq_zero_of_le_zero (pdepth_le hroot (n := 0) (by simp))

lemma pdepth_pos (hroot : ∀ x : V, ∃ n : ℕ, pp^[n] x = r) {x : V} (h : x ≠ r) :
    0 < pdepth pp r hroot x := by
  rcases Nat.eq_zero_or_pos (pdepth pp r hroot x) with h0 | h0
  · exfalso
    have h1 := pdepth_spec hroot x
    rw [h0] at h1
    simp only [Function.iterate_zero_apply] at h1
    exact h h1
  · exact h0


/-! ### The satisfiable hypothesis: a fixed root

Fixed-point root reachability is supplied by `IsRootedForest` in the root tree-piece module.
except the fixed point at the root". -/


section FixedRoot

variable {pp : V → V} {r : V} {A : Finset V} {lam : ℕ}


@[simp] lemma pp_iter_root {pp : V → V} {r : V} (hfix : pp r = r) (n : ℕ) :
    pp^[n] r = r := by
  induction n with
  | zero => rfl
  | succ k ih => rw [Function.iterate_succ_apply', ih, hfix]


/-- Along a `pp`-orbit, `pdepth` drops by exactly the number of steps, as long as the iterate
has not yet passed the root.  (No acyclicity is needed: only the minimality of `pdepth`.) -/
theorem pdepth_iter_add_of_le (hroot : ∀ x : V, ∃ n : ℕ, pp^[n] x = r)
    {y v : V} {n : ℕ} (h : pp^[n] y = v) (hn : n ≤ pdepth pp r hroot y) :
    pdepth pp r hroot v + n = pdepth pp r hroot y := by
  have hvs : pp^[pdepth pp r hroot v] v = r := pdepth_spec hroot v
  have hys : pp^[pdepth pp r hroot y] y = r := pdepth_spec hroot y
  have hub : pdepth pp r hroot y ≤ n + pdepth pp r hroot v := by
    have h1 : pp^[n + pdepth pp r hroot v] y = r := by
      rw [Nat.add_comm n (pdepth pp r hroot v), Function.iterate_add_apply, h, hvs]
    exact pdepth_le hroot h1
  have hlb : pdepth pp r hroot v + n ≤ pdepth pp r hroot y := by
    have h1 : pp^[pdepth pp r hroot y - n] v = r := by
      rw [← h, ← Function.iterate_add_apply, Nat.sub_add_cancel hn, hys]
    have h2 := pdepth_le hroot h1
    have h3 : pdepth pp r hroot v + n ≤ (pdepth pp r hroot y - n) + n :=
      Nat.add_le_add_right h2 n
    rwa [Nat.sub_add_cancel hn] at h3
  exact Nat.le_antisymm hlb (by rw [Nat.add_comm] at hub; exact hub)

/-- A strict descendant of `v` has strictly larger depth.  Only the fixed-root hypothesis
`pp r = r` is used, and only to handle the case in which the orbit of `y` reaches `r` first. -/
theorem pdepth_lt_of_mem_desc_of_root (hroot : ∀ x : V, ∃ n : ℕ, pp^[n] x = r)
    (hfix : pp r = r) {y v : V} (h : y ∈ desc pp v) (hne : y ≠ v) :
    pdepth pp r hroot v < pdepth pp r hroot y := by
  rw [mem_desc] at h
  obtain ⟨n, hn⟩ := h
  have hn0 : n ≠ 0 := by
    rintro rfl
    simp only [Function.iterate_zero_apply] at hn
    exact hne hn
  have hpos : 1 ≤ n := Nat.one_le_iff_ne_zero.mpr hn0
  have hyr : y ≠ r := by
    intro hyr
    rw [hyr] at hn
    rw [pp_iter_root hfix] at hn
    exact hne (hyr.trans hn)
  have hyd : 1 ≤ pdepth pp r hroot y := pdepth_pos hroot hyr
  by_cases hle : n ≤ pdepth pp r hroot y
  · have h1 := pdepth_iter_add_of_le hroot hn hle
    omega
  · push Not at hle
    -- the orbit of `y` reaches `r` before time `n`, so `v` is the root
    have h1 : pp^[n - pdepth pp r hroot y] r = v := by
      have h2 : pp^[n - pdepth pp r hroot y] (pp^[pdepth pp r hroot y] y) = v := by
        rw [← Function.iterate_add_apply, Nat.sub_add_cancel (le_of_lt hle), hn]
      rwa [pdepth_spec hroot y] at h2
    rw [pp_iter_root hfix] at h1
    rw [← h1, pdepth_root]
    omega

/-- A vertex whose orbit hits the root can only be the root. -/
theorem eq_root_of_mem_desc_root (hfix : pp r = r) {v : V} (h : r ∈ desc pp v) : v = r := by
  rw [mem_desc] at h
  obtain ⟨n, hn⟩ := h
  rw [pp_iter_root hfix] at hn
  exact hn.symm


end FixedRoot


/-! ### The ancestor chain of a vertex -/

section Ancestors

variable {pp : V → V} {r : V}

/-- The set of `pp`-ancestors of `v`, including `v` itself and the common root `r`. -/
noncomputable def ancestors (pp : V → V) (r : V) (hroot : ∀ x : V, ∃ n : ℕ, pp^[n] x = r)
    (v : V) : Finset V :=
  (Finset.range (pdepth pp r hroot v + 1)).image (fun i => pp^[i] v)

variable (hroot : ∀ x : V, ∃ n : ℕ, pp^[n] x = r)

lemma mem_ancestors {v x : V} :
    x ∈ ancestors pp r hroot v ↔ ∃ i, i ≤ pdepth pp r hroot v ∧ pp^[i] v = x := by
  classical
  simp only [ancestors, Finset.mem_image, Finset.mem_range]
  constructor
  · rintro ⟨i, hi, rfl⟩
    exact ⟨i, by omega, rfl⟩
  · rintro ⟨i, hi, rfl⟩
    exact ⟨i, by omega, rfl⟩

lemma self_mem_ancestors (v : V) : v ∈ ancestors pp r hroot v := by
  rw [mem_ancestors]
  exact ⟨0, by omega, rfl⟩

lemma root_mem_ancestors (v : V) : r ∈ ancestors pp r hroot v := by
  rw [mem_ancestors]
  exact ⟨pdepth pp r hroot v, le_rfl, pdepth_spec hroot v⟩

lemma pp_mem_ancestors {v x : V} (hx : x ∈ ancestors pp r hroot v) (hne : x ≠ r) :
    pp x ∈ ancestors pp r hroot v := by
  rw [mem_ancestors] at hx ⊢
  obtain ⟨i, hi, rfl⟩ := hx
  have hlt : i < pdepth pp r hroot v := by
    rcases lt_or_ge i (pdepth pp r hroot v) with h | h
    · exact h
    · exfalso
      apply hne
      rw [← pdepth_spec hroot v]
      congr 1
      omega
  exact ⟨i + 1, by omega, by rw [Function.iterate_succ_apply']⟩


/-- A strict ancestor of `v` has `v` as a descendant. -/
lemma ancestor_mem_desc {v x : V} (hx : x ∈ ancestors pp r hroot v) (hne : x ≠ v) :
    v ∈ desc pp x := by
  rw [mem_ancestors] at hx
  obtain ⟨i, hi, rfl⟩ := hx
  rw [mem_desc]
  have h0 : i ≠ 0 := by rintro rfl; exact hne rfl
  exact ⟨i, rfl⟩


/-- A vertex of the ancestor chain of `v` reaches the root. -/
lemma iter_eq_root_of_mem_ancestors {v x : V} (hx : x ∈ ancestors pp r hroot v) :
    ∃ n, pp^[n] x = r := by
  rw [mem_ancestors] at hx
  obtain ⟨i, hi, rfl⟩ := hx
  exact ⟨pdepth pp r hroot v - i, by
    rw [← Function.iterate_add_apply, Nat.sub_add_cancel hi, pdepth_spec hroot v]⟩


end Ancestors


/-! ### Trimming to exactly `lam` marked vertices -/

section Trim

variable {pp : V → V} {r : V} {A : Finset V} {lam : ℕ}

/-- A non-root member of a rooted piece with no child inside the piece can be deleted. -/
lemma isRootedPiece_erase {v : V} {P : Finset V} (h : IsRootedPiece pp v P) {w : V}
    (_hw : w ∈ P) (hwv : w ≠ v) (hnokid : ∀ x ∈ P, x ≠ w → pp x ≠ w) :
    IsRootedPiece pp v (P.erase w) := by
  refine ⟨Finset.mem_erase.mpr ⟨fun hc => hwv hc.symm, h.1⟩, ?_, ?_⟩
  · intro x hx hxv
    obtain ⟨hxw, hxP⟩ := Finset.mem_erase.mp hx
    exact Finset.mem_erase.mpr ⟨hnokid x hxP hxw, h.2.1 x hxP hxv⟩
  · intro x hx
    exact h.2.2 x (Finset.mem_of_mem_erase hx)


/-- `Finset.erase` is monotone in the set. -/
lemma erase_subset_erase_of_subset {s t : Finset V} (h : s ⊆ t) (a : V) :
    s.erase a ⊆ t.erase a := by
  intro x hx
  obtain ⟨hxa, hxs⟩ := Finset.mem_erase.mp hx
  exact Finset.mem_erase.mpr ⟨hxa, h hxs⟩


section FixedRootSpine

variable {pp : V → V} {r : V} {A : Finset V} {lam : ℕ}


/-- Depth decreases strictly along a strict ancestor, with the fixed-root hypothesis. -/
theorem pdepth_lt_of_ancestor_of_root (hroot : ∀ x : V, ∃ n : ℕ, pp^[n] x = r)
    (hfix : pp r = r) {v x : V} (hx : x ∈ ancestors pp r hroot v) (hne : x ≠ v) :
    pdepth pp r hroot x < pdepth pp r hroot v :=
  pdepth_lt_of_mem_desc_of_root hroot hfix (ancestor_mem_desc hroot hx hne)
    (fun h => hne h.symm)

lemma exists_removable_of_root (hroot : ∀ x : V, ∃ n : ℕ, pp^[n] x = r)
    (hfix : pp r = r)
    {v : V} {P : Finset V} (h : IsRootedPiece pp v P) (hcard : 2 ≤ P.card) :
    ∃ w ∈ P, w ≠ v ∧ ∀ x ∈ P, x ≠ w → pp x ≠ w := by
  classical
  have hne : (P.erase v).Nonempty := by
    rw [← Finset.card_pos, Finset.card_erase_of_mem h.1]
    have := Finset.card_pos.mpr ⟨v, h.1⟩
    omega
  obtain ⟨w, hw, hmax⟩ := Finset.exists_max_image (P.erase v)
    (fun x => pdepth pp r hroot x) hne
  have hwP : w ∈ P := Finset.mem_of_mem_erase hw
  have hwv : w ≠ v := Finset.ne_of_mem_erase hw
  refine ⟨w, hwP, hwv, ?_⟩
  intro x hxP hxw hpp
  have hxd : x ∈ desc pp w := mem_desc.mpr ⟨1, hpp⟩
  have h1 : pdepth pp r hroot w < pdepth pp r hroot x :=
    pdepth_lt_of_mem_desc_of_root hroot hfix hxd hxw
  have h2 : pdepth pp r hroot v < pdepth pp r hroot w :=
    pdepth_lt_of_mem_desc_of_root hroot hfix (mem_desc.mpr (h.2.2 w hwP)) hwv
  have hxv : x ≠ v := by
    intro hc
    rw [hc] at h1
    omega
  have h3 := hmax x (Finset.mem_erase.mpr ⟨hxv, hxP⟩)
  omega


theorem exists_trimmed_piece_of_root (hroot : ∀ x : V, ∃ n : ℕ, pp^[n] x = r)
    (hfix : pp r = r)
    {v : V} {P : Finset V} (h : IsRootedPiece pp v P) {lam : ℕ} (hlam : 1 ≤ lam)
    (hcard : lam ≤ (A ∩ P).card) :
    ∃ Q : Finset V, Q ⊆ P ∧ IsRootedPiece pp v Q ∧ (A ∩ Q).card = lam := by
  classical
  suffices H : ∀ n, ∀ P : Finset V, P.card ≤ n → IsRootedPiece pp v P →
      lam ≤ (A ∩ P).card → ∃ Q : Finset V, Q ⊆ P ∧ IsRootedPiece pp v Q ∧
        (A ∩ Q).card = lam from H _ P le_rfl h hcard
  intro n
  induction n with
  | zero =>
      intro P hPc hPiece hPcard
      have hempty : P = ∅ := Finset.card_eq_zero.mp (by omega)
      rw [hempty] at hPiece
      simpa using hPiece.1
  | succ n ih =>
      intro P hPc hPiece hPcard
      by_cases hEq : (A ∩ P).card = lam
      · exact ⟨P, Finset.Subset.refl P, hPiece, hEq⟩
      · have hgt : lam + 1 ≤ (A ∩ P).card := by omega
        have hle : (A ∩ P).card ≤ P.card := Finset.card_le_card (Finset.inter_subset_right)
        have hcard2 : 2 ≤ P.card := by omega
        obtain ⟨w, hwP, hwv, hnokid⟩ := exists_removable_of_root hroot hfix hPiece hcard2
        have hP' : IsRootedPiece pp v (P.erase w) := isRootedPiece_erase hPiece hwP hwv hnokid
        have hsub : P.erase w ⊆ P := Finset.erase_subset w P
        have hcard' : lam ≤ (A ∩ P.erase w).card := by
          have h1 : A ∩ P ⊆ insert w (A ∩ P.erase w) := by
            intro x hx
            obtain ⟨hxA, hxP⟩ := Finset.mem_inter.mp hx
            by_cases hxw : x = w
            · exact Finset.mem_insert.mpr (Or.inl hxw)
            · exact Finset.mem_insert.mpr
                (Or.inr (Finset.mem_inter.mpr ⟨hxA, Finset.mem_erase.mpr ⟨hxw, hxP⟩⟩))
          have h2 := Finset.card_le_card h1
          have h3 : (insert w (A ∩ P.erase w)).card ≤ (A ∩ P.erase w).card + 1 :=
            Finset.card_insert_le w _
          omega
        have hlt : (P.erase w).card < P.card := Finset.card_erase_lt_of_mem hwP
        obtain ⟨Q, hQsub, hQpiece, hQcard⟩ := ih (P.erase w) (by omega) hP' hcard'
        exact ⟨Q, hQsub.trans hsub, hQpiece, hQcard⟩


theorem exists_trimmed_family_of_root (hroot : ∀ x : V, ∃ n : ℕ, pp^[n] x = r)
    (hfix : pp r = r)
    {s : Finset (V × Finset V)} (hpiece : ∀ p ∈ s, IsRootedPiece pp p.1 p.2)
    (hdisj : ∀ p ∈ s, ∀ q ∈ s, p ≠ q → Disjoint (p.2.erase p.1) (q.2.erase q.1))
    {lam : ℕ} (hlam : 1 ≤ lam) (hmark : ∀ p ∈ s, lam ≤ (A ∩ p.2).card) :
    ∃ T : V × Finset V → Finset V,
      (∀ p ∈ s, T p ⊆ p.2 ∧ IsRootedPiece pp p.1 (T p) ∧ (A ∩ T p).card = lam) ∧
      (∀ p ∈ s, ∀ q ∈ s, p ≠ q → Disjoint ((T p).erase p.1) ((T q).erase q.1)) := by
  classical
  have hex : ∀ p : V × Finset V, ∃ Q : Finset V, p ∈ s → Q ⊆ p.2 ∧
      IsRootedPiece pp p.1 Q ∧ (A ∩ Q).card = lam := by
    intro p
    by_cases hp : p ∈ s
    · obtain ⟨Q, h1, h2, h3⟩ := exists_trimmed_piece_of_root hroot hfix (hpiece p hp) hlam (hmark p hp)
      exact ⟨Q, fun _ => ⟨h1, h2, h3⟩⟩
    · exact ⟨p.2, fun hp' => absurd hp' hp⟩
  choose T hT using hex
  refine ⟨T, fun p hp => hT p hp, ?_⟩
  intro p hp q hq hpq
  exact Finset.disjoint_of_subset_left (erase_subset_erase_of_subset (hT p hp).1 p.1)
    (Finset.disjoint_of_subset_right (erase_subset_erase_of_subset (hT q hq).1 q.1)
      (hdisj p hp q hq hpq))


theorem exists_root_spine_piece_of_root (hroot : ∀ x : V, ∃ n : ℕ, pp^[n] x = r)
    (hfix : pp r = r)
    (s : Finset (V × Finset V)) (hne : s.Nonempty)
    (hpiece : ∀ p ∈ s, IsRootedPiece pp p.1 p.2)
    (hdisj : ∀ p ∈ s, ∀ q ∈ s, p ≠ q → Disjoint (p.2.erase p.1) (q.2.erase q.1))
    (hmark : ∀ p ∈ s, lam ≤ (A ∩ p.2).card) :
    ∃ j ∈ s, ∃ Q : Finset V, IsRootedPiece pp r Q ∧ j.2 ⊆ Q ∧ lam ≤ (A ∩ Q).card ∧
      ∀ q ∈ s, q ≠ j → Disjoint (Q.erase r) (q.2.erase q.1) := by
  classical
  obtain ⟨j, hjs, hmin⟩ := Finset.exists_min_image s (fun p : V × Finset V =>
    pdepth pp r hroot p.1) hne
  refine ⟨j, hjs, j.2 ∪ ancestors pp r hroot j.1, ?_, Finset.subset_union_left, ?_, ?_⟩
  · -- `Q` is a rooted piece at `r`
    have hjs' := hpiece j hjs
    refine ⟨?_, ?_, ?_⟩
    · exact Finset.mem_union_right _ (root_mem_ancestors hroot j.1)
    · intro x hx hxr
      rcases Finset.mem_union.mp hx with hx | hx
      · by_cases hxj : x = j.1
        · subst hxj
          refine Finset.mem_union_right _ ?_
          have hpos : 1 ≤ pdepth pp r hroot j.1 := pdepth_pos hroot hxr
          rw [mem_ancestors]
          exact ⟨1, hpos, by simp⟩
        · exact Finset.mem_union_left _ (hjs'.2.1 x hx hxj)
      · exact Finset.mem_union_right _ (pp_mem_ancestors hroot hx hxr)
    · intro x hx
      rcases Finset.mem_union.mp hx with hx | hx
      · obtain ⟨n, hn⟩ := hjs'.2.2 x hx
        refine ⟨n + pdepth pp r hroot j.1, ?_⟩
        rw [Nat.add_comm n (pdepth pp r hroot j.1), Function.iterate_add_apply, hn,
          pdepth_spec hroot j.1]
      · exact iter_eq_root_of_mem_ancestors hroot hx
  · -- at least `lam` marked vertices
    have hsub : A ∩ j.2 ⊆ A ∩ (j.2 ∪ ancestors pp r hroot j.1) := by
      intro x hx
      obtain ⟨hxA, hxj⟩ := Finset.mem_inter.mp hx
      exact Finset.mem_inter.mpr ⟨hxA, Finset.mem_union_left _ hxj⟩
    exact le_trans (hmark j hjs) (Finset.card_le_card hsub)
  · -- disjointness of the parent-edge sets
    intro q hqs hqj
    have hq := hpiece q hqs
    rw [Finset.disjoint_left]
    intro y hy hyq
    obtain ⟨hyr, hyQ⟩ := Finset.mem_erase.mp hy
    obtain ⟨hyq1, hyq2⟩ := Finset.mem_erase.mp hyq
    -- a parent edge of `q` has its child endpoint strictly deeper than `q.1`
    have h1 : pdepth pp r hroot q.1 < pdepth pp r hroot y :=
      pdepth_lt_of_mem_desc_of_root hroot hfix (mem_desc.mpr (hq.2.2 y hyq2)) hyq1
    have h3 := hmin q hqs
    rcases Finset.mem_union.mp hyQ with hy | hy
    · by_cases hyj : y = j.1
      · rw [hyj] at h1; omega
      · exact absurd (Finset.mem_erase.mpr ⟨hyq1, hyq2⟩)
          (Finset.disjoint_left.mp (hdisj j hjs q hqs (Ne.symm hqj))
            (Finset.mem_erase.mpr ⟨hyj, hy⟩))
    · by_cases hyj : y = j.1
      · rw [hyj] at h1; omega
      · have h2 := pdepth_lt_of_ancestor_of_root hroot hfix hy hyj
        omega



end FixedRootSpine


/-! ### The tree partition with a distinguished root-spine piece -/

section RootSpinePartition

variable {pp : V → V} {r : V} {A : Finset V} {lam : ℕ}

/-- The integer tree-piece partition together with one piece extended to the common root. The
returned family retains pairwise disjoint non-root vertex sets; the distinguished spine is
likewise disjoint from all other pieces. -/
theorem exists_root_spine_pieces {k : ℕ} (hforest : IsRootedForest pp r)
    (A : Finset V) (hlam : 2 ≤ lam) (hk : 1 ≤ k) (hA : 3 ^ k * lam ≤ A.card) :
    ∃ (s : Finset (V × Finset V)) (j : V × Finset V) (Q : Finset V),
      3 ^ (k - 1) + 1 ≤ s.card ∧ j ∈ s ∧
      (∀ p ∈ s, IsRootedPiece pp p.1 p.2) ∧
      (∀ p ∈ s, lam ≤ (A ∩ p.2).card ∧ (A ∩ p.2).card ≤ 2 * lam - 1) ∧
      (∀ p ∈ s, ∀ q ∈ s, p ≠ q → Disjoint (p.2.erase p.1) (q.2.erase q.1)) ∧
      IsRootedPiece pp r Q ∧ j.2 ⊆ Q ∧ lam ≤ (A ∩ Q).card ∧
      (∀ q ∈ s, q ≠ j → Disjoint (Q.erase r) (q.2.erase q.1)) := by
  classical
  obtain ⟨s, hcard, hpiece, hmark, hdisj⟩ :=
    exists_tree_pieces hforest A hlam hk hA
  have hne : s.Nonempty := by
    rw [Finset.nonempty_iff_ne_empty]
    intro hempty
    rw [hempty] at hcard
    simp at hcard
  obtain ⟨j, hjs, Q, hQpiece, hjsub, hQmark, hQdisj⟩ :=
    exists_root_spine_piece_of_root hforest.2 hforest.1 s hne hpiece hdisj
      (fun p hp => (hmark p hp).1)
  exact ⟨s, j, Q, hcard, hjs, hpiece, hmark, hdisj, hQpiece, hjsub, hQmark, hQdisj⟩

end RootSpinePartition

end Trim

end Depth

end Hutchcroft
