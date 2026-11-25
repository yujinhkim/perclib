/-
Migration source: https://github.com/yujinhkim/Critical-Long-range-percolation
Integration revision: 3b3d1d0e43ef940bfaa2292ee5c2ee094ac4edbf
Licence: Apache-2.0 for the PercLib Lean sources and tooling; see third_party/critical-lrp/.
External provenance and modifications are recorded in the file-specific notices below.
-/

/-
The tree-graph inequality (I.2.2) of Hutchcroft, *Critical long-range percolation I*,
arXiv:2508.18807v1, Section I.2.1, p. 22, from the BK inequality.

Ingredients: the deterministic branch-point decomposition `exists_branch_split_mem`
(Decomp/Main), the BK inequality `bk_three`, and the tree-sum recursion
`TreeSumRecursion`, which is the purely combinatorial identity `TS Z = ∑_A ∑_w k v w · TS A ·
TS (Z \ A)` over the splits `A` of `Z` containing a fixed basepoint, normalized so that each
unordered split is counted once.  Its one-sided consequence `TS_split_le` (any single split)
is proved unconditionally in `TreeRec.lean`.
-/
module

public import Mathlib
public import PercLib.CriticalLRP.TreeExpansion.MomentAssembly

set_option autoImplicit true

set_option autoImplicit false
set_option linter.unusedSectionVars false
set_option maxHeartbeats 2000000

@[expose] public section

namespace PercLib.CriticalLRP.TreeGraph

open Finset
open PercLib.CriticalLRP.TreeExpansion

variable {V : Type*} [Fintype V] [DecidableEq V]
variable {E : Type*} [Fintype E] [DecidableEq E]
variable {ends : E → Sym2 V} {s : Finset E} {v : V}

/-! ### Elementary probability facts -/

theorem prob_univ (pr : E → ℝ) : prob pr (Set.univ : Set (Finset E)) = 1 := by
  rw [prob, PercLib.CriticalLRP.probability]
  simp only [PercLib.CriticalLRP.expectation, Set.mem_univ, ite_true, mul_one]
  exact PercLib.CriticalLRP.configurationLaw_sum pr

theorem prob_iUnion_le_sum {pr : E → ℝ} (hp : ∀ e, 0 ≤ pr e) (hp1 : ∀ e, pr e ≤ 1)
    {ι : Type*} [Fintype ι] (A : ι → Set (Finset E)) :
    prob pr (⋃ i, A i) ≤ ∑ i, prob pr (A i) := by
  have h := prob_biUnion_le_sum hp hp1 (Finset.univ : Finset ι) A
  simpa using h

theorem isIncreasing_conn_forall {α : Type*} (y : α → V) (A : Finset α) (w : V) :
    IsIncreasing {s : Finset E | ∀ a ∈ A, Conn ends s w (y a)} := by
  intro s hs t hst a ha
  exact conn_mono hst (hs a ha)

/-! ### The tree-sum recursion -/

/-- **The tree-graph recursion identity**, for the label type `Fin m`: the normalized tree sum
over the leaf set `Z` is the sum over the splits `A ∋ a₀` of `Z` (one representative of each
unordered split) of the branch-point contribution.  This is the combinatorial content of
(I.2.2) that remains to be proved separately; its one-sided consequence `TS_split_le` is
proved unconditionally in `TreeRec.lean`. -/
def TreeSumRecursionAt (k : V → V → ℝ) (m : ℕ) : Prop :=
  ∀ (Z : Finset (Fin m)) (y : Fin m → V) (v : V) (a₀ : Fin m), a₀ ∈ Z → 2 ≤ Z.card →
    TS k Z y v = ∑ A ∈ Z.powerset.filter (fun A => A.Nonempty ∧ A ≠ Z ∧ a₀ ∈ A),
      ∑ w : V, k v w * TS k A y w * TS k (Z \ A) y w


/-! ### The induction -/

theorem prob_le_TS_aux {α : Type*} [Fintype α] [DecidableEq α]
    (pr : E → ℝ) (hp : ∀ e, 0 ≤ pr e) (hp1 : ∀ e, pr e ≤ 1) (hBK : BKIncreasing pr)
    (k : V → V → ℝ) (hk_eq : ∀ a b, twoPoint pr ends a b = k a b)
    (hk : ∀ a b, 0 ≤ k a b) (hkuu : ∀ u : V, k u u = 1)
    (hrec : ∀ (Z : Finset α) (y : α → V) (v : V) (a₀ : α), a₀ ∈ Z → 2 ≤ Z.card →
      TS k Z y v = ∑ A ∈ Z.powerset.filter (fun A => A.Nonempty ∧ A ≠ Z ∧ a₀ ∈ A),
        ∑ w : V, k v w * TS k A y w * TS k (Z \ A) y w)
    (y : α → V) :
    ∀ (n : ℕ) (Z : Finset α) (v : V), Z.card = n → Z.Nonempty →
      prob pr {t | ∀ a ∈ Z, Conn ends t v (y a)} ≤ TS k Z y v := by
  intro n
  induction n using Nat.strong_induction_on with
  | _ n ih =>
    intro Z v hZ hne
    classical
    rcases Nat.lt_or_ge Z.card 2 with h1 | h1
    · -- a single label
      have hc1 : Z.card = 1 := by
        have := Finset.card_pos.mpr hne
        omega
      obtain ⟨a, rfl⟩ := Finset.card_eq_one.mp hc1
      have hev : {t : Finset E | ∀ b ∈ ({a} : Finset α), Conn ends t v (y b)}
          = {t | Conn ends t v (y a)} := by
        ext t; simp
      rw [hev, TS_singleton]
      exact le_of_eq (hk_eq v (y a))
    · -- at least two labels
      obtain ⟨a₀, ha₀⟩ := hne
      have hne0 : Z.Nonempty := ⟨a₀, ha₀⟩
      have hne' : (Z.erase a₀).Nonempty := by
        rw [← Finset.card_pos, Finset.card_erase_of_mem ha₀]
        have := Finset.card_pos.mpr hne0
        omega
      have hdisj : Disjoint ({a₀} : Finset α) (Z.erase a₀) :=
        Finset.disjoint_singleton_left.mpr (Finset.notMem_erase a₀ Z)
      by_cases hall : ∀ a ∈ Z, ∀ b ∈ Z, y a = y b
      · -- all terminal values agree
        have hyu : ∀ a ∈ Z, y a = y a₀ := fun a ha => hall a ha a₀ ha₀
        have hev : {t : Finset E | ∀ a ∈ Z, Conn ends t v (y a)}
            = {t | Conn ends t v (y a₀)} := by
          ext t
          constructor
          · intro h; exact h a₀ ha₀
          · intro h a ha; rw [hyu a ha]; exact h
        rw [hev]
        have hsplit := TS_split_le (k := k) hk hdisj ⟨a₀, Finset.mem_singleton_self a₀⟩ hne' y v
        rw [← Finset.insert_eq, Finset.insert_erase ha₀] at hsplit
        have hsingle : ∀ w : V, TS k ({a₀} : Finset α) y w = k w (y a₀) :=
          fun w => TS_singleton k a₀ y w
        have hcongr : TS k (Z.erase a₀) y (y a₀)
            = TS k (Z.erase a₀) (fun _ => y a₀) (y a₀) :=
          TS_congr (fun a ha => hyu a (Finset.mem_of_mem_erase ha)) _
        have hconst : 1 ≤ TS k (Z.erase a₀) y (y a₀) := by
          rw [hcongr]
          exact one_le_TS_const (k := k) (hk := hk) (huu := hkuu (y a₀))
            (n := (Z.erase a₀).card) (Z := Z.erase a₀) rfl hne'
        have hnonneg : ∀ w : V, 0 ≤ k v w * TS k ({a₀} : Finset α) y w *
            TS k (Z.erase a₀) y w :=
          fun w => mul_nonneg (mul_nonneg (hk _ _) (TS_nonneg hk _ _ _)) (TS_nonneg hk _ _ _)
        have hterm : k v (y a₀) ≤ ∑ w : V, k v w * TS k ({a₀} : Finset α) y w *
            TS k (Z.erase a₀) y w := by
          have h1' : k v (y a₀) ≤ k v (y a₀) * TS k (Z.erase a₀) y (y a₀) := by
            calc k v (y a₀) = k v (y a₀) * 1 := (mul_one _).symm
              _ ≤ k v (y a₀) * TS k (Z.erase a₀) y (y a₀) :=
                  mul_le_mul_of_nonneg_left hconst (hk _ _)
          refine le_trans h1' (le_trans (le_of_eq ?_) (Finset.single_le_sum
            (f := fun w => k v w * TS k ({a₀} : Finset α) y w * TS k (Z.erase a₀) y w)
            (fun w _ => hnonneg w) (Finset.mem_univ (y a₀))))
          rw [hsingle, hkuu]
          ring
        exact le_trans (le_of_eq (hk_eq v (y a₀))) (le_trans hterm hsplit)
      · -- genuinely different terminal values: branch-point decomposition
        push Not at hall
        obtain ⟨a₁, ha₁, b₁, hb₁, hab₁⟩ := hall
        have hne'' : ∃ a b : ↥Z, y a.val ≠ y b.val :=
          ⟨⟨a₁, ha₁⟩, ⟨b₁, hb₁⟩, hab₁⟩
        set S : Finset (Finset α) := Z.powerset.filter (fun A => A.Nonempty ∧ A ≠ Z ∧ a₀ ∈ A)
          with hS
        set E0 : V → Set (Finset E) := fun w => {t | Conn ends t v w} with hE0
        set Eg : Finset α → V → Set (Finset E) :=
          fun A w => {t | ∀ a ∈ A, Conn ends t w (y a)} with hEg
        have hsub : {t : Finset E | ∀ a ∈ Z, Conn ends t v (y a)}
            ⊆ ⋃ (A : Finset α) (_ : A ∈ S), ⋃ (w : V),
                DisjOcc3 (E0 w) (Eg A w) (Eg (Z \ A) w) := by
          intro t ht
          obtain ⟨w, A, W0, WA, WB, hmem, hneA, hcA, hW0, hWA, hWB, hd1, hd2, hd3,
            hc0, hcA', hcB⟩ :=
            exists_branch_split_mem (ends := ends) (s := t) (v := v)
              (y := fun a : ↥Z => y a.val) (fun a => ht a.val a.2) hne'' ⟨a₀, ha₀⟩
          set A' : Finset α := A.image Subtype.val with hA'
          have hA'sub : A' ⊆ Z := by
            intro a ha
            obtain ⟨b, -, rfl⟩ := Finset.mem_image.mp ha
            exact b.2
          have hA'ne : A'.Nonempty := hneA.image _
          have hA'neZ : A' ≠ Z := by
            intro hEq
            have hcard1 : A'.card = A.card := Finset.card_image_of_injective _ Subtype.val_injective
            have hproper : A ⊂ Finset.univ := by
              rw [Finset.ssubset_iff_subset_ne]
              refine ⟨Finset.subset_univ _, ?_⟩
              intro huniv
              obtain ⟨b, hb⟩ := hcA
              rw [Finset.eq_univ_iff_forall] at huniv
              rw [Finset.mem_compl] at hb
              exact hb (huniv b)
            have hlt : A.card < Z.card := by
              have hc := Finset.card_lt_card hproper
              rwa [Finset.card_univ, Fintype.card_coe] at hc
            have h3 : A'.card = Z.card := by rw [hEq]
            omega
          refine Set.mem_iUnion₂.mpr ⟨A', ?_, Set.mem_iUnion.mpr ⟨w, ?_⟩⟩
          · rw [hS, Finset.mem_filter, Finset.mem_powerset]
            exact ⟨hA'sub, hA'ne, hA'neZ, by rw [hA']; exact Finset.mem_image_of_mem _ hmem⟩
          · refine ⟨W0, WA, WB, hW0, hWA, hWB, hc0, ?_, ?_, hd1, hd2, hd3⟩
            · intro a ha
              obtain ⟨b, hb, rfl⟩ := Finset.mem_image.mp ha
              exact hcA' b hb
            · intro a ha
              rw [Finset.mem_sdiff] at ha
              refine hcB ⟨a, ha.1⟩ ?_
              rw [Finset.mem_compl]
              intro hmemA
              exact ha.2 (by rw [hA']; exact Finset.mem_image_of_mem _ hmemA)
        -- the chain of inequalities
        have hstep1 : prob pr {t | ∀ a ∈ Z, Conn ends t v (y a)}
            ≤ ∑ A ∈ S, prob pr (⋃ (w : V), DisjOcc3 (E0 w) (Eg A w) (Eg (Z \ A) w)) := by
          refine le_trans (prob_mono hp hp1 hsub) ?_
          have hble := prob_biUnion_le_sum hp hp1 S
            (fun A => ⋃ (w : V), DisjOcc3 (E0 w) (Eg A w) (Eg (Z \ A) w))
          simpa using hble
        have hstep3 : ∀ A ∈ S, ∀ w : V, prob pr (DisjOcc3 (E0 w) (Eg A w) (Eg (Z \ A) w))
            ≤ prob pr (E0 w) * prob pr (Eg A w) * prob pr (Eg (Z \ A) w) :=
          fun A _ w => bk_three hBK (conn_isIncreasing ends v w) (isIncreasing_conn_forall y A w)
            (isIncreasing_conn_forall y (Z \ A) w)
        have hstep4 : ∀ A ∈ S, ∀ w : V,
            prob pr (E0 w) * prob pr (Eg A w) * prob pr (Eg (Z \ A) w)
              ≤ k v w * TS k A y w * TS k (Z \ A) y w := by
          intro A hA w
          rw [hS, Finset.mem_filter, Finset.mem_powerset] at hA
          obtain ⟨hAZ, hAne, hAneZ, -⟩ := hA
          have hAssub : A ⊂ Z := Finset.ssubset_iff_subset_ne.mpr ⟨hAZ, hAneZ⟩
          have hAcard : A.card < n := by
            have hc := Finset.card_lt_card hAssub
            rw [hZ] at hc
            exact hc
          have hltA : prob pr (Eg A w) ≤ TS k A y w := ih A.card hAcard A w rfl hAne
          have hBne : (Z \ A).Nonempty := by
            have hnot : ¬ Z ⊆ A := fun h => hAneZ (Finset.Subset.antisymm hAZ h)
            rw [Finset.subset_iff] at hnot
            push Not at hnot
            obtain ⟨x, hxZ, hxA⟩ := hnot
            exact ⟨x, Finset.mem_sdiff.mpr ⟨hxZ, hxA⟩⟩
          have hBcard : (Z \ A).card < n := by
            have hsub2 : Z \ A ⊆ Z := Finset.sdiff_subset
            have hne2 : Z \ A ≠ Z := by
              intro h
              obtain ⟨x, hx⟩ := hAne
              have hx2 : x ∈ Z \ A := by rw [h]; exact hAZ hx
              exact (Finset.mem_sdiff.mp hx2).2 hx
            have hc := Finset.card_lt_card (Finset.ssubset_iff_subset_ne.mpr ⟨hsub2, hne2⟩)
            rw [hZ] at hc
            exact hc
          have hltB : prob pr (Eg (Z \ A) w) ≤ TS k (Z \ A) y w :=
            ih (Z \ A).card hBcard (Z \ A) w rfl hBne
          have hE0eq : prob pr (E0 w) = k v w := hk_eq v w
          rw [hE0eq]
          have hPB : 0 ≤ prob pr (Eg (Z \ A) w) := prob_nonneg hp hp1 _
          have hTSA : 0 ≤ TS k A y w := TS_nonneg hk _ _ _
          have h00 : 0 ≤ k v w := hk _ _
          calc k v w * prob pr (Eg A w) * prob pr (Eg (Z \ A) w)
              ≤ k v w * TS k A y w * prob pr (Eg (Z \ A) w) := by
                refine mul_le_mul_of_nonneg_right ?_ hPB
                exact mul_le_mul_of_nonneg_left hltA h00
            _ ≤ k v w * TS k A y w * TS k (Z \ A) y w :=
                mul_le_mul_of_nonneg_left hltB (mul_nonneg h00 hTSA)
        have hrecZ : (∑ A ∈ S, ∑ w : V, k v w * TS k A y w * TS k (Z \ A) y w) = TS k Z y v := by
          have h := hrec Z y v a₀ ha₀ h1
          rw [hS]
          exact h.symm
        calc prob pr {t | ∀ a ∈ Z, Conn ends t v (y a)}
            ≤ ∑ A ∈ S, prob pr (⋃ (w : V), DisjOcc3 (E0 w) (Eg A w) (Eg (Z \ A) w)) := hstep1
          _ ≤ ∑ A ∈ S, ∑ w : V, prob pr (DisjOcc3 (E0 w) (Eg A w) (Eg (Z \ A) w)) :=
              Finset.sum_le_sum fun A hA => prob_iUnion_le_sum hp hp1 _
          _ ≤ ∑ A ∈ S, ∑ w : V, prob pr (E0 w) * prob pr (Eg A w) * prob pr (Eg (Z \ A) w) :=
              Finset.sum_le_sum fun A hA => Finset.sum_le_sum fun w _ => hstep3 A hA w
          _ ≤ ∑ A ∈ S, ∑ w : V, k v w * TS k A y w * TS k (Z \ A) y w :=
              Finset.sum_le_sum fun A hA => Finset.sum_le_sum fun w _ => hstep4 A hA w
          _ = TS k Z y v := hrecZ

/-! ### The tree sums agree with the repository's `treeSum` -/

noncomputable def LTon.equivLT (m : ℕ) : LTon (Fin m) Finset.univ ≃ RTree.LT (Fin m) where
  toFun t := ⟨t.1, t.2.1, by rw [← List.toFinset_card_of_nodup t.2.1, t.2.2]; simp⟩
  invFun t := ⟨t.1, t.2.1, by
    refine Finset.eq_univ_of_card _ ?_
    rw [List.toFinset_card_of_nodup t.2.1, t.2.2]⟩
  left_inv t := rfl
  right_inv t := rfl

theorem OnTrees_univ_eq (k : V → V → ℝ) (m : ℕ) (y : Fin m → V) (v : V) :
    OnTrees k (Finset.univ : Finset (Fin m)) y v
      = ∑ t : RTree.LT (Fin m), RTree.wt k t.1 (fun q => y (RTree.leafOfPos t.1 q)) v := by
  rw [OnTrees]
  refine Fintype.sum_equiv (LTon.equivLT m) _ _ (fun t => ?_)
  show RTree.wtL k t.1 y v = RTree.wt k t.1 (fun q => y (RTree.leafOfPos t.1 q)) v
  exact (RTree.wt_eq_wtL k t.1 y v).symm

theorem TS_univ_eq_treeSum (k : V → V → ℝ) (m : ℕ) (y : Fin m → V) (v : V) :
    TS k (Finset.univ : Finset (Fin m)) y v = treeSum k m v y := by
  rw [TS, OnTrees_univ_eq, treeSum, Finset.card_univ, Fintype.card_fin]

/-- **The tree-graph inequality (I.2.2) from the BK inequality**, given the tree-sum
recursion identity `TreeSumRecursionAt`. -/
theorem treeGraphBound_of_bk (pr : E → ℝ) (hp : ∀ e, 0 ≤ pr e) (hp1 : ∀ e, pr e ≤ 1)
    (hBK : BKIncreasing pr)
    (hrec : ∀ m : ℕ, TreeSumRecursionAt (twoPoint pr ends) m) :
    TreeGraphBound pr ends (twoPoint pr ends) := by
  intro m hm x
  classical
  have hk0 : ∀ a b : V, 0 ≤ twoPoint pr ends a b := fun a b => prob_nonneg hp hp1 _
  have hkuu : ∀ u : V, twoPoint pr ends u u = 1 := by
    intro u
    have huniv : {t : Finset E | Conn ends t u u} = Set.univ := by
      ext t; simp [conn_refl]
    rw [twoPoint, huniv, prob_univ]
  have h := prob_le_TS_aux (ends := ends) pr hp hp1 hBK (twoPoint pr ends) (fun a b => rfl)
    hk0 hkuu (hrec m) (y := fun j : Fin m => x (Fin.succ j)) m Finset.univ (x 0)
    (by simp) ⟨⟨0, hm⟩, Finset.mem_univ _⟩
  have hev : {t : Finset E | ∀ a ∈ (Finset.univ : Finset (Fin m)), Conn ends t (x 0)
        ((fun j : Fin m => x (Fin.succ j)) a)}
      = {t : Finset E | ∀ i : Fin (m + 1), Conn ends t (x 0) (x i)} := by
    ext t
    constructor
    · intro h' i
      refine Fin.cases ?_ (fun j => h' j (Finset.mem_univ j)) i
      exact conn_refl ends t (x 0)
    · intro h' a _
      exact h' (Fin.succ a)
  rw [hev, TS_univ_eq_treeSum] at h
  exact h

end PercLib.CriticalLRP.TreeGraph
