/-
Swarm `smwtzmkep`, member `m4`, direction (3).
-/
module

public import PercLib.CriticalLRP.Analysis.Cutoff.ExcludedFlux

/-!
# Finite-fibre reindexing of the excluded increment

The excluded flux of the source is written twice in the repository: once as a sum over
**ordered pairs** of vertices (`pairIncr`, the open-coordinate form `Σ_x Σ_{y ∈ B_r(x)}`), and
once as a sum over **closed edges** (`edgeIncr`, the closed-coordinate form `Σ_e`).  The
pointwise bridge is `ExcludedFlux.edgeIncr_mk`: `edgeIncr s(x,y) = pairIncr x y + pairIncr y x`,
together with `ExcludedFlux.edgeIncr_loop`: a loop contributes nothing.

This file supplies the missing *summation* bridge:

* `sum_pairs_eq_sum_sym2`: for a symmetric window `X` the ordered-pair sum over `X × X`
  equals the edge sum over the unordered pairs of `X`;
* `iSup_square_sum_eq_iSup_finset_sum` and `iSup_sym2_sum_eq_iSup_finset_sum`: the two
  cofinality statements identifying the `iSup` over `Finset (V × V)` of ordered-pair sums with
  the `iSup` over square windows, and the `iSup` over `Finset (Sym2 V)` of edge sums with the
  `iSup` over symmetric squares `X.sym2`;
* `tsum_pairs_eq_tsum_sym2`: the abstract `tsum` form of the same identity;
* `tsum_pairIncr_eq_tsum_edgeIncr`: consequently the two `tsum`s of the excluded increment agree,
  `Σ'_p pairIncr p.1 p.2 = Σ'_e edgeIncr e`.

The diagonal is handled explicitly (`pairIncr_self`), and out-of-window pairs never enter
because both sides are confined to `X`.  No derivative, moment or measurability claim is made.
-/

set_option autoImplicit false
set_option linter.unusedSectionVars false

open scoped ENNReal NNReal

@[expose] public section

namespace PercLib.CriticalLRP.Orchestration

attribute [local instance] Classical.propDecidable

variable {V : Type*} [Countable V]

/-! ## Summing a function over an image by its fibres -/

/-- Summing over the image of `f` by fibres recovers the sum over the whole finite set. -/
theorem sum_image_fibre {α : Type*} {β : Type*} [DecidableEq β] {M : Type*} [AddCommMonoid M]
    (s : Finset α) (f : α → β) (g : α → M) :
    ∑ b ∈ s.image f, (∑ a ∈ s.filter (fun a => f a = b), g a) = ∑ a ∈ s, g a := by
  rw [Finset.sum_fiberwise_of_maps_to (t := s.image f) (fun i hi => Finset.mem_image_of_mem f hi)]

/-! ## The two fibres of the unordered-pair map -/

omit [Countable V] in
/-- The fibre of the unordered-pair map over the loop `s(x,x)` is the diagonal point. -/
theorem filter_pair_eq_mk_self [DecidableEq V] {X : Finset V} {x : V} (hx : x ∈ X) :
    (X ×ˢ X).filter (fun p : V × V => s(p.1, p.2) = s(x, x)) = {(x, x)} := by
  classical
  ext p
  simp only [Finset.mem_filter, Finset.mem_product, Finset.mem_singleton]
  constructor
  · rintro ⟨-, h⟩
    rcases Sym2.eq_iff.mp h with ⟨h1, h2⟩ | ⟨h1, h2⟩
    · exact Prod.ext h1 h2
    · exact Prod.ext h1 h2
  · rintro rfl
    exact ⟨⟨hx, hx⟩, rfl⟩

omit [Countable V] in
/-- The fibre of the unordered-pair map over an edge is the pair of its two orderings. -/
theorem filter_pair_eq_mk_pair [DecidableEq V] {X : Finset V} {x y : V} (hx : x ∈ X)
    (hy : y ∈ X) :
    (X ×ˢ X).filter (fun p : V × V => s(p.1, p.2) = s(x, y)) = {(x, y), (y, x)} := by
  classical
  ext p
  simp only [Finset.mem_filter, Finset.mem_product, Finset.mem_insert, Finset.mem_singleton]
  constructor
  · rintro ⟨-, h⟩
    rcases Sym2.eq_iff.mp h with ⟨h1, h2⟩ | ⟨h1, h2⟩
    · exact Or.inl (Prod.ext h1 h2)
    · exact Or.inr (Prod.ext h1 h2)
  · rintro (rfl | rfl)
    · exact ⟨⟨hx, hy⟩, rfl⟩
    · exact ⟨⟨hy, hx⟩, Sym2.eq_swap⟩

/-! ## The finite-window identity -/

omit [Countable V] in
/-- The image of a symmetric window under the unordered-pair map is its symmetric square. -/
theorem image_pair_mk_eq_sym2 [DecidableEq V] (X : Finset V) :
    (X ×ˢ X).image (fun p : V × V => s(p.1, p.2)) = X.sym2 := by
  classical
  ext e
  rw [Finset.mem_image, Finset.mem_sym2_iff]
  constructor
  · rintro ⟨p, hp, rfl⟩
    rw [Finset.mem_product] at hp
    intro a ha
    rw [Sym2.mem_iff] at ha
    rcases ha with rfl | rfl
    · exact hp.1
    · exact hp.2
  · intro he
    exact ⟨Quot.out e, Finset.mem_product.mpr
      ⟨he _ (Sym2.out_fst_mem e), he _ (Sym2.out_snd_mem e)⟩, Sym2.mk_fst_out_snd_out e⟩

omit [Countable V] in
/-- **The finite-window identity, abstract form.**  If an ordered-pair increment `φ` vanishes on
the diagonal and an edge increment `ε` splits over an edge as the sum of its two ordered-pair
increments, then on every finite window `X` the ordered-pair sum over `X × X` equals the edge
sum over the unordered pairs inside `X`. -/
theorem sum_pairs_eq_sum_sym2 {φ : V → V → ℝ≥0∞} {ε : Sym2 V → ℝ≥0∞}
    (hdiag : ∀ x : V, φ x x = 0) (hmk : ∀ x y : V, ε s(x, y) = φ x y + φ y x) (X : Finset V) :
    ∑ x ∈ X, ∑ y ∈ X, φ x y = ∑ e ∈ X.sym2, ε e := by
  classical
  have hfibre : ∀ e ∈ X.sym2,
      (∑ p ∈ (X ×ˢ X).filter (fun p : V × V => s(p.1, p.2) = e), φ p.1 p.2) = ε e := by
    intro e he
    revert he
    induction e using Sym2.ind with
    | _ x y =>
      intro he
      rw [Finset.mk_mem_sym2_iff] at he
      obtain ⟨hx, hy⟩ := he
      by_cases hxy : x = y
      · subst hxy
        rw [filter_pair_eq_mk_self hx, Finset.sum_singleton, hmk x x, hdiag x]
        simp
      · rw [filter_pair_eq_mk_pair hx hy, Finset.sum_insert (by simp [Prod.ext_iff, hxy]),
          Finset.sum_singleton, hmk]
  calc ∑ x ∈ X, ∑ y ∈ X, φ x y
      = ∑ p ∈ X ×ˢ X, φ p.1 p.2 := (Finset.sum_product X X (fun p : V × V => φ p.1 p.2)).symm
    _ = ∑ e ∈ (X ×ˢ X).image (fun p : V × V => s(p.1, p.2)),
          ∑ p ∈ (X ×ˢ X).filter (fun p => s(p.1, p.2) = e), φ p.1 p.2 :=
        (sum_image_fibre _ _ _).symm
    _ = ∑ e ∈ X.sym2, ε e := by
        rw [image_pair_mk_eq_sym2 X]
        exact Finset.sum_congr rfl hfibre

/-! ## The diagonal of the excluded increment -/

omit [Countable V] in
/-- A vertex contributes nothing paired with itself. -/
theorem pairIncr_self (d : V → V → Prop) [DecidableRel d] (ω : Config V) (o : V)
    (A : Finset V) (x : V) : pairIncr d ω o A x x = 0 := by
  simp only [pairIncr]
  by_cases hxb : Connects ω o x <;> simp [hxb]

/-- **The finite-window identity for the excluded increment**: on a symmetric window `X` the
open-coordinate ordered-pair sum equals the closed-coordinate edge sum. -/
theorem sum_pairIncr_eq_sum_edgeIncr (d : V → V → Prop) [DecidableRel d]
    (hd : ∀ a b, (d a b ↔ d b a)) (ω : Config V) (o : V) (A : Finset V) (X : Finset V) :
    ∑ x ∈ X, ∑ y ∈ X, pairIncr d ω o A x y
      = ∑ e ∈ X.sym2, edgeIncr d hd ω o A e :=
  sum_pairs_eq_sum_sym2 (pairIncr_self d ω o A) (fun x y => edgeIncr_mk d hd ω o A x y) X

/-! ## Loop-free form -/

/-- **Loop-free form of the finite-window identity.**  A loop of the window carries no edge
increment (`edgeIncr_loop`), so the edge sum may be taken over the non-loop edges of `X` alone. -/
theorem sum_pairIncr_eq_sum_edgeIncr_notDiag [DecidableEq V] (d : V → V → Prop) [DecidableRel d]
    (hd : ∀ a b, (d a b ↔ d b a)) (ω : Config V) (o : V) (A : Finset V) (X : Finset V) :
    ∑ x ∈ X, ∑ y ∈ X, pairIncr d ω o A x y
      = ∑ e ∈ X.sym2.filter (fun e => ¬ e.IsDiag), edgeIncr d hd ω o A e := by
  have hfilter : (∑ e ∈ X.sym2, (if ¬ e.IsDiag then edgeIncr d hd ω o A e else 0))
      = ∑ e ∈ X.sym2, edgeIncr d hd ω o A e := by
    refine Finset.sum_congr rfl fun e _ => ?_
    induction e using Sym2.ind with
    | _ x y =>
      by_cases hxy : x = y
      · subst hxy
        rw [ite_eq_right (c := ¬ s(x, x).IsDiag)
          (not_not.mpr (Sym2.mk_isDiag_iff.mpr rfl))]
        exact (edgeIncr_loop d hd ω o A x).symm
      · rw [ite_eq_left (c := ¬ s(x, y).IsDiag)
          (fun hdiag => hxy (Sym2.mk_isDiag_iff.mp hdiag))]
  rw [Finset.sum_filter, hfilter, sum_pairIncr_eq_sum_edgeIncr d hd ω o A X]

/-! ## Cofinality of square windows and symmetric squares -/

omit [Countable V] in
/-- Square windows are cofinal among the finite subsets of `V × V`. -/
theorem iSup_square_sum_eq_iSup_finset_sum (φ : V × V → ℝ≥0∞) :
    (⨆ X : Finset V, ∑ p ∈ X ×ˢ X, φ p) = ⨆ P : Finset (V × V), ∑ p ∈ P, φ p := by
  refine le_antisymm (iSup_le fun X => le_iSup (fun P : Finset (V × V) => ∑ p ∈ P, φ p) (X ×ˢ X)) ?_
  refine iSup_le fun P => ?_
  refine le_iSup_of_le (P.image Prod.fst ∪ P.image Prod.snd)
    (Finset.sum_le_sum_of_subset_of_nonneg ?_ (fun i _ _ => zero_le))
  intro p hp
  exact Finset.mem_product.mpr
    ⟨Finset.mem_union_left _ (Finset.mem_image_of_mem Prod.fst hp),
      Finset.mem_union_right _ (Finset.mem_image_of_mem Prod.snd hp)⟩

omit [Countable V] in
/-- Symmetric squares are cofinal among the finite sets of edges: every finite edge set is
contained in `X.sym2` for the window `X` of the endpoints of its members. -/
theorem iSup_sym2_sum_eq_iSup_finset_sum (g : Sym2 V → ℝ≥0∞) :
    (⨆ X : Finset V, ∑ e ∈ X.sym2, g e) = ⨆ E : Finset (Sym2 V), ∑ e ∈ E, g e := by
  classical
  refine le_antisymm (iSup_le fun X => le_iSup (fun E : Finset (Sym2 V) => ∑ e ∈ E, g e) X.sym2) ?_
  refine iSup_le fun E => ?_
  refine le_iSup_of_le (E.biUnion fun e => {(Quot.out e).1, (Quot.out e).2})
    (Finset.sum_le_sum_of_subset_of_nonneg ?_ (fun i _ _ => zero_le))
  intro e he
  rw [Finset.mem_sym2_iff]
  intro a ha
  rw [Finset.mem_biUnion]
  refine ⟨e, he, ?_⟩
  rw [← Sym2.mk_fst_out_snd_out e] at ha
  rw [Sym2.mem_iff] at ha
  rcases ha with rfl | rfl <;> simp

/-! ## The `tsum` identity -/

omit [Countable V] in
/-- **The `tsum` identity, abstract form.**  An ordered-pair increment vanishing on the diagonal
whose symmetrization is an edge increment has the same `tsum` read over ordered pairs or over
unordered edges.  Both sides are `iSup`s of finite sums: square windows are cofinal among the
finite subsets of `V × V`, and symmetric squares are cofinal among the finite sets of edges. -/
theorem tsum_pairs_eq_tsum_sym2 {φ : V → V → ℝ≥0∞} {ε : Sym2 V → ℝ≥0∞}
    (hdiag : ∀ x : V, φ x x = 0) (hmk : ∀ x y : V, ε s(x, y) = φ x y + φ y x) :
    (∑' p : V × V, φ p.1 p.2) = ∑' e : Sym2 V, ε e := by
  classical
  rw [ENNReal.tsum_eq_iSup_sum, ENNReal.tsum_eq_iSup_sum]
  calc (⨆ P : Finset (V × V), ∑ p ∈ P, φ p.1 p.2)
      = ⨆ X : Finset V, ∑ p ∈ X ×ˢ X, φ p.1 p.2 :=
        (iSup_square_sum_eq_iSup_finset_sum (fun p : V × V => φ p.1 p.2)).symm
    _ = ⨆ X : Finset V, ∑ e ∈ X.sym2, ε e := by
        refine iSup_congr fun X => ?_
        rw [Finset.sum_product]
        exact sum_pairs_eq_sum_sym2 hdiag hmk X
    _ = ⨆ E : Finset (Sym2 V), ∑ e ∈ E, ε e := iSup_sym2_sum_eq_iSup_finset_sum ε

/-- **The ordered-pair and edge `tsum`s of the excluded increment agree.** -/
theorem tsum_pairIncr_eq_tsum_edgeIncr (d : V → V → Prop) [DecidableRel d]
    (hd : ∀ a b, (d a b ↔ d b a)) (ω : Config V) (o : V) (A : Finset V) :
    (∑' p : V × V, pairIncr d ω o A p.1 p.2) = ∑' e : Sym2 V, edgeIncr d hd ω o A e :=
  tsum_pairs_eq_tsum_sym2 (pairIncr_self d ω o A) (fun x y => edgeIncr_mk d hd ω o A x y)

end PercLib.CriticalLRP.Orchestration

/-! ## Axiom audit -/

set_option linter.hashCommand false
set_option linter.style.longLine false

namespace PercLib.CriticalLRP.Orchestration

#print axioms PercLib.CriticalLRP.Orchestration.sum_image_fibre
#print axioms PercLib.CriticalLRP.Orchestration.filter_pair_eq_mk_self
#print axioms PercLib.CriticalLRP.Orchestration.filter_pair_eq_mk_pair
#print axioms PercLib.CriticalLRP.Orchestration.image_pair_mk_eq_sym2
#print axioms PercLib.CriticalLRP.Orchestration.sum_pairs_eq_sum_sym2
#print axioms PercLib.CriticalLRP.Orchestration.pairIncr_self
#print axioms PercLib.CriticalLRP.Orchestration.sum_pairIncr_eq_sum_edgeIncr
#print axioms PercLib.CriticalLRP.Orchestration.sum_pairIncr_eq_sum_edgeIncr_notDiag
#print axioms PercLib.CriticalLRP.Orchestration.iSup_square_sum_eq_iSup_finset_sum
#print axioms PercLib.CriticalLRP.Orchestration.iSup_sym2_sum_eq_iSup_finset_sum
#print axioms PercLib.CriticalLRP.Orchestration.tsum_pairs_eq_tsum_sym2
#print axioms PercLib.CriticalLRP.Orchestration.tsum_pairIncr_eq_tsum_edgeIncr

end PercLib.CriticalLRP.Orchestration
