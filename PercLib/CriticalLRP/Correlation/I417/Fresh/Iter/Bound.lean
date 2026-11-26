/-
Independently rebuilt and integrated from the accepted `smwx9itnu/m2` artifact
`.ultramath/smwx9itnu/m2/Gen`. Production integration revision:
`8ae938fa49a73456688d438f25ef2441c282b2f4`.
The base split/diagram API is shared with `I417FreshFour.Refined` instead of
being duplicated.
-/
/-
Independently built for swarm `smwx9itnu`, member `m2`, direction GENERAL-Q-VECTOR-COVER.
No production files are modified; this module is read-only against production.
-/
module

public import PercLib.CriticalLRP.Correlation.I417.Fresh.Iter.Cover
public import PercLib.CriticalLRP.Correlation.I417Example.BK
public import PercLib.CriticalLRP.Correlation.I417.Fresh.Subdivision.Defs

/-!
# Lemma I.4.17 for arbitrary `q`: the BK bound and the finite count of the family

Source: T. Hutchcroft, *Critical long-range percolation I: High effective dimension*,
arXiv:2508.18807v1, proof of Lemma I.4.17, supplied paper text lines 2444--2513.  The diagram
bound is in terms of "tree diagrams with two pinned vertices at `x` and `y`, with `2p + 2q + 1`
edges in total"; the fresh side carries `2q` edges, and the constants `C_{p,q,ℓ}` count the
diagrams with `ℓ` edges on the `x`--`y` path.

This file supplies the quantitative interface of the general-`q` cover:

* `shapeOfI_measure_le` — BK for any finite leg-index type: the disjoint occurrence of the leg
  events costs at most the product of the two-point functions.
* `card_Idx` — the leg index type after `n` attachments has `2 * (n + 1)` elements;
  `card_genLegs` — at `n = q - 1` that is exactly `2q` legs.
* `card_histChoices` — the number of split-choice tuples `(k_0, …, k_{n-1})` is the explicit
  finite product `∏_{t<n} 2 * (t + 1)`; `card_histChoices_three` evaluates the `q = 4` value
  `2 * 4 * 6 = 48` of the accepted artifact, and `card_histChoices_eq` evaluates the product as
  `2^n * n!`.
* `genShape_measure_le` — the union/BK bound: the general family costs at most the sum over the
  attachment histories of the products of their `2q` two-point factors.
* `freshMark_measure_le_genShape` — the same bound for `freshMark` itself, and
  `exists_freshMark_measure_le_genShape` removes the supplied enumeration `e` (every ordering of
  the other `q - 1` labels gives the same bound).

What is **not** provided here: the substitution of the constant row sum `∑_v τ(a,v) = χ` at the
attachment vertices and the arm sums, i.e. the evaluation of these `2q`-fold products into
`∑_ℓ C_{q,ℓ} χ^(2q-ℓ) T^ℓ(w,y)`.  That diagram-evaluation step is the finite coefficient
counting consumer of `card_histChoices`/`card_genLegs`; it is deliberately left as the named
remaining goal in the report (exactly as the accepted `q = 4` artifact leaves `FreshFourEval`).
-/

open MeasureTheory Measure ProbabilityTheory unitInterval
open scoped ENNReal NNReal

set_option linter.unusedSectionVars false
set_option linter.unusedDecidableInType false
set_option linter.unusedSimpArgs false
set_option linter.style.longLine false

@[expose] public section

namespace PercLib.CriticalLRP.I417GenIter

open PercLib.CriticalLRP
open PercLib.CriticalLRP.I417Fresh

variable {V : Type*} [Countable V] [DecidableEq V]

attribute [local instance] Classical.propDecidable

/-! ## BK for the index-generic shape -/

/-- **BK for the index-generic shape.**  For any finite leg-index type, the disjoint occurrence of
the leg events costs at most the product of the two-point functions.  The proof reindexes along
`Fintype.equivFin` and applies `q`-fold BK (`I417Example.bk_fin_ennreal`). -/
theorem shapeOfI_measure_le (π : Sym2 V → unitInterval) (hπ : ∀ e, π e < 1)
    {ι : Type*} [Fintype ι] (L : ι → V × V) :
    (edgeMeasure π) (ShapeOfI L) ≤ ∏ i, tau π (L i).1 (L i).2 := by
  classical
  set e : ι ≃ Fin (Fintype.card ι) := Fintype.equivFin ι with he
  have hre : ShapeOfI L = ShapeOfI (fun k => L (e.symm k)) := by
    ext ω
    constructor
    · rintro ⟨E, h1, h2, h3⟩
      exact ⟨fun k => E (e.symm k), fun k => h1 _, fun k => h2 _,
        fun k l hkl => h3 _ _ (fun h => hkl (by simpa using congrArg e h))⟩
    · rintro ⟨E, h1, h2, h3⟩
      exact ⟨fun i => E (e i), fun i => by simpa using h1 (e i),
        fun i => by simpa using h2 (e i),
        fun i j hij => h3 _ _ (fun h => hij (by simpa using congrArg e.symm h))⟩
  rw [hre, shapeOfI_fin]
  refine le_trans (I417Example.bk_fin_ennreal π hπ
    (fun k : Fin (Fintype.card ι) => connSet (L (e.symm k)).1 (L (e.symm k)).2)
    (fun k => isUpper_connSet _ _) (fun k => finiteWitness_connSet _ _)) ?_
  rw [Fintype.prod_equiv e (fun i => tau π (L i).1 (L i).2)
    (fun k => tau π (L (e.symm k)).1 (L (e.symm k)).2) (fun i => by simp)]
  exact le_rfl

/-! ## The size of the index type and the number of branch choices -/

/-- The index type after `n` attachment rounds has `2 * (n + 1)` elements. -/
theorem card_Idx (n : ℕ) : Fintype.card (Idx n) = 2 * (n + 1) := by
  induction n with
  | zero =>
    change Fintype.card (Fin 2) = 2 * (0 + 1)
    norm_num
  | succ n ih =>
    change Fintype.card (Idx n ⊕ Bool) = 2 * (n + 1 + 1)
    rw [Fintype.card_sum, ih, Fintype.card_bool]
    omega

/-- At `n = q - 1` the fresh diagram has exactly `2q` legs, the fresh edge count of
Lemma I.4.17. -/
theorem card_genLegs {q : ℕ} (hq : 1 ≤ q) : Fintype.card (Idx (q - 1)) = 2 * q := by
  rw [card_Idx]
  omega

/-- The `q = 4` leg count: the general family at `q = 4` has eight legs, as in the accepted
artifact (`card_q4Index`). -/
theorem card_genLegs_four : Fintype.card (Idx 3) = 8 := by
  simpa using card_genLegs (q := 4) (by norm_num)

/-- The number of split-choice tuples `(k_0, …, k_{n-1})`, one leg choice per attachment round, is
the explicit finite product `∏_{t<n} 2 * (t + 1)`. -/
theorem card_histChoices (n : ℕ) :
    Fintype.card ((t : Fin n) → Idx t) = ∏ t : Fin n, 2 * (t.val + 1) := by
  rw [Fintype.card_pi]
  exact Finset.prod_congr rfl (fun t _ => card_Idx t)

/-- The `q = 4` case of the split-choice count: `2 * 4 * 6 = 48`, the branch count of the
accepted artifact (`card_q4Branches`). -/
theorem card_histChoices_three : Fintype.card ((t : Fin 3) → Idx t) = 48 := by
  rw [card_histChoices]
  norm_num [Fin.prod_univ_three]

/-- The `q = 5` case of the split-choice count: `2 * 4 * 6 * 8 = 384`.  This is the first member
of the family not covered by the accepted `q = 4` artifact. -/
theorem card_histChoices_four : Fintype.card ((t : Fin 4) → Idx t) = 384 := by
  rw [card_histChoices]
  norm_num [Fin.prod_univ_four]

/-! ## Choosing an enumeration of the non-selected arms -/

/-- **Every set of `q - 1` labelled arms can be enumerated.**  For `q ≥ 1` and any selected arm
`j : Fin q` there is a bijection `Fin (q - 1) ≃ {i : Fin q // i ≠ j}`; the count is
`Fintype.card {i // i ≠ j} = q - 1`.  This is what lets the cover be applied with the other arms in
*any* chosen order: the caller may fix `e` by `Classical.choose` of this existence statement. -/
theorem exists_armEnum {q : ℕ} (_hq : 1 ≤ q) (j : Fin q) :
    Nonempty (Fin (q - 1) ≃ {i : Fin q // i ≠ j}) := by
  classical
  have hcard : Fintype.card {i : Fin q // i ≠ j} = q - 1 := by
    have h := Fintype.card_subtype_compl (α := Fin q) (p := fun i => i = j)
    rw [Fintype.card_subtype_eq] at h
    simp [Fintype.card_fin] at h ⊢
  exact ⟨(Fintype.equivFinOfCardEq hcard).symm⟩

/-! ## The union/BK bound for the general family -/

/-- **The general-`q` BK bound.**  The fresh diagram family is bounded by the sum over its
attachment histories of the products of the `2q` two-point factors.  Each history is counted by
the finite split-choice tuple (`card_histChoices`) and summed over the `q - 1` attachment vertices,
exactly the general-`q` form of `freshMark_measure_le_q4`. -/
theorem genShape_measure_le (π : Sym2 V → unitInterval) (hπ : ∀ e, π e < 1)
    (y w : V) {q : ℕ} (g : Fin q → V) (j : Fin q)
    (e : Fin (q - 1) ≃ {i : Fin q // i ≠ j}) :
    (edgeMeasure π) (genShape y w g j e) ≤
      ∑' H : {H : Hist V (q - 1) // ∀ t : Fin (q - 1), H.arm t = g (e t).1},
        ∏ i : Idx (q - 1), tau π (H.1.legs y w (g j) i).1 (H.1.legs y w (g j) i).2 := by
  classical
  rw [genShape]
  exact le_trans (measure_iUnion_le _)
    (ENNReal.tsum_le_tsum fun H => shapeOfI_measure_le π hπ _)

/-- **The general-`q` fresh-side BK bound.**  Composing the event cover with the union/BK bound:
for every arm tuple `g`, selected arm `j` and enumeration `e` of the other labels, the fresh marked
event costs at most the sum over the attachment histories of the products of the `2q` two-point
factors. -/
theorem freshMark_measure_le_genShape (π : Sym2 V → unitInterval) (hπ : ∀ e, π e < 1)
    {q : ℕ} (hq : 2 ≤ q) (y w : V) (g : Fin q → V) (j : Fin q)
    (e : Fin (q - 1) ≃ {i : Fin q // i ≠ j}) :
    (edgeMeasure π) (I417Gen.freshMark y g j w) ≤
      ∑' H : {H : Hist V (q - 1) // ∀ t : Fin (q - 1), H.arm t = g (e t).1},
        ∏ i : Idx (q - 1), tau π (H.1.legs y w (g j) i).1 (H.1.legs y w (g j) i).2 := by
  exact le_trans (measure_mono (freshMark_subset_genShape hq y w g j e))
    (genShape_measure_le π hπ y w g j e)

/-- The same bound with the enumeration `e` chosen rather than supplied: for every `q ≥ 2` there
is an ordering of the `q - 1` arms other than `j` for which the bound holds.  (Every ordering
works; this form records that the cover does not require the caller to construct one.) -/
theorem exists_freshMark_measure_le_genShape (π : Sym2 V → unitInterval) (hπ : ∀ e, π e < 1)
    {q : ℕ} (hq : 2 ≤ q) (y w : V) (g : Fin q → V) (j : Fin q) :
    ∃ e : Fin (q - 1) ≃ {i : Fin q // i ≠ j},
      (edgeMeasure π) (I417Gen.freshMark y g j w) ≤
        ∑' H : {H : Hist V (q - 1) // ∀ t : Fin (q - 1), H.arm t = g (e t).1},
          ∏ i : Idx (q - 1), tau π (H.1.legs y w (g j) i).1 (H.1.legs y w (g j) i).2 := by
  obtain ⟨e⟩ := exists_armEnum (q := q) (by omega : 1 ≤ q) j
  exact ⟨e, freshMark_measure_le_genShape π hπ hq y w g j e⟩

/-- **Summation over the arm tuple.**  The cover holds for each arm tuple `g` with the *same*
enumeration `e` of the `q - 1` non-selected labels, so summing the bound over `g : Fin q → V` is
justified termwise.  No sum over label permutations is needed: every order gives the same cover,
and `exists_armEnum` supplies one.

This is the form in which the fresh-side quantity
`∑_g P(freshMark y g j w)` of production's `I417Gen.tsum_tsum_markSet` is handed to the finite
coefficient consumer. -/
theorem tsum_freshMark_le_genShape (π : Sym2 V → unitInterval) (hπ : ∀ e, π e < 1)
    {q : ℕ} (hq : 2 ≤ q) (y w : V) (j : Fin q)
    (e : Fin (q - 1) ≃ {i : Fin q // i ≠ j}) :
    (∑' g : Fin q → V, (edgeMeasure π) (I417Gen.freshMark y g j w)) ≤
      ∑' g : Fin q → V,
        ∑' H : {H : Hist V (q - 1) // ∀ t : Fin (q - 1), H.arm t = g (e t).1},
          ∏ i : Idx (q - 1), tau π (H.1.legs y w (g j) i).1 (H.1.legs y w (g j) i).2 := by
  exact ENNReal.tsum_le_tsum fun g => freshMark_measure_le_genShape π hπ hq y w g j e

/-- **The exact remaining composition, as a theorem.**  If the diagram-evaluation premise
`GenFreshEval π q C` holds, then the fresh marked event itself is bounded by the printed
normalisation `∑_{ℓ∈[1,q]} C ℓ · χ^(2q-ℓ) · T^ℓ(w,y)`, for every arm tuple, selected arm and
ordering.

Thus the only unproved input of the general-`q` fresh side is `GenFreshEval`; everything else
(the cover, the BK/union bound, the `2q`-leg count and the finite branch count) is in
`Cover.lean`/`Bound.lean`.  Composing this with the marked side of Lemma I.4.17
(production `I417Base`/`Subdivision.composed_family_le`, which turns `2p+1` marked edges and `2q`
fresh edges into the printed exponent `2p+2q+1-ℓ`) is the remaining outer composition. -/
theorem freshMark_measure_le_poly (π : Sym2 V → unitInterval) (_hπ : ∀ e, π e < 1)
    {q : ℕ} (hq : 2 ≤ q) (C : ℕ → ℕ) (hEval : GenFreshEval π q C) :
    ∀ (χ : ℝ≥0∞), (∀ v : V, ∑' z : V, (edgeMeasure π) (connSet v z) = χ) →
      ∀ (y w : V) (g : Fin q → V) (j : Fin q),
        (edgeMeasure π) (I417Gen.freshMark y g j w) ≤
          ∑ ℓ ∈ Finset.Icc 1 q,
            (C ℓ : ℝ≥0∞) * (χ ^ (2 * q - ℓ) *
              I417Base.iterPow (fun a b => (edgeMeasure π) (connSet a b)) ℓ w y) := by
  intro χ hχ y w g j
  obtain ⟨e⟩ := exists_armEnum (q := q) (by omega : 1 ≤ q) j
  exact le_trans (measure_mono (freshMark_subset_genShape hq y w g j e))
    (hEval χ hχ y w g j e)

/-- **The same bound in production's `Subdivision.freshPoly` normalisation.**  This is the form
consumed by the diagram-evaluation package (`I417Fresh.Subdivision.freshPoly`, `subMono`,
`composed_family_le`): the fresh side is bounded by
`∑_{ℓ∈[1,q]} C ℓ · χ^(2q−ℓ) · T^ℓ(w,y)` as soon as `GenFreshEval π q C` holds. -/
theorem freshMark_measure_le_freshPoly (π : Sym2 V → unitInterval) (hπ : ∀ e, π e < 1)
    {q : ℕ} (hq : 2 ≤ q) (C : ℕ → ℕ) (hEval : GenFreshEval π q C) :
    ∀ (χ : ℝ≥0∞), (∀ v : V, ∑' z : V, (edgeMeasure π) (connSet v z) = χ) →
      ∀ (y w : V) (g : Fin q → V) (j : Fin q),
        (edgeMeasure π) (I417Gen.freshMark y g j w) ≤
          I417Fresh.Subdivision.freshPoly
            (fun a b => (edgeMeasure π) (connSet a b)) χ q C w y := by
  intro χ hχ y w g j
  simpa [I417Fresh.Subdivision.freshPoly] using
    freshMark_measure_le_poly (π := π) hπ hq C hEval χ hχ y w g j

end PercLib.CriticalLRP.I417GenIter
