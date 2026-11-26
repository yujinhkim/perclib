/- Independently rebuilt and integrated finding f3 of swarm `smwwyd7lg`, member `m1`.
Production integration revision: `d2734e7c030f377ae4642466daef7f78ff648cb8`. -/

module

public import PercLib.CriticalLRP.Correlation.I417.Fresh.Fork.Defs

/-!
# The `q = 3` fresh side of Lemma I.4.17: fork BK bound and the double-star fork

Source: Tom Hutchcroft, *Critical long-range percolation I: High effective
dimension*, arXiv:2508.18807v1, Lemma I.4.17 (p. 45) and its proof.

This file proves, for the canonical model `edgeMeasure π` on an arbitrary
countable vertex set and with the only hypothesis `π e < 1` (van den
Berg–Kesten):

* `bk_six_le` — six-fold iterated BK in `ℝ≥0∞` form;
* `forkEvent_measure_le` — the fork event is at most its six two-point factors;
* `fresh_fork_three_le` — the fresh side at `q = 3` with the mark and two arms at
  the first hub and the remaining arm and the marked arm `y` at the second:
  the arm sum is at most the explicit two-hub monomial
  `τ(w,a)·χ(a)·χ(a)·τ(w,b)·(χ(b)·τ(b,y))`, with no arm dropped (so no
  unrestricted vertex sum appears);
* `fresh_fork_le_forkBound` — the same, absorbed into the summed two-hub
  diagram `forkBound`;
* `mem_connSet_of_single`, `dsForkW_*`, `ds_forkEvent` — in the six-edge double
  star of `I417.Fresh.Obstruction` the fork event holds, with the six edges of
  the double star as its six pairwise edge-disjoint witnesses;
* `q3_doubleStar_fork_not_chain` — the same double star in which the four-arm
  hub event holds admits **no** chain spider for any spine vector and any
  injective slot assignment (production `ds_no_chainSpider`): at `q = 3` the
  chain family is not a cover of the fresh hub event, while the fork family is.
-/

open MeasureTheory Measure ProbabilityTheory unitInterval
open scoped ENNReal NNReal

set_option linter.unusedSectionVars false

@[expose] public section

namespace PercLib.CriticalLRP.I417Fresh

namespace Q3

variable {V : Type*} [Countable V]

/-! ## The fork event is increasing and finitely witnessed -/

theorem isUpperSet_forkReq (w a b : V) (u v : Fin 2 → V) (i : Fin 6) :
    IsUpperSet (forkReq w a b u v i) := by
  fin_cases i
  · exact isUpper_connSet w a
  · exact isUpper_connSet a (u 0)
  · exact isUpper_connSet a (u 1)
  · exact isUpper_connSet w b
  · exact isUpper_connSet b (v 0)
  · exact isUpper_connSet b (v 1)

theorem finiteWitness_forkReq (w a b : V) (u v : Fin 2 → V) (i : Fin 6) :
    Percolation.FiniteWitness (forkReq w a b u v i) := by
  fin_cases i
  · exact finiteWitness_connSet w a
  · exact finiteWitness_connSet a (u 0)
  · exact finiteWitness_connSet a (u 1)
  · exact finiteWitness_connSet w b
  · exact finiteWitness_connSet b (v 0)
  · exact finiteWitness_connSet b (v 1)

/-- **Six-fold iterated BK**, `ℝ≥0∞` form: the measure of a six-fold disjoint
occurrence of increasing finitely witnessed events is at most the product of
their measures. -/
theorem bk_six_le (π : Sym2 V → unitInterval) (hπ : ∀ e, π e < 1)
    (A : Fin 6 → Set (Config V)) (hA : ∀ i, IsUpperSet (A i))
    (hf : ∀ i, Percolation.FiniteWitness (A i)) :
    (edgeMeasure π) (Percolation.DisjointOccurrenceFin A) ≤
      ∏ i, (edgeMeasure π) (A i) :=
  I417Example.bk_fin_ennreal π hπ A hA hf

/-- **The fork event carries its six-point monomial.** -/
theorem forkEvent_measure_le (π : Sym2 V → unitInterval) (hπ : ∀ e, π e < 1)
    (w a b : V) (u v : Fin 2 → V) :
    (edgeMeasure π) (forkEvent w a b u v) ≤ forkMono π w a b u v := by
  have h := bk_six_le (V := V) π hπ (forkReq w a b u v)
    (isUpperSet_forkReq w a b u v) (finiteWitness_forkReq w a b u v)
  have hprod : (∏ i : Fin 6, (edgeMeasure π) (forkReq w a b u v i)) =
      forkMono π w a b u v := by
    rw [Fin.prod_univ_six]
    simp only [forkReq, Matrix.cons_val_zero]
    rfl
  rw [hprod] at h
  exact h

/-! ## Summing the three arms out -/

theorem symm_finThreeArrow_zero (p : V × V × V) :
    (finThreeArrowEquiv V).symm p 0 = p.1 := by
  simp [finThreeArrowEquiv]

theorem symm_finThreeArrow_one (p : V × V × V) :
    (finThreeArrowEquiv V).symm p 1 = p.2.1 := by
  simp [finThreeArrowEquiv]

theorem symm_finThreeArrow_two (p : V × V × V) :
    (finThreeArrowEquiv V).symm p 2 = p.2.2 := by
  simp [finThreeArrowEquiv]

/-- Reindexing a sum over three labelled arms as an iterated sum. -/
theorem tsum_fin3 (H : V → V → V → ℝ≥0∞) :
    (∑' g : Fin 3 → V, H (g 0) (g 1) (g 2)) = ∑' a : V, ∑' b : V, ∑' c : V, H a b c := by
  have h := Equiv.tsum_eq (finThreeArrowEquiv V).symm
    (fun g : Fin 3 → V => H (g 0) (g 1) (g 2))
  rw [← h]
  simp only [symm_finThreeArrow_zero, symm_finThreeArrow_one, symm_finThreeArrow_two]
  rw [ENNReal.tsum_prod']
  exact tsum_congr fun a => ENNReal.tsum_prod'

/-- The three labelled arms sum out independently. -/
theorem tsum_fin3_mul (f k l : V → ℝ≥0∞) :
    (∑' g : Fin 3 → V, f (g 0) * k (g 1) * l (g 2)) =
      (∑' z, f z) * (∑' z, k z) * (∑' z, l z) := by
  rw [tsum_fin3 (fun a b c => f a * k b * l c)]
  simp only [ENNReal.tsum_mul_left, ENNReal.tsum_mul_right]

/-! ## The `q = 3` fresh arm sum with the mark and two arms at the first hub -/

/-- **The fresh side at `q = 3`, two hubs.**  With the mark `y` and the arms
`g 0`, `g 1`, `g 2`, the fork puts `g 0`, `g 1` at the hub `a` and `g 2`, `y` at
the hub `b`.  Every arm is retained: the two legs at `b` are summed out to
`hubArmSum`, and the leg to `y` stays visible as `τ(b,y)`. -/
theorem fresh_fork_three_le (π : Sym2 V → unitInterval) (hπ : ∀ e, π e < 1)
    (y w a b : V) :
    (∑' g : Fin 3 → V, (edgeMeasure π) (forkEvent w a b ![g 0, g 1] ![g 2, y])) ≤
      tau π w a * hubArmSum π a * hubArmSum π a * tau π w b *
        (hubArmSum π b * tau π b y) := by
  have h1 : ∀ g : Fin 3 → V,
      (edgeMeasure π) (forkEvent w a b ![g 0, g 1] ![g 2, y]) ≤
        tau π w a * tau π a (g 0) * tau π a (g 1) * tau π w b * tau π b (g 2) *
          tau π b y := by
    intro g
    have h := forkEvent_measure_le π hπ w a b ![g 0, g 1] ![g 2, y]
    simpa only [forkMono, Matrix.cons_val_zero, Matrix.cons_val_one] using h
  refine le_trans (ENNReal.tsum_le_tsum h1) ?_
  have hfac : (∑' g : Fin 3 → V, tau π w a * tau π a (g 0) * tau π a (g 1) *
        tau π w b * tau π b (g 2) * tau π b y) =
      (tau π w a * tau π w b * tau π b y) *
        (∑' g : Fin 3 → V, tau π a (g 0) * tau π a (g 1) * tau π b (g 2)) := by
    rw [← ENNReal.tsum_mul_left]
    exact tsum_congr fun g => by ring
  rw [hfac, tsum_fin3_mul]
  simp only [hubArmSum]
  exact le_of_eq (by ring)

/-- **The `q = 3` fresh fork sum inside the summed two-hub diagram.** -/
theorem fresh_fork_le_forkBound (π : Sym2 V → unitInterval) (hπ : ∀ e, π e < 1)
    (y w a b : V) :
    (∑' g : Fin 3 → V, (edgeMeasure π) (forkEvent w a b ![g 0, g 1] ![g 2, y])) ≤
      forkBound π y w := by
  refine le_trans (fresh_fork_three_le π hπ y w a b) ?_
  have hrew : tau π w a * hubArmSum π a * hubArmSum π a * tau π w b *
        (hubArmSum π b * tau π b y) =
      tau π w b * tau π b y * hubArmSum π b * tau π w a *
        (hubArmSum π a * hubArmSum π a) := by ring
  rw [hrew]
  exact ENNReal.le_tsum (f := fun p : V × V =>
    tau π w p.1 * tau π p.1 y * hubArmSum π p.1 * tau π w p.2 *
      (hubArmSum π p.2 * hubArmSum π p.2)) (b, a)

/-! ## The double star: a single open edge connects its endpoints -/

/-- An open single edge connects its endpoints. -/
theorem mem_connSet_of_single {a b : DSV} (hne : a ≠ b) {W : Finset (Sym2 DSV)}
    (h : s(a, b) ∈ W) : (W : Set (Sym2 DSV)) ∈ connSet a b := by
  refine pathConnects_iff.mp ?_
  refine ⟨SimpleGraph.Walk.cons ((SimpleGraph.top_adj a b).2 hne) SimpleGraph.Walk.nil, ?_⟩
  intro e he
  have h' : e = s(a, b) := by simpa using he
  rw [h']
  exact h

theorem dsForkW_subFinset : ∀ i : Fin 6, dsForkW i ⊆ dsE := by decide

theorem dsForkW_sub (i : Fin 6) :
    (dsForkW i : Set (Sym2 DSV)) ⊆ (dsE : Set (Sym2 DSV)) :=
  Finset.coe_subset.mpr (dsForkW_subFinset i)

theorem dsForkW_mem (i : Fin 6) :
    (dsForkW i : Set (Sym2 DSV)) ∈ forkReq (V := DSV) 0 1 2 ![3, 4] ![5, 6] i := by
  fin_cases i
  · exact mem_connSet_of_single (by decide) (by decide)
  · exact mem_connSet_of_single (by decide) (by decide)
  · exact mem_connSet_of_single (by decide) (by decide)
  · exact mem_connSet_of_single (by decide) (by decide)
  · exact mem_connSet_of_single (by decide) (by decide)
  · exact mem_connSet_of_single (by decide) (by decide)

theorem dsForkW_disj : ∀ i j : Fin 6, i ≠ j → Disjoint (dsForkW i) (dsForkW j) := by
  decide

/-- **The fork event holds in the fully open double star.**  The six witnesses
are the six edges `0-1`, `1-3`, `1-4`, `0-2`, `2-5`, `2-6` of `dsE`. -/
theorem ds_forkEvent :
    (dsE : Config DSV) ∈ forkEvent (V := DSV) 0 1 2 ![3, 4] ![5, 6] :=
  ⟨dsForkW, dsForkW_sub, dsForkW_mem, dsForkW_disj⟩

/-- **The double star separates the fork family from the chain family.**  In the
configuration `dsE` the four-arm hub event holds (`ds_hubEvent`, with hub `0`,
mark `6` and arms `3`, `4`, `5`), the fork event with the same data and with the
marked arm at the second hub holds, and yet there is **no** chain spider with
that hub event for any spine vector `u` and any injective assignment `z` of the
four slots onto the four terminals (`ds_no_chainSpider`).

Hence at `q = 3` the chain family of `freshCombBound` cannot be obtained from
the fresh hub event by a configurationwise disjoint-witness cover, while the
two-hub fork of `forkEvent` — whose BK evaluation is `forkEvent_measure_le` and
whose arm sum is `fresh_fork_three_le` — is available in the very same
configuration. -/
theorem q3_doubleStar_fork_not_chain :
    (Connects (dsE : Config DSV) 6 0 ∧ Connects (dsE : Config DSV) 0 3 ∧
        Connects (dsE : Config DSV) 0 4 ∧ Connects (dsE : Config DSV) 0 5) ∧
      (dsE : Config DSV) ∈ forkEvent (V := DSV) 0 1 2 ![3, 4] ![5, 6] ∧
      (∀ (u z : Fin 4 → DSV), (∀ i, z i = 3 ∨ z i = 4 ∨ z i = 5 ∨ z i = 6) →
        Function.Injective z → ¬ ChainSpider (dsE : Config DSV) 0 u z) :=
  ⟨ds_hubEvent, ds_forkEvent, fun u z hz hinj => ds_no_chainSpider u z hz hinj⟩

end Q3

end PercLib.CriticalLRP.I417Fresh
