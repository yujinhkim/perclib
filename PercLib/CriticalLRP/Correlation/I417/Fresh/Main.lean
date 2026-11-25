/- Integrated from independently rebuilt Ultramath work.
Production base 7a04599a899ac160fd051de07e5a0ef98d771674.
Scratch source: ../../.ultramath/smwvlmbqa/m4/Main.lean.
-/

module

public import PercLib.CriticalLRP.Correlation.I417.General.Main
public import PercLib.CriticalLRP.Correlation.TreeGraphCanonical
public import PercLib.CriticalLRP.Correlation.I417.Fresh.Defs

/-!
# The I.4.17 fresh side: unconditional spine retention and the diagram bounds

This file proves, with no hypothesis beyond BK (`π e < 1` for every edge `e`):

* `freshMark_subset_hubStar` — for **every** `q`, every configuration of `freshMark y g j w` has the
  mark `w` in the cluster of `y` and every arm `g j'` in the cluster of `w`.  This is the spine of
  the printed proof (`w` on a simple open path `y → {y_1,…,y_q}`), and it is what keeps `w` visible
  for the polygon composition with the base side of I.4.17.
* `freshMark_measure_le_twoArm` — the direct two-arm BK bound
  `P(freshMark y g j w) ≤ τ(y,w) · τ(w, g j)`, for **every** `q`.
* `freshMark_measure_le_oneHub` — the three-arm single-hub diagram
  `P(freshMark y g j w) ≤ ∑_a τ(w,a) τ(a,y) τ(a, g j)`, for **every** `q`, got by pushing the
  whole star through `twoLeaf_treeGraph` at `w`.  Three arms is the largest hub that a
  two-arm branch decomposition can serve. The checked arithmetic example records what
  breaks beyond that.
* `fresh_factor_one_le` — the summed bound at `q = 1`, with the arm retained as `hubArmSum`:
  `∑_{g : Fin 1 → V} P(freshMark y g 0 w) ≤ ∑_a τ(w,a) τ(a,y) ∑_z τ(a,z)`.
* `freshCombBound_holds_one` — the `q = 1` instance of the named general-`q` premise
  `FreshCombBound`, i.e. the fresh side of I.4.17 at `q = 1` with no remaining premise.

For `q ≥ 2` no single-hub diagram can carry all arms; the remaining premise is `FreshCombBound π q`
(the generic finite diagram family) which `Defs.lean` states exactly.
-/

open MeasureTheory Measure ProbabilityTheory unitInterval
open scoped ENNReal NNReal

set_option linter.unusedSectionVars false

@[expose] public section

namespace PercLib.CriticalLRP.I417Fresh

variable {V : Type*} [Countable V]

/-! ## Elementary set facts -/

/-- Unfolding of the hub membership: `y ↔ w` and every arm `w ↔ g j'`. -/
theorem mem_hubStar_iff {y w : V} {q : ℕ} {g : Fin q → V} {ω : Config V} :
    ω ∈ hubStar y w g ↔ Connects ω y w ∧ ∀ j : Fin q, Connects ω w (g j) := by
  simp only [hubStar, armStar, connSet, Set.mem_inter_iff, Set.mem_iInter, Set.mem_ofPred_eq]

/-- Unfolding of the arm-star membership. -/
theorem mem_armStar_iff {w : V} {q : ℕ} {g : Fin q → V} {ω : Config V} :
    ω ∈ armStar w g ↔ ∀ j : Fin q, Connects ω w (g j) := by
  simp only [armStar, connSet, Set.mem_iInter, Set.mem_ofPred_eq]

/-- `connSet` is symmetric. -/
theorem connSet_swap (a b : V) : connSet a b = connSet b a := by
  ext ω
  exact ⟨connects_symm, connects_symm⟩

/-- A disjoint occurrence is contained in its left factor, for increasing left factors: the
witness `s` is a subset of `ω`, so monotonicity puts `ω` itself in the left event. -/
theorem disjointOccurrence_subset_left {A B : Set (Config V)} (hA : IsUpperSet A) :
    Percolation.DisjointOccurrence A B ⊆ A := by
  rintro ω ⟨s, _t, hs, _ht, _hd, ha, _hb⟩
  exact hA hs ha

/-- A disjoint occurrence is contained in its right factor, for increasing right factors. -/
theorem disjointOccurrence_subset_right {A B : Set (Config V)} (hB : IsUpperSet B) :
    Percolation.DisjointOccurrence A B ⊆ B := by
  rintro ω ⟨_s, t, _hs, ht, _hd, _ha, hb⟩
  exact hB ht hb

/-- **The spine of the fresh event, for every `q`.**  Every configuration in `freshMark y g j w`
has `y ↔ w` and `w ↔ g j'` for every arm `j'`.  The first comes from the `y → w` half of the
disjoint occurrence; the second is `y ↔ w` composed with `y ↔ g j'`, both in the fresh cluster. -/
theorem freshMark_subset_hubStar (y w : V) {q : ℕ} (g : Fin q → V) (j : Fin q) :
    I417Gen.freshMark y g j w ⊆ hubStar y w g := by
  intro ω hω
  have hDO : ω ∈ Percolation.DisjointOccurrence (connSet y w) (connSet w (g j)) := hω.1
  have harm : ω ∈ I417A.labelEvent y g := hω.2
  obtain ⟨s, _t, hs, _ht, _hd, hsw, _htw⟩ := hDO
  have hsw' : Connects (s : Set (Sym2 V)) y w := hsw
  have h1 : Connects ω y w := connects_mono (fun e he => hs he) hsw'
  have h2 : ∀ j' : Fin q, Connects ω y (g j') := by
    intro j'
    rw [I417A.labelEvent_eq_iInter] at harm
    exact Set.mem_iInter.mp harm j'
  refine ⟨h1, ?_⟩
  exact (mem_armStar_iff).mpr fun j' => connects_trans (connects_symm h1) (h2 j')

/-- The hub event is increasing. -/
theorem isUpperSet_hubStar (y w : V) {q : ℕ} (g : Fin q → V) : IsUpperSet (hubStar y w g) := by
  intro ω ω' hωω' hω
  refine (mem_hubStar_iff).mpr ⟨?_, ?_⟩
  · exact (isUpper_connSet y w) hωω' ((mem_hubStar_iff).mp hω).1
  · intro j
    exact (isUpper_connSet w (g j)) hωω' (((mem_hubStar_iff).mp hω).2 j)

/-- The hub event is finitely witnessed: the union of the finitely many witnesses of the spine and
of the `q` arms. -/
theorem finiteWitness_hubStar (y w : V) {q : ℕ} (g : Fin q → V) :
    Percolation.FiniteWitness (hubStar y w g) := by
  classical
  intro ω hω
  obtain ⟨hspine, harms⟩ := (mem_hubStar_iff).mp hω
  obtain ⟨S₀, hS₀, hS₀A⟩ := (finiteWitness_connSet y w) ω hspine
  have h : ∀ j : Fin q, ∃ S : Finset (Sym2 V), (S : Set (Sym2 V)) ⊆ ω ∧
      (S : Set (Sym2 V)) ∈ connSet w (g j) :=
    fun j => (finiteWitness_connSet w (g j)) ω (harms j)
  choose T hT hTA using h
  refine ⟨S₀ ∪ (Finset.univ : Finset (Fin q)).sup T, ?_, ?_⟩
  · intro e he
    rcases Finset.mem_union.mp he with he | he
    · exact hS₀ he
    · obtain ⟨j, _, hje⟩ := Finset.mem_sup.mp he
      exact hT j hje
  · refine (mem_hubStar_iff).mpr ⟨?_, ?_⟩
    · exact (isUpper_connSet y w) (fun e he => Finset.mem_union_left _ he) hS₀A
    · intro j
      have hsub : (T j : Set (Sym2 V)) ⊆
          ((S₀ ∪ (Finset.univ : Finset (Fin q)).sup T : Finset (Sym2 V)) : Set (Sym2 V)) := by
        intro e he
        exact Finset.mem_union_right _ (Finset.mem_sup.mpr ⟨j, Finset.mem_univ j, he⟩)
      exact (isUpper_connSet w (g j)) hsub (hTA j)

/-! ## The two-arm and single-hub diagram bounds -/

/-- **Two-arm BK bound, every `q`.**  The fresh event is a disjoint occurrence of `y ↔ w` and
`w ↔ g j`, so BK gives `τ(y,w) · τ(w, g j)`.  This keeps the spine and the terminal arm and drops
the other `q − 1` arms; it is the one bound that is uniform in `q`. -/
theorem freshMark_measure_le_twoArm (π : Sym2 V → unitInterval) (hπ : ∀ e, π e < 1)
    (y w : V) {q : ℕ} (g : Fin q → V) (j : Fin q) :
    (edgeMeasure π) (I417Gen.freshMark y g j w) ≤ tau π y w * tau π w (g j) := by
  refine le_trans (measure_mono (Set.inter_subset_left)) ?_
  exact bk_ennreal π hπ (connSet y w) (connSet w (g j)) (isUpper_connSet y w)
    (isUpper_connSet w (g j)) (finiteWitness_connSet y w) (finiteWitness_connSet w (g j))

/-- **Single-hub three-arm diagram, every `q`.**  The spine and the terminal arm both live at the
hub `w`, so the two-arm tree-graph inequality `twoLeaf_treeGraph` at `w` evaluates the whole thing:
one extra hub `a` is summed and the three arms `w → a`, `a → y`, `a → g j` are its three edges. -/
theorem freshMark_measure_le_oneHub (π : Sym2 V → unitInterval) (hπ : ∀ e, π e < 1)
    (y w : V) {q : ℕ} (g : Fin q → V) (j : Fin q) :
    (edgeMeasure π) (I417Gen.freshMark y g j w) ≤
      ∑' a : V, tau π w a * tau π a y * tau π a (g j) := by
  refine le_trans (measure_mono (freshMark_subset_hubStar y w g j)) ?_
  have hsub : hubStar y w g ⊆ connSet w y ∩ connSet w (g j) := by
    rintro ω hω
    obtain ⟨h1, h2⟩ := (mem_hubStar_iff).mp hω
    exact ⟨(connSet_swap y w) ▸ h1, h2 j⟩
  refine le_trans (measure_mono hsub) ?_
  exact twoLeaf_treeGraph π hπ w y (g j)

/-! ## The `q = 1` fresh factor, unconditionally -/

/-- **The fresh-copy factor at `q = 1`, with the arm retained.**  A complete tree-diagram bound for
`∑_g P(freshMark y g 0 w)`: one summed hub `a`, three two-point factors, no hypothesis beyond BK. -/
theorem fresh_factor_one_le (π : Sym2 V → unitInterval) (hπ : ∀ e, π e < 1) (y w : V) :
    (∑' g : Fin 1 → V, (edgeMeasure π) (I417Gen.freshMark y g 0 w)) ≤
      ∑' a : V, tau π w a * tau π a y * hubArmSum π a := by
  have h1 : ∀ g : Fin 1 → V,
      (edgeMeasure π) (I417Gen.freshMark y g 0 w) ≤
        ∑' a : V, tau π w a * tau π a y * tau π a (g 0) :=
    fun g => freshMark_measure_le_oneHub π hπ y w g 0
  refine le_trans (ENNReal.tsum_le_tsum h1) ?_
  rw [ENNReal.tsum_comm]
  refine ENNReal.tsum_le_tsum fun a => ?_
  have he : (∑' g : Fin 1 → V, tau π w a * tau π a y * tau π a (g 0)) =
      ∑' z : V, tau π w a * tau π a y * tau π a z :=
    Equiv.tsum_eq (finOneArrowEquiv V) (fun z => tau π w a * tau π a y * tau π a z)
  have hstep : (∑' z : V, tau π w a * tau π a y * tau π a z) =
      tau π w a * tau π a y * hubArmSum π a := by
    rw [hubArmSum, ENNReal.tsum_mul_left]
  rw [he, hstep]

/-- At `q = 1` the aggregated diagram bound is the chain bound plus the single-hub three-arm sum. -/
theorem freshCombBound_one (π : Sym2 V → unitInterval) (y w : V) :
    freshCombBound π 1 y w =
      freshChainBound π 1 y w + ∑' a : V, tau π w a * tau π a y * hubArmSum π a := by
  rw [freshCombBound, firstHubBound]
  congr 1
  refine tsum_congr fun a => ?_
  rw [show (1 : ℕ) - 1 = 0 from rfl]
  simp only [armComb, mul_one]

/-- **The fresh side of Lemma I.4.17 at `q = 1`, with no remaining premise.** -/
theorem freshCombBound_holds_one (π : Sym2 V → unitInterval) (hπ : ∀ e, π e < 1) :
    FreshCombBound π 1 := by
  intro y w j
  have hj : j = 0 := by ext; omega
  subst hj
  rw [freshCombBound_one]
  calc (∑' g : Fin 1 → V, (edgeMeasure π) (I417Gen.freshMark y g 0 w))
      ≤ ∑' a : V, tau π w a * tau π a y * hubArmSum π a := fresh_factor_one_le π hπ y w
    _ ≤ freshChainBound π 1 y w + ∑' a : V, tau π w a * tau π a y * hubArmSum π a :=
        le_add_left le_rfl


/-! ## The summed fresh factor at every `q` -/

/-- **The summed fresh factor passes to the hub star, for every `q`, with no BK hypothesis.**  This
is the `w`-composition form: the whole sum over the `q` arms is bounded by the same sum with the
spine `y ↔ w` made explicit at the hub `w`. -/
theorem fresh_factor_le_hubStar (π : Sym2 V → unitInterval) (y w : V) {q : ℕ} (j : Fin q) :
    (∑' g : Fin q → V, (edgeMeasure π) (I417Gen.freshMark y g j w)) ≤
      ∑' g : Fin q → V, (edgeMeasure π) (hubStar y w g) :=
  ENNReal.tsum_le_tsum fun g => measure_mono (freshMark_subset_hubStar y w g j)

/-- The same, with the hub event's arms made explicit: at every `q` the fresh factor is at most the
sum over the `q` arms of the probability that the mark lies in the cluster of `y` and all arms in
the cluster of the mark. -/
theorem fresh_factor_le_hubStar_apply (π : Sym2 V → unitInterval) (y w : V) {q : ℕ}
    (j : Fin q) :
    (∑' g : Fin q → V, (edgeMeasure π) (I417Gen.freshMark y g j w)) ≤
      ∑' g : Fin q → V,
        (edgeMeasure π) (connSet y w ∩ ⋂ j' : Fin q, connSet w (g j')) :=
  fresh_factor_le_hubStar π y w j

end PercLib.CriticalLRP.I417Fresh
