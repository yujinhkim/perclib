/- Independently verified and integrated from `smwx1cgtv`, member `m1`, findings f1/f2.
# A finite obstruction to an auxiliary four-arm fresh inequality.

This refutes an additional general hypothesis about arbitrary countable vertex types; it is
not a counterexample to Lemma I.4.17 or to its transitive weighted-graph setting. Production
integration revision: `eb6654a2cff425941b393dbaf8a5d579ec193cab`.

Source: T. Hutchcroft, *Critical long-range percolation I: high effective dimension*,
arXiv:2508.18807v1, Lemma I.4.17 (p. 45); the fresh-side input is the `q = 2` statement isolated in
`PercLib.CriticalLRP.Correlation.I417.Fresh.Two.Poly`:

  `∑_g (edgeMeasure π) (freshMark y g j w) ≤ fourArmFresh π y w = ∑_a τ(w,a) τ(a,y) χ(a)²`.

This file proves that this inequality is **false**: on `V = Fin 3` with the two-edge star
`π {0,1} = π {0,2} = 1/5` and `π e = 0` otherwise (so `∀ e, π e < 1`), at `y = w = 0`, `j = 0`,

  `∑_g μ(freshMark 0 g 0 0) = 57/25 > 32547/15625 = fourArmFresh π 0 0`.

Why: for `w = y` the fresh event is the labelled event (`freshMark_self_eq_labelEvent`), so the left
side is the second cluster moment `E|K_0|²`, while the right side is built from `(E|K_0|)²` (the
`a = y` term of the hub sum) times the spine factors; the variance of `|K_0|` is invisible to the
hub sum.  Every measure below is a cylinder, or a finite union/intersection handled by monotonicity
against cylinders, so all values are exact rationals.

No `sorry`, no custom axioms.
-/
module

public import PercLib.CriticalLRP.Correlation.I417.Fresh.Two.Poly.Defs
public import PercLib.CriticalLRP.Correlation.I417.Fresh.Two.Poly.Main

/-! Exact finite obstruction to the auxiliary four-arm fresh hypothesis. The model is
inhomogeneous, so this is not a counterexample to Lemma I.4.17 or its transitive setting. -/

open MeasureTheory Measure ProbabilityTheory unitInterval
open scoped ENNReal NNReal

set_option linter.unusedSectionVars false

@[expose] public section

namespace PercLib.CriticalLRP.I417FreshTwo.Cex

attribute [local instance] Classical.propDecidable

/-! ## Part 0: the counterexample data -/

/-- The edge `{0,1}` of `Fin 3`. -/
def cexEdge01 : Sym2 (Fin 3) := s(0, 1)

/-- The edge `{0,2}` of `Fin 3`. -/
def cexEdge02 : Sym2 (Fin 3) := s(0, 2)

/-- The edge `{1,2}` of `Fin 3`. -/
def cexEdge12 : Sym2 (Fin 3) := s(1, 2)

/-- The edge probability `1/5` of the two star edges. -/
noncomputable def cexFifth : unitInterval := ⟨1/5, by norm_num, by norm_num⟩

/-- **The counterexample law**: the two-edge star at `0` with edge probability `1/5`; every other
pair of `Fin 3` (including the three diagonal pairs) is closed. -/
noncomputable def piCex : Sym2 (Fin 3) → unitInterval :=
  fun e => if e = cexEdge01 then cexFifth else if e = cexEdge02 then cexFifth else 0

theorem cexEdge01_ne_02 : cexEdge01 ≠ cexEdge02 := by
  simp only [cexEdge01, cexEdge02]; decide

theorem cexEdge01_ne_12 : cexEdge01 ≠ cexEdge12 := by
  simp only [cexEdge01, cexEdge12]; decide

theorem cexEdge02_ne_12 : cexEdge02 ≠ cexEdge12 := by
  simp only [cexEdge02, cexEdge12]; decide

theorem cexEdge02_ne_01 : cexEdge02 ≠ cexEdge01 := fun h => cexEdge01_ne_02 h.symm

theorem cexEdge12_ne_01 : cexEdge12 ≠ cexEdge01 := fun h => cexEdge01_ne_12 h.symm

theorem cexEdge12_ne_02 : cexEdge12 ≠ cexEdge02 := fun h => cexEdge02_ne_12 h.symm

@[simp] theorem piCex_01 : piCex cexEdge01 = cexFifth := by simp [piCex]

@[simp] theorem piCex_02 : piCex cexEdge02 = cexFifth := by simp [piCex, cexEdge02_ne_01]

@[simp] theorem piCex_12 : piCex cexEdge12 = 0 := by
  simp [piCex, cexEdge12_ne_01, cexEdge12_ne_02]

theorem toNNReal_cexFifth : unitInterval.toNNReal cexFifth = 1 / 5 :=
  NNReal.eq (by simp [cexFifth])

/-- Every edge of the counterexample is strictly subcritical, as the target requires. -/
theorem piCex_lt_one : ∀ e, piCex e < 1 := by
  intro e
  change (piCex e : ℝ) < 1
  by_cases h1 : e = cexEdge01
  · rw [h1, piCex_01]; simp only [cexFifth]; norm_num
  · by_cases h2 : e = cexEdge02
    · rw [h2, piCex_02]; simp only [cexFifth]; norm_num
    · rw [show piCex e = 0 from by simp [piCex, h1, h2]]; norm_num

/-! ## Part 1: for `w = y` the fresh event is the labelled event -/

theorem connSet_self_eq_univ {V : Type*} [Countable V] (y : V) :
    connSet y y = (Set.univ : Set (Config V)) :=
  Set.eq_univ_of_forall (fun ω => connects_refl ω y)

theorem freshMark_self_eq_labelEvent {V : Type*} [Countable V] (y : V) {q : ℕ}
    (g : Fin q → V) (j : Fin q) :
    I417Gen.freshMark y g j y = I417A.labelEvent y g := by
  have hDO : Percolation.DisjointOccurrence (connSet y y) (connSet y (g j))
      = connSet y (g j) := by
    apply Set.Subset.antisymm
    · rintro ω ⟨s, t, -, ht, -, -, hB⟩
      exact isUpper_connSet y (g j) ht hB
    · intro ω hω
      obtain ⟨t, ht, hBt⟩ := finiteWitness_connSet y (g j) ω hω
      refine ⟨∅, t, by simp, ht, by simp, ?_, hBt⟩
      rw [connSet_self_eq_univ]
      exact Set.mem_univ _
  rw [I417Gen.freshMark, hDO]
  refine Set.inter_eq_right.mpr ?_
  intro ω hω
  exact mem_cluster_iff.mp (hω j)

/-! ## Part 2: connectivity on `Fin 3` -/

theorem connects_of_adj {ω : Config (Fin 3)} {x y : Fin 3} (h : (openGraph ω).Adj x y) :
    Connects ω x y := by
  rw [Connects, SimpleGraph.reachable_iff_reflTransGen]
  exact Relation.ReflTransGen.single h

theorem reachable_mem {A : Set (Fin 3)} {ω : Config (Fin 3)} {x y : Fin 3}
    (h : Connects ω x y) (hx : x ∈ A)
    (hA : ∀ a ∈ A, ∀ b, (openGraph ω).Adj a b → b ∈ A) : y ∈ A := by
  rw [Connects, SimpleGraph.reachable_iff_reflTransGen] at h
  induction h with
  | refl => exact hx
  | tail _ hstep ih => exact hA _ ih _ hstep

theorem adj_of_mem {ω : Config (Fin 3)} {x y : Fin 3} (hne : x ≠ y) (h : s(x, y) ∈ ω) :
    (openGraph ω).Adj x y :=
  openGraph_adj.mpr ⟨hne, h⟩

theorem connects_zero_one_iff (ω : Config (Fin 3)) :
    Connects ω 0 1 ↔ cexEdge01 ∈ ω ∨ (cexEdge02 ∈ ω ∧ cexEdge12 ∈ ω) := by
  constructor
  · intro h
    by_cases h01 : cexEdge01 ∈ ω
    · exact Or.inl h01
    by_cases h02 : cexEdge02 ∈ ω
    · by_cases h12 : cexEdge12 ∈ ω
      · exact Or.inr ⟨h02, h12⟩
      · exfalso
        have hmem := reachable_mem (A := ({0, 2} : Set (Fin 3))) h (by simp) ?_
        · simp at hmem
        · intro a ha b hb
          simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at ha ⊢
          rcases ha with rfl | rfl
          · have hne := (openGraph_adj.mp hb).1
            fin_cases b
            · exact absurd rfl hne
            · exact absurd (openGraph_adj.mp hb).2 h01
            · simp
          · have hne := (openGraph_adj.mp hb).1
            fin_cases b
            · simp
            · exact absurd (by simpa [cexEdge12, Sym2.eq_swap] using
                (openGraph_adj.mp hb).2) h12
            · exact absurd rfl hne
    · exfalso
      have hmem := reachable_mem (A := ({0} : Set (Fin 3))) h (by simp) ?_
      · simp at hmem
      · intro a ha b hb
        simp only [Set.mem_singleton_iff] at ha ⊢
        subst ha
        have hne := (openGraph_adj.mp hb).1
        fin_cases b
        · exact absurd rfl hne
        · exact absurd (openGraph_adj.mp hb).2 h01
        · exact absurd (openGraph_adj.mp hb).2 h02
  · rintro (h | ⟨h1, h2⟩)
    · exact connects_of_adj (adj_of_mem (by decide) h)
    · exact (connects_of_adj (adj_of_mem (by decide) h1)).trans
        (connects_of_adj (adj_of_mem (by decide) (by
          simpa [cexEdge12, Sym2.eq_swap] using h2)))

theorem connects_one_two_iff (ω : Config (Fin 3)) :
    Connects ω 1 2 ↔ cexEdge12 ∈ ω ∨ (cexEdge01 ∈ ω ∧ cexEdge02 ∈ ω) := by
  constructor
  · intro h
    by_cases h12 : cexEdge12 ∈ ω
    · exact Or.inl h12
    by_cases h01 : cexEdge01 ∈ ω
    · by_cases h02 : cexEdge02 ∈ ω
      · exact Or.inr ⟨h01, h02⟩
      · exfalso
        have hmem := reachable_mem (A := ({0, 1} : Set (Fin 3))) h (by simp) ?_
        · simp at hmem
        · intro a ha b hb
          simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at ha ⊢
          rcases ha with rfl | rfl
          · have hne := (openGraph_adj.mp hb).1
            fin_cases b
            · exact absurd rfl hne
            · simp
            · exact absurd (openGraph_adj.mp hb).2 h02
          · have hne := (openGraph_adj.mp hb).1
            fin_cases b
            · simp
            · exact absurd rfl hne
            · exact absurd (by simpa [cexEdge12, Sym2.eq_swap] using
                (openGraph_adj.mp hb).2) h12
    · exfalso
      have hmem := reachable_mem (A := ({1} : Set (Fin 3))) h (by simp) ?_
      · simp at hmem
      · intro a ha b hb
        simp only [Set.mem_singleton_iff] at ha ⊢
        subst ha
        have hne := (openGraph_adj.mp hb).1
        fin_cases b
        · exact absurd (by simpa [cexEdge01, Sym2.eq_swap] using
            (openGraph_adj.mp hb).2) h01
        · exact absurd rfl hne
        · exact absurd (by simpa [cexEdge12, Sym2.eq_swap] using
            (openGraph_adj.mp hb).2) h12
  · rintro (h | ⟨h1, h2⟩)
    · exact connects_of_adj (adj_of_mem (by decide) h)
    · exact (connects_of_adj (adj_of_mem (by decide) (by
          simpa [cexEdge01, Sym2.eq_swap] using h1))).trans
        (connects_of_adj (adj_of_mem (by decide) h2))

theorem connects_zero_two_iff (ω : Config (Fin 3)) :
    Connects ω 0 2 ↔ cexEdge02 ∈ ω ∨ (cexEdge01 ∈ ω ∧ cexEdge12 ∈ ω) := by
  constructor
  · intro h
    by_cases h02 : cexEdge02 ∈ ω
    · exact Or.inl h02
    by_cases h01 : cexEdge01 ∈ ω
    · by_cases h12 : cexEdge12 ∈ ω
      · exact Or.inr ⟨h01, h12⟩
      · exfalso
        have hmem := reachable_mem (A := ({2} : Set (Fin 3))) (connects_symm h) (by simp) ?_
        · simp at hmem
        · intro a ha b hb
          simp only [Set.mem_singleton_iff] at ha ⊢
          subst ha
          have hne := (openGraph_adj.mp hb).1
          fin_cases b
          · exact absurd (by simpa [cexEdge02, Sym2.eq_swap] using
              (openGraph_adj.mp hb).2) h02
          · exact absurd (by simpa [cexEdge12, Sym2.eq_swap] using
              (openGraph_adj.mp hb).2) h12
          · exact absurd rfl hne
    · exfalso
      have hmem := reachable_mem (A := ({0} : Set (Fin 3))) h (by simp) ?_
      · simp at hmem
      · intro a ha b hb
        simp only [Set.mem_singleton_iff] at ha ⊢
        subst ha
        have hne := (openGraph_adj.mp hb).1
        fin_cases b
        · exact absurd rfl hne
        · exact absurd (openGraph_adj.mp hb).2 h01
        · exact absurd (openGraph_adj.mp hb).2 h02
  · rintro (h | ⟨h1, h2⟩)
    · exact connects_of_adj (adj_of_mem (by decide) h)
    · exact (connects_of_adj (adj_of_mem (by decide) h1)).trans
        (connects_of_adj (adj_of_mem (by decide) (by
          simpa [cexEdge12, Sym2.eq_swap] using h2)))

theorem connSet_comm (a b : Fin 3) : connSet a b = connSet b a := by
  ext ω
  exact ⟨fun h => connects_symm h, fun h => connects_symm h⟩

/-! ## Part 3: cylinder probabilities -/

theorem measure_mem_single (e : Sym2 (Fin 3)) :
    (edgeMeasure piCex) {ω : Config (Fin 3) | e ∈ ω} =
      ((unitInterval.toNNReal (piCex e)) : ℝ≥0∞) := by
  have h := edgeMeasure_cylinder piCex ({e} : Finset (Sym2 (Fin 3)))
  simpa using h

theorem measure_e01 : (edgeMeasure piCex) {ω : Config (Fin 3) | cexEdge01 ∈ ω}
    = ((1 / 5 : ℝ≥0) : ℝ≥0∞) := by
  rw [measure_mem_single, piCex_01, toNNReal_cexFifth]

theorem measure_e02 : (edgeMeasure piCex) {ω : Config (Fin 3) | cexEdge02 ∈ ω}
    = ((1 / 5 : ℝ≥0) : ℝ≥0∞) := by
  rw [measure_mem_single, piCex_02, toNNReal_cexFifth]

theorem measure_e12 : (edgeMeasure piCex) {ω : Config (Fin 3) | cexEdge12 ∈ ω} = 0 := by
  rw [measure_mem_single, piCex_12]
  simp

theorem measure_e01_e02 :
    (edgeMeasure piCex) ({ω : Config (Fin 3) | cexEdge01 ∈ ω} ∩
      {ω : Config (Fin 3) | cexEdge02 ∈ ω}) = ((1 / 25 : ℝ≥0) : ℝ≥0∞) := by
  have h := edgeMeasure_cylinder piCex ({cexEdge01, cexEdge02} : Finset (Sym2 (Fin 3)))
  rw [Finset.prod_insert (by simp [cexEdge01_ne_02]), Finset.prod_singleton,
    piCex_01, piCex_02, toNNReal_cexFifth] at h
  rw [show ({ω : Config (Fin 3) | cexEdge01 ∈ ω} ∩ {ω : Config (Fin 3) | cexEdge02 ∈ ω})
      = {ω : Config (Fin 3) | ∀ e ∈ ({cexEdge01, cexEdge02} : Finset (Sym2 (Fin 3))), e ∈ ω}
      from by ext ω; simp]
  rw [h, ← ENNReal.coe_mul]
  norm_num

theorem coe_sum_fin3 (f : Fin 3 → ℝ≥0) :
    ((∑ i, f i : ℝ≥0) : ℝ≥0∞) = ∑ i, ((f i : ℝ≥0) : ℝ≥0∞) := by
  rw [Fin.sum_univ_three, Fin.sum_univ_three]
  push_cast
  ring

theorem sum_coe_fin3_fin3 (f : Fin 3 → Fin 3 → ℝ≥0) :
    ((∑ a : Fin 3, ∑ b : Fin 3, f a b : ℝ≥0) : ℝ≥0∞)
      = ∑ a : Fin 3, ∑ b : Fin 3, ((f a b : ℝ≥0) : ℝ≥0∞) := by
  rw [coe_sum_fin3]
  apply Finset.sum_congr rfl
  intro a _
  rw [coe_sum_fin3]

/-! ## Part 4: the two-point function and cluster-size tables -/

theorem tau_comm (a b : Fin 3) : I417Fresh.tau piCex a b = I417Fresh.tau piCex b a := by
  rw [I417Fresh.tau_def, I417Fresh.tau_def, connSet_comm]

theorem tau_00 : I417Fresh.tau piCex 0 0 = 1 := by
  rw [I417Fresh.tau_def, connSet_self_eq_univ, measure_univ]

theorem tau_11 : I417Fresh.tau piCex 1 1 = 1 := by
  rw [I417Fresh.tau_def, connSet_self_eq_univ, measure_univ]

theorem tau_22 : I417Fresh.tau piCex 2 2 = 1 := by
  rw [I417Fresh.tau_def, connSet_self_eq_univ, measure_univ]

theorem tau_01 : I417Fresh.tau piCex 0 1 = ((1 / 5 : ℝ≥0) : ℝ≥0∞) := by
  rw [I417Fresh.tau_def]
  refine le_antisymm ?_ ?_
  · calc (edgeMeasure piCex) (connSet (0 : Fin 3) 1)
        ≤ (edgeMeasure piCex) ({ω : Config (Fin 3) | cexEdge01 ∈ ω} ∪
            {ω : Config (Fin 3) | cexEdge12 ∈ ω}) :=
          measure_mono (fun ω hω => by
            rcases (connects_zero_one_iff ω).mp hω with h | ⟨-, h⟩
            · exact Or.inl h
            · exact Or.inr h)
    _ ≤ _ + _ := measure_union_le _ _
    _ = ((1 / 5 : ℝ≥0) : ℝ≥0∞) + 0 := by rw [measure_e01, measure_e12]
    _ = ((1 / 5 : ℝ≥0) : ℝ≥0∞) := by rw [add_zero]
  · calc ((1 / 5 : ℝ≥0) : ℝ≥0∞)
        = (edgeMeasure piCex) {ω : Config (Fin 3) | cexEdge01 ∈ ω} := by rw [measure_e01]
    _ ≤ (edgeMeasure piCex) (connSet (0 : Fin 3) 1) :=
        measure_mono (fun ω hω => (connects_zero_one_iff ω).mpr (Or.inl hω))

theorem tau_02 : I417Fresh.tau piCex 0 2 = ((1 / 5 : ℝ≥0) : ℝ≥0∞) := by
  rw [I417Fresh.tau_def]
  refine le_antisymm ?_ ?_
  · calc (edgeMeasure piCex) (connSet (0 : Fin 3) 2)
        ≤ (edgeMeasure piCex) ({ω : Config (Fin 3) | cexEdge02 ∈ ω} ∪
            {ω : Config (Fin 3) | cexEdge12 ∈ ω}) :=
          measure_mono (fun ω hω => by
            rcases (connects_zero_two_iff ω).mp hω with h | ⟨-, h⟩
            · exact Or.inl h
            · exact Or.inr h)
    _ ≤ _ + _ := measure_union_le _ _
    _ = ((1 / 5 : ℝ≥0) : ℝ≥0∞) + 0 := by rw [measure_e02, measure_e12]
    _ = ((1 / 5 : ℝ≥0) : ℝ≥0∞) := by rw [add_zero]
  · calc ((1 / 5 : ℝ≥0) : ℝ≥0∞)
        = (edgeMeasure piCex) {ω : Config (Fin 3) | cexEdge02 ∈ ω} := by rw [measure_e02]
    _ ≤ (edgeMeasure piCex) (connSet (0 : Fin 3) 2) :=
        measure_mono (fun ω hω => (connects_zero_two_iff ω).mpr (Or.inl hω))

theorem tau_12 : I417Fresh.tau piCex 1 2 = ((1 / 25 : ℝ≥0) : ℝ≥0∞) := by
  rw [I417Fresh.tau_def]
  refine le_antisymm ?_ ?_
  · calc (edgeMeasure piCex) (connSet (1 : Fin 3) 2)
        ≤ (edgeMeasure piCex) ({ω : Config (Fin 3) | cexEdge12 ∈ ω} ∪
            ({ω : Config (Fin 3) | cexEdge01 ∈ ω} ∩
              {ω : Config (Fin 3) | cexEdge02 ∈ ω})) :=
          measure_mono (fun ω hω => by
            rcases (connects_one_two_iff ω).mp hω with h | ⟨h1, h2⟩
            · exact Or.inl h
            · exact Or.inr ⟨h1, h2⟩)
    _ ≤ _ + _ := measure_union_le _ _
    _ = 0 + ((1 / 25 : ℝ≥0) : ℝ≥0∞) := by rw [measure_e12, measure_e01_e02]
    _ = ((1 / 25 : ℝ≥0) : ℝ≥0∞) := by rw [zero_add]
  · calc ((1 / 25 : ℝ≥0) : ℝ≥0∞)
        = (edgeMeasure piCex) ({ω : Config (Fin 3) | cexEdge01 ∈ ω} ∩
            {ω : Config (Fin 3) | cexEdge02 ∈ ω}) := by rw [measure_e01_e02]
    _ ≤ (edgeMeasure piCex) (connSet (1 : Fin 3) 2) :=
        measure_mono (fun ω hω => (connects_one_two_iff ω).mpr (Or.inr ⟨hω.1, hω.2⟩))

/-- The two-point function of the counterexample as a `ℝ≥0`-valued table. -/
noncomputable def tauNN : Fin 3 → Fin 3 → ℝ≥0
  | 0, 0 => 1
  | 1, 1 => 1
  | 2, 2 => 1
  | 0, _ => 1 / 5
  | _, 0 => 1 / 5
  | _, _ => 1 / 25

theorem tau_eq (a b : Fin 3) : I417Fresh.tau piCex a b = ((tauNN a b : ℝ≥0) : ℝ≥0∞) := by
  fin_cases a
  · fin_cases b
    · simpa [tauNN] using tau_00
    · simpa [tauNN] using tau_01
    · simpa [tauNN] using tau_02
  · fin_cases b
    · simpa [tauNN] using (show I417Fresh.tau piCex 1 0 = ((1 / 5 : ℝ≥0) : ℝ≥0∞) from by
        rw [tau_comm]; exact tau_01)
    · simpa [tauNN] using tau_11
    · simpa [tauNN] using tau_12
  · fin_cases b
    · simpa [tauNN] using (show I417Fresh.tau piCex 2 0 = ((1 / 5 : ℝ≥0) : ℝ≥0∞) from by
        rw [tau_comm]; exact tau_02)
    · simpa [tauNN] using (show I417Fresh.tau piCex 2 1 = ((1 / 25 : ℝ≥0) : ℝ≥0∞) from by
        rw [tau_comm]; exact tau_12)
    · simpa [tauNN] using tau_22

/-- The expected cluster size `χ(a) = ∑_z τ(a,z)`. -/
noncomputable def hubNN : Fin 3 → ℝ≥0
  | 0 => 7 / 5
  | _ => 31 / 25

theorem hubArmSum_eq (a : Fin 3) :
    I417Fresh.hubArmSum piCex a = ((hubNN a : ℝ≥0) : ℝ≥0∞) := by
  rw [I417Fresh.hubArmSum, tsum_fintype, Fin.sum_univ_three]
  simp only [tau_eq]
  rw [← ENNReal.coe_add, ← ENNReal.coe_add]
  congr 1
  fin_cases a <;> simp [tauNN, hubNN] <;> norm_num

/-- The `a`-summand of `fourArmFresh`. -/
noncomputable def armNN : Fin 3 → ℝ≥0 :=
  fun a => tauNN 0 a * tauNN a 0 * (hubNN a * hubNN a)

theorem fourArmFresh_eq :
    I417FreshTwo.fourArmFresh piCex 0 0 = ((∑ a : Fin 3, armNN a : ℝ≥0) : ℝ≥0∞) := by
  rw [I417FreshTwo.fourArmFresh, tsum_fintype]
  simp only [I417FreshTwo.kernel_def, tau_eq, hubArmSum_eq]
  trans ((∑ a : Fin 3, ((armNN a : ℝ≥0) : ℝ≥0∞)))
  · apply Finset.sum_congr rfl
    intro a _
    rw [← ENNReal.coe_mul, ← ENNReal.coe_mul, ← ENNReal.coe_mul]
    rfl
  · rw [← coe_sum_fin3]

theorem armNN_sum : (∑ a : Fin 3, armNN a) = 32547 / 15625 := by
  simp only [Fin.sum_univ_three, armNN, tauNN, hubNN]
  rw [← NNReal.coe_inj]
  push_cast
  norm_num

theorem fourArmFresh_val :
    I417FreshTwo.fourArmFresh piCex 0 0 = ((32547 / 15625 : ℝ≥0) : ℝ≥0∞) := by
  rw [fourArmFresh_eq, armNN_sum]

/-! ## Part 5: the labelled events, the left side, and the refutation -/

theorem labelEvent_fin_two (g : Fin 2 → Fin 3) :
    I417A.labelEvent (0 : Fin 3) g = connSet 0 (g 0) ∩ connSet 0 (g 1) := by
  ext ω
  constructor
  · intro h
    exact ⟨mem_cluster_iff.mp (h 0), mem_cluster_iff.mp (h 1)⟩
  · rintro ⟨h0, h1⟩ i
    fin_cases i
    · exact mem_cluster_iff.mpr h0
    · exact mem_cluster_iff.mpr h1

theorem measure_conn_0_1_0_2 :
    (edgeMeasure piCex) (connSet (0 : Fin 3) 1 ∩ connSet (0 : Fin 3) 2)
      = ((1 / 25 : ℝ≥0) : ℝ≥0∞) := by
  refine le_antisymm ?_ ?_
  · calc (edgeMeasure piCex) (connSet (0 : Fin 3) 1 ∩ connSet (0 : Fin 3) 2)
        ≤ (edgeMeasure piCex) (({ω : Config (Fin 3) | cexEdge01 ∈ ω} ∩
            {ω : Config (Fin 3) | cexEdge02 ∈ ω}) ∪ {ω : Config (Fin 3) | cexEdge12 ∈ ω}) :=
          measure_mono (fun ω hω => by
            obtain ⟨h1, h2⟩ := hω
            rcases (connects_zero_one_iff ω).mp h1 with a | ⟨-, b⟩
            · rcases (connects_zero_two_iff ω).mp h2 with c | ⟨-, d⟩
              · exact Or.inl ⟨a, c⟩
              · exact Or.inr d
            · exact Or.inr b)
    _ ≤ _ + _ := measure_union_le _ _
    _ = ((1 / 25 : ℝ≥0) : ℝ≥0∞) + 0 := by rw [measure_e01_e02, measure_e12]
    _ = ((1 / 25 : ℝ≥0) : ℝ≥0∞) := by rw [add_zero]
  · calc ((1 / 25 : ℝ≥0) : ℝ≥0∞)
        = (edgeMeasure piCex) ({ω : Config (Fin 3) | cexEdge01 ∈ ω} ∩
            {ω : Config (Fin 3) | cexEdge02 ∈ ω}) := by rw [measure_e01_e02]
    _ ≤ (edgeMeasure piCex) (connSet (0 : Fin 3) 1 ∩ connSet (0 : Fin 3) 2) :=
        measure_mono (fun ω hω =>
          ⟨(connects_zero_one_iff ω).mpr (Or.inl hω.1),
           (connects_zero_two_iff ω).mpr (Or.inl hω.2)⟩)

/-- The labelled-event table `labelNN a b = P(a ∈ K_0, b ∈ K_0)`. -/
noncomputable def labelNN : Fin 3 → Fin 3 → ℝ≥0
  | 0, 0 => 1
  | 0, _ => 1 / 5
  | _, 0 => 1 / 5
  | 1, 1 => 1 / 5
  | 2, 2 => 1 / 5
  | _, _ => 1 / 25

theorem label_measure_00 :
    (edgeMeasure piCex) (connSet (0 : Fin 3) 0 ∩ connSet (0 : Fin 3) 0)
      = ((labelNN (0 : Fin 3) 0 : ℝ≥0) : ℝ≥0∞) := by
  rw [connSet_self_eq_univ, Set.univ_inter, measure_univ]
  simp [labelNN]

theorem label_measure_01 :
    (edgeMeasure piCex) (connSet (0 : Fin 3) 0 ∩ connSet (0 : Fin 3) 1)
      = ((labelNN (0 : Fin 3) 1 : ℝ≥0) : ℝ≥0∞) := by
  rw [connSet_self_eq_univ, Set.univ_inter, ← I417Fresh.tau_def, tau_01]
  simp [labelNN]

theorem label_measure_02 :
    (edgeMeasure piCex) (connSet (0 : Fin 3) 0 ∩ connSet (0 : Fin 3) 2)
      = ((labelNN (0 : Fin 3) 2 : ℝ≥0) : ℝ≥0∞) := by
  rw [connSet_self_eq_univ, Set.univ_inter, ← I417Fresh.tau_def, tau_02]
  simp [labelNN]

theorem label_measure_10 :
    (edgeMeasure piCex) (connSet (0 : Fin 3) 1 ∩ connSet (0 : Fin 3) 0)
      = ((labelNN (1 : Fin 3) 0 : ℝ≥0) : ℝ≥0∞) := by
  rw [Set.inter_comm, connSet_self_eq_univ, Set.univ_inter, ← I417Fresh.tau_def, tau_01]
  simp [labelNN]

theorem label_measure_11 :
    (edgeMeasure piCex) (connSet (0 : Fin 3) 1 ∩ connSet (0 : Fin 3) 1)
      = ((labelNN (1 : Fin 3) 1 : ℝ≥0) : ℝ≥0∞) := by
  rw [Set.inter_self, ← I417Fresh.tau_def, tau_01]
  simp [labelNN]

theorem label_measure_12 :
    (edgeMeasure piCex) (connSet (0 : Fin 3) 1 ∩ connSet (0 : Fin 3) 2)
      = ((labelNN (1 : Fin 3) 2 : ℝ≥0) : ℝ≥0∞) := by
  rw [measure_conn_0_1_0_2]
  simp [labelNN]

theorem label_measure_20 :
    (edgeMeasure piCex) (connSet (0 : Fin 3) 2 ∩ connSet (0 : Fin 3) 0)
      = ((labelNN (2 : Fin 3) 0 : ℝ≥0) : ℝ≥0∞) := by
  rw [Set.inter_comm, connSet_self_eq_univ, Set.univ_inter, ← I417Fresh.tau_def, tau_02]
  simp [labelNN]

theorem label_measure_21 :
    (edgeMeasure piCex) (connSet (0 : Fin 3) 2 ∩ connSet (0 : Fin 3) 1)
      = ((labelNN (2 : Fin 3) 1 : ℝ≥0) : ℝ≥0∞) := by
  rw [Set.inter_comm, measure_conn_0_1_0_2]
  simp [labelNN]

theorem label_measure_22 :
    (edgeMeasure piCex) (connSet (0 : Fin 3) 2 ∩ connSet (0 : Fin 3) 2)
      = ((labelNN (2 : Fin 3) 2 : ℝ≥0) : ℝ≥0∞) := by
  rw [Set.inter_self, ← I417Fresh.tau_def, tau_02]
  simp [labelNN]

theorem label_measure (a b : Fin 3) :
    (edgeMeasure piCex) (connSet (0 : Fin 3) a ∩ connSet (0 : Fin 3) b)
      = ((labelNN a b : ℝ≥0) : ℝ≥0∞) := by
  fin_cases a <;> fin_cases b
  · exact label_measure_00
  · exact label_measure_01
  · exact label_measure_02
  · exact label_measure_10
  · exact label_measure_11
  · exact label_measure_12
  · exact label_measure_20
  · exact label_measure_21
  · exact label_measure_22

theorem tsum_freshMark_eq :
    ∑' g : Fin 2 → Fin 3, (edgeMeasure piCex) (I417Gen.freshMark 0 g 0 0)
      = ((∑ a : Fin 3, ∑ b : Fin 3, labelNN a b : ℝ≥0) : ℝ≥0∞) := by
  have hterm : ∀ g : Fin 2 → Fin 3, (edgeMeasure piCex) (I417Gen.freshMark 0 g 0 0)
      = ((labelNN (g 0) (g 1) : ℝ≥0) : ℝ≥0∞) := by
    intro g
    rw [freshMark_self_eq_labelEvent, labelEvent_fin_two, label_measure]
  have hfun : ∀ a b : Fin 3,
      labelNN ((finTwoArrowEquiv (Fin 3)).symm (a, b) 0)
        ((finTwoArrowEquiv (Fin 3)).symm (a, b) 1) = labelNN a b := by
    intro a b
    have h0 : (finTwoArrowEquiv (Fin 3)).symm (a, b) 0 = a := by simp [finTwoArrowEquiv]
    have h1 : (finTwoArrowEquiv (Fin 3)).symm (a, b) 1 = b := by simp [finTwoArrowEquiv]
    rw [h0, h1]
  simp only [hterm]
  rw [tsum_fintype, ← Equiv.sum_comp (finTwoArrowEquiv (Fin 3)).symm]
  rw [Fintype.sum_prod_type]
  simp only [hfun]
  rw [sum_coe_fin3_fin3]

theorem labelNN_sum : (∑ a : Fin 3, ∑ b : Fin 3, labelNN a b) = 57 / 25 := by
  simp only [Fin.sum_univ_three, labelNN]
  rw [← NNReal.coe_inj]
  push_cast
  norm_num

theorem LHS_val :
    ∑' g : Fin 2 → Fin 3, (edgeMeasure piCex) (I417Gen.freshMark 0 g 0 0)
      = ((57 / 25 : ℝ≥0) : ℝ≥0∞) := by
  rw [tsum_freshMark_eq, labelNN_sum]

/-- **The four-factor `q = 2` fresh input fails at `π = piCex`, `y = w = 0`, `j = 0`.** -/
theorem fourArmFresh_lt_freshSum :
    I417FreshTwo.fourArmFresh piCex 0 0
      < ∑' g : Fin 2 → Fin 3, (edgeMeasure piCex) (I417Gen.freshMark 0 g 0 0) := by
  rw [fourArmFresh_val, LHS_val, ENNReal.coe_lt_coe]
  norm_num

/-- **The universal statement is false**: there are a countable vertex set, a law with
`∀ e, π e < 1` and `y w j` for which the four-factor fresh bound fails. -/
theorem not_fourArmFresh_bound :
    ¬ (∀ (y w : Fin 3) (j : Fin 2),
        (∑' g : Fin 2 → Fin 3, (edgeMeasure piCex) (I417Gen.freshMark y g j w))
          ≤ I417FreshTwo.fourArmFresh piCex y w) := by
  intro h
  exact absurd (h 0 0 0) (not_le.mpr fourArmFresh_lt_freshSum)

end PercLib.CriticalLRP.I417FreshTwo.Cex

namespace PercLib.CriticalLRP.I417FreshTwo.Cex

set_option linter.hashCommand false

#print axioms freshMark_self_eq_labelEvent
#print axioms piCex_lt_one
#print axioms tau_01
#print axioms tau_12
#print axioms fourArmFresh_val
#print axioms labelNN_sum
#print axioms LHS_val
#print axioms fourArmFresh_lt_freshSum
#print axioms not_fourArmFresh_bound

end PercLib.CriticalLRP.I417FreshTwo.Cex
