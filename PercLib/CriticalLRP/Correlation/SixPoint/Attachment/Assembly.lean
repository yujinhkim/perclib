/-
Copyright (c) 2026 PercLib contributors. Released under Apache 2.0.

Final assembly of the `p = 5`, `k = 1` mixed fifth cluster-moment bound.
Internal vertices stay in the per-pattern union bounds and the joint pair
stays in one BK group.  The shape sum over `Fin 15 × Fin 7` becomes `105`
only via `tsum_fin15_fin7_const`.

Analytic assembly supplied by Ultramath `smwpszpj0` member `m3`.  Independently
checked with the repaired `Final` at revision
`5c25062c071ed99bd44904ceb185d8dba8f9093f`.
-/
module

public import PercLib.CriticalLRP.Correlation.SixPoint.Attachment.Final

open Set MeasureTheory
open scoped ENNReal BigOperators
open PercLib.Percolation.Bond
open PercLib.CriticalLRP.TreeExpansion.FivePoint

@[expose] public section

namespace PercLib.CriticalLRP.TreeExpansion.SixPoint

variable {V : Type*}

/-! ## Reindexing `Fin 15 × Fin 7` -/

/-- A double sum over the shape parameters as a single sum over the product index. -/
theorem tsum_fin15_fin7 (f : Fin 15 → Fin 7 → ℝ≥0∞) :
    (∑' k : Fin 15, ∑' j : Fin 7, f k j) = ∑' p : Fin 15 × Fin 7, f p.1 p.2 :=
  (ENNReal.tsum_prod (f := f)).symm

/-- Move the two shape sums out past the five free vertex sums. -/
theorem tsum_five_fin15_fin7_swap (F : V → V → V → V → V → Fin 15 → Fin 7 → ℝ≥0∞) :
    (∑' y, ∑' z, ∑' w, ∑' q, ∑' r, ∑' k : Fin 15, ∑' j : Fin 7, F y z w q r k j) =
      ∑' p : Fin 15 × Fin 7, ∑' y, ∑' z, ∑' w, ∑' q, ∑' r, F y z w q r p.1 p.2 := by
  calc (∑' y, ∑' z, ∑' w, ∑' q, ∑' r, ∑' k : Fin 15, ∑' j : Fin 7, F y z w q r k j)
      = ∑' y, ∑' z, ∑' w, ∑' q, ∑' r,
          ∑' p : Fin 15 × Fin 7, F y z w q r p.1 p.2 :=
        tsum_congr fun y => tsum_congr fun z => tsum_congr fun w => tsum_congr fun q =>
          tsum_congr fun r => tsum_fin15_fin7 _
    _ = ∑' y, ∑' z, ∑' w, ∑' q, ∑' p : Fin 15 × Fin 7, ∑' r, F y z w q r p.1 p.2 :=
        tsum_congr fun y => tsum_congr fun z => tsum_congr fun w => tsum_congr fun q =>
          ENNReal.tsum_comm
    _ = ∑' y, ∑' z, ∑' w, ∑' p : Fin 15 × Fin 7, ∑' q, ∑' r, F y z w q r p.1 p.2 :=
        tsum_congr fun y => tsum_congr fun z => tsum_congr fun w => ENNReal.tsum_comm
    _ = ∑' y, ∑' z, ∑' p : Fin 15 × Fin 7, ∑' w, ∑' q, ∑' r, F y z w q r p.1 p.2 :=
        tsum_congr fun y => tsum_congr fun z => ENNReal.tsum_comm
    _ = ∑' y, ∑' p : Fin 15 × Fin 7, ∑' z, ∑' w, ∑' q, ∑' r, F y z w q r p.1 p.2 :=
        tsum_congr fun y => ENNReal.tsum_comm
    _ = ∑' p : Fin 15 × Fin 7, ∑' y, ∑' z, ∑' w, ∑' q, ∑' r, F y z w q r p.1 p.2 :=
        ENNReal.tsum_comm

/-! ## Where the root `0` sits in each of the fifteen patterns -/

/-- In every one of the fifteen normalised patterns the root `0` occupies slot `0` or slot `2`. -/
theorem pat_root_slot (k : Fin 15) :
    PercLib.CriticalLRP.TreeExpansion.FivePoint.pat k 0 = 0 ∨
      PercLib.CriticalLRP.TreeExpansion.FivePoint.pat k 2 = 0 := by
  rw [← patF_eq]
  fin_cases k <;> decide

/-- Slot `0` and slot `2` of a pattern are distinct, so at most one case above fires. -/
theorem pat_zero_ne_two (k : Fin 15) :
    PercLib.CriticalLRP.TreeExpansion.FivePoint.pat k 0 ≠
      PercLib.CriticalLRP.TreeExpansion.FivePoint.pat k 2 := by
  rw [← patF_eq]
  fin_cases k <;> decide

/-- **Pointwise `15 * 7` slot bound.**  This is the review `pointwiseU` / `pointwiseV` pair,
merged into one unconditional statement by case analysis on the root slot. -/
theorem pointwiseD [Countable V] (π : Sym2 V → unitInterval) (T : Fin 6 → V)
    (k : Fin 15) (j : Fin 7) :
    law π (⋃ c : V, ⋃ u : V, ⋃ v : V, ⋃ w : V,
        {ω | SixShape (openGraph ω) k j c u v w T}) ≤ slotD π T k j := by
  by_cases h : PercLib.CriticalLRP.TreeExpansion.FivePoint.pat k 0 = 0
  · simp only [slotD, ite_eq_left h]
    exact slotU_le π j _ _ _ _ _ _
  · have h2 : PercLib.CriticalLRP.TreeExpansion.FivePoint.pat k 2 = 0 :=
      (pat_root_slot k).resolve_left h
    simp only [slotD, ite_eq_right h]
    exact slotV_le π j _ _ _ _ _ _

/-- Compatibility with the root-slot-conditioned form. The condition is redundant for this
particular pointwise bound, but is retained in the interface. -/
theorem pointwiseU_of_slotD [Countable V] (π : Sym2 V → unitInterval) (k : Fin 15) (j : Fin 7)
    (_hk : PercLib.CriticalLRP.TreeExpansion.FivePoint.pat k 0 = 0) (T : Fin 6 → V) :
    law π (⋃ c, ⋃ u, ⋃ v, ⋃ w, {ω | SixShape (openGraph ω) k j c u v w T}) ≤
      slotU π j (T (lift5 (PercLib.CriticalLRP.TreeExpansion.FivePoint.pat k 0)))
        (T (lift5 (PercLib.CriticalLRP.TreeExpansion.FivePoint.pat k 1)))
        (T (lift5 (PercLib.CriticalLRP.TreeExpansion.FivePoint.pat k 2)))
        (T (lift5 (PercLib.CriticalLRP.TreeExpansion.FivePoint.pat k 3)))
        (T (lift5 (PercLib.CriticalLRP.TreeExpansion.FivePoint.pat k 4))) (T 5) := by
  simpa only [slotD, ite_eq_left _hk] using pointwiseD π T k j

/-- The corresponding form when the root is in the middle comb slot. -/
theorem pointwiseV_of_slotD [Countable V] (π : Sym2 V → unitInterval) (k : Fin 15) (j : Fin 7)
    (_hk : PercLib.CriticalLRP.TreeExpansion.FivePoint.pat k 2 = 0) (T : Fin 6 → V) :
    law π (⋃ c, ⋃ u, ⋃ v, ⋃ w, {ω | SixShape (openGraph ω) k j c u v w T}) ≤
      slotV π j (T (lift5 (PercLib.CriticalLRP.TreeExpansion.FivePoint.pat k 0)))
        (T (lift5 (PercLib.CriticalLRP.TreeExpansion.FivePoint.pat k 1)))
        (T (lift5 (PercLib.CriticalLRP.TreeExpansion.FivePoint.pat k 2)))
        (T (lift5 (PercLib.CriticalLRP.TreeExpansion.FivePoint.pat k 3)))
        (T (lift5 (PercLib.CriticalLRP.TreeExpansion.FivePoint.pat k 4))) (T 5) := by
  have h0 : ¬ PercLib.CriticalLRP.TreeExpansion.FivePoint.pat k 0 = 0 :=
    fun h => pat_zero_ne_two k (h.trans _hk.symm)
  simpa only [slotD, ite_eq_right h0] using pointwiseD π T k j

/-! ## The composable `105`-fold cover -/

/-- **The deterministic cover, regrouped.**  The two-step union bound keeps the witness sums
`c, u, v, w` *inside* the per-`(k, j)` measure of the union, which is the form the BK step
needs.  (The fully expanded per-`(k, j, c, u, v, w)` sum cannot be composed with the
union-measure bound: `μ (⋃ i, A i) ≤ ∑' i, μ (A i)` runs the other way.  Conversely the
chunked form re-derives the expanded one -- see `sixPoint_le_sixShapeSum_via_chunk` below --
so it is strictly the stronger interface.) -/
theorem sixPoint_le_sixShapeChunk [Countable V] (π : Sym2 V → unitInterval) (T : Fin 6 → V) :
    law π (⋂ i : Fin 6,
        {ω : PercLib.CriticalLRP.Config V | PercLib.CriticalLRP.Connects ω (T 0) (T i)}) ≤
      ∑' k : Fin 15, ∑' j : Fin 7,
        law π (⋃ c : V, ⋃ u : V, ⋃ v : V, ⋃ w : V,
          {ω | SixShape (openGraph ω) k j c u v w T}) := by
  refine (measure_mono (sixPoint_subset_sixShapeEvents T)).trans ?_
  refine (measure_iUnion_le (μ := law π) (s := fun k : Fin 15 => ⋃ j : Fin 7, ⋃ c : V,
    ⋃ u : V, ⋃ v : V, ⋃ w : V, {ω | SixShape (openGraph ω) k j c u v w T})).trans ?_
  refine ENNReal.tsum_le_tsum fun k => ?_
  exact measure_iUnion_le (μ := law π) (s := fun j : Fin 7 => ⋃ c : V, ⋃ u : V, ⋃ v : V,
    ⋃ w : V, {ω | SixShape (openGraph ω) k j c u v w T})

/-- The chunked cover implies the expanded `Cover.sixPoint_le_sixShapeSum`: the expanded
statement is the weaker (larger right-hand side) of the two. -/
theorem sixPoint_le_sixShapeSum_via_chunk [Countable V] (π : Sym2 V → unitInterval)
    (T : Fin 6 → V) :
    law π (⋂ i : Fin 6,
        {ω : PercLib.CriticalLRP.Config V | PercLib.CriticalLRP.Connects ω (T 0) (T i)}) ≤
      ∑' k : Fin 15, ∑' j : Fin 7, ∑' c : V, ∑' u : V, ∑' v : V, ∑' w : V,
        law π {ω | SixShape (openGraph ω) k j c u v w T} := by
  refine (sixPoint_le_sixShapeChunk π T).trans ?_
  refine ENNReal.tsum_le_tsum fun k => ENNReal.tsum_le_tsum fun j => ?_
  refine (measure_iUnion_le (μ := law π) (s := fun c : V => ⋃ u : V, ⋃ v : V, ⋃ w : V,
    {ω | SixShape (openGraph ω) k j c u v w T})).trans ?_
  refine ENNReal.tsum_le_tsum fun c => ?_
  refine (measure_iUnion_le (μ := law π) (s := fun u : V => ⋃ v : V, ⋃ w : V,
    {ω | SixShape (openGraph ω) k j c u v w T})).trans ?_
  refine ENNReal.tsum_le_tsum fun u => ?_
  refine (measure_iUnion_le (μ := law π) (s := fun v : V => ⋃ w : V,
    {ω | SixShape (openGraph ω) k j c u v w T})).trans ?_
  exact ENNReal.tsum_le_tsum fun v => measure_iUnion_le _

/-- The six-point connection event for the root tuple `(0, y, z, w, q, r)`. -/
theorem iInter_six_conn [Zero V] (y z w q r : V) :
    (⋂ i : Fin 6, {ω : PercLib.CriticalLRP.Config V |
        PercLib.CriticalLRP.Connects ω (![0, y, z, w, q, r] (0 : Fin 6))
          (![0, y, z, w, q, r] i)}) =
      conn 0 y ∩ conn 0 z ∩ conn 0 w ∩ conn 0 q ∩ conn 0 r := by
  ext ω
  simp only [Set.mem_iInter, Set.mem_ofPred_eq, Set.mem_inter_iff, conn]
  constructor
  · intro h
    exact ⟨⟨⟨⟨h 1, h 2⟩, h 3⟩, h 4⟩, h 5⟩
  · rintro ⟨⟨⟨⟨h1, h2⟩, h3⟩, h4⟩, h5⟩ i
    fin_cases i
    · exact SimpleGraph.Reachable.refl _
    · exact h1
    · exact h2
    · exact h3
    · exact h4
    · exact h5

/-! ## Assembling the fifth moment -/

/-- **Abstract assembly.**  A per-`(k, j)` pointwise bound on the five-point connection
probability, together with the exact value of each of the `105` slot diagrams, gives the
native fifth-moment inequality.  This is the whole `ENNReal` content of the argument: the
deterministic cover and the BK bounds only feed `hD`, and `Final` only feeds `hE`. -/
theorem fifth_moment_le_of_slotChunks [Countable V] [AddCommGroup V]
    (π : Sym2 V → unitInterval)
    (D : Fin 15 → Fin 7 → V → V → V → V → V → ℝ≥0∞)
    (hD : ∀ y z w q r : V,
      law π (conn 0 y ∩ conn 0 z ∩ conn 0 w ∩ conn 0 q ∩ conn 0 r) ≤
        ∑' k : Fin 15, ∑' j : Fin 7, D k j y z w q r)
    (hE : ∀ (k : Fin 15) (j : Fin 7),
      (∑' y, ∑' z, ∑' w, ∑' q, ∑' r, D k j y z w q r) =
        secondMoment π 0 * (∑' x, tau π 0 x) ^ 6) :
    ∫⁻ ω, (PercLib.CriticalLRP.Percolation.cardFun (PercLib.CriticalLRP.cluster ω (0 : V))) ^ 5
        ∂(law π) ≤
      105 * (∫⁻ ω, (PercLib.CriticalLRP.Percolation.cardFun
        (PercLib.CriticalLRP.cluster ω (0 : V))) ^ 2 ∂(law π)) *
        (∫⁻ ω, PercLib.CriticalLRP.Percolation.cardFun
          (PercLib.CriticalLRP.cluster ω (0 : V)) ∂(law π)) ^ 6 := by
  have hmain :
      ∫⁻ ω, (PercLib.CriticalLRP.Percolation.cardFun (PercLib.CriticalLRP.cluster ω (0 : V))) ^ 5
          ∂(law π) ≤
        105 * secondMoment π 0 * (∑' x, tau π 0 x) ^ 6 := by
    rw [lintegral_cardFun_five_eq π 0]
    calc ∑' y, ∑' z, ∑' w, ∑' q, ∑' r,
          law π (conn 0 y ∩ conn 0 z ∩ conn 0 w ∩ conn 0 q ∩ conn 0 r)
        ≤ ∑' y, ∑' z, ∑' w, ∑' q, ∑' r, ∑' k : Fin 15, ∑' j : Fin 7,
            D k j y z w q r :=
          ENNReal.tsum_le_tsum fun y => ENNReal.tsum_le_tsum fun z =>
            ENNReal.tsum_le_tsum fun w => ENNReal.tsum_le_tsum fun q =>
              ENNReal.tsum_le_tsum fun r => hD y z w q r
      _ = ∑' p : Fin 15 × Fin 7, ∑' y, ∑' z, ∑' w, ∑' q, ∑' r,
            D p.1 p.2 y z w q r :=
          tsum_five_fin15_fin7_swap (fun y z w q r k j => D k j y z w q r)
      _ = ∑' _ : Fin 15 × Fin 7, secondMoment π 0 * (∑' x, tau π 0 x) ^ 6 := by
          refine tsum_congr fun p => ?_
          obtain ⟨k, j⟩ := p
          exact hE k j
      _ = 105 * (secondMoment π 0 * (∑' x, tau π 0 x) ^ 6) := tsum_fin15_fin7_const _
      _ = 105 * secondMoment π 0 * (∑' x, tau π 0 x) ^ 6 := (mul_assoc _ _ _).symm
  simpa only [← firstMoment_eq, firstMoment, secondMoment] using hmain

/-- **The `p = 5`, `k = 1` bound, as an evaluation-function interface.**
The two arguments are supplied below by the compiled `evalslotU` and `evalslotV`;
they do not occur in `fifth_moment_le`.  Profile invariance is used only in the
exact evaluations, not in the finite union and summation accounting. -/
theorem fifth_moment_le_of_slotEvaluations [Countable V] [AddCommGroup V]
    (π : Sym2 V → unitInterval)
    (hU : ∀ (k : Fin 15) (j : Fin 7),
      PercLib.CriticalLRP.TreeExpansion.FivePoint.pat k 0 = 0 →
      (∑' y, ∑' z, ∑' w, ∑' q, ∑' r,
        slotU π j (![0, y, z, w, q, r] (lift5 (PercLib.CriticalLRP.TreeExpansion.FivePoint.pat k 0)))
          (![0, y, z, w, q, r] (lift5 (PercLib.CriticalLRP.TreeExpansion.FivePoint.pat k 1)))
          (![0, y, z, w, q, r] (lift5 (PercLib.CriticalLRP.TreeExpansion.FivePoint.pat k 2)))
          (![0, y, z, w, q, r] (lift5 (PercLib.CriticalLRP.TreeExpansion.FivePoint.pat k 3)))
          (![0, y, z, w, q, r] (lift5 (PercLib.CriticalLRP.TreeExpansion.FivePoint.pat k 4)))
          (![0, y, z, w, q, r] 5)) =
        secondMoment π 0 * (∑' x, tau π 0 x) ^ 6)
    (hV : ∀ (k : Fin 15) (j : Fin 7),
      PercLib.CriticalLRP.TreeExpansion.FivePoint.pat k 2 = 0 →
      (∑' y, ∑' z, ∑' w, ∑' q, ∑' r,
        slotV π j (![0, y, z, w, q, r] (lift5 (PercLib.CriticalLRP.TreeExpansion.FivePoint.pat k 0)))
          (![0, y, z, w, q, r] (lift5 (PercLib.CriticalLRP.TreeExpansion.FivePoint.pat k 1)))
          (![0, y, z, w, q, r] (lift5 (PercLib.CriticalLRP.TreeExpansion.FivePoint.pat k 2)))
          (![0, y, z, w, q, r] (lift5 (PercLib.CriticalLRP.TreeExpansion.FivePoint.pat k 3)))
          (![0, y, z, w, q, r] (lift5 (PercLib.CriticalLRP.TreeExpansion.FivePoint.pat k 4)))
          (![0, y, z, w, q, r] 5)) =
        secondMoment π 0 * (∑' x, tau π 0 x) ^ 6) :
    ∫⁻ ω, (PercLib.CriticalLRP.Percolation.cardFun (PercLib.CriticalLRP.cluster ω (0 : V))) ^ 5
        ∂(law π) ≤
      105 * (∫⁻ ω, (PercLib.CriticalLRP.Percolation.cardFun
        (PercLib.CriticalLRP.cluster ω (0 : V))) ^ 2 ∂(law π)) *
        (∫⁻ ω, PercLib.CriticalLRP.Percolation.cardFun
          (PercLib.CriticalLRP.cluster ω (0 : V)) ∂(law π)) ^ 6 := by
  refine fifth_moment_le_of_slotChunks π (fun k j y z w q r => slotD π ![0, y, z, w, q, r] k j)
    ?_ ?_
  · intro y z w q r
    rw [← iInter_six_conn y z w q r]
    refine (sixPoint_le_sixShapeChunk (V := V) π ![0, y, z, w, q, r]).trans ?_
    exact ENNReal.tsum_le_tsum fun k => ENNReal.tsum_le_tsum fun j => pointwiseD π _ k j
  · intro k j
    by_cases h : PercLib.CriticalLRP.TreeExpansion.FivePoint.pat k 0 = 0
    · simp only [slotD, ite_eq_left h]
      exact hU k j h
    · have h2 : PercLib.CriticalLRP.TreeExpansion.FivePoint.pat k 2 = 0 :=
        (pat_root_slot k).resolve_left h
      simp only [slotD, ite_eq_right h]
      exact hV k j h2


/-- The `p = 5`, `k = 1` mixed fifth cluster-moment bound. -/
theorem fifth_moment_le [Countable V] [AddCommGroup V] (π : Sym2 V → unitInterval)
    (hq : ∀ x y g : V, π s(x + g, y + g) = π s(x, y)) :
    ∫⁻ ω, (PercLib.CriticalLRP.Percolation.cardFun
      (PercLib.CriticalLRP.cluster ω (0 : V))) ^ 5 ∂(law π) ≤
      105 * (∫⁻ ω, (PercLib.CriticalLRP.Percolation.cardFun
        (PercLib.CriticalLRP.cluster ω (0 : V))) ^ 2 ∂(law π)) *
        (∫⁻ ω, PercLib.CriticalLRP.Percolation.cardFun
          (PercLib.CriticalLRP.cluster ω (0 : V)) ∂(law π)) ^ 6 :=
  fifth_moment_le_of_slotEvaluations π
    (fun k j hk => evalslotU π hq k j hk)
    (fun k j hk => evalslotV π hq k j hk)


end PercLib.CriticalLRP.TreeExpansion.SixPoint

#print axioms PercLib.CriticalLRP.TreeExpansion.SixPoint.tsum_fin15_fin7
#print axioms PercLib.CriticalLRP.TreeExpansion.SixPoint.tsum_five_fin15_fin7_swap
#print axioms PercLib.CriticalLRP.TreeExpansion.SixPoint.pat_root_slot
#print axioms PercLib.CriticalLRP.TreeExpansion.SixPoint.pat_zero_ne_two
#print axioms PercLib.CriticalLRP.TreeExpansion.SixPoint.pointwiseD
#print axioms PercLib.CriticalLRP.TreeExpansion.SixPoint.pointwiseU_of_slotD
#print axioms PercLib.CriticalLRP.TreeExpansion.SixPoint.pointwiseV_of_slotD
#print axioms PercLib.CriticalLRP.TreeExpansion.SixPoint.sixPoint_le_sixShapeChunk
#print axioms PercLib.CriticalLRP.TreeExpansion.SixPoint.sixPoint_le_sixShapeSum_via_chunk
#print axioms PercLib.CriticalLRP.TreeExpansion.SixPoint.iInter_six_conn
#print axioms PercLib.CriticalLRP.TreeExpansion.SixPoint.fifth_moment_le_of_slotChunks
#print axioms PercLib.CriticalLRP.TreeExpansion.SixPoint.fifth_moment_le_of_slotEvaluations
#print axioms PercLib.CriticalLRP.TreeExpansion.SixPoint.fifth_moment_le
