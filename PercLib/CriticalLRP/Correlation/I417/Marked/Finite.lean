/- Independently rebuilt and verified at production revision
    eb9b71a3cf20a0fe9906271415f5b17efd80f5ad.
    Original scratch source is recorded below. -/
module

public import PercLib.CriticalLRP.Correlation.I417.Marked.Diagram
public import PercLib.CriticalLRP.TreeExpansion.AtlasRealization.MarkedAtlas.Bound

/-!
Finite conversion and assembly for the marked diagram bound.
-/

open scoped ENNReal NNReal

@[expose] public section

set_option linter.unusedSectionVars false
set_option linter.unusedFintypeInType false
set_option linter.unusedDecidableInType false

namespace PercLib.CriticalLRP.FiniteMarkedJoin

open PercLib.CriticalLRP.TreeExpansion
open PercLib.CriticalLRP.TreeExpansion.Real
open PercLib.CriticalLRP.I417Marked
open PercLib.CriticalLRP.MarkedAtlas
open PercLib.CriticalLRP.TreeGraph

universe u v

variable {V : Type u} [Fintype V] [DecidableEq V]

/-- A finite product of finite ENNReal entries is finite. -/
theorem prod_ne_top_of_forall_ne_top {ι : Type*} (s : Finset ι) (f : ι → ℝ≥0∞)
    (hf : ∀ i ∈ s, f i ≠ ∞) : ∏ i ∈ s, f i ≠ ∞ := by
  classical
  induction s using Finset.induction with
  | empty => simp
  | @insert a s ha ih =>
    rw [Finset.prod_insert ha]
    exact ENNReal.mul_ne_top (hf a (Finset.mem_insert_self a s))
      (ih (fun b hb => hf b (Finset.mem_insert_of_mem hb)))

/-- Finite internal-position sums are finite whenever every atlas kernel entry is finite. -/
theorem posSumWtE_ne_top_of_finite (k : V → V → ℝ≥0∞) (hk : ∀ a b, k a b ≠ ∞)
    {α : Type v} [DecidableEq α] (t : RTree α) (y : α → V) (x : V) :
    posSumWtE k t y x ≠ ∞ := by
  classical
  rw [posSumWtE, tsum_fintype]
  refine ENNReal.sum_ne_top.mpr (fun φ _ => ?_)
  exact prod_ne_top_of_forall_ne_top _ _ (fun _ _ => hk _ _)

/-- Convert a finite atlas weight to real notation without any integrability assumption. -/
theorem posSumWtE_toReal (k : V → V → ℝ≥0∞) (hk : ∀ a b, k a b ≠ ∞)
    {α : Type v} [DecidableEq α] (t : RTree α) (y : α → V) (x : V) :
    (posSumWtE k t y x).toReal =
      ∑ φ : t.IPos → V, ∏ e : AEdge t,
        (k (srcPos t φ x e) (dstPos t φ y e)).toReal := by
  classical
  rw [posSumWtE, tsum_fintype]
  rw [ENNReal.toReal_sum (fun φ _ => prod_ne_top_of_forall_ne_top _ _ (fun _ _ => hk _ _))]
  exact Finset.sum_congr rfl (fun φ _ => ENNReal.toReal_prod _ _)

/-- The marked labelled diagram has finite values under a finite finite-valued kernel. -/
theorem labelledMarkedDiagram_ne_top (k : V → V → ℝ≥0∞) (hk : ∀ a b, k a b ≠ ∞)
    (p : ℕ) (x w : V) : labelledMarkedDiagram k p x w ≠ ∞ := by
  classical
  unfold labelledMarkedDiagram
  refine ENNReal.sum_ne_top.mpr (fun t _ => ?_)
  rw [tsum_fintype]
  refine ENNReal.sum_ne_top.mpr (fun y _ => ?_)
  by_cases hy : y (markLabel p) = w
  · simpa [hy] using posSumWtE_ne_top_of_finite k hk t.1 y x
  · simp [hy]

/-- Convert the labelled marked diagram from ENNReal to finite real notation. -/
theorem labelledMarkedDiagram_toReal (k : V → V → ℝ≥0∞) (hk : ∀ a b, k a b ≠ ∞)
    (p : ℕ) (x w : V) :
    (labelledMarkedDiagram k p x w).toReal =
      ∑ t : LTon (Label p) (Finset.univ : Finset (Label p)),
        ∑' y : Label p → V, (if y (markLabel p) = w then 1 else 0) *
          ∑ φ : t.1.IPos → V, ∏ e : AEdge t.1,
            (k (srcPos t.1 φ x e) (dstPos t.1 φ y e)).toReal := by
  classical
  unfold labelledMarkedDiagram
  rw [ENNReal.toReal_sum (fun t _ => ?_)]
  · refine Finset.sum_congr rfl (fun t _ => ?_)
    rw [tsum_fintype (f := fun y : Label p → V =>
      (if y (markLabel p) = w then 1 else 0) * posSumWtE k t.1 y x)]
    rw [ENNReal.toReal_sum (s := (Finset.univ : Finset (Label p → V)))
      (f := fun y : Label p → V =>
        (if y (markLabel p) = w then 1 else 0) * posSumWtE k t.1 y x)
      (fun y _ => ?_)]
    · simp only [tsum_fintype]
      refine Finset.sum_congr rfl (fun (y : Label p → V) _ => ?_)
      by_cases hy : y (markLabel p) = w
      · simp only [hy, ↓reduceIte, one_mul]
        exact posSumWtE_toReal (V := V) k hk t.1 y x
      · simp [hy]
    · by_cases hy : y (markLabel p) = w
      · simpa [hy] using posSumWtE_ne_top_of_finite k hk t.1 y x
      · simp [hy]
  · rw [tsum_fintype]
    refine ENNReal.sum_ne_top.mpr (fun y _ => ?_)
    by_cases hy : y (markLabel p) = w
    · simpa [hy] using posSumWtE_ne_top_of_finite k hk t.1 y x
    · simp [hy]

/-- Freeze one of a `Fin p ⊕ PUnit` assignment's label values and sum the other `p`.
Both repeated ordinary vertices and a mark equal to an ordinary vertex are allowed. -/
theorem sum_pinned_label (p : ℕ) (w : V) (F : (Label p → V) → ℝ) :
    (∑ f : Fin p → V, F (markTerm f w)) =
      ∑' y : Label p → V, if y (markLabel p) = w then F y else 0 := by
  classical
  let e : (Fin p → V) ≃ {y : Label p → V // y (markLabel p) = w} :=
    { toFun := fun f => ⟨markTerm f w, rfl⟩
      invFun := fun y => fun i => y.1 (Sum.inl i)
      left_inv := by intro f; rfl
      right_inv := by
        intro y
        apply Subtype.ext
        funext i
        cases i with
        | inl i => rfl
        | inr a =>
          cases a
          exact y.2.symm }
  refine (Fintype.sum_equiv e (fun f => F (markTerm f w))
    (fun y => F y.1) (fun f => rfl)).trans ?_
  rw [tsum_fintype (f := fun y : Label p → V => if y (markLabel p) = w then F y else 0)]
  let g : ({y : Label p → V // y (markLabel p) = w} ⊕
      {y : Label p → V // ¬ y (markLabel p) = w}) → ℝ :=
    Sum.elim (fun y => F y.1) (fun _ => 0)
  calc
    (∑ y : {y : Label p → V // y (markLabel p) = w}, F y.1) = ∑ z, g z := by
      rw [Fintype.sum_sum_type]
      simp [g]
    _ = ∑ y : Label p → V, if y (markLabel p) = w then F y else 0 := by
      symm
      refine Fintype.sum_equiv
        ((Equiv.sumCompl (fun y : Label p → V => y (markLabel p) = w)).symm)
        (fun y => if y (markLabel p) = w then F y else 0) g (fun y => ?_)
      by_cases hy : y (markLabel p) = w
      · simp [g, hy, Equiv.sumCompl]
      · simp [g, hy, Equiv.sumCompl]

variable {E : Type*} [Fintype E] [DecidableEq E]

/-- Join the finite marked-atlas BK bound to the exact marked-depth evaluation.
The only model premise beyond BK and bounded Bernoulli weights is the usual constant row sum
(the finite transitive first-moment input).  The vertex and edge types are both finite. -/
theorem finite_marked_moment_le_polygon_toReal
    (pr : E → ℝ) (hp : ∀ e, 0 ≤ pr e) (hp1 : ∀ e, pr e ≤ 1)
    (hBK : TreeGraph.BKIncreasing pr) (ends : E → Sym2 V) (x w : V)
    (k : V → V → ℝ≥0∞) (hk : ∀ a b, k a b ≠ ∞)
    (hkval : ∀ a b, (k a b).toReal = prob pr {ω : Finset E | TreeGraph.Conn ends ω a b})
    (χ : ℝ≥0∞) (hχ : ∀ v, ∑' y, k v y = χ) (p : ℕ) :
    (∑ f : Fin p → V, prob pr (MarkedBaseEvent ends x f w)) ≤
      (markedPolygonBound χ k p x w).toReal := by
  classical
  rw [← labelledMarkedDiagram_eq_polygon k χ hχ p x w]
  calc
    (∑ f : Fin p → V, prob pr (MarkedBaseEvent ends x f w))
        ≤ ∑ f : Fin p → V, ∑ t : LTon (Label p) (Finset.univ : Finset (Label p)),
          markDiag pr ends x (markTerm f w) t := by
      refine Finset.sum_le_sum (fun f _ => ?_)
      exact prob_markedBase_le_shapeSum pr hp hp1 hBK ends x f w
    _ = ∑ t : LTon (Label p) (Finset.univ : Finset (Label p)),
          ∑ f : Fin p → V, markDiag pr ends x (markTerm f w) t := Finset.sum_comm
    _ = (labelledMarkedDiagram k p x w).toReal := by
      rw [labelledMarkedDiagram_toReal k hk p x w]
      refine Finset.sum_congr rfl (fun t _ => ?_)
      have hterm (y : Label p → V) :
          markDiag pr ends x y t =
            ∑ φ : t.1.IPos → V, ∏ e : AEdge t.1,
              (k (srcPos t.1 φ x e) (dstPos t.1 φ y e)).toReal := by
        simp only [markDiag, ConnEvent, hkval]
      calc
        (∑ f : Fin p → V, markDiag pr ends x (markTerm f w) t) =
            ∑' y : Label p → V, if y (markLabel p) = w then markDiag pr ends x y t else 0 :=
          sum_pinned_label p w (fun y => markDiag pr ends x y t)
        _ = ∑' y : Label p → V,
            (if y (markLabel p) = w then 1 else 0) * markDiag pr ends x y t := by
          rw [tsum_fintype (f := fun y : Label p → V =>
            if y (markLabel p) = w then markDiag pr ends x y t else 0)]
          simp only [tsum_fintype]
          refine Finset.sum_congr rfl (fun y _ => ?_)
          by_cases hy : y (markLabel p) = w <;> simp [hy]
        _ = ∑' y : Label p → V,
            (if y (markLabel p) = w then 1 else 0) *
              ∑ φ : t.1.IPos → V, ∏ e : AEdge t.1,
                (k (srcPos t.1 φ x e) (dstPos t.1 φ y e)).toReal := by
          simp only [hterm, tsum_fintype]

/-- The joined finite marked bound directly at the cast finite Bernoulli connection kernel.
The constant row sum remains an explicit transitivity input; its finiteness is automatic here
because the vertex type and all kernel entries are finite. -/
theorem finite_marked_moment_le_polygon_of_real
    (pr : E → ℝ) (hp : ∀ e, 0 ≤ pr e) (hp1 : ∀ e, pr e ≤ 1)
    (hBK : TreeGraph.BKIncreasing pr) (ends : E → Sym2 V) (x w : V)
    (χ : ℝ≥0∞)
    (hχ : ∀ v, ∑' y, ENNReal.ofReal
      (prob pr {ω : Finset E | TreeGraph.Conn ends ω v y}) = χ) (p : ℕ) :
    (∑ f : Fin p → V, prob pr (MarkedBaseEvent ends x f w)) ≤
      (markedPolygonBound χ
        (fun a b => ENNReal.ofReal
          (prob pr {ω : Finset E | TreeGraph.Conn ends ω a b})) p x w).toReal := by
  apply finite_marked_moment_le_polygon_toReal pr hp hp1 hBK ends x w
  · intro a b
    exact ENNReal.ofReal_ne_top
  · intro a b
    rw [ENNReal.toReal_ofReal (prob_nonneg hp hp1 _)]
  · exact hχ

end PercLib.CriticalLRP.FiniteMarkedJoin
