/-
Final assembly of the `p = 4`, `k = 2` instance of the Hutchcroft tree-graph moment bound.
Ultramath `smwpq441z` member m3 (Direction C).

The native fourth cluster moment is expanded by Tonelli into the fourfold sum of four-point
connection probabilities.  Every four-point connection event is covered by one of the fifteen
normalized `CombShape` slot patterns, each of which is bounded — with the *same* common centre
`v` for both joint two-arm groups — by threefold BK.  The fifteen resulting double-star
diagrams all evaluate to `E|K_0|^2 * (E|K_0| * E|K_0|^2)`, using full translation invariance
of the profile only (no finiteness, no separate second-moment hypothesis).
-/
module

public import PercLib.CriticalLRP.Correlation.FourthMoment.MixedK2.Event

open Set MeasureTheory
open scoped ENNReal BigOperators
open PercLib.Percolation.Bond
open PercLib.Probability

@[expose] public section

namespace PercLib.CriticalLRP.TreeExpansion.FivePoint

variable {V : Type*}

/-- The union over both branch vertices of the shallow/deep regrouping is contained in the
three-group certificate event, whose bound does not mention `u` or `w`. -/
theorem combSlots_union_subset_threeCert [Countable V] (b0 b1 b2 b3 b4 v : V) :
    (⋃ u : V, ⋃ w : V, {ω | CombSlots (openGraph ω) b0 b1 b2 b3 b4 u v w}) ⊆
      ThreeCertEvent (V := V) (conn b0 v ∩ conn b1 v) (conn b2 v)
        (conn b3 v ∩ conn b4 v) := by
  intro ω hω
  obtain ⟨u, hu⟩ := Set.mem_iUnion.mp hω
  obtain ⟨w, hw⟩ := Set.mem_iUnion.mp hu
  exact combSlots_subset_threeCert b0 b1 b2 b3 b4 u v w hw

/-- **The `u`- and `w`-free three-group slot bound.** -/
theorem combSlots_event_three_free [Countable V] (π : Sym2 V → unitInterval)
    (b0 b1 b2 b3 b4 v : V) :
    law π (⋃ u : V, ⋃ w : V, {ω | CombSlots (openGraph ω) b0 b1 b2 b3 b4 u v w}) ≤
      jointP π b0 b1 v * (tau π b2 v * jointP π b3 b4 v) :=
  (measure_mono (combSlots_union_subset_threeCert b0 b1 b2 b3 b4 v)).trans
    (by
      have h := threeCert_le (V := V) π (isUpperSet_inter_conn b0 b1 v)
        (isIncreasing_connects b2 v) (isUpperSet_inter_conn b3 b4 v)
      simpa [jointP, tau, conn] using h)

/-- **Per-pattern slot bound, all fifteen patterns.**  The two branch vertices are union
bounded; the remaining sum is over the common centre and is exactly the slot diagram. -/
theorem slotEvent_le_k2 [Countable V] (π : Sym2 V → unitInterval) (k : Fin 15)
    (T : Fin 5 → V) :
    law π (⋃ u : V, ⋃ v : V, ⋃ w : V, {ω | CombShape (openGraph ω) k u v w T}) ≤
      slotDiagramK2 π k T := by
  rw [show (⋃ u : V, ⋃ v : V, ⋃ w : V, {ω | CombShape (openGraph ω) k u v w T}) =
      ⋃ v : V, ⋃ u : V, ⋃ w : V, {ω | CombShape (openGraph ω) k u v w T} from
    Set.iUnion_comm (fun u v => ⋃ w : V, {ω | CombShape (openGraph ω) k u v w T})]
  refine (measure_iUnion_le (μ := law π) (s := fun v : V =>
    ⋃ u : V, ⋃ w : V, {ω | CombShape (openGraph ω) k u v w T})).trans ?_
  refine ENNReal.tsum_le_tsum fun v => ?_
  have h := combSlots_event_three_free (V := V) π (T (pat k 0)) (T (pat k 1))
    (T (pat k 2)) (T (pat k 3)) (T (pat k 4)) v
  simpa only [CombShape, slotDiagramK2, starK2] using h

/-- The pointwise four-point event bound by the fifteen slot diagrams. -/
theorem fourPoint_le_slotSumK2 [Countable V] (π : Sym2 V → unitInterval)
    (o x1 x2 x3 x4 : V) :
    law π (conn o x1 ∩ conn o x2 ∩ conn o x3 ∩ conn o x4) ≤
      ∑' k : Fin 15, slotDiagramK2 π k ![o, x1, x2, x3, x4] := by
  refine (measure_mono (fourPoint_subset_slotEvents o x1 x2 x3 x4)).trans ?_
  rw [show (⋃ k : Fin 15, ⋃ w : V, ⋃ u : V, ⋃ v : V,
        {ω | CombShape (openGraph ω) k u v w ![o, x1, x2, x3, x4]}) =
      ⋃ k : Fin 15, ⋃ u : V, ⋃ v : V, ⋃ w : V,
        {ω | CombShape (openGraph ω) k u v w ![o, x1, x2, x3, x4]} from by
    ext ω
    simp only [Set.mem_iUnion]
    exact ⟨fun ⟨k, w, u, v, h⟩ => ⟨k, u, v, w, h⟩,
      fun ⟨k, u, v, w, h⟩ => ⟨k, w, u, v, h⟩⟩]
  exact (measure_iUnion_le (μ := law π) (s := fun k : Fin 15 =>
    ⋃ u : V, ⋃ v : V, ⋃ w : V,
      {ω | CombShape (openGraph ω) k u v w ![o, x1, x2, x3, x4]})).trans
    (ENNReal.tsum_le_tsum fun k => slotEvent_le_k2 π k ![o, x1, x2, x3, x4])

/-- **Lemma I.4.16 at `p = 4`, `k = 2`.**  For independent bond percolation with a fully
translation-invariant profile `π` on a countable abelian group, the fourth cluster moment is
bounded by `15 (E|K_0|^2)^2 E|K_0|`, with no moment-finiteness hypothesis and no separate
second-moment invariance hypothesis. -/
theorem fourth_moment_mixed_k2_le [Countable V] [AddCommGroup V]
    (π : Sym2 V → unitInterval)
    (hq : ∀ x y g : V, π s(x + g, y + g) = π s(x, y)) :
    ∫⁻ ω, (PercLib.CriticalLRP.Percolation.cardFun
        (PercLib.CriticalLRP.cluster ω 0)) ^ 4 ∂(law π) ≤
      15 * (∫⁻ ω, (PercLib.CriticalLRP.Percolation.cardFun
          (PercLib.CriticalLRP.cluster ω 0)) ^ 2 ∂(law π)) ^ 2 *
        (∫⁻ ω, PercLib.CriticalLRP.Percolation.cardFun
          (PercLib.CriticalLRP.cluster ω 0) ∂(law π)) := by
  have hmain : ∫⁻ ω, (PercLib.CriticalLRP.Percolation.cardFun
        (PercLib.CriticalLRP.cluster ω 0)) ^ 4 ∂(law π) ≤
      15 * (secondMoment π 0) ^ 2 * (firstMoment π 0) := by
    rw [lintegral_cardFun_four_eq π 0]
    calc ∑' y, ∑' z, ∑' w, ∑' q,
          law π (conn 0 y ∩ conn 0 z ∩ conn 0 w ∩ conn 0 q)
        ≤ ∑' y, ∑' z, ∑' w, ∑' q, ∑' k : Fin 15,
            slotDiagramK2 π k ![0, y, z, w, q] :=
          ENNReal.tsum_le_tsum fun y => ENNReal.tsum_le_tsum fun z =>
            ENNReal.tsum_le_tsum fun w => ENNReal.tsum_le_tsum fun q =>
              fourPoint_le_slotSumK2 π 0 y z w q
      _ = ∑' k : Fin 15, ∑' y, ∑' z, ∑' w, ∑' q,
            slotDiagramK2 π k ![0, y, z, w, q] :=
          tsum_fin_four_swap (F := fun y z w q k => slotDiagramK2 π k ![0, y, z, w, q])
      _ = ∑' k : Fin 15,
            (secondMoment π 0 * ((∑' x, tau π 0 x) * secondMoment π 0)) :=
          tsum_congr fun k => tsum_slotDiagramK2 π hq k
      _ = 15 * (secondMoment π 0 * ((∑' x, tau π 0 x) * secondMoment π 0)) :=
          tsum_fin15_const _
      _ = 15 * (secondMoment π 0) ^ 2 * (firstMoment π 0) := by
          rw [firstMoment_eq π 0]
          ring
  simpa only [secondMoment, firstMoment] using hmain

#print axioms PercLib.CriticalLRP.TreeExpansion.FivePoint.fourth_moment_mixed_k2_le

end PercLib.CriticalLRP.TreeExpansion.FivePoint
