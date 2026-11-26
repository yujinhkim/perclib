/-
Swarm `smwxk27m7`, member `m2`, direction (A) `SOCKET-ORDER-TO-SHAPE-BOUNDS`.

# From the root-socket evaluations to shape-mass bounds

`K2Mass.shapeTotal π 0 k j` is the mass of the six-terminal shape event of labelled pattern `k`
at split `j`, with the five non-root terminals summed over `V`.  By the accepted root-class
collapse (`K2Mass.shapeTotal_eq_rootSlot`) the `15 × 7` shape masses collapse onto the two
canonical root sockets `patSlot0` (root `0` in comb slot `0`) and `patSlot2` (root `0` in comb
slot `2`).

This file proves the off-middle canonical bound

  `shapeTotal π 0 patSlot{0,2} j ≤ shapeCost π 0`

at the split positions `j = 0, 1, 5, 6`, for **both** root sockets, from

* the certified event regrouping at the split position (`SplitPattern.combSystem_twoJointThree_*`
  composed with fivefold BK, `twoJointThree_le`), which bounds the shape event mass by the
  two-interior-vertex sum of the five-factor slot product `slotProd2`;
* the accepted root-socket evaluation of that slot product
  (`SplitEval2.RootSocket.slotU2_*_tsum`, `slotV2_*_tsum`), which returns `monomial2 π 0`;
* one reindexing of the seven nested nonnegative sums, from the order in which the shape sum
  produces its arguments (`b`-terminals first, interior vertices last) to the peel order of the
  evaluation (`TwoJointEval.tsum_seven_perm`, i.e. `ENNReal.tsum_comm` iterated).

Nothing is factored, no independence is used, no finiteness of any moment is assumed, and the
pin of each evaluation keeps its root socket: `monomial2` and `shapeCost` are the same element of
`ℝ≥0∞`, `(E|K|²)²(E|K|)³`, so the bound is exactly the one consumed by
`K2Mass.fifth_moment_k2_le_of_rootSlot_bounds`.

## What is *not* claimed

The split positions `j = 3` and `j = 4` are not treated here: their event-level certificates are
the subject of the two dedicated directions registered for them.  `j = 2` (the middle split) is
already unconditional at production HEAD through `K2Mass.shapeTotal_mid_le` and is not repeated.
The moment theorem itself is therefore still conditional on the `j = 3, 4` root-socket bounds;
`fifth_moment_k2_le_of_rootSlot_0156` below states exactly how much is left.
-/
module

public import PercLib.CriticalLRP.Correlation.SixPoint.SplitEvaluation3.Defs

/-!
# Shape-mass bounds at both canonical root sockets for the splits `j = 0, 1, 5, 6`
-/

open Set MeasureTheory
open scoped ENNReal BigOperators
open PercLib.Percolation.Bond
open PercLib.CriticalLRP.TreeExpansion.FivePoint
open PercLib.CriticalLRP.TreeExpansion.SixPoint
open PercLib.CriticalLRP.TreeExpansion.SixPoint.K2Mass
open PercLib.CriticalLRP.SixPoint.TwoJointEval
open PercLib.CriticalLRP.SixPoint.SplitEval
open PercLib.CriticalLRP.SixPoint.SplitEval2
open PercLib.CriticalLRP.SixPoint.SplitEval2.RootSocket

@[expose] public section

namespace PercLib.CriticalLRP.SixPoint.SplitEval3

set_option linter.style.longLine false
set_option linter.style.setOption false

variable {V : Type*}

/-! ## The shape mass at a canonical root socket is `massSlot0` / `massSlot2` -/

/-- `pat patSlot0` is the identity pattern. -/
theorem pat_patSlot0 : pat patSlot0 = ![0, 1, 2, 3, 4] := by
  funext i; fin_cases i <;> rfl

/-- `pat patSlot2` puts the root in comb slot `2`. -/
theorem pat_patSlot2 : pat patSlot2 = ![1, 2, 0, 3, 4] := by
  funext i; fin_cases i <;> rfl

/-- **`shapeMass` at `patSlot0` is `massSlot0`.**  `pat patSlot0 = ![0,1,2,3,4]`, so the five
comb leaves of the labelled pattern are the root `x` followed by `y, z, w, q`, and the sixth
terminal is `r`. -/
theorem shapeMass_patSlot0 (π : Sym2 V → unitInterval) (x : V) (j : Fin 7) (y z w q r : V) :
    shapeMass π x patSlot0 j y z w q r = massSlot0 π x j y z w q r := by
  rw [shapeMass_apply, massSlot0]
  simp only [SixShape, pat_patSlot0, lift5]
  rfl

/-- **`shapeMass` at `patSlot2` is `massSlot2`.**  `pat patSlot2 = ![1,2,0,3,4]`, so the third
comb leaf `b₂` is the root `x` and the five summed terminals are `y = b₀`, `z = b₁`, `w = b₃`,
`q = b₄`, `r = t`. -/
theorem shapeMass_patSlot2 (π : Sym2 V → unitInterval) (x : V) (j : Fin 7) (y z w q r : V) :
    shapeMass π x patSlot2 j y z w q r = massSlot2 π x j y z w q r := by
  rw [shapeMass_apply, massSlot2]
  simp only [SixShape, pat_patSlot2, lift5]
  rfl

/-- `shapeTotal` at `patSlot0` as one fivefold sum of `massSlot0`. -/
theorem shapeTotal_patSlot0_eq_tsum (π : Sym2 V → unitInterval) (x : V) (j : Fin 7) :
    shapeTotal π x patSlot0 j = ∑' b1, ∑' b2, ∑' b3, ∑' b4, ∑' t,
      massSlot0 π x j b1 b2 b3 b4 t :=
  tsum_congr fun y => tsum_congr fun z => tsum_congr fun w => tsum_congr fun q =>
    tsum_congr fun r => shapeMass_patSlot0 π x j y z w q r

/-- `shapeTotal` at `patSlot2` as one fivefold sum of `massSlot2`. -/
theorem shapeTotal_patSlot2_eq_tsum (π : Sym2 V → unitInterval) (x : V) (j : Fin 7) :
    shapeTotal π x patSlot2 j = ∑' b0, ∑' b1, ∑' b3, ∑' b4, ∑' t,
      massSlot2 π x j b0 b1 b3 b4 t :=
  tsum_congr fun y => tsum_congr fun z => tsum_congr fun w => tsum_congr fun q =>
    tsum_congr fun r => shapeMass_patSlot2 π x j y z w q r

/-! ## The slot products of the four treated split positions, in `slotProd2` form -/

/-- `SplitEval.prodZero` is `slotProd2 π 0` at `(i₁, i₂) = (v, c)`: only the order of the two
innermost two-point factors differs. -/
theorem prodZero_eq_slotProd2 (π : Sym2 V → unitInterval) (b0 b1 b2 b3 b4 t v c : V) :
    prodZero π b0 b1 b2 b3 b4 t v c = slotProd2 π 0 v c b0 b1 b2 b3 b4 t := by
  simp only [prodZero, slotProd2]
  ring

/-- `prodOne` is `slotProd2 π 1` at `(i₁, i₂) = (v, c)`. -/
theorem prodOne_eq_slotProd2 (π : Sym2 V → unitInterval) (b0 b1 b2 b3 b4 t v c : V) :
    prodOne π b0 b1 b2 b3 b4 t v c = slotProd2 π 1 v c b0 b1 b2 b3 b4 t := rfl

/-- `SplitEval.prodFive` is `slotProd2 π 5` at `(i₁, i₂) = (c, w)`. -/
theorem prodFive_eq_slotProd2 (π : Sym2 V → unitInterval) (b0 b1 b2 b3 b4 t c w : V) :
    prodFive π b0 b1 b2 b3 b4 t c w = slotProd2 π 5 c w b0 b1 b2 b3 b4 t := rfl

/-- `SplitEval.prodSix` is `slotProd2 π 6` at `(i₁, i₂) = (v, w)`. -/
theorem prodSix_eq_slotProd2 (π : Sym2 V → unitInterval) (b0 b1 b2 b3 b4 t v w : V) :
    prodSix π b0 b1 b2 b3 b4 t v w = slotProd2 π 6 v w b0 b1 b2 b3 b4 t := rfl

/-! ## The `j = 1` event bridge

The only split position among `0, 1, 5, 6` whose union bound is not in production: the star
centres `u, w` do not occur in the certificate `combSystem_twoJointThree_one`, so they are
eliminated by containment *inside* the event, before the union bound.  This is exactly the
pattern of `SplitEval.combSystem_zero_union_le`. -/

/-- **The `j = 1` slot bound, free vertices included.** -/
theorem combSystem_one_union_le [Countable V] (π : Sym2 V → unitInterval)
    (b0 b1 b2 b3 b4 t : V) :
    law π (⋃ c : V, ⋃ u : V, ⋃ v : V, ⋃ w' : V,
        {ω : PercLib.CriticalLRP.Config V |
          CombSystem (PercLib.CriticalLRP.openGraph ω) b0 b1 b2 b3 b4 t u v w' c 1}) ≤
      slotOne π b0 b1 b2 b3 b4 t := by
  classical
  have hsub : (⋃ c : V, ⋃ u : V, ⋃ v : V, ⋃ w' : V,
      {ω : PercLib.CriticalLRP.Config V |
        CombSystem (PercLib.CriticalLRP.openGraph ω) b0 b1 b2 b3 b4 t u v w' c 1}) ⊆
      (⋃ c : V, ⋃ v : V, TwoJointThreeCert (conn b0 v ∩ conn c v)
        (conn b3 v ∩ conn b4 v) (conn b2 v) (conn b1 c) (conn t c)) := by
    intro ω hω
    simp only [Set.mem_iUnion] at hω ⊢
    obtain ⟨c, u, v, w, hw⟩ := hω
    exact ⟨c, v, SplitPattern.combSystem_twoJointThree_one b0 b1 b2 b3 b4 t u v w c hw⟩
  calc law π (⋃ c : V, ⋃ u : V, ⋃ v : V, ⋃ w' : V,
        {ω : PercLib.CriticalLRP.Config V |
          CombSystem (PercLib.CriticalLRP.openGraph ω) b0 b1 b2 b3 b4 t u v w' c 1})
      ≤ law π (⋃ c : V, ⋃ v : V, TwoJointThreeCert (conn b0 v ∩ conn c v)
          (conn b3 v ∩ conn b4 v) (conn b2 v) (conn b1 c) (conn t c)) :=
        measure_mono hsub
    _ ≤ ∑' c : V, ∑' v : V, law π (TwoJointThreeCert (conn b0 v ∩ conn c v)
          (conn b3 v ∩ conn b4 v) (conn b2 v) (conn b1 c) (conn t c)) := by
        refine (measure_iUnion_le (μ := law π) (s := fun c : V => ⋃ v : V,
          TwoJointThreeCert (conn b0 v ∩ conn c v) (conn b3 v ∩ conn b4 v)
            (conn b2 v) (conn b1 c) (conn t c))).trans ?_
        exact ENNReal.tsum_le_tsum fun c =>
          measure_iUnion_le (μ := law π) (s := fun v : V =>
            TwoJointThreeCert (conn b0 v ∩ conn c v) (conn b3 v ∩ conn b4 v)
              (conn b2 v) (conn b1 c) (conn t c))
    _ ≤ ∑' c : V, ∑' v : V, prodOne π b0 b1 b2 b3 b4 t v c :=
        ENNReal.tsum_le_tsum fun c => ENNReal.tsum_le_tsum fun v => by
          simpa only [prodOne, jointP, tau] using
            twoJointThree_le (V := V) π
              ((isUpperSet_conn b0 v).inter (isUpperSet_conn c v))
              ((isUpperSet_conn b3 v).inter (isUpperSet_conn b4 v))
              (isUpperSet_conn b2 v) (isUpperSet_conn b1 c) (isUpperSet_conn t c)
    _ = slotOne π b0 b1 b2 b3 b4 t := rfl

/-! ## `j = 0` -/

/-- **`j = 0`, root socket `b₀`.** -/
theorem shapeTotal_patSlot0_zero_le [Countable V] [AddCommGroup V] (π : Sym2 V → unitInterval)
    (hq : ∀ x y g : V, π s(x + g, y + g) = π s(x, y)) :
    shapeTotal π 0 patSlot0 0 ≤ shapeCost π 0 := by
  have hb : (∑' b1, ∑' b2, ∑' b3, ∑' b4, ∑' t, massSlot0 π 0 0 b1 b2 b3 b4 t)
      ≤ ∑' b1, ∑' b2, ∑' b3, ∑' b4, ∑' t, slotZero π 0 b1 b2 b3 b4 t :=
    ENNReal.tsum_le_tsum fun b1 => ENNReal.tsum_le_tsum fun b2 =>
      ENNReal.tsum_le_tsum fun b3 => ENNReal.tsum_le_tsum fun b4 =>
        ENNReal.tsum_le_tsum fun t => combSystem_zero_union_le (V := V) π 0 b1 b2 b3 b4 t
  have hperm : (∑' b1, ∑' b2, ∑' b3, ∑' b4, ∑' t, slotZero π 0 b1 b2 b3 b4 t)
      = ∑' c, ∑' t', ∑' v, ∑' b1, ∑' b2, ∑' b3, ∑' b4,
          slotProd2 π 0 v c 0 b1 b2 b3 b4 t' := by
    simp only [slotZero, prodZero_eq_slotProd2]
    exact (tsum_seven_perm permZero0
      (H := fun a0 a1 a2 a3 a4 a5 a6 => slotProd2 π 0 a6 a5 0 a0 a1 a2 a3 a4)).symm
  calc shapeTotal π 0 patSlot0 0
      = ∑' b1, ∑' b2, ∑' b3, ∑' b4, ∑' t, massSlot0 π 0 0 b1 b2 b3 b4 t :=
        shapeTotal_patSlot0_eq_tsum π 0 0
    _ ≤ ∑' b1, ∑' b2, ∑' b3, ∑' b4, ∑' t, slotZero π 0 b1 b2 b3 b4 t := hb
    _ = ∑' c, ∑' t', ∑' v, ∑' b1, ∑' b2, ∑' b3, ∑' b4,
          slotProd2 π 0 v c 0 b1 b2 b3 b4 t' := hperm
    _ = monomial2 π 0 := RootSocket.slotU2_zero_tsum π hq 0
    _ = shapeCost π 0 := rfl

/-- **`j = 0`, root socket `b₂`.** -/
theorem shapeTotal_patSlot2_zero_le [Countable V] [AddCommGroup V] (π : Sym2 V → unitInterval)
    (hq : ∀ x y g : V, π s(x + g, y + g) = π s(x, y)) :
    shapeTotal π 0 patSlot2 0 ≤ shapeCost π 0 := by
  have hb : (∑' b0, ∑' b1, ∑' b3, ∑' b4, ∑' t, massSlot2 π 0 0 b0 b1 b3 b4 t)
      ≤ ∑' b0, ∑' b1, ∑' b3, ∑' b4, ∑' t, slotZero π b0 b1 0 b3 b4 t :=
    ENNReal.tsum_le_tsum fun b0 => ENNReal.tsum_le_tsum fun b1 =>
      ENNReal.tsum_le_tsum fun b3 => ENNReal.tsum_le_tsum fun b4 =>
        ENNReal.tsum_le_tsum fun t => combSystem_zero_union_le (V := V) π b0 b1 0 b3 b4 t
  have hperm : (∑' b0, ∑' b1, ∑' b3, ∑' b4, ∑' t, slotZero π b0 b1 0 b3 b4 t)
      = ∑' v, ∑' b1, ∑' c, ∑' t', ∑' b0, ∑' b3, ∑' b4,
          slotProd2 π 0 v c b0 b1 0 b3 b4 t' := by
    simp only [slotZero, prodZero_eq_slotProd2]
    exact (tsum_seven_perm permZero2
      (H := fun a0 a1 a2 a3 a4 a5 a6 => slotProd2 π 0 a6 a5 a0 a1 0 a2 a3 a4)).symm
  calc shapeTotal π 0 patSlot2 0
      = ∑' b0, ∑' b1, ∑' b3, ∑' b4, ∑' t, massSlot2 π 0 0 b0 b1 b3 b4 t :=
        shapeTotal_patSlot2_eq_tsum π 0 0
    _ ≤ ∑' b0, ∑' b1, ∑' b3, ∑' b4, ∑' t, slotZero π b0 b1 0 b3 b4 t := hb
    _ = ∑' v, ∑' b1, ∑' c, ∑' t', ∑' b0, ∑' b3, ∑' b4,
          slotProd2 π 0 v c b0 b1 0 b3 b4 t' := hperm
    _ = monomial2 π 0 := RootSocket.slotV2_zero_tsum π hq 0
    _ = shapeCost π 0 := rfl



/-- **`j = 1`, root socket `b₀`.** -/
theorem shapeTotal_patSlot0_one_le [Countable V] [AddCommGroup V] (π : Sym2 V → unitInterval)
    (hq : ∀ x y g : V, π s(x + g, y + g) = π s(x, y)) :
    shapeTotal π 0 patSlot0 1 ≤ shapeCost π 0 := by
  have hb : (∑' b1, ∑' b2, ∑' b3, ∑' b4, ∑' t, massSlot0 π 0 1 b1 b2 b3 b4 t)
      ≤ ∑' b1, ∑' b2, ∑' b3, ∑' b4, ∑' t, slotOne π 0 b1 b2 b3 b4 t := by
    refine ENNReal.tsum_le_tsum fun b1 =>
      ENNReal.tsum_le_tsum fun b2 =>
      ENNReal.tsum_le_tsum fun b3 =>
      ENNReal.tsum_le_tsum fun b4 =>
      ENNReal.tsum_le_tsum fun t =>
        (show _ ≤ _ from combSystem_one_union_le (V := V) π 0 b1 b2 b3 b4 t)
  have hperm : (∑' b1, ∑' b2, ∑' b3, ∑' b4, ∑' t, slotOne π 0 b1 b2 b3 b4 t)
      = ∑' i₁, ∑' i₂, ∑' b1, ∑' t', ∑' b2, ∑' b3, ∑' b4,
          slotProd2 π 1 i₁ i₂ 0 b1 b2 b3 b4 t' := by
    simp only [slotOne, prodOne_eq_slotProd2]
    exact (tsum_seven_perm permOne0 (H := fun a0 a1 a2 a3 a4 a5 a6 => slotProd2 π 1 a6 a5 0 a0 a1 a2 a3 a4)).symm
  calc shapeTotal π 0 patSlot0 1
      = ∑' b1, ∑' b2, ∑' b3, ∑' b4, ∑' t, massSlot0 π 0 1 b1 b2 b3 b4 t := shapeTotal_patSlot0_eq_tsum π 0 1
    _ ≤ ∑' b1, ∑' b2, ∑' b3, ∑' b4, ∑' t, slotOne π 0 b1 b2 b3 b4 t := hb
    _ = ∑' i₁, ∑' i₂, ∑' b1, ∑' t', ∑' b2, ∑' b3, ∑' b4,
          slotProd2 π 1 i₁ i₂ 0 b1 b2 b3 b4 t' := hperm
    _ = monomial2 π 0 := RootSocket.slotU2_one_tsum π hq 0
    _ = shapeCost π 0 := rfl

/-- **`j = 1`, root socket `b₂`.** -/
theorem shapeTotal_patSlot2_one_le [Countable V] [AddCommGroup V] (π : Sym2 V → unitInterval)
    (hq : ∀ x y g : V, π s(x + g, y + g) = π s(x, y)) :
    shapeTotal π 0 patSlot2 1 ≤ shapeCost π 0 := by
  have hb : (∑' b0, ∑' b1, ∑' b3, ∑' b4, ∑' t, massSlot2 π 0 1 b0 b1 b3 b4 t)
      ≤ ∑' b0, ∑' b1, ∑' b3, ∑' b4, ∑' t, slotOne π b0 b1 0 b3 b4 t := by
    refine ENNReal.tsum_le_tsum fun b0 =>
      ENNReal.tsum_le_tsum fun b1 =>
      ENNReal.tsum_le_tsum fun b3 =>
      ENNReal.tsum_le_tsum fun b4 =>
      ENNReal.tsum_le_tsum fun t =>
        (show _ ≤ _ from combSystem_one_union_le (V := V) π b0 b1 0 b3 b4 t)
  have hperm : (∑' b0, ∑' b1, ∑' b3, ∑' b4, ∑' t, slotOne π b0 b1 0 b3 b4 t)
      = ∑' i₁, ∑' b0, ∑' i₂, ∑' t', ∑' b1, ∑' b3, ∑' b4,
          slotProd2 π 1 i₁ i₂ b0 b1 0 b3 b4 t' := by
    simp only [slotOne, prodOne_eq_slotProd2]
    exact (tsum_seven_perm permOne2 (H := fun a0 a1 a2 a3 a4 a5 a6 => slotProd2 π 1 a6 a5 a0 a1 0 a2 a3 a4)).symm
  calc shapeTotal π 0 patSlot2 1
      = ∑' b0, ∑' b1, ∑' b3, ∑' b4, ∑' t, massSlot2 π 0 1 b0 b1 b3 b4 t := shapeTotal_patSlot2_eq_tsum π 0 1
    _ ≤ ∑' b0, ∑' b1, ∑' b3, ∑' b4, ∑' t, slotOne π b0 b1 0 b3 b4 t := hb
    _ = ∑' i₁, ∑' b0, ∑' i₂, ∑' t', ∑' b1, ∑' b3, ∑' b4,
          slotProd2 π 1 i₁ i₂ b0 b1 0 b3 b4 t' := hperm
    _ = monomial2 π 0 := RootSocket.slotV2_one_tsum π hq 0
    _ = shapeCost π 0 := rfl

/-- **`j = 5`, root socket `b₀`.** -/
theorem shapeTotal_patSlot0_five_le [Countable V] [AddCommGroup V] (π : Sym2 V → unitInterval)
    (hq : ∀ x y g : V, π s(x + g, y + g) = π s(x, y)) :
    shapeTotal π 0 patSlot0 5 ≤ shapeCost π 0 := by
  have hb : (∑' b1, ∑' b2, ∑' b3, ∑' b4, ∑' t, massSlot0 π 0 5 b1 b2 b3 b4 t)
      ≤ ∑' b1, ∑' b2, ∑' b3, ∑' b4, ∑' t, slotFive π 0 b1 b2 b3 b4 t := by
    refine ENNReal.tsum_le_tsum fun b1 =>
      ENNReal.tsum_le_tsum fun b2 =>
      ENNReal.tsum_le_tsum fun b3 =>
      ENNReal.tsum_le_tsum fun b4 =>
      ENNReal.tsum_le_tsum fun t =>
        (show _ ≤ _ from combSystem_five_union_le (V := V) π 0 b1 b2 b3 b4 t)
  have hperm : (∑' b1, ∑' b2, ∑' b3, ∑' b4, ∑' t, slotFive π 0 b1 b2 b3 b4 t)
      = ∑' i₁, ∑' b1, ∑' t', ∑' i₂, ∑' b2, ∑' b4, ∑' b3,
          slotProd2 π 5 i₁ i₂ 0 b1 b2 b3 b4 t' := by
    simp only [slotFive, prodFive_eq_slotProd2]
    exact (tsum_seven_perm permFive0 (H := fun a0 a1 a2 a3 a4 a5 a6 => slotProd2 π 5 a5 a6 0 a0 a1 a2 a3 a4)).symm
  calc shapeTotal π 0 patSlot0 5
      = ∑' b1, ∑' b2, ∑' b3, ∑' b4, ∑' t, massSlot0 π 0 5 b1 b2 b3 b4 t := shapeTotal_patSlot0_eq_tsum π 0 5
    _ ≤ ∑' b1, ∑' b2, ∑' b3, ∑' b4, ∑' t, slotFive π 0 b1 b2 b3 b4 t := hb
    _ = ∑' i₁, ∑' b1, ∑' t', ∑' i₂, ∑' b2, ∑' b4, ∑' b3,
          slotProd2 π 5 i₁ i₂ 0 b1 b2 b3 b4 t' := hperm
    _ = monomial2 π 0 := RootSocket.slotU2_five_tsum π hq 0
    _ = shapeCost π 0 := rfl

/-- **`j = 5`, root socket `b₂`.** -/
theorem shapeTotal_patSlot2_five_le [Countable V] [AddCommGroup V] (π : Sym2 V → unitInterval)
    (hq : ∀ x y g : V, π s(x + g, y + g) = π s(x, y)) :
    shapeTotal π 0 patSlot2 5 ≤ shapeCost π 0 := by
  have hb : (∑' b0, ∑' b1, ∑' b3, ∑' b4, ∑' t, massSlot2 π 0 5 b0 b1 b3 b4 t)
      ≤ ∑' b0, ∑' b1, ∑' b3, ∑' b4, ∑' t, slotFive π b0 b1 0 b3 b4 t := by
    refine ENNReal.tsum_le_tsum fun b0 =>
      ENNReal.tsum_le_tsum fun b1 =>
      ENNReal.tsum_le_tsum fun b3 =>
      ENNReal.tsum_le_tsum fun b4 =>
      ENNReal.tsum_le_tsum fun t =>
        (show _ ≤ _ from combSystem_five_union_le (V := V) π b0 b1 0 b3 b4 t)
  have hperm : (∑' b0, ∑' b1, ∑' b3, ∑' b4, ∑' t, slotFive π b0 b1 0 b3 b4 t)
      = ∑' i₂, ∑' i₁, ∑' t', ∑' b0, ∑' b1, ∑' b4, ∑' b3,
          slotProd2 π 5 i₁ i₂ b0 b1 0 b3 b4 t' := by
    simp only [slotFive, prodFive_eq_slotProd2]
    exact (tsum_seven_perm permFive2 (H := fun a0 a1 a2 a3 a4 a5 a6 => slotProd2 π 5 a5 a6 a0 a1 0 a2 a3 a4)).symm
  calc shapeTotal π 0 patSlot2 5
      = ∑' b0, ∑' b1, ∑' b3, ∑' b4, ∑' t, massSlot2 π 0 5 b0 b1 b3 b4 t := shapeTotal_patSlot2_eq_tsum π 0 5
    _ ≤ ∑' b0, ∑' b1, ∑' b3, ∑' b4, ∑' t, slotFive π b0 b1 0 b3 b4 t := hb
    _ = ∑' i₂, ∑' i₁, ∑' t', ∑' b0, ∑' b1, ∑' b4, ∑' b3,
          slotProd2 π 5 i₁ i₂ b0 b1 0 b3 b4 t' := hperm
    _ = monomial2 π 0 := RootSocket.slotV2_five_tsum π hq 0
    _ = shapeCost π 0 := rfl

/-- **`j = 6`, root socket `b₀`.** -/
theorem shapeTotal_patSlot0_six_le [Countable V] [AddCommGroup V] (π : Sym2 V → unitInterval)
    (hq : ∀ x y g : V, π s(x + g, y + g) = π s(x, y)) :
    shapeTotal π 0 patSlot0 6 ≤ shapeCost π 0 := by
  have hb : (∑' b1, ∑' b2, ∑' b3, ∑' b4, ∑' t, massSlot0 π 0 6 b1 b2 b3 b4 t)
      ≤ ∑' b1, ∑' b2, ∑' b3, ∑' b4, ∑' t, slotSix π 0 b1 b2 b3 b4 t := by
    refine ENNReal.tsum_le_tsum fun b1 =>
      ENNReal.tsum_le_tsum fun b2 =>
      ENNReal.tsum_le_tsum fun b3 =>
      ENNReal.tsum_le_tsum fun b4 =>
      ENNReal.tsum_le_tsum fun t =>
        (show _ ≤ _ from combSystem_six_union_le (V := V) π 0 b1 b2 b3 b4 t)
  have hperm : (∑' b1, ∑' b2, ∑' b3, ∑' b4, ∑' t, slotSix π 0 b1 b2 b3 b4 t)
      = ∑' i₁, ∑' b1, ∑' b2, ∑' i₂, ∑' t', ∑' b4, ∑' b3,
          slotProd2 π 6 i₁ i₂ 0 b1 b2 b3 b4 t' := by
    simp only [slotSix, prodSix_eq_slotProd2]
    exact (tsum_seven_perm permSix0 (H := fun a0 a1 a2 a3 a4 a5 a6 => slotProd2 π 6 a5 a6 0 a0 a1 a2 a3 a4)).symm
  calc shapeTotal π 0 patSlot0 6
      = ∑' b1, ∑' b2, ∑' b3, ∑' b4, ∑' t, massSlot0 π 0 6 b1 b2 b3 b4 t := shapeTotal_patSlot0_eq_tsum π 0 6
    _ ≤ ∑' b1, ∑' b2, ∑' b3, ∑' b4, ∑' t, slotSix π 0 b1 b2 b3 b4 t := hb
    _ = ∑' i₁, ∑' b1, ∑' b2, ∑' i₂, ∑' t', ∑' b4, ∑' b3,
          slotProd2 π 6 i₁ i₂ 0 b1 b2 b3 b4 t' := hperm
    _ = monomial2 π 0 := RootSocket.slotU2_six_tsum π hq 0
    _ = shapeCost π 0 := rfl

/-- **`j = 6`, root socket `b₂`.** -/
theorem shapeTotal_patSlot2_six_le [Countable V] [AddCommGroup V] (π : Sym2 V → unitInterval)
    (hq : ∀ x y g : V, π s(x + g, y + g) = π s(x, y)) :
    shapeTotal π 0 patSlot2 6 ≤ shapeCost π 0 := by
  have hb : (∑' b0, ∑' b1, ∑' b3, ∑' b4, ∑' t, massSlot2 π 0 6 b0 b1 b3 b4 t)
      ≤ ∑' b0, ∑' b1, ∑' b3, ∑' b4, ∑' t, slotSix π b0 b1 0 b3 b4 t := by
    refine ENNReal.tsum_le_tsum fun b0 =>
      ENNReal.tsum_le_tsum fun b1 =>
      ENNReal.tsum_le_tsum fun b3 =>
      ENNReal.tsum_le_tsum fun b4 =>
      ENNReal.tsum_le_tsum fun t =>
        (show _ ≤ _ from combSystem_six_union_le (V := V) π b0 b1 0 b3 b4 t)
  have hperm : (∑' b0, ∑' b1, ∑' b3, ∑' b4, ∑' t, slotSix π b0 b1 0 b3 b4 t)
      = ∑' i₁, ∑' b0, ∑' b1, ∑' i₂, ∑' t', ∑' b4, ∑' b3,
          slotProd2 π 6 i₁ i₂ b0 b1 0 b3 b4 t' := by
    simp only [slotSix, prodSix_eq_slotProd2]
    exact (tsum_seven_perm permSix2 (H := fun a0 a1 a2 a3 a4 a5 a6 => slotProd2 π 6 a5 a6 a0 a1 0 a2 a3 a4)).symm
  calc shapeTotal π 0 patSlot2 6
      = ∑' b0, ∑' b1, ∑' b3, ∑' b4, ∑' t, massSlot2 π 0 6 b0 b1 b3 b4 t := shapeTotal_patSlot2_eq_tsum π 0 6
    _ ≤ ∑' b0, ∑' b1, ∑' b3, ∑' b4, ∑' t, slotSix π b0 b1 0 b3 b4 t := hb
    _ = ∑' i₁, ∑' b0, ∑' b1, ∑' i₂, ∑' t', ∑' b4, ∑' b3,
          slotProd2 π 6 i₁ i₂ b0 b1 0 b3 b4 t' := hperm
    _ = monomial2 π 0 := RootSocket.slotV2_six_tsum π hq 0
    _ = shapeCost π 0 := rfl

/-! ## The eight bounds, collected, and exactly what is left of `I.4.16` at `p = 5`, `k = 2` -/

/-- **Both canonical root-socket masses at the splits `0, 1, 5, 6`.** -/
theorem shapeTotal_rootSlot_le_0156 [Countable V] [AddCommGroup V]
    (π : Sym2 V → unitInterval)
    (hq : ∀ x y g : V, π s(x + g, y + g) = π s(x, y)) {j : Fin 7}
    (hj : j = 0 ∨ j = 1 ∨ j = 5 ∨ j = 6) :
    shapeTotal π 0 patSlot0 j ≤ shapeCost π 0 ∧
      shapeTotal π 0 patSlot2 j ≤ shapeCost π 0 := by
  rcases hj with rfl | rfl | rfl | rfl
  · exact ⟨shapeTotal_patSlot0_zero_le π hq, shapeTotal_patSlot2_zero_le π hq⟩
  · exact ⟨shapeTotal_patSlot0_one_le π hq, shapeTotal_patSlot2_one_le π hq⟩
  · exact ⟨shapeTotal_patSlot0_five_le π hq, shapeTotal_patSlot2_five_le π hq⟩
  · exact ⟨shapeTotal_patSlot0_six_le π hq, shapeTotal_patSlot2_six_le π hq⟩

/-- **The `p = 5`, `k = 2` fifth-moment bound from only the two root sockets at `j = 3` and
`j = 4`.**

Everything else is discharged:

* the middle split `j = 2` by production's `K2Mass.shapeTotal_mid_le` (no hypothesis);
* the splits `j = 0, 1, 5, 6` at both root sockets by the eight bounds of this file;
* the passage from the `15 × 7` shape masses to the two root classes by
  `K2Mass.fifth_moment_k2_le_of_rootSlot_bounds`.

So `Lemma I.4.16` at `p = 5`, `k = 2` is reduced to exactly four inequalities, the shape masses of
the two canonical root sockets at the split positions `3` and `4`.  Each of those requires only the
event-level union bound at its split position, of the kind proved here for `j = 0, 1, 5, 6` and by
`SplitPattern.combSystem_twoJointThree_three` / `..._four` at `j = 3, 4`; the sevenfold reindexing
and the socket evaluation are `permThree0`/`permThree2`/`permFour0`/`permFour2` away from
`RootSocket.slotU2_three_tsum` / `slotV2_three_tsum` / `slotU2_four_tsum` / `slotV2_four_tsum`. -/
theorem fifth_moment_k2_le_of_rootSlot_three_four [Countable V] [AddCommGroup V]
    (π : Sym2 V → unitInterval)
    (hq : ∀ x y g : V, π s(x + g, y + g) = π s(x, y))
    (h0₃ : shapeTotal π 0 patSlot0 3 ≤ shapeCost π 0)
    (h2₃ : shapeTotal π 0 patSlot2 3 ≤ shapeCost π 0)
    (h0₄ : shapeTotal π 0 patSlot0 4 ≤ shapeCost π 0)
    (h2₄ : shapeTotal π 0 patSlot2 4 ≤ shapeCost π 0) :
    ∫⁻ ω, (PercLib.CriticalLRP.Percolation.cardFun
        (PercLib.CriticalLRP.cluster ω (0 : V))) ^ 5 ∂(law π) ≤
      105 * (∫⁻ ω, (PercLib.CriticalLRP.Percolation.cardFun
          (PercLib.CriticalLRP.cluster ω (0 : V))) ^ 2 ∂(law π)) ^ 2 *
        (∫⁻ ω, PercLib.CriticalLRP.Percolation.cardFun
          (PercLib.CriticalLRP.cluster ω (0 : V)) ∂(law π)) ^ 3 := by
  refine fifth_moment_k2_le_of_rootSlot_bounds π hq (fun j hj => ?_) (fun j hj => ?_)
  · fin_cases j
    · exact shapeTotal_patSlot0_zero_le π hq
    · exact shapeTotal_patSlot0_one_le π hq
    · exact absurd rfl hj
    · exact h0₃
    · exact h0₄
    · exact shapeTotal_patSlot0_five_le π hq
    · exact shapeTotal_patSlot0_six_le π hq
  · fin_cases j
    · exact shapeTotal_patSlot2_zero_le π hq
    · exact shapeTotal_patSlot2_one_le π hq
    · exact absurd rfl hj
    · exact h2₃
    · exact h2₄
    · exact shapeTotal_patSlot2_five_le π hq
    · exact shapeTotal_patSlot2_six_le π hq

end PercLib.CriticalLRP.SixPoint.SplitEval3
