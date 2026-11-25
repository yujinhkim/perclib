/-
Scratch deliverable of swarm `smwu2am6k`, member `m1`, direction `d1`.

# The `polyK`/`triPoint` link (`hlink`) from the literal identification

`Analysis/Polygon/Model.lean`'s `source_polygon_bound`
(Lemma I.4.18 at the configured model) carries
the hypothesis

  `hlink : ∀ y, polyK (M.twoPoint M.betaCrit) 3 0 y ≤ M.triPoint 0 y`

— the real threefold convolution of `τ_{β_c}` is pointwise below the open triangle `∇_{β_c}(0,·)`,
which that file states as an explicit remaining input.

This file *derives* it (in fact, an equality, under the Case 2 finiteness) from the literal
identification proved in `Main.lean`.  The real sum
`polyK T 3 0 y = ∑' u, (∑' v, T 0 v * T v u) * T u y` (`I418C.polyK_three`) is *syntactically* the
abstract iterated convolution of `litT` once translation invariance rewrites `T v u = τ(0,u-v)` and
`T u y = τ(0,y-u)`; the abstract assembly supplies the summability, and
`openTriangle_eq_ofReal_tsum` identifies that convolution with `∇_{β_c}(0,y)`.

No new definition; nothing is assumed beyond (HD)(2).
-/
module

public import PercLib.CriticalLRP.Analysis.OpenTriangle.Case2Literal.Model
public import PercLib.CriticalLRP.Analysis.Polygon.Core
public import PercLib.CriticalLRP.Analysis.TriangleAverage.Defs

/-! # Literal Case 2: Link

Definitional links from Case 2 convolution to polyK and TriangleAverage.nabla.
-/

set_option autoImplicit false


set_option linter.hashCommand false

@[expose] public section

open scoped ENNReal

namespace PercLib.CriticalLRP.Orchestration.SourceModelData

open PercLib.CriticalLRP Orchestration I418C

/-- `τ(a,b) = τ(0,b-a)` at the model, in the real-valued presentation `M.twoPoint`. -/
theorem twoPoint_eq_origin (M : SourceModelData) (a b : M.V) :
    M.twoPoint M.betaCrit a b = M.twoPoint M.betaCrit 0 (b - a) := by
  rw [show M.twoPoint M.betaCrit a b
        = (twoPointFunction M.kernel M.kernel_nonneg M.betaCrit a b).toReal from rfl,
    show M.twoPoint M.betaCrit 0 (b - a)
        = (twoPointFunction M.kernel M.kernel_nonneg M.betaCrit 0 (b - a)).toReal from rfl,
    twoPointFunction_eq_origin M.kernel_shift M.kernel_nonneg M.betaCrit a b]

/-- **`polyK` of `M.twoPoint` *is* the abstract iterated convolution of the literal profile.** -/
theorem polyK_three_eq_tsum (M : SourceModelData) (y : M.V) :
    polyK (M.twoPoint M.betaCrit) 3 0 y
      = ∑' b, (∑' a, HD.litT M.kernel M.kernel_nonneg M.betaCrit a *
            HD.litT M.kernel M.kernel_nonneg M.betaCrit (b - a)) *
          HD.litT M.kernel M.kernel_nonneg M.betaCrit (y - b) := by
  rw [polyK_three]
  refine tsum_congr fun b => ?_
  have hout : M.twoPoint M.betaCrit b y = HD.litT M.kernel M.kernel_nonneg M.betaCrit (y - b) :=
    M.twoPoint_eq_origin b y
  have hin : (∑' a, M.twoPoint M.betaCrit 0 a * M.twoPoint M.betaCrit a b)
      = ∑' a, HD.litT M.kernel M.kernel_nonneg M.betaCrit a *
          HD.litT M.kernel M.kernel_nonneg M.betaCrit (b - a) :=
    tsum_congr fun a => by rw [M.twoPoint_eq_origin a b]; rfl
  rw [hin, hout]

/-- **The `TriangleAverage.nabla` bridge**, definitional.

`docs/CRITICAL_LRP_CASE2_PROFILE.md` lists as still open "identifying that iterated convolution with
the repository's `ENNReal`-valued `TriangleAverage.nabla` (including translation and Fubini steps)".
`TriangleAverage.nabla M y` and `TriTail.openTriangle M.kernel M.kernel_nonneg M.betaCrit 0 y` are
the *same* iterated sum, so this is `rfl`; the content is that the identification theorem
`HD.openTriangle_eq_tsum_ENNReal` applies to `TriangleAverage.nabla` verbatim, and hence so do the
Case 2 bound and the finiteness statement.  This file deliberately proves everything at
`TriTail.openTriangle` and only records the bridge here. -/
theorem nabla_eq_openTriangle (M : SourceModelData) (y : M.V) :
    PercLib.CriticalLRP.TriangleAverage.nabla M y
      = TriTail.openTriangle M.kernel M.kernel_nonneg M.betaCrit 0 y := rfl

/-- The Case 2 pointwise bound at `TriangleAverage.nabla`. -/
theorem nabla_toReal_le_powMajorant_case2 (M : SourceModelData) (hd : 6 < M.d) {C : ℝ}
    (hC : 1 ≤ C)
    (hHD : ∀ x y : M.V, x ≠ y →
      M.twoPoint M.betaCrit x y ≤ C * (M.S.ρ (toVec (x - y))) ^ (-(M.d : ℝ) + 2))
    {y : M.V} (hy : y ≠ 0) :
    (PercLib.CriticalLRP.TriangleAverage.nabla M y).toReal
      ≤ Analysis.powMajorant (HD.srcCase2Const M.d C M.S) ((M.d : ℝ) - 6) (M.S.dist 0 y) := by
  rw [M.nabla_eq_openTriangle]
  exact M.openTriangle_toReal_le_powMajorant_case2 hd hC hHD y hy

/-- **The `polyK`/open-triangle equality** under (HD)(2):

`polyK τ_{β_c}(3,0,y) = ∇_{β_c}(0,y) = M.triPoint 0 y`.

This is `polyK_three_eq_tsum` composed with `openTriangle_eq_ofReal_tsum`; the abstract Case 2
assembly provides the summability that licenses `toReal (ofReal _) = _`. -/
theorem polyK_three_eq_triPoint (M : SourceModelData) (hd : 6 < M.d) {C : ℝ} (hC : 1 ≤ C)
    (hHD : ∀ x y : M.V, x ≠ y →
      M.twoPoint M.betaCrit x y ≤ C * (M.S.ρ (toVec (x - y))) ^ (-(M.d : ℝ) + 2))
    (y : M.V) : polyK (M.twoPoint M.betaCrit) 3 0 y = M.triPoint 0 y := by
  have h2 : 2 < M.d := by omega
  have hC' : (1 : ℝ) ≤ C * (CriticalLRPConv.srcLowerUnit M.S) ^ (-((M.d : ℝ) - 2)) := by
    have h := M.one_le_srcLowerUnit_rpow h2
    nlinarith
  have hid := Orchestration.HD.openTriangle_eq_ofReal_tsum
    (J := M.kernel) (hJ := M.kernel_nonneg) (β := M.betaCrit)
    M.kernel_shift hd hC' (M.HD_to_supNorm hd hC hHD) y
  have hnn : 0 ≤ ∑' b, (∑' a, HD.litT M.kernel M.kernel_nonneg M.betaCrit a *
        HD.litT M.kernel M.kernel_nonneg M.betaCrit (b - a)) *
      HD.litT M.kernel M.kernel_nonneg M.betaCrit (y - b) :=
    tsum_nonneg fun b => mul_nonneg
      (tsum_nonneg fun a => mul_nonneg
        (Orchestration.HD.litT_nonneg _ _ _ a)
        (Orchestration.HD.litT_nonneg _ _ _ (b - a)))
      (Orchestration.HD.litT_nonneg _ _ _ (y - b))
  rw [M.polyK_three_eq_tsum y,
    show M.triPoint 0 y
      = (TriTail.openTriangle M.kernel M.kernel_nonneg M.betaCrit 0 y).toReal from rfl, hid,
    ENNReal.toReal_ofReal hnn]

/-- **The `hlink` hypothesis of `source_polygon_bound`, discharged.**

`Polygon/Model.lean` requires `hlink : ∀ y, polyK (M.twoPoint M.betaCrit) 3 0 y ≤ M.triPoint 0 y`
as an explicit input to `source_triSup` / `source_polygon_bound`.  It follows from (HD)(2) alone
(with `1 ≤ C`; the `0 < C` form is `polyK_three_le_triPoint_of_pos`). -/
theorem polyK_three_le_triPoint (M : SourceModelData) (hd : 6 < M.d) {C : ℝ} (hC : 1 ≤ C)
    (hHD : ∀ x y : M.V, x ≠ y →
      M.twoPoint M.betaCrit x y ≤ C * (M.S.ρ (toVec (x - y))) ^ (-(M.d : ℝ) + 2))
    (y : M.V) : polyK (M.twoPoint M.betaCrit) 3 0 y ≤ M.triPoint 0 y :=
  le_of_eq (M.polyK_three_eq_triPoint hd hC hHD y)

/-- The same with the `0 < C` bookkeeping of `HD M`'s second disjunct. -/
theorem polyK_three_le_triPoint_of_pos (M : SourceModelData) (hd : 6 < M.d) {C : ℝ} (_hC : 0 < C)
    (hHD : ∀ x y : M.V, x ≠ y →
      M.twoPoint M.betaCrit x y ≤ C * (M.S.ρ (toVec (x - y))) ^ (-(M.d : ℝ) + 2))
    (y : M.V) : polyK (M.twoPoint M.betaCrit) 3 0 y ≤ M.triPoint 0 y := by
  refine M.polyK_three_le_triPoint hd (C := max 1 C) (le_max_left _ _) ?_ y
  intro x y' hxy
  refine (hHD x y' hxy).trans (mul_le_mul_of_nonneg_right (le_max_right (1 : ℝ) C) ?_)
  exact Real.rpow_nonneg (CriticalLRPConv.src_nonneg M.S _) _

/-! ## The two uncut convolution summabilities (`hB2`, `hB3`)

`source_triSup` and `source_polygon_bound` in `Polygon/Model.lean` take

`hB2 : ∀ u, Summable (fun v => M.twoPoint M.betaCrit 0 v * M.twoPoint M.betaCrit v u)` and
`hB3 : ∀ y, Summable (fun u => (∑' v, M.twoPoint M.betaCrit 0 v * M.twoPoint M.betaCrit v u) *
M.twoPoint M.betaCrit u y)`

as explicit inputs.  Both are the abstract assembly's own `Summable` outputs after rewriting
`M.twoPoint M.betaCrit a b = τ_{β_c}(0, b-a)`; neither needs a new estimate. -/

/-- `hB2`: summability of the uncut twofold convolution, from (HD)(2). -/
theorem summable_uncut_two (M : SourceModelData) (hd : 6 < M.d) {C : ℝ} (hC : 1 ≤ C)
    (hHD : ∀ x y : M.V, x ≠ y →
      M.twoPoint M.betaCrit x y ≤ C * (M.S.ρ (toVec (x - y))) ^ (-(M.d : ℝ) + 2))
    (u : M.V) :
    Summable (fun v => M.twoPoint M.betaCrit 0 v * M.twoPoint M.betaCrit v u) := by
  have h2 : 2 < M.d := by omega
  have hC' : (1 : ℝ) ≤ C * (CriticalLRPConv.srcLowerUnit M.S) ^ (-((M.d : ℝ) - 2)) := by
    have h := M.one_le_srcLowerUnit_rpow h2
    nlinarith
  have ht : ∀ x : Fin M.d → ℤ, x ≠ 0 →
      HD.litT M.kernel M.kernel_nonneg M.betaCrit x
        ≤ (C * (CriticalLRPConv.srcLowerUnit M.S) ^ (-((M.d : ℝ) - 2))) *
            ‖x‖ ^ (-(M.d : ℝ) + 2) :=
    fun x hx => Orchestration.HD.litT_le_of_HD hC' (M.HD_to_supNorm hd hC hHD) hx
  have h := (Orchestration.HD.convolution_two_case2
    (t := HD.litT M.kernel M.kernel_nonneg M.betaCrit)
    hd hC' (Orchestration.HD.litT_nonneg _ _ _)
    (Orchestration.HD.litT_zero _ _ _) ht u).1
  refine h.congr fun v => ?_
  change HD.litT M.kernel M.kernel_nonneg M.betaCrit v *
      HD.litT M.kernel M.kernel_nonneg M.betaCrit (u - v)
    = M.twoPoint M.betaCrit 0 v * M.twoPoint M.betaCrit v u
  rw [M.twoPoint_eq_origin v u]
  rfl

/-- `hB3`: summability of the uncut threefold convolution, from (HD)(2). -/
theorem summable_uncut_three (M : SourceModelData) (hd : 6 < M.d) {C : ℝ} (hC : 1 ≤ C)
    (hHD : ∀ x y : M.V, x ≠ y →
      M.twoPoint M.betaCrit x y ≤ C * (M.S.ρ (toVec (x - y))) ^ (-(M.d : ℝ) + 2))
    (y : M.V) :
    Summable (fun u => (∑' v, M.twoPoint M.betaCrit 0 v * M.twoPoint M.betaCrit v u) *
      M.twoPoint M.betaCrit u y) := by
  have h2 : 2 < M.d := by omega
  have hC' : (1 : ℝ) ≤ C * (CriticalLRPConv.srcLowerUnit M.S) ^ (-((M.d : ℝ) - 2)) := by
    have h := M.one_le_srcLowerUnit_rpow h2
    nlinarith
  have ht : ∀ x : Fin M.d → ℤ, x ≠ 0 →
      HD.litT M.kernel M.kernel_nonneg M.betaCrit x
        ≤ (C * (CriticalLRPConv.srcLowerUnit M.S) ^ (-((M.d : ℝ) - 2))) *
            ‖x‖ ^ (-(M.d : ℝ) + 2) :=
    fun x hx => Orchestration.HD.litT_le_of_HD hC' (M.HD_to_supNorm hd hC hHD) hx
  have h := (Orchestration.HD.triple_convolution_case2
    (t := HD.litT M.kernel M.kernel_nonneg M.betaCrit)
    hd hC' (Orchestration.HD.litT_nonneg _ _ _)
    (Orchestration.HD.litT_zero _ _ _) ht y).1
  refine h.congr fun u => ?_
  change (∑' a, HD.litT M.kernel M.kernel_nonneg M.betaCrit a *
      HD.litT M.kernel M.kernel_nonneg M.betaCrit (u - a)) *
      HD.litT M.kernel M.kernel_nonneg M.betaCrit (y - u)
    = (∑' v, M.twoPoint M.betaCrit 0 v * M.twoPoint M.betaCrit v u) * M.twoPoint M.betaCrit u y
  rw [M.twoPoint_eq_origin u y]
  congr 1
  refine tsum_congr fun a => ?_
  rw [M.twoPoint_eq_origin a u]
  rfl

end PercLib.CriticalLRP.Orchestration.SourceModelData

open PercLib.CriticalLRP.Orchestration

#print axioms SourceModelData.nabla_eq_openTriangle
#print axioms SourceModelData.nabla_toReal_le_powMajorant_case2
#print axioms SourceModelData.twoPoint_eq_origin
#print axioms SourceModelData.polyK_three_eq_tsum
#print axioms SourceModelData.polyK_three_eq_triPoint
#print axioms SourceModelData.polyK_three_le_triPoint
#print axioms SourceModelData.polyK_three_le_triPoint_of_pos
#print axioms SourceModelData.summable_uncut_two
#print axioms SourceModelData.summable_uncut_three
