/- Integrated from independently rebuilt Ultramath work, base revision 4140ac56119d2cd80995f91886669efe004839d5.
Scratch source: ../../.ultramath/smwqozn0q/m3/Source.lean ; cutoff definitions deduplicated.
-/
module

/-
Direction C (member m3, swarm smwqozn0q): the model-level instantiation of the assembly layer.

This file names the source objects of Lemma I.4.18 that production does not yet provide
(the *cutoff* two-point function `T_{β_c,r}`, and the real-valued open triangle `∇_{β_c}(0,·)`),
proves the model-level facts that the assembly needs (diagonal = 1, nonnegativity, translation
invariance of the configured kernel, and `∇(0,y) ≤ ∇_{β_c}` under the triangle condition), and
then instantiates `polygon_bound_sup` on `SourceModelData`.

Nothing here touches production files.
-/
public import PercLib.CriticalLRP.Analysis.Polygon.Core
public import PercLib.CriticalLRP.Orchestration.Defs
public import PercLib.CriticalLRP.Analysis.TriTail

set_option autoImplicit false
set_option linter.unusedSectionVars false

open MeasureTheory Measure
open scoped ENNReal NNReal BigOperators

@[expose] public section

namespace PercLib.CriticalLRP.Orchestration.SourceModelData

open PercLib.CriticalLRP.Orchestration
open PercLib.CriticalLRP.I418C

variable (M : SourceModelData)

/-- A direct conversion to the long-range `twoPointFunction`. -/
theorem cutTwoPoint_eq_toReal (r : ℝ) (x y : M.V) :
    M.cutTwoPoint r x y
      = (twoPointFunction (M.cutKernel r) (M.cutKernel_nonneg r) M.betaCrit x y).toReal := rfl

theorem triPoint_nonneg (x y : M.V) : 0 ≤ M.triPoint x y := ENNReal.toReal_nonneg

theorem cutTriPoint_def (r : ℝ) (y : M.V) :
    M.cutTriPoint r y = polyK (M.cutTwoPoint r) 3 0 y := rfl

theorem cutTriPoint_nonneg (r : ℝ) (y : M.V) : 0 ≤ M.cutTriPoint r y :=
  polyK_nonneg _ (fun _ _ => M.cutTwoPoint_nonneg r _ _) 3 0 y

/-- **Translation invariance of the configured kernel**: `radialSym` only depends on `x - y`. -/
theorem kernel_shift (a : M.V) (e : Sym2 M.V) :
    M.kernel (Sym2.map (fun x => x + a) e) = M.kernel e := by
  induction e using Sym2.ind with
  | _ x y =>
    rw [SourceModelData.kernel, Sym2.map_mk, radialSym_mk, radialSym_mk]
    by_cases h : x = y
    · subst h
      rw [ite_eq_left rfl, ite_eq_left rfl]
    · have h' : x + a ≠ y + a := fun hh => h (add_right_cancel hh)
      rw [ite_eq_right h', ite_eq_right h]
      congr 1
      rw [SourceNormData.dist, SourceNormData.dist,
        show (x + a) - (y + a) = x - y from by
          funext i; simp only [Pi.sub_apply, Pi.add_apply]; ring]

/-- **`∇(0,y) ≤ ∇_{β_c}`**: the triangle diagram bounds the open triangle, under the triangle
condition `∇_{β_c} < ∞` (which is what makes the conversion to `ℝ` faithful). -/
theorem triPoint_le_self (hTri : PercLib.CriticalLRP.TriTail.openTriangleSelf M.kernel
    M.kernel_nonneg M.betaCrit 0 < ⊤) (y : M.V) : M.triPoint 0 y ≤ M.triSelf := by
  have h := PercLib.CriticalLRP.TriTail.openTriangle_le_diagonal M.kernel_shift
    M.kernel_nonneg M.betaCrit y
  exact ENNReal.toReal_mono hTri.ne h

/-- **Cutoff triple dominated by the triangle diagram.**  If the cutoff threefold power is
pointwise below the uncut open triangle (the monotone-convergence step
`T_{β_c,r} ≤ T_{β_c} ⟹ T^3_{β_c,r} ≤ T^3_{β_c}` in `ℝ≥0∞`), then it is below the triangle
constant `∇_{β_c}`, which is the `triSup` field of `PowerInputs`. -/
theorem cutTriPoint_le_triSelf (r : ℝ)
    (hTri : PercLib.CriticalLRP.TriTail.openTriangleSelf M.kernel M.kernel_nonneg M.betaCrit 0 < ⊤)
    (hκ : ∀ y : M.V, M.cutTriPoint r y ≤ M.triPoint 0 y) (y : M.V) :
    M.cutTriPoint r y ≤ M.triSelf :=
  (hκ y).trans (M.triPoint_le_self hTri y)

/-- `S.dist 0 y = ρ y` is the source norm of `y`, so the ball `M.ball R` is `{‖y‖ ≤ R}`. -/
theorem dist_zero_eq (y : M.V) : M.S.dist 0 y = M.S.ρ (toVec y) := by
  rw [SourceNormData.dist, show toVec (0 - y) = -toVec y from by
    funext i; simp [toVec]]
  exact M.S.ρ_neg (toVec y)

/-- **`triSup` at the model, derived rather than assumed.**  Combining the proved domination
`T_{β_c,r} ≤ τ_{β_c}` with `polyK_three_mono` and the triangle-condition bound
`∇_{β_c}(0,y) ≤ ∇_{β_c}`, the cutoff threefold power is below the triangle diagram.

Remaining inputs: summability of the two- and three-step convolutions of the *uncut* two-point
function (finiteness under `∇ < ∞`) and the `ℝ/ℝ≥0∞` correspondence `hlink` between the real
threefold convolution and `triPoint`. -/
theorem source_triSup (r : ℝ)
    (hTri : PercLib.CriticalLRP.TriTail.openTriangleSelf M.kernel M.kernel_nonneg M.betaCrit 0 < ⊤)
    (hB2 : ∀ u : M.V, Summable (fun v => M.twoPoint M.betaCrit 0 v * M.twoPoint M.betaCrit v u))
    (hB3 : ∀ y : M.V,
      Summable (fun u => (∑' v, M.twoPoint M.betaCrit 0 v * M.twoPoint M.betaCrit v u)
        * M.twoPoint M.betaCrit u y))
    (hlink : ∀ y : M.V, polyK (M.twoPoint M.betaCrit) 3 0 y ≤ M.triPoint 0 y)
    (y : M.V) : M.cutTriPoint r y ≤ M.triSelf :=
  (polyK_three_mono (fun _ _ => M.cutTwoPoint_nonneg r _ _)
    (fun x y => M.cutTwoPoint_le_twoPoint r x y) hB2 hB3 y).trans
    ((hlink y).trans (M.triPoint_le_self hTri y))

/-- The same chain on the tail: the cutoff threefold power is below `∇_{r^c}` wherever the uncut
open triangle is. -/
theorem source_triTail (r cc trc : ℝ)
    (hB2 : ∀ u : M.V, Summable (fun v => M.twoPoint M.betaCrit 0 v * M.twoPoint M.betaCrit v u))
    (hB3 : ∀ y : M.V,
      Summable (fun u => (∑' v, M.twoPoint M.betaCrit 0 v * M.twoPoint M.betaCrit v u)
        * M.twoPoint M.betaCrit u y))
    (hlink : ∀ y : M.V, polyK (M.twoPoint M.betaCrit) 3 0 y ≤ M.triPoint 0 y)
    (htailc : ∀ y : M.V, r ^ cc ≤ M.S.dist 0 y → M.triPoint 0 y ≤ trc)
    (y : M.V) (hy : r ^ cc ≤ M.S.dist 0 y) : M.cutTriPoint r y ≤ trc :=
  (polyK_three_mono (fun _ _ => M.cutTwoPoint_nonneg r _ _)
    (fun x y => M.cutTwoPoint_le_twoPoint r x y) hB2 hB3 y).trans ((hlink y).trans (htailc y hy))

end PercLib.CriticalLRP.Orchestration.SourceModelData

namespace PercLib.CriticalLRP.I418C

open PercLib.CriticalLRP.Orchestration

/-- **Composition at the model, with the cutoff triple.**  This is the paper's
`T^ℓ(0,0) = ∑_y T^3(0,y) T^{ℓ-3}(y,0)` at the cutoff two-point function: no uncut object occurs
on either side. -/
theorem source_comp (M : SourceModelData) (r χ : ℝ)
    (H : PowerInputs (polyK (M.cutTwoPoint r)) M.triSelf χ) (n : ℕ) :
    polyK (M.cutTwoPoint r) (n + 3) 0 0
      = ∑' y, M.cutTriPoint r y * polyK (M.cutTwoPoint r) n y 0 :=
  H.comp n

/-- **Lemma I.4.18, source-model assembly (`ℓ ≥ 4`), with the cutoff/uncut comparison derived.**

This is the paper's proof at the actual model objects:

* `P = polyK (M.cutTwoPoint r)` — the matrix powers of the *cutoff* two-point function
  `T_{β_c,r}`; direction B supplies `H`, whose `comp` field is the composition identity
  `P (n+3) 0 0 = ∑_y cutTriPoint r y * P n y 0` (`source_comp`);
* `κ = M.cutTriPoint r = P 3 0 ·` — the cutoff threefold power;
* the *uncut* triangle objects `M.triPoint M 0` and `M.triSelf = ∇_{β_c}` enter only through
  `hlink` (real threefold convolution of `τ_{β_c}` ≤ `∇_{β_c}(0,·)`) and `htailc` (the uncut tail
  `∇_{r^c}`); the `triSup` field of `H` is derived from them by `source_triSup` using the proved
  domination `cutTwoPoint_le_twoPoint` and the generic `polyK_three_mono`;
* `χ = E_{β_c,r}|K|`, `s` a finite set containing the open `R`-ball, `|B_R| ≤ K R^d` the
  normalized ball count, `c₀ r^α ≤ χ` the first-moment comparison.

Conclusion, uniformly in `ℓ ≥ 4` and `r ≥ 1`:
`sup_x T^ℓ_{β_c,r}(0,x) ≤ max 1 (∇_{β_c} K/c₀) (∇_{r^c} + r^{-c}) (E_{β_c,r}|K|)^{ℓ-3}`
with `c = α/(4d)`.  (`ℓ = 3` is the separate constant bound `T^3(0,0) ≤ ∇_{β_c}`,
`PowerInputs.ell_three_le`.) -/
theorem source_polygon_bound
    (M : SourceModelData)
    (r R trc χ : ℝ) (s : Finset M.V) {c₀ K cc : ℝ}
    (hr : 1 ≤ r) (hc₀ : 0 < c₀) (hK : 0 ≤ K)
    (hB2 : ∀ u : M.V, Summable (fun v => M.twoPoint M.betaCrit 0 v * M.twoPoint M.betaCrit v u))
    (hB3 : ∀ y : M.V,
      Summable (fun u => (∑' v, M.twoPoint M.betaCrit 0 v * M.twoPoint M.betaCrit v u)
        * M.twoPoint M.betaCrit u y))
    (hlink : ∀ y : M.V, polyK (M.twoPoint M.betaCrit) 3 0 y ≤ M.triPoint 0 y)
    (H : PowerInputs (polyK (M.cutTwoPoint r)) M.triSelf χ)
    {ell : ℕ} (hell : 4 ≤ ell)
    (hct : cc = M.α / (4 * (M.d : ℝ)))
    (hfar : ∀ y : M.V, y ∉ s → R ≤ M.S.dist 0 y)
    (htailc : ∀ y : M.V, r ^ cc ≤ M.S.dist 0 y → M.triPoint 0 y ≤ trc)
    (htrc : 0 ≤ trc)
    (hcard : (s.card : ℝ) ≤ K * R ^ (M.d : ℝ))
    (hR : R = r ^ (M.α / (2 * (M.d : ℝ))))
    (hχ : c₀ * r ^ M.α ≤ χ)
    (hdiag : ∀ x : M.V, polyK (M.cutTwoPoint r) ell 0 x ≤ polyK (M.cutTwoPoint r) ell 0 0) :
    ∀ x : M.V, polyK (M.cutTwoPoint r) ell 0 x
      ≤ max 1 (M.triSelf * K / c₀) * (trc + r ^ (-cc)) * χ ^ (ell - 3) := by
  have htail : ∀ y : M.V, r ^ cc ≤ M.S.dist 0 y → polyK (M.cutTwoPoint r) 3 0 y ≤ trc :=
    fun y hy => M.source_triTail r cc trc hB2 hB3 hlink htailc y hy
  exact polygon_bound_sup H s (fun y => M.S.dist 0 y) r R trc M.hα M.hd hc₀ hK hr hell hct
    hfar htail htrc hcard hR hχ hdiag

end PercLib.CriticalLRP.I418C
