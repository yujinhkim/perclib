/-
Windowed `ℓ = 3` inputs for the Case-3 numerator of Proposition I.4.15.

Accepted and independently rebuilt from Ultramath `smwzf17v9`, member `m6`, direction `d6`.

Hutchcroft, *Critical long-range percolation I* (arXiv:2508.18807v1).  In Case 3 of the
proof of Proposition I.4.15 (p. 47) the numerator `E_{β_c,r}[|K|³|K ∩ B_r|]` is bounded
vertex by vertex with Lemma I.4.17 at `p = 3`, `q = 0` and then summed over the window
`B_r`.  The `ℓ = 3` summand of that lemma is controlled in the printed argument by
Lemma I.4.18 at `ℓ = 3`,

  `sup_x T³_{β_c,r}(0,x) = T³_{β_c,r}(0,0) ≤ C (∇_{r^c} + r^{-c}) (E_{β_c,r}|K|)^0`,

a per-vertex bound which is *false* at the base: `T(0,0) = 1` gives `T³(0,0) ≥ 1`
(`I418C.one_le_polyK_three`) while `∇_{r^c} + r^{-c} → 0`.  Consequently the per-vertex
hypothesis `hT3` of `SecondMomentCase3.connCubeMass_le_of_windowGap` is not an available
input (see `NoGo.lean`), and the consumer must be restated in terms of the *windowed* sum
`∑_{y ∈ B_r} T³_{β_c,r}(0,y)`, which is what the definition below introduces.  The
windowed sum is what the window summation over `y` actually needs; `Windowed.lean` proves
it from the honest constant bound `sup_x T³ ≤ ∇` of Lemma I.4.18 at `ℓ = 3` together with
the source's own triangle tail `∇_{r^c}`.

Nothing here asserts an analytic estimate: this is a definition layer plus the elementary
implication "per-vertex ⟹ windowed", which exhibits the windowed hypothesis as weaker than
the per-vertex one.
-/
module

public import PercLib.CriticalLRP.Analysis.SecondMomentCase3.Case3

/-! # Windowed `ℓ = 3` inputs for the Case-3 numerator -/

set_option linter.style.longLine false

@[expose] public section

noncomputable section

open Filter Topology
open scoped ENNReal NNReal BigOperators

namespace PercLib.CriticalLRP
namespace Orchestration
namespace SourceModelData

variable (M : SourceModelData)

/-- **The windowed `ℓ = 3` polygon sum.**  This is the `ℓ = 3` part of the Case-3 numerator
summation, `∑_{y ∈ B_r} T³_{β_c,r}(0,y)`, with `T_{β_c,r}` the two-point matrix of the
range-truncated law (`M.cutTwoPoint r`) and `B_r` the window as the finite set
`E1Sign.ballF M r` used by the assembled consumer. -/
noncomputable def windowPolyKThree (r : ℝ) : ℝ :=
  ∑ y ∈ E1Sign.ballF M r, I418C.polyK (M.cutTwoPoint r) 3 (0 : M.V) y

/-- **The per-vertex `ℓ = 3` input `hT3`.**  Uniform in the window vertex `y` and in the
radius, with the Case-3 driver `∇_{r^c} + r^{-c}`.  This is the shape in which
`SecondMomentCase3.connCubeMass_le_of_windowGap` consumes the `ℓ = 3` term; `NoGo.lean`
shows it is unsatisfiable whenever the driver vanishes. -/
def PerVertexEllThreeGap (c Cp : ℝ) : Prop :=
  ∀ r : ℝ, 1 ≤ r → ∀ y : M.V,
    I418C.polyK (M.cutTwoPoint r) 3 (0 : M.V) y ≤ Cp * M.case3Driver c r

/-- **The windowed `ℓ = 3` input.**  Only the *sum* of the `ℓ = 3` polygon entries over the
window is controlled, by the driver times the volume of the window.  This is exactly the
form in which the window summation of the Case-3 numerator uses the `ℓ = 3` term: it
produces the `|B_r|` that cancels the `|B_r|` of the denominator of (I.4.16). -/
def WindowedEllThreeGap (c Cp : ℝ) : Prop :=
  ∀ r : ℝ, 1 ≤ r →
    M.windowPolyKThree r ≤ Cp * ((M.ball r).ncard : ℝ) * M.case3Driver c r

/-- **The Case-3 bundle with the windowed `ℓ = 3` conjunct.** -/
def Case3PolygonBundleWindowed (c Cp : ℝ) : Prop :=
  Tendsto (M.case3Driver c) atTop (𝓝 0) ∧
  Analysis.LogarithmicallyIntegrable (M.case3Driver c) ∧
  M.WindowedEllThreeGap c Cp ∧
  (∀ r : ℝ, 1 ≤ r → ∀ x : M.V,
    I418C.polyK (M.cutTwoPoint r) 4 (0 : M.V) x
      ≤ Cp * M.case3Driver c r * (M.cutMassAt r 0).toReal)


/-- The `ℓ = 3` entries are nonnegative. -/
theorem polyK_three_cutTwoPoint_nonneg (r : ℝ) (y : M.V) :
    0 ≤ I418C.polyK (M.cutTwoPoint r) 3 (0 : M.V) y :=
  I418C.polyK_nonneg _ (fun a b => M.cutTwoPoint_nonneg r a b) _ _ _

/-- The windowed `ℓ = 3` sum is nonnegative. -/
theorem windowPolyKThree_nonneg (r : ℝ) : 0 ≤ M.windowPolyKThree r :=
  Finset.sum_nonneg fun y _ => M.polyK_three_cutTwoPoint_nonneg r y

/-- **The per-vertex input implies the windowed one.**  So the windowed hypothesis is the
weaker of the two; combined with `NoGo.lean` (the per-vertex one is false) this is the
statement that the consumer must be restated in the windowed form, and not something
stronger than what the paper's argument can ever supply. -/
theorem windowedEllThreeGap_of_perVertex {c Cp : ℝ}
    (h : M.PerVertexEllThreeGap c Cp) : M.WindowedEllThreeGap c Cp := by
  intro r hr
  calc M.windowPolyKThree r
      = ∑ y ∈ E1Sign.ballF M r, I418C.polyK (M.cutTwoPoint r) 3 (0 : M.V) y := rfl
    _ ≤ ∑ _y ∈ E1Sign.ballF M r, Cp * M.case3Driver c r :=
        Finset.sum_le_sum fun y _ => h r hr y
    _ = ((E1Sign.ballF M r).card : ℝ) * (Cp * M.case3Driver c r) := by
        rw [Finset.sum_const, nsmul_eq_mul]
    _ = Cp * ((M.ball r).ncard : ℝ) * M.case3Driver c r := by
        rw [E1Sign.card_ballF M r]
        ring

end SourceModelData
end Orchestration
end PercLib.CriticalLRP
