/-
Copyright (c) 2026 PercLib contributors. Released under Apache 2.0.

# Per-edge weights of the cut-off pivotal mass

Swarm `smwv576pz`, member `m1`, direction A1 (repair of the `smwv4hzkh` m7 packet).

The cut-off pivotal mass of the first moment is the edge series

  `sMomentWeight 0 A q cutProb cutEdgeDeriv r
     = ∑'_e |cutEdgeDeriv r e| · (2 · max (∑_{x∈A} |q x|) 0 · P_r(e ∈ touchSet · 0))`

(`RussoInf/SpatialDominated.lean`, unfolded by `pivotalWeightOf`).  This file isolates the
per-edge summand `pivotalTerm` together with the algebraic facts that the edge-sum /
radius-integral interchange of `PivotalWeight/Interchange.lean` uses, so that the interchange is
stated about a named object rather than a raw `tsum`.

Nothing here is a claim about finiteness: `pivotalTerm` is a definition, and its lemmas are pure
`ring` / `max` / `Finset` algebra plus measurability in the radius.  In particular this module is
independent of every envelope or moment input.
-/
module

public import PercLib.CriticalLRP.Analysis.Cutoff.OffCorner.RadiusPivotalWeight

/-!
The per-edge weight `pivotalTerm` of the total pivotal mass, and its truncation-bound algebra.
-/

@[expose] public section

set_option autoImplicit false
set_option linter.style.longLine false

noncomputable section

open MeasureTheory

open scoped ENNReal NNReal Topology

namespace PercLib.CriticalLRP.Orchestration

namespace SourceModelData

variable (M : SourceModelData)

/-- **The per-edge weight of the total pivotal mass of the cut-off first moment.**

This is the summand of `sMomentWeight (0 : M.V) A q M.cutProb M.cutEdgeDeriv r`, with the
truncation bound `m = ∑_{x∈A} |q x|` kept as a parameter.  It is nonnegative, and it is
proportional to the `m = 1` weight with the factor `max m 0`. -/
noncomputable def pivotalTerm (m : ℝ) (r : ℝ) (e : Sym2 M.V) : ℝ :=
  |M.cutEdgeDeriv r e| *
    (2 * max m 0 * (M.cutLaw r).real {ω : Config M.V | e ∈ touchSet ω (0 : M.V)})

/-- The per-edge pivotal weight is nonnegative. -/
theorem pivotalTerm_nonneg (m : ℝ) (r : ℝ) (e : Sym2 M.V) :
    0 ≤ M.pivotalTerm m r e :=
  mul_nonneg (abs_nonneg _)
    (mul_nonneg (mul_nonneg (by norm_num) (le_max_right m 0)) measureReal_nonneg)

/-- The weight at truncation bound `1` written without the `max`: this is the shape in which the
landed interior-scale envelope `weightedTouch_le_env` / `m1_summable_env` is stated. -/
theorem pivotalTerm_one_eq (r : ℝ) (e : Sym2 M.V) :
    M.pivotalTerm 1 r e =
      |M.cutEdgeDeriv r e| *
        (2 * (M.cutLaw r).real {ω : Config M.V | e ∈ touchSet ω (0 : M.V)}) := by
  rw [pivotalTerm, max_eq_left (show (0 : ℝ) ≤ 1 by norm_num)]
  ring

/-- The per-edge weight at truncation bound `m` is `max m 0` times the weight at bound `1`.

This is the only place where the truncation bound enters, and it is why integrability of the
total pivotal weight does not have to be reproved for every finite observation `A`. -/
theorem pivotalTerm_eq_smul_one (m : ℝ) (r : ℝ) (e : Sym2 M.V) :
    M.pivotalTerm m r e = max m 0 * M.pivotalTerm 1 r e := by
  unfold pivotalTerm
  rw [max_eq_left (show (0 : ℝ) ≤ 1 by norm_num)]
  ring

/-- **Vertex decomposition of the per-edge weight of a finite observation.**

For a finite vertex set `A` with weights `q`, the per-edge weight of the total moment
`∑_{x∈A} |q x|` splits as the finite sum of the per-vertex weights: the truncation bound
`max (∑_{x∈A} |q x|) 0` is the sum of the per-vertex bounds `max |q x| 0`. -/
theorem pivotalTerm_finset_sum (A : Finset M.V) (q : M.V → ℝ) (r : ℝ) (e : Sym2 M.V) :
    M.pivotalTerm (∑ x ∈ A, |q x|) r e = ∑ x ∈ A, M.pivotalTerm |q x| r e := by
  have hS : (0 : ℝ) ≤ ∑ x ∈ A, |q x| := Finset.sum_nonneg fun x _ => abs_nonneg (q x)
  have hP : (0 : ℝ) ≤ (M.cutLaw r).real {ω : Config M.V | e ∈ touchSet ω (0 : M.V)} :=
    measureReal_nonneg
  unfold pivotalTerm
  rw [max_eq_left hS]
  calc |M.cutEdgeDeriv r e| *
        (2 * (∑ x ∈ A, |q x|) *
          (M.cutLaw r).real {ω : Config M.V | e ∈ touchSet ω (0 : M.V)})
      = (|M.cutEdgeDeriv r e| *
          (2 * (M.cutLaw r).real {ω : Config M.V | e ∈ touchSet ω (0 : M.V)}))
          * ∑ x ∈ A, |q x| := by ring
    _ = ∑ x ∈ A, (|M.cutEdgeDeriv r e| *
          (2 * (M.cutLaw r).real {ω : Config M.V | e ∈ touchSet ω (0 : M.V)})) * |q x| :=
        Finset.mul_sum ..
    _ = ∑ x ∈ A, |M.cutEdgeDeriv r e| *
          (2 * max |q x| 0 *
            (M.cutLaw r).real {ω : Config M.V | e ∈ touchSet ω (0 : M.V)}) := by
        refine Finset.sum_congr rfl fun x _ => ?_
        rw [max_eq_left (abs_nonneg (q x))]
        ring

/-- **The total pivotal weight of a finite observation is the per-edge series.**

Definitional identification: the left-hand side is `pivotalWeightOf` with truncation bound
`∑_{x∈A} |q x|`, whose summand is `pivotalTerm` by construction (the only step is
`cutLaw r = edgeMeasure (cutProb r)`, which is `rfl` in production). -/
theorem sMomentWeight_eq_tsum_pivotalTerm (A : Finset M.V) (q : M.V → ℝ) (r : ℝ) :
    sMomentWeight (0 : M.V) A q M.cutProb M.cutEdgeDeriv r
      = ∑' e : Sym2 M.V, M.pivotalTerm (∑ x ∈ A, |q x|) r e := by
  simp only [sMomentWeight, pivotalWeightOf, pivotalTerm, M.cutLaw_eq_edgeMeasure r]

/-- The total pivotal weight of a finite observation as the edge series of the finite sum of the
per-vertex weights. -/
theorem sMomentWeight_eq_tsum_finset_sum (A : Finset M.V) (q : M.V → ℝ) (r : ℝ) :
    sMomentWeight (0 : M.V) A q M.cutProb M.cutEdgeDeriv r
      = ∑' e : Sym2 M.V, ∑ x ∈ A, M.pivotalTerm |q x| r e := by
  rw [M.sMomentWeight_eq_tsum_pivotalTerm]
  exact tsum_congr fun e => M.pivotalTerm_finset_sum A q r e

/-- The per-edge weight is measurable in the cut-off radius. -/
theorem measurable_pivotalTerm (m : ℝ) (e : Sym2 M.V) :
    Measurable fun r => M.pivotalTerm m r e := by
  have h := (M.measurable_weightedTouch e).const_mul (max m 0)
  convert h using 1
  funext r
  unfold pivotalTerm
  ring

end SourceModelData

end PercLib.CriticalLRP.Orchestration
