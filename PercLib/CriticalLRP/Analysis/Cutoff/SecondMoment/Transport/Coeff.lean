/-
Copyright (c) 2026 PercLib contributors. Released under Apache 2.0.

# The coefficient `M.coeffRHS r` on the *edge* side of the `p = 2` assembly

Swarm `smwvc1d9z`, member `m3`, direction `d2`

Integration donor: `.ultramath/smwvc1d9z/m3/Coeff.lean`, checked at `a6a74fb05eb13da61d4ce2cb87e2f55e7bd7c31f`. (referee / integration audit).

The `p = 2` target of Lemma I.4.1 is an identity of the form

  `∑'_e M.cutEdgeDeriv r e * pivotalFlux (M.cutLaw r) F e = M.rhsScalarTwo r`,

with `F = (fun ω => (clusterVol ω 0).toReal ^ 2)` and, by
`SecondMoment/Defs.rhsScalarTwo`, `M.rhsScalarTwo r = M.coeffRHS r * (M.p2RHS r).toReal`.

The left-hand side carries the coefficient `M.coeffRHS r = β_c (-K'(r))` **inside every
summand**: `M.cutEdgeDeriv r e` is literally `β_c (-K'(r))` times the closed-edge weight
`e^{-β_c J_r(e)}` (which is `1 - q_e(r)`, the deficit of the cut-off edge probability).  The
right-hand side carries the same coefficient as an outside factor.  Nothing in the project
currently states that the two presentations agree, so the edge sum and the source's `p = 2`
right-hand side cannot be compared without redoing the `Sym2.lift` case analysis on a
per-edge basis.  This file records the two presentations once and for all:

* `SourceModelData.cutEdgeDeriv_eq_coeffRHS_mul` — `M.cutEdgeDeriv r e` is `M.coeffRHS r` times
  the closed-edge weight, as a `Sym2`-level identity (loop edges included, both sides `0`);
* `SourceModelData.tsum_cutEdgeDeriv_mul_pivotalFlux` — hence the whole edge `tsum` of the
  `p = 2` flux factors as `M.coeffRHS r` times the `tsum` of the closed-edge weight times that
  flux.  The interchange is `tsum_mul_left`, which for `ℝ` is unconditional: no summability of
  the flux, no radius-uniform majorant and no moment hypothesis enters.

This is bookkeeping, not analysis: it does **not** prove the edge-sum identity, and no derivative
is claimed.  Where the identity still stands open is recorded in `RESULTS.md`.
-/
module

public import PercLib.CriticalLRP.Analysis.Cutoff.SecondMoment.Transport.Defs
public import PercLib.CriticalLRP.Analysis.Cutoff.SecondMoment.Transport.Basic
public import PercLib.CriticalLRP.Analysis.Cutoff.SecondMoment.Transport.ToReal
public import PercLib.CriticalLRP.Analysis.Cutoff.Deriv

/-!
# The `coeffRHS` factorization of the edge sum

`cutEdgeDeriv r e = coeffRHS r * cutEdgeClosedWeight r e`, and the edge `tsum` factors.
-/

set_option autoImplicit false
set_option linter.hashCommand false
set_option linter.style.longLine false

@[expose] public section

noncomputable section

open MeasureTheory
open scoped ENNReal NNReal

namespace PercLib.CriticalLRP

namespace Orchestration

namespace SourceModelData

variable (M : SourceModelData)

attribute [local instance] Classical.propDecidable

/-- The two branches of `cutEdgeClosedWeight`, exposed for the factorization proof. -/
@[simp] theorem cutEdgeClosedWeight_mk (r : ℝ) (x y : M.V) :
    M.cutEdgeClosedWeight r s(x, y) =
      (if x = y then 0 else
        (if M.S.dist x y ≤ r then
          Real.exp (-((M.betaCrit : ℝ) *
            FiniteVolume.cutoffProfile M.K r (M.S.dist x y)))
         else 0)) := rfl

/-- **The cut-off derivative weight is `β_c (-K'(r))` times the closed-edge weight.**  Loop
edges give `0 = β_c (-K'(r)) * 0`; the other edges give the identity by associativity of the
product in `ℝ`.  No hypothesis on the radius, the profile or the derivative. -/
theorem cutEdgeDeriv_eq_coeffRHS_mul (r : ℝ) (e : Sym2 M.V) :
    M.cutEdgeDeriv r e = M.coeffRHS r * M.cutEdgeClosedWeight r e := by
  induction e using Sym2.ind with
  | h x y =>
    rw [M.cutEdgeDeriv_mk r x y, M.cutEdgeClosedWeight_mk r x y]
    simp only [SourceModelData.coeffRHS]
    split_ifs <;> ring

/-- **The `p = 2` edge sum factors the coefficient `β_c (-K'(r))` out.**  For any real-valued
functional `F`, the `tsum` over the edges of `cutEdgeDeriv r e * pivotalFlux μ F e` is
`M.coeffRHS r` times the `tsum` of `cutEdgeClosedWeight r e * pivotalFlux μ F e`.

No summability hypothesis: `tsum_mul_left` over `ℝ` is unconditional (and both sides agree at
`M.coeffRHS r = 0`).  Consequently the whole `p = 2` derivative weight sits on the *outside* of
the edge sum, exactly as `M.rhsScalarTwo r = M.coeffRHS r * (M.p2RHS r).toReal` has it. -/
theorem tsum_cutEdgeDeriv_mul_pivotalFlux (r : ℝ) (F : Config M.V → ℝ) :
    ∑' e : Sym2 M.V, M.cutEdgeDeriv r e * pivotalFlux (M.cutLaw r) F e
      = M.coeffRHS r *
        ∑' e : Sym2 M.V, M.cutEdgeClosedWeight r e * pivotalFlux (M.cutLaw r) F e := by
  rw [← tsum_mul_left]
  exact tsum_congr fun e => by
    rw [M.cutEdgeDeriv_eq_coeffRHS_mul r e]
    ring

/-- **The `p = 2` edge sum against the source's coefficient and the paper sum.**  Combining the
`coeffRHS` factorization with `ToReal.rhsScalarTwo_eq_integral_toReal_p2PaperSum` puts the exact
edge-side and vertex-side presentation of the *same* coefficient side by side:

`∑'_e cutEdgeDeriv r e * pivotalFlux μ F e = coeffRHS r * ∑'_e closedWeight e * pivotalFlux μ F e`
must be compared with
`rhsScalarTwo r = coeffRHS r * ∫ ω, (PivotFlux.p2PaperSum M r ω).toReal ∂(M.cutLaw r)`.

The two are **not** identified here: doing so is exactly the per-edge published-flux identity
(direction B) together with the ordered-pair/`Sym2` reindexing (direction A). -/
theorem tsum_cutEdgeDeriv_mul_pivotalFlux_eq_coeffRHS_mul_integral_p2PaperSum
    (r : ℝ) (F : Config M.V → ℝ) (h : M.p2RHS r ≠ ⊤) :
    ∑' e : Sym2 M.V, M.cutEdgeDeriv r e * pivotalFlux (M.cutLaw r) F e
        = M.coeffRHS r *
            ∑' e : Sym2 M.V, M.cutEdgeClosedWeight r e * pivotalFlux (M.cutLaw r) F e
      ∧ M.rhsScalarTwo r
          = M.coeffRHS r * ∫ ω, (PivotFlux.p2PaperSum M r ω).toReal ∂(M.cutLaw r) :=
  ⟨M.tsum_cutEdgeDeriv_mul_pivotalFlux r F, PivotFlux.rhsScalarTwo_eq_integral_toReal_p2PaperSum M r h⟩

end SourceModelData

end Orchestration

end PercLib.CriticalLRP

end

/-! ## Axiom audit -/

namespace PercLib.CriticalLRP.Orchestration

#print axioms SourceModelData.cutEdgeDeriv_eq_coeffRHS_mul
#print axioms SourceModelData.tsum_cutEdgeDeriv_mul_pivotalFlux
#print axioms SourceModelData.tsum_cutEdgeDeriv_mul_pivotalFlux_eq_coeffRHS_mul_integral_p2PaperSum

end PercLib.CriticalLRP.Orchestration
