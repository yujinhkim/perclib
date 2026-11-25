/- Integrated from independently rebuilt Ultramath work.
Production base 38371c8354fd1b28220794b007003710ea155dea.
Scratch source: ../../.ultramath/smwvlmbqa/m6/QOne.lean; module paths rewritten.
-/

module

public import PercLib.CriticalLRP.Correlation.I417.General.SourceForm
public import PercLib.CriticalLRP.Correlation.I417.Defs
public import PercLib.CriticalLRP.Correlation.I417.Base.Poly

/-!
# Lemma I.4.17, `q = 1`, arbitrary `p`: the `∑_w` composition into polygon powers

Production (`Correlation/I417/General/SourceForm.lean`) has already reduced the general-`p`,
`q = 1` case of Lemma I.4.17 to the single marked family

  `gap ≤ ∑_w E[|K_x|^p 1(w∈K_x)] · τ(y,w) · ∑_z τ(w,z)`     (`moment_gap_tsub_le_marked_q_one`),

where `gap = E|K|^p E|K| - E[|K_x|^p |K_y| 1(x ↮ y)]`.  The one remaining input is the
*diagram* bound on the base side, exactly as the source has it: the marked tree-graph
expansion gives, with integer coefficients `C_ℓ` counting the diagrams whose marked path has
length `ℓ`,

  `E[|K_x|^p 1(w∈K_x)] ≤ ∑_{ℓ=2}^{p+1} C_ℓ χ^(2p+1-ℓ) T^ℓ(x,w)`,   `χ = E|K|`,

see `Marked.tsum_wtE_marked` for the diagram evaluation: every such diagram is worth exactly
`χ^(2p+1-ℓ) T^ℓ(x,w)` regardless of its shape.

This file records the **second** half of that step, which is pure `ℝ≥0∞` matrix arithmetic and
is proved here unconditionally: composing with the fresh factor `τ(y,w)·χ` and summing over
`w` turns each `T^ℓ(x,w)` into `T^(ℓ+1)(y,x)` (`Poly.tsum_iterPow_mul`), raising the exponent

  `gap ≤ ∑_{ℓ=2}^{p+1} C_ℓ χ^(2p+2-ℓ) T^(ℓ+1)(x,y)`,

i.e. the source's `∑_{ℓ=3}^{p+q+1} C_{p,q,ℓ} T^ℓ(x,y) (E|K|)^{2p+2q+1-ℓ}` at `q = 1`, where
`ℓ` in the source's display is `ℓ+1` here and the exponent is `2p+3-(ℓ+1) = 2p+2-ℓ`.

The residual premise `hjoint` is the *marked tree-graph inequality* for the canonical model
(`E[|K_x|^p 1(w∈K_x)]` bounded by its tree diagrams); it is a precise percolation statement,
not a restatement of the conclusion.  Everything else — BK in the fresh copy (already in
production), transitivity of the mean volume, symmetry of the two-point function, and the
whole `∑_w` composition — is discharged here.
-/

open MeasureTheory Measure ProbabilityTheory unitInterval
open scoped ENNReal NNReal

@[expose] public section

namespace PercLib.CriticalLRP.I417Base

open PercLib.CriticalLRP.TreeExpansion
open PercLib.CriticalLRP.I417Gen

/-- The two-point function is symmetric. -/
theorem edgeMeasure_connSet_comm {V : Type*} (π : Sym2 V → unitInterval) (a b : V) :
    (edgeMeasure π) (connSet a b) = (edgeMeasure π) (connSet b a) := by
  have h : connSet a b = connSet b a := by
    ext ω
    exact SimpleGraph.reachable_comm
  rw [h]

variable {V : Type*} [Countable V] [DecidableEq V]

/-- **Lemma I.4.17, `q = 1`, arbitrary `p`, polygon form.**  Assume the marked tree-graph
bound on the base side with integer coefficients `C`, and the transitivity of the mean
cluster volume (`∀ v, E|K_v| = E|K_x|`).  Then the moment gap is bounded by the finite
polygon/two-point matrix sum

  `∑_{ℓ=2}^{p+1} C_ℓ χ^(2p+2-ℓ) T^(ℓ+1)(x,y)`,

with `T` the two-point matrix and `χ = E|K|`.  This is exactly the `q = 1` case of the
source's display `∑_{ℓ=3}^{p+q+1} C_{p,q,ℓ} T^ℓ(x,y) (E|K|)^{2p+2q+1-ℓ}`. -/
theorem q_one_polygon (π : Sym2 V → unitInterval) (hπ : ∀ e, π e < 1) (x y : V)
    (hχ : ∀ v : V, I417.meanVol π v = I417.meanVol π x)
    (p : ℕ) (C : ℕ → ℕ)
    (hjoint : ∀ w : V, jointPow π x p w ≤
      ∑ ℓ ∈ Finset.Icc 2 (p + 1), (C ℓ : ℝ≥0∞) *
        ((I417.meanVol π x) ^ (2 * p + 1 - ℓ) *
          iterPow (fun a b => (edgeMeasure π) (connSet a b)) ℓ x w)) :
    I417A.momentProd π x y p 1 - I417A.rawDiff π x y p 1 ≤
      ∑ ℓ ∈ Finset.Icc 2 (p + 1), (C ℓ : ℝ≥0∞) *
        ((I417.meanVol π x) ^ (2 * p + 2 - ℓ) *
          iterPow (fun a b => (edgeMeasure π) (connSet a b)) (ℓ + 1) x y) := by
  set χ : ℝ≥0∞ := I417.meanVol π x with hχdef
  set τ : V → V → ℝ≥0∞ := fun a b => (edgeMeasure π) (connSet a b) with hτdef
  have hτsym : ∀ a b : V, τ a b = τ b a :=
    fun a b => edgeMeasure_connSet_comm π a b
  have hfresh : ∀ w : V, (∑' z : V, (edgeMeasure π) (connSet w z)) = χ := by
    intro w
    change I417.meanVol π w = χ
    rw [hχdef]
    exact hχ w
  -- the production reduction to the marked family
  have hgap := moment_gap_tsub_le_marked_q_one π hπ x y p
  refine le_trans hgap ?_
  rw [show (∑' w : V, jointPow π x p w *
        ((edgeMeasure π) (connSet y w) * (∑' z : V, (edgeMeasure π) (connSet w z))))
      = ∑' w : V, jointPow π x p w * (τ y w * χ) from
    tsum_congr fun w => by rw [hfresh w]]
  -- monotonicity in the base factor
  refine le_trans (ENNReal.tsum_le_tsum fun w => mul_le_mul' (hjoint w) le_rfl) ?_
  -- the composition, term by term
  refine le_of_eq ?_
  calc (∑' w : V, (∑ ℓ ∈ Finset.Icc 2 (p + 1), (C ℓ : ℝ≥0∞) *
          (χ ^ (2 * p + 1 - ℓ) * iterPow τ ℓ x w)) * (τ y w * χ))
      = ∑' w : V, ∑ ℓ ∈ Finset.Icc 2 (p + 1), ((C ℓ : ℝ≥0∞) *
          (χ ^ (2 * p + 1 - ℓ) * iterPow τ ℓ x w)) * (τ y w * χ) := by
            refine tsum_congr fun w => ?_
            rw [Finset.sum_mul]
    _ = ∑ ℓ ∈ Finset.Icc 2 (p + 1), ∑' w : V, ((C ℓ : ℝ≥0∞) *
          (χ ^ (2 * p + 1 - ℓ) * iterPow τ ℓ x w)) * (τ y w * χ) :=
            tsum_finset_sum _ _
    _ = ∑ ℓ ∈ Finset.Icc 2 (p + 1), (C ℓ : ℝ≥0∞) *
          (χ ^ (2 * p + 2 - ℓ) * iterPow τ (ℓ + 1) x y) := by
            refine Finset.sum_congr rfl fun ℓ hℓ => ?_
            have hℓ1 : ℓ ≤ p + 1 := (Finset.mem_Icc.mp hℓ).2
            rw [show (∑' w : V, ((C ℓ : ℝ≥0∞) *
                  (χ ^ (2 * p + 1 - ℓ) * iterPow τ ℓ x w)) * (τ y w * χ))
                = ∑' w : V, ((C ℓ : ℝ≥0∞) * χ ^ (2 * p + 1 - ℓ) * χ) *
                    (iterPow τ ℓ x w * τ y w) from
                  tsum_congr fun w => by ring,
                ENNReal.tsum_mul_left, tsum_iterPow_mul τ hτsym ℓ y x]
            rw [mul_assoc (↑(C ℓ) : ℝ≥0∞) (χ ^ (2 * p + 1 - ℓ)) χ, ← pow_succ]
            have hexp : 2 * p + 1 - ℓ + 1 = 2 * p + 2 - ℓ := by omega
            rw [hexp, iterPow_comm τ hτsym (ℓ + 1) y x]
            ring

end PercLib.CriticalLRP.I417Base
