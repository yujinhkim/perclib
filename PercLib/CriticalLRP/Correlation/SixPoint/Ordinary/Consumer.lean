/-
Copyright (c) 2026 PercLib contributors. Released under Apache 2.0.

Consumer for the ordinary `p = 5`, `k = 0` generalized tree-graph inequality
(Hutchcroft, Lemma I.4.16, case `k = 0`):

  `∫⁻ ω, |K₀(ω)|^5 ∂law π  ≤  105 * (∫⁻ ω, |K₀(ω)| ∂law π)^9`

The coefficient is `(2p-3)!! = 7!! = 105 = 15 * 7` and the exponent is `2p-1 = 9`.
Nothing here uses the mixed `k = 1` bound; the only shared ingredients are the
deterministic six-terminal cover (`sixPoint_le_sixShapeChunk`) and the exact
fifth-power identity `lintegral_cardFun_five_eq`.

This module is *proof only*.  It contains no new definitions, so it needs no
`Defs`/`Basic` change.  The two genuinely new mathematical inputs are kept as
explicit hypotheses throughout:

* `hP` -- the per-shape nine-tau **event bound**: for each of the `15 * 7` six-terminal
  shapes, the law of the event "the nine-split tree on the six terminals exists" is
  bounded by its nine-tau diagram `D k j y z w q r`;
* `hE` -- the **diagram evaluation**: the five-leaf, four-internal-point sum of that
  diagram is at most `(∑' x, tau π 0 x)^9`.

`fifth_moment_ordinary_le_of_nineSlotDiagram` is therefore a compiled conditional
consumer, not the final theorem; `latticeLongRange_fifth_moment_ordinary_le` is its
canonical specialization at `latticeLongRangeMeasure d α β`.

Supplied by Ultramath `smwpv4yqm` member `m3` (direction C).
-/
module

public import PercLib.CriticalLRP.Correlation.SixPoint.Attachment.Assembly
public import PercLib.CriticalLRP.PowerLawTreeMoments

open Set MeasureTheory
open scoped ENNReal BigOperators
open PercLib.Percolation.Bond
open PercLib.CriticalLRP.TreeExpansion.FivePoint

@[expose] public section

namespace PercLib.CriticalLRP.TreeExpansion.SixPoint

variable {V : Type*}

/-! ## Step 1: the pure `ℝ≥0∞` accounting -/

/-- **Abstract ordinary assembly.**  A per-shape pointwise bound `hD` on the fivefold joint
connection probability, together with a per-shape bound `hE` on the five-leaf sum of the
shape diagrams, gives the ordinary fifth-moment inequality with coefficient `105` and
exponent `9`.

This is the whole `ℝ≥0∞` content of the `k = 0` case: the deterministic cover and the
nine-fold BK step only feed `hD`, the diagram evaluation only feeds `hE`.  No finiteness,
second-moment or subcriticality hypothesis appears. -/
theorem fifth_moment_ordinary_le_of_nineChunks [Countable V] [AddCommGroup V]
    (π : Sym2 V → unitInterval)
    (D : Fin 15 → Fin 7 → V → V → V → V → V → ℝ≥0∞)
    (hD : ∀ y z w q r : V,
      law π (conn 0 y ∩ conn 0 z ∩ conn 0 w ∩ conn 0 q ∩ conn 0 r) ≤
        ∑' k : Fin 15, ∑' j : Fin 7, D k j y z w q r)
    (hE : ∀ (k : Fin 15) (j : Fin 7),
      (∑' y, ∑' z, ∑' w, ∑' q, ∑' r, D k j y z w q r) ≤ (∑' x, tau π 0 x) ^ 9) :
    ∫⁻ ω, (PercLib.CriticalLRP.Percolation.cardFun
        (PercLib.CriticalLRP.cluster ω (0 : V))) ^ 5 ∂(law π) ≤
      105 * (∫⁻ ω, PercLib.CriticalLRP.Percolation.cardFun
        (PercLib.CriticalLRP.cluster ω (0 : V)) ∂(law π)) ^ 9 := by
  have hmain :
      ∫⁻ ω, (PercLib.CriticalLRP.Percolation.cardFun (PercLib.CriticalLRP.cluster ω (0 : V))) ^ 5
          ∂(law π) ≤
        105 * (∑' x, tau π 0 x) ^ 9 := by
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
      _ ≤ ∑' _ : Fin 15 × Fin 7, (∑' x, tau π 0 x) ^ 9 :=
          ENNReal.tsum_le_tsum fun p => hE p.1 p.2
      _ = 105 * (∑' x, tau π 0 x) ^ 9 := tsum_fin15_fin7_const _
  simpa only [← firstMoment_eq, firstMoment] using hmain

/-- Equality form of `fifth_moment_ordinary_le_of_nineChunks`: the diagram evaluation is
usually proved as an equality. -/
theorem fifth_moment_ordinary_le_of_nineChunks_eq [Countable V] [AddCommGroup V]
    (π : Sym2 V → unitInterval)
    (D : Fin 15 → Fin 7 → V → V → V → V → V → ℝ≥0∞)
    (hD : ∀ y z w q r : V,
      law π (conn 0 y ∩ conn 0 z ∩ conn 0 w ∩ conn 0 q ∩ conn 0 r) ≤
        ∑' k : Fin 15, ∑' j : Fin 7, D k j y z w q r)
    (hE : ∀ (k : Fin 15) (j : Fin 7),
      (∑' y, ∑' z, ∑' w, ∑' q, ∑' r, D k j y z w q r) = (∑' x, tau π 0 x) ^ 9) :
    ∫⁻ ω, (PercLib.CriticalLRP.Percolation.cardFun
        (PercLib.CriticalLRP.cluster ω (0 : V))) ^ 5 ∂(law π) ≤
      105 * (∫⁻ ω, PercLib.CriticalLRP.Percolation.cardFun
        (PercLib.CriticalLRP.cluster ω (0 : V)) ∂(law π)) ^ 9 :=
  fifth_moment_ordinary_le_of_nineChunks π D hD fun k j => (hE k j).le

/-- The two normalisations of the susceptibility: `firstMoment π x` *is* the integral of
`cardFun`, and `firstMoment_eq` identifies it with `∑' y, tau π x y`.  Recording the ninth
power lets a diagram evaluation be delivered in either form. -/
theorem nine_firstMoment_eq_tsum_tau [Countable V] (π : Sym2 V → unitInterval) (x : V) :
    (firstMoment π x) ^ 9 = (∑' y, tau π x y) ^ 9 := by
  rw [firstMoment_eq]

/-- **`firstMoment` form.**  Same as `fifth_moment_ordinary_le_of_nineChunks`, with the
diagram evaluation delivered as `(firstMoment π 0)^9`; the right-hand side is then already
the problem's `105 * (∫⁻ ω, cardFun (cluster ω 0) ∂law π)^9` up to unfolding `firstMoment`. -/
theorem fifth_moment_ordinary_le_of_nineChunks_firstMoment [Countable V] [AddCommGroup V]
    (π : Sym2 V → unitInterval)
    (D : Fin 15 → Fin 7 → V → V → V → V → V → ℝ≥0∞)
    (hD : ∀ y z w q r : V,
      law π (conn 0 y ∩ conn 0 z ∩ conn 0 w ∩ conn 0 q ∩ conn 0 r) ≤
        ∑' k : Fin 15, ∑' j : Fin 7, D k j y z w q r)
    (hE : ∀ (k : Fin 15) (j : Fin 7),
      (∑' y, ∑' z, ∑' w, ∑' q, ∑' r, D k j y z w q r) ≤ (firstMoment π 0) ^ 9) :
    ∫⁻ ω, (PercLib.CriticalLRP.Percolation.cardFun
        (PercLib.CriticalLRP.cluster ω (0 : V))) ^ 5 ∂(law π) ≤
      105 * (∫⁻ ω, PercLib.CriticalLRP.Percolation.cardFun
        (PercLib.CriticalLRP.cluster ω (0 : V)) ∂(law π)) ^ 9 :=
  fifth_moment_ordinary_le_of_nineChunks π D hD fun k j =>
    (hE k j).trans (le_of_eq (nine_firstMoment_eq_tsum_tau π 0))

/-! ## Step 2: the deterministic six-terminal cover -/

/-- **Ordinary assembly from the six-terminal cover.**  The hypotheses are exactly the two
inputs that the event side must supply for the ordinary `k = 0` case, in the shape produced
by the committed six-terminal cover `sixPoint_le_sixShapeChunk`:

* `hP`: for every one of the `105` shapes `(k, j)` and every terminal vector
  `![0, y, z, w, q, r]`, the probability that the split nine-arm tree occurs is bounded by
  the nine-tau diagram `D k j y z w q r` (all four internal vertices `c, u, v, w` remain
  under the union in the *event*, and inside `D` as sums -- no joint group, and no internal
  vertex is dropped);
* `hE`: the five-leaf and four-internal-point sum of each diagram is at most
  `(∑' x, tau π 0 x)^9`.

Unlike the mixed `k = 1` interface, `hE` carries no second-moment factor: the ordinary
`k = 0` case spends all nine tree edges on `tau`. -/
theorem fifth_moment_ordinary_le_of_nineSlotBound [Countable V] [AddCommGroup V]
    (π : Sym2 V → unitInterval)
    (D : Fin 15 → Fin 7 → V → V → V → V → V → ℝ≥0∞)
    (hP : ∀ (k : Fin 15) (j : Fin 7) (y z w q r : V),
      law π (⋃ c : V, ⋃ a : V, ⋃ b : V, ⋃ d : V,
        {ω | SixShape (openGraph ω) k j c a b d ![0, y, z, w, q, r]}) ≤ D k j y z w q r)
    (hE : ∀ (k : Fin 15) (j : Fin 7),
      (∑' y, ∑' z, ∑' w, ∑' q, ∑' r, D k j y z w q r) ≤ (∑' x, tau π 0 x) ^ 9) :
    ∫⁻ ω, (PercLib.CriticalLRP.Percolation.cardFun
        (PercLib.CriticalLRP.cluster ω (0 : V))) ^ 5 ∂(law π) ≤
      105 * (∫⁻ ω, PercLib.CriticalLRP.Percolation.cardFun
        (PercLib.CriticalLRP.cluster ω (0 : V)) ∂(law π)) ^ 9 := by
  refine fifth_moment_ordinary_le_of_nineChunks π D (fun y z w q r => ?_) hE
  rw [← iInter_six_conn y z w q r]
  refine (sixPoint_le_sixShapeChunk (V := V) π ![0, y, z, w, q, r]).trans ?_
  exact ENNReal.tsum_le_tsum fun k => ENNReal.tsum_le_tsum fun j => hP k j y z w q r

/-- Equality form of `fifth_moment_ordinary_le_of_nineSlotBound`. -/
theorem fifth_moment_ordinary_le_of_nineSlotDiagram [Countable V] [AddCommGroup V]
    (π : Sym2 V → unitInterval)
    (D : Fin 15 → Fin 7 → V → V → V → V → V → ℝ≥0∞)
    (hP : ∀ (k : Fin 15) (j : Fin 7) (y z w q r : V),
      law π (⋃ c : V, ⋃ a : V, ⋃ b : V, ⋃ d : V,
        {ω | SixShape (openGraph ω) k j c a b d ![0, y, z, w, q, r]}) ≤ D k j y z w q r)
    (hE : ∀ (k : Fin 15) (j : Fin 7),
      (∑' y, ∑' z, ∑' w, ∑' q, ∑' r, D k j y z w q r) = (∑' x, tau π 0 x) ^ 9) :
    ∫⁻ ω, (PercLib.CriticalLRP.Percolation.cardFun
        (PercLib.CriticalLRP.cluster ω (0 : V))) ^ 5 ∂(law π) ≤
      105 * (∫⁻ ω, PercLib.CriticalLRP.Percolation.cardFun
        (PercLib.CriticalLRP.cluster ω (0 : V)) ∂(law π)) ^ 9 :=
  fifth_moment_ordinary_le_of_nineSlotBound π D hP fun k j => (hE k j).le

/-- **Irreducible single-premise form.**  No diagram is exhibited at all: for each of the
`105` shapes the five-leaf sum of the cover event itself is at most `(∑' x, tau π 0 x)^9`.
This is the weakest per-shape input that still yields the ordinary bound, so it is the
safest statement to compare against whichever of the event bound and the diagram evaluation
land first. -/
theorem fifth_moment_ordinary_le_of_nineShapeSum [Countable V] [AddCommGroup V]
    (π : Sym2 V → unitInterval)
    (hS : ∀ (k : Fin 15) (j : Fin 7),
      (∑' y, ∑' z, ∑' w, ∑' q, ∑' r,
        law π (⋃ c : V, ⋃ a : V, ⋃ b : V, ⋃ d : V,
          {ω | SixShape (openGraph ω) k j c a b d ![0, y, z, w, q, r]})) ≤
        (∑' x, tau π 0 x) ^ 9) :
    ∫⁻ ω, (PercLib.CriticalLRP.Percolation.cardFun
        (PercLib.CriticalLRP.cluster ω (0 : V))) ^ 5 ∂(law π) ≤
      105 * (∫⁻ ω, PercLib.CriticalLRP.Percolation.cardFun
        (PercLib.CriticalLRP.cluster ω (0 : V)) ∂(law π)) ^ 9 := by
  refine fifth_moment_ordinary_le_of_nineChunks π
    (fun k j y z w q r =>
      law π (⋃ c : V, ⋃ a : V, ⋃ b : V, ⋃ d : V,
        {ω | SixShape (openGraph ω) k j c a b d ![0, y, z, w, q, r]}))
    (fun y z w q r => ?_) hS
  rw [← iInter_six_conn y z w q r]
  exact sixPoint_le_sixShapeChunk (V := V) π ![0, y, z, w, q, r]

/-! ## Step 3: the canonical lattice specialization -/

/-- The canonical power-law law is invariant under simultaneous right translation; this is
`lrKernel_unitInterval_translation_of_pair`, restated for the profile that
`latticeLongRangeMeasure` uses.  Any diagram evaluation that needs full profile invariance
is to be run at this profile. -/
theorem latticeLongRange_profile_invariance (d : ℕ) (α : ℝ) (β : NNReal)
    (x y g : Fin d → ℤ) :
    bernoulliEdgeProb (lrKernel d α) (lrKernel_nonneg d α) β s(x + g, y + g) =
      bernoulliEdgeProb (lrKernel d α) (lrKernel_nonneg d α) β s(x, y) :=
  lrKernel_unitInterval_translation_of_pair d α β x y g

/-- **Ordinary fifth moment at the canonical power-law law**, from the two per-shape inputs
at the canonical profile.  There is no finite-moment, subcriticality or critical-sharpness
premise: the inequality is an identity of extended nonnegative quantities that holds for
every `d`, `α` and `β`. -/
theorem latticeLongRange_fifth_moment_ordinary_le (d : ℕ) (α : ℝ) (β : NNReal)
    (D : Fin 15 → Fin 7 → (Fin d → ℤ) → (Fin d → ℤ) → (Fin d → ℤ) → (Fin d → ℤ) →
      (Fin d → ℤ) → ℝ≥0∞)
    (hP : ∀ (k : Fin 15) (j : Fin 7) (y z w q r : Fin d → ℤ),
      law (bernoulliEdgeProb (lrKernel d α) (lrKernel_nonneg d α) β)
        (⋃ c : Fin d → ℤ, ⋃ a : Fin d → ℤ, ⋃ b : Fin d → ℤ, ⋃ d' : Fin d → ℤ,
          {ω | SixShape (openGraph ω) k j c a b d' ![0, y, z, w, q, r]}) ≤
        D k j y z w q r)
    (hE : ∀ (k : Fin 15) (j : Fin 7),
      (∑' y, ∑' z, ∑' w, ∑' q, ∑' r, D k j y z w q r) ≤
        (∑' x, tau (bernoulliEdgeProb (lrKernel d α) (lrKernel_nonneg d α) β) 0 x) ^ 9) :
    ∫⁻ ω, (PercLib.CriticalLRP.Percolation.cardFun
        (PercLib.CriticalLRP.cluster ω (0 : Fin d → ℤ))) ^ 5
        ∂(latticeLongRangeMeasure d α β) ≤
      105 * (∫⁻ ω, PercLib.CriticalLRP.Percolation.cardFun
        (PercLib.CriticalLRP.cluster ω (0 : Fin d → ℤ))
        ∂(latticeLongRangeMeasure d α β)) ^ 9 := by
  have h := fifth_moment_ordinary_le_of_nineSlotBound
    (bernoulliEdgeProb (lrKernel d α) (lrKernel_nonneg d α) β) D hP hE
  simpa only [latticeLongRangeMeasure, longRangeMeasure] using h

end PercLib.CriticalLRP.TreeExpansion.SixPoint

#print axioms PercLib.CriticalLRP.TreeExpansion.SixPoint.fifth_moment_ordinary_le_of_nineChunks
#print axioms PercLib.CriticalLRP.TreeExpansion.SixPoint.fifth_moment_ordinary_le_of_nineChunks_eq
#print axioms PercLib.CriticalLRP.TreeExpansion.SixPoint.nine_firstMoment_eq_tsum_tau
#print axioms PercLib.CriticalLRP.TreeExpansion.SixPoint.fifth_moment_ordinary_le_of_nineChunks_firstMoment
#print axioms PercLib.CriticalLRP.TreeExpansion.SixPoint.fifth_moment_ordinary_le_of_nineSlotBound
#print axioms PercLib.CriticalLRP.TreeExpansion.SixPoint.fifth_moment_ordinary_le_of_nineSlotDiagram
#print axioms PercLib.CriticalLRP.TreeExpansion.SixPoint.fifth_moment_ordinary_le_of_nineShapeSum
#print axioms PercLib.CriticalLRP.TreeExpansion.SixPoint.latticeLongRange_profile_invariance
#print axioms PercLib.CriticalLRP.TreeExpansion.SixPoint.latticeLongRange_fifth_moment_ordinary_le
