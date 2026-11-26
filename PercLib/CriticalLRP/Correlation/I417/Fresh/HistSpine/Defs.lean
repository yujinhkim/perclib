/-
One-step reindexing on actual `I417GenIter.Hist` histories, from independently reviewed
`smwxdrsgz/m1`. Only the history-specific definitions are new; the analytic spine core is reused.
-/
module

public import PercLib.CriticalLRP.Correlation.I417.Fresh.Spine.Defs

/-!
# Weights and fibres on the production attachment histories

`histW` retains a two-point weight for every leg, while `splitWt` sums an
attachment vertex and its newly attached arm before the chain is collapsed.
`histFibre` restricts this sum to one split-choice branch.

This is not a proof of the closed form of the iterated weight, nor of the
packaging into the general fresh profile.
-/

open MeasureTheory Measure ProbabilityTheory unitInterval
open scoped ENNReal BigOperators

@[expose] public section

namespace PercLib.CriticalLRP.I417HistToSpine

/-! ## The actual history-side objects

These are the only new definitions; every file after `Defs.lean` contains theorems about them.
They speak about production's actual objects: `I417GenIter.Hist`, `Hist.legs`, `Hist.snoc`,
`I417FreshDepth.splitChoices`, and the two-point factor `I417Fresh.tau` (whose row sums are the
`χ` of the printed normal form). -/

open PercLib.CriticalLRP

variable {V : Type*}

/-- The product of the two-point factors of **all** `2(n+1)` legs of the diagram built by an
attachment history `H`.  `W` is a leg weight: `W i` is put on the leg in slot `i`, so that
`histW (fun _ => tau) H y w ga` is precisely the product appearing in
`I417GenIter.genShape_measure_le`. -/
noncomputable def histW {n : ℕ} (W : (i : I417GenIter.Idx n) → V → V → ℝ≥0∞)
    (H : I417GenIter.Hist V n) (y w ga : V) : ℝ≥0∞ :=
  ∏ i : I417GenIter.Idx n, W i (H.legs y w ga i).1 (H.legs y w ga i).2

/-- **One attachment step, on weights.**  Splitting the leg in slot `s` at `z` and attaching the
arm `z → d` replaces the weight of the split slot by the nested sum
`∑_z W(inl s)(a,z) · W(inr false)(z,b) · ∑_d W(inr true)(z,d)` and leaves every other slot's weight
alone.  This is the combinatorial content of "the arm attached at the split point is summed out
before the leg structure collapses": the inner `∑_d` is taken first, at the split vertex `z`, while
the outer `∑_z` inserts `z` into the chain. -/
noncomputable def splitWt {ι : Type*} [DecidableEq ι]
    (W : ι ⊕ Bool → V → V → ℝ≥0∞) (s : ι) (i : ι) : V → V → ℝ≥0∞ :=
  if i = s then fun a b =>
      ∑' z : V, W (Sum.inl i) a z * W (Sum.inr false) z b * (∑' d : V, W (Sum.inr true) z d)
  else W (Sum.inl i)

/-- The **fibre sum** of the fresh diagram family over the branches with a fixed split-choice
tuple `k`: the sum over all attachment histories realising `k` (i.e. over all attachment vertices
and all attached arms) of the product of the leg weights, with the mark target `ga` still free.
`k = I417FreshDepth.splitChoices H` is production's own branch map, so this is exactly the inner
sum of `I417GenIter.genShape_measure_le` restricted to one branch. -/
noncomputable def histFibre {n : ℕ} (W : (i : I417GenIter.Idx n) → V → V → ℝ≥0∞)
    (y w : V) (k : (t : Fin n) → I417GenIter.Idx t) : V → ℝ≥0∞ :=
  fun ga => ∑' H : {H : I417GenIter.Hist V n // I417FreshDepth.splitChoices H = k},
    histW W H.1 y w ga

end PercLib.CriticalLRP.I417HistToSpine
