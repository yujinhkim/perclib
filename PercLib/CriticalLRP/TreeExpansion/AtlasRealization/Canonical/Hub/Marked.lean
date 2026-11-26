/- Independently rebuilt and integrated from `smwx2gpeq`, member `m1` finding f1.
Production integration revision: `4a0f1d2a3c823f8e636a9296a0a909362bdee4d7`.

Production is read only (HEAD 4a0f1d2a3c823f8e636a9296a0a909362bdee4d7,
`.scratch/critical-lrp-orchestration`).

# The hub-regrouped marked joint-moment bound

This file applies `CanonHub/Main.lean` to the actual canonical moment studied in
`PercLib.CriticalLRP.Correlation.I417.MarkedJoint`, namely

`I417Gen.jointPow π x p w = E[|K_x|^p 1(w ∈ K_x)]`.

The result is a bound with the hubs regrouped: a hub selection that depends on the shape alone,
`k` blocks of three raw two-point factors, and `2(p+1) - 1 - 3k` single raw two-point factors.

## What this does and does not claim

It is a bound on `E[|K_x|^p 1(w ∈ K_x)]`.  It does **not** identify those raw two-point factors
with the source's in-cluster two-point functions, does not identify the blocks with in-cluster
three-point functions, and does not by itself give the mixed-`k` moment inequality: those are
separate steps (see `README.md` in this directory).  It is infrastructure, applied.

The bound is stated in the arm-labelling form `∑' f : Fin p → V` (the shape of
`I417Gen.tsum_labelEvent_inter`), with the mark inserted as the last terminal by
`I417Marked.markedExtend`.  That form is chosen so that no `if`-then-else over a `Decidable`
instance appears in a comparison between two sums from different modules.
-/
module

public import PercLib.CriticalLRP.TreeExpansion.AtlasRealization.Canonical.Hub.Main
public import PercLib.CriticalLRP.Correlation.I417.MarkedJoint.Main

/-!
# The marked joint-moment bound with the hubs regrouped
-/

@[expose] public section

open MeasureTheory Measure ProbabilityTheory
open scoped ENNReal

set_option autoImplicit false
set_option linter.unusedSectionVars false
set_option linter.unusedFintypeInType false
set_option linter.unusedDecidableInType false

namespace CanonAtlas

open Finset

open PercLib.CriticalLRP (Config connSet edgeMeasure)
open PercLib.CriticalLRP.TreeExpansion (RTree LTon)
open PercLib.CriticalLRP.TreeExpansion.Real (AEdge hubAEdges offHubAEdges)

variable {V : Type*} [DecidableEq V] [Countable V]

/-- **The hub-regrouped marked joint-moment bound.**

For every `p` and every `k ≤ ⌈p/2⌉` there is a selection `K` of `k` same-parity internal vertices
for every fully labelled `(p + 1)`-leaf shape -- depending on the shape only, hence uniform in the
arm tuple and the positions -- such that

`E[|K_x|^p 1(w ∈ K_x)] ≤ markedHubBound π x w p K`,

and at each `(f, t, φ)` the product is `k` blocks of three raw two-point connection
probabilities (the 3-stars of the hubs `K t`) times the `2(p+1) - 1 - 3k` raw two-point
probabilities of the atlas edges not adjacent to a hub.

Every factor is `edgeMeasure π (connSet u v)`; no factor is a joint or in-cluster quantity. -/
theorem jointPow_le_markedHubBound (π : Sym2 V → unitInterval) (hπ : ∀ e, π e < 1)
    (x w : V) (p : ℕ) {k : ℕ} (hk : k ≤ (p + 1) / 2) :
    ∃ K : (t : LTon (Fin (p + 1)) Finset.univ) → Finset t.1.IPos,
      (∀ t : LTon (Fin (p + 1)) Finset.univ,
        (K t).card = k ∧
        ((∀ v ∈ K t, RTree.iposDepth t.1 v % 2 = 0) ∨
          (∀ v ∈ K t, RTree.iposDepth t.1 v % 2 = 1)) ∧
        (hubAEdges t.1 (K t)).card = 3 * k ∧
        (offHubAEdges t.1 (K t)).card = 2 * t.1.numLeaves - 1 - 3 * k) ∧
      PercLib.CriticalLRP.I417Gen.jointPow π x p w ≤ markedHubBound π x w p K := by
  classical
  obtain ⟨K, hK⟩ := exists_hubSelection (q := p + 1) (k := k) (by simpa using hk)
  refine ⟨K, hK, ?_⟩
  have harm : PercLib.CriticalLRP.I417Gen.jointPow π x p w
      = ∑' f : Fin p → V,
          edgeMeasure π (PercLib.CriticalLRP.I417A.labelEvent x
            (PercLib.CriticalLRP.I417Marked.markedExtend w f)) := by
    rw [← PercLib.CriticalLRP.I417Gen.tsum_labelEvent_inter π x p w]
    exact tsum_congr fun f =>
      congrArg (edgeMeasure π) (PercLib.CriticalLRP.I417Marked.labelEvent_markedExtend x w f).symm
  rw [harm, markedHubBound]
  exact ENNReal.tsum_le_tsum fun f =>
    edgeMeasure_labelEvent_le_tsum_hubSplit_of_selection π hπ (Nat.succ_pos p) x
      (PercLib.CriticalLRP.I417Marked.markedExtend w f) K (fun t => (hK t).2.1)

end CanonAtlas
