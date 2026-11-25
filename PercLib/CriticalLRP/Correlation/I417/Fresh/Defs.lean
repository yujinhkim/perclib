/- Integrated from independently rebuilt Ultramath work.
Production base 7a04599a899ac160fd051de07e5a0ef98d771674.
Scratch source: ../../.ultramath/smwvlmbqa/m4/Defs.lean.
-/

module

public import PercLib.CriticalLRP.Correlation.I417.General.Main
public import PercLib.CriticalLRP.Correlation.TreeGraphCanonical

/-!
# The I.4.17 fresh side: spine/hub reduction and the finite diagram family

Source: Tom Hutchcroft, *Critical long-range percolation I: High effective dimension*,
arXiv:2508.18807v1, Lemma I.4.17 (p. 45) and its proof.

The proof of Lemma I.4.17 factorises the marked two-copy sum over the two independent copies.  Its
**fresh-copy factor** is

  `∑_{y_1,…,y_q} P(y_1,…,y_q ∈ K̃_y, w on a simple open path connecting y to {y_1,…,y_q})`,

with `w` the marked vertex.  Production (`PercLib.CriticalLRP.I417Gen`, modules
`Correlation/I417/General/{Defs,Main}.lean`) realises this factor as

  `F(q,y,j,w) = ∑_{g : Fin q → V} (edgeMeasure π) (freshMark y g j w)`,

where `freshMark y g j w = {y↔w} ∘ {w↔g j} ∩ ⋂_{j'} {y ↔ g j'}` is the `DisjointOccurrence` of the
two halves of a path `y → w → g j`, intersected with the `q` labelled arms lying in the fresh
cluster.  That module deliberately stops there: *evaluating* `jointPow` and `F` by tree diagrams is
the diagram side of I.4.17.

This file fixes the objects the diagram side needs and states — as a single named `Prop`, with no
analytic wrapper around it — the one inequality that remains on the fresh side.

## The two structural facts the paper uses, and what they cost

1. **The spine.**  The mark `w` lies on an open path from `y` to the terminal arm `g j`, and the
   two halves of that path are *edge-disjoint*.  Hence every configuration in `freshMark y g j w`
   has `w` in the cluster of `y`, and every arm `g j'` in the cluster of `w`:
   `freshMark y g j w ⊆ hubStar y w g` (`Main.freshMark_subset_hubStar`).  This is what makes the
   `w`-summation a polygon (matrix-power) composition with the base side of I.4.17, and it is why
   `w` must stay visible rather than being absorbed into a `χ` factor.

2. **The arms must be kept.**  Discarding any arm leaves an unrestricted vertex sum and the bound
   diverges.  The paper keeps them through the tree-graph expansion, which produces one two-point
   factor per free vertex.

Fact 2 is why the *single-hub* diagram `∑_a τ(w,a) ∏_j τ(a, g j)` is not available once the hub
carries three or more arms; `Main.freshMark_measure_le_oneHub` proves the two-arm case (all `q`),
and the documentation records what breaks for more arms.  The correct family is the
tree/comb family, and `freshCombBound` below is its aggregated form written as an explicit iterated
`tsum`, so that the remaining premise is a finite diagram sum and not a black box.

Definitions only in this file.
-/

open MeasureTheory Measure ProbabilityTheory unitInterval
open scoped ENNReal NNReal

set_option linter.unusedSectionVars false

@[expose] public section

namespace PercLib.CriticalLRP.I417Fresh

variable {V : Type*} [Countable V]

/-- **The `q`-arm star at the hub `w`**: all `q` labelled arms of the fresh side lie in the cluster
of the hub.  This is the hub half of the fresh event, without the `y ↔ w` spine. -/
def armStar (w : V) {q : ℕ} (g : Fin q → V) : Set (Config V) :=
  ⋂ j : Fin q, connSet w (g j)

/-- **The spine-plus-hub event**: the mark `w` is in the cluster of `y` and every arm is in the
cluster of `w`.  The paper's condition `w on a simple open path from y to {y_1,…,y_q}` implies this,
and `Main.freshMark_subset_hubStar` is the inclusion. -/
def hubStar (y w : V) {q : ℕ} (g : Fin q → V) : Set (Config V) :=
  connSet y w ∩ armStar w g

/-- The two-point function `τ(u,v) = P(u ↔ v)` of the canonical model, valued in `ℝ≥0∞`. -/
noncomputable def tau (π : Sym2 V → unitInterval) (u v : V) : ℝ≥0∞ :=
  (edgeMeasure π) (connSet u v)

theorem tau_def (π : Sym2 V → unitInterval) (u v : V) :
    tau π u v = (edgeMeasure π) (connSet u v) := rfl

/-- The free arm sum at a hub: `∑_z τ(a,z)`.  This is the factor one summed arm contributes. -/
noncomputable def hubArmSum (π : Sym2 V → unitInterval) (a : V) : ℝ≥0∞ :=
  ∑' z : V, tau π a z

/-- **The comb tail.**  `armComb π a n` is the aggregated diagram fan-out of `n` further arm
levels hanging off the chain of hubs that starts at `a`: one new hub `b` per level, contributing the
chain factor `τ(a,b)`, the free-arm factor `hubArmSum b`, and the rest of the chain.  A level may
stay (`b = a`, using `τ(a,a) = 1`), which is what lets several arms hang off one hub. -/
noncomputable def armComb (π : Sym2 V → unitInterval) (a : V) : ℕ → ℝ≥0∞
  | 0 => 1
  | (n + 1) => ∑' b : V, tau π a b * hubArmSum π b * armComb π b n

/-- **The aggregated fresh-side tree diagram bound.**  `freshCombBound π q y w` is the value of the
fresh-side diagram sum of Lemma I.4.17 for `q` arms, in the following explicit form.

The diagram is a chain of hubs `w = v 0, v 1, …, v (q+1)` (`Fin.cons w u`), each consecutive pair
joined by one two-point factor `τ(v i, v (i+1))`.  The hub `w` is the *mark* `w` of I.4.17, so its
chain position is fixed: that is the spine.  Each of the `q+1` arm levels `v 1, …, v (q+1)` then
carries one arm, which is either a free arm (`hubArmSum`) or the I.4.17 arm `y` (`τ(·,y)`); the
product form below allows either at *every* level, which only enlarges the bound and keeps every
`y`-dependent term that the polygon composition with the base side needs.

The monomial has `2q + 2` two-point factors: the printed fresh-side diagram has `2q + 1` edges, and
the extra factor is the loss in allowing the `y`-slot at every level.  No arm is ever dropped, so no
unrestricted vertex sum appears.

For `q = 1` the chain is `w → a → a` and the value is at least the three-arm single-hub diagram
`∑_a τ(w,a) τ(a,y) ∑_z τ(a,z)`, which `Main.fresh_factor_one_le` proves unconditionally. -/
noncomputable def freshChainBound (π : Sym2 V → unitInterval) (q : ℕ) (y w : V) : ℝ≥0∞ :=
  ∑' u : Fin (q + 1) → V,
    (∏ i : Fin (q + 1),
        tau π ((Fin.cons w u : Fin (q + 2) → V) (Fin.castSucc i))
          ((Fin.cons w u : Fin (q + 2) → V) i.succ)) *
      (∏ i : Fin (q + 1),
        (hubArmSum π ((Fin.cons w u : Fin (q + 2) → V) i.succ) +
          tau π ((Fin.cons w u : Fin (q + 2) → V) i.succ) y))

/-- The single-hub diagram with the mark `w` in the spine and one arm at the first hub `a`; the
remaining `q − 1` arms hang off the chain (`armComb`).  For `q = 1` this is exactly the three-arm
single-hub diagram `∑_a τ(w,a) τ(a,y) ∑_z τ(a,z)`. -/
noncomputable def firstHubBound (π : Sym2 V → unitInterval) (q : ℕ) (y w : V) : ℝ≥0∞ :=
  ∑' a : V, tau π w a * tau π a y * hubArmSum π a * armComb π a (q - 1)

/-- **The aggregated fresh-side tree diagram bound.**  `freshCombBound π q y w` is the value of the
fresh-side diagram sum of Lemma I.4.17 for `q` arms, as the sum of

* `freshChainBound` — the general chain of hubs `w = v 0, v 1, …, v (q+1)`, each consecutive pair
  joined by one two-point factor, each of the `q+1` arm levels carrying either a free arm
  (`hubArmSum`) or the I.4.17 arm `y` (`τ(·,y)`).  The direct configurationwise cover is proved
  at `q = 1` and `q = 2`.  It does not extend in the same form to `q = 3`:
  `Correlation/I417/Fresh/Obstruction` constructs a six-edge double star on which the four-arm
  event holds but the eight spine-and-leg requirements have no pairwise edge-disjoint witnesses.
  This does not refute `FreshCombBound π 3`, since an upper bound need not use that particular
  cover.  A level may stay put (`v (i+1) = v i`, `τ(v,v) = 1`), which lets several arms hang off
  one hub.  The monomial has `2q + 2` two-point factors against the printed
  fresh-side diagram's `2q + 1` edges: the extra factor is the loss in allowing the `y`-slot at
  every level, and no arm is ever dropped, so no unrestricted vertex sum appears;
* `firstHubBound` — the single-hub diagram with the mark `w` as spine, which is the shape available
  in closed form (and is what `Main.fresh_factor_one_le` proves unconditionally at `q = 1`). -/
noncomputable def freshCombBound (π : Sym2 V → unitInterval) (q : ℕ) (y w : V) : ℝ≥0∞ :=
  freshChainBound π q y w + firstHubBound π q y w

/-- **The fresh side of Lemma I.4.17, general `q`.**  The fresh-copy factor is bounded by the
aggregated tree diagram above.  No finiteness, transitivity or moment hypothesis is folded in: a
consumer must supply exactly this inequality, at the law it needs. -/
def FreshCombBound (π : Sym2 V → unitInterval) (q : ℕ) : Prop :=
  ∀ (y w : V) (j : Fin q),
    (∑' g : Fin q → V, (edgeMeasure π) (I417Gen.freshMark y g j w)) ≤ freshCombBound π q y w

/-- The canonical equivalence `(Fin 1 → V) ≃ V`, used to reindex the one-arm sum. -/
def finOneArrowEquiv (V : Type*) : (Fin 1 → V) ≃ V where
  toFun g := g 0
  invFun z := fun _ => z
  left_inv g := by funext i; fin_cases i; rfl
  right_inv _ := rfl


end PercLib.CriticalLRP.I417Fresh
