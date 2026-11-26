/-
Independently rebuilt and integrated from the accepted `smwx5p94b/m3` artifact.
Prepared at base `5e579c30ee2c5caa2d151372f1929efd8ed587fb`;
production integration revision `9be3dd2832bf4fe01e33a70c2c3192ab4c837d88`.
The coordinator moved `fanSpineHubW` to this definitions file and qualified module imports.
-/

module

public import PercLib.CriticalLRP.Correlation.I417.Fresh.Fork.Main

/-!
# The `q = 3` fresh side of Lemma I.4.17: the one-hub *spine–hub* family

Source: Tom Hutchcroft, *Critical long-range percolation I: High effective
dimension*, arXiv:2508.18807v1, Lemma I.4.17 (p. 45) and its proof, p. 45:

> "Since the events defining the conditions on `Kx` and `K~y` in the last line are
> independent, we obtain the bound ... Expanding each of these probabilities out as
> in the proof of the tree-graph inequality yields the claim: We obtain a bound in
> terms of tree diagrams with two pinned vertices at `x` and `y`, with `2p+2q+1`
> edges in total, some number `3 ≤ ℓ ≤ p+q+1` of which belong to the path
> connecting `x` and `y`."

The **fresh** factor of that display is

`∑_{y_1,…,y_q} P(y_1,…,y_q ∈ K~y, w on a simple open path from y to {y_1,…,y_q})`

which production (`PercLib.CriticalLRP.I417Gen.freshMark`) realises as
`∑_g P(freshMark y g j w)`, and bounds by the larger hub event
`hubStar y w g = {y ↔ w} ∩ ⋂_j {w ↔ g j}` (`freshMark_subset_hubStar`).

## What this file adds

Production's fresh side at `q = 3` is the aggregate `freshCombBound π 3 y w`, a sum
of a **chain** family (`freshChainBound`, `2(q+1) = 8` two-point factors) and
`firstHubBound`. `I417/Fresh/Obstruction` shows that the fixed chain cover fails on
the six-edge double star, and `I417/Fresh/Fork` supplies the two-hub **fork**
family (`6 = 2q` factors), which the double star does admit.

The fork is not a cover either: `Main.fan_not_forkEvent` below exhibits a five-edge
configuration (the **fan**: the mark `w` at the end of a spine `w–a`, the hub `a`
carrying all three arms, and the arm `y` adjacent to the mark) on which the fresh hub
event holds and **no** fork event has pairwise edge-disjoint witnesses, for any
choice of the two hubs. The obstruction is a cut count: the fan has five edges, and
the six fork requirements of that configuration always have total cut separation at
least six (`fanSep_ge_six`).

The family defined here closes exactly that configuration with the source-faithful
number of factors. Its five requirements are

* `w ↔ a` — the spine joining the mark to the hub,
* `w ↔ y` — the marked arm at the mark,
* `a ↔ g i` for `i < 3` — the three labelled arms at the hub,

so the BK monomial is `τ(w,a) · τ(w,y) · τ(a,g 0) · τ(a,g 1) · τ(a,g 2)`: **five**
two-point factors, against the source's fresh-side budget of `2q = 6` and the chain
family's `2q + 2 = 8`. No arm is dropped and no arm is summed only partially; the
arm `y` stays visible as its own factor.

`Main.fan_spineHubEvent` shows the family is non-vacuous exactly where the fork
fails, so `fork ∪ spineHub` covers both the double star and the fan, while neither
family alone covers both.

Definitions only in this file.
-/

open MeasureTheory Measure ProbabilityTheory unitInterval
open scoped ENNReal NNReal

set_option linter.unusedSectionVars false

@[expose] public section

namespace PercLib.CriticalLRP.I417Fresh

namespace Q3

variable {V : Type*} [Countable V]

/-! ## The spine–hub family -/

/-- **The five connection requirements of the spine–hub family**: the spine `w ↔ a`,
the marked arm `w ↔ y` at the mark, and the three labelled arms at the hub `a`. -/
def spineHubReq (w a y : V) (g : Fin 3 → V) : Fin 5 → Set (Config V) :=
  ![connSet w a, connSet w y, connSet a (g 0), connSet a (g 1), connSet a (g 2)]

/-- **The spine–hub event**: pairwise edge-disjoint witness sets for the five
requirements, all inside the configuration. This is `DisjointOccurrenceFin` of
`spineHubReq`, so the iterated van den Berg–Kesten inequality applies to it
directly. -/
def spineHubEvent (w a y : V) (g : Fin 3 → V) : Set (Config V) :=
  Percolation.DisjointOccurrenceFin (spineHubReq w a y g)

/-- The five two-point factors carried by the spine–hub event, in slot order. -/
noncomputable def spineHubMono (π : Sym2 V → unitInterval) (w a y : V)
    (g : Fin 3 → V) : ℝ≥0∞ :=
  tau π w a * tau π w y * tau π a (g 0) * tau π a (g 1) * tau π a (g 2)

/-- **The summed spine–hub diagram** at `q = 3`: the hub is summed over, the three
arms are summed out to `hubArmSum`, and the marked arm `y` is kept as its own
factor. It carries the five two-point factors `τ(w,a)`, `τ(w,y)` and `χ(a)^3`. -/
noncomputable def spineHubBound (π : Sym2 V → unitInterval) (y w : V) : ℝ≥0∞ :=
  ∑' a : V, tau π w a * tau π w y * (hubArmSum π a) ^ 3

/-- The same diagram written with the three arm factors separated. -/
theorem spineHubBound_eq (π : Sym2 V → unitInterval) (y w : V) :
    spineHubBound π y w =
      ∑' a : V, tau π w a * tau π w y * hubArmSum π a * hubArmSum π a *
        hubArmSum π a := by
  simp only [spineHubBound, pow_three, mul_assoc]

/-! ## The fan: a fresh configuration no fork covers

Vertices `Fin 6`: `0` is the mark `w`, `1` the hub, `2, 3, 4` the three arms and `5`
the marked arm `y`. The five edges are the spine `0–1`, the hub legs `1–2`, `1–3`,
`1–4`, and the arm edge `0–5`. -/

/-- The vertex type of the fan. -/
abbrev FV : Type := Fin 6

/-- The five edges of the fan. -/
def fanE : Finset (Sym2 FV) := {s(0, 1), s(0, 5), s(1, 2), s(1, 3), s(1, 4)}

/-- The mark `w` of the fan. -/
def fanW : FV := 0

/-- The hub `a` of the fan. -/
def fanHub : FV := 1

/-- The labelled arm `y` of the fan. -/
def fanY : FV := 5

/-- The three fresh arms of the fan. -/
def fanArm : Fin 3 → FV := ![2, 3, 4]

/-- The five cuts of the fan, as the side of the distinguished edge: the cut of the
spine `0–1` (side `{0,5}`), and the pendant cuts at `5`, `2`, `3` and `4`. -/
def fanSide : Fin 5 → FV → Bool :=
  ![![true, false, false, false, false, true],
    ![false, false, false, false, false, true],
    ![false, false, true, false, false, false],
    ![false, false, false, true, false, false],
    ![false, false, false, false, true, false]]

/-- The distinguished edge of each of the five cuts. -/
def fanCutEdge : Fin 5 → Sym2 FV := ![s(0, 1), s(0, 5), s(1, 2), s(1, 3), s(1, 4)]

/-- The six fork requirements of `Q3.forkReq` written as an explicit list of vertex
pairs, in the same slot order. -/
def fanPair (a b : FV) (u v : Fin 2 → FV) : Fin 6 → FV × FV :=
  ![(0, a), (a, u 0), (a, u 1), (0, b), (b, v 0), (b, v 1)]

/-- The number of the six fork requirements that cut `c` separates. -/
def fanCnt (c : Fin 5) (a b : FV) (u v : Fin 2 → FV) : ℕ :=
  ∑ i : Fin 6,
    if fanSide c (fanPair a b u v i).1 ≠ fanSide c (fanPair a b u v i).2 then 1 else 0

/-- The total cut separation of the six fork requirements: a lower bound for the
number of edges in any family of pairwise edge-disjoint witnesses. -/
def fanSep (a b : FV) (u v : Fin 2 → FV) : ℕ :=
  ∑ c : Fin 5, fanCnt c a b u v

/-- The five single-edge witnesses of the spine–hub family on the fan: the spine
`0–1`, the arm edge `0–5`, and the three hub legs `1–2`, `1–3`, `1–4`. -/
def fanSpineHubW : Fin 5 → Finset (Sym2 FV) :=
  ![{s(0, 1)}, {s(0, 5)}, {s(1, 2)}, {s(1, 3)}, {s(1, 4)}]

end Q3

end PercLib.CriticalLRP.I417Fresh
