/-
Ordinary `p = 5`, `k = 0` nine-tau diagram for the six-terminal attachment.

Supplied by Ultramath `smwpv4yqm` member `m2` (direction `d1`, task B).

The six-terminal arm system `CombSystem` of `Attachment/Defs.lean` consists of the seven comb
arms `b₀—u, b₁—u, b₂—v, b₃—w, b₄—w, u—v, v—w` plus the sixth arm `t—c` whose endpoint `c`
lies on arm `j`.  Splitting arm `j` at `c` gives the nine walks of `Attachment.Split.combSystem_nine`,
i.e. the nine edges of the tree on the six terminals `b₀,…,b₄,t` and the four internal points
`c,u,v,w`.  In the **ordinary** (`k = 0`) regrouping each of those nine walks carries one
two-point factor, so the per-shape diagram is a *nine-fold* product of `tau` factors — no joint
pair and no second moment occurs (contrast `Attachment.Basic.slotU`, which keeps one joint pair
for the mixed `k = 1` bound).

The nine edge lists, in the order of `combSystem_nine` (arm `j` is split into its two halves):

| `j` | arm split | the nine edges |
|---|---|---|
| 0 | `b₀—u` | `b₀c, cu, b₁u, b₂v, b₃w, b₄w, uv, vw, tc` |
| 1 | `b₁—u` | `b₀u, b₁c, cu, b₂v, b₃w, b₄w, uv, vw, tc` |
| 2 | `b₂—v` | `b₀u, b₁u, b₂c, cv, b₃w, b₄w, uv, vw, tc` |
| 3 | `b₃—w` | `b₀u, b₁u, b₂v, b₃c, cw, b₄w, uv, vw, tc` |
| 4 | `b₄—w` | `b₀u, b₁u, b₂v, b₃w, b₄c, cw, uv, vw, tc` |
| 5 | `u—v`  | `b₀u, b₁u, b₂v, b₃w, b₄w, uc, cv, vw, tc` |
| 6 | `v—w`  | `b₀u, b₁u, b₂v, b₃w, b₄w, uv, vc, cw, tc` |

`ordProd` is the product of the nine factors, `ordSlotU`/`ordSlotV` sum it over the four
internal points, and `ordD` is the per-`(k, j)` diagram of the fifteen patterns at the root `0`.
The evaluation of the diagram to `(∑' x, tau π 0 x) ^ 9` is in `Eval.lean`/`Main.lean`.
-/
module

public import PercLib.CriticalLRP.Correlation.SixPoint.Attachment.Split
public import PercLib.Probability.CountableBK
public import PercLib.Probability.OpenEventHarris

open Set MeasureTheory
open scoped ENNReal BigOperators
open PercLib.Probability
open PercLib.Percolation.Bond
open PercLib.CriticalLRP.TreeExpansion.FivePoint

@[expose] public section

namespace PercLib.CriticalLRP.TreeExpansion.SixPoint

variable {V : Type*}

/-- **The nine two-point factors of the split six-terminal tree.**  `b₀,…,b₄` are the five comb
terminals, `t` the sixth, `c` the landing point of `t—c` and `u, v, w` the three comb junctions.
Arm `j` is split at `c` into its two halves. -/
noncomputable def ordProd (π : Sym2 V → unitInterval) (j : Fin 7)
    (b0 b1 b2 b3 b4 t c u v w : V) : ℝ≥0∞ :=
  match j with
  | 0 => tau π b0 c * tau π c u * tau π b1 u * tau π b2 v * tau π b3 w * tau π b4 w *
      tau π u v * tau π v w * tau π t c
  | 1 => tau π b0 u * tau π b1 c * tau π c u * tau π b2 v * tau π b3 w * tau π b4 w *
      tau π u v * tau π v w * tau π t c
  | 2 => tau π b0 u * tau π b1 u * tau π b2 c * tau π c v * tau π b3 w * tau π b4 w *
      tau π u v * tau π v w * tau π t c
  | 3 => tau π b0 u * tau π b1 u * tau π b2 v * tau π b3 c * tau π c w * tau π b4 w *
      tau π u v * tau π v w * tau π t c
  | 4 => tau π b0 u * tau π b1 u * tau π b2 v * tau π b3 w * tau π b4 c * tau π c w *
      tau π u v * tau π v w * tau π t c
  | 5 => tau π b0 u * tau π b1 u * tau π b2 v * tau π b3 w * tau π b4 w *
      tau π u c * tau π c v * tau π v w * tau π t c
  | 6 => tau π b0 u * tau π b1 u * tau π b2 v * tau π b3 w * tau π b4 w *
      tau π u v * tau π v c * tau π c w * tau π t c

/-- The per-shape diagram when the root sits in comb slot `0` (pattern case `pat k 0 = 0`):
the root is the terminal `b₀`, the five free terminals are `b₁,b₂,b₃,b₄,t`, and the four
internal points `c,u,v,w` are summed inside the diagram. -/
noncomputable def ordSlotU (π : Sym2 V → unitInterval) (j : Fin 7)
    (root b1 b2 b3 b4 t : V) : ℝ≥0∞ :=
  ∑' c, ∑' u, ∑' v, ∑' w, ordProd π j root b1 b2 b3 b4 t c u v w

/-- The per-shape diagram when the root sits in comb slot `2` (pattern case `pat k 2 = 0`):
the root is the terminal `b₂`, the five free terminals are `b₀,b₁,b₃,b₄,t`. -/
noncomputable def ordSlotV (π : Sym2 V → unitInterval) (j : Fin 7)
    (root b0 b1 b3 b4 t : V) : ℝ≥0∞ :=
  ∑' c, ∑' u, ∑' v, ∑' w, ordProd π j b0 b1 root b3 b4 t c u v w

/-- **The per-`(k, j)` ordinary diagram.**  For the terminal vector `T` the six terminals are
`T 0, …, T 5`; the root `T 0` occupies comb slot `0` when `pat k 0 = 0`; in the
remaining cases `pat k 2 = 0` places it in comb slot `2`.  `ordD` must be the right-hand side of the per-shape BK
bound (`law π (⋃ c u v w, SixShape …) ≤ ordD π k j T`). -/
noncomputable def ordD (π : Sym2 V → unitInterval) (k : Fin 15) (j : Fin 7)
    (T : Fin 6 → V) : ℝ≥0∞ :=
  if PercLib.CriticalLRP.TreeExpansion.FivePoint.pat k 0 = 0 then
    ordSlotU π j (T 0) (T (lift5 (PercLib.CriticalLRP.TreeExpansion.FivePoint.pat k 1)))
      (T (lift5 (PercLib.CriticalLRP.TreeExpansion.FivePoint.pat k 2)))
      (T (lift5 (PercLib.CriticalLRP.TreeExpansion.FivePoint.pat k 3)))
      (T (lift5 (PercLib.CriticalLRP.TreeExpansion.FivePoint.pat k 4))) (T 5)
  else
    ordSlotV π j (T 0) (T (lift5 (PercLib.CriticalLRP.TreeExpansion.FivePoint.pat k 0)))
      (T (lift5 (PercLib.CriticalLRP.TreeExpansion.FivePoint.pat k 1)))
      (T (lift5 (PercLib.CriticalLRP.TreeExpansion.FivePoint.pat k 3)))
      (T (lift5 (PercLib.CriticalLRP.TreeExpansion.FivePoint.pat k 4))) (T 5)

/-! ## Iterated disjoint occurrence of a finite family -/

/-- Iterated disjoint occurrence `((A₀ □ A₁) □ A₂) ⋯` of a `Fin k`-indexed family of events,
with `iterDC 0 = univ`.  This is the `Fin`-indexed form of
`List.foldl disjointOccurrence` used by `countable_profile_bk_foldl`. -/
def iterDC {ι : Type*} : (k : ℕ) → (Fin k → Set (Set ι)) → Set (Set ι)
  | 0, _ => Set.univ
  | (k + 1), A => disjointOccurrence (iterDC k fun i => A i.castSucc) (A (Fin.last k))

/-- The nine-singleton certificate event: nine increasing events with nine pairwise disjoint
finite open certificates.  For the nine endpoint pairs of the split six-terminal arm system this
is the `k = 0` counterpart of `SevenGroupEvent` (which had one joint pair plus six singletons). -/
def NineEvent {ι : Type*} (A : Fin 9 → Set (Set ι)) : Set (Set ι) := iterDC 9 A

/-! ## The nine endpoint pairs of the split six-terminal arm system -/

/-- **The nine endpoint pairs.**  For a comb on slots `b0 … b4, t` with internal vertices
`u, v, w`, a landing point `c` on arm `j : Fin 7`, the nine edges of the split six-leaf tree,
in this order:

* slot `0`: first half of the split arm, `armSrc j — c`;
* slot `1`: second half of the split arm, `c — armTgt j`;
* slots `2 + m`, `m : Fin 6`: the six comb arms other than `j`, enumerated by
  `Fin.succAbove j`;
* slot `8`: the new arm `t — c`. -/
def nineEnds (j : Fin 7) (b0 b1 b2 b3 b4 t u v w c : V) : Fin 9 → V × V
  | ⟨0, _⟩ => (armSrc b0 b1 b2 b3 b4 u v j, c)
  | ⟨1, _⟩ => (c, armTgt u v w j)
  | ⟨2, _⟩ => (armSrc b0 b1 b2 b3 b4 u v (Fin.succAbove j 0),
      armTgt u v w (Fin.succAbove j 0))
  | ⟨3, _⟩ => (armSrc b0 b1 b2 b3 b4 u v (Fin.succAbove j 1),
      armTgt u v w (Fin.succAbove j 1))
  | ⟨4, _⟩ => (armSrc b0 b1 b2 b3 b4 u v (Fin.succAbove j 2),
      armTgt u v w (Fin.succAbove j 2))
  | ⟨5, _⟩ => (armSrc b0 b1 b2 b3 b4 u v (Fin.succAbove j 3),
      armTgt u v w (Fin.succAbove j 3))
  | ⟨6, _⟩ => (armSrc b0 b1 b2 b3 b4 u v (Fin.succAbove j 4),
      armTgt u v w (Fin.succAbove j 4))
  | ⟨7, _⟩ => (armSrc b0 b1 b2 b3 b4 u v (Fin.succAbove j 5),
      armTgt u v w (Fin.succAbove j 5))
  | ⟨8, _⟩ => (t, c)

/-- **The nine walks.**  Given the seven comb arms, the new arm `Q : t — c` and the two halves
`A`, `B` of arm `j`, this packages the nine walks with the endpoints prescribed by `nineEnds`. -/
def nineWalks {G : SimpleGraph V} {b0 b1 b2 b3 b4 t u v w c : V} {j : Fin 7}
    (p0 : G.Walk b0 u) (p1 : G.Walk b1 u) (p2 : G.Walk b2 v) (p3 : G.Walk b3 w)
    (p4 : G.Walk b4 w) (s1 : G.Walk u v) (s2 : G.Walk v w) (Q : G.Walk t c)
    (A : G.Walk (armSrc b0 b1 b2 b3 b4 u v j) c) (B : G.Walk c (armTgt u v w j)) :
    (i : Fin 9) → G.Walk (nineEnds j b0 b1 b2 b3 b4 t u v w c i).1
      (nineEnds j b0 b1 b2 b3 b4 t u v w c i).2
  | ⟨0, _⟩ => A
  | ⟨1, _⟩ => B
  | ⟨2, _⟩ => combFam p0 p1 p2 p3 p4 s1 s2 (Fin.succAbove j 0)
  | ⟨3, _⟩ => combFam p0 p1 p2 p3 p4 s1 s2 (Fin.succAbove j 1)
  | ⟨4, _⟩ => combFam p0 p1 p2 p3 p4 s1 s2 (Fin.succAbove j 2)
  | ⟨5, _⟩ => combFam p0 p1 p2 p3 p4 s1 s2 (Fin.succAbove j 3)
  | ⟨6, _⟩ => combFam p0 p1 p2 p3 p4 s1 s2 (Fin.succAbove j 4)
  | ⟨7, _⟩ => combFam p0 p1 p2 p3 p4 s1 s2 (Fin.succAbove j 5)
  | ⟨8, _⟩ => Q

/-- **The nine-tau diagram.**  The product of the two-point functions on the nine endpoint
pairs of the split six-terminal arm system.  This is the right-hand side of the per-shape
`k = 0` BK bound; it has nine factors and no `jointP` group. -/
noncomputable def nineDiag (π : Sym2 V → unitInterval) (j : Fin 7)
    (b0 b1 b2 b3 b4 t u v w c : V) : ℝ≥0∞ :=
  ∏ i : Fin 9, tau π (nineEnds j b0 b1 b2 b3 b4 t u v w c i).1
    (nineEnds j b0 b1 b2 b3 b4 t u v w c i).2

/-- The nine-tau diagram of the `k`-th six-terminal shape: the terminals `T 0, …, T 5` are
substituted into the comb slots exactly as in `SixShape`. -/
noncomputable def nineShapeDiag (π : Sym2 V → unitInterval) (T : Fin 6 → V) (k : Fin 15)
    (j : Fin 7) (c u v w : V) : ℝ≥0∞ :=
  nineDiag π j (T (lift5 (pat k 0))) (T (lift5 (pat k 1))) (T (lift5 (pat k 2)))
    (T (lift5 (pat k 3))) (T (lift5 (pat k 4))) (T 5) u v w c


/-! ## The nine connection events -/

/-- The nine connection events of the split six-terminal arm system, indexed so that slot `i`
corresponds to the endpoints `nineEnds … i` of the walk `nineWalks … i`.  For the ordinary
(`k = 0`) regrouping these nine events are the ones that enter the nine-singleton BK bound. -/
def nineConns (j : Fin 7) (b0 b1 b2 b3 b4 t u v w c : V) : Fin 9 → Set (Config V) :=
  fun i => conn (nineEnds j b0 b1 b2 b3 b4 t u v w c i).1
    (nineEnds j b0 b1 b2 b3 b4 t u v w c i).2

/-- The per-`(k, j)` chunk of the ordinary (`k = 0`) nine-tau bound: the four internal vertices
`c, u, v, w` summed out at the terminal vector `T`.  This is the `D k j y z w q r` of the consumer
interface (`sixPoint_le_sixShapeChunk`), and it has nine factors, no joint pair and no
second-moment factor. -/
noncomputable def nineShapeChunk (π : Sym2 V → unitInterval) (T : Fin 6 → V) (k : Fin 15)
    (j : Fin 7) : ℝ≥0∞ :=
  ∑' c : V, ∑' u : V, ∑' v : V, ∑' w : V, nineShapeDiag π T k j c u v w

end PercLib.CriticalLRP.TreeExpansion.SixPoint
