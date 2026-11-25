/- Integrated from independently rebuilt Ultramath work.
Production base 545744b3e9550f31ac4373c2b1bb2f9134b2f93c.
Scratch source: repository-root .ultramath/smwvrtsxf/m2/Defs.lean.
-/
module

public import PercLib.CriticalLRP.Correlation.I417.Fresh.Two.Main

/-!
# The chain-spider cover of the four-arm fresh-side hub event: objects

Source: Tom Hutchcroft, *Critical long-range percolation I: High effective dimension*,
arXiv:2508.18807v1, Lemma I.4.17 (p. 45) and its proof.

Production (`PercLib.CriticalLRP.I417Fresh`) states the fresh-side inequality of Lemma I.4.17 as the
named premise `FreshCombBound π q`, whose diagram value `freshCombBound π q y w` is the sum of the
**chain family** `freshChainBound π q y w` and `firstHubBound π q y w`.  Both are sums of monomials
of one fixed shape: a *spine walk* `w = v 0 → v 1 → … → v (q+1)` of `q+1` steps starting at the
mark `w`, with the `q+1` two-point factors along the walk and one **arm slot**
`χ(v i) + τ(v i, y)` at each spine vertex `v i`.  At `q = 3` that is four spine steps and four
slots.  `freshCombBound_holds_one` and `freshCombBound_two` are proved by covering the hub event
configuration by configuration with the disjoint occurrence of exactly this monomial's connection
events, which is what lets the van den Berg–Kesten inequality produce the monomial.

The objects of this file describe that shape: the `2 (q+1)` connection requirements of the spine
walk and the legs (`ChainSpider`), and the number of double-star cuts that separate them
(`chainSep`, and the cut-by-cut count `chainSepC`).  The companion file `Main.lean` shows that this
shape is **not** a cover of the four-arm hub event.

Definitions only in this file.
-/

open MeasureTheory Measure ProbabilityTheory unitInterval
open scoped ENNReal NNReal

set_option linter.unusedSectionVars false

@[expose] public section

namespace PercLib.CriticalLRP.I417Fresh

/-- The seven vertices of the double star, as `Fin 7`: `0` is the hub, `1` and `2` are the two
branch points, `3`, `4` hang off `1` and `5`, `6` hang off `2`.  Vertex `6` is the terminal that
the spine is attached to. -/
abbrev DSV : Type := Fin 7

/-- The four terminals of the four-arm hub event in the double star. -/
def dsArm : Fin 4 → DSV := ![3, 4, 5, 6]

/-- The six edges of the double star. -/
def dsE : Finset (Sym2 DSV) :=
  {s(0, 1), s(0, 2), s(1, 3), s(1, 4), s(2, 5), s(2, 6)}

/-- The `b₁`-side of the first cut: `{1,3,4}`. -/
def dsS0 : DSV → Bool := ![false, true, false, true, true, false, false]

/-- The `b₂`-side of the second cut: `{2,5,6}`. -/
def dsS1 : DSV → Bool := ![false, false, true, false, false, true, true]

/-- The pendant side of the cut at the terminal `3`. -/
def dsS2 : DSV → Bool := ![false, false, false, true, false, false, false]

/-- The pendant side of the cut at the terminal `4`. -/
def dsS3 : DSV → Bool := ![false, false, false, false, true, false, false]

/-- The pendant side of the cut at the terminal `5`. -/
def dsS4 : DSV → Bool := ![false, false, false, false, false, true, false]

/-- The pendant side of the cut at the terminal `6`. -/
def dsS5 : DSV → Bool := ![false, false, false, false, false, false, true]

/-- The six cuts of the double star, as sides. -/
def dsSide : Fin 6 → DSV → Bool := ![dsS0, dsS1, dsS2, dsS3, dsS4, dsS5]

/-- The distinguished edge of each cut: the unique edge of the double star whose endpoints lie
on different sides. -/
def dsCutEdge : Fin 6 → Sym2 DSV := ![s(0, 1), s(0, 2), s(1, 3), s(1, 4), s(2, 5), s(2, 6)]

/-- The number of the six cuts separating `a` and `b`.  This is the graph distance in the double
star, and it is the number of edges that any witness for `a ↔ b` must contain. -/
def nsep (a b : DSV) : ℕ := ∑ c : Fin 6, if dsSide c a ≠ dsSide c b then 1 else 0

/-- The same count written out cut by cut; this is the form that `Main.chainSepX_ge_seven_perm`
evaluates. -/
def nsepC (a b : DSV) : ℕ :=
  (if dsS0 a ≠ dsS0 b then 1 else 0) + (if dsS1 a ≠ dsS1 b then 1 else 0)
    + (if dsS2 a ≠ dsS2 b then 1 else 0) + (if dsS3 a ≠ dsS3 b then 1 else 0)
    + (if dsS4 a ≠ dsS4 b then 1 else 0) + (if dsS5 a ≠ dsS5 b then 1 else 0)

/-- The spine-walk vertices *before* each of the four steps: `![w, u 0, u 1, u 2]`. -/
def spineSrc (w : DSV) (u : Fin 4 → DSV) : Fin 4 → DSV := ![w, u 0, u 1, u 2]

/-- The spine-walk vertices *after* each of the four steps: `![u 0, u 1, u 2, u 3]`. -/
def spineTgt (u : Fin 4 → DSV) : Fin 4 → DSV := ![u 0, u 1, u 2, u 3]

/-- The total separation count of a chain shape: the four spine steps plus the four legs, each leg
joining the slot `u i` to the terminal `z i`.  This is a lower bound for the number of edges in any
family of pairwise edge-disjoint witnesses of the eight connections. -/
def chainSep (w : DSV) (u z : Fin 4 → DSV) : ℕ :=
  (∑ i : Fin 4, nsep (spineSrc w u i) (spineTgt u i)) + ∑ i : Fin 4, nsep (u i) (z i)

/-- The separation count of a chain shape written out requirement by requirement. -/
def chainSepX (w : DSV) (u z : Fin 4 → DSV) : ℕ :=
  nsepC w (u 0) + nsepC (u 0) (u 1) + nsepC (u 1) (u 2) + nsepC (u 2) (u 3)
    + nsepC (u 0) (z 0) + nsepC (u 1) (z 1) + nsepC (u 2) (z 2) + nsepC (u 3) (z 3)

/-- The number of separated spine requirements of cut `c`. -/
def cntS (c : Fin 6) (w : DSV) (u : Fin 4 → DSV) : ℕ :=
  ∑ i : Fin 4, if dsSide c (spineSrc w u i) ≠ dsSide c (spineTgt u i) then 1 else 0

/-- The number of separated leg requirements of cut `c`. -/
def cntL (c : Fin 6) (u z : Fin 4 → DSV) : ℕ :=
  ∑ i : Fin 4, if dsSide c (u i) ≠ dsSide c (z i) then 1 else 0

/-- The cut-by-cut separation count of a chain shape: each of the six cuts contributes the number
of the eight requirements that it separates. -/
def chainSepC (w : DSV) (u z : Fin 4 → DSV) : ℕ :=
  (cntS 0 w u + cntL 0 u z) + (cntS 1 w u + cntL 1 u z) + (cntS 2 w u + cntL 2 u z)
    + (cntS 3 w u + cntL 3 u z) + (cntS 4 w u + cntL 4 u z) + (cntS 5 w u + cntL 5 u z)

/-- Reindex a slot assignment by the position of its terminal in `dsArm`.
For a slot outside the four terminals this returns `3`; the reindexing identities are used only
with the explicit terminal-range hypothesis. -/
def dsSlot (z : Fin 4 → DSV) (i : Fin 4) : Fin 4 :=
  if z i = 3 then 0 else if z i = 4 then 1 else if z i = 5 then 2 else 3

/-- **A chain spider**: pairwise edge-disjoint witnesses, inside `ω`, for the four spine steps of
the walk `w → u 0 → u 1 → u 2 → u 3` and for the four legs joining the slots `u i` to the terminals
`z i`.  This is exactly the configuration pattern whose BK bound is the chain monomial
`freshChainBound π 3 y w` at the spine vector `u`, with the slot `u i` hosting `z i`; the two
witness families are kept separate so that the legs can use the `χ`-slots of the monomial. -/
def ChainSpider (ω : Config DSV) (w : DSV) (u z : Fin 4 → DSV) : Prop :=
  ∃ S L : Fin 4 → Finset (Sym2 DSV),
    (∀ i, (S i : Set (Sym2 DSV)) ⊆ ω) ∧ (∀ i, (L i : Set (Sym2 DSV)) ⊆ ω) ∧
      (∀ i, Connects (S i : Config DSV) (spineSrc w u i) (spineTgt u i)) ∧
        (∀ i, Connects (L i : Config DSV) (u i) (z i)) ∧
          (∀ i j, i ≠ j → Disjoint (S i) (S j)) ∧
            (∀ i j, Disjoint (S i) (L j)) ∧ (∀ i j, i ≠ j → Disjoint (L i) (L j))

end PercLib.CriticalLRP.I417Fresh
