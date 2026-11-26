/- Independently rebuilt and integrated findings f3/f4 of swarm `smwwyd7lg`, member `m1`.
Production integration revision: `d2734e7c030f377ae4642466daef7f78ff648cb8`.
The candidate was `.ultramath/smwwyd7lg/m1/ForkQ3/Defs.lean`. -/

module

public import PercLib.CriticalLRP.Correlation.I417.Fresh.Obstruction.Main

/-!
# The `q = 3` fresh side of Lemma I.4.17: the two-hub *fork* family

Source: Tom Hutchcroft, *Critical long-range percolation I: High effective
dimension*, arXiv:2508.18807v1, Lemma I.4.17 (p. 45) and its proof.

Production's fresh side (`PercLib.CriticalLRP.I417Fresh`) bounds the fresh-copy
factor `∑_g P(freshMark y g j w)` by `freshCombBound π q y w`, the sum of a
**chain family** `freshChainBound` (a spine walk `w = v 0 → v 1 → … → v (q+1)`
with one arm slot per spine vertex) and `firstHubBound`.  The `q = 1` and
`q = 2` cases are proved by covering the hub event with the disjoint occurrence
of exactly one chain monomial (`Fresh/Main.lean`, `Fresh/Two/Main.lean`).

At `q = 3` the chain shape cannot cover the four-arm hub event:
`Fresh/Obstruction/Main.ds_no_chainSpider` exhibits the six-edge double star,
in which the four-arm hub event holds but for **every** spine vector `u` and
every injective assignment `z` of the four slots onto the four terminals, the
eight chain requirements have no pairwise edge-disjoint witnesses.

This file fixes the shape the double star *does* admit: the **fork**.  The mark
`w` is joined to two hubs `a` and `b` by two *separate* spines, and each hub
carries two of the four leaves.  In the double star the fork uses all six edges
exactly once, so it is covered there, while no chain is.

Contents (definitions only; theorems are in `ForkQ3/Main.lean`):

* `forkReq`, `forkEvent` — the six connection requirements and their disjoint
  occurrence;
* `forkMono` — the six two-point factors the fork event carries;
* `forkBound` — the two-hub diagram summed over both hubs, with the two
  `b`-legs summed out to `hubArmSum` (one `a`-leg kept as `τ(·,y)`, see
  `Main.fresh_fork_three_le`);
* `dsForkW` — the explicit six single-edge witnesses of the double star;
* `finThreeArrowEquiv` — the reindexing `(Fin 3 → V) ≃ V × V × V` used to sum
  the three arms out.

No analytic hypothesis is introduced anywhere: `tau` is the canonical two-point
function of the infinite product law `edgeMeasure π`, and every statement below
is about that law.
-/

open MeasureTheory Measure ProbabilityTheory unitInterval
open scoped ENNReal NNReal

set_option linter.unusedSectionVars false

@[expose] public section

namespace PercLib.CriticalLRP.I417Fresh

namespace Q3

variable {V : Type*} [Countable V]

/-- **The six connection requirements of the fork**, in slot order: the first
spine `w ↔ a`, the two legs at the hub `a` (`a ↔ u 0`, `a ↔ u 1`), the second
spine `w ↔ b`, and the two legs at the hub `b` (`b ↔ v 0`, `b ↔ v 1`). -/
def forkReq (w a b : V) (u v : Fin 2 → V) : Fin 6 → Set (Config V) :=
  ![connSet w a, connSet a (u 0), connSet a (u 1),
    connSet w b, connSet b (v 0), connSet b (v 1)]

/-- **The fork event**: pairwise edge-disjoint witnesses for the six fork
requirements, all inside the configuration.  This is
`Percolation.DisjointOccurrenceFin` of `forkReq`, so the iterated
van den Berg–Kesten inequality applies to it directly. -/
def forkEvent (w a b : V) (u v : Fin 2 → V) : Set (Config V) :=
  Percolation.DisjointOccurrenceFin (forkReq w a b u v)

/-- The six two-point factors carried by the fork event, in the same slot
order. -/
noncomputable def forkMono (π : Sym2 V → unitInterval) (w a b : V)
    (u v : Fin 2 → V) : ℝ≥0∞ :=
  tau π w a * tau π a (u 0) * tau π a (u 1) * tau π w b * tau π b (v 0) *
    tau π b (v 1)

/-- **The two-hub fork diagram**, summed out: both hubs are summed over, the two
legs at the second hub `b` are summed out to `hubArmSum`.  This is the `q = 3`
fresh side, so three of the four leaves are summed arms and the fourth is the
fixed arm `y`, kept at the first hub `a`. -/
noncomputable def forkBound (π : Sym2 V → unitInterval) (y w : V) : ℝ≥0∞ :=
  ∑' p : V × V,
    tau π w p.1 * tau π p.1 y * hubArmSum π p.1 * tau π w p.2 *
      (hubArmSum π p.2 * hubArmSum π p.2)

/-- The six single-edge witnesses of the fork in the double star of
`Fresh/Obstruction/Defs.lean`: spines `0 → 1` and `0 → 2`, legs `1 → 3`,
`1 → 4`, `2 → 5`, `2 → 6`.  They are six distinct edges of `dsE`, hence
pairwise edge-disjoint. -/
def dsForkW : Fin 6 → Finset (Sym2 DSV) :=
  ![{s(0, 1)}, {s(1, 3)}, {s(1, 4)}, {s(0, 2)}, {s(2, 5)}, {s(2, 6)}]

/-- The canonical equivalence `(Fin 3 → V) ≃ V × V × V`, used to sum the three
fresh arms independently. -/
def finThreeArrowEquiv (V : Type*) : (Fin 3 → V) ≃ V × V × V where
  toFun g := (g 0, g 1, g 2)
  invFun p i := if i = 0 then p.1 else if i = 1 then p.2.1 else p.2.2
  left_inv g := by
    funext i
    fin_cases i <;> simp
  right_inv p := by
    obtain ⟨a, b, c⟩ := p
    simp


/-- The constant spine vector: the mark `w` followed by `q+1` copies of the
single hub `a`, as a function on the `q+2` spine positions. -/
def constSpine (w a : V) (q : ℕ) : Fin (q + 2) → V :=
  Fin.cons w (fun _ : Fin (q + 1) => a)

/-- The `q`-th chain monomial of `freshChainBound`, as a function of the spine
vector `u : Fin (q+1) → V`.  `freshChainBound` is by definition the sum of
`chainTerm` over `u`. -/
noncomputable def chainTerm (π : Sym2 V → unitInterval) (q : ℕ) (y w : V)
    (u : Fin (q + 1) → V) : ℝ≥0∞ :=
  (∏ i : Fin (q + 1), tau π ((Fin.cons w u : Fin (q + 2) → V) (Fin.castSucc i))
      ((Fin.cons w u : Fin (q + 2) → V) i.succ)) *
    (∏ i : Fin (q + 1), (hubArmSum π ((Fin.cons w u : Fin (q + 2) → V) i.succ) +
      tau π ((Fin.cons w u : Fin (q + 2) → V) i.succ) y))

/-- `freshChainBound` is the sum of `chainTerm` over the spine vector. -/
theorem freshChainBound_eq_tsum (π : Sym2 V → unitInterval) (q : ℕ) (y w : V) :
    freshChainBound π q y w = ∑' u : Fin (q + 1) → V, chainTerm π q y w u := rfl


/-! ## The three-star: a configuration the chain covers

The cut data below (`tsS0` … `tsForkSep`) is the counting geometry used in the *numerical* check
that the fork separation count of the three-star is `7` (see `ForkQ3/Incomparable.lean`); the
corresponding finite check is not formalised. -/

/-- The six edges of the **three-star**: the mark `0`, a first hub `1` carrying the three arms
`3`, `4`, `5`, and a second hub `2` carrying the arm `6`.  (Vertex `6` is the marked arm `y` of the
fresh side, `3`, `4`, `5` are the three arms `g 0`, `g 1`, `g 2`.) -/
def tsE : Finset (Sym2 DSV) :=
  {s(0, 1), s(0, 2), s(1, 3), s(1, 4), s(1, 5), s(2, 6)}

/-- The component `{1,3,4,5}` behind the edge `0-1`. -/
def tsS0 : DSV → Bool := ![false, true, false, true, true, true, false]

/-- The component `{2,6}` behind the edge `0-2`. -/
def tsS1 : DSV → Bool := ![false, false, true, false, false, false, true]

/-- The pendant `{3}`. -/
def tsS2 : DSV → Bool := ![false, false, false, true, false, false, false]

/-- The pendant `{4}`. -/
def tsS3 : DSV → Bool := ![false, false, false, false, true, false, false]

/-- The pendant `{5}`. -/
def tsS4 : DSV → Bool := ![false, false, false, false, false, true, false]

/-- The pendant `{6}`. -/
def tsS5 : DSV → Bool := ![false, false, false, false, false, false, true]

/-- The six cuts of the three-star, as the sides containing the pendant part. -/
def tsSide : Fin 6 → DSV → Bool := ![tsS0, tsS1, tsS2, tsS3, tsS4, tsS5]

/-- The distinguished edge of each cut: the unique edge of `tsE` whose endpoints lie on different
sides. -/
def tsCutEdge : Fin 6 → Sym2 DSV :=
  ![s(0, 1), s(0, 2), s(1, 3), s(1, 4), s(1, 5), s(2, 6)]

/-- The number of the six cuts of the three-star separating `a` and `b`; this is the graph distance
in `tsE`. -/
def tsNsep (a b : DSV) : ℕ := ∑ c : Fin 6, if tsSide c a ≠ tsSide c b then 1 else 0

/-- The two endpoints of the `i`-th fork requirement at hubs `a`, `b` and slot assignment `z`, in
slot order: `0 ↔ a`, `a ↔ z 0`, `a ↔ z 1`, `0 ↔ b`, `b ↔ z 2`, `b ↔ z 3`. -/
def tsForkPair (a b : DSV) (z : Fin 4 → DSV) : Fin 6 → DSV × DSV :=
  ![(0, a), (a, z 0), (a, z 1), (0, b), (b, z 2), (b, z 3)]

/-- The total cut-separation count of the six fork requirements: a lower bound for the number of
edges in any family of pairwise edge-disjoint witnesses. -/
def tsForkSep (a b : DSV) (z : Fin 4 → DSV) : ℕ :=
  ∑ i : Fin 6, tsNsep (tsForkPair a b z i).1 (tsForkPair a b z i).2

end Q3

end PercLib.CriticalLRP.I417Fresh

