/- Integrated from independently rebuilt Ultramath work.
Production base 37c0efc68ae8ef365d8d155bc931fd784fdfde2b.
Scratch source: ../../.ultramath/smwvnrt0i/m3/M3Defs.lean.
-/

module

public import PercLib.CriticalLRP.Correlation.I417.Fresh.Main
public import PercLib.CriticalLRP.Correlation.I417Example.TreeBound

/-!
# The fresh-side `q = 2` chain bound: objects

Source: Tom Hutchcroft, *Critical long-range percolation I: high effective dimension*,
arXiv:2508.18807v1, proof of Lemma I.4.17 (p. 45).  The fresh-copy factor
`∑_{y₁,…,y_q} P(y₁,…,y_q ∈ K̃_y, w on a simple open path from y to {y₁,…,y_q})` is bounded there
by expanding the probability into tree diagrams.  `PercLib.CriticalLRP.I417Fresh` states the
resulting inequality as the named premise `FreshCombBound π q`, with diagram value
`freshCombBound π q y w`, and proves it at `q = 1` (`freshCombBound_holds_one`).  The companion file
`M3Main.lean` proves it at `q = 2` with no hypothesis beyond BK (`π e < 1`).

Objects fixed here (no new mathematical assumption is introduced):

* `finTwoArrowEquiv` — the reindexing `(Fin 2 → V) ≃ V × V`, so that the two labelled fresh arms
  can be summed independently.
* `leafShape` — the right-hand side of the checked three-terminal tree-graph inequality
  `I417Example.threeLeaf_treeGraph` at the fresh hub `w`, with the spine arm `y` and the two
  labelled arms `g 0`, `g 1`: the printed two-level branch-point diagram family, written with
  `tau`.
* `chainPt u v = ![u,v,v]` — the single point of the production chain family at which a whole fresh
  diagram is absorbed.
* `chainTerm2` — the `q = 2` monomial of `freshChainBound`.
* `sTerm1`, `sTerm2`, `sTerm3` — the three `leafShape` summands after the two arms are summed out.
  The point of the split is that `sTerm2 u v = sTerm3 v u` (`M3Main.tsum_sTerm2_eq_sTerm3`), so the
  three shapes are absorbed by one chain point rather than three.

Definitions only in this file; the evaluation lemmas `freshChainBound_two_eq` and
`chainTerm2_chainPt` are the two facts about them that `M3Main` uses.
-/

open MeasureTheory Measure ProbabilityTheory unitInterval
open scoped ENNReal NNReal

set_option linter.unusedSectionVars false

@[expose] public section

namespace PercLib.CriticalLRP.I417Fresh

variable {V : Type*} [Countable V]

/-- The canonical equivalence `(Fin 2 → V) ≃ V × V`, used to sum the two labelled fresh arms
independently. -/
def finTwoArrowEquiv (V : Type*) : (Fin 2 → V) ≃ V × V where
  toFun g := (g 0, g 1)
  invFun p := fun i => if i = 0 then p.1 else p.2
  left_inv g := by
    funext i
    fin_cases i <;> simp
  right_inv p := by
    simp

/-- The three-terminal diagram family of `I417Example.threeLeaf_treeGraph` at the fresh hub `w`,
with the spine arm `y` and the two labelled arms `g 0`, `g 1`. -/
noncomputable def leafShape (π : Sym2 V → unitInterval) (y w : V) (g : Fin 2 → V) : ℝ≥0∞ :=
  (∑' u : V, ∑' v : V,
      tau π w u * tau π u y * tau π u v * tau π v (g 0) * tau π v (g 1)) +
    (∑' u : V, ∑' v : V,
      tau π w v * tau π v u * tau π u y * tau π u (g 0) * tau π v (g 1)) +
      (∑' u : V, ∑' v : V,
        tau π w u * tau π u v * tau π v y * tau π u (g 0) * tau π v (g 1))

/-- The first `leafShape` summand after summing the two arms out. -/
noncomputable def sTerm1 (π : Sym2 V → unitInterval) (y w u v : V) : ℝ≥0∞ :=
  tau π w u * tau π u y * tau π u v * (hubArmSum π v * hubArmSum π v)

/-- The second `leafShape` summand after summing the two arms out. -/
noncomputable def sTerm2 (π : Sym2 V → unitInterval) (y w u v : V) : ℝ≥0∞ :=
  tau π w v * tau π v u * tau π u y * (hubArmSum π u * hubArmSum π v)

/-- The third `leafShape` summand after summing the two arms out.  Swapping the two indices turns
`sTerm2` into `sTerm3`; that is the reason one chain point suffices for all three shapes. -/
noncomputable def sTerm3 (π : Sym2 V → unitInterval) (y w u v : V) : ℝ≥0∞ :=
  tau π w u * tau π u v * tau π v y * (hubArmSum π u * hubArmSum π v)

/-- The special chain point `![u,v,v]` of `Fin 3 → V`. -/
def chainPt (u v : V) : Fin 3 → V := Fin.cons u (Fin.cons v (Fin.cons v Fin.elim0))

/-- The `q = 2` monomial of the production chain family `freshChainBound`: the spine
`w → u 0 → u 1 → u 2` with one arm slot at each of `u 0`, `u 1`, `u 2`. -/
noncomputable def chainTerm2 (π : Sym2 V → unitInterval) (y w : V) (u : Fin 3 → V) : ℝ≥0∞ :=
  (∏ i : Fin 3,
      tau π ((Fin.cons w u : Fin 4 → V) (Fin.castSucc i)) ((Fin.cons w u : Fin 4 → V) i.succ)) *
    (∏ i : Fin 3,
      (hubArmSum π ((Fin.cons w u : Fin 4 → V) i.succ) +
        tau π ((Fin.cons w u : Fin 4 → V) i.succ) y))

/-- **The hub-star form of the fresh-side diagram bound.**  This is `FreshCombBound π q` with the
fresh occurrence `freshMark` replaced by its monotone hull `hubStar`; it is the statement that the
`q`-arm hub diagram sum is dominated by the chain family.  It implies `FreshCombBound π q`
(`M3Main.freshCombBound_of_hubStarChain`) and is proved there at `q = 2`
(`M3Main.hubStarChain_two`); for `q ≥ 3` it is the exact remaining combinatorial content. -/
def HubStarChain (π : Sym2 V → unitInterval) (q : ℕ) : Prop :=
  ∀ y w : V, (∑' g : Fin q → V, (edgeMeasure π) (hubStar y w g)) ≤ freshCombBound π q y w

/-- The chain family at `q = 2` is the sum of `chainTerm2` over the three spine positions. -/
theorem freshChainBound_two_eq (π : Sym2 V → unitInterval) (y w : V) :
    freshChainBound π 2 y w = ∑' u : Fin 3 → V, chainTerm2 π y w u := rfl

/-- **Value of the chain monomial at the spine `w → u → v → v`.**  The two-point factors along the
spine are `τ(w,u)`, `τ(u,v)`, `τ(v,v) = 1`, and the three arm slots are read at `u`, `v`, `v`. -/
theorem chainTerm2_chainPt (π : Sym2 V → unitInterval) (y w u v : V) :
    chainTerm2 π y w (chainPt u v) = tau π w u * tau π u v * tau π v v *
      ((hubArmSum π u + tau π u y) * (hubArmSum π v + tau π v y) *
        (hubArmSum π v + tau π v y)) := by
  simp only [chainTerm2, Fin.prod_univ_three, chainPt]
  rfl

end PercLib.CriticalLRP.I417Fresh
