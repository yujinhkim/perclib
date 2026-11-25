/- Integrated from reviewed Ultramath root-pair work.
Production base 1eaaabcf41deb59c0da2c83d0f2d7ad9d952510f.
Scratch source output: ../../.ultramath/smwvlmbqa/m3/Defs.lean.
-/

module

public import PercLib.CriticalLRP.Correlation.SixPoint.MixedK2.Chain

/-!
# Root-in-joint-pair `p = 5`, `k = 2` diagrams

Hutchcroft's proof of Lemma I.4.16 pairs, at each distinguished hub of the binary tree, one
arm towards the root side with one free arm, and leaves the third arm as a single two-point
factor (his `p = 3` example pairs the root itself with a leaf: `{0 ↔ x, w}`).

The production fan `HubK2.hubStar` and chain `HubK2.hubChain` instead keep the root in a
*separate* two-point arm at the first hub.  That choice is fatal for the pointwise event
bound: in nearest-neighbour percolation (`tau x y = p ^ |x-y|`, `jointP a b c = p ^ span`),
every diagram with normaliser `(E|K|^2)^2 (E|K|)^3` that keeps the root out of both joint
pairs has arm cost at least `6` at the six consecutive positions `0,1,2,3,4,5`, while the
five-point connection event there costs exactly `5`.  Feeding the root into the first joint
pair removes exactly one unit of cost.

`hubChainRoot` is that corrected shape: joint pair `(o, a)` at `c1`, single arm `b – c1`,
joint pair `(d, e)` at `c2`, spine arm `c1 – c2`, single arm `f – c2`.  It is a tree on the
six terminals `o,a,b,d,e,f` plus the two hubs, hence `7` arms, and it still evaluates to
`(E|K|^2)^2 (E|K|)^3` (see `Main.lean`): the arm `tau(b,c1)` sums to the susceptibility, the
pair `(d,e)` at `c2` to the second moment, the spine telescopes, and the remaining
`sum_c1 sum_a jointP o a c1` is the native second moment (`tsum_jointP_centre'`).
-/

open Set MeasureTheory
open scoped ENNReal BigOperators
open PercLib.Percolation.Bond
open PercLib.Probability

@[expose] public section

namespace PercLib.CriticalLRP.TreeExpansion.HubRoot

open PercLib.CriticalLRP.TreeExpansion.FivePoint

variable {V : Type*}

/-- **Root-in-pair chain integrand.**  Joint pair `(o,a)` and single arm `b` at `c1`, joint
pair `(d,e)` at `c2`, spine arm `c1 – c2`, single arm `f` at `c2`. -/
noncomputable def hubChainRoot (π : Sym2 V → unitInterval) (o a b d e f c1 c2 : V) : ℝ≥0∞ :=
  (jointP π o a c1 * tau π b c1) * (jointP π d e c2 * tau π c1 c2) * tau π f c2

/-- The root-in-pair chain slot diagram for a leaf labelling `σ`. -/
noncomputable def slotChainRoot (π : Sym2 V → unitInterval) (σ : Equiv.Perm (Fin 5)) (o : V)
    (L : Fin 5 → V) : ℝ≥0∞ :=
  ∑' c1, ∑' c2,
    hubChainRoot π o (L (σ 0)) (L (σ 1)) (L (σ 2)) (L (σ 3)) (L (σ 4)) c1 c2

end PercLib.CriticalLRP.TreeExpansion.HubRoot


/-! ## Integer arm-cost vocabulary -/

namespace PercLib.CriticalLRP.TreeExpansion.HubRoot.Obstruction

/-- Cost of a two-point arm between integer positions. -/
def zdist (a b : ℤ) : ℤ := max a b - min a b

/-- Cost of a joint pair: the span of the two leaves and the hub. -/
def zspan3 (a b c : ℤ) : ℤ := max a (max b c) - min a (min b c)

/-- Cost of two joint pairs measured from hubs `c` and `d` (leaves `a b` and `c d`). -/
def zspan4 (a b c d : ℤ) : ℤ := max (max a b) (max c d) - min (min a b) (min c d)


end PercLib.CriticalLRP.TreeExpansion.HubRoot.Obstruction
