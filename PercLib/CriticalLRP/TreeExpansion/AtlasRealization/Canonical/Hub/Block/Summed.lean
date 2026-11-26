/-
Independently reviewed and integrated from the partial artifact
`.ultramath/smwx6p0op/m3/HubEval`. Production integration revision:
`57e71d7ca447d7d83bfa761bb296fde27f6eb970`. This is a concrete one-shape
hub evaluation, not a general mixed-moment theorem.
-/
/-
The summed one-hub block of `t3`: exact leaf-sum evaluation, the summed atlas bound, and the
pinned-hub block evaluation.

Independently built for swarm `smwx6p0op`, member `m3`, direction HUB-EVALUATED-BLOCK.

Source: T. Hutchcroft, *Critical long-range percolation I: High effective dimension*,
arXiv:2508.18807v1, proof of Lemma I.4.16 (pp. 44--45) and Lemma I.4.17 (pp. 45--46).

## What is summed, and what "evaluated" means here

The block of `Assembly.lean` is a function of the shape's positions.  Of the five positions of
`t3` -- the root leaf `c`, the hub's position `φ hubI`, the other internal position `φ innerI`, and
the three labelled leaf positions `z0, z1, z2` -- the block's *hub pair* has `c` and `φ innerI` as
its two points, and the three raw arms end at `z2`, `z0`, `z1`.  So the only positions at which the
block is a product of independent factors are the three leaf positions, and those are exactly what
the source's tree-graph expansion sums over its labelled leaves.

* `tsum_hubBlockValue` -- **the exact value of the leaf-summed block**: the hub joint value times
  three free arm sums `armSum (φ hubI)`, `armSum (φ innerI)`, `armSum (φ innerI)`.  No hypothesis,
  no inequality: this is the evaluated diagram sum, and it is *not* a per-position majorant.
* `tsum_atlasValue_le_block` -- the summed canonical atlas value at `t3` is at most that value.
* `tsum_atlasValue_le_const` -- under the paper's constant-row-sum hypothesis `χ` the same bound
  reads `joint value * χ³`.
* `pinnedHubPairSum_eq` -- the source's `E|K|^2` slot is exactly the second cluster moment.  It
  needs **both** far ends of a joint pair at a **pinned** hub to be free, which the block at `t3`
  never has: one of its pair points is the root leaf `c`.  The two are different objects and this
  file does not identify them.
* `tsum_tau_mul_pinnedHubPairSum` -- **the weighted, summed one-hub block evaluation**: an incoming
  two-point factor from a pinned vertex `c`, against the pinned-hub block, summed over the hub
  position, evaluates to `armSum c * secondMoment 0` under translation invariance.  That is the
  source's per-hub accounting -- one first-moment factor in, one `E|K|^2` for the block -- and it
  needs translation invariance for the block value to be independent of the hub position.
* `tsum_pinnedHubPairSum_eq_top` -- the honest limitation: without the incoming pinned factor the
  hub position cannot be summed, so the source's "the vertices in the distinguished set are not
  summed over" is a real restriction and not a convention.
-/
module

public import PercLib.CriticalLRP.TreeExpansion.AtlasRealization.Canonical.Hub.Block.Assembly
public import PercLib.CriticalLRP.Correlation.FourthMoment.MixedK2.Transport

/-!
# The summed and evaluated one-hub block of `t3`
-/

@[expose] public section

open MeasureTheory Measure
open scoped ENNReal BigOperators

open PercLib.CriticalLRP (Config connSet edgeMeasure)
open PercLib.CriticalLRP.TreeExpansion.Real (srcPos dstPos childPos)
open PercLib.CriticalLRP.TreeExpansion.FivePoint (jointP secondMoment secondMoment_eq)

set_option autoImplicit false
set_option linter.unusedSectionVars false
set_option linter.unusedFintypeInType false
set_option linter.unusedDecidableInType false

namespace PercLib.CriticalLRP.TreeExpansion.HubEval

variable {V : Type*}

/-! ### The exact value of the leaf-summed block -/

/-- **The block evaluated, in leaf-position form.**  Instantiating `hubBlockValue` at the leaf
assignment `![z0, z1, z2]`: slot `0` ends at `z2`, slots `1` and `2` at `z0` and `z1`. -/
theorem hubBlockValue_leaf [DecidableEq V] [Countable V] (π : Sym2 V → unitInterval)
    (c : V) (φ : t3.IPos → V) (z0 z1 z2 : V) :
    hubBlockValue π ![z0, z1, z2] c φ =
      jointP π c (φ innerI) (φ hubI) *
        (PercLib.Percolation.Bond.tau π (φ hubI) z2 *
          (PercLib.Percolation.Bond.tau π (φ innerI) z0 *
            PercLib.Percolation.Bond.tau π (φ innerI) z1)) :=
  hubBlockValue_eq π _ c φ

/-- A generic evaluation: `J` times an inner product, summed over three independent positions. -/
theorem tsum_tsum_tsum_mul_prod [Countable V] (J : ℝ≥0∞) (P Q : V → ℝ≥0∞) :
    (∑' z0 : V, ∑' z1 : V, ∑' z2 : V, J * (Q z2 * (P z0 * P z1))) =
      J * ((∑' z : V, Q z) * ((∑' z : V, P z) * ∑' z : V, P z)) := by
  have h2 : ∀ z0 z1 : V, (∑' z2 : V, J * (Q z2 * (P z0 * P z1))) =
      J * ((∑' z : V, Q z) * (P z0 * P z1)) := by
    intro z0 z1
    rw [ENNReal.tsum_mul_left, ENNReal.tsum_mul_right]
  have h1 : ∀ z0 : V, (∑' z1 : V, J * ((∑' z : V, Q z) * (P z0 * P z1))) =
      J * ((∑' z : V, Q z) * (P z0 * ∑' z : V, P z)) := by
    intro z0
    rw [ENNReal.tsum_mul_left, ENNReal.tsum_mul_left, ENNReal.tsum_mul_left]
  calc (∑' z0 : V, ∑' z1 : V, ∑' z2 : V, J * (Q z2 * (P z0 * P z1)))
      = ∑' z0 : V, J * ((∑' z : V, Q z) * (P z0 * ∑' z : V, P z)) :=
        tsum_congr fun z0 => (tsum_congr fun z1 => h2 z0 z1).trans (h1 z0)
    _ = J * ((∑' z : V, Q z) * ((∑' z : V, P z) * ∑' z : V, P z)) := by
        rw [ENNReal.tsum_mul_left, ENNReal.tsum_mul_left, ENNReal.tsum_mul_right]

/-- **The leaf-summed block, evaluated exactly.**  The three leaf positions are the only free
positions of the block, so summing them produces one free arm sum per leaf and leaves the hub joint
value in place.  This is an identity, not a majorant. -/
theorem tsum_hubBlockValue [DecidableEq V] [Countable V] (π : Sym2 V → unitInterval) (c : V)
    (φ : t3.IPos → V) :
    (∑' z0 : V, ∑' z1 : V, ∑' z2 : V, hubBlockValue π ![z0, z1, z2] c φ) =
      jointP π c (φ innerI) (φ hubI) *
        (armSum π (φ hubI) * (armSum π (φ innerI) * armSum π (φ innerI))) := by
  have h : (∑' z0 : V, ∑' z1 : V, ∑' z2 : V, hubBlockValue π ![z0, z1, z2] c φ) =
      ∑' z0 : V, ∑' z1 : V, ∑' z2 : V,
        jointP π c (φ innerI) (φ hubI) *
          (PercLib.Percolation.Bond.tau π (φ hubI) z2 *
            (PercLib.Percolation.Bond.tau π (φ innerI) z0 *
              PercLib.Percolation.Bond.tau π (φ innerI) z1)) :=
    tsum_congr fun z0 => tsum_congr fun z1 => tsum_congr fun z2 =>
      hubBlockValue_leaf π c φ z0 z1 z2
  rw [h, tsum_tsum_tsum_mul_prod]
  simp only [armSum]

/-! ### The summed atlas value -/

/-- **The summed canonical atlas value of `t3`, bounded by the evaluated block.**  Summing the
per-position block bound over the three leaf positions and then evaluating with
`tsum_hubBlockValue`. -/
theorem tsum_atlasValue_le_block [DecidableEq V] [Countable V]
    (π : Sym2 V → unitInterval) (hπ : ∀ e, π e < 1) (c : V) (φ : t3.IPos → V) :
    (∑' z0 : V, ∑' z1 : V, ∑' z2 : V,
        edgeMeasure π (CanonAtlas.CanonAtlasEvent ![z0, z1, z2] c t3 φ)) ≤
      jointP π c (φ innerI) (φ hubI) *
        (armSum π (φ hubI) * (armSum π (φ innerI) * armSum π (φ innerI))) :=
  (ENNReal.tsum_le_tsum fun _ =>
      ENNReal.tsum_le_tsum fun _ =>
        ENNReal.tsum_le_tsum fun _ =>
          edgeMeasure_canonAtlasEvent_le_hubBlock π hπ _ c φ).trans
    (le_of_eq (tsum_hubBlockValue π c φ))

/-- The free arm sum is the paper's constant `χ` under the constant-row-sum hypothesis. -/
theorem armSum_eq_of_const_rowSum [Countable V] (π : Sym2 V → unitInterval) (χ : ℝ≥0∞)
    (hχ : ∀ v : V, ∑' y : V, edgeMeasure π (connSet v y) = χ) (a : V) :
    armSum π a = χ := by
  rw [armSum]
  refine (tsum_congr fun z => ?_).trans (hχ a)
  exact HubJointEval.edgeMeasure_connSet_eq_tau π a z

/-- **The summed atlas value at the paper's normalisation**: one hub joint value times `χ` for
each of the three summed leaf positions.  `χ³` is `2p - 1 - 3k` two-point factors plus the third
arm of the hub, all of which are two-point factors in the block of `t3`; the hub's own two merged
arms stay inside the joint value and are never split into two-point factors. -/
theorem tsum_atlasValue_le_const [DecidableEq V] [Countable V] (π : Sym2 V → unitInterval)
    (hπ : ∀ e, π e < 1) (χ : ℝ≥0∞)
    (hχ : ∀ v : V, ∑' y : V, edgeMeasure π (connSet v y) = χ) (c : V) (φ : t3.IPos → V) :
    (∑' z0 : V, ∑' z1 : V, ∑' z2 : V,
        edgeMeasure π (CanonAtlas.CanonAtlasEvent ![z0, z1, z2] c t3 φ)) ≤
      jointP π c (φ innerI) (φ hubI) * (χ * (χ * χ)) := by
  refine (tsum_atlasValue_le_block π hπ c φ).trans (le_of_eq ?_)
  rw [armSum_eq_of_const_rowSum π χ hχ, armSum_eq_of_const_rowSum π χ hχ]

/-! ### The source's `E|K|^2` slot, and the weighted summed block -/

/-- **The source's hub slot is the second cluster moment.**  Both far ends of a joint pair at a
*pinned* hub, summed, give exactly `E|K|^2` at that hub (production `secondMoment_eq`).  This is a
different object from `hubBlockValue`, whose joint pair has the root leaf `c` as its first point. -/
theorem pinnedHubPairSum_eq [Countable V] (π : Sym2 V → unitInterval) (a : V) :
    pinnedHubPairSum π a = secondMoment π a :=
  (secondMoment_eq π a).symm

/-- **The weighted, summed one-hub block evaluation.**  A pinned incoming two-point factor
`τ(c, a)` against the pinned-hub block `E|K|^2` at `a`, summed over the hub position, is one first
moment times one second moment.

The only hypothesis is translation invariance of `π`, and it is used exactly once: to make the
block value independent of the hub position (`secondMoment_root_independent`).  Without it the sum
is not a product of moments. -/
theorem tsum_tau_mul_pinnedHubPairSum [Countable V] [AddCommGroup V]
    (π : Sym2 V → unitInterval) (hq : ∀ x y g : V, π s(x + g, y + g) = π s(x, y)) (c : V) :
    (∑' a : V, PercLib.Percolation.Bond.tau π c a * pinnedHubPairSum π a) =
      armSum π c * secondMoment π 0 := by
  have hconst : ∀ a : V, pinnedHubPairSum π a = secondMoment π 0 := by
    intro a
    rw [pinnedHubPairSum_eq]
    exact PercLib.CriticalLRP.TreeExpansion.FivePoint.secondMoment_root_independent π hq a
  calc (∑' a : V, PercLib.Percolation.Bond.tau π c a * pinnedHubPairSum π a)
      = ∑' a : V, PercLib.Percolation.Bond.tau π c a * secondMoment π 0 :=
        tsum_congr fun a => by rw [hconst a]
    _ = armSum π c * secondMoment π 0 := by
        rw [armSum, ENNReal.tsum_mul_right]

/-- The pinned-hub block is at least `1`: the two far ends may coincide with the hub. -/
theorem one_le_pinnedHubPairSum [Countable V] (π : Sym2 V → unitInterval) (a : V) :
    1 ≤ pinnedHubPairSum π a := by
  have hdiag : jointP π a a a = 1 := by
    simp [jointP, PercLib.Percolation.Bond.conn_self]
  calc (1 : ℝ≥0∞) = jointP π a a a := hdiag.symm
    _ ≤ (∑' w : V, jointP π a w a) := ENNReal.le_tsum (f := fun w => jointP π a w a) a
    _ ≤ pinnedHubPairSum π a :=
        ENNReal.le_tsum (f := fun u => ∑' w : V, jointP π u w a) a

/-- **The hub position cannot be freed.**  The sum of the pinned-hub block over the hub position
diverges on any infinite vertex group with translation invariance, because every term is the same
second moment and it is at least `1`.  Thus this unweighted hub-position sum does not recover
the source's moment evaluation: an incoming factor or another attachment is required, as in
`tsum_tau_mul_pinnedHubPairSum`.  No complete moment recovery is asserted here. -/
theorem tsum_pinnedHubPairSum_eq_top [Countable V] [Infinite V] [AddCommGroup V]
    (π : Sym2 V → unitInterval) (hq : ∀ x y g : V, π s(x + g, y + g) = π s(x, y)) :
    (∑' a : V, pinnedHubPairSum π a) = ⊤ := by
  have hconst : ∀ a : V, pinnedHubPairSum π a = secondMoment π 0 := by
    intro a
    rw [pinnedHubPairSum_eq]
    exact PercLib.CriticalLRP.TreeExpansion.FivePoint.secondMoment_root_independent π hq a
  rw [tsum_congr hconst]
  refine ENNReal.tsum_const_eq_top_of_ne_zero ?_
  intro h0
  have h1 := one_le_pinnedHubPairSum π (0 : V)
  rw [hconst 0, h0] at h1
  exact absurd h1 (by simp)

end PercLib.CriticalLRP.TreeExpansion.HubEval
