/-
Ultramath swarm `smwxh86dl`, member `m1`, direction d1
(`MISSING-SPLIT-ROOT-EVALUATIONS`).

Definitions only: the `p = 5`, `k = 2` two-joint/three-single slot diagrams at every split
position `j : Fin 7`, for the two root roles used by the `Fin 15` pattern family
(`FivePoint.pat k 0 = 0` and `FivePoint.pat k 2 = 0`).

The diagram at split position `j` is the product of the five `k = 2` groups supplied by the
event-level regroupings: two joint groups `jointP π x y z` (two connections to a shared spine
target `z`, i.e. the two legs and the spine of one three-star) and three single two-point
groups `tau π x y` (the three residual edges of the split tree).

The star set and spine choice at each `j` is the one of the production certificates
(`SplitPattern.combSystem_twoJointThree_zero/five/six`, and at `j = 2` the production
`TwoJointThree.combSystem_twoJointThree`): the star set `{u, w}` at `j = 0,1,2,3,4`,
`{u, v}` at `j = 5` and `{u, c}` at `j = 6`, with the spine pointing into the tree.

The two internal vertices appearing in the product are `i₁` and `i₂`; at `j = 0..4` they are
the shared spine target `v = i₁` and the landing point `c = i₂`, at `j = 5` they are the
landing point `c = i₁` and `w = i₂`, at `j = 6` they are `v = i₁` and `w = i₂`.

`slotProd2` is the product only.  The root-pinned sums over the seven free vertices appear in
the evaluation theorems at the end of this file, each in a peel order; any other order of the
same seven free vertices is the same extended sum (`ENNReal.tsum_comm`, compare
`TwoJointEval.tsum_seven_perm`), so the order carries no mathematical content.

For each fixed root socket the seven free vertices are peeled so that every factor is summed
exactly once:

* a joint group `jointP x y v` with `v` free and one leg held gives `E|K|²`
  (`tsum_jointP_centre`), and with both legs free and the centre held it also gives `E|K|²`
  (`secondMoment_eq` at the held centre, then `secondMoment_root_independent`);
* a two-point group `tau x y` with one endpoint held gives `E|K|` (`tau_row` / `tau_col`).

The only hypothesis is the full profile invariance
`hq : ∀ x y g, π s(x + g, y + g) = π s(x, y)`; no independence and no moment finiteness.
-/
module

public import PercLib.CriticalLRP.Correlation.SixPoint.TwoJointEval.Eval
public import PercLib.CriticalLRP.Correlation.SixPoint.SplitPattern.Regroup

/-!
# The `k = 2` five-group products at all seven split positions

The `slotProd2` family, with two completed `j = 0` evaluations below.
The remaining split/root evaluations are not asserted here.
-/

open Set MeasureTheory
open scoped ENNReal BigOperators
open PercLib.Percolation.Bond
open PercLib.CriticalLRP.TreeExpansion.FivePoint

@[expose] public section

namespace PercLib.CriticalLRP.SixPoint.SplitEval2

variable {V : Type*}

/-- **The `k = 2` five-group product at split position `j`.**  Two joint groups and three
two-point groups in the positions of the production certificates; `i₁`, `i₂` are the two
internal vertices appearing in the product (see the module docstring for which is which). -/
noncomputable def slotProd2 (π : Sym2 V → unitInterval) (j : Fin 7)
    (i₁ i₂ b0 b1 b2 b3 b4 t : V) : ℝ≥0∞ :=
  match j with
  /- `j = 0`: `c` on the arm `b₀ — u`; stars `{b₁, c, v}` at `u`, `{b₃, b₄, v}` at `w`. -/
  | 0 => jointP π b1 i₂ i₁ * (jointP π b3 b4 i₁ * (tau π b2 i₁ * (tau π t i₂ * tau π b0 i₂)))
  /- `j = 1`: mirror of `j = 0` under `b₀ ↔ b₁`. -/
  | 1 => jointP π b0 i₂ i₁ * (jointP π b3 b4 i₁ * (tau π b2 i₁ * (tau π b1 i₂ * tau π t i₂)))
  /- `j = 2`: the production middle split; stars `{b₀, b₁, v}` at `u`, `{b₃, b₄, v}` at `w`. -/
  | 2 => jointP π b0 b1 i₁ * (jointP π b3 b4 i₁ * (tau π b2 i₂ * (tau π i₁ i₂ * tau π t i₂)))
  /- `j = 3`: `c` on the arm `b₃ — w`; stars `{b₀, b₁, v}` at `u`, `{b₄, c, v}` at `w`. -/
  | 3 => jointP π b0 b1 i₁ * (jointP π b4 i₂ i₁ * (tau π b2 i₁ * (tau π b3 i₂ * tau π t i₂)))
  /- `j = 4`: mirror of `j = 3` under `b₃ ↔ b₄`. -/
  | 4 => jointP π b0 b1 i₁ * (jointP π b3 i₂ i₁ * (tau π b2 i₁ * (tau π b4 i₂ * tau π t i₂)))
  /- `j = 5`: `c` on the spine `u — v`; stars `{b₀, b₁, c}` at `u`, `{b₂, c, w}` at `v`. -/
  | 5 => jointP π b0 b1 i₁ * (jointP π b2 i₁ i₂ * (tau π b3 i₂ * (tau π b4 i₂ * tau π t i₁)))
  /- `j = 6`: `c` on the spine `v — w`; stars `{b₀, b₁, v}` at `u`, `{v, t, w}` at `c`. -/
  | 6 => jointP π b0 b1 i₁ * (jointP π i₁ t i₂ * (tau π b2 i₁ * (tau π b3 i₂ * tau π b4 i₂)))

/-! ## Split position `0` -/

/-- **`j = 0`, root in comb slot `0`.**  The star at `u` contributes the joint group
`(b₁, c) @ v`, the star at `w` the joint group `(b₃, b₄) @ v`, and the residual edges are
`b₂ — v`, `t — c`, `b₀ — c`.  Peel order `{b₃,b₄}`, `b₂`, `{v,b₁}`, `t`, `c`. -/
theorem slotU2_zero_tsum [Countable V] [AddCommGroup V] (π : Sym2 V → unitInterval)
    (hq : ∀ x y g : V, π s(x + g, y + g) = π s(x, y)) (b0 : V) :
    (∑' c, ∑' t, ∑' v, ∑' b1, ∑' b2, ∑' b3, ∑' b4,
        slotProd2 π 0 v c b0 b1 b2 b3 b4 t) =
      (secondMoment π 0) ^ 2 * (∑' x, tau π 0 x) ^ 3 := by
  classical
  simp only [slotProd2]
  -- step 1: `{b₃, b₄}` at the free spine target `v` is a second moment
  have h1 : ∀ (c t v b1 b2 : V),
      (∑' b3, ∑' b4, jointP π b1 c v * (jointP π b3 b4 v *
          (tau π b2 v * (tau π t c * tau π b0 c)))) =
        jointP π b1 c v * (tau π b2 v * (tau π t c * tau π b0 c)) *
          secondMoment π 0 := by
    intro c t v b1 b2
    have k : ∀ (b3 b4 : V),
        jointP π b1 c v * (jointP π b3 b4 v * (tau π b2 v * (tau π t c * tau π b0 c))) =
          (jointP π b1 c v * (tau π b2 v * (tau π t c * tau π b0 c))) *
            jointP π b3 b4 v := fun b3 b4 => by ring
    simp only [k, ENNReal.tsum_mul_left]
    rw [show (∑' b3, ∑' b4, jointP π b3 b4 v) = secondMoment π v from
      (secondMoment_eq π v).symm]
    rw [secondMoment_root_independent π hq v]
  -- step 2: `b₂` is a first moment
  have h2 : ∀ (c t v b1 : V),
      (∑' b2, jointP π b1 c v * (tau π b2 v * (tau π t c * tau π b0 c)) *
          secondMoment π 0) =
        jointP π b1 c v * ((tau π t c * tau π b0 c) * secondMoment π 0) *
          (∑' x, tau π 0 x) := by
    intro c t v b1
    have k : ∀ b2 : V,
        jointP π b1 c v * (tau π b2 v * (tau π t c * tau π b0 c)) * secondMoment π 0 =
          (jointP π b1 c v * ((tau π t c * tau π b0 c) * secondMoment π 0)) *
            tau π b2 v := fun b2 => by ring
    simp only [k, ENNReal.tsum_mul_left]
    rw [tau_col π hq v]
  -- step 3: `{v, b₁}` with the held leg `c` is a second moment
  have h3 : ∀ (c t : V),
      (∑' v, ∑' b1, jointP π b1 c v * ((tau π t c * tau π b0 c) * secondMoment π 0) *
          (∑' x, tau π 0 x)) =
        (tau π t c * tau π b0 c) * secondMoment π 0 * (∑' x, tau π 0 x) *
          secondMoment π 0 := by
    intro c t
    have k : ∀ (v b1 : V),
        jointP π b1 c v * ((tau π t c * tau π b0 c) * secondMoment π 0) *
            (∑' x, tau π 0 x) =
          ((tau π t c * tau π b0 c) * secondMoment π 0 * (∑' x, tau π 0 x)) *
            jointP π c b1 v := fun v b1 => by rw [jointP_comm π b1 c v]; ring
    simp only [k, ENNReal.tsum_mul_left]
    rw [tsum_jointP_centre π hq c]
  -- step 4: `t` is a first moment
  have h4 : ∀ c : V,
      (∑' t, (tau π t c * tau π b0 c) * secondMoment π 0 * (∑' x, tau π 0 x) *
          secondMoment π 0) =
        tau π b0 c * secondMoment π 0 * (∑' x, tau π 0 x) * secondMoment π 0 *
          (∑' x, tau π 0 x) := by
    intro c
    have k : ∀ t : V,
        (tau π t c * tau π b0 c) * secondMoment π 0 * (∑' x, tau π 0 x) *
            secondMoment π 0 =
          (tau π b0 c * secondMoment π 0 * (∑' x, tau π 0 x) * secondMoment π 0) *
            tau π t c := fun t => by ring
    simp only [k, ENNReal.tsum_mul_left]
    rw [tau_col π hq c]
  -- step 5: `c` is the last first moment
  have h5 : (∑' c, tau π b0 c * secondMoment π 0 * (∑' x, tau π 0 x) *
      secondMoment π 0 * (∑' x, tau π 0 x)) =
      (secondMoment π 0) ^ 2 * (∑' x, tau π 0 x) ^ 3 := by
    have k : ∀ c : V,
        tau π b0 c * secondMoment π 0 * (∑' x, tau π 0 x) * secondMoment π 0 *
            (∑' x, tau π 0 x) =
          (secondMoment π 0 * (∑' x, tau π 0 x) * secondMoment π 0 *
            (∑' x, tau π 0 x)) * tau π b0 c := fun c => by ring
    simp only [k, ENNReal.tsum_mul_left]
    rw [tau_row π hq b0]
    ring
  refine (tsum_congr fun c => tsum_congr fun t => tsum_congr fun v => tsum_congr fun b1 =>
    tsum_congr fun b2 => h1 c t v b1 b2).trans ?_
  refine (tsum_congr fun c => tsum_congr fun t => tsum_congr fun v => tsum_congr fun b1 =>
    h2 c t v b1).trans ?_
  refine (tsum_congr fun c => tsum_congr fun t => h3 c t).trans ?_
  refine (tsum_congr fun c => h4 c).trans ?_
  exact h5

/-- **`j = 0`, root in comb slot `2`.**  Same diagram, the root `b₂` held and `b₀` summed.
Peel order `{b₃,b₄}`, `b₀`, `t`, `{b₁,c}`, `v`. -/
theorem slotV2_zero_tsum [Countable V] [AddCommGroup V] (π : Sym2 V → unitInterval)
    (hq : ∀ x y g : V, π s(x + g, y + g) = π s(x, y)) (b2 : V) :
    (∑' v, ∑' c, ∑' b1, ∑' t, ∑' b0, ∑' b3, ∑' b4,
        slotProd2 π 0 v c b0 b1 b2 b3 b4 t) =
      (secondMoment π 0) ^ 2 * (∑' x, tau π 0 x) ^ 3 := by
  classical
  simp only [slotProd2]
  have h1 : ∀ (v c b1 t b0 : V),
      (∑' b3, ∑' b4, jointP π b1 c v * (jointP π b3 b4 v *
          (tau π b2 v * (tau π t c * tau π b0 c)))) =
        jointP π b1 c v * (tau π b2 v * (tau π t c * tau π b0 c)) *
          secondMoment π 0 := by
    intro v c b1 t b0
    have k : ∀ (b3 b4 : V),
        jointP π b1 c v * (jointP π b3 b4 v * (tau π b2 v * (tau π t c * tau π b0 c))) =
          (jointP π b1 c v * (tau π b2 v * (tau π t c * tau π b0 c))) *
            jointP π b3 b4 v := fun b3 b4 => by ring
    simp only [k, ENNReal.tsum_mul_left]
    rw [show (∑' b3, ∑' b4, jointP π b3 b4 v) = secondMoment π v from
      (secondMoment_eq π v).symm]
    rw [secondMoment_root_independent π hq v]
  have h2 : ∀ (v c b1 t : V),
      (∑' b0, jointP π b1 c v * (tau π b2 v * (tau π t c * tau π b0 c)) *
          secondMoment π 0) =
        jointP π b1 c v * (tau π b2 v * (tau π t c * secondMoment π 0)) *
          (∑' x, tau π 0 x) := by
    intro v c b1 t
    have k : ∀ b0 : V,
        jointP π b1 c v * (tau π b2 v * (tau π t c * tau π b0 c)) * secondMoment π 0 =
          (jointP π b1 c v * (tau π b2 v * (tau π t c * secondMoment π 0))) *
            tau π b0 c := fun b0 => by ring
    simp only [k, ENNReal.tsum_mul_left]
    rw [tau_col π hq c]
  have h3 : ∀ (v c b1 : V),
      (∑' t, jointP π b1 c v * (tau π b2 v * (tau π t c * secondMoment π 0)) *
          (∑' x, tau π 0 x)) =
        jointP π b1 c v * (tau π b2 v * secondMoment π 0) * (∑' x, tau π 0 x) *
          (∑' x, tau π 0 x) := by
    intro v c b1
    have k : ∀ t : V,
        jointP π b1 c v * (tau π b2 v * (tau π t c * secondMoment π 0)) *
            (∑' x, tau π 0 x) =
          (jointP π b1 c v * (tau π b2 v * secondMoment π 0) *
            (∑' x, tau π 0 x)) * tau π t c := fun t => by ring
    simp only [k, ENNReal.tsum_mul_left]
    rw [tau_col π hq c]
  have h4 : ∀ (v : V),
      (∑' c, ∑' b1, jointP π b1 c v * (tau π b2 v * secondMoment π 0) *
          (∑' x, tau π 0 x) * (∑' x, tau π 0 x)) =
        tau π b2 v * secondMoment π 0 * (∑' x, tau π 0 x) * (∑' x, tau π 0 x) *
          secondMoment π 0 := by
    intro v
    have k : ∀ (c b1 : V),
        jointP π b1 c v * (tau π b2 v * secondMoment π 0) * (∑' x, tau π 0 x) *
            (∑' x, tau π 0 x) =
          (tau π b2 v * secondMoment π 0 * (∑' x, tau π 0 x) * (∑' x, tau π 0 x)) *
            jointP π b1 c v := fun c b1 => by ring
    simp only [k, ENNReal.tsum_mul_left]
    rw [show (∑' c, ∑' b1, jointP π b1 c v) = secondMoment π v from by
      rw [ENNReal.tsum_comm]
      exact (secondMoment_eq π v).symm]
    rw [secondMoment_root_independent π hq v]
  have h5 : (∑' v, tau π b2 v * secondMoment π 0 * (∑' x, tau π 0 x) *
      (∑' x, tau π 0 x) * secondMoment π 0) =
      (secondMoment π 0) ^ 2 * (∑' x, tau π 0 x) ^ 3 := by
    have k : ∀ v : V,
        tau π b2 v * secondMoment π 0 * (∑' x, tau π 0 x) * (∑' x, tau π 0 x) *
            secondMoment π 0 =
          (secondMoment π 0 * (∑' x, tau π 0 x) * (∑' x, tau π 0 x) *
            secondMoment π 0) * tau π b2 v := fun v => by ring
    simp only [k, ENNReal.tsum_mul_left]
    rw [tau_row π hq b2]
    ring
  refine (tsum_congr fun v => tsum_congr fun c => tsum_congr fun b1 => tsum_congr fun t =>
    tsum_congr fun b0 => h1 v c b1 t b0).trans ?_
  refine (tsum_congr fun v => tsum_congr fun c => tsum_congr fun b1 => tsum_congr fun t =>
    h2 v c b1 t).trans ?_
  refine (tsum_congr fun v => tsum_congr fun c => tsum_congr fun b1 => h3 v c b1).trans ?_
  refine (tsum_congr fun v => h4 v).trans ?_
  exact h5


end PercLib.CriticalLRP.SixPoint.SplitEval2
