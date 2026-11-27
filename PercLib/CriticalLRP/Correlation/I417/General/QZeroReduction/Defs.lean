/-
Accepted from Ultramath `smwzg77c3`, member `m4`, independently rebuilt.
Production integration based on commit `81c6038182e9a883ffcd3d870aed7cd4829649d4`.
Original direction `d4`.

Copyright (c) 2026 PercLib contributors. Released under Apache 2.0.

# Named forms of the `q = 0`, `p = 3` per-vertex tree gap

Hutchcroft, *Critical long-range percolation I*, arXiv:2508.18807v1, Lemma I.4.17
(printed p. 45): for integers `p, q ≥ 0` and vertices `x, y`,

```
0 ≤ E|K|^p E|K|^q − E[|K_x|^p |K_y|^q 1(x ↮ y)]
    ≤ ∑_{ℓ=3}^{p+q+1} C_{p,q,ℓ} T^ℓ(x,y) (E|K|)^{2p+2q+1−ℓ}.
```

At `p = 3`, `q = 0` the left-hand side is the connected star moment
`E[|K_x|³ 1(x ↔ y)]` (`I417Gen.starMoment`, produced exactly by
`I417Gen.rawDiff_add_starMoment`), and the right-hand side has the two terms `ℓ = 3` and `ℓ = 4`:

```
E[|K_0|³ 1(y ∈ K_0)] ≤ C₃ T³(0,y) χ⁴ + C₄ T⁴(0,y) χ³,      χ = E_{β_c,r}|K|.
```

This file names the three statement forms used by the reduction in `Main.lean`:

* `TwoTermTarget` — the source's two-term estimate in the exact real shape consumed by
  `SecondMomentCase3.connCubeMass_toReal_le_of_perVertex_gap` (`F r y = connCubeVertexMass r y`);
* `KpowTwoTerm` — its natural `ℝ≥0∞` parent, using the extended-real matrix power
  `KernelPower.Kpow (M.cutTwoPointE r)` and the `ℝ≥0∞` cut mass `M.cutMassAt r 0`;
* `FourTermTreeBound` — the *labelled-tree* residual: the four `ℓ = 1,2,3,4` classes obtained from
  the tree-graph bound for the four labels `{y, x₁, x₂, x₃}`, each class evaluated at the exact
  degree `ℓ + (4 − ℓ)`.  `Main.hgap_of_treeFour` shows it implies `TwoTermTarget` with explicit
  constants; see the module notes of `Main.lean` for why the `ℓ = 1,2` classes are free.

No theorem is asserted here: this is a definition layer only.
-/
module

public import PercLib.CriticalLRP.Correlation.I417.General.QZeroStar.Main
public import PercLib.CriticalLRP.VolumeMoments.HigherMoments.I420Case3.CutPoly.Defs

/-! # Named statement forms for the `q = 0` star gap -/

noncomputable section

open MeasureTheory Measure ProbabilityTheory unitInterval
open scoped ENNReal NNReal

@[expose] public section

namespace PercLib.CriticalLRP.M4QZero

open PercLib.CriticalLRP Orchestration
open PercLib.CriticalLRP.KernelPower

variable (M : SourceModelData)

/-! ## The source's `χ = E_{β_c,r}|K|` and `T^ℓ(0,y)`, in real form -/

/-- The source's cutoff susceptibility `χ = E_{β_c,r}|K|`, as a real number. -/
noncomputable def chi (r : ℝ) : ℝ := (M.cutMassAt r 0).toReal

/-- The source's `ℓ`-fold polygon power `T^ℓ(0,y) = polyK (cutTwoPoint r) ℓ 0 y` at the origin. -/
noncomputable def Tpow (r : ℝ) (n : ℕ) (y : M.V) : ℝ :=
  I418C.polyK (M.cutTwoPoint r) n (0 : M.V) y

@[simp]
theorem Tpow_def (r : ℝ) (n : ℕ) (y : M.V) :
    Tpow M r n y = I418C.polyK (M.cutTwoPoint r) n (0 : M.V) y := rfl

@[simp]
theorem chi_def (r : ℝ) : chi M r = (M.cutMassAt r 0).toReal := rfl

/-! ## The target -/

/-- **The exact two-term `q = 0` per-vertex tree estimate**, real form.

`(M.connCubeVertexMass r y).toReal = E_{β_c,r}[|K_0|³ 1(y ∈ K_0)]` by
`Orchestration.SourceModelData.connCubeVertexMass_eq_starMoment`, so this is the source's
Lemma I.4.17 at `p = 3`, `q = 0`, per vertex, in the shape consumed by
`SecondMomentCase3.connCubeMass_toReal_le_of_perVertex_gap`. -/
def TwoTermTarget (r : ℝ) (y : M.V) (C3 C4 : ℝ) : Prop :=
  (M.connCubeVertexMass r y).toReal
    ≤ C3 * Tpow M r 3 y * chi M r ^ 4 + C4 * Tpow M r 4 y * chi M r ^ 3

/-- **The two-term estimate at a general root `x`.**  `TwoTermTarget` is the instance `x = 0`;
`Main.twoTermTargetAt_iff` shows this form at any root `x` is *equivalent* to the statement at the
origin for the vertex `y - x`, so nothing is gained or lost by moving the root. -/
def TwoTermTargetAt (r : ℝ) (x y : M.V) (C3 C4 : ℝ) : Prop :=
  (I417Gen.starMoment (M.cutProb r) x y 3).toReal
    ≤ C3 * I418C.polyK (M.cutTwoPoint r) 3 x y * chi M r ^ 4
      + C4 * I418C.polyK (M.cutTwoPoint r) 4 x y * chi M r ^ 3

/-- **The natural `ℝ≥0∞` parent of the target**, in the form a cutoff star-moment estimate
actually produces: the extended-real matrix power `Kpow (cutTwoPointE r)` and the `ℝ≥0∞`
susceptibility `M.cutMassAt r 0`, with `χ⁴ = (cutMassAt r 0)⁴`.  `Main.hgap_of_KpowTwoTerm`
converts it to `TwoTermTarget` with no loss, under the honest finiteness `χ ≠ ⊤`. -/
def KpowTwoTerm (r : ℝ) (y : M.V) (C3 C4 : ℝ) : Prop :=
  I417Gen.starMoment (M.cutProb r) (0 : M.V) y 3
    ≤ ENNReal.ofReal C3 * Kpow (M.cutTwoPointE r) 3 0 y * (M.cutMassAt r 0) ^ 4
      + ENNReal.ofReal C4 * Kpow (M.cutTwoPointE r) 4 0 y * (M.cutMassAt r 0) ^ 3

/-- **The `cutPoly` parent of the target.**  Same statement as `KpowTwoTerm`, with the Case-3
polygon interface `I420Case3.cutPoly M r y j = ofReal (polyK (cutTwoPoint r) j 0 y)` in place of the
extended-real matrix power.  `Main.hgap_of_cutPolyTwoTerm` converts it to `TwoTermTarget`. -/
def CutPolyTwoTerm (r : ℝ) (y : M.V) (C3 C4 : ℝ) : Prop :=
  I417Gen.starMoment (M.cutProb r) (0 : M.V) y 3
    ≤ ENNReal.ofReal C3 * I420Case3.cutPoly M r y 3 * (M.cutMassAt r 0) ^ 4
      + ENNReal.ofReal C4 * I420Case3.cutPoly M r y 4 * (M.cutMassAt r 0) ^ 3

/-- **A strong total-degree-four labelled-tree residual.**

This records the four classes `τ χ³`, `T² χ²`, `T³ χ`, `T⁴`, i.e. total degree `4`, obtained when
every off-path free vertex is charged a single `χ` and none of them is a branch vertex.  It is
*tighter* than the classes the tree-graph bound actually produces (which reach total degree seven,
see `TreeClassesBound`), so it is a strengthening of the residual, not a weakening.
`Main.hgap_of_treeFour` proves that it implies `TwoTermTarget` with constants
`C₃ = A + C`, `C₄ = B + D`, using only `τ ≤ T³`, `T² ≤ T⁴` and `χ ≥ 1`. -/
def FourTermTreeBound (r : ℝ) (y : M.V) (A B C D : ℝ) : Prop :=
  I417Gen.starMoment (M.cutProb r) (0 : M.V) y 3
    ≤ ENNReal.ofReal (A * M.cutTwoPoint r 0 y * chi M r ^ 3
        + B * Tpow M r 2 y * chi M r ^ 2
        + C * Tpow M r 3 y * chi M r
        + D * Tpow M r 4 y)

/-- **The tree-graph classes, excluding the degree-five class.**

Take a reduced tree on the root `0` and the four leaves `y, x₁, x₂, x₃`, with `p` unlabelled
branch vertices and tree distance `ℓ = dist(0,y)`.  It has `4 + p` edges, and evaluating its
`∏ τ` with one row sum `∑_x τ(u,x) ≤ χ` for each of the `4 + p − ℓ` off-path free vertices gives
the class `T^ℓ(0,y) χ^{4+p−ℓ}`.  The possible classes are

* `p = 0`: `T χ³`;
* `p = 1`: `T χ⁴`, `T² χ³`;
* `p = 2`: `T χ⁵`, `T² χ⁴`, `T³ χ³`;
* `p = 3`: `T χ⁶`, `T² χ⁵`, `T³ χ⁴`, `T⁴ χ³`.

Using only `0 ≤ T ≤ T² ≤ T³ ≤ T⁴` and `χ ≥ 1`, every class with `ℓ ≤ 3`, `m ≤ 4` and the class
`T⁴ χ³` absorb into `T³ χ⁴ + T⁴ χ³`; and `T χ⁴ ≤ T² χ⁴`, `T² χ³ ≤ T² χ⁴`.  This `Prop` records
the resulting five-term bound.  The three classes `T χ⁵`, `T χ⁶`, `T² χ⁵` (short `0`–`y` path,
deep off-path subtree) are *not* absorbable — see `Main.deep_class_not_absorbable`.
`Main.hgap_of_treeClasses` proves `TreeClassesBound ⟹ TwoTermTarget` with
`C₃ = A + B + C + D`, `C₄ = E`. -/
def TreeClassesBound (r : ℝ) (y : M.V) (A B C D E : ℝ) : Prop :=
  I417Gen.starMoment (M.cutProb r) (0 : M.V) y 3
    ≤ ENNReal.ofReal (A * M.cutTwoPoint r 0 y * chi M r ^ 3
        + B * Tpow M r 2 y * chi M r ^ 4
        + C * Tpow M r 3 y * chi M r ^ 3
        + D * Tpow M r 3 y * chi M r ^ 4
        + E * Tpow M r 4 y * chi M r ^ 3)

/-- **The single-term residual** `E[|K_0|³ 1(y ∈ K_0)] ≤ A · τ(0,y) · χ⁴`.  This is the
`ℓ = 1` class of the tree-graph bound pushed all the way down to the two-point function; it is
strictly stronger than `TwoTermTarget` (`Main.hgap_of_tauChi`), because `T³(0,y) ≥ τ(0,y)`. -/
def TauChiBound (r : ℝ) (y : M.V) (A : ℝ) : Prop :=
  I417Gen.starMoment (M.cutProb r) (0 : M.V) y 3
    ≤ ENNReal.ofReal (A * M.cutTwoPoint r 0 y * chi M r ^ 4)

end PercLib.CriticalLRP.M4QZero
