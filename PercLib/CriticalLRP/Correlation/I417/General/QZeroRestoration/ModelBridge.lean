/-
Copyright (c) 2026 PercLib contributors. Released under Apache 2.0.

Accepted from Ultramath `smwzg77c3`, member `m8`, independently rebuilt.
Production integration based on commit `81c6038182e9a883ffcd3d870aed7cd4829649d4`.
Original direction d8.

# The Case-3 numerator as the printed `p = 2`, `q = 1` instance of Lemma I.4.17

Source: Tom Hutchcroft, *Critical long-range percolation I: High effective dimension*,
arXiv:2508.18807v1, Lemma I.4.17 (p. 45–46), printed `p = 2`, `q = 1` display

```
E|K|² E|K| − E[|K_x|² |K_y| 1(x ↮ y)]  ≤  T³(x,y) (E|K|)⁴ + 2 T⁴(x,y) (E|K|)³ .
```

`Main.lean` proves that the `q = 0` star moment `E[|K_x|^p |K̃_y|^q 1(y ∈ K_x)]` of the restoration
coupling is the star itself for **every** `p, q`, in particular at `(p,q) = (2,1)`.  This file
translates that identity into the production vocabulary of the cutoff law:

* `connCubeVertexMass_eq_restoredConn` — the Case-3 per-vertex numerator
  `E_{β_c,r}[|K_0|³ 1(y ∈ K_0)]` **is** `restoredConn (M.cutProb r) 0 y 2 1`;
* `connCubeVertexMass_add_rawDiff_eq` — the additive source-shape identity
  `connCubeVertexMass r y + I417A.rawDiff (M.cutProb r) 0 y 2 1 = E_{β_c,r}[|K_0|² |K_y|]`
  (a *joint* moment in one copy, not a product of moments);
* `connCubeVertexMass_le_twoTerm_of_source_two_one` — the transport: the printed `(2,1)` two-term
  estimate, in `ℝ≥0∞` and in the model's own matrix powers, yields the per-vertex target with the
  printed constants `C₃ = 1` and `C₄ = 2`.

The residual hypothesis of the last theorem is the still-open source tree-diagram estimate at
`(p,q) = (2,1)` — a *non-degenerate* instance (`q = 1 ≥ 1`), so the marked covering of
`I417Gen.prodSet_subset` applies and the `q = 0` degeneracy recorded by
`I417Gen.prodSet_not_subset_q_zero` is not involved.

One care about the printed shape: the printed left-hand side writes the *product* `E|K|^p E|K|^q`,
while the object that the star equals (`restoredTotal_eq_jointMoment`) is the *joint* moment
`∫ |K_x|^p |K_y|^q` in a single copy.  The two differ by the covariance of `|K_x|^p` and `|K_y|^q`,
which is exactly the resampling step the repository already records as unjustified for the raw
coupling.  The theorems here therefore use the restored/joint total, which is the reading under
which the `(2,1)` instance *is* the target.

No `sorry`, no `admit`, no `native_decide`, no custom axioms.
-/
module

public import PercLib.CriticalLRP.Correlation.I417.General.QZeroRestoration.Main
public import PercLib.CriticalLRP.Correlation.I417.General.QZeroStar.Main
public import PercLib.CriticalLRP.Analysis.Polygon.Bridge
public import PercLib.CriticalLRP.VolumeMoments.HigherMoments.I420Case3.CutPoly.Defs

/-! # Model-level form of the identification -/

noncomputable section

open MeasureTheory Measure ProbabilityTheory unitInterval
open scoped ENNReal NNReal

set_option linter.unusedSectionVars false

@[expose] public section

namespace PercLib.CriticalLRP.I417Gen

attribute [local instance] Classical.propDecidable

variable {V : Type*} [Countable V]

/-- The concrete indicator of the cluster at `y` equals the indicator of the event `y ∈ K_x`. -/
theorem cluster_indicator_eq_set_indicator (x y : V) (ω : Config V) :
    (cluster ω x).indicator (fun _ => (1 : ℝ≥0∞)) y =
      {ω' : Config V | y ∈ cluster ω' x}.indicator (fun _ => (1 : ℝ≥0∞)) ω := by
  by_cases h : y ∈ cluster ω x <;> simp [h]

/-- **The additive source-shape identity at `(p,q) = (2,1)`**:
`starMoment π x y 3 + E[1(y∉K_x)|K_x|²|K_y|] = E[|K_x|²|K_y|]`.

The right-hand side is a *joint* moment in one copy.  The printed `(2,1)` display instead writes the
product `E|K|² E|K|`; the two differ by the covariance of `|K_x|²` and `|K_y|`, which is exactly the
resampling step the repository records as not justified for the raw coupling. -/
theorem starMoment_three_add_rawDiff_two_one (π : Sym2 V → unitInterval) (x y : V) :
    starMoment π x y 3 + I417A.rawDiff π x y 2 1
      = ∫⁻ ω, Percolation.cardFun (cluster ω x) ^ 2 *
          Percolation.cardFun (cluster ω y) ∂(edgeMeasure π) := by
  have hF : Measurable fun ω : Config V =>
      Percolation.cardFun (cluster ω x) ^ 2 * Percolation.cardFun (cluster ω y) := by
    refine Measurable.mul ?_ ?_
    · simpa only [cluster_idBondGraph] using
        (Percolation.measurable_cardFun_cluster (idBondGraph V) x).pow_const 2
    · simpa only [cluster_idBondGraph] using
        Percolation.measurable_cardFun_cluster (idBondGraph V) y
  rw [starMoment_three_eq_jointMoment, I417A.rawDiff, I417A.notConnSet_eq]
  simp only [pow_one]
  rw [show (∫⁻ ω, {ω' : Config V | y ∉ cluster ω' x}.indicator (fun _ => (1 : ℝ≥0∞)) ω *
        (Percolation.cardFun (cluster ω x) ^ 2 * Percolation.cardFun (cluster ω y))
        ∂(edgeMeasure π))
      = ∫⁻ ω in {ω' : Config V | y ∈ cluster ω' x}ᶜ,
          (Percolation.cardFun (cluster ω x) ^ 2 * Percolation.cardFun (cluster ω y))
          ∂(edgeMeasure π) from
    lintegral_indicator_one_mul (measurableSet_cluster_mem x y).compl _]
  rw [show (∫⁻ ω, (cluster ω x).indicator (fun _ => (1 : ℝ≥0∞)) y *
        (Percolation.cardFun (cluster ω x) ^ 2 * Percolation.cardFun (cluster ω y))
        ∂(edgeMeasure π))
      = ∫⁻ ω in {ω' : Config V | y ∈ cluster ω' x},
          (Percolation.cardFun (cluster ω x) ^ 2 * Percolation.cardFun (cluster ω y))
          ∂(edgeMeasure π) from by
    rw [← lintegral_indicator_one_mul (measurableSet_cluster_mem x y) (fun ω =>
      Percolation.cardFun (cluster ω x) ^ 2 * Percolation.cardFun (cluster ω y))]
    exact lintegral_congr fun ω => by rw [cluster_indicator_eq_set_indicator]]
  exact (lintegral_add_compl (μ := edgeMeasure π)
    (f := fun ω => Percolation.cardFun (cluster ω x) ^ 2 *
      Percolation.cardFun (cluster ω y)) (measurableSet_cluster_mem x y))

end PercLib.CriticalLRP.I417Gen

namespace PercLib.CriticalLRP.Orchestration.SourceModelData

open PercLib.CriticalLRP.I417Gen
open PercLib.CriticalLRP.KernelPower
open PercLib.CriticalLRP.I418C

variable (M : SourceModelData)

/-- **The Case-3 per-vertex numerator is the printed `p = 2`, `q = 1` connected moment.**
`E_{β_c,r}[|K_0|³ 1(y ∈ K_0)] = ∫∫ 1(y ∈ K_0(ω₁)) |K_0(ω₁)|² |K_y(ω̃)|` in the restoration
coupling `ω̃ = restoreMap 0 (ω₂,ω₁)`. -/
theorem connCubeVertexMass_eq_restoredConn (r : ℝ) (y : M.V) :
    M.connCubeVertexMass r y = restoredConn (M.cutProb r) (0 : M.V) y 2 1 := by
  rw [M.connCubeVertexMass_eq_starMoment r y, ← restoredConn_two_one_eq_starMoment]

/-- **The Case-3 per-vertex numerator plus the excluded moment is the one-copy joint moment**
`E_{β_c,r}[|K_0|² |K_y|]`. -/
theorem connCubeVertexMass_add_rawDiff_eq (r : ℝ) (y : M.V) :
    M.connCubeVertexMass r y + I417A.rawDiff (M.cutProb r) (0 : M.V) y 2 1
      = ∫⁻ ω, Percolation.cardFun (cluster ω (0 : M.V)) ^ 2 *
          Percolation.cardFun (cluster ω y) ∂(M.cutLaw r) := by
  rw [M.connCubeVertexMass_eq_starMoment r y, M.cutLaw_eq_edgeMeasure]
  exact starMoment_three_add_rawDiff_two_one (M.cutProb r) (0 : M.V) y

/-- **Transport of the printed `(2,1)` estimate to the per-vertex Case-3 target.**

If the printed `p = 2`, `q = 1` instance of Lemma I.4.17 holds in the model's own matrix powers,
`E[|K_0|³ 1(y∈K_0)] ≤ T³(0,y) χ⁴ + 2 T⁴(0,y) χ³` with `T^ℓ = Kpow M.cutTwoPointE ℓ 0 y` and
`χ = M.cutMassAt r 0`, then the per-vertex target holds with the printed constants
`C₃ = 1`, `C₄ = 2`, in the `I418C.polyK`/`I420Case3.cutPoly` vocabulary and in `ℝ`. -/
theorem connCubeVertexMass_le_twoTerm_of_source_two_one (r : ℝ)
    (hχ : M.cutMassAt r 0 ≠ ⊤)
    (hsrc : ∀ y : M.V, restoredConn (M.cutProb r) (0 : M.V) y 2 1 ≤
      Kpow (M.cutTwoPointE r) 3 0 y * (M.cutMassAt r 0) ^ 4 +
        2 * Kpow (M.cutTwoPointE r) 4 0 y * (M.cutMassAt r 0) ^ 3)
    (y : M.V) :
    (M.connCubeVertexMass r y).toReal ≤
      1 * polyK (M.cutTwoPoint r) 3 0 y * ((M.cutMassAt r 0).toReal) ^ 4 +
        2 * polyK (M.cutTwoPoint r) 4 0 y * ((M.cutMassAt r 0).toReal) ^ 3 := by
  set χ := M.cutMassAt r 0 with hχdef
  have h3 : Kpow (M.cutTwoPointE r) 3 0 y ≠ ⊤ := M.cutKpow_ne_top_of_chi_ne_top r hχ 3 0 y
  have h4 : Kpow (M.cutTwoPointE r) 4 0 y ≠ ⊤ := M.cutKpow_ne_top_of_chi_ne_top r hχ 4 0 y
  have hχ4 : χ ^ 4 ≠ ⊤ := ENNReal.pow_ne_top hχ
  have hχ3 : χ ^ 3 ≠ ⊤ := ENNReal.pow_ne_top hχ
  have hterm3 : Kpow (M.cutTwoPointE r) 3 0 y * χ ^ 4 ≠ ⊤ :=
    ENNReal.mul_ne_top h3 hχ4
  have hterm4 : 2 * Kpow (M.cutTwoPointE r) 4 0 y * χ ^ 3 ≠ ⊤ :=
    ENNReal.mul_ne_top (ENNReal.mul_ne_top (by simp) h4) hχ3
  have hbound : M.connCubeVertexMass r y ≤
      Kpow (M.cutTwoPointE r) 3 0 y * χ ^ 4 + 2 * Kpow (M.cutTwoPointE r) 4 0 y * χ ^ 3 := by
    rw [M.connCubeVertexMass_eq_restoredConn r y]
    exact hsrc y
  have hR : (Kpow (M.cutTwoPointE r) 3 0 y * χ ^ 4 +
      2 * Kpow (M.cutTwoPointE r) 4 0 y * χ ^ 3).toReal
      = polyK (M.cutTwoPoint r) 3 0 y * ((M.cutMassAt r 0).toReal) ^ 4 +
        2 * polyK (M.cutTwoPoint r) 4 0 y * ((M.cutMassAt r 0).toReal) ^ 3 := by
    rw [ENNReal.toReal_add hterm3 hterm4, ENNReal.toReal_mul, ENNReal.toReal_mul,
      ENNReal.toReal_mul, ENNReal.toReal_pow, ENNReal.toReal_pow,
      M.cutKpow_toReal_eq_polyK r hχ 3 0 y, M.cutKpow_toReal_eq_polyK r hχ 4 0 y]
    simp only [ENNReal.toReal_ofNat]
    ring
  calc (M.connCubeVertexMass r y).toReal
      ≤ (Kpow (M.cutTwoPointE r) 3 0 y * χ ^ 4 +
          2 * Kpow (M.cutTwoPointE r) 4 0 y * χ ^ 3).toReal :=
        ENNReal.toReal_mono (ENNReal.add_ne_top.mpr ⟨hterm3, hterm4⟩) hbound
    _ = polyK (M.cutTwoPoint r) 3 0 y * ((M.cutMassAt r 0).toReal) ^ 4 +
          2 * polyK (M.cutTwoPoint r) 4 0 y * ((M.cutMassAt r 0).toReal) ^ 3 := hR
    _ = 1 * polyK (M.cutTwoPoint r) 3 0 y * ((M.cutMassAt r 0).toReal) ^ 4 +
          2 * polyK (M.cutTwoPoint r) 4 0 y * ((M.cutMassAt r 0).toReal) ^ 3 := by
        ring

/-- **The Case-3 numerator as a sum of restored two-copy connected moments**:
`E_{β_c,r}[|K_0|³ |K_0 ∩ B_r|] = ∑_{y ∈ B_r} ∫∫ 1(y ∈ K_0(ω₁)) |K_0(ω₁)|² |K_y(ω̃)|`. -/
theorem connCubeMass_eq_sum_restoredConn (r : ℝ) :
    M.connCubeMass r = ∑ y ∈ E1Sign.ballF M r, restoredConn (M.cutProb r) (0 : M.V) y 2 1 := by
  rw [M.connCubeMass_eq_sum_starMoment r]
  exact Finset.sum_congr rfl fun y _ => by
    rw [← restoredConn_two_one_eq_starMoment]

/-- **The per-vertex target in the natural `ℝ≥0∞` parent (`I420Case3.cutPoly`) from the printed
`(2,1)` estimate**: if the `(2,1)` instance bounds the restored connected moment by
`cutPoly 3 · χ⁴ + 2 · cutPoly 4 · χ³` then the Case-3 per-vertex numerator satisfies the same bound,
with the printed constants `C₃ = 1`, `C₄ = 2` and no real-valued conversion needed. -/
theorem connCubeVertexMass_le_cutPoly_twoTerm_of_source_two_one (r : ℝ)
    (hsrc : ∀ y : M.V, restoredConn (M.cutProb r) (0 : M.V) y 2 1 ≤
      I420Case3.cutPoly M r y 3 * (M.cutMassAt r 0) ^ 4 +
        2 * I420Case3.cutPoly M r y 4 * (M.cutMassAt r 0) ^ 3)
    (y : M.V) :
    M.connCubeVertexMass r y ≤
      1 * I420Case3.cutPoly M r y 3 * (M.cutMassAt r 0) ^ 4 +
        2 * I420Case3.cutPoly M r y 4 * (M.cutMassAt r 0) ^ 3 := by
  rw [M.connCubeVertexMass_eq_restoredConn r y]
  simpa only [one_mul] using hsrc y

end PercLib.CriticalLRP.Orchestration.SourceModelData
