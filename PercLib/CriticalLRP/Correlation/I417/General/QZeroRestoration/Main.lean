/-
Copyright (c) 2026 PercLib contributors. Released under Apache 2.0.

Accepted from Ultramath `smwzg77c3`, member `m8`, independently rebuilt.
Production integration based on commit `81c6038182e9a883ffcd3d870aed7cd4829649d4`.
Original direction d8.

# The `q = 0` connected star moment *is* the restored two-copy moment at `(p,q) = (2,1)`

Source: Tom Hutchcroft, *Critical long-range percolation I: High effective dimension*,
arXiv:2508.18807v1, Lemma I.4.17 (printed p. 45–46) together with its `p = 2`, `q = 1` display

```
E|K|² E|K| − E[|K_x|² |K_y| 1(x ↮ y)]  ≤  T³(x,y) (E|K|)⁴ + 2 T⁴(x,y) (E|K|)³ .
```

## The point of this file

The Case-3 numerator of Proposition I.4.15 is the `q = 0` star moment
`E[|K_0|³ 1(y ∈ K_0)]` (`connCubeVertexMass_eq_starMoment`).  The pinned target is

```
starMoment ≤ C₃ T³(0,y) χ⁴ + C₄ T⁴(0,y) χ³ ,   χ = E|K| .
```

`QZeroStar/Main.lean` records that the printed *covering* step of Lemma I.4.17 degenerates at
`q = 0` (`prodSet_not_subset_q_zero`): with an empty target set there is no path on the fresh copy,
so the marked vertex `w` does not exist and the general marked expansion cannot be specialised.
That obstruction is about the printed *expansion*, not about the star.

The identity below says the star is not a one-copy object that needs that expansion at all: in the
restoration coupling of the printed proof it is *exactly* the connected part of the two-copy moment
of Lemma I.4.17 at **`(p,q) = (2,1)`** — or, equivalently, at `(1,2)`: for every `p, q`,

```
starMoment π x y (p+q)  =  ∫∫ 1(y ∈ K_x(ω₁)) |K_x(ω₁)|^p |K̃_y(ω)|^q .
```

The reason is deterministic and sharp.  On the event `y ∈ K_x(ω₁)` the restored configuration `ω̃`
agrees with `ω₁` on every edge touching `K_x(ω₁)`, so `K_x(ω̃) = K_x(ω₁)`; since `y` lies in that
cluster, also `K_y(ω̃) = K_x(ω₁)`.  Hence `|K̃_y| = |K_x(ω₁)|` on the event, and the `p` and `q`
powers recombine into `|K_x|^{p+q}`.

Consequences recorded here:

* `restoredConn_eq_starMoment` — the identification, all `p, q`;
* `restoredConn_two_one_eq_starMoment`, `restoredConn_one_two_eq_starMoment` — the two instances of
  total degree three, both non-degenerate (`q ≥ 1`), whose printed right-hand sides are
  `T³χ⁴ + 2T⁴χ³` and hence carry *exactly* the two powers of the target;
* `starMoment_three_eq_jointMoment` — the same identity in one-copy form,
  `starMoment π x y 3 = ∫ 1(y∈K_x) |K_x|² |K_y|`, which exhibits the star as the printed `(2,1)`
  left-hand side `E[|K_x|²|K_y|] − E[1(y∉K_x)|K_x|²|K_y|]` when the *one-copy* joint moment is used;
* `restoredTotal_eq_jointMoment` — the restored two-copy total equals the one-copy joint moment
  `∫ |K_x|^p |K_y|^q` (law preservation of the restoration map), which is precisely the step at
  which the printed proof replaces a joint moment by a product of moments;
* `restoredDiag_eq_rawDiff` — the restored excluded part is the landed one-copy `I417A.rawDiff`,
  so the only difference between the printed LHS and the star is the product-versus-joint step.

No `sorry`, no `admit`, no `native_decide`, no custom axioms.  The definitions are in `Defs.lean`.
-/
module

public import PercLib.CriticalLRP.Correlation.I417.General.QZeroRestoration.Defs

/-! # The star moment as a restored two-copy moment -/

noncomputable section

open MeasureTheory Measure ProbabilityTheory unitInterval
open scoped ENNReal NNReal

set_option linter.unusedSectionVars false

@[expose] public section

namespace PercLib.CriticalLRP.I417Gen

attribute [local instance] Classical.propDecidable

variable {V : Type*} [Countable V]

/-! ## The deterministic cluster identity of the restoration coupling -/

/-- **The restored configuration has the base cluster of `x`**: `K_x(ω̃) = K_x(ω₁)` for
`ω̃ = restoreMap x (ω₂,ω₁)`.  This is `cluster_forceOn_compl_touchSet` unfolded. -/
theorem cluster_restoreMap_self (ρ : Config V × Config V) (x : V) :
    cluster (restoreMap x ρ) x = cluster ρ.2 x :=
  cluster_forceOn_compl_touchSet ρ.1 ρ.2 x

/-- A vertex of the cluster of `o` has the cluster of `o` as its own cluster. -/
theorem cluster_eq_of_mem_cluster_star {ω : Config V} {o y : V} (hy : y ∈ cluster ω o) :
    cluster ω y = cluster ω o :=
  cluster_eq_iff.mpr (connects_symm (mem_cluster_iff.mp hy))

/-- **On `{y ∈ K_x(ω₁)}` the restored cluster of `y` is the base cluster of `x`.**  This is the
pointwise content of the source's identity
`E[|K_x|^p|K̃_y|^q 1(y∈K_x)] = E[|K_x|^{p+q} 1(y∈K_x)]`. -/
theorem cluster_restoreMap_eq_of_mem {ρ : Config V × Config V} {x y : V}
    (hy : y ∈ cluster ρ.2 x) :
    cluster (restoreMap x ρ) y = cluster ρ.2 x := by
  have hy' : y ∈ cluster (restoreMap x ρ) x := by
    rw [cluster_restoreMap_self ρ x]; exact hy
  rw [cluster_eq_of_mem_cluster_star hy', cluster_restoreMap_self ρ x]

/-! ## Measurability of the two integrands -/

theorem measurable_starIntegrand (x y : V) (n : ℕ) :
    Measurable fun ω : Config V =>
      (cluster ω x).indicator (fun _ => (1 : ℝ≥0∞)) y *
        Percolation.cardFun (cluster ω x) ^ n := by
  refine Measurable.mul ?_ ?_
  · exact measurable_const.indicator (measurableSet_cluster_mem x y)
  · simpa only [cluster_idBondGraph] using
      (Percolation.measurable_cardFun_cluster (idBondGraph V) x).pow_const n

theorem measurable_cardFun_restoreMap (x y : V) (q : ℕ) :
    Measurable fun ρ : Config V × Config V =>
      Percolation.cardFun (cluster (restoreMap x ρ) y) ^ q := by
  have hbase : Measurable fun ρ : Config V × Config V =>
      Percolation.cardFun (cluster (restoreMap x ρ) y) := by
    have h := (Percolation.measurable_cardFun_cluster (idBondGraph V) y).comp
      (measurable_restoreMap x)
    simpa only [cluster_idBondGraph, Function.comp_def] using h
  exact hbase.pow_const q

theorem measurable_cardFun_snd (x : V) (p : ℕ) :
    Measurable fun ρ : Config V × Config V => Percolation.cardFun (cluster ρ.2 x) ^ p := by
  have hbase : Measurable fun ρ : Config V × Config V =>
      Percolation.cardFun (cluster ρ.2 x) := by
    have h := (Percolation.measurable_cardFun_cluster (idBondGraph V) x).comp
      (measurable_snd : Measurable (Prod.snd : Config V × Config V → Config V))
    simpa only [cluster_idBondGraph, Function.comp_def] using h
  exact hbase.pow_const p

theorem measurable_cardFun_indicator_snd (x y : V) (p : ℕ) :
    Measurable fun ρ : Config V × Config V =>
      (cluster ρ.2 x).indicator (fun _ => (1 : ℝ≥0∞)) y *
        Percolation.cardFun (cluster ρ.2 x) ^ p := by
  refine Measurable.mul ?_ (measurable_cardFun_snd x p)
  exact measurable_const.indicator (measurableSet_cluster_mem x y |>.preimage measurable_snd)

/-! ## The identification -/

/-- The `(μ ⊗ μ)`-integral of a function of the second coordinate is the `μ`-integral, because
`μ` is a probability measure. -/
theorem lintegral_snd_eq (π : Sym2 V → unitInterval) {G : Config V → ℝ≥0∞} (hG : Measurable G) :
    (∫⁻ ρ : Config V × Config V, G ρ.2 ∂((edgeMeasure π).prod (edgeMeasure π)))
      = ∫⁻ ω, G ω ∂(edgeMeasure π) := by
  have hprob : IsProbabilityMeasure (edgeMeasure π) := inferInstance
  have hmeas : AEMeasurable (fun z : Config V × Config V => G z.2)
      ((edgeMeasure π).prod (edgeMeasure π)) :=
    (hG.comp (measurable_snd : Measurable (Prod.snd : Config V × Config V → Config V))).aemeasurable
  rw [MeasureTheory.lintegral_prod (f := fun z : Config V × Config V => G z.2) hmeas]
  simp only [@measure_univ _ _ (edgeMeasure π) hprob, lintegral_const, mul_one]

/-- **The `q = 0` connected star moment is the restored two-copy connected moment at `(p,q)`.**
For every `p, q`:
`starMoment π x y (p+q) = ∫∫ 1(y ∈ K_x(ω₁)) |K_x(ω₁)|^p |K̃_y(ω)|^q`. -/
theorem restoredConn_eq_starMoment (π : Sym2 V → unitInterval) (x y : V) (p q : ℕ) :
    restoredConn π x y p q = starMoment π x y (p + q) := by
  have hG := measurable_starIntegrand (V := V) x y (p + q)
  rw [starMoment, eq_comm]
  rw [show (∫⁻ ω, (connSet x y).indicator (fun _ => (1 : ℝ≥0∞)) ω *
        Percolation.cardFun (cluster ω x) ^ (p + q) ∂(edgeMeasure π))
      = ∫⁻ ω, (cluster ω x).indicator (fun _ => (1 : ℝ≥0∞)) y *
          Percolation.cardFun (cluster ω x) ^ (p + q) ∂(edgeMeasure π) from
    lintegral_congr fun ω => by
      rw [cluster_indicator_apply_ennreal x y ω]]
  rw [← lintegral_snd_eq π hG]
  refine lintegral_congr fun ρ => ?_
  by_cases hy : y ∈ cluster ρ.2 x
  · have hclu : cluster (restoreMap x ρ) y = cluster ρ.2 x :=
      cluster_restoreMap_eq_of_mem hy
    simp only [Set.indicator_of_mem hy, hclu, ← pow_add]
  · simp only [Set.indicator_of_notMem hy, zero_mul]

/-! ## The two instances of total degree three -/

/-- **`(p,q) = (2,1)`**: the star at exponent three is the restored two-copy connected moment of the
printed `p = 2`, `q = 1` display of Lemma I.4.17, whose right-hand side is `T³χ⁴ + 2T⁴χ³`. -/
theorem restoredConn_two_one_eq_starMoment (π : Sym2 V → unitInterval) (x y : V) :
    restoredConn π x y 2 1 = starMoment π x y 3 := by
  simpa using restoredConn_eq_starMoment π x y 2 1

/-- **`(p,q) = (1,2)`**: the same star is also the restored two-copy connected moment at `(1,2)`,
the other instance of total degree three, whose right-hand side is again `T³χ⁴ + 2T⁴χ³`. -/
theorem restoredConn_one_two_eq_starMoment (π : Sym2 V → unitInterval) (x y : V) :
    restoredConn π x y 1 2 = starMoment π x y 3 := by
  simpa using restoredConn_eq_starMoment π x y 1 2

/-- **`(p,q) = (1,1)`**: the star at exponent two is the restored two-copy connected moment at
`(1,1)`, whose printed right-hand side is the single term `T³(x,y) χ²` (`p+q+1 = 3`).  Together with
the `(2,1)` instance this exhibits the general pattern `star(n) = restoredConn (n-1) 1`. -/
theorem restoredConn_one_one_eq_starMoment (π : Sym2 V → unitInterval) (x y : V) :
    restoredConn π x y 1 1 = starMoment π x y 2 := by
  simpa using restoredConn_eq_starMoment π x y 1 1

/-- The `(2,1)` and `(1,2)` restored connected moments agree: both are the star at
exponent three. -/
theorem restoredConn_two_one_eq_one_two (π : Sym2 V → unitInterval) (x y : V) :
    restoredConn π x y 2 1 = restoredConn π x y 1 2 := by
  rw [restoredConn_two_one_eq_starMoment, restoredConn_one_two_eq_starMoment]

/-! ## The one-copy joint-moment form -/

/-- **The restored total moment is the one-copy joint moment.**  By the law preservation of the
restoration map (`map_restoreMap`) and `K_x(ω̃) = K_x(ω₁)`, the restored two-copy total equals
`∫ |K_x|^p |K_y|^q` in a *single* copy.  This is exactly the quantity the printed proof replaces by
the product of the two moments. -/
theorem restoredTotal_eq_jointMoment (π : Sym2 V → unitInterval) (x y : V) (p q : ℕ) :
    restoredTotal π x y p q
      = ∫⁻ ω, Percolation.cardFun (cluster ω x) ^ p *
          Percolation.cardFun (cluster ω y) ^ q ∂(edgeMeasure π) := by
  have hF : Measurable fun ω : Config V =>
      Percolation.cardFun (cluster ω x) ^ p * Percolation.cardFun (cluster ω y) ^ q := by
    refine Measurable.mul ?_ ?_
    · simpa only [cluster_idBondGraph] using
        (Percolation.measurable_cardFun_cluster (idBondGraph V) x).pow_const p
    · simpa only [cluster_idBondGraph] using
        (Percolation.measurable_cardFun_cluster (idBondGraph V) y).pow_const q
  have hcomp : Measurable fun ρ : Config V × Config V =>
      Percolation.cardFun (cluster (restoreMap x ρ) x) ^ p *
        Percolation.cardFun (cluster (restoreMap x ρ) y) ^ q :=
    hF.comp (measurable_restoreMap x)
  have hstep : (∫⁻ ρ : Config V × Config V,
        Percolation.cardFun (cluster ρ.2 x) ^ p *
          Percolation.cardFun (cluster (restoreMap x ρ) y) ^ q
        ∂((edgeMeasure π).prod (edgeMeasure π)))
      = ∫⁻ ρ : Config V × Config V,
        Percolation.cardFun (cluster (restoreMap x ρ) x) ^ p *
          Percolation.cardFun (cluster (restoreMap x ρ) y) ^ q
        ∂((edgeMeasure π).prod (edgeMeasure π)) := by
    refine lintegral_congr fun ρ => ?_
    rw [cluster_restoreMap_self ρ x]
  have hmap := lintegral_map (μ := (edgeMeasure π).prod (edgeMeasure π)) (g := restoreMap x)
    (f := fun ω : Config V =>
      Percolation.cardFun (cluster ω x) ^ p * Percolation.cardFun (cluster ω y) ^ q)
    hF (measurable_restoreMap x)
  rw [map_restoreMap π x] at hmap
  rw [restoredTotal, hstep]
  exact hmap.symm

/-- **The restored excluded part is the landed one-copy excluded moment** `I417A.rawDiff`: the same
restoration argument with the indicator of `y ∉ K_x`. -/
theorem restoredDiag_eq_rawDiff (π : Sym2 V → unitInterval) (x y : V) (p q : ℕ) :
    restoredDiag π x y p q = I417A.rawDiff π x y p q := by
  have hF : Measurable fun ω : Config V =>
      Percolation.cardFun (cluster ω x) ^ p *
        (cluster ω x)ᶜ.indicator (fun _ => (1 : ℝ≥0∞)) y *
        Percolation.cardFun (cluster ω y) ^ q := by
    refine Measurable.mul (Measurable.mul ?_ ?_) ?_
    · simpa only [cluster_idBondGraph] using
        (Percolation.measurable_cardFun_cluster (idBondGraph V) x).pow_const p
    · exact measurable_const.indicator (measurableSet_cluster_mem x y).compl
    · simpa only [cluster_idBondGraph] using
        (Percolation.measurable_cardFun_cluster (idBondGraph V) y).pow_const q
  have hcomp : Measurable fun ρ : Config V × Config V =>
      Percolation.cardFun (cluster (restoreMap x ρ) x) ^ p *
        (cluster (restoreMap x ρ) x)ᶜ.indicator (fun _ => (1 : ℝ≥0∞)) y *
        Percolation.cardFun (cluster (restoreMap x ρ) y) ^ q :=
    hF.comp (measurable_restoreMap x)
  have hstep : (∫⁻ ρ : Config V × Config V,
        (cluster ρ.2 x)ᶜ.indicator (fun _ => (1 : ℝ≥0∞)) y *
          (Percolation.cardFun (cluster ρ.2 x) ^ p *
            Percolation.cardFun (cluster (restoreMap x ρ) y) ^ q)
        ∂((edgeMeasure π).prod (edgeMeasure π)))
      = ∫⁻ ρ : Config V × Config V,
        Percolation.cardFun (cluster (restoreMap x ρ) x) ^ p *
          (cluster (restoreMap x ρ) x)ᶜ.indicator (fun _ => (1 : ℝ≥0∞)) y *
          Percolation.cardFun (cluster (restoreMap x ρ) y) ^ q
        ∂((edgeMeasure π).prod (edgeMeasure π)) := by
    refine lintegral_congr fun ρ => ?_
    rw [cluster_restoreMap_self ρ x]
    ring
  have hmap := lintegral_map (μ := (edgeMeasure π).prod (edgeMeasure π)) (g := restoreMap x)
    (f := fun ω : Config V => Percolation.cardFun (cluster ω x) ^ p *
      (cluster ω x)ᶜ.indicator (fun _ => (1 : ℝ≥0∞)) y *
      Percolation.cardFun (cluster ω y) ^ q) hF (measurable_restoreMap x)
  rw [map_restoreMap π x] at hmap
  rw [restoredDiag, hstep]
  rw [hmap.symm, I417A.rawDiff, I417A.notConnSet_eq]
  refine lintegral_congr fun ω => ?_
  by_cases hy : y ∈ cluster ω x
  · rw [Set.indicator_of_notMem (s := (cluster ω x)ᶜ) (by simpa using hy),
      Set.indicator_of_notMem (s := {ω : Config V | y ∉ cluster ω x}) (by simpa using hy)]
    ring
  · rw [Set.indicator_of_mem (s := (cluster ω x)ᶜ) (by simpa using hy),
      Set.indicator_of_mem (s := {ω : Config V | y ∉ cluster ω x}) (by simpa using hy)]
    ring

/-- **The star in one-copy joint-moment form**:
`starMoment π x y 3 = ∫ 1(y ∈ K_x) |K_x|² |K_y|`.  On `{y ∈ K_x}` one has `K_y = K_x`, so
`|K_x|² |K_y| = |K_x|³`; this exhibits the star as the printed `(2,1)` left-hand side with the
*joint* moment in place of the product of moments. -/
theorem starMoment_three_eq_jointMoment (π : Sym2 V → unitInterval) (x y : V) :
    starMoment π x y 3
      = ∫⁻ ω, (cluster ω x).indicator (fun _ => (1 : ℝ≥0∞)) y *
          (Percolation.cardFun (cluster ω x) ^ 2 *
            Percolation.cardFun (cluster ω y)) ∂(edgeMeasure π) := by
  rw [starMoment]
  refine lintegral_congr fun ω => ?_
  by_cases hy : y ∈ cluster ω x
  · have hclu : cluster ω y = cluster ω x := cluster_eq_of_mem_cluster_star hy
    rw [cluster_indicator_apply_ennreal x y ω, Set.indicator_of_mem hy, hclu, pow_succ]
  · rw [cluster_indicator_apply_ennreal x y ω, Set.indicator_of_notMem hy, zero_mul,
      zero_mul]

end PercLib.CriticalLRP.I417Gen
