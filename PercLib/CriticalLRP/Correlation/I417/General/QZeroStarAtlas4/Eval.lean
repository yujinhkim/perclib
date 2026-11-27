/-
Ultramath swarm `smwziumdb`, member `m7`, direction `d4`.

Copyright (c) 2026 PercLib contributors. Released under Apache 2.0.

Accepted and independently rebuilt from Ultramath `smwziumdb`.
Supporting integration based on production commit `5d2d681b941eb1c687f1ba17e6a798b8f0175aa0`.

# The `q = 0`, `p = 3` star as a polygon sum: `chi ^ (7 - ell) k ^ ell (x,y)` per shape

`Main.lean` proves the four-label event realization `starMoment ≤ starAtlasSum`, whose right-hand
side is the sum over the fifteen labelled four-leaf shapes of the product of the two-point
function over the seven atlas edges.  This file performs the two evaluations that turn that sum
into the source's polygon form.

* **Per shape.**  With the mark `y` pinned at the leaf carrying the label `3` and the three arms
  summed over, the atlas product of a shape `t` with marked depth `ℓ = starDepth t` is worth
  exactly `χ^(2·4−1−ℓ) · T^ℓ(x,y)`, i.e. `χ^(7−ℓ) k^ℓ(x,y)`.  This is production's
  `I417Base.tsum_wtE_marked` (`χ^(2L−1−depth) · pathW`) combined with `pathW_eq_iterPow`
  (`pathW = iterPow`), fed by `CanonAtlas.Measure.tsum_atlasProduct_eq_wtE`
  (`∑_φ atlasProduct = wtE`) and the coordinate-splitting `tsum_pinned_eq_tsum_arms`.
* **Summed over shapes.**  `starMoment ≤ ∑_t χ^(7−starDepth t) · iterPow (starDepth t) x y`,
  which is the diagrammatic bound of Lemma I.4.17 at `(p,q) = (3,0)` with the *actual*
  root-to-mark depths of the fifteen shapes — the class `ℓ = 2` included.

The depth-grouping into `∑_ℓ C_ℓ χ^(7−ℓ) k^ℓ` with `C_ℓ` the number of shapes of depth `ℓ` is
the finite count `I417Base.finset_sum_by_fiber` would supply; it is *not* performed here, so no
numerical coefficient is claimed.

Definitions live in `Defs.lean`; this file has theorems only.

No `sorry`, no custom axioms.
-/
module

public import PercLib.CriticalLRP.Correlation.I417.General.QZeroStarAtlas4.Main
public import PercLib.CriticalLRP.Correlation.I417.MarkedJoint.Transversal.Depth

/-! # Evaluation and transversal comparison for the four-labelled star -/

open MeasureTheory Measure ProbabilityTheory unitInterval
open scoped ENNReal NNReal

set_option linter.unusedSectionVars false

open PercLib.CriticalLRP.TreeExpansion

@[expose] public section

namespace PercLib.CriticalLRP.QZeroStarAtlas4

attribute [local instance] Classical.propDecidable

variable {V : Type*} [Countable V]

/-! ## Pinning the last label -/

/-- **Pinning the last label.**  Summing over the three arms with the mark `y` fixed at the last
label is the same as summing over the whole four-label tuple with its last entry pinned to `y`. -/
theorem tsum_pinned_eq_tsum_arms (F : (Fin 4 → V) → ℝ≥0∞) (y : V) :
    (∑' g : Fin 4 → V, (if g (Fin.last 3) = y then 1 else 0) * F g)
      = ∑' f : Fin 3 → V, F (starLabels f y) := by
  have key : (∑' g : Fin 4 → V, (if g (Fin.last 3) = y then 1 else 0) * F g)
      = ∑' p : V × (Fin 3 → V),
          (if p.1 = y then 1 else 0) * F (starLabels p.2 p.1) := by
    refine (Equiv.tsum_eq fin4Equiv.symm
      (fun g : Fin 4 → V => (if g (Fin.last 3) = y then 1 else 0) * F g)).symm.trans ?_
    refine tsum_congr fun p => ?_
    obtain ⟨v, f⟩ := p
    have h1 : fin4Equiv.symm (v, f) = starLabels f v := rfl
    have h2 : starLabels f v (Fin.last 3) = v := starLabels_last f v
    rw [h1, h2]
  rw [key]
  have hprod : (∑' p : V × (Fin 3 → V),
        (fun (v : V) (f : Fin 3 → V) => (if v = y then 1 else 0) * F (starLabels f v)) p.1 p.2)
      = ∑' v : V, ∑' f : Fin 3 → V, (if v = y then 1 else 0) * F (starLabels f v) :=
    ENNReal.tsum_prod
      (f := fun (v : V) (f : Fin 3 → V) => (if v = y then 1 else 0) * F (starLabels f v))
  change (∑' p : V × (Fin 3 → V),
        (fun (v : V) (f : Fin 3 → V) => (if v = y then 1 else 0) * F (starLabels f v)) p.1 p.2)
      = ∑' f : Fin 3 → V, F (starLabels f y)
  rw [hprod]
  refine (tsum_eq_single y (fun v hv => ?_)).trans ?_
  · refine ENNReal.tsum_eq_zero.mpr fun f => ?_
    simp [hv]
  · simp

/-! ## The value of one shape -/

/-- **The value of one four-label shape with the mark pinned.**
`∑_{x_1 x_2 x_3} ∑_{φ} ∏_{e} P(e) = χ^(7−ℓ) T^ℓ(x,y)` with `ℓ = starDepth t` the length of the
tree path from the root to the leaf carrying the marked label. -/
theorem tsum_arms_wtE (π : Sym2 V → unitInterval) (x y : V)
    (hχ : ∀ a : V, ∑' b : V, tauK π a b = I417.meanVol π x)
    (t : LTon (Fin 4) Finset.univ) :
    (∑' f : Fin 3 → V,
        I417Base.wtE (tauK π) t.1 (fun p => starLabels f y (RTree.leafOfPos t.1 p)) x)
      = (I417.meanVol π x) ^ (2 * 4 - 1 - starDepth t)
          * I417Base.iterPow (tauK π) (starDepth t) x y := by
  classical
  -- the leaf position carrying the marked label, and the leaf-position equivalence
  have hmem : Fin.last 3 ∈ t.1.leaves := MarkedAtlas.mark_mem_leaves t (Finset.mem_univ _)
  set q : t.1.LeafPos := MarkedAtlas.markPos t.1 (Fin.last 3) hmem with hqdef
  have hq' : RTree.leafOfPos t.1 q = Fin.last 3 :=
    MarkedAtlas.leafOfPos_markPos t.1 (Fin.last 3) hmem
  have hbj : Function.Bijective (RTree.leafOfPos t.1) :=
    ⟨RTree.leafOfPos_injective t.2.1,
      fun a => RTree.exists_leafOfPos t.1 a
        (MarkedAtlas.mark_mem_leaves t (Finset.mem_univ a))⟩
  set e : t.1.LeafPos ≃ Fin 4 := Equiv.ofBijective (RTree.leafOfPos t.1) hbj with hedef
  -- unpin: replace the sum over the three arms by a sum over the pinned four-label tuple
  rw [← tsum_pinned_eq_tsum_arms
    (fun g : Fin 4 → V =>
      I417Base.wtE (tauK π) t.1 (fun p => g (RTree.leafOfPos t.1 p)) x) y]
  -- transport the label sum along the leaf-position equivalence
  refine (Equiv.tsum_eq (Equiv.arrowCongr e (Equiv.refl V))
    (fun g : Fin 4 → V => (if g (Fin.last 3) = y then 1 else 0) *
      I417Base.wtE (tauK π) t.1 (fun p => g (RTree.leafOfPos t.1 p)) x)).symm.trans ?_
  -- the transported summand is the marked tree weight at the marked leaf `q`
  have hcongr : (∑' yv : t.1.LeafPos → V,
      (if (Equiv.arrowCongr e (Equiv.refl V)) yv (Fin.last 3) = y then 1 else 0) *
        I417Base.wtE (tauK π) t.1
          (fun p => (Equiv.arrowCongr e (Equiv.refl V)) yv (RTree.leafOfPos t.1 p)) x)
      = ∑' yv : t.1.LeafPos → V,
          (if yv q = y then 1 else 0) * I417Base.wtE (tauK π) t.1 yv x := by
    refine tsum_congr fun yv => ?_
    have harg : (fun p : t.1.LeafPos =>
        (Equiv.arrowCongr e (Equiv.refl V)) yv (RTree.leafOfPos t.1 p)) = yv := by
      funext p
      have hp : RTree.leafOfPos t.1 p = e p := rfl
      rw [hp]
      exact congrArg yv (Equiv.symm_apply_apply e p)
    have hlast : (Equiv.arrowCongr e (Equiv.refl V)) yv (Fin.last 3) = yv q := by
      have hp : (Equiv.arrowCongr e (Equiv.refl V)) yv (Fin.last 3)
          = yv (e.symm (Fin.last 3)) := rfl
      rw [hp]
      have hsym : e.symm (Fin.last 3) = q := by
        have h1 : Fin.last 3 = e q := hq'.symm
        rw [h1]
        exact Equiv.symm_apply_apply e q
      rw [hsym]
    rw [hlast, harg]
  rw [hcongr]
  -- production's marked leaf sum
  rw [I417Base.tsum_wtE_marked (tauK π) (I417.meanVol π x) hχ t.1 q x y]
  rw [I417Base.pathW_eq_iterPow]
  rw [MarkedAtlas.numLeaves_eq_card t]
  rw [hqdef]
  rfl

/-! ## Summing over the shapes -/

/-- **The `(p,q) = (3,0)` star as the sum of the fifteen shape values.**  Each labelled four-leaf
shape contributes `χ^(7−starDepth) · T^starDepth(x,y)`. -/
theorem starMoment_le_shape_eval (π : Sym2 V → unitInterval) (hπ : ∀ e, π e < 1) (x y : V)
    (hχ : ∀ a : V, ∑' b : V, tauK π a b = I417.meanVol π x) :
    I417Gen.starMoment π x y 3 ≤
      ∑' t : LTon (Fin 4) Finset.univ,
        (I417.meanVol π x) ^ (2 * 4 - 1 - starDepth t)
          * I417Base.iterPow (tauK π) (starDepth t) x y := by
  refine le_trans (starMoment_le_tsum_shapes π hπ x y) (le_of_eq ?_)
  refine tsum_congr fun t => ?_
  rw [ENNReal.tsum_comm]
  refine Eq.trans (tsum_congr fun f => ?_) (tsum_arms_wtE π x y hχ t)
  exact CanonAtlas.Measure.tsum_atlasProduct_eq_wtE π x (starLabels f y) t.1

/-! ## Elementary bounds on the marked depth -/

/-- Every four-label shape has marked depth at least one. -/
theorem starDepth_pos (t : LTon (Fin 4) Finset.univ) : 0 < starDepth t :=
  MarkedAtlas.markDepth_pos (Fin.last 3) t (Finset.mem_univ _)

/-- Every four-label shape has marked depth at most four, the number of labels. -/
theorem starDepth_le (t : LTon (Fin 4) Finset.univ) : starDepth t ≤ 4 := by
  have h := MarkedAtlas.markDepth_le_card (Fin.last 3) t (Finset.mem_univ _)
  simpa [starDepth] using h

/-! ## The bridge to production's marked joint moment and its non-plane coefficients -/

/-- **The star moment is production's marked joint moment.**  `E[|K_x|^p 1(x ↔ y)]` written as
an integral over the base configuration is the same number either way; only the order of the two
factors and the spelling of the indicator differ. -/
theorem starMoment_eq_jointPow (π : Sym2 V → unitInterval) (x y : V) (p : ℕ) :
    I417Gen.starMoment π x y p = I417Gen.jointPow π x p y := by
  rw [I417Gen.starMoment, I417Gen.jointPow]
  refine MeasureTheory.lintegral_congr fun ω => ?_
  have h : (connSet x y).indicator (fun _ => (1 : ℝ≥0∞)) ω
      = (cluster ω x).indicator (fun _ => (1 : ℝ≥0∞)) y := by
    rw [connSet_eq]
    simp only [Set.indicator_apply, Set.mem_ofPred_eq, mem_cluster_iff]
  rw [h, mul_comm]

/-- **The `q = 0`, `p = 3` star bound in the source's polygon form, with non-plane marked-depth
coefficients.**  This is production's `jointPow_le_nonplane_markedDepth` at `p = 3`, transported
to `starMoment`:

  `E[|K_x|³ 1(x ↔ y)] ≤ ∑_{ℓ=2}^{4} C_ℓ χ^(7-ℓ) T^ℓ(x,y)`,  `χ = E|K|`,

where `C_ℓ = nonplaneMarkedCount 3 ℓ` is the number of child-swap orbits of fully labelled
four-leaf shapes whose marked leaf hangs at depth `ℓ`.  The coefficients are explicit finite
cardinalities; their numerical values are **not** computed here (see `NOTES.md`). -/
theorem starMoment_le_nonplane_markedDepth (π : Sym2 V → unitInterval) (hπ : ∀ e, π e < 1)
    (x y : V) (hχ : ∀ v : V, I417.meanVol π v = I417.meanVol π x) :
    I417Gen.starMoment π x y 3 ≤
      ∑ ℓ ∈ Finset.Icc 2 4,
        (PercLib.CriticalLRP.I417MarkedTransversal.nonplaneMarkedCount 3 ℓ : ℝ≥0∞) *
          ((I417.meanVol π x) ^ (2 * 3 + 1 - ℓ) *
            I417Base.iterPow (tauK π) ℓ x y) := by
  rw [starMoment_eq_jointPow]
  refine PercLib.CriticalLRP.I417MarkedTransversal.jointPow_le_nonplane_markedDepth
    π hπ (I417.meanVol π x) ?_ x (by norm_num) y
  intro v
  change I417.meanVol π v = I417.meanVol π x
  exact hχ v

end PercLib.CriticalLRP.QZeroStarAtlas4
