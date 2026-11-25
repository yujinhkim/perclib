module

public import PercLib.CriticalLRP.Analysis.Cutoff.Resampling
public import PercLib.CriticalLRP.MomentMonotonicity.StrictCutoffEpsilon

/-!
# Strict decrease of the source cutoff kernel from density positivity

Direction `d8` of swarm `smwtzmkep`, member `m5`.

`K r = ∫_{Ioi r} |deriv K|` (`SourceModelData.K_eq_integral`) is only *weakly* decreasing: the
source axioms are compatible with `|deriv K|` vanishing on an interval (the error function `δ` may
equal `-1` there), so no strict difference follows from `K_antitone` and `K_pos` alone.  This file
proves the strict difference from the honest, pointwise density hypothesis

  `∀ t ∈ Ioo s r, 0 < |deriv K t|`:

then `K r < K s`, because `K s - K r` is the `toReal` of the `lintegral` of `|deriv K|` over
`Ioc s r`, whose support is the whole interval `Ioo s r` and hence has positive measure.

Consequences: strict positivity of the subtractive cutoff profile `J_r(x,y) = K(dist x y) - K r` for
in-range non-loop edges, hence `0 < cutKernel r e` and (for `0 < β_c`) `0 < openProb r e`.  This is
the strict `K`-difference input; it is a statement about `K` and the profile only, with no flux,
transport or majorant claim.
-/

/-! ## Strict decrease of the cutoff kernel -/

set_option linter.style.longLine false
set_option linter.hashCommand false

@[expose] public section

noncomputable section

open MeasureTheory Filter
open scoped ENNReal NNReal Topology

namespace PercLib.CriticalLRP.Orchestration

namespace SourceModelData

variable (M : SourceModelData)

attribute [local instance] Classical.propDecidable

/-- `K u` as the `toReal` of the tail `lintegral` of `|K'|`. -/
theorem K_eq_lintegral {u : ℝ} (hu : 0 < u) :
    M.K u = (∫⁻ t in Set.Ioi u, ENNReal.ofReal |deriv M.K t|).toReal := by
  rw [M.K_eq_integral u hu,
    MeasureTheory.integral_eq_lintegral_of_nonneg_ae (Filter.Eventually.of_forall fun t => abs_nonneg _)
      (measurable_deriv M.K).abs.aestronglyMeasurable]

/-- **The strict difference of the cutoff kernel.**  If `|deriv K|` does not vanish on `(s,r)`, then
`K` is strictly larger at the smaller radius. -/
theorem K_lt_of_deriv_ne_zero {s r : ℝ} (hs : 0 < s) (hsr : s < r)
    (hdens : ∀ t ∈ Set.Ioo s r, 0 < |deriv M.K t|) : M.K r < M.K s := by
  classical
  set f : ℝ → ℝ≥0∞ := fun t => ENNReal.ofReal |deriv M.K t| with hf
  have hfmeas : Measurable f := (measurable_deriv M.K).abs.ennreal_ofReal
  have hKs := M.K_eq_lintegral hs
  have hKr := M.K_eq_lintegral (lt_trans hs hsr)
  -- the tail at `s` splits into `Ioc s r` and `Ioi r`
  have hsplit : (∫⁻ t in Set.Ioi s, f t) = (∫⁻ t in Set.Ioc s r, f t)
      + (∫⁻ t in Set.Ioi r, f t) := by
    have hunion : Set.Ioi s = Set.Ioc s r ∪ Set.Ioi r := by
      ext t
      simp only [Set.mem_Ioi, Set.mem_Ioc, Set.mem_union]
      constructor
      · intro h
        rcases le_or_gt t r with h' | h'
        · exact Or.inl ⟨h, h'⟩
        · exact Or.inr h'
      · rintro (⟨h, -⟩ | h)
        · exact h
        · exact lt_trans hsr h
    have hdisj : Disjoint (Set.Ioc s r) (Set.Ioi r) := by
      rw [Set.disjoint_left]
      intro t ht1 ht2
      exact absurd ht2 (not_lt.mpr ht1.2)
    rw [hunion, MeasureTheory.lintegral_union measurableSet_Ioi hdisj]
  -- positivity of the middle piece
  have hsuppmeas : MeasurableSet (Function.support f) :=
    hfmeas (measurableSet_singleton 0).compl
  have hpos : 0 < ∫⁻ t in Set.Ioc s r, f t := by
    rw [MeasureTheory.lintegral_pos_iff_support hfmeas, Measure.restrict_apply hsuppmeas]
    have hsub : Set.Ioo s r ⊆ Function.support f ∩ Set.Ioc s r := by
      intro t ht
      refine ⟨?_, ⟨ht.1, ht.2.le⟩⟩
      have h1 : 0 < |deriv M.K t| := hdens t ht
      simp only [hf, Function.mem_support, ne_eq, ENNReal.ofReal_eq_zero, not_le]
      exact h1
    have hvol : 0 < volume (Set.Ioo s r) := by
      rw [Real.volume_Ioo]
      exact ENNReal.ofReal_pos.mpr (by linarith)
    exact lt_of_lt_of_le hvol (measure_mono hsub)
  -- finiteness of the middle piece
  have hKs_ne : (∫⁻ t in Set.Ioi s, f t) ≠ ⊤ := by
    intro htop
    rw [htop, ENNReal.toReal_top] at hKs
    have := M.K_pos hs
    linarith
  have hmid_ne : (∫⁻ t in Set.Ioc s r, f t) ≠ ⊤ :=
    ne_top_of_le_ne_top hKs_ne (MeasureTheory.lintegral_mono_set (fun t ht => ht.1))
  have hKr_ne : (∫⁻ t in Set.Ioi r, f t) ≠ ⊤ := by
    intro htop
    rw [htop, ENNReal.toReal_top] at hKr
    have := M.K_pos (lt_trans hs hsr)
    linarith
  have hmidpos : 0 < (∫⁻ t in Set.Ioc s r, f t).toReal :=
    ENNReal.toReal_pos hpos.ne' hmid_ne
  calc M.K r = (∫⁻ t in Set.Ioi r, f t).toReal := hKr
    _ < (∫⁻ t in Set.Ioc s r, f t).toReal + (∫⁻ t in Set.Ioi r, f t).toReal := by
        linarith
    _ = ((∫⁻ t in Set.Ioc s r, f t) + (∫⁻ t in Set.Ioi r, f t)).toReal :=
        (ENNReal.toReal_add hmid_ne hKr_ne).symm
    _ = (∫⁻ t in Set.Ioi s, f t).toReal := by rw [hsplit]
    _ = M.K s := hKs.symm

/-- **Strict positivity of the subtractive cutoff profile** for `s < r`, from density positivity
on `(s,r)`. -/
theorem cutoffProfile_pos_of_lt {s r : ℝ} (hs : 0 < s) (hsr : s < r)
    (hdens : ∀ t ∈ Set.Ioo s r, 0 < |deriv M.K t|) :
    0 < PercLib.CriticalLRP.FiniteVolume.cutoffProfile M.K r s := by
  rw [PercLib.CriticalLRP.FiniteVolume.cutoffProfile, ite_eq_left hsr.le]
  exact sub_pos.mpr (M.K_lt_of_deriv_ne_zero hs hsr hdens)

/-- **Strict positivity of the cut-off kernel of an in-range non-loop edge.** -/
theorem cutKernel_pos_of_lt {r : ℝ} {x y : M.V} (hxy : x ≠ y) (hd : M.S.dist x y < r)
    (hdens : ∀ t ∈ Set.Ioo (M.S.dist x y) r, 0 < |deriv M.K t|) :
    0 < M.cutKernel r s(x, y) := by
  rw [cutKernel_mk, ite_eq_right hxy]
  exact M.cutoffProfile_pos_of_lt (M.S.dist_pos hxy) hd hdens

/-- **Strict positivity of the cut-off kernel off the corner set.**  At a radius which is not the
length of any pair of distinct vertices, every non-loop edge of length at most `r` has a strictly
positive cut-off kernel, provided the density is positive on `(0,r)`. -/
theorem cutKernel_pos_of_offCorner {r : ℝ} (hoff : r ∉ M.cornerRadii)
    {x y : M.V} (hxy : x ≠ y) (hd : M.S.dist x y ≤ r)
    (hdens : ∀ t ∈ Set.Ioo 0 r, 0 < |deriv M.K t|) :
    0 < M.cutKernel r s(x, y) := by
  have hlt : M.S.dist x y < r := by
    rcases lt_or_eq_of_le hd with h | h
    · exact h
    · exact absurd (show r ∈ M.cornerRadii from ⟨x, y, hxy, h⟩) hoff
  exact M.cutKernel_pos_of_lt hxy hlt (fun t ht => hdens t ⟨lt_trans (M.S.dist_pos hxy) ht.1, ht.2⟩)

/-- **Positivity of `|K'|` on a tail**, from the two-sided power bounds of
`SourceModelData.exists_deriv_bounds`.  This is the model-level supply of the density hypothesis. -/
theorem exists_deriv_pos_of_gt :
    ∃ R : ℝ, 0 < R ∧ ∀ t : ℝ, R < t → 0 < |deriv M.K t| := by
  obtain ⟨R, hRpos, -, hlow, -⟩ := M.exists_deriv_bounds
  refine ⟨R, hRpos, fun t ht => ?_⟩
  have ht0 : 0 < t := lt_trans hRpos ht
  have h1 : 0 < (1 / 2 : ℝ) * t ^ (-(M.d : ℝ) - M.α - 1) :=
    mul_pos (by norm_num) (Real.rpow_pos_of_pos ht0 _)
  exact lt_of_lt_of_le h1 (hlow t ht)

/-- **Kernel positivity off the corner set, above the density radius.**  For the density radius `R`
of `exists_deriv_pos_of_gt`, at a radius `r > R` which is not a lattice distance, every non-loop edge
of length in `(R, r]` has a strictly positive cut-off kernel: no density hypothesis remains. -/
theorem exists_cutKernel_pos_of_offCorner :
    ∃ R : ℝ, 0 < R ∧ ∀ ⦃r : ℝ⦄, R < r → r ∉ M.cornerRadii → ∀ ⦃x y : M.V⦄, x ≠ y →
      R < M.S.dist x y → M.S.dist x y ≤ r → 0 < M.cutKernel r s(x, y) := by
  obtain ⟨R, hRpos, hdensR⟩ := M.exists_deriv_pos_of_gt
  refine ⟨R, hRpos, fun r _ hoff x y hxy hdR hd => ?_⟩
  have hlt : M.S.dist x y < r := by
    rcases lt_or_eq_of_le hd with h | h
    · exact h
    · exact absurd (show r ∈ M.cornerRadii from ⟨x, y, hxy, h⟩) hoff
  exact M.cutKernel_pos_of_lt hxy hlt (fun t ht => hdensR t (lt_trans hdR ht.1))

end SourceModelData

end PercLib.CriticalLRP.Orchestration

/-! ## Axiom audit -/

#print axioms PercLib.CriticalLRP.Orchestration.SourceModelData.K_eq_lintegral
#print axioms PercLib.CriticalLRP.Orchestration.SourceModelData.K_lt_of_deriv_ne_zero
#print axioms PercLib.CriticalLRP.Orchestration.SourceModelData.cutoffProfile_pos_of_lt
#print axioms PercLib.CriticalLRP.Orchestration.SourceModelData.cutKernel_pos_of_lt
#print axioms PercLib.CriticalLRP.Orchestration.SourceModelData.cutKernel_pos_of_offCorner
#print axioms PercLib.CriticalLRP.Orchestration.SourceModelData.exists_deriv_pos_of_gt
#print axioms PercLib.CriticalLRP.Orchestration.SourceModelData.exists_cutKernel_pos_of_offCorner
