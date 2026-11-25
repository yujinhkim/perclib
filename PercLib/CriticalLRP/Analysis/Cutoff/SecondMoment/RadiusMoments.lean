/-
Copyright (c) 2026 PercLib contributors. Released under Apache 2.0.

# The radius variable of Lemma I.4.1: almost-everywhere differentiability and the corner set

Swarm `smwv94uce`, member `m1`, direction d5.

Lemma I.4.1 of Hutchcroft, *Critical long-range percolation I* (arXiv:2508.18807v1), states the
cut-off volume-moment derivative formula "for every integer `p >= 1`, every `0 <= beta <= beta_c`
and every `r > 0`".  Commit `47aa44c` shows the literal `r > 0` cannot be a two-sided statement at a
radius attained by the norm: the profile uses the *closed* ball, so the derivative weight of an edge
of length exactly `r0` switches on only at `r0`, and the moment function has a corner there
(`CornerOneSided`, `RadiusOneSided`).

This file fixes the quantifier honestly, and does so **without** repeating any binomial or
mass-transport algebra and **without** deriving the derivative formula.  What it proves is:

* `monotoneOn_cutMomentReal` - on a window whose top `b` carries a finite `p`-th moment,
  `r |-> (M.cutMoment p r).toReal` is nondecreasing in `r`;
* `ae_differentiableAt_cutMomentReal` / `ae_differentiableAt_cutMomentReal_two` - hence it is
  differentiable at Lebesgue-almost-every radius of any such window, at every `p` and in
  particular at `p = 2`;
* `deriv_nonneg_of_lt` / `ae_deriv_nonneg_cutMomentReal_two` - the radius derivative is
  nonnegative wherever it exists below the finiteness radius;
* `volume_cornerRadii` - the corner set `M.cornerRadii` (the radii attained by the norm at a
  nonzero lattice vector) is Lebesgue-null; on a compact window it is even finite
  (`finite_cornerRadii_inter_Ioo`), but nullity on the whole halfline is what the radius
  integration needs, and it is what is proved here;
* `ae_notMem_cornerRadii`, `ae_notMem_cornerRadii_restrict` - almost every radius is off-corner,
  on the line and on any measurable window;
* `ae_hasDerivAt_of_offCorner` / `ae_hasDerivAt_of_offCorner_two` - **corner elimination**: a
  pointwise off-corner derivative formula upgrades to the same formula at almost every radius of
  the window.  This is the exact shape in which the off-corner `p = 2` cut-moment derivative is
  consumed by the radius integration, and it needs the pointwise formula at off-corner radii only;
* `ae_radius_picture_two` - the capstone: at `p = 2` almost every radius of the window is
  simultaneously off-corner, a differentiability point, and has nonnegative radius derivative.

## The one remaining input, stated exactly

Everything above is unconditional in `p : Nat`, in the profile `M.K`, in `M.betaCrit`, and in the
geometry `M.S`; no differentiability, monotonicity of `deriv`, or continuity of `deriv M.K` is
assumed.  The single hypothesis is `M.cutMoment p b != top` at the *top* `b` of the window - the
same convention the production interface uses (`hvol : M.cutMoment 1 r != top` in
`OffCorner/NormalizedAggregate/Finiteness.lean`).  It is required because
`ENNReal.toReal_mono` needs the larger value finite, and it is satisfied for every finite radius by
the range-truncated law (a finite-range law at `beta <= beta_c`), but that finiteness is **not**
landed in production and is therefore left explicit rather than assumed away.

## What is deliberately *not* claimed

* No derivative *formula*: the identification of the off-corner radius derivative with
  `beta |J'(r)|` times the `p = 2` cut moment, with its two excluded terms
  `E|K| sum_{y in B_r, y notin K} |K_y|^2` and `2 E|K|^2 sum_{y in B_r, y notin K} |K_y|`, is the
  input `D` of `ae_hasDerivAt_of_offCorner_two` and is not proved here.
* No two-sided differentiability at an attained radius: that is false, by `47aa44c`.
* No absolute continuity, no fundamental theorem of calculus and no integrability claim.  The
  landed interface `abs_sub_le_integral_cutMomentReal` asks for differentiability at *every*
  off-corner point plus a majorant; nothing here weakens that, and nothing here supplies the
  majorant.

No `sorry`, no `admit`, no `native_decide`, no custom axioms.  Axiom audit: only `propext`,
`Classical.choice`, `Quot.sound` (`Audit.lean`).
-/
module

public import PercLib.CriticalLRP.Analysis.Cutoff.CutoffMomentContinuity
public import PercLib.CriticalLRP.Analysis.Cutoff.CornerRadii

/-!
# Almost-everywhere radius differentiability of every natural cutoff moment

Section 1: monotonicity in the cutoff radius.  Section 2: almost-everywhere differentiability, at
every `p` and at `p = 2`.  Section 3: the corner set is Lebesgue-null.  Section 4: capstone for
`p = 2`.  Section 5: nonnegativity of the radius derivative.  Section 6: corner elimination, i.e.
upgrading a pointwise off-corner formula to an almost-everywhere formula on the window - the shape
needed by the radius integration of Lemma I.4.1.
-/

set_option autoImplicit false
set_option linter.hashCommand false
set_option linter.style.longLine false

@[expose] public section

noncomputable section

open MeasureTheory Filter Topology Set
open scoped ENNReal NNReal Topology

namespace PercLib.CriticalLRP.Orchestration

namespace SourceModelData

variable (M : SourceModelData)

/-! ## 1. Monotonicity of the `p`-th cutoff moment in the cutoff radius -/

/-- **The `p`-th cutoff moment is monotone in the cutoff radius.**  On a window bounded above by a
radius at which the moment is finite, `(M.cutMoment p r).toReal` is nondecreasing in `r`. -/
theorem monotoneOn_cutMomentReal {b : ℝ} (p : ℕ) (hfin : M.cutMoment p b ≠ ⊤) :
    MonotoneOn (fun r => M.cutMomentReal p r) (Set.Iic b) := by
  intro x _hx y hy hxy
  exact M.cutMomentReal_le_of_le hxy p (ne_top_of_le_ne_top hfin (M.cutMoment_monotone p hy))

/-! ## 2. Almost-everywhere differentiability in the cutoff radius -/

/-- **Almost-everywhere differentiability on a window.** -/
theorem ae_differentiableWithinAt_cutMomentReal {b : ℝ} (p : ℕ)
    (hfin : M.cutMoment p b ≠ ⊤) :
    ∀ᵐ r ∂(volume : Measure ℝ),
      r ≤ b → DifferentiableWithinAt ℝ (fun r => M.cutMomentReal p r) (Set.Iic b) r :=
  (M.monotoneOn_cutMomentReal p hfin).ae_differentiableWithinAt_of_mem

/-- **Almost-everywhere differentiability on a window.** -/
theorem ae_differentiableAt_cutMomentReal {a b : ℝ} (_hab : a < b) (p : ℕ)
    (hfin : M.cutMoment p b ≠ ⊤) :
    ∀ᵐ r ∂(volume.restrict (Set.Ioo a b)),
      DifferentiableAt ℝ (fun r => M.cutMomentReal p r) r := by
  rw [ae_restrict_iff' measurableSet_Ioo]
  filter_upwards [M.ae_differentiableWithinAt_cutMomentReal p hfin] with r hd hr
  have hrb : r ≤ b := le_of_lt hr.2
  exact (hd hrb).differentiableAt (Iic_mem_nhds hr.2)

/-- **The `p = 2` case of almost-everywhere differentiability.** -/
theorem ae_differentiableAt_cutMomentReal_two {a b : ℝ} (hab : a < b)
    (hfin : M.cutMoment 2 b ≠ ⊤) :
    ∀ᵐ r ∂(volume.restrict (Set.Ioo a b)),
      DifferentiableAt ℝ (fun r => M.cutMomentReal 2 r) r :=
  M.ae_differentiableAt_cutMomentReal hab 2 hfin

/-! ## 3. The corner set is Lebesgue-null -/

/-- **The corner set is Lebesgue-null.** -/
theorem volume_cornerRadii : volume M.cornerRadii = 0 := by
  have hcov : M.cornerRadii ⊆ ⋃ n : ℕ, M.cornerRadii ∩ Set.Icc (n : ℝ) ((n : ℝ) + 1) := by
    intro r hr
    have hpos : 0 < r := M.attainedRadii_pos (by rwa [← M.attainedRadii_eq_cornerRadii] at hr)
    refine Set.mem_iUnion.mpr ⟨⌊r⌋₊, Set.mem_inter hr ⟨?_, ?_⟩⟩
    · exact Nat.floor_le (le_of_lt hpos)
    · have := Nat.lt_floor_add_one r
      linarith
  refine measure_mono_null hcov (measure_iUnion_null fun n => ?_)
  rw [← M.attainedRadii_eq_cornerRadii]
  exact M.volume_attainedRadii_inter_Icc (n : ℝ) ((n : ℝ) + 1)

/-- Almost every cutoff radius is off-corner. -/
theorem ae_notMem_cornerRadii : ∀ᵐ r ∂(volume : Measure ℝ), r ∉ M.cornerRadii := by
  rw [ae_iff]
  simpa using M.volume_cornerRadii

/-! ## 4. Capstone: the `p = 2` radius statement -/

/-- **The honestly attainable form of the Lemma I.4.1 radius quantifier at `p = 2`.** -/
theorem ae_differentiableAt_and_notMem_cornerRadii_two {a b : ℝ} (_hab : a < b)
    (hfin : M.cutMoment 2 b ≠ ⊤) :
    ∀ᵐ r ∂(volume.restrict (Set.Ioo a b)),
      r ∉ M.cornerRadii ∧ DifferentiableAt ℝ (fun r => M.cutMomentReal 2 r) r := by
  rw [ae_restrict_iff' measurableSet_Ioo]
  filter_upwards [M.ae_notMem_cornerRadii, M.ae_differentiableWithinAt_cutMomentReal 2 hfin]
    with r hoff hd hr
  have hrb : r ≤ b := le_of_lt hr.2
  exact ⟨hoff, (hd hrb).differentiableAt (Iic_mem_nhds hr.2)⟩


/-! ## 5. Nonnegativity of the radius derivative -/

/-- **The radius derivative of the `p`-th cutoff moment is nonnegative wherever it exists.**  This is
monotonicity of the moment in the radius, read off through `MonotoneOn.derivWithin_nonneg`; the
closed-ball convention and the size of `beta` play no role. -/
theorem deriv_nonneg_of_lt {b : ℝ} (p : ℕ) (hfin : M.cutMoment p b ≠ ⊤) {r : ℝ} (hr : r < b) :
    0 ≤ deriv (fun r => M.cutMomentReal p r) r := by
  have hdw : derivWithin (fun r => M.cutMomentReal p r) (Set.Iic b) r
      = deriv (fun r => M.cutMomentReal p r) r :=
    derivWithin_of_mem_nhds (Iic_mem_nhds hr)
  rw [← hdw]
  exact (M.monotoneOn_cutMomentReal p hfin).derivWithin_nonneg

/-- **Almost-everywhere nonnegativity of the radius derivative.** -/
theorem ae_deriv_nonneg_cutMomentReal {a b : ℝ} (_hab : a < b) (p : ℕ)
    (hfin : M.cutMoment p b ≠ ⊤) :
    ∀ᵐ r ∂(volume.restrict (Set.Ioo a b)),
      0 ≤ deriv (fun r => M.cutMomentReal p r) r := by
  rw [ae_restrict_iff' measurableSet_Ioo]
  filter_upwards with r hr
  exact M.deriv_nonneg_of_lt p hfin hr.2

/-- The `p = 2` case of almost-everywhere nonnegativity of the radius derivative. -/
theorem ae_deriv_nonneg_cutMomentReal_two {a b : ℝ} (hab : a < b) (hfin : M.cutMoment 2 b ≠ ⊤) :
    ∀ᵐ r ∂(volume.restrict (Set.Ioo a b)),
      0 ≤ deriv (fun r => M.cutMomentReal 2 r) r :=
  M.ae_deriv_nonneg_cutMomentReal hab 2 hfin

/-! ## 6. Eliminating the corner exception set -/

/-- **Almost every radius is off-corner, on any measurable window.** -/
theorem ae_notMem_cornerRadii_restrict (s : Set ℝ) (hs : MeasurableSet s) :
    ∀ᵐ r ∂(volume.restrict s), r ∉ M.cornerRadii := by
  rw [ae_restrict_iff' hs]
  filter_upwards [M.ae_notMem_cornerRadii] with r hr _
  exact hr

/-- **Corner elimination at general `p`.**  A pointwise off-corner derivative formula upgrades to a
formula that holds at Lebesgue-almost-every radius of the window, with the *same* derivative
expression.  The corner set is the only obstruction, and it is null (`volume_cornerRadii`). -/
theorem ae_hasDerivAt_of_offCorner {a b : ℝ} (p : ℕ) (D : ℝ → ℝ)
    (hgood : ∀ u ∈ Set.Ioo a b, u ∉ M.cornerRadii →
      HasDerivAt (fun r => M.cutMomentReal p r) (D u) u) :
    ∀ᵐ r ∂(volume.restrict (Set.Ioo a b)),
      HasDerivAt (fun r => M.cutMomentReal p r) (D r) r := by
  rw [ae_restrict_iff' measurableSet_Ioo]
  filter_upwards [M.ae_notMem_cornerRadii] with r hoff hr
  exact hgood r hr hoff

/-- **Corner elimination at `p = 2`.**  This is the form in which the off-corner second-moment
derivative of Lemma I.4.1 is consumed by the radius integration: the pointwise off-corner statement
is needed only on a dense set of non-corner radii, and it then holds almost everywhere. -/
theorem ae_hasDerivAt_of_offCorner_two {a b : ℝ} (D : ℝ → ℝ)
    (hgood : ∀ u ∈ Set.Ioo a b, u ∉ M.cornerRadii →
      HasDerivAt (fun r => M.cutMomentReal 2 r) (D u) u) :
    ∀ᵐ r ∂(volume.restrict (Set.Ioo a b)),
      HasDerivAt (fun r => M.cutMomentReal 2 r) (D r) r :=
  M.ae_hasDerivAt_of_offCorner 2 D hgood

/-- **Capstone for the `p = 2` radius picture.**  Almost every radius of a window on which the second
moment is finite is simultaneously off-corner, a differentiability point of `r ↦ E_{β_c,r}|K|²`, and
a point where the radius derivative is nonnegative.  Together with
`ae_hasDerivAt_of_offCorner_two` this is the complete radius-variable input needed to integrate the
`p = 2` case of Lemma I.4.1 over a radius window. -/
theorem ae_radius_picture_two {a b : ℝ} (hab : a < b) (hfin : M.cutMoment 2 b ≠ ⊤) :
    ∀ᵐ r ∂(volume.restrict (Set.Ioo a b)),
      r ∉ M.cornerRadii ∧ DifferentiableAt ℝ (fun r => M.cutMomentReal 2 r) r ∧
        0 ≤ deriv (fun r => M.cutMomentReal 2 r) r := by
  filter_upwards [M.ae_differentiableAt_and_notMem_cornerRadii_two hab hfin,
    M.ae_deriv_nonneg_cutMomentReal_two hab hfin] with r h hd
  exact ⟨h.1, h.2, hd⟩


/-! ## 7. The `p = 2` radius-integration corollaries -/

/-- **Radius bounds at `p = 2` with the corner finiteness discharged.**  The landed
`abs_sub_le_integral_cutMomentReal` asks the caller for `(M.cornerRadii ∩ Ioo a b).Finite`; that is
`finite_cornerRadii_inter_Ioo`, supplied here.  What remains is the off-corner differentiability
plus majorant `hgood`, which is where the source's `p = 2` cut-moment derivative enters. -/
theorem abs_sub_le_integral_cutMomentReal_two {a b : ℝ} (ha : 0 < a) {b' : ℝ} (hbb' : b < b')
    (hfin : M.cutMoment 2 b' ≠ ⊤) {g : ℝ → ℝ} (hgcont : ContinuousOn g (Set.Icc a b))
    (hgood : ∀ u ∈ Set.Ioo a b, u ∉ M.cornerRadii →
      DifferentiableAt ℝ (fun r => M.cutMomentReal 2 r) u ∧
        |deriv (fun r => M.cutMomentReal 2 r) u| ≤ g u) :
    ∀ x ∈ Set.Icc a b, ∀ y ∈ Set.Icc a b, x ≤ y →
      |M.cutMomentReal 2 y - M.cutMomentReal 2 x| ≤ ∫ t in x..y, g t :=
  M.abs_sub_le_integral_cutMomentReal ha 2 (by norm_num) hbb' hfin hgcont
    (M.finite_cornerRadii_inter_Ioo a b) hgood

/-- **Absolute continuity of the second cutoff moment in the radius**, with the corner finiteness
discharged.  This is the exact `p = 2` regularity that the radius integration of Lemma I.4.1 needs;
the remaining input is the off-corner derivative and its majorant. -/
theorem cutMomentReal_absolutelyContinuousOn_two {a b : ℝ} (ha : 0 < a) (hab : a ≤ b) {b' : ℝ}
    (hbb' : b < b') (hfin : M.cutMoment 2 b' ≠ ⊤) {g : ℝ → ℝ}
    (hgcont : ContinuousOn g (Set.Icc a b))
    (hgood : ∀ u ∈ Set.Ioo a b, u ∉ M.cornerRadii →
      DifferentiableAt ℝ (fun r => M.cutMomentReal 2 r) u ∧
        |deriv (fun r => M.cutMomentReal 2 r) u| ≤ g u) :
    AbsolutelyContinuousOnInterval
      (fun r => M.cutMomentReal 2 r) a b :=
  M.cutMomentReal_absolutelyContinuousOn ha hab 2 (by norm_num) hbb' hfin hgcont
    (M.finite_cornerRadii_inter_Ioo a b) hgood

end SourceModelData

end PercLib.CriticalLRP.Orchestration
