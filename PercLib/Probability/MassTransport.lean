/-
Copyright (c) 2026 PercLib contributors. Released under Apache 2.0.
Q-83: the mass-transport principle on groups. New for this project; no upstream proof is
copied. No new definition: the action, its measure preservation and the diagonal
invariance of the transport are explicit hypotheses.
-/
module

public import PercLib.Percolation.Bond.Basic
public import PercLib.Probability.Transport.Reindexing
public import Mathlib.MeasureTheory.Integral.Lebesgue.Countable
public import Mathlib.Topology.Algebra.InfiniteSum.ENNReal

/-!
# The mass-transport principle

* `tsum_mass_transport` (IHJ3): for a group `Γ` and a diagonally invariant
  `F : Γ → Γ → ℝ≥0∞`, the mass sent out of `1` equals the mass received at `1`.
* `lintegral_mass_transport` (K5ZX): the averaged version for a countable group acting by
  measure-preserving maps, with the action given as an explicit family of maps.
* `law_mass_transport`: the instance for bond percolation, where `Γ` acts on
  `Config Γ` by `ω ↦ Sym2.map (g * ·) '' ω` and the profile is left-invariant.

Each has an additive version (`ℤ^d`, the hierarchical lattice, ...).
-/

@[expose] public section

noncomputable section

open MeasureTheory
open scoped ENNReal

namespace PercLib.Probability

/-- **Mass-transport principle on a group** (IHJ3). If `F (g * x) (g * y) = F x y` for all
`g x y`, then `∑' x, F 1 x = ∑' x, F x 1`. -/
@[to_additive tsum_mass_transport_add /-- **Mass-transport principle on an additive group** (IHJ3). If
`F (g + x) (g + y) = F x y` for all `g x y`, then `∑' x, F 0 x = ∑' x, F x 0`. -/]
theorem tsum_mass_transport {Γ : Type*} [Group Γ] (F : Γ → Γ → ℝ≥0∞)
    (hF : ∀ g x y, F (g * x) (g * y) = F x y) :
    ∑' x, F 1 x = ∑' x, F x 1 := by
  have h : ∀ x, F x 1 = F 1 x⁻¹ := fun x => by
    rw [← hF x⁻¹ x 1, inv_mul_cancel, mul_one]
  simp_rw [h]
  exact ((Equiv.inv Γ).tsum_eq (fun x => F 1 x)).symm

/-- **Mass-transport principle for an invariant random transport** (K5ZX), with the action
given as a family of measure-preserving maps `act g`. No group-action axioms are needed. -/
@[to_additive lintegral_mass_transport_add /-- **Mass-transport principle for an invariant random transport** (K5ZX),
additive version. -/]
theorem lintegral_mass_transport {Γ Ω : Type*} [Group Γ] [Countable Γ] [MeasurableSpace Ω]
    {μ : Measure Ω} (act : Γ → Ω → Ω) (hact : ∀ g, MeasurePreserving (act g) μ μ)
    (t : Ω → Γ → Γ → ℝ≥0∞) (ht : ∀ x y, Measurable fun ω => t ω x y)
    (hinv : ∀ ω g x y, t (act g ω) (g * x) (g * y) = t ω x y) :
    ∫⁻ ω, ∑' y, t ω 1 y ∂μ = ∫⁻ ω, ∑' x, t ω x 1 ∂μ := by
  rw [lintegral_tsum fun y => (ht 1 y).aemeasurable,
    lintegral_tsum fun x => (ht x 1).aemeasurable]
  apply tsum_mass_transport (fun x y => ∫⁻ ω, t ω x y ∂μ)
  intro g x y
  rw [← (hact g).lintegral_comp (ht (g * x) (g * y))]
  simp only [hinv]

/-- K5ZX for a measure-preserving `MulAction`. -/
@[to_additive /-- K5ZX for a measure-preserving `AddAction`. -/]
theorem lintegral_mass_transport_smul {Γ Ω : Type*} [Group Γ] [Countable Γ]
    [MeasurableSpace Ω] [MulAction Γ Ω] {μ : Measure Ω}
    (hact : ∀ g : Γ, MeasurePreserving (fun ω : Ω => g • ω) μ μ)
    (t : Ω → Γ → Γ → ℝ≥0∞) (ht : ∀ x y, Measurable fun ω => t ω x y)
    (hinv : ∀ ω (g : Γ) x y, t (g • ω) (g * x) (g * y) = t ω x y) :
    ∫⁻ ω, ∑' y, t ω 1 y ∂μ = ∫⁻ ω, ∑' x, t ω x 1 ∂μ :=
  lintegral_mass_transport (fun g ω => g • ω) hact t ht hinv

end PercLib.Probability

namespace PercLib.Percolation.Bond
open PercLib.Probability

/-- Left multiplication relabels pairs by an equivalence. -/
@[to_additive /-- Left addition relabels pairs by an equivalence. -/]
theorem exists_equiv_sym2Map_mul_left {Γ : Type*} [Group Γ] (g : Γ) :
    ∃ E : Sym2 Γ ≃ Sym2 Γ, ⇑E = Sym2.map (g * ·) :=
  ⟨{ toFun := Sym2.map (g * ·)
     invFun := Sym2.map (g⁻¹ * ·)
     left_inv := by intro b; induction b using Sym2.ind with | _ x y => simp
     right_inv := by intro b; induction b using Sym2.ind with | _ x y => simp }, rfl⟩

/-- For a left-invariant profile, the action `ω ↦ Sym2.map (g * ·) '' ω` of `Γ` on
configurations preserves `law q`. -/
@[to_additive /-- For a translation-invariant profile, `ω ↦ Sym2.map (g + ·) '' ω`
preserves `law q`. -/]
theorem measurePreserving_image_sym2Map_mul_left {Γ : Type*} [Group Γ]
    (q : Sym2 Γ → unitInterval) (hq : ∀ g x y : Γ, q s(g * x, g * y) = q s(x, y)) (g : Γ) :
    MeasurePreserving (fun ω : Config Γ => Sym2.map (g * ·) '' ω) (law q) (law q) := by
  obtain ⟨E, hE⟩ := exists_equiv_sym2Map_mul_left g
  refine ⟨?_, ?_⟩
  · rw [← hE]
    exact measurable_image_equiv E
  · exact prodBernoulli_map_image_sym2_invariant q (Equiv.mulLeft g) fun b => by
      induction b using Sym2.ind with | _ x y => exact hq g x y

/-- **Mass-transport principle for bond percolation** on a countable group with a
left-invariant profile. -/
@[to_additive law_mass_transport_add /-- **Mass-transport principle for bond percolation** on a countable additive
group with a translation-invariant profile. -/]
theorem law_mass_transport {Γ : Type*} [Group Γ] [Countable Γ]
    (q : Sym2 Γ → unitInterval) (hq : ∀ g x y : Γ, q s(g * x, g * y) = q s(x, y))
    (t : Config Γ → Γ → Γ → ℝ≥0∞) (ht : ∀ x y, Measurable fun ω => t ω x y)
    (hinv : ∀ ω (g : Γ) x y, t (Sym2.map (g * ·) '' ω) (g * x) (g * y) = t ω x y) :
    ∫⁻ ω, ∑' y, t ω 1 y ∂(law q) = ∫⁻ ω, ∑' x, t ω x 1 ∂(law q) :=
  lintegral_mass_transport (fun g ω => Sym2.map (g * ·) '' ω)
    (measurePreserving_image_sym2Map_mul_left q hq) t ht hinv

/-! ### Non-vacuity witnesses (D-5) -/

/-- On `ℤ`, the transport `F x y = 1` if `y = x + 1` (else `0`) sends mass `1` out of `0`
and `0` receives mass `1`. -/
example : (∑' y : ℤ, if y = 0 + 1 then (1 : ℝ≥0∞) else 0) = 1 ∧
    (∑' x : ℤ, if (0 : ℤ) = x + 1 then (1 : ℝ≥0∞) else 0) = 1 ∧
    (∑' y : ℤ, if y = 0 + 1 then (1 : ℝ≥0∞) else 0) =
      ∑' x : ℤ, if (0 : ℤ) = x + 1 then (1 : ℝ≥0∞) else 0 := by
  have h1 : (∑' y : ℤ, if y = 0 + 1 then (1 : ℝ≥0∞) else 0) = 1 := tsum_ite_eq _ _
  have h2 : (∑' x : ℤ, if (0 : ℤ) = x + 1 then (1 : ℝ≥0∞) else 0) = 1 := by
    have : (fun x : ℤ => if (0 : ℤ) = x + 1 then (1 : ℝ≥0∞) else 0) =
        fun x => if x = -1 then 1 else 0 := by
      funext x
      congr 1
      apply propext
      omega
    rw [this, tsum_ite_eq]
  refine ⟨h1, h2, ?_⟩
  exact tsum_mass_transport_add (fun x y : ℤ => if y = x + 1 then (1 : ℝ≥0∞) else 0)
    (fun g x y => by simp [add_assoc])

/-- The bond hypotheses hold on `ℤ` for every constant profile, and the averaged transport
of the same kernel (a deterministic `t`) moves mass `1`. -/
example (p : unitInterval) :
    ∫⁻ ω, ∑' y, (fun (_ : Config ℤ) (x y : ℤ) => if y = x + 1 then (1 : ℝ≥0∞) else 0) ω 0 y
        ∂(law (fun _ : Sym2 ℤ => p)) =
      ∫⁻ ω, ∑' x, (fun (_ : Config ℤ) (x y : ℤ) => if y = x + 1 then (1 : ℝ≥0∞) else 0) ω x 0
        ∂(law (fun _ : Sym2 ℤ => p)) :=
  law_mass_transport_add (fun _ => p) (fun _ _ _ => rfl)
    (fun (_ : Config ℤ) (x y : ℤ) => if y = x + 1 then (1 : ℝ≥0∞) else 0)
    (fun _ _ => measurable_const) (fun _ g x y => by simp [add_assoc])

end PercLib.Percolation.Bond
