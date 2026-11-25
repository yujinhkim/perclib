/-
Copyright (c) 2026 PercLib contributors. Released under Apache 2.0.

Summation and evaluation of the five-point tree diagrams. This only supplies
analytic assembly: the full five-point realization remains an explicit input.
-/
module

public import PercLib.CriticalLRP.Correlation.FourthMoment.Assembly

open Set MeasureTheory
open scoped ENNReal
open PercLib.Percolation.Bond
open PercLib.CriticalLRP.TreeExpansion

@[expose] public section

namespace PercLib.CriticalLRP.TreeExpansion.FivePoint

variable {V : Type*}

theorem tsum_permute_four_three (G : V → V → V → V → V → V → V → ℝ≥0∞) :
    (∑' a, ∑' b, ∑' c, ∑' d, ∑' e, ∑' f, ∑' g, G a b c d e f g) =
      ∑' g, ∑' f, ∑' e, ∑' a, ∑' b, ∑' c, ∑' d, G a b c d e f g := by
  calc
    ∑' a, ∑' b, ∑' c, ∑' d, ∑' e, ∑' f, ∑' g, G a b c d e f g =
        ∑' a, ∑' b, ∑' c, ∑' d, ∑' e, ∑' g, ∑' f, G a b c d e f g := tsum_congr fun a => tsum_congr fun b => tsum_congr fun c => tsum_congr fun d => tsum_congr fun e => ENNReal.tsum_comm
    _ = ∑' a, ∑' b, ∑' c, ∑' d, ∑' g, ∑' e, ∑' f, G a b c d e f g := tsum_congr fun a => tsum_congr fun b => tsum_congr fun c => tsum_congr fun d => ENNReal.tsum_comm
    _ = ∑' a, ∑' b, ∑' c, ∑' g, ∑' d, ∑' e, ∑' f, G a b c d e f g := tsum_congr fun a => tsum_congr fun b => tsum_congr fun c => ENNReal.tsum_comm
    _ = ∑' a, ∑' b, ∑' g, ∑' c, ∑' d, ∑' e, ∑' f, G a b c d e f g := tsum_congr fun a => tsum_congr fun b => ENNReal.tsum_comm
    _ = ∑' a, ∑' g, ∑' b, ∑' c, ∑' d, ∑' e, ∑' f, G a b c d e f g := tsum_congr fun a => ENNReal.tsum_comm
    _ = ∑' g, ∑' a, ∑' b, ∑' c, ∑' d, ∑' e, ∑' f, G a b c d e f g := ENNReal.tsum_comm
    _ = ∑' g, ∑' a, ∑' b, ∑' c, ∑' d, ∑' f, ∑' e, G a b c d e f g := tsum_congr fun g => tsum_congr fun a => tsum_congr fun b => tsum_congr fun c => tsum_congr fun d => ENNReal.tsum_comm
    _ = ∑' g, ∑' a, ∑' b, ∑' c, ∑' f, ∑' d, ∑' e, G a b c d e f g := tsum_congr fun g => tsum_congr fun a => tsum_congr fun b => tsum_congr fun c => ENNReal.tsum_comm
    _ = ∑' g, ∑' a, ∑' b, ∑' f, ∑' c, ∑' d, ∑' e, G a b c d e f g := tsum_congr fun g => tsum_congr fun a => tsum_congr fun b => ENNReal.tsum_comm
    _ = ∑' g, ∑' a, ∑' f, ∑' b, ∑' c, ∑' d, ∑' e, G a b c d e f g := tsum_congr fun g => tsum_congr fun a => ENNReal.tsum_comm
    _ = ∑' g, ∑' f, ∑' a, ∑' b, ∑' c, ∑' d, ∑' e, G a b c d e f g := tsum_congr fun g => ENNReal.tsum_comm
    _ = ∑' g, ∑' f, ∑' a, ∑' b, ∑' c, ∑' e, ∑' d, G a b c d e f g := tsum_congr fun g => tsum_congr fun f => tsum_congr fun a => tsum_congr fun b => tsum_congr fun c => ENNReal.tsum_comm
    _ = ∑' g, ∑' f, ∑' a, ∑' b, ∑' e, ∑' c, ∑' d, G a b c d e f g := tsum_congr fun g => tsum_congr fun f => tsum_congr fun a => tsum_congr fun b => ENNReal.tsum_comm
    _ = ∑' g, ∑' f, ∑' a, ∑' e, ∑' b, ∑' c, ∑' d, G a b c d e f g := tsum_congr fun g => tsum_congr fun f => tsum_congr fun a => ENNReal.tsum_comm
    _ = ∑' g, ∑' f, ∑' e, ∑' a, ∑' b, ∑' c, ∑' d, G a b c d e f g := tsum_congr fun g => tsum_congr fun f => ENNReal.tsum_comm


theorem tsum_reverse_three (P : V → V → V → ℝ≥0∞) :
    (∑' u₃, ∑' u₂, ∑' u₁, P u₁ u₂ u₃) = ∑' u₁, ∑' u₂, ∑' u₃, P u₁ u₂ u₃ := by
  calc
    _ = ∑' u₂, ∑' u₃, ∑' u₁, P u₁ u₂ u₃ := ENNReal.tsum_comm
    _ = ∑' u₂, ∑' u₁, ∑' u₃, P u₁ u₂ u₃ := tsum_congr fun u₂ => ENNReal.tsum_comm
    _ = _ := ENNReal.tsum_comm

theorem tsum_four_mul_with {f g h k : V → ℝ≥0∞} (C : ℝ≥0∞) :
    (∑' a, ∑' b, ∑' c, ∑' d, f a * g b * h c * k d * C) =
      (∑' a, f a) * (∑' b, g b) * (∑' c, h c) * (∑' d, k d) * C := by
  rw [tsum_move_last_four]
  have hinner : ∀ d : V, (∑' a, ∑' b, ∑' c, f a * g b * h c * k d * C) =
      ((∑' a, f a) * (∑' b, g b) * (∑' c, h c)) * (k d * C) := by
    intro d
    rw [show (∑' a, ∑' b, ∑' c, f a * g b * h c * k d * C) =
        ∑' a, ∑' b, ∑' c, f a * g b * (h c * (k d * C)) from
      tsum_congr fun a => tsum_congr fun b => tsum_congr fun c => by ring]
    rw [tsum_three_mul, ENNReal.tsum_mul_right]
    ring
  calc
    (∑' d, ∑' a, ∑' b, ∑' c, f a * g b * h c * k d * C) =
        ∑' d, ((∑' a, f a) * (∑' b, g b) * (∑' c, h c)) * (k d * C) :=
      tsum_congr hinner
    _ = ∑' d, (((∑' a, f a) * (∑' b, g b) * (∑' c, h c)) * C) * k d :=
      tsum_congr fun d => by ring
    _ = _ := by rw [ENNReal.tsum_mul_left]; ring

theorem tsum_prefix_factor
    {f g h k : V → V → V → V → ℝ≥0∞} (P : V → V → V → ℝ≥0∞) :
    (∑' u₁, ∑' u₂, ∑' u₃, ∑' a, ∑' b, ∑' c, ∑' d,
      f u₁ u₂ u₃ a * g u₁ u₂ u₃ b * h u₁ u₂ u₃ c * k u₁ u₂ u₃ d * P u₁ u₂ u₃) =
      ∑' u₁, ∑' u₂, ∑' u₃,
        (∑' a, f u₁ u₂ u₃ a) * (∑' b, g u₁ u₂ u₃ b) *
          (∑' c, h u₁ u₂ u₃ c) * (∑' d, k u₁ u₂ u₃ d) * P u₁ u₂ u₃ := by
  apply tsum_congr; intro u₁; apply tsum_congr; intro u₂; apply tsum_congr; intro u₃
  exact tsum_four_mul_with (P u₁ u₂ u₃)

theorem comb_branch {R : V → V → ℝ≥0∞} {X : ℝ≥0∞} {root : V}
    (hrow : ∀ a, (∑' b, R a b) = X) :
    (∑' u₁, ∑' u₂, ∑' u₃, R root u₁ * R u₁ u₂ * R u₂ u₃) = X ^ 3 := by
  calc
    _ = ∑' u₁, ∑' u₂, R root u₁ * R u₁ u₂ * X := by
      apply tsum_congr; intro u₁; apply tsum_congr; intro u₂
      rw [ENNReal.tsum_mul_left, hrow u₂]
    _ = ∑' u₁, R root u₁ * (X * X) := by
      apply tsum_congr; intro u₁
      rw [ENNReal.tsum_mul_right, ENNReal.tsum_mul_left, hrow u₁]
      ring
    _ = X ^ 3 := by rw [ENNReal.tsum_mul_right, hrow root]; ring

theorem bal_branch {R : V → V → ℝ≥0∞} {X : ℝ≥0∞} {root : V}
    (hrow : ∀ a, (∑' b, R a b) = X) :
    (∑' u, ∑' v, ∑' w, R root u * R u v * R u w) = X ^ 3 := by
  calc
    _ = ∑' u, ∑' v, R root u * R u v * X := by
      apply tsum_congr; intro u; apply tsum_congr; intro v
      rw [ENNReal.tsum_mul_left, hrow u]
    _ = ∑' u, R root u * (X * X) := by
      apply tsum_congr; intro u
      rw [ENNReal.tsum_mul_right, ENNReal.tsum_mul_left, hrow u]
      ring
    _ = X ^ 3 := by rw [ENNReal.tsum_mul_right, hrow root]; ring

theorem tsum_combDiagram [Countable V] [AddCommGroup V] (π : Sym2 V → unitInterval)
    (hrow : ∀ a : V, (∑' b, tau π a b) = ∑' x, tau π 0 x)
    (hcol : ∀ b : V, (∑' a, tau π a b) = ∑' x, tau π 0 x)
    (root : V) :
    (∑' x₁, ∑' x₂, ∑' x₃, ∑' x₄, combDiagram π root x₁ x₂ x₃ x₄) =
      (∑' x, tau π 0 x) ^ 7 := by
  unfold combDiagram
  simp_rw [show ∀ x₁ x₂ x₃ x₄ u₁ u₂ u₃,
      tau π root u₁ * tau π x₁ u₁ * tau π u₁ u₂ * tau π x₂ u₂ * tau π u₂ u₃ *
          tau π x₃ u₃ * tau π x₄ u₃ =
        tau π x₁ u₁ * tau π x₂ u₂ * tau π x₃ u₃ * tau π x₄ u₃ *
          (tau π root u₁ * tau π u₁ u₂ * tau π u₂ u₃) from
    fun x₁ x₂ x₃ x₄ u₁ u₂ u₃ => by ring]
  rw [tsum_permute_four_three, tsum_reverse_three]
  rw [tsum_prefix_factor (P := fun u₁ u₂ u₃ =>
    tau π root u₁ * tau π u₁ u₂ * tau π u₂ u₃)]
  simp only [hcol]
  rw [tsum_const_mul_three, comb_branch (R := tau π) hrow]
  ring

theorem tsum_balDiagram [Countable V] [AddCommGroup V] (π : Sym2 V → unitInterval)
    (hrow : ∀ a : V, (∑' b, tau π a b) = ∑' x, tau π 0 x)
    (hcol : ∀ b : V, (∑' a, tau π a b) = ∑' x, tau π 0 x)
    (root : V) :
    (∑' x₁, ∑' x₂, ∑' x₃, ∑' x₄, balDiagram π root x₁ x₂ x₃ x₄) =
      (∑' x, tau π 0 x) ^ 7 := by
  unfold balDiagram
  simp_rw [show ∀ x₁ x₂ x₃ x₄ u v w,
      tau π root u * tau π u v * tau π x₁ v * tau π x₂ v * tau π u w *
          tau π x₃ w * tau π x₄ w =
        tau π x₁ v * tau π x₂ v * tau π x₃ w * tau π x₄ w *
          (tau π root u * tau π u v * tau π u w) from
    fun x₁ x₂ x₃ x₄ u v w => by ring]
  rw [tsum_permute_four_three, tsum_reverse_three]
  rw [tsum_prefix_factor (P := fun u v w =>
    tau π root u * tau π u v * tau π u w)]
  simp only [hcol]
  rw [tsum_const_mul_three, bal_branch (R := tau π) hrow]
  ring



private theorem tsum_tuple4_reindex
    (D : V × V × V × V → ℝ≥0∞) (e : (V × V × V × V) ≃ (V × V × V × V)) :
    (∑' a, ∑' b, ∑' c, ∑' d, D (e (a, b, c, d))) =
      ∑' a, ∑' b, ∑' c, ∑' d, D (a, b, c, d) := by
  simp_rw [← ENNReal.tsum_prod]
  exact Equiv.tsum_eq e D


theorem tsum_comb_acbd [Countable V] [AddCommGroup V] (π : Sym2 V → unitInterval)
    (hrow : ∀ a : V, (∑' b, tau π a b) = ∑' x, tau π 0 x)
    (hcol : ∀ b : V, (∑' a, tau π a b) = ∑' x, tau π 0 x)
    (root : V) :
    (∑' a, ∑' b, ∑' c, ∑' d, combDiagram π root a c b d) =
      (∑' x, tau π 0 x) ^ 7 := by
  let e : (V × V × V × V) ≃ (V × V × V × V) :=
    { toFun := fun (a, b, c, d) => (a, c, b, d),
       invFun := fun (a, b, c, d) => (a, c, b, d),
       left_inv := by rintro ⟨a, b, c, d⟩; rfl,
       right_inv := by rintro ⟨a, b, c, d⟩; rfl }
  exact (tsum_tuple4_reindex (D := fun (a, b, c, d) => combDiagram π root a c b d) e).symm.trans
    (tsum_combDiagram π hrow hcol root)


theorem tsum_comb_adbc [Countable V] [AddCommGroup V] (π : Sym2 V → unitInterval)
    (hrow : ∀ a : V, (∑' b, tau π a b) = ∑' x, tau π 0 x)
    (hcol : ∀ b : V, (∑' a, tau π a b) = ∑' x, tau π 0 x)
    (root : V) :
    (∑' a, ∑' b, ∑' c, ∑' d, combDiagram π root a d b c) =
      (∑' x, tau π 0 x) ^ 7 := by
  let e : (V × V × V × V) ≃ (V × V × V × V) :=
    { toFun := fun (a, b, c, d) => (a, c, d, b),
       invFun := fun (a, b, c, d) => (a, d, b, c),
       left_inv := by rintro ⟨a, b, c, d⟩; rfl,
       right_inv := by rintro ⟨a, b, c, d⟩; rfl }
  exact (tsum_tuple4_reindex (D := fun (a, b, c, d) => combDiagram π root a d b c) e).symm.trans
    (tsum_combDiagram π hrow hcol root)


theorem tsum_comb_bacd [Countable V] [AddCommGroup V] (π : Sym2 V → unitInterval)
    (hrow : ∀ a : V, (∑' b, tau π a b) = ∑' x, tau π 0 x)
    (hcol : ∀ b : V, (∑' a, tau π a b) = ∑' x, tau π 0 x)
    (root : V) :
    (∑' a, ∑' b, ∑' c, ∑' d, combDiagram π root b a c d) =
      (∑' x, tau π 0 x) ^ 7 := by
  let e : (V × V × V × V) ≃ (V × V × V × V) :=
    { toFun := fun (a, b, c, d) => (b, a, c, d),
       invFun := fun (a, b, c, d) => (b, a, c, d),
       left_inv := by rintro ⟨a, b, c, d⟩; rfl,
       right_inv := by rintro ⟨a, b, c, d⟩; rfl }
  exact (tsum_tuple4_reindex (D := fun (a, b, c, d) => combDiagram π root b a c d) e).symm.trans
    (tsum_combDiagram π hrow hcol root)


theorem tsum_comb_bcad [Countable V] [AddCommGroup V] (π : Sym2 V → unitInterval)
    (hrow : ∀ a : V, (∑' b, tau π a b) = ∑' x, tau π 0 x)
    (hcol : ∀ b : V, (∑' a, tau π a b) = ∑' x, tau π 0 x)
    (root : V) :
    (∑' a, ∑' b, ∑' c, ∑' d, combDiagram π root b c a d) =
      (∑' x, tau π 0 x) ^ 7 := by
  let e : (V × V × V × V) ≃ (V × V × V × V) :=
    { toFun := fun (a, b, c, d) => (c, a, b, d),
       invFun := fun (a, b, c, d) => (b, c, a, d),
       left_inv := by rintro ⟨a, b, c, d⟩; rfl,
       right_inv := by rintro ⟨a, b, c, d⟩; rfl }
  exact (tsum_tuple4_reindex (D := fun (a, b, c, d) => combDiagram π root b c a d) e).symm.trans
    (tsum_combDiagram π hrow hcol root)


theorem tsum_comb_bdac [Countable V] [AddCommGroup V] (π : Sym2 V → unitInterval)
    (hrow : ∀ a : V, (∑' b, tau π a b) = ∑' x, tau π 0 x)
    (hcol : ∀ b : V, (∑' a, tau π a b) = ∑' x, tau π 0 x)
    (root : V) :
    (∑' a, ∑' b, ∑' c, ∑' d, combDiagram π root b d a c) =
      (∑' x, tau π 0 x) ^ 7 := by
  let e : (V × V × V × V) ≃ (V × V × V × V) :=
    { toFun := fun (a, b, c, d) => (c, a, d, b),
       invFun := fun (a, b, c, d) => (b, d, a, c),
       left_inv := by rintro ⟨a, b, c, d⟩; rfl,
       right_inv := by rintro ⟨a, b, c, d⟩; rfl }
  exact (tsum_tuple4_reindex (D := fun (a, b, c, d) => combDiagram π root b d a c) e).symm.trans
    (tsum_combDiagram π hrow hcol root)


theorem tsum_comb_cabd [Countable V] [AddCommGroup V] (π : Sym2 V → unitInterval)
    (hrow : ∀ a : V, (∑' b, tau π a b) = ∑' x, tau π 0 x)
    (hcol : ∀ b : V, (∑' a, tau π a b) = ∑' x, tau π 0 x)
    (root : V) :
    (∑' a, ∑' b, ∑' c, ∑' d, combDiagram π root c a b d) =
      (∑' x, tau π 0 x) ^ 7 := by
  let e : (V × V × V × V) ≃ (V × V × V × V) :=
    { toFun := fun (a, b, c, d) => (b, c, a, d),
       invFun := fun (a, b, c, d) => (c, a, b, d),
       left_inv := by rintro ⟨a, b, c, d⟩; rfl,
       right_inv := by rintro ⟨a, b, c, d⟩; rfl }
  exact (tsum_tuple4_reindex (D := fun (a, b, c, d) => combDiagram π root c a b d) e).symm.trans
    (tsum_combDiagram π hrow hcol root)


theorem tsum_comb_cbad [Countable V] [AddCommGroup V] (π : Sym2 V → unitInterval)
    (hrow : ∀ a : V, (∑' b, tau π a b) = ∑' x, tau π 0 x)
    (hcol : ∀ b : V, (∑' a, tau π a b) = ∑' x, tau π 0 x)
    (root : V) :
    (∑' a, ∑' b, ∑' c, ∑' d, combDiagram π root c b a d) =
      (∑' x, tau π 0 x) ^ 7 := by
  let e : (V × V × V × V) ≃ (V × V × V × V) :=
    { toFun := fun (a, b, c, d) => (c, b, a, d),
       invFun := fun (a, b, c, d) => (c, b, a, d),
       left_inv := by rintro ⟨a, b, c, d⟩; rfl,
       right_inv := by rintro ⟨a, b, c, d⟩; rfl }
  exact (tsum_tuple4_reindex (D := fun (a, b, c, d) => combDiagram π root c b a d) e).symm.trans
    (tsum_combDiagram π hrow hcol root)


theorem tsum_comb_cdab [Countable V] [AddCommGroup V] (π : Sym2 V → unitInterval)
    (hrow : ∀ a : V, (∑' b, tau π a b) = ∑' x, tau π 0 x)
    (hcol : ∀ b : V, (∑' a, tau π a b) = ∑' x, tau π 0 x)
    (root : V) :
    (∑' a, ∑' b, ∑' c, ∑' d, combDiagram π root c d a b) =
      (∑' x, tau π 0 x) ^ 7 := by
  let e : (V × V × V × V) ≃ (V × V × V × V) :=
    { toFun := fun (a, b, c, d) => (c, d, a, b),
       invFun := fun (a, b, c, d) => (c, d, a, b),
       left_inv := by rintro ⟨a, b, c, d⟩; rfl,
       right_inv := by rintro ⟨a, b, c, d⟩; rfl }
  exact (tsum_tuple4_reindex (D := fun (a, b, c, d) => combDiagram π root c d a b) e).symm.trans
    (tsum_combDiagram π hrow hcol root)


theorem tsum_comb_dabc [Countable V] [AddCommGroup V] (π : Sym2 V → unitInterval)
    (hrow : ∀ a : V, (∑' b, tau π a b) = ∑' x, tau π 0 x)
    (hcol : ∀ b : V, (∑' a, tau π a b) = ∑' x, tau π 0 x)
    (root : V) :
    (∑' a, ∑' b, ∑' c, ∑' d, combDiagram π root d a b c) =
      (∑' x, tau π 0 x) ^ 7 := by
  let e : (V × V × V × V) ≃ (V × V × V × V) :=
    { toFun := fun (a, b, c, d) => (b, c, d, a),
       invFun := fun (a, b, c, d) => (d, a, b, c),
       left_inv := by rintro ⟨a, b, c, d⟩; rfl,
       right_inv := by rintro ⟨a, b, c, d⟩; rfl }
  exact (tsum_tuple4_reindex (D := fun (a, b, c, d) => combDiagram π root d a b c) e).symm.trans
    (tsum_combDiagram π hrow hcol root)


theorem tsum_comb_dbac [Countable V] [AddCommGroup V] (π : Sym2 V → unitInterval)
    (hrow : ∀ a : V, (∑' b, tau π a b) = ∑' x, tau π 0 x)
    (hcol : ∀ b : V, (∑' a, tau π a b) = ∑' x, tau π 0 x)
    (root : V) :
    (∑' a, ∑' b, ∑' c, ∑' d, combDiagram π root d b a c) =
      (∑' x, tau π 0 x) ^ 7 := by
  let e : (V × V × V × V) ≃ (V × V × V × V) :=
    { toFun := fun (a, b, c, d) => (c, b, d, a),
       invFun := fun (a, b, c, d) => (d, b, a, c),
       left_inv := by rintro ⟨a, b, c, d⟩; rfl,
       right_inv := by rintro ⟨a, b, c, d⟩; rfl }
  exact (tsum_tuple4_reindex (D := fun (a, b, c, d) => combDiagram π root d b a c) e).symm.trans
    (tsum_combDiagram π hrow hcol root)


theorem tsum_comb_dcab [Countable V] [AddCommGroup V] (π : Sym2 V → unitInterval)
    (hrow : ∀ a : V, (∑' b, tau π a b) = ∑' x, tau π 0 x)
    (hcol : ∀ b : V, (∑' a, tau π a b) = ∑' x, tau π 0 x)
    (root : V) :
    (∑' a, ∑' b, ∑' c, ∑' d, combDiagram π root d c a b) =
      (∑' x, tau π 0 x) ^ 7 := by
  let e : (V × V × V × V) ≃ (V × V × V × V) :=
    { toFun := fun (a, b, c, d) => (c, d, b, a),
       invFun := fun (a, b, c, d) => (d, c, a, b),
       left_inv := by rintro ⟨a, b, c, d⟩; rfl,
       right_inv := by rintro ⟨a, b, c, d⟩; rfl }
  exact (tsum_tuple4_reindex (D := fun (a, b, c, d) => combDiagram π root d c a b) e).symm.trans
    (tsum_combDiagram π hrow hcol root)


theorem tsum_bal_acbd [Countable V] [AddCommGroup V] (π : Sym2 V → unitInterval)
    (hrow : ∀ a : V, (∑' b, tau π a b) = ∑' x, tau π 0 x)
    (hcol : ∀ b : V, (∑' a, tau π a b) = ∑' x, tau π 0 x)
    (root : V) :
    (∑' a, ∑' b, ∑' c, ∑' d, balDiagram π root a c b d) =
      (∑' x, tau π 0 x) ^ 7 := by
  let e : (V × V × V × V) ≃ (V × V × V × V) :=
    { toFun := fun (a, b, c, d) => (a, c, b, d),
       invFun := fun (a, b, c, d) => (a, c, b, d),
       left_inv := by rintro ⟨a, b, c, d⟩; rfl,
       right_inv := by rintro ⟨a, b, c, d⟩; rfl }
  exact (tsum_tuple4_reindex (D := fun (a, b, c, d) => balDiagram π root a c b d) e).symm.trans
    (tsum_balDiagram π hrow hcol root)


theorem tsum_bal_adbc [Countable V] [AddCommGroup V] (π : Sym2 V → unitInterval)
    (hrow : ∀ a : V, (∑' b, tau π a b) = ∑' x, tau π 0 x)
    (hcol : ∀ b : V, (∑' a, tau π a b) = ∑' x, tau π 0 x)
    (root : V) :
    (∑' a, ∑' b, ∑' c, ∑' d, balDiagram π root a d b c) =
      (∑' x, tau π 0 x) ^ 7 := by
  let e : (V × V × V × V) ≃ (V × V × V × V) :=
    { toFun := fun (a, b, c, d) => (a, c, d, b),
       invFun := fun (a, b, c, d) => (a, d, b, c),
       left_inv := by rintro ⟨a, b, c, d⟩; rfl,
       right_inv := by rintro ⟨a, b, c, d⟩; rfl }
  exact (tsum_tuple4_reindex (D := fun (a, b, c, d) => balDiagram π root a d b c) e).symm.trans
    (tsum_balDiagram π hrow hcol root)

theorem tsum_fivePointDiagram [Countable V] [AddCommGroup V] (π : Sym2 V → unitInterval)
    (hrow : ∀ a : V, (∑' b, tau π a b) = ∑' x, tau π 0 x)
    (hcol : ∀ b : V, (∑' a, tau π a b) = ∑' x, tau π 0 x)
    (root : V) :
    (∑' x₁, ∑' x₂, ∑' x₃, ∑' x₄, fivePointDiagram π root x₁ x₂ x₃ x₄) =
      15 * (∑' x, tau π 0 x) ^ 7 := by
  simp only [fivePointDiagram, ENNReal.tsum_add]
  simp_rw [tsum_combDiagram π hrow hcol root, tsum_comb_acbd π hrow hcol root, tsum_comb_adbc π hrow hcol root, tsum_comb_bacd π hrow hcol root, tsum_comb_bcad π hrow hcol root, tsum_comb_bdac π hrow hcol root, tsum_comb_cabd π hrow hcol root, tsum_comb_cbad π hrow hcol root, tsum_comb_cdab π hrow hcol root, tsum_comb_dabc π hrow hcol root, tsum_comb_dbac π hrow hcol root, tsum_comb_dcab π hrow hcol root, tsum_balDiagram π hrow hcol root, tsum_bal_acbd π hrow hcol root, tsum_bal_adbc π hrow hcol root]
  ring

#print axioms PercLib.CriticalLRP.TreeExpansion.FivePoint.tsum_fivePointDiagram

end PercLib.CriticalLRP.TreeExpansion.FivePoint
