/-
Copyright (c) 2026 PercLib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

New proofs for issue 145 (Q-19), written on 2026-11-14 by PROVER-E. No upstream proof is
copied.
-/
module

public import Mathlib.Analysis.Calculus.Deriv.MeanValue
public import PercLib.Percolation.Bond.Intensity.Defs
public import PercLib.Percolation.Bond.LocalConnectivity
public import PercLib.Probability.RussoFinset

/-!
# Russo's formula for finite-volume connection probabilities

For a finite vertex set `S` and `x y : S`, the internal connection event
`{ω | ((openGraph ω).induce S).Reachable x y}` depends only on the internal pairs
`S.sym2`. In the intensity parametrisation `q_b = intensityProfile J b` its probability is
differentiable in `b` within `[0, ∞)`, with derivative

`∑_{e ∈ S.sym2} J(e) e^{-b J(e)} P_b(e is pivotal)`

(`law_localConn_hasDerivWithinAt`). Loops are never pivotal, the probability is monotone
in `b` on `[0, ∞)`, and the derivative is at most the sum of `J` over the off-diagonal
internal pairs. The finite-volume susceptibility `∑_{y ∈ S} P(x ↔ y in S)` has the summed
derivative. This file adds no definition.
-/

@[expose] public section

open MeasureTheory Set PercLib.Probability
open scoped NNReal
open Classical

namespace PercLib.Percolation.Bond

variable {V : Type*}

/-- An internal connection event depends only on the internal pairs. -/
theorem localConn_dependsOn_sym2 (S : Finset V) (x y : (S : Set V)) (ω : Config V) :
    ω ∈ {ω : Config V | ((openGraph ω).induce (S : Set V)).Reachable x y} ↔
      ω ∩ ↑S.sym2 ∈ {ω : Config V | ((openGraph ω).induce (S : Set V)).Reachable x y} := by
  refine localConn_iff_of_agree (S : Set V) x y fun a ha b hb => ?_
  have : s(a, b) ∈ (S.sym2 : Set (Sym2 V)) := Finset.mk_mem_sym2_iff.2 ⟨ha, hb⟩
  exact ⟨fun h => ⟨h, this⟩, fun h => h.1⟩

/-- Internal connection events are increasing. -/
theorem isUpperSet_localConn (S : Set V) (x y : S) :
    IsUpperSet {ω : Config V | ((openGraph ω).induce S).Reachable x y} :=
  fun _ _ h hxy => localConn_mono_config S x y h hxy

/-- Opening or closing a loop does not change the open graph. -/
theorem openGraph_insert_of_isDiag (ω : Config V) {e : Sym2 V} (he : e.IsDiag) :
    openGraph (insert e ω) = openGraph ω := by
  ext a b
  rw [openGraph_adj_iff, openGraph_adj_iff, mem_insert_iff]
  constructor
  · rintro ⟨h | h, hab⟩
    · exact absurd (h ▸ he) (Sym2.mk_isDiag_iff.not.2 hab)
    · exact ⟨h, hab⟩
  · rintro ⟨h, hab⟩
    exact ⟨Or.inr h, hab⟩

/-- Closing a loop does not change the open graph. -/
theorem openGraph_sdiff_of_isDiag (ω : Config V) {e : Sym2 V} (he : e.IsDiag) :
    openGraph (ω \ {e}) = openGraph ω := by
  rw [← openGraph_insert_of_isDiag (ω \ {e}) he, insert_sdiff_singleton,
    openGraph_insert_of_isDiag ω he]

/-- **Loops are never pivotal** for an event defined through the open graph. -/
theorem pivotal_eq_empty_of_isDiag {A : Set (Config V)}
    (hA : ∀ ω ω' : Config V, openGraph ω = openGraph ω' → (ω ∈ A ↔ ω' ∈ A))
    {e : Sym2 V} (he : e.IsDiag) :
    {ω : Config V | insert e ω ∈ A ∧ ω \ {e} ∉ A} = ∅ := by
  ext ω
  simp only [mem_ofPred_eq, mem_empty_iff_false, iff_false, not_and, not_not]
  intro h
  exact (hA _ _ ((openGraph_sdiff_of_isDiag ω he).trans
    (openGraph_insert_of_isDiag ω he).symm)).2 h

/-- On `[0, ∞)` the canonical intensity profile has the explicit exponential form. -/
theorem intensityProfile_toNNReal_coe (J : Sym2 V → ℝ≥0) {b : ℝ} (hb : 0 ≤ b) (e : Sym2 V) :
    (intensityProfile J b.toNNReal e : ℝ) = 1 - Real.exp (-b * J e) := by
  change 1 - Real.exp (-((b.toNNReal : ℝ≥0) : ℝ) * (J e : ℝ)) = _
  rw [Real.coe_toNNReal b hb]

/-- **Russo's formula for an internal connection probability**, in the intensity
parametrisation, as a derivative within `[0, ∞)`. -/
theorem law_localConn_hasDerivWithinAt (J : Sym2 V → ℝ≥0) (S : Finset V) (x y : (S : Set V))
    {β : ℝ} (hβ : 0 ≤ β) :
    HasDerivWithinAt
      (fun b => (law (intensityProfile J b.toNNReal)).real
        {ω : Config V | ((openGraph ω).induce (S : Set V)).Reachable x y})
      (∑ e ∈ S.sym2, ((J e : ℝ) * Real.exp (-β * J e)) *
        (law (intensityProfile J β.toNNReal)).real
          {ω | insert e ω ∈ {ω : Config V | ((openGraph ω).induce (S : Set V)).Reachable x y} ∧
            ω \ {e} ∉ {ω : Config V | ((openGraph ω).induce (S : Set V)).Reachable x y}})
      (Ici 0) β :=
  event_intensity_real_hasDerivWithinAt_of_dependsOn (fun e => (J e : ℝ)) S.sym2 β
    (fun b => intensityProfile J b.toNNReal) (Ici 0)
    (fun e _ => intensityProfile_toNNReal_coe J hβ e)
    (fun _ hb e _ => intensityProfile_toNNReal_coe J (mem_Ici.1 hb) e)
    (isUpperSet_localConn _ x y) (localConn_dependsOn_sym2 S x y)

/-- Internal connection events are unchanged by loops. -/
theorem localConn_congr_openGraph (S : Set V) (x y : S) (ω ω' : Config V)
    (h : openGraph ω = openGraph ω') :
    ω ∈ {ω : Config V | ((openGraph ω).induce S).Reachable x y} ↔
      ω' ∈ {ω : Config V | ((openGraph ω).induce S).Reachable x y} := by
  simp only [mem_ofPred_eq, h]

/-- **The Russo derivative is at most the sum of `J` over off-diagonal internal pairs.** -/
theorem localConn_russo_le (J : Sym2 V → ℝ≥0) (S : Finset V) (x y : (S : Set V)) {β : ℝ}
    (hβ : 0 ≤ β) :
    (∑ e ∈ S.sym2, ((J e : ℝ) * Real.exp (-β * J e)) *
        (law (intensityProfile J β.toNNReal)).real
          {ω | insert e ω ∈ {ω : Config V | ((openGraph ω).induce (S : Set V)).Reachable x y} ∧
            ω \ {e} ∉ {ω : Config V | ((openGraph ω).induce (S : Set V)).Reachable x y}}) ≤
      ∑ e ∈ S.sym2.filter (fun e => ¬ e.IsDiag), (J e : ℝ) := by
  classical
  rw [← Finset.sum_filter_add_sum_filter_not S.sym2 (fun e => ¬ e.IsDiag)]
  have hdiag : ∑ e ∈ S.sym2.filter (fun e => ¬ ¬ e.IsDiag), ((J e : ℝ) * Real.exp (-β * J e)) *
      (law (intensityProfile J β.toNNReal)).real
        {ω | insert e ω ∈ {ω : Config V | ((openGraph ω).induce (S : Set V)).Reachable x y} ∧
          ω \ {e} ∉ {ω : Config V | ((openGraph ω).induce (S : Set V)).Reachable x y}} = 0 := by
    refine Finset.sum_eq_zero fun e he => ?_
    have he' : e.IsDiag := not_not.1 (Finset.mem_filter.1 he).2
    rw [pivotal_eq_empty_of_isDiag (localConn_congr_openGraph _ x y) he', measureReal_empty,
      mul_zero]
  rw [hdiag, add_zero]
  refine Finset.sum_le_sum fun e _ => ?_
  have hexp : Real.exp (-β * J e) ≤ 1 :=
    Real.exp_le_one_iff.2 (by nlinarith [(J e).coe_nonneg])
  have hP : (law (intensityProfile J β.toNNReal)).real
      {ω | insert e ω ∈ {ω : Config V | ((openGraph ω).induce (S : Set V)).Reachable x y} ∧
        ω \ {e} ∉ {ω : Config V | ((openGraph ω).induce (S : Set V)).Reachable x y}} ≤ 1 :=
    measureReal_le_one
  calc ((J e : ℝ) * Real.exp (-β * J e)) * _ ≤ ((J e : ℝ) * 1) * 1 := by
        gcongr
    _ = J e := by ring

/-- **Internal connection probabilities increase with the intensity** on `[0, ∞)`. -/
theorem monotoneOn_law_localConn (J : Sym2 V → ℝ≥0) (S : Finset V) (x y : (S : Set V)) :
    MonotoneOn (fun b : ℝ => (law (intensityProfile J b.toNNReal)).real
      {ω : Config V | ((openGraph ω).induce (S : Set V)).Reachable x y}) (Ici 0) := by
  refine monotoneOn_of_hasDerivWithinAt_nonneg (convex_Ici 0)
    (f' := fun b => ∑ e ∈ S.sym2, ((J e : ℝ) * Real.exp (-b * J e)) *
        (law (intensityProfile J b.toNNReal)).real
          {ω | insert e ω ∈ {ω : Config V | ((openGraph ω).induce (S : Set V)).Reachable x y} ∧
            ω \ {e} ∉ {ω : Config V | ((openGraph ω).induce (S : Set V)).Reachable x y}})
    (fun b hb => (law_localConn_hasDerivWithinAt J S x y hb).continuousWithinAt)
    (fun b hb => ?_) (fun b hb => ?_)
  · rw [interior_Ici] at hb ⊢
    exact (law_localConn_hasDerivWithinAt J S x y (le_of_lt hb)).mono Ioi_subset_Ici_self
  · exact Finset.sum_nonneg fun e _ =>
      mul_nonneg (mul_nonneg (J e).coe_nonneg (Real.exp_pos _).le) measureReal_nonneg

/-- **Russo's formula for the finite-volume susceptibility** `∑_{y ∈ S} P(x ↔ y in S)`. -/
theorem sum_law_localConn_hasDerivWithinAt (J : Sym2 V → ℝ≥0) (S : Finset V)
    (x : (S : Set V)) {β : ℝ} (hβ : 0 ≤ β) :
    HasDerivWithinAt
      (fun b => ∑ y : (S : Set V), (law (intensityProfile J b.toNNReal)).real
        {ω : Config V | ((openGraph ω).induce (S : Set V)).Reachable x y})
      (∑ y : (S : Set V), ∑ e ∈ S.sym2, ((J e : ℝ) * Real.exp (-β * J e)) *
        (law (intensityProfile J β.toNNReal)).real
          {ω | insert e ω ∈ {ω : Config V | ((openGraph ω).induce (S : Set V)).Reachable x y} ∧
            ω \ {e} ∉ {ω : Config V | ((openGraph ω).induce (S : Set V)).Reachable x y}})
      (Ici 0) β :=
  HasDerivWithinAt.fun_sum fun y _ => law_localConn_hasDerivWithinAt J S x y hβ

/-! ### Non-vacuity -/

/-- A loop of positive intensity contributes nothing: on `Bool` with `S = univ`, the
pivotal event of the loop `s(false, false)` is empty. -/
example :
    {ω | insert s(false, false) ω ∈ {ω : Config Bool |
        ((openGraph ω).induce ((Finset.univ : Finset Bool) : Set Bool)).Reachable
          ⟨false, by simp⟩ ⟨true, by simp⟩} ∧
      ω \ {s(false, false)} ∉ {ω : Config Bool |
        ((openGraph ω).induce ((Finset.univ : Finset Bool) : Set Bool)).Reachable
          ⟨false, by simp⟩ ⟨true, by simp⟩}} = ∅ :=
  pivotal_eq_empty_of_isDiag (localConn_congr_openGraph _ _ _) (Sym2.mk_isDiag_iff.2 rfl)

/-- The formula applies on `S = {false, true}` with `J ≡ 1` at every `β ≥ 0`. -/
example (β : ℝ) (hβ : 0 ≤ β) :
    MonotoneOn (fun b : ℝ => (law (intensityProfile (fun _ : Sym2 Bool => 1) b.toNNReal)).real
      {ω : Config Bool | ((openGraph ω).induce ((Finset.univ : Finset Bool) : Set Bool)).Reachable
        ⟨false, by simp⟩ ⟨true, by simp⟩}) (Ici 0) ∧
    ∃ d, HasDerivWithinAt (fun b : ℝ => (law (intensityProfile (fun _ : Sym2 Bool => 1)
      b.toNNReal)).real
      {ω : Config Bool | ((openGraph ω).induce ((Finset.univ : Finset Bool) : Set Bool)).Reachable
        ⟨false, by simp⟩ ⟨true, by simp⟩}) d (Ici 0) β :=
  ⟨monotoneOn_law_localConn _ _ _ _, _, law_localConn_hasDerivWithinAt _ _ _ _ hβ⟩

end PercLib.Percolation.Bond
