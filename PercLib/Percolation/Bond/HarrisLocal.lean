/-
Copyright (c) 2026 PercLib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

New proofs for issue 196 (Q-36), written on 2026-11-15 by PROVER-E. No upstream proof is
copied.
-/
module

public import PercLib.Percolation.Bond.LocalConnectivity
public import PercLib.Probability.OpenEventHarris

/-!
# Harris corollaries for internal and escape events

Internal connection events `{x ↔ y in (openGraph ω).induce S}` are increasing and, for a
countable domain `S`, measurable. Harris therefore gives positive correlation of internal
connections, internal supermultiplicativity `τ^S(x,y) τ^S(y,z) ≤ τ^S(x,z)`, the escape
transfer `τ(x,y) P(y ↔ Fᶜ) ≤ P(x ↔ Fᶜ)` and its internal version, and the bound for
finitely many internal connections. This file adds no definition.
-/

@[expose] public section

open MeasureTheory Set PercLib.Probability

namespace PercLib.Percolation.Bond

variable {V : Type*}

/-- **Harris for two internal connection events.** -/
theorem law_harris_localConn [Countable V] (q : Sym2 V → unitInterval) (S : Set V)
    [Countable S] (x y u v : S) :
    law q {ω | ((openGraph ω).induce S).Reachable x y} *
        law q {ω | ((openGraph ω).induce S).Reachable u v} ≤
      law q ({ω | ((openGraph ω).induce S).Reachable x y} ∩
        {ω | ((openGraph ω).induce S).Reachable u v}) :=
  prodBernoulli_harris q (fun _ _ h hω => localConn_mono_config S x y h hω)
    (fun _ _ h hω => localConn_mono_config S u v h hω)
    (measurableSet_localConn S x y) (measurableSet_localConn S u v)

/-- **Internal supermultiplicativity.** -/
theorem law_localConn_mul_le [Countable V] (q : Sym2 V → unitInterval) (S : Set V)
    [Countable S] (x y z : S) :
    law q {ω | ((openGraph ω).induce S).Reachable x y} *
        law q {ω | ((openGraph ω).induce S).Reachable y z} ≤
      law q {ω | ((openGraph ω).induce S).Reachable x z} :=
  (law_harris_localConn q S x y y z).trans (measure_mono fun _ ⟨h1, h2⟩ => h1.trans h2)

/-- **Escape transfer.** If `x` is joined to `y` and `y` escapes `F`, then `x` escapes `F`. -/
theorem tau_mul_law_escape_le [Countable V] (q : Sym2 V → unitInterval) (x y : V) (F : Set V) :
    tau q x y * law q (⋃ w ∈ Fᶜ, conn y w) ≤ law q (⋃ w ∈ Fᶜ, conn x w) := by
  refine (prodBernoulli_harris q (isUpperSet_conn x y) (isUpperSet_escape y F)
    (measurableSet_conn x y) (measurableSet_escape y F)).trans (measure_mono ?_)
  rintro ω ⟨hxy, hy⟩
  obtain ⟨w, hw, hyw⟩ := mem_iUnion₂.1 hy
  exact mem_iUnion₂.2 ⟨w, hw, conn_trans hxy hyw⟩

/-- The event that `x` is joined inside `S` to a vertex of `S` outside `F`. -/
theorem measurableSet_localEscape [Countable V] (S : Set V) [Countable S] (x : S) (F : Set V) :
    MeasurableSet {ω : Config V | ∃ w : S, (w : V) ∉ F ∧
      ((openGraph ω).induce S).Reachable x w} := by
  have : {ω : Config V | ∃ w : S, (w : V) ∉ F ∧ ((openGraph ω).induce S).Reachable x w} =
      ⋃ w : S, {_ω : Config V | (w : V) ∉ F} ∩
        {ω : Config V | ((openGraph ω).induce S).Reachable x w} := by
    ext ω
    simp
  rw [this]
  exact MeasurableSet.iUnion fun w => (MeasurableSet.const _).inter (measurableSet_localConn S x w)

/-- **Internal escape transfer.** -/
theorem law_localConn_mul_localEscape_le [Countable V] (q : Sym2 V → unitInterval) (S : Set V)
    [Countable S] (x y : S) (F : Set V) :
    law q {ω | ((openGraph ω).induce S).Reachable x y} *
        law q {ω : Config V | ∃ w : S, (w : V) ∉ F ∧ ((openGraph ω).induce S).Reachable y w} ≤
      law q {ω : Config V | ∃ w : S, (w : V) ∉ F ∧ ((openGraph ω).induce S).Reachable x w} := by
  refine (prodBernoulli_harris q (fun _ _ h hω => localConn_mono_config S x y h hω)
    (fun _ _ h hω => by
      obtain ⟨w, hw, hyw⟩ := hω
      exact ⟨w, hw, localConn_mono_config S y w h hyw⟩)
    (measurableSet_localConn S x y) (measurableSet_localEscape S y F)).trans
    (measure_mono ?_)
  rintro ω ⟨hxy, w, hw, hyw⟩
  exact ⟨w, hw, SimpleGraph.Reachable.trans hxy hyw⟩

/-- **Harris for finitely many internal connections.** -/
theorem prod_law_localConn_le [Countable V] (q : Sym2 V → unitInterval) (S : Set V)
    [Countable S] {α : Type*} (s : Finset α) (x y : α → S) :
    ∏ i ∈ s, law q {ω | ((openGraph ω).induce S).Reachable (x i) (y i)} ≤
      law q (⋂ i ∈ s, {ω | ((openGraph ω).induce S).Reachable (x i) (y i)}) :=
  prodBernoulli_prod_le_biInter q s _
    (fun i _ _ _ h hω => localConn_mono_config S (x i) (y i) h hω)
    (fun i _ => measurableSet_localConn S (x i) (y i))

/-! ### Non-vacuity -/

/-- With `S = univ`, internal supermultiplicativity is the full one. -/
example (q : Sym2 ℕ → unitInterval) (x y z : (univ : Set ℕ)) :
    law q {ω | ((openGraph ω).induce univ).Reachable x y} *
        law q {ω | ((openGraph ω).induce univ).Reachable y z} ≤
      law q {ω | ((openGraph ω).induce univ).Reachable x z} :=
  law_localConn_mul_le q univ x y z

/-- If `y ∉ F`, the escape of `y` from `F` is sure, and the transfer gives `τ(x,y) ≤ P(x ↔ Fᶜ)`. -/
example (q : Sym2 ℕ → unitInterval) (x : ℕ) :
    tau q x 0 ≤ law q (⋃ w ∈ (∅ : Set ℕ)ᶜ, conn x w) := by
  have h := tau_mul_law_escape_le q x 0 ∅
  have hsure : (⋃ w ∈ (∅ : Set ℕ)ᶜ, conn 0 w : Set (Config ℕ)) = univ :=
    eq_univ_of_forall fun ω => mem_iUnion₂.2 ⟨0, by simp, mem_conn_iff ω 0 0 |>.2 (.refl _)⟩
  rw [hsure, measure_univ, mul_one] at h
  exact h

end PercLib.Percolation.Bond
