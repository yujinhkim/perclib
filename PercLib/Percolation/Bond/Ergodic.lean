/-
Copyright (c) 2026 PercLib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

New for this project (issue 124, Q-8, item 3). No upstream proof is copied.
-/
module

public import PercLib.Percolation.Bond.Basic
public import PercLib.Probability.Mixing

/-!
# Ergodicity of translation-invariant bond percolation

Let `G` be an infinite additive group and `q : Sym2 G → unitInterval` a translation-invariant
profile, `q s(x + g, y + g) = q s(x, y)`. Every measurable event of bond configurations that
is invariant under all translations `ω ↦ Sym2.map (· + g) '' ω` has probability `0` or `1`,
and every measurable translation-invariant `ℕ∞`-valued observable is almost surely constant.

The issue asked also for `[Countable G]` and for an explicit hypothesis that each translation
preserves `law q`. Neither is needed: preservation follows from translation invariance of `q`
by S-1 (`prodBernoulli_map_image_sym2_invariant`), and an injective sequence in `G`, which
exists because `G` is infinite, already separates finite sets of pairs.
-/

@[expose] public section

noncomputable section

open MeasureTheory Filter Set PercLib.Probability

namespace PercLib.Percolation.Bond

variable {G : Type*} [AddGroup G]

/-- For fixed pairs `i` and `j`, only finitely many terms of an injective sequence `g` give
translations carrying `i` to `j`. -/
theorem finite_setOf_sym2Map_add_eq {g : ℕ → G} (hg : Function.Injective g) (i j : Sym2 G) :
    {n | Sym2.map (· + g n) i = j}.Finite := by
  induction i using Sym2.ind with
  | _ x y =>
  induction j using Sym2.ind with
  | _ u v =>
  refine ((Set.toFinite {-x + u, -x + v}).preimage hg.injOn).subset fun n hn => ?_
  simp only [mem_ofPred_eq, Sym2.map_mk, Sym2.eq_iff] at hn
  simp only [mem_preimage, mem_insert_iff, mem_singleton_iff]
  rcases hn with ⟨h, -⟩ | ⟨h, -⟩
  · left; rw [← h, neg_add_cancel_left]
  · right; rw [← h, neg_add_cancel_left]

/-- A translation, as a relabelling of pairs. -/
theorem exists_equiv_sym2Map_add (a : G) :
    ∃ E : Sym2 G ≃ Sym2 G, ⇑E = Sym2.map (· + a) :=
  ⟨{ toFun := Sym2.map (· + a)
     invFun := Sym2.map (· + -a)
     left_inv := by intro b; induction b using Sym2.ind with | _ x y => simp
     right_inv := by intro b; induction b using Sym2.ind with | _ x y => simp }, rfl⟩

/-- Translating configurations is measurable. -/
theorem measurable_image_sym2Map_add (a : G) :
    Measurable (fun ω : Config G => Sym2.map (· + a) '' ω) := by
  obtain ⟨E, hE⟩ := exists_equiv_sym2Map_add a
  rw [← hE]
  exact measurable_image_equiv E

/-- A translation-invariant profile gives a translation-invariant law. -/
theorem measurePreserving_image_sym2Map_add (q : Sym2 G → unitInterval)
    (hq : ∀ x y g : G, q s(x + g, y + g) = q s(x, y)) (a : G) :
    MeasurePreserving (fun ω : Config G => Sym2.map (· + a) '' ω) (law q) (law q) :=
  ⟨measurable_image_sym2Map_add a,
    prodBernoulli_map_image_sym2_invariant q (Equiv.addRight a) fun b => by
      induction b using Sym2.ind with | _ x y => exact hq x y a⟩

/-- **Ergodicity.** For a translation-invariant profile on an infinite additive group, every
measurable translation-invariant event has probability `0` or `1`. -/
theorem law_eq_zero_or_one_of_translation_invariant [Infinite G] (q : Sym2 G → unitInterval)
    (hq : ∀ x y g : G, q s(x + g, y + g) = q s(x, y))
    {A : Set (Config G)} (hA : MeasurableSet A)
    (hinv : ∀ g : G, (fun ω : Config G => Sym2.map (· + g) '' ω) ⁻¹' A = A) :
    law q A = 0 ∨ law q A = 1 := by
  set g : ℕ → G := ⇑(Infinite.natEmbedding G) with hgdef
  have hg : Function.Injective g := (Infinite.natEmbedding G).injective
  choose e he using fun n => exists_equiv_sym2Map_add (g n)
  refine prodBernoulli_eq_zero_or_one_of_invariant q e (fun n => ?_)
    (eventually_forall_notMem_of_finite e fun i j => ?_) hA fun n => ?_
  · rw [he n]
    exact measurePreserving_image_sym2Map_add q hq (g n)
  · simp only [he]
    exact finite_setOf_sym2Map_add_eq hg i j
  · rw [he n]
    exact hinv (g n)

/-- **Ergodicity for observables.** For a translation-invariant profile on an infinite
additive group, every measurable translation-invariant `ℕ∞`-valued observable is almost surely
constant. -/
theorem ae_eq_const_of_translation_invariant [Infinite G] (q : Sym2 G → unitInterval)
    (hq : ∀ x y g : G, q s(x + g, y + g) = q s(x, y))
    {f : Config G → ℕ∞} (hf : Measurable f)
    (hinv : ∀ (g : G) (ω : Config G), f (Sym2.map (· + g) '' ω) = f ω) :
    ∃ c : ℕ∞, ∀ᵐ ω ∂(law q), f ω = c := by
  set g : ℕ → G := ⇑(Infinite.natEmbedding G) with hgdef
  have hg : Function.Injective g := (Infinite.natEmbedding G).injective
  choose e he using fun n => exists_equiv_sym2Map_add (g n)
  refine prodBernoulli_ae_eq_const_of_invariant q e (fun n => ?_)
    (eventually_forall_notMem_of_finite e fun i j => ?_) hf fun n ω => ?_
  · rw [he n]
    exact measurePreserving_image_sym2Map_add q hq (g n)
  · simp only [he]
    exact finite_setOf_sym2Map_add_eq hg i j
  · rw [he n]
    exact hinv (g n) ω

/-! ### Non-vacuity -/

theorem measurableSet_nonempty_int : MeasurableSet {ω : Config ℤ | ω.Nonempty} := by
  have : {ω : Config ℤ | ω.Nonempty} = ⋃ x : ℤ, ⋃ y : ℤ, {ω | s(x, y) ∈ ω} := by
    ext ω
    simp only [mem_ofPred_eq, mem_iUnion]
    constructor
    · rintro ⟨e, he⟩
      induction e using Sym2.ind with | _ x y => exact ⟨x, y, he⟩
    · rintro ⟨x, y, h⟩
      exact ⟨_, h⟩
  rw [this]
  exact MeasurableSet.iUnion fun x => MeasurableSet.iUnion fun y => measurableSet_mem _

/-- On `ℤ` with a constant profile, the translation-invariant event that some pair is open has
probability `0` or `1`. -/
example (r : unitInterval) :
    law (fun _ : Sym2 ℤ => r) {ω : Config ℤ | ω.Nonempty} = 0 ∨
      law (fun _ : Sym2 ℤ => r) {ω : Config ℤ | ω.Nonempty} = 1 :=
  law_eq_zero_or_one_of_translation_invariant _ (fun _ _ _ => rfl) measurableSet_nonempty_int
    fun g => by
      ext ω
      simp only [mem_preimage, mem_ofPred_eq, Set.image_nonempty]

open Classical in
/-- The observable form applies to the non-constant invariant observable
`ω ↦ if ω.Nonempty then 1 else 0`. -/
example (r : unitInterval) : ∃ c : ℕ∞, ∀ᵐ ω ∂(law (fun _ : Sym2 ℤ => r)),
    (if ω.Nonempty then (1 : ℕ∞) else 0) = c :=
  ae_eq_const_of_translation_invariant _ (fun _ _ _ => rfl)
    (Measurable.ite measurableSet_nonempty_int measurable_const measurable_const)
    fun g ω => by simp only [Set.image_nonempty]

end PercLib.Percolation.Bond

end
