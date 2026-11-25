/-
Copyright (c) 2026 PercLib contributors. Released under Apache 2.0.
New finite-transcript proofs on the canonical Bernoulli law, using pinned mathlib
product measures and the existing PercLib block-independence API. Adaptive queries
are functions of the previously recorded bits; no independence of the random
queried set and the answers is asserted. No upstream exploration proof is copied.
-/
module

public import PercLib.Meta.Tag

public import PercLib.Probability.ProductExpectation
public import PercLib.Probability.ProdBernoulliIndependence
public import Mathlib.Data.Sym.Sym2

@[expose] public section

open MeasureTheory ProbabilityTheory Set
open scoped ENNReal Classical

namespace PercLib.Probability

variable {ι J : Type*}

/-- Distinct queried coordinates retain their Bernoulli product law. -/
theorem prodBernoulli_map_query (p : ι → unitInterval) (e : J → ι)
    (he : Function.Injective e) :
    (prodBernoulli p).map (fun ω j => e j ∈ ω) =
      Measure.infinitePi (fun j => bernoulliMeasure True False (p (e j))) := by
  rw [prodBernoulli_eq_map, Measure.map_map (by fun_prop) measurable_setOfPred]
  exact Measure.map_infinitePi_infinitePi_of_inj he

/-- A transcript on finitely many distinct coordinates has the product of its bit weights. -/
theorem prodBernoulli_transcript [Fintype J] (p : ι → unitInterval)
    (e : J → ι) (he : Function.Injective e) (b : J → Bool) :
    prodBernoulli p {ω | ∀ j, e j ∈ ω ↔ b j = true} =
      ∏ j, if b j then (unitInterval.toNNReal (p (e j)) : ℝ≥0∞)
        else (unitInterval.toNNReal (unitInterval.symm (p (e j))) : ℝ≥0∞) := by
  have h := congrArg (fun μ : Measure (J → Prop) => μ {fun j => b j = true})
    (prodBernoulli_map_query p e he)
  rw [Measure.map_apply (by fun_prop) (measurableSet_singleton _),
    Measure.infinitePi_eq_pi, Measure.pi_singleton] at h
  convert h using 1
  · congr 1
    ext ω
    simp [funext_iff]
  · apply Finset.prod_congr rfl
    intro j _
    cases b j <;> simp [bernoulliMeasure_def]

/-- An event on unqueried coordinates factors from the transcript. No positivity is needed. -/
theorem prodBernoulli_transcript_inter [Fintype J] (p : ι → unitInterval)
    (e : J → ι) (he : Function.Injective e) (b : J → Bool)
    (B : Set (Set ((Set.range e)ᶜ : Set ι))) (hB : MeasurableSet B) :
    prodBernoulli p {ω | (∀ j, e j ∈ ω ↔ b j = true) ∧
      (Subtype.val ⁻¹' ω : Set ((Set.range e)ᶜ : Set ι)) ∈ B} =
      (∏ j, if b j then (unitInterval.toNNReal (p (e j)) : ℝ≥0∞)
        else (unitInterval.toNNReal (unitInterval.symm (p (e j))) : ℝ≥0∞)) *
      prodBernoulli p {ω | (Subtype.val ⁻¹' ω : Set ((Set.range e)ᶜ : Set ι)) ∈ B} := by
  let A : Set (Set (Set.range e)) := {η | ∀ j, (⟨e j, Set.mem_range_self j⟩ : Set.range e) ∈ η ↔ b j = true}
  have hA : MeasurableSet A := by
    simp only [A, Set.ofPred_forall]
    apply MeasurableSet.iInter
    intro j
    cases b j
    · simp only [Bool.false_eq_true, iff_false]
      exact (measurableSet_mem (⟨e j, Set.mem_range_self j⟩ : Set.range e)).compl
    · simpa using measurableSet_mem (⟨e j, Set.mem_range_self j⟩ : Set.range e)
  have h := prodBernoulli_block_inter p (Set.range e) (Set.range e)ᶜ
    disjoint_compl_right A B hA hB
  change prodBernoulli p {ω | (∀ j, e j ∈ ω ↔ b j = true) ∧
      (Subtype.val ⁻¹' ω : Set ((Set.range e)ᶜ : Set ι)) ∈ B} =
    prodBernoulli p {ω | ∀ j, e j ∈ ω ↔ b j = true} *
      prodBernoulli p {ω | (Subtype.val ⁻¹' ω : Set ((Set.range e)ᶜ : Set ι)) ∈ B} at h
  rwa [prodBernoulli_transcript p e he b] at h

/-- A deterministic adaptive run follows a fixed bit string exactly on its transcript
cylinder. The next query sees only the preceding bits. Apply this at a leaf's depth;
the path to that leaf fixes all its queries. No no-repeat hypothesis is needed for
this deterministic identity. -/
@[tag "86IX"] theorem adaptive_answers_eq_iff {n : ℕ}
    (next : (k : Fin n) → (Fin k.val → Bool) → ι)
    (answers : Set ι → Fin n → Bool)
    (hrun : ∀ ω k, answers ω k = true ↔
      next k (fun j => answers ω ⟨j.val, j.isLt.trans k.isLt⟩) ∈ ω)
    (b : Fin n → Bool) (ω : Set ι) :
    answers ω = b ↔ ∀ k,
      next k (fun j => b ⟨j.val, j.isLt.trans k.isLt⟩) ∈ ω ↔ b k = true := by
  constructor
  · intro h k
    rw [← h]
    exact (hrun ω k).symm
  · intro h
    funext k
    have hall : ∀ m, ∀ hm : m < n, answers ω ⟨m, hm⟩ = b ⟨m, hm⟩ := by
      intro m
      induction m using Nat.strong_induction_on with
      | h m ih =>
        intro hm
        have hprefix : (fun j : Fin m => answers ω ⟨j.val, j.isLt.trans hm⟩) =
            (fun j : Fin m => b ⟨j.val, j.isLt.trans hm⟩) := by
          funext j
          exact ih j.val j.isLt _
        have hr := hrun ω ⟨m, hm⟩
        rw [hprefix] at hr
        have hb := hr.trans (h ⟨m, hm⟩)
        cases ha : answers ω ⟨m, hm⟩ <;> cases hc : b ⟨m, hm⟩ <;> simp_all
    exact hall k.val k.isLt

/-- Adaptive leaf probabilities use the distinct coordinates along that leaf.
Repeating a coordinate is explicitly excluded from this product formula. -/
theorem prodBernoulli_adaptive_answers {n : ℕ} (p : ι → unitInterval)
    (next : (k : Fin n) → (Fin k.val → Bool) → ι)
    (answers : Set ι → Fin n → Bool)
    (hrun : ∀ ω k, answers ω k = true ↔
      next k (fun j => answers ω ⟨j.val, j.isLt.trans k.isLt⟩) ∈ ω)
    (b : Fin n → Bool)
    (he : Function.Injective (fun k => next k (fun j => b ⟨j.val, j.isLt.trans k.isLt⟩))) :
    prodBernoulli p {ω | answers ω = b} =
      ∏ k, if b k then
        (unitInterval.toNNReal (p (next k (fun j => b ⟨j.val, j.isLt.trans k.isLt⟩))) : ℝ≥0∞)
      else (unitInterval.toNNReal (unitInterval.symm
        (p (next k (fun j => b ⟨j.val, j.isLt.trans k.isLt⟩)))) : ℝ≥0∞) := by
  simp_rw [adaptive_answers_eq_iff next answers hrun b]
  exact prodBernoulli_transcript p _ he b

/-- The actual adaptive leaf also factors from every measurable event on the complement
of its fixed transcript coordinates. -/
theorem prodBernoulli_adaptive_answers_inter {n : ℕ} (p : ι → unitInterval)
    (next : (k : Fin n) → (Fin k.val → Bool) → ι)
    (answers : Set ι → Fin n → Bool)
    (hrun : ∀ ω k, answers ω k = true ↔
      next k (fun j => answers ω ⟨j.val, j.isLt.trans k.isLt⟩) ∈ ω)
    (b : Fin n → Bool) (e : Fin n → ι)
    (heq : ∀ k, e k = next k (fun j => b ⟨j.val, j.isLt.trans k.isLt⟩))
    (he : Function.Injective e) (B : Set (Set ((Set.range e)ᶜ : Set ι)))
    (hB : MeasurableSet B) :
    prodBernoulli p {ω | answers ω = b ∧
      (Subtype.val ⁻¹' ω : Set ((Set.range e)ᶜ : Set ι)) ∈ B} =
      prodBernoulli p {ω | answers ω = b} *
        prodBernoulli p {ω | (Subtype.val ⁻¹' ω : Set ((Set.range e)ᶜ : Set ι)) ∈ B} := by
  have hleaf (ω) : answers ω = b ↔ ∀ k, e k ∈ ω ↔ b k = true := by
    simpa only [heq] using adaptive_answers_eq_iff next answers hrun b ω
  simp_rw [hleaf]
  rw [prodBernoulli_transcript p e he b]
  exact prodBernoulli_transcript_inter p e he b B hB

-- An empty transcript has probability one.
example (p : ι → unitInterval) :
    prodBernoulli p {ω | ∀ j : Fin 0, Fin.elim0 j ∈ ω ↔ true = true} = 1 := by simp

-- Distinct queried bonds may include a loop; the probability space retains it.
example (p : Sym2 Bool → unitInterval) :
    prodBernoulli p {ω | s(false, false) ∈ ω ∧ s(false, true) ∉ ω} =
      (unitInterval.toNNReal (p s(false, false)) : ℝ≥0∞) *
        (unitInterval.toNNReal (unitInterval.symm (p s(false, true))) : ℝ≥0∞) := by
  have he : Function.Injective (fun b : Bool => if b then s(false, false) else s(false, true)) := by
    intro a b h
    cases a <;> cases b <;> simp_all
  simpa [Fintype.prod_bool, Bool.forall_bool, and_comm] using
    prodBernoulli_transcript p (fun b : Bool => if b then s(false, false) else s(false, true)) he id

-- A one-step deterministic execution satisfies the adaptive hypotheses.
example (p : ι → unitInterval) (i : ι) (b : Fin 1 → Bool) :
    prodBernoulli p {ω | (fun _ : Fin 1 => decide (i ∈ ω)) = b} =
      ∏ k, if b k then (unitInterval.toNNReal (p i) : ℝ≥0∞)
        else (unitInterval.toNNReal (unitInterval.symm (p i)) : ℝ≥0∞) := by
  exact prodBernoulli_adaptive_answers p (fun _ _ => i)
    (fun ω _ => decide (i ∈ ω)) (by intro ω k; simp) b
    (fun _ _ _ => Subsingleton.elim _ _)

end PercLib.Probability
