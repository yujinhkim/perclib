/-
Copyright (c) 2026 PercLib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

New for this project (issue 156, Q-22, items 1, 2 and the first half of 4). No upstream
proof is copied.
-/
module

public import PercLib.Percolation.Bond.Susceptibility
public import PercLib.Percolation.Bond.LocalConnectivity
public import PercLib.Probability.Coupling.Monotone
public import PercLib.Probability.FiniteContinuity
public import PercLib.Probability.OpenEventHarris
public import Mathlib.Topology.Semicontinuity.Basic

/-!
# Regularity of `τ`, `χ` and `θ` in the profile

Profiles carry the pointwise order and the product topology.

* `τ`, `χ`, `θ` and the probability that some cluster is infinite are monotone in the
  profile (from the monotone coupling S-2).
* The probability of an event determined by finitely many pairs is continuous in the profile.
* `τ` is lower semicontinuous, as the supremum over a finite exhaustion of internal connection
  probabilities.
* Along a monotone, continuous one-parameter family of profiles, `τ` is left-continuous.
-/

@[expose] public section

noncomputable section

open MeasureTheory Set Filter Topology PercLib.Probability
open scoped ENNReal

namespace PercLib.Percolation.Bond

variable {V : Type*}

/-! ### Monotonicity -/

/-- The two-point function is monotone in the profile. -/
theorem tau_mono [Countable V] {q q' : Sym2 V → unitInterval} (h : q ≤ q') (x y : V) :
    tau q x y ≤ tau q' x y :=
  prodBernoulli_mono_event q q' h (measurableSet_conn x y) (isUpperSet_conn x y)

/-- The susceptibility is monotone in the profile. -/
theorem chi_mono [Countable V] {q q' : Sym2 V → unitInterval} (h : q ≤ q') (x : V) :
    chi q x ≤ chi q' x :=
  lintegral_prodBernoulli_mono q q' h
    ((Measurable.of_discrete (f := ((↑) : ℕ∞ → ℝ≥0∞))).comp (measurable_encard_cluster x))
    fun _ _ hle => ENat.toENNReal_le.2 (Set.encard_le_encard fun _ hy => conn_mono hle hy)

/-- The probability that the cluster of `x` is infinite is monotone in the profile. -/
theorem law_cluster_infinite_mono [Countable V] {q q' : Sym2 V → unitInterval} (h : q ≤ q')
    (x : V) :
    law q {ω | (cluster ω x).Infinite} ≤ law q' {ω | (cluster ω x).Infinite} :=
  prodBernoulli_mono_event q q' h (measurableSet_cluster_infinite x)
    fun _ _ hle hinf => hinf.mono fun _ hy => conn_mono hle hy

/-- The probability that some cluster is infinite is monotone in the profile. -/
theorem law_exists_cluster_infinite_mono [Countable V] {q q' : Sym2 V → unitInterval}
    (h : q ≤ q') :
    law q {ω | ∃ x, (cluster ω x).Infinite} ≤ law q' {ω | ∃ x, (cluster ω x).Infinite} := by
  have hm : MeasurableSet {ω : Config V | ∃ x, (cluster ω x).Infinite} := by
    have : {ω : Config V | ∃ x, (cluster ω x).Infinite} =
        ⋃ x, {ω : Config V | (cluster ω x).Infinite} := by
      ext ω
      simp
    rw [this]
    exact MeasurableSet.iUnion fun x => measurableSet_cluster_infinite x
  exact prodBernoulli_mono_event q q' h hm
    fun _ _ hle ⟨x, hinf⟩ => ⟨x, hinf.mono fun _ hy => conn_mono hle hy⟩

/-! ### Events determined by finitely many coordinates -/

/-- The probability of an event determined by a finite set of coordinates is continuous in
the profile. No countability or measurability is needed. -/
theorem continuous_prodBernoulli_of_determined {ι : Type*} (F : Finset ι) {E : Set (Set ι)}
    (hE : ∀ ω ω', ω ∩ (F : Set ι) = ω' ∩ (F : Set ι) → (ω ∈ E ↔ ω' ∈ E)) :
    Continuous fun p : ι → unitInterval => prodBernoulli p E := by
  have hset : E = {ω : Set ι | (Subtype.val ⁻¹' ω : Set F) ∈
      {η : Set F | (Subtype.val '' η : Set ι) ∈ E}} := by
    ext ω
    refine hE _ _ ?_
    ext i
    simp only [mem_inter_iff, mem_image, mem_preimage, Subtype.exists, exists_and_right,
      exists_eq_right, Finset.mem_coe]
    constructor
    · rintro ⟨hω, hF⟩
      exact ⟨⟨hF, hω⟩, hF⟩
    · rintro ⟨⟨hF, hω⟩, -⟩
      exact ⟨hω, hF⟩
  rw [hset]
  exact continuous_prodBernoulli_cylinder F _

/-! ### Lower semicontinuity of `τ` -/

/-- An internal connection event of a finite domain has a probability continuous in the
profile. -/
theorem continuous_law_localConn (S : Finset V) (x y : V) :
    Continuous fun q : Sym2 V → unitInterval =>
      law q {ω : Config V | ∃ hx : x ∈ (S : Set V), ∃ hy : y ∈ (S : Set V),
        ((openGraph ω).induce (S : Set V)).Reachable ⟨x, hx⟩ ⟨y, hy⟩} := by
  classical
  set F : Finset (Sym2 V) := (S ×ˢ S).image fun z => s(z.1, z.2) with hF
  refine continuous_prodBernoulli_of_determined F fun ω ω' h => ?_
  simp only [mem_ofPred_eq]
  refine exists_congr fun hx => exists_congr fun hy => localConn_iff_of_agree _ _ _
    fun a ha b hb => ?_
  have hab : s(a, b) ∈ (F : Set (Sym2 V)) := by
    simp only [hF, Finset.coe_image, Finset.coe_product, mem_image, mem_prod, Finset.mem_coe]
    exact ⟨(a, b), ⟨ha, hb⟩, rfl⟩
  have := congrArg (s(a, b) ∈ ·) h
  simp only [eq_iff_iff, mem_inter_iff] at this
  exact ⟨fun hω => (this.1 ⟨hω, hab⟩).1, fun hω => (this.2 ⟨hω, hab⟩).1⟩

/-- A countable type has an increasing exhaustion by finite sets. -/
theorem exists_finset_exhaustion [Countable V] :
    ∃ S : ℕ → Finset V, Monotone S ∧ ∀ v, ∃ n, v ∈ S n := by
  classical
  rcases isEmpty_or_nonempty V with hV | hV
  · exact ⟨fun _ => ∅, fun _ _ _ => le_rfl, fun v => isEmptyElim v⟩
  · obtain ⟨f, hf⟩ := exists_surjective_nat V
    refine ⟨fun n => (Finset.range n).image f, fun m n hmn => ?_, fun v => ?_⟩
    · exact Finset.image_subset_image (Finset.range_subset_range.2 hmn)
    · obtain ⟨k, rfl⟩ := hf v
      exact ⟨k + 1, Finset.mem_image.2 ⟨k, Finset.mem_range.2 (Nat.lt_succ_self k), rfl⟩⟩

/-- **Lower semicontinuity of `τ`** in the profile. -/
theorem lowerSemicontinuous_tau [Countable V] (x y : V) :
    LowerSemicontinuous fun q : Sym2 V → unitInterval => tau q x y := by
  obtain ⟨S, hS, hcover⟩ := exists_finset_exhaustion (V := V)
  have hS' : Monotone fun n => (S n : Set V) := fun m n hmn => Finset.coe_subset.2 (hS hmn)
  have heq : (fun q : Sym2 V → unitInterval => tau q x y) = fun q =>
      ⨆ n, law q {ω : Config V | ∃ hx : x ∈ (S n : Set V), ∃ hy : y ∈ (S n : Set V),
        ((openGraph ω).induce (S n : Set V)).Reachable ⟨x, hx⟩ ⟨y, hy⟩} := by
    funext q
    exact tau_eq_iSup_localConn q hS' hcover x y
  rw [heq]
  exact lowerSemicontinuous_iSup fun n => (continuous_law_localConn (S n) x y).lowerSemicontinuous

/-! ### One-parameter families -/

/-- A lower semicontinuous monotone function is left-continuous. -/
theorem continuousWithinAt_Iic_of_lowerSemicontinuous_of_monotone {α : Type*}
    [TopologicalSpace α] [Preorder α] {f : α → ℝ≥0∞} (hf : LowerSemicontinuous f)
    (hmono : Monotone f) (t : α) : ContinuousWithinAt f (Iic t) t := by
  refine tendsto_order.2 ⟨fun a ha => ?_, fun b hb => ?_⟩
  · exact nhdsWithin_le_nhds (hf t a ha)
  · exact eventually_nhdsWithin_of_forall fun s hs => (hmono hs).trans_lt hb

/-- **Left-continuity of `τ`** along a monotone family of profiles that is continuous in
each coordinate. -/
theorem continuousWithinAt_tau_Iic [Countable V] {α : Type*} [TopologicalSpace α] [Preorder α]
    {q : α → Sym2 V → unitInterval} (hmono : Monotone q) (hcont : ∀ e, Continuous (q · e))
    (x y : V) (t : α) :
    ContinuousWithinAt (fun s => tau (q s) x y) (Iic t) t :=
  continuousWithinAt_Iic_of_lowerSemicontinuous_of_monotone
    (LowerSemicontinuous.comp (lowerSemicontinuous_tau x y) (continuous_pi hcont))
    (fun _ _ hst => tau_mono (hmono hst) x y) t

/-! ### Non-vacuity -/

/-- The constant family `t ↦ t` on `ℤ`, with `t ∈ [0, 1]`, satisfies the hypotheses of the
left-continuity statement. -/
example (x y : ℤ) (t : unitInterval) :
    ContinuousWithinAt (fun s : unitInterval => tau (fun _ : Sym2 ℤ => s) x y) (Iic t) t :=
  continuousWithinAt_tau_Iic (q := fun s _ => s) (fun _ _ h _ => h) (fun _ => continuous_id) x y t

end PercLib.Percolation.Bond

end
