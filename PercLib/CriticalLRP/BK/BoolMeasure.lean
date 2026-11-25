/-
Migration source: https://github.com/yujinhkim/Critical-Long-range-percolation
Integration revision: 3b3d1d0e43ef940bfaa2292ee5c2ee094ac4edbf
Licence: Apache-2.0 for the PercLib Lean sources and tooling; see third_party/critical-lrp/.
External provenance and modifications are recorded in the file-specific notices below.
-/

/-
# Direction B: the `Bool`-coding measurability bridge, and Lemma I.2.1(i) for arbitrary
increasing functionals of the clusters

Hutchcroft, *Critical long-range percolation I* (arXiv:2508.18807), Lemma I.2.1(i) says that the
two-cluster BK inequality for *all* increasing measurable cluster-determined events implies
`E[F(K_x) G(K_y) 1{x ↮ y}] ≤ E F(K_x) · E G(K_y)` for all non-negative increasing functionals
`F, G` of the clusters.  In this repository:

* `BK/BorelReduction.twoCluster_functional_of_borelBK` is that implication, conditional on the
  indicator-level inequality for all increasing **measurable** cluster-determined `A`, `B`
  (`MeasurableSet` for the σ-algebra on `Set E`);
* `BK/BKGeneral.twoCluster_bk_general_ennreal` is the indicator-level inequality, but it asks for
  measurability of the `Bool`-coded images `boolOf '' A`, `boolOf '' B`, and of
  `boolOf '' (A ∩ B ∩ {x ↮ y})`.

The two do not compose: one consumes `MeasurableSet A`, the other produces it only in the image
form.  This file closes that gap *without assuming anything new*, by proving that the `Bool`
coding is an isomorphism of the two σ-algebras in the only sense needed:

`MeasurableSet (boolOf '' A) ↔ MeasurableSet A`   (`measurableSet_boolOf_image_iff`),

which rests on `Measurable (fun x : E → Bool => setOfBool x)` (`measurable_setOfBool`), i.e. on
`e ∈ setOfBool x ↔ x e = true`, plus injectivity of `boolOf`.

Consequences proved here (all in this file, no root edits):

* `boolOf_image_compl`, `boolOf_image_iUnion`, `boolOf_image_inter`, `boolOf_image_sdiff`:
  `boolOf '' ·` commutes with the Boolean σ-algebra operations, so the coding is a σ-algebra
  isomorphism of `Set E` onto its image;
* `BoolCode` (section 2): an inductive Boolean-code syntax over the edge type with semantics a set
  of `Bool` configurations, `measurableSet_event` (every code denotes a measurable event, by
  structural induction, with no measurability hypothesis supplied by the user) and
  `upper_event_of_pos` / `isUpperSet_preimage_event` (positive codes denote increasing events);
* `bk_borel_subset_measurable`, `bk_borel_measurable`: the general Borel BK inequality with **plain**
  `MeasurableSet` hypotheses (no `Bool`-image measurability to supply);
* `twoCluster_bk_general_measurable`: the general two-cluster BK inequality for all increasing
  cluster-determined measurable events;
* `twoCluster_bk_infinite`, `twoCluster_bk_infinite_real`: `P(x ↮ y, |K_x| = ∞, |K_y| = ∞) ≤
  P(|K_x| = ∞) P(|K_y| = ∞)` for `p e < 1` — the events are not finitely witnessed;
* `twoCluster_functional_bk_ennreal`, `twoCluster_functional_bk_toReal_le` and
  `twoCluster_functional_infinite`: **Lemma I.2.1(i) for arbitrary non-negative increasing
  measurable functionals of the clusters**, with the abstract indicator-level BK hypothesis
  discharged and **no continuity-from-below hypothesis** (compare `twoCluster_functional_toReal_le`,
  which needs `hFcont`, `hHcont`);
* section 4 (canonical model): `edgeMeasure_twoCluster_bk_measurable(_real)` and
  `longRangeMeasure_twoCluster_bk_measurable(_real)` generalise `edgeMeasure_twoCluster_bk` /
  `longRangeMeasure_twoCluster_bk` by replacing finite-witness hypotheses with measurability;
  `edgeMeasure_twoCluster_functional`, `longRangeMeasure_twoCluster_functional` and
  `longRangeMeasure_twoCluster_functional_infinite` are the `ℝ≥0∞` forms on `Config V` and on
  `P_β`; `edgeMeasure_twoCluster_functional_integral` and
  `longRangeMeasure_twoCluster_functional_integral` are the paper's expectation display
  `E[F(K_x)G(K_y) 1{x ↮ y}] ≤ E F(K_x) · E G(K_y)` as a plain real integral over the event.

No new axioms, no `sorry`; every premise is explicit.  Additive only: the root project is not
modified.

## Compile / audit

```
LEAN_PATH="<repo>/.lake/build/lib/lean:$LEAN_PATH" lean .ultramath/smwga3bqk/m5/BoolMeasure.lean
```
-/
module

public import PercLib.CriticalLRP.BK.BorelReduction
public import PercLib.CriticalLRP.BK.BKGeneral
public import PercLib.CriticalLRP.BK.Association
public import PercLib.CriticalLRP.BK.CanonicalBridge

set_option linter.unusedSectionVars false
set_option linter.unusedSimpArgs false
set_option linter.unnecessarySimpa false
set_option linter.unusedTactic false
set_option linter.unusedVariables false

set_option autoImplicit true

@[expose] public section

namespace PercLib.CriticalLRP

open MeasureTheory ProbabilityTheory
open scoped ENNReal NNReal

namespace Percolation
universe u v

/-! ## 1. The `Bool`-coding measurability bridge -/

section BoolBridgeBasic
variable {E : Type v}

attribute [local instance] Classical.propDecidable

/-- **The Boolean coding map is measurable.**  A set of edges `S` is measurable in the coordinate
σ-algebra of `Set E` exactly when `e ↦ (e ∈ S)` is measurable, and `e ∈ setOfBool x ↔ x e = true`;
this is the missing direction relating `MeasurableSet A` and `MeasurableSet (boolOf '' A)`. -/
theorem measurable_setOfBool : Measurable (fun x : E → Bool => setOfBool x) := by
  rw [measurable_set_iff]
  intro e
  have h : (fun x : E → Bool => e ∈ setOfBool x) = (fun x : E → Bool => x e = true) := by
    funext x; simp [setOfBool]
  rw [h]
  exact (measurable_pi_apply (X := fun _ : E => Bool) e).eq_const true

/-- The `Bool`-coded image of a set of edge sets is the preimage under `setOfBool`; the identity
that makes the coding an isomorphism rather than merely an injection. -/
theorem boolOf_image_eq_preimage (A : Set (Set E)) : boolOf '' A = setOfBool ⁻¹' A := by
  ext x
  constructor
  · rintro ⟨ω, hω, rfl⟩
    simpa [setOfBool_boolOf] using hω
  · intro hx
    exact ⟨setOfBool x, hx, by simp⟩

end BoolBridgeBasic

section BoolBridge
variable {E : Type v} [Countable E]

attribute [local instance] Classical.propDecidable

theorem boolOf_surjective : Function.Surjective (fun ω : Set E => boolOf ω) :=
  fun x => ⟨setOfBool x, by simp⟩

theorem boolOf_bijective : Function.Bijective (fun ω : Set E => boolOf ω) :=
  ⟨boolOf_injective, boolOf_surjective⟩

/-- `boolOf` is injective, so pulling back the coded image recovers the original event. -/
theorem preimage_image_boolOf (A : Set (Set E)) : boolOf ⁻¹' (boolOf '' A) = A :=
  Set.preimage_image_eq A boolOf_injective

/-- **The `Bool` coding reflects and preserves measurability.**  This is the exact statement
missing between `BK/BorelReduction` (which consumes `MeasurableSet A`) and
`BK/BKGeneral.twoCluster_bk_general_ennreal` (which produces `MeasurableSet (boolOf '' A)`). -/
theorem measurableSet_boolOf_image_iff {A : Set (Set E)} :
    MeasurableSet (boolOf '' A) ↔ MeasurableSet A := by
  constructor
  · intro h
    rw [← preimage_image_boolOf A]
    exact h.preimage measurable_boolOf
  · intro h
    rw [boolOf_image_eq_preimage]
    exact h.preimage measurable_setOfBool

/-- Measurability of an event gives measurability of its `Bool`-coded image. -/
theorem measurableSet_boolOf_image {A : Set (Set E)} (h : MeasurableSet A) :
    MeasurableSet (boolOf '' A) :=
  measurableSet_boolOf_image_iff.mpr h

/-- The coding sends complements to complements (injectivity). -/
theorem boolOf_image_compl (A : Set (Set E)) : boolOf '' Aᶜ = (boolOf '' A)ᶜ :=
  Set.image_compl_eq (f := boolOf) boolOf_bijective

/-- The coding commutes with arbitrary unions. -/
theorem boolOf_image_iUnion {ι : Sort*} (A : ι → Set (Set E)) :
    boolOf '' (⋃ i, A i) = ⋃ i, boolOf '' A i :=
  Set.image_iUnion

/-- The coding commutes with binary intersections (injectivity). -/
theorem boolOf_image_inter (A B : Set (Set E)) : boolOf '' (A ∩ B) = boolOf '' A ∩ boolOf '' B :=
  Set.image_inter (f := boolOf) boolOf_injective

/-- The coding commutes with binary differences (injectivity). -/
theorem boolOf_image_sdiff (A B : Set (Set E)) : boolOf '' (A \ B) = boolOf '' A \ boolOf '' B :=
  Set.image_sdiff (f := boolOf) boolOf_injective A B

/-- The coded image of `x ↔ y` is measurable: the automation applied to a genuine canonical graph
event. -/
theorem measurableSet_boolOf_image_conn (G : BondGraph V E) (x y : V) :
    MeasurableSet (boolOf '' {ω : Set E | Conn G ω x y}) :=
  measurableSet_boolOf_image (measurableSet_conn G x y)

/-- The coded image of a level set of an increasing cluster functional is measurable: the
canonical input shape of the indicator-level BK inequality. -/
theorem measurableSet_boolOf_image_level (G : BondGraph V E) {F : Set V → ℝ} (x : V) (s : ℝ)
    (hFmeas : Measurable fun ω => F (cluster G ω x)) :
    MeasurableSet (boolOf '' {ω : Set E | s < F (cluster G ω x)}) :=
  measurableSet_boolOf_image (hFmeas measurableSet_Ioi)

end BoolBridge

/-! ## 2. Boolean-coded events: syntax, semantics, measurability, monotonicity

The "Boolean-coding" layer alluded to in the project description: a small inductive syntax of
codes over the edge type, with semantics a set of `Bool` configurations.  Every code denotes a
measurable event of the product σ-algebra (no hypothesis on the code), and positive codes denote
increasing events, so both measurability facts needed by the general BK are *computed* from the
syntax instead of supplied by the user. -/

section Codes
variable {E : Type v}

/-- Syntax of Boolean codes over an edge type. -/
inductive BoolCode (E : Type v) : Type v where
  | atom (e : E) : BoolCode E
  | top : BoolCode E
  | bot : BoolCode E
  | conj (a b : BoolCode E) : BoolCode E
  | disj (a b : BoolCode E) : BoolCode E
  | neg (a : BoolCode E) : BoolCode E

namespace BoolCode

/-- Evaluation of a code at a `Bool` configuration. -/
def sat : BoolCode E → (E → Bool) → Bool
  | atom e, x => x e
  | top, _ => true
  | bot, _ => false
  | conj a b, x => (sat a x && sat b x)
  | disj a b, x => (sat a x || sat b x)
  | neg a, x => !(sat a x)

/-- The event coded by a code. -/
def event (c : BoolCode E) : Set (E → Bool) := {x | c.sat x = true}

@[simp] theorem mem_event_iff (c : BoolCode E) (x : E → Bool) : x ∈ c.event ↔ c.sat x = true :=
  Iff.rfl

@[simp] theorem sat_atom (e : E) (x : E → Bool) : (atom e).sat x = x e := rfl

@[simp] theorem sat_top (x : E → Bool) : (top : BoolCode E).sat x = true := rfl

@[simp] theorem sat_bot (x : E → Bool) : (bot : BoolCode E).sat x = false := rfl

@[simp] theorem sat_conj (a b : BoolCode E) (x : E → Bool) :
    (conj a b).sat x = (a.sat x && b.sat x) := rfl

@[simp] theorem sat_disj (a b : BoolCode E) (x : E → Bool) :
    (disj a b).sat x = (a.sat x || b.sat x) := rfl

@[simp] theorem sat_neg (a : BoolCode E) (x : E → Bool) : (neg a).sat x = !(a.sat x) := rfl

theorem event_atom (e : E) : (atom e).event = {x : E → Bool | x e = true} := by
  ext x; simp [event]

theorem event_top : (top : BoolCode E).event = Set.univ := by
  ext x; simp [event]

theorem event_bot : (bot : BoolCode E).event = (∅ : Set (E → Bool)) := by
  ext x; simp [event]

theorem event_conj (a b : BoolCode E) : (conj a b).event = a.event ∩ b.event := by
  ext x; simp [event, Bool.and_eq_true]

theorem event_disj (a b : BoolCode E) : (disj a b).event = a.event ∪ b.event := by
  ext x; simp [event, Bool.or_eq_true]

theorem event_neg (a : BoolCode E) : (neg a).event = a.eventᶜ := by
  ext x; simp [event]

/-- **Every coded event is measurable** (structural induction over the syntax); no hypothesis on
the code is needed beyond the coordinate σ-algebra on `E → Bool`. -/
theorem measurableSet_event : ∀ c : BoolCode E, MeasurableSet c.event
  | atom e => by
      rw [event_atom]
      exact measurableSet_eq_fun (measurable_pi_apply (X := fun _ : E => Bool) e) measurable_const
  | top => by rw [event_top]; exact MeasurableSet.univ
  | bot => by rw [event_bot]; exact MeasurableSet.empty
  | conj a b => by
      rw [event_conj]; exact (measurableSet_event a).inter (measurableSet_event b)
  | disj a b => by
      rw [event_disj]; exact (measurableSet_event a).union (measurableSet_event b)
  | neg a => by rw [event_neg]; exact (measurableSet_event a).compl

/-- The positive fragment: codes without `neg`.  These denote increasing events. -/
inductive Positive : BoolCode E → Prop where
  | atom (e : E) : Positive (atom e)
  | top : Positive top
  | bot : Positive bot
  | conj {a b} : Positive a → Positive b → Positive (conj a b)
  | disj {a b} : Positive a → Positive b → Positive (disj a b)

theorem BoolUpper_inter {A B : Set (E → Bool)} (hA : BoolUpper A) (hB : BoolUpper B) :
    BoolUpper (A ∩ B) := by
  intro x y hxy hx
  exact ⟨hA x y hxy hx.1, hB x y hxy hx.2⟩

theorem BoolUpper_union {A B : Set (E → Bool)} (hA : BoolUpper A) (hB : BoolUpper B) :
    BoolUpper (A ∪ B) := by
  intro x y hxy hx
  rcases hx with h | h
  · exact Or.inl (hA x y hxy h)
  · exact Or.inr (hB x y hxy h)

theorem BoolUpper_univ : BoolUpper (Set.univ : Set (E → Bool)) := by
  intro x y _ _; trivial

theorem BoolUpper_empty : BoolUpper (∅ : Set (E → Bool)) := by
  intro x y _ hx; exact hx.elim

theorem BoolUpper_atom (e : E) : BoolUpper (atom e).event := by
  intro x y hxy hx
  have h1 : x e = true := by simpa [event] using hx
  have h2 := ble_iff.mp hxy e h1
  simpa [event] using h2

/-- Positive codes denote increasing events, in the repository's `Bool`-coding (`BoolUpper`). -/
theorem upper_event_of_pos : ∀ {c : BoolCode E}, c.Positive → BoolUpper c.event
  | _, Positive.atom e => BoolUpper_atom e
  | _, Positive.top => by simpa only [event_top] using BoolUpper_univ
  | _, Positive.bot => by simpa only [event_bot] using BoolUpper_empty
  | _, Positive.conj ha hb => by
      have h := BoolUpper_inter (upper_event_of_pos ha) (upper_event_of_pos hb)
      simpa only [event_conj] using h
  | _, Positive.disj ha hb => by
      have h := BoolUpper_union (upper_event_of_pos ha) (upper_event_of_pos hb)
      simpa only [event_disj] using h

/-- Positive codes denote increasing (upper) subsets of the edge configuration space. -/
theorem isUpperSet_preimage_event {c : BoolCode E} (hc : c.Positive) :
    IsUpperSet (boolOf ⁻¹' c.event) :=
  isUpperSet_preimage_iff.mpr (upper_event_of_pos hc)

/-- The pulled-back coded event is measurable in the coordinate σ-algebra of `Set E`. -/
theorem measurableSet_preimage_event [Countable E] (c : BoolCode E) :
    MeasurableSet (boolOf ⁻¹' c.event) :=
  measurable_boolOf (measurableSet_event c)

/-- Its `Bool`-coded image is measurable: the second measurability fact the general BK consumes,
again computed from the syntax. -/
theorem measurableSet_boolOf_image_preimage_event [Countable E] (c : BoolCode E) :
    MeasurableSet (boolOf '' (boolOf ⁻¹' c.event)) :=
  measurableSet_boolOf_image_preimage (measurableSet_event c)

end BoolCode

end Codes

/-! ## 3. Two-cluster BK for all increasing measurable cluster-determined events, and Lemma
I.2.1(i) for arbitrary increasing functionals -/

section Applications
variable {E : Type v} [Countable E]
attribute [local instance] Classical.propDecidable

/-- **The general two-cluster BK inequality** (Hutchcroft, Lemma I.2.1(i), indicator form) for
*all* increasing cluster-determined **measurable** events: `P(A ∩ B ∩ {x ↮ y}) ≤ P(A)P(B)`.

Unlike `twoCluster_bk_general_ennreal`, this takes plain `MeasurableSet` hypotheses and derives the
`Bool`-image measurability from `measurableSet_boolOf_image`. -/
theorem twoCluster_bk_general_measurable (G : BondGraph V E) (p : E → unitInterval)
    (hp : ∀ e, p e < 1) (x y : V)
    {A B : Set (Set E)} (hA : IsUpperSet A) (hB : IsUpperSet B)
    (hdA : ClusterDeterminedAt G x A) (hdB : ClusterDeterminedAt G y B)
    (hmA : MeasurableSet A) (hmB : MeasurableSet B) :
    (edgeLaw p) (A ∩ B ∩ {ω | ¬ Conn G ω x y}) ≤ (edgeLaw p) A * (edgeLaw p) B :=
  twoCluster_bk_general_ennreal G p hp x y hA hB hdA hdB
    (measurableSet_boolOf_image hmA) (measurableSet_boolOf_image hmB)
    (measurableSet_boolOf_image ((hmA.inter hmB).inter (measurableSet_conn G x y).compl))

/-- **Lemma I.2.1(i) for arbitrary increasing functionals of the clusters**, in `ℝ≥0∞` form:
`∫_{x ↮ y} F(K_x) G(K_y) ≤ (∫ F(K_x)) (∫ G(K_y))` for non-negative increasing measurable `F`,
`G`.  This is `twoCluster_functional_of_borelBK` with its indicator-level BK input discharged by
`twoCluster_bk_general_measurable`, hence **unconditional** given `p e < 1`. -/
theorem twoCluster_functional_bk_ennreal (G : BondGraph V E) (p : E → unitInterval)
    (hp : ∀ e, p e < 1) (x y : V) {F H : Set V → ℝ}
    (hF0 : ∀ S, 0 ≤ F S) (hH0 : ∀ S, 0 ≤ H S)
    (hFmono : ∀ S T : Set V, S ⊆ T → F S ≤ F T)
    (hHmono : ∀ S T : Set V, S ⊆ T → H S ≤ H T)
    (hFmeas : Measurable fun ω => F (cluster G ω x))
    (hHmeas : Measurable fun ω => H (cluster G ω y)) :
    (∫⁻ ω, ({ω : Set E | ¬ Conn G ω x y}).indicator (fun _ => (1 : ℝ≥0∞)) ω *
        ENNReal.ofReal (F (cluster G ω x) * H (cluster G ω y)) ∂(edgeLaw p))
      ≤ (∫⁻ ω, ENNReal.ofReal (F (cluster G ω x)) ∂(edgeLaw p)) *
          (∫⁻ ω, ENNReal.ofReal (H (cluster G ω y)) ∂(edgeLaw p)) :=
  twoCluster_functional_of_borelBK G p x y hF0 hH0 hFmono hHmono hFmeas hHmeas
    (fun _ _ hA hAm hdA hB hBm hdB =>
      twoCluster_bk_general_measurable G p hp x y hA hB hdA hdB hAm hBm)

/-- **Lemma I.2.1(i) in expectation (`toReal`) form, with no continuity hypothesis.**  Same
conclusion as `twoCluster_functional_toReal_le`, which additionally requires `F`, `G` to be
continuous from below along a finite exhaustion; that restriction is unnecessary.  The hypotheses
are non-negativity, monotonicity, measurability, `p e < 1`, and finiteness of the two one-point
expectations (which the paper assumes when writing the inequality in `ℝ`). -/
theorem twoCluster_functional_bk_toReal_le (G : BondGraph V E)
    (p : E → unitInterval) (hp : ∀ e, p e < 1) (x y : V) {F H : Set V → ℝ}
    (hF0 : ∀ S, 0 ≤ F S) (hH0 : ∀ S, 0 ≤ H S)
    (hFmono : ∀ S T : Set V, S ⊆ T → F S ≤ F T)
    (hHmono : ∀ S T : Set V, S ⊆ T → H S ≤ H T)
    (hFmeas : Measurable fun ω => F (cluster G ω x))
    (hHmeas : Measurable fun ω => H (cluster G ω y))
    (hFfin : (∫⁻ ω, ENNReal.ofReal (F (cluster G ω x)) ∂(edgeLaw p)) ≠ ⊤)
    (hHfin : (∫⁻ ω, ENNReal.ofReal (H (cluster G ω y)) ∂(edgeLaw p)) ≠ ⊤) :
    (∫⁻ ω, ({ω : Set E | ¬ Conn G ω x y}).indicator (fun _ => (1 : ℝ≥0∞)) ω *
        ENNReal.ofReal (F (cluster G ω x) * H (cluster G ω y)) ∂(edgeLaw p)).toReal
      ≤ (∫⁻ ω, ENNReal.ofReal (F (cluster G ω x)) ∂(edgeLaw p)).toReal *
          (∫⁻ ω, ENNReal.ofReal (H (cluster G ω y)) ∂(edgeLaw p)).toReal := by
  have hle := twoCluster_functional_bk_ennreal G p hp x y hF0 hH0 hFmono hHmono hFmeas hHmeas
  have hfinR : (∫⁻ ω, ENNReal.ofReal (F (cluster G ω x)) ∂(edgeLaw p)) *
      (∫⁻ ω, ENNReal.ofReal (H (cluster G ω y)) ∂(edgeLaw p)) ≠ ⊤ :=
    ENNReal.mul_ne_top hFfin hHfin
  have hfinL : (∫⁻ ω, ({ω : Set E | ¬ Conn G ω x y}).indicator (fun _ => (1 : ℝ≥0∞)) ω *
      ENNReal.ofReal (F (cluster G ω x) * H (cluster G ω y)) ∂(edgeLaw p)) ≠ ⊤ :=
    ne_top_of_le_ne_top hfinR hle
  have h := (ENNReal.toReal_le_toReal hfinL hfinR).mpr hle
  rwa [ENNReal.toReal_mul] at h

/-- **The general Borel BK inequality with plain measurability** (Hutchcroft, footnote 11 / Section
I.2.1): for increasing **measurable** events `A`, `B`, the measure of any measurable subset of the
disjoint occurrence part is at most the product of the measures.  Same statement as
`bk_borel_subset`, but the `Bool`-image measurability hypotheses are discharged rather than
assumed. -/
theorem bk_borel_subset_measurable (p : E → unitInterval) (hp : ∀ e, p e < 1)
    {A B : Set (Set E)} (hA : IsUpperSet A) (hB : IsUpperSet B)
    (hmA : MeasurableSet A) (hmB : MeasurableSet B)
    {C : Set (Set E)} (hC : C ⊆ DisjointOccurrencePart A B) (hmC : MeasurableSet C) :
    (edgeLaw p).real C ≤ (edgeLaw p).real A * (edgeLaw p).real B :=
  bk_borel_subset p hp hA hB (measurableSet_boolOf_image hmA) (measurableSet_boolOf_image hmB)
    hC (measurableSet_boolOf_image hmC)

/-- **The general Borel BK inequality in disjoint-occurrence form**, with plain measurability of
`A`, `B` and of the disjoint-occurrence part. -/
theorem bk_borel_measurable (p : E → unitInterval) (hp : ∀ e, p e < 1)
    {A B : Set (Set E)} (hA : IsUpperSet A) (hB : IsUpperSet B)
    (hmA : MeasurableSet A) (hmB : MeasurableSet B)
    (hmD : MeasurableSet (DisjointOccurrencePart A B)) :
    (edgeLaw p).real (DisjointOccurrencePart A B) ≤
      (edgeLaw p).real A * (edgeLaw p).real B :=
  bk_borel p hp hA hB (measurableSet_boolOf_image hmA) (measurableSet_boolOf_image hmB)
    (measurableSet_boolOf_image hmD)

/-- The functional `S ↦ 1 {S infinite}`: the percolation functional measuring whether the cluster
is infinite.  It is monotone and measurable, but is **not** continuous from below along any finite
exhaustion, so it is outside the continuity class handled by `twoCluster_functional_toReal_le`. -/
noncomputable def infiniteIndicator (S : Set V) : ℝ := if S.Infinite then 1 else 0

theorem infiniteIndicator_nonneg (S : Set V) : 0 ≤ infiniteIndicator S := by
  unfold infiniteIndicator; split <;> norm_num

theorem infiniteIndicator_mono {S T : Set V} (h : S ⊆ T) :
    infiniteIndicator S ≤ infiniteIndicator T := by
  unfold infiniteIndicator
  by_cases hS : S.Infinite
  · have hT : T.Infinite := hS.mono h
    simp [hS, hT]
  · simp only [hS, ite_false]
    split <;> norm_num

theorem measurable_infiniteIndicator (G : BondGraph V E) (x : V) :
    Measurable fun ω => infiniteIndicator (cluster G ω x) := by
  have h : Measurable fun ω : Set E => infiniteIndicator (cluster G ω x) := by
    refine Measurable.ite (measurableSet_infinite_cluster G x) measurable_const measurable_const
  exact h

/-- **Percolation BK at `p e < 1`: two-cluster form with infinite clusters.**  For distinct sites
`x`, `y`: `P(x ↮ y, |K_x| = ∞, |K_y| = ∞) ≤ P(|K_x| = ∞) · P(|K_y| = ∞)`.

This is the case the finite-witness and continuity-from-below routes cannot reach (the event
`{|K_x| = ∞}` is not finitely witnessed), and it is the motivating application of the general
Borel two-cluster BK inequality in the paper.  It is a direct instance of
`twoCluster_bk_general_measurable`. -/
theorem twoCluster_bk_infinite (G : BondGraph V E) (p : E → unitInterval)
    (hp : ∀ e, p e < 1) (x y : V) :
    (edgeLaw p) ({ω : Set E | (cluster G ω x).Infinite} ∩
        {ω : Set E | (cluster G ω y).Infinite} ∩ {ω | ¬ Conn G ω x y})
      ≤ (edgeLaw p) {ω : Set E | (cluster G ω x).Infinite} *
          (edgeLaw p) {ω : Set E | (cluster G ω y).Infinite} := by
  refine twoCluster_bk_general_measurable G p hp x y ?_ ?_ ?_ ?_ ?_ ?_
  · intro ω ω' hsub hinf
    exact hinf.mono (cluster_mono hsub x)
  · intro ω ω' hsub hinf
    exact hinf.mono (cluster_mono hsub y)
  · intro ω ω' hcl
    have h : (cluster G ω x).Infinite ↔ (cluster G ω' x).Infinite := by rw [hcl]
    simpa using h
  · intro ω ω' hcl
    have h : (cluster G ω y).Infinite ↔ (cluster G ω' y).Infinite := by rw [hcl]
    simpa using h
  · exact measurableSet_infinite_cluster G x
  · exact measurableSet_infinite_cluster G y

/-- The same percolation BK inequality in `Measure.real` (probability) form. -/
theorem twoCluster_bk_infinite_real (G : BondGraph V E) (p : E → unitInterval)
    (hp : ∀ e, p e < 1) (x y : V) :
    (edgeLaw p).real ({ω : Set E | (cluster G ω x).Infinite} ∩
        {ω : Set E | (cluster G ω y).Infinite} ∩ {ω | ¬ Conn G ω x y})
      ≤ (edgeLaw p).real {ω : Set E | (cluster G ω x).Infinite} *
          (edgeLaw p).real {ω : Set E | (cluster G ω y).Infinite} := by
  have hle := twoCluster_bk_infinite G p hp x y
  have hR : (edgeLaw p) {ω : Set E | (cluster G ω x).Infinite} *
      (edgeLaw p) {ω : Set E | (cluster G ω y).Infinite} ≠ ⊤ :=
    ENNReal.mul_ne_top (measure_ne_top _ _) (measure_ne_top _ _)
  have hL : (edgeLaw p) ({ω : Set E | (cluster G ω x).Infinite} ∩
      {ω : Set E | (cluster G ω y).Infinite} ∩ {ω | ¬ Conn G ω x y}) ≠ ⊤ :=
    measure_ne_top _ _
  have h := (ENNReal.toReal_le_toReal hL hR).mpr hle
  rwa [ENNReal.toReal_mul] at h

/-- **Lemma I.2.1(i) applied to the percolation functional `1{|K| = ∞}`**, in `ℝ≥0∞` form:
`E[1{x ↮ y} 1{|K_x| = ∞} 1{|K_y| = ∞}] ≤ E 1{|K_x| = ∞} · E 1{|K_y| = ∞}`.  The functional is
not continuous from below, so this instance is not available from the finite-exhaustion form of
Lemma I.2.1(i) in `BK/FunctionalFromBelow`. -/
theorem twoCluster_functional_infinite (G : BondGraph V E) (p : E → unitInterval)
    (hp : ∀ e, p e < 1) (x y : V) :
    (∫⁻ ω, ({ω : Set E | ¬ Conn G ω x y}).indicator (fun _ => (1 : ℝ≥0∞)) ω *
        ENNReal.ofReal (infiniteIndicator (cluster G ω x) * infiniteIndicator (cluster G ω y))
          ∂(edgeLaw p))
      ≤ (∫⁻ ω, ENNReal.ofReal (infiniteIndicator (cluster G ω x)) ∂(edgeLaw p)) *
          (∫⁻ ω, ENNReal.ofReal (infiniteIndicator (cluster G ω y)) ∂(edgeLaw p)) :=
  twoCluster_functional_bk_ennreal G p hp x y
    (fun S => infiniteIndicator_nonneg S) (fun S => infiniteIndicator_nonneg S)
    (fun _ _ h => infiniteIndicator_mono h) (fun _ _ h => infiniteIndicator_mono h)
    (measurable_infiniteIndicator G x) (measurable_infiniteIndicator G y)

end Applications

end Percolation

/-! ## 4. The canonical model and the paper's law `P_β = longRangeMeasure`

The two-cluster correlation statement transported to `Config V = Set (Sym2 V)` and to
`longRangeMeasure J hJ β`, in the forms in which later sections consume it. -/

section Canonical
variable {V : Type*} [Countable V]
attribute [local instance] Classical.propDecidable

/-- **The general two-cluster BK inequality on the canonical model**, with the canonical notion of
a cluster event (`ClusterEvent`, Hutchcroft's "event depending only on `K_x`"), for *all*
increasing **measurable** events.  This strictly generalises `edgeMeasure_twoCluster_bk`, which
additionally requires `Percolation.FiniteWitness A` and `Percolation.FiniteWitness B`. -/
theorem edgeMeasure_twoCluster_bk_measurable (π : Sym2 V → unitInterval) (hπ : ∀ e, π e < 1)
    (x y : V) {A B : Set (Config V)}
    (hA : IsUpperSet A) (hB : IsUpperSet B) (hdA : ClusterEvent x A) (hdB : ClusterEvent y B)
    (hmA : MeasurableSet A) (hmB : MeasurableSet B) :
    (edgeMeasure π) (A ∩ B ∩ {ω : Config V | ¬ Connects ω x y}) ≤
      (edgeMeasure π) A * (edgeMeasure π) B := by
  let := Encodable.ofCountable (Sym2 V)
  rw [edgeMeasure_eq_edgeLaw]
  have h := Percolation.twoCluster_bk_general_measurable (idBondGraph V) π hπ x y hA hB
    (clusterDeterminedAt_idBondGraph_iff x A |>.mpr hdA)
    (clusterDeterminedAt_idBondGraph_iff y B |>.mpr hdB) hmA hmB
  simpa only [conn_idBondGraph_iff] using h

/-- The real (`Measure.real`) form of `edgeMeasure_twoCluster_bk_measurable`: the same conclusion
as `edgeMeasure_twoCluster_bk`, without the finite-witness hypotheses. -/
theorem edgeMeasure_twoCluster_bk_measurable_real (π : Sym2 V → unitInterval)
    (hπ : ∀ e, π e < 1) (x y : V) {A B : Set (Config V)}
    (hA : IsUpperSet A) (hB : IsUpperSet B) (hdA : ClusterEvent x A) (hdB : ClusterEvent y B)
    (hmA : MeasurableSet A) (hmB : MeasurableSet B) :
    (edgeMeasure π).real (A ∩ B ∩ {ω : Config V | ¬ Connects ω x y}) ≤
      (edgeMeasure π).real A * (edgeMeasure π).real B := by
  have h := edgeMeasure_twoCluster_bk_measurable π hπ x y hA hB hdA hdB hmA hmB
  have hR : (edgeMeasure π) A * (edgeMeasure π) B ≠ ⊤ :=
    ENNReal.mul_ne_top (measure_ne_top _ _) (measure_ne_top _ _)
  have h := (ENNReal.toReal_le_toReal (measure_ne_top _ _) hR).mpr h
  rwa [ENNReal.toReal_mul] at h

/-- **The general two-cluster BK inequality for the paper's law `P_β`**, `ℝ≥0∞` form. -/
theorem longRangeMeasure_twoCluster_bk_measurable {J : Sym2 V → ℝ} (hJ : ∀ e, 0 ≤ J e)
    (β : NNReal) (x y : V) {A B : Set (Config V)}
    (hA : IsUpperSet A) (hB : IsUpperSet B) (hdA : ClusterEvent x A) (hdB : ClusterEvent y B)
    (hmA : MeasurableSet A) (hmB : MeasurableSet B) :
    (longRangeMeasure J hJ β) (A ∩ B ∩ {ω : Config V | ¬ Connects ω x y}) ≤
      (longRangeMeasure J hJ β) A * (longRangeMeasure J hJ β) B := by
  rw [longRangeMeasure]
  exact edgeMeasure_twoCluster_bk_measurable _ (fun e => bernoulliEdgeProb_lt_one hJ β e) x y
    hA hB hdA hdB hmA hmB

/-- **The general two-cluster BK inequality for `P_β`**, real form: strictly generalises
`longRangeMeasure_twoCluster_bk` by replacing the finite-witness hypotheses by measurability. -/
theorem longRangeMeasure_twoCluster_bk_measurable_real {J : Sym2 V → ℝ} (hJ : ∀ e, 0 ≤ J e)
    (β : NNReal) (x y : V) {A B : Set (Config V)}
    (hA : IsUpperSet A) (hB : IsUpperSet B) (hdA : ClusterEvent x A) (hdB : ClusterEvent y B)
    (hmA : MeasurableSet A) (hmB : MeasurableSet B) :
    (longRangeMeasure J hJ β).real (A ∩ B ∩ {ω : Config V | ¬ Connects ω x y}) ≤
      (longRangeMeasure J hJ β).real A * (longRangeMeasure J hJ β).real B := by
  rw [longRangeMeasure]
  exact edgeMeasure_twoCluster_bk_measurable_real _ (fun e => bernoulliEdgeProb_lt_one hJ β e) x y
    hA hB hdA hdB hmA hmB

/-- **Consistency check: the general canonical BK inequality implies the finitely witnessed one.**
This is the statement of `edgeMeasure_twoCluster_bk` (`BK/CanonicalBridge.lean`) re-derived from
`edgeMeasure_twoCluster_bk_measurable_real`, so the measurable version really is a strict
generalisation of the previously verified finite-witness theorem. -/
theorem edgeMeasure_twoCluster_bk_of_finiteWitness (π : Sym2 V → unitInterval)
    (hπ : ∀ e, π e < 1) (x y : V) (A B : Set (Config V))
    (hA : IsUpperSet A) (hfA : Percolation.FiniteWitness A) (hdA : ClusterEvent x A)
    (hB : IsUpperSet B) (hfB : Percolation.FiniteWitness B) (hdB : ClusterEvent y B) :
    (edgeMeasure π).real (A ∩ B ∩ {ω : Config V | ¬ Connects ω x y}) ≤
      (edgeMeasure π).real A * (edgeMeasure π).real B :=
  edgeMeasure_twoCluster_bk_measurable_real π hπ x y hA hB hdA hdB
    (Percolation.measurableSet_finiteWitness A hA hfA)
    (Percolation.measurableSet_finiteWitness B hB hfB)

/-- **Consistency check for `P_β`**: the finite-witness statement `longRangeMeasure_twoCluster_bk`
re-derived from the general measurable version. -/
theorem longRangeMeasure_twoCluster_bk_of_finiteWitness {J : Sym2 V → ℝ} (hJ : ∀ e, 0 ≤ J e)
    (β : NNReal) (x y : V) (A B : Set (Config V))
    (hA : IsUpperSet A) (hfA : Percolation.FiniteWitness A) (hdA : ClusterEvent x A)
    (hB : IsUpperSet B) (hfB : Percolation.FiniteWitness B) (hdB : ClusterEvent y B) :
    (longRangeMeasure J hJ β).real (A ∩ B ∩ {ω : Config V | ¬ Connects ω x y}) ≤
      (longRangeMeasure J hJ β).real A * (longRangeMeasure J hJ β).real B :=
  longRangeMeasure_twoCluster_bk_measurable_real hJ β x y hA hB hdA hdB
    (Percolation.measurableSet_finiteWitness A hA hfA)
    (Percolation.measurableSet_finiteWitness B hB hfB)

/-- **Lemma I.2.1(i) on the canonical model** for arbitrary non-negative increasing measurable
functionals of the clusters, `ℝ≥0∞` form. -/
theorem edgeMeasure_twoCluster_functional (π : Sym2 V → unitInterval) (hπ : ∀ e, π e < 1)
    (x y : V) {F H : Set V → ℝ}
    (hF0 : ∀ S, 0 ≤ F S) (hH0 : ∀ S, 0 ≤ H S)
    (hFmono : ∀ S T : Set V, S ⊆ T → F S ≤ F T)
    (hHmono : ∀ S T : Set V, S ⊆ T → H S ≤ H T)
    (hFmeas : Measurable fun ω : Config V => F (cluster ω x))
    (hHmeas : Measurable fun ω : Config V => H (cluster ω y)) :
    (∫⁻ ω, ({ω : Config V | ¬ Connects ω x y}).indicator (fun _ => (1 : ℝ≥0∞)) ω *
        ENNReal.ofReal (F (cluster ω x) * H (cluster ω y)) ∂(edgeMeasure π))
      ≤ (∫⁻ ω, ENNReal.ofReal (F (cluster ω x)) ∂(edgeMeasure π)) *
          (∫⁻ ω, ENNReal.ofReal (H (cluster ω y)) ∂(edgeMeasure π)) := by
  let := Encodable.ofCountable (Sym2 V)
  rw [edgeMeasure_eq_edgeLaw]
  have h := Percolation.twoCluster_functional_bk_ennreal (idBondGraph V) π hπ x y
    (F := F) (H := H) hF0 hH0 hFmono hHmono
    (by simpa only [cluster_idBondGraph] using hFmeas)
    (by simpa only [cluster_idBondGraph] using hHmeas)
  simpa only [cluster_idBondGraph, conn_idBondGraph_iff] using h

/-- **Lemma I.2.1(i) for the paper's law `P_β`**, `ℝ≥0∞` form. -/
theorem longRangeMeasure_twoCluster_functional {J : Sym2 V → ℝ} (hJ : ∀ e, 0 ≤ J e)
    (β : NNReal) (x y : V) {F H : Set V → ℝ}
    (hF0 : ∀ S, 0 ≤ F S) (hH0 : ∀ S, 0 ≤ H S)
    (hFmono : ∀ S T : Set V, S ⊆ T → F S ≤ F T)
    (hHmono : ∀ S T : Set V, S ⊆ T → H S ≤ H T)
    (hFmeas : Measurable fun ω : Config V => F (cluster ω x))
    (hHmeas : Measurable fun ω : Config V => H (cluster ω y)) :
    (∫⁻ ω, ({ω : Config V | ¬ Connects ω x y}).indicator (fun _ => (1 : ℝ≥0∞)) ω *
        ENNReal.ofReal (F (cluster ω x) * H (cluster ω y)) ∂(longRangeMeasure J hJ β))
      ≤ (∫⁻ ω, ENNReal.ofReal (F (cluster ω x)) ∂(longRangeMeasure J hJ β)) *
          (∫⁻ ω, ENNReal.ofReal (H (cluster ω y)) ∂(longRangeMeasure J hJ β)) := by
  rw [longRangeMeasure]
  exact edgeMeasure_twoCluster_functional _ (fun e => bernoulliEdgeProb_lt_one hJ β e) x y
    hF0 hH0 hFmono hHmono hFmeas hHmeas

/-- Measurability of `{|K_x| = ∞}` on the canonical model (via `InInfiniteCluster`). -/
theorem measurableSet_cluster_infinite_canonical (x : V) :
    MeasurableSet {ω : Config V | (cluster ω x).Infinite} := by
  have h : {ω : Config V | (cluster ω x).Infinite} = {ω : Config V | InInfiniteCluster ω x} := by
    ext ω
    exact (inInfiniteCluster_iff_infinite ω x).symm
  rw [h]
  exact measurableSet_inInfiniteCluster x

/-- Measurability of `ω ↦ 1{|K_x| = ∞}` on the canonical model. -/
theorem measurable_infiniteIndicator_canonical (x : V) :
    Measurable fun ω : Config V => Percolation.infiniteIndicator (cluster ω x) :=
  Measurable.ite (measurableSet_cluster_infinite_canonical x) measurable_const measurable_const

/-- **Lemma I.2.1(i) for the percolation functional `1{|K| = ∞}` under `P_β`**, `ℝ≥0∞` form.
(For the unconditional cluster-cardinality form see `longRangeMeasure_twoCluster_cardFun`; for the
set-level infinite-cluster inequality see `CountableProduct/ClusterInfinite.lean`, whose statement
is the `F = G = 1{|K| = ∞}` instance of the general theorem proved here.) -/
theorem longRangeMeasure_twoCluster_functional_infinite {J : Sym2 V → ℝ} (hJ : ∀ e, 0 ≤ J e)
    (β : NNReal) (x y : V) :
    (∫⁻ ω, ({ω : Config V | ¬ Connects ω x y}).indicator (fun _ => (1 : ℝ≥0∞)) ω *
        ENNReal.ofReal (Percolation.infiniteIndicator (cluster ω x) * Percolation.infiniteIndicator (cluster ω y))
          ∂(longRangeMeasure J hJ β))
      ≤ (∫⁻ ω, ENNReal.ofReal (Percolation.infiniteIndicator (cluster ω x)) ∂(longRangeMeasure J hJ β)) *
          (∫⁻ ω, ENNReal.ofReal (Percolation.infiniteIndicator (cluster ω y)) ∂(longRangeMeasure J hJ β)) :=
  longRangeMeasure_twoCluster_functional hJ β x y
    (fun S => Percolation.infiniteIndicator_nonneg S) (fun S => Percolation.infiniteIndicator_nonneg S)
    (fun _ _ h => Percolation.infiniteIndicator_mono h) (fun _ _ h => Percolation.infiniteIndicator_mono h)
    (measurable_infiniteIndicator_canonical x) (measurable_infiniteIndicator_canonical y)

/-- **Lemma I.2.1(i) in the paper's expectation notation on the canonical model**:
`E[F(K_x) G(K_y) 1{x ↮ y}] ≤ E F(K_x) · E G(K_y)`, as a plain real integral over the event. -/
theorem edgeMeasure_twoCluster_functional_integral (π : Sym2 V → unitInterval) (hπ : ∀ e, π e < 1)
    (x y : V) {F H : Set V → ℝ}
    (hF0 : ∀ S, 0 ≤ F S) (hH0 : ∀ S, 0 ≤ H S)
    (hFmono : ∀ S T : Set V, S ⊆ T → F S ≤ F T)
    (hHmono : ∀ S T : Set V, S ⊆ T → H S ≤ H T)
    (hFmeas : Measurable fun ω : Config V => F (cluster ω x))
    (hHmeas : Measurable fun ω : Config V => H (cluster ω y))
    (hFint : Integrable (fun ω : Config V => F (cluster ω x)) (edgeMeasure π))
    (hHint : Integrable (fun ω : Config V => H (cluster ω y)) (edgeMeasure π))
    (hFGint : Integrable (fun ω : Config V => F (cluster ω x) * H (cluster ω y))
      (edgeMeasure π)) :
    (∫ ω in {ω : Config V | ¬ Connects ω x y}, F (cluster ω x) * H (cluster ω y)
        ∂(edgeMeasure π))
      ≤ (∫ ω, F (cluster ω x) ∂(edgeMeasure π)) *
          (∫ ω, H (cluster ω y) ∂(edgeMeasure π)) := by
  have hs : MeasurableSet {ω : Config V | ¬ Connects ω x y} :=
    (measurableSet_connects x y).compl
  have hFG0 : ∀ ω : Config V, 0 ≤ F (cluster ω x) * H (cluster ω y) :=
    fun ω => mul_nonneg (hF0 _) (hH0 _)
  have hFGmeas : Measurable fun ω : Config V => F (cluster ω x) * H (cluster ω y) :=
    hFmeas.mul hHmeas
  -- step 1: the set integral is the `toReal` of the lintegral appearing in the BK inequality
  have hL : (∫ ω in {ω : Config V | ¬ Connects ω x y}, F (cluster ω x) * H (cluster ω y)
      ∂(edgeMeasure π)) =
      (∫⁻ ω, ({ω : Config V | ¬ Connects ω x y}).indicator (fun _ => (1 : ℝ≥0∞)) ω *
        ENNReal.ofReal (F (cluster ω x) * H (cluster ω y)) ∂(edgeMeasure π)).toReal := by
    rw [← integral_indicator hs,
      integral_eq_lintegral_of_nonneg_ae (Filter.Eventually.of_forall (fun ω => ?_))
        ((hFGmeas.indicator hs).aestronglyMeasurable)]
    · congr 1
      refine lintegral_congr fun ω => ?_
      by_cases hω : ω ∈ {ω : Config V | ¬ Connects ω x y}
      · rw [Set.indicator_of_mem hω, Set.indicator_of_mem hω]
        simp
      · rw [Set.indicator_of_notMem hω, Set.indicator_of_notMem hω]
        simp
    · exact Set.indicator_nonneg (fun ω _ => hFG0 ω) ω
  -- step 2: the two one-point lintegrals are the real integrals
  have hR1 : (∫⁻ ω, ENNReal.ofReal (F (cluster ω x)) ∂(edgeMeasure π)).toReal =
      ∫ ω, F (cluster ω x) ∂(edgeMeasure π) :=
    (integral_eq_lintegral_of_nonneg_ae (Filter.Eventually.of_forall (fun ω => hF0 _))
      hFmeas.aestronglyMeasurable).symm
  have hR2 : (∫⁻ ω, ENNReal.ofReal (H (cluster ω y)) ∂(edgeMeasure π)).toReal =
      ∫ ω, H (cluster ω y) ∂(edgeMeasure π) :=
    (integral_eq_lintegral_of_nonneg_ae (Filter.Eventually.of_forall (fun ω => hH0 _))
      hHmeas.aestronglyMeasurable).symm
  -- step 3: finiteness of the one-point lintegrals from integrability
  have hFfin : (∫⁻ ω, ENNReal.ofReal (F (cluster ω x)) ∂(edgeMeasure π)) ≠ ⊤ :=
    (lintegral_ofReal_ne_top_iff_integrable hFmeas.aestronglyMeasurable
      (Filter.Eventually.of_forall (fun ω => hF0 _))).mpr hFint
  have hHfin : (∫⁻ ω, ENNReal.ofReal (H (cluster ω y)) ∂(edgeMeasure π)) ≠ ⊤ :=
    (lintegral_ofReal_ne_top_iff_integrable hHmeas.aestronglyMeasurable
      (Filter.Eventually.of_forall (fun ω => hH0 _))).mpr hHint
  have hBH := edgeMeasure_twoCluster_functional π hπ x y hF0 hH0 hFmono hHmono hFmeas hHmeas
  rw [hL]
  calc (∫⁻ ω, ({ω : Config V | ¬ Connects ω x y}).indicator (fun _ => (1 : ℝ≥0∞)) ω *
        ENNReal.ofReal (F (cluster ω x) * H (cluster ω y)) ∂(edgeMeasure π)).toReal
      ≤ ((∫⁻ ω, ENNReal.ofReal (F (cluster ω x)) ∂(edgeMeasure π)) *
          (∫⁻ ω, ENNReal.ofReal (H (cluster ω y)) ∂(edgeMeasure π))).toReal :=
        ENNReal.toReal_mono (ENNReal.mul_ne_top hFfin hHfin) hBH
    _ = (∫ ω, F (cluster ω x) ∂(edgeMeasure π)) *
          (∫ ω, H (cluster ω y) ∂(edgeMeasure π)) := by
        rw [ENNReal.toReal_mul, hR1, hR2]

/-- **Lemma I.2.1(i) in expectation notation for `P_β`.** -/
theorem longRangeMeasure_twoCluster_functional_integral {J : Sym2 V → ℝ} (hJ : ∀ e, 0 ≤ J e)
    (β : NNReal) (x y : V) {F H : Set V → ℝ}
    (hF0 : ∀ S, 0 ≤ F S) (hH0 : ∀ S, 0 ≤ H S)
    (hFmono : ∀ S T : Set V, S ⊆ T → F S ≤ F T)
    (hHmono : ∀ S T : Set V, S ⊆ T → H S ≤ H T)
    (hFmeas : Measurable fun ω : Config V => F (cluster ω x))
    (hHmeas : Measurable fun ω : Config V => H (cluster ω y))
    (hFint : Integrable (fun ω : Config V => F (cluster ω x)) (longRangeMeasure J hJ β))
    (hHint : Integrable (fun ω : Config V => H (cluster ω y)) (longRangeMeasure J hJ β))
    (hFGint : Integrable (fun ω : Config V => F (cluster ω x) * H (cluster ω y))
      (longRangeMeasure J hJ β)) :
    (∫ ω in {ω : Config V | ¬ Connects ω x y}, F (cluster ω x) * H (cluster ω y)
        ∂(longRangeMeasure J hJ β))
      ≤ (∫ ω, F (cluster ω x) ∂(longRangeMeasure J hJ β)) *
          (∫ ω, H (cluster ω y) ∂(longRangeMeasure J hJ β)) := by
  rw [longRangeMeasure]
  exact edgeMeasure_twoCluster_functional_integral _ (fun e => bernoulliEdgeProb_lt_one hJ β e) x y
    hF0 hH0 hFmono hHmono hFmeas hHmeas hFint hHint hFGint

end Canonical


end PercLib.CriticalLRP

/-! ## Audit -/

#print axioms PercLib.CriticalLRP.Percolation.measurable_setOfBool
#print axioms PercLib.CriticalLRP.Percolation.measurableSet_boolOf_image_iff
#print axioms PercLib.CriticalLRP.Percolation.twoCluster_bk_general_measurable
#print axioms PercLib.CriticalLRP.Percolation.twoCluster_functional_bk_ennreal
#print axioms PercLib.CriticalLRP.Percolation.twoCluster_functional_bk_toReal_le
#print axioms PercLib.CriticalLRP.Percolation.BoolCode.measurableSet_event
#print axioms PercLib.CriticalLRP.Percolation.BoolCode.isUpperSet_preimage_event
#print axioms PercLib.CriticalLRP.Percolation.twoCluster_bk_infinite
#print axioms PercLib.CriticalLRP.Percolation.twoCluster_bk_infinite_real
#print axioms PercLib.CriticalLRP.Percolation.bk_borel_subset_measurable
#print axioms PercLib.CriticalLRP.Percolation.bk_borel_measurable
#print axioms PercLib.CriticalLRP.Percolation.twoCluster_functional_infinite
#print axioms PercLib.CriticalLRP.edgeMeasure_twoCluster_functional
#print axioms PercLib.CriticalLRP.longRangeMeasure_twoCluster_functional
#print axioms PercLib.CriticalLRP.edgeMeasure_twoCluster_functional_integral
#print axioms PercLib.CriticalLRP.longRangeMeasure_twoCluster_functional_integral
#print axioms PercLib.CriticalLRP.edgeMeasure_twoCluster_bk_measurable
#print axioms PercLib.CriticalLRP.edgeMeasure_twoCluster_bk_measurable_real
#print axioms PercLib.CriticalLRP.longRangeMeasure_twoCluster_bk_measurable
#print axioms PercLib.CriticalLRP.longRangeMeasure_twoCluster_bk_measurable_real
#print axioms PercLib.CriticalLRP.longRangeMeasure_twoCluster_functional_infinite
#print axioms PercLib.CriticalLRP.measurableSet_cluster_infinite_canonical
#print axioms PercLib.CriticalLRP.edgeMeasure_twoCluster_bk_of_finiteWitness
#print axioms PercLib.CriticalLRP.longRangeMeasure_twoCluster_bk_of_finiteWitness
