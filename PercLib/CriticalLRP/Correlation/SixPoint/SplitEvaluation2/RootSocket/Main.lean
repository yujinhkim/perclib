/-
Swarm `smwxii2d9`, member `m1`, direction d3 (`PINNED-EAR-ELIMINATION`).

Root-socket evaluations of the `k = 2` slot products `slotProd2` at every split position
`j : Fin 7`, in both pattern root sockets (`b₀` held, comb slot `0`, and `b₂` held, comb slot
`2`), i.e. the two root classes of the `Fin 15` pattern family; at `j = 0` all three admissible
sockets `0`, `1`, `2` are evaluated.

## What the pinned-ear caveat is, and why it is not a condition on the vertex

Every slot evaluation ends with a *pin step*: the last surviving joint group has one ear held (the
pin) while its centre and its other ear are summed, and `tsum_jointP_centre` gives `E|K|²` for
**every** held vertex `r : V` — the identity has no condition on `r` at all.  Two things are
genuinely required, and both are statements about the *sharing structure*, not about the vertex:

* the two vertices the pin sums (centre and one ear) must each occur in no surviving factor other
  than the joint group being pinned;
* the pinned ear is *not* consumed: it may occur in other factors and may be summed later.  At
  `j = 0` with socket `0` the pin holds the **interior** landing point `i₂` and sums the spine
  `i₁` with the ear `b₁`, and `i₂` is then consumed by the residual two-point factor
  `b₀ — i₂`; the two interior vertices are legitimate pins whenever they are leaves at that moment.

So the caveat is never "this terminal cannot be the root".  It is "the pin must be taken at a
leaf of the current diagram, and the peel order must consume each free vertex in the one surviving
factor that mentions it".  Consequently the root socket is a free choice among the admissible
leaves, and the socket sums at different admissible roots are different sevenfold sums that happen
to take the same value.

This file makes that usable: it proves the two root sockets that the pattern family uses at every
split position, and at `j = 0` also the third (`b₁`), each from scratch through the same three
identities `tsum_jointP_centre` / `secondMoment_eq` / `tau_row`–`tau_col`.  No reindexing of one
socket into another is used anywhere: they are independent sums.

Only the five-factor slot *diagrams* are evaluated here.  The event-level union bounds that produce
them (`SplitPattern.combSystem_twoJointThree_zero/five/six` for `j = 0,5,6`,
`TwoJointThree.combSystem_twoJointThree` for `j = 2`, and the `b₀ ↔ b₁` transport for `j = 1`) are
production; the corresponding event-level bridges at `j = 3,4` are **not** in this file, and the
reindexing from the peel order of each theorem to the pattern order of the assembly is **not** in
this file either (both are listed in `NOTES.md`).

## Hypotheses and invariants

`V` is a countable additive commutative group, `π : Sym2 V → unitInterval` is an arbitrary edge
law, and the only hypothesis beyond that is the **full profile invariance**
`hq : ∀ x y g, π s(x + g, y + g) = π s(x, y)`.  No independence, no moment finiteness, no
factorisation of `tau`, no constraint on `secondMoment π 0` and `∑' x, tau π 0 x` being finite or
infinite: every step is an `ℝ≥0∞` identity, no sum is truncated, and the pin is never taken
through a divergent constant.  All proofs are elementary consequences of the three peel
identities; no new axiom is introduced.
-/
module

public import PercLib.CriticalLRP.Correlation.SixPoint.SplitEvaluation2.RootSocket.Defs

/-!
# Root-socket evaluations of `slotProd2` at both pattern root sockets
-/

open Set MeasureTheory
open scoped ENNReal BigOperators
open PercLib.Percolation.Bond
open PercLib.CriticalLRP.TreeExpansion.FivePoint

set_option linter.style.longLine false
set_option linter.style.setOption false

@[expose] public section

namespace PercLib.CriticalLRP.SixPoint.SplitEval2.RootSocket

variable {V : Type*}

/-! ## The three peel steps, coefficient on the left -/

/-- **The pin step, centre outer.**  The pinned ear `r` is held, the centre `c` and the other ear
`q` are summed; the value is `E|K|²`, for every vertex `r`. -/
theorem peel_pin [Countable V] [AddCommGroup V] (π : Sym2 V → unitInterval)
    (hq : ∀ x y g : V, π s(x + g, y + g) = π s(x, y)) {C : ℝ≥0∞} {r : V}
    {F : V → V → ℝ≥0∞} (h : ∀ q c, F q c = C * jointP π r q c) :
    (∑' c, ∑' q, F q c) = C * secondMoment π 0 := by
  rw [tsum_congr fun c => tsum_congr fun q => h q c]
  simp only [ENNReal.tsum_mul_left]
  exact congrArg (fun t => C * t) (tsum_jointP_centre π hq r)

/-- **The pin step, ear outer.** -/
theorem peel_pin' [Countable V] [AddCommGroup V] (π : Sym2 V → unitInterval)
    (hq : ∀ x y g : V, π s(x + g, y + g) = π s(x, y)) {C : ℝ≥0∞} {r : V}
    {F : V → V → ℝ≥0∞} (h : ∀ q c, F q c = C * jointP π r q c) :
    (∑' q, ∑' c, F q c) = C * secondMoment π 0 := by
  rw [tsum_congr fun q => tsum_congr fun c => h q c]
  simp only [ENNReal.tsum_mul_left]
  rw [show (∑' q, ∑' c, jointP π r q c) = ∑' c, ∑' q, jointP π r q c from ENNReal.tsum_comm]
  exact congrArg (fun t => C * t) (tsum_jointP_centre π hq r)

/-- **Both ears summed, the centre held.** -/
theorem peel_joint_ears [Countable V] [AddCommGroup V] (π : Sym2 V → unitInterval)
    (hq : ∀ x y g : V, π s(x + g, y + g) = π s(x, y)) {C : ℝ≥0∞} {z : V}
    {F : V → V → ℝ≥0∞} (h : ∀ a b, F a b = C * jointP π a b z) :
    (∑' a, ∑' b, F a b) = C * secondMoment π 0 := by
  rw [tsum_congr fun a => tsum_congr fun b => h a b]
  simp only [ENNReal.tsum_mul_left]
  exact congrArg (fun t => C * t)
    ((show (∑' a, ∑' b, jointP π a b z) = secondMoment π z from (secondMoment_eq π z).symm).trans
      (secondMoment_root_independent π hq z))

/-- **Both ears summed, the centre held, other nesting.** -/
theorem peel_joint_ears' [Countable V] [AddCommGroup V] (π : Sym2 V → unitInterval)
    (hq : ∀ x y g : V, π s(x + g, y + g) = π s(x, y)) {C : ℝ≥0∞} {z : V}
    {F : V → V → ℝ≥0∞} (h : ∀ a b, F a b = C * jointP π a b z) :
    (∑' b, ∑' a, F a b) = C * secondMoment π 0 := by
  rw [tsum_congr fun b => tsum_congr fun a => h a b]
  simp only [ENNReal.tsum_mul_left]
  rw [ENNReal.tsum_comm]
  exact congrArg (fun t => C * t)
    ((show (∑' a, ∑' b, jointP π a b z) = secondMoment π z from (secondMoment_eq π z).symm).trans
      (secondMoment_root_independent π hq z))

/-- **One endpoint summed, the other held.** -/
theorem peel_tau [Countable V] [AddCommGroup V] (π : Sym2 V → unitInterval)
    (hq : ∀ x y g : V, π s(x + g, y + g) = π s(x, y)) {C : ℝ≥0∞} {z : V}
    {F : V → ℝ≥0∞} (h : ∀ a, F a = C * tau π a z) :
    (∑' a, F a) = C * (∑' x, tau π 0 x) := by
  rw [tsum_congr h]
  simp only [ENNReal.tsum_mul_left]
  exact congrArg (fun t => C * t) (tau_col π hq z)

/-- **One endpoint summed, the other held, pair reversed.** -/
theorem peel_tau' [Countable V] [AddCommGroup V] (π : Sym2 V → unitInterval)
    (hq : ∀ x y g : V, π s(x + g, y + g) = π s(x, y)) {C : ℝ≥0∞} {z : V}
    {F : V → ℝ≥0∞} (h : ∀ a, F a = C * tau π z a) :
    (∑' a, F a) = C * (∑' x, tau π 0 x) := by
  rw [tsum_congr h]
  simp only [ENNReal.tsum_mul_left]
  exact congrArg (fun t => C * t) (tau_row π hq z)

/-! ## The three peel steps, coefficient on the right

The socket evaluations below accumulate the constant obtained from each closed factor on the
right of the residual product, so these four forms are the ones the peels consume. -/

/-- **The pin step, centre outer, coefficient on the right.** -/
theorem peel_pin_R [Countable V] [AddCommGroup V] (π : Sym2 V → unitInterval)
    (hq : ∀ x y g : V, π s(x + g, y + g) = π s(x, y)) {C : ℝ≥0∞} {r : V}
    {F : V → V → ℝ≥0∞} (h : ∀ q c, F q c = jointP π r q c * C) :
    (∑' c, ∑' q, F q c) = secondMoment π 0 * C := by
  rw [tsum_congr fun c => tsum_congr fun q => h q c]
  simp only [ENNReal.tsum_mul_right]
  exact congrArg (fun t => t * C) (tsum_jointP_centre π hq r)

/-- **Both ears summed, the centre held, coefficient on the right.** -/
theorem peel_joint_ears_R [Countable V] [AddCommGroup V] (π : Sym2 V → unitInterval)
    (hq : ∀ x y g : V, π s(x + g, y + g) = π s(x, y)) {C : ℝ≥0∞} {z : V}
    {F : V → V → ℝ≥0∞} (h : ∀ a b, F a b = jointP π a b z * C) :
    (∑' a, ∑' b, F a b) = secondMoment π 0 * C := by
  rw [tsum_congr fun a => tsum_congr fun b => h a b]
  simp only [ENNReal.tsum_mul_right]
  exact congrArg (fun t => t * C)
    ((show (∑' a, ∑' b, jointP π a b z) = secondMoment π z from (secondMoment_eq π z).symm).trans
      (secondMoment_root_independent π hq z))

/-- **One endpoint summed, the other held, coefficient on the right.** -/
theorem peel_tau_R [Countable V] [AddCommGroup V] (π : Sym2 V → unitInterval)
    (hq : ∀ x y g : V, π s(x + g, y + g) = π s(x, y)) {C : ℝ≥0∞} {z : V}
    {F : V → ℝ≥0∞} (h : ∀ a, F a = tau π a z * C) :
    (∑' a, F a) = (∑' x, tau π 0 x) * C := by
  rw [tsum_congr h]
  simp only [ENNReal.tsum_mul_right]
  exact congrArg (fun t => t * C) (tau_col π hq z)

/-- **One endpoint summed, the other held, pair reversed, coefficient on the right.** -/
theorem peel_tau'_R [Countable V] [AddCommGroup V] (π : Sym2 V → unitInterval)
    (hq : ∀ x y g : V, π s(x + g, y + g) = π s(x, y)) {C : ℝ≥0∞} {z : V}
    {F : V → ℝ≥0∞} (h : ∀ a, F a = tau π z a * C) :
    (∑' a, F a) = (∑' x, tau π 0 x) * C := by
  rw [tsum_congr h]
  simp only [ENNReal.tsum_mul_right]
  exact congrArg (fun t => t * C) (tau_row π hq z)

/-! ## The socket evaluations

Each theorem is one sevenfold `ℝ≥0∞` sum, in an explicit peel order (innermost factor first).  The
docstring above each states the comb socket that is held and the peel sequence.  The `j = 0` group
has all three admissible comb sockets `0`, `1`, `2`; at `j = 1..6` it has the two sockets `0` and
`2` that the `Fin 15` pattern family uses. -/

/-- Root socket `b₀` at `j = 0`: `b0` is held and the five other comb terminals and the two interior vertices are summed.  Peel (innermost factor first): ears {b3,b4} at i₁; tau b2-i₁ over b2; pin i₂,i₁ about i₂; tau t-i₂ over t; tau b0-i₂ over i₂. -/
theorem slotU2_zero_tsum [Countable V] [AddCommGroup V] (π : Sym2 V → unitInterval)
    (hq : ∀ x y g : V, π s(x + g, y + g) = π s(x, y)) (b0 : V) :
    (∑' i₂, ∑' t, ∑' i₁, ∑' b1, ∑' b2, ∑' b3, ∑' b4, slotProd2 π 0 i₁ i₂ b0 b1 b2 b3 b4 t) =
      monomial2 π 0 := by
  classical
  have h1 : ∀ (i₂ t i₁ b1 b2 : V), (∑' b3, ∑' b4, slotProd2 π 0 i₁ i₂ b0 b1 b2 b3 b4 t) =
        secondMoment π 0 * (jointP π b1 i₂ i₁ * (tau π b2 i₁ * (tau π t i₂ * (tau π b0 i₂)))) := by
    intro i₂ t i₁ b1 b2
    refine peel_joint_ears_R π hq (C := jointP π b1 i₂ i₁ * (tau π b2 i₁ * (tau π t i₂ * (tau π b0 i₂)))) (z := i₁)
      (F := fun b3 b4 => slotProd2 π 0 i₁ i₂ b0 b1 b2 b3 b4 t) ?_
    intro b3 b4
    change jointP π b1 i₂ i₁ * (jointP π b3 b4 i₁ * (tau π b2 i₁ * (tau π t i₂ * (tau π b0 i₂)))) = jointP π b3 b4 i₁ * (jointP π b1 i₂ i₁ * (tau π b2 i₁ * (tau π t i₂ * (tau π b0 i₂))))
    ring
  have h2 : ∀ (i₂ t i₁ b1 : V), (∑' b2, secondMoment π 0 * (jointP π b1 i₂ i₁ * (tau π b2 i₁ * (tau π t i₂ * (tau π b0 i₂))))) =
        (∑' x, tau π 0 x) * (secondMoment π 0 * (jointP π b1 i₂ i₁ * (tau π t i₂ * (tau π b0 i₂)))) := by
    intro i₂ t i₁ b1
    refine peel_tau_R π hq (C := secondMoment π 0 * (jointP π b1 i₂ i₁ * (tau π t i₂ * (tau π b0 i₂)))) (z := i₁)
      (F := fun b2 => secondMoment π 0 * (jointP π b1 i₂ i₁ * (tau π b2 i₁ * (tau π t i₂ * (tau π b0 i₂))))) ?_
    intro b2
    ring
  have h3 : ∀ (i₂ t : V), (∑' i₁, ∑' b1, (∑' x, tau π 0 x) * (secondMoment π 0 * (jointP π b1 i₂ i₁ * (tau π t i₂ * (tau π b0 i₂))))) =
        secondMoment π 0 * ((∑' x, tau π 0 x) * (secondMoment π 0 * (tau π t i₂ * (tau π b0 i₂)))) := by
    intro i₂ t
    refine peel_pin_R π hq (C := (∑' x, tau π 0 x) * (secondMoment π 0 * (tau π t i₂ * (tau π b0 i₂)))) (r := i₂)
      (F := fun b1 i₁ => (∑' x, tau π 0 x) * (secondMoment π 0 * (jointP π b1 i₂ i₁ * (tau π t i₂ * (tau π b0 i₂))))) ?_
    intro b1 i₁
    rw [jointP_comm π i₂ b1 i₁]; ring
  have h4 : ∀ (i₂ : V), (∑' t, secondMoment π 0 * ((∑' x, tau π 0 x) * (secondMoment π 0 * (tau π t i₂ * (tau π b0 i₂))))) =
        (∑' x, tau π 0 x) * (secondMoment π 0 * ((∑' x, tau π 0 x) * (secondMoment π 0 * (tau π b0 i₂)))) := by
    intro i₂
    refine peel_tau_R π hq (C := secondMoment π 0 * ((∑' x, tau π 0 x) * (secondMoment π 0 * (tau π b0 i₂)))) (z := i₂)
      (F := fun t => secondMoment π 0 * ((∑' x, tau π 0 x) * (secondMoment π 0 * (tau π t i₂ * (tau π b0 i₂))))) ?_
    intro t
    ring
  have h5 : (∑' i₂, (∑' x, tau π 0 x) * (secondMoment π 0 * ((∑' x, tau π 0 x) * (secondMoment π 0 * (tau π b0 i₂))))) = monomial2 π 0 := by
    unfold monomial2
    rw [show (∑' i₂, (∑' x, tau π 0 x) * (secondMoment π 0 * ((∑' x, tau π 0 x) * (secondMoment π 0 * (tau π b0 i₂))))) = (∑' x, tau π 0 x) * ((∑' x, tau π 0 x) * (secondMoment π 0 * ((∑' x, tau π 0 x) * (secondMoment π 0)))) from by
      refine peel_tau'_R π hq (C := (∑' x, tau π 0 x) * (secondMoment π 0 * ((∑' x, tau π 0 x) * (secondMoment π 0)))) (z := b0)
        (F := fun i₂ => (∑' x, tau π 0 x) * (secondMoment π 0 * ((∑' x, tau π 0 x) * (secondMoment π 0 * (tau π b0 i₂))))) ?_
      intro i₂
      ring]
    ring
  refine (tsum_congr fun i₂ => tsum_congr fun t => tsum_congr fun i₁ => tsum_congr fun b1 => tsum_congr fun b2 => h1 i₂ t i₁ b1 b2).trans ?_
  refine (tsum_congr fun i₂ => tsum_congr fun t => tsum_congr fun i₁ => tsum_congr fun b1 => h2 i₂ t i₁ b1).trans ?_
  refine (tsum_congr fun i₂ => tsum_congr fun t => h3 i₂ t).trans ?_
  refine (tsum_congr fun i₂ => h4 i₂).trans ?_
  exact h5

/-- Root socket `b₁` at `j = 0`: `b1` is held and the five other comb terminals and the two interior vertices are summed.  Peel (innermost factor first): ears {b3,b4} at i₁; tau b2-i₁ over b2; tau t-i₂ over t; tau b0-i₂ over b0; pin i₂,i₁ about b1. -/
theorem slotW2_zero_tsum [Countable V] [AddCommGroup V] (π : Sym2 V → unitInterval)
    (hq : ∀ x y g : V, π s(x + g, y + g) = π s(x, y)) (b1 : V) :
    (∑' i₁, ∑' i₂, ∑' b0, ∑' t, ∑' b2, ∑' b3, ∑' b4, slotProd2 π 0 i₁ i₂ b0 b1 b2 b3 b4 t) =
      monomial2 π 0 := by
  classical
  have h1 : ∀ (i₁ i₂ b0 t b2 : V), (∑' b3, ∑' b4, slotProd2 π 0 i₁ i₂ b0 b1 b2 b3 b4 t) =
        secondMoment π 0 * (jointP π b1 i₂ i₁ * (tau π b2 i₁ * (tau π t i₂ * (tau π b0 i₂)))) := by
    intro i₁ i₂ b0 t b2
    refine peel_joint_ears_R π hq (C := jointP π b1 i₂ i₁ * (tau π b2 i₁ * (tau π t i₂ * (tau π b0 i₂)))) (z := i₁)
      (F := fun b3 b4 => slotProd2 π 0 i₁ i₂ b0 b1 b2 b3 b4 t) ?_
    intro b3 b4
    change jointP π b1 i₂ i₁ * (jointP π b3 b4 i₁ * (tau π b2 i₁ * (tau π t i₂ * (tau π b0 i₂)))) = jointP π b3 b4 i₁ * (jointP π b1 i₂ i₁ * (tau π b2 i₁ * (tau π t i₂ * (tau π b0 i₂))))
    ring
  have h2 : ∀ (i₁ i₂ b0 t : V), (∑' b2, secondMoment π 0 * (jointP π b1 i₂ i₁ * (tau π b2 i₁ * (tau π t i₂ * (tau π b0 i₂))))) =
        (∑' x, tau π 0 x) * (secondMoment π 0 * (jointP π b1 i₂ i₁ * (tau π t i₂ * (tau π b0 i₂)))) := by
    intro i₁ i₂ b0 t
    refine peel_tau_R π hq (C := secondMoment π 0 * (jointP π b1 i₂ i₁ * (tau π t i₂ * (tau π b0 i₂)))) (z := i₁)
      (F := fun b2 => secondMoment π 0 * (jointP π b1 i₂ i₁ * (tau π b2 i₁ * (tau π t i₂ * (tau π b0 i₂))))) ?_
    intro b2
    ring
  have h3 : ∀ (i₁ i₂ b0 : V), (∑' t, (∑' x, tau π 0 x) * (secondMoment π 0 * (jointP π b1 i₂ i₁ * (tau π t i₂ * (tau π b0 i₂))))) =
        (∑' x, tau π 0 x) * ((∑' x, tau π 0 x) * (secondMoment π 0 * (jointP π b1 i₂ i₁ * (tau π b0 i₂)))) := by
    intro i₁ i₂ b0
    refine peel_tau_R π hq (C := (∑' x, tau π 0 x) * (secondMoment π 0 * (jointP π b1 i₂ i₁ * (tau π b0 i₂)))) (z := i₂)
      (F := fun t => (∑' x, tau π 0 x) * (secondMoment π 0 * (jointP π b1 i₂ i₁ * (tau π t i₂ * (tau π b0 i₂))))) ?_
    intro t
    ring
  have h4 : ∀ (i₁ i₂ : V), (∑' b0, (∑' x, tau π 0 x) * ((∑' x, tau π 0 x) * (secondMoment π 0 * (jointP π b1 i₂ i₁ * (tau π b0 i₂))))) =
        (∑' x, tau π 0 x) * ((∑' x, tau π 0 x) * ((∑' x, tau π 0 x) * (secondMoment π 0 * (jointP π b1 i₂ i₁)))) := by
    intro i₁ i₂
    refine peel_tau_R π hq (C := (∑' x, tau π 0 x) * ((∑' x, tau π 0 x) * (secondMoment π 0 * (jointP π b1 i₂ i₁)))) (z := i₂)
      (F := fun b0 => (∑' x, tau π 0 x) * ((∑' x, tau π 0 x) * (secondMoment π 0 * (jointP π b1 i₂ i₁ * (tau π b0 i₂))))) ?_
    intro b0
    ring
  have h5 : (∑' i₁, ∑' i₂, (∑' x, tau π 0 x) * ((∑' x, tau π 0 x) * ((∑' x, tau π 0 x) * (secondMoment π 0 * (jointP π b1 i₂ i₁))))) = monomial2 π 0 := by
    unfold monomial2
    rw [show (∑' i₁, ∑' i₂, (∑' x, tau π 0 x) * ((∑' x, tau π 0 x) * ((∑' x, tau π 0 x) * (secondMoment π 0 * (jointP π b1 i₂ i₁))))) = secondMoment π 0 * ((∑' x, tau π 0 x) * ((∑' x, tau π 0 x) * ((∑' x, tau π 0 x) * (secondMoment π 0)))) from by
      refine peel_pin_R π hq (C := (∑' x, tau π 0 x) * ((∑' x, tau π 0 x) * ((∑' x, tau π 0 x) * (secondMoment π 0)))) (r := b1)
        (F := fun i₂ i₁ => (∑' x, tau π 0 x) * ((∑' x, tau π 0 x) * ((∑' x, tau π 0 x) * (secondMoment π 0 * (jointP π b1 i₂ i₁))))) ?_
      intro i₂ i₁
      ring]
    ring
  refine (tsum_congr fun i₁ => tsum_congr fun i₂ => tsum_congr fun b0 => tsum_congr fun t => tsum_congr fun b2 => h1 i₁ i₂ b0 t b2).trans ?_
  refine (tsum_congr fun i₁ => tsum_congr fun i₂ => tsum_congr fun b0 => tsum_congr fun t => h2 i₁ i₂ b0 t).trans ?_
  refine (tsum_congr fun i₁ => tsum_congr fun i₂ => tsum_congr fun b0 => h3 i₁ i₂ b0).trans ?_
  refine (tsum_congr fun i₁ => tsum_congr fun i₂ => h4 i₁ i₂).trans ?_
  exact h5

/-- Root socket `b₂` at `j = 0`: `b2` is held and the five other comb terminals and the two interior vertices are summed.  Peel (innermost factor first): ears {b3,b4} at i₁; tau b0-i₂ over b0; tau t-i₂ over t; ears {b1,i₂} at i₁; tau b2-i₁ over i₁. -/
theorem slotV2_zero_tsum [Countable V] [AddCommGroup V] (π : Sym2 V → unitInterval)
    (hq : ∀ x y g : V, π s(x + g, y + g) = π s(x, y)) (b2 : V) :
    (∑' i₁, ∑' b1, ∑' i₂, ∑' t, ∑' b0, ∑' b3, ∑' b4, slotProd2 π 0 i₁ i₂ b0 b1 b2 b3 b4 t) =
      monomial2 π 0 := by
  classical
  have h1 : ∀ (i₁ b1 i₂ t b0 : V), (∑' b3, ∑' b4, slotProd2 π 0 i₁ i₂ b0 b1 b2 b3 b4 t) =
        secondMoment π 0 * (jointP π b1 i₂ i₁ * (tau π b2 i₁ * (tau π t i₂ * (tau π b0 i₂)))) := by
    intro i₁ b1 i₂ t b0
    refine peel_joint_ears_R π hq (C := jointP π b1 i₂ i₁ * (tau π b2 i₁ * (tau π t i₂ * (tau π b0 i₂)))) (z := i₁)
      (F := fun b3 b4 => slotProd2 π 0 i₁ i₂ b0 b1 b2 b3 b4 t) ?_
    intro b3 b4
    change jointP π b1 i₂ i₁ * (jointP π b3 b4 i₁ * (tau π b2 i₁ * (tau π t i₂ * (tau π b0 i₂)))) = jointP π b3 b4 i₁ * (jointP π b1 i₂ i₁ * (tau π b2 i₁ * (tau π t i₂ * (tau π b0 i₂))))
    ring
  have h2 : ∀ (i₁ b1 i₂ t : V), (∑' b0, secondMoment π 0 * (jointP π b1 i₂ i₁ * (tau π b2 i₁ * (tau π t i₂ * (tau π b0 i₂))))) =
        (∑' x, tau π 0 x) * (secondMoment π 0 * (jointP π b1 i₂ i₁ * (tau π b2 i₁ * (tau π t i₂)))) := by
    intro i₁ b1 i₂ t
    refine peel_tau_R π hq (C := secondMoment π 0 * (jointP π b1 i₂ i₁ * (tau π b2 i₁ * (tau π t i₂)))) (z := i₂)
      (F := fun b0 => secondMoment π 0 * (jointP π b1 i₂ i₁ * (tau π b2 i₁ * (tau π t i₂ * (tau π b0 i₂))))) ?_
    intro b0
    ring
  have h3 : ∀ (i₁ b1 i₂ : V), (∑' t, (∑' x, tau π 0 x) * (secondMoment π 0 * (jointP π b1 i₂ i₁ * (tau π b2 i₁ * (tau π t i₂))))) =
        (∑' x, tau π 0 x) * ((∑' x, tau π 0 x) * (secondMoment π 0 * (jointP π b1 i₂ i₁ * (tau π b2 i₁)))) := by
    intro i₁ b1 i₂
    refine peel_tau_R π hq (C := (∑' x, tau π 0 x) * (secondMoment π 0 * (jointP π b1 i₂ i₁ * (tau π b2 i₁)))) (z := i₂)
      (F := fun t => (∑' x, tau π 0 x) * (secondMoment π 0 * (jointP π b1 i₂ i₁ * (tau π b2 i₁ * (tau π t i₂))))) ?_
    intro t
    ring
  have h4 : ∀ (i₁ : V), (∑' b1, ∑' i₂, (∑' x, tau π 0 x) * ((∑' x, tau π 0 x) * (secondMoment π 0 * (jointP π b1 i₂ i₁ * (tau π b2 i₁))))) =
        secondMoment π 0 * ((∑' x, tau π 0 x) * ((∑' x, tau π 0 x) * (secondMoment π 0 * (tau π b2 i₁)))) := by
    intro i₁
    refine peel_joint_ears_R π hq (C := (∑' x, tau π 0 x) * ((∑' x, tau π 0 x) * (secondMoment π 0 * (tau π b2 i₁)))) (z := i₁)
      (F := fun b1 i₂ => (∑' x, tau π 0 x) * ((∑' x, tau π 0 x) * (secondMoment π 0 * (jointP π b1 i₂ i₁ * (tau π b2 i₁))))) ?_
    intro b1 i₂
    ring
  have h5 : (∑' i₁, secondMoment π 0 * ((∑' x, tau π 0 x) * ((∑' x, tau π 0 x) * (secondMoment π 0 * (tau π b2 i₁))))) = monomial2 π 0 := by
    unfold monomial2
    rw [show (∑' i₁, secondMoment π 0 * ((∑' x, tau π 0 x) * ((∑' x, tau π 0 x) * (secondMoment π 0 * (tau π b2 i₁))))) = (∑' x, tau π 0 x) * (secondMoment π 0 * ((∑' x, tau π 0 x) * ((∑' x, tau π 0 x) * (secondMoment π 0)))) from by
      refine peel_tau'_R π hq (C := secondMoment π 0 * ((∑' x, tau π 0 x) * ((∑' x, tau π 0 x) * (secondMoment π 0)))) (z := b2)
        (F := fun i₁ => secondMoment π 0 * ((∑' x, tau π 0 x) * ((∑' x, tau π 0 x) * (secondMoment π 0 * (tau π b2 i₁))))) ?_
      intro i₁
      ring]
    ring
  refine (tsum_congr fun i₁ => tsum_congr fun b1 => tsum_congr fun i₂ => tsum_congr fun t => tsum_congr fun b0 => h1 i₁ b1 i₂ t b0).trans ?_
  refine (tsum_congr fun i₁ => tsum_congr fun b1 => tsum_congr fun i₂ => tsum_congr fun t => h2 i₁ b1 i₂ t).trans ?_
  refine (tsum_congr fun i₁ => tsum_congr fun b1 => tsum_congr fun i₂ => h3 i₁ b1 i₂).trans ?_
  refine (tsum_congr fun i₁ => h4 i₁).trans ?_
  exact h5

/-- Root socket `b₀` at `j = 1`: `b0` is held and the five other comb terminals and the two interior vertices are summed.  Peel (innermost factor first): ears {b3,b4} at i₁; tau b2-i₁ over b2; tau t-i₂ over t; tau b1-i₂ over b1; pin i₂,i₁ about b0. -/
theorem slotU2_one_tsum [Countable V] [AddCommGroup V] (π : Sym2 V → unitInterval)
    (hq : ∀ x y g : V, π s(x + g, y + g) = π s(x, y)) (b0 : V) :
    (∑' i₁, ∑' i₂, ∑' b1, ∑' t, ∑' b2, ∑' b3, ∑' b4, slotProd2 π 1 i₁ i₂ b0 b1 b2 b3 b4 t) =
      monomial2 π 0 := by
  classical
  have h1 : ∀ (i₁ i₂ b1 t b2 : V), (∑' b3, ∑' b4, slotProd2 π 1 i₁ i₂ b0 b1 b2 b3 b4 t) =
        secondMoment π 0 * (jointP π b0 i₂ i₁ * (tau π b2 i₁ * (tau π b1 i₂ * (tau π t i₂)))) := by
    intro i₁ i₂ b1 t b2
    refine peel_joint_ears_R π hq (C := jointP π b0 i₂ i₁ * (tau π b2 i₁ * (tau π b1 i₂ * (tau π t i₂)))) (z := i₁)
      (F := fun b3 b4 => slotProd2 π 1 i₁ i₂ b0 b1 b2 b3 b4 t) ?_
    intro b3 b4
    change jointP π b0 i₂ i₁ * (jointP π b3 b4 i₁ * (tau π b2 i₁ * (tau π b1 i₂ * (tau π t i₂)))) = jointP π b3 b4 i₁ * (jointP π b0 i₂ i₁ * (tau π b2 i₁ * (tau π b1 i₂ * (tau π t i₂))))
    ring
  have h2 : ∀ (i₁ i₂ b1 t : V), (∑' b2, secondMoment π 0 * (jointP π b0 i₂ i₁ * (tau π b2 i₁ * (tau π b1 i₂ * (tau π t i₂))))) =
        (∑' x, tau π 0 x) * (secondMoment π 0 * (jointP π b0 i₂ i₁ * (tau π b1 i₂ * (tau π t i₂)))) := by
    intro i₁ i₂ b1 t
    refine peel_tau_R π hq (C := secondMoment π 0 * (jointP π b0 i₂ i₁ * (tau π b1 i₂ * (tau π t i₂)))) (z := i₁)
      (F := fun b2 => secondMoment π 0 * (jointP π b0 i₂ i₁ * (tau π b2 i₁ * (tau π b1 i₂ * (tau π t i₂))))) ?_
    intro b2
    ring
  have h3 : ∀ (i₁ i₂ b1 : V), (∑' t, (∑' x, tau π 0 x) * (secondMoment π 0 * (jointP π b0 i₂ i₁ * (tau π b1 i₂ * (tau π t i₂))))) =
        (∑' x, tau π 0 x) * ((∑' x, tau π 0 x) * (secondMoment π 0 * (jointP π b0 i₂ i₁ * (tau π b1 i₂)))) := by
    intro i₁ i₂ b1
    refine peel_tau_R π hq (C := (∑' x, tau π 0 x) * (secondMoment π 0 * (jointP π b0 i₂ i₁ * (tau π b1 i₂)))) (z := i₂)
      (F := fun t => (∑' x, tau π 0 x) * (secondMoment π 0 * (jointP π b0 i₂ i₁ * (tau π b1 i₂ * (tau π t i₂))))) ?_
    intro t
    ring
  have h4 : ∀ (i₁ i₂ : V), (∑' b1, (∑' x, tau π 0 x) * ((∑' x, tau π 0 x) * (secondMoment π 0 * (jointP π b0 i₂ i₁ * (tau π b1 i₂))))) =
        (∑' x, tau π 0 x) * ((∑' x, tau π 0 x) * ((∑' x, tau π 0 x) * (secondMoment π 0 * (jointP π b0 i₂ i₁)))) := by
    intro i₁ i₂
    refine peel_tau_R π hq (C := (∑' x, tau π 0 x) * ((∑' x, tau π 0 x) * (secondMoment π 0 * (jointP π b0 i₂ i₁)))) (z := i₂)
      (F := fun b1 => (∑' x, tau π 0 x) * ((∑' x, tau π 0 x) * (secondMoment π 0 * (jointP π b0 i₂ i₁ * (tau π b1 i₂))))) ?_
    intro b1
    ring
  have h5 : (∑' i₁, ∑' i₂, (∑' x, tau π 0 x) * ((∑' x, tau π 0 x) * ((∑' x, tau π 0 x) * (secondMoment π 0 * (jointP π b0 i₂ i₁))))) = monomial2 π 0 := by
    unfold monomial2
    rw [show (∑' i₁, ∑' i₂, (∑' x, tau π 0 x) * ((∑' x, tau π 0 x) * ((∑' x, tau π 0 x) * (secondMoment π 0 * (jointP π b0 i₂ i₁))))) = secondMoment π 0 * ((∑' x, tau π 0 x) * ((∑' x, tau π 0 x) * ((∑' x, tau π 0 x) * (secondMoment π 0)))) from by
      refine peel_pin_R π hq (C := (∑' x, tau π 0 x) * ((∑' x, tau π 0 x) * ((∑' x, tau π 0 x) * (secondMoment π 0)))) (r := b0)
        (F := fun i₂ i₁ => (∑' x, tau π 0 x) * ((∑' x, tau π 0 x) * ((∑' x, tau π 0 x) * (secondMoment π 0 * (jointP π b0 i₂ i₁))))) ?_
      intro i₂ i₁
      ring]
    ring
  refine (tsum_congr fun i₁ => tsum_congr fun i₂ => tsum_congr fun b1 => tsum_congr fun t => tsum_congr fun b2 => h1 i₁ i₂ b1 t b2).trans ?_
  refine (tsum_congr fun i₁ => tsum_congr fun i₂ => tsum_congr fun b1 => tsum_congr fun t => h2 i₁ i₂ b1 t).trans ?_
  refine (tsum_congr fun i₁ => tsum_congr fun i₂ => tsum_congr fun b1 => h3 i₁ i₂ b1).trans ?_
  refine (tsum_congr fun i₁ => tsum_congr fun i₂ => h4 i₁ i₂).trans ?_
  exact h5

/-- Root socket `b₂` at `j = 1`: `b2` is held and the five other comb terminals and the two interior vertices are summed.  Peel (innermost factor first): ears {b3,b4} at i₁; tau b1-i₂ over b1; tau t-i₂ over t; ears {b0,i₂} at i₁; tau b2-i₁ over i₁. -/
theorem slotV2_one_tsum [Countable V] [AddCommGroup V] (π : Sym2 V → unitInterval)
    (hq : ∀ x y g : V, π s(x + g, y + g) = π s(x, y)) (b2 : V) :
    (∑' i₁, ∑' b0, ∑' i₂, ∑' t, ∑' b1, ∑' b3, ∑' b4, slotProd2 π 1 i₁ i₂ b0 b1 b2 b3 b4 t) =
      monomial2 π 0 := by
  classical
  have h1 : ∀ (i₁ b0 i₂ t b1 : V), (∑' b3, ∑' b4, slotProd2 π 1 i₁ i₂ b0 b1 b2 b3 b4 t) =
        secondMoment π 0 * (jointP π b0 i₂ i₁ * (tau π b2 i₁ * (tau π b1 i₂ * (tau π t i₂)))) := by
    intro i₁ b0 i₂ t b1
    refine peel_joint_ears_R π hq (C := jointP π b0 i₂ i₁ * (tau π b2 i₁ * (tau π b1 i₂ * (tau π t i₂)))) (z := i₁)
      (F := fun b3 b4 => slotProd2 π 1 i₁ i₂ b0 b1 b2 b3 b4 t) ?_
    intro b3 b4
    change jointP π b0 i₂ i₁ * (jointP π b3 b4 i₁ * (tau π b2 i₁ * (tau π b1 i₂ * (tau π t i₂)))) = jointP π b3 b4 i₁ * (jointP π b0 i₂ i₁ * (tau π b2 i₁ * (tau π b1 i₂ * (tau π t i₂))))
    ring
  have h2 : ∀ (i₁ b0 i₂ t : V), (∑' b1, secondMoment π 0 * (jointP π b0 i₂ i₁ * (tau π b2 i₁ * (tau π b1 i₂ * (tau π t i₂))))) =
        (∑' x, tau π 0 x) * (secondMoment π 0 * (jointP π b0 i₂ i₁ * (tau π b2 i₁ * (tau π t i₂)))) := by
    intro i₁ b0 i₂ t
    refine peel_tau_R π hq (C := secondMoment π 0 * (jointP π b0 i₂ i₁ * (tau π b2 i₁ * (tau π t i₂)))) (z := i₂)
      (F := fun b1 => secondMoment π 0 * (jointP π b0 i₂ i₁ * (tau π b2 i₁ * (tau π b1 i₂ * (tau π t i₂))))) ?_
    intro b1
    ring
  have h3 : ∀ (i₁ b0 i₂ : V), (∑' t, (∑' x, tau π 0 x) * (secondMoment π 0 * (jointP π b0 i₂ i₁ * (tau π b2 i₁ * (tau π t i₂))))) =
        (∑' x, tau π 0 x) * ((∑' x, tau π 0 x) * (secondMoment π 0 * (jointP π b0 i₂ i₁ * (tau π b2 i₁)))) := by
    intro i₁ b0 i₂
    refine peel_tau_R π hq (C := (∑' x, tau π 0 x) * (secondMoment π 0 * (jointP π b0 i₂ i₁ * (tau π b2 i₁)))) (z := i₂)
      (F := fun t => (∑' x, tau π 0 x) * (secondMoment π 0 * (jointP π b0 i₂ i₁ * (tau π b2 i₁ * (tau π t i₂))))) ?_
    intro t
    ring
  have h4 : ∀ (i₁ : V), (∑' b0, ∑' i₂, (∑' x, tau π 0 x) * ((∑' x, tau π 0 x) * (secondMoment π 0 * (jointP π b0 i₂ i₁ * (tau π b2 i₁))))) =
        secondMoment π 0 * ((∑' x, tau π 0 x) * ((∑' x, tau π 0 x) * (secondMoment π 0 * (tau π b2 i₁)))) := by
    intro i₁
    refine peel_joint_ears_R π hq (C := (∑' x, tau π 0 x) * ((∑' x, tau π 0 x) * (secondMoment π 0 * (tau π b2 i₁)))) (z := i₁)
      (F := fun b0 i₂ => (∑' x, tau π 0 x) * ((∑' x, tau π 0 x) * (secondMoment π 0 * (jointP π b0 i₂ i₁ * (tau π b2 i₁))))) ?_
    intro b0 i₂
    ring
  have h5 : (∑' i₁, secondMoment π 0 * ((∑' x, tau π 0 x) * ((∑' x, tau π 0 x) * (secondMoment π 0 * (tau π b2 i₁))))) = monomial2 π 0 := by
    unfold monomial2
    rw [show (∑' i₁, secondMoment π 0 * ((∑' x, tau π 0 x) * ((∑' x, tau π 0 x) * (secondMoment π 0 * (tau π b2 i₁))))) = (∑' x, tau π 0 x) * (secondMoment π 0 * ((∑' x, tau π 0 x) * ((∑' x, tau π 0 x) * (secondMoment π 0)))) from by
      refine peel_tau'_R π hq (C := secondMoment π 0 * ((∑' x, tau π 0 x) * ((∑' x, tau π 0 x) * (secondMoment π 0)))) (z := b2)
        (F := fun i₁ => secondMoment π 0 * ((∑' x, tau π 0 x) * ((∑' x, tau π 0 x) * (secondMoment π 0 * (tau π b2 i₁))))) ?_
      intro i₁
      ring]
    ring
  refine (tsum_congr fun i₁ => tsum_congr fun b0 => tsum_congr fun i₂ => tsum_congr fun t => tsum_congr fun b1 => h1 i₁ b0 i₂ t b1).trans ?_
  refine (tsum_congr fun i₁ => tsum_congr fun b0 => tsum_congr fun i₂ => tsum_congr fun t => h2 i₁ b0 i₂ t).trans ?_
  refine (tsum_congr fun i₁ => tsum_congr fun b0 => tsum_congr fun i₂ => h3 i₁ b0 i₂).trans ?_
  refine (tsum_congr fun i₁ => h4 i₁).trans ?_
  exact h5

/-- Root socket `b₀` at `j = 3`: `b0` is held and the five other comb terminals and the two interior vertices are summed.  Peel (innermost factor first): tau b3-i₂ over b3; tau t-i₂ over t; ears {b4,i₂} at i₁; tau b2-i₁ over b2; pin b1,i₁ about b0. -/
theorem slotU2_three_tsum [Countable V] [AddCommGroup V] (π : Sym2 V → unitInterval)
    (hq : ∀ x y g : V, π s(x + g, y + g) = π s(x, y)) (b0 : V) :
    (∑' i₁, ∑' b1, ∑' b2, ∑' b4, ∑' i₂, ∑' t, ∑' b3, slotProd2 π 3 i₁ i₂ b0 b1 b2 b3 b4 t) =
      monomial2 π 0 := by
  classical
  have h1 : ∀ (i₁ b1 b2 b4 i₂ t : V), (∑' b3, slotProd2 π 3 i₁ i₂ b0 b1 b2 b3 b4 t) =
        (∑' x, tau π 0 x) * (jointP π b0 b1 i₁ * (jointP π b4 i₂ i₁ * (tau π b2 i₁ * (tau π t i₂)))) := by
    intro i₁ b1 b2 b4 i₂ t
    refine peel_tau_R π hq (C := jointP π b0 b1 i₁ * (jointP π b4 i₂ i₁ * (tau π b2 i₁ * (tau π t i₂)))) (z := i₂)
      (F := fun b3 => slotProd2 π 3 i₁ i₂ b0 b1 b2 b3 b4 t) ?_
    intro b3
    change jointP π b0 b1 i₁ * (jointP π b4 i₂ i₁ * (tau π b2 i₁ * (tau π b3 i₂ * (tau π t i₂)))) = tau π b3 i₂ * (jointP π b0 b1 i₁ * (jointP π b4 i₂ i₁ * (tau π b2 i₁ * (tau π t i₂))))
    ring
  have h2 : ∀ (i₁ b1 b2 b4 i₂ : V), (∑' t, (∑' x, tau π 0 x) * (jointP π b0 b1 i₁ * (jointP π b4 i₂ i₁ * (tau π b2 i₁ * (tau π t i₂))))) =
        (∑' x, tau π 0 x) * ((∑' x, tau π 0 x) * (jointP π b0 b1 i₁ * (jointP π b4 i₂ i₁ * (tau π b2 i₁)))) := by
    intro i₁ b1 b2 b4 i₂
    refine peel_tau_R π hq (C := (∑' x, tau π 0 x) * (jointP π b0 b1 i₁ * (jointP π b4 i₂ i₁ * (tau π b2 i₁)))) (z := i₂)
      (F := fun t => (∑' x, tau π 0 x) * (jointP π b0 b1 i₁ * (jointP π b4 i₂ i₁ * (tau π b2 i₁ * (tau π t i₂))))) ?_
    intro t
    ring
  have h3 : ∀ (i₁ b1 b2 : V), (∑' b4, ∑' i₂, (∑' x, tau π 0 x) * ((∑' x, tau π 0 x) * (jointP π b0 b1 i₁ * (jointP π b4 i₂ i₁ * (tau π b2 i₁))))) =
        secondMoment π 0 * ((∑' x, tau π 0 x) * ((∑' x, tau π 0 x) * (jointP π b0 b1 i₁ * (tau π b2 i₁)))) := by
    intro i₁ b1 b2
    refine peel_joint_ears_R π hq (C := (∑' x, tau π 0 x) * ((∑' x, tau π 0 x) * (jointP π b0 b1 i₁ * (tau π b2 i₁)))) (z := i₁)
      (F := fun b4 i₂ => (∑' x, tau π 0 x) * ((∑' x, tau π 0 x) * (jointP π b0 b1 i₁ * (jointP π b4 i₂ i₁ * (tau π b2 i₁))))) ?_
    intro b4 i₂
    ring
  have h4 : ∀ (i₁ b1 : V), (∑' b2, secondMoment π 0 * ((∑' x, tau π 0 x) * ((∑' x, tau π 0 x) * (jointP π b0 b1 i₁ * (tau π b2 i₁))))) =
        (∑' x, tau π 0 x) * (secondMoment π 0 * ((∑' x, tau π 0 x) * ((∑' x, tau π 0 x) * (jointP π b0 b1 i₁)))) := by
    intro i₁ b1
    refine peel_tau_R π hq (C := secondMoment π 0 * ((∑' x, tau π 0 x) * ((∑' x, tau π 0 x) * (jointP π b0 b1 i₁)))) (z := i₁)
      (F := fun b2 => secondMoment π 0 * ((∑' x, tau π 0 x) * ((∑' x, tau π 0 x) * (jointP π b0 b1 i₁ * (tau π b2 i₁))))) ?_
    intro b2
    ring
  have h5 : (∑' i₁, ∑' b1, (∑' x, tau π 0 x) * (secondMoment π 0 * ((∑' x, tau π 0 x) * ((∑' x, tau π 0 x) * (jointP π b0 b1 i₁))))) = monomial2 π 0 := by
    unfold monomial2
    rw [show (∑' i₁, ∑' b1, (∑' x, tau π 0 x) * (secondMoment π 0 * ((∑' x, tau π 0 x) * ((∑' x, tau π 0 x) * (jointP π b0 b1 i₁))))) = secondMoment π 0 * ((∑' x, tau π 0 x) * (secondMoment π 0 * ((∑' x, tau π 0 x) * ((∑' x, tau π 0 x))))) from by
      refine peel_pin_R π hq (C := (∑' x, tau π 0 x) * (secondMoment π 0 * ((∑' x, tau π 0 x) * ((∑' x, tau π 0 x))))) (r := b0)
        (F := fun b1 i₁ => (∑' x, tau π 0 x) * (secondMoment π 0 * ((∑' x, tau π 0 x) * ((∑' x, tau π 0 x) * (jointP π b0 b1 i₁))))) ?_
      intro b1 i₁
      ring]
    ring
  refine (tsum_congr fun i₁ => tsum_congr fun b1 => tsum_congr fun b2 => tsum_congr fun b4 => tsum_congr fun i₂ => tsum_congr fun t => h1 i₁ b1 b2 b4 i₂ t).trans ?_
  refine (tsum_congr fun i₁ => tsum_congr fun b1 => tsum_congr fun b2 => tsum_congr fun b4 => tsum_congr fun i₂ => h2 i₁ b1 b2 b4 i₂).trans ?_
  refine (tsum_congr fun i₁ => tsum_congr fun b1 => tsum_congr fun b2 => h3 i₁ b1 b2).trans ?_
  refine (tsum_congr fun i₁ => tsum_congr fun b1 => h4 i₁ b1).trans ?_
  exact h5

/-- Root socket `b₂` at `j = 3`: `b2` is held and the five other comb terminals and the two interior vertices are summed.  Peel (innermost factor first): tau b3-i₂ over b3; tau t-i₂ over t; ears {b4,i₂} at i₁; ears {b0,b1} at i₁; tau b2-i₁ over i₁. -/
theorem slotV2_three_tsum [Countable V] [AddCommGroup V] (π : Sym2 V → unitInterval)
    (hq : ∀ x y g : V, π s(x + g, y + g) = π s(x, y)) (b2 : V) :
    (∑' i₁, ∑' b0, ∑' b1, ∑' b4, ∑' i₂, ∑' t, ∑' b3, slotProd2 π 3 i₁ i₂ b0 b1 b2 b3 b4 t) =
      monomial2 π 0 := by
  classical
  have h1 : ∀ (i₁ b0 b1 b4 i₂ t : V), (∑' b3, slotProd2 π 3 i₁ i₂ b0 b1 b2 b3 b4 t) =
        (∑' x, tau π 0 x) * (jointP π b0 b1 i₁ * (jointP π b4 i₂ i₁ * (tau π b2 i₁ * (tau π t i₂)))) := by
    intro i₁ b0 b1 b4 i₂ t
    refine peel_tau_R π hq (C := jointP π b0 b1 i₁ * (jointP π b4 i₂ i₁ * (tau π b2 i₁ * (tau π t i₂)))) (z := i₂)
      (F := fun b3 => slotProd2 π 3 i₁ i₂ b0 b1 b2 b3 b4 t) ?_
    intro b3
    change jointP π b0 b1 i₁ * (jointP π b4 i₂ i₁ * (tau π b2 i₁ * (tau π b3 i₂ * (tau π t i₂)))) = tau π b3 i₂ * (jointP π b0 b1 i₁ * (jointP π b4 i₂ i₁ * (tau π b2 i₁ * (tau π t i₂))))
    ring
  have h2 : ∀ (i₁ b0 b1 b4 i₂ : V), (∑' t, (∑' x, tau π 0 x) * (jointP π b0 b1 i₁ * (jointP π b4 i₂ i₁ * (tau π b2 i₁ * (tau π t i₂))))) =
        (∑' x, tau π 0 x) * ((∑' x, tau π 0 x) * (jointP π b0 b1 i₁ * (jointP π b4 i₂ i₁ * (tau π b2 i₁)))) := by
    intro i₁ b0 b1 b4 i₂
    refine peel_tau_R π hq (C := (∑' x, tau π 0 x) * (jointP π b0 b1 i₁ * (jointP π b4 i₂ i₁ * (tau π b2 i₁)))) (z := i₂)
      (F := fun t => (∑' x, tau π 0 x) * (jointP π b0 b1 i₁ * (jointP π b4 i₂ i₁ * (tau π b2 i₁ * (tau π t i₂))))) ?_
    intro t
    ring
  have h3 : ∀ (i₁ b0 b1 : V), (∑' b4, ∑' i₂, (∑' x, tau π 0 x) * ((∑' x, tau π 0 x) * (jointP π b0 b1 i₁ * (jointP π b4 i₂ i₁ * (tau π b2 i₁))))) =
        secondMoment π 0 * ((∑' x, tau π 0 x) * ((∑' x, tau π 0 x) * (jointP π b0 b1 i₁ * (tau π b2 i₁)))) := by
    intro i₁ b0 b1
    refine peel_joint_ears_R π hq (C := (∑' x, tau π 0 x) * ((∑' x, tau π 0 x) * (jointP π b0 b1 i₁ * (tau π b2 i₁)))) (z := i₁)
      (F := fun b4 i₂ => (∑' x, tau π 0 x) * ((∑' x, tau π 0 x) * (jointP π b0 b1 i₁ * (jointP π b4 i₂ i₁ * (tau π b2 i₁))))) ?_
    intro b4 i₂
    ring
  have h4 : ∀ (i₁ : V), (∑' b0, ∑' b1, secondMoment π 0 * ((∑' x, tau π 0 x) * ((∑' x, tau π 0 x) * (jointP π b0 b1 i₁ * (tau π b2 i₁))))) =
        secondMoment π 0 * (secondMoment π 0 * ((∑' x, tau π 0 x) * ((∑' x, tau π 0 x) * (tau π b2 i₁)))) := by
    intro i₁
    refine peel_joint_ears_R π hq (C := secondMoment π 0 * ((∑' x, tau π 0 x) * ((∑' x, tau π 0 x) * (tau π b2 i₁)))) (z := i₁)
      (F := fun b0 b1 => secondMoment π 0 * ((∑' x, tau π 0 x) * ((∑' x, tau π 0 x) * (jointP π b0 b1 i₁ * (tau π b2 i₁))))) ?_
    intro b0 b1
    ring
  have h5 : (∑' i₁, secondMoment π 0 * (secondMoment π 0 * ((∑' x, tau π 0 x) * ((∑' x, tau π 0 x) * (tau π b2 i₁))))) = monomial2 π 0 := by
    unfold monomial2
    rw [show (∑' i₁, secondMoment π 0 * (secondMoment π 0 * ((∑' x, tau π 0 x) * ((∑' x, tau π 0 x) * (tau π b2 i₁))))) = (∑' x, tau π 0 x) * (secondMoment π 0 * (secondMoment π 0 * ((∑' x, tau π 0 x) * ((∑' x, tau π 0 x))))) from by
      refine peel_tau'_R π hq (C := secondMoment π 0 * (secondMoment π 0 * ((∑' x, tau π 0 x) * ((∑' x, tau π 0 x))))) (z := b2)
        (F := fun i₁ => secondMoment π 0 * (secondMoment π 0 * ((∑' x, tau π 0 x) * ((∑' x, tau π 0 x) * (tau π b2 i₁))))) ?_
      intro i₁
      ring]
    ring
  refine (tsum_congr fun i₁ => tsum_congr fun b0 => tsum_congr fun b1 => tsum_congr fun b4 => tsum_congr fun i₂ => tsum_congr fun t => h1 i₁ b0 b1 b4 i₂ t).trans ?_
  refine (tsum_congr fun i₁ => tsum_congr fun b0 => tsum_congr fun b1 => tsum_congr fun b4 => tsum_congr fun i₂ => h2 i₁ b0 b1 b4 i₂).trans ?_
  refine (tsum_congr fun i₁ => tsum_congr fun b0 => tsum_congr fun b1 => h3 i₁ b0 b1).trans ?_
  refine (tsum_congr fun i₁ => h4 i₁).trans ?_
  exact h5

/-- Root socket `b₀` at `j = 4`: `b0` is held and the five other comb terminals and the two interior vertices are summed.  Peel (innermost factor first): tau b4-i₂ over b4; tau t-i₂ over t; ears {b3,i₂} at i₁; tau b2-i₁ over b2; pin b1,i₁ about b0. -/
theorem slotU2_four_tsum [Countable V] [AddCommGroup V] (π : Sym2 V → unitInterval)
    (hq : ∀ x y g : V, π s(x + g, y + g) = π s(x, y)) (b0 : V) :
    (∑' i₁, ∑' b1, ∑' b2, ∑' b3, ∑' i₂, ∑' t, ∑' b4, slotProd2 π 4 i₁ i₂ b0 b1 b2 b3 b4 t) =
      monomial2 π 0 := by
  classical
  have h1 : ∀ (i₁ b1 b2 b3 i₂ t : V), (∑' b4, slotProd2 π 4 i₁ i₂ b0 b1 b2 b3 b4 t) =
        (∑' x, tau π 0 x) * (jointP π b0 b1 i₁ * (jointP π b3 i₂ i₁ * (tau π b2 i₁ * (tau π t i₂)))) := by
    intro i₁ b1 b2 b3 i₂ t
    refine peel_tau_R π hq (C := jointP π b0 b1 i₁ * (jointP π b3 i₂ i₁ * (tau π b2 i₁ * (tau π t i₂)))) (z := i₂)
      (F := fun b4 => slotProd2 π 4 i₁ i₂ b0 b1 b2 b3 b4 t) ?_
    intro b4
    change jointP π b0 b1 i₁ * (jointP π b3 i₂ i₁ * (tau π b2 i₁ * (tau π b4 i₂ * (tau π t i₂)))) = tau π b4 i₂ * (jointP π b0 b1 i₁ * (jointP π b3 i₂ i₁ * (tau π b2 i₁ * (tau π t i₂))))
    ring
  have h2 : ∀ (i₁ b1 b2 b3 i₂ : V), (∑' t, (∑' x, tau π 0 x) * (jointP π b0 b1 i₁ * (jointP π b3 i₂ i₁ * (tau π b2 i₁ * (tau π t i₂))))) =
        (∑' x, tau π 0 x) * ((∑' x, tau π 0 x) * (jointP π b0 b1 i₁ * (jointP π b3 i₂ i₁ * (tau π b2 i₁)))) := by
    intro i₁ b1 b2 b3 i₂
    refine peel_tau_R π hq (C := (∑' x, tau π 0 x) * (jointP π b0 b1 i₁ * (jointP π b3 i₂ i₁ * (tau π b2 i₁)))) (z := i₂)
      (F := fun t => (∑' x, tau π 0 x) * (jointP π b0 b1 i₁ * (jointP π b3 i₂ i₁ * (tau π b2 i₁ * (tau π t i₂))))) ?_
    intro t
    ring
  have h3 : ∀ (i₁ b1 b2 : V), (∑' b3, ∑' i₂, (∑' x, tau π 0 x) * ((∑' x, tau π 0 x) * (jointP π b0 b1 i₁ * (jointP π b3 i₂ i₁ * (tau π b2 i₁))))) =
        secondMoment π 0 * ((∑' x, tau π 0 x) * ((∑' x, tau π 0 x) * (jointP π b0 b1 i₁ * (tau π b2 i₁)))) := by
    intro i₁ b1 b2
    refine peel_joint_ears_R π hq (C := (∑' x, tau π 0 x) * ((∑' x, tau π 0 x) * (jointP π b0 b1 i₁ * (tau π b2 i₁)))) (z := i₁)
      (F := fun b3 i₂ => (∑' x, tau π 0 x) * ((∑' x, tau π 0 x) * (jointP π b0 b1 i₁ * (jointP π b3 i₂ i₁ * (tau π b2 i₁))))) ?_
    intro b3 i₂
    ring
  have h4 : ∀ (i₁ b1 : V), (∑' b2, secondMoment π 0 * ((∑' x, tau π 0 x) * ((∑' x, tau π 0 x) * (jointP π b0 b1 i₁ * (tau π b2 i₁))))) =
        (∑' x, tau π 0 x) * (secondMoment π 0 * ((∑' x, tau π 0 x) * ((∑' x, tau π 0 x) * (jointP π b0 b1 i₁)))) := by
    intro i₁ b1
    refine peel_tau_R π hq (C := secondMoment π 0 * ((∑' x, tau π 0 x) * ((∑' x, tau π 0 x) * (jointP π b0 b1 i₁)))) (z := i₁)
      (F := fun b2 => secondMoment π 0 * ((∑' x, tau π 0 x) * ((∑' x, tau π 0 x) * (jointP π b0 b1 i₁ * (tau π b2 i₁))))) ?_
    intro b2
    ring
  have h5 : (∑' i₁, ∑' b1, (∑' x, tau π 0 x) * (secondMoment π 0 * ((∑' x, tau π 0 x) * ((∑' x, tau π 0 x) * (jointP π b0 b1 i₁))))) = monomial2 π 0 := by
    unfold monomial2
    rw [show (∑' i₁, ∑' b1, (∑' x, tau π 0 x) * (secondMoment π 0 * ((∑' x, tau π 0 x) * ((∑' x, tau π 0 x) * (jointP π b0 b1 i₁))))) = secondMoment π 0 * ((∑' x, tau π 0 x) * (secondMoment π 0 * ((∑' x, tau π 0 x) * ((∑' x, tau π 0 x))))) from by
      refine peel_pin_R π hq (C := (∑' x, tau π 0 x) * (secondMoment π 0 * ((∑' x, tau π 0 x) * ((∑' x, tau π 0 x))))) (r := b0)
        (F := fun b1 i₁ => (∑' x, tau π 0 x) * (secondMoment π 0 * ((∑' x, tau π 0 x) * ((∑' x, tau π 0 x) * (jointP π b0 b1 i₁))))) ?_
      intro b1 i₁
      ring]
    ring
  refine (tsum_congr fun i₁ => tsum_congr fun b1 => tsum_congr fun b2 => tsum_congr fun b3 => tsum_congr fun i₂ => tsum_congr fun t => h1 i₁ b1 b2 b3 i₂ t).trans ?_
  refine (tsum_congr fun i₁ => tsum_congr fun b1 => tsum_congr fun b2 => tsum_congr fun b3 => tsum_congr fun i₂ => h2 i₁ b1 b2 b3 i₂).trans ?_
  refine (tsum_congr fun i₁ => tsum_congr fun b1 => tsum_congr fun b2 => h3 i₁ b1 b2).trans ?_
  refine (tsum_congr fun i₁ => tsum_congr fun b1 => h4 i₁ b1).trans ?_
  exact h5

/-- Root socket `b₂` at `j = 4`: `b2` is held and the five other comb terminals and the two interior vertices are summed.  Peel (innermost factor first): tau b4-i₂ over b4; tau t-i₂ over t; ears {b3,i₂} at i₁; ears {b0,b1} at i₁; tau b2-i₁ over i₁. -/
theorem slotV2_four_tsum [Countable V] [AddCommGroup V] (π : Sym2 V → unitInterval)
    (hq : ∀ x y g : V, π s(x + g, y + g) = π s(x, y)) (b2 : V) :
    (∑' i₁, ∑' b0, ∑' b1, ∑' b3, ∑' i₂, ∑' t, ∑' b4, slotProd2 π 4 i₁ i₂ b0 b1 b2 b3 b4 t) =
      monomial2 π 0 := by
  classical
  have h1 : ∀ (i₁ b0 b1 b3 i₂ t : V), (∑' b4, slotProd2 π 4 i₁ i₂ b0 b1 b2 b3 b4 t) =
        (∑' x, tau π 0 x) * (jointP π b0 b1 i₁ * (jointP π b3 i₂ i₁ * (tau π b2 i₁ * (tau π t i₂)))) := by
    intro i₁ b0 b1 b3 i₂ t
    refine peel_tau_R π hq (C := jointP π b0 b1 i₁ * (jointP π b3 i₂ i₁ * (tau π b2 i₁ * (tau π t i₂)))) (z := i₂)
      (F := fun b4 => slotProd2 π 4 i₁ i₂ b0 b1 b2 b3 b4 t) ?_
    intro b4
    change jointP π b0 b1 i₁ * (jointP π b3 i₂ i₁ * (tau π b2 i₁ * (tau π b4 i₂ * (tau π t i₂)))) = tau π b4 i₂ * (jointP π b0 b1 i₁ * (jointP π b3 i₂ i₁ * (tau π b2 i₁ * (tau π t i₂))))
    ring
  have h2 : ∀ (i₁ b0 b1 b3 i₂ : V), (∑' t, (∑' x, tau π 0 x) * (jointP π b0 b1 i₁ * (jointP π b3 i₂ i₁ * (tau π b2 i₁ * (tau π t i₂))))) =
        (∑' x, tau π 0 x) * ((∑' x, tau π 0 x) * (jointP π b0 b1 i₁ * (jointP π b3 i₂ i₁ * (tau π b2 i₁)))) := by
    intro i₁ b0 b1 b3 i₂
    refine peel_tau_R π hq (C := (∑' x, tau π 0 x) * (jointP π b0 b1 i₁ * (jointP π b3 i₂ i₁ * (tau π b2 i₁)))) (z := i₂)
      (F := fun t => (∑' x, tau π 0 x) * (jointP π b0 b1 i₁ * (jointP π b3 i₂ i₁ * (tau π b2 i₁ * (tau π t i₂))))) ?_
    intro t
    ring
  have h3 : ∀ (i₁ b0 b1 : V), (∑' b3, ∑' i₂, (∑' x, tau π 0 x) * ((∑' x, tau π 0 x) * (jointP π b0 b1 i₁ * (jointP π b3 i₂ i₁ * (tau π b2 i₁))))) =
        secondMoment π 0 * ((∑' x, tau π 0 x) * ((∑' x, tau π 0 x) * (jointP π b0 b1 i₁ * (tau π b2 i₁)))) := by
    intro i₁ b0 b1
    refine peel_joint_ears_R π hq (C := (∑' x, tau π 0 x) * ((∑' x, tau π 0 x) * (jointP π b0 b1 i₁ * (tau π b2 i₁)))) (z := i₁)
      (F := fun b3 i₂ => (∑' x, tau π 0 x) * ((∑' x, tau π 0 x) * (jointP π b0 b1 i₁ * (jointP π b3 i₂ i₁ * (tau π b2 i₁))))) ?_
    intro b3 i₂
    ring
  have h4 : ∀ (i₁ : V), (∑' b0, ∑' b1, secondMoment π 0 * ((∑' x, tau π 0 x) * ((∑' x, tau π 0 x) * (jointP π b0 b1 i₁ * (tau π b2 i₁))))) =
        secondMoment π 0 * (secondMoment π 0 * ((∑' x, tau π 0 x) * ((∑' x, tau π 0 x) * (tau π b2 i₁)))) := by
    intro i₁
    refine peel_joint_ears_R π hq (C := secondMoment π 0 * ((∑' x, tau π 0 x) * ((∑' x, tau π 0 x) * (tau π b2 i₁)))) (z := i₁)
      (F := fun b0 b1 => secondMoment π 0 * ((∑' x, tau π 0 x) * ((∑' x, tau π 0 x) * (jointP π b0 b1 i₁ * (tau π b2 i₁))))) ?_
    intro b0 b1
    ring
  have h5 : (∑' i₁, secondMoment π 0 * (secondMoment π 0 * ((∑' x, tau π 0 x) * ((∑' x, tau π 0 x) * (tau π b2 i₁))))) = monomial2 π 0 := by
    unfold monomial2
    rw [show (∑' i₁, secondMoment π 0 * (secondMoment π 0 * ((∑' x, tau π 0 x) * ((∑' x, tau π 0 x) * (tau π b2 i₁))))) = (∑' x, tau π 0 x) * (secondMoment π 0 * (secondMoment π 0 * ((∑' x, tau π 0 x) * ((∑' x, tau π 0 x))))) from by
      refine peel_tau'_R π hq (C := secondMoment π 0 * (secondMoment π 0 * ((∑' x, tau π 0 x) * ((∑' x, tau π 0 x))))) (z := b2)
        (F := fun i₁ => secondMoment π 0 * (secondMoment π 0 * ((∑' x, tau π 0 x) * ((∑' x, tau π 0 x) * (tau π b2 i₁))))) ?_
      intro i₁
      ring]
    ring
  refine (tsum_congr fun i₁ => tsum_congr fun b0 => tsum_congr fun b1 => tsum_congr fun b3 => tsum_congr fun i₂ => tsum_congr fun t => h1 i₁ b0 b1 b3 i₂ t).trans ?_
  refine (tsum_congr fun i₁ => tsum_congr fun b0 => tsum_congr fun b1 => tsum_congr fun b3 => tsum_congr fun i₂ => h2 i₁ b0 b1 b3 i₂).trans ?_
  refine (tsum_congr fun i₁ => tsum_congr fun b0 => tsum_congr fun b1 => h3 i₁ b0 b1).trans ?_
  refine (tsum_congr fun i₁ => h4 i₁).trans ?_
  exact h5

/-- Root socket `b₀` at `j = 5`: `b0` is held and the five other comb terminals and the two interior vertices are summed.  Peel (innermost factor first): tau b3-i₂ over b3; tau b4-i₂ over b4; pin i₁,i₂ about i₁; tau t-i₁ over t; pin b1,i₁ about b0. -/
theorem slotU2_five_tsum [Countable V] [AddCommGroup V] (π : Sym2 V → unitInterval)
    (hq : ∀ x y g : V, π s(x + g, y + g) = π s(x, y)) (b0 : V) :
    (∑' i₁, ∑' b1, ∑' t, ∑' i₂, ∑' b2, ∑' b4, ∑' b3, slotProd2 π 5 i₁ i₂ b0 b1 b2 b3 b4 t) =
      monomial2 π 0 := by
  classical
  have h1 : ∀ (i₁ b1 t i₂ b2 b4 : V), (∑' b3, slotProd2 π 5 i₁ i₂ b0 b1 b2 b3 b4 t) =
        (∑' x, tau π 0 x) * (jointP π b0 b1 i₁ * (jointP π b2 i₁ i₂ * (tau π b4 i₂ * (tau π t i₁)))) := by
    intro i₁ b1 t i₂ b2 b4
    refine peel_tau_R π hq (C := jointP π b0 b1 i₁ * (jointP π b2 i₁ i₂ * (tau π b4 i₂ * (tau π t i₁)))) (z := i₂)
      (F := fun b3 => slotProd2 π 5 i₁ i₂ b0 b1 b2 b3 b4 t) ?_
    intro b3
    change jointP π b0 b1 i₁ * (jointP π b2 i₁ i₂ * (tau π b3 i₂ * (tau π b4 i₂ * (tau π t i₁)))) = tau π b3 i₂ * (jointP π b0 b1 i₁ * (jointP π b2 i₁ i₂ * (tau π b4 i₂ * (tau π t i₁))))
    ring
  have h2 : ∀ (i₁ b1 t i₂ b2 : V), (∑' b4, (∑' x, tau π 0 x) * (jointP π b0 b1 i₁ * (jointP π b2 i₁ i₂ * (tau π b4 i₂ * (tau π t i₁))))) =
        (∑' x, tau π 0 x) * ((∑' x, tau π 0 x) * (jointP π b0 b1 i₁ * (jointP π b2 i₁ i₂ * (tau π t i₁)))) := by
    intro i₁ b1 t i₂ b2
    refine peel_tau_R π hq (C := (∑' x, tau π 0 x) * (jointP π b0 b1 i₁ * (jointP π b2 i₁ i₂ * (tau π t i₁)))) (z := i₂)
      (F := fun b4 => (∑' x, tau π 0 x) * (jointP π b0 b1 i₁ * (jointP π b2 i₁ i₂ * (tau π b4 i₂ * (tau π t i₁))))) ?_
    intro b4
    ring
  have h3 : ∀ (i₁ b1 t : V), (∑' i₂, ∑' b2, (∑' x, tau π 0 x) * ((∑' x, tau π 0 x) * (jointP π b0 b1 i₁ * (jointP π b2 i₁ i₂ * (tau π t i₁))))) =
        secondMoment π 0 * ((∑' x, tau π 0 x) * ((∑' x, tau π 0 x) * (jointP π b0 b1 i₁ * (tau π t i₁)))) := by
    intro i₁ b1 t
    refine peel_pin_R π hq (C := (∑' x, tau π 0 x) * ((∑' x, tau π 0 x) * (jointP π b0 b1 i₁ * (tau π t i₁)))) (r := i₁)
      (F := fun b2 i₂ => (∑' x, tau π 0 x) * ((∑' x, tau π 0 x) * (jointP π b0 b1 i₁ * (jointP π b2 i₁ i₂ * (tau π t i₁))))) ?_
    intro b2 i₂
    rw [jointP_comm π i₁ b2 i₂]; ring
  have h4 : ∀ (i₁ b1 : V), (∑' t, secondMoment π 0 * ((∑' x, tau π 0 x) * ((∑' x, tau π 0 x) * (jointP π b0 b1 i₁ * (tau π t i₁))))) =
        (∑' x, tau π 0 x) * (secondMoment π 0 * ((∑' x, tau π 0 x) * ((∑' x, tau π 0 x) * (jointP π b0 b1 i₁)))) := by
    intro i₁ b1
    refine peel_tau_R π hq (C := secondMoment π 0 * ((∑' x, tau π 0 x) * ((∑' x, tau π 0 x) * (jointP π b0 b1 i₁)))) (z := i₁)
      (F := fun t => secondMoment π 0 * ((∑' x, tau π 0 x) * ((∑' x, tau π 0 x) * (jointP π b0 b1 i₁ * (tau π t i₁))))) ?_
    intro t
    ring
  have h5 : (∑' i₁, ∑' b1, (∑' x, tau π 0 x) * (secondMoment π 0 * ((∑' x, tau π 0 x) * ((∑' x, tau π 0 x) * (jointP π b0 b1 i₁))))) = monomial2 π 0 := by
    unfold monomial2
    rw [show (∑' i₁, ∑' b1, (∑' x, tau π 0 x) * (secondMoment π 0 * ((∑' x, tau π 0 x) * ((∑' x, tau π 0 x) * (jointP π b0 b1 i₁))))) = secondMoment π 0 * ((∑' x, tau π 0 x) * (secondMoment π 0 * ((∑' x, tau π 0 x) * ((∑' x, tau π 0 x))))) from by
      refine peel_pin_R π hq (C := (∑' x, tau π 0 x) * (secondMoment π 0 * ((∑' x, tau π 0 x) * ((∑' x, tau π 0 x))))) (r := b0)
        (F := fun b1 i₁ => (∑' x, tau π 0 x) * (secondMoment π 0 * ((∑' x, tau π 0 x) * ((∑' x, tau π 0 x) * (jointP π b0 b1 i₁))))) ?_
      intro b1 i₁
      ring]
    ring
  refine (tsum_congr fun i₁ => tsum_congr fun b1 => tsum_congr fun t => tsum_congr fun i₂ => tsum_congr fun b2 => tsum_congr fun b4 => h1 i₁ b1 t i₂ b2 b4).trans ?_
  refine (tsum_congr fun i₁ => tsum_congr fun b1 => tsum_congr fun t => tsum_congr fun i₂ => tsum_congr fun b2 => h2 i₁ b1 t i₂ b2).trans ?_
  refine (tsum_congr fun i₁ => tsum_congr fun b1 => tsum_congr fun t => h3 i₁ b1 t).trans ?_
  refine (tsum_congr fun i₁ => tsum_congr fun b1 => h4 i₁ b1).trans ?_
  exact h5

/-- Root socket `b₂` at `j = 5`: `b2` is held and the five other comb terminals and the two interior vertices are summed.  Peel (innermost factor first): tau b3-i₂ over b3; tau b4-i₂ over b4; ears {b0,b1} at i₁; tau t-i₁ over t; pin i₁,i₂ about b2. -/
theorem slotV2_five_tsum [Countable V] [AddCommGroup V] (π : Sym2 V → unitInterval)
    (hq : ∀ x y g : V, π s(x + g, y + g) = π s(x, y)) (b2 : V) :
    (∑' i₂, ∑' i₁, ∑' t, ∑' b0, ∑' b1, ∑' b4, ∑' b3, slotProd2 π 5 i₁ i₂ b0 b1 b2 b3 b4 t) =
      monomial2 π 0 := by
  classical
  have h1 : ∀ (i₂ i₁ t b0 b1 b4 : V), (∑' b3, slotProd2 π 5 i₁ i₂ b0 b1 b2 b3 b4 t) =
        (∑' x, tau π 0 x) * (jointP π b0 b1 i₁ * (jointP π b2 i₁ i₂ * (tau π b4 i₂ * (tau π t i₁)))) := by
    intro i₂ i₁ t b0 b1 b4
    refine peel_tau_R π hq (C := jointP π b0 b1 i₁ * (jointP π b2 i₁ i₂ * (tau π b4 i₂ * (tau π t i₁)))) (z := i₂)
      (F := fun b3 => slotProd2 π 5 i₁ i₂ b0 b1 b2 b3 b4 t) ?_
    intro b3
    change jointP π b0 b1 i₁ * (jointP π b2 i₁ i₂ * (tau π b3 i₂ * (tau π b4 i₂ * (tau π t i₁)))) = tau π b3 i₂ * (jointP π b0 b1 i₁ * (jointP π b2 i₁ i₂ * (tau π b4 i₂ * (tau π t i₁))))
    ring
  have h2 : ∀ (i₂ i₁ t b0 b1 : V), (∑' b4, (∑' x, tau π 0 x) * (jointP π b0 b1 i₁ * (jointP π b2 i₁ i₂ * (tau π b4 i₂ * (tau π t i₁))))) =
        (∑' x, tau π 0 x) * ((∑' x, tau π 0 x) * (jointP π b0 b1 i₁ * (jointP π b2 i₁ i₂ * (tau π t i₁)))) := by
    intro i₂ i₁ t b0 b1
    refine peel_tau_R π hq (C := (∑' x, tau π 0 x) * (jointP π b0 b1 i₁ * (jointP π b2 i₁ i₂ * (tau π t i₁)))) (z := i₂)
      (F := fun b4 => (∑' x, tau π 0 x) * (jointP π b0 b1 i₁ * (jointP π b2 i₁ i₂ * (tau π b4 i₂ * (tau π t i₁))))) ?_
    intro b4
    ring
  have h3 : ∀ (i₂ i₁ t : V), (∑' b0, ∑' b1, (∑' x, tau π 0 x) * ((∑' x, tau π 0 x) * (jointP π b0 b1 i₁ * (jointP π b2 i₁ i₂ * (tau π t i₁))))) =
        secondMoment π 0 * ((∑' x, tau π 0 x) * ((∑' x, tau π 0 x) * (jointP π b2 i₁ i₂ * (tau π t i₁)))) := by
    intro i₂ i₁ t
    refine peel_joint_ears_R π hq (C := (∑' x, tau π 0 x) * ((∑' x, tau π 0 x) * (jointP π b2 i₁ i₂ * (tau π t i₁)))) (z := i₁)
      (F := fun b0 b1 => (∑' x, tau π 0 x) * ((∑' x, tau π 0 x) * (jointP π b0 b1 i₁ * (jointP π b2 i₁ i₂ * (tau π t i₁))))) ?_
    intro b0 b1
    ring
  have h4 : ∀ (i₂ i₁ : V), (∑' t, secondMoment π 0 * ((∑' x, tau π 0 x) * ((∑' x, tau π 0 x) * (jointP π b2 i₁ i₂ * (tau π t i₁))))) =
        (∑' x, tau π 0 x) * (secondMoment π 0 * ((∑' x, tau π 0 x) * ((∑' x, tau π 0 x) * (jointP π b2 i₁ i₂)))) := by
    intro i₂ i₁
    refine peel_tau_R π hq (C := secondMoment π 0 * ((∑' x, tau π 0 x) * ((∑' x, tau π 0 x) * (jointP π b2 i₁ i₂)))) (z := i₁)
      (F := fun t => secondMoment π 0 * ((∑' x, tau π 0 x) * ((∑' x, tau π 0 x) * (jointP π b2 i₁ i₂ * (tau π t i₁))))) ?_
    intro t
    ring
  have h5 : (∑' i₂, ∑' i₁, (∑' x, tau π 0 x) * (secondMoment π 0 * ((∑' x, tau π 0 x) * ((∑' x, tau π 0 x) * (jointP π b2 i₁ i₂))))) = monomial2 π 0 := by
    unfold monomial2
    rw [show (∑' i₂, ∑' i₁, (∑' x, tau π 0 x) * (secondMoment π 0 * ((∑' x, tau π 0 x) * ((∑' x, tau π 0 x) * (jointP π b2 i₁ i₂))))) = secondMoment π 0 * ((∑' x, tau π 0 x) * (secondMoment π 0 * ((∑' x, tau π 0 x) * ((∑' x, tau π 0 x))))) from by
      refine peel_pin_R π hq (C := (∑' x, tau π 0 x) * (secondMoment π 0 * ((∑' x, tau π 0 x) * ((∑' x, tau π 0 x))))) (r := b2)
        (F := fun i₁ i₂ => (∑' x, tau π 0 x) * (secondMoment π 0 * ((∑' x, tau π 0 x) * ((∑' x, tau π 0 x) * (jointP π b2 i₁ i₂))))) ?_
      intro i₁ i₂
      ring]
    ring
  refine (tsum_congr fun i₂ => tsum_congr fun i₁ => tsum_congr fun t => tsum_congr fun b0 => tsum_congr fun b1 => tsum_congr fun b4 => h1 i₂ i₁ t b0 b1 b4).trans ?_
  refine (tsum_congr fun i₂ => tsum_congr fun i₁ => tsum_congr fun t => tsum_congr fun b0 => tsum_congr fun b1 => h2 i₂ i₁ t b0 b1).trans ?_
  refine (tsum_congr fun i₂ => tsum_congr fun i₁ => tsum_congr fun t => h3 i₂ i₁ t).trans ?_
  refine (tsum_congr fun i₂ => tsum_congr fun i₁ => h4 i₂ i₁).trans ?_
  exact h5

/-- Root socket `b₀` at `j = 6`: `b0` is held and the five other comb terminals and the two interior vertices are summed.  Peel (innermost factor first): tau b3-i₂ over b3; tau b4-i₂ over b4; pin t,i₂ about i₁; tau b2-i₁ over b2; pin b1,i₁ about b0. -/
theorem slotU2_six_tsum [Countable V] [AddCommGroup V] (π : Sym2 V → unitInterval)
    (hq : ∀ x y g : V, π s(x + g, y + g) = π s(x, y)) (b0 : V) :
    (∑' i₁, ∑' b1, ∑' b2, ∑' i₂, ∑' t, ∑' b4, ∑' b3, slotProd2 π 6 i₁ i₂ b0 b1 b2 b3 b4 t) =
      monomial2 π 0 := by
  classical
  have h1 : ∀ (i₁ b1 b2 i₂ t b4 : V), (∑' b3, slotProd2 π 6 i₁ i₂ b0 b1 b2 b3 b4 t) =
        (∑' x, tau π 0 x) * (jointP π b0 b1 i₁ * (jointP π i₁ t i₂ * (tau π b2 i₁ * (tau π b4 i₂)))) := by
    intro i₁ b1 b2 i₂ t b4
    refine peel_tau_R π hq (C := jointP π b0 b1 i₁ * (jointP π i₁ t i₂ * (tau π b2 i₁ * (tau π b4 i₂)))) (z := i₂)
      (F := fun b3 => slotProd2 π 6 i₁ i₂ b0 b1 b2 b3 b4 t) ?_
    intro b3
    change jointP π b0 b1 i₁ * (jointP π i₁ t i₂ * (tau π b2 i₁ * (tau π b3 i₂ * (tau π b4 i₂)))) = tau π b3 i₂ * (jointP π b0 b1 i₁ * (jointP π i₁ t i₂ * (tau π b2 i₁ * (tau π b4 i₂))))
    ring
  have h2 : ∀ (i₁ b1 b2 i₂ t : V), (∑' b4, (∑' x, tau π 0 x) * (jointP π b0 b1 i₁ * (jointP π i₁ t i₂ * (tau π b2 i₁ * (tau π b4 i₂))))) =
        (∑' x, tau π 0 x) * ((∑' x, tau π 0 x) * (jointP π b0 b1 i₁ * (jointP π i₁ t i₂ * (tau π b2 i₁)))) := by
    intro i₁ b1 b2 i₂ t
    refine peel_tau_R π hq (C := (∑' x, tau π 0 x) * (jointP π b0 b1 i₁ * (jointP π i₁ t i₂ * (tau π b2 i₁)))) (z := i₂)
      (F := fun b4 => (∑' x, tau π 0 x) * (jointP π b0 b1 i₁ * (jointP π i₁ t i₂ * (tau π b2 i₁ * (tau π b4 i₂))))) ?_
    intro b4
    ring
  have h3 : ∀ (i₁ b1 b2 : V), (∑' i₂, ∑' t, (∑' x, tau π 0 x) * ((∑' x, tau π 0 x) * (jointP π b0 b1 i₁ * (jointP π i₁ t i₂ * (tau π b2 i₁))))) =
        secondMoment π 0 * ((∑' x, tau π 0 x) * ((∑' x, tau π 0 x) * (jointP π b0 b1 i₁ * (tau π b2 i₁)))) := by
    intro i₁ b1 b2
    refine peel_pin_R π hq (C := (∑' x, tau π 0 x) * ((∑' x, tau π 0 x) * (jointP π b0 b1 i₁ * (tau π b2 i₁)))) (r := i₁)
      (F := fun t i₂ => (∑' x, tau π 0 x) * ((∑' x, tau π 0 x) * (jointP π b0 b1 i₁ * (jointP π i₁ t i₂ * (tau π b2 i₁))))) ?_
    intro t i₂
    ring
  have h4 : ∀ (i₁ b1 : V), (∑' b2, secondMoment π 0 * ((∑' x, tau π 0 x) * ((∑' x, tau π 0 x) * (jointP π b0 b1 i₁ * (tau π b2 i₁))))) =
        (∑' x, tau π 0 x) * (secondMoment π 0 * ((∑' x, tau π 0 x) * ((∑' x, tau π 0 x) * (jointP π b0 b1 i₁)))) := by
    intro i₁ b1
    refine peel_tau_R π hq (C := secondMoment π 0 * ((∑' x, tau π 0 x) * ((∑' x, tau π 0 x) * (jointP π b0 b1 i₁)))) (z := i₁)
      (F := fun b2 => secondMoment π 0 * ((∑' x, tau π 0 x) * ((∑' x, tau π 0 x) * (jointP π b0 b1 i₁ * (tau π b2 i₁))))) ?_
    intro b2
    ring
  have h5 : (∑' i₁, ∑' b1, (∑' x, tau π 0 x) * (secondMoment π 0 * ((∑' x, tau π 0 x) * ((∑' x, tau π 0 x) * (jointP π b0 b1 i₁))))) = monomial2 π 0 := by
    unfold monomial2
    rw [show (∑' i₁, ∑' b1, (∑' x, tau π 0 x) * (secondMoment π 0 * ((∑' x, tau π 0 x) * ((∑' x, tau π 0 x) * (jointP π b0 b1 i₁))))) = secondMoment π 0 * ((∑' x, tau π 0 x) * (secondMoment π 0 * ((∑' x, tau π 0 x) * ((∑' x, tau π 0 x))))) from by
      refine peel_pin_R π hq (C := (∑' x, tau π 0 x) * (secondMoment π 0 * ((∑' x, tau π 0 x) * ((∑' x, tau π 0 x))))) (r := b0)
        (F := fun b1 i₁ => (∑' x, tau π 0 x) * (secondMoment π 0 * ((∑' x, tau π 0 x) * ((∑' x, tau π 0 x) * (jointP π b0 b1 i₁))))) ?_
      intro b1 i₁
      ring]
    ring
  refine (tsum_congr fun i₁ => tsum_congr fun b1 => tsum_congr fun b2 => tsum_congr fun i₂ => tsum_congr fun t => tsum_congr fun b4 => h1 i₁ b1 b2 i₂ t b4).trans ?_
  refine (tsum_congr fun i₁ => tsum_congr fun b1 => tsum_congr fun b2 => tsum_congr fun i₂ => tsum_congr fun t => h2 i₁ b1 b2 i₂ t).trans ?_
  refine (tsum_congr fun i₁ => tsum_congr fun b1 => tsum_congr fun b2 => h3 i₁ b1 b2).trans ?_
  refine (tsum_congr fun i₁ => tsum_congr fun b1 => h4 i₁ b1).trans ?_
  exact h5

/-- Root socket `b₂` at `j = 6`: `b2` is held and the five other comb terminals and the two interior vertices are summed.  Peel (innermost factor first): tau b3-i₂ over b3; tau b4-i₂ over b4; pin t,i₂ about i₁; ears {b0,b1} at i₁; tau b2-i₁ over i₁. -/
theorem slotV2_six_tsum [Countable V] [AddCommGroup V] (π : Sym2 V → unitInterval)
    (hq : ∀ x y g : V, π s(x + g, y + g) = π s(x, y)) (b2 : V) :
    (∑' i₁, ∑' b0, ∑' b1, ∑' i₂, ∑' t, ∑' b4, ∑' b3, slotProd2 π 6 i₁ i₂ b0 b1 b2 b3 b4 t) =
      monomial2 π 0 := by
  classical
  have h1 : ∀ (i₁ b0 b1 i₂ t b4 : V), (∑' b3, slotProd2 π 6 i₁ i₂ b0 b1 b2 b3 b4 t) =
        (∑' x, tau π 0 x) * (jointP π b0 b1 i₁ * (jointP π i₁ t i₂ * (tau π b2 i₁ * (tau π b4 i₂)))) := by
    intro i₁ b0 b1 i₂ t b4
    refine peel_tau_R π hq (C := jointP π b0 b1 i₁ * (jointP π i₁ t i₂ * (tau π b2 i₁ * (tau π b4 i₂)))) (z := i₂)
      (F := fun b3 => slotProd2 π 6 i₁ i₂ b0 b1 b2 b3 b4 t) ?_
    intro b3
    change jointP π b0 b1 i₁ * (jointP π i₁ t i₂ * (tau π b2 i₁ * (tau π b3 i₂ * (tau π b4 i₂)))) = tau π b3 i₂ * (jointP π b0 b1 i₁ * (jointP π i₁ t i₂ * (tau π b2 i₁ * (tau π b4 i₂))))
    ring
  have h2 : ∀ (i₁ b0 b1 i₂ t : V), (∑' b4, (∑' x, tau π 0 x) * (jointP π b0 b1 i₁ * (jointP π i₁ t i₂ * (tau π b2 i₁ * (tau π b4 i₂))))) =
        (∑' x, tau π 0 x) * ((∑' x, tau π 0 x) * (jointP π b0 b1 i₁ * (jointP π i₁ t i₂ * (tau π b2 i₁)))) := by
    intro i₁ b0 b1 i₂ t
    refine peel_tau_R π hq (C := (∑' x, tau π 0 x) * (jointP π b0 b1 i₁ * (jointP π i₁ t i₂ * (tau π b2 i₁)))) (z := i₂)
      (F := fun b4 => (∑' x, tau π 0 x) * (jointP π b0 b1 i₁ * (jointP π i₁ t i₂ * (tau π b2 i₁ * (tau π b4 i₂))))) ?_
    intro b4
    ring
  have h3 : ∀ (i₁ b0 b1 : V), (∑' i₂, ∑' t, (∑' x, tau π 0 x) * ((∑' x, tau π 0 x) * (jointP π b0 b1 i₁ * (jointP π i₁ t i₂ * (tau π b2 i₁))))) =
        secondMoment π 0 * ((∑' x, tau π 0 x) * ((∑' x, tau π 0 x) * (jointP π b0 b1 i₁ * (tau π b2 i₁)))) := by
    intro i₁ b0 b1
    refine peel_pin_R π hq (C := (∑' x, tau π 0 x) * ((∑' x, tau π 0 x) * (jointP π b0 b1 i₁ * (tau π b2 i₁)))) (r := i₁)
      (F := fun t i₂ => (∑' x, tau π 0 x) * ((∑' x, tau π 0 x) * (jointP π b0 b1 i₁ * (jointP π i₁ t i₂ * (tau π b2 i₁))))) ?_
    intro t i₂
    ring
  have h4 : ∀ (i₁ : V), (∑' b0, ∑' b1, secondMoment π 0 * ((∑' x, tau π 0 x) * ((∑' x, tau π 0 x) * (jointP π b0 b1 i₁ * (tau π b2 i₁))))) =
        secondMoment π 0 * (secondMoment π 0 * ((∑' x, tau π 0 x) * ((∑' x, tau π 0 x) * (tau π b2 i₁)))) := by
    intro i₁
    refine peel_joint_ears_R π hq (C := secondMoment π 0 * ((∑' x, tau π 0 x) * ((∑' x, tau π 0 x) * (tau π b2 i₁)))) (z := i₁)
      (F := fun b0 b1 => secondMoment π 0 * ((∑' x, tau π 0 x) * ((∑' x, tau π 0 x) * (jointP π b0 b1 i₁ * (tau π b2 i₁))))) ?_
    intro b0 b1
    ring
  have h5 : (∑' i₁, secondMoment π 0 * (secondMoment π 0 * ((∑' x, tau π 0 x) * ((∑' x, tau π 0 x) * (tau π b2 i₁))))) = monomial2 π 0 := by
    unfold monomial2
    rw [show (∑' i₁, secondMoment π 0 * (secondMoment π 0 * ((∑' x, tau π 0 x) * ((∑' x, tau π 0 x) * (tau π b2 i₁))))) = (∑' x, tau π 0 x) * (secondMoment π 0 * (secondMoment π 0 * ((∑' x, tau π 0 x) * ((∑' x, tau π 0 x))))) from by
      refine peel_tau'_R π hq (C := secondMoment π 0 * (secondMoment π 0 * ((∑' x, tau π 0 x) * ((∑' x, tau π 0 x))))) (z := b2)
        (F := fun i₁ => secondMoment π 0 * (secondMoment π 0 * ((∑' x, tau π 0 x) * ((∑' x, tau π 0 x) * (tau π b2 i₁))))) ?_
      intro i₁
      ring]
    ring
  refine (tsum_congr fun i₁ => tsum_congr fun b0 => tsum_congr fun b1 => tsum_congr fun i₂ => tsum_congr fun t => tsum_congr fun b4 => h1 i₁ b0 b1 i₂ t b4).trans ?_
  refine (tsum_congr fun i₁ => tsum_congr fun b0 => tsum_congr fun b1 => tsum_congr fun i₂ => tsum_congr fun t => h2 i₁ b0 b1 i₂ t).trans ?_
  refine (tsum_congr fun i₁ => tsum_congr fun b0 => tsum_congr fun b1 => h3 i₁ b0 b1).trans ?_
  refine (tsum_congr fun i₁ => h4 i₁).trans ?_
  exact h5

/-- Root socket `b₀` at `j = 2`: `b0` is held and the five other comb terminals and the two interior vertices are summed.  Peel (innermost factor first): tau b2-i₂ over b2; tau t-i₂ over t; ears {b3,b4} at i₁; tau i₁-i₂ over i₂; pin b1,i₁ about b0. -/
theorem slotU2_two_tsum [Countable V] [AddCommGroup V] (π : Sym2 V → unitInterval)
    (hq : ∀ x y g : V, π s(x + g, y + g) = π s(x, y)) (b0 : V) :
    (∑' i₁, ∑' b1, ∑' i₂, ∑' b3, ∑' b4, ∑' t, ∑' b2, slotProd2 π 2 i₁ i₂ b0 b1 b2 b3 b4 t) =
      monomial2 π 0 := by
  classical
  have h1 : ∀ (i₁ b1 i₂ b3 b4 t : V), (∑' b2, slotProd2 π 2 i₁ i₂ b0 b1 b2 b3 b4 t) =
        (∑' x, tau π 0 x) * (jointP π b0 b1 i₁ * (jointP π b3 b4 i₁ * (tau π i₁ i₂ * (tau π t i₂)))) := by
    intro i₁ b1 i₂ b3 b4 t
    refine peel_tau_R π hq (C := jointP π b0 b1 i₁ * (jointP π b3 b4 i₁ * (tau π i₁ i₂ * (tau π t i₂)))) (z := i₂)
      (F := fun b2 => slotProd2 π 2 i₁ i₂ b0 b1 b2 b3 b4 t) ?_
    intro b2
    change jointP π b0 b1 i₁ * (jointP π b3 b4 i₁ * (tau π b2 i₂ * (tau π i₁ i₂ * (tau π t i₂)))) = tau π b2 i₂ * (jointP π b0 b1 i₁ * (jointP π b3 b4 i₁ * (tau π i₁ i₂ * (tau π t i₂))))
    ring
  have h2 : ∀ (i₁ b1 i₂ b3 b4 : V), (∑' t, (∑' x, tau π 0 x) * (jointP π b0 b1 i₁ * (jointP π b3 b4 i₁ * (tau π i₁ i₂ * (tau π t i₂))))) =
        (∑' x, tau π 0 x) * ((∑' x, tau π 0 x) * (jointP π b0 b1 i₁ * (jointP π b3 b4 i₁ * (tau π i₁ i₂)))) := by
    intro i₁ b1 i₂ b3 b4
    refine peel_tau_R π hq (C := (∑' x, tau π 0 x) * (jointP π b0 b1 i₁ * (jointP π b3 b4 i₁ * (tau π i₁ i₂)))) (z := i₂)
      (F := fun t => (∑' x, tau π 0 x) * (jointP π b0 b1 i₁ * (jointP π b3 b4 i₁ * (tau π i₁ i₂ * (tau π t i₂))))) ?_
    intro t
    ring
  have h3 : ∀ (i₁ b1 i₂ : V), (∑' b3, ∑' b4, (∑' x, tau π 0 x) * ((∑' x, tau π 0 x) * (jointP π b0 b1 i₁ * (jointP π b3 b4 i₁ * (tau π i₁ i₂))))) =
        secondMoment π 0 * ((∑' x, tau π 0 x) * ((∑' x, tau π 0 x) * (jointP π b0 b1 i₁ * (tau π i₁ i₂)))) := by
    intro i₁ b1 i₂
    refine peel_joint_ears_R π hq (C := (∑' x, tau π 0 x) * ((∑' x, tau π 0 x) * (jointP π b0 b1 i₁ * (tau π i₁ i₂)))) (z := i₁)
      (F := fun b3 b4 => (∑' x, tau π 0 x) * ((∑' x, tau π 0 x) * (jointP π b0 b1 i₁ * (jointP π b3 b4 i₁ * (tau π i₁ i₂))))) ?_
    intro b3 b4
    ring
  have h4 : ∀ (i₁ b1 : V), (∑' i₂, secondMoment π 0 * ((∑' x, tau π 0 x) * ((∑' x, tau π 0 x) * (jointP π b0 b1 i₁ * (tau π i₁ i₂))))) =
        (∑' x, tau π 0 x) * (secondMoment π 0 * ((∑' x, tau π 0 x) * ((∑' x, tau π 0 x) * (jointP π b0 b1 i₁)))) := by
    intro i₁ b1
    refine peel_tau'_R π hq (C := secondMoment π 0 * ((∑' x, tau π 0 x) * ((∑' x, tau π 0 x) * (jointP π b0 b1 i₁)))) (z := i₁)
      (F := fun i₂ => secondMoment π 0 * ((∑' x, tau π 0 x) * ((∑' x, tau π 0 x) * (jointP π b0 b1 i₁ * (tau π i₁ i₂))))) ?_
    intro i₂
    ring
  have h5 : (∑' i₁, ∑' b1, (∑' x, tau π 0 x) * (secondMoment π 0 * ((∑' x, tau π 0 x) * ((∑' x, tau π 0 x) * (jointP π b0 b1 i₁))))) = monomial2 π 0 := by
    unfold monomial2
    rw [show (∑' i₁, ∑' b1, (∑' x, tau π 0 x) * (secondMoment π 0 * ((∑' x, tau π 0 x) * ((∑' x, tau π 0 x) * (jointP π b0 b1 i₁))))) = secondMoment π 0 * ((∑' x, tau π 0 x) * (secondMoment π 0 * ((∑' x, tau π 0 x) * ((∑' x, tau π 0 x))))) from by
      refine peel_pin_R π hq (C := (∑' x, tau π 0 x) * (secondMoment π 0 * ((∑' x, tau π 0 x) * ((∑' x, tau π 0 x))))) (r := b0)
        (F := fun b1 i₁ => (∑' x, tau π 0 x) * (secondMoment π 0 * ((∑' x, tau π 0 x) * ((∑' x, tau π 0 x) * (jointP π b0 b1 i₁))))) ?_
      intro b1 i₁
      ring]
    ring
  refine (tsum_congr fun i₁ => tsum_congr fun b1 => tsum_congr fun i₂ => tsum_congr fun b3 => tsum_congr fun b4 => tsum_congr fun t => h1 i₁ b1 i₂ b3 b4 t).trans ?_
  refine (tsum_congr fun i₁ => tsum_congr fun b1 => tsum_congr fun i₂ => tsum_congr fun b3 => tsum_congr fun b4 => h2 i₁ b1 i₂ b3 b4).trans ?_
  refine (tsum_congr fun i₁ => tsum_congr fun b1 => tsum_congr fun i₂ => h3 i₁ b1 i₂).trans ?_
  refine (tsum_congr fun i₁ => tsum_congr fun b1 => h4 i₁ b1).trans ?_
  exact h5

/-- Root socket `b₂` at `j = 2`: `b2` is held and the five other comb terminals and the two interior vertices are summed.  Peel (innermost factor first): tau t-i₂ over t; ears {b3,b4} at i₁; ears {b0,b1} at i₁; tau i₁-i₂ over i₁; tau b2-i₂ over i₂. -/
theorem slotV2_two_tsum [Countable V] [AddCommGroup V] (π : Sym2 V → unitInterval)
    (hq : ∀ x y g : V, π s(x + g, y + g) = π s(x, y)) (b2 : V) :
    (∑' i₂, ∑' i₁, ∑' b0, ∑' b1, ∑' b3, ∑' b4, ∑' t, slotProd2 π 2 i₁ i₂ b0 b1 b2 b3 b4 t) =
      monomial2 π 0 := by
  classical
  have h1 : ∀ (i₂ i₁ b0 b1 b3 b4 : V), (∑' t, slotProd2 π 2 i₁ i₂ b0 b1 b2 b3 b4 t) =
        (∑' x, tau π 0 x) * (jointP π b0 b1 i₁ * (jointP π b3 b4 i₁ * (tau π b2 i₂ * (tau π i₁ i₂)))) := by
    intro i₂ i₁ b0 b1 b3 b4
    refine peel_tau_R π hq (C := jointP π b0 b1 i₁ * (jointP π b3 b4 i₁ * (tau π b2 i₂ * (tau π i₁ i₂)))) (z := i₂)
      (F := fun t => slotProd2 π 2 i₁ i₂ b0 b1 b2 b3 b4 t) ?_
    intro t
    change jointP π b0 b1 i₁ * (jointP π b3 b4 i₁ * (tau π b2 i₂ * (tau π i₁ i₂ * (tau π t i₂)))) = tau π t i₂ * (jointP π b0 b1 i₁ * (jointP π b3 b4 i₁ * (tau π b2 i₂ * (tau π i₁ i₂))))
    ring
  have h2 : ∀ (i₂ i₁ b0 b1 : V), (∑' b3, ∑' b4, (∑' x, tau π 0 x) * (jointP π b0 b1 i₁ * (jointP π b3 b4 i₁ * (tau π b2 i₂ * (tau π i₁ i₂))))) =
        secondMoment π 0 * ((∑' x, tau π 0 x) * (jointP π b0 b1 i₁ * (tau π b2 i₂ * (tau π i₁ i₂)))) := by
    intro i₂ i₁ b0 b1
    refine peel_joint_ears_R π hq (C := (∑' x, tau π 0 x) * (jointP π b0 b1 i₁ * (tau π b2 i₂ * (tau π i₁ i₂)))) (z := i₁)
      (F := fun b3 b4 => (∑' x, tau π 0 x) * (jointP π b0 b1 i₁ * (jointP π b3 b4 i₁ * (tau π b2 i₂ * (tau π i₁ i₂))))) ?_
    intro b3 b4
    ring
  have h3 : ∀ (i₂ i₁ : V), (∑' b0, ∑' b1, secondMoment π 0 * ((∑' x, tau π 0 x) * (jointP π b0 b1 i₁ * (tau π b2 i₂ * (tau π i₁ i₂))))) =
        secondMoment π 0 * (secondMoment π 0 * ((∑' x, tau π 0 x) * (tau π b2 i₂ * (tau π i₁ i₂)))) := by
    intro i₂ i₁
    refine peel_joint_ears_R π hq (C := secondMoment π 0 * ((∑' x, tau π 0 x) * (tau π b2 i₂ * (tau π i₁ i₂)))) (z := i₁)
      (F := fun b0 b1 => secondMoment π 0 * ((∑' x, tau π 0 x) * (jointP π b0 b1 i₁ * (tau π b2 i₂ * (tau π i₁ i₂))))) ?_
    intro b0 b1
    ring
  have h4 : ∀ (i₂ : V), (∑' i₁, secondMoment π 0 * (secondMoment π 0 * ((∑' x, tau π 0 x) * (tau π b2 i₂ * (tau π i₁ i₂))))) =
        (∑' x, tau π 0 x) * (secondMoment π 0 * (secondMoment π 0 * ((∑' x, tau π 0 x) * (tau π b2 i₂)))) := by
    intro i₂
    refine peel_tau_R π hq (C := secondMoment π 0 * (secondMoment π 0 * ((∑' x, tau π 0 x) * (tau π b2 i₂)))) (z := i₂)
      (F := fun i₁ => secondMoment π 0 * (secondMoment π 0 * ((∑' x, tau π 0 x) * (tau π b2 i₂ * (tau π i₁ i₂))))) ?_
    intro i₁
    ring
  have h5 : (∑' i₂, (∑' x, tau π 0 x) * (secondMoment π 0 * (secondMoment π 0 * ((∑' x, tau π 0 x) * (tau π b2 i₂))))) = monomial2 π 0 := by
    unfold monomial2
    rw [show (∑' i₂, (∑' x, tau π 0 x) * (secondMoment π 0 * (secondMoment π 0 * ((∑' x, tau π 0 x) * (tau π b2 i₂))))) = (∑' x, tau π 0 x) * ((∑' x, tau π 0 x) * (secondMoment π 0 * (secondMoment π 0 * ((∑' x, tau π 0 x))))) from by
      refine peel_tau'_R π hq (C := (∑' x, tau π 0 x) * (secondMoment π 0 * (secondMoment π 0 * ((∑' x, tau π 0 x))))) (z := b2)
        (F := fun i₂ => (∑' x, tau π 0 x) * (secondMoment π 0 * (secondMoment π 0 * ((∑' x, tau π 0 x) * (tau π b2 i₂))))) ?_
      intro i₂
      ring]
    ring
  refine (tsum_congr fun i₂ => tsum_congr fun i₁ => tsum_congr fun b0 => tsum_congr fun b1 => tsum_congr fun b3 => tsum_congr fun b4 => h1 i₂ i₁ b0 b1 b3 b4).trans ?_
  refine (tsum_congr fun i₂ => tsum_congr fun i₁ => tsum_congr fun b0 => tsum_congr fun b1 => h2 i₂ i₁ b0 b1).trans ?_
  refine (tsum_congr fun i₂ => tsum_congr fun i₁ => h3 i₂ i₁).trans ?_
  refine (tsum_congr fun i₂ => h4 i₂).trans ?_
  exact h5

end PercLib.CriticalLRP.SixPoint.SplitEval2.RootSocket
