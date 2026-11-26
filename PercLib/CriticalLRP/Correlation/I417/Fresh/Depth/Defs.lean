/-
Independently rebuilt from accepted `smwxb4a1l/m2` coefficient artifacts.
Production revision `d9a001b7f0a33cf6395158f7621ad4de1fe3c7c8`.
Only the finite range/cardinality results are integrated; this does not prove
the arbitrary-q weighted fresh evaluation or the further geometric link lemmas
outlined in the artifact narrative.
-/
/-
Independently built for swarm `smwxb4a1l`, member `m2`, direction
`GENERAL-Q-STRUCTURAL-GAP-AUDIT`.  Nothing here is committed to the production tree: the
files live under `.ultramath/smwxb4a1l/m2/` only, and
`repo/.scratch/critical-lrp-orchestration` at HEAD `d9a001b7` is read-only.
-/
module

public import PercLib.CriticalLRP.Correlation.I417.Fresh.Iter.Bound
public import PercLib.CriticalLRP.Correlation.I417.Fresh.Subdivision.Poly

/-!
# The pin--mark path length and its coefficient cardinalities, for the iterated
first-hit fresh cover at arbitrary `q`

Source: T. Hutchcroft, *Critical long-range percolation I: High effective dimension*,
arXiv:2508.18807v1, Lemma I.4.17 and its proof (supplied text pp. 43--46, lines 2444--2513):

> "We obtain a bound in terms of tree diagrams with two pinned vertices at `x` and `y`, with
> `2p + 2q + 1` edges in total, some number `3 ≤ ℓ ≤ p + q + 1` of them belong to the path
> connecting `x` and `y`."

Production's arbitrary-`q` cover (`I417GenIter.genShape`, `Correlation/I417/Fresh/Iter/Defs.lean`)
indexes the fresh side by an attachment history `H : Hist V (q - 1)`; the legs are produced by
`Hist.legs`, i.e. by iterating `splitAt` (`Correlation/I417/Fresh/Four/Refined/Defs.lean`).  The
fresh-side normal form of Lemma I.4.17,

  `∑_{ℓ∈[1,q]} C_ℓ · χ^(2q-ℓ) · T^ℓ(w,y)`,

needs two things that production's iterated cover does not yet provide:

* a **depth `ℓ` attached to the actual cover members**, i.e. the number of legs of the `2q`-leg
  diagram that lie on the pin--mark path `y → w`, so that `2q - ℓ` is the number of remaining
  (fully summed) legs;
* the **coefficients `C_ℓ`** as an explicit finite cardinal, namely the number of split-choice
  tuples of the cover whose pin--mark path has length `ℓ`.

This file defines exactly those two objects, in the leg model (no `RTree`):

* `splitChoices H : (t : Fin n) → Idx t` — the split leg chosen in each attachment round.
  It depends only on the *branch* of the cover, not on the attachment vertices, which is why the
  coefficient below is a cardinal of a finite type.
* `pathLegsK n k : Finset (Idx n)` — the legs on the pin--mark path, propagated through the
  split rule `leg k ↦ {leg k, new leg}` of `splitAt` (splitting a path leg lengthens the path by
  one leg, splitting an off-path leg leaves it unchanged).
* `markDepthK n k = (pathLegsK n k).card` — the number of legs on the path, i.e. the `ℓ` of the
  fresh normal form.  `markDepth H` is its value on a history.
* `wSlotK n k : Idx n` — the slot whose intended target is `w`. The subsequent
  geometric endpoint/linking statements are explicitly not proved in this package.
* `genCoeff q ℓ = depthCount (q - 1) ℓ = #{k : (t : Fin (q-1)) → Idx t // markDepthK = ℓ}` — the
  explicit cardinality `C_ℓ` of the printed normal form.  It is finite (`card_histChoices`), it
  depends only on the split choices, and `QDeep/Main.lean` evaluates it as
  `(1,1)`, `(3,3,2)`, `(15,15,12,6)`, `(105,105,90,60,24)` for `q = 2,3,4,5`; the `q = 4` row is
  exactly the coefficient list `15,15,12,6` of production's accepted
  `I417FreshFour.Eval.freshFourProfile` (i.e. `6 χ⁴T⁴ + 12 χ⁵T³ + 15 χ⁶T² + 15 χ⁷T`), and the
  `q = 5` row is exactly `24, 60, 90, 105, 105`.
* `genFreshProfile k χ q y w` — the resulting coefficient-weighted fresh polynomial with these
  defined coefficients, in production's `I417Fresh.Subdivision.freshPoly` normalisation.

Everything here is definitions plus docstrings; `QDeep/Main.lean` carries the proofs.
-/

open MeasureTheory Measure ProbabilityTheory unitInterval
open scoped ENNReal NNReal

set_option linter.unusedSectionVars false
set_option linter.style.longLine false

@[expose] public section

namespace PercLib.CriticalLRP.I417FreshDepth

open PercLib.CriticalLRP
open PercLib.CriticalLRP.I417GenIter

variable {V : Type*} [Countable V] [DecidableEq V]

/-- `Idx n` carries a genuine (computable) decidable equality, so that the branch counts below are
computable and can be evaluated by kernel reduction (`decide`). -/
instance instDecidableEqIdx (n : ℕ) : DecidableEq (Idx n) := by
  induction n with
  | zero => exact inferInstanceAs (DecidableEq (Fin 2))
  | succ n ih => exact inferInstanceAs (DecidableEq (Idx n ⊕ Bool))

/-- The base slot of the two-leg diagram, as an element of `Idx 0 = Fin 2`: the leg `(y,w)`, which
is the first leg of the pin--mark path. -/
def idxZero : Idx 0 := (0 : Fin 2)

/-! ## The branch of a history, and the legs of the pin--mark path -/

/-- **The split choices of an attachment history.**  `splitChoices H : (t : Fin n) → Idx t`
records, for each of the `n` attachment rounds, the leg that was split.  The attachment vertices
and the attached arms are *forgotten*: the pin--mark path length below depends only on these legs,
which is what makes the fresh-side coefficients `C_ℓ` finite cardinals (`card_histChoices`). -/
def splitChoices : {n : ℕ} → Hist V n → ((t : Fin n) → Idx t)
  | _, .nil => fun t => Fin.elim0 t
  | _, @Hist.snoc _ n H k _z _d => Fin.snoc (α := fun t : Fin (n + 1) => Idx t.val)
      (splitChoices H) k

/-- **The legs of the pin--mark path, from the split choices alone.**

* `n = 0`: the diagram is `y → w → g j` and there is one leg on the path, the leg `(y,w)` in
  slot `0` (the pin slot).
* One more round, splitting leg `i`: if `i` lies on the current path, then `splitAt` replaces it by
  the two halves `(·,z)` and `(z,·)` — both on the path — so the path gains exactly one leg and the
  new path legs are `Sum.inl i` and `Sum.inr false`; the new arm leg `Sum.inr true` is off the path.
  If `i` is off the path, the path is unchanged and only the index type grows (`Sum.inl`).

The mark `w` is the *target* of the last path leg (`wSlotK`), and `markDepthK` counts the legs of
the path from the pin `y` to `w`. -/
def pathLegsK : (n : ℕ) → ((t : Fin n) → Idx t) → Finset (Idx n)
  | 0, _ => {idxZero}
  | n + 1, k =>
    if k (Fin.last n) ∈ pathLegsK n (fun t => k t.castSucc) then
      (((pathLegsK n (fun t => k t.castSucc)).erase (k (Fin.last n))).image Sum.inl ∪
        {Sum.inl (k (Fin.last n)), Sum.inr false} : Finset (Idx (n + 1)))
    else (((pathLegsK n (fun t => k t.castSucc)).image Sum.inl : Finset (Idx (n + 1))))

/-- **The length of the pin--mark path** carried by a branch of the iterated first-hit cover: the
number of legs of the `2(n+1)`-leg diagram that lie on the path from `y` to `w` (it grows by one
exactly when the split leg is on the path, and starts at the single leg `(y,w)`; for small `q` the
identity `markDepthK n k = (pathLegsK n k).card` is checked by kernel reduction in
`QDeep/Main.lean`).  This is the `ℓ` of the fresh normal form `χ^(2q-ℓ) T^ℓ(w,y)`; the remaining
`2(n+1) - ℓ` legs are fully summed and supply the `χ`-power. -/
def markDepthK : (n : ℕ) → ((t : Fin n) → Idx t) → ℕ
  | 0, _ => 1
  | n + 1, k =>
    markDepthK n (fun t => k t.castSucc) +
      (if k (Fin.last n) ∈ pathLegsK n (fun t => k t.castSucc) then 1 else 0)

/-- **The slot whose target is the mark `w`.**  `Hist.legs H y w ga (wSlot H)` is a leg of the
diagram that ends at `w` (`legs_wSlot` in `QDeep/Main.lean`), so the mark is genuinely an endpoint
of a path leg and `markDepth` is the distance from the pin to it. -/
def wSlotK : (n : ℕ) → ((t : Fin n) → Idx t) → Idx n
  | 0, _ => idxZero
  | n + 1, k =>
    if k (Fin.last n) = wSlotK n (fun t => k t.castSucc) then Sum.inr false
    else Sum.inl (wSlotK n (fun t => k t.castSucc))

/-- The pin--mark path length of a history: it depends only on the history's split choices
(a direct consequence of the definition, not a separate global linkage theorem), never on the attachment vertices or the arm values. -/
def markDepth {n : ℕ} (H : Hist V n) : ℕ := markDepthK n (splitChoices H)

/-- The mark slot of a history (the slot whose target is `w`). -/
def wSlot {n : ℕ} (H : Hist V n) : Idx n := wSlotK n (splitChoices H)

/-- **The `ℓ`-th coefficient of the general-`q` fresh normal form**, as an explicit finite
cardinality: the number of branches `k : (t : Fin (q-1)) → Idx t` of the iterated first-hit cover
whose pin--mark path has length `ℓ`.  Summed over `ℓ` this is `2^(q-1) (q-1)!` — production's
`card_histChoices_eq`, i.e. the total number of branches of the `2q`-leg split construction. -/
def depthCount (n ℓ : ℕ) : ℕ :=
  Fintype.card {k : ((t : Fin n) → Idx t) // markDepthK n k = ℓ}

/-- The coefficient `C_ℓ` of the general-`q` fresh normal form, `ℓ ∈ [1,q]`. -/
noncomputable def genCoeff (q ℓ : ℕ) : ℕ := depthCount (q - 1) ℓ

/-- **The general-`q` fresh polynomial with the cover's own coefficients**: the printed
normalisation `∑_{ℓ∈[1,q]} C_ℓ χ^(2q-ℓ) T^ℓ(w,y)` with `C_ℓ = genCoeff q ℓ` the number of
branches of the iterated first-hit cover with pin--mark path length `ℓ`.

By construction this is production's `I417Fresh.Subdivision.freshPoly` with coefficient function
`genCoeff q` (`genFreshProfile_eq_freshPoly`), so a branch evaluation of `genShape` lands directly
in the normalisation consumed by `Subdivision.composed_family_le` / `marked_fresh_le`. -/
noncomputable def genFreshProfile {V : Type*} [Countable V] [DecidableEq V]
    (k : V → V → ℝ≥0∞) (χ : ℝ≥0∞) (q : ℕ) (v w : V) : ℝ≥0∞ :=
  ∑ ℓ ∈ Finset.Icc 1 q, (genCoeff q ℓ : ℝ≥0∞) * (χ ^ (2 * q - ℓ) * I417Base.iterPow k ℓ v w)

end PercLib.CriticalLRP.I417FreshDepth
