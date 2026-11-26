/-
Coordinator-integrated from the independently rebuilt `smwxb4a1l/m1` Q5 artifact.
Original production base `8d1c9eb3738a26cc63afc07f525ba4af357bd905`; review revisions
are confined to strict module lints and explicit branch-lemma aggregation.
-/
/-
Independently built for swarm `smwxb4a1l`, member `m1`, direction Q5-FINITE-EVALUATION.
Read-only against production (`d9a001b7f0a33cf6395158f7621ad4de1fe3c7c8`); this directory is the
only place written. Definitions only in this file.
-/
module

public import PercLib.CriticalLRP.Correlation.I417.General.Defs
public import PercLib.CriticalLRP.Correlation.I417.Fresh.Iter.Cover

/-!
# Lemma I.4.17 at `q = 5`: the ten-edge fresh diagram family

Source: T. Hutchcroft, *Critical long-range percolation I: High effective dimension*,
arXiv:2508.18807v1, Lemma I.4.17 and its proof (supplied paper text lines 2444--2513,
`repo/.scratch/formalization-next/paper.txt`, pp. 43--46).

Production's `I417GenIter` builds the fresh side of the `q`-fold two-copy expansion as `2q`
edge-disjoint legs: the two halves `y → w`, `w → g j` of the selected arm's path, plus one
attachment round per remaining arm, each round first-hitting the diagram built so far and splitting
the hit leg (`I417GenIter.Hist`, `Hist.legs`, `genShape`).  At `q = 5` the fresh side carries
`2q = 10` edges and there are `q - 1 = 4` attachment rounds, i.e. `2 · 4 · 6 · 8 = 384` branch
choices of split legs and four summed attachment vertices `z1, …, z4`.

This file only *names* the objects the evaluation works with; every proof is elsewhere.

* `q5Legs` — the ten legs of one branch, written as the four-fold nested `splitAt` of production's
  `I417FreshFour.Refined.splitAt`/`baseLegs` on the explicit nested index type
  `((((Fin 2 ⊕ Bool) ⊕ Bool) ⊕ Bool) ⊕ Bool)` of `2 · (4 + 1) = 10` slots.  It is definitionally the
  `Hist.legs` of the concrete attachment history `histFive` (see `q5Legs_eq_hist`), so no new
  diagram notion is introduced: it is production's iterated first-hit attachment, instantiated.
* `histFive` — the canonical `Hist V 4` with split legs `k1, …, k4`, hit vertices `z1, …, z4` and
  attached arms `gb, gc, gd, ge`.
* `armEquiv5` — for five distinct labels, the reindexing `(Fin 5 → V) ≃ V × V × V × V × V` which
  turns the five-arm sum of the fresh event into five independent one-variable sums.  All five *arm
  labels are retained*: the reindexing is a bijection, not a collapse to multisets.
* `q5Shape` — the union of the `384` ten-leg shapes over the branch choices and the four summed
  attachment vertices, with the five labels `ga, gb, gc, gd, ge` kept in place.
* `freshFiveProfile` — the target polynomial `24 χ⁵ T⁵ + 60 χ⁶ T⁴ + 90 χ⁷ T³ + 105 χ⁸ T² +
  105 χ⁹ T(w,y)`, each monomial carrying `(10 - ℓ) + ℓ = 10 = 2q` two-point factors.  The
  coefficients `24, 60, 90, 105, 105` are the numbers of branches with `ℓ = 5, 4, 3, 2, 1`
  (`Q5Eval` proves the aggregation; the finite count was independently recomputed by the branch
  simulator and reproduces the accepted `q = 4` vector `6, 12, 15, 15` as a check).

Degeneracies (`w = y`, `w = g j`, coincident arms, attachment points at existing vertices, trivial
legs) are absorbed by the vertex sums; a trivial walk is a legal witness, exactly
as in the accepted `q = 2`, `q = 3` and `q = 4` artifacts.
-/

open MeasureTheory Measure ProbabilityTheory unitInterval
open scoped ENNReal NNReal

set_option linter.unusedSectionVars false
set_option linter.unusedDecidableInType false
set_option linter.style.longLine false
set_option linter.style.show false
set_option linter.unusedSimpArgs false

@[expose] public section

namespace PercLib.CriticalLRP.I417FreshFive

open PercLib.CriticalLRP

export PercLib.CriticalLRP.I417FreshFour.Refined
  (LegWalk ShapeOfI splitAt baseLegs baseWalks Diag baseDiag)

variable {V : Type*} [Countable V] [DecidableEq V]

/-! ## The canonical attachment history and its ten legs -/

/-- **The canonical attachment history** of `q = 5`: production's `I417GenIter.Hist`, four `snoc`
rounds from the empty history, with the split legs `k1, …, k4`, hit vertices `z1, …, z4` and attached
arms `gb, gc, gd, ge`.  Its selected arm is `ga`. -/
def histFive (k1 : I417GenIter.Idx 0) (k2 : I417GenIter.Idx 1) (k3 : I417GenIter.Idx 2)
    (k4 : I417GenIter.Idx 3) (z1 z2 z3 z4 gb gc gd ge : V) : I417GenIter.Hist V 4 :=
  I417GenIter.Hist.snoc
    (I417GenIter.Hist.snoc (I417GenIter.Hist.snoc (I417GenIter.Hist.snoc
      I417GenIter.Hist.nil k1 z1 gb) k2 z2 gc) k3 z3 gd) k4 z4 ge

/-- `Idx n` has decidable equality (it is a nested sum of `Fin 2` and `Bool`). -/
instance instDecidableEqIdx (n : ℕ) : DecidableEq (I417GenIter.Idx n) := by
  induction n with
  | zero => exact inferInstanceAs (DecidableEq (Fin 2))
  | succ n ih =>
    letI := ih
    exact inferInstanceAs (DecidableEq (I417GenIter.Idx n ⊕ Bool))

/-- **The ten legs of one `q = 5` branch.**  Start from the two halves `y → w`, `w → ga` of the
selected arm's path (production's `baseLegs`) and attach the four remaining arms `gb, gc, gd, ge` one
at a time, each at the first-hit vertex `z1, z2, z3, z4` inside the diagram built so far; `k1, …,
k4` record which leg each attachment splits.  It is production's `I417GenIter.Hist.legs` of the
canonical history `histFive`, cast to the explicit nested index type of `2 · (4 + 1) = 10` slots;
no new diagram notion is introduced.  The index type grows `2 → 4 → 6 → 8 → 10`, so the
result has exactly `2q = 10` legs — ten two-point factors at `q = 5`. -/
noncomputable def q5Legs (k1 : Fin 2) (k2 : Fin 2 ⊕ Bool) (k3 : (Fin 2 ⊕ Bool) ⊕ Bool)
    (k4 : ((Fin 2 ⊕ Bool) ⊕ Bool) ⊕ Bool) (z1 z2 z3 z4 y w ga gb gc gd ge : V) :
    (((Fin 2 ⊕ Bool) ⊕ Bool) ⊕ Bool) ⊕ Bool → V × V :=
  splitAt (splitAt (splitAt (splitAt (baseLegs y w ga) k1 z1 gb) k2 z2 gc) k3 z3 gd) k4 z4 ge

/-- **The `q = 5` fresh family**: the union of the `2 · 4 · 6 · 8 = 384` ten-leg shapes over the
branch choices and over the four summed attachment vertices.  All five arm labels are retained: the
selected arm is `ga`, the four attached arms are `gb, gc, gd, ge`. -/
def q5Shape (y w ga gb gc gd ge : V) : Set (Config V) :=
  ⋃ (k1 : Fin 2), ⋃ (k2 : Fin 2 ⊕ Bool), ⋃ (k3 : (Fin 2 ⊕ Bool) ⊕ Bool),
    ⋃ (k4 : ((Fin 2 ⊕ Bool) ⊕ Bool) ⊕ Bool), ⋃ (z1 : V), ⋃ (z2 : V), ⋃ (z3 : V), ⋃ (z4 : V),
      ShapeOfI (q5Legs k1 k2 k3 k4 z1 z2 z3 z4 y w ga gb gc gd ge)

/-! ## The five labelled arms as a tuple -/

/-- **The five-arm reindexing.**  For five *distinct* labels `a b c d e : Fin 5`, evaluation at the
five coordinates is a bijection `(Fin 5 → V) ≃ V × V × V × V × V`.  The inverse puts the five values
back at the five labelled slots and is defined by a five-way `if`; the distinctness hypotheses make
the five cases exhaustive.  The `q = 5` analogue of `I417FreshFour.Eval.armEquiv4`. -/
def armEquiv5 (a b c d e : Fin 5) (hab : a ≠ b) (hac : a ≠ c) (had : a ≠ d) (hae : a ≠ e)
    (hbc : b ≠ c) (hbd : b ≠ d) (hbe : b ≠ e) (hcd : c ≠ d) (hce : c ≠ e) (hde : d ≠ e) :
    (Fin 5 → V) ≃ V × V × V × V × V where
  toFun g := (g a, g b, g c, g d, g e)
  invFun p i := if i = a then p.1 else if i = b then p.2.1 else if i = c then p.2.2.1
    else if i = d then p.2.2.2.1 else p.2.2.2.2
  left_inv g := by
    funext i
    by_cases h1 : i = a
    · simp [h1]
    by_cases h2 : i = b
    · simp [h2, h1, hab.symm]
    by_cases h3 : i = c
    · simp [h3, h1, h2, hac.symm, hbc.symm]
    by_cases h4 : i = d
    · simp [h4, h1, h2, h3, had.symm, hbd.symm, hcd.symm]
    · have h5 : i = e := by
        have hi := i.isLt
        have ha := a.isLt
        have hb := b.isLt
        have hc := c.isLt
        have hd := d.isLt
        have he := e.isLt
        have h1' : i.val ≠ a.val := fun h => h1 (Fin.ext h)
        have h2' : i.val ≠ b.val := fun h => h2 (Fin.ext h)
        have h3' : i.val ≠ c.val := fun h => h3 (Fin.ext h)
        have h4' : i.val ≠ d.val := fun h => h4 (Fin.ext h)
        exact Fin.ext (by omega)
      simp [h5, h1, h2, h3, h4, hae.symm, hbe.symm, hce.symm, hde.symm]
  right_inv p := by
    have e1 : (if a = a then p.1 else if a = b then p.2.1 else if a = c then p.2.2.1
        else if a = d then p.2.2.2.1 else p.2.2.2.2) = p.1 := by simp
    have e2 : (if b = a then p.1 else if b = b then p.2.1 else if b = c then p.2.2.1
        else if b = d then p.2.2.2.1 else p.2.2.2.2) = p.2.1 := by simp [hab.symm]
    have e3 : (if c = a then p.1 else if c = b then p.2.1 else if c = c then p.2.2.1
        else if c = d then p.2.2.2.1 else p.2.2.2.2) = p.2.2.1 := by
      simp [hac.symm, hbc.symm]
    have e4 : (if d = a then p.1 else if d = b then p.2.1 else if d = c then p.2.2.1
        else if d = d then p.2.2.2.1 else p.2.2.2.2) = p.2.2.2.1 := by
      simp [had.symm, hbd.symm, hcd.symm]
    have e5 : (if e = a then p.1 else if e = b then p.2.1 else if e = c then p.2.2.1
        else if e = d then p.2.2.2.1 else p.2.2.2.2) = p.2.2.2.2 := by
      simp [hae.symm, hbe.symm, hce.symm, hde.symm]
    show ((if a = a then p.1 else if a = b then p.2.1 else if a = c then p.2.2.1
        else if a = d then p.2.2.2.1 else p.2.2.2.2),
      (if b = a then p.1 else if b = b then p.2.1 else if b = c then p.2.2.1
        else if b = d then p.2.2.2.1 else p.2.2.2.2),
      (if c = a then p.1 else if c = b then p.2.1 else if c = c then p.2.2.1
        else if c = d then p.2.2.2.1 else p.2.2.2.2),
      (if d = a then p.1 else if d = b then p.2.1 else if d = c then p.2.2.1
        else if d = d then p.2.2.2.1 else p.2.2.2.2),
      (if e = a then p.1 else if e = b then p.2.1 else if e = c then p.2.2.1
        else if e = d then p.2.2.2.1 else p.2.2.2.2)) = p
    rw [e1, e2, e3, e4, e5]

/-! ## The `q = 5` fresh-side polynomial -/

/-- **The `q = 5` fresh-side polynomial** in the normalisation of Lemma I.4.17:
`24 χ⁵ T⁵ + 60 χ⁶ T⁴ + 90 χ⁷ T³ + 105 χ⁸ T² + 105 χ⁹ T(w,y)`.  Every monomial carries
`(10 - ℓ) + ℓ = 10 = 2q` two-point factors, and the coefficients are the numbers of the `384`
branches whose mark has `y`-depth `ℓ = 5, 4, 3, 2, 1`.  After composition with the `2p + 1`-edge
marked side the total factor count is `2p + 11` and the path powers lie in `[3, p + 6]`. -/
noncomputable def freshFiveProfile (π : Sym2 V → unitInterval) (χ : ℝ≥0∞) (y w : V) : ℝ≥0∞ :=
  24 * (χ ^ 5 * I417Base.iterPow (fun a b => (edgeMeasure π) (connSet a b)) 5 w y) +
    60 * (χ ^ 6 * I417Base.iterPow (fun a b => (edgeMeasure π) (connSet a b)) 4 w y) +
      90 * (χ ^ 7 * I417Base.iterPow (fun a b => (edgeMeasure π) (connSet a b)) 3 w y) +
        105 * (χ ^ 8 * I417Base.iterPow (fun a b => (edgeMeasure π) (connSet a b)) 2 w y) +
          105 * (χ ^ 9 * I417Base.iterPow (fun a b => (edgeMeasure π) (connSet a b)) 1 w y)

end PercLib.CriticalLRP.I417FreshFive
