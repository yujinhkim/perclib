/-
Definitions for direction `HISTORY-FIBRE-PACKAGING` (swarm `smwxfstjy`, member `m1`).

Read-only against production `repo/.scratch/critical-lrp-orchestration` (HEAD `3f10797`),
modules `PercLib.CriticalLRP.Correlation.I417.Fresh.HistSpine.{Defs,Bridge}`,
`...Fresh.SplitClosedForm.{Defs,Chain}` and `...Fresh.Depth.{Defs,Main}`.

Every theorem is in `Main.lean`; the axiom audit is `Check.lean`.

## What is defined and why

Production's accepted one-step reindexing `I417HistToSpine.histW_snoc_tsum` collapses one
attachment round *inside a single history*.  Packaging it as an iteration over the whole
history fibre needs three new objects:

* `finSnoc` — the `Fin.snoc` extension of a split-choice tuple `(t : Fin n) → Idx t` by one
  further choice `s : Idx n`, with the dependent `α` fixed once so that it can be rewritten.
* `stepSet` — one attachment round on a *finite set of diagram slots*: the split slot `j` is
  replaced by the two halves `Sum.inl j`, `Sum.inr false` and every other slot `i` is carried
  along as `Sum.inl i`.  This is production's `I417FreshDepth.pathLegsK` step, in the form that
  composes along the rounds.
* `chainF` — the propagation of such a slot set through all remaining attachment rounds.  It
  is the forward (round by round) counterpart of the backward recursion `chainM`, and it is what
  identifies `chainM n k 0 idxZero` with the number of legs on the pin--mark path.
* `histSuccEquiv` / `fibreSnocEquiv` — a history of stage `n + 1` is a `snoc`, and the histories
  whose split choices extend `k` by `s` are exactly the `snoc H s z d` with `splitChoices H = k`.
  This is the fibre reindexing used by `histFibre_snoc`.
-/
module

public import PercLib.CriticalLRP.Correlation.I417.Fresh.SplitClosedForm.Chain
public import PercLib.CriticalLRP.Correlation.I417.Fresh.Depth.Main

/-!
# Definitions for the history-fibre iteration of the iterated first-hit fresh cover

`finSnoc` (one more split choice), `stepSet`/`chainF` (a slot set propagated through the
remaining attachment rounds), and the two reindexing equivalences `histSuccEquiv`,
`fibreSnocEquiv`.  Theorems are in `Main.lean`; the axiom audit is `Check.lean`.
-/

open MeasureTheory Measure ProbabilityTheory unitInterval
open scoped ENNReal NNReal BigOperators

set_option linter.unusedSectionVars false
set_option linter.unusedDecidableInType false
set_option linter.style.longLine false

@[expose] public section

namespace PercLib.CriticalLRP.I417HistFibre

open PercLib.CriticalLRP

variable {V : Type*} [Countable V] [DecidableEq V]

/-! ## Extending a split-choice tuple by one round -/

/-- The split-choice tuple `f` of the rounds `0, …, n-1`, extended by the choice `s` for round
`n`.  This is production's own `Fin.snoc` (`I417FreshDepth.splitChoices` builds histories with it),
written with the dependent index family `α t = Idx t` fixed once, so that the last and the
`castSucc` projections are rewrite rules rather than definitional coincidences. -/
def finSnoc {n : ℕ} (f : (t : Fin n) → I417GenIter.Idx t) (s : I417GenIter.Idx n) :
    (t : Fin (n + 1)) → I417GenIter.Idx t.val :=
  Fin.snoc f s

/-- The second slot of the two-leg base diagram (`Idx 0 = Fin 2`): the leg `(w, ga)` whose
target is the free arm endpoint.  Recorded as a definition because the numeral `1` does not
elaborate at type `Idx 0` without unfolding the recursion. -/
def idxOne : I417GenIter.Idx 0 := (1 : Fin 2)

/-! ## A set of diagram slots, propagated through one attachment round -/

/-- The left half of the slot type `Idx (m+1) = Idx m ⊕ Bool`, at the types that actually occur in
the recursion.  Written as a definition so that every lemma below mentions the same function type
`Idx m → Idx (m+1)` and no instance is selected through the unfolded sum type. -/
def slotInl {m : ℕ} : I417GenIter.Idx m → I417GenIter.Idx (m + 1) := Sum.inl

/-- The right halves of the slot type, at the types that actually occur in the recursion. -/
def slotInr {m : ℕ} (b : Bool) : I417GenIter.Idx (m + 1) := Sum.inr b




/-- **One attachment round on a finite set of slots.**  `stepSet j A` is the image of `A` under
the split of the slot `j`: every slot `i ∈ A` is carried along as `Sum.inl i`, and if the split
slot `j` itself is in `A` then the new leg `Sum.inr false` (the part of `j` that keeps its target)
joins it; the newly attached arm `Sum.inr true` is never in the image.

This is the slot-set form of production's path rule: `pathLegsK (n+1) k` is
`stepSet (k (Fin.last n)) (pathLegsK n (k ∘ castSucc))` up to the `erase`/`image` bookkeeping of
`Depth/Defs.lean` (see `pathLegsK_eq_stepSet` in `MarkDepth.lean`). -/
noncomputable def stepSet {m : ℕ} (j : I417GenIter.Idx m) (A : Finset (I417GenIter.Idx m)) :
    Finset (I417GenIter.Idx (m + 1)) :=
  A.image slotInl ∪ (if j ∈ A then {slotInr false} else ∅)

/-- **The arm part of the step of a singleton**: the new leg `Sum.inr false` if the slot is the
split slot, and nothing otherwise. -/
def stepArm {m : ℕ} (j a : I417GenIter.Idx m) : Finset (I417GenIter.Idx (m + 1)) :=
  if a = j then {slotInr false} else ∅

/-- **The slot set of a chain, propagated through all remaining rounds.**  `chainF n k t S` is the
set of slots of the final `2(n+1)`-leg diagram that the slots in `S : Finset (Idx t)` resolve
into after the splits `k t, …, k (n-1)`; at the top stage `t = n` no split remains and the set is
`S` itself.  It is the forward recursion matching `I417SplitClosedForm.chainM`
(`chainM` is its cardinality on singletons, `chainM_eq_card_chainF`). -/
noncomputable def chainF (n : ℕ) (k : (u : Fin n) → I417GenIter.Idx u) (t : Fin (n + 1))
    (S : Finset (I417GenIter.Idx t.val)) : Finset (I417GenIter.Idx n) :=
  if h : t.val < n then
    chainF n k ⟨t.val + 1, Nat.succ_lt_succ h⟩ (stepSet (k ⟨t.val, h⟩) S)
  else
    have hcast : t.val = n := Nat.le_antisymm (Nat.le_of_lt_succ t.isLt) (Nat.le_of_not_lt h)
    hcast ▸ S
termination_by n - t.val
decreasing_by exact Nat.sub_lt_sub_left ‹t.val < n› (Nat.lt_succ_self t.val)

/-- **The split choices of a `snoc` are the extended tuple.**  This is production's own definition
of `I417FreshDepth.splitChoices`, recorded as a rewrite rule from the `finSnoc` form. -/
theorem splitChoices_snoc {n : ℕ} (H : I417GenIter.Hist V n) (s : I417GenIter.Idx n)
    (z d : V) :
    I417FreshDepth.splitChoices (I417GenIter.Hist.snoc H s z d) =
      finSnoc (I417FreshDepth.splitChoices H) s := rfl

/-! ## The fibre reindexing of one attachment round -/

/-- **A history of positive stage is a `snoc`**: deleting the last record is a bijection onto the
previous stage together with the last split slot, vertex and arm. -/
def histSuccEquiv (n : ℕ) : I417GenIter.Hist V (n + 1) ≃
    I417GenIter.Hist V n × (I417GenIter.Idx n × (V × V)) where
  toFun H := match H with
    | .snoc H s z d => (H, s, z, d)
  invFun p := .snoc p.1 p.2.1 p.2.2.1 p.2.2.2
  left_inv H := by cases H; rfl
  right_inv p := by obtain ⟨H, s, z, d⟩ := p; rfl

/-- **The fibre of the `snoc` extension.**  The histories of stage `n + 1` whose split choices are
`finSnoc k s` are exactly the `snoc H s z d` with `splitChoices H = k`: the last split choice is
forced to be `s` and the earlier ones are the split choices of the tail history.  The attachment
vertex `z` and the arm `d` are free. -/
def fibreSnocEquiv {n : ℕ} (k : (t : Fin n) → I417GenIter.Idx t) (s : I417GenIter.Idx n) :
    {H' : I417GenIter.Hist V (n + 1) //
        I417FreshDepth.splitChoices H' = finSnoc k s} ≃
      {H : I417GenIter.Hist V n // I417FreshDepth.splitChoices H = k} × (V × V) where
  toFun H' := by
    obtain ⟨H', hH'⟩ := H'
    cases H' with
    | snoc H s₀ z d =>
      have hlast : s₀ = s := by
        have h := congrFun hH' (Fin.last n)
        simpa [splitChoices_snoc, finSnoc] using h
      subst hlast
      refine (⟨H, ?_⟩, (z, d))
      funext t
      have h := congrFun hH' t.castSucc
      simpa [splitChoices_snoc, finSnoc] using h
  invFun p :=
    ⟨.snoc p.1.1 s p.2.1 p.2.2, by rw [splitChoices_snoc, p.1.2]⟩
  left_inv H' := by
    obtain ⟨H', hH'⟩ := H'
    cases H' with
    | snoc H s₀ z d =>
      have hlast : s₀ = s := by
        have h := congrFun hH' (Fin.last n)
        simpa [splitChoices_snoc, finSnoc] using h
      subst hlast
      rfl
  right_inv p := by
    obtain ⟨⟨H, hH⟩, z, d⟩ := p
    rfl

end PercLib.CriticalLRP.I417HistFibre
