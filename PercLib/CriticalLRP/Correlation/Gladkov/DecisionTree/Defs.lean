/-
Copyright (c) 2026 PercLib contributors. Released under Apache 2.0.

The finite decision-tree model underlying Gladkov's amalgamation lemma
(arXiv:2408.08457v2, Lemma 3.1 = [GZ24, Lemma 4.2]).

Reference: the finite-graph tree of [Gla24, Section 2]: each node queries an edge and
carries a decision in `{"S", "S̄"}`; decision nodes have four descendants indexed by the
pair of revealed bits `(C1(e), C2(e))`; the nodes on a path query pairwise distinct
edges; the leaf node also queries its edge. `BuildSet` returns the set of queried
edges whose decision is `"S"`, so an unqueried edge is never in `S`.

This file sets up the transcript machinery only. The amalgamation theorem is in
`DecisionTree.Main`.
-/
module

public import PercLib.CriticalLRP.Correlation.Gladkov.RandomAmalgam

/-!
# Decision-tree transcripts for the amalgamation lemma

A strategy is a map from the list of records already collected to the next decision
`some (e, c)` or to the stop symbol `none`. A record stores the queried edge, its class
(`true` = `"S"`) and the two revealed bits. `trace` is the list of records collected
after `Fintype.card ι` steps; it has stabilised by then because a consistent strategy
never repeats an edge.

The two configurations are encoded as one configuration on `ι × Bool`, as in
`PercLib.CriticalLRP.Correlation.Gladkov.Amalgam`: `(i, false)` is the coordinate of edge
`i` in the first copy and `(i, true)` that in the second copy.
-/

set_option autoImplicit false

@[expose] public section

open MeasureTheory
open PercLib.Probability
open scoped ENNReal

namespace PercLib.GladkovAmalgam

variable {ι : Type*}

/-- A record of one decision-tree node: the queried edge, its class (`true` for `"S"`) and
the two revealed bits. -/
structure Rec (ι : Type*) where
  /-- The queried edge. -/
  edge : ι
  /-- The class of the queried edge: `true` means the node's decision is `"S"`. -/
  cls : Bool
  /-- The value of the first copy at the queried edge. -/
  v1 : Bool
  /-- The value of the second copy at the queried edge. -/
  v2 : Bool
  deriving DecidableEq, Repr

/-- A decision tree: the next decision as a function of the transcript so far. -/
abbrev Tree (ι : Type*) := List (Rec ι) → Option (ι × Bool)

/-- The copy of the queried edge whose value is read off by `C1 →_S C2` when the edge is
decided `"S"` (resp. `"S̄"`). -/
def firstCopy (c : Bool) : Bool := !c

/-- The copy of the queried edge whose value is read off by `C2 →_S C1`. -/
def secondCopy (c : Bool) : Bool := c

/-- The value of the configuration `ν` at the coordinate `x`, as a bit. -/
noncomputable def bit (ν : Set (ι × Bool)) (x : ι × Bool) : Bool := by
  classical
  exact decide (x ∈ ν)

theorem bit_eq_true {ν : Set (ι × Bool)} {x : ι × Bool} : bit ν x = true ↔ x ∈ ν := by
  classical
  simp [bit]

theorem bit_eq_false {ν : Set (ι × Bool)} {x : ι × Bool} : bit ν x = false ↔ x ∉ ν := by
  classical
  simp [bit]

theorem bit_congr {ν ν' : Set (ι × Bool)} {x : ι × Bool} (h : x ∈ ν ↔ x ∈ ν') :
    bit ν x = bit ν' x := by
  by_cases hx : x ∈ ν
  · rw [bit_eq_true.2 hx, bit_eq_true.2 (h.1 hx)]
  · rw [bit_eq_false.2 hx, bit_eq_false.2 fun hc => hx (h.2 hc)]

/-- One step of the run against a configuration `ν`: the revealed bits are the values of
both copies at the queried edge. -/
noncomputable def step (σ : Tree ι) (ν : Set (ι × Bool)) (τ : List (Rec ι)) :
    List (Rec ι) :=
  match σ τ with
  | none => τ
  | some (i, c) => τ ++ [⟨i, c, bit ν (i, false), bit ν (i, true)⟩]

/-- One step of the reconstruction: the bits are read off the amalgamated pair, the class
selects which coordinate of the pair gives which copy. -/
noncomputable def readStep (σ : Tree ι) (η : Set (ι × Bool)) (τ : List (Rec ι)) :
    List (Rec ι) :=
  match σ τ with
  | none => τ
  | some (i, c) => τ ++ [⟨i, c, bit η (i, firstCopy c), bit η (i, secondCopy c)⟩]

/-- The run against `ν`, after `n` steps. -/
noncomputable def runN (σ : Tree ι) (ν : Set (ι × Bool)) : ℕ → List (Rec ι)
  | 0 => []
  | n + 1 => step σ ν (runN σ ν n)

/-- **Consistency along paths.** Along the run against any configuration the strategy never
queries an edge it has already queried: this is [Gla24, Section 2]'s requirement that the
nodes on every path from the initial node query pairwise distinct edges. -/
def Consistent (σ : Tree ι) : Prop :=
  ∀ (ν : Set (ι × Bool)) (n : ℕ) (i : ι) (c : Bool), σ (runN σ ν n) = some (i, c) →
    ∀ r ∈ runN σ ν n, r.edge ≠ i

/-- A strategy that never queries an edge of its transcript at all is consistent. -/
theorem consistent_of_strong {σ : Tree ι}
    (h : ∀ (τ : List (Rec ι)) (i : ι) (c : Bool), σ τ = some (i, c) →
      ∀ r ∈ τ, r.edge ≠ i) :
    Consistent σ :=
  fun _ _ i c hc => h _ i c hc

/-- The reconstruction run from the amalgamated pair `η`, after `n` steps. -/
noncomputable def readN (σ : Tree ι) (η : Set (ι × Bool)) : ℕ → List (Rec ι)
  | 0 => []
  | n + 1 => readStep σ η (readN σ η n)

/-- The whole transcript of the run against `ν`: `Fintype.card ι` steps suffice. -/
noncomputable def trace (σ : Tree ι) [Fintype ι] (ν : Set (ι × Bool)) : List (Rec ι) :=
  runN σ ν (Fintype.card ι)

/-- The whole reconstruction transcript. -/
noncomputable def readback (σ : Tree ι) [Fintype ι] (η : Set (ι × Bool)) : List (Rec ι) :=
  readN σ η (Fintype.card ι)

theorem runN_succ (σ : Tree ι) (ν : Set (ι × Bool)) (n : ℕ) :
    runN σ ν (n + 1) = step σ ν (runN σ ν n) := rfl

/-- The set `S(C1,C2)` built by the tree: the queried edges decided `"S"`. Edges that were
never queried are not in `S`, as in `BuildSet`. -/
noncomputable def treeSet (σ : Tree ι) [Fintype ι] (ν : Set (ι × Bool)) : Set ι :=
  {i | ∃ r ∈ trace σ ν, r.edge = i ∧ r.cls = true}

/-- The set decoded from the reconstruction transcript. -/
noncomputable def readSet (σ : Tree ι) [Fintype ι] (η : Set (ι × Bool)) : Set ι :=
  {i | ∃ r ∈ readback σ η, r.edge = i ∧ r.cls = true}

/-- `C1 →_S C2`: the first copy on `S`, the second off `S`. -/
noncomputable def treeFirst (σ : Tree ι) [Fintype ι] (ν : Set (ι × Bool)) : Set ι :=
  amalFirst (treeSet σ ν) ν

/-- `C2 →_S C1`: the second copy on `S`, the first off `S`. -/
noncomputable def treeSecond (σ : Tree ι) [Fintype ι] (ν : Set (ι × Bool)) : Set ι :=
  amalSecond (treeSet σ ν) ν

/-- The pair `(C1 →_S C2, C2 →_S C1)` encoded as a single configuration on `ι × Bool`. -/
noncomputable def treeConfig (σ : Tree ι) [Fintype ι] (ν : Set (ι × Bool)) :
    Set (ι × Bool) :=
  {x | (x.2 = false ∧ x.1 ∈ treeFirst σ ν) ∨ (x.2 = true ∧ x.1 ∈ treeSecond σ ν)}

/-- The configuration encoding a pair of configurations. -/
def pairConfig (a b : Set ι) : Set (ι × Bool) :=
  {x | (x.2 = false ∧ x.1 ∈ a) ∨ (x.2 = true ∧ x.1 ∈ b)}

/-- The configuration reconstructed from the amalgamated pair: coordinates of the decoded
set `S` keep their copy, the others are swapped. -/
noncomputable def unamal (σ : Tree ι) [Fintype ι] (η : Set (ι × Bool)) : Set (ι × Bool) :=
  {x | (x.1 ∈ readSet σ η ∧ x ∈ η) ∨ (x.1 ∉ readSet σ η ∧ (x.1, !x.2) ∈ η)}

/-! ### The run stabilises -/

theorem step_of_none {σ : Tree ι} {ν : Set (ι × Bool)} {τ : List (Rec ι)}
    (h : σ τ = none) :
    step σ ν τ = τ := by
  unfold step
  rw [h]

theorem step_of_some {σ : Tree ι} {ν : Set (ι × Bool)} {τ : List (Rec ι)} {i : ι} {c : Bool}
    (h : σ τ = some (i, c)) :
    step σ ν τ = τ ++ [⟨i, c, bit ν (i, false), bit ν (i, true)⟩] := by
  classical
  unfold step
  rw [h]

theorem prefix_step (σ : Tree ι) (ν : Set (ι × Bool)) (τ : List (Rec ι)) :
    τ <+: step σ ν τ := by
  rcases h : σ τ with _ | ⟨i, c⟩
  · rw [step_of_none h]
  · rw [step_of_some h]
    exact List.prefix_append _ _

theorem length_step_le (σ : Tree ι) (ν : Set (ι × Bool)) (τ : List (Rec ι)) :
    (step σ ν τ).length ≤ τ.length + 1 := by
  rcases h : σ τ with _ | ⟨i, c⟩
  · rw [step_of_none h]
    simp
  · rw [step_of_some h]
    simp

theorem length_step_of_ne {σ : Tree ι} {ν : Set (ι × Bool)} {τ : List (Rec ι)}
    (h : step σ ν τ ≠ τ) : (step σ ν τ).length = τ.length + 1 := by
  rcases hc : σ τ with _ | ⟨i, c⟩
  · rw [step_of_none hc] at h
    exact absurd rfl h
  · rw [step_of_some hc]
    simp

theorem prefix_runN_succ (σ : Tree ι) (ν : Set (ι × Bool)) (n : ℕ) :
    runN σ ν n <+: runN σ ν (n + 1) :=
  prefix_step σ ν _

theorem prefix_runN (σ : Tree ι) (ν : Set (ι × Bool)) {n m : ℕ} (h : n ≤ m) :
    runN σ ν n <+: runN σ ν m := by
  induction m, h using Nat.le_induction with
  | base => exact List.prefix_rfl
  | succ m _ ih => exact ih.trans (prefix_runN_succ σ ν m)

theorem length_runN_le (σ : Tree ι) (ν : Set (ι × Bool)) (n : ℕ) :
    (runN σ ν n).length ≤ n := by
  induction n with
  | zero => simp [runN]
  | succ n ih =>
      exact le_trans (length_step_le σ ν (runN σ ν n)) (Nat.succ_le_succ ih)

/-! ### Edges along a transcript are pairwise distinct -/

/-- The edges of a transcript are pairwise distinct. -/
def EdgesNodup (l : List (Rec ι)) : Prop := (l.map Rec.edge).Nodup

/-- Distinct members of a transcript carry distinct edges. -/
def EdgeInj (l : List (Rec ι)) : Prop := ∀ r ∈ l, ∀ r' ∈ l, r.edge = r'.edge → r = r'

theorem edgeInj_of_edgesNodup {l : List (Rec ι)} (h : EdgesNodup l) : EdgeInj l := by
  have h' : l.Nodup := List.Nodup.of_map _ h
  have := (List.nodup_map_iff_inj_on h').1 h
  intro r hr r' hr' he
  exact this r hr r' hr' he

theorem edgesNodup_step {σ : Tree ι} {ν : Set (ι × Bool)} {n : ℕ}
    (hσ : Consistent σ) (h : EdgesNodup (runN σ ν n)) :
    EdgesNodup (runN σ ν (n + 1)) := by
  rcases hc : σ (runN σ ν n) with _ | ⟨i, c⟩
  · rw [runN_succ, step_of_none hc]
    exact h
  · rw [runN_succ, step_of_some hc]
    unfold EdgesNodup at h ⊢
    rw [List.map_append, List.map_cons, List.map_nil]
    refine List.nodup_append.2 ⟨h, List.nodup_singleton i, ?_⟩
    intro a ha b hb
    rw [List.mem_singleton] at hb
    obtain ⟨r, hr, rfl⟩ := List.mem_map.1 ha
    rw [hb]
    exact hσ ν n i c hc r hr

theorem runN_edgesNodup {σ : Tree ι} (hσ : Consistent σ) (ν : Set (ι × Bool)) (n : ℕ) :
    EdgesNodup (runN σ ν n) := by
  induction n with
  | zero => exact List.nodup_nil
  | succ n ih => exact edgesNodup_step (ν := ν) hσ ih

theorem length_runN_le_card {σ : Tree ι} [Fintype ι] (hσ : Consistent σ)
    (ν : Set (ι × Bool)) (n : ℕ) : (runN σ ν n).length ≤ Fintype.card ι := by
  have h := List.Nodup.length_le_card (runN_edgesNodup hσ ν n)
  simpa using h

/-! ### The transcript stabilises within `card ι` steps -/

theorem length_runN_of_unstable {σ : Tree ι} {ν : Set (ι × Bool)} :
    ∀ n : ℕ, (∀ m < n, step σ ν (runN σ ν m) ≠ runN σ ν m) →
      (runN σ ν n).length = n := by
  intro n
  induction n with
  | zero => intro _; simp [runN]
  | succ n ih =>
      intro h
      have h' := ih fun m hm => h m (Nat.lt_succ_of_lt hm)
      have hstep : runN σ ν (n + 1) = step σ ν (runN σ ν n) := rfl
      rw [hstep, length_step_of_ne (h n (Nat.lt_succ_self n)), h']

theorem edges_cover_of_length [Fintype ι] {l : List (Rec ι)} (h : EdgesNodup l)
    (hlen : l.length = Fintype.card ι) : ∀ i : ι, ∃ r ∈ l, r.edge = i := by
  classical
  have hcard : (l.map Rec.edge).toFinset.card = Fintype.card ι := by
    rw [List.toFinset_card_of_nodup h, List.length_map, hlen]
  have huniv : (l.map Rec.edge).toFinset = (Finset.univ : Finset ι) := by
    apply Finset.eq_univ_of_card
    simpa using hcard
  intro i
  have hi : i ∈ (l.map Rec.edge).toFinset := by rw [huniv]; exact Finset.mem_univ i
  obtain ⟨r, hr, he⟩ := List.mem_map.1 (List.mem_toFinset.1 hi)
  exact ⟨r, hr, he⟩

/-- A consistent strategy always stabilises within `card ι` steps. -/
theorem exists_stable {σ : Tree ι} [Fintype ι] (hσ : Consistent σ) (ν : Set (ι × Bool)) :
    ∃ n ≤ Fintype.card ι, step σ ν (runN σ ν n) = runN σ ν n := by
  classical
  by_contra hall
  push Not at hall
  have hunst : ∀ m < Fintype.card ι, step σ ν (runN σ ν m) ≠ runN σ ν m :=
    fun m hm => hall m (le_of_lt hm)
  set N := Fintype.card ι with hN
  have hlen : (runN σ ν N).length = N := length_runN_of_unstable N hunst
  have hnodup : EdgesNodup (runN σ ν N) := runN_edgesNodup hσ ν N
  rcases hc : σ (runN σ ν N) with _ | ⟨i, c⟩
  · exact hall N (le_refl N) (step_of_none hc)
  · obtain ⟨r, hr, he⟩ := edges_cover_of_length hnodup hlen i
    exact hσ ν N i c hc r hr he

theorem runN_eq_of_stable {σ : Tree ι} {ν : Set (ι × Bool)} {n : ℕ}
    (h : step σ ν (runN σ ν n) = runN σ ν n) :
    ∀ m : ℕ, n ≤ m → runN σ ν m = runN σ ν n := by
  intro m hm
  obtain ⟨k, rfl⟩ := Nat.exists_eq_add_of_le hm
  clear hm
  induction k with
  | zero => simp
  | succ k ih =>
      rw [Nat.add_succ, runN_succ, ih, h]

theorem step_trace {σ : Tree ι} [Fintype ι] (hσ : Consistent σ) (ν : Set (ι × Bool)) :
    step σ ν (trace σ ν) = trace σ ν := by
  obtain ⟨n, hn, hstab⟩ := exists_stable hσ ν
  have h := runN_eq_of_stable hstab (Fintype.card ι) hn
  rw [trace, h]
  exact hstab

/-! ### The class of a queried edge -/

theorem treeSet_iff_class {σ : Tree ι} [Fintype ι] (hσ : Consistent σ) (ν : Set (ι × Bool))
    {r : Rec ι} (hr : r ∈ trace σ ν) : (r.edge ∈ treeSet σ ν ↔ r.cls = true) := by
  constructor
  · rintro ⟨r', hr', he, hc⟩
    have hinj := edgeInj_of_edgesNodup (runN_edgesNodup hσ ν (Fintype.card ι))
    have : r = r' := hinj r hr r' hr' he.symm
    rw [this, hc]
  · intro hc
    exact ⟨r, hr, rfl, hc⟩

theorem not_mem_treeSet_of_not_mem {σ : Tree ι} [Fintype ι] (ν : Set (ι × Bool)) {i : ι}
    (h : ∀ r ∈ trace σ ν, r.edge ≠ i) : i ∉ treeSet σ ν := by
  rintro ⟨r, hr, he, -⟩
  exact h r hr he

/-! ### The pair reading of the two amalgamations -/

theorem mem_treeConfig_of_mem {σ : Tree ι} [Fintype ι] {ν : Set (ι × Bool)} {i : ι}
    (h : i ∈ treeSet σ ν) :
    ((i, false) ∈ treeConfig σ ν ↔ (i, false) ∈ ν) ∧
      ((i, true) ∈ treeConfig σ ν ↔ (i, true) ∈ ν) := by
  classical
  constructor <;> simp [treeConfig, treeFirst, treeSecond, amalFirst, amalSecond, h]

theorem mem_treeConfig_of_not_mem {σ : Tree ι} [Fintype ι] {ν : Set (ι × Bool)} {i : ι}
    (h : i ∉ treeSet σ ν) :
    ((i, false) ∈ treeConfig σ ν ↔ (i, true) ∈ ν) ∧
      ((i, true) ∈ treeConfig σ ν ↔ (i, false) ∈ ν) := by
  classical
  constructor <;> simp [treeConfig, treeFirst, treeSecond, amalFirst, amalSecond, h]

end PercLib.GladkovAmalgam
