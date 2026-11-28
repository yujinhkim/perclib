/-
Copyright (c) 2026 PercLib contributors. Released under Apache 2.0.

# A finite edge-by-edge root-cluster exploration

Source: T. Hutchcroft, *On the derivation of mean-field percolation critical exponents from
the triangle condition* (arXiv:2106.06400), proof of Theorem 1.3, which applies Theorem 3.1
to "a decision tree that explores the cluster of the origin one edge at a time, stopping if
and when it first finds `n` vertices in `K`":

> This decision tree can only query edges with at least one endpoint in `K`, and the edges
> queried by `T` all have endpoints in some set of size at most `n`.  Using the assumption
> that `∑_{e ∈ E^→_o} J_e = 1`, it follows that
> `∑_e J_e Rev_{β₁}(T,e) ≤ E_{β₁}[|K| ∧ n]`.

This file builds the finite combinatorial model of that exploration and proves the displayed
estimate for it, in the unnormalised form

`∑_e J_e · Rev_β(T,e) ≤ A · ∑_{k=1}^{n} P_β(|K| ≥ k) = A · E_β[|K| ∧ n]`,

where `A = ∑_{e ∋ v} J_e` is the common incident edge-weight sum (`1` under the source's
normalisation).  A finite vertex type `V`, a finite edge type `E` with two endpoint maps
`lft rgt : E → V`, and edge weights `J : E → ℝ` replace the weighted graph `G = (V, E, J)`;
a configuration is a `Bool`-valued function `E → Bool` (`true` = open).  The exploration is
deterministic, greedy and queries one edge at a time: at each step it picks an edge that is
incident to the discovered set and not yet queried, and when that edge is open it also
discovers its other endpoint.

The four parts of the file are: (I) the exploration and its invariants — the discovered set
never exceeds `n` vertices, it is contained in the open cluster of the root, and every queried
edge has an endpoint in the discovered set; (II) the charging, Fubini and tail-sum identities
and the resulting budget; (III) the termination analysis showing that the run for `#E` steps
has stopped with exactly `|K| ∧ n` vertices discovered; (IV) a two-vertex example in which both
sides of the budget are computed.  Nothing in Part I is probabilistic; the product Bernoulli
law enters only through the production weight `LRP.confWeight` and its normalisation.
-/
module

public import PercLib.CriticalLRP.Analysis.SecondMomentCase3.CriticalVolumeTail.Entropy.Pinsker

/-!
# Finite edge-by-edge cluster exploration and its revealment budget

The finite root-cluster exploration of the proof of `thm:DM_Chi` (arXiv:2106.06400,
Theorem 1.3), its invariants, its exact stopping on `|K| ∧ n` vertices, and the revealment
estimate `∑_e J_e Rev_β(T,e) ≤ A ∑_{k=1}^{n} P_β(|K| ≥ k)` for the actual product
Bernoulli law of `LRP.confWeight J β`.
-/

set_option autoImplicit false

@[expose] public section

open Finset

namespace LRP
namespace Reveal

variable {V E : Type*}

/-! ### Endpoints, adjacency and reachability -/

/-- `v` is an endpoint of the edge `e`. -/
def Incident (lft rgt : E → V) (e : E) (v : V) : Prop := lft e = v ∨ rgt e = v

/-- The one-step adjacency relation of the open graph: the two endpoints of an open edge. -/
def Adj (lft rgt : E → V) (ω : E → Bool) (x y : V) : Prop :=
  ∃ e, ω e = true ∧ ((lft e = x ∧ rgt e = y) ∨ (lft e = y ∧ rgt e = x))

theorem adj_comm (lft rgt : E → V) (ω : E → Bool) (x y : V) :
    Adj lft rgt ω x y ↔ Adj lft rgt ω y x := by
  constructor
  · rintro ⟨e, hop, hxy | hxy⟩
    · exact ⟨e, hop, Or.inr hxy⟩
    · exact ⟨e, hop, Or.inl hxy⟩
  · rintro ⟨e, hop, hxy | hxy⟩
    · exact ⟨e, hop, Or.inr hxy⟩
    · exact ⟨e, hop, Or.inl hxy⟩

/-- Reachability in the open graph, as the reflexive-transitive closure of `Adj`. -/
def Reach (lft rgt : E → V) (ω : E → Bool) (x y : V) : Prop :=
  Relation.ReflTransGen (Adj lft rgt ω) x y

theorem reach_refl (lft rgt : E → V) (ω : E → Bool) (x : V) : Reach lft rgt ω x x :=
  Relation.ReflTransGen.refl

theorem reach_of_adj {lft rgt : E → V} {ω : E → Bool} {x y : V} (h : Adj lft rgt ω x y) :
    Reach lft rgt ω x y :=
  Relation.ReflTransGen.single h

theorem reach_tail {lft rgt : E → V} {ω : E → Bool} {x y z : V}
    (h : Reach lft rgt ω x y) (h' : Adj lft rgt ω y z) : Reach lft rgt ω x z :=
  Relation.ReflTransGen.tail h h'

/-! ### The far endpoint of an incident edge -/

section Far

variable [DecidableEq V]

/-- The vertex to add to the discovered set when `e` is found open: the endpoint of `e` that
is not yet known. -/
def farS (lft rgt : E → V) (S : Finset V) (e : E) : V :=
  if lft e ∈ S then rgt e else lft e

theorem mem_insert_farS {lft rgt : E → V} {S : Finset V} {e : E}
    (h : lft e ∈ S ∨ rgt e ∈ S) :
    lft e ∈ insert (farS lft rgt S e) S ∧ rgt e ∈ insert (farS lft rgt S e) S := by
  by_cases hl : lft e ∈ S
  · have hfar : farS lft rgt S e = rgt e := by simp [farS, hl]
    rw [hfar]
    exact ⟨mem_insert_of_mem hl, mem_insert_self _ _⟩
  · have hr : rgt e ∈ S := by tauto
    have hfar : farS lft rgt S e = lft e := by simp [farS, hl]
    rw [hfar]
    exact ⟨mem_insert_self _ _, mem_insert_of_mem hr⟩

/-- An open edge with one endpoint already connected to the root connects its far endpoint. -/
theorem reach_farS {lft rgt : E → V} {ω : E → Bool} {root : V} {S : Finset V} {e : E}
    (hS : ∀ v ∈ S, Reach lft rgt ω root v) (hinc : lft e ∈ S ∨ rgt e ∈ S)
    (hopen : ω e = true) : Reach lft rgt ω root (farS lft rgt S e) := by
  by_cases hl : lft e ∈ S
  · have hfar : farS lft rgt S e = rgt e := by simp [farS, hl]
    rw [hfar]
    exact reach_tail (hS _ hl) ⟨e, hopen, Or.inl ⟨rfl, rfl⟩⟩
  · have hr : rgt e ∈ S := by tauto
    have hfar : farS lft rgt S e = lft e := by simp [farS, hl]
    rw [hfar]
    exact reach_tail (hS _ hr) ⟨e, hopen, Or.inr ⟨rfl, rfl⟩⟩

end Far

/-! ### Incident edge weights -/

section Weights

variable [Fintype E] [DecidableEq V]

/-- The finite set of edges incident to `v`. -/
def incFinset (lft rgt : E → V) (v : V) : Finset E :=
  univ.filter (fun e => lft e = v ∨ rgt e = v)

theorem mem_incFinset (lft rgt : E → V) (e : E) (v : V) :
    e ∈ incFinset lft rgt v ↔ lft e = v ∨ rgt e = v := by
  simp [incFinset]

/-- The total weight of the edges incident to `v`.  This is the source's
`A = ∑_{e ∈ E^→_o} J_e`, which is `1` under the normalisation of `[75]`; it is transcribed
here as a genuine real number, not assumed to be `1`. -/
def weightAt (lft rgt : E → V) (J : E → ℝ) (v : V) : ℝ :=
  ∑ e ∈ incFinset lft rgt v, J e

theorem weightAt_nonneg {lft rgt : E → V} {J : E → ℝ} (hJ : ∀ e, 0 ≤ J e) (v : V) :
    0 ≤ weightAt lft rgt J v :=
  sum_nonneg fun e _ => hJ e

end Weights

/-! ### The cluster of the root -/

section Cluster

variable [Fintype V]

/-- The cluster of `root` in the open graph, as a finite set. -/
noncomputable def clusterF (lft rgt : E → V) (ω : E → Bool) (root : V) : Finset V := by
  classical
  exact univ.filter (fun v => Reach lft rgt ω root v)

theorem mem_clusterF (lft rgt : E → V) (ω : E → Bool) (root v : V) :
    v ∈ clusterF lft rgt ω root ↔ Reach lft rgt ω root v := by
  classical
  simp [clusterF]

theorem root_mem_clusterF (lft rgt : E → V) (ω : E → Bool) (root : V) :
    root ∈ clusterF lft rgt ω root := by
  rw [mem_clusterF]
  exact reach_refl lft rgt ω root

end Cluster

/-- State of the exploration: the discovered vertices and the queried edges. -/
structure State (V E : Type*) where
  /-- Vertices discovered so far. -/
  disc : Finset V
  /-- Edges queried so far. -/
  quer : Finset E

/-! ### The exploration dynamics -/

section Explore

variable [Fintype E] [DecidableEq V] [DecidableEq E]

/-- The candidate edges: incident to the discovered set, not yet queried. -/
def cand (lft rgt : E → V) (st : State V E) : Finset E :=
  univ.filter (fun e => (lft e ∈ st.disc ∨ rgt e ∈ st.disc) ∧ e ∉ st.quer)

theorem mem_cand {lft rgt : E → V} {st : State V E} {e : E} :
    e ∈ cand lft rgt st ↔ (lft e ∈ st.disc ∨ rgt e ∈ st.disc) ∧ e ∉ st.quer := by
  simp [cand]

/-- One exploration step: if the discovered set already has `n` vertices, or no candidate
edge remains, the state does not change; otherwise one candidate edge is queried, and if it
is open its far endpoint is discovered. -/
noncomputable def step (lft rgt : E → V) (n : ℕ) (ω : E → Bool) (st : State V E) :
    State V E :=
  if n ≤ st.disc.card then st
  else if h : (cand lft rgt st).Nonempty then
    if ω h.choose = true then
      ⟨insert (farS lft rgt st.disc h.choose) st.disc, insert h.choose st.quer⟩
    else ⟨st.disc, insert h.choose st.quer⟩
  else st

theorem step_of_lt {lft rgt : E → V} {n : ℕ} {ω : E → Bool} {st : State V E}
    (h : n ≤ st.disc.card) : step lft rgt n ω st = st := by
  unfold step
  rw [ite_eq_left h]

theorem step_of_empty {lft rgt : E → V} {n : ℕ} {ω : E → Bool} {st : State V E}
    (hbig : ¬ n ≤ st.disc.card) (hne : ¬ (cand lft rgt st).Nonempty) :
    step lft rgt n ω st = st := by
  unfold step
  rw [ite_eq_right hbig, dite_eq_right hne]

theorem step_of_open {lft rgt : E → V} {n : ℕ} {ω : E → Bool} {st : State V E}
    (hbig : ¬ n ≤ st.disc.card) (hne : (cand lft rgt st).Nonempty) (hop : ω hne.choose = true) :
    step lft rgt n ω st =
      ⟨insert (farS lft rgt st.disc hne.choose) st.disc, insert hne.choose st.quer⟩ := by
  unfold step
  rw [ite_eq_right hbig, dite_eq_left hne, ite_eq_left hop]

theorem step_of_closed {lft rgt : E → V} {n : ℕ} {ω : E → Bool} {st : State V E}
    (hbig : ¬ n ≤ st.disc.card) (hne : (cand lft rgt st).Nonempty)
    (hop : ¬ ω hne.choose = true) :
    step lft rgt n ω st = ⟨st.disc, insert hne.choose st.quer⟩ := by
  unfold step
  rw [ite_eq_right hbig, dite_eq_left hne, ite_eq_right hop]

/-- The exploration state after `k` steps, started from the root. -/
noncomputable def state (lft rgt : E → V) (n : ℕ) (ω : E → Bool) (root : V) :
    ℕ → State V E
  | 0 => ⟨{root}, ∅⟩
  | k + 1 => step lft rgt n ω (state lft rgt n ω root k)

theorem state_zero (lft rgt : E → V) (n : ℕ) (ω : E → Bool) (root : V) :
    state lft rgt n ω root 0 = ⟨{root}, ∅⟩ := rfl

theorem state_succ (lft rgt : E → V) (n : ℕ) (ω : E → Bool) (root : V) (k : ℕ) :
    state lft rgt n ω root (k + 1) = step lft rgt n ω (state lft rgt n ω root k) := rfl

/-- The discovered vertices after `k` steps. -/
noncomputable def disc (lft rgt : E → V) (n : ℕ) (ω : E → Bool) (root : V) (k : ℕ) :
    Finset V :=
  (state lft rgt n ω root k).disc

/-- The queried edges after `k` steps. -/
noncomputable def quer (lft rgt : E → V) (n : ℕ) (ω : E → Bool) (root : V) (k : ℕ) :
    Finset E :=
  (state lft rgt n ω root k).quer

end Explore

/-! ### The invariants of the exploration -/

/-- The four invariants maintained by the exploration: the discovered set has at most `n`
vertices, it is contained in the open cluster of the root, every queried edge is incident to
the discovered set, and every queried edge that is open has both endpoints discovered. -/
def InvS (lft rgt : E → V) (n : ℕ) (ω : E → Bool) (root : V) (S : Finset V) (Q : Finset E) :
    Prop :=
  S.card ≤ n ∧
    (∀ v ∈ S, Reach lft rgt ω root v) ∧
    (∀ e ∈ Q, lft e ∈ S ∨ rgt e ∈ S) ∧
    (∀ e ∈ Q, ω e = true → lft e ∈ S ∧ rgt e ∈ S)

/-- The invariant on the exploration state. -/
def Inv (lft rgt : E → V) (n : ℕ) (ω : E → Bool) (root : V) (st : State V E) : Prop :=
  InvS lft rgt n ω root st.disc st.quer

theorem invS_open {lft rgt : E → V} {n : ℕ} {ω : E → Bool} {root : V} {S : Finset V}
    {Q : Finset E} [DecidableEq V] [DecidableEq E] (h : InvS lft rgt n ω root S Q) {e : E}
    (hlt : S.card < n)
    (hincid : lft e ∈ S ∨ rgt e ∈ S) (hopen : ω e = true) :
    InvS lft rgt n ω root (insert (farS lft rgt S e) S) (insert e Q) := by
  obtain ⟨hcard, hreach, hinc, hclos⟩ := h
  have hspec := mem_insert_farS (lft := lft) (rgt := rgt) (S := S) hincid
  refine ⟨?_, ?_, ?_, ?_⟩
  · by_cases hmem : farS lft rgt S e ∈ S
    · rw [card_insert_of_mem hmem]; exact hcard
    · rw [card_insert_of_notMem hmem]; omega
  · intro v hv
    rcases mem_insert.mp hv with hv' | hv'
    · rw [hv']
      exact reach_farS (lft := lft) (rgt := rgt) hreach hincid hopen
    · exact hreach v hv'
  · intro e' he'
    rcases mem_insert.mp he' with he'' | he''
    · rw [he'']; exact Or.inl hspec.1
    · rcases hinc e' he'' with hh | hh
      · exact Or.inl (mem_insert_of_mem hh)
      · exact Or.inr (mem_insert_of_mem hh)
  · intro e' he' hop
    rcases mem_insert.mp he' with he'' | he''
    · rw [he'']; exact hspec
    · obtain ⟨h1, h2⟩ := hclos e' he'' hop
      exact ⟨mem_insert_of_mem h1, mem_insert_of_mem h2⟩

theorem invS_closed {lft rgt : E → V} {n : ℕ} {ω : E → Bool} {root : V} {S : Finset V}
    {Q : Finset E} [DecidableEq E] (h : InvS lft rgt n ω root S Q) {e : E}
    (hincid : lft e ∈ S ∨ rgt e ∈ S) (hclosed : ω e = false) :
    InvS lft rgt n ω root S (insert e Q) := by
  obtain ⟨hcard, hreach, hinc, hclos⟩ := h
  refine ⟨hcard, hreach, ?_, ?_⟩
  · intro e' he'
    rcases mem_insert.mp he' with he'' | he''
    · rw [he'']; exact hincid
    · exact hinc e' he''
  · intro e' he' hop
    rcases mem_insert.mp he' with he'' | he''
    · rw [he''] at hop
      rw [hop] at hclosed
      exact absurd hclosed (by simp)
    · exact hclos e' he'' hop

theorem inv_init {lft rgt : E → V} {n : ℕ} {ω : E → Bool} {root : V}
    (hn : 1 ≤ n) : Inv lft rgt n ω root ⟨{root}, ∅⟩ := by
  refine ⟨?_, ?_, ?_, ?_⟩
  · simpa using hn
  · intro v hv
    rw [mem_singleton] at hv
    simpa [hv] using reach_refl lft rgt ω root
  · intro e he
    exact absurd he (by simp)
  · intro e he
    exact absurd he (by simp)

/-! ### The invariant along the trajectory -/

section Trajectory

variable [Fintype E] [DecidableEq V] [DecidableEq E]

theorem inv_step {lft rgt : E → V} {n : ℕ} {ω : E → Bool} {root : V} {st : State V E}
    (h : Inv lft rgt n ω root st) : Inv lft rgt n ω root (step lft rgt n ω st) := by
  obtain ⟨hcard, hreach, hinc, hclos⟩ := h
  have hst : InvS lft rgt n ω root st.disc st.quer := ⟨hcard, hreach, hinc, hclos⟩
  by_cases hbig : n ≤ st.disc.card
  · rw [step_of_lt hbig]
    exact hst
  · by_cases hne : (cand lft rgt st).Nonempty
    · have hincid : lft hne.choose ∈ st.disc ∨ rgt hne.choose ∈ st.disc :=
        (mem_cand.mp hne.choose_spec).1
      by_cases hop : ω hne.choose = true
      · have hstep : step lft rgt n ω st =
            ⟨insert (farS lft rgt st.disc hne.choose) st.disc, insert hne.choose st.quer⟩ := by
          unfold step
          rw [ite_eq_right hbig, dite_eq_left hne, ite_eq_left hop]
        rw [hstep]
        exact invS_open hst (by omega) hincid hop
      · have hstep : step lft rgt n ω st = ⟨st.disc, insert hne.choose st.quer⟩ := by
          unfold step
          rw [ite_eq_right hbig, dite_eq_left hne, ite_eq_right hop]
        rw [hstep]
        exact invS_closed hst hincid (by simpa using hop)
    · have hstep : step lft rgt n ω st = st := by
        unfold step
        rw [ite_eq_right hbig, dite_eq_right hne]
      rw [hstep]
      exact hst

theorem inv_state {lft rgt : E → V} {n : ℕ} {ω : E → Bool} {root : V} (hn : 1 ≤ n)
    (k : ℕ) : Inv lft rgt n ω root (state lft rgt n ω root k) := by
  induction k with
  | zero => exact inv_init hn
  | succ k ih =>
    rw [state_succ]
    exact inv_step ih

theorem disc_card_le {lft rgt : E → V} {n : ℕ} {ω : E → Bool} {root : V} (hn : 1 ≤ n)
    (k : ℕ) : (disc lft rgt n ω root k).card ≤ n :=
  (inv_state hn k).1

theorem disc_reach {lft rgt : E → V} {n : ℕ} {ω : E → Bool} {root : V} (hn : 1 ≤ n)
    (k : ℕ) : ∀ v ∈ disc lft rgt n ω root k, Reach lft rgt ω root v :=
  (inv_state hn k).2.1

theorem quer_incident {lft rgt : E → V} {n : ℕ} {ω : E → Bool} {root : V} (hn : 1 ≤ n)
    (k : ℕ) : ∀ e ∈ quer lft rgt n ω root k,
      lft e ∈ disc lft rgt n ω root k ∨ rgt e ∈ disc lft rgt n ω root k :=
  (inv_state hn k).2.2.1

theorem quer_open_discovered {lft rgt : E → V} {n : ℕ} {ω : E → Bool} {root : V}
    (hn : 1 ≤ n) (k : ℕ) : ∀ e ∈ quer lft rgt n ω root k, ω e = true →
      lft e ∈ disc lft rgt n ω root k ∧ rgt e ∈ disc lft rgt n ω root k :=
  (inv_state hn k).2.2.2

end Trajectory

section ClusterSubset

variable [Fintype V] [Fintype E] [DecidableEq V] [DecidableEq E]

theorem disc_subset_cluster {lft rgt : E → V} {n : ℕ} {ω : E → Bool} {root : V}
    (hn : 1 ≤ n) (k : ℕ) : disc lft rgt n ω root k ⊆ clusterF lft rgt ω root := by
  intro v hv
  rw [mem_clusterF]
  exact disc_reach hn k v hv

end ClusterSubset
/-! ## Part II: the revealment budget -/

section Charge

variable [Fintype E] [DecidableEq V]

/-- **Double counting.**  Each edge of `Q` has an endpoint in `S`, and the incident weights of
the vertices of `S` count every such edge with weight `J e` at least once, so the total weight
of `Q` is at most the total incident weight of `S`. -/
theorem sum_inc_le {lft rgt : E → V} {J : E → ℝ} {S : Finset V} {Q : Finset E}
    (hJ : ∀ e, 0 ≤ J e) (hinc : ∀ e ∈ Q, lft e ∈ S ∨ rgt e ∈ S) :
    ∑ e ∈ Q, J e ≤ ∑ v ∈ S, weightAt lft rgt J v := by
  classical
  have hincfun : ∀ e : E, (∑ v ∈ S, (if lft e = v ∨ rgt e = v then J e else 0))
      = ((S.filter (fun v => lft e = v ∨ rgt e = v)).card : ℝ) * J e := by
    intro e
    have hpt : ∀ v : V, (if lft e = v ∨ rgt e = v then J e else 0)
        = (if lft e = v ∨ rgt e = v then (1 : ℝ) else 0) * J e := by
      intro v
      by_cases h : (lft e = v ∨ rgt e = v)
      · rw [ite_eq_left h, ite_eq_left h, one_mul]
      · rw [ite_eq_right h, ite_eq_right h, zero_mul]
    rw [sum_congr rfl fun v _ => hpt v, ← sum_mul, sum_boole]
  have hsum : ∑ v ∈ S, weightAt lft rgt J v
      = ∑ e : E, ∑ v ∈ S, (if lft e = v ∨ rgt e = v then J e else 0) := by
    rw [show ∑ v ∈ S, weightAt lft rgt J v
        = ∑ v ∈ S, ∑ e : E, (if lft e = v ∨ rgt e = v then J e else 0) from
      sum_congr rfl fun v _ => by rw [weightAt, incFinset, sum_filter]]
    exact sum_comm
  have hnonneg : ∀ e : E, ∀ v ∈ S,
      (0 : ℝ) ≤ (if lft e = v ∨ rgt e = v then J e else 0) := by
    intro e v _
    by_cases h : (lft e = v ∨ rgt e = v)
    · rw [ite_eq_left h]; exact hJ e
    · rw [ite_eq_right h]
  have hterm : ∀ e ∈ Q, J e ≤ ∑ v ∈ S, (if lft e = v ∨ rgt e = v then J e else 0) := by
    intro e he
    rcases hinc e he with h | h
    · calc J e = (if lft e = lft e ∨ rgt e = lft e then J e else 0) := by simp
        _ ≤ ∑ v ∈ S, (if lft e = v ∨ rgt e = v then J e else 0) :=
            single_le_sum (s := S) (f := fun v => if lft e = v ∨ rgt e = v then J e else 0)
              (hnonneg e) h
    · calc J e = (if lft e = rgt e ∨ rgt e = rgt e then J e else 0) := by simp
        _ ≤ ∑ v ∈ S, (if lft e = v ∨ rgt e = v then J e else 0) :=
            single_le_sum (s := S) (f := fun v => if lft e = v ∨ rgt e = v then J e else 0)
              (hnonneg e) h
  calc ∑ e ∈ Q, J e
      ≤ ∑ e ∈ Q, ∑ v ∈ S, (if lft e = v ∨ rgt e = v then J e else 0) := sum_le_sum hterm
    _ ≤ ∑ e : E, ∑ v ∈ S, (if lft e = v ∨ rgt e = v then J e else 0) :=
        sum_le_sum_of_subset_of_nonneg (subset_univ Q) (fun e _ _ => sum_nonneg (hnonneg e))
    _ = ∑ v ∈ S, weightAt lft rgt J v := hsum.symm

/-- **The charging bound**: if every vertex has total incident edge weight `A`, then the
`J`-weight of a set of edges each incident to `S` is at most `A · #S`. -/
theorem charge {lft rgt : E → V} {J : E → ℝ} {A : ℝ} (hJ : ∀ e, 0 ≤ J e)
    (hA : ∀ v, weightAt lft rgt J v = A) {S : Finset V} {Q : Finset E}
    (hinc : ∀ e ∈ Q, lft e ∈ S ∨ rgt e ∈ S) : ∑ e ∈ Q, J e ≤ A * S.card := by
  have h1 : ∑ v ∈ S, weightAt lft rgt J v = A * S.card := by
    rw [sum_congr rfl fun v _ => hA v, sum_const, nsmul_eq_mul, mul_comm]
  calc ∑ e ∈ Q, J e ≤ ∑ v ∈ S, weightAt lft rgt J v := sum_inc_le hJ hinc
    _ = A * S.card := h1

end Charge

/-! ### The tail-sum identity -/

/-- **`E[min X n] = ∑_{k=1}^{n} P(X ≥ k)`** for a finite probability weight: the expected
number of integers `k ∈ {1, …, n}` with `k ≤ X`. -/
theorem sum_min_eq_sum_tail {Ω : Type*} [Fintype Ω] (w : Ω → ℝ) (X : Ω → ℕ) (n : ℕ) :
    ∑ ω, w ω * ((min (X ω) n : ℕ) : ℝ)
      = ∑ j ∈ Finset.Icc 1 n, ∑ ω, (if j ≤ X ω then w ω else 0) := by
  classical
  rw [show (∑ j ∈ Finset.Icc 1 n, ∑ ω, (if j ≤ X ω then w ω else 0))
      = ∑ ω, ∑ j ∈ Finset.Icc 1 n, (if j ≤ X ω then w ω else 0) from sum_comm]
  refine sum_congr rfl fun ω _ => ?_
  have hpt : ∀ j : ℕ, (if j ≤ X ω then w ω else 0)
      = w ω * (if j ≤ X ω then (1 : ℝ) else 0) := by
    intro j
    by_cases h : j ≤ X ω
    · rw [ite_eq_left h, ite_eq_left h, mul_one]
    · rw [ite_eq_right h, ite_eq_right h, mul_zero]
  have hfil : (Finset.Icc 1 n).filter (fun j => j ≤ X ω) = Finset.Icc 1 (min (X ω) n) := by
    ext j
    simp only [mem_filter, mem_Icc, Nat.le_min]
    omega
  have hcard : ((Finset.Icc 1 (min (X ω) n)).card : ℝ) = ((min (X ω) n : ℕ) : ℝ) := by
    rw [Nat.card_Icc]
    simp
  calc w ω * ((min (X ω) n : ℕ) : ℝ)
      = w ω * ((Finset.Icc 1 (min (X ω) n)).card : ℝ) := by rw [hcard]
    _ = w ω * (((Finset.Icc 1 n).filter (fun j => j ≤ X ω)).card : ℝ) := by rw [hfil]
    _ = w ω * (∑ j ∈ Finset.Icc 1 n, (if j ≤ X ω then (1 : ℝ) else 0)) := by
        rw [sum_boole]
    _ = ∑ j ∈ Finset.Icc 1 n, w ω * (if j ≤ X ω then (1 : ℝ) else 0) := mul_sum _ _ _
    _ = ∑ j ∈ Finset.Icc 1 n, (if j ≤ X ω then w ω else 0) :=
        sum_congr rfl fun j _ => (hpt j).symm

/-! ### Fubini for the queried edge weight -/

section Fubini

variable [Fintype E] [DecidableEq E]

/-- **Fubini over a configuration-dependent edge set**: the expectation of the total weight of
the queried edges is the `J`-weighted sum of the individual revealment probabilities. -/
theorem sum_weight_mul_setsum {Ω : Type*} [Fintype Ω] (w : Ω → ℝ) (J : E → ℝ)
    (Qf : Ω → Finset E) :
    ∑ ω, w ω * (∑ e ∈ Qf ω, J e)
      = ∑ e, J e * ∑ ω, (if e ∈ Qf ω then w ω else 0) := by
  classical
  have hsplit : ∀ ω : Ω, w ω * (∑ e ∈ Qf ω, J e) = ∑ e ∈ Qf ω, w ω * J e := by
    intro ω
    rw [mul_sum]
  have hfilter : ∀ ω : Ω, (∑ e ∈ Qf ω, w ω * J e)
      = ∑ e : E, (if e ∈ Qf ω then w ω * J e else 0) := by
    intro ω
    rw [← sum_filter]
    congr 1
    ext e
    simp
  have hinner : ∀ e : E, (∑ ω : Ω, (if e ∈ Qf ω then w ω * J e else 0))
      = J e * ∑ ω : Ω, (if e ∈ Qf ω then w ω else 0) := by
    intro e
    have hpt : ∀ ω : Ω, (if e ∈ Qf ω then w ω * J e else 0)
        = (if e ∈ Qf ω then w ω else 0) * J e := by
      intro ω
      by_cases h : e ∈ Qf ω
      · rw [ite_eq_left h, ite_eq_left h]
      · rw [ite_eq_right h, ite_eq_right h, zero_mul]
    calc ∑ ω : Ω, (if e ∈ Qf ω then w ω * J e else 0)
        = ∑ ω : Ω, (if e ∈ Qf ω then w ω else 0) * J e := sum_congr rfl fun ω _ => hpt ω
      _ = (∑ ω : Ω, (if e ∈ Qf ω then w ω else 0)) * J e := (sum_mul _ _ _).symm
      _ = J e * ∑ ω : Ω, (if e ∈ Qf ω then w ω else 0) := mul_comm _ _
  calc ∑ ω, w ω * (∑ e ∈ Qf ω, J e)
      = ∑ ω, ∑ e : E, (if e ∈ Qf ω then w ω * J e else 0) := by
        refine sum_congr rfl fun ω _ => ?_
        rw [hsplit ω, hfilter ω]
    _ = ∑ e : E, ∑ ω, (if e ∈ Qf ω then w ω * J e else 0) := sum_comm
    _ = ∑ e, J e * ∑ ω, (if e ∈ Qf ω then w ω else 0) := sum_congr rfl fun e _ => hinner e

end Fubini

/-! ### Nonnegativity of the product weight -/

section WeightNonneg

variable [Fintype E]

/-- Every configuration has nonnegative product weight. -/
theorem confWeight_nonneg {J : E → ℝ} {β : ℝ} (hJ : ∀ e, 0 < J e) (hβ : 0 < β)
    (ω : E → Bool) : 0 ≤ confWeight J β ω := by
  classical
  exact prod_nonneg fun e _ => (bem_pos (J := J) (β := β) hJ hβ e (ω e)).le

/-- Every event has nonnegative probability under the product weight. -/
theorem evProb_nonneg {J : E → ℝ} {β : ℝ} [DecidableEq E] (hJ : ∀ e, 0 < J e)
    (hβ : 0 < β) (A : Set (E → Bool)) : 0 ≤ evProb J β A := by
  classical
  rw [evProb]
  refine sum_nonneg fun ω _ => ?_
  exact confWeight_nonneg hJ hβ ω

end WeightNonneg

/-! ### The revealment budget of the exploration -/

section Budget

variable [Fintype V] [Fintype E] [DecidableEq V] [DecidableEq E]

/-- The revealment probability of the edge `e`: the probability, under the product Bernoulli
law of `LRP.confWeight J β` at intensity `β`, that the exploration has queried `e` by time
`k`. -/
noncomputable def Rev (lft rgt : E → V) (J : E → ℝ) (β : ℝ) (n : ℕ) (root : V) (k : ℕ)
    (e : E) : ℝ :=
  evProb J β {ω : E → Bool | e ∈ quer lft rgt n ω root k}

/-- The pointwise charging bound at the actual exploration: the total weight of the queried
edges never exceeds `A` times the number of discovered vertices, which is at most
`A` times `|K| ∧ n`. -/
theorem quer_sum_le_min {lft rgt : E → V} {J : E → ℝ} {A : ℝ} (hJ : ∀ e, 0 < J e)
    (hA : ∀ v, weightAt lft rgt J v = A) {n : ℕ} (hn : 1 ≤ n) (ω : E → Bool) (root : V)
    (k : ℕ) :
    ∑ e ∈ quer lft rgt n ω root k, J e
      ≤ A * ((min (clusterF lft rgt ω root).card n : ℕ) : ℝ) := by
  have hJ0 : ∀ e, 0 ≤ J e := fun e => (hJ e).le
  have hA0 : 0 ≤ A := by
    rw [← hA root]
    exact weightAt_nonneg hJ0 root
  have h1 : ∑ e ∈ quer lft rgt n ω root k, J e ≤ A * (disc lft rgt n ω root k).card :=
    charge hJ0 hA (quer_incident hn k)
  have h2 : (disc lft rgt n ω root k).card ≤ (clusterF lft rgt ω root).card :=
    card_le_card (disc_subset_cluster hn k)
  have h3 : (disc lft rgt n ω root k).card ≤ min (clusterF lft rgt ω root).card n :=
    Nat.le_min.mpr ⟨h2, disc_card_le hn k⟩
  have h4 : ((disc lft rgt n ω root k).card : ℝ)
      ≤ ((min (clusterF lft rgt ω root).card n : ℕ) : ℝ) := by
    exact_mod_cast h3
  exact h1.trans (mul_le_mul_of_nonneg_left h4 hA0)

/-- **The revealment budget of the source's cluster exploration.**  For positive edge weights
`J`, positive intensity `β`, vertices all of whose incident edge weight is `A`, and `n ≥ 1`,

`∑_e J_e · Rev_β(T,e) ≤ A · ∑_{k=1}^{n} P_β(|K| ≥ k) = A · E_β[|K| ∧ n]`.

The right-hand side is the source's `∑_{k=1}^n ℙ_{β₁}(|K| ≥ k)` multiplied by the incident
edge-weight sum `A`, which is `1` under the normalisation `∑_{e ∈ E^→_o} J_e = 1`. -/
theorem revealment_budget {lft rgt : E → V} {J : E → ℝ} {A β : ℝ} (hJ : ∀ e, 0 < J e)
    (hβ : 0 < β) (hA : ∀ v, weightAt lft rgt J v = A) {n : ℕ} (hn : 1 ≤ n) (root : V)
    (k : ℕ) :
    ∑ e, J e * Rev lft rgt J β n root k e
      ≤ A * ∑ j ∈ Finset.Icc 1 n,
          evProb J β {ω : E → Bool | j ≤ (clusterF lft rgt ω root).card} := by
  classical
  have hmin := quer_sum_le_min (lft := lft) (rgt := rgt) (J := J) (A := A) hJ hA hn
  have hRev : ∀ e : E, Rev lft rgt J β n root k e
      = ∑ ω : E → Bool,
          (if e ∈ quer lft rgt n ω root k then confWeight J β ω else 0) := by
    intro e
    rw [Rev, evProb, sum_filter]
    refine sum_congr rfl fun ω _ => ?_
    by_cases h : e ∈ quer lft rgt n ω root k <;> simp [h]
  have hfib := sum_weight_mul_setsum (confWeight J β) J
    (fun ω : E → Bool => quer lft rgt n ω root k)
  have h1 : ∑ e, J e * Rev lft rgt J β n root k e
      = ∑ ω : E → Bool, confWeight J β ω * (∑ e ∈ quer lft rgt n ω root k, J e) := by
    rw [hfib]
    exact sum_congr rfl fun e _ => by rw [hRev e]
  rw [h1]
  calc ∑ ω : E → Bool, confWeight J β ω * (∑ e ∈ quer lft rgt n ω root k, J e)
      ≤ ∑ ω : E → Bool, confWeight J β ω
          * (A * ((min (clusterF lft rgt ω root).card n : ℕ) : ℝ)) :=
        sum_le_sum fun ω _ =>
          mul_le_mul_of_nonneg_left (hmin ω root k) (confWeight_nonneg hJ hβ ω)
    _ = A * ∑ ω : E → Bool,
          confWeight J β ω * ((min (clusterF lft rgt ω root).card n : ℕ) : ℝ) := by
        rw [mul_sum]
        exact sum_congr rfl fun ω _ => by ring
    _ = A * ∑ j ∈ Finset.Icc 1 n, ∑ ω : E → Bool,
          (if j ≤ (clusterF lft rgt ω root).card then confWeight J β ω else 0) := by
        rw [sum_min_eq_sum_tail (fun ω => confWeight J β ω)
          (fun ω => (clusterF lft rgt ω root).card) n]
    _ = A * ∑ j ∈ Finset.Icc 1 n,
          evProb J β {ω : E → Bool | j ≤ (clusterF lft rgt ω root).card} := by
        refine congrArg (fun x => A * x) (sum_congr rfl fun j _ => ?_)
        rw [evProb, sum_filter]
        refine sum_congr rfl fun ω _ => ?_
        by_cases h : j ≤ (clusterF lft rgt ω root).card <;> simp [h]

omit [Fintype V] in
/-- **The inhomogeneous form of the budget.**  Homogeneity of the incident edge weights is
used only to turn `∑_{v ∈ disc} weightAt v` into `A · #disc`; without it the exact statement is
`∑_e J_e · Rev_β(T,e) ≤ E_β[∑_{v ∈ disc} (∑_{e ∋ v} J_e)]`. -/
theorem revealment_budget_inhom {lft rgt : E → V} {J : E → ℝ} {β : ℝ} (hJ : ∀ e, 0 < J e)
    (hβ : 0 < β) {n : ℕ} (hn : 1 ≤ n) (root : V) (k : ℕ) :
    ∑ e, J e * Rev lft rgt J β n root k e
      ≤ ∑ ω : E → Bool, confWeight J β ω
          * ∑ v ∈ disc lft rgt n ω root k, weightAt lft rgt J v := by
  classical
  have hJ0 : ∀ e, 0 ≤ J e := fun e => (hJ e).le
  have hpt : ∀ ω : E → Bool, ∑ e ∈ quer lft rgt n ω root k, J e
      ≤ ∑ v ∈ disc lft rgt n ω root k, weightAt lft rgt J v :=
    fun ω => sum_inc_le hJ0 (quer_incident hn k)
  have hRev : ∀ e : E, Rev lft rgt J β n root k e
      = ∑ ω : E → Bool,
          (if e ∈ quer lft rgt n ω root k then confWeight J β ω else 0) := by
    intro e
    rw [Rev, evProb, sum_filter]
    refine sum_congr rfl fun ω _ => ?_
    by_cases h : e ∈ quer lft rgt n ω root k <;> simp [h]
  have hfib := sum_weight_mul_setsum (confWeight J β) J
    (fun ω : E → Bool => quer lft rgt n ω root k)
  have h1 : ∑ e, J e * Rev lft rgt J β n root k e
      = ∑ ω : E → Bool, confWeight J β ω * (∑ e ∈ quer lft rgt n ω root k, J e) := by
    rw [hfib]
    exact sum_congr rfl fun e _ => by rw [hRev e]
  rw [h1]
  exact sum_le_sum fun ω _ =>
    mul_le_mul_of_nonneg_left (hpt ω) (confWeight_nonneg hJ hβ ω)

/-- The source's normalised form: if every vertex has incident edge weight `1`
(`∑_{e ∈ E^→_o} J_e = 1`), then
`∑_e J_e · Rev_β(T,e) ≤ ∑_{k=1}^{n} P_β(|K| ≥ k)`. -/
theorem revealment_budget_normalised {lft rgt : E → V} {J : E → ℝ} {β : ℝ}
    (hJ : ∀ e, 0 < J e) (hβ : 0 < β) (hA : ∀ v, weightAt lft rgt J v = 1) {n : ℕ}
    (hn : 1 ≤ n) (root : V) (k : ℕ) :
    ∑ e, J e * Rev lft rgt J β n root k e
      ≤ ∑ j ∈ Finset.Icc 1 n,
          evProb J β {ω : E → Bool | j ≤ (clusterF lft rgt ω root).card} := by
  simpa using revealment_budget (lft := lft) (rgt := rgt) (J := J) (A := 1) hJ hβ hA hn root k

end Budget

/-! ## Part III: the exploration stops at `|K| ∧ n`

The source's decision tree "stop[s] if and when it first finds `n` vertices in `K`".  This part
shows that the exploration of Part I, run for `|E|` steps, has indeed stopped: either the
discovered set already has `n` vertices, or every edge incident to it has been queried; in the
second case the discovered set is the whole cluster of the root.  Consequently the discovered
set has exactly `|K| ∧ n` vertices at that time, which is the set of size at most `n` in the
source's argument.
-/

/-- If the discovered set is closed under open edges, then it contains the whole cluster. -/
theorem mem_of_reach_closed {lft rgt : E → V} {ω : E → Bool} {S : Finset V} {root : V}
    (hroot : root ∈ S) (hstep : ∀ x y : V, x ∈ S → Adj lft rgt ω x y → y ∈ S) {v : V}
    (h : Reach lft rgt ω root v) : v ∈ S := by
  unfold Reach at h
  induction h with
  | refl => exact hroot
  | tail _ hbc ih => exact hstep _ _ ih hbc

section Stopping

variable [Fintype E] [DecidableEq V] [DecidableEq E]

/-- The exploration has stopped at time `k`: either the discovered set already has `n`
vertices, or every edge incident to it has already been queried. -/
def Stalled (lft rgt : E → V) (n : ℕ) (ω : E → Bool) (root : V) (k : ℕ) : Prop :=
  n ≤ (state lft rgt n ω root k).disc.card ∨ cand lft rgt (state lft rgt n ω root k) = ∅

theorem not_stalled_iff {lft rgt : E → V} {n : ℕ} {ω : E → Bool} {root : V} {k : ℕ} :
    ¬ Stalled lft rgt n ω root k ↔
      ¬ n ≤ (state lft rgt n ω root k).disc.card ∧
        (cand lft rgt (state lft rgt n ω root k)).Nonempty := by
  unfold Stalled
  constructor
  · intro h
    refine ⟨fun h1 => h (Or.inl h1), ?_⟩
    by_contra h2
    exact h (Or.inr (by by_contra hne; exact h2 (nonempty_iff_ne_empty.mpr hne)))
  · rintro ⟨h1, h2⟩ (h | h)
    · exact h1 h
    · rw [h] at h2
      simp at h2

/-- A stopped exploration does not change its state. -/
theorem stalled_step {lft rgt : E → V} {n : ℕ} {ω : E → Bool} {root : V} {k : ℕ}
    (h : Stalled lft rgt n ω root k) :
    state lft rgt n ω root (k + 1) = state lft rgt n ω root k := by
  rcases h with hbig | hemp
  · rw [state_succ]
    exact step_of_lt hbig
  · by_cases hbig : n ≤ (state lft rgt n ω root k).disc.card
    · rw [state_succ]
      exact step_of_lt hbig
    · rw [state_succ]
      unfold step
      rw [ite_eq_right hbig]
      rw [dite_eq_right]
      intro hne
      rw [hemp] at hne
      simp at hne

/-- After the exploration has stopped, its state is frozen. -/
theorem state_eq_of_stalled {lft rgt : E → V} {n : ℕ} {ω : E → Bool} {root : V} {j : ℕ}
    (h : Stalled lft rgt n ω root j) :
    ∀ k, j ≤ k → state lft rgt n ω root k = state lft rgt n ω root j := by
  intro k hk
  induction k, hk using Nat.le_induction with
  | base => rfl
  | succ k hk ih =>
    rw [state_succ, ih]
    exact stalled_step h

/-- Stall is a property of the state, so it propagates forwards. -/
theorem stalled_mono {lft rgt : E → V} {n : ℕ} {ω : E → Bool} {root : V} {j k : ℕ}
    (hjk : j ≤ k) (h : Stalled lft rgt n ω root j) : Stalled lft rgt n ω root k := by
  unfold Stalled at *
  rw [state_eq_of_stalled h k hjk]
  exact h

/-- A non-stopped step queries one new edge. -/
theorem quer_card_succ {lft rgt : E → V} {n : ℕ} {ω : E → Bool} {root : V} {k : ℕ}
    (h : ¬ Stalled lft rgt n ω root k) :
    (state lft rgt n ω root (k + 1)).quer.card
      = (state lft rgt n ω root k).quer.card + 1 := by
  obtain ⟨hbig, hne⟩ := not_stalled_iff.mp h
  have hnotmem : hne.choose ∉ (state lft rgt n ω root k).quer := (mem_cand.mp hne.choose_spec).2
  rw [state_succ]
  unfold step
  rw [ite_eq_right hbig, dite_eq_left hne]
  split_ifs with hop
  · exact card_insert_of_notMem hnotmem
  · exact card_insert_of_notMem hnotmem

/-- **Progress**: before the exploration stops, it queries at least one new edge at each step. -/
theorem quer_card_ge (lft rgt : E → V) (n : ℕ) (ω : E → Bool) (root : V) (k : ℕ) :
    k ≤ (state lft rgt n ω root k).quer.card ∨
      ∃ j, j < k ∧ Stalled lft rgt n ω root j := by
  induction k with
  | zero => exact Or.inl (Nat.zero_le _)
  | succ k ih =>
    rcases ih with hk | ⟨j, hj, hs⟩
    · by_cases hst : Stalled lft rgt n ω root k
      · exact Or.inr ⟨k, Nat.lt_succ_self k, hst⟩
      · exact Or.inl (by rw [quer_card_succ hst]; omega)
    · exact Or.inr ⟨j, Nat.lt_trans hj (Nat.lt_succ_self k), hs⟩

/-- **The exploration has stopped after `|E|` steps**, because every step before that queries
a new edge and there are only `|E|` edges. -/
theorem stalled_at_card (lft rgt : E → V) (n : ℕ) (ω : E → Bool) (root : V) :
    Stalled lft rgt n ω root (Fintype.card E) := by
  rcases quer_card_ge lft rgt n ω root (Fintype.card E) with hk | ⟨j, hj, hs⟩
  · right
    have hle : (state lft rgt n ω root (Fintype.card E)).quer.card ≤ Fintype.card E := by
      rw [← Finset.card_univ]
      exact card_le_univ _
    have heq : (state lft rgt n ω root (Fintype.card E)).quer.card = Fintype.card E :=
      le_antisymm hle hk
    have huniv : (state lft rgt n ω root (Fintype.card E)).quer = univ :=
      eq_univ_of_card (s := (state lft rgt n ω root (Fintype.card E)).quer) heq
    ext e
    rw [cand, huniv]
    simp
  · exact stalled_mono (Nat.le_of_lt hj) hs

/-- The root is discovered at every time. -/
theorem root_mem_disc {lft rgt : E → V} {n : ℕ} {ω : E → Bool} {root : V} (k : ℕ) :
    root ∈ (state lft rgt n ω root k).disc := by
  induction k with
  | zero => exact mem_singleton_self root
  | succ k ih =>
    rw [state_succ]
    by_cases hbig : n ≤ (state lft rgt n ω root k).disc.card
    · rw [step_of_lt hbig]
      exact ih
    · by_cases hne : (cand lft rgt (state lft rgt n ω root k)).Nonempty
      · by_cases hop : ω hne.choose = true
        · rw [step_of_open hbig hne hop]
          exact mem_insert_of_mem ih
        · rw [step_of_closed hbig hne hop]
          exact ih
      · rw [step_of_empty hbig hne]
        exact ih

end Stopping

section StopCluster

variable [Fintype V] [Fintype E] [DecidableEq V] [DecidableEq E]

/-- If no candidate edge remains, the discovered set is closed under open edges, hence it is
the whole cluster. -/
theorem clusterF_subset_disc {lft rgt : E → V} {n : ℕ} {ω : E → Bool} {root : V}
    {k : ℕ} (hn : 1 ≤ n) (hemp : cand lft rgt (state lft rgt n ω root k) = ∅) :
    clusterF lft rgt ω root ⊆ (state lft rgt n ω root k).disc := by
  have hstep : ∀ x y : V, x ∈ (state lft rgt n ω root k).disc → Adj lft rgt ω x y →
      y ∈ (state lft rgt n ω root k).disc := by
    intro x y hx hadj
    obtain ⟨e, hop, hxy | hxy⟩ := hadj
    · have hinc : lft e ∈ (state lft rgt n ω root k).disc := by rw [hxy.1]; exact hx
      have hmem : e ∈ (state lft rgt n ω root k).quer := by
        by_contra hnot
        have hc : e ∈ cand lft rgt (state lft rgt n ω root k) :=
          mem_cand.mpr ⟨Or.inl hinc, hnot⟩
        rw [hemp] at hc
        exact absurd hc (by simp)
      have hboth := quer_open_discovered hn k e hmem hop
      rw [← hxy.2]
      exact hboth.2
    · have hinc : rgt e ∈ (state lft rgt n ω root k).disc := by rw [hxy.2]; exact hx
      have hmem : e ∈ (state lft rgt n ω root k).quer := by
        by_contra hnot
        have hc : e ∈ cand lft rgt (state lft rgt n ω root k) :=
          mem_cand.mpr ⟨Or.inr hinc, hnot⟩
        rw [hemp] at hc
        exact absurd hc (by simp)
      have hboth := quer_open_discovered hn k e hmem hop
      rw [← hxy.1]
      exact hboth.1
  intro v hv
  rw [mem_clusterF] at hv
  exact mem_of_reach_closed (root_mem_disc k) hstep hv

/-- **At the stopping time the discovered set has exactly `|K| ∧ n` vertices.** -/
theorem disc_card_at_card (lft rgt : E → V) (n : ℕ) (ω : E → Bool) (root : V)
    (hn : 1 ≤ n) :
    (state lft rgt n ω root (Fintype.card E)).disc.card
      = min (clusterF lft rgt ω root).card n := by
  have hst := stalled_at_card lft rgt n ω root
  have hsub := disc_subset_cluster (lft := lft) (rgt := rgt) (n := n) (ω := ω) (root := root)
    hn (Fintype.card E)
  have hcard := disc_card_le (lft := lft) (rgt := rgt) (n := n) (ω := ω) (root := root)
    hn (Fintype.card E)
  rcases hst with hbig | hemp
  · have heqn : (state lft rgt n ω root (Fintype.card E)).disc.card = n :=
      le_antisymm hcard hbig
    have hcl : n ≤ (clusterF lft rgt ω root).card := by
      rw [← heqn]
      exact card_le_card hsub
    rw [heqn, min_eq_right hcl]
  · have h2 := clusterF_subset_disc (lft := lft) (rgt := rgt) (n := n) (ω := ω) (root := root)
      (k := Fintype.card E) hn hemp
    have heqc : (state lft rgt n ω root (Fintype.card E)).disc.card
        = (clusterF lft rgt ω root).card :=
      le_antisymm (card_le_card hsub) (card_le_card h2)
    rw [heqc, min_eq_left (by rw [← heqc]; exact hcard)]

/-- **The stopped form of the revealment budget**: running the exploration for `|E|` steps,
which stops it, the budget `∑_e J_e Rev_β(T,e) ≤ A ∑_{k=1}^{n} P_β(|K| ≥ k)` holds. -/
theorem revealment_budget_stopped {lft rgt : E → V} {J : E → ℝ} {A β : ℝ}
    (hJ : ∀ e, 0 < J e)
    (hβ : 0 < β) (hA : ∀ v, weightAt lft rgt J v = A) {n : ℕ} (hn : 1 ≤ n) (root : V) :
    ∑ e, J e * Rev lft rgt J β n root (Fintype.card E) e
      ≤ A * ∑ j ∈ Finset.Icc 1 n,
          evProb J β {ω : E → Bool | j ≤ (clusterF lft rgt ω root).card} :=
  revealment_budget (lft := lft) (rgt := rgt) (J := J) (A := A) hJ hβ hA hn root
    (Fintype.card E)

end StopCluster

/-! ## Part IV: a non-vacuous example

The two-vertex graph with one edge of weight `1` satisfies the homogeneity hypothesis with
`A = 1`, the exploration queries that edge, and the probability of the event `|K| ≥ 1` is `1`,
so the budget reads `1 ≤ 1 + P_1(|K| ≥ 2)`.  This checks that the definitions compute the
source's quantities and that the constant `A` is the incident edge-weight sum.
-/

section Example

/-- The left endpoint of the single edge of the two-vertex example. -/
def exLft : Unit → Bool := fun _ => false

/-- The right endpoint of the single edge of the two-vertex example. -/
def exRgt : Unit → Bool := fun _ => true

/-- The weight of the single edge of the two-vertex example. -/
def exJ : Unit → ℝ := fun _ => 1

/-- The single incident edge has total weight `1` at both vertices. -/
theorem ex_weightAt (v : Bool) : weightAt exLft exRgt exJ v = 1 := by
  cases v <;> simp [weightAt, incFinset, exLft, exRgt, exJ]

/-- The exploration queries the only edge in its first step. -/
theorem ex_quer_one (ω : Unit → Bool) : quer exLft exRgt 2 ω false 1 = univ := by
  have hbig : ¬ 2 ≤ (state exLft exRgt 2 ω false 0).disc.card := by
    rw [state_zero]
    simp
  have hne : (cand exLft exRgt (state exLft exRgt 2 ω false 0)).Nonempty := by
    refine ⟨(), ?_⟩
    rw [state_zero]
    simp [cand, exLft]
  have hstep : (step exLft exRgt 2 ω (state exLft exRgt 2 ω false 0)).quer
      = insert hne.choose (state exLft exRgt 2 ω false 0).quer := by
    by_cases hop : ω hne.choose = true
    · rw [step_of_open hbig hne hop]
    · rw [step_of_closed hbig hne hop]
  rw [quer, state_succ, hstep]
  have hq : (state exLft exRgt 2 ω false 0).quer = ∅ := rfl
  rw [hq]
  refine eq_univ_of_forall fun e => ?_
  rw [mem_insert]
  exact Or.inl (Subsingleton.elim e hne.choose)

/-- The whole configuration space is a set of full probability. -/
theorem ex_evProb_univ (β : ℝ) : evProb exJ β (Set.univ : Set (Unit → Bool)) = 1 := by
  classical
  have h : evProb exJ β (Set.univ : Set (Unit → Bool)) = ∑ ω, confWeight exJ β ω := by
    rw [evProb]
    simp
  rw [h, sum_confWeight]

/-- The event `|K| ≥ 1` has probability `1`, since the cluster always contains the root. -/
theorem ex_tail_one (β : ℝ) :
    evProb exJ β {ω : Unit → Bool | 1 ≤ (clusterF exLft exRgt ω false).card} = 1 := by
  have hset : {ω : Unit → Bool | 1 ≤ (clusterF exLft exRgt ω false).card}
      = (Set.univ : Set (Unit → Bool)) := by
    ext ω
    exact ⟨fun _ => Set.mem_univ ω, fun _ =>
      one_le_card.mpr ⟨false, root_mem_clusterF exLft exRgt ω false⟩⟩
  rw [hset, ex_evProb_univ]

/-- The revealment probability of the single edge is `1`: the exploration always queries it. -/
theorem ex_rev_one (β : ℝ) : Rev exLft exRgt exJ β 2 false 1 () = 1 := by
  have hset : {ω : Unit → Bool | () ∈ quer exLft exRgt 2 ω false 1}
      = (Set.univ : Set (Unit → Bool)) := by
    ext ω
    simp [ex_quer_one ω]
  rw [Rev, hset, ex_evProb_univ]

/-- **The budget at the example**: the left-hand side is exactly `1` and the `k = 1` tail term
is exactly `1`, so the finite estimate contains the true inequality `1 ≤ 1 + P_1(|K| ≥ 2)`. -/
theorem revealment_example :
    ∑ e, exJ e * Rev exLft exRgt exJ 1 2 false 1 e = 1 ∧
      evProb exJ 1 {ω : Unit → Bool | 1 ≤ (clusterF exLft exRgt ω false).card} = 1 ∧
      (∑ e, exJ e * Rev exLft exRgt exJ 1 2 false 1 e
        ≤ 1 * ∑ j ∈ Finset.Icc 1 2,
            evProb exJ 1 {ω : Unit → Bool | j ≤ (clusterF exLft exRgt ω false).card}) := by
  have hsum : ∑ e, exJ e * Rev exLft exRgt exJ 1 2 false 1 e = 1 := by
    rw [Fintype.sum_unique]
    simp [exJ, ex_rev_one]
  refine ⟨hsum, ex_tail_one 1, ?_⟩
  rw [hsum, one_mul]
  have hmem : (1 : ℕ) ∈ Finset.Icc 1 2 := by simp
  have hnonneg : ∀ j ∈ Finset.Icc 1 2,
      (0 : ℝ) ≤
        evProb exJ 1 {ω : Unit → Bool | j ≤ (clusterF exLft exRgt ω false).card} :=
    fun j _ => evProb_nonneg (J := exJ) (fun _ => one_pos) one_pos _
  have hle : evProb exJ 1 {ω : Unit → Bool | 1 ≤ (clusterF exLft exRgt ω false).card}
      ≤ ∑ j ∈ Finset.Icc 1 2,
          evProb exJ 1 {ω : Unit → Bool | j ≤ (clusterF exLft exRgt ω false).card} :=
    single_le_sum hnonneg hmem
  rw [ex_tail_one 1] at hle
  simpa using hle

end Example

end Reveal
end LRP

namespace LRP
namespace Reveal

set_option linter.hashCommand false

#print axioms mem_of_reach_closed
#print axioms inv_state
#print axioms disc_subset_cluster
#print axioms sum_inc_le
#print axioms charge
#print axioms sum_min_eq_sum_tail
#print axioms sum_weight_mul_setsum
#print axioms confWeight_nonneg
#print axioms quer_sum_le_min
#print axioms revealment_budget
#print axioms revealment_budget_inhom
#print axioms revealment_budget_normalised
#print axioms stalled_at_card
#print axioms quer_card_ge
#print axioms disc_card_at_card
#print axioms revealment_budget_stopped
#print axioms evProb_nonneg
#print axioms ex_weightAt
#print axioms ex_quer_one
#print axioms ex_tail_one
#print axioms ex_rev_one
#print axioms revealment_example

end Reveal
end LRP
