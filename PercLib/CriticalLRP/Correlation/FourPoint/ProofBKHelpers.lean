/- Integrated from independently rebuilt Ultramath work.
Production base 3b6ff818cd3ac1a9cee99dcfff154a2ff4f85095.
Scratch source: ../../.ultramath/smwvp122a/m3/ProofBKHelpers.lean.
-/

module

public import PercLib.CriticalLRP.Correlation.FourPoint.ProofCover
public import PercLib.CriticalLRP.TreeGraph.ThreePoint

/-!
The three-fold BK assembly for the `p = 3`, `k = 1` case of Lemma I.4.16.

This file contains the percolation-side ingredients of that step, all proved:

* `prob_union_le` — the probability of a union is at most the sum;
* `isIncreasing_conn_and` — the joint event `{o ↔ t, w}` is increasing;
* `disjOcc3_swap` — `DisjOcc3` is symmetric in its last two arguments;
* `mem_disjOcc3_of_walks` — four walks with pairwise disjoint edge lists put the configuration in
  the three-fold disjoint occurrence of the joint cluster and the two arms (the transport of
  `HasCover` to disjoint witness sets, via `walk_restrict`);
* `pair_eq_of_triple` — unpacking the partition `{t, u, v} = {x, y, z}`: if `t = x` then the two
  arms are `y` and `z` in some order (this is where the distinctness of `x, y, z` is used).

The remaining step — assembling these into

  `P(o ↔ x,y,z) ≤ ∑_w [ P(o↔x,w)P(w↔y)P(w↔z) + P(o↔y,w)P(w↔x)P(w↔z)
                     + P(o↔z,w)P(w↔x)P(w↔y) ]`

by the union bound over `w` and over the three choices of the joint terminal — is *not* completed
here; the case analysis on which terminal is joint, together with the sum reindexing, remains.
-/
/-
The BK (van den Berg--Kesten) half of the `p = 3`, `k = 1` case of the generalized tree-graph
inequality (Lemma I.4.16 of the source).

The paper's displayed inequality (p. 44) is

  `E|K|^3 = ∑_{x,y,z} P(0 ↔ x,y,z) ≤ 3 ∑_{x,y,z,w} P(0 ↔ x,w) P(w ↔ y) P(w ↔ z)`.

The factor `3` there arises from summing the symmetric bound for a single ordered triple over the
ordered triples `(x, y, z)`.  For one ordered triple `(o, x, y, z)` the deterministic cover
(`cover_of_reachable`) says that on `{o ↔ x, y, z}` at least one of the three pairings holds, so
the union bound and the three-fold BK inequality `bk_three` give

  `P(o ↔ x,y,z) ≤ ∑_w [ P(o ↔ x,w)P(w ↔ y)P(w ↔ z)
                      + P(o ↔ y,w)P(w ↔ x)P(w ↔ z)
                      + P(o ↔ z,w)P(w ↔ x)P(w ↔ y) ]`,

which is exactly the paper's line for one triple, with the three printed alternatives summed
instead of a single fixed pairing.  The proof is the transport of the cover's walks to disjoint
witness sets (`walk_restrict`) followed by the union bound `prob_biUnion_le_sum` and `bk_three`.
-/

@[expose] public section

namespace PercLib.CriticalLRP.FourPoint

open PercLib.CriticalLRP.TreeGraph

set_option linter.unusedSectionVars false
set_option linter.unusedDecidableInType false
set_option linter.unusedFintypeInType false

variable {V : Type*} [DecidableEq V]
variable {E : Type*} [Fintype E] [DecidableEq E]

/-- The probability of a union is at most the sum of the probabilities. -/
theorem prob_union_le {p : E → ℝ} (hp : ∀ e, 0 ≤ p e) (hp1 : ∀ e, p e ≤ 1)
    (A B : Set (Finset E)) : prob p (A ∪ B) ≤ prob p A + prob p B := by
  have key := prob_biUnion_le_sum hp hp1 (W := ({false, true} : Finset Bool))
    (A := fun k : Bool => if k then B else A)
  have hset : (⋃ k ∈ ({false, true} : Finset Bool), (if k then B else A)) = A ∪ B := by
    ext s
    simp only [Set.mem_iUnion, Finset.mem_insert, Finset.mem_singleton]
    constructor
    · rintro ⟨k, rfl | rfl, hk⟩
      · exact Or.inl hk
      · exact Or.inr hk
    · intro h
      rcases h with h | h
      · exact ⟨false, Or.inl rfl, h⟩
      · exact ⟨true, Or.inr rfl, h⟩
  rw [hset] at key
  have hsum : ∑ k ∈ ({false, true} : Finset Bool), prob p (if k then B else A)
      = prob p A + prob p B := by
    rw [Finset.sum_insert (by simp), Finset.sum_singleton]
    simp
  rwa [hsum] at key

/-- On a configuration in which the four walks exist with pairwise disjoint edge lists, the
configuration belongs to the three-fold disjoint occurrence of the joint cluster and the two
arms. -/
theorem mem_disjOcc3_of_walks {ends : E → Sym2 V} {s : Finset E} {o t w u v : V}
    (P : (openGraph ends s).Walk o w) (Q : (openGraph ends s).Walk t w)
    (R : (openGraph ends s).Walk u w) (S : (openGraph ends s).Walk v w)
    (hPQ_R : (P.edges ++ Q.edges).Disjoint R.edges)
    (hPQ_S : (P.edges ++ Q.edges).Disjoint S.edges)
    (hRS : R.edges.Disjoint S.edges) :
    s ∈ DisjOcc3 {s | Conn ends s o t ∧ Conn ends s o w} {s | Conn ends s w u}
      {s | Conn ends s w v} := by
  classical
  refine ⟨s.filter (fun a => ends a ∈ P.edges) ∪ s.filter (fun a => ends a ∈ Q.edges),
    s.filter (fun a => ends a ∈ R.edges), s.filter (fun a => ends a ∈ S.edges),
    Finset.union_subset (Finset.filter_subset _ _) (Finset.filter_subset _ _),
    Finset.filter_subset _ _, Finset.filter_subset _ _, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · -- `Conn o t` and `Conn o w` inside the joint witness
    have hw : Conn ends (s.filter (fun a => ends a ∈ P.edges) ∪
        s.filter (fun a => ends a ∈ Q.edges)) o w :=
      (walk_restrict P).elim fun P' =>
        conn_mono (Finset.subset_union_left) ⟨P'⟩
    have hwt : Conn ends (s.filter (fun a => ends a ∈ P.edges) ∪
        s.filter (fun a => ends a ∈ Q.edges)) w t :=
      (walk_restrict Q).elim fun Q' =>
        conn_mono (Finset.subset_union_right) ⟨Q'.reverse⟩
    exact ⟨conn_trans hw hwt, hw⟩
  · exact (walk_restrict R).elim fun R' => ⟨R'.reverse⟩
  · exact (walk_restrict S).elim fun S' => ⟨S'.reverse⟩
  · rw [Finset.disjoint_left]
    intro a ha hb
    rw [Finset.mem_union, Finset.mem_filter, Finset.mem_filter] at ha
    rw [Finset.mem_filter] at hb
    rcases ha with ⟨-, ha⟩ | ⟨-, ha⟩
    · exact (List.disjoint_left.mp hPQ_R) (List.mem_append_left _ ha) hb.2
    · exact (List.disjoint_left.mp hPQ_R) (List.mem_append_right _ ha) hb.2
  · rw [Finset.disjoint_left]
    intro a ha hb
    rw [Finset.mem_union, Finset.mem_filter, Finset.mem_filter] at ha
    rw [Finset.mem_filter] at hb
    rcases ha with ⟨-, ha⟩ | ⟨-, ha⟩
    · exact (List.disjoint_left.mp hPQ_S) (List.mem_append_left _ ha) hb.2
    · exact (List.disjoint_left.mp hPQ_S) (List.mem_append_right _ ha) hb.2
  · rw [Finset.disjoint_left]
    intro a ha hb
    rw [Finset.mem_filter] at ha hb
    exact (List.disjoint_left.mp hRS) ha.2 hb.2

/-- Unordered pair form of the partition step: if `{t, u, v} = {x, y, z}` and `t = x`, the two
arms are `y` and `z` in some order. -/
theorem pair_eq_of_triple {x y z u v : V} (hxy : x ≠ y) (hxz : x ≠ z) (hyz : y ≠ z)
    (h : ({x, u, v} : Finset V) = {x, y, z}) :
    (u = y ∧ v = z) ∨ (u = z ∧ v = y) := by
  classical
  have hxyz : ({x, y, z} : Finset V).card = 3 := by
    rw [Finset.card_insert_of_notMem (by simp [hxy, hxz]),
      Finset.card_insert_of_notMem (by simp [hyz])]
    simp
  have hcard : ({x, u, v} : Finset V).card = 3 := by rw [h]; exact hxyz
  have hxnot : x ∉ ({u, v} : Finset V) := by
    intro hmem
    have hsub : ({x, u, v} : Finset V) = {u, v} := Finset.insert_eq_self.mpr hmem
    rw [hsub] at hcard
    have hle : ({u, v} : Finset V).card ≤ 2 := by
      have := Finset.card_insert_le u ({v} : Finset V)
      simpa using this
    omega
  have h2 : ({u, v} : Finset V) = {y, z} := by
    have := congrArg (fun F : Finset V => F.erase x) h
    rw [Finset.erase_insert hxnot] at this
    rwa [Finset.erase_insert (by simp [hxy, hxz])] at this
  have huv : u ≠ v := by
    rintro rfl
    rw [show ({x, u, u} : Finset V) = {x, u} from by simp] at hcard
    have hle : ({x, u} : Finset V).card ≤ 2 := by
      have := Finset.card_insert_le x ({u} : Finset V)
      simpa using this
    omega
  have hu : u ∈ ({y, z} : Finset V) := by rw [← h2]; simp
  have hv : v ∈ ({y, z} : Finset V) := by rw [← h2]; simp
  simp only [Finset.mem_insert, Finset.mem_singleton] at hu hv
  rcases hu with rfl | rfl <;> rcases hv with rfl | rfl
  · exact absurd rfl huv
  · exact Or.inl ⟨rfl, rfl⟩
  · exact Or.inr ⟨rfl, rfl⟩
  · exact absurd rfl huv

/-- `DisjOcc3` is symmetric in its last two arguments. -/
theorem disjOcc3_swap (A B C : Set (Finset E)) : DisjOcc3 A B C = DisjOcc3 A C B := by
  ext s
  simp only [DisjOcc3, Set.mem_ofPred_eq]
  constructor <;>
    rintro ⟨W₀, W₁, W₂, h0, h1, h2, m0, m1, m2, d01, d02, d12⟩ <;>
    exact ⟨W₀, W₂, W₁, h0, h2, h1, m0, m2, m1, d02, d01, d12.symm⟩

/-- The joint event `{o ↔ t, w}` is increasing. -/
theorem isIncreasing_conn_and (ends : E → Sym2 V) (o t w : V) :
    IsIncreasing {s | Conn ends s o t ∧ Conn ends s o w} := by
  intro s hs t' hst
  exact ⟨conn_mono hst hs.1, conn_mono hst hs.2⟩


end PercLib.CriticalLRP.FourPoint
