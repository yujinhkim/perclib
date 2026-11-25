/-
Migration source: https://github.com/yujinhkim/Critical-Long-range-percolation
Integration revision: 3b3d1d0e43ef940bfaa2292ee5c2ee094ac4edbf
Licence: Apache-2.0 for the PercLib Lean sources and tooling; see third_party/critical-lrp/.
External provenance and modifications are recorded in the file-specific notices below.
-/

/-
# Theorem 2.3 of arXiv:2008.11197v2 stated faithfully: the `k = 0` endpoint needs a real exponent

Reference: T. Hutchcroft, *Power-law bounds for critical long-range percolation below the
upper-critical dimension*, arXiv:2008.11197v2, Theorem 2.3 and its proof in Section 2.1.

The source prints, for a countable weighted graph `G = (V, E, J)`, finite non-empty `Λ ⊆ V`,
every `β ≥ 0`, every `λ ≥ 1`, every `k ≥ 0` and every `u ∈ V`,

    P(|K_max(Λ)| ≥ 3^k λ) ≤ P(|K_max(Λ)| ≥ λ)^(3^(k-1) + 1)                       (2.8)
    P(|K_u ∩ Λ| ≥ 3^k λ) ≤ P(|K_max(Λ)| ≥ λ)^(3^(k-1)) · P(|K_u ∩ Λ| ≥ λ)         (2.9)

and adds *"(This theorem does not require λ to be an integer.)"*.  The proof, however, only
produces (2.8)/(2.9) from Lemma 2.4 for `k ≥ 1`: Lemma 2.4 takes `k ≥ 1` and outputs
`m ≥ 3^(k-1) + 1 ≥ 2` disjoint witnesses, and (2.11) counts `3^(k-1)` maximum-size factors plus
one pointed factor.

For `k ≥ 1` the exponent `3^(k-1)` is a natural number, so the printed exponents agree with the
natural-number exponents `3^(k-1)+1` and `3^(k-1)` used by the repo's `meets_pow_bound`.  At
`k = 0` the exponent is `3^(-1) = 1/3`, which is *not* a natural number: the faithful reading of
the printed display requires the **real** exponent `(3 : ℝ)^((k : ℝ) - 1)`.  Encoding it with
`Nat` subtraction (`3 ^ (k - 1)` in `ℕ`) silently replaces `1/3` by `1` and `4/3` by `2`, i.e. a
different statement.  Both statements happen to be *false* at `k = 0` (see `K0Refutation.lean`),
but the faithful one is the one this file states, so that a refutation refutes the printed theorem
rather than an artefact of the encoding.

This file contains only the statement layer (definitions, the exponent bookkeeping, and the
positive `k ≥ 1` direction of (2.8) which the repo already proves).  Nothing here claims (2.9) for
`k ≥ 1`: that requires the pointed witness `u ∈ V_i` of the source's proof of (2.11) and is not
discharged in this file (nor elsewhere in the current tree).
-/
module

public import PercLib.CriticalLRP.Tightness.MaxClusterPower

set_option autoImplicit true

set_option linter.unusedSectionVars false

@[expose] public section

namespace Hutchcroft

open PercLib.CriticalLRP.Percolation MeasureTheory
open scoped ENNReal NNReal

attribute [local instance] Classical.propDecidable

variable {V : Type*} [Fintype V] [DecidableEq V] {E : Type*} [Fintype E] [DecidableEq E]
  [Nonempty E]

/-! ### The pointed event `{|K_u ∩ Λ| ≥ lam}` -/

/-- `PointedMeets G Λ u lam`: the event `{|K_u ∩ Λ| ≥ lam}` of (2.9), i.e. the cluster of `u`
contains at least `lam` vertices of the window `Λ`.  This is the pointed analogue of
`Hutchcroft.MaxMeets G Λ lam = {|K_max(Λ)| ≥ lam}`: the same witness but with `u` fixed. -/
def PointedMeets (G : BondGraph V E) (Λ : Finset V) (u : V) (lam : ℕ) : Set (Set E) :=
  {ω | ∃ t : Finset V, t ⊆ Λ ∧ lam ≤ t.card ∧ ∀ y ∈ t, Conn G ω u y}

@[simp]
theorem mem_PointedMeets {G : BondGraph V E} {Λ : Finset V} {u : V} {lam : ℕ} {ω : Set E} :
    ω ∈ PointedMeets G Λ u lam ↔
      ∃ t : Finset V, t ⊆ Λ ∧ lam ≤ t.card ∧ ∀ y ∈ t, Conn G ω u y :=
  Iff.rfl

/-- `{|K_u ∩ Λ| ≥ lam} ⊆ {|K_max(Λ)| ≥ lam}`: the pointed event is contained in the maximum-size
event, because `|K_u ∩ Λ| ≤ |K_max(Λ)|` vertex by vertex. -/
theorem pointedMeets_subset_maxMeets (G : BondGraph V E) (Λ : Finset V) (u : V) (lam : ℕ) :
    PointedMeets G Λ u lam ⊆ MaxMeets G Λ lam := by
  rintro ω ⟨t, ht, hcard, hconn⟩
  exact ⟨t, ht, hcard, u, hconn⟩

theorem pointedMeets_upper (G : BondGraph V E) (Λ : Finset V) (u : V) (lam : ℕ) :
    IsUpperSet (PointedMeets G Λ u lam) := by
  rintro ω ω' hωω' ⟨t, ht, hcard, hconn⟩
  exact ⟨t, ht, hcard, fun y hy => conn_mono G hωω' (hconn y hy)⟩

theorem pointedMeets_antitone (G : BondGraph V E) (Λ : Finset V) (u : V) {lam lam' : ℕ}
    (h : lam ≤ lam') : PointedMeets G Λ u lam' ⊆ PointedMeets G Λ u lam := by
  rintro ω ⟨t, ht, hcard, hconn⟩
  exact ⟨t, ht, le_trans h hcard, hconn⟩

/-! ### The exponents `3^(k-1)` and `3^(k-1) + 1` as real numbers -/

/-- `3^(k-1)` read as the **real** number `(3 : ℝ) ^ ((k : ℝ) - 1)`.

At `k = 0` this is `3^(-1) = 1/3`; at `k ≥ 1` it is the natural number `3^(k-1)`.  Using this
definition (rather than `3 ^ (k - 1)` in `ℕ`, which truncates `0 - 1` to `0`) is what makes the
statement faithful to the source. -/
noncomputable def threeExp (k : ℕ) : ℝ := (3 : ℝ) ^ ((k : ℝ) - 1)

/-- `3^(k-1) + 1` read as a real number: the number of disjoint witnesses in (2.8)/(2.10). -/
noncomputable def threeExpSucc (k : ℕ) : ℝ := threeExp k + 1

theorem threeExp_zero : threeExp 0 = 1 / 3 := by
  have h : ((0 : ℕ) : ℝ) - 1 = (-1 : ℝ) := by norm_num
  rw [threeExp, h, Real.rpow_neg_one]
  norm_num

theorem threeExpSucc_zero : threeExpSucc 0 = 4 / 3 := by
  rw [threeExpSucc, threeExp_zero]; norm_num

theorem threeExp_one : threeExp 1 = 1 := by
  have h : ((1 : ℕ) : ℝ) - 1 = (0 : ℝ) := by norm_num
  rw [threeExp, h, Real.rpow_zero]

/-- For `k ≥ 1` the real exponent `3^(k-1)` *is* the natural number `3^(k-1)`: this is the
consistency statement that the source's exponent reduces to the repo's natural-number exponent
away from the false endpoint `k = 0`. -/
theorem threeExp_eq_natCast {k : ℕ} (hk : 1 ≤ k) : threeExp k = ((3 ^ (k - 1) : ℕ) : ℝ) := by
  have h : (k : ℝ) - 1 = ((k - 1 : ℕ) : ℝ) := by
    rw [← Nat.cast_one, ← Nat.cast_sub hk]
  rw [threeExp, h, Real.rpow_natCast, Nat.cast_pow]
  norm_num

theorem threeExpSucc_eq_natCast {k : ℕ} (hk : 1 ≤ k) :
    threeExpSucc k = ((3 ^ (k - 1) + 1 : ℕ) : ℝ) := by
  rw [threeExpSucc, threeExp_eq_natCast hk]
  push_cast
  ring

/-- At `k = 0` the exponent of (2.8) is `4/3 > 1`, which is exactly what makes the display fail
there: its left-hand side is a probability `q` and the right-hand side is `q^(4/3) ≤ q`, strictly
below `q` when `0 < q < 1`. -/
theorem one_lt_threeExpSucc_zero : 1 < threeExpSucc 0 := by
  rw [threeExpSucc_zero]; norm_num

theorem threeExp_zero_pos : 0 < threeExp 0 := by
  rw [threeExp_zero]; norm_num

/-! ### The displays (2.8) and (2.9) as per-instance statements -/

/-- **(2.8)** for one instance, with the *real* exponent of the source:

`P(|K_max(Λ)| ≥ 3^k λ) ≤ P(|K_max(Λ)| ≥ λ)^(3^(k-1) + 1)`.

Here `λ = lam : ℕ` (the source allows real `λ`), and `p` is the edge-parameter family of the
Bernoulli bond law `edgeLaw p`. -/
def Display28 (G : BondGraph V E) (Λ : Finset V) (k lam : ℕ) (p : E → unitInterval) : Prop :=
  (edgeLaw p).real (MaxMeets G Λ (3 ^ k * lam)) ≤
    (edgeLaw p).real (MaxMeets G Λ lam) ^ threeExpSucc k

/-- **(2.9)** for one instance, with the *real* exponent of the source:

`P(|K_u ∩ Λ| ≥ 3^k λ) ≤ P(|K_max(Λ)| ≥ λ)^(3^(k-1)) · P(|K_u ∩ Λ| ≥ λ)`. -/
def Display29 (G : BondGraph V E) (Λ : Finset V) (k lam : ℕ) (u : V) (p : E → unitInterval) :
    Prop :=
  (edgeLaw p).real (PointedMeets G Λ u (3 ^ k * lam)) ≤
    (edgeLaw p).real (MaxMeets G Λ lam) ^ threeExp k *
      (edgeLaw p).real (PointedMeets G Λ u lam)

/-- **(2.8) for every window and every `k ≥ 1`, `λ ≥ 1`** — the correct (provable) range of
Theorem 2.3.  This is the form the repo discharges (see `display28_of_one_le`). -/
def Theorem28FromOne (G : BondGraph V E) (p : E → unitInterval) : Prop :=
  ∀ (Λ : Finset V), Λ.Nonempty → ∀ k lam : ℕ, 1 ≤ lam → 1 ≤ k → Display28 G Λ k lam p

/-- **(2.9) for every window and every `k ≥ 1`, `λ ≥ 1`** — the correct (provable) range.  It is
*not* discharged in this file: only its statement is recorded, as the interface a pointed-witness
proof must meet. -/
def Theorem29FromOne (G : BondGraph V E) (p : E → unitInterval) : Prop :=
  ∀ (Λ : Finset V), Λ.Nonempty → ∀ (u : V) (k lam : ℕ), 1 ≤ lam → 1 ≤ k → Display29 G Λ k lam u p

/-- The printed range `k ≥ 0` of (2.8): what Theorem 2.3 as printed asserts.  It is **false**; see
`K0Refutation.not_theorem28Printed`. -/
def Theorem28Printed (G : BondGraph V E) (p : E → unitInterval) : Prop :=
  ∀ (Λ : Finset V), Λ.Nonempty → ∀ k lam : ℕ, 1 ≤ lam → Display28 G Λ k lam p

/-- The printed range `k ≥ 0` of (2.9): **false**; see `K0Refutation.not_theorem29Printed`. -/
def Theorem29Printed (G : BondGraph V E) (p : E → unitInterval) : Prop :=
  ∀ (Λ : Finset V), Λ.Nonempty → ∀ (u : V) (k lam : ℕ), 1 ≤ lam → Display29 G Λ k lam u p

/-! ### The `λ = 1` endpoint, and (2.8) for `k ≥ 1` -/

/-- For a non-empty window, `{|K_max(Λ)| ≥ 1}` is the whole configuration space: the cluster of
any vertex of the window already contains that vertex.  (The source's Theorem 2.3 assumes `Λ`
non-empty; for (2.8) this is the only place that hypothesis is used.) -/
theorem maxMeets_one_eq_univ (G : BondGraph V E) {Λ : Finset V} (hΛ : Λ.Nonempty) :
    MaxMeets G Λ 1 = Set.univ := by
  ext ω
  refine ⟨fun _ => trivial, fun _ => ?_⟩
  obtain ⟨v, hv⟩ := hΛ
  exact ⟨{v}, Finset.singleton_subset_iff.mpr hv, by simp, v,
    fun y hy => by
      rw [Finset.mem_singleton.mp hy]
      exact conn_refl G ω v⟩

/-- The real measure of the whole configuration space under the Bernoulli bond law is `1`. -/
theorem edgeLaw_real_univ (p : E → unitInterval) :
    (edgeLaw p).real (Set.univ : Set (Set E)) = 1 := by
  rw [Measure.real_def, measure_univ]
  simp

/-- **(2.8) of Theorem 2.3 for `k ≥ 1` and integer `λ ≥ 1`**, in the real-exponent form of the
source.  It is `meets_pow_bound` (the repo's finite, integer-threshold case) at `λ ≥ 2`, together
with the trivial case `λ = 1` (where the right-hand side is `1`). -/
theorem display28_of_one_le (G : BondGraph V E) {k lam : ℕ} (hlam : 1 ≤ lam) (hk : 1 ≤ k)
    (p : E → unitInterval) (hp : ∀ e, p e < 1) (Λ : Finset V) (hΛ : Λ.Nonempty) :
    Display28 G Λ k lam p := by
  rcases lt_or_eq_of_le hlam with h2 | h1
  · -- `lam ≥ 2`: this is the repo's `meets_pow_bound`
    have h := meets_pow_bound G Λ h2 hk p hp
    rw [Display28, threeExpSucc_eq_natCast hk, Real.rpow_natCast]
    exact h
  · -- `lam = 1`: the right-hand side is `1` and the left-hand side is a probability
    subst h1
    rw [Display28, Nat.mul_one, maxMeets_one_eq_univ G hΛ, edgeLaw_real_univ, Real.one_rpow]
    have hmono := measureReal_mono (μ := edgeLaw p) (Set.subset_univ (MaxMeets G Λ (3 ^ k)))
    rwa [edgeLaw_real_univ] at hmono

/-- **(2.8) for `k ≥ 1`, `λ ≥ 1`**, assembled over all windows: the positive half of Theorem 2.3
that the current tree discharges. -/
theorem theorem28FromOne_of_meets_pow_bound (G : BondGraph V E) (p : E → unitInterval)
    (hp : ∀ e, p e < 1) : Theorem28FromOne G p :=
  fun Λ hΛ _ _ hlam hk => display28_of_one_le G hlam hk p hp Λ hΛ

end Hutchcroft
