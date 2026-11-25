/-
Migration source: https://github.com/yujinhkim/Critical-Long-range-percolation
Integration revision: 3b3d1d0e43ef940bfaa2292ee5c2ee094ac4edbf
Licence: Apache-2.0 for the PercLib Lean sources and tooling; see third_party/critical-lrp/.
External provenance and modifications are recorded in the file-specific notices below.
-/

/-
Hutchcroft, *Critical long-range percolation I: High effective dimension*,
arXiv:2508.18807v1, Lemma I.4.1 (p. 33) and the error terms `𝓔_{1,r}`, `𝓔_{2,r}`
of Section I.4.1 — the part of the computation that is *not* Russo's formula.

Lemma I.4.1 reads

  ∂_r E_{β,r}|K|^p = β|J'(r)| ∑_{ℓ=0}^{p-1} C(p,ℓ)
      E_{β,r}[ |K|^{ℓ+1} ∑_{y ∈ B_r} 1(y ∉ K) |K_y|^{p-ℓ} ].

Its proof has three algebraic ingredients, isolated here so that they can be
reused by any instantiation of the model (they involve no probability at all):

* `add_pow_eq_pow_add_sum` / `mul_add_pow_sub_pow`: the expansion
  `[(|K|+|K_y|)^p - |K|^p] = ∑_{ℓ<p} C(p,ℓ)|K|^ℓ|K_y|^(p-ℓ)` and its version
  with one extra factor `|K|`, which turns it into `∑_ℓ C(p,ℓ)|K|^(ℓ+1)|K_y|^(p-ℓ)`.

* `ClusterStruct.pivot_add_mul_card`: for a fixed configuration, with `K` the
  cluster of the origin, `K_y` the cluster of `y` and `B` a finite set of
  vertices,

    `|K| ∑_{y∈B} 1(y∉K)|K_y| + |K|^2 |K∩B| = |K| ∑_{y∈B}|K_y|`.

  This is the identity behind the definition of the error term `𝓔_{1,r}` on
  p. 35, whose numerator is exactly
  `|B_r|(E|K|)^2 - E[|K|∑_{y∈B_r}|K_y|] + E[|K|^2|K∩B_r|]`; the last term is
  the `|K|^2|K∩B_r|` above.  The same computation with `|K_y|^2` in place of
  `|K_y|` gives the term `E[|K|^3|K∩B_r|]` in `𝓔_{2,r}` (p. 43).

Everything is stated for `ℝ≥0∞`-valued volumes, so that infinite clusters are
allowed and no integrability hypothesis is needed.  `encard` is supplied as the
canonical instance `ClusterStruct.ofSet`.
-/
module

public import Mathlib

set_option linter.unusedSectionVars false
set_option linter.unusedSimpArgs false
set_option linter.unnecessarySimpa false
set_option linter.unusedTactic false
set_option linter.unusedVariables false

set_option autoImplicit true

noncomputable section

@[expose] public section

open Finset

open scoped ENNReal

namespace PercLib.CriticalLRP.VolumeMoments

attribute [local instance] Classical.propDecidable

/-! ### The binomial expansion used in Lemma I.4.1 -/

/-- `(a+b)^p = a^p + ∑_{ℓ<p} C(p,ℓ) a^ℓ b^(p-ℓ)` for `p ≥ 1`, in a commutative
semiring.  This is the identity behind
`[(|K|+|K_y|)^p - |K|^p] = ∑_{ℓ<p} C(p,ℓ)|K|^ℓ|K_y|^(p-ℓ)`. -/
theorem add_pow_eq_pow_add_sum {R : Type*} [CommSemiring R] (a b : R) (p : ℕ) (hp : 1 ≤ p) :
    (a + b) ^ p = a ^ p + ∑ ℓ ∈ Finset.range p, (p.choose ℓ : R) * a ^ ℓ * b ^ (p - ℓ) := by
  rw [add_pow, Finset.sum_range_succ]
  have hlast : a ^ p * b ^ (p - p) * ((p.choose p : ℕ) : R) = a ^ p := by
    rw [Nat.sub_self, pow_zero, mul_one, Nat.choose_self, Nat.cast_one, mul_one]
  rw [hlast, add_comm]
  congr 1
  exact Finset.sum_congr rfl fun ℓ _ => by ring

/-- The same identity in the form used in Lemma I.4.1: after multiplying by the
extra factor `a` coming from the mass-transport step, the `p`-th finite
difference of the cluster volume is the sum over `ℓ < p` of
`C(p,ℓ) a^(ℓ+1) b^(p-ℓ)`. -/
theorem mul_add_pow_sub_pow {R : Type*} [CommSemiring R] (a b : R) (p : ℕ) (hp : 1 ≤ p) :
    a * (a + b) ^ p
      = a ^ (p + 1) + ∑ ℓ ∈ Finset.range p, (p.choose ℓ : R) * a ^ (ℓ + 1) * b ^ (p - ℓ) := by
  rw [add_pow_eq_pow_add_sum a b p hp, mul_add, Finset.mul_sum]
  congr 1
  · rw [pow_succ]; ring
  · refine Finset.sum_congr rfl fun ℓ _ => ?_
    ring

/-! ### Cluster structures -/

/-- A cluster structure on a vertex type: `cl x` is the cluster of `x` and `vol`
is the volume of a set of vertices (in the application, `vol = encard`).  The
only property needed below is that clusters are equivalence classes: a vertex
`y` of the cluster of `x` has the same cluster as `x`. -/
structure ClusterStruct (V : Type*) where
  /-- the cluster of a vertex -/
  cl : V → Set V
  /-- the volume of a set of vertices -/
  vol : Set V → ℝ≥0∞
  /-- every vertex is in its own cluster -/
  mem_self : ∀ x, x ∈ cl x
  /-- clusters are equivalence classes -/
  eq_of_mem : ∀ {x y : V}, y ∈ cl x → cl y = cl x

/-- The canonical cluster structure associated with an equivalence relation,
with volume `encard`.  In the percolation application `r` is the reachability
relation of a configuration. -/
def ClusterStruct.ofSet {V : Type*} (cl : V → Set V)
    (hself : ∀ x, x ∈ cl x) (heq : ∀ {x y : V}, y ∈ cl x → cl y = cl x) :
    ClusterStruct V :=
  ⟨cl, fun s => s.encard, hself, heq⟩

namespace ClusterStruct

variable {V : Type*} (K : ClusterStruct V)

/-- Vertices of a cluster have the same cluster. -/
theorem cl_eq {x y : V} (h : y ∈ K.cl x) : K.cl y = K.cl x := K.eq_of_mem h

/-- Hence vertices of a cluster have the same volume. -/
theorem vol_cl_eq {x y : V} (h : y ∈ K.cl x) : K.vol (K.cl y) = K.vol (K.cl x) := by
  rw [cl_eq K h]

/-- **The pivot identity of Lemma I.4.1 / the error term `𝓔_{1,r}`.**
For a fixed configuration, with `K` the cluster of the origin and `B` a finite
set of vertices,
`|K| ∑_{y∈B} 1(y∉K)|K_y| + |K|^2 |K∩B| = |K| ∑_{y∈B}|K_y|`.

In the paper this says
`|K| ∑_{y∈B_r} 1(y∉K)|K_y| = |K| ∑_{y∈B_r}|K_y| - |K|^2 |K ∩ B_r|`, which is how
the term `E[|K|^2|K∩B_r|]` in the definition of `𝓔_{1,r}` arises. -/
theorem pivot_add_mul_card (x : V) (B : Finset V) :
    K.vol (K.cl x) * (∑ y ∈ B, if y ∈ K.cl x then 0 else K.vol (K.cl y))
        + K.vol (K.cl x) ^ 2 * ((B.filter (fun y => y ∈ K.cl x)).card : ℝ≥0∞)
      = K.vol (K.cl x) * (∑ y ∈ B, K.vol (K.cl y)) := by
  classical
  have hcard : ((B.filter (fun y => y ∈ K.cl x)).card : ℝ≥0∞)
      = ∑ y ∈ B, if y ∈ K.cl x then 1 else 0 := by
    rw [Finset.card_filter]
    push_cast
    rfl
  have h1 : K.vol (K.cl x) * (∑ y ∈ B, if y ∈ K.cl x then 0 else K.vol (K.cl y))
      = ∑ y ∈ B, K.vol (K.cl x) * (if y ∈ K.cl x then 0 else K.vol (K.cl y)) :=
    Finset.mul_sum B (fun y => if y ∈ K.cl x then 0 else K.vol (K.cl y)) (K.vol (K.cl x))
  have h2 : K.vol (K.cl x) ^ 2 * ((B.filter (fun y => y ∈ K.cl x)).card : ℝ≥0∞)
      = ∑ y ∈ B, K.vol (K.cl x) ^ 2 * (if y ∈ K.cl x then 1 else 0) := by
    rw [hcard, Finset.mul_sum]
  have h3 : K.vol (K.cl x) * (∑ y ∈ B, K.vol (K.cl y))
      = ∑ y ∈ B, K.vol (K.cl x) * K.vol (K.cl y) :=
    Finset.mul_sum B (fun y => K.vol (K.cl y)) (K.vol (K.cl x))
  rw [h1, h2, h3, ← Finset.sum_add_distrib]
  refine Finset.sum_congr rfl fun y _ => ?_
  by_cases hy : y ∈ K.cl x
  · have hv : K.vol (K.cl y) = K.vol (K.cl x) := vol_cl_eq K hy
    simp only [hy, ite_true, hv]
    ring
  · simp only [hy, ite_false, mul_zero, add_zero]

/-- **The general pivot identity**: for any exponent `q`, and with `K` the
cluster of the origin,

`|K| ∑_{y∈B} 1(y∉K)|K_y|^q + |K|^(q+1) |K∩B| = |K| ∑_{y∈B}|K_y|^q`.

`q = 1` is `pivot_add_mul_card`; `q = 2` gives the term `E[|K|^3|K∩B_r|]` of
`𝓔_{2,r}` (paper p. 43); the case `q = p-ℓ` is exactly the summand of
Lemma I.4.1. -/
theorem pivot_add_pow (x : V) (B : Finset V) (q : ℕ) :
    K.vol (K.cl x) * (∑ y ∈ B, if y ∈ K.cl x then 0 else (K.vol (K.cl y)) ^ q)
        + (K.vol (K.cl x)) ^ (q + 1) * ((B.filter (fun y => y ∈ K.cl x)).card : ℝ≥0∞)
      = K.vol (K.cl x) * (∑ y ∈ B, (K.vol (K.cl y)) ^ q) := by
  classical
  have hcard : ((B.filter (fun y => y ∈ K.cl x)).card : ℝ≥0∞)
      = ∑ y ∈ B, if y ∈ K.cl x then 1 else 0 := by
    rw [Finset.card_filter]
    push_cast
    rfl
  have h1 : K.vol (K.cl x) * (∑ y ∈ B, if y ∈ K.cl x then 0 else (K.vol (K.cl y)) ^ q)
      = ∑ y ∈ B, K.vol (K.cl x) * (if y ∈ K.cl x then 0 else (K.vol (K.cl y)) ^ q) :=
    Finset.mul_sum B (fun y => if y ∈ K.cl x then 0 else (K.vol (K.cl y)) ^ q) (K.vol (K.cl x))
  have h2 : (K.vol (K.cl x)) ^ (q + 1) * ((B.filter (fun y => y ∈ K.cl x)).card : ℝ≥0∞)
      = ∑ y ∈ B, (K.vol (K.cl x)) ^ (q + 1) * (if y ∈ K.cl x then 1 else 0) := by
    rw [hcard, Finset.mul_sum]
  have h3 : K.vol (K.cl x) * (∑ y ∈ B, (K.vol (K.cl y)) ^ q)
      = ∑ y ∈ B, K.vol (K.cl x) * (K.vol (K.cl y)) ^ q :=
    Finset.mul_sum B (fun y => (K.vol (K.cl y)) ^ q) (K.vol (K.cl x))
  rw [h1, h2, h3, ← Finset.sum_add_distrib]
  refine Finset.sum_congr rfl fun y _ => ?_
  by_cases hy : y ∈ K.cl x
  · have hv : K.vol (K.cl y) = K.vol (K.cl x) := vol_cl_eq K hy
    simp only [hy, ite_true, hv, mul_zero, zero_add]
    rw [mul_one, pow_succ]
    ring
  · simp only [hy, ite_false, mul_zero, add_zero]

end ClusterStruct

end PercLib.CriticalLRP.VolumeMoments
