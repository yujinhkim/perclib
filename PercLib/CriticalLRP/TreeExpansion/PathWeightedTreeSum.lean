/-
Migration source: https://github.com/yujinhkim/Critical-Long-range-percolation
Integration revision: 3b3d1d0e43ef940bfaa2292ee5c2ee094ac4edbf
Licence: Apache-2.0 for the PercLib Lean sources and tooling; see third_party/critical-lrp/.
External provenance and modifications are recorded in the file-specific notices below.
-/

/-
# The analytic (path) core of the marked-leaf tree sum, and where the 2-term
  subadditivity hypothesis hsub stops being enough

Context.  The target is, for a finite abelian `V`, nonnegative `pr`, `ends`, origin `o` and a
nonnegative weight `A : V → ℝ`,

  `∑_x A (x i₀)^p * treeSum (twoPoint pr ends) n o x
      ≤ M (n-1) * n^(max p 1) * (clusterVolume pr ends o)^(2n-2) * ∑_y A y ^ p * twoPoint pr ends o y`

and the hypothesis offered for `A` is the *two-term* path estimate

  `hsub : ∀ a b, A (a+b)^p ≤ 2^(max (p-1) 0) * (A a ^ p + A b ^ p)`.

This file proves the analytic facts that any general-`n` proof consumes, and records that
`hsub` alone is **not** enough once `n ≥ 3`, by an exact rational counterexample.

What the tree sum reduces to.  With `k a b = T (b-a)` (translation invariance) and constant row
sums `S = ∑ y, T y`, a marked leaf `i₀` at distance `ℓ` from the root gives, for every plane
tree and after summing over all leaf and internal values,

  `S^(2n-1-ℓ) * P_ℓ`,   `P_ℓ = ∑_u B (u_1 + … + u_ℓ) * ∏_j T (u_j)`,  `B = A^p`.

(Verified independently against `treeSum` by brute force in `probe.py`, and `n = 2` — the case
`ℓ = 2` — is the compiled `weightedTreeSum_two_general`.)  Hence

  `LHS = S^(2n-1) * ∑_ℓ C ℓ * E_{ν^{*ℓ}} B`,  `ν = T/S`,  `E_ℓ B = ∑_v ν^{*ℓ}(v) * B v`,

the powers of `S` cancel against `Q = S * E_1 B`, and the target is *equivalent* to

  `∑_ℓ C ℓ * E_ℓ B ≤ M (n-1) * n^(max p 1) * E_1 B`.      (TARGET)

The path step (`P_ℓ ≤ ℓ^(max p 1) * S^(ℓ-1) * Q`) is `∑_j` of the ℓ-ary estimate
`B (u_1 + … + u_ℓ) ≤ ℓ^(max (p-1) 0) * ∑_j B (u_j)`, i.e. the `ℓ`-fold version of `hsub`.
`path_rpow_le` proves the ℓ-ary estimate from *subadditivity of `A`* — which is what the source
has, `A y = |⟨y,u⟩|` — and `hsub_of_subadd` shows that this hypothesis implies `hsub`.  The
converse is false: `A₄_path_fails` below exhibits `A : ZMod 4 → ℝ` with `hsub` at `p = 4` for
which the 3-term estimate fails, and `A₄_target_fails` gives the resulting failure of (TARGET)
at `n = 3` with the exact rational margin `21296/81 > 243`.
-/
module

public import PercLib.CriticalLRP.TreeExpansion.SpatialTreeGraph

set_option linter.unusedSectionVars false
set_option linter.unusedSimpArgs false
set_option linter.unnecessarySimpa false
set_option linter.unusedTactic false
set_option linter.unusedVariables false

set_option autoImplicit true

set_option autoImplicit false
set_option linter.unusedSectionVars false
set_option maxHeartbeats 2000000
set_option linter.deprecated false

@[expose] public section

namespace PercLib.CriticalLRP.TreeExpansion

open Finset
open PercLib.CriticalLRP.TreeGraph

/-! ## 1. From two-term subadditivity to the `ℓ`-term estimate

The source's inequality `(∑_{m≤ℓ} a_m)^p ≤ ℓ^(max (p-1) 0) ∑_{m≤ℓ} a_m^p` is applied there to
`a_m = |φ (z_m - z_{m-1})|`, where `φ` is additive, so that `a` is *subadditive*.  Here is the
abstract form: a subadditive nonnegative `A` with `A 0 = 0` satisfies the `ℓ`-term estimate for
every real exponent `p ≥ 0`. -/

variable {V : Type*} [AddCommGroup V]

/-- **Subadditivity telescopes over a finite sum.**  `A 0 = 0` and `A (a+b) ≤ A a + A b` give
`A (∑ i∈s, u i) ≤ ∑ i∈s, A (u i)`. -/
theorem subadd_sum_le {A : V → ℝ} (h0 : A 0 = 0) (hA : ∀ a b : V, A (a + b) ≤ A a + A b)
    {ι : Type*} (s : Finset ι) (u : ι → V) :
    A (∑ i ∈ s, u i) ≤ ∑ i ∈ s, A (u i) := by
  classical
  induction s using Finset.induction_on with
  | empty => simpa using le_of_eq h0
  | insert a t ha ih =>
      rw [Finset.sum_insert ha, Finset.sum_insert ha]
      refine (hA _ _).trans ?_
      linarith

/-- **The `ℓ`-term path estimate from subadditivity of `A`.**  For `A ≥ 0`, `A 0 = 0`,
`A (a+b) ≤ A a + A b`, real `p ≥ 0` and `1 ≤ ℓ`,

  `A (u_0 + … + u_{ℓ-1})^p ≤ ℓ^(max (p-1) 0) * ∑_j A (u_j)^p`.

This is the only form in which the path decomposition of the marked leaf is consumed: it is
`hsub` iterated to `ℓ` terms without compounding the `2^(max (p-1) 0)` factor. -/
theorem path_rpow_le {A : V → ℝ} (hA0 : ∀ a : V, 0 ≤ A a) (h0 : A 0 = 0)
    (hA : ∀ a b : V, A (a + b) ≤ A a + A b) {p : ℝ} (hp : 0 ≤ p)
    {ℓ : ℕ} (hℓ : 1 ≤ ℓ) (u : Fin ℓ → V) :
    A (∑ j, u j) ^ p ≤ (ℓ : ℝ) ^ (max (p - 1) 0) * ∑ j, A (u j) ^ p := by
  classical
  have hsum : A (∑ j, u j) ≤ ∑ j, A (u j) := by
    simpa using subadd_sum_le h0 hA (Finset.univ : Finset (Fin ℓ)) u
  rcases eq_or_lt_of_le hp with hp0 | hp0
  · -- `p = 0`: both sides are `1` and `ℓ ≥ 1`
    subst hp0
    have h2 : (ℓ : ℝ) ^ (max ((0 : ℝ) - 1) 0) = 1 := by
      rw [max_eq_right (by norm_num : ((0 : ℝ) - 1) ≤ 0), Real.rpow_zero]
    rw [h2, one_mul]
    simp only [Real.rpow_zero, Finset.sum_const, Finset.card_univ, Fintype.card_fin,
      nsmul_eq_mul, mul_one]
    exact_mod_cast hℓ
  · refine (Real.rpow_le_rpow (hA0 _) hsum hp0.le).trans ?_
    have hne : (Finset.univ : Finset (Fin ℓ)).Nonempty :=
      ⟨⟨0, by omega⟩, Finset.mem_univ _⟩
    have := sum_rpow_le_card_mul (Finset.univ : Finset (Fin ℓ)) (fun j => A (u j))
      (fun i _ => hA0 (u i)) hp hne
    simpa using this

/-! ## 2. Subadditivity implies the campaign's two-term hypothesis

Since `(x+y)^p ≤ 2^(max (p-1) 0) (x^p + y^p)` for `x, y ≥ 0`, the honest hypothesis
`A (a+b) ≤ A a + A b` implies the target's `hsub`.  So everything the campaign can prove from
`hsub` is also available from the source-faithful hypothesis. -/

/-- `(x + y)^p ≤ 2^(max (p-1) 0) * (x^p + y^p)` for `x, y ≥ 0` and `p ≥ 0`. -/
theorem two_rpow_le {x y p : ℝ} (hx : 0 ≤ x) (hy : 0 ≤ y) (hp : 0 ≤ p) :
    (x + y) ^ p ≤ (2 : ℝ) ^ (max (p - 1) 0) * (x ^ p + y ^ p) := by
  have hne : (Finset.univ : Finset (Fin 2)).Nonempty := ⟨0, Finset.mem_univ _⟩
  have hnn : ∀ i ∈ (Finset.univ : Finset (Fin 2)), 0 ≤ (![x, y] : Fin 2 → ℝ) i := by
    intro i _
    fin_cases i <;> simp [hx, hy]
  have h := sum_rpow_le_card_mul (Finset.univ : Finset (Fin 2)) (![x, y] : Fin 2 → ℝ)
    hnn hp hne
  simpa [Fin.sum_univ_two] using h

/-- **The campaign's `hsub` follows from subadditivity of `A`.** -/
theorem hsub_of_subadd {A : V → ℝ} (hA0 : ∀ a : V, 0 ≤ A a)
    (hA : ∀ a b : V, A (a + b) ≤ A a + A b) {p : ℝ} (hp : 0 ≤ p) :
    ∀ a b : V, A (a + b) ^ p ≤ (2 : ℝ) ^ (max (p - 1) 0) * (A a ^ p + A b ^ p) := by
  intro a b
  refine (Real.rpow_le_rpow (hA0 _) (hA a b) hp).trans ?_
  exact two_rpow_le (hA0 a) (hA0 b) hp

/-! ## 3. For `p ≤ 1` the two-term hypothesis already gives the `ℓ`-term estimate

At `p ≤ 1` the factor `2^(max (p-1) 0)` is `1`, so `hsub` says that `B = A^p` is subadditive and
the `ℓ`-term estimate follows directly.  The gap therefore only opens at `p > 1`. -/

/-- **At `p ≤ 1`, `hsub` gives the `ℓ`-term estimate.** -/
theorem path_rpow_le_of_hsub_le_one {A : V → ℝ} (_hA0 : ∀ a : V, 0 ≤ A a) (h0 : A 0 = 0)
    {p : ℝ} (hp : 0 ≤ p) (hp1 : p ≤ 1)
    (hsub : ∀ a b : V, A (a + b) ^ p ≤ A a ^ p + A b ^ p)
    {ℓ : ℕ} (hℓ : 1 ≤ ℓ) (u : Fin ℓ → V) :
    A (∑ j, u j) ^ p ≤ ∑ j, A (u j) ^ p := by
  classical
  rcases eq_or_lt_of_le hp with hp0 | hp0
  · subst hp0
    rw [Real.rpow_zero]
    have : (1 : ℝ) ≤ (ℓ : ℝ) := by exact_mod_cast hℓ
    simpa using this
  · have hsub' : ∀ a b : V, A (a + b) ^ p ≤ A a ^ p + A b ^ p := hsub
    have hB0 : A 0 ^ p = 0 := by rw [h0, Real.zero_rpow hp0.ne']
    have := subadd_sum_le (A := fun y => A y ^ p) hB0 hsub'
      (Finset.univ : Finset (Fin ℓ)) u
    simpa using this

/-! ## 3b. The marked-edge exponent is exactly `2n-2`

A tree with `n` labelled leaves has `2n-1` edges, of which `ℓ` lie on the root–`i₀` path; the
other `2n-1-ℓ` each contribute the row sum `S`.  Together with the `ℓ-1` factors `S` produced by
the `ℓ` path increments (`P_ℓ ≤ ℓ^(max p 1) S^(ℓ-1) Q`), the marked-edge factor is *exactly*
`S^(2n-2)`:

  `S^(2n-1-ℓ) * S^(ℓ-1) = S^(2n-2)`  for `1 ≤ ℓ ≤ 2n-1`.

So there is no need to "spend" a factor `S ≥ 1` to pass from `S^(2n-3)` to `S^(2n-2)`: the exact
accounting already produces the exponent `2n-2` of the target, and the target needs no
hypothesis `S ≥ 1`. -/

/-- **The marked-edge exponent is exactly `2n-2`.** -/
theorem markedEdge_factor (S : ℝ) {n ℓ : ℕ} (h1 : 1 ≤ ℓ) (h2 : ℓ ≤ 2 * n - 1) :
    S ^ (2 * n - 1 - ℓ) * S ^ (ℓ - 1) = S ^ (2 * n - 2) := by
  rw [← pow_add]
  congr 1
  omega

/-! ## 4. The path length `ℓ` is at most the number `n` of labelled leaves

The marked leaf `i₀` hangs at distance `ℓ` from the root, and `ℓ ≤ n`.  With `rpow_max_le_of_le`
this is what turns the path count `ℓ · ℓ^(max (p-1) 0) = ℓ^(max p 1)` into the target's
`n^(max p 1)`. -/

namespace RTree

variable {α : Type*}

/-- The number of edges on the tree path from the root to a leaf position. -/
def depth : (t : RTree α) → LeafPos t → ℕ
  | leaf _, _ => 1
  | node l r, Sum.inl p => depth l p + 1
  | node l r, Sum.inr p => depth r p + 1

/-- **Every leaf hangs at distance at most the number of leaves from the root.** -/
theorem depth_le_numLeaves : ∀ (t : RTree α) (p : LeafPos t), depth t p ≤ t.numLeaves
  | leaf _, _ => le_refl 1
  | node l r, Sum.inl p => by
      have hl : depth l p ≤ l.numLeaves := depth_le_numLeaves l p
      have hr : 0 < r.numLeaves := numLeaves_pos r
      rw [numLeaves_node]
      show depth l p + 1 ≤ l.numLeaves + r.numLeaves
      omega
  | node l r, Sum.inr p => by
      have hr : depth r p ≤ r.numLeaves := depth_le_numLeaves r p
      have hl : 0 < l.numLeaves := numLeaves_pos l
      rw [numLeaves_node]
      show depth r p + 1 ≤ l.numLeaves + r.numLeaves
      omega

/-- For a tree fully labelled by `Fin n` the depth of every leaf is at most `n`. -/
theorem depth_le_of_fullyLabelled {n : ℕ} {t : RTree (Fin n)} (ht : FullyLabelled t)
    (p : LeafPos t) : depth t p ≤ n := by
  have h := depth_le_numLeaves t p
  have h2 : t.numLeaves = n := by
    have := ht.2
    rwa [Fintype.card_fin] at this
  omega

end RTree

/-! ## 5. The two constant identities of the final bookkeeping -/

/-- `2^(max p 1) = 2 * 2^(max (p-1) 0)`: the coefficient `2^(max p 1)` of the target is exactly
`2 * 2^(max (p-1) 0)`, the `2` being the number of terms in the two-term estimate. -/
theorem two_rpow_max (p : ℝ) :
    (2 : ℝ) ^ (max p 1) = 2 * (2 : ℝ) ^ (max (p - 1) 0) := by
  rcases lt_or_ge p 1 with h | h
  · rw [max_eq_right h.le, max_eq_right (by linarith : p - 1 ≤ 0), Real.rpow_zero, mul_one,
      Real.rpow_one]
  · rw [max_eq_left h, max_eq_left (by linarith : (0 : ℝ) ≤ p - 1)]
    have hp : p = 1 + (p - 1) := by ring
    rw [hp, Real.rpow_add (by norm_num : (0 : ℝ) < 2), Real.rpow_one]
    ring

/-- `ℓ ≤ n` gives `ℓ^(max p 1) ≤ n^(max p 1)`: the path length `ℓ` never exceeds the number `n`
of labelled leaves, so the path count `ℓ · ℓ^(max (p-1) 0) = ℓ^(max p 1)` is `≤ n^(max p 1)`. -/
theorem rpow_max_le_of_le {ℓ n : ℕ} (hℓn : ℓ ≤ n) (p : ℝ) :
    (ℓ : ℝ) ^ (max p 1) ≤ (n : ℝ) ^ (max p 1) := by
  refine Real.rpow_le_rpow (by positivity) ?_ (le_trans zero_le_one (le_max_right p 1))
  exact_mod_cast hℓn

/-! ## 6. The `n = 1` anchor with an arbitrary (non-vacuous) weight

`treeSum_one` gives `treeSum k 1 o x = k o (x 0)`, so at `n = 1` the marked-leaf sum is the
identity `∑_x A (x 0)^p treeSum k 1 o x = ∑_y A y ^ p k o y`, with constants
`M 0 = 1`, `1^(max p 1) = 1`, `S^0 = 1`.  No hypothesis on `A` is used: the arbitrary-weight
formulation is non-vacuous at the base case. -/

/-- **`n = 1`, arbitrary weight**: the marked-leaf tree sum is exactly the weighted two-point
sum. -/
theorem weightedTreeSum_one_general {V : Type*} [Fintype V] [DecidableEq V] {E : Type*}
    [Fintype E] [DecidableEq E] (pr : E → ℝ) (ends : E → Sym2 V) (o : V) (A : V → ℝ)
    (p : ℝ) :
    (∑ x : Fin 1 → V, A (x 0) ^ p * treeSum (twoPoint pr ends) 1 o x)
      = (VolumeMoments.M 0 : ℝ) * (1 : ℝ) ^ (max p 1) *
          (clusterVolume pr ends o) ^ (2 * 1 - 2) *
          ∑ y : V, A y ^ p * twoPoint pr ends o y := by
  classical
  have hL : (∑ x : Fin 1 → V, A (x 0) ^ p * treeSum (twoPoint pr ends) 1 o x)
      = ∑ y : V, A y ^ p * twoPoint pr ends o y := by
    rw [Finset.sum_congr rfl fun x _ => by rw [treeSum_one]]
    refine Fintype.sum_equiv (Equiv.funUnique (Fin 1) V)
      (fun x : Fin 1 → V => A (x 0) ^ p * twoPoint pr ends o (x 0))
      (fun y : V => A y ^ p * twoPoint pr ends o y) ?_
    intro x
    simp [Equiv.funUnique]
  rw [hL]
  simp

/-! ## 7. `hsub` is strictly weaker than the `ℓ`-term estimate for `p > 1`

An exact rational witness on `V = ZMod 4`, `p = 4` (so `2^(max (p-1) 0) = 8`):

  `A = (0, 1, 2, 10/3)` on `0, 1, 2, 3`.

* `A` satisfies the two-term hypothesis `A (a+b)^4 ≤ 8 (A a^4 + A b^4)` for **all** `16` pairs;
* but with `u = (1, 1, 1)` and `u_0 + u_1 + u_2 = 3`:
  `A 3^4 = 10000/81 ≈ 123.46 > 3^(max (4-1) 0) * (A 1^4 + A 1^4 + A 1^4) = 27 * 3 = 81`.

Consequently the ℓ-ary path estimate — hence `P_ℓ ≤ ℓ^(max p 1) S^(ℓ-1) Q` and the `n ≥ 3` bound
— does **not** follow from `hsub`; a hypothesis such as `path_rpow_le`'s (subadditivity of `A`,
or the ℓ-ary estimate itself) is necessary.  At `n = 3` the same `A` and the kernel `T = δ_1`
(kernel `k a b = 1` iff `b = a+1`; nonnegative, translation invariant, constant row sums `1`)
give `E_1 B = 1`, `E_2 B = 16`, `E_3 B = 10000/81`, so `E_2 B + 2 E_3 B = 21296/81 ≈ 262.9`
against the target's `M 2 * 3^4 * E_1 B = 3 * 81 = 243`: the target itself fails for this
kernel.  (Symmetry `T z = T (-z)`, which every `twoPoint` has, is what is missing there; the
current `WeightedTreeSum` signature does not record it.) -/

/-- The witness `A` on `ZMod 4`. -/
noncomputable def A₄ : ZMod 4 → ℝ := fun v =>
  if v = 0 then 0 else if v = 1 then 1 else if v = 2 then 2 else (10 : ℝ) / 3

/-- Every element of `ZMod 4` is one of `0, 1, 2, 3`. -/
theorem zmod_four_cases (a : ZMod 4) : a = 0 ∨ a = 1 ∨ a = 2 ∨ a = 3 := by revert a; decide

/-- **The witness satisfies the campaign's two-term hypothesis at `p = 4`** (all `16` pairs). -/
theorem A₄_hsub :
    ∀ a b : ZMod 4, A₄ (a + b) ^ (4 : ℝ) ≤ (8 : ℝ) * (A₄ a ^ (4 : ℝ) + A₄ b ^ (4 : ℝ)) := by
  intro a b
  rcases zmod_four_cases a with rfl | rfl | rfl | rfl <;>
    rcases zmod_four_cases b with rfl | rfl | rfl | rfl <;>
    (repeat (first | unfold A₄ | rw [ite_eq_left (by decide)] | rw [ite_eq_right (by decide)])) <;>
    norm_num

/-- **The witness violates the three-term estimate**: `A (1+1+1)^4 > 3^(max (4-1) 0) * ∑ A 1^4`. -/
theorem A₄_path_fails :
    (3 : ℝ) ^ (max ((4 : ℝ) - 1) 0) * (A₄ 1 ^ (4 : ℝ) + A₄ 1 ^ (4 : ℝ) + A₄ 1 ^ (4 : ℝ))
      < A₄ ((1 : ZMod 4) + 1 + 1) ^ (4 : ℝ) := by
  (repeat (first | unfold A₄ | rw [ite_eq_left (by decide)] | rw [ite_eq_right (by decide)]))
  norm_num

/-- **The `n = 3` target functional fails for `hsub` alone.**  With `B = A₄^4`, the three tree
values of the marked-leaf sum at `n = 3` collapse to `E_2 B + 2 * E_3 B` (one tree with the
marked leaf at depth `2`, two at depth `3`), and this exceeds the target's
`M 2 * 3^max(4,1) * E_1 B = 3 * 81 * 1`. -/
theorem A₄_target_fails :
    (VolumeMoments.M 2 : ℝ) * (3 : ℝ) ^ (max (4 : ℝ) 1) * A₄ 1 ^ (4 : ℝ)
      < A₄ 2 ^ (4 : ℝ) + 2 * A₄ ((1 : ZMod 4) + 1 + 1) ^ (4 : ℝ) := by
  (repeat (first | unfold A₄ | rw [ite_eq_left (by decide)] | rw [ite_eq_right (by decide)]))
  norm_num [VolumeMoments.M]

end PercLib.CriticalLRP.TreeExpansion

/-! ## Axiom audit -/

#print axioms PercLib.CriticalLRP.TreeExpansion.subadd_sum_le
#print axioms PercLib.CriticalLRP.TreeExpansion.path_rpow_le
#print axioms PercLib.CriticalLRP.TreeExpansion.two_rpow_le
#print axioms PercLib.CriticalLRP.TreeExpansion.hsub_of_subadd
#print axioms PercLib.CriticalLRP.TreeExpansion.path_rpow_le_of_hsub_le_one
#print axioms PercLib.CriticalLRP.TreeExpansion.two_rpow_max
#print axioms PercLib.CriticalLRP.TreeExpansion.markedEdge_factor
#print axioms PercLib.CriticalLRP.TreeExpansion.rpow_max_le_of_le
#print axioms PercLib.CriticalLRP.TreeExpansion.RTree.depth_le_numLeaves
#print axioms PercLib.CriticalLRP.TreeExpansion.RTree.depth_le_of_fullyLabelled
#print axioms PercLib.CriticalLRP.TreeExpansion.weightedTreeSum_one_general
#print axioms PercLib.CriticalLRP.TreeExpansion.A₄_hsub
#print axioms PercLib.CriticalLRP.TreeExpansion.A₄_path_fails
#print axioms PercLib.CriticalLRP.TreeExpansion.A₄_target_fails
