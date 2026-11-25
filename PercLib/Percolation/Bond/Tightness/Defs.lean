/-
Copyright (c) 2026 PercLib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
New statement definitions for T-6 (issue 46), written on 2026-11-14, on the D-2 interface.
Source: T. Hutchcroft, "Power-law bounds for critical long-range percolation below the
upper-critical dimension", arXiv:2008.11197v2, §2.1, Theorem 2.2 and Theorem 2.3
(printed p. 14). No code is copied.
-/
module

public import PercLib.Percolation.Bond.Basic
public import Mathlib.Analysis.SpecialFunctions.Exp
public import Mathlib.Data.Set.Card

/-! # Universal tightness of the largest cluster intersection: statements

Fix a finite nonempty set `Λ` of vertices. The open cluster of `v` is the full cluster
`cluster ω v`; paths may leave `Λ`.

* `maxClusterIntersection Λ ω = max_{v ∈ Λ} |K_v ∩ Λ|` (the source's `|K_max(Λ)|`).
* `clusterIntersection Λ ω u = |K_u ∩ Λ|`; the root `u` need not lie in `Λ`.
* `tightnessScale q Λ = min {n ∈ ℕ : P(max ≥ n) ≤ e⁻¹}` (the source's `M`). The set is
  nonempty because the maximum is at most `|Λ|`.

Two target statements, with no proof in this file (D-16):

* `UniversalTightness`, Theorem 2.2 with the source's constants `1/9` and `27`, for every
  `a ≥ 1` and `0 < ε ≤ 1`:
  `P(max ≥ a M) ≤ exp(-a/9)`, `P(max < ε M) ≤ 27 ε`, and
  `P(|K_u ∩ Λ| ≥ a M) ≤ e · P(|K_u ∩ Λ| ≥ M) · exp(-a/9)`.
* `TightnessBK`, Theorem 2.3, **on the reading `k ≥ 1` of issue 52.** The source prints
  `k ≥ 0`; issue 52 gives a counterexample at `k = 0` (one edge with `p = 1/2`, `Λ` its
  endpoints, `λ = 2`), confirmed by AUDITOR, and the source's proof of Theorem 2.2 uses
  only `k ≥ 1`. Tom's decision on issue 52 is pending; this statement follows ARCHITECT's
  instruction on #34 to proceed on `k ≥ 1`, marked as such.

**Generalisation, stated explicitly.** The source works with the profile
`1 - exp(-β J e)` of a countable weighted graph. These statements quantify over every
profile `q : Sym2 V → unitInterval` on a countable vertex type, including the values `0`
and `1`; every profile with values below one is of the source's form. The diagonal of `q`
is irrelevant because the open graph discards loops (D-2).
-/

@[expose] public section
noncomputable section

open MeasureTheory Set
open scoped ENNReal

namespace PercLib.Percolation.Bond

variable {V : Type*}

/-- The largest number of vertices of `Λ` in one open cluster:
`max_{v ∈ Λ} |K_v ∩ Λ|`. Clusters are the full clusters, not clusters in `Λ`. -/
def maxClusterIntersection (Λ : Finset V) (ω : Config V) : ℕ :=
  Λ.sup fun v => (cluster ω v ∩ (Λ : Set V)).ncard

/-- The number of vertices of `Λ` in the open cluster of `u`: `|K_u ∩ Λ|`. -/
def clusterIntersection (Λ : Finset V) (ω : Config V) (u : V) : ℕ :=
  (cluster ω u ∩ (Λ : Set V)).ncard

/-- The source's scale `M`: the least `n` with `P(max_{v ∈ Λ} |K_v ∩ Λ| ≥ n) ≤ e⁻¹`. -/
def tightnessScale (q : Sym2 V → unitInterval) (Λ : Finset V) : ℕ :=
  sInf {n : ℕ | law q {ω | n ≤ maxClusterIntersection Λ ω} ≤ ENNReal.ofReal (Real.exp (-1))}

/-- **Universal tightness** (Hutchcroft, arXiv:2008.11197v2, Theorem 2.2): for every
profile on a countable vertex type, every finite nonempty `Λ`, every root `u`, every
`a ≥ 1` and every `0 < ε ≤ 1`. -/
def UniversalTightness (V : Type*) [Countable V] : Prop :=
  ∀ (q : Sym2 V → unitInterval) (Λ : Finset V), Λ.Nonempty →
    (∀ a : ℝ, 1 ≤ a →
      law q {ω | a * (tightnessScale q Λ : ℝ) ≤ (maxClusterIntersection Λ ω : ℝ)} ≤
        ENNReal.ofReal (Real.exp (-a / 9))) ∧
    (∀ ε : ℝ, 0 < ε → ε ≤ 1 →
      law q {ω | (maxClusterIntersection Λ ω : ℝ) < ε * (tightnessScale q Λ : ℝ)} ≤
        ENNReal.ofReal (27 * ε)) ∧
    (∀ (u : V) (a : ℝ), 1 ≤ a →
      law q {ω | a * (tightnessScale q Λ : ℝ) ≤ (clusterIntersection Λ ω u : ℝ)} ≤
        ENNReal.ofReal (Real.exp 1) *
          law q {ω | tightnessScale q Λ ≤ clusterIntersection Λ ω u} *
          ENNReal.ofReal (Real.exp (-a / 9)))

/-- **The BK step** (Hutchcroft, arXiv:2008.11197v2, Theorem 2.3), **on the reading
`k ≥ 1` of issue 52**; the printed `k ≥ 0` is false at `k = 0`. For every `λ ≥ 1` and
`k ≥ 1`:
`P(max ≥ 3^k λ) ≤ P(max ≥ λ)^(3^(k-1) + 1)` and
`P(|K_u ∩ Λ| ≥ 3^k λ) ≤ P(max ≥ λ)^(3^(k-1)) · P(|K_u ∩ Λ| ≥ λ)`. -/
def TightnessBK (V : Type*) [Countable V] : Prop :=
  ∀ (q : Sym2 V → unitInterval) (Λ : Finset V), Λ.Nonempty →
    ∀ (l : ℝ), 1 ≤ l → ∀ k : ℕ, 1 ≤ k →
      law q {ω | (3 : ℝ) ^ k * l ≤ (maxClusterIntersection Λ ω : ℝ)} ≤
          law q {ω | l ≤ (maxClusterIntersection Λ ω : ℝ)} ^ (3 ^ (k - 1) + 1) ∧
      ∀ u : V,
        law q {ω | (3 : ℝ) ^ k * l ≤ (clusterIntersection Λ ω u : ℝ)} ≤
          law q {ω | l ≤ (maxClusterIntersection Λ ω : ℝ)} ^ (3 ^ (k - 1)) *
            law q {ω | l ≤ (clusterIntersection Λ ω u : ℝ)}

/-! ### Non-vacuity: a singleton `Λ` -/

/-- With `Λ = {v}` the largest intersection is always one. -/
theorem maxClusterIntersection_singleton (v : V) (ω : Config V) :
    maxClusterIntersection {v} ω = 1 := by
  have h : cluster ω v ∩ (({v} : Finset V) : Set V) = {v} := by
    rw [Finset.coe_singleton]
    exact Set.inter_eq_right.2 (Set.singleton_subset_iff.2 (mem_cluster_self ω v))
  rw [maxClusterIntersection, Finset.sup_singleton, h, Set.ncard_singleton]

/-- With `Λ = {v}` the scale is two, for every profile: the scale is a genuine
quantile, not a trivial value. -/
theorem tightnessScale_singleton (q : Sym2 V → unitInterval) (v : V) :
    tightnessScale q {v} = 2 := by
  have hexp : Real.exp (-1) < 1 := by
    have h := Real.exp_lt_exp.2 (show (-1 : ℝ) < 0 by norm_num)
    rwa [Real.exp_zero] at h
  have he : ENNReal.ofReal (Real.exp (-1)) < 1 := ENNReal.ofReal_lt_one.2 hexp
  have h2 : 2 ∈ {n : ℕ | law q {ω | n ≤ maxClusterIntersection {v} ω} ≤
      ENNReal.ofReal (Real.exp (-1))} := by
    have hempty : {ω : Config V | 2 ≤ maxClusterIntersection {v} ω} = ∅ :=
      Set.subset_empty_iff.1 fun ω hω => by
        have h' : 2 ≤ maxClusterIntersection {v} ω := hω
        rw [maxClusterIntersection_singleton] at h'
        omega
    show law q {ω : Config V | 2 ≤ maxClusterIntersection {v} ω} ≤ _
    rw [hempty, measure_empty]
    exact zero_le
  apply le_antisymm (Nat.sInf_le h2)
  apply le_csInf ⟨2, h2⟩
  intro n hn
  by_contra hlt
  have huniv : {ω : Config V | n ≤ maxClusterIntersection {v} ω} = Set.univ :=
    Set.eq_univ_of_forall fun ω => by
      show n ≤ maxClusterIntersection {v} ω
      rw [maxClusterIntersection_singleton]
      omega
  have hn' : law q {ω : Config V | n ≤ maxClusterIntersection {v} ω} ≤
      ENNReal.ofReal (Real.exp (-1)) := hn
  rw [huniv, measure_univ] at hn'
  exact absurd hn' (not_le.2 he)

end PercLib.Percolation.Bond
