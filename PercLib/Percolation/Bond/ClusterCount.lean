/-
Copyright (c) 2026 PercLib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

New proofs for issue 177 (Q-27), written on 2026-11-14 by PROVER-E. No upstream proof is
copied.
-/
module

public import Mathlib.Combinatorics.SimpleGraph.Connectivity.Finite
public import Mathlib.MeasureTheory.Integral.Bochner.Basic
public import Mathlib.Topology.Algebra.InfiniteSum.Real
public import PercLib.Percolation.Bond.ClusterPartition
public import PercLib.Percolation.Bond.Susceptibility
public import PercLib.Probability.Coupling.Monotone

/-!
# The number of clusters on a finite vertex set

On a finite vertex type, `κ(ω) = Nat.card (openGraph ω).ConnectedComponent` is the number
of open clusters. This file proves:

* `κ(ω) = ∑_v 1 / |K_v(ω)|`, so `E κ = ∑_v E[1 / |K_v|]`;
* `∑_v χ(v) = E ∑_C |C|²`, the sum over the clusters;
* `κ` is antitone in `ω`, and opening one pair lowers it by at most one;
* `E_{q'} κ ≤ E_q κ` when `q ≤ q'`.

This file adds no definition.
-/

@[expose] public section

open MeasureTheory Set SimpleGraph PercLib.Probability
open scoped ENNReal

namespace PercLib.Percolation.Bond

variable {V : Type*}

/-- Every component of a finite graph has at least one vertex. -/
theorem one_le_ncard_supp [Finite V] (ω : Config V) (C : (openGraph ω).ConnectedComponent) :
    1 ≤ C.supp.ncard := by
  obtain ⟨v, hv⟩ := C.exists_rep
  exact Nat.one_le_iff_ne_zero.2 ((Set.ncard_pos (Set.toFinite _)).2
    ⟨v, (ConnectedComponent.mem_supp_iff _ v).2 hv⟩).ne'

/-- **The number of clusters is the sum of the inverse cluster sizes.** -/
theorem card_connectedComponent_eq_sum_inv [Fintype V] (ω : Config V) :
    (Nat.card (openGraph ω).ConnectedComponent : ℝ) = ∑ v, 1 / ((cluster ω v).ncard : ℝ) := by
  have hsum := tsum_cluster_real_function ω (fun n => 1 / (n : ℝ))
  rw [tsum_fintype] at hsum
  rw [hsum]
  have hone : ∀ C : (openGraph ω).ConnectedComponent,
      (C.supp.ncard : ℝ) * (1 / (C.supp.ncard : ℝ)) = 1 := by
    intro C
    have hpos : (0 : ℝ) < C.supp.ncard := by exact_mod_cast one_le_ncard_supp ω C
    field_simp
  classical
  have := Fintype.ofFinite (openGraph ω).ConnectedComponent
  simp_rw [hone]
  rw [tsum_fintype, Finset.sum_const, Finset.card_univ, ← Nat.card_eq_fintype_card,
    nsmul_eq_mul, mul_one]

/-- On a finite vertex type every configuration function is integrable. -/
theorem integrable_of_fintype [Fintype V] (q : Sym2 V → unitInterval) (f : Config V → ℝ) :
    Integrable f (law q) :=
  Integrable.of_finite

/-- **Expected number of clusters.** -/
theorem integral_card_connectedComponent [Fintype V] (q : Sym2 V → unitInterval) :
    ∫ ω, (Nat.card (openGraph ω).ConnectedComponent : ℝ) ∂law q =
      ∑ v, ∫ ω, 1 / ((cluster ω v).ncard : ℝ) ∂law q := by
  simp_rw [card_connectedComponent_eq_sum_inv]
  exact integral_finsetSum _ fun v _ => integrable_of_fintype q _

/-- The cluster volumes add up to the sum of the squared cluster sizes. -/
theorem sum_encard_cluster_eq [Fintype V] (ω : Config V) :
    ∑ v, ((cluster ω v).encard : ℝ≥0∞) =
      ((∑' C : (openGraph ω).ConnectedComponent, C.supp.ncard ^ 2 : ℕ) : ℝ≥0∞) := by
  rw [← tsum_cluster_ncard_eq_tsum_component_sq, tsum_fintype, Nat.cast_sum]
  refine Finset.sum_congr rfl fun v _ => ?_
  rw [← (Set.toFinite (cluster ω v)).cast_ncard_eq]
  rfl

/-- **The susceptibilities add up to the expected sum of squared cluster sizes.** -/
theorem sum_chi_eq_lintegral [Fintype V] (q : Sym2 V → unitInterval) :
    ∑ v, chi q v =
      ∫⁻ ω, ((∑' C : (openGraph ω).ConnectedComponent, C.supp.ncard ^ 2 : ℕ) : ℝ≥0∞) ∂law q := by
  simp only [chi]
  rw [← lintegral_finsetSum _ fun v _ => measurable_of_finite _]
  exact lintegral_congr fun ω => sum_encard_cluster_eq ω

/-- **The number of clusters is antitone in the configuration.** -/
theorem card_connectedComponent_anti [Finite V] {ω ω' : Config V} (h : ω ⊆ ω') :
    Nat.card (openGraph ω').ConnectedComponent ≤ Nat.card (openGraph ω).ConnectedComponent :=
  ConnectedComponent.card_le_card_of_le (openGraph_mono h)

/-- There are at most as many clusters as vertices. -/
theorem card_connectedComponent_le [Finite V] (ω : Config V) :
    Nat.card (openGraph ω).ConnectedComponent ≤ Nat.card V :=
  Nat.card_le_card_of_surjective (openGraph ω).connectedComponentMk fun C => C.exists_rep

/-- After opening `s(a, b)`, a vertex joined to `u` was already joined to `u`, or the two
were joined to the two ends of the new pair. -/
theorem reachable_or_of_reachable_insert (ω : Config V) (a b u w : V)
    (h : (openGraph (insert s(a, b) ω)).Reachable u w) :
    (openGraph ω).Reachable u w ∨
      ((openGraph ω).Reachable u a ∧ (openGraph ω).Reachable w b) ∨
      ((openGraph ω).Reachable u b ∧ (openGraph ω).Reachable w a) := by
  rw [SimpleGraph.reachable_iff_reflTransGen] at h
  induction h with
  | refl => exact Or.inl (Reachable.refl u)
  | @tail w z _ hadj ih =>
    rw [openGraph_adj_iff, mem_insert_iff] at hadj
    obtain ⟨he | he, hne⟩ := hadj
    · rcases Sym2.eq_iff.1 he with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
      · rcases ih with h | ⟨h1, h2⟩ | ⟨h1, _⟩
        · exact Or.inr (Or.inl ⟨h, Reachable.refl _⟩)
        · exact Or.inl (h1.trans h2)
        · exact Or.inl h1
      · rcases ih with h | ⟨h1, _⟩ | ⟨h1, h2⟩
        · exact Or.inr (Or.inr ⟨h, Reachable.refl _⟩)
        · exact Or.inl h1
        · exact Or.inl (h1.trans h2)
    · have hwz : (openGraph ω).Reachable z w :=
        (SimpleGraph.Adj.reachable ((openGraph_adj_iff ω w z).2 ⟨he, hne⟩)).symm
      rcases ih with h | ⟨h1, h2⟩ | ⟨h1, h2⟩
      · exact Or.inl (h.trans hwz.symm)
      · exact Or.inr (Or.inl ⟨h1, hwz.trans h2⟩)
      · exact Or.inr (Or.inr ⟨h1, hwz.trans h2⟩)

/-- **Opening one pair lowers the number of clusters by at most one.** -/
theorem card_connectedComponent_le_insert_add_one [Finite V] (ω : Config V) (e : Sym2 V) :
    Nat.card (openGraph ω).ConnectedComponent ≤
      Nat.card (openGraph (insert e ω)).ConnectedComponent + 1 := by
  classical
  induction e using Sym2.ind with
  | _ a b =>
  set G := openGraph ω
  set G' := openGraph (insert s(a, b) ω)
  have hle : G ≤ G' := openGraph_mono (subset_insert _ _)
  let φ := ConnectedComponent.map (Hom.ofLE hle)
  let ψ : G.ConnectedComponent → Option G'.ConnectedComponent := fun C =>
    if C = G.connectedComponentMk b then none else some (φ C)
  have hψ : Function.Injective ψ := by
    intro C₁ C₂ h
    by_cases h₁ : C₁ = G.connectedComponentMk b
    · by_cases h₂ : C₂ = G.connectedComponentMk b
      · rw [h₁, h₂]
      · simp only [ψ, h₁, h₂, ite_true, ite_false, reduceCtorEq] at h
    · by_cases h₂ : C₂ = G.connectedComponentMk b
      · simp only [ψ, h₁, h₂, ite_true, ite_false, reduceCtorEq] at h
      · simp only [ψ, h₁, h₂, ite_false, Option.some.injEq] at h
        obtain ⟨u, hu⟩ := C₁.exists_rep
        obtain ⟨v, hv⟩ := C₂.exists_rep
        rw [← hu, ← hv] at h ⊢
        rw [← hu] at h₁
        rw [← hv] at h₂
        have huv : G'.Reachable u v := by
          simp only [φ] at h
          exact ConnectedComponent.exact h
        rcases reachable_or_of_reachable_insert ω a b u v huv with h1 | ⟨_, h2⟩ | ⟨h1, _⟩
        · exact ConnectedComponent.sound h1
        · exact absurd (ConnectedComponent.sound h2) h₂
        · exact absurd (ConnectedComponent.sound h1) h₁
  have := Fintype.ofFinite G'.ConnectedComponent
  calc Nat.card G.ConnectedComponent ≤ Nat.card (Option G'.ConnectedComponent) :=
        Nat.card_le_card_of_injective ψ hψ
    _ = Nat.card G'.ConnectedComponent + 1 := by
        rw [Nat.card_eq_fintype_card, Nat.card_eq_fintype_card, Fintype.card_option]

/-- **More open pairs give fewer clusters on average.** -/
theorem integral_card_connectedComponent_anti [Fintype V] {q q' : Sym2 V → unitInterval}
    (h : q ≤ q') :
    ∫ ω, (Nat.card (openGraph ω).ConnectedComponent : ℝ) ∂law q' ≤
      ∫ ω, (Nat.card (openGraph ω).ConnectedComponent : ℝ) ∂law q := by
  set κ : Config V → ℕ := fun ω => Nat.card (openGraph ω).ConnectedComponent
  set N : ℕ := Nat.card V
  set F : Config V → ℝ≥0∞ := fun ω => ((N - κ ω : ℕ) : ℝ≥0∞)
  have hF : Monotone F := fun ω ω' hωω' => by
    simp only [F]
    exact_mod_cast Nat.sub_le_sub_left (card_connectedComponent_anti hωω') N
  have hmono := lintegral_prodBernoulli_mono q q' h (measurable_of_finite F) hF
  have hreal : ∀ r : Sym2 V → unitInterval,
      ∫ ω, (κ ω : ℝ) ∂law r = N - (∫⁻ ω, F ω ∂law r).toReal := by
    intro r
    have hpt : ∀ ω, (κ ω : ℝ) = N - ((N - κ ω : ℕ) : ℝ) := fun ω => by
      rw [Nat.cast_sub (card_connectedComponent_le ω)]
      ring
    simp_rw [hpt]
    rw [integral_sub (integrable_const _) (integrable_of_fintype r _), integral_const,
      probReal_univ, one_smul,
      integral_eq_lintegral_of_nonneg_ae (.of_forall fun ω => Nat.cast_nonneg _)
        (measurable_of_finite _).aestronglyMeasurable]
    congr 2
    refine lintegral_congr fun ω => ?_
    simp [F]
  have hfin : ∀ r : Sym2 V → unitInterval, ∫⁻ ω, F ω ∂law r ≠ ∞ := fun r => by
    refine ne_top_of_le_ne_top (b := ∫⁻ _ω, (N : ℝ≥0∞) ∂law r) (by simp) ?_
    exact lintegral_mono fun ω => by simp only [F]; exact_mod_cast Nat.sub_le N (κ ω)
  change ∫ ω, (κ ω : ℝ) ∂law q' ≤ ∫ ω, (κ ω : ℝ) ∂law q
  rw [hreal q, hreal q']
  have := (ENNReal.toReal_le_toReal (hfin q) (hfin q')).2 hmono
  linarith

/-! ### Non-vacuity -/

/-- With no open pair, every vertex is its own cluster. -/
example : Nat.card (openGraph (∅ : Config (Fin 3))).ConnectedComponent = 3 := by
  have h := card_connectedComponent_eq_sum_inv (∅ : Config (Fin 3))
  simp only [cluster_empty, ncard_singleton, Nat.cast_one, div_one, Finset.sum_const,
    Finset.card_univ, Fintype.card_fin, nsmul_eq_mul, mul_one] at h
  exact_mod_cast h

/-- With every pair open on `Fin 3`, there is one cluster. -/
example : Nat.card (openGraph (univ : Config (Fin 3))).ConnectedComponent = 1 := by
  have h1 := card_connectedComponent_le_insert_add_one (∅ : Config (Fin 3)) s(0, 1)
  have hle : Nat.card (openGraph (univ : Config (Fin 3))).ConnectedComponent ≤ 1 := by
    have hconn : (openGraph (univ : Config (Fin 3))).Preconnected := fun a b => by
      by_cases hab : a = b
      · rw [hab]
      · exact mem_conn_of_mem hab (mem_univ _)
    have : Nonempty (Fin 3) := ⟨0⟩
    have : Subsingleton (openGraph (univ : Config (Fin 3))).ConnectedComponent :=
      ⟨fun C D => by
        obtain ⟨u, rfl⟩ := C.exists_rep
        obtain ⟨v, rfl⟩ := D.exists_rep
        exact ConnectedComponent.sound (hconn u v)⟩
    exact Finite.card_le_one_iff_subsingleton.2 this
  have hpos : 1 ≤ Nat.card (openGraph (univ : Config (Fin 3))).ConnectedComponent :=
    Nat.one_le_iff_ne_zero.2 (Nat.card_ne_zero.2 ⟨⟨(openGraph _).connectedComponentMk 0⟩,
      inferInstance⟩)
  omega

/-- The expected number of clusters is antitone in the profile. -/
example : ∫ ω, (Nat.card (openGraph ω).ConnectedComponent : ℝ)
      ∂law (fun _ : Sym2 Bool => (1 : unitInterval)) ≤
    ∫ ω, (Nat.card (openGraph ω).ConnectedComponent : ℝ)
      ∂law (fun _ : Sym2 Bool => (⟨1 / 2, by norm_num, by norm_num⟩ : unitInterval)) :=
  integral_card_connectedComponent_anti fun _ => unitInterval.le_one _

end PercLib.Percolation.Bond
