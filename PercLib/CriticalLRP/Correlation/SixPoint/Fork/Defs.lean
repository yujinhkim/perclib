/-
Swarm `smwprafq1`, member `m2` (direction B: event/BK side of `p = 5`, `k = 1`).

# Definitions for the six-terminal fork shape

The target inequality is Hutchcroft's Lemma I.4.16 at `p = 5`, `k = 1`,

  `E|K|^5 ≤ 105 (E|K|^2) (E|K|)^6`,

i.e. one *joint pair* of connection events (kept joint so that it sums to the native second
moment `E|K|^2`) plus six single two-point factors.

This file records the objects the event side needs:

* `SevenCertEvent`: seven increasing events certified by seven pairwise disjoint finite
  open sets (input of sevenfold BK);
* `ForkSlots` / `ForkEvent`: the concrete nine-arm six-terminal shape whose sevenfold
  regrouping is *one* joint pair plus *six* two-point events.  The combinatorial tree is

    `b0 — u — a — v — w`  with  `b1` at `u`,  `b2` at `v`,  `b3, b4` at `w`,  `y` at `a`

  (nine arms: `p0 : b0 → u`, `p1 : b1 → u`, `t0 : u → a`, `t1 : a → v`, `p2 : b2 → v`,
  `s2 : v → w`, `p3 : b3 → w`, `p4 : b4 → w`, `p5 : y → a`).  The joint pair is
  `conn b0 a ∩ conn b1 a`, certified by the fork `{p0, p1, t0}` at the common centre `a`;
  the six remaining arms are the six two-point groups.

Definitions only; every proof lives in `Regroup.lean` / `Eval.lean` / `Main.lean`.
-/
module

public import PercLib.CriticalLRP.Correlation.FourthMoment.MixedK2.Final

set_option autoImplicit false

open Set MeasureTheory
open scoped ENNReal BigOperators
open PercLib.Percolation.Bond
open PercLib.Probability

@[expose] public section

namespace PercLib.CriticalLRP.TreeExpansion.FivePoint

variable {V : Type*}

/-- **Seven certified increasing events.**  Seven events with seven pairwise disjoint finite
certificates lying in `ω`; this is the exact hypothesis of sevenfold BK. -/
def SevenCertEvent (A₀ A₁ A₂ A₃ A₄ A₅ A₆ : Set (Config V)) : Set (Config V) :=
  {ω | ∃ W₀ W₁ W₂ W₃ W₄ W₅ W₆ : Set (Sym2 V),
        W₀.Finite ∧ W₁.Finite ∧ W₂.Finite ∧ W₃.Finite ∧ W₄.Finite ∧ W₅.Finite ∧
          W₆.Finite ∧
        W₀ ⊆ ω ∧ W₁ ⊆ ω ∧ W₂ ⊆ ω ∧ W₃ ⊆ ω ∧ W₄ ⊆ ω ∧ W₅ ⊆ ω ∧ W₆ ⊆ ω ∧
        W₀ ∈ A₀ ∧ W₁ ∈ A₁ ∧ W₂ ∈ A₂ ∧ W₃ ∈ A₃ ∧ W₄ ∈ A₄ ∧ W₅ ∈ A₅ ∧ W₆ ∈ A₆ ∧
        Disjoint W₀ W₁ ∧ Disjoint W₀ W₂ ∧ Disjoint W₀ W₃ ∧ Disjoint W₀ W₄ ∧
          Disjoint W₀ W₅ ∧ Disjoint W₀ W₆ ∧
        Disjoint W₁ W₂ ∧ Disjoint W₁ W₃ ∧ Disjoint W₁ W₄ ∧ Disjoint W₁ W₅ ∧
          Disjoint W₁ W₆ ∧
        Disjoint W₂ W₃ ∧ Disjoint W₂ W₄ ∧ Disjoint W₂ W₅ ∧ Disjoint W₂ W₆ ∧
        Disjoint W₃ W₄ ∧ Disjoint W₃ W₅ ∧ Disjoint W₃ W₆ ∧
        Disjoint W₄ W₅ ∧ Disjoint W₄ W₆ ∧ Disjoint W₅ W₆}

/-- **The nine-arm six-terminal fork slot.**  The six terminals are
`b0 b1 b2 b3 b4 y`; `u a v w` are the four branch vertices, with `u` the parent of the root
leaf `b0`, `a` the parent of `u`, `v` next and `w` last.  The single hypothesis is that the
concatenation of the nine arm edge lists has no repeated edge (equivalently: the nine arms
are pairwise edge-disjoint and each is a trail).

The pair centre is `a`; the fork is `p0`, `p1`, `t0` (the root leaf, its sibling `b1`, and the
spine step `u → a`).  The sixth leaf `y` is attached at the subdivision point `a` of the
spine edge `u — v`. -/
def ForkSlots [Countable V] (ω : Config V) (b0 b1 b2 b3 b4 y u a v w : V) : Prop :=
  ∃ (p0 : (openGraph ω).Walk b0 u) (p1 : (openGraph ω).Walk b1 u)
    (t0 : (openGraph ω).Walk u a) (t1 : (openGraph ω).Walk a v)
    (p2 : (openGraph ω).Walk b2 v) (s2 : (openGraph ω).Walk v w)
    (p3 : (openGraph ω).Walk b3 w) (p4 : (openGraph ω).Walk b4 w)
    (p5 : (openGraph ω).Walk y a),
    (p0.edges ++ p1.edges ++ t0.edges ++ t1.edges ++ p2.edges ++ s2.edges ++
      p3.edges ++ p4.edges ++ p5.edges).Nodup

/-- The configuration-level fork event: one of the nine-arm realizations of the six-terminal
fork shape exists, with all four branch vertices existentially quantified. -/
def ForkEvent [Countable V] (b0 b1 b2 b3 b4 y : V) : Set (Config V) :=
  ⋃ u, ⋃ a, ⋃ v, ⋃ w, {ω | ForkSlots ω b0 b1 b2 b3 b4 y u a v w}

/-- The seven BK groups of the fork shape, as a `Fin 7`-indexed family of events at the pair
centre `a` and the two lower hubs `v`, `w`:
group `0` is the **joint pair** `conn b0 a ∩ conn b1 a` (kept joint: it is the group that
sums to the native second moment), and groups `1 … 6` are the six two-point groups
`a — v`, `b2 — v`, `v — w`, `b3 — w`, `b4 — w`, `y — a`. -/
def forkGroup [Countable V] (b0 b1 b2 b3 b4 y a v w : V) : Fin 7 → Set (Config V) :=
  ![conn b0 a ∩ conn b1 a, conn a v, conn b2 v, conn v w, conn b3 w, conn b4 w, conn y a]

/-- **The fork slot diagram**: the right-hand side of the sevenfold BK bound, with the pair
centre `a` and the two lower hubs `v`, `w` summed.  The five free leaves `b1 … b4, y` stay
free (they are summed in the assembly). -/
noncomputable def forkDiagram [Countable V] (π : Sym2 V → unitInterval)
    (b0 b1 b2 b3 b4 y : V) : ℝ≥0∞ :=
  ∑' a, ∑' v, ∑' w,
    jointP π b0 b1 a *
      (tau π a v * (tau π b2 v * (tau π v w * (tau π b3 w * (tau π b4 w * tau π y a)))))

end PercLib.CriticalLRP.TreeExpansion.FivePoint
