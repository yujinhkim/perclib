/-
Split-position star/single data for the remaining `k = 2` certificates of
`Correlation.SixPoint.SplitPattern`.

Swarm `smwxfstjy`, member `m3`, direction `REMAINING-SPLIT-CERTIFICATES`.

Production (`SplitPattern/Regroup.lean`) proves the two-joint/three-single regrouping at
split positions `j = 0, 5, 6` (and `TwoJointThree` at `j = 2` with the star set `{u, w}`).
This directory supplies the three remaining positions `j = 1, 3, 4`.

Nothing here is new mathematics: the file records, as *definitions plus machine-checked
tables*, which star pair and which three residual edge pairs the certificates of this
directory actually use, and verifies against the classification of `SplitPattern.Defs` that

* the star pair really is one of the three admissible `k = 2` star sets at that position
  (`usedStars_mem`), and
* the three single two-point factors really are exactly the residual edges of the split
  tree at that position (`residual_eq_usedSingles`).

That is the finite content the paper's `k`-step (Lemma I.4.16, proof: re-partition the
`p - 1` internal vertices into the two bipartition classes, take `k` from the larger class)
needs: the `k = 2` three-stars are edge-disjoint and their complement is exactly three
edges.  No moment evaluation and no splitting of any joint pair is asserted here.

Vertex indices are those of `SplitPattern.Defs.vert`: `0..4` are `b₀..b₄`, `5` is `t`,
`6, 7, 8` are `u, v, w`, `9` is the landing point `c`.
-/
module

public import PercLib.CriticalLRP.Correlation.SixPoint.SplitPattern.Regroup

/-!
# Star data and residual edges for the seven split certificates

Event and graph data only; no moment evaluation is claimed.
-/

open Set MeasureTheory
open scoped ENNReal BigOperators
open PercLib.Percolation.Bond
open PercLib.CriticalLRP.TreeExpansion
open PercLib.CriticalLRP.TreeExpansion.SixPoint

@[expose] public section

namespace PercLib.CriticalLRP.TreeExpansion.SixPoint.SplitPattern

variable {V : Type*}

/-! ## The star pair used by the certificates at each split position -/

/-- The two internal centres of the two three-stars used by the certificate at split
position `j`.

* `j = 0, 1`: the split arm ends at `u`; the stars are centred at `u` (with leaves
  `b₁, c, v` resp. `b₀, c, v`) and at `w` (leaves `b₃, b₄, v`).
* `j = 2`: production, the stars are centred at `u` and `w`.
* `j = 3, 4`: the split arm ends at `w`; the stars are centred at `u` (leaves `b₀, b₁, v`)
  and at `w` (leaves `b₄, c, v` resp. `b₃, c, v`).
* `j = 5`: the split arm is the spine `u — v`; stars at `u` and at `v`.
* `j = 6`: the split arm is the spine `v — w`; stars at `u` and at the landing point `c`.
-/
def usedStars : Fin 7 → ℕ × ℕ
  | 0 => (6, 8)
  | 1 => (6, 8)
  | 2 => (6, 8)
  | 3 => (6, 8)
  | 4 => (6, 8)
  | 5 => (6, 7)
  | 6 => (6, 9)

/-- The three residual edge pairs, i.e. the three two-point factors of the certificate at
split position `j`, written as vertex index pairs (smaller coordinate first).

* `j = 0`: `b₂ — v`, `b₀ — c`, `t — c`.
* `j = 1`: `b₂ — v`, `b₁ — c`, `t — c`.
* `j = 2`: `t — c`, `b₂ — c`, `c — v` (the production pattern).
* `j = 3`: `b₂ — v`, `b₃ — c`, `t — c`.
* `j = 4`: `b₂ — v`, `b₄ — c`, `t — c`.
* `j = 5`: `b₃ — w`, `b₄ — w`, `t — c`.
* `j = 6`: `b₂ — v`, `b₃ — w`, `b₄ — w`.
-/
def usedSingles : Fin 7 → List (ℕ × ℕ)
  | 0 => [(2, 7), (0, 9), (5, 9)]
  | 1 => [(2, 7), (1, 9), (5, 9)]
  | 2 => [(5, 9), (2, 9), (7, 9)]
  | 3 => [(2, 7), (3, 9), (5, 9)]
  | 4 => [(2, 7), (4, 9), (5, 9)]
  | 5 => [(3, 8), (4, 8), (5, 9)]
  | 6 => [(2, 7), (3, 8), (4, 8)]

/-! ## The five groups of the certificate at each split position -/

/-- The five groups of one `k = 2` certificate, in BK nesting order: the two joint pairs
(each a connection of two leaves to a common spine target) and the three two-point factors. -/
abbrev FiveGroups (V : Type*) : Type _ :=
  Set (Config V) × Set (Config V) × Set (Config V) × Set (Config V) × Set (Config V)

namespace FiveGroups

variable {V : Type*}

/-- The first joint group. -/
def J0 (g : FiveGroups V) : Set (Config V) := g.1

/-- The second joint group. -/
def J1 (g : FiveGroups V) : Set (Config V) := g.2.1

/-- The first two-point factor. -/
def S0 (g : FiveGroups V) : Set (Config V) := g.2.2.1

/-- The second two-point factor. -/
def S1 (g : FiveGroups V) : Set (Config V) := g.2.2.2.1

/-- The third two-point factor. -/
def S2 (g : FiveGroups V) : Set (Config V) := g.2.2.2.2

/-- The certificate event of a five-group assignment. -/
def cert (g : FiveGroups V) : Set (Config V) :=
  TwoJointThreeCert g.J0 g.J1 g.S0 g.S1 g.S2

/-- The fivefold product of the group probabilities, in the nesting order of
`twoJointThree_le`. -/
noncomputable def lawProd (π : Sym2 V → unitInterval) (g : FiveGroups V) : ℝ≥0∞ :=
  law π g.J0 * (law π g.J1 * (law π g.S0 * (law π g.S1 * law π g.S2)))

end FiveGroups

/-- **The five groups at each split position of the six-terminal arm system.**  At split
position `j` the two three-stars are those of `usedStars` and the three two-point factors
are the residual edges of `usedSingles`, translated to vertex level:

* `j = 0`: `(b₁ v, c v)`, `(b₃ v, b₄ v)`, `b₂ v`, `b₀ c`, `t c`
* `j = 1`: `(b₀ v, c v)`, `(b₃ v, b₄ v)`, `b₂ v`, `b₁ c`, `t c`
* `j = 2`: `(b₀ v, b₁ v)`, `(b₃ v, b₄ v)`, `b₂ c`, `c v`, `t c`  (production)
* `j = 3`: `(b₀ v, b₁ v)`, `(b₄ v, c v)`, `b₂ v`, `b₃ c`, `t c`
* `j = 4`: `(b₀ v, b₁ v)`, `(b₃ v, c v)`, `b₂ v`, `b₄ c`, `t c`
* `j = 5`: `(b₀ c, b₁ c)`, `(b₂ w, c w)`, `b₃ w`, `b₄ w`, `t c`
* `j = 6`: `(b₀ v, b₁ v)`, `(v w, t w)`, `b₂ v`, `b₃ w`, `b₄ w`
-/
def splitEvents (b0 b1 b2 b3 b4 t _u v w c : V) : Fin 7 → FiveGroups V
  | 0 => (conn b1 v ∩ conn c v, conn b3 v ∩ conn b4 v, conn b2 v, conn b0 c, conn t c)
  | 1 => (conn b0 v ∩ conn c v, conn b3 v ∩ conn b4 v, conn b2 v, conn b1 c, conn t c)
  | 2 => (conn b0 v ∩ conn b1 v, conn b3 v ∩ conn b4 v, conn b2 c, conn c v, conn t c)
  | 3 => (conn b0 v ∩ conn b1 v, conn b4 v ∩ conn c v, conn b2 v, conn b3 c, conn t c)
  | 4 => (conn b0 v ∩ conn b1 v, conn b3 v ∩ conn c v, conn b2 v, conn b4 c, conn t c)
  | 5 => (conn b0 c ∩ conn b1 c, conn b2 w ∩ conn c w, conn b3 w, conn b4 w, conn t c)
  | _ => (conn b0 v ∩ conn b1 v, conn v w ∩ conn t w, conn b2 v, conn b3 w, conn b4 w)

/-! ## The finite cross-checks against the classification -/

/-- **The star pair used by every certificate is admissible.**  At every split position the
two centres of the certificate are one of the three admissible `k = 2` star sets classified
in `SplitPattern.Defs`, hence (by `star_partition`) the two three-stars are edge-disjoint
and their complement is three residual edges. -/
theorem usedStars_mem : ∀ j : Fin 7, usedStars j ∈ indepPairs j := by decide

/-- The two centres are internally distinct and in increasing order. -/
theorem usedStars_lt : ∀ j : Fin 7, (usedStars j).1 < (usedStars j).2 := by decide

/-- **The three single factors are exactly the residual edges.**  At every split position,
deleting the edges incident to the two star centres from the nine-edge split tree leaves
exactly the three edge pairs of `usedSingles`.  This is the finite statement that the
regrouping is a genuine partition of the nine macro-edges: two three-stars plus three
two-point factors, with no edge dropped and no edge counted twice. -/
theorem residual_eq_usedSingles : ∀ j : Fin 7,
    (residual j (usedStars j).1 (usedStars j).2).toFinset = (usedSingles j).toFinset := by
  decide

/-- The certificate at every split position carries exactly three single two-point factors. -/
theorem usedSingles_length : ∀ j : Fin 7, (usedSingles j).length = 3 := by decide

/-- The leaves of the two three-stars used by the certificate, as vertex indices, listed in
the order the split tree's edge list produces them. -/
def usedLeaves : Fin 7 → List ℕ × List ℕ
  | 0 => ([1, 7, 9], [3, 4, 7])
  | 1 => ([0, 7, 9], [3, 4, 7])
  | 2 => ([0, 1, 7], [3, 4, 7])
  | 3 => ([0, 1, 7], [4, 7, 9])
  | 4 => ([0, 1, 7], [3, 7, 9])
  | 5 => ([0, 1, 9], [2, 8, 9])
  | 6 => ([0, 1, 7], [5, 7, 8])

/-- **The stars used by the certificates are the tree's three-stars.**
The three edges at each chosen centre are exactly the edges to the three listed leaves, so the
two `StarCert`s of the certificate at position `j` carry the macro-edges at `u`/`w`/`v`/`c`
and nothing else.  Together with `residual_eq_usedSingles` this says the certificate's five
groups partition the nine macro-edges of the split tree. -/
theorem nbrs_usedStars : ∀ j : Fin 7,
    nbrs j (usedStars j).1 = (usedLeaves j).1 ∧ nbrs j (usedStars j).2 = (usedLeaves j).2 := by
  decide

/-- The five groups of `splitEvents` at `j = 2` are exactly production's. -/
theorem splitEvents_two (b0 b1 b2 b3 b4 t u v w c : V) :
    splitEvents b0 b1 b2 b3 b4 t u v w c 2 =
      (conn b0 v ∩ conn b1 v, conn b3 v ∩ conn b4 v, conn b2 c, conn c v, conn t c) := rfl

end PercLib.CriticalLRP.TreeExpansion.SixPoint.SplitPattern
